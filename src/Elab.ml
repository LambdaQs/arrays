open AbsLambdaQs
open AbsQSharp
open Printf
open Map
open List

let unimplemented_error s = "Not yet implemented: " ^ s

(*
TODO:
1) Q# -> concrete lambda Q#
2) concrete -> abstract lambda Q# (type inference)
3) typechecking lambda Q#
3') Alias typechecking

elaboration and type checking should really be separate
*)

(* TODO: important note: Elaboration: well-typed and well-scoped programs *)

(* what I will be using for a wildcard var when a placeholer var is needed *)
(* TODO: add freshvars so that different strings represent different exp's *)
let wild_var = MVar (Ident "_wild_")

module Strmap = Map.Make (String)
open Strmap

(* the type of an environment. TODO: figure out specifically how this works *)
(* type env_t = { vars : (typ) Strmap.t } could make this a record to be nicer *)
(* maybe check all variables and scopes etc... on LambdaQS level, but this can still be used as the stack *)
type env_t =
  {qrefs: int Strmap.t; qalls: int Strmap.t; vars: (typ * exp) Strmap.t}

(* FIXME: dummy implementation!! *)
(* JZ: what type is term here? Im assuming its an LQS expression *)
(* Kartik: that's right! We are calling `typeof` after elaborating Q# expressions *)
let typeof term env : typ = TDummy

(* looks for elif* + else? + ... and returns a list of the elifs/elses, and a list of the other stuff *)
let rec extract_ifs (stmts : stm list) : stm list * stm list =
  match stmts with
  | SEIf (e, s) :: stmts' ->
      let ifs, stmts'' = extract_ifs stmts' in
      (SEIf (e, s) :: ifs, stmts'')
  | SElse scope :: stmts' ->
      ([SElse scope], stmts')
  | _ ->
      ([], stmts)

let rec assess_purity_scope (scp : scope) : bool =
  match scp with
  | Scp stmts ->
      fold_left ( && ) true (List.map assess_purity_stmt stmts)

and assess_purity_stmt (stmt : stm) : bool =
  match stmt with _ -> failwith "TODO"

and assess_purity_expr (ex : expr) : bool = match ex with _ -> failwith "TODO"

(*
let add_qubit_cxt (var : string) (env : env_t) (qref : bool) : env_t =
    if qref
    then
        let str_i = string_of_int(cardinal(env.qrefs)) in


    let vars' = Strmap.add var  env.vars in
    let env' = {env with vars = vars'} in
*)

(* given two LQS types, returns the combined type or returns error if there is a problem *)
(* since things may be void, I made a helper for this *)
(* TODO: figure out what to do with TQRef here *)
let combine_types (ty1 : typ) (ty2 : typ) : typ =
  match (ty1, ty2) with
  | TDummy, _ ->
      ty2
      (* FIXME: but sometimes void should take precidence like in a simple if statement? *)
  | _, TDummy ->
      ty1
  | TQref _, TQref _ ->
      ty1
  | _ ->
      if ty1 == ty2 then ty1 else failwith "Branches have different types"

(* elab takes in the the program and the environment composed of the
   signature and context *)
let rec elab (prog : doc) (env : env_t) : cmd =
  match prog with
  | Prog [ns] ->
      elab_nmspace ns env
  | _ ->
      failwith (unimplemented_error "Multiple namespaces")

and elab_nmspace (ns : nmspace) (env : env_t) : cmd =
  match ns with
  (* TODO: do something with the namespace's name *)
  (* Should probably store them in the env! *)
  | NDec (_, elmts) ->
      elab_nselmts elmts env

and elab_nselmts (elmts : nSElmnt list) (env : env_t) : cmd =
  match elmts with
  (* TODO: do we always want to return empty? *)
  | [] ->
      CRet (TUnit, ETriv)
  (* TODO: do something with imports *)
  | NSOp _ :: elmts ->
      elab_nselmts elmts env
  | NSOpAs _ :: elmts ->
      elab_nselmts elmts env
  | NSTy _ :: _ ->
      failwith (unimplemented_error "Type declarations (NSTy)")
  (* TODO: do something with declaration prefix *)
  | NSCall (_, calld) :: t -> (
      let x, body = elab_calldec calld env in
      let ty_body = typeof body env in
      match x with
      | MVar (Ident var_name) ->
          let vars' = Strmap.add var_name (ty_body, EVar x) env.vars in
          let env' = {env with vars= vars'} in
          let m = elab_nselmts t env in
          CBnd (typeof body env, typeof m env', body, x, m) )

(* preps the param, to be used in curry *)
and prep_param (arg : string) (argtyp : tp) (env : env_t) : typ * env_t =
  match argtyp with
  | TpQbit ->
      (*FIXME: should we also be adding to vars here? *)
      let i = cardinal env.qalls in
      let qalls' = Strmap.add arg i env.qalls in
      let env' = {env with qalls= qalls'} in
      let qtype = TQAll (MKVar (Ident (string_of_int i))) in
      (qtype, env')
  | _ ->
      (*FIXME: this seems slightly wrong, but we need to somehow connect argtype to arg when elabing body *)
      let argtyp' = elab_type argtyp in
      (* need to elab here so we can add to context *)
      let vars' = Strmap.add arg (argtyp', EVar (MVar (Ident arg))) env.vars in
      let env' = {env with vars= vars'} in
      (argtyp', env')

and curry (params : param list) (rettyp : tp) (body : body) (env : env_t) : exp
    =
  match params with
  | [] ->
      failwith (unimplemented_error "Empty parameter list")
      (*FIXME: what to do if the param is a qubit? *)
  | [ParNI (NItem (UIdent arg, typ))] ->
      (* if typ is TQbit, have to do smth entirely different so this gets a bit annoying *)
      (*FIXME: if type is Qubit[n], I dont know what to do here/in prep_param (JZ) *)
      let typ', env' = prep_param arg typ env in
      let pbody = elab_body body env' in
      ELam
        ( typ'
        , elab_type rettyp
        , MVar (Ident arg)
        , ECmd (typeof pbody env', pbody) )
      (*FIXME: pbody is a cmd here, so typeof must account for this *)
  | ParNI (NItem (UIdent arg, typ)) :: t ->
      (*FIXME: this branch is wrong!!!! if f a b = c, then the first curry step has rettype b -> c, not c*)
      let typ', env' = prep_param arg typ env in
      ELam (typ', elab_type rettyp, MVar (Ident arg), curry t rettyp body env')
  | _ ->
      failwith (unimplemented_error "Nested paramss (ParNIA)")

(* what is going on here? Why these specific return values? *)
and elab_calldec (calld : callDec) (env : env_t) : var * exp =
  match calld with
  (* TODO: make sure only pure things happen inside functions, although qubits can still be passed *)
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) ->
      (MVar (Ident name), curry params rettyp body env)
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) ->
      (MVar (Ident name), curry params rettyp body env)
  | _ ->
      failwith
        (unimplemented_error
           "Operations with type parameters (tyArg != TAEmpty)" )

(* TODO: should indeed type check at this level *)
(* not translating, but elaborating *)
and elab_type (typ : tp) : typ =
  match typ with
  | TpEmp ->
      failwith (unimplemented_error "(TEmp)")
  | TpPar (TIdent tyarg) ->
      failwith (unimplemented_error "(TPar)")
  | TpUDT _ ->
      failwith (unimplemented_error "(TQNm)")
  | TpTpl typs -> (
    match typs with
    | [t1; t2] ->
        TProd (elab_type t1, elab_type t2)
    | _ ->
        failwith "only 2-ples are accepted" )
  | TpFun (ty1, ty2) ->
      TFun (elab_type ty1, elab_type ty2)
  (* TODO: is TOp the same type as TFun? *)
  | TpOp (ty1, ty2, chars) ->
      TFun (elab_type ty1, elab_type ty2) (*TODO: what to do with chars here? *)
  | TpArr typ ->
      TArr (elab_type typ)
  | TpBInt ->
      failwith (unimplemented_error "(TBInt)")
  | TpBool ->
      TBool
  | TpDbl ->
      failwith (unimplemented_error "(TDbl)")
  | TpInt ->
      TInt
  | TpPli ->
      TPauli
  (* TODO: should send to Qref, but what should the key be? *)
  | TpQbit ->
      (* given polymorphic key *)
      failwith (unimplemented_error "(TQbit)")
  | TpRng ->
      failwith (unimplemented_error "(TRng)")
  | TpRes ->
      failwith (unimplemented_error "(TRes)")
  | TpStr ->
      TStr
  | TpUnit ->
      TUnit

and elab_body (body : body) (env : env_t) : cmd =
  match body with
  | BSpec _ ->
      failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) ->
      if assess_purity_scope (Scp stmts) then
        let exp = elab_stmts_fun stmts env in
        CRet (typeof exp env, exp)
      else elab_stmts_op stmts env

(* TODO: currently, this returns an exp * typ, so is typeof useless? *)
(* can we give a scope a type? probably, at least if there is a void type *)
and elab_stmts_fun (stmts : stm list) (env : env_t) : exp =
  match stmts with
  (* TODO: shouldn't always return empty *)
  (* namely, how to deal with the final return statement? *)
  | [] ->
      ETriv
  (* TODO: in general, we'll want to use CBnd -- what var should we bind to? *)
  (* (* TODO: this is wrong since sometimes we want CGap *)
     | (SExp exp) :: [] -> CRet (elab_exp exp) *)
  (* ENSURE: This is the same as SLet when there is a wild? *)
  | SExp exp :: stmts' ->
      let e = elab_exp exp env in
      let m = elab_stmts_fun stmts' env in
      ELet (typeof e env, typeof m env, e, wild_var, m)
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      elab_exp exp
        env (* TODO: should things after return statement be ignored? *)
  | SFail exp :: stmts' ->
      failwith (unimplemented_error "(SFail)")
  | SLet (bnd, exp) :: stmts' -> (
    match bnd with
    | BndWild ->
        let e = elab_exp exp env in
        let m = elab_stmts_fun stmts' env in
        ELet (typeof e env, typeof m env, e, wild_var, m)
    | BndName (UIdent var) ->
        let e = elab_exp exp env in
        (* TODO: in anycase *)
        let m = elab_stmts_fun stmts' env in
        ELet (typeof e env, typeof m env, e, MVar (Ident var), m)
    | BndTplA bnds ->
        failwith (unimplemented_error "list binds") )
  (* TODO: what differentiates SLet, SMut, and SSet? *)
  | SMut (bnd, exp) :: stmts' ->
      failwith (unimplemented_error "SMut")
  | SSet (bnd, exp) :: stmts' ->
      failwith (unimplemented_error "SSet")
  | SSetOp (UIdent arg, sOp, exp) :: stmts' ->
      failwith (unimplemented_error "SSetOp")
  | SSetW (UIdent arg, exp1, larr, exp2) :: stmts' ->
      failwith (unimplemented_error "SSetW")
  (* TODO: look up how these are done in other languages since the implementation here is probably similar *)
  (* I have some ideas for how this would work, but gets translated to exp anyways and not cmd *)
  (* will either need to figure out what VAR to bind to as in the above or do CRet (EIte)  *)
  | SIf (exp, scope) :: stmts' -> (
      let ites, stmts'' = extract_ifs stmts' in
      let m = elab_stmts_fun stmts'' env in
      let ite = elab_ite (SIf (exp, scope) :: ites) env in
      match stmts'' with
      | [] ->
          ite
      | _ ->
          ELet (typeof ite env, typeof m env, ite, wild_var, m) )
  (* these must come after if, so wont be dealt with here *)
  | SEIf (exp, scope) :: stmts' ->
      failwith "Elif statement does not occur after an If statement"
  | SElse scope :: stmts' ->
      failwith "Else statement does not occur after an If statement"
  | SFor (bnd, exp, scope) :: stmts' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SWhile (exp, scope) :: stmts' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  (* TODO: can we assume that when SUntil appears, SRep must have come before? *)
  | SRep scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUntil exp :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUntilF (exp, scope) :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SWithin scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SApply scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUse (QBnd (bnd, qbitInit)) :: stms' ->
      failwith "Cannot create a Qubit inside a function"
  | SUseS (qbitBnd, scope) :: stms' ->
      failwith "Cannot create a Qubit inside a function"

and elab_stmts_op (stmts : stm list) (env : env_t) : cmd =
  match stmts with
  (* TODO: shouldn't always return empty *)
  (* namely, how to deal with the final return statement? *)
  | [] ->
      CRet (TUnit, ETriv)
  (* TODO: in general, we'll want to use CBnd -- what var should we bind to? *)
  (* (* TODO: this is wrong since sometimes we want CGap *)
     | (SExp exp) :: [] -> CRet (elab_exp exp) *)
  (* I beleive that this is actually the correct translation: *)
  | SExp exp :: stmts' ->
      let m = elab_stmts_op stmts' env in
      let e = elab_exp exp env in
      (* FIXME: typeof seems bad here *)
      CBnd (typeof e env, typeof m env, e, wild_var, m)
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      let e = elab_exp exp env in
      CRet (typeof e env, e)
      (* should things after return statement be ignored? *)
  | SFail exp :: stmts' ->
      failwith (unimplemented_error "(SFail)")
  | SLet (bnd, exp) :: stmts' -> (
    match bnd with
    | BndWild ->
        let m = elab_stmts_op stmts' env in
        let e = elab_exp exp env in
        CBnd (typeof e env, typeof m env, e, wild_var, m)
    | BndName (UIdent var) ->
        let m = elab_stmts_op stmts' env in
        CBnd
          (typeof exp env, typeof m env, elab_exp exp env, MVar (Ident var), m)
    | BndTplA bnds ->
        failwith (unimplemented_error "list binds") )
  (* TODO: what differentiates SLet, SMut, and SSet? *)
  | SMut (bnd, exp) :: stmts' ->
      failwith (unimplemented_error "SMut")
  | SSet (bnd, exp) :: stmts' ->
      failwith (unimplemented_error "SSet")
  | SSetOp (UIdent arg, sOp, exp) :: stmts' ->
      failwith (unimplemented_error "SSetOp")
  | SSetW (UIdent arg, exp1, larr, exp2) :: stmts' ->
      failwith (unimplemented_error "SSetW")
  (* TODO: look up how these are done in other languages since the implementation here is probably similar *)
  (* I have some ideas for how this would work, but gets translated to exp anyways and not cmd *)
  (* will either need to figure out what VAR to bind to as in the above or do CRet (EIte)  *)
  | SIf (exp, scope) :: stmts' ->
      let ites, stmts'' = extract_ifs stmts' in
      let m = elab_stmts_op stmts'' env in
      let ite = elab_ite (SIf (exp, scope) :: ites) env in
      CBnd (typeof ite env, typeof m env, ite, wild_var, m)
  (* these must come after if, so wont be dealt with here *)
  | SEIf (exp, scope) :: stmts' ->
      failwith "Elif statement does not occur after an If statement"
  | SElse scope :: stmts' ->
      failwith "Else statement does not occur after an If statement"
  | SFor (bnd, exp, scope) :: stmts' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SWhile (exp, scope) :: stmts' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  (* TODO: can we assume that when SUntil appears, SRep must have come before? *)
  | SRep scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUntil exp :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUntilF (exp, scope) :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SWithin scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SApply scope :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | SUse (QBnd (bnd, qbitInit)) :: stms' -> (
    match qbitInit with
    | QInitS -> (
      match bnd with
      | BndWild ->
          failwith "Must bind Qubit to a variable"
          (* TODO: should this be an error? *)
      | BndName (UIdent var) ->
          failwith "TODO"
      | BndTplA bnds ->
          failwith "mismatch in number of binds" )
    | QInitA num ->
        failwith (unimplemented_error "(QInitA)")
    | QInitT qs ->
        failwith (unimplemented_error "(QInitT)") )
  | SUseS (qbitBnd, scope) :: stms' ->
      failwith (unimplemented_error "Most statements (SFail, SLet, ...)")

and elab_exp (exp : expr) (env : env_t) : exp =
  match exp with
  | EName (QUnqual (UIdent x)) ->
      EVar (MVar (Ident x))
  | ECall (e1, [e2]) ->
      (* FIXME: env needs to be passed correctly here *)
      EAp (typeof e1 env, typeof e2 env, elab_exp e1 env, elab_exp e2 env)
  | ECall (e1, [e2; e3]) ->
      (* FIXME: env needs to be passed correctly here *)
      EAp
        ( TDummy
          (* its too annoying to access this here and will probably be TDummy anyways *)
        , typeof e3 env
        , EAp (typeof e1 env, typeof e2 env, elab_exp e1 env, elab_exp e2 env)
        , elab_exp e3 env )
  | EEq (e1, e2) ->
      EEq (elab_exp e1 env, elab_exp e2 env)
  | EAdd (e1, e2) ->
      EAdd (elab_exp e1 env, elab_exp e2 env)
  (* Is this correct? Why the type mismatch? *)
  | EInt (Integ i) ->
      EInt (int_of_string i)
  | _ ->
      failwith (unimplemented_error "Most expressions")

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
(* TODO: type type of an if statement may be complex, since types can be ty, ty/void, or void
   should maybe expand this *)
(* TODO: add test for type checking branches in all cases *)
and elab_ite (stmts : stm list) (env : env_t) : exp =
  match stmts with
  | [SIf (cond, Scp stmts')] ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts' env in
      EIte (typeof e1 env, cond', e1, ETriv)
  (* TODO: make sure branches are the same *)
  | [SEIf (cond, Scp stmts')] ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts' env in
      EIte (typeof e1 env, cond', e1, ETriv)
  | [SIf (cond, Scp stmts1); SElse (Scp stmts2)] ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts1 env in
      let e2 = elab_stmts_fun stmts2 env in
      (* FIXME: should we ensure e1 and e2 have same type here? *)
      EIte (typeof e1 env, cond', e1, e2)
  | [SEIf (cond, Scp stmts1); SElse (Scp stmts2)] ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts1 env in
      let e2 = elab_stmts_fun stmts2 env in
      (* FIXME: should we ensure e1 and e2 have same type here? *)
      EIte (typeof e1 env, cond', e1, e2)
  | SIf (cond, Scp stmts1) :: stmts' ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts1 env in
      let stmts'' = elab_ite stmts' env in
      (* FIXME: should we ensure e1 and e2 have same type here? *)
      EIte (typeof e1 env, cond', e1, stmts'')
  | SEIf (cond, Scp stmts1) :: stmts' ->
      let cond' = elab_exp cond env in
      let e1 = elab_stmts_fun stmts1 env in
      let stmts'' = elab_ite stmts' env in
      (* FIXME: should we ensure e1 and e2 have same type here? *)
      EIte (typeof e1 env, cond', e1, stmts'')
  | _ ->
      failwith "Unexpected case in ITE translation"

(* Example: *)
let parse (c : in_channel) : doc =
  ParQSharp.pDoc LexQSharp.token (Lexing.from_channel c)

let elab_example () =
  (* TODO: add real cmd line arg parsing *)
  if Array.length Sys.argv != 2 then failwith "Usage: ./TestElab <filename>"
  else
    let channel = open_in Sys.argv.(1) in
    let in_prog = parse channel in
    let out_prog = elab in_prog {qrefs= empty; qalls= empty; vars= empty} in
    print_string
      ( "[Input abstract syntax]\n\n"
      ^ (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_prog
      ^ "\n\n" ) ;
    print_string
      ( "[Output abstract syntax]\n\n"
      ^ (fun x -> ShowLambdaQs.show (ShowLambdaQs.showCmd x)) out_prog
      ^ "\n\n" )
;;

elab_example ()
