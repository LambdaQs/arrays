open AbsLambdaQs
open AbsQSharp
open Printf
open Map

let unimplemented_error s = "Not yet implemented: " ^ s

(*
TODO:
1) Q# -> concrete lambda Q#
2) concrete -> abstract lambda Q# (type inference)
3) typechecking lambda Q#
3’) Alias typechecking

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
type env_t = {qrefs: int Strmap.t; vars: (typ * exp) Strmap.t}

(* FIXME: dummy implementation!! *)
(* JZ: what is this doing? *)
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

(* should also take in signature (stack data struc to keep track of Qubits) and
   context (to keep track of variables and types) *)
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
  | NSCall (_, calld) :: t ->
      let name, body = elab_calldec calld env in
      let m = elab_nselmts t env in
      CBnd (typeof body env, typeof m env, body, name, m)

and curry (params : param list) (rettyp : tp) (body : body) (is_fun : bool)
    (env : env_t) : exp =
  match params with
  | [] ->
      failwith (unimplemented_error "Empty parameter list")
  | [ParNI (NItem (UIdent arg, typ))] ->
      let pbody = elab_body body is_fun env in
      ELam
        ( elab_type typ
        , elab_type rettyp
        , MVar (Ident arg)
        , ECmd (typeof pbody env, pbody) )
  | ParNI (NItem (UIdent arg, typ)) :: t ->
      ELam
        ( elab_type typ
        , elab_type rettyp
        , MVar (Ident arg)
        , curry t rettyp body is_fun env )
  | _ ->
      failwith (unimplemented_error "Nested paramss (ParNIA)")

(* what is going on here? Why these specific return values? *)
and elab_calldec (calld : callDec) (env : env_t) : var * exp =
  match calld with
  (* make sure only pure things happen inside functions, although qubits can still be passed *)
  (* TODO: should fix this based on the above *)
  (* Kartik: why is TAEmpty being used here? *)
  (* JZ: its just the case where there is no type argument, the much easier case to deal with *)
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) ->
      (MVar (Ident name), curry params rettyp body true env)
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) ->
      (MVar (Ident name), curry params rettyp body false env)
  | _ ->
      failwith (unimplemented_error "Operations with type parameters (tyArg)")

(* TODO: should indeed type check at this level *)
(* not translating, but elaborating *)
and elab_type (typ : tp) : typ =
  match typ with
  | TEmp ->
      failwith (unimplemented_error "(TEmp)")
  | TPar (TIdent tyarg) ->
      failwith (unimplemented_error "(TPar)")
  | TUDT _ ->
      failwith (unimplemented_error "(TQNm)")
  | TTpl typs ->
      failwith (unimplemented_error "(TTpl)")
  (* is this right?? TParr is partial function, which sounds different than just the type of a function  *)
  | TFun (ty1, ty2) ->
      TFun (elab_type ty1, elab_type ty2)
  (* TODO: is TOp the same type as TFun? *)
  | TOp (ty1, ty2, chars) ->
      failwith (unimplemented_error "(TOp)")
  | TArr typ ->
      TArr (elab_type typ)
  | TBInt ->
      failwith (unimplemented_error "(TBInt)")
  | TBool ->
      TBool
  | TDbl ->
      failwith (unimplemented_error "(TDbl)")
  | TInt ->
      TInt
  | TPli ->
      failwith (unimplemented_error "(TPli)")
  (* TODO: should send to Qref, but what should the key be? *)
  | TQbit ->
      failwith (unimplemented_error "(TQbit)")
  | TRng ->
      failwith (unimplemented_error "(TRng)")
  | TRes ->
      failwith (unimplemented_error "(TRes)")
  | TStr ->
      TStr
  | TUnit ->
      TUnit

and elab_body (body : body) (is_fun : bool) (env : env_t) : cmd =
  match body with
  | BSpec _ ->
      failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) ->
      if is_fun then
        let exp, ty = elab_stmts_fun stmts env in
        CRet (exp, ty)
      else elab_stmts_op stmts env

(* TODO: currently, this returns an exp * typ, so is typeof useless? *)
(* can we give a scope a type? probably, at least if there is a void type *)
and elab_stmts_fun (stmts : stm list) (env : env_t) : typ * exp =
  match stmts with
  (* TODO: shouldn't always return empty *)
  (* namely, how to deal with the final return statement? *)
  | [] ->
      (TUnit, ETriv)
  (* TODO: in general, we'll want to use CBnd -- what var should we bind to? *)
  (* (* TODO: this is wrong since sometimes we want CGap *)
     | (SExp exp) :: [] -> CRet (elab_exp exp) *)
  (* ENSURE: This is the same as SLet when there is a wild? *)
  | SExp exp :: stmts' ->
      let ty_e, e = elab_exp exp env in
      let ty_m, m = elab_stmts_fun stmts' env in
      (ty_m, ELet (ty_e, ty_m, e, wild_var, m))
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      elab_exp exp env (* should things after return statement be ignored? *)
  | SFail exp :: stmts' ->
      failwith (unimplemented_error "(SFail)")
  | SLet (bnd, exp) :: stmts' -> (
    match bnd with
    | BndWild ->
        let ty_e, e = elab_exp exp env in
        let ty_m, m = elab_stmts_fun stmts' env in
        (ty_m, ELet (ty_e, ty_m, e, wild_var, m))
    | BndName (UIdent var) ->
        let ty_e, e = elab_exp exp env in
        let vars' = Strmap.add var (ty_e, e) env.vars in
        let env' = {env with vars= vars'} in
        let ty_m, m = elab_stmts_fun stmts' env' in
        (ty_m, ELet (ty_e, ty_m, e, MVar (Ident var), m))
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
      let ty_m, m = elab_stmts_fun stmts'' env in
      let ty_ite, ite = elab_ite (SIf (exp, scope) :: ites) env in
      match stmts'' with
      | [] ->
          (ty_ite, ite)
      | _ ->
          (combine_types ty_ite ty_m, ELet (ty_ite, ty_m, ite, wild_var, m)) )
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
      let ty_e, e = elab_exp exp env in
      (* FIXME: typeof seems bad here *)
      CBnd (ty_e, typeof m env, e, wild_var, m)
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      let ty_e, e = elab_exp exp env in
      CRet (ty_e, e)
      (* should things after return statement be ignored? *)
  | SFail exp :: stmts' ->
      failwith (unimplemented_error "(SFail)")
  | SLet (bnd, exp) :: stmts' -> (
    match bnd with
    | BndWild ->
        let m = elab_stmts_op stmts' env in
        let ty_e, e = elab_exp exp env in
        CBnd (typeof exp env, typeof m env, elab_exp exp, wild_var, m)
    | BndName (UIdent var) ->
        let m = elab_stmts stmts' env in
        CBnd (typeof exp env, typeof m env, elab_exp exp, MVar (Ident var), m)
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
      let m = elab_stmts stmts'' env in
      CBnd
        ( typeof scope env
        , typeof m env
        , elab_ite (SIf (exp, scope) :: ites) env
        , wild_var
        , m )
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

and elab_exp (exp : expr) (env : env_t) : typ * exp =
  match exp with
  | EName (QUnqual (UIdent x)) ->
      EVar (MVar (Ident x))
  | ECall (e1, [e2]) ->
      (* FIXME: env needs to be passed correctly here *)
      EAp (typeof e1 empty, typeof e2 empty, elab_exp e1, elab_exp e2)
  | ECall (e1, [e2; e3]) ->
      (* FIXME: env needs to be passed correctly here *)
      EAp
        ( typeof e1 empty
        , typeof e2 empty
        , EAp (typeof e1 empty, typeof e2 empty, elab_exp e1, elab_exp e2)
        , elab_exp e2 )
  | EEq (e1, e2) ->
      EEq (elab_exp e1, elab_exp e2)
  | EAdd (e1, e2) ->
      EAdd (elab_exp e1, elab_exp e2)
  (* Is this correct? Why the type mismatch? *)
  | EInt (Int i) ->
      EInt (int_of_string i)
  | _ ->
      failwith (unimplemented_error "Most expressions")

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
(* TODO: type type of an if statement may be complex, since types can be ty, ty/void, or void
   should maybe expand this *)
and elab_ite (stmts : stm list) (env : env_t) : typ * exp =
  match stmts with
  | [SIf (cond, Scp stmts')] ->
      let ty_c, cond' = elab_exp cond in
      if cond' != TBool then
        failwith "Expected TBool but different type present"
      else
        let ty_cmd, cmd1 = elab_stmts_fun stmts' env in
        EIte (TUnit, cond', ECmd (TUnit, cmd1), ETriv)
  (* TODO: make sure branches are the same *)
  | [SEIf (cond, Scp stmts')] ->
      let cond' = elab_exp cond in
      let cmd1 = elab_stmts stmts' env in
      EIte (TUnit, cond', ECmd (TUnit, cmd1), ETriv)
  | [SIf (cond, Scp stmts1); SElse (Scp stmts2)] ->
      let cond' = elab_exp cond in
      let cmd1 = elab_stmts stmts1 env in
      let cmd2 = elab_stmts stmts2 env in
      EIte (TUnit, cond', ECmd (TUnit, cmd1), ECmd (TUnit, cmd2))
  | [SEIf (cond, Scp stmts1); SElse (Scp stmts2)] ->
      let cond' = elab_exp cond in
      let cmd1 = elab_stmts stmts1 env in
      let cmd2 = elab_stmts stmts2 env in
      EIte (TUnit, cond', ECmd (TUnit, cmd1), ECmd (TUnit, cmd2))
  | SIf (cond, Scp stmts1) :: stmts' ->
      let cond' = elab_exp cond in
      let cmd1 = elab_stmts stmts1 env in
      let stmts'' = elab_ite stmts' env in
      EIte (TUnit, cond', ECmd (TUnit, cmd1), stmts'')
  | SEIf (cond, Scp stmts1) :: stmts' ->
      let cond' = elab_exp cond in
      let cmd1 = elab_stmts stmts1 env in
      let stmts'' = elab_ite stmts' env in
      EIte (TUnit, cond', ECmd (TUnit, cmd1), stmts'')
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
    let out_prog = elab in_prog empty in
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
