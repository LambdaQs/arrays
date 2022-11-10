open AbsLambdaQs
open AbsQSharp
open Printf
open Map
open List
open Either

let unimplemented_error s = "Not yet implemented: " ^ s

(*
TODO:
1) Q# -> concrete lambda Q#
2) concrete -> abstract lambda Q# (type inference)
3) typechecking lambda Q#
3') Alias typechecking

elaboration and type checking should really be separate
*)

(* NOTE: Elaboration: well-typed and well-scoped programs *)

(* what I will be using for a wildcard var when a placeholer var is needed *)
(* TODO: add freshvars so that different strings represent different exp's *)
let wild_var = MVar (Ident "_wild_")

module Strmap = Map.Make (String)
open Strmap

(*FIXME: we may also need the var -> typ map, including exp here may be useless *)
type env_t =
  { qrefs: int Strmap.t
  ; qalls: int Strmap.t
  ; vars: (typ * exp) Strmap.t
  ; newtys: typ Strmap.t }

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

(* note that a scope is classical iff all its stmts are pure *)
let rec assess_purity_scope (scp : scope) : bool =
  match scp with
  | Scp stmts ->
      fold_left ( && ) true (List.map assess_purity_stmt stmts)

and assess_purity_stmt (stmt : stm) : bool =
  match stmt with _ -> failwith "TODO"

and assess_purity_expr (ex : expr) : bool = match ex with _ -> failwith "TODO"

(* given two LQS types, returns the combined type or returns error if there is a problem *)
(* since things may be void, I made a helper for this *)
(* TODO: figure out what to do with TQRef here *)
(* let combine_types (ty1 : typ) (ty2 : typ) : typ =
   match (ty1, ty2) with
   | TDummy, _ ->
       ty2
       (* FIXME: but sometimes void should take precidence like in a simple if statement? *)
   | _, TDummy ->
       ty1
   | TQref _, TQref _ ->
       ty1
   | _ ->
       if ty1 == ty2 then ty1 else failwith "Branches have different types" *)

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
  | NSClbl (_, calld) :: t -> (
      let f, ty_body, body = elab_calldec calld env in
      match f with
      | MVar (Ident func_name) ->
          let vars' = Strmap.add func_name (ty_body, EVar f) env.vars in
          (* f is a function here *)
          let env' = {env with vars= vars'} in
          let m = elab_nselmts t env in
          (*FIXME: do we want the final type here? or the type of the entire function f *)
          CBnd (ty_body, typeof m env', body, f, m) )
(*FIXME: pretty sure m will always typecheck to unit?*)

(* preps the param, to be used in curry *)
and prep_param (arg : string) (argtyp : tp) (env : env_t) : typ * env_t =
  match argtyp with
  | TpQbit ->
      (*FIXME: should we also be adding to vars here? *)
      let i = cardinal env.qalls in
      (*FIXME: should probably generate i a different way, but fine for now *)
      let qalls' = Strmap.add arg i env.qalls in
      let env' = {env with qalls= qalls'} in
      let qtype = TQAll (MKVar (Ident (string_of_int i))) in
      (qtype, env')
      (*FIXME: if type is Qubit[n], should be more like first branch?
          Not really sure what to do here. *)
  | _ ->
      (*FIXME: this seems slightly wrong, but we need to somehow connect
               argtype to arg when elabing body and I believe this does that *)
      let argtyp' = elab_type argtyp env in
      let vars' = Strmap.add arg (argtyp', EVar (MVar (Ident arg))) env.vars in
      let env' = {env with vars= vars'} in
      (argtyp', env')

(* I am having curry return a type here since its pretty easy to get the type of the curried
   function, possibly easier than to use typeof? *)
and curry (params : param list) (rettyp : tp) (body : body) (env : env_t) :
    typ * exp =
  match params with
  | [] ->
      failwith (unimplemented_error "Empty parameter list")
  | [ParNI (NItem (UIdent arg, typ))] ->
      (* if typ is TQbit, have to do smth entirely different so this gets a bit annoying *)
      let typ', env' = prep_param arg typ env in
      let ty_body, pbody = elab_body body env' in
      let rettyp' = elab_type rettyp env in
      (*TODO: should we be checking ty_body against rettyp'? *)
      ( TFun (typ', rettyp')
      , ELam
          ( typ'
          , rettyp' (*TODO: per above rettyp' could also be ty_body? *)
          , MVar (Ident arg)
          , ECmd (ty_body, pbody) ) )
  | ParNI (NItem (UIdent arg, typ)) :: t ->
      let typ', env' = prep_param arg typ env in
      let cur_ty, cur = curry t rettyp body env' in
      (TFun (typ', cur_ty), ELam (typ', cur_ty, MVar (Ident arg), cur))
  | _ ->
      failwith (unimplemented_error "Nested paramss (ParNIA)")

(* what is going on here? Why these specific return values? *)
and elab_calldec (calld : callDec) (env : env_t) : var * typ * exp =
  match calld with
  (* TODO: make sure only pure things happen inside functions, although qubits can still be passed *)
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) ->
      let rettyp', body' = curry params rettyp body env in
      (MVar (Ident name), rettyp', body')
  (*FIXME: add mechanism here to ensure that functions stay pure *)
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) ->
      let rettyp', body' = curry params rettyp body env in
      (MVar (Ident name), rettyp', body')
  | CDFun (UIdent name, TAList [TIdent new_ty], ParTpl params, rettyp, body) ->
      let newtys' =
        Strmap.add new_ty (TTVar (MTVar (Ident new_ty))) env.newtys
      in
      let env' = {env with newtys= newtys'} in
      let rettyp', body' = curry params rettyp body env' in
      (MVar (Ident name), rettyp', body')
  | _ ->
      failwith (unimplemented_error "Callables with multiple type parameters")

and elab_type (typ : tp) (env : env_t) : typ =
  match typ with
  | TpEmp ->
      failwith (unimplemented_error "(TEmp)")
  | TpPar (TIdent tyarg) -> (
    match Strmap.find_opt tyarg env.newtys with
    | None ->
        failwith "Undefined type variable"
    | Some t ->
        t )
  | TpUDT _ ->
      failwith (unimplemented_error "(TQNm)")
  | TpTpl typs -> (
    match typs with
    (*FIXME: this first case comes up some times, incorrectly I think, but just translating t seems to work well enough *)
    | [t] ->
        elab_type t env
    | [t1; t2] ->
        TProd (elab_type t1 env, elab_type t2 env)
    | _ ->
        failwith "only 2-ples are accepted" )
  | TpFun (ty1, ty2) ->
      TFun (elab_type ty1 env, elab_type ty2 env)
  (* TODO: is TOp the same type as TFun? *)
  | TpOp (ty1, ty2, chars) ->
      TFun (elab_type ty1 env, elab_type ty2 env)
      (*TODO: what to do with chars here? *)
  | TpArr typ ->
      TArr (elab_type typ env)
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

and elab_body (body : body) (env : env_t) : typ * cmd =
  match body with
  | BSpec _ ->
      failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) -> (
      let scope = elab_stmts stmts env in
      match scope with
      | Left exp ->
          (typeof exp env, CRet (typeof exp env, exp))
          (*FIXME: is s_ty the type for both parts here? *)
      | Right cmd ->
          (typeof cmd env, cmd) )
(*FIXME: is it ok that cmd is a command not an exp here? *)

(*
    (* might want to have typ outputted by elab_stmts and elab_exp, in which case this works better here: *)
     let (s_ty, scope) = elab_stmts stmts env in
      match scope with
      | Left exp -> (s_ty, CRet (s_ty, exp)) (*FIXME: is s_ty the type for both parts here? *)
      | Right cmd -> (s_ty, cmd) *)

(* (* not sure if this is the correct approach, so commenting out for now     *)
   if assess_purity_scope (Scp stmts) then
     let exp = elab_stmts_fun stmts env in
     CRet (typeof exp env, exp)
   else elab_stmts_op stmts env *)

and elab_stmts (stmts : stm list) (env : env_t) : (exp, cmd) Either.t =
  match stmts with
  (* TODO: shouldn't always return empty *)
  (* namely, how to deal with the final return statement? *)
  | [] ->
      Left ETriv
  (*FIXME: JZ: I am still pretty confused about this case, so someone should check this *)
  | SExp exp :: stmts' -> (
      let e = elab_exp exp env in
      let s = elab_stmts stmts' env in
      match s with
      | Left e_s ->
          Left (ELet (typeof e env, typeof e_s env, e, wild_var, e_s))
      | Right c_s ->
          Right (CBnd (typeof e env, typeof c_s env, e, wild_var, c_s)) )
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      Left (elab_exp exp env)
      (* TODO: should things after return statement be ignored? *)
  | SFail exp :: stmts' ->
      failwith (unimplemented_error "(SFail)")
  | SLet (bnd, exp) :: stmts' -> (
    match bnd with
    | BndWild -> (
        let e = elab_exp exp env in
        let s = elab_stmts stmts' env in
        match s with
        | Left e_s ->
            Left (ELet (typeof e env, typeof e_s env, e, wild_var, e_s))
        | Right c_s ->
            Right (CBnd (typeof e env, typeof c_s env, e, wild_var, c_s)) )
    | BndName (UIdent var) -> (
        let e = elab_exp exp env in
        let ty_e = typeof e env in
        let vars' = Strmap.add var (ty_e, e) env.vars in
        let env' = {env with vars= vars'} in
        let s = elab_stmts stmts' env' in
        match s with
        | Left e_s ->
            Left (ELet (ty_e, typeof e_s env, e, MVar (Ident var), e_s))
        | Right c_s ->
            Right (CBnd (ty_e, typeof c_s env, e, MVar (Ident var), c_s)) )
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
      (*FIXME: if let bindings occur in if statements, then we should pass an updated env' here *)
      (*however, it is impossible to check this without evaluating the conditions, so things might break!! *)
      let s = elab_stmts stmts'' env in
      let ite = elab_ite (SIf (exp, scope) :: ites) env in
      match stmts'' with
      | [] ->
          (*FIXME: should check if ite is pure or not and encapsulate accordingly *)
          (* or should ite always be an exp. this seems a bit nicer, we don't need to put it in a cmd just because,
             the returns within will be encapsulated *)
          Left ite
      | _ -> (
        match s with
        | Left e_s ->
            Left (ELet (typeof ite env, typeof e_s env, ite, wild_var, e_s))
        | Right c_s ->
            Right (CBnd (typeof ite env, typeof c_s env, ite, wild_var, c_s)) )
      )
  (* these must come after if, so wont be dealt with here *)
  | SEIf (exp, scope) :: stmts' ->
      failwith "Elif statement does not occur after an If statement"
  | SElse scope :: stmts' ->
      failwith "Else statement does not occur after an If statement"
  | SFor (bnd, exp, scope) :: stmts' ->
      failwith (unimplemented_error "statement SFor")
  | SWhile (exp, scope) :: stmts' ->
      failwith (unimplemented_error "statement SWhile")
  (* TODO: can we assume that when SUntil appears, SRep must have come before? *)
  | SRep scope :: stms' ->
      failwith (unimplemented_error "statement SRep")
  | SUntil exp :: stms' ->
      failwith (unimplemented_error "statement SUntil")
  | SUntilF (exp, scope) :: stms' ->
      failwith (unimplemented_error "statement SUntilF")
  | SWithin scope :: stms' ->
      failwith (unimplemented_error "statement SWithin")
  | SApply scope :: stms' ->
      failwith (unimplemented_error "statement SApply")
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
      failwith (unimplemented_error "statement SUseS")

(* Note: should not worry too much about calling quantum things exp's, quantum things will be
   encapsulated accordingly in elab_exp *)
and elab_exp (exp : expr) (env : env_t) : exp =
  match exp with
  | EName (QUnqual (UIdent x)) ->
      EVar (MVar (Ident x))
      (*FIXME: if ECall is a quantum op, things must be done differently here *)
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
  | ECall (e1, [e2; e3; e4]) ->
      EAp
        ( TDummy
          (* its too annoying to access this here and will probably be TDummy anyways *)
        , typeof e3 env
        , EAp (typeof e1 env, typeof e2 env, elab_exp e1 env, elab_exp e2 env)
        , elab_exp e3 env )
  | EEq (e1, e2) ->
      EEql (elab_exp e1 env, elab_exp e2 env)
  | EAdd (e1, e2) ->
      EAdd (elab_exp e1 env, elab_exp e2 env)
  | EArr es ->
      EArrC
        (TDummy, EInt (List.length es), List.map (fun e -> elab_exp e env) es)
  | ETp [e] ->
      elab_exp e env
  | ETp [e1; e2] ->
      EPair (typeof e1 env, typeof e2 env, elab_exp e1 env, elab_exp e2 env)
  | EStr str ->
      EStr str
  | EStrI str ->
      EStr str
  | EEmp ->
      EWld
  | EBool BTru ->
      ETrue
  | EBool BFls ->
      EFls
  (* Is this correct? Why the type mismatch? *)
  | EInt (Integ i) ->
      EInt (int_of_string i)
  | x ->
      failwith
        (unimplemented_error
           ("expressions: " ^ ShowQSharp.show (ShowQSharp.showExpr x)) )

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
(* TODO: type of an if statement may be complex, since types can be ty, ty/void, or void
   should maybe expand this *)
(* TODO: add test for type checking branches in all cases *)
and elab_ite (stmts : stm list) (env : env_t) : exp =
  match stmts with
  | [SIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof e1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof m1 env, cond', ECmd (typeof m1 env, m1), ETriv) )
  (* note that the first two branched are the same *)
  | [SEIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof e1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof m1 env, cond', ECmd (typeof m1 env, m1), ETriv) )
  | [SIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          if typeof e1 env == typeof e2 env then
            EIte (typeof e1 env, cond', e1, e2)
          else failwith "branches cannot be different types"
      | Right m1, Right m2 ->
          if typeof m1 env == typeof m2 env then
            EIte
              ( typeof m1 env
              , cond'
              , ECmd (typeof m1 env, m1)
              , ECmd (typeof m2 env, m2) )
          else failwith "branches cannot be different types"
      | _ ->
          failwith "branches cannot be different purities" )
  | [SEIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          if typeof e1 env == typeof e2 env then
            EIte (typeof e1 env, cond', e1, e2)
          else failwith "branches cannot be different types"
      | Right m1, Right m2 ->
          if typeof m1 env == typeof m2 env then
            EIte
              ( typeof m1 env
              , cond'
              , ECmd (typeof m1 env, m1)
              , ECmd (typeof m2 env, m2) )
          else failwith "branches cannot be different types"
      | _ ->
          failwith "branches cannot be different purities" )
  | SIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          if typeof e1 env == typeof stmts'' env then
            EIte (typeof e1 env, cond', e1, stmts'')
          else failwith "branches cannot be different types"
      | Right m1 ->
          if typeof m1 env == typeof stmts'' env then
            EIte (typeof m1 env, cond', ECmd (typeof m1 env, m1), stmts'')
          else failwith "branches cannot be different types" )
  | SEIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          if typeof e1 env == typeof stmts'' env then
            EIte (typeof e1 env, cond', e1, stmts'')
          else failwith "branches cannot be different types"
      | Right m1 ->
          if typeof m1 env == typeof stmts'' env then
            EIte (typeof m1 env, cond', ECmd (typeof m1 env, m1), stmts'')
          else failwith "branches cannot be different types" )
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
    print_string
      ( "[Input abstract syntax]\n\n"
      ^ (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_prog
      ^ "\n\n" ) ;
    let out_prog =
      elab in_prog {qrefs= empty; qalls= empty; vars= empty; newtys= empty}
    in
    print_string
      ( "[Output abstract syntax]\n\n"
      ^ (fun x -> ShowLambdaQs.show (ShowLambdaQs.showCmd x)) out_prog
      ^ "\n\n" )
;;

elab_example ()
