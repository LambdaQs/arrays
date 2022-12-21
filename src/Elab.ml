open AbsLambdaQs
open AbsQSharp
open Printf
open Map
open List
open Either

let unimplemented_error s = "NYI: " ^ s

type lqsterm = (exp, cmd) Either.t

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

type env_t =
  { qrefs: int Strmap.t
  ; qalls: int Strmap.t
  ; vars: typ Strmap.t
  ; tvars: typ Strmap.t }
(*FIXME: make tvars a more simpler structure *)

(* FIXME: dummy implementation!! *)
(* JZ: what type is term here? Im assuming its an LQS expression *)
(* Kartik: that's right! We are calling `typeof` after elaborating Q# expressions *)
let typeof (term : lqsterm) (env : env_t) : typ =
  match term with
  | Left (EVar (MVar (Ident var_name))) -> (
    match Strmap.find_opt var_name env.vars with
    | None ->
        TDummy (*FIXME: should eventually be an error? *)
    | Some t ->
        t )
  | Left (EArrC (ty, _, _)) ->
      TArr ty
  | Left ETriv ->
      TUnit
  | _ ->
      TDummy

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
(* TODO: figure out what to do with TQRef and TQAll here *)
let rec combine_types (ty1 : typ) (ty2 : typ) : typ =
  match (ty1, ty2) with
  (* TODO: eventually, TDummy should not be allowed here *)
  | TDummy, _ ->
      ty2
  | _, TDummy ->
      ty1
  | TTVar tvar1, TTVar tvar2 ->
      if tvar1 == tvar2 then ty1 else failwith "type variable mismatch"
  | TQref _, TQref _ ->
      ty1
  | TQAll _, TQAll _ ->
      ty1
  | TFun (in1, ou1), TFun (in2, ou2) ->
      TFun (combine_types in1 in2, combine_types ou1 ou2)
  | TAll (tv1, ou1), TAll (tv2, ou2) ->
      if tv1 == tv2 then TAll (tv1, combine_types ou1 ou2)
      else failwith "type variable mismatch"
  | TCmd t1, TCmd t2 ->
      TCmd (combine_types t1 t2)
  | TProd (l1, r1), TFun (l2, r2) ->
      TProd (combine_types l1 l2, combine_types r1 r2)
  | TArr t1, TArr t2 ->
      TArr (combine_types t1 t2)
  | _ ->
      if ty1 == ty2 then ty1
      else
        failwith
          ( "type mismatch:\nty1: "
          ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty1)
          ^ "\nty2: "
          ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty2) )

(* elab takes in the the program and the environment composed of the
   signature and context *)
let rec elab (prog : doc) (env : env_t) : exp =
  match prog with
  | Prog [ns] ->
      elab_nmspace ns env
  | _ ->
      failwith (unimplemented_error "Multiple namespaces")

and elab_nmspace (ns : nmspace) (env : env_t) : exp =
  match ns with
  (* TODO: do something with the namespace's name *)
  (* Should probably store them in the env! *)
  | NDec (_, elmts) ->
      elab_nselmts elmts env

and elab_nselmts (elmts : nSElmnt list) (env : env_t) : exp =
  match elmts with
  (* TODO: do we always want to return empty? *)
  | [] ->
      ETriv
  (* TODO: do something with imports *)
  | NSOp _ :: elmts ->
      elab_nselmts elmts env
  | NSOpAs _ :: elmts ->
      elab_nselmts elmts env
  | NSTy _ :: _ ->
      failwith (unimplemented_error "Type declarations (NSTy)")
  (* TODO: do something with declaration prefix *)
  | NSClbl (_, calld) :: elmts -> (
      let f, ty_body, body = elab_calldec calld env in
      match f with
      | MVar (Ident func_name) ->
          let vars' = Strmap.add func_name ty_body env.vars in
          (* f is a function here *)
          let env' = {env with vars= vars'} in
          let m = elab_nselmts elmts env' in
          (*FIXME: do we want the final type here? or the type of the entire function f *)
          (* JZ: right now, its the entire type which seems correct *)
          ELet (ty_body, typeof (Left m) env', body, f, m) )
(*FIXME: pretty sure m will always typecheck to unit?*)
(*JZ: we say let f = ..body.. in ..m.., so the type of m may have nothing to do with f *)

and elab_calldec (calld : callDec) (env : env_t) : var * typ * exp =
  match calld with
  (* TODO: make sure only pure things happen inside functions, although qubits can still be passed *)
  (* TODO: add mechanism here to ensure that functions stay pure *)
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) ->
      let rettyp', body' = curry [] params rettyp body env in
      (MVar (Ident name), rettyp', body')
  | CDFun (UIdent name, TAList tvars, ParTpl params, rettyp, body) ->
      let rettyp', body' = curry tvars params rettyp body env in
      (MVar (Ident name), rettyp', body')
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) ->
      let rettyp', body' = curry [] params rettyp body env in
      (MVar (Ident name), rettyp', body')
  | CDOp (UIdent name, TAList tvars, ParTpl params, rettyp, _, body) ->
      let rettyp', body' = curry tvars params rettyp body env in
      (MVar (Ident name), rettyp', body')

(* NOTE: curry returns a type here since it's pretty easy to get the type of the curried
   function, possibly easier than to use typeof? *)
and curry (tyvars : tIdent list) (params : param list) (rettyp : tp)
    (body : body) (env : env_t) : typ * exp =
  match (tyvars, params) with
  | tv :: tvs, _ ->
      (* note that these four lines are the 'prep_param' for tyvar. Much simpler, so no helper *)
      let (TIdent tvstr) = tv in
      let tv' = MTVar (Ident tvstr) in
      let tvars' = Strmap.add tvstr (TTVar tv') env.tvars in
      let env' = {env with tvars= tvars'} in
      let cur_ty, cur = curry tvs params rettyp body env' in
      (TAll (tv', cur_ty), ETLam (tv', cur_ty, tv', cur))
  | [], [] ->
      let typ' = TUnit in
      let ty_body, pbody = elab_body body env in
      let rettyp' = elab_type rettyp env in
      ( TFun (typ', rettyp')
      , ELam
          ( typ'
          , rettyp'
          , wild_var (* TODO: might want to make this argument optional *)
          , match pbody with Left e -> e | Right c -> ECmd (ty_body, c) ) )
  | [], [ParNI (NItem (UIdent arg, typ))] ->
      (* if typ is TQbit, have to do smth entirely different so this gets a bit annoying *)
      let typ', env' = prep_param arg typ env in
      let ty_body, pbody = elab_body body env' in
      let rettyp' = elab_type rettyp env in
      ( TFun (typ', combine_types rettyp' ty_body)
        (* note that we check ty_body against rettyp' *)
      , ELam
          ( typ'
          , rettyp'
          , MVar (Ident arg)
          , match pbody with Left e -> e | Right c -> ECmd (ty_body, c) ) )
  | [], ParNI (NItem (UIdent arg, typ)) :: t ->
      let typ', env' = prep_param arg typ env in
      let cur_ty, cur = curry [] t rettyp body env' in
      (TFun (typ', cur_ty), ELam (typ', cur_ty, MVar (Ident arg), cur))
  | [], _ ->
      failwith (unimplemented_error "Nested paramss (ParNIA)")

(* preps the param, to be used in curry *)
and prep_param (arg : string) (argtyp : tp) (env : env_t) : typ * env_t =
  match argtyp with
  | TpQbit ->
      (*FIXME: should probably generate i a different way, but fine for now *)
      let i = cardinal env.qalls in
      let qtype = TQAll (MKVar (Ident (string_of_int i))) in
      let qalls' = Strmap.add arg i env.qalls in
      let vars' = Strmap.add arg qtype env.vars in
      let env' = {env with qalls= qalls'; vars= vars'} in
      (qtype, env')
      (* Note that we basically do the same thing for lists of qubits as qubits *)
  | TpArr TpQbit ->
      let i = cardinal env.qalls in
      let qlisttype = TArr (TQAll (MKVar (Ident (string_of_int i)))) in
      let qalls' = Strmap.add arg i env.qalls in
      let vars' = Strmap.add arg qlisttype env.vars in
      let env' = {env with qalls= qalls'; vars= vars'} in
      (qlisttype, env')
  | _ ->
      let argtyp' = elab_type argtyp env in
      let vars' = Strmap.add arg argtyp' env.vars in
      let env' = {env with vars= vars'} in
      (argtyp', env')

and elab_body (body : body) (env : env_t) : typ * lqsterm =
  match body with
  | BSpec (SSpec (SNBody, SGIntr) :: _) ->
      (TUnit, Left ETriv) (* TODO: add intrinsic unitary to environment? *)
  | BSpec (SSpec (SNBody, SGImpl (_, Scp stmts)) :: _) ->
      let scope = elab_stmts stmts env in
      (typeof scope env, scope)
  | BSpec [] ->
      (TUnit, Left ETriv)
  | BSpec _ ->
      failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) ->
      let scope = elab_stmts stmts env in
      (typeof scope env, scope)

and elab_stmts (stmts : stm list) (env : env_t) : lqsterm =
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
          Left (ELet (typeof (Left e) env, typeof s env, e, wild_var, e_s))
      | Right c_s ->
          Right (CBnd (typeof (Left e) env, typeof s env, e, wild_var, c_s)) )
  (* this one is strightforward, just return the exp *)
  | SRet exp :: _ ->
      Left (elab_exp exp env)
      (*FIXME: in an operaton, this should be a command *)
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
            Left (ELet (typeof (Left e) env, typeof s env, e, wild_var, e_s))
        | Right c_s ->
            Right (CBnd (typeof (Left e) env, typeof s env, e, wild_var, c_s)) )
    | BndName (UIdent var) -> (
        let e = elab_exp exp env in
        let ty_e = typeof (Left e) env in
        let vars' = Strmap.add var ty_e env.vars in
        let env' = {env with vars= vars'} in
        let s = elab_stmts stmts' env' in
        match s with
        | Left e_s ->
            Left (ELet (ty_e, typeof s env, e, MVar (Ident var), e_s))
        | Right c_s ->
            Right (CBnd (ty_e, typeof s env, e, MVar (Ident var), c_s)) )
    | BndTplA bnds ->
        failwith (unimplemented_error "list binds") )
  (* TODO: what differentiates SLet, SMut, and SSet? *)
  | SMut (bnd, exp) :: stmts' ->
      elab_stmts
        (SLet (bnd, exp) :: stmts')
        env (*FIXME: make this specific to Mut *)
  | SSet (bnd, exp) :: stmts' ->
      elab_stmts
        (SLet (bnd, exp) :: stmts')
        env (*FIXME: make this specific to Set *)
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
          (* or should ite always be an exp. this seems a bit nicer, we don't need to put it in a cmd just because,
             the returns within will be encapsulated *)
          Left ite
      | _ -> (
        match s with
        | Left e_s ->
            Left (ELet (typeof (Left ite) env, typeof s env, ite, wild_var, e_s))
        | Right c_s ->
            Right
              (CBnd (typeof (Left ite) env, typeof s env, ite, wild_var, c_s)) )
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
      | BndName (UIdent var) -> (
          let i = cardinal env.qrefs in
          let qtype = TQref (MKey (Ident (string_of_int i))) in
          let qrefs' = Strmap.add var i env.qrefs in
          let vars' = Strmap.add var qtype env.vars in
          let env' = {env with qrefs= qrefs'; vars= vars'} in
          let s = elab_stmts stms' env' in
          match s with
          | Left e_s ->
              Right
                (CBnd
                   ( qtype
                   , typeof s env'
                   , EQloc (MKey (Ident (string_of_int i)))
                   , MVar (Ident var)
                   , CRet (typeof s env, e_s) ) )
          | Right m_s ->
              Right
                (CBnd
                   ( qtype
                   , typeof s env'
                   , EQloc (MKey (Ident (string_of_int i)))
                   , MVar (Ident var)
                   , m_s ) ) )
      | BndTplA bnds ->
          failwith "mismatch in number of binds" )
    | QInitA num ->
        failwith (unimplemented_error "(QInitA)")
    | QInitT qs ->
        failwith (unimplemented_error "(QInitT)") )
  | SUseS (qbitBnd, scope) :: stms' ->
      failwith (unimplemented_error "statement SUseS")

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
(* TODO: make use of combine_types to avoid repeated code *)
and elab_ite (stmts : stm list) (env : env_t) : exp =
  match stmts with
  | [SIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof s1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof s1 env, cond', ECmd (typeof s1 env, m1), ETriv) )
  (* note that the first two branched are the same *)
  | [SEIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof s1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof s1 env, cond', ECmd (typeof s1 env, m1), ETriv) )
  | [SIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      let t1 = typeof s1 env in
      let t2 = typeof s2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          EIte (combine_types t1 t2, cond', e1, e2)
      | Right m1, Right m2 ->
          EIte
            ( combine_types t1 t2
            , ( if typeof (Left cond') env == TBool then cond'
                (*TODO: make sure we should be checking this here! *)
              else failwith "expected bool, different type present" )
            , ECmd (t1, m1)
            , ECmd (t2, m2) )
      | _ ->
          failwith "branches cannot be different types" )
  | [SEIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      let t1 = typeof s1 env in
      let t2 = typeof s2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          EIte (combine_types t1 t2, cond', e1, e2)
      | Right m1, Right m2 ->
          EIte
            ( combine_types t1 t2
            , ( if typeof (Left cond') env == TBool then cond'
              else failwith "expected bool, different type present" )
            , ECmd (t1, m1)
            , ECmd (t2, m2) )
      | _ ->
          failwith "branches cannot be different types" )
  | SIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let t1 = typeof s1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          EIte (combine_types t1 (typeof (Left stmts'') env), cond', e1, stmts'')
      | Right m1 ->
          EIte
            ( combine_types t1 (typeof (Left stmts'') env)
            , cond'
            , ECmd (t1, m1)
            , stmts'' ) )
  | SEIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let s1 = elab_stmts stmts1 env in
      let t1 = typeof s1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          EIte (combine_types t1 (typeof (Left stmts'') env), cond', e1, stmts'')
      | Right m1 ->
          EIte
            ( combine_types t1 (typeof (Left stmts'') env)
            , cond'
            , ECmd (t1, m1)
            , stmts'' ) )
  | _ ->
      failwith "Unexpected case in ITE translation"

(* Note: should not worry too much about calling quantum things exp's,
   quantum things will be encapsulated accordingly in elab_exp *)
and elab_exp (exp : expr) (env : env_t) : exp =
  match exp with
  | QsEEmp ->
      EWld
  | QsEName (QUnqual (UIdent x)) ->
      EVar (MVar (Ident x))
  | QsENameT _ ->
      failwith "TODO: QsENameT"
  | QsEInt (Integ i) ->
      EInt (int_of_string i)
  | QsEBInt (BigInt i) ->
      EInt (int_of_string i) (*FIXME: should this also just be int? *)
  | QsEDbl (Doubl i) ->
      EDbl (float_of_string i)
  | QsEStr str ->
      EStr str
  | QsEStrI str ->
      EStr str
  | QsEBool BTru ->
      ETrue
  | QsEBool BFls ->
      EFls
  | QsERes ROne ->
      ETrue
  | QsERes RZero ->
      EFls
  | QsEPli _ ->
      failwith "TODO: QsEPli"
  | QsETp [e] ->
      (* FIXME: like below in elab type, this maybe should be illegal, but can just turn to normal exp *)
      elab_exp e env
  | QsETp [e1; e2] ->
      let e1' = elab_exp e1 env in
      let e2' = elab_exp e2 env in
      EPair (typeof (Left e1') env, typeof (Left e2') env, e1', e2')
  | QsETp _ ->
      failwith "only 2-ples are accepted"
  | QsEArr es -> (
    match es with
    | [] ->
        EArrC (TUnit, EInt 0, [])
    | e :: es' ->
        let ty = typeof (Left (elab_exp e env)) env in
        EArrC (ty, EInt (List.length es), List.map (fun e -> elab_exp e env) es)
    )
  | QsESArr _ ->
      failwith
        "TODO: QsESArr" (*should we just translate this syntactic sugar? *)
  | QsEItem _ ->
      failwith
        "TODO: QsEItem" (*should we just translate this syntactic sugar? *)
  | QsEUnwrap _ ->
      failwith "TODO: QsEUnwrap"
  | QsEIndex (lis, ind) -> (
      let lis' = elab_exp lis env in
      let ind' = elab_exp ind env in
      match typeof (Left lis') env with
      | TArr ty -> (
        (*TODO: is this correct? We can index into a list with a range, so should be something like this *)
        match ind' with
        | ERng _ ->
            EArrI (TArr ty, lis', ind')
        | ERngR _ ->
            EArrI (TArr ty, lis', ind')
        | ERngL _ ->
            EArrI (TArr ty, lis', ind')
        | EInt _ ->
            EArrI (ty, lis', ind')
        | _ ->
            failwith "incorrect type for indexing into a list" )
      | _ ->
          failwith "expected list type" )
  | QsECtrl _ ->
      failwith "TODO: non-trivial Controlled functor"
  | QsEAdj _ ->
      failwith "TODO: QsEAdj"
  | QsECall (* TODO: This needs to be generalized *)
      ( QsECtrl (QsEName (QUnqual (UIdent "X")))
      , QsEArr [QsEName (QUnqual (UIdent ctl))] :: [tgt] ) ->
      ECmd
        ( TUnit
        , CDiag
            ( MUni (Ident "I")
            , MUni (Ident "X")
            , EVar (MVar (Ident ctl))
            , elab_exp tgt env ) )
  | QsECall (func, es) -> (
      let func' = elab_exp func env in
      match es with
      | [QsETp es'] ->
          elab_app func' es env (* deals with weird uncurried case *)
      | _ ->
          elab_app func' es env )
  | QsEPos _ ->
      failwith "TODO: QsEPos"
  | QsENeg _ ->
      failwith "TODO: QsENeg"
  | QsELNot e ->
      ENot (elab_exp e env)
  | QsEBNot _ ->
      failwith "TODO: QsEBNot"
  | QsEPow (e1, e2) ->
      EPow (elab_exp e1 env, elab_exp e2 env)
  | QsEMul (e1, e2) ->
      EMul (elab_exp e1 env, elab_exp e2 env)
  | QsEDiv (e1, e2) ->
      EDiv (elab_exp e1 env, elab_exp e2 env)
  | QsEMod (e1, e2) ->
      EMod (elab_exp e1 env, elab_exp e2 env)
  | QsEAdd (e1, e2) ->
      EAdd (elab_exp e1 env, elab_exp e2 env)
  | QsESub (e1, e2) ->
      ESub (elab_exp e1 env, elab_exp e2 env)
  | QsEShiftR _ ->
      failwith "TODO: QsEShiftR"
  | QsEShiftL _ ->
      failwith "TODO: QsEShiftL"
  | QsEGt (e1, e2) ->
      EGt (elab_exp e1 env, elab_exp e2 env)
  | QsEGte (e1, e2) ->
      EGte (elab_exp e1 env, elab_exp e2 env)
  | QsELt (e1, _, e2) ->
      ELt (elab_exp e1 env, elab_exp e2 env)
  | QsELte (e1, _, e2) ->
      ELte (elab_exp e1 env, elab_exp e2 env)
  | QsEEq (e1, e2) ->
      EEql (elab_exp e1 env, elab_exp e2 env)
  | QsENeq (e1, e2) ->
      ENEql (elab_exp e1 env, elab_exp e2 env)
  | QsECond (cond, e1, e2) ->
      let e1' = elab_exp e1 env in
      let e2' = elab_exp e2 env in
      let t1 = typeof (Left e1') env in
      let t2 = typeof (Left e2') env in
      if t1 == t2 then EIte (t1, elab_exp cond env, e1', e2')
      else failwith "Type error: QsECond"
  | QsERange (l, r) ->
      ERng (elab_exp l env, elab_exp r env)
  | QsERangeR l ->
      ERngR (elab_exp l env)
  | QsERangeL r ->
      ERngL (elab_exp r env)
  | QsERangeLR ->
      failwith (unimplemented_error "QsERangeLR")
  | x ->
      failwith (unimplemented_error (ShowQSharp.show (ShowQSharp.showExpr x)))

(* separate helper for function application to deal with both curried and uncurried case *)
(* note that it takes in an *)
and elab_app (func : exp) (args : expr list) (env : env_t) : exp =
  match args with
  | [] ->
      failwith "applying function to zero arguments"
  | [e] ->
      let e' = elab_exp e env in
      EAp (typeof (Left func) env, typeof (Left e') env, func, e')
  | e :: es ->
      let f_to_e = elab_app func [e] env in
      elab_app f_to_e es env

and elab_type (typ : tp) (env : env_t) : typ =
  match typ with
  | TpEmp ->
      failwith (unimplemented_error "(TEmp)")
  | TpPar (TIdent tyarg) -> (
    match Strmap.find_opt tyarg env.tvars with
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
      failwith (unimplemented_error "(TpQbit)")
  | TpRng ->
      TRng
  | TpRes ->
      failwith (unimplemented_error "(TpRes)")
  | TpStr ->
      TStr
  | TpUnit ->
      TUnit

let parse (c : in_channel) : doc =
  ParQSharp.pDoc LexQSharp.token (Lexing.from_channel c)

let elab_main () =
  (* TODO: add real cmd line arg parsing *)
  if Array.length Sys.argv != 2 then failwith "Usage: ./TestElab <filename>"
  else
    let channel = open_in Sys.argv.(1) in
    let in_ast = parse channel in
    print_string
      ( "[Input abstract syntax]\n\n"
      ^ (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_ast
      ^ "\n\n" ) ;
    let out_ast =
      elab in_ast {qrefs= empty; qalls= empty; vars= empty; tvars= empty}
    in
    print_string
      ( "[Output abstract syntax]\n\n"
      ^ (fun x -> ShowLambdaQs.show (ShowLambdaQs.showExp x)) out_ast
      ^ "\n\n[Linearized tree]\n\n"
      ^ PrintLambdaQs.printTree PrintLambdaQs.prtExp out_ast
      ^ "\n" )
;;

elab_main ()
