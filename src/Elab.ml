open AbsLambdaQs
open AbsQSharp
open Printf
open Map
open List
open Either

let nyi s = failwith ("NYI: " ^ s)

let type_mismatch_error ty1 ty2 =
  failwith
    ( "type mismatch:\nty1: "
    ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty1)
    ^ "\nty2: "
    ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty2) )

type lqsterm = (exp, cmd) Either.t

(* NOTE: Elaboration: well-typed and well-scoped programs *)

(* what I will be using for a wildcard var when a placeholer var is needed *)
(* TODO: add freshvars so that different strings represent different exp's *)
let wild_var = MVar (Ident "_wild_")

module Strmap = Map.Make (String)
open Strmap

type env_t = {qrefs: int Strmap.t; qalls: int Strmap.t; vars: typ Strmap.t}

(* checks if two types are equal *)
let rec equal_types_bool (ty1 : typ) (ty2 : typ) : bool =
  (* when would this case actually come up? *)
  match (ty1, ty2) with
  | TTVar tv1, TTVar tv2 ->
      tv1 = tv2
  | TQref q1, TQref q2 ->
      q1 = q2
  | TQAll k1, TQAll k2 ->
      k1 = k2 (* TODO: figure out what to do with TQRef and TQAll here *)
  | TFun (in1, ou1), TFun (in2, ou2) ->
      equal_types_bool in1 in2 && equal_types_bool ou1 ou2
  | TAll (tv1, ou1), TAll (tv2, ou2) ->
      (*TODO: what about <T'> -> f(T') vs <U'> -> f(U'), technically these types should be equal *)
      tv1 = tv2 && equal_types_bool ou1 ou2
  | TCmd t1, TCmd t2 ->
      equal_types_bool t1 t2
  | TProd (l1, r1), TProd (l2, r2) ->
      equal_types_bool l1 l2 && equal_types_bool r1 r2
  | TArr t1, TArr t2 ->
      equal_types_bool t1 t2
  | _ ->
      ty1 = ty2

(* given two LQS types, returns the combined type or returns error if there is a problem *)
(* favors ty1 *)
let equal_types (ty1 : typ) (ty2 : typ) : typ =
  if equal_types_bool ty1 ty2 then ty1 else type_mismatch_error ty1 ty2

(* used when replacing an abstract type with a specific type *)
(* favors first input *)
let valid_replacement_type (specty : typ) (absty : typ) : typ =
  match (specty, absty) with
  | TQref _, TQAll _ ->
      specty
  | TQAll _, TQAll _ ->
      specty
  | _ ->
      equal_types specty absty

(*
let rec check_fun_type (theor_ty : typ) (act_ty : typ) (args : typ list) : bool =
    equal_types_bool theor_ty act_ty
 *)

let rec checkfor_dup_qubits (tys : typ list) : bool =
  let rec check_dups (t, ts) =
    match ts with
    | [] ->
        false
    | t1 :: ts' ->
        equal_types_bool t t1 || check_dups (t, ts')
  in
  match tys with [] -> false | t :: ts -> check_dups (t, ts)

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

(* takes T' -> (U' -> ... -> (t1 -> (t2 ... -> (tn -> tout)...) to ( [T',U'...], [t1,...,tout] ) *)
let rec pullout_tyvars (ty : typ) : tVar list * typ =
  match ty with
  | TAll (intv, outy) ->
      let tvs, ty' = pullout_tyvars outy in
      (intv :: tvs, ty')
  | _ ->
      ([], ty)

(* does the opposite of pullout_tyvars, for putting the type back together *)
let rec pushin_tyvars (tvs : tVar list) (ty : typ) : typ =
  match tvs with [] -> ty | tv :: tvs' -> TAll (tv, pushin_tyvars tvs' ty)

(* takes T' -> (U' -> ... -> (t1 -> (t2 ... -> (tn -> tout)...) to ( [T',U'...], t1, (t2 ... -> (tn -> tout)...)) *)
let rec decompose_fun_type (ty : typ) : tVar list * typ * typ =
  match pullout_tyvars ty with
  | tvs, TFun (inty, outy) ->
      (tvs, inty, outy)
  | tvs, ty' ->
      failwith
        ( "expected function type, instead got: "
        ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty') )

(* could make the following into a single function with option type, but this is better for testing *)
let rec contains_poly_type (ty : typ) : bool =
  match ty with
  | TTVar _ ->
      true
  | TQref k ->
      false
  | TQAll kv ->
      false
  | TFun (t1, t2) ->
      contains_poly_type t1 || contains_poly_type t2
  | TAll (tv, ty) ->
      failwith "TODO: can this case occur?"
  | TCmd t ->
      contains_poly_type t
  | TProd (t1, t2) ->
      contains_poly_type t1 || contains_poly_type t2
  | TArr t ->
      contains_poly_type t
  | _ ->
      false

(* returns ("T'", type to replace T' with) *)
(* we assume contains_poly_type ty returns true *)
(* could unify this with contains_poly_type but would require more checks on if types match *)
let rec get_tyvar_replacements (ty : typ) (argty : typ) : (tVar * typ) list =
  match (ty, argty) with
  | TTVar tvar, _ ->
      (* if we simply apply T' -> U' to T', then no replacement is made *)
      (* FIXME: this seems wrong, actually, but won't affect most cases *)
      (* TODO: use fresh vars to fix *)
      [(tvar, argty)]
  | TQref k, TQref k' ->
      []
  | TQAll kv, TQref k ->
      []
  | TQAll kv, TQAll kv' ->
      []
  | TFun (t1, t2), TFun (argty1, argty2) ->
      get_tyvar_replacements t1 argty1 @ get_tyvar_replacements t2 argty2
  | TAll (tv, ty), _ ->
      failwith "TODO: can this case occur?"
  | TCmd ty', TCmd argty' ->
      get_tyvar_replacements ty' argty'
  | TProd (t1, t2), TProd (argty1, argty2) ->
      get_tyvar_replacements t1 argty1 @ get_tyvar_replacements t2 argty2
  | TArr ty', TArr argty' ->
      get_tyvar_replacements ty' argty'
  | _ ->
      if ty = argty then [] else type_mismatch_error ty argty

(* checks that we don't overload type variables *)
let rec safe_replacement (replist : (tVar * typ) list) : (tVar * typ) list =
  let rec remove_dup p ps =
    match (p, ps) with
    | (tv, ty), [] ->
        []
    | (tv, ty), (tv', ty') :: ps' ->
        if tv = tv' then
          if ty = ty' then remove_dup p ps'
          else
            failwith
              ( "trying to replace a single type variable with two different \
                 types: \n\n\
                \                 ty1: "
              ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty)
              ^ "\nty2: "
              ^ ShowLambdaQs.show (ShowLambdaQs.showTyp ty') )
        else (tv', ty') :: remove_dup p ps'
  in
  match replist with [] -> [] | p :: ps -> p :: remove_dup p ps

(* kind of like filter on tvs and map on tys, loops through funty and replaces tv with replty *)
let rec replace_single_tyvar (funty : typ) (tv : tVar) (replty : typ) : typ =
  match funty with
  (* at this step, we filter out the tv that is being replaced *)
  (* uses monomorphization of polymorphic types *)
  | TAll (tv', ty) ->
      if tv = tv' then replace_single_tyvar ty tv replty
      else TAll (tv', replace_single_tyvar ty tv replty)
  (* then we map, should never see TAll after this point *)
  | TFun (ty1, ty2) ->
      TFun
        (replace_single_tyvar ty1 tv replty, replace_single_tyvar ty2 tv replty)
  | TTVar tv' ->
      if tv = tv' then replty else funty
  | TCmd ty1 ->
      TCmd (replace_single_tyvar ty1 tv replty)
  | TProd (ty1, ty2) ->
      TProd
        (replace_single_tyvar ty1 tv replty, replace_single_tyvar ty2 tv replty)
  | TArr ty1 ->
      TArr (replace_single_tyvar ty1 tv replty)
  | _ ->
      funty

let rec replace_tyvars (funty : typ) (tvreps : (tVar * typ) list) : typ =
  match tvreps with
  | [] ->
      funty
  | (tv, replty) :: tvreps' ->
      replace_tyvars (replace_single_tyvar funty tv replty) tvreps'

(* note that as long as TDummy never occurs as an output of typeof, we know it will never occur in the final tree *)
let rec typeof (term : lqsterm) (env : env_t) : typ =
  match term with
  | Left (EVar (MVar (Ident var_name))) -> (
    match Strmap.find_opt var_name env.vars with
    | None ->
        failwith ("variable name not found: " ^ var_name)
    | Some t ->
        t )
  | Left EWld ->
      failwith "TODO: EWld"
  | Left (ELet (t1, t2, e1, v, e2)) ->
      t2 (* TODO: run tests to make sure this is sufficient *)
  | Left (ELam (t1, t2, v, e)) ->
      TFun (t1, t2)
  | Left (ETLam (tv, exp)) ->
      TAll (tv, typeof (Left exp) env)
  (* note that when we build the Eap, we add the types, so t1 and t2 will be the correct form *)
  | Left (EAp (t1, t2, e1, e2)) -> (
    match decompose_fun_type t1 with
    (* since e2 has all instantiated variables, we dont need to worry about tyvars here *)
    | tvs, inty, outy ->
        pushin_tyvars tvs outy )
  (* NOTE: this is a rare case *)
  | Left (ETAp (tv, ty, e1, e2)) ->
      failwith "TODO: ETAp"
  | Left (ECmd (ty, cm)) ->
      ty
  | Left (EQloc key) ->
      failwith "TODO: EQloc"
  | Left (EProj (i, t1, t2, e)) -> (
    match i with
    | 1 ->
        t1
    | 2 ->
        t2
    | _ ->
        failwith "invalid index for projection" )
  | Left (EPair (t1, t2, e1, e2)) ->
      TProd (t1, t2)
  | Left ETriv ->
      TUnit
  | Left ETrue ->
      TBool
  | Left EFls ->
      TBool
  | Left (EIte (ty, _, _, _)) ->
      ty
  | Left (ENot _) ->
      TBool
  | Left (EArrNew (ty, _, _)) ->
      TArr ty
  | Left (EArrRep (ty, _, _)) ->
      TArr ty
  (* this is all already setup in elab_exp below, so just returning ty suffices *)
  | Left (EArrIdx (ty, lis, ind)) ->
      ty
  | Left (EArrLen _) ->
      TInt
  | Left (EPow _) ->
      TInt
  | Left (EMul _) ->
      TInt
  | Left (EDiv _) ->
      TInt
  | Left (EMod _) ->
      TInt
  | Left (EAdd _) ->
      TInt
  | Left (ESub _) ->
      TInt
  | Left (EGt _) ->
      TBool
  | Left (EGte _) ->
      TBool
  | Left (ELt _) ->
      TBool
  | Left (ELte _) ->
      TBool
  | Left (EEql _) ->
      TBool
  | Left (ENEql _) ->
      TBool
  | Left (ERng _) ->
      TRng
  | Left (ERngR _) ->
      TRng
  | Left (ERngL _) ->
      TRng
  | Left (EInt _) ->
      TInt
  | Left (EDbl _) ->
      TDbl
  | Left (EStr _) ->
      TStr
  | Left (EVarT (v, ty)) ->
      ty
  | Right (CRet (ty, exp)) ->
      ty
  | Right (CBnd (ty1, ty2, exp, var, cmd)) ->
      ty2
  | Right (CNew (ty, var, cmd)) ->
      ty
  | Right (CGap _) ->
      TUnit
  | Right (CDiag _) ->
      TUnit
  | Right (CMeas _) ->
      TInt

(* elab takes in the the program and the environment composed of the
   signature and context *)
let rec elab (prog : doc) (env : env_t) : exp =
  match prog with
  | Prog [ns] ->
      elab_nmspace ns env
  | _ ->
      nyi "Multiple namespaces"

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
      nyi "Type declarations (NSTy)"
  (* TODO: do something with declaration prefix *)
  | NSClbl (_, calld) :: elmts -> (
      (* here fexp is a lambda function from the inputs to body *)
      let fvar, fty, fexp = elab_calldec calld env in
      match fvar with
      | MVar (Ident func_name) ->
          let vars' = Strmap.add func_name fty env.vars in
          (* f is a function here *)
          let env' = {env with vars= vars'} in
          let m = elab_nselmts elmts env' in
          ELet (fty, typeof (Left m) env', fexp, fvar, m) )

(*FIXME: pretty sure m will always typecheck to unit?*)
(*JZ: we say let f = ..body.. in ..m.., so the type of m may have nothing to do with f *)

(* FIXME: could make this with curry, curry_tyvars in a nicer way, but this works for now *)
(*TODO: TODO: check rety against type of body and get NewQubit() example to fail *)
and elab_calldec (calld : callDec) (env : env_t) : var * typ * exp =
  match calld with
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) -> (
      let fty, fexp, args, ty_body = curry params body [] env in
      match (rettyp, ty_body) with
      | TpQbit, TQref _ ->
          failwith "trying to return qref that is only in scope of function"
      | TpQbit, TQAll _ ->
          failwith "TODO"
      | TpQbit, _ ->
          failwith "function does not return a qubit"
      | _ ->
          let _ = equal_types ty_body (elab_type rettyp [] env) in
          let fty', fexp' = curry_tyvars [] fty fexp in
          (* add tyvars at this step *)
          (MVar (Ident name), fty', fexp') )
  | CDFun (UIdent name, TAList tvars, ParTpl params, rettyp, body) -> (
      let fty, fexp, args, ty_body =
        curry params body (elab_tyvars tvars) env
      in
      let fty', fexp' = curry_tyvars (elab_tyvars tvars) fty fexp in
      match (rettyp, ty_body) with
      | TpQbit, TQref _ ->
          failwith "trying to return qref that is only in scope of function"
      | TpQbit, TQAll _ ->
          failwith "TODO"
      | TpQbit, _ ->
          failwith "function does not return a qubit"
      | _ ->
          let _ = equal_types ty_body (elab_type rettyp [] env) in
          (MVar (Ident name), fty', fexp') )
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) -> (
      let fty, fexp, args, ty_body = curry params body [] env in
      let fty', fexp' = curry_tyvars [] fty fexp in
      match (rettyp, ty_body) with
      | TpQbit, TQref _ ->
          failwith "trying to return qref that is only in scope of function"
      | TpQbit, TQAll _ ->
          failwith "TODO"
      | TpQbit, _ ->
          failwith "function does not return a qubit"
      | _ ->
          let _ = equal_types ty_body (elab_type rettyp [] env) in
          (MVar (Ident name), fty', fexp') )
  | CDOp (UIdent name, TAList tvars, ParTpl params, rettyp, _, body) -> (
      let fty, fexp, args, ty_body =
        curry params body (elab_tyvars tvars) env
      in
      let fty', fexp' = curry_tyvars (elab_tyvars tvars) fty fexp in
      match (rettyp, ty_body) with
      | TpQbit, TQref _ ->
          failwith "trying to return qref that is only in scope of function"
      | TpQbit, TQAll _ ->
          failwith "TODO"
      | TpQbit, _ ->
          failwith "function does not return a qubit"
      | _ ->
          let _ = equal_types ty_body (elab_type rettyp [] env) in
          (MVar (Ident name), fty', fexp') )

(* very simple function that translates the tIdents to tVars, basically just a map *)
and elab_tyvars (tyvars : tIdent list) : tVar list =
  match tyvars with
  | [] ->
      []
  | tv :: tvs ->
      let (TIdent tvstr) = tv in
      MTVar (Ident tvstr) :: elab_tyvars tvs

(* this just adds the tyvars to the output of curry *)
and curry_tyvars (tyvars : tVar list) (ty : typ) (ex : exp) : typ * exp =
  match tyvars with
  | [] ->
      (ty, ex)
  | tv :: tvs ->
      let ty', ex' = curry_tyvars tvs ty ex in
      (TAll (tv, ty'), ETLam (tv, ex'))

(* FIXME: figure out how the typing works here *)
(* NOTE: curry returns a type here since it's pretty easy to get the type of the curried
   function, possibly easier than to use typeof? *)
(* also note that we don't check against the theoretical function type at this step *)
(* TODO: this function could be split up into multiple functions *)
and curry (params : param list) (body : body) (tyvars : tVar list) (env : env_t)
    : typ * exp * typ list * typ =
  match params with
  | [] ->
      let typ' = TUnit in
      let ty_body, pbody = elab_body body env in
      (* TODO: should i make the replacement here? or should the function be abstract? probably the latter *)
      (* TODO: if return type is tqref, fail, if tqall, check against signature *)
      (* let checked_rettyp = valid_replacement_type ty_body rettyp' in *)
      ( TFun (typ', ty_body)
      , ELam
          ( typ'
          , ty_body
          , wild_var (* TODO: might want to make this argument optional *)
          , match pbody with Left e -> e | Right c -> ECmd (ty_body, c) )
      , []
      , ty_body )
  | [ParNI (NItem (UIdent arg, typ))] ->
      (* if typ is TQbit, have to do smth entirely different so this gets a bit annoying *)
      let typ', env' = prep_param arg typ tyvars env in
      let ty_body, pbody = elab_body body env' in
      ( TFun (typ', ty_body) (* note that we check ty_body against rettyp' *)
      , ELam
          ( typ'
          , ty_body
          , MVar (Ident arg)
          , match pbody with Left e -> e | Right c -> ECmd (ty_body, c) )
      , [typ']
      , ty_body )
  | ParNI (NItem (UIdent arg, typ)) :: t ->
      let typ', env' = prep_param arg typ tyvars env in
      let ty_cur, cur, input_tys, ty_body = curry t body tyvars env' in
      ( TFun (typ', ty_cur)
      , ELam (typ', ty_cur, MVar (Ident arg), cur)
      , typ' :: input_tys
      , ty_body )
  | _ ->
      nyi "Nested paramss (ParNIA)"

(* preps the param, to be used in curry *)
and prep_param (arg : string) (argtyp : tp) (tyvars : tVar list) (env : env_t) :
    typ * env_t =
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
      (* FIXME: is this correct? or should len(l) qalls be created? *)
      let i = cardinal env.qalls in
      let qlisttype = TArr (TQAll (MKVar (Ident (string_of_int i)))) in
      let qalls' = Strmap.add arg i env.qalls in
      let vars' = Strmap.add arg qlisttype env.vars in
      let env' = {env with qalls= qalls'; vars= vars'} in
      (qlisttype, env')
  | _ ->
      let argtyp' = elab_type argtyp tyvars env in
      let vars' = Strmap.add arg argtyp' env.vars in
      let env' = {env with vars= vars'} in
      (argtyp', env')

(* nice helper, that is specialized for let bindings with qubits *)
(* the returned exp is the binding expression *)
and prep_qubit_bind (qvar : string) (q : qbitInit) (env : env_t) :
    typ * exp * env_t =
  match q with
  | QInitS ->
      let i = cardinal env.qrefs in
      let qtype = TQref (MKey (Ident (string_of_int i))) in
      (*this seems pretty redundant, but is perhaps helpful *)
      let qrefs' = Strmap.add qvar i env.qrefs in
      let vars' = Strmap.add qvar qtype env.vars in
      let env' = {env with qrefs= qrefs'; vars= vars'} in
      (qtype, EQloc (MKey (Ident (string_of_int i))), env')
  (* FIXME: should not be qalls, since we are creating len specific qubits *)
  (* FIXME: !!!!!!! figure out this case, since it is the whole point of qsharp-arrays *)
  | QInitA len ->
      let len' = elab_exp len env in
      let _ = equal_types (typeof (Left len') env) TInt in
      let i = cardinal env.qalls in
      let qltype = TArr (TQAll (MKVar (Ident (string_of_int i)))) in
      (*this seems pretty redundant, but is perhaps helpful *)
      let qalls' = Strmap.add qvar i env.qalls in
      let vars' = Strmap.add qvar qltype env.vars in
      let env' = {env with qalls= qalls'; vars= vars'} in
      (*TODO: what goes in the list here? *)
      (qltype, EArrNew (TQAll (MKVar (Ident (string_of_int i))), len', []), env')
  | QInitT qs ->
      failwith "TODO"

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
      nyi "Specializations (BSpec)"
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
      nyi "(SFail)"
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
            Left (ELet (ty_e, typeof s env', e, MVar (Ident var), e_s))
        | Right c_s ->
            Right (CBnd (ty_e, typeof s env', e, MVar (Ident var), c_s)) )
    | BndTplA bnds ->
        nyi "list binds" )
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
      nyi "SSetOp"
  | SSetW (UIdent arg, exp1, larr, exp2) :: stmts' ->
      nyi "SSetW"
  | SIf (exp, scope) :: stmts' -> (
      let ites, stmts'' = extract_ifs stmts' in
      (*FIXME: if let bindings occur in if statements, then we should pass an updated env' here *)
      (*however, it is impossible to check this without evaluating the conditions, so things might break!! *)
      let s = elab_stmts stmts'' env in
      let ite = elab_ite (SIf (exp, scope) :: ites) env in
      match stmts'' with
      | [] ->
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
      nyi "statement SFor"
  | SWhile (exp, scope) :: stmts' ->
      nyi "statement SWhile"
  (* TODO: can we assume that when SUntil appears, SRep must have come before? *)
  | SRep scope :: stms' ->
      nyi "statement SRep"
  | SUntil exp :: stms' ->
      nyi "statement SUntil"
  | SUntilF (exp, scope) :: stms' ->
      nyi "statement SUntilF"
  | SWithin scope :: stms' ->
      nyi "statement SWithin"
  | SApply scope :: stms' ->
      nyi "statement SApply"
  | SUse (QBnd (bnd, qbitInit)) :: stms' -> (
    match bnd with
    | BndWild ->
        failwith "Must bind Qubit to a variable, otherwise they are wasted"
    | BndName (UIdent var) ->
        let qtype, qexp, env' = prep_qubit_bind var qbitInit env in
        let s = elab_stmts stms' env' in
        let s_ty = typeof s env' in
        let s_cmd =
          match s with Left e_s -> CRet (s_ty, e_s) | Right m_s -> m_s
        in
        Right (CNew (s_ty, MVar (Ident var), s_cmd))
    | BndTplA bnds ->
        failwith "mismatch in number of binds" )
  | SUseS (qbitBnd, scope) :: stms' ->
      nyi "statement SUseS"

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
(* TODO: make use of equal_types to avoid repeated code *)
and elab_ite (stmts : stm list) (env : env_t) : exp =
  match stmts with
  (* first two branches are degenerate case when no else, so nothing happens, i.e., we return ETriv *)
  | [SIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof s1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof s1 env, cond', ECmd (typeof s1 env, m1), ETriv) )
  (* note that the first two branched are the same *)
  | [SEIf (cond, Scp stmts')] -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts' env in
      match s1 with
      | Left e1 ->
          EIte (typeof s1 env, cond', e1, ETriv)
      | Right m1 ->
          EIte (typeof s1 env, cond', ECmd (typeof s1 env, m1), ETriv) )
  (* these are the real base cases*)
  | [SIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      let t1 = typeof s1 env in
      let t2 = typeof s2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          EIte (equal_types t1 t2, cond', e1, e2)
      | Right m1, Right m2 ->
          EIte (equal_types t1 t2, cond', ECmd (t1, m1), ECmd (t2, m2))
      | _ ->
          failwith "branches cannot be different types" )
  | [SEIf (cond, Scp stmts1); SElse (Scp stmts2)] -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts1 env in
      let s2 = elab_stmts stmts2 env in
      let t1 = typeof s1 env in
      let t2 = typeof s2 env in
      match (s1, s2) with
      | Left e1, Left e2 ->
          EIte (equal_types t1 t2, cond', e1, e2)
      | Right m1, Right m2 ->
          EIte (equal_types t1 t2, cond', ECmd (t1, m1), ECmd (t2, m2))
      | _ ->
          failwith "branches cannot be different types" )
  | SIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts1 env in
      let t1 = typeof s1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          EIte (equal_types t1 (typeof (Left stmts'') env), cond', e1, stmts'')
      | Right m1 ->
          EIte
            ( equal_types t1 (typeof (Left stmts'') env)
            , cond'
            , ECmd (t1, m1)
            , stmts'' ) )
  | SEIf (cond, Scp stmts1) :: stmts' -> (
      let cond' = elab_exp cond env in
      let _ = equal_types (typeof (Left cond') env) TBool in
      let s1 = elab_stmts stmts1 env in
      let t1 = typeof s1 env in
      let stmts'' = elab_ite stmts' env in
      match s1 with
      | Left e1 ->
          EIte (equal_types t1 (typeof (Left stmts'') env), cond', e1, stmts'')
      | Right m1 ->
          EIte
            ( equal_types t1 (typeof (Left stmts'') env)
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
      EInt (int_of_string i)
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
      (*elab_exp e env *)
      failwith "1-ples not allowed (testing for fix)"
  | QsETp [e1; e2] ->
      let e1' = elab_exp e1 env in
      let e2' = elab_exp e2 env in
      (* let ty1 = typeof (Left e1') env in
         let ty2 = typeof (Left e2') env in
         let ty = equal_types ty1 ty2 in *)
      EPair (typeof (Left e1') env, typeof (Left e2') env, e1', e2')
  | QsETp _ ->
      failwith "only 2-ples are accepted"
  | QsEArr es -> (
    match es with
    | [] ->
        (* FIXME: how to do type inference here? *)
        EArrNew (TUnit, EInt 0, [])
    | e :: es' ->
        let ty = typeof (Left (elab_exp e env)) env in
        EArrNew
          (ty, EInt (List.length es), List.map (fun e -> elab_exp e env) es) )
  | QsESArr (elem, _, num) -> (
      let elem' = elab_exp elem env in
      let num' = elab_exp num env in
      match typeof (Left num') env with
      | TInt ->
          EArrRep (typeof (Left elem') env, num', elem')
      | _ ->
          failwith "must repeat elem with int" )
  | QsEItem _ ->
      failwith "TODO: QsEItem"
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
            EArrIdx (TArr ty, lis', ind')
        | ERngR _ ->
            EArrIdx (TArr ty, lis', ind')
        | ERngL _ ->
            EArrIdx (TArr ty, lis', ind')
        | EInt _ ->
            EArrIdx (ty, lis', ind')
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
  | QsECall (QsEName (QUnqual (UIdent "Length")), es) -> (
    match es with
    | [arr] -> (
        let arr' = elab_exp arr env in
        match typeof (Left arr') env with
        | TArr ty ->
            EArrLen arr'
        | _ ->
            failwith "expected array type" )
    | _ ->
        failwith "Length takes 1 argument" )
  | QsECall (func, es) ->
      let func' = elab_exp func env in
      let es' = List.map (fun e -> elab_exp e env) es in
      let tys = List.map (fun e -> typeof (Left e) env) es' in
      if checkfor_dup_qubits tys (*TODO: add better error message *) then
        failwith "clone error!"
      else elab_app func' es' env
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
      EIte (equal_types t1 t2, elab_exp cond env, e1', e2')
  | QsERange (l, r) ->
      ERng (elab_exp l env, elab_exp r env)
  | QsERangeR l ->
      ERngR (elab_exp l env)
  | QsERangeL r ->
      ERngL (elab_exp r env)
  | QsERangeLR ->
      nyi "QsERangeLR"
  | x ->
      nyi (ShowQSharp.show (ShowQSharp.showExpr x))

(* separate helper for function application to deal with both curried and uncurried case *)
(* TODO: write function that takes in this expr list and checks for duplicated qubits *)
(* NOTE: the type of the function being applied might change, but typeof funcname should always
   return the origional type of the function, so this can always be checked to ensure safety *)
and elab_app (func : exp) (args : exp list) (env : env_t) : exp =
  match args with
  | [] ->
      failwith "applying function to zero arguments"
  | [e] ->
      (*FIXME: deal with type inference here *)
      let argty = typeof (Left e) env in
      let funty = typeof (Left func) env in
      let tvs, arg1ty, outy = decompose_fun_type funty in
      if contains_poly_type arg1ty then
        let reppairs = safe_replacement (get_tyvar_replacements arg1ty argty) in
        (* match reppairs with
           | [(tv, ty)] -> type_mismatch_error (TTVar tv) (replace_single_tyvar funty tv ty)
           | _ -> failwith "???" *)
        (* if (List.length reppairs = 1) then failwith "w" else failwith "y)" *)
        EAp (replace_tyvars funty reppairs, argty, func, e)
        (*TODO: add subtyping at this next step *)
      else
        (* this is where we ensure that arg1 and argty are the same *)
        EAp (funty, valid_replacement_type argty arg1ty, func, e)
  | e :: es ->
      (* we only look at types, so the fact that the exp looks akward is fine for the recursion *)
      let f_to_e = elab_app func [e] env in
      elab_app f_to_e es env

and elab_type (typ : tp) (tyvars : tVar list) (env : env_t) : typ =
  match typ with
  | TpEmp ->
      nyi "(TEmp)"
  | TpPar (TIdent tvstr) ->
      if List.mem (MTVar (Ident tvstr)) tyvars then TTVar (MTVar (Ident tvstr))
      else failwith ("Undefined type variable: " ^ tvstr)
  | TpUDT _ ->
      nyi "(TQNm)"
  | TpTpl typs -> (
    match typs with
    (*FIXME: this first case comes up some times, incorrectly I think, but just translating t seems to work well enough *)
    | [t] ->
        elab_type t tyvars env
    | [t1; t2] ->
        TProd (elab_type t1 tyvars env, elab_type t2 tyvars env)
    | _ ->
        failwith "only 2-ples are accepted" )
  | TpFun (ty1, ty2) ->
      TFun (elab_type ty1 tyvars env, elab_type ty2 tyvars env)
  (* TODO: is TOp the same type as TFun? *)
  | TpOp (ty1, ty2, chars) ->
      TFun (elab_type ty1 tyvars env, elab_type ty2 tyvars env)
      (*TODO: what to do with chars here? *)
  | TpArr typ ->
      TArr (elab_type typ tyvars env)
  | TpBInt ->
      nyi "(TBInt)"
  | TpBool ->
      TBool
  | TpDbl ->
      nyi "(TDbl)"
  | TpInt ->
      TInt
  | TpPli ->
      TPauli
  (* TODO: should send to Qref, but what should the key be? *)
  | TpQbit ->
      nyi "(TpQbit)"
      (* given polymorphic key *)
      (* nyi "(TpQbit)" *)
  | TpRng ->
      TRng
  | TpRes ->
      nyi "(TpRes)"
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
    (* TODO: create an environment where basic functions are defined *)
    let out_ast = elab in_ast {qrefs= empty; qalls= empty; vars= empty} in
    print_string
      ( "[Output abstract syntax]\n\n"
      ^ (fun x -> ShowLambdaQs.show (ShowLambdaQs.showExp x)) out_ast
      ^ "\n\n[Linearized tree]\n\n"
      ^ PrintLambdaQs.printTree PrintLambdaQs.prtExp out_ast
      ^ "\n" )
;;

elab_main ()
