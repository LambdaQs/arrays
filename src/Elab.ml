open AbsLambdaQs
open AbsQSharp
open Printf
open Map
open String
open List
open Either



(* open Z3 *)

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

(******************************)
(* Basic projection functions *)
(******************************)

let tv_var (tv : typedVar) : var = match tv with TyVar (v, t) -> v

let tv_type (tv : typedVar) : typ = match tv with TyVar (v, t) -> t

let te_exp (te : typedExp) : exp = match te with TyExp (e, t) -> e

let te_type (te : typedExp) : typ = match te with TyExp (v, t) -> t

(**************************)
(* General typing helpers *)
(**************************)

(* checks if two types are equal *)
let rec equal_types_bool (ty1 : typ) (ty2 : typ) : bool =
  (*  when would this case actually come up? *)
  match (ty1, ty2) with
  | TTVar tv1, TTVar tv2 ->
      tv1 = tv2
  | TQref q1, TQref q2 ->
      q1 = q2
  | TQAll k1, TQAll k2 ->
      (* TODO: this used to be k1 = k2, but i think it should just be true; SHOULD RUN TESTS! *)
      true
      (* TODO: figure out what to do with TQRef and TQAll here *)
      (* TODO: this can be made more nuances by replacing tvars which may not exactly be the same *)
      (* TODO: do something with constraints here *)
  | TFun (tvs1, ins1, ou1, _, _), TFun (tvs2, ins2, ou2, _, _) -> (
    match (ins1, ins2) with
    | [], [] ->
        tvs1 = tvs2 && equal_types_bool ou1 ou2
    | i1 :: ins1', i2 :: ins2' ->
        equal_types_bool i1 i2
        && equal_types_bool (TFun (tvs1, ins1', ou1, [], [])) (TFun (tvs2, ins2', ou2, [], []))
    | _ ->
        false )
  | TCmd t1, TCmd t2 ->
      equal_types_bool t1 t2
  | TProd (l1, r1), TProd (l2, r2) ->
      equal_types_bool l1 l2 && equal_types_bool r1 r2
  | TArr (s1, t1), TArr (s2, t2) ->
      s1 = s2 && equal_types_bool t1 t2
  | TAbsArr t1, TAbsArr t2 ->
      equal_types_bool t1 t2
  | _ ->
      ty1 = ty2

(* given two LQS types, returns the combined type or returns error if there is a problem *)
(* favors ty1 *)
let equal_types (ty1 : typ) (ty2 : typ) : typ =
  if equal_types_bool ty1 ty2 then ty1 else type_mismatch_error ty1 ty2

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

let rec gen_qubits (var : string) (len : int) (env : env_t) : typ * env_t =
  if len < 0 then failwith "out of bounds qubit creation value"
  else if len = 0 then (TDummy, env)
  else
    let i = cardinal env.qrefs in
    let qtype = TQAll (MKVar (Ident (string_of_int i))) in
    let qname = var ^ string_of_int (i - 1) in
    let qrefs' = Strmap.add qname i env.qrefs in
    let vars' = Strmap.add qname qtype env.vars in
    let env' = {env with qalls= qrefs'; vars= vars'} in
    (* let q_exp = EVar (MVar (Ident qname)) in  *)
    let qs, env'' = gen_qubits var (len - 1) env' in
    (qtype, env'')

(****************************)
(* qubit param name helpers *)
(****************************)

let add_qubit_index (qlty : typ) (ind : int) : typ =
  match qlty with
  | TQAll (MKVar (Ident qlname)) ->
      let qname = qlname ^ "_" ^ string_of_int ind in
      TQAll (MKVar (Ident qname))
  | TQref (MKey _) ->
      failwith "How to deal with indexing here?"
  | _ ->
      qlty

let extract_qubit_index (qlty : typ) (ind : int) : typ = failwith "TODO"

(*******************************)
(* Function definition helpers *)
(*******************************)

(* this checks non qubit types in function signatures, giving a primitive translation fro qs types to lqs types *)
(* no env required, but need tyvars for TpPar check *)
let rec elab_type (tyvars : tVar list) (qstyp : tp) : typ =
  match qstyp with
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
        elab_type tyvars t
    | [t1; t2] ->
        TProd (elab_type tyvars t1, elab_type tyvars t2)
    | _ ->
        failwith "only 2-ples are accepted" )
  | TpFun (ty1, ty2) ->
      TFun ([], [elab_type tyvars ty1], elab_type tyvars ty2, [], [])
  (* TODO: is TOp the same type as TFun? *)
  | TpOp (ty1, ty2, chars) ->
      TFun ([], [elab_type tyvars ty1], elab_type tyvars ty2, [], [])
      (*TODO: what to do with chars here? *)
  | TpArr typ ->
      TAbsArr (elab_type tyvars typ)
  | TpBInt ->
      nyi "(TpBInt)"
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
      failwith "This case should never be hit"
  | TpRng ->
      TRng
  | TpRes ->
      nyi "(TpRes)"
  | TpStr ->
      TStr
  | TpUnit ->
      TUnit

let rec check_for_qubit_in_input (kv : kVar) (args : typedVar list) : bool =
  match args with
  | [] ->
      false
  | TyVar (MVar (Ident s), ty) :: args' -> (
    match ty with
    | TQAll kv' ->
        kv = kv' || check_for_qubit_in_input kv args'
        (* just split up the product, not the nicest code though*)
    | TProd (t1, t2) ->
        check_for_qubit_in_input kv
          (TyVar (MVar (Ident "t1"), t1) :: TyVar (MVar (Ident "t2"), t2) :: args')
        (*FIXME: make more clear and also do we just let qubits have the same kvar as their list? *)
    | TArr (l, ty) ->
        check_for_qubit_in_input kv (TyVar (MVar (Ident "list"), ty) :: args')
    | TAbsArr ty ->
        check_for_qubit_in_input kv (TyVar (MVar (Ident "list"), ty) :: args')
    | _ ->
        check_for_qubit_in_input kv args' )


(* checks the the actual return type is valid *)
let check_retty (theor_retty : tp) (act_retty : typ) (tyvars : tVar list)
    (args : typedVar list) : typ =
  match (theor_retty, act_retty) with
  | TpQbit, TQref _ ->
      failwith "trying to return qref that is only in scope of function"
  | TpQbit, TQAll kv ->
    (* FIXME: this step should be more complex in order to check if the returned 
       qubit type is from an input list. Although where would an awry tqall even come from ??? *)
      if check_for_qubit_in_input kv args then act_retty
      else failwith "returned TQAll that is not in correct scope"
  | TpArr TpQbit, TArr _ ->
      failwith "TODO: checking for TArr Qubit return type"
  | TpArr TpQbit, TAbsArr qall ->
    (* FIXME: from the fixme above, I just assume it would be impossible for a bad TAbsArr to
       show up, but could check that the return came from a param *)
       TAbsArr qall
  | TpQbit, _ ->
      failwith "function does not return a qubit"
      (* FIXME: what about other arrays? We can return an abstract array with a specific array *)
  | _ ->
      equal_types (elab_type tyvars theor_retty) act_retty


(********************************)
(* Function application helpers *)
(********************************)

let rec valid_application (funty : typ) (argty : typ) : bool = failwith "TODO"

(* used when replacing an abstract type with a specific type *)
(* favors first input *)
(* NOTE: this could be used for tvars being replaced with types, but this is done with a different 
   function, so when this is actually called, the main concern is with qubit replacement *)
(* FIXME: considering the previus note, this should be improved specifcally for qubits *)
let rec valid_replacement_type (specty : typ) (absty : typ) : typ =
  match (specty, absty) with
  | TQref _, TQAll _ ->
      specty
  | TQAll _, TQAll _ ->
      specty
  | _, TArr _ ->
      failwith "list arg of function param cannot have definite length"
    (* FIXME: this next line seems wrong and the one after that is maybe wrong*)
  | TArr (l, specty'), TAbsArr absty' ->
      TArr (l, valid_replacement_type specty' absty')
  | TAbsArr specty', TAbsArr absty' ->
      TAbsArr (valid_replacement_type specty' absty')
  | _ ->
      equal_types specty absty

let rec checkfor_dup_qubits (tys : typ list) : bool =
  let rec check_dups (t, ts) =
    match ts with
    | [] ->
        false
    | t1 :: ts' ->
        equal_types_bool t t1 || check_dups (t, ts')
  in
  match tys with
  | [] ->
      false
  | TQref n :: ts ->
      check_dups (TQref n, ts) || checkfor_dup_qubits ts
  | TQAll n :: ts ->
      checkfor_dup_qubits ts
      (* check_dups (TQAll n, ts) || checkfor_dup_qubits ts *)
  (* TODO: add lists here too? *)
  | t :: ts ->
      checkfor_dup_qubits ts

(* could make the following into a single function with option type, but this is better for testing *)
let rec contains_poly_type (ty : typ) : bool =
  match ty with
  | TTVar _ ->
      true
  | TQref k ->
      false
  | TQAll kv ->
      false
  | TFun (tvs, tins, tout, _, _) ->
      List.fold_left ( || ) false (List.map contains_poly_type tins)
      || contains_poly_type tout
  | TCmd t ->
      contains_poly_type t
  | TProd (t1, t2) ->
      contains_poly_type t1 || contains_poly_type t2
  | TArr (s, t) ->
      failwith "list arg of function param cannot have definite length"
  | TAbsArr t ->
      contains_poly_type t
  | _ ->
      false

(* returns [("T'", type to replace T' with)] *)
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
  | TFun (tvs, tins, tour, _, _), TFun (argtvs, argtins, argtout, _, _) ->
      failwith "TODO: for now, we dont consider functions as arguments"
      (* get_tyvar_replacements t1 argty1 @ get_tyvar_replacements t2 argty2 *)
  | TCmd ty', TCmd argty' ->
      get_tyvar_replacements ty' argty'
  | TProd (t1, t2), TProd (argty1, argty2) ->
      get_tyvar_replacements t1 argty1 @ get_tyvar_replacements t2 argty2
  | TArr (s1, ty'), _ ->
      failwith "list arg of function param cannot have definite length"
  | TAbsArr ty', TArr (s2, argty') ->
      get_tyvar_replacements ty' argty'
  | TAbsArr ty', TAbsArr argty' ->
      get_tyvar_replacements ty' argty'
  | _ ->
      (* can hit this case because of the recursion *)
      if ty = argty then [] else type_mismatch_error ty argty

(* checks that we don't overload type variables *)
let rec safe_replacement (replist : (tVar * typ) list) : (tVar * typ) list =
  (* this function should remove all exact copies of p from ps and through error if there are conflicts with p *)
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
  match replist with [] -> [] | p :: ps -> p :: remove_dup p (safe_replacement ps)



(* kind of like filter on tvs and map on tys, loops through funty and replaces tv with replty *)
let rec replace_single_tyvar (paramty : typ) (tv : tVar) (replty : typ) : typ =
   match paramty with
   | TFun (tvs, intys, outy, reqs, ens) ->
       let tvs' = List.filter (fun tv0 -> tv0 <> tv) tvs in
       (* FIXME: this step technically wrong since if a function of type `T -> ... is also an argument
          and `T is overloaded, being a tvar in the outside function that the innard `T will get replaced,
          buy this is (a) too complex and (b) is probably ambiguous bad coding anyways... *)
       let intys' = List.map (fun ty0 -> replace_single_tyvar ty0 tv replty) intys in
       let outy' = replace_single_tyvar outy tv replty in
       TFun (tvs', intys', outy', reqs, ens) 
   | TTVar tv' ->
       if tv = tv' then replty else paramty
   | TCmd ty1 ->
       TCmd (replace_single_tyvar ty1 tv replty)
   | TProd (ty1, ty2) ->
       TProd
         (replace_single_tyvar ty1 tv replty, replace_single_tyvar ty2 tv replty)
   | TArr (s, ty1) ->
       failwith "list arg of function param cannot have definite length"
   | TAbsArr ty1 ->
       TAbsArr (replace_single_tyvar ty1 tv replty)
   | _ ->
      paramty

let rec replace_tyvars_in_type (paramty : typ) (tvreps : (tVar * typ) list) : typ =
   match tvreps with
   | [] ->
      paramty
   | (tv, replty) :: tvreps' ->
      replace_tyvars_in_type (replace_single_tyvar paramty tv replty) tvreps'

let rec replace_tyvars_in_tvlist (tvs : tVar list) (tvreps : (tVar * typ) list) : tVar list =
    match tvreps with 
    | [] -> tvs 
    | (tv, replty) :: tvreps' ->
        replace_tyvars_in_tvlist (List.filter (fun tv0 -> tv0 <> tv) tvs) tvreps'


let rec apply_to_single_arg (tvs : tVar list) (in1ty : typ) (resttys : typ list) (outy : typ) (argty : typ) : typ =
  if contains_poly_type in1ty 
    then 
        let tvreps = safe_replacement (get_tyvar_replacements in1ty argty) in 
        let tvs' = replace_tyvars_in_tvlist tvs tvreps in 
        let resttys' = List.map (fun ty0 -> replace_tyvars_in_type ty0 tvreps) resttys in
        let outy' = replace_tyvars_in_type outy tvreps in
        match resttys' with 
        | [] -> outy' 
        | _ -> TFun (tvs', resttys', outy', [], [])
    else 
        let _ = valid_replacement_type in1ty argty in
        match resttys with 
        | [] -> outy 
        | _ -> TFun (tvs, resttys, outy, [], [])



let rec type_of_application (funty : typ) (args : typedExp list) : typ =
  match funty with 
  | TFun (tvs, intys, outy, _, _) -> 
    (match intys, args with 
    | _, [] -> funty
    | [], a::args -> failwith ("too many arguments to function: "  ^ ShowLambdaQs.show (ShowLambdaQs.showTyp funty))
    | in1ty :: intys', [TyExp (arg1, ty1)] ->
        let funty' = apply_to_single_arg tvs in1ty intys' outy ty1 in
        funty'
    | in1ty :: intys', TyExp (arg1, ty1) :: args' -> 
        let funty' = apply_to_single_arg tvs in1ty intys' outy ty1 in
        type_of_application funty' args'
        )
  | _ -> failwith
        ( "expected function type, ifnstead got: "
        ^ ShowLambdaQs.show (ShowLambdaQs.showTyp funty) )

(*****)
(* This is the main type checker*)
(*****)

(* note that as long as TDummy never occurs as an output of typeof, we know it will never occur in the final tree *)
(* TODO: add some basic Z3 checks here *)
let rec typeof (term : lqsterm) (env : env_t) : typ =
  match term with
  | Left (EVar (MVar (Ident var_name))) -> (
    match Strmap.find_opt var_name env.vars with
    | None ->
        failwith ("variable name not found: " ^ var_name)
    | Some t ->
        t )
  | Left (EArg _) -> failwith "EArg should not show up here since they are only used in constraints"
  | Left EWld ->
      failwith "TODO: EWld"
  | Left (ELet (v, e1, t1, e2, t2)) ->
      t2 (* TODO: run tests to make sure this is sufficient *)
  | Left (ELam (tvs, params, ret_e, ret_t)) ->
      let intys = List.map tv_type params in
      TFun (tvs, intys, ret_t, [], [])
  (* note that when we build the Eap, we add the types, so t1 and t2 will be the correct form *)
  | Left (EAp (f, f_ty, args)) ->
      type_of_application f_ty args
  (* NOTE: this is a rare case *)
  | Left (ETAp (f, f_ty, ty_arg)) ->
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
  | Left (EArrNew (ty, s, _)) ->
      TArr (s, ty)
  | Left (EArrRep (ty, s, _)) ->
      TArr (s, ty)
  | Left (EArrIdx (ty, lis, ind)) ->
      (* FIXME: now that we keep track of lengths, this is now wrong. I think length must also be abstract *)
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
  | Right (CRet (ty, exp)) ->
      ty
  | Right (CBnd (var, exp, ty1, cmd, ty2)) ->
      ty2
  | Right (CNew (ty, var, cmd)) ->
      ty
  | Right (CNewArr (ty, _, var, cmd)) ->
      ty
  | Right (CGap _) ->
      TUnit
  | Right (CDiag _) ->
      TUnit
  | Right (CMeas _) ->
      TInt

(*****)
(* begining of elaboration loop *)
(*****)

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
      let fvar, fexp, fty = elab_calldec calld env in
      match fvar with
      | MVar (Ident func_name) ->
          let vars' = Strmap.add func_name fty env.vars in
          let env' = {env with vars= vars'} in
          let m = elab_nselmts elmts env' in
          ELet (fvar, fexp, fty, m, typeof (Left m) env') )
(*FIXME: eventually elmts in empty, so the last m will typecheck to ETriv? *)

and elab_calldec (calld : callDec) (env : env_t) : var * exp * typ =
  match calld with
  | CDFun (UIdent name, TAEmpty, ParTpl params, rettyp, body) ->
      let params', env' = elab_params [] params env in
      let ty_body, pbody = elab_body body env' in
      let body_exp =
        match pbody with Left e -> e | Right c -> ECmd (ty_body, c)
      in
      let _ = check_retty rettyp ty_body [] params' in
      let fvar = MVar (Ident name) in
      let fexp = ELam ([], params', body_exp, ty_body) in
      let fty = TFun ([], List.map tv_type params', ty_body, [], []) in
      (fvar, fexp, fty)
  | CDFun (UIdent name, TAList tvars, ParTpl params, rettyp, body) ->
      let tvs' = elab_tyvars tvars in
      let params', env' = elab_params tvs' params env in
      let ty_body, pbody = elab_body body env' in
      let body_exp =
        match pbody with Left e -> e | Right c -> ECmd (ty_body, c)
      in
      let _ = check_retty rettyp ty_body tvs' params' in
      let fvar = MVar (Ident name) in
      let fexp = ELam (tvs', params', body_exp, ty_body) in
      let fty = TFun (tvs', List.map tv_type params', ty_body, [], []) in
      (fvar, fexp, fty)
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, rettyp, _, body) ->
      let params', env' = elab_params [] params env in
      let ty_body, pbody = elab_body body env' in
      let body_exp =
        match pbody with Left e -> e | Right c -> ECmd (ty_body, c)
      in
      let _ = check_retty rettyp ty_body [] params' in
      let fvar = MVar (Ident name) in
      let fexp = ELam ([], params', body_exp, ty_body) in
      let fty = TFun ([], List.map tv_type params', ty_body, [], []) in
      (fvar, fexp, fty)
  | CDOp (UIdent name, TAList tvars, ParTpl params, rettyp, _, body) ->
      let tvs' = elab_tyvars tvars in
      let params', env' = elab_params tvs' params env in
      let ty_body, pbody = elab_body body env' in
      let body_exp =
        match pbody with Left e -> e | Right c -> ECmd (ty_body, c)
      in
      let _ = check_retty rettyp ty_body tvs' params' in
      let fvar = MVar (Ident name) in
      let fexp = ELam (tvs', params', body_exp, ty_body) in
      let fty = TFun (tvs', List.map tv_type params', ty_body, [], []) in
      (fvar, fexp, fty)

(* very simple function that translates the tIdents to tVars, basically just a map *)
and elab_tyvars (tyvars : tIdent list) : tVar list =
  match tyvars with
  | [] ->
      []
  | tv :: tvs ->
      let (TIdent tvstr) = tv in
      MTVar (Ident tvstr) :: elab_tyvars tvs

(* processes function parameters. Note that we can process in either order, here we start with the nth arg *)
and elab_params (tyvars : tVar list) (params : param list) (env : env_t) :
    typedVar list * env_t =
  match params with
  | [] ->
      ([], env)
  | ParNI (NItem (UIdent parname, partyp)) :: params' -> (
      match partyp with
      | TpQbit ->
          (* should probably generate i a different way, but fine for now *)
          let i = cardinal env.qalls in
          let qtype = TQAll (MKVar (Ident (string_of_int i))) in
          let qalls' = Strmap.add parname i env.qalls in
          let vars' = Strmap.add parname qtype env.vars in
          let env' = {env with qalls= qalls'; vars= vars'} in
          let params'', env'' = elab_params tyvars params' env' in
          (TyVar (MVar (Ident parname), qtype) :: params'', env'')
          (* Note that we basically do the same thing for lists of qubits as qubits *)
      | TpArr TpQbit ->
          (* FIXME: what should we do here? Perhaps  *)
          let i = cardinal env.qalls in
          (* here we give qall keys a slightly different form for lists *)
          let qlname = "ql" ^ string_of_int i in
          let qlisttype = TAbsArr (TQAll (MKVar (Ident qlname))) in
          let qalls' = Strmap.add parname i env.qalls in
          let vars' = Strmap.add parname qlisttype env.vars in
          let env' = {env with qalls= qalls'; vars= vars'} in
          let params'', env'' = elab_params tyvars params' env' in
          (TyVar (MVar (Ident parname), qlisttype) :: params'', env'')
          (* TODO: add case for tuple *)
      | _ ->
          let partyp' = elab_type tyvars partyp in
          let vars' = Strmap.add parname partyp' env.vars in
          let env' = {env with vars= vars'} in
          let params'', env'' = elab_params tyvars params' env' in
          (TyVar (MVar (Ident parname), partyp') :: params'', env'') )
  | _ ->
      nyi "Nested paramss (ParNIA)"

(* nice helper, that is specialized for let bindings with qubits *)
(* the returned exp is the binding expression *)
and elab_qubit_bind (qvar : string) (q : qbitInit) (stmts : stm list)
    (env : env_t) : cmd * env_t =
  match q with
  | QInitS ->
      let i = cardinal env.qrefs in
      let qtype = TQref (MKey (BNat i)) in
      (*this seems pretty redundant, but is perhaps helpful *)
      let qrefs' = Strmap.add qvar i env.qrefs in
      let vars' = Strmap.add qvar qtype env.vars in
      let env' = {env with qrefs= qrefs'; vars= vars'} in
      let s = elab_stmts stmts env' in
      let s_ty = typeof s env' in
      let s_cmd =
        match s with Left e_s -> CRet (s_ty, e_s) | Right m_s -> m_s
      in
      (CNew (s_ty, MVar (Ident qvar), s_cmd), env')
      (* TODO: figure out what to do with abstract lengths here *)
      (* If the number is not abstract, this is totally easy and we just make i new qrefs. The trouble
         is when the length is abstract because then we make qrefs? but its not clear how many we make. 
         So its like the start, k, is known, but the offset in k+offset is unknown *)
  | QInitA len ->
      (* FIXME: does not really make sence that qlist will have type qall but contain qrefs *)
      let len' = elab_exp len env in
      let _ = equal_types (typeof (Left len') env) TInt in
      let len'' =
        match len' with EInt e -> e | _ -> failwith "TODO: abstract length"
      in
      if len'' < 1 then failwith "cannot have 0 length qubit list"
      else
        let qtype, env' = gen_qubits qvar len'' env in
        let qltype = TArr (BNat len'', qtype) in
        let vars' = Strmap.add qvar qltype env.vars in
        let env'' = {env' with vars= vars'} in
        let s = elab_stmts stmts env'' in
        let s_ty = typeof s env'' in
        let s_cmd =
          match s with Left e_s -> CRet (s_ty, e_s) | Right m_s -> m_s
        in
        (CNewArr (s_ty, BNat len'', MVar (Ident qvar), s_cmd), env')
  | QInitT qs ->
      failwith "TODO (QInitT)"

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
          Left (ELet (wild_var, e, typeof (Left e) env, e_s, typeof s env))
      | Right c_s ->
          Right (CBnd (wild_var, e, typeof (Left e) env, c_s, typeof s env)) )
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
            Left (ELet (wild_var, e, typeof (Left e) env, e_s, typeof s env))
        | Right c_s ->
            Right (CBnd (wild_var, e, typeof (Left e) env, c_s, typeof s env)) )
    | BndName (UIdent var) -> (
        let e = elab_exp exp env in
        let ty_e = typeof (Left e) env in
        let vars' = Strmap.add var ty_e env.vars in
        let env' = {env with vars= vars'} in
        let s = elab_stmts stmts' env' in
        match s with
        | Left e_s ->
            Left (ELet (MVar (Ident var), e, ty_e, e_s, typeof s env'))
        | Right c_s ->
            Right (CBnd (MVar (Ident var), e, ty_e, c_s, typeof s env')) )
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
            Left (ELet (wild_var, ite, typeof (Left ite) env, e_s, typeof s env))
        | Right c_s ->
            Right
              (CBnd (wild_var, ite, typeof (Left ite) env, c_s, typeof s env)) )
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
        let m, _ = elab_qubit_bind var qbitInit stms' env in
        Right m
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
        EArrNew (TDummy, BNat 0, [])
    | e :: es' ->
        let ty = typeof (Left (elab_exp e env)) env in
        EArrNew
          (ty, BNat (List.length es), List.map (fun e -> elab_exp e env) es) )
  | QsESArr (elem, _, num) -> (
      let elem' = elab_exp elem env in
      let num' = elab_exp num env in
      match typeof (Left num') env with
      | TInt ->
          EArrRep (typeof (Left elem') env, BNat 1 (* FIXME: *), elem')
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
      | TArr (s, ty) -> (
        (*FIXME: how to deal with the new length of the list here? *)
        match typeof (Left ind') env with
        | TRng ->
            (* TODO: should EArrIdx hold the type list T or just T??? *)
            (* Currently, I do things so that the type is the type of the entire statement, so an array 
                if indexed with a range or the type held by the list if indexed by an int *)
            EArrIdx (TArr (s, ty), lis', ind')
        | TInt ->
            (* FIXME: what I do with add_qubit_index here seems odd/overcomplicated 
               need to figure out how indexing into arrays works when either the array 
               or the index is abstract. *)
            EArrIdx (ty, lis', ind')
            (* FIXME: do something so that we somehow keep track of where indexed qubits come from.
               If a is a qall list, what type should a[i] have? clearly a qall, perhaps of type k + i??? *)
            (* EArrIdx (add_qubit_index ty integ, lis', ind') *)
        | _ ->
            failwith "incorrect type for indexing into a list"
            (*TODO: bad repeated code from TArr and AAbsArr *) )
      | TAbsArr ty -> (
        match typeof (Left ind') env with
        | TRng ->
            EArrIdx (TAbsArr ty, lis', ind')
        | TInt ->
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
        (*TODO: put CNOT constraint here *)
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
        | TArr (s, ty) ->
            EArrLen arr'
        | TAbsArr ty ->
            EArrLen arr'
        | _ ->
            failwith "expected array type" )
    | _ ->
        failwith "Length takes 1 argument" )
  | QsECall (f, es) -> (
      let fexp = elab_exp f env in
      let fty = typeof (Left fexp) env in
      match fty with
      | TFun (tvs, intys, outy, _, _) ->
          let args = List.map (fun e -> elab_exp e env) es in
          let argtys = List.map (fun e -> typeof (Left e) env) args in
          if checkfor_dup_qubits argtys (*TODO: add better error message *) then
            failwith ("clone error!" )
          else 
            let ap_exp = elab_app fexp fty args argtys env in
            (* this is where we type check the final function application (other checks are run within elab_app)*)
            let _ = typeof (Left ap_exp) env in 
            ap_exp
      | _ ->
          failwith
            ( "expected function type, instead got: "
            ^ ShowLambdaQs.show (ShowLambdaQs.showTyp fty) ) )
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

(* Note: potential duplicate arguments are now checked in elab_exp (only qubits, not functions) *)
(* NOTE: unlike origionally, EAp now holds the more abstract type of the function being applied - no monomorphization occurs.
   Thus, instead we get the specific type of the partially applied function with typeof *)
and elab_app (func : exp) (funty : typ) (args : exp list) (argtys : typ list)
   (env : env_t) : exp =
 match (args, argtys) with
 | [], [] ->
     failwith "applying function to zero arguments"
 | [arg], [argty] ->
       (match func with
       | EAp (func', funty', args') ->
           EAp (func', funty', args' @ [TyExp (arg, argty)])
       | _ ->
           EAp (func, funty, [TyExp (arg, argty)]))
 | arg :: args', argty :: argtys' ->
     (* we only look at types, so the fact that the exp looks akward is fine for the recursion *)
     let f_to_e = elab_app func funty [arg] [argty] env in
     let f_to_e_ty = typeof (Left f_to_e) env in
     elab_app f_to_e f_to_e_ty args' argtys' env
 | _, _ ->
     failwith "impossible case since argtys is a map over args"


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
