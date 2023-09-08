open AbsLambdaQs
open ShowLambdaQs
open AbsQSharp
open Printf
open Map
open String
open List
open Either
open Elab
module Strmap = Map.Make (String)
open Strmap

(* FIXME: use a simler data structure for exivars. Basically just need a set or list *)
type env_t =
  { funcdefs: (exp * typ) Strmap.t
  ; paramvars: int Strmap.t
  ; bodyvars: (exp * typ) Strmap.t
  ; exivars: typ Strmap.t }

(* TODO: see if z3 can actually generate these constraints somehow *)

(* To move forward: connect to qsharp codebase and see if there is any cloning that occurs.
   Expect that qsharp should break. Why is it breaking? If ever there is a function that is unkown,
   probably cloning occurs! *)

let rec replace_args_in_conExp (con : constrExp) (repl_args : constrExp list) :
    constrExp =
  match con with
  | CrApp (MVar (Ident fname), fun_args) ->
      let fun_args' =
        List.map (fun a -> replace_args_in_conExp a repl_args) fun_args
      in
      CrApp (MVar (Ident fname), fun_args')
  | CrArg i ->
      List.nth repl_args i
  | CrRet ->
      CrRet
  | CrExi (Ident i) ->
      CrExi (Ident i)
  | CrFun (Ident fname) ->
      CrFun (Ident fname)
  | CrInt i ->
      CrInt i
  | CrAdd (i1, i2) ->
      CrAdd
        ( replace_args_in_conExp i1 repl_args
        , replace_args_in_conExp i2 repl_args )
  | CrSub (i1, i2) ->
      CrSub
        ( replace_args_in_conExp i1 repl_args
        , replace_args_in_conExp i2 repl_args )
  | CrMul (i1, i2) ->
      CrSub
        ( replace_args_in_conExp i1 repl_args
        , replace_args_in_conExp i2 repl_args )
  | CrMod (i1, i2) ->
      CrSub
        ( replace_args_in_conExp i1 repl_args
        , replace_args_in_conExp i2 repl_args )
  | CrIdx (arr, i) ->
      CrIdx
        ( replace_args_in_conExp arr repl_args
        , replace_args_in_conExp i repl_args )
  | CrLen arr ->
      CrLen (replace_args_in_conExp arr repl_args)

and replace_args_in_con (con : constr) (repl_args : constrExp list) (env : env_t)
    : constr =
  match con with
  | CrIsRange arr ->
      (* FIXME: this should be [] be making the return type constr list, also fixes problems below *)
      CrIsRange (replace_args_in_conExp arr repl_args)
  | CrLt (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrLt (i1', i2')
  | CrLe (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrLe (i1', i2')
  | CrGt (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrGt (i1', i2')
  | CrGe (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrGe (i1', i2')
  | CrEq (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrEq (i1', i2')
  | CrNeq (i1, i2) ->
      let i1' = replace_args_in_conExp i1 repl_args in
      let i2' = replace_args_in_conExp i2 repl_args in
      CrNeq (i1', i2')
  | CrAnd (c1, c2) ->
      let c1' = replace_args_in_con c1 repl_args env in
      let c2' = replace_args_in_con c2 repl_args env in
      CrAnd (c1', c2')
  | CrOr (c1, c2) ->
      let c1' = replace_args_in_con c1 repl_args env in
      let c2' = replace_args_in_con c2 repl_args env in
      CrOr (c1', c2')
  | CrImp (c1, c2) ->
      let c1' = replace_args_in_con c1 repl_args env in
      let c2' = replace_args_in_con c2 repl_args env in
      CrImp (c1', c2')
  | CrForall (Ident var_name, c) ->
      let c' = replace_args_in_con c repl_args env in
      CrForall (Ident var_name, c')
  | CrSatCons (CrArg i, fun_args) -> (
      let fun_args' =
        List.map (fun a -> replace_args_in_conExp a repl_args) fun_args
      in
      match List.nth repl_args i with
      | CrFun (Ident fname) -> (
        match Strmap.find_opt fname env.funcdefs with
        | Some (_, TFun (tvs, ins, TUnit, [r], ens)) ->
            replace_args_in_con r fun_args' env
        | Some (_, TFun (tvs, ins, TUnit, reqs, ens)) ->
            failwith "TODO: generalize to this case"
        | _ ->
            failwith "FIXME: something went wrong 2" )
      | _ ->
          failwith "FIXME: something went wrong" )
  | CrSatCons (_, args) ->
      failwith "CrSatCons: impossible case2"
(*
   (* could also just add params to environment so avoid this *)
   let rec get_param_num (arg : var) (env : env_t) : int =
     let (MVar (Ident vname)) = arg in
     match Strmap.find_opt vname env.paramvars with
     | Some i ->
         i
     | None ->
         failwith ("argument not present in param list: " ^ var_to_string arg) *)

let rec var_to_constrExp (v : var) (params : param list) (env : env_t) :
    constrExp =
  let (MVar (Ident vname)) = v in
  (* TODO: can also potentially substitute functon defs here? What to do when vnam is a func def? *)
  match Strmap.find_opt vname env.bodyvars with
  | Some (e, t) ->
      exp_to_constrExp e params env
  | None -> (
    match Strmap.find_opt vname env.exivars with
    | Some t ->
        CrExi (Ident vname)
    | None -> (
      match Strmap.find_opt vname env.paramvars with
      | Some i ->
          CrArg i
      | None -> (
        match Strmap.find_opt vname env.funcdefs with
        | Some _ ->
            CrFun (Ident vname)
        | None ->
            failwith
              ( "argument not present in funcdefs, bodyvars, exivars, or \
                 paramars: " ^ var_to_string v ) ) ) )

(* NB: this is not really a general function for all exps, but rather, takes chains of function
   applications and turns them into constrExps. So for example, do not call this on a function. *)
and exp_to_constrExp (exp : exp) (params : param list) (env : env_t) : constrExp
    =
  match exp with
  | EVar fvar ->
      var_to_constrExp fvar params env
  | ELam _ ->
      failwith "TODO: impossible case?"
  | EAp (EVar f_var, ty, args) ->
      let cons =
        List.map
          (fun a -> exp_to_constrExp (Elab.get_arg_exp a) params env)
          args
      in
      CrApp (f_var, cons)
  | EAp _ ->
      failwith
        "TODO: other EAp cases, so only the lamdba function case. To fix, just \
         create a var name"
  | EArrLen arr ->
      CrLen (exp_to_constrExp arr params env)
  | EArrIdx (ty, arr, i) ->
      CrIdx (exp_to_constrExp arr params env, exp_to_constrExp i params env)
  | EAdd (i1, i2) ->
      CrAdd (exp_to_constrExp i1 params env, exp_to_constrExp i2 params env)
  | ESub (i1, i2) ->
      CrSub (exp_to_constrExp i1 params env, exp_to_constrExp i2 params env)
  | EMul (i1, i2) ->
      CrMul (exp_to_constrExp i1 params env, exp_to_constrExp i2 params env)
  | EMod (i1, i2) ->
      CrMod (exp_to_constrExp i1 params env, exp_to_constrExp i2 params env)
  | EInt i ->
      CrInt i
  | _ ->
      print_endline (ShowLambdaQs.show (ShowLambdaQs.showExp exp)) ;
      failwith "TODO: all other cases"

(* FIXME: what happens if we call CNOT on variables that are in the scope of the function?
   Then we dont have the variable in scope where the constraint is. But this also means we
   have more information on the variable since it is defined in the body. So do we do some
   sort of evaluation here? *)
let rec generate_clone_reqs (tvs : tVar list) (params : param list) (body : exp)
    (env : env_t) : constr list =
  match body with
  | EVar _ ->
      []
      (* Note the two different types of let bindings, one wild with operation and one pure *)
  | ELet (MVar (Ident "_wild_"), vexp, vty, bexp, bty) ->
      let cs1 = generate_clone_reqs tvs params vexp env in
      let cs2 = generate_clone_reqs tvs params bexp env in
      cs1 @ cs2
      (* In this branch, I assume we cant have something like let a = CNOT(a,b) ... *)
  | ELet (MVar (Ident vname), vexp, vty, bexp, bty) ->
      (* because of let _ = cnot(a,b) in ..., we must look for constraints in vexp *)
      (* let cs1 = generate_clone_reqs tvs params vexp env in *)
      let bodyvars' = Strmap.add vname (vexp, vty) env.bodyvars in
      let env' = {env with bodyvars= bodyvars'} in
      let cs2 = generate_clone_reqs tvs params bexp env' in
      cs2
      (* cs1 @ cs2 *)
  | EAp (EVar (MVar (Ident "CNOT")), _, [Arg (a1, ty1); Arg (a2, ty2)]) ->
      let ce1 = exp_to_constrExp a1 params env in
      let ce2 = exp_to_constrExp a2 params env in
      [CrNeq (ce1, ce2)]
  (* Here, we assume that if the return type is unit and the function is a parameter, there are some
     abstract requirements. *)
  | EAp (EVar (MVar (Ident func_name)), TFun (_, _, TUnit, _, _), args) -> (
      (* note that the reqs in TFun above are empty, so we must fetch them from the environment *)
      let reqs =
        match Strmap.find_opt func_name env.funcdefs with
        | Some (_, TFun (_, _, _, rs, _)) ->
            rs
        | _ ->
            []
        (* failwith
           "func name not found; case shouldnt come up because an error \
            would be thrown earlier" *)
      in
      let cons =
        List.map
          (fun a -> exp_to_constrExp (Elab.get_arg_exp a) params env)
          args
      in
      match Strmap.find_opt func_name env.paramvars with
      | Some i ->
          [CrSatCons (CrArg i, cons)]
      | None ->
          let reqs' = List.map (fun r -> replace_args_in_con r cons env) reqs in
          reqs' )
  (* in all other cases, I assume that no cnots occur within arguments  *)
  | EAp _ ->
      []
  | EFor (MVar (Ident istr), range, exp, sc, sc_ty) -> (
    match range with
    | ERng (l, r) ->
        let l' = exp_to_constrExp l params env in
        let r' = exp_to_constrExp r params env in
        let exivars' = Strmap.add istr TInt env.exivars in
        let env' = {env with exivars= exivars'} in
        let cons = generate_clone_reqs tvs params exp env' in
        List.map
          (fun c ->
            CrForall
              ( Ident istr
              , CrImp
                  ( CrAnd
                      ( CrGe (CrExi (Ident istr), l')
                      , CrLt (CrExi (Ident istr), r') )
                  , c ) ) )
          cons
        (* For the other cases, perhaps need to do substitutions *)
    | _ ->
        failwith "TODO: for now, ranges must be of form l .. r" )
  | ECmd (ty, CDiag (g1, g2, e1, e2)) ->
      let ce1 = exp_to_constrExp e1 params env in
      let ce2 = exp_to_constrExp e2 params env in
      [CrNeq (ce1, ce2)]
  | ECmd _ ->
      []
  | EIte (ty, b, e1, e2) ->
      let cs1 = generate_clone_reqs tvs params e1 env in
      let cs2 = generate_clone_reqs tvs params e2 env in
      cs1 @ cs2
  | _ ->
      []

(* TODO: add a type checker on the lqs level, or make the one in elab.ml more thoroug,
   i.e., actually check that all the types are what they should be *)
(* May also want a more formal data struct to hold individual function defs *)
let rec check_prog_for_clone (exp : exp) (env : env_t) =
  match exp with
  | ELet
      ( MVar (Ident v)
      , ELam (tvs, params, retexp, retty)
      , TFun (tvs', tys, retty', reqs, ens)
      , e2
      , t2 ) ->
      let cons = generate_clone_reqs tvs params retexp env in
      let _ =
        ShowLambdaQs.show (ShowLambdaQs.showList ShowLambdaQs.showConstr cons)
        |> print_endline
      in
      (* let _ = check_funcdec_for_clone reqs cons params env in *)
      let funcdefs' =
        Strmap.add v
          ( ELam (tvs, params, retexp, retty)
          , TFun (tvs', tys, retty', reqs, ens) )
          env.funcdefs
      in
      let env' = {env with funcdefs= funcdefs'} in
      check_prog_for_clone e2 env'
  | _ ->
      print_endline "done"

(* let def_env = {funcdefs= empty; bodyvars= empty; exivars= empty}

   let detcons_main () = check_prog_for_clone applyCNOTchain def_env ;;

   detcons_main () *)
