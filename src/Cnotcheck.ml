(* to compile: ocamlfind ocamlopt -thread -package z3 -linkpkg -o Clonecheck Clonecheck.ml *)

open AbsLambdaQs
open ShowLambdaQs
open AbsQSharp
open Printf
open Map
open String
open List
open Either
open Elab
open Z3
open Z3.Arithmetic
open Z3.Boolean
open Z3.Expr
open Z3.FuncDecl
open Z3.Quantifier
open Z3.Symbol
module Strmap = Map.Make (String)
open Strmap

(* this type is helpful because (for example) we want to make a single function that checks the body of a function, and the
   return type of a function may be an array or an int, requiring different representations *)
type z3_exp =
  | Z3_Int of Expr.expr
  | Z3_Qall of Expr.expr
  | Z3_Qarr of FuncDecl.func_decl * Expr.expr
  | Z3_no_ret

let mk_z3_exp_add (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.mk_add ctx [i1'; i2'])
  | _ ->
      failwith "expected (Z3_Int, Z3_Int), got something else instead"

let mk_z3_exp_sub (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.mk_sub ctx [i1'; i2'])
  | _ ->
      failwith "expected (Z3_Int, Z3_Int), got something else instead"

let mk_z3_exp_mul (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.mk_mul ctx [i1'; i2'])
  | _ ->
      failwith "expected (Z3_Int, Z3_Int), got something else instead"

let mk_z3_exp_idx (arr : z3_exp) (i : z3_exp) : z3_exp =
  match (arr, i) with
  | Z3_Qarr (arr', len), Z3_Int i' ->
    Z3_Qall (FuncDecl.apply arr' [i'])
  | _ ->
      failwith "expected (Z3Qarr, Z3_Int), got something else instead"

let mk_z3_exp_len (arr : z3_exp) : z3_exp =
  match arr with
  | Z3_Qarr (arr', len) ->
    Z3_Int len
  | _ ->
      failwith "expected Z3Qarr, got something else instead"
      
let get_z3_exp_int (e : z3_exp) : Expr.expr =
  match e with 
  | Z3_Int i -> i
  | Z3_Qall i -> i 
  | _ -> failwith "expected some form of int exp, got something else instead"



type env_t = {funcdefs: (exp * typ) Strmap.t ; z3vars: z3_exp Strmap.t; ret_count: int}



let get_func_retty (func_name : string) (env : env_t) : typ = 
  match Strmap.find_opt func_name env.funcdefs with
  | Some ( ELam (tvs, params, retexp, retty)
  , TFun (tvs', tys, retty', reqs, ens) ) -> retty' 
  | Some _ -> failwith "expected function type, got something else"
  | None -> failwith "function name not found in environment"


let get_func_reqs (func_name : string) (env : env_t) : constr list = 
  match Strmap.find_opt func_name env.funcdefs with
  | Some ( ELam (tvs, params, retexp, retty)
  , TFun (tvs', tys, retty', reqs, ens) ) -> reqs 
  | Some _ -> failwith "expected function type, got something else"
  | None -> failwith "function name not found in environment"


  let get_func_ens (func_name : string) (env : env_t) : constr list = 
    match Strmap.find_opt func_name env.funcdefs with
    | Some ( ELam (tvs, params, retexp, retty)
    , TFun (tvs', tys, retty', reqs, ens) ) -> ens 
    | Some _ -> failwith "expected function type, got something else"
    | None -> failwith "function name not found in environment"


(* NB!!!!!! Nowhere do we ever check that the ensures statements actually are true based on what
   happens inside the function, that is not really the point of this project. We assume that annotations
   are always faithful to the function defs *)

let create_z3_array (arr_name : string) (ctx : Z3.context)
    (solver : Solver.solver) : z3_exp =
  (* making the constant 0 *)
  let zero = Integer.mk_numeral_i ctx 0 in
  (* creating the integer sort *)
  let int_sort = Integer.mk_sort ctx in
  (* Declare the array a and its length n, which is now implicitly associated to length *)
  let arr = FuncDecl.mk_func_decl_s ctx arr_name [int_sort] int_sort in
  let arrlen = Integer.mk_const_s ctx (arr_name ^ "len") in
  (* length is greater than 0 *)
  let ge = Arithmetic.mk_ge ctx arrlen zero in
  let _ = Solver.add solver [ge] in
  (* Creating the bound variable "i" *)
  let ilow = Quantifier.mk_bound ctx 0 int_sort in
  (* Creating the implication body "if i < 0 then a[i] = 0" *)
  let bodylow =
    Boolean.mk_implies ctx
      (Arithmetic.mk_lt ctx ilow zero)
      (Boolean.mk_eq ctx (FuncDecl.apply arr [ilow]) zero)
  in
  (* Creating the universal quantifier "for all i, if i < 0 then a[i] = 0" *)
  let forall_expr1 =
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall ctx
         [int_sort] (* Empty sort list *)
         [Symbol.mk_string ctx "i"] (* Bound variables *)
         bodylow (* Quantifier body *)
         None (* Weight: none *)
         [] (* Patterns: empty list *)
         [] (* No multi-patterns *)
         None (* No quantifier id *)
         None (* No skolem id *) )
  in
  (* Creating the bound variable "i" *)
  let iupp = Quantifier.mk_bound ctx 0 int_sort in
  (* Creating the implication body "if i < 0 then a[i] = 0" *)
  let bodyupp =
    Boolean.mk_implies ctx
      (Arithmetic.mk_ge ctx iupp arrlen)
      (Boolean.mk_eq ctx (FuncDecl.apply arr [iupp]) zero)
  in
  (* Creating the universal quantifier "for all i, if i >= alen then a[i] = 0" *)
  let forall_expr2 =
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall ctx
         [int_sort] (* Empty sort list *)
         [Symbol.mk_string ctx "i"] (* Bound variables *)
         bodyupp (* Quantifier body *)
         None (* Weight: none *)
         [] (* Patterns: empty list *)
         [] (* No multi-patterns *)
         None (* No quantifier id *)
         None (* No skolem id *) )
  in
  let _ = Solver.add solver [forall_expr1; forall_expr2] in
  Z3_Qarr (arr, arrlen)

let array_is_range (arr : FuncDecl.func_decl) (arrlen : Expr.expr)
    (ctx : Z3.context) : Expr.expr =
  (* making the constant 0 *)
  let zero = Integer.mk_numeral_i ctx 0 in
  (* creating the integer sort *)
  let int_sort = Integer.mk_sort ctx in
  (* getting the string name for arr *)
  let arr_name = Symbol.to_string (FuncDecl.get_name arr) in
  (* creating the base integer *)
  let base_val = Integer.mk_const_s ctx (arr_name ^ "base") in
  (* Creating the bound variable "i" *)
  let i = Quantifier.mk_bound ctx 0 int_sort in
  let i_ge_zero = Arithmetic.mk_ge ctx i zero in
  let i_lt_alen = Arithmetic.mk_lt ctx i arrlen in
  let i_in_range = Boolean.mk_and ctx [i_ge_zero; i_lt_alen] in
  let body =
    Boolean.mk_implies ctx i_in_range
      (Boolean.mk_eq ctx (FuncDecl.apply arr [i])
         (Arithmetic.mk_add ctx [base_val; i]) )
  in
  let forall_expr =
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall ctx
         [int_sort] (* Empty sort list *)
         [Symbol.mk_string ctx "i"] (* Bound variables *)
         body (* Quantifier body *)
         None (* Weight: none *)
         [] (* Patterns: empty list *)
         [] (* No multi-patterns *)
         None (* No quantifier id *)
         None (* No skolem id *) )
  in
  forall_expr


(* *)
(* *)
(* *)
(* *)
(* *)
(* *)
(* The start of the z3 translation *)

let rec add_params_to_ctx (params : param list) (env : env_t) (ctx : Z3.context)
    (solver : Solver.solver) : z3_exp list * env_t =
  match params with
  | Param (MVar (Ident qlist_name), TAbsArr (TQAll k)) :: params' ->
      let z3_qarr = create_z3_array qlist_name ctx solver in
      let z3vars' = Strmap.add qlist_name z3_qarr env.z3vars in
      let env' = {env with z3vars= z3vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qarr :: ps, env'')
  | Param (MVar (Ident q_name), TQAll k) :: params' ->
      let z3_qubit = Z3_Qall (Integer.mk_const_s ctx q_name) in
      let z3vars' = Strmap.add q_name z3_qubit env.z3vars in
      let env' = {env with z3vars= z3vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qubit :: ps, env'')
  | Param (MVar (Ident int_name), TInt) :: params' ->
      let z3_int = Z3_Int (Integer.mk_const_s ctx int_name) in
      let z3vars' = Strmap.add int_name z3_int env.z3vars in
      let env' = {env with z3vars= z3vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_int :: ps, env'')
  | Param (MVar (Ident var_name), ty) :: params' ->
      add_params_to_ctx params' env ctx solver
  | [] ->
      ([], env)

(***********************************)
(* Adding/checking the constraints *)
(***********************************)

(* let get_z3_qarr_exp (params : z3_exp list) (ret : z3_exp) (exp : constrExp) :
    FuncDecl.func_decl =
  match exp with
  | EArg i -> (
    match List.nth params i with
    | Z3_Qarr (arr, len) ->
        arr
    | _ ->
        failwith "expected Z3_Qarr, got something else" )
  | EVar (MVar (Ident "RET")) -> (
    match ret with
    | Z3_Qarr (arr, len) ->
        arr
    | _ ->
        failwith "expected Z3_Qarr, got something else" )
  | _ ->
      failwith "TODO or error"

let get_z3_qarr_length_exp (params : z3_exp list) (ret : z3_exp) (exp : exp) :
    Expr.expr =
  match exp with
  | EArg i -> (
    match List.nth params i with
    | Z3_Qarr (arr, len) ->
        len
    | _ ->
        failwith "expected Z3_Qarr, got something else" )
  | EVar (MVar (Ident "RET")) -> (
    match ret with
    | Z3_Qarr (arr, len) ->
        len
    | _ ->
        failwith "expected Z3_Qarr, got something else" )
  | _ ->
      failwith "TODO or error"
      *)


  
(********************************************************)
(* IMPORTANT: here is where we generate the constraints *)
(********************************************************)

let rec generate_constraint_exp (params : z3_exp list) (ret : z3_exp)
    (cons : constr) (env : env_t) (ctx : Z3.context) (solver : Solver.solver) : Expr.expr =
  match cons with
  | CrIsRange arr -> (
    match constrExp_to_z3_exp params ret arr env ctx solver with 
    | Z3_Qarr (arr', len'), env' ->
      let range_con = array_is_range arr' len' ctx in
      range_con
    | _ -> failwith "expected Z3_Qarr, got something else instead")
  | CrLt (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let lt = Arithmetic.mk_lt ctx i1' i2' in
    lt
  | CrLe (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let le = Arithmetic.mk_le ctx i1' i2' in
    le
  | CrGt (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let gt = Arithmetic.mk_gt ctx i1' i2' in
    gt
  | CrGe (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let ge = Arithmetic.mk_ge ctx i1' i2' in
    ge
  | CrEq (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let eq = Boolean.mk_eq ctx i1' i2' in
    eq
  | CrNeq (i1, i2) -> 
    let i1' = constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int in 
    let i2' = constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int in 
    let eq = Boolean.mk_eq ctx i1' i2' in
    let neq = Boolean.mk_not ctx eq in
    neq
  | CrAnd (c1, c2) -> 
    let c1' = generate_constraint_exp params ret c1 env ctx solver in
    let c2' = generate_constraint_exp params ret c2 env ctx solver in
    let andd = Boolean.mk_and ctx [c1'; c2'] in
    andd
  | CrOr (c1, c2) -> failwith "TODO: COr"
  | CrImp (c1, c2) -> 
    let c1' = generate_constraint_exp params ret c1 env ctx solver in
    let c2' = generate_constraint_exp params ret c2 env ctx solver in
    let imp = Boolean.mk_implies ctx c1' c2' in
    imp
  | CrForall (Ident var_name, c) -> 
      (* for now, we just assume v is always a number, but this will be a huge problem later on... *)
      let forall_body = generate_constraint_exp params ret c env ctx solver in
      let int_sort = Integer.mk_sort ctx in
      let forall_expr =
        Quantifier.expr_of_quantifier
          (Quantifier.mk_forall ctx
             [int_sort] (* Empty sort list *)
             [Symbol.mk_string ctx var_name] (* Bound variables *)
             forall_body (* Quantifier body *)
             None (* Weight: none *)
             [] (* Patterns: empty list *)
             [] (* No multi-patterns *)
             None (* No quantifier id *)
             None (* No skolem id *) )
      in
      forall_expr


and constrExp_to_z3_exp (params : z3_exp list) (ret : z3_exp) (exp : constrExp) (env : env_t) 
  (ctx : Z3.context) (solver : Solver.solver) : z3_exp * env_t =
  match exp with
  | CrApp (MVar (Ident fname), args) ->
    (* could just generate the numbers outside the function to avoid all this *)
    let rec fold_args argus envi = 
      (match argus with 
      | a :: argus' ->
        let a', envi' = constrExp_to_z3_exp params ret a envi ctx solver in 
        let argus'', envi'' = fold_args argus' envi' in 
        (a' :: argus'', envi'')
      | [] -> ([], envi))
    in 
    let args_z3, env' = fold_args args env in 
    let ret_string = "ret_" ^ string_of_int env'.ret_count in
    let ret_count' = env'.ret_count + 1 in
    let env'' = {env' with ret_count= ret_count'} in
    let retty = get_func_retty fname env'' in
    let ens = get_func_ens fname env'' in
    let ret_z3 =
      match retty with
      | TInt ->
          Z3_Int (Integer.mk_const_s ctx ret_string)
      | TAbsArr (TQAll _) ->
          create_z3_array ret_string ctx solver
      | TQAll _ ->
          Z3_Qall (Integer.mk_const_s ctx ret_string)
      | TUnit ->
          Z3_no_ret
      | _ ->
          failwith "TODO: must add z3_exp based on return type"
    in
    let _ = add_ens_to_solver args_z3 ret_z3 ens ctx solver in
    (ret_z3, env'')
  | CrArg i -> (List.nth params i, env)
  | CrRet -> (ret, env)
  | CrExi (Ident i) -> 
    let int_sort = Integer.mk_sort ctx in
    let exivar = Quantifier.mk_bound ctx 0 int_sort in 
    (Z3_Int exivar, env)
  | CrInt i -> 
    let i = Integer.mk_numeral_i ctx i in 
    (Z3_Int i, env)
  | CrAdd (i1, i2) -> 
    let i1', env' = constrExp_to_z3_exp params ret i1 env ctx solver in 
    let i2', env'' = constrExp_to_z3_exp params ret i2 env' ctx solver in 
    (mk_z3_exp_add ctx i1' i2', env'')
  | CrSub (i1, i2) ->
    let i1', env' = constrExp_to_z3_exp params ret i1 env ctx solver in 
    let i2', env'' = constrExp_to_z3_exp params ret i2 env' ctx solver in 
    (mk_z3_exp_sub ctx i1' i2', env'')
  | CrIdx (arr, i) ->
    let arr', env' = constrExp_to_z3_exp params ret arr env ctx solver in 
    let i', env'' = constrExp_to_z3_exp params ret i env' ctx solver in 
    (mk_z3_exp_idx arr' i', env'')
  | CrLen arr ->
    let arr', env' = constrExp_to_z3_exp params ret arr env ctx solver in 
    (mk_z3_exp_len arr', env')


and add_reqs_to_solver (func_name : string) (params : z3_exp list)
    (reqs : constr list) (ctx : Z3.context) (solver : Solver.solver) =
  match reqs with
  | req :: reqs' ->
      let con = generate_constraint_exp params Z3_no_ret req ctx in
      let _ = Solver.add solver [con] in
      add_reqs_to_solver func_name params reqs' ctx solver
  | [] -> (
      let model_name = "[define " ^ func_name ^ "]" in
      match Solver.check solver [] with
      | Solver.SATISFIABLE -> (
        (* Print model if satisfiable *)
        match Solver.get_model solver with
        | Some m ->
            ()
        | None ->
            print_endline ("Possibility for no valid arguments in " ^ model_name)
        )
      | _ ->
          failwith ("No valid arguments in " ^ model_name) )


and add_ens_to_solver (args : z3_exp list) (ret : z3_exp)
    (ens : constr list) (ctx : Z3.context) (solver : Solver.solver) =
  match ens with
  | en :: ens' ->
      let con = generate_constraint_exp args ret en ctx in
      let _ = Solver.add solver [con] in
      add_ens_to_solver args ret ens' ctx solver
  | [] ->
      ()



(* This function checks to see if there is a counter example witness for a constraint *)
let check_for_constr_witness (model_name : string) (params : z3_exp list)
    (ret : z3_exp) (cons : constr) (ctx : Z3.context) (solver : Solver.solver) =
  let cons' = generate_constraint_exp params ret cons ctx in
  let neggate_cons = Boolean.mk_not ctx cons' in
  (* let _ = Solver.add solver [neggate_cons] in *)
  (* Check satisfiability *)
  ( match Solver.check solver [] with
  | Solver.SATISFIABLE ->
      ()
  | _ ->
      print_endline "NOT SAT BEFORE CONSTRAINT, SOMETHING WENT WRONG." ) ;
  match Solver.check solver [neggate_cons] with
  | Solver.SATISFIABLE -> (
    (* Print model if satisfiable *)
    match Solver.get_model solver with
    | Some m ->
        (* TO print the solver:  *)
        let mes =
          "SAT:\n" ^ Model.to_string m
          ^ "\nThe above witness shows that the following constraint in " ^ model_name
          ^ " may not be held:\n" 
          ^ constr_to_string cons
        in
        (* uncomment out the next like for a better error message where \n works *)
        print_endline mes; 
        failwith "see above"
    | None ->
        print_endline
          "No model found although constraints may be satisfiable: this means \
           we don't know if a constraint holds." )
  | _ ->
      print_endline ("succesful " ^ model_name)


(***********************)
(***********************)
(***********************)


(* FIXME: seems odd that there is this and also the get_z3_int_exp, etc... functions
   above. Why are there both? I guess the ones above are meant to be used only for
   constraints? But this could be bad repeated code in the end. *)
(* I guess the reason is that we are a bit more limited in the variables that are
   referenced in the constaints; many different things can happen in a body. Can
   still probably combine the two functions, though *)
let rec check_body_applications (body : exp) (env : env_t) (ctx : Z3.context)
    (solver : Solver.solver) : z3_exp * env_t =
  match body with
  | EVar (MVar (Ident var_name)) -> (
    match Strmap.find_opt var_name env.z3vars with
    | None ->
        failwith ("variable name not found: " ^ var_name)
    | Some t ->
        (t, env) )
  | ELet (MVar (Ident vname), vexp, vty, bexp, bty) ->
      let vexp_z3, env' = check_body_applications vexp env ctx solver in
      let z3vars' = Strmap.add vname vexp_z3 env'.z3vars in
      let vars' = Strmap.add vname vty env'.vars in
      let env'' = {env' with z3vars= z3vars'; vars= vars'} in
      check_body_applications bexp env'' ctx solver
  | EAp (f, TFun (tvs, paramtys, retty, reqs, ens), args) ->
      let args_z3 =
        List.map
          (fun arg ->
            match arg with
            | Arg (e, t) -> (
              match check_body_applications e env ctx solver with
              | e_z3, env' ->
                  e_z3 ) )
          args
      in
      (* this is just useful for error printint *)
      let func_name =
        match f with
        | EVar (MVar (Ident f_name)) ->
            f_name
        | ELam _ ->
            "lambda_function"
        | _ ->
            failwith "expected either variable or lambda function"
      in
      let _ = check_reqs_are_satisfied func_name args_z3 reqs ctx solver in
      let ret_string = "ret_" ^ string_of_int env.ret_count in
      let ret_count' = env.ret_count + 1 in
      let env' = {env with ret_count= ret_count'} in
      let ret_z3 =
        match retty with
        | TInt ->
            Z3_Int (Integer.mk_const_s ctx ret_string)
        | TAbsArr (TQAll _) ->
            create_z3_array ret_string ctx solver
        | TQAll _ ->
            Z3_Qall (Integer.mk_const_s ctx ret_string)
        | TUnit ->
            Z3_no_ret
        | _ ->
            failwith "TODO: must add z3_exp based on return type"
      in
      let _ = add_ens_to_solver args_z3 ret_z3 ens ctx solver in
      (ret_z3, env')
  | EAp (f, fty, args) ->
      failwith "trying to apply function, but instead got different type"
      (* FIXME: get this better error message to work *)
      (* ("trying to apply function, but instead got type: " ^ ShowLambdaQs.show (ShowLambdaQs.showTyp fty)) *)
  | ECmd _ ->
      (Z3_no_ret, env)
  | EArrIdx (ty, arr, ind) -> (
    match check_body_applications ind env ctx solver with
    | Z3_Int i, env' -> (
      match check_body_applications arr env' ctx solver with
      | Z3_Qarr (arr', len), env'' ->
          let ind_in_bound =
            Boolean.mk_and ctx
              [ Arithmetic.mk_ge ctx i (Integer.mk_numeral_i ctx 0)
              ; Arithmetic.mk_lt ctx i len ]
          in
          let not_bounds = Boolean.mk_not ctx ind_in_bound in
          let arr_name = Symbol.to_string (FuncDecl.get_name arr') in
          ( match Solver.check solver [not_bounds] with
          | Solver.SATISFIABLE -> (
            (* Print model if satisfiable *)
            match Solver.get_model solver with
            | Some m ->
                (* TO print the solver:  *)
                print_endline
                  ( "Potential out of bounds error while indexing into array "
                  ^ arr_name )
            | None ->
                print_endline
                  "No model found although constraints may be satisfiable: \
                   this means we don't know if a constraint holds." )
          | _ ->
              print_endline ("succesful index into " ^ arr_name) ) ;
          (Z3_Qall (FuncDecl.apply arr' [i]), env'')
      | _ ->
          failwith "expected Z3_Qarr in EArrIdx, got something else"
          (* TODO: could get some ensures statements to pass by doing more here *)
      )
    | _ ->
        (Z3_no_ret, env) )
  | EArrLen arr -> (
    match check_body_applications arr env ctx solver with
    | Z3_Qarr (arr', len), env' ->
        (Z3_Int len, env')
    | _ ->
        failwith "Expected Z3_Qarr, got something else instead" )
  | EIte (ty, b, e1, e2) ->
      (* TODO: find a way to check both branches *)
      let _ = check_body_applications e1 env ctx solver in
      check_body_applications e2 env ctx solver
  | EWld ->
      (Z3_no_ret, env)
  | ETriv ->
      (Z3_no_ret, env)
  (* these that follow are weird because instead of making a return exp, we just return the actual z3
     exp. So i think this actually helps us check the ensures statements, even though this is not the
     point of the project. When EAp, the application could be simple, but we always make a new
     z3 expression, wasting space i think. But since we know exactly what the function is here, we can
     avoid this. *)
  | EPow _ ->
      failwith "TODO: check_body_applications: EPow"
  | EMul (i1, i2) -> (
    match check_body_applications i1 env ctx solver with
    | i1', env' -> (
      match check_body_applications i2 env' ctx solver with
      | i2', env'' ->
          (mk_z3_exp_mul ctx i1' i2', env'') ) )
  | EDiv _ ->
      failwith "TODO: check_body_applications: EDiv"
  | EMod _ ->
      failwith "TODO: check_body_applications: EMod"
  | EAdd (i1, i2) -> (
    match check_body_applications i1 env ctx solver with
    | i1', env' -> (
      match check_body_applications i2 env' ctx solver with
      | i2', env'' ->
          (mk_z3_exp_add ctx i1' i2', env'') ) )
  | ESub (i1, i2) -> (
    match check_body_applications i1 env ctx solver with
    | i1', env' -> (
      match check_body_applications i2 env' ctx solver with
      | i2', env'' ->
          (mk_z3_exp_sub ctx i1' i2', env'') ) )
  | EGt _ ->
      failwith "TODO: check_body_applications: EGt"
  | EGte _ ->
      failwith "TODO: check_body_applications: EGte"
  | ELt _ ->
      failwith "TODO: check_body_applications: ELt"
  | ELte _ ->
      failwith "TODO: check_body_applications: ELte"
  | EEql _ ->
      failwith "TODO: check_body_applications: EEql"
  | ENEql _ ->
      failwith "TODO: check_body_applications: ENeql"
  | ERng (l, u) ->
      (Z3_no_ret, env)
  | ERngR u ->
      (Z3_no_ret, env)
  | ERngL l ->
      (Z3_no_ret, env)
  | EInt i ->
      (Z3_Int (Integer.mk_numeral_i ctx i), env)
  | EDbl _ ->
      failwith "TODO: check_body_applications: EDbl"
  | EStr _ ->
      failwith "TODO: check_body_applications: EStr"
  | _ ->
      failwith "TODO: check_body_applications"
(* | _ ->
    failwith ("TODO: check_body_applications" ^ ShowLambdaQs.show (ShowLambdaQs.showExp body)) *)

let check_funcdec_for_clone (func_name : string) (tvs : tVar list)
    (params : param list) (body : exp) (reqs : constr list) (ens : constr list)
    (env : env_t) =
  (* configuration for the context *)
  let cfg = [("model", "true"); ("proof", "false")] in
  (* creating the context *)
  let ctx = Z3.mk_context cfg in
  (* creating a solver *)
  let solver = Solver.mk_solver ctx None in
  (*
     (* making the constants 0 and 1 *)
     let zero = Integer.mk_numeral_i ctx 0 in
     let one = Integer.mk_numeral_i ctx 1 in
     (* creating the integer sort *)
     let int_sort = Integer.mk_sort ctx in
  *)
  (* print_endline (print_exp body); *)
  let z3_params, env' = add_params_to_ctx params env ctx solver in
  let _ = add_reqs_to_solver func_name z3_params reqs ctx solver in
  let body_z3_exp, env'' = check_body_applications body env' ctx solver in
  check_ens_are_ensured func_name z3_params body_z3_exp ens ctx solver

(* let assertions = Solver.get_assertions solver in
   List.iter (fun ast -> print_endline (Expr.to_string ast)) assertions *)

   let rec check_prog_for_clone (exp : exp) (env : env_t) =
    match exp with
    | ELet
        ( MVar (Ident v)
        , ELam (tvs, params, retexp, retty)
        , TFun (tvs', tys, retty', reqs, ens)
        , e2
        , t2 ) ->
        let cons = generate_cnot_reqs tvs params retexp env in
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

let def_env = {vars= empty; z3vars= empty; ret_count= 0}

let clonecheck_main () = check_prog_for_clone mostrest def_env ;;

clonecheck_main ()
