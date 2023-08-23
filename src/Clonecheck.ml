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
open SampleLQSProgs
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
      failwith "expected Z3_Int, got something else instead"

let mk_z3_exp_sub (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.mk_sub ctx [i1'; i2'])
  | _ ->
      failwith "expected Z3_Int, got something else instead"

let mk_z3_exp_mul (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.mk_mul ctx [i1'; i2'])
  | _ ->
      failwith "expected Z3_Int, got something else instead"

type env_t = {vars: typ Strmap.t; z3vars: z3_exp Strmap.t; ret_count: int}

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

(*
   (* TODO:  *)
   let set_qlists_equal (ql1 : z3_exp) (ql2 : z3_exp) (ctx : Z3.context)
       (solver : Solver.solver) =
     match (ql1, ql2) with
     | Z3_Qarr (a, alen), Z3_Qarr (b, blen) ->
         (* creating the integer sort *)
         (* let int_sort = Integer.mk_sort ctx in *)
         (* lengths are equal *)
         let eq_len = Boolean.mk_eq ctx alen blen in
         Solver.add solver [eq_len]
     | _ ->
         failwith "expected two qlists, got something else" *)

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
      let vars' = Strmap.add qlist_name (TAbsArr (TQAll k)) env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qarr :: ps, env'')
  | Param (MVar (Ident q_name), TQAll k) :: params' ->
      let z3_qubit = Z3_Qall (Integer.mk_const_s ctx q_name) in
      let z3vars' = Strmap.add q_name z3_qubit env.z3vars in
      let vars' = Strmap.add q_name (TQAll k) env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qubit :: ps, env'')
  | Param (MVar (Ident int_name), TInt) :: params' ->
      let z3_int = Z3_Int (Integer.mk_const_s ctx int_name) in
      let z3vars' = Strmap.add int_name z3_int env.z3vars in
      let vars' = Strmap.add int_name TInt env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_int :: ps, env'')
  | Param (MVar (Ident var_name), ty) :: params' ->
      let vars' = Strmap.add var_name ty env.vars in
      let env' = {env with vars= vars'} in
      add_params_to_ctx params' env' ctx solver
  | [] ->
      ([], env)

(***********************************)
(* Adding/checking the constraints *)
(***********************************)

let get_z3_qarr_exp (params : z3_exp list) (ret : z3_exp) (exp : exp) :
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

(* TODO: if this gets to complicated, use helpers and recursion to reduce cases *)
let rec get_z3_int_exp (params : z3_exp list) (ret : z3_exp) (exp : exp)
    (ctx : Z3.context) : Expr.expr =
  match exp with
  | EArg i -> (
    match List.nth params i with
    | Z3_Int i' ->
        i'
    | Z3_Qall i' ->
        i'
    | Z3_no_ret ->
        failwith "PE"
    | _ ->
        failwith ("expected Z3_Int, got something else: " ^ exp_to_string exp) )
  | EVar (MVar (Ident "RET")) -> (
    match ret with
    | Z3_Int i' ->
        i'
    | Z3_Qall i' ->
        i'
    | _ ->
        failwith ("expected Z3_Int, got something else: " ^ exp_to_string exp) )
  | EVar (MVar (Ident "i")) ->
      let int_sort = Integer.mk_sort ctx in
      Quantifier.mk_bound ctx 0 int_sort
  | EVar (MVar (Ident "j")) ->
      let int_sort = Integer.mk_sort ctx in
      Quantifier.mk_bound ctx 0 int_sort
  | EArrLen e ->
      get_z3_qarr_length_exp params ret e
  | EArrIdx (_, arr, i) ->
      let arr' = get_z3_qarr_exp params ret arr in
      let i' = get_z3_int_exp params ret i ctx in
      (* FIXME: technically, the following is a qkey. is this a problem? *)
      FuncDecl.apply arr' [i']
  | EAdd (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      Arithmetic.mk_add ctx [i1'; i2']
  | ESub (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      Arithmetic.mk_sub ctx [i1'; i2']
  | EMul (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      Arithmetic.mk_mul ctx [i1'; i2']
  | EMod (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      Arithmetic.Integer.mk_mod ctx i1' i2'
  | EInt i ->
      Integer.mk_numeral_i ctx i
  | _ ->
      failwith "TODO or error"

(********************************************************)
(* IMPORTANT: here is where we generate the constraints *)
(********************************************************)

let rec generate_constraint_exp (params : z3_exp list) (ret : z3_exp)
    (cons : constr) (ctx : Z3.context) : Expr.expr =
  match cons with
  | CBool (EAp (EVar (MVar (Ident "is_range")), _, [Arg (arr, _)])) ->
      let arr' = get_z3_qarr_exp params ret arr in
      let len' = get_z3_qarr_length_exp params ret arr in
      let range_con = array_is_range arr' len' ctx in
      range_con
  | CBool _ ->
      failwith "TODO: CBool"
  | CLt (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let lt = Arithmetic.mk_lt ctx i1' i2' in
      lt
      (* Solver.add solver [lt] *)
  | CLe (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let le = Arithmetic.mk_le ctx i1' i2' in
      le
      (* Solver.add solver [le] *)
  | CGt (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let gt = Arithmetic.mk_gt ctx i1' i2' in
      gt
      (* Solver.add solver [gt] *)
  | CGe (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let ge = Arithmetic.mk_ge ctx i1' i2' in
      ge
      (* Solver.add solver [ge] *)
  | CEq (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let eq = Boolean.mk_eq ctx i1' i2' in
      eq
      (* Solver.add solver [eq] *)
  | CNeq (i1, i2) ->
      let i1' = get_z3_int_exp params ret i1 ctx in
      let i2' = get_z3_int_exp params ret i2 ctx in
      let eq = Boolean.mk_eq ctx i1' i2' in
      let neq = Boolean.mk_not ctx eq in
      neq
      (* Solver.add solver [neq] *)
  | CAnd (c1, c2) ->
      let c1' = generate_constraint_exp params ret c1 ctx in
      let c2' = generate_constraint_exp params ret c2 ctx in
      let andd = Boolean.mk_and ctx [c1'; c2'] in
      andd
  | COr (c1, c2) ->
      failwith "TODO: COr"
  | CImp (c1, c2) ->
      let c1' = generate_constraint_exp params ret c1 ctx in
      let c2' = generate_constraint_exp params ret c2 ctx in
      let imp = Boolean.mk_implies ctx c1' c2' in
      imp
  | CForall (MVar (Ident var_name), c) ->
      (* for now, we just assume v is always a number, but this will be a huge problem later on... *)
      let forall_body = generate_constraint_exp params ret c ctx in
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
          ^ "\nThe above witness shows that a constraint in " ^ model_name
          ^ " may not be held"
        in
        (* uncomment out the next like for a better error message where \n works *)
        (* print_endline mes;  *)
        failwith mes
    | None ->
        print_endline
          "No model found although constraints may be satisfiable: this means \
           we don't know if a constraint holds." )
  | _ ->
      print_endline ("succesful " ^ model_name)

(**********************************)
(* interesting the asymmetry here *)
(**********************************)

(* *)
(* This first set is called during function definition *)
(* *)
let rec add_reqs_to_solver (func_name : string) (params : z3_exp list)
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

(*These constrs are inverted *)
let rec check_ens_are_ensured (func_name : string) (params : z3_exp list)
    (ret_z3 : z3_exp) (ens : constr list) (ctx : Z3.context)
    (solver : Solver.solver) =
  match ens with
  | CBool (EVar (MVar (Ident "SKIP_ENS"))) :: ens' ->
      print_endline ("skipping ensure check for " ^ func_name)
  | en :: ens' ->
      let model_name = "[define " ^ func_name ^ "]" in
      let _ = check_for_constr_witness model_name params ret_z3 en ctx solver in
      check_ens_are_ensured func_name params ret_z3 ens' ctx solver
  | [] ->
      ()

(***)
(* This second set is called during function application *)
(***)

(*These constrs are inverted *)
let rec check_reqs_are_satisfied (func_name : string) (args : z3_exp list)
    (reqs : constr list) (ctx : Z3.context) (solver : Solver.solver) =
  match reqs with
  | req :: reqs' ->
      let model_name = "[apply " ^ func_name ^ "]" in
      let _ =
        check_for_constr_witness model_name args Z3_no_ret req ctx solver
      in
      check_reqs_are_satisfied func_name args reqs' ctx solver
  | [] ->
      ()

let rec add_ens_to_solver (args : z3_exp list) (ret : z3_exp)
    (ens : constr list) (ctx : Z3.context) (solver : Solver.solver) =
  match ens with
  | CBool (EVar (MVar (Ident "SKIP_ENS"))) :: ens' ->
      add_ens_to_solver args ret ens' ctx solver
  | en :: ens' ->
      let con = generate_constraint_exp args ret en ctx in
      let _ = Solver.add solver [con] in
      add_ens_to_solver args ret ens' ctx solver
  | [] ->
      ()

(***********************)
(***********************)
(***********************)

(*
   let rec get_z3_term_of_exp (exp : exp) (env : env_t) (ctx : Z3.context) : z3_exp
       =
     match exp with
     | EVar (MVar (Ident var_name)) -> (
       match Strmap.find_opt var_name env.z3vars with
       | None ->
           failwith ("variable name not found: " ^ var_name)
       | Some t ->
           t )
     | EInt i ->
         Z3_Int (Integer.mk_numeral_i ctx i)
     | _ ->
         failwith "TODO: get_z3_term_of_exp" *)

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

(* TODO: add a type checker on the lqs level, or make the one in elab.ml more thoroug,
   i.e., actually check that all the types are what they should be *)
(* let type_check_exp (exp : AbsLambdaQs.exp) (env : env_t) =  *)
let rec check_prog_for_clone (exp : exp) (env : env_t) =
  match exp with
  | ELet
      ( MVar (Ident v)
      , ELam (tvs, params, retexp, retty)
      , TFun (tvs', tys, retty', reqs, ens)
      , e2
      , t2 ) ->
      let _ = print_endline ("checking definition for: " ^ v) in
      let _ = check_funcdec_for_clone v tvs params retexp reqs ens env in
      let _ = print_endline "Done with check\n\n" in
      let vars' = Strmap.add v (TFun (tvs', tys, retty', reqs, ens)) env.vars in
      let env' = {env with vars= vars'} in
      (* this is so that param names are not confused accross multiple functions,
         we append the function name to the param name*)
      (* let renamed_params =
           List.map
             (fun p ->
               match p with
               | TyVar (MVar (Ident n), e) ->
                   TyVar (MVar (Ident (v ^ n)), e) )
             params
         in *)
      check_prog_for_clone e2 env'
  | _ ->
      print_endline "The program is safe"

let def_env = {vars= empty; z3vars= empty; ret_count= 0}

let clonecheck_main () = check_prog_for_clone mostrest def_env ;;

clonecheck_main ()
