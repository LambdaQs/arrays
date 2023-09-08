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
open Detcons
open Arrays
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

let mk_z3_exp_mod (ctx : Z3.context) (i1 : z3_exp) (i2 : z3_exp) : z3_exp =
  match (i1, i2) with
  | Z3_Int i1', Z3_Int i2' ->
      Z3_Int (Arithmetic.Integer.mk_mod ctx i1' i2')
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
  | Z3_Int i ->
      i
  | Z3_Qall i ->
      i
  | _ ->
      failwith "expected some form of int exp, got something else instead"

let ret_count = ref 0

let get_func_retty (func_name : string) (env : env_t) : typ =
  match Strmap.find_opt func_name env.funcdefs with
  | Some (ELam (tvs, params, retexp, retty), TFun (tvs', tys, retty', reqs, ens))
    ->
      retty'
  | Some _ ->
      failwith "expected function type, got something else"
  | None ->
      failwith "function name not found in environment"

let get_func_reqs (func_name : string) (env : env_t) : constr list =
  match Strmap.find_opt func_name env.funcdefs with
  | Some (ELam (tvs, params, retexp, retty), TFun (tvs', tys, retty', reqs, ens))
    ->
      reqs
  | Some _ ->
      failwith "expected function type, got something else"
  | None ->
      failwith "function name not found in environment"

let get_func_ens (func_name : string) (env : env_t) : constr list =
  match Strmap.find_opt func_name env.funcdefs with
  | Some (ELam (tvs, params, retexp, retty), TFun (tvs', tys, retty', reqs, ens))
    ->
      ens
  | Some _ ->
      failwith "expected function type, got something else"
  | None ->
      failwith "function name not found in environment"

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

(* could just make this a function param -> z3_exp and then just zip *)
let rec add_params_to_ctx (params : param list) (env : env_t) (ctx : Z3.context)
    (solver : Solver.solver) : z3_exp list * env_t =
  match params with
  | Param (MVar (Ident qlist_name), TAbsArr (TQAll k)) :: params' ->
      let z3_qarr = create_z3_array qlist_name ctx solver in
      let i = cardinal env.paramvars in
      let paramvars' = Strmap.add qlist_name i env.paramvars in
      let env' = {env with paramvars= paramvars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qarr :: ps, env'')
  | Param (MVar (Ident q_name), TQAll k) :: params' ->
      let z3_qubit = Z3_Qall (Integer.mk_const_s ctx q_name) in
      let i = cardinal env.paramvars in
      let paramvars' = Strmap.add q_name i env.paramvars in
      let env' = {env with paramvars= paramvars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_qubit :: ps, env'')
  | Param (MVar (Ident int_name), TInt) :: params' ->
      let z3_int = Z3_Int (Integer.mk_const_s ctx int_name) in
      let i = cardinal env.paramvars in
      let paramvars' = Strmap.add int_name i env.paramvars in
      let env' = {env with paramvars= paramvars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (z3_int :: ps, env'')
  | Param (MVar (Ident var_name), ty) :: params' ->
      let i = cardinal env.paramvars in
      let paramvars' = Strmap.add var_name i env.paramvars in
      let env' = {env with paramvars= paramvars'} in
      let ps, env'' = add_params_to_ctx params' env' ctx solver in
      (Z3_no_ret :: ps, env'')
  | [] ->
      ([], env)

(***********************************)
(* Adding/checking the constraints *)
(***********************************)

let rec generate_constraint_exp (params : z3_exp list) (ret : z3_exp)
    (cons : constr) (env : env_t) (ctx : Z3.context) (solver : Solver.solver) :
    Expr.expr =
  match cons with
  | CrIsRange arr -> (
    match constrExp_to_z3_exp params ret arr env ctx solver with
    | Z3_Qarr (arr', len') ->
        let range_con = array_is_range arr' len' ctx in
        range_con
    | _ ->
        failwith "expected Z3_Qarr, got something else instead" )
  | CrLt (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let lt = Arithmetic.mk_lt ctx i1' i2' in
      lt
  | CrLe (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let le = Arithmetic.mk_le ctx i1' i2' in
      le
  | CrGt (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let gt = Arithmetic.mk_gt ctx i1' i2' in
      gt
  | CrGe (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let ge = Arithmetic.mk_ge ctx i1' i2' in
      ge
  | CrEq (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let eq = Boolean.mk_eq ctx i1' i2' in
      eq
  | CrNeq (i1, i2) ->
      let i1' =
        constrExp_to_z3_exp params ret i1 env ctx solver |> get_z3_exp_int
      in
      let i2' =
        constrExp_to_z3_exp params ret i2 env ctx solver |> get_z3_exp_int
      in
      let eq = Boolean.mk_eq ctx i1' i2' in
      let neq = Boolean.mk_not ctx eq in
      neq
  | CrAnd (c1, c2) ->
      let c1' = generate_constraint_exp params ret c1 env ctx solver in
      let c2' = generate_constraint_exp params ret c2 env ctx solver in
      let andd = Boolean.mk_and ctx [c1'; c2'] in
      andd
  | CrOr (c1, c2) ->
      failwith "TODO: COr"
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
  | CrSatCons (CrArg i, args) ->
      print_endline "Warning: Applying abstract operation." ;
      mk_true ctx
  | CrSatCons (_, args) ->
      failwith "CrSatCons: impossible case"

and constrExp_to_z3_exp (params : z3_exp list) (ret : z3_exp) (exp : constrExp)
    (env : env_t) (ctx : Z3.context) (solver : Solver.solver) : z3_exp =
  match exp with
  | CrApp (MVar (Ident fname), args) ->
      (* could just generate the numbers outside the function to avoid all this *)
      let args_z3 =
        List.map (fun a -> constrExp_to_z3_exp params ret a env ctx solver) args
      in
      let ret_string = "ret_" ^ string_of_int !ret_count in
      let _ = incr ret_count in
      let retty = get_func_retty fname env in
      let ens = get_func_ens fname env in
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
      let _ = add_ens_to_solver args_z3 ret_z3 ens env ctx solver in
      ret_z3
  | CrArg i ->
      List.nth params i
  | CrRet ->
      ret
  | CrExi (Ident i) ->
      let int_sort = Integer.mk_sort ctx in
      (* FIXME: eventually, this will need to count the number of the exivar *)
      let exivar = Quantifier.mk_bound ctx 0 int_sort in
      Z3_Int exivar
  | CrFun _ ->
      failwith "impossible case: crfun should not appear in a clone constraint"
  | CrInt i ->
      let i = Integer.mk_numeral_i ctx i in
      Z3_Int i
  | CrAdd (i1, i2) ->
      let i1' = constrExp_to_z3_exp params ret i1 env ctx solver in
      let i2' = constrExp_to_z3_exp params ret i2 env ctx solver in
      mk_z3_exp_add ctx i1' i2'
  | CrSub (i1, i2) ->
      let i1' = constrExp_to_z3_exp params ret i1 env ctx solver in
      let i2' = constrExp_to_z3_exp params ret i2 env ctx solver in
      mk_z3_exp_sub ctx i1' i2'
  | CrMul (i1, i2) ->
      let i1' = constrExp_to_z3_exp params ret i1 env ctx solver in
      let i2' = constrExp_to_z3_exp params ret i2 env ctx solver in
      mk_z3_exp_mul ctx i1' i2'
  | CrMod (i1, i2) ->
      let i1' = constrExp_to_z3_exp params ret i1 env ctx solver in
      let i2' = constrExp_to_z3_exp params ret i2 env ctx solver in
      mk_z3_exp_mod ctx i1' i2'
  | CrIdx (arr, i) ->
      let arr' = constrExp_to_z3_exp params ret arr env ctx solver in
      let i' = constrExp_to_z3_exp params ret i env ctx solver in
      mk_z3_exp_idx arr' i'
  | CrLen arr ->
      let arr' = constrExp_to_z3_exp params ret arr env ctx solver in
      mk_z3_exp_len arr'

and add_reqs_to_solver (func_name : string) (params : z3_exp list)
    (reqs : constr list) (env : env_t) (ctx : Z3.context)
    (solver : Solver.solver) =
  match reqs with
  | req :: reqs' ->
      let con = generate_constraint_exp params Z3_no_ret req env ctx solver in
      let _ = Solver.add solver [con] in
      add_reqs_to_solver func_name params reqs' env ctx solver
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

and add_ens_to_solver (args : z3_exp list) (ret : z3_exp) (ens : constr list)
    (env : env_t) (ctx : Z3.context) (solver : Solver.solver) =
  match ens with
  | en :: ens' ->
      let con = generate_constraint_exp args ret en env ctx solver in
      let _ = Solver.add solver [con] in
      add_ens_to_solver args ret ens' env ctx solver
  | [] ->
      ()

(* This function checks to see if there is a counter example witness for a constraint *)
let check_for_constr_witness (model_name : string) (params : z3_exp list)
    (cons : constr) (env : env_t) (ctx : Z3.context) (solver : Solver.solver) =
  let cons' = generate_constraint_exp params Z3_no_ret cons env ctx solver in
  let neggate_cons = Boolean.mk_not ctx cons' in
  (* let _ = Solver.add solver [neggate_cons] in *)
  (* Check satisfiability *)
  ( match Solver.check solver [] with
  | Solver.SATISFIABLE ->
      ()
  | _ ->
      print_endline "NOT SAT BEFORE CONSTRAINT, SOMETHING WENT WRONG." ) ;
  (* let assertions = Solver.get_assertions solver in
     List.iter (fun ast -> print_endline (Expr.to_string ast)) assertions ;
     print_endline (Expr.to_string neggate_cons) ; *)
  match Solver.check solver [neggate_cons] with
  | Solver.SATISFIABLE -> (
    (* Print model if satisfiable *)
    match Solver.get_model solver with
    | Some m ->
        (* TO print the solver:  *)
        let mes =
          "SAT:\n" ^ Model.to_string m
          ^ "\nThe above witness shows that the following constraint in "
          ^ model_name ^ " may not be held:\n" ^ constr_to_string cons
        in
        (* uncomment out the next like for a better error message where \n works *)
        print_endline mes ; failwith "see above"
    | None ->
        print_endline
          "No model found although constraints may be satisfiable: this means \
           we don't know if a constraint holds." )
  | _ ->
      print_endline ("succesful " ^ model_name)

(***********************)
(***********************)
(***********************)

let rec check_cnot_applications (func_name : string) (params : z3_exp list)
    (cnot_cons : constr list) (env : env_t) (ctx : Z3.context)
    (solver : Solver.solver) : unit =
  match cnot_cons with
  | c :: cnot_cons' ->
      let model_name = "[cnot_ap " ^ func_name ^ "]" in
      check_for_constr_witness model_name params c env ctx solver ;
      check_cnot_applications func_name params cnot_cons' env ctx solver
  | [] ->
      ()

(* FIXME: FIXME: do this in a better way, perhaps make replace_args_in_con more general in Detcons.ml *)
let rec remove_bad (reqs : constr list) : constr list =
  match reqs with
  | CrIsRange _ :: reqs' ->
      remove_bad reqs'
  | r :: reqs' ->
      r :: remove_bad reqs'
  | [] ->
      []

let rec check_prog_for_clone (exp : exp) (env : env_t) =
  match exp with
  | ELet
      ( MVar (Ident func_name)
      , ELam (tvs, params, retexp, retty)
      , TFun (tvs', tys, retty', reqs, ens)
      , e2
      , t2 ) ->
      let cfg = [("model", "true"); ("proof", "false")] in
      (* creating the context *)
      let ctx = Z3.mk_context cfg in
      (* creating a solver *)
      let solver = Solver.mk_solver ctx None in
      (* getting the z3 params *)
      let z3_params, env' = add_params_to_ctx params env ctx solver in
      (* adding reqs about these z3 params to the solver *)
      let _ = add_reqs_to_solver func_name z3_params reqs env' ctx solver in
      (* getting the cnot constraints *)
      let cnot_cons = remove_bad (generate_clone_reqs tvs params retexp env') in
      print_endline ("constraints for " ^ func_name ^ ":") ;
      let _ =
        ShowLambdaQs.show
          (ShowLambdaQs.showList ShowLambdaQs.showConstr cnot_cons)
        |> print_endline
      in
      let _ =
        check_cnot_applications func_name z3_params cnot_cons env' ctx solver
      in
      let funcdefs' =
        Strmap.add func_name
          ( ELam (tvs, params, retexp, retty)
            (* reqs here is empty for the time being *)
          , TFun (tvs', tys, retty', cnot_cons @ reqs, ens) )
          env.funcdefs
      in
      (* note that we just want to use env here, since we dont want the params *)
      let env'' = {env with funcdefs= funcdefs'} in
      print_endline ("done with analysis for " ^ func_name) ;
      print_endline "\n" ;
      check_prog_for_clone e2 env''
  | _ ->
      print_endline "done"

(* FIXME: get rid of the different environments to avoid all this confusion *)

let def_env2 =
  {funcdefs= empty; bodyvars= empty; exivars= empty; paramvars= empty}

let funcdefs =
  Strmap.add (get_func_name qMost)
    (get_func_exp qMost, get_func_type qMost)
    empty

let funcdefs' =
  Strmap.add (get_func_name qRest)
    (get_func_exp qRest, get_func_type qRest)
    funcdefs

let funcdefs'' =
  Strmap.add (get_func_name qRev)
    (get_func_exp qRev, get_func_type qRev)
    funcdefs'

let funcdefs''' =
   Strmap.add (get_func_name qTail)
     (get_func_exp qTail, get_func_type qTail)
     funcdefs''

let funcdefs'''' =
  Strmap.add (get_func_name cnot)
    (get_func_exp cnot, get_func_type cnot)
    funcdefs'''

let arr_env2 = {def_env2 with funcdefs= funcdefs''''}

(*  *)
(*  *)
(*  *)

let def_env = {qrefs= empty; qalls= empty; vars= empty}

let arr_vars = Strmap.add (get_func_name qMost) (get_func_type qMost) empty

let arr_vars' = Strmap.add (get_func_name qRest) (get_func_type qRest) arr_vars

let arr_vars'' = Strmap.add (get_func_name qRev) (get_func_type qRev) arr_vars'

let arr_vars''' =
   Strmap.add (get_func_name qTail) (get_func_type qTail) arr_vars''

let arr_vars'''' =
  Strmap.add (get_func_name cnot) (get_func_type cnot) arr_vars'''

let arrays_env = {def_env with vars= arr_vars''''}

let get_env (sysargs : key array) : Elab.env_t =
  if Array.exists (fun s -> s = "-arrlib") Sys.argv then arrays_env else def_env

let elab_main () =
  (* TODO: add real cmd line arg parsing *)
  if Array.length Sys.argv < 2 then
    failwith
      "Usage: dune exec ./run_elab.exe -- <file_name> (optional -arrlib or \
       -assume_range flag)"
  else
    let env = get_env Sys.argv in
    let channel = open_in Sys.argv.(1) in
    let in_ast = Elab.parse channel in
    print_string
      ( "[Input abstract syntax]\n\n"
      ^ (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_ast
      ^ "\n\n" ) ;
    (* TODO: create an environment where basic functions are defined *)
    let out_ast = elab in_ast env in
    print_string
      ( "[Output abstract syntax]\n\n"
      ^ ShowLambdaQs.show (ShowLambdaQs.showExp out_ast)
      ^ "\n\n[Linearized tree]\n\n"
      ^ PrintLambdaQs.printTree PrintLambdaQs.prtExp out_ast
      ^ "\n\n[Funcdef list]\n\n"
      ^ ShowLambdaQs.show
          (ShowLambdaQs.showList ShowLambdaQs.showFuncdef
             (prog_to_func_list out_ast) )
      ^ "\n\n" ) ;
    if Array.exists (fun s -> s = "-assume_range") Sys.argv then
      check_prog_for_clone (assume_ranges out_ast) arr_env2
    else check_prog_for_clone out_ast arr_env2

let cnotcheck_main () = check_prog_for_clone qApplyToEachZip arr_env2 ;;

(* let cnotcheck_main () =
     check_prog_for_clone (add_range_predicate mostrestzip 0) arr_env
   ;; *)

elab_main ()

(*
   cnotcheck_main () *)
