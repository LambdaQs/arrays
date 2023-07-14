open Z3
open Z3.Arithmetic
open Z3.Boolean
open Z3.Expr
open Z3.FuncDecl
open Z3.Quantifier
open Z3.Symbol




let create_z3_array (arr_name : string) (ctx : Z3.context) (solver : Solver.solver) : (FuncDecl.func_decl *  Expr.expr) =
  
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
  let bodylow = Boolean.mk_implies ctx (Arithmetic.mk_lt ctx ilow zero) (Boolean.mk_eq ctx (FuncDecl.apply arr [ilow]) zero) in
  (* Creating the universal quantifier "for all i, if i < 0 then a[i] = 0" *)

  let forall_expr1 = Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx
  [int_sort]  (* Empty sort list *)
  [Symbol.mk_string ctx "i"]  (* Bound variables *)
  bodylow  (* Quantifier body *)
  None  (* Weight: none *)
  []  (* Patterns: empty list *)
  []  (* No multi-patterns *)
  None  (* No quantifier id *)
  None  (* No skolem id *)) in

  
  (* Creating the bound variable "i" *)
  let iupp = Quantifier.mk_bound ctx 0 int_sort in
  (* Creating the implication body "if i < 0 then a[i] = 0" *)
  let bodyupp = Boolean.mk_implies ctx (Arithmetic.mk_ge ctx iupp arrlen) (Boolean.mk_eq ctx (FuncDecl.apply arr [iupp]) zero) in
  (* Creating the universal quantifier "for all i, if i >= alen then a[i] = 0" *)

  let forall_expr2 = Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx
  [int_sort]  (* Empty sort list *)
  [Symbol.mk_string ctx "i"]  (* Bound variables *)
  bodyupp  (* Quantifier body *)
  None  (* Weight: none *)
  []  (* Patterns: empty list *)
  []  (* No multi-patterns *)
  None  (* No quantifier id *)
  None  (* No skolem id *)) in

  let _ = Solver.add solver [forall_expr1; forall_expr2] in

  (arr, arrlen)


let array_is_range (arr : FuncDecl.func_decl) (arrlen : Expr.expr ) 
                  (ctx : Z3.context) (solver : Solver.solver) : Expr.expr =
  
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
  
  let body = (Boolean.mk_implies ctx 
              i_in_range
              (Boolean.mk_eq ctx (FuncDecl.apply arr [i]) (Arithmetic.mk_add ctx [base_val; i]))) in
  
  let forall_expr = Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx
      [int_sort]  (* Empty sort list *)
      [Symbol.mk_string ctx "i"]  (* Bound variables *)
      body  (* Quantifier body *)
      None  (* Weight: none *)
      []  (* Patterns: empty list *)
      []  (* No multi-patterns *)
      None  (* No quantifier id *)
      None  (* No skolem id *)) in
  
  let _ = Solver.add solver [forall_expr] in

  base_val



let () =
  let cfg = [("model", "true"); ("proof", "false")] in  (* configuration for the context *)
  let ctx = Z3.mk_context cfg in                           (* creating the context *)

  (* creating a solver and adding the assertion *)
  let slvr = Solver.mk_solver ctx None in


  (* making the constants 0 and 1 *)
  let zero = Integer.mk_numeral_i ctx 0 in
  let one = Integer.mk_numeral_i ctx 1 in
  (* creating the integer sort *)
  let int_sort = Integer.mk_sort ctx in


  (* Declare the array a and its length n, which is now implicitly associated to length *)
  let a, alen = create_z3_array "a" ctx slvr in

  (* let _ = array_is_range a alen ctx slvr in  *)

  let b, blen = create_z3_array "b" ctx slvr in

  let c, clen = create_z3_array "c" ctx slvr in

  let most_len = Boolean.mk_eq ctx blen (Arithmetic.mk_sub ctx [alen; one]) in
  let rest_len = Boolean.mk_eq ctx clen (Arithmetic.mk_sub ctx [alen; one]) in

  let _ = Solver.add slvr [most_len; rest_len] in


  let i_most = Quantifier.mk_bound ctx 0 int_sort in

  let i_most_ge_zero = Arithmetic.mk_ge ctx i_most zero in
  let i_most_lt_blen = Arithmetic.mk_lt ctx i_most blen in
  let i_most_in_range = Boolean.mk_and ctx [i_most_ge_zero; i_most_lt_blen] in
  

  let body_most = (Boolean.mk_implies ctx 
              i_most_in_range
              (Boolean.mk_eq ctx (FuncDecl.apply a [i_most]) (FuncDecl.apply b [i_most]))) in
  
  let forall_expr_most = Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx
      [int_sort]  (* Empty sort list *)
      [Symbol.mk_string ctx "i"]  (* Bound variables *)
      body_most  (* Quantifier body *)
      None  (* Weight: none *)
      []  (* Patterns: empty list *)
      []  (* No multi-patterns *)
      None  (* No quantifier id *)
      None  (* No skolem id *)) in

  let _ = Solver.add slvr [forall_expr_most] in


  (* TODO: can I use the same i here, or do I need to make a new one each time? Probably make new one *)
  let i_rest = Quantifier.mk_bound ctx 0 int_sort in

  let i_rest_ge_zero = Arithmetic.mk_ge ctx i_rest zero in
  let i_rest_lt_clen = Arithmetic.mk_lt ctx i_rest clen in
  let i_rest_in_range = Boolean.mk_and ctx [i_rest_ge_zero; i_rest_lt_clen] in
  
  let body_rest = (Boolean.mk_implies ctx 
              i_rest_in_range
              (Boolean.mk_eq ctx (FuncDecl.apply a [(Arithmetic.mk_add ctx [i_rest; one])]) (FuncDecl.apply c [i_rest]))) in
  
  let forall_expr_rest = Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx
      [int_sort]  (* Empty sort list *)
      [Symbol.mk_string ctx "i"]  (* Bound variables *)
      body_rest  (* Quantifier body *)
      None  (* Weight: none *)
      []  (* Patterns: empty list *)
      []  (* No multi-patterns *)
      None  (* No quantifier id *)
      None  (* No skolem id *)) in

  let _ = Solver.add slvr [forall_expr_rest] in



  (* Creating the bound variable "x" *)
  let x = Quantifier.mk_bound ctx 0 int_sort in

  (* Define the conditions for x *)
  let geq_zero = Arithmetic.mk_ge ctx x zero in
  let lt_len = Arithmetic.mk_lt ctx x blen in
 
  (* Define equality condition for array selections *)
  let eq_selects = Boolean.mk_eq ctx (FuncDecl.apply b [x]) (FuncDecl.apply c [x]) in
 
  (* Combine conditions *)
  let conditions = Boolean.mk_and ctx [geq_zero; lt_len; eq_selects] in
 
  (* Create exists quantifier *)
  let exists_expr = Quantifier.expr_of_quantifier 
    (Quantifier.mk_exists ctx
        [int_sort]
        [Symbol.mk_string ctx "x"]
        conditions
        None
        []
        []
        None
        None) in
 
  (* Add the assertion to the solver *)
  let _ = Solver.add slvr [exists_expr] in


  (* let testEq = Boolean.mk_eq ctx alen (Integer.mk_numeral_i ctx 5) in *)
  (* let _ = Solver.add slvr [testEq] in *)

  (* Check satisfiability *)
  match Solver.check slvr [] with
  | Solver.SATISFIABLE ->
    (* Print model if satisfiable *)
    begin
      match Solver.get_model slvr with
      | Some m -> print_endline ("SAT:\n" ^ (Model.to_string m) ^ "\nThe above witness shows that cloning may occur.")
      | None -> print_endline "No model found although constraints may be satisfiable: this means we don't know if cloning occurs."
    end
  | _ -> print_endline "Not satisfiable: this means that cloning is impossible."



