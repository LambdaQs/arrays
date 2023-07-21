(* to compile: ocamlfind ocamlopt -thread -package z3 -linkpkg -o Clonecheck1 Clonecheck1.ml *)

open AbsLambdaQs
open ShowLambdaQs
(* for some reason, this doesn't need to be opened in Elab.ml; check the makefile*)

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

type z3_exp =
  | Z3_Int of Expr.expr
  | Z3_Qall of Expr.expr
  | Z3_Qarr of FuncDecl.func_decl * Expr.expr

type env_t = {vars: typ Strmap.t; z3vars: z3_exp Strmap.t; ret_count: int}

(* NB!!!!!! Nowhere do we ever check that the ensures statements actually are true based on what
   happens inside the function, that is not really the point of this project. We assume that annotations
   are always faithful to the function defs *)

let testfunctree =
  ELet
    ( MVar (Ident "X")
    , ELam
        ( []
        , [TyVar (MVar (Ident "qubit"), TQAll (MKVar (Ident "0")))]
          (* NB: The next line was manually anotated *)
        , ECmd (TUnit, CGap (MUni (Ident "X"), EVar (MVar (Ident "qubit"))))
        , TUnit )
    , TFun ([], [TQAll (MKVar (Ident "0"))], TUnit, [], [])
    , ELet
        ( MVar (Ident "CNOT")
        , ELam
            ( []
            , [ TyVar (MVar (Ident "control"), TQAll (MKVar (Ident "0")))
              ; TyVar (MVar (Ident "target"), TQAll (MKVar (Ident "1"))) ]
            , ELet
                ( MVar (Ident "_wild_")
                , ECmd
                    ( TUnit
                    , CDiag
                        ( MUni (Ident "I")
                        , MUni (Ident "X")
                        , EVar (MVar (Ident "control"))
                        , EVar (MVar (Ident "target")) ) )
                , TUnit
                , ETriv
                , TUnit )
            , TUnit )
        , TFun
            ( []
            , [TQAll (MKVar (Ident "0")); TQAll (MKVar (Ident "1"))]
            , TUnit
            , [CNeq (EArg (BNat 0), EArg (BNat 1))]
            , [] )
        , ELet
            ( MVar (Ident "qMost")
            , ELam
                ( []
                , [ TyVar
                      ( MVar (Ident "array")
                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                , EArrIdx
                    ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                    , EVar (MVar (Ident "array"))
                    , ERngL
                        (ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 2))
                    )
                , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
            , TFun
                ( []
                , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                , TAbsArr (TQAll (MKVar (Ident "ql0")))
                , []
                , [] )
            , ELet
                ( MVar (Ident "qRest")
                , ELam
                    ( []
                    , [ TyVar
                          ( MVar (Ident "array")
                          , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                    , EArrIdx
                        ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                        , EVar (MVar (Ident "array"))
                        , ERngR (EInt 1) )
                    , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                , TFun
                    ( []
                    , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                    , TAbsArr (TQAll (MKVar (Ident "ql0")))
                    , []
                    , [] )
                , ELet
                    ( MVar (Ident "ApplyCNOT_oneelem")
                    , ELam
                        ( []
                        , [ TyVar
                              ( MVar (Ident "a")
                              , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                          ; TyVar (MVar (Ident "i"), TInt) ]
                        , ELet
                            ( MVar (Ident "b")
                            , EAp
                                ( EVar (MVar (Ident "qMost"))
                                , TFun
                                    ( []
                                    , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                                    , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                    , []
                                    , [] )
                                , [ TyExp
                                      ( EVar (MVar (Ident "a"))
                                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                                  ] )
                            , TAbsArr (TQAll (MKVar (Ident "ql0")))
                            , ELet
                                ( MVar (Ident "c")
                                , EAp
                                    ( EVar (MVar (Ident "qRest"))
                                    , TFun
                                        ( []
                                        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                                        , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                        , []
                                        , [] )
                                    , [ TyExp
                                          ( EVar (MVar (Ident "a"))
                                          , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                          ) ] )
                                , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                , ELet
                                    ( MVar (Ident "_wild_")
                                    , EAp
                                        ( EVar (MVar (Ident "CNOT"))
                                        , TFun
                                            ( []
                                            , [ TQAll (MKVar (Ident "0"))
                                              ; TQAll (MKVar (Ident "1")) ]
                                            , TUnit
                                            , []
                                            , [] )
                                        , [ TyExp
                                              ( EArrIdx
                                                  ( TQAll (MKVar (Ident "ql0"))
                                                  , EVar (MVar (Ident "b"))
                                                  , EVar (MVar (Ident "i")) )
                                              , TQAll (MKVar (Ident "ql0")) )
                                          ; TyExp
                                              ( EArrIdx
                                                  ( TQAll (MKVar (Ident "ql0"))
                                                  , EVar (MVar (Ident "c"))
                                                  , EVar (MVar (Ident "i")) )
                                              , TQAll (MKVar (Ident "ql0")) ) ]
                                        )
                                    , TUnit
                                    , ETriv
                                    , TUnit )
                                , TUnit )
                            , TUnit )
                        , TUnit )
                    , TFun
                        ( []
                        , [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt]
                        , TUnit
                        , []
                        , [] )
                    , ETriv
                    , TUnit )
                , TUnit )
            , TUnit )
        , TUnit )
    , TUnit )

(* let testfunctree =
   ELet
     ( MVar (Ident "X")
     , ELam
         ( []
         , [TyVar (MVar (Ident "qubit"), TQAll (MKVar (Ident "0")))]
           (* NB: The next line was manually anotated *)
         , ECmd (TUnit, CGap (MUni (Ident "X"), EVar (MVar (Ident "qubit"))))
         , TUnit
          )
     , TFun ([], [TQAll (MKVar (Ident "0"))], TUnit)
     , ELet
         ( MVar (Ident "CNOT")
         , ELam
             ( []
             , [ TyVar (MVar (Ident "control"), TQAll (MKVar (Ident "0")))
               ; TyVar (MVar (Ident "target"), TQAll (MKVar (Ident "1"))) ]
             , ELet
                 ( MVar (Ident "_wild_")
                 , ECmd
                     ( TUnit
                     , CDiag
                         ( MUni (Ident "I")
                         , MUni (Ident "X")
                         , EVar (MVar (Ident "control"))
                         , EVar (MVar (Ident "target")) ) )
                 , TUnit
                 , ETriv
                 , TUnit )
             , TUnit )
         , TFun
             ([], [TQAll (MKVar (Ident "0")); TQAll (MKVar (Ident "1"))], TUnit, [ CNeq
             (EVar (MVar (Ident "control")), EVar (MVar (Ident "target")))
         ], [])
         , ELet
             ( MVar (Ident "qMost")
             , ELam
                 ( []
                 , [ TyVar
                       ( MVar (Ident "array")
                       , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                 , EArrIdx
                     ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                     , EVar (MVar (Ident "array"))
                     , ERngL
                         (ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 2))
                     )
                 , TAbsArr (TQAll (MKVar (Ident "ql0")))
                 , [CGt (EArrLen (EVar (MVar (Ident "array"))), EInt 0)]
                 , [ CEq
                       ( EArrLen (EVar (MVar (Ident "RET")))
                       , ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 1) )
                   ; CForall
                       ( MVar (Ident "i")
                       , CImp
                           ( CAnd
                               ( CGe (EVar (MVar (Ident "i")), EInt 0)
                               , CLt
                                   ( EVar (MVar (Ident "i"))
                                   , EArrLen (EVar (MVar (Ident "RET"))) ) )
                           , CEq
                               ( EArrIdx
                                   ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                                   , EVar (MVar (Ident "array"))
                                   , EVar (MVar (Ident "i")) )
                               , EArrIdx
                                   ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                                   , EVar (MVar (Ident "RET"))
                                   , EVar (MVar (Ident "i")) ) ) ) ) ] )
             , TFun
                 ( []
                 , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                 , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
             , ELet
                 ( MVar (Ident "qRest")
                 , ELam
                     ( []
                     , [ TyVar
                           ( MVar (Ident "array")
                           , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                     , EArrIdx
                         ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                         , EVar (MVar (Ident "array"))
                         , ERngR (EInt 1) )
                     , TAbsArr (TQAll (MKVar (Ident "ql0")))
                     , []
                     , [] )
                 , TFun
                     ( []
                     , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                     , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                 , ELet
                     ( MVar (Ident "ApplyCNOT_oneelem")
                     , ELam
                         ( []
                         , [ TyVar
                               ( MVar (Ident "a")
                               , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                           ; TyVar (MVar (Ident "i"), TInt) ]
                         , ELet
                             ( MVar (Ident "b")
                             , EAp
                                 ( EVar (MVar (Ident "qMost"))
                                 , TFun
                                     ( []
                                     , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                                     , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                                 , [ TyExp
                                       ( EVar (MVar (Ident "a"))
                                       , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                                   ] )
                             , TAbsArr (TQAll (MKVar (Ident "ql0")))
                             , ELet
                                 ( MVar (Ident "c")
                                 , EAp
                                     ( EVar (MVar (Ident "qRest"))
                                     , TFun
                                         ( []
                                         , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                                         , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                         )
                                     , [ TyExp
                                           ( EVar (MVar (Ident "a"))
                                           , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                           ) ] )
                                 , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                 , ELet
                                     ( MVar (Ident "_wild_")
                                     , EAp
                                         ( EVar (MVar (Ident "CNOT"))
                                         , TFun
                                             ( []
                                             , [ TQAll (MKVar (Ident "0"))
                                               ; TQAll (MKVar (Ident "1")) ]
                                             , TUnit )
                                         , [ TyExp
                                               ( EArrIdx
                                                   ( TQAll (MKVar (Ident "ql0"))
                                                   , EVar (MVar (Ident "b"))
                                                   , EVar (MVar (Ident "i")) )
                                               , TQAll (MKVar (Ident "ql0")) )
                                           ; TyExp
                                               ( EArrIdx
                                                   ( TQAll (MKVar (Ident "ql0"))
                                                   , EVar (MVar (Ident "c"))
                                                   , EVar (MVar (Ident "i")) )
                                               , TQAll (MKVar (Ident "ql0")) ) ]
                                         )
                                     , TUnit
                                     , ETriv
                                     , TUnit )
                                 , TUnit )
                             , TUnit )
                         , TUnit
                         , []
                         , [] )
                     , TFun
                         ( []
                         , [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt]
                         , TUnit )
                     , ETriv
                     , TUnit )
                 , TUnit )
             , TUnit )
         , TUnit )
     , TUnit ) *)

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
    (ctx : Z3.context) (solver : Solver.solver) : unit =
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
  Solver.add solver [forall_expr]
(* base_val *)

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
      failwith "expected two qlists, got something else"

let rec add_params_to_ctx (params : typedVar list) (env : env_t)
    (ctx : Z3.context) (solver : Solver.solver) : z3_exp list * env_t =
  match params with
  | TyVar (MVar (Ident qlist_name), TAbsArr (TQAll k)) :: params' ->
      let z3_qarr = create_z3_array qlist_name ctx solver in
      let z3vars' = Strmap.add qlist_name z3_qarr env.z3vars in
      let vars' = Strmap.add qlist_name (TAbsArr (TQAll k)) env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let (ps, env'') = add_params_to_ctx params' env' ctx solver in 
      (z3_qarr :: ps, env'')
  | TyVar (MVar (Ident q_name), TQAll k) :: params' ->
      let z3_qubit = Z3_Qall (Integer.mk_const_s ctx q_name) in
      let z3vars' = Strmap.add q_name z3_qubit env.z3vars in
      let vars' = Strmap.add q_name (TQAll k) env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let (ps, env'') = add_params_to_ctx params' env' ctx solver in 
      (z3_qubit :: ps, env'')
  | TyVar (MVar (Ident int_name), TInt) :: params' ->
      let z3_int = Z3_Int (Integer.mk_const_s ctx int_name) in
      let z3vars' = Strmap.add int_name z3_int env.z3vars in
      let vars' = Strmap.add int_name TInt env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      let (ps, env'') = add_params_to_ctx params' env' ctx solver in 
      (z3_int :: ps, env'')
  | TyVar (MVar (Ident var_name), ty) :: params' ->
      let vars' = Strmap.add var_name ty env.vars in
      let env' = {env with vars= vars'} in
      add_params_to_ctx params' env' ctx solver
  | [] ->
      ([], env)

(**********************************)
(* interesting the asymmetry here *)
(**********************************)

(* This first set is called during function definition *)
let rec add_reqs_to_solver (params : z3_exp list) (reqs : constr list)
    (ctx : Z3.context) (solver : Solver.solver) =
  match reqs with r :: rs -> print_endline "TODO" | [] -> ()

let check_ens_are_ensured (params : z3_exp list) (ret_z3 : z3_exp)
    (ens : constr list) (ctx : Z3.context) (solver : Solver.solver)
    =
  match ens with en :: ens' -> print_endline "TODO" | [] -> ()



(* This second set is called during function application *)
let check_reqs_are_satisfied (args_z3 : z3_exp list) (reqs : constr list)
    (ctx : Z3.context) (solver : Solver.solver) =
  match reqs with en :: ens' -> print_endline "TODO" | [] -> ()

let add_ens_to_solver (args : z3_exp list) (ret : z3_exp) (ens : constr list) 
                (env : env_t) (ctx : Z3.context) (solver : Solver.solver) =
                match ens with en :: ens' -> print_endline "TODO" | [] -> ()

(***********************)
(***********************)
(***********************)

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
      failwith "TODO: get_z3_term_of_exp"

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
      let z3vars' = Strmap.add vname vexp_z3 env.z3vars in
      let vars' = Strmap.add vname vty env.vars in
      let env' = {env with z3vars= z3vars'; vars= vars'} in
      check_body_applications bexp env' ctx solver
  | EAp (f, TFun (tvs, paramtys, retty, reqs, ens), args) ->
      let args_z3 =
        List.map
          (fun arg ->
            match arg with
            | TyExp (e, t) -> (
              match check_body_applications e env ctx solver with
              | e_z3, env' ->
                  e_z3 ) )
          args
      in
      let _ = check_reqs_are_satisfied args_z3 reqs ctx solver in
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
        | _ ->
            failwith "TODO: must add z3_exp based on return type"
      in 
      let _ = add_ens_to_solver args_z3 ret_z3 ens env ctx solver in
      (ret_z3, env')
  | EAp (f, fty, args) ->
      failwith "trying to apply function, but instead got different type"
      (* FIXME: get this better error message to work *)
      (* ("trying to apply function, but instead got type: " ^ ShowLambdaQs.show (ShowLambdaQs.showTyp fty)) *)
  | ECmd _ ->
      failwith "TODO ECmd"
  | EArrIdx (ty, arr, len) ->
      failwith "TODO EArrIdx"
  | EArrLen arr ->
      failwith "TODO EArrLen"
  | EIte (ty, b, e1, e2) ->
      (* TODO: find a way to check both branches *)
      let _ = check_body_applications e1 env ctx solver in
      check_body_applications e2 env ctx solver
  | _ ->
      failwith "TODO: check_body_applications"

let check_funcdec_for_clone (tvs : tVar list) (params : typedVar list)
    (body : exp) (reqs : constr list) (ens : constr list) (env : env_t) =
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
  let (z3_params, env') = add_params_to_ctx params env ctx solver in
  let _ = add_reqs_to_solver z3_params reqs ctx solver in
  let body_z3_exp, env'' = check_body_applications body env' ctx solver in
  let _ = check_ens_are_ensured z3_params body_z3_exp ens env'' ctx solver in
  (* Check satisfiability, i.e., are the ensures constraints satisfied? *)
  match Solver.check solver [] with
  | Solver.SATISFIABLE -> (
    (* Print model if satisfiable *)
    match Solver.get_model solver with
    | Some m ->
        print_endline
          ( "SAT:\n" ^ Model.to_string m
          ^ "\n\
             The above witness shows that the function output may not satisfy \
             the constraints." )
    | None ->
        print_endline
          "No model found although constraints may be satisfiable: this means \
           we don't know if the output satisfies the constraints." )
  | _ ->
      print_endline
        "Not satisfiable: this means that the program does as it should!"


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
      let _ = check_funcdec_for_clone tvs params retexp reqs ens env in
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

let check_func_tree (func : exp) =
  let cfg = [("model", "true"); ("proof", "false")] in
  (* configuration for the context *)
  let ctx = Z3.mk_context cfg in
  (* creating the context *)

  (* creating a solver and adding the assertion *)
  let solver = Solver.mk_solver ctx None in
  (*
     (* making the constants 0 and 1 *)
     let zero = Integer.mk_numeral_i ctx 0 in
     let one = Integer.mk_numeral_i ctx 1 in
     (* creating the integer sort *)
     let int_sort = Integer.mk_sort ctx in
     (* Declare the array a and its length n, which is now implicitly associated to length *)
  *)

  (* Check satisfiability *)
  match Solver.check solver [] with
  | Solver.SATISFIABLE -> (
    (* Print model if satisfiable *)
    match Solver.get_model solver with
    | Some m ->
        print_endline
          ( "SAT:\n" ^ Model.to_string m
          ^ "\nThe above witness shows that cloning may occur." )
    | None ->
        print_endline
          "No model found although constraints may be satisfiable: this means \
           we don't know if cloning occurs." )
  | _ ->
      print_endline
        "Not satisfiable: this means that cloning doesn't occur and program is \
         safe!"
;;

check_func_tree testfunctree
