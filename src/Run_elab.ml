open Map
open String
open List
open Either
open Elab
open Arrays
(* open AbsQSharp *)

module Strmap = Map.Make (String)
open Strmap

let def_env = {qrefs= empty; qalls= empty; vars= empty}

let arr_vars = Strmap.add (get_func_name qMost) (get_func_type qMost) empty

let arr_vars' = Strmap.add (get_func_name qRest) (get_func_type qRest) arr_vars

let arr_vars'' = Strmap.add (get_func_name cnot) (get_func_type cnot) arr_vars'

let arrays_env = {qrefs= empty; qalls= empty; vars= arr_vars''}

let get_env (sysargs : key array) : env_t =
  if Array.length Sys.argv = 2 then def_env
  else if Array.length Sys.argv = 3 && Sys.argv.(2) = "-arrlib" then arrays_env
  else
    failwith
      "Usage: dune exec ./run_elab.exe -- <file_name> (optional -arrlib flag)"

let elab_main () =
  (* TODO: add real cmd line arg parsing *)
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
    ^ "\n")
;;

elab_main ()
