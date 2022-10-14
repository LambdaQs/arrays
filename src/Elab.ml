open AbsLambdaQs
open AbsQSharp
open Printf
open Map

let unimplemented_error s = "Not yet implemented: " ^ s

module Strmap = Map.Make(String)

(* the type of an environment. TODO: figure out specifically how this works *)
type env_t = { vars : (AbsLambdaQs.typ) Strmap.t }

type 


(* should also take in signature (stack data struc to keep track of Qubits) and 
   context (to keep track of variables and types) *)
let rec elab (prog : AbsQSharp.doc) : AbsLambdaQs.cmd =
  match prog with
  | Prog ([ns]) -> elab_nmspace ns
  | _ -> failwith (unimplemented_error "Multiple namespaces")

and elab_nmspace (ns : AbsQSharp.nmspace) : AbsLambdaQs.cmd =
  match ns with
  (* TODO: do something with the namespace's name *)
  | NDec (_, elmts) -> elab_nselmts elmts

and elab_nselmts (elmts : AbsQSharp.nSElmnt list) : AbsLambdaQs.cmd =
  match elmts with
  (* TODO: do we always want to return empty? *)
  | [] -> CRet (ETriv)
  (* TODO: do something with imports *)
  | NSOp _ :: elmts -> elab_nselmts elmts
  | NSOpAs _ :: elmts -> elab_nselmts elmts
  | NSTy _ :: _ -> failwith (unimplemented_error "Type declarations (NSTy)")
  (* TODO: do something with declaration prefix *)
  | NSCall (_, calld) :: t ->
      let (name, body) = elab_calldec calld in
      AbsLambdaQs.CBnd (name, body, elab_nselmts t)

and curry (params : AbsQSharp.param list) (body : AbsQSharp.body) : AbsLambdaQs.exp =
  match params with
  | [] -> failwith (unimplemented_error "Empty parameter list")
  | [ParNI (NItem (UIdent arg,typ))] ->
      AbsLambdaQs.proc (MVar (Ident arg), elab_type typ, elab_body body)
  | (ParNI (NItem (UIdent arg,typ))) :: t ->
      AbsLambdaQs.ELam (MVar (Ident arg), elab_type typ, curry t body)
  | _ -> failwith (unimplemented_error "Nested paramss (ParNIA)")


and elab_calldec (calld : AbsQSharp.callDec) : AbsLambdaQs.var * AbsLambdaQs.exp =
  match calld with
  | CDFun _ -> failwith (unimplemented_error "Function declarations (CDFun)")
  (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, params, typ, _, body) ->
     (match params with
      | ParTpl params ->
          (MVar (Ident name), curry params body))
      (* | _ -> failwith (unimplemented_error "Operations with multiple arguments")) *)
  | _ -> failwith (unimplemented_error "Operations with type parameters (tyArg)")

and elab_type (typ : AbsQSharp.typ) : AbsLambdaQs.typ =
  match typ with
  | TEmp -> failwith (unimplemented_error "(TEmp)")
  | TPar (TIdent tyarg) -> failwith (unimplemented_error "(TPar)")
  | TQNm _ -> failwith (unimplemented_error "(TQNm)")
  | TTpl typs -> failwith (unimplemented_error "(TTpl)")
  (* is this right?? TParr is partial function, which sounds different than just the type of a function  *)
  | TFun (ty1, ty2) -> AbsLambdaQs.TParr (elab_type ty1, elab_type ty2) 
  (* TODO: is TOp the same type as TFun? *)
  | TOp (ty1, ty2, chars) -> failwith (unimplemented_error "(TOp)")
  | TArr typ -> AbsLambdaQs.TArr (elab_type typ)
  | TBInt -> failwith (unimplemented_error "(TBInt)")
  | TBool -> AbsLambdaQs.TBool
  | TDbl -> failwith (unimplemented_error "(TDbl)")
  | TInt -> AbsLambdaQs.TInt
  | TPli -> failwith (unimplemented_error "(TPli)")
  (* TODO: should send to Qref, but what should the key be? *)
  | TQbit -> failwith (unimplemented_error "(TQbit)")
  | TRng -> failwith (unimplemented_error "(TRng)")
  | TRes -> failwith (unimplemented_error "(TRes)")
  | TStr -> AbsLambdaQs.TStr
  | TUnit -> AbsLambdaQs.TUnit


and elab_body (body : AbsQSharp.body) : AbsLambdaQs.cmd =
  match body with
  | BSpec _ -> failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) -> elab_stmts stmts



and elab_stmts (stmts : AbsQSharp.stm list) : AbsLambdaQs.cmd =
  match stmts with
  (* TODO: shouldn't always return empty *)
  | [] -> CRet ETriv
  (* TODO: in general, we'll want to use CBnd -- what var should we bind to? *)

  (* TODO: this is wrong since sometimes we want CGap *)
  | (SExp exp) :: [] -> AbsLambdaQs.CRet (elab_exp exp) 
  | (SExp exp) :: stmts' -> failwith (unimplemented_error "must determine exp")
  | (SRet exp) :: _ -> AbsLambdaQs.CRet (elab_exp exp) (* should things after return statement be ignored? *)
  | SFail exp :: stmts' -> failwith (unimplemented_error "(SFail)")
  | (SLet (bnd, exp)) :: stmts' -> 
    (match bnd with 
     | BndWild -> elab_stmts stmts' (* TODO: may want to account for unpure 'let _ = ... ' statements *)
     | BndName (UIdent var) -> CBnd (MVar (Ident var), elab_exp exp, elab_stmts stmts')
     | BndTplA bnds -> failwith (unimplemented_error "list binds"))
  (* TODO: what differentiates SLet, SMut, and SSet? *)
  | (SMut (bnd, exp)) :: stmts' -> 
    (match bnd with 
     | BndWild -> elab_stmts stmts' 
     | BndName (UIdent var) -> CBnd (MVar (Ident var), elab_exp exp, elab_stmts stmts')
     | BndTplA bnds -> failwith (unimplemented_error "list binds"))
  | (SSet (bnd, exp)) :: stmts' -> 
      (match bnd with 
       | BndWild -> elab_stmts stmts' 
       | BndName (UIdent var) -> CBnd (MVar (Ident var), elab_exp exp, elab_stmts stmts')
       | BndTplA bnds -> failwith (unimplemented_error "list binds"))
  | SSetOp (UIdent arg, sOp, exp) :: stmts' -> failwith (unimplemented_error "SSetOp")
  | SSetW (UIdent arg, exp1, exp2) :: stmts' -> failwith (unimplemented_error "SSetW")
  (* TODO: look up how these are done in other languages since the implementation here is probably similar *)
  (* I have some ideas for how this would work, but gets translated to exp anyways and not cmd *)
  (* will either need to figure out what VAR to bind to as in the above or do CRet (EIte)  *)
  | (SIf (exp, scope)) :: stmts' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SEIf (exp, scope)) :: stmts' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SElse scope) :: stmts' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SFor (bnd, exp, scope)) :: stmts' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SWhile (exp, scope)) :: stmts' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  
  (* TODO: can we assume that when SUntil appears, SRep must have come before? *)
  | (SRep scope) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SUntil exp) :: stms'  -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SUntilF (exp, scope)) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  
  | (SWithin scope) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SApply scope) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  
  | (SUse qbitBnd) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")
  | (SUseS (qbitBnd, scope)) :: stms' -> failwith (unimplemented_error "Most statements (SFail, SLet, ...)")


and elab_exp (exp : AbsQSharp.exp) : AbsLambdaQs.exp =
  match exp with
  | EName (QUnqual (UIdent x)) -> EVar (MVar (Ident x))
  | ECall (e1, [e2]) -> AbsLambdaQs.EAp(elab_exp e1, elab_exp e2)
  | ECall (e1, [e2; e3]) -> AbsLambdaQs.EAp((AbsLambdaQs.EAp(elab_exp e1, elab_exp e2)), elab_exp e2)
  | _ -> failwith (unimplemented_error "Most expressions")

(* Example: *)
let parse (c : in_channel) : AbsQSharp.doc =
    ParQSharp.pDoc LexQSharp.token (Lexing.from_channel c)

let elab_example () =
  (* TODO: add real cmd line arg parsing *)
  if Array.length Sys.argv != 2
  then failwith "Usage: ./TestElab <filename>"
  else
    let channel = open_in Sys.argv.(1) in
    let in_prog = parse channel in
    let out_prog = elab in_prog in
    print_string ("[Input abstract syntax]\n\n"^
                  (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_prog ^ "\n\n");
    print_string ("[Output abstract syntax]\n\n"^
                  (fun x -> ShowLambdaQs.show (ShowLambdaQs.showCmd x)) out_prog ^ "\n\n")
;;

elab_example ();;
