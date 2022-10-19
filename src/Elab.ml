open AbsLambdaQs
open AbsQSharp
open Printf
open Map

let unimplemented_error s = "Not yet implemented: " ^ s

(* what I will be using for a wildcard var when a placeholer var is needed *)
(* TODO: add freshvars so that different strings represent different exp's *)
let wild_var = AbsLambdaQs.MVar (AbsLambdaQs.Ident "_wild_")

module Strmap = Map.Make(String)

(* the type of an environment. TODO: figure out specifically how this works *)
(* type env_t = { vars : (AbsLambdaQs.typ) Strmap.t } could make this a record to be nicer *)
(* maybe check all variables and scopes etc... on LambdaQS level, but this can still be used as the stack *)
type env_t = int Strmap.t



(* looks for elif* + else? + ... and returns a list of the elifs/elses, and a list of the other stuff *)
let rec extract_ifs (stmts : AbsQSharp.stm list) : AbsQSharp.stm list * AbsQSharp.stm list =
  match stmts with
  | (SEIf (e, s)) :: stmts' -> let (ifs, stmts'') = extract_ifs stmts'
                          in ((SEIf (e, s)) :: ifs, stmts'')
  | (SElse scope) :: stmts' -> ([(SElse scope)], stmts')
  | _ -> ([], stmts)


(* should also take in signature (stack data struc to keep track of Qubits) and
   context (to keep track of variables and types) *)
let rec elab (prog : AbsQSharp.doc) (env : env_t) : AbsLambdaQs.cmd =
  match prog with
  | Prog ([ns]) -> elab_nmspace ns env
  | _ -> failwith (unimplemented_error "Multiple namespaces")

and elab_nmspace (ns : AbsQSharp.nmspace) (env : env_t) : AbsLambdaQs.cmd =
  match ns with
  (* TODO: do something with the namespace's name *)
  (* Should probably store them in the env! *)
  | NDec (_, elmts) -> elab_nselmts elmts env

and elab_nselmts (elmts : AbsQSharp.nSElmnt list) (env : env_t) : AbsLambdaQs.cmd =
  match elmts with
  (* TODO: do we always want to return empty? *)
  | [] -> CRet (ETriv)
  (* TODO: do something with imports *)
  | NSOp _ :: elmts -> elab_nselmts elmts env
  | NSOpAs _ :: elmts -> elab_nselmts elmts env
  | NSTy _ :: _ -> failwith (unimplemented_error "Type declarations (NSTy)")
  (* TODO: do something with declaration prefix *)
  | NSCall (_, calld) :: t ->
      let (name, body) = elab_calldec calld env in
      AbsLambdaQs.CBnd (name, body, elab_nselmts t env)


and curry (params : AbsQSharp.param list) (body : AbsQSharp.body) (env : env_t): AbsLambdaQs.exp =
  match params with
  | [] -> failwith (unimplemented_error "Empty parameter list")
  | [ParNI (NItem (UIdent arg,typ))] ->
      AbsLambdaQs.proc (MVar (Ident arg), elab_type typ, elab_body body env)
  | (ParNI (NItem (UIdent arg,typ))) :: t ->
      AbsLambdaQs.ELam (MVar (Ident arg), elab_type typ, curry t body env)
  | _ -> failwith (unimplemented_error "Nested paramss (ParNIA)")


(* what is going on here? Why these specific return values? *)
and elab_calldec (calld : AbsQSharp.callDec) (env : env_t) : AbsLambdaQs.var * AbsLambdaQs.exp =
  match calld with
  | CDFun (UIdent name, TAEmpty, ParTpl params, typ, body) ->
          (MVar (Ident name), curry params body env)

    (* TODO: what do we want to do with characteristics? We're currently ignoring them *)
  | CDOp (UIdent name, TAEmpty, ParTpl params, typ, _, body) ->
         (MVar (Ident name), curry params body env)

  | _ -> failwith (unimplemented_error "Operations with type parameters (tyArg)")

and elab_type (typ : AbsQSharp.typ) : AbsLambdaQs.typ =
  match typ with
  | TEmp -> failwith (unimplemented_error "(TEmp)")
  | TPar (TIdent tyarg) -> failwith (unimplemented_error "(TPar)")
  | TUDT _ -> failwith (unimplemented_error "(TQNm)")
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


  and elab_body (body : AbsQSharp.body) (env : env_t) : AbsLambdaQs.cmd =
  match body with
  | BSpec _ -> failwith (unimplemented_error "Specializations (BSpec)")
  | BScope (Scp stmts) -> elab_stmts stmts env


and elab_stmts (stmts : AbsQSharp.stm list) (env : env_t) : AbsLambdaQs.cmd =
  match stmts with
  (* TODO: shouldn't always return empty *)
  | [] -> CRet ETriv
  (* TODO: in general, we'll want to use CBnd -- what var should we bind to? *)

  (* (* TODO: this is wrong since sometimes we want CGap *)
     | (SExp exp) :: [] -> AbsLambdaQs.CRet (elab_exp exp) *)
  (* I beleive that this is actually the correct translation: *)
  | (SExp exp) :: stmts' -> CBnd (wild_var, elab_exp exp, elab_stmts stmts' env)
  (* this one is strightforward, just return the exp *)
  | (SRet exp) :: _ -> CRet (elab_exp exp) (* should things after return statement be ignored? *)
  | (SFail exp) :: stmts' -> failwith (unimplemented_error "(SFail)")
  | (SLet (bnd, exp)) :: stmts' ->
    (match bnd with
     | BndWild -> CBnd (wild_var, elab_exp exp, elab_stmts stmts' env)
     | BndName (UIdent var) -> CBnd (MVar (Ident var), elab_exp exp, elab_stmts stmts' env)
     | BndTplA bnds -> failwith (unimplemented_error "list binds"))
  (* TODO: what differentiates SLet, SMut, and SSet? *)
  | (SMut (bnd, exp)) :: stmts' -> failwith (unimplemented_error "SMut")
  | (SSet (bnd, exp)) :: stmts' -> failwith (unimplemented_error "SSet")

  | SSetOp (UIdent arg, sOp, exp) :: stmts' -> failwith (unimplemented_error "SSetOp")
  | SSetW (UIdent arg, exp1, larr, exp2) :: stmts' -> failwith (unimplemented_error "SSetW")
  (* TODO: look up how these are done in other languages since the implementation here is probably similar *)
  (* I have some ideas for how this would work, but gets translated to exp anyways and not cmd *)
  (* will either need to figure out what VAR to bind to as in the above or do CRet (EIte)  *)
  | (SIf (exp, scope)) :: stmts' ->
        let (ites, stmts'') = extract_ifs stmts' in
        CBnd (wild_var, elab_ite ((SIf (exp, scope)) :: ites) env, elab_stmts stmts'' env)

  (* these must come after if, so wont be dealt with here *)
  | (SEIf (exp, scope)) :: stmts' -> failwith ("Elif statement does not occur after an If statement")
  | (SElse scope) :: stmts' -> failwith ("Else statement does not occur after an If statement")

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
  | EEq (e1, e2) -> AbsLambdaQs.EEq (elab_exp e1, elab_exp e2)
  | EAdd (e1, e2) -> AbsLambdaQs.EAdd (elab_exp e1, elab_exp e2)
  (* Is this correct? Why the type mismatch? *)
  | EInt (Int i) -> AbsLambdaQs.EInt (int_of_string i)
  | _ -> failwith (unimplemented_error "Most expressions")

(* note that if and elif are basically the same when they come first, elif just had stuff before it *)
(* However, elif is different from else when they appear second *)
and elab_ite (stmts : AbsQSharp.stm list) (env : env_t) : AbsLambdaQs.exp =
  match stmts with
  | (SIf (cond, Scp stmts')) :: [] ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts' env in
        EIte (cond', ECmd cmd1, ETriv)
  | (SEIf (cond, Scp stmts')) :: [] ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts' env in
        EIte (cond', ECmd cmd1, ETriv)
  | (SIf (cond, (Scp stmts1))) :: (SElse (Scp stmts2)) :: [] ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts1 env in
        let cmd2 = elab_stmts stmts2 env in
        EIte (cond', ECmd cmd1, ECmd cmd2)
  | (SEIf (cond, (Scp stmts1))) :: (SElse (Scp stmts2)) :: [] ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts1 env in
        let cmd2 = elab_stmts stmts2 env in
        EIte (cond', ECmd cmd1, ECmd cmd2)
  | (SIf (cond, (Scp stmts1))) :: stmts' ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts1 env in
        let stmts'' = elab_ite stmts' env in
        EIte (cond', ECmd cmd1, stmts'')
  | (SEIf (cond, (Scp stmts1))) :: stmts' ->
        let cond' = elab_exp cond in
        let cmd1 = elab_stmts stmts1 env in
        let stmts'' = elab_ite stmts' env in
        EIte (cond', ECmd cmd1, stmts'')
  | _ -> failwith ("Unexpected case in ITE translation")





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
    let out_prog = elab in_prog Strmap.empty in
    print_string ("[Input abstract syntax]\n\n"^
                  (fun x -> ShowQSharp.show (ShowQSharp.showDoc x)) in_prog ^ "\n\n");
    print_string ("[Output abstract syntax]\n\n"^
                  (fun x -> ShowLambdaQs.show (ShowLambdaQs.showCmd x)) out_prog ^ "\n\n")
;;

elab_example ();;
