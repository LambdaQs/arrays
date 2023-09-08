open AbsLambdaQs

(* some helpers *)

let get_func_name (func : exp) : string =
  match func with
  | ELet (MVar (Ident v), _, _, _, _) ->
      v
  | _ ->
      failwith "non let case"

let get_func_exp (func : exp) : exp =
  match func with ELet (_, fex, _, _, _) -> fex | _ -> failwith "non let case"

let get_func_type (func : exp) : typ =
  match func with ELet (_, _, fty, _, _) -> fty | _ -> failwith "non let case"

(********************)
(* actual functions *)
(********************)

let x_gate =
  ELet
    ( MVar (Ident "X")
    , ELam
        ( []
        , [Param (MVar (Ident "qubit"), TQAll (MKVar (Ident "0")))]
        , ECmd (TUnit, CGap (MUni (Ident "X"), EVar (MVar (Ident "qubit"))))
        , TUnit )
    , TFun ([], [TQAll (MKVar (Ident "0"))], TUnit, [], [])
    , ETriv
    , TUnit )

let cnot =
  ELet
    ( MVar (Ident "CNOT")
    , ELam
        ( []
        , [ Param (MVar (Ident "control"), TQAll (MKVar (Ident "0")))
          ; Param (MVar (Ident "target"), TQAll (MKVar (Ident "1"))) ]
        , ELet
            (* FIXME: get rid of wild here by changing Elab.ml *)
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
        , [CrNeq (CrArg 0, CrArg 1)]
        , [] )
    , ETriv
    , TUnit )

let qMost =
  ELet
    ( MVar (Ident "qMost")
    , ELam
        ( []
        , [Param (MVar (Ident "array"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , EArrIdx
            ( TAbsArr (TQAll (MKVar (Ident "ql0")))
            , EVar (MVar (Ident "array"))
            , ERngL (ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 2)) )
        , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
    , TFun
        ( []
        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
        , TAbsArr (TQAll (MKVar (Ident "ql0")))
        , [CrGt (CrLen (CrArg 0), CrInt 0)]
        , [ CrEq (CrLen CrRet, CrSub (CrLen (CrArg 0), CrInt 1))
          ; CrForall
              ( Ident "i"
              , CrImp
                  ( CrAnd
                      ( CrGe (CrExi (Ident "i"), CrInt 0)
                      , CrLt (CrExi (Ident "i"), CrLen CrRet) )
                  , CrEq
                      ( CrIdx (CrRet, CrExi (Ident "i"))
                      , CrIdx (CrArg 0, CrExi (Ident "i")) ) ) ) ] )
    , ETriv
    , TUnit )

let qRest =
  ELet
    ( MVar (Ident "qRest")
    , ELam
        ( []
        , [Param (MVar (Ident "array"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , EArrIdx
            ( TAbsArr (TQAll (MKVar (Ident "ql0")))
            , EVar (MVar (Ident "array"))
            , ERngR (EInt 1) )
        , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
    , TFun
        ( []
        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
        , TAbsArr (TQAll (MKVar (Ident "ql0")))
        , [CrGt (CrLen (CrArg 0), CrInt 0)]
        , [ CrEq (CrLen CrRet, CrSub (CrLen (CrArg 0), CrInt 1))
          ; CrForall
              ( Ident "i"
              , CrImp
                  ( CrAnd
                      ( CrGe (CrExi (Ident "i"), CrInt 0)
                      , CrLt (CrExi (Ident "i"), CrLen CrRet) )
                  , CrEq
                      ( CrIdx (CrRet, CrExi (Ident "i"))
                      , CrIdx (CrArg 0, CrAdd (CrExi (Ident "i"), CrInt 1)) ) )
              ) ] )
    , ETriv
    , TUnit )

let qRev =
  ELet
    ( MVar (Ident "qRev")
    , ELam
        ( []
        , [Param (MVar (Ident "array"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , EArrIdx
            ( TAbsArr (TQAll (MKVar (Ident "ql0")))
            , EVar (MVar (Ident "array"))
            , ERng (ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 1), EInt 0)
            )
        , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
    , TFun
        ( []
        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
        , TAbsArr (TQAll (MKVar (Ident "ql0")))
        , []
        , [ CrEq (CrLen CrRet, CrLen (CrArg 0))
          ; CrForall
              ( Ident "i"
              , CrImp
                  ( CrAnd
                      ( CrGe (CrExi (Ident "i"), CrInt 0)
                      , CrLt (CrExi (Ident "i"), CrLen CrRet) )
                  , CrEq
                      ( CrIdx (CrRet, CrExi (Ident "i"))
                      , CrIdx
                          ( CrArg 0
                          , CrSub
                              ( CrSub (CrLen (CrArg 0), CrInt 1)
                              , CrExi (Ident "i") ) ) ) ) ) ] )
    , ETriv
    , TUnit )

let qTail =
  ELet
    ( MVar (Ident "qTail")
    , ELam
        ( []
        , [Param (MVar (Ident "array"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , EArrIdx
            ( TQAll (MKVar (Ident "ql0"))
            , EVar (MVar (Ident "array"))
            , ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 1) )
        , TQAll (MKVar (Ident "ql0")) )
    , TFun
        ( []
        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
        , TQAll (MKVar (Ident "ql0"))
        , []
        , [CrEq (CrRet, CrIdx (CrArg 0, CrSub (CrLen (CrArg 0), CrInt 1)))] )
    , ETriv
    , TUnit )

let qApplyToEachZip =
  ELet
    ( MVar (Ident "qApplyToEachZip")
    , ELam
        ( []
        , [ Param
              ( MVar (Ident "doubleElemOp")
              , TFun
                  ( []
                  , [TQAll (MKVar (Ident "in0")); TQAll (MKVar (Ident "in1"))]
                  , TUnit
                  , []
                  , [] ) )
          ; Param (MVar (Ident "qs1"), TAbsArr (TQAll (MKVar (Ident "ql0"))))
          ; Param (MVar (Ident "qs2"), TAbsArr (TQAll (MKVar (Ident "ql1")))) ]
        , EFor
            ( MVar (Ident "idxQubit")
            , ERng (EInt 0, ESub (EArrLen (EVar (MVar (Ident "qs1"))), EInt 1))
            , ELet
                ( MVar (Ident "_wild_")
                , EAp
                    ( EVar (MVar (Ident "doubleElemOp"))
                    , TFun
                        ( []
                        , [ TQAll (MKVar (Ident "in0"))
                          ; TQAll (MKVar (Ident "in1")) ]
                        , TUnit
                        , []
                        , [] )
                    , [ Arg
                          ( EArrIdx
                              ( TQAll (MKVar (Ident "ql0"))
                              , EVar (MVar (Ident "qs1"))
                              , EVar (MVar (Ident "idxQubit")) )
                          , TQAll (MKVar (Ident "ql0")) )
                      ; Arg
                          ( EArrIdx
                              ( TQAll (MKVar (Ident "ql1"))
                              , EVar (MVar (Ident "qs2"))
                              , EVar (MVar (Ident "idxQubit")) )
                          , TQAll (MKVar (Ident "ql1")) ) ] )
                , TUnit
                , ETriv
                , TUnit )
            , ETriv
            , TUnit )
        , TUnit )
    , TFun
        ( []
        , [ TFun
              ( []
              , [TQAll (MKVar (Ident "in0")); TQAll (MKVar (Ident "in1"))]
              , TUnit
              , []
              , [] )
          ; TAbsArr (TQAll (MKVar (Ident "ql0")))
          ; TAbsArr (TQAll (MKVar (Ident "ql1"))) ]
        , TUnit
        , [ CrForall
              ( Ident "idxQubit"
              , CrImp
                  ( CrAnd
                      ( CrGe (CrExi (Ident "idxQubit"), CrInt 0)
                      , CrLt
                          ( CrExi (Ident "idxQubit")
                          , CrSub (CrLen (CrArg 1), CrInt 1) ) )
                  , CrSatCons
                      ( CrArg 0
                      , [ CrIdx (CrArg 1, CrExi (Ident "idxQubit"))
                        ; CrIdx (CrArg 2, CrExi (Ident "idxQubit")) ] ) ) ) ]
        , [] )
    , ETriv
    , TUnit )
