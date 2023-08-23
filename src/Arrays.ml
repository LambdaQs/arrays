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

let applyCNOT_oneelem =
  ELet
    ( MVar (Ident "ApplyCNOT_oneelem")
    , ELam
        ( []
        , [ Param (MVar (Ident "a"), TAbsArr (TQAll (MKVar (Ident "ql0"))))
          ; Param (MVar (Ident "i"), TInt) ]
        , ELet
            ( MVar (Ident "b")
            , EAp
                ( EVar (MVar (Ident "qMost"))
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
                                  , CrIdx (CrArg 0, CrExi (Ident "i")) ) ) ) ]
                    )
                , [ Arg
                      ( EVar (MVar (Ident "a"))
                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
            , TAbsArr (TQAll (MKVar (Ident "ql0")))
            , ELet
                ( MVar (Ident "c")
                , EAp
                    ( EVar (MVar (Ident "qRest"))
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
                                      , CrIdx
                                          ( CrArg 0
                                          , CrAdd (CrExi (Ident "i"), CrInt 1)
                                          ) ) ) ) ] )
                    , [ Arg
                          ( EVar (MVar (Ident "a"))
                          , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
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
                        , [ Arg
                              ( EArrIdx
                                  ( TQAll (MKVar (Ident "ql0"))
                                  , EVar (MVar (Ident "b"))
                                  , EVar (MVar (Ident "i")) )
                              , TQAll (MKVar (Ident "ql0")) )
                          ; Arg
                              ( EArrIdx
                                  ( TQAll (MKVar (Ident "ql0"))
                                  , EVar (MVar (Ident "c"))
                                  , EVar (MVar (Ident "i")) )
                              , TQAll (MKVar (Ident "ql0")) ) ] )
                    , TUnit
                    , ETriv
                    , TUnit )
                , TUnit )
            , TUnit )
        , TUnit )
    , TFun ([], [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt], TUnit, [], [])
    , ETriv
    , TUnit )

let applyCNOTchain =
  ELet
    ( MVar (Ident "ApplyCNOTchain")
    , ELam
        ( []
        , [Param (MVar (Ident "a"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , ELet
            ( MVar (Ident "b")
            , EAp
                ( EVar (MVar (Ident "qMost"))
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
                                  , CrIdx (CrArg 0, CrExi (Ident "i")) ) ) ) ]
                    )
                , [ Arg
                      ( EVar (MVar (Ident "a"))
                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
            , TAbsArr (TQAll (MKVar (Ident "ql0")))
            , ELet
                ( MVar (Ident "c")
                , EAp
                    ( EVar (MVar (Ident "qRest"))
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
                                      , CrIdx
                                          ( CrArg 0
                                          , CrAdd (CrExi (Ident "i"), CrInt 1)
                                          ) ) ) ) ] )
                    , [ Arg
                          ( EVar (MVar (Ident "a"))
                          , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
                , TAbsArr (TQAll (MKVar (Ident "ql0")))
                , EFor
                    ( MVar (Ident "idxQubit")
                    , ERng
                        ( EInt 0
                        , ESub (EArrLen (EVar (MVar (Ident "a"))), EInt 1) )
                    , ELet
                        ( MVar (Ident "_wild_")
                        , EAp
                            ( EVar (MVar (Ident "CNOT"))
                            , TFun
                                ( []
                                , [ TQAll (MKVar (Ident "0"))
                                  ; TQAll (MKVar (Ident "1")) ]
                                , TUnit
                                , [CrNeq (CrArg 0, CrArg 1)]
                                , [] )
                            , [ Arg
                                  ( EArrIdx
                                      ( TQAll (MKVar (Ident "ql0"))
                                      , EVar (MVar (Ident "b"))
                                      , EVar (MVar (Ident "idxQubit")) )
                                  , TQAll (MKVar (Ident "ql0")) )
                              ; Arg
                                  ( EArrIdx
                                      ( TQAll (MKVar (Ident "ql0"))
                                      , EVar (MVar (Ident "c"))
                                      , EVar (MVar (Ident "idxQubit")) )
                                  , TQAll (MKVar (Ident "ql0")) ) ] )
                        , TUnit
                        , ETriv
                        , TUnit )
                    , ETriv
                    , TUnit )
                , TUnit )
            , TUnit )
        , TUnit )
    , TFun ([], [TAbsArr (TQAll (MKVar (Ident "ql0")))], TUnit, [], [])
    , ETriv
    , TUnit )

let textlist =
  [ CrNeq
      ( CrIdx (CrApp (MVar (Ident "qMost"), [CrArg 0]), CrArg 1)
      , CrIdx (CrApp (MVar (Ident "qRest"), [CrArg 0]), CrArg 1) ) ]

let testlist2 =
  [ Funcdef
      ( MVar (Ident "ApplyCNOT_oneelem")
      , Funcexp
          ( []
          , [ Param (MVar (Ident "a"), TAbsArr (TQAll (MKVar (Ident "ql0"))))
            ; Param (MVar (Ident "i"), TInt) ]
          , ELet
              ( MVar (Ident "b")
              , EAp
                  ( EVar (MVar (Ident "qMost"))
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
                                    , CrIdx (CrArg 0, CrExi (Ident "i")) ) ) )
                        ] )
                  , [ Arg
                        ( EVar (MVar (Ident "a"))
                        , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
              , TAbsArr (TQAll (MKVar (Ident "ql0")))
              , ELet
                  ( MVar (Ident "c")
                  , EAp
                      ( EVar (MVar (Ident "qRest"))
                      , TFun
                          ( []
                          , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                          , TAbsArr (TQAll (MKVar (Ident "ql0")))
                          , [CrGt (CrLen (CrArg 0), CrInt 0)]
                          , [ CrEq
                                (CrLen CrRet, CrSub (CrLen (CrArg 0), CrInt 1))
                            ; CrForall
                                ( Ident "i"
                                , CrImp
                                    ( CrAnd
                                        ( CrGe (CrExi (Ident "i"), CrInt 0)
                                        , CrLt (CrExi (Ident "i"), CrLen CrRet)
                                        )
                                    , CrEq
                                        ( CrIdx (CrRet, CrExi (Ident "i"))
                                        , CrIdx
                                            ( CrArg 0
                                            , CrAdd (CrExi (Ident "i"), CrInt 1)
                                            ) ) ) ) ] )
                      , [ Arg
                            ( EVar (MVar (Ident "a"))
                            , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
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
                              , [CrNeq (CrArg 0, CrArg 1)]
                              , [] )
                          , [ Arg
                                ( EArrIdx
                                    ( TQAll (MKVar (Ident "ql0"))
                                    , EVar (MVar (Ident "b"))
                                    , EVar (MVar (Ident "i")) )
                                , TQAll (MKVar (Ident "ql0")) )
                            ; Arg
                                ( EArrIdx
                                    ( TQAll (MKVar (Ident "ql0"))
                                    , EVar (MVar (Ident "c"))
                                    , EVar (MVar (Ident "i")) )
                                , TQAll (MKVar (Ident "ql0")) ) ] )
                      , TUnit
                      , ETriv
                      , TUnit )
                  , TUnit )
              , TUnit )
          , TUnit )
      , Functyp
          ([], [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt], TUnit, [], []) )
  ]
