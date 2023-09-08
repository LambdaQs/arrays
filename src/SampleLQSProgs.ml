open AbsLambdaQs

let mostrest_oneelem =
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

let mostrestzip =
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
                        , ESub (EArrLen (EVar (MVar (Ident "a"))), EInt 0) )
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

let rev_oneelem =
  ELet
    ( MVar (Ident "ApplyCNOT_oneelem")
    , ELam
        ( []
        , [ Param (MVar (Ident "a"), TAbsArr (TQAll (MKVar (Ident "ql0"))))
          ; Param (MVar (Ident "i"), TInt) ]
        , ELet
            ( MVar (Ident "b")
            , EAp
                ( EVar (MVar (Ident "qRev"))
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
                        , [TQAll (MKVar (Ident "0")); TQAll (MKVar (Ident "1"))]
                        , TUnit
                        , [CrNeq (CrArg 0, CrArg 1)]
                        , [] )
                    , [ Arg
                          ( EArrIdx
                              ( TQAll (MKVar (Ident "ql0"))
                              , EVar (MVar (Ident "a"))
                              , EVar (MVar (Ident "i")) )
                          , TQAll (MKVar (Ident "ql0")) )
                      ; Arg
                          ( EArrIdx
                              ( TQAll (MKVar (Ident "ql0"))
                              , EVar (MVar (Ident "b"))
                              , EVar (MVar (Ident "i")) )
                          , TQAll (MKVar (Ident "ql0")) ) ] )
                , TUnit
                , ETriv
                , TUnit )
            , TUnit )
        , TUnit )
    , TFun ([], [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt], TUnit, [], [])
    , ETriv
    , TUnit )

let revzip =
  ELet
    ( MVar (Ident "ApplyCNOTchain")
    , ELam
        ( []
        , [Param (MVar (Ident "a"), TAbsArr (TQAll (MKVar (Ident "ql0"))))]
        , ELet
            ( MVar (Ident "b")
            , EAp
                ( EVar (MVar (Ident "qRev"))
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
                , [ Arg
                      ( EVar (MVar (Ident "a"))
                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ] )
            , TAbsArr (TQAll (MKVar (Ident "ql0")))
            , EFor
                ( MVar (Ident "idxQubit")
                , ERng (EInt 0, ESub (EArrLen (EVar (MVar (Ident "a"))), EInt 1))
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
                                  , EVar (MVar (Ident "a"))
                                  , EVar (MVar (Ident "idxQubit")) )
                              , TQAll (MKVar (Ident "ql0")) )
                          ; Arg
                              ( EArrIdx
                                  ( TQAll (MKVar (Ident "ql0"))
                                  , EVar (MVar (Ident "b"))
                                  , EVar (MVar (Ident "idxQubit")) )
                              , TQAll (MKVar (Ident "ql0")) ) ] )
                    , TUnit
                    , ETriv
                    , TUnit )
                , ETriv
                , TUnit )
            , TUnit )
        , TUnit )
    , TFun
        ( []
        , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
        , TUnit
        , []
        , [] )
    , ETriv
    , TUnit )
