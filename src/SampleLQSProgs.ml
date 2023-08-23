open AbsLambdaQs








let length_of_exp a = CrApp (MVar (Ident "length"), a)

let basic_int_prog =
  ELet
    ( MVar (Ident "run_if_eq")
    , ELam
        ( []
        , [Param (MVar (Ident "aa"), TInt); Param (MVar (Ident "bb"), TInt)]
        , ETriv
        , TUnit )
    , TFun ([], [TInt; TInt], TUnit, [CrEq (CrArg 0, CrArg 1)], [])
    , ELet
        ( MVar (Ident "run_if_neq")
        , ELam
            ( []
            , [Param (MVar (Ident "aa"), TInt); Param (MVar (Ident "bb"), TInt)]
            , ETriv
            , TUnit )
        , TFun ([], [TInt; TInt], TUnit, [CrNeq (CrArg 0, CrArg 1)], [])
        , ELet
            ( MVar (Ident "add_three")
            , ELam
                ( []
                , [Param (MVar (Ident "a"), TInt)]
                , EAdd (EVar (MVar (Ident "a")), EInt 3)
                , TInt )
            , TFun
                ([], [TInt], TInt, [], [CrEq (CrRet, CrAdd (CrArg 0, CrInt 3))])
            , ELet
                ( MVar (Ident "sub_two")
                , ELam
                    ( []
                    , [Param (MVar (Ident "b"), TInt)]
                    , ESub (EVar (MVar (Ident "b")), EInt 2)
                    , TInt )
                , TFun
                    ( []
                    , [TInt]
                    , TInt
                    , []
                    , [CrEq (CrRet, CrSub (CrArg 0, CrInt 2))] )
                , ELet
                    ( MVar (Ident "main")
                    , ELam
                        ( []
                        , [Param (MVar (Ident "c"), TInt)]
                        , ELet
                            ( MVar (Ident "d")
                            , EAp
                                ( EVar (MVar (Ident "add_three"))
                                , TFun
                                    ( []
                                    , [TInt]
                                    , TInt
                                    , []
                                    , [CrEq (CrRet, CrAdd (CrArg 0, CrInt 3))]
                                    )
                                , [Arg (EVar (MVar (Ident "c")), TInt)] )
                            , TInt
                            , ELet
                                ( MVar (Ident "e")
                                , EAp
                                    ( EVar (MVar (Ident "sub_two"))
                                    , TFun
                                        ( []
                                        , [TInt]
                                        , TInt
                                        , []
                                        , [ CrEq
                                              (CrRet, CrSub (CrArg 0, CrInt 2))
                                          ] )
                                    , [Arg (EVar (MVar (Ident "c")), TInt)] )
                                , TInt
                                , ELet
                                    ( MVar (Ident "_wild_")
                                    , EAp
                                        ( EVar (MVar (Ident "run_if_neq"))
                                        , TFun
                                            ( []
                                            , [TInt; TInt]
                                            , TUnit
                                            , [CrNeq (CrArg 0, CrArg 1)]
                                            , [] )
                                        , [ Arg (EVar (MVar (Ident "d")), TInt)
                                          ; Arg (EVar (MVar (Ident "e")), TInt)
                                          ] )
                                    , TUnit
                                    , ETriv
                                    , TUnit )
                                , TUnit )
                            , TUnit )
                        , TUnit )
                    , TFun ([], [TInt], TUnit, [], [])
                    , ETriv
                    , TUnit )
                , TUnit )
            , TUnit )
        , TUnit )
    , TUnit )

let mostrest =
  ELet
    ( MVar (Ident "X")
    , ELam
        ( []
        , [Param (MVar (Ident "qubit"), TQAll (MKVar (Ident "0")))]
        , ETriv
        , TUnit )
    , TFun ([], [TQAll (MKVar (Ident "0"))], TUnit, [], [])
    , ELet
        ( MVar (Ident "CNOT")
        , ELam
            ( []
            , [ Param (MVar (Ident "control"), TQAll (MKVar (Ident "0")))
              ; Param (MVar (Ident "target"), TQAll (MKVar (Ident "1"))) ]
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
            , [CrNeq (CrArg 0, CrArg 1)]
            , [] )
        , ELet
            ( MVar (Ident "qMost")
            , ELam
                ( []
                , [ Param
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
                , [CrGt (length_of_exp (CrArg 0), CrInt 0)]
                , [ CrBool (EVar (MVar (Ident "SKIP_ENS")))
                  ; CrEq
                      ( length_of_exp CrRet
                      , CrSub (length_of_exp (CrArg 0), CrInt 1) )
                  ; CrForall
                      ( Ident "i"
                      , CrImp
                          ( CrAnd
                              ( CrGe (CrExi (Ident "i"), CrInt 0)
                              , CrLt (CrExi (Ident "i"), length_of_exp CrRet) )
                          , CrEq
                              ( CrInd (CrRet, CrExi (Ident "i"))
                              , CrInd (CrArg 0, CrExi (Ident "i")) ) ) ) ] )
            , ELet
                ( MVar (Ident "qRest")
                , ELam
                    ( []
                    , [ Param
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
                    , [CrGt (EArrLen (CrArg 0), EInt 0)]
                    , [ CrBool (EVar (MVar (Ident "SKIP_ENS")))
                      ; CrEq (EArrLen CrRet, ESub (EArrLen (CrArg 0), EInt 1))
                      ; CForall
                          ( MVar (Ident "i")
                          , CImp
                              ( CAnd
                                  ( CGe (EVar (MVar (Ident "i")), EInt 0)
                                  , CLt (EVar (MVar (Ident "i")), EArrLen CrRet)
                                  )
                              , CrEq
                                  ( EArrIdx
                                      ( TQAll (MKVar (Ident "ql0"))
                                      , CrRet
                                      , EVar (MVar (Ident "i")) )
                                  , EArrIdx
                                      ( TQAll (MKVar (Ident "ql0"))
                                      , CrArg 0
                                      , EAdd (EVar (MVar (Ident "i")), EInt 1)
                                      ) ) ) ) ] )
                , ELet
                    ( MVar (Ident "ApplyCNOT_oneelem")
                    , ELam
                        ( []
                        , [ Param
                              ( MVar (Ident "a")
                              , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
                          ; Param (MVar (Ident "i"), TInt) ]
                        , ELet
                            ( MVar (Ident "b")
                            , EAp
                                ( EVar (MVar (Ident "qMost"))
                                , TFun
                                    ( []
                                    , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                                    , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                    , [CGt (EArrLen (CrArg 0), EInt 0)]
                                    , [ CBool (EVar (MVar (Ident "SKIP_ENS")))
                                      ; CrEq
                                          ( EArrLen CrRet
                                          , ESub (EArrLen (CrArg 0), EInt 1) )
                                      ; CForall
                                          ( MVar (Ident "i")
                                          , CImp
                                              ( CAnd
                                                  ( CGe
                                                      ( EVar (MVar (Ident "i"))
                                                      , EInt 0 )
                                                  , CLt
                                                      ( EVar (MVar (Ident "i"))
                                                      , EArrLen
                                                          (EVar
                                                             (MVar (Ident "RET"))
                                                          ) ) )
                                              , CrEq
                                                  ( EArrIdx
                                                      ( TQAll
                                                          (MKVar (Ident "ql0"))
                                                      , CrArg 0
                                                      , EVar (MVar (Ident "i"))
                                                      )
                                                  , EArrIdx
                                                      ( TQAll
                                                          (MKVar (Ident "ql0"))
                                                      , CrRet
                                                      , EVar (MVar (Ident "i"))
                                                      ) ) ) ) ] )
                                , [ Arg
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
                                        , [CGt (EArrLen (CrArg 0), EInt 0)]
                                        , [ CBool
                                              (EVar (MVar (Ident "SKIP_ENS")))
                                          ; CrEq
                                              ( EArrLen CrRet
                                              , ESub (EArrLen (CrArg 0), EInt 1)
                                              )
                                          ; CForall
                                              ( MVar (Ident "i")
                                              , CImp
                                                  ( CAnd
                                                      ( CGe
                                                          ( EVar
                                                              (MVar (Ident "i"))
                                                          , EInt 0 )
                                                      , CLt
                                                          ( EVar
                                                              (MVar (Ident "i"))
                                                          , EArrLen
                                                              (EVar
                                                                 (MVar
                                                                    (Ident "RET")
                                                                 ) ) ) )
                                                  , CrEq
                                                      ( EArrIdx
                                                          ( TQAll
                                                              (MKVar
                                                                 (Ident "ql0")
                                                              )
                                                          , EVar
                                                              (MVar (Ident "RET")
                                                              )
                                                          , EVar
                                                              (MVar (Ident "i"))
                                                          )
                                                      , EArrIdx
                                                          ( TQAll
                                                              (MKVar
                                                                 (Ident "ql0")
                                                              )
                                                          , CrArg 0
                                                          , EAdd
                                                              ( EVar
                                                                  (MVar
                                                                     (Ident "i")
                                                                  )
                                                              , EInt 1 ) ) ) )
                                              ) ] )
                                    , [ Arg
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
                                            , [CNeq (CrArg 0, CrArg 1)]
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
                        , [ CGt (EArrLen (CrArg 0), EInt 0)
                          ; CAnd
                              ( CGe (CrArg 1, EInt 0)
                              , CLt (CrArg 1, ESub (EArrLen (CrArg 0), EInt 1))
                              )
                          ; CBool
                              (EAp
                                 ( EVar (MVar (Ident "is_range"))
                                 , TInt
                                 , [ Arg
                                       ( CrArg 0
                                       , TAbsArr (TQAll (MKVar (Ident "ql0")))
                                       ) ] ) ) ]
                        , [] )
                    , ETriv
                    , TUnit )
                , TUnit )
            , TUnit )
        , TUnit )
    , TUnit )

let idrev =
  ELet
    ( MVar (Ident "X")
    , ELam
        ( []
        , [Param (MVar (Ident "qubit"), TQAll (MKVar (Ident "0")))]
        , ETriv
        , TUnit )
    , TFun ([], [TQAll (MKVar (Ident "0"))], TUnit, [], [])
    , ELet
        ( MVar (Ident "CNOT")
        , ELam
            ( []
            , [ Param (MVar (Ident "control"), TQAll (MKVar (Ident "0")))
              ; Param (MVar (Ident "target"), TQAll (MKVar (Ident "1"))) ]
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
            , [CNeq (CrArg 0, CrArg 1)]
            , [] )
        , ELet
            ( MVar (Ident "qRev")
            , ELam
                ( []
                , [ Param
                      ( MVar (Ident "array")
                      , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                , EArrIdx
                    ( TAbsArr (TQAll (MKVar (Ident "ql0")))
                    , EVar (MVar (Ident "array"))
                    , ERng
                        ( ESub (EArrLen (EVar (MVar (Ident "array"))), EInt 1)
                        , EInt 0 ) )
                , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
            , TFun
                ( []
                , [TAbsArr (TQAll (MKVar (Ident "ql0")))]
                , TAbsArr (TQAll (MKVar (Ident "ql0")))
                , []
                , [ CBool (EVar (MVar (Ident "SKIP_ENS")))
                  ; CrEq (EArrLen CrRet, EArrLen (CrArg 0))
                  ; CForall
                      ( MVar (Ident "i")
                      , CImp
                          ( CAnd
                              ( CGe (EVar (MVar (Ident "i")), EInt 0)
                              , CLt (EVar (MVar (Ident "i")), EArrLen CrRet) )
                          , CrEq
                              ( EArrIdx
                                  ( TQAll (MKVar (Ident "ql0"))
                                  , CrRet
                                  , EVar (MVar (Ident "i")) )
                              , EArrIdx
                                  ( TQAll (MKVar (Ident "ql0"))
                                  , CrArg 0
                                  , ESub
                                      ( ESub (EArrLen (CrArg 0), EInt 1)
                                      , EVar (MVar (Ident "i")) ) ) ) ) ) ] )
            , ELet
                ( MVar (Ident "ApplyCNOT_oneelem")
                , ELam
                    ( []
                    , [ Param
                          ( MVar (Ident "a")
                          , TAbsArr (TQAll (MKVar (Ident "ql0"))) )
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
                                , [ CBool (EVar (MVar (Ident "SKIP_ENS")))
                                  ; CrEq (EArrLen CrRet, EArrLen (CrArg 0))
                                  ; CForall
                                      ( MVar (Ident "i")
                                      , CImp
                                          ( CAnd
                                              ( CGe
                                                  ( EVar (MVar (Ident "i"))
                                                  , EInt 0 )
                                              , CLt
                                                  ( EVar (MVar (Ident "i"))
                                                  , EArrLen CrRet ) )
                                          , CrEq
                                              ( EArrIdx
                                                  ( TQAll (MKVar (Ident "ql0"))
                                                  , CrRet
                                                  , EVar (MVar (Ident "i")) )
                                              , EArrIdx
                                                  ( TQAll (MKVar (Ident "ql0"))
                                                  , CrArg 0
                                                  , ESub
                                                      ( ESub
                                                          ( EArrLen (CrArg 0)
                                                          , EInt 1 )
                                                      , EVar (MVar (Ident "i"))
                                                      ) ) ) ) ) ] )
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
                                    , [CNeq (CrArg 0, CrArg 1)]
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
                , TFun
                    ( []
                    , [TAbsArr (TQAll (MKVar (Ident "ql0"))); TInt]
                    , TUnit
                    , [ CrEq (EMod (EArrLen (CrArg 0), EInt 2), EInt 0)
                      ; CAnd
                          ( CGe (CrArg 1, EInt 0)
                          , CLt (CrArg 1, EArrLen (CrArg 0)) )
                      ; CBool
                          (EAp
                             ( EVar (MVar (Ident "is_range"))
                             , TInt
                             , [ Arg
                                   ( CrArg 0
                                   , TAbsArr (TQAll (MKVar (Ident "ql0"))) ) ]
                             ) ) ]
                    , [] )
                , ETriv
                , TUnit )
            , TUnit )
        , TUnit )
    , TUnit )
