# Requirements

- [BNF Converter](https://github.com/BNFC/bnfc): `cabal install BNFC`.
- `opam install menhir utop`

# Build and run using:

```
make
./TestLambdaQs
```

The binary lets us enter expressions. Pressing Ctrl-D will parse them and exit the app. One can also pass input through stdin:

```
❯ echo "cmd D(I, X; q1, q2)" | ./TestLambdaQs
[Abstract syntax]

ECmd (CDiag (MUni (Ident "I"), MUni (Ident "X"), EVar (MVar (Ident "q1")), EVar (MVar (Ident "q2"))))

[Linearized tree]

cmd D (I, X;
q1, q2)
```

# Extending the source
`make genclean` will clean up most of the auto-generated files except those by `bnfc`. Write modules assuming the existence of the remaining source files, which include those for the AST, the lexer and the parser specs, the print and show infrastructure, etc.

# Examples from QAlgol (QPL '22):

## Example 3.1

```
cmd new q1 in
ret let q2 be q1 in
cmd D(I, X; q1, q2)
```

## Example 3.2

```
let newQbit be proc(dummy:unit)
  new x in ret x
in ()
```

## WIP example with specification

TODO
