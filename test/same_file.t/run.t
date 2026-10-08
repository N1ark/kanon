A file that is given on the command line and used by a module is loaded once,
whichever way its path is written.

  $ cat > lang.knl <<'KN'
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Plus : TInt -> TInt -> TInt [@comm]
  > infix "+" = Plus, plus
  > KN
  $ cat > m.kn <<'KN'
  > rule plus : Plus (v1, v2) =
  >   | zero: 0, x -> x
  > KN
  $ kanon ocaml out lang.knl m.kn
  $ kanon ocaml out lang.knl ./m.kn
  $ kanon ocaml out lang.knl "$PWD/m.kn"
  $ mkdir dir
  $ kanon ocaml out lang.knl dir/../m.kn
