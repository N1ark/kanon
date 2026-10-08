The generated OCaml enables the warning on unused match cases, which a build
that makes warnings errors (the dune dev profile) fails on: the default case
that Kanon adds to a rule is left out when an earlier case matches anything,
even if it is not written `_`, such as a pair of variables.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Minus : TInt -> TInt -> TInt
  > infix "-" = Minus, minus
  > KN
  $ cat > m.kn <<'KN'
  > rule minus : Minus (v1, v2) =
  >   | zero: x, 0 -> x
  >   | other: x, y -> y
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/t.ml t.ml && cp out/Generated/rules.ml r.ml
  $ ocamlfind ocamlc -package zarith -warn-error +11 -c t.ml r.ml 2>&1 | grep -B3 Error || true
