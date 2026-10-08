The output of `tests.ml` asserts the sorts of the operands like the rules do,
with the same last case `_`, which is unused when the sorts are all the ones
that it matches: like theirs, it is compiled with the warning off, so that a
build that makes warnings errors (the dune dev profile) accepts it.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > [@@@ocaml_rules "R"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Plus : TInt -> TInt -> TInt
  > infix "+" = Plus, plus
  > KN
  $ cat > m.kn <<'KN'
  > rule plus : Plus (v1, v2) =
  >   | zero: x, 0 -> x
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/*.ml .
  $ ocamlfind ocamlc -package zarith -warn-error +11 -c t.ml r.ml tests.ml 2>&1 | grep -B3 Error || true
