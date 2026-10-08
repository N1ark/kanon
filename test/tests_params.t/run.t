The parameters of a rule may have any name, even that of the source of random
values in the output of `tests.ml`: it compiles.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > [@@@ocaml_rules "R"]
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
  > rule plus : Plus (src, dst) =
  >   | same: src + src -> dst
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/*.ml .
  $ ocamlfind ocamlc -package zarith -c t.ml r.ml tests.ml 2>&1 | grep -A3 Error || true
