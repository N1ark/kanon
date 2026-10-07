The parameters of a rule may have any name, even that of the source of random
values in the output of `ocaml-tests`: it compiles.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
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
  $ kanon ocaml-types lang.knl > t.ml
  $ kanon ocaml lang.knl > r.ml
  $ (echo "open R"; kanon ocaml-tests lang.knl) > tests.ml
  $ ocamlfind ocamlc -package zarith -c t.ml r.ml tests.ml 2>&1 | grep -A3 Error || true
