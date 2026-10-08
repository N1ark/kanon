The output of `tests.ml` is included where the modules of the rules are
open. A module named like an OCaml one (`Int`) does not hide what the tests use
of it: a repeated variable compares the tags of terms.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > [@@@ocaml_rules "R"]
  > use "int"
  > KN
  $ cat > int.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Plus : TInt -> TInt -> TInt
  > infix "+" = Plus, plus
  > KN
  $ cat > int.kn <<'KN'
  > rule plus : Plus (v1, v2) =
  >   | same: x + x -> x
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/*.ml .
  $ ocamlfind ocamlc -package zarith -c t.ml r.ml tests.ml 2>&1 | grep -A1 Error || true
