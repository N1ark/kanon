The inequality of two terms compiles: it is the negation of the equality of
their tags.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Ne_types"]
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > node Add : TInt -> TInt -> TInt
  > KN
  $ cat > rules.kn <<'KN'
  > rule add : Add (v1, v2) =
  >   | diff: x, y when x <> y -> x
  > KN
  $ kanon ocaml-types lang.knl > ne_types.ml
  $ kanon ocaml lang.knl > ne_rules.ml
  $ ocamlfind ocamlc -package zarith -c ne_types.ml ne_rules.ml
