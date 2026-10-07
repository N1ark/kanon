The sort variables of a typing may have primes, even a single letter with
one: the typed interface compiles.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "P_types"]
  > [@@@ocaml_rules "P_rules"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TBool
  > node Eq2 : a' -> a' -> TBool
  > KN
  $ cat > m.kn <<'KN'
  > rule eq2 : Eq2 (x, y) =
  >   | same: x, x -> Eq2 (x, x)
  > KN
  $ kanon ocaml-types lang.knl > p_types.ml
  $ kanon ocaml lang.knl > p_rules.ml
  $ kanon ocaml-typed lang.knl > p_typed.ml
  $ ocamlfind ocamlc -package zarith -c p_types.ml p_rules.ml p_typed.ml
