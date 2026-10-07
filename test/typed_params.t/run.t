The parameters of a rule function that are written in another order than those
of its spec keep their order in the typed interface: it compiles.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "P_types"]
  > [@@@ocaml_rules "P_rules"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Scale of int : TInt -> TInt
  > KN
  $ cat > m.kn <<'KN'
  > rule scale (v : t) (k : int) : Scale (k, v) =
  >   | one: _ when k = 1 -> v
  > KN
  $ kanon ocaml-types lang.knl > p_types.ml
  $ kanon ocaml lang.knl > p_rules.ml
  $ kanon ocaml-typed lang.knl > p_typed.ml
  $ ocamlfind ocamlc -package zarith -c p_types.ml p_rules.ml p_typed.ml 2>&1 | grep -A8 Error || true
