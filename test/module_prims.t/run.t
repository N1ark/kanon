The tests call the primitives in the module of `[@@@ocaml_prims]`, with the
rules open: a Kanon module of the same name would hide it, so it is an error.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "prims"
  > KN
  $ cat > prims.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > prims.kn <<'KN'
  > prim zero : t
  > fn is_zero (x : t) : bool = x = zero
  > KN
  $ kanon ocaml out lang.knl
  ./prims.knl:1:5: the module Prims has the name of a module that the generated code uses
  [1]
