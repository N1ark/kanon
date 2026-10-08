The equality of two values of a declared type is the generated `equal_item`, so
a variable of that name would capture it: it is an error, as for the equality
of terms, `equal_t`, and that of the types of terms, `equal_ty`.

  $ cat > lang2.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "m2"
  > type item = I of int | J
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > KN
  $ cat > m2.knl <<'KN'
  > KN
  $ cat > m2.kn <<'KN'
  > fn g (equal_item : item) (b : item) : bool = equal_item = b
  > KN
  $ kanon ocaml lang2.knl > /dev/null
  ./m2.kn:1:6: equal_item is the OCaml name of the equality of item
  [1]
  $ cat > m2.kn <<'KN'
  > fn g (equal_ty : int) (a b : t) : bool = type_of a = type_of b
  > KN
  $ kanon ocaml lang2.knl > /dev/null
  ./m2.kn:1:6: equal_ty is the OCaml name of the equality of ty
  [1]
  $ cat > m2.kn <<'KN'
  > fn g (equal_t : int) (a b : t) : bool = a = b
  > KN
  $ kanon ocaml lang2.knl > /dev/null
  ./m2.kn:1:6: equal_t is the OCaml name of the equality of t
  [1]
