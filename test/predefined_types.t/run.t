A type of the language may not have the name of a predefined OCaml type: the
generated types would define a cyclic abbreviation (`type string = string`), or
hide the type that they use (`t list`).

  $ cat > lang.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > type string [@ocaml "string"] [@lean "String"]
  > KN
  $ kanon ocaml out lang.knl && cat out/Generated/types.ml
  lang.knl:3:5: string is a predefined OCaml type
  [1]
  $ cat > lang.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > type list = Nil | Cons
  > KN
  $ kanon ocaml out lang.knl && cat out/Generated/types.ml
  lang.knl:3:5: list is a predefined OCaml type
  [1]
