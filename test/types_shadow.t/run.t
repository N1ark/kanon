The generated types call the standard library as `Stdlib.Int`, so that a module
of the program that has the name of one of its modules (here `Int` and
`Hashtbl`, opened by the library that includes the types) does not hide it.

  $ cat > lang.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > type var [@ocaml "string"] [@lean "String"]
  > node Var of var
  > node Neg : TInt -> TInt
  > KN
  $ touch lang.kn
  $ kanon ocaml out lang.knl lang.kn && cp out/Generated/types.ml t.ml
  $ cat > shadow.ml <<'ML'
  > module Int = struct let equal _ _ = 0 end
  > module Hashtbl = struct let hash _ = true end
  > ML
  $ ocamlfind ocamlc -package zarith -c shadow.ml
  $ ocamlfind ocamlc -package zarith -open Shadow -c t.ml 2>&1 | grep -A2 Error || true
