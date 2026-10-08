The traversals of a type `x` over sorts and those of a type `ty_x` over terms
have different names, and the generated OCaml compiles.

  $ cat > lang.knl <<'KN'
  > [@@@traversals]
  > [@@@ocaml_types "T"]
  > use "m"
  > type ty_x = A of t
  > type x = B of ty
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node N of ty_x : TInt
  > sort S of x
  > KN
  $ cat > m.knl <<'KN'
  > KN
  $ cat > m.kn <<'KN'
  > fn f (x : int) : int = x
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/t.ml t.ml && cp out/Generated/rules.ml r.ml
  $ ocamlfind ocamlc -package zarith -w -a -c t.ml r.ml 2>&1 | head -5
