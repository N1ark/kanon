The fields of a record type may be named like those of the terms (`kind`, `ty`
and `tag`): the generated OCaml compiles, and its fields are the record's.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > type info = { kind : bool; ty : int; tag : int }
  > node Neg : TInt -> TInt
  > node Tagged of info : TInt
  > KN
  $ cat > m.kn <<'KN'
  > fn pick (i : info) : int = if i.kind then i.ty else i.tag
  > fn make (n : int) : info = { kind = n < 0; ty = n; tag = n + 1 }
  > fn check (v : t) : int = pick (make (match v with Int n -> n | _ -> 0))
  > rule neg : Neg v =
  >   | neg: Neg x -> x
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/t.ml t.ml && cp out/Generated/rules.ml r.ml
  $ cat > main.ml <<'ML'
  > let () =
  >   let open T in
  >   let int n = node (Int (Z.of_int n)) TInt in
  >   Printf.printf "%s %s\n"
  >     (Z.to_string (R.Kanon_flat.m_check (int (-3))))
  >     (Z.to_string (R.Kanon_flat.m_check (int 4)))
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml r.ml main.ml -o main.exe 2>&1 | head -8
  $ ./main.exe
  -3 5
