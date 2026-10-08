Names that are keywords of OCaml but not of Kanon (`end`, `to`, `val`,
`method`, ...) are names of the generated OCaml too: variables, parameters,
local functions, fields, types, functions and primitives.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > [@@@ocaml_prims "P"]
  > [@@@ocaml_rules "R"]
  > [@@@traversals]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Neg : TInt -> TInt
  > type range = { from' : int; to : int }
  > type val [@ocaml "int"] [@lean "Int"]
  > type span = { lo : t; end : t }
  > node Span of span : TInt
  > KN
  $ cat > m.kn <<'KN'
  > prim private : int -> int
  > fn size (r : range) : int = r.to - r.from'
  > fn mk (lo to : int) : range = { from' = lo; to = to }
  > fn id (x : val) : val = x
  > fn end (to : int) (done : int) : int =
  >   let new (method : int) : int = method + done in
  >   let (val, _) = (to, to) in
  >   match new val with
  >   | include as module -> private include + module
  > rule virtual : Neg open =
  >   | neg: Neg object -> object
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/*.ml .
  $ cat > p.ml <<'ML'
  > let \#private (x : Z.t) = x
  > ML
  $ cat > main.ml <<'ML'
  > let () =
  >   let r = R.Kanon_flat.m_mk (Z.of_int 2) (Z.of_int 9) in
  >   Printf.printf "%s %s %s\n" (Z.to_string r.T.\#to)
  >     (Z.to_string (R.Kanon_flat.m_size r))
  >     (Z.to_string (R.Kanon_flat.m_end (Z.of_int 5) (Z.of_int 1)))
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml p.ml r.ml typed.ml tests.ml main.ml -o main.exe 2>&1 | grep -A3 Error || true
  $ ./main.exe
  9 7 12
