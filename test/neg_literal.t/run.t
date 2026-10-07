The negation of a negative literal is a positive literal, in expressions and in
patterns, and the generated OCaml computes it.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > KN
  $ cat > rules.kn <<'KN'
  > fn add (x : int) : int = x + -(-5)
  > fn is_five (x : int) : int = match x with | -(-5) -> 1 | _ -> 0
  > KN
  $ kanon ocaml-types lang.knl > t.ml
  $ kanon ocaml lang.knl > r.ml
  $ cat > main.ml <<'ML'
  > let () =
  >   Printf.printf "%s %d %d\n"
  >     (Z.to_string (R.Kanon_flat.rules_add (Z.of_int 1)))
  >     (Z.to_int (R.Kanon_flat.rules_is_five (Z.of_int 5)))
  >     (Z.to_int (R.Kanon_flat.rules_is_five (Z.of_int (-5))))
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml r.ml main.ml -o main.exe 2>&1 | head -5
  $ ./main.exe
  6 1 0
