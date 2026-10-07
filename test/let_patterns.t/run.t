A `let` pattern is a case of a match: it may have integer literals and repeated
variables, which a failed match refuses, and the generated OCaml compiles.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > KN
  $ cat > rules.kn <<'KN'
  > fn lit (a b : int) : int = let (x, 0) = (a, b) in x
  > fn same (a b : int) : int = let (x, x) = (a, b) in x
  > KN
  $ kanon ocaml-types lang.knl > t.ml
  $ kanon ocaml lang.knl > r.ml
  $ cat > main.ml <<'ML'
  > let show f a b =
  >   match f (Z.of_int a) (Z.of_int b) with
  >   | z -> Z.to_string z
  >   | exception Match_failure _ -> "fail"
  > let () =
  >   Printf.printf "%s %s %s %s\n"
  >     (show R.Kanon_flat.rules_lit 1 0) (show R.Kanon_flat.rules_lit 1 5)
  >     (show R.Kanon_flat.rules_same 3 3) (show R.Kanon_flat.rules_same 3 4)
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml r.ml main.ml -o main.exe 2>&1 | head -8
  $ ./main.exe
  1 fail 3 fail
