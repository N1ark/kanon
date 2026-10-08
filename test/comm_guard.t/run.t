In a rule of a commutative node, a pattern is matched in either order when it
has a guard that may hold of the operands swapped only, such as a symmetric
pattern with a guard on its variables, or variables bound nowhere else that the
guard reads.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Neg : TInt -> TInt
  > node Plus : TInt -> TInt -> TInt [@comm]
  > infix "+" = Plus, plus
  > KN
  $ cat > rules.kn <<'KN'
  > fn is_big (t : t) : bool = match t with | Int z when z > 5 -> true | _ -> false
  > rule plus : Plus (v1, v2) =
  >   | lt: Int x, Int y when x < y -> Int 100
  >   | big: x, y when is_big x -> Int 200
  > fn first_big (t : t) : int =
  >   match t with | Plus (x, y) when is_big x -> 1 | _ -> 0
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/t.ml t.ml && cp out/Generated/rules.ml r.ml
  $ cat > main.ml <<'ML'
  > open T
  > let int n = node (Int (Z.of_int n)) TInt
  > let show (t : t) =
  >   match t.kind with
  >   | Int z -> "Int " ^ Z.to_string z
  >   | Op2 (Plus, _, _) -> "Plus"
  >   | _ -> "?"
  > let neg a = node (Op1 (Neg, a)) TInt
  > let plus a b = show (R.Rules.plus a b)
  > let () =
  >   Printf.printf "%s %s %s %s\n"
  >     (plus (int 1) (int 3)) (plus (int 3) (int 1))
  >     (plus (neg (int 1)) (int 7)) (plus (int 7) (neg (int 1)));
  >   let p a b = node (Op2 (Plus, a, b)) TInt in
  >   Printf.printf "%s %s\n"
  >     (Z.to_string (R.Rules.first_big (p (int 7) (int 1))))
  >     (Z.to_string (R.Rules.first_big (p (int 1) (int 7))))
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml r.ml main.ml -o main.exe 2>&1 | head -8
  $ ./main.exe
  Int 100 Int 100 Int 200 Int 200
  1 1
