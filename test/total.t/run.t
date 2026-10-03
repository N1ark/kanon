`[@total]` on a `fn`: a per-node function that must have a case for every node
of the language, so that a node without one is an error, not a silent fall
through. It applies once the language is complete, after the cases of every
`extend fn`.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > [@@@ocaml_rules "Rules"]
  > sort TInt
  > type var [@ocaml "string"] [@lean "String"]
  > node Int of int : TInt
  > node Neg : TInt -> TInt
  > node Var of var : TInt
  > node Add : TInt -> TInt -> TInt
  > node Sub : TInt -> TInt -> TInt
  > notation Int
  > infix "+" = Add, add
  > KN

A function with a case for each node passes. The cases may be in an or-pattern,
and bind the operands in any way.

  $ cat > ok.kn <<'KN'
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ | Var _ -> []
  >   | Neg a -> [a]
  >   | a + b -> [a; b]
  >   | Sub (a, b) -> [a; b]
  > KN
  $ kanon ocaml lang.knl ok.kn | grep -A8 "^let operands"
  let operands (v : t) : (t list) =
      (match v with
      | { kind = Int (_); _ } -> []
      | { kind = Var (_); _ } -> []
      | { kind = Op1 ((Neg), a); _ } -> (a :: [])
      | { kind = Op2 ((Add), a, b); _ } -> (a :: (b :: []))
      | { kind = Op2 ((Sub), a, b); _ } -> (a :: (b :: []))
      )
  
  $ for b in ocaml-types ocaml-typed ocaml-tests lean-signatures lean-model lean-statements lean-lifts lean-soundness; do
  >   kanon $b lang.knl ok.kn > /dev/null || echo "$b failed"
  > done

The error lists all the missing nodes, leaves first and then operators, in the
order of their declaration, at the function.

  $ cat > bad.kn <<'KN'
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ -> []
  >   | Neg a -> [a]
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:0: fn operands is [@total] but has no case for Var, Add, Sub
  [1]

A case that matches any term, `_` or a variable, even with a guard, or with
other patterns that are not blanks, is an error.

  $ for last in '_ -> []' 'x -> []' '_ when true -> []' '(Int _ | _) -> []'; do
  >   cat > bad.kn <<KN
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ | Var _ -> []
  >   | $last
  > KN
  >   kanon ocaml lang.knl bad.kn
  > done
  bad.kn:4:4: fn operands is [@total]: it cannot have a catch-all case, which would hide missing nodes: list the nodes
  bad.kn:4:4: fn operands is [@total]: it cannot have a catch-all case, which would hide missing nodes: list the nodes
  bad.kn:4:4: fn operands is [@total]: it cannot have a catch-all case, which would hide missing nodes: list the nodes
  bad.kn:4:5: fn operands is [@total]: it cannot have a catch-all case, which would hide missing nodes: list the nodes
  [1]
  $ cat > bad.kn <<'KN'
  > fn operands (v : t) (n : int) : t list [@total] =
  >   match v, n with
  >   | Int _, _ | Var _, _ | Neg _, _ | Add _, _ | Sub _, _ -> []
  >   | _, 0 -> []
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:4:4: fn operands is [@total]: it cannot have a catch-all case, which would hide missing nodes: list the nodes
  [1]

A case with a guard does not cover its node, and neither does one whose
arguments or whose other patterns are not blanks: it may not match.

  $ cat > bad.kn <<'KN'
  > fn operands (v : t) (n : int) : t list [@total] =
  >   match v, n with
  >   | Int _, _ | Var _, _ -> []
  >   | Neg a, _ when n > 0 -> [a]
  >   | Add (a, b), 0 -> [a; b]
  >   | Sub (a, 0), _ -> [a]
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:0: fn operands is [@total] but has no case for Neg, Add, Sub
  [1]

The scrutinee is the first term parameter, in a match behind `let`s.

  $ cat > ok.kn <<'KN'
  > fn operands (n : int) (v : t) (cs : t list) : t list [@total] =
  >   let k = n + 1 in
  >   match k, cs, v with
  >   | _, _, Int _ | _, _, Var _ -> []
  >   | _, _, Neg a -> [a]
  >   | _, _, Add (a, b) -> [a; b]
  >   | _, _, Sub (a, b) -> cs
  > KN
  $ kanon ocaml lang.knl ok.kn | grep -c "Op2 ((Sub)"
  1
  $ cat > bad.kn <<'KN'
  > fn operands (v : t) : t list [@total] = []
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:0: fn operands is [@total]: it must end with a match on v
  [1]
  $ cat > bad.kn <<'KN'
  > fn operands (n : int) : int list [@total] =
  >   match n with
  >   | _ -> []
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:0: fn operands is [@total]: it has no term parameter
  [1]

`extend fn` appends its cases to a `[@total]` function, which has no final
catch-all case to go before, and the check sees them.

  $ cat > bad.kn <<'KN'
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ | Var _ -> []
  >   | Neg a -> [a]
  > extend fn operands =
  >   | a + b -> [a; b]
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:0: fn operands is [@total] but has no case for Sub
  [1]
  $ cat > good.kn <<'KN'
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ | Var _ -> []
  >   | Neg a -> [a]
  > extend fn operands =
  >   | a + b | Sub (a, b) -> [a; b]
  > KN
  $ kanon ocaml lang.knl good.kn | grep -A8 "^let operands"
  let operands (v : t) : (t list) =
      (match v with
      | { kind = Int (_); _ } -> []
      | { kind = Var (_); _ } -> []
      | { kind = Op1 ((Neg), a); _ } -> (a :: [])
      | { kind = Op2 ((Add), a, b); _ } -> (a :: (b :: []))
      | { kind = Op2 ((Sub), a, b); _ } -> (a :: (b :: []))
      )
  

A module that adds nodes, used after the function, must extend it: the check
runs once, on the final language, whatever the order of the modules.

  $ cat > base.kn <<'KN'
  > fn operands (v : t) : t list [@total] =
  >   match v with
  >   | Int _ | Var _ -> []
  >   | Neg a -> [a]
  >   | a + b -> [a; b]
  >   | Sub (a, b) -> [a; b]
  > KN
  $ cat > ext.kn <<'KN'
  > extend fn operands =
  >   | Mul (a, b) -> [b; a]
  > KN
  $ (echo 'use "base"'; cat lang.knl; echo 'node Mul : TInt -> TInt -> TInt') > full.knl
  $ kanon ocaml full.knl
  ./base.kn:1:0: fn operands is [@total] but has no case for Mul
  [1]
  $ (cat full.knl; echo 'use "ext"') > fixed.knl
  $ kanon ocaml fixed.knl | grep -A9 "^let operands"
  let operands (v : t) : (t list) =
      (match v with
      | { kind = Int (_); _ } -> []
      | { kind = Var (_); _ } -> []
      | { kind = Op1 ((Neg), a); _ } -> (a :: [])
      | { kind = Op2 ((Add), a, b); _ } -> (a :: (b :: []))
      | { kind = Op2 ((Sub), a, b); _ } -> (a :: (b :: []))
      | { kind = Op2 ((Mul), a, b); _ } -> (b :: (a :: []))
      )
  

The nodes of an interleaved declaration are listed in the order of the file, and
`[@total]` combines with `[@no_lean]`.

  $ cat > inter.knl <<'KN'
  > sort TInt
  > node Add : TInt -> TInt -> TInt
  > node Int of int : TInt
  > node Neg : TInt -> TInt
  > node Zero : TInt
  > KN
  $ cat > bad.kn <<'KN'
  > fn operands (v : t) : t list [@total] [@no_lean] =
  >   match v with
  >   | Neg a -> [a]
  > KN
  $ kanon ocaml inter.knl bad.kn
  bad.kn:1:0: fn operands is [@total] but has no case for Int, Zero, Add
  [1]

Only a `fn` can be `[@total]`.

  $ cat > bad.kn <<'KN'
  > rule add : Add (v1, v2) [@total]
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:26: unknown attribute [@total]
  [1]
  $ cat > bad.kn <<'KN'
  > prim p : int -> int [@total]
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:22: unknown attribute [@total]
  [1]
