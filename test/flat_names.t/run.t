The functions of the rules are called by their flat name in OCaml (`Int.add` is
`int_add`): a variable of that name would capture the call, so it is an error,
like one that shadows a global function.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "int"
  > use "user"
  > KN
  $ cat > int.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > KN
  $ cat > int.kn <<'KN'
  > fn add (x y : int) : int = x + y
  > KN
  $ cat > user.knl <<'KN'
  > KN
  $ cat > user.kn <<'KN'
  > fn double (int_add : int) : int = Int.add int_add int_add
  > KN
  $ kanon ocaml out lang.knl
  ./user.kn:1:11: int_add is the OCaml name of Int.add
  [1]
