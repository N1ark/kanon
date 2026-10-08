Local functions and variables share their scope, as in OCaml: a variable hides
a local function of the same name, and the other way round, so the generated
OCaml means what the rules say.

  $ cat > lang.knl <<'KN'
  > use "rules"
  > KN
  $ cat > rules.kn <<'KN'
  > fn a (y : int) : int = let g (x : int) : int = x + 1 in let g = 10 in g y
  > KN
  $ kanon ocaml out lang.knl
  ./rules.kn:1:70: unknown function g
  [1]
  $ cat > rules.kn <<'KN'
  > fn a (y : int) : int = let g = 10 in let g (x : int) : int = x + 1 in g
  > KN
  $ kanon ocaml out lang.knl
  ./rules.kn:1:70: unbound variable g
  [1]
  $ cat > rules.kn <<'KN'
  > fn a (y : int) : int = let g (x : int) : int = x + 1 in let h (g : int) : int = g 1 in h y
  > KN
  $ kanon ocaml out lang.knl
  ./rules.kn:1:80: unknown function g
  [1]
  $ cat > rules.kn <<'KN'
  > fn a (y : int) : int = let g (x : int) : int = x + 1 in let (g, _) = (y, y) in g y
  > KN
  $ kanon ocaml out lang.knl
  ./rules.kn:1:79: unknown function g
  [1]
