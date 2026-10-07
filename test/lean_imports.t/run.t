A module that mentions the data type of another module, in the arguments of its
nodes, in the types of its functions or in its own types, depends on it:
its Lean files import the types of that module, whether it `use`s it or not.

  $ cat > lang.knl <<'KN'
  > use "a"
  > use "b"
  > use "c"
  > use "d"
  > KN
  $ cat > b.knl <<'KN'
  > [@@@lean_root "BMod"]
  > type color = Red | Green
  > sort TB
  > node B of int : TB
  > KN
  $ cat > a.knl <<'KN'
  > [@@@lean_root "AMod"]
  > sort TA
  > node A of color : TA
  > KN
  $ cat > c.knl <<'KN'
  > [@@@lean_root "CMod"]
  > KN
  $ cat > c.kn <<'KN'
  > fn width (c : color) : int = 0
  > KN
  $ cat > d.knl <<'KN'
  > [@@@lean_root "DMod"]
  > type palette = { main : color; others : color list }
  > KN
  $ kanon lean-all out lang.knl
  $ grep -H '^import BMod.Types' out/AMod/Node.lean out/CMod/Model.lean out/DMod/Types.lean
  out/AMod/Node.lean:import BMod.Types
  out/CMod/Model.lean:import BMod.Types
  out/DMod/Types.lean:import BMod.Types
