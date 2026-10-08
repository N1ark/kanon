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
  $ grep -H '^import Generated.BMod.Types' out/Generated/AMod/Node.lean out/Generated/CMod/Model.lean out/Generated/DMod/Types.lean
  out/Generated/AMod/Node.lean:import Generated.BMod.Types
  out/Generated/CMod/Model.lean:import Generated.BMod.Types
  out/Generated/DMod/Types.lean:import Generated.BMod.Types

The types that Lean already has (`[@lean "String"]`) are not defined by their
module: a module that mentions one does not depend on it.

  $ cat > lang2.knl <<'KN'
  > use "e"
  > type var [@lean "String"]
  > node Var of var
  > KN
  $ cat > e.knl <<'KN'
  > [@@@lean_root "EMod"]
  > sort TE
  > node E of var : TE
  > KN
  $ kanon lean-all out2 lang2.knl
  $ grep '^import' out2/Generated/EMod/Model.lean
  import Generated.EMod.Lang
  import KanonCore.Model
  import KanonCore.Attr
  import KanonCore.Embed

The model of a module without nodes or sorts has no `Lang.lean` to import the
attributes of its proofs from (`kanon_body`, on its helpers), so it imports them:

  $ cat > lang3.knl <<'KN'
  > use "util"
  > KN
  $ cat > util.knl <<'KN'
  > [@@@lean_root "UMod"]
  > KN
  $ cat > util.kn <<'KN'
  > fn double (x : int) : int = x + x
  > KN
  $ kanon lean-all out3 lang3.knl
  $ grep '^import' out3/Generated/UMod/Model.lean
  import KanonCore.Model
  import KanonCore.Attr
  import KanonCore.Embed
  import KanonCore.ProofAttr
