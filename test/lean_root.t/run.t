Two modules with the same Lean root would write the same files, one over the
other: kanon lean-all reports it, and writes nothing.

  $ cat > lang.knl <<'KN'
  > use "a"
  > use "b"
  > KN
  $ cat > a.knl <<'KN'
  > [@@@lean_root "Same"]
  > sort TA
  > node A of int : TA
  > KN
  $ cat > b.knl <<'KN'
  > [@@@lean_root "Same"]
  > sort TB
  > node B of int : TB
  > KN
  $ kanon lean-all out lang.knl
  kanon: two modules write the Lean file Same/Node.lean: give them different roots with [@@@lean_root]
  [1]
  $ test -e out || echo nothing written
  nothing written

The root is the namespace and the directory of the Lean files, so it is a Lean
name (identifiers separated by dots, that Lean does not reserve), and not that
of the libraries that Lean provides (`Lean`, `Init`, `Std`, `Lake`) or that the
files import (`KanonCore`, `KanonBool`):

  $ for r in "my root" 1st A..B "" fun A/B ../x Lean Init Std Lake KanonCore KanonBool Lean.Foo Foo.end; do
  >   printf '[@@@lean_root "%s"]\nsort TA\nnode A of int : TA\n' "$r" > lang2.knl
  >   kanon lean-all out2 lang2.knl 2>&1
  > done
  kanon: the root "my root" of the module Lang2 is not a Lean name
  kanon: the root "1st" of the module Lang2 is not a Lean name
  kanon: the root "A..B" of the module Lang2 is not a Lean name
  kanon: the root "" of the module Lang2 is not a Lean name
  kanon: the root "fun" of the module Lang2 is not a Lean name
  kanon: the root "A/B" of the module Lang2 is not a Lean name
  kanon: the root "../x" of the module Lang2 is not a Lean name
  kanon: the root "Lean" of the module Lang2 is that of a library
  kanon: the root "Init" of the module Lang2 is that of a library
  kanon: the root "Std" of the module Lang2 is that of a library
  kanon: the root "Lake" of the module Lang2 is that of a library
  kanon: the root "KanonCore" of the module Lang2 is that of a library
  kanon: the root "KanonBool" of the module Lang2 is that of a library
  kanon: the root "Lean.Foo" of the module Lang2 is that of a library
  kanon: the root "Foo.end" of the module Lang2 is not a Lean name
  [1]
  $ test -e out2 || echo nothing written
  nothing written

The names of the modules that the language uses are checked too, and a root
may have several parts:

  $ cat > lang3.knl <<'KN'
  > use "b3"
  > KN
  $ cat > b3.knl <<'KN'
  > [@@@lean_root "Lean"]
  > sort TB
  > node B of int : TB
  > KN
  $ kanon lean-all out3 lang3.knl
  kanon: the root "Lean" of the module B3 is that of a library
  [1]
  $ sed -i 's/"Lean"/"My.Lang"/' b3.knl
  $ kanon lean-all out3 lang3.knl
  $ ls out3/My/Lang | head -2
  Lang.lean
  Lift.lean
