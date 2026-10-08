import KanonBool.Generated.Soundness

/-!
# The bool module

The rules of the bool module (`modules/bool.kn`), modelled and proved once, for
every language that uses it. Kanon generates the directory `Generated/`, with
`Node.lean` (its sort and nodes), `Lang.lean` (the typing of the nodes, and the
classes `Lang` and `Typed` of what it needs of a language), `Model.lean`,
`Lift.lean`, `Statements/`, `Soundness/` and `Soundness.lean` (by `kanon lean-all
. +bool.knl +bool.kn`, in `lean/`, which clears it first); `Sem.lean` (its
values and the meaning of its nodes), `Prims.lean` (its primitives, and what
`sure_neq` and the oracle `sort_by_tag` satisfy) and `Proofs.lean`, beside it,
are written by hand.
-/
