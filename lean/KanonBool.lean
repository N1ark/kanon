import Generated.KanonBool.Soundness

/-!
# The bool module

The rules of the bool module (`modules/bool.kn`), modelled and proved once, for
every language that uses it. Kanon generates the directory `Generated/KanonBool/`
(by `kanon lean . +bool.knl +bool.kn`, in `lean/`, which clears it first), with
`Node.lean` (its sort and nodes), `Lang.lean` (the typing of the nodes, and the
classes `Lang` and `Typed` of what it needs of a language), `Model.lean`,
`Lift.lean`, `Statements/`, `Soundness/` and `Soundness.lean`; `KanonBool/Sem.lean`
(its values and the meaning of its nodes), `KanonBool/Prims.lean` (its
primitives, and what `sure_neq` and the oracle `sort_by_tag` satisfy) and
`KanonBool/Proofs.lean` are written by hand.
-/
