import KanonBool.Soundness.Laws
import KanonBool.Soundness.Bool.and_
import KanonBool.Soundness.Bool.or_
import KanonBool.Soundness.Bool.not_
import KanonBool.Soundness.Bool.ite
import KanonBool.Soundness.Bool.eq
import KanonBool.Soundness.Bool.eq_untyped
import KanonBool.Soundness.Bool.distinct

/-!
# The bool module, proved once

The rules of the bool module (`modules/bool.kn`), proved for every language that
uses it, over its interface (`[@@@lean_module "KanonBool"]`): Kanon generates
`Syntax.lean` (the interface), `Ops.lean`, `Statements*.lean`, `Lifts.lean` and
`Soundness/` (by `kanon lean-all . +bool.knl +bool.kn`, in `lean/`); `Val.lean`
(the operations on values), `Lang.lean` (what the module needs of the semantics),
`Lib/` (congruence, the tactic `kanon_bool`) and `Proofs/` are written by hand.
-/
