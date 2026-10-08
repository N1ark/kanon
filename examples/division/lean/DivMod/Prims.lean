import Generated.DivMod.Lang

/-!
# The meaning of the subsort `TNonzero`

The terms of the subsort `TNonzero` (`[@lean "Nonzero"]`) have no value zero.
-/

namespace DivMod

open Kanon

variable {S : Kanon.Sem} [Lang S]

/-- The terms whose value is not zero. -/
def Nonzero (e : S.Term) : Prop := ∀ ρ z, S.eval ρ e = some (Values.vint.inj z) → z ≠ 0

end DivMod
