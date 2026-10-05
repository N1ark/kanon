import NumMod.Sem
import EvenMod.Syntax

/-!
# What the even module needs of the semantics of a language

The even integers are integers (`NumMod.Sem.vint`); the remainder by 2 is
evaluated by `rem2V`. The invariant of the sort `TEven` (`even_inv`, part of the
typing of its terms in the interface) means, at the literals, that they are
even (`even_inv_Ev`): that is what the rule `Ev z → 0` of `rem2` relies on.
-/

namespace EvenMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- The remainder of an integer by 2; poison otherwise. -/
def rem2V {V : Type} (vint : Int → V) (toInt : V → Option Int) (a : Option V) : Option V :=
  a.bind fun x => (toInt x).map fun m => vint (m % 2)

theorem rem2V_mono {V : Type} {vint : Int → V} {toInt : V → Option Int} {a a' : Option V}
    (ha : OLe a a') : OLe (rem2V vint toInt a) (rem2V vint toInt a') := by
  intro v e
  simp only [rem2V, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, rest⟩ := e
  exact ⟨x, ha _ hx, rest⟩

/-- What the even module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LNum : NumMod.Syntax B LBool} (L : Syntax B LBool LNum)
    [KanonBool.Sem LBool] [NumMod.Sem LNum] where
  /-- The invariant of `TEven`, at its literals: they are even. -/
  even_inv_Ev : ∀ z t, L.even_inv (B.node (L.EvK z) t) ↔ z % 2 = 0 := by kanon_law
  ev_Ev : ∀ ρ z t, S.ev ρ (B.node (L.EvK z) t) = some (NumMod.Sem.vint LNum z) := by kanon_law
  ev_Rem2 : ∀ ρ a t, S.ev ρ (B.node (L.Rem2K a) t) =
    rem2V (NumMod.Sem.vint LNum) (NumMod.Sem.toInt LNum) (S.ev ρ a) := by kanon_law

end EvenMod
