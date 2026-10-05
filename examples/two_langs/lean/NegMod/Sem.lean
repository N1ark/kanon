import NumMod.Sem
import NegMod.Syntax

/-!
# What the neg module needs of the semantics of a language

The negation of an integer, evaluated by `negV`; the module extends the num
module, and what it needs of a language assumes what that one needs
(`NumMod.Sem`).
-/

namespace NegMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- The negation of an integer; poison otherwise. -/
def negV {V : Type} (vint : Int → V) (toInt : V → Option Int) (a : Option V) : Option V :=
  a.bind fun x => (toInt x).map fun m => vint (0 - m)

theorem negV_mono {V : Type} {vint : Int → V} {toInt : V → Option Int} {a a' : Option V}
    (ha : OLe a a') : OLe (negV vint toInt a) (negV vint toInt a') := by
  intro v e
  simp only [negV, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, rest⟩ := e
  exact ⟨x, ha _ hx, rest⟩

/-- What the neg module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} {LBool : KanonBool.Syntax B} {LNum : NumMod.Syntax B LBool} (L : Syntax B LBool LNum)
    [KanonBool.Sem LBool] [NumMod.Sem LNum] where
  ev_Neg : ∀ ρ a t, S.ev ρ (B.node (L.NegK a) t) =
    negV (NumMod.Sem.vint LNum) (NumMod.Sem.toInt LNum) (S.ev ρ a) := by kanon_law

end NegMod
