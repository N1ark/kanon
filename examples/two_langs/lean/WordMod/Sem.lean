import KanonBool.Sem
import CfgMod.Sem
import WordMod.Syntax

/-!
# What the word module needs of the semantics of a language

The words are integers, whatever their width: a literal is its integer, a blob
the integer of its bits, a sum the sum of the integers (`addV`, whatever its
flags), and a rounding the word itself.
-/

namespace WordMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- The sum of two integers; poison otherwise. -/
def addV {V : Type} (vint : Int → V) (toInt : V → Option Int) (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun k => vint (m + k)

theorem addV_mono {V : Type} {vint : Int → V} {toInt : V → Option Int} {a a' b b' : Option V}
    (ha : OLe a a') (hb : OLe b b') : OLe (addV vint toInt a b) (addV vint toInt a' b') := by
  intro v e
  simp only [addV, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

/-- What the word module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LCfg : CfgMod.Syntax B} (L : Syntax B LBool LCfg)
    [KanonBool.Sem LBool] [CfgMod.Sem LCfg] where
  /-- The integer values. -/
  vint : Int → S.Val
  /-- The integer of a value, if it is one. -/
  toInt : S.Val → Option Int
  ev_Wd : ∀ ρ z n t, S.ev ρ (B.node (L.WdK z n) t) = some (vint z) := by kanon_law
  ev_WBlob : ∀ ρ b l t, S.ev ρ (B.node (L.WBlobK b l) t) = some (vint b.bits) := by kanon_law
  ev_WAdd : ∀ ρ f n a b t, S.ev ρ (B.node (L.WAddK f n a b) t) =
    addV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_WRound : ∀ ρ m n a t, S.ev ρ (B.node (L.WRoundK m n a) t) = S.ev ρ a := by kanon_law

end WordMod
