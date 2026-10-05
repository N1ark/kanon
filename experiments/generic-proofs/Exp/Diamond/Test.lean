import Exp.Generic.XMod

/-! Diamond: two modules that both use `B` (X via I, and Y directly), used together by one
language interface. Lean merges the fields of the shared parent `BMod.Lang`. -/

namespace Exp.Diamond

open Classical Kanon

/-- A module `Y` that uses only `B`: a node `Xor`. -/
structure YLang (S : Sem) extends toB : BMod.Lang S where
  xorK : S.Term → S.Term → Kind
  ev_xor : ∀ ρ a b t, S.ev ρ (mk (xorK a b) t) =
    (S.ev ρ a).bind fun x => (S.ev ρ b).bind fun y =>
      (db x).bind fun p => (db y).map fun q => vb (p ^^ q)

theorem YLang.xor_self {S : Sem} (L : YLang S) (ρ : S.Env) (a : S.Term) (t : S.Ty)
    (h : ∃ v b, S.ev ρ a = some v ∧ L.db v = some b) :
    S.ev ρ (L.mk (L.xorK a a) t) = some (L.vb false) := by
  obtain ⟨v, b, hv, hb⟩ := h
  simp [L.ev_xor, hv, hb]

/-- A language with X (hence I, B) and Y (hence B). -/
structure ZLang (S : Sem) extends toX : XMod.Lang S, toY : YLang S

variable {S : Sem} (L : ZLang S)

-- the generic theorems of all modules apply, through the projections
example : ∀ (b : Bool) (t : S.Ty),
    S.Refines (L.mk (L.notK (L.mk (L.litK b) t)) L.tbool) (L.mk (L.litK (!b)) L.tbool) :=
  BMod.not_.lit L.toY.toB
example : ∀ (b : Bool) (t : S.Ty),
    S.Refines (L.mk (L.notK (L.mk (L.litK b) t)) L.tbool) (L.mk (L.litK (!b)) L.tbool) :=
  BMod.not_.lit L.toX.toI.toB
-- the two paths to `B` are the same interface (definitionally)
example : L.toY.toB = L.toX.toI.toB := rfl
example (ρ a t h) := L.toY.xor_self ρ a t h

end Exp.Diamond
