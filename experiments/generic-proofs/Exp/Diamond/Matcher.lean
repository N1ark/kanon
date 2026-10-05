import Exp.L1.Generic

/-! A helper fn with a catch-all over ANY other node (`fn is_pos v = match v with #z -> 0 < z | _ -> false`),
used by an arm's side condition. Generic side: the module asks for a *matcher* of its own node. -/

namespace Exp.Matcher

open Classical Kanon

structure Lang (S : Sem) extends toI : IMod.Lang S where
  asILit : S.Term → Option Int
  asILit_sound : ∀ v z, asILit v = some z → ∃ t, v = mk (ilitK z) t

/-- The helper, generic: the catch-all is the `none` of the matcher. -/
def Lang.isPos {S : Sem} (L : Lang S) (v : S.Term) : Bool :=
  match L.asILit v with | some z => decide (0 < z) | none => false

theorem lt.pos {S : Sem} (L : Lang S) : ∀ (b : S.Term), L.isPos b = true →
    S.Refines (L.mk (L.ltK (L.mk (L.ilitK 0) L.tint) b) L.tbool) (L.mk (L.litK true) L.tbool) := by
  intro b h
  unfold Lang.isPos at h
  split at h
  · rename_i z hz
    obtain ⟨t, rfl⟩ := L.asILit_sound _ _ hz
    simp only [decide_eq_true_eq] at h
    refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · imod_simp at w ⊢; grind
    · imod_simp at w e ⊢
      grind [BMod.Lang.vb_db', BMod.Lang.db_vb', BMod.Lang.vb_inj, IMod.Lang.vi_di', IMod.Lang.di_vi',
        IMod.Lang.vi_inj]
  · cases h

end Exp.Matcher

namespace Exp.L1

/-- The helper as the closed model defines it today (closed match with a catch-all). -/
def isPos (v : Term) : Bool := match v with | .mk (.ILit z) _ => decide (0 < z) | _ => false

def mlang : Matcher.Lang sem :=
  { Generic.lang with
    asILit := fun v => match v with | .mk (.ILit z) _ => some z | _ => none
    asILit_sound := fun v z h => by
      rcases v with ⟨k, t⟩; cases k <;> simp_all <;> exact ⟨_, rfl⟩ }

/-- Bridge between the closed helper and the generic one: one case per constructor. -/
theorem isPos_eq (v : Term) : isPos v = mlang.isPos v := by
  rcases v with ⟨k, t⟩; cases k <;> rfl

theorem lt.pos : ∀ b, isPos b = true →
    Refines (.mk (.Lt (.mk (.ILit 0) .TInt) b) .TBool) (.mk (.BLit true) .TBool) := by
  intro b h; rw [isPos_eq] at h; exact Matcher.lt.pos mlang b h

end Exp.L1
