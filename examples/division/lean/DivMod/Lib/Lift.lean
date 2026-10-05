import KanonCore.Proof
import DivMod.Statements

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the int module, with which `kanon_congr`
proves that its specs are monotone (`Lifts.lean`).
-/

namespace DivMod

open Classical Kanon Kanon.Sem

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} {L : Syntax B} [Sem L]

theorem refines_plus {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (B.node (L.PlusK a b) t) (B.node (L.PlusK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Plus] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Plus _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Plus] at e ⊢
    exact addV_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_div {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (B.node (L.DivK a b) t) (B.node (L.DivK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Div] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Div _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Div] at e ⊢
    exact divV_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_sq1 {a a' : S.Term} {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (B.node (L.Sq1K a) t) (B.node (L.Sq1K a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Sq1] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2
    exact ⟨(L.WT_Sq1 _ _).2 ⟨⟨sa.trans w.1.1, w.1.2⟩, wa⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Sq1] at e ⊢
    exact sq1V_mono (ha.ev w.2 ρ) v e

attribute [kanon_congr_lemma] refines_plus refines_div refines_sq1

end Sem

end DivMod
