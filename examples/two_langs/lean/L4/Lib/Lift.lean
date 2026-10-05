import KanonCore.Proof
import L4.Statements

/-!
# Refinement by congruence, over the terms of the language

For the arms that the language proves itself: that of `Word.double_closed`,
which its module marks `[@lean_closed]`. The operations are monotone.
-/

namespace L4

open Kanon Kanon.Sem KanonBool

theorem evOp1_mono (op : Op1) {a a' : Option Val} (ha : OLe a a') :
    OLe (evOp1 op a) (evOp1 op a') := by
  cases op
  · exact pnot_mono ha
  · exact ha
  · exact ha

theorem evOp2_mono (op : Op2) {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (evOp2 op a b) (evOp2 op a' b') := by
  cases op
  · exact pand_mono ha hb
  · exact por_mono ha hb
  · exact peq_mono ha hb
  · exact WordMod.addV_mono ha hb

theorem Refines.op1 {op : Op1} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Op1 op a) t) (.mk (.Op1 op a') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [sem, Term.WT] at w ⊢
    obtain ⟨wa, sa⟩ := ha.syn w.2
    simp only [sem] at sa
    exact ⟨⟨by rw [sa]; exact w.1, wa⟩, rfl⟩
  · simp only [sem, Term.WT, ev] at w e ⊢
    exact evOp1_mono op (ha.ev w.2 ρ) v e

theorem Refines.op2 {op : Op2} {a a' b b' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') : Refines (.mk (.Op2 op a b) t) (.mk (.Op2 op a' b') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [sem, Term.WT] at w ⊢
    obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    simp only [sem] at sa sb
    exact ⟨⟨by rw [sa, sb]; exact w.1, wa, wb⟩, rfl⟩
  · simp only [sem, Term.WT, ev] at w e ⊢
    exact evOp2_mono op (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

/-- The type of an `ite` is that of its branches, which the spec of `ite`
writes `ty if_`. -/
theorem Refines.op3 {op : Op3} {a a' b b' c c' : Term} (ha : Refines a a')
    (hb : Refines b b') (hc : Refines c c') :
    Refines (.mk (.Op3 op a b c) (ty b)) (.mk (.Op3 op a' b' c') (ty b')) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [sem, Term.WT] at w ⊢
    obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.1
    obtain ⟨wc, sc⟩ := hc.syn w.2.2.2
    simp only [sem, ty] at sa sb sc w ⊢
    exact ⟨⟨by rw [sa, sb, sc]; exact w.1, wa, wb, wc⟩, sb⟩
  · simp only [sem, Term.WT, ev] at w e ⊢
    cases op
    exact pite_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2.1 ρ) (hc.ev w.2.2.2 ρ) v e

attribute [kanon_congr_lemma] Refines.op1 Refines.op2 Refines.op3

end L4
