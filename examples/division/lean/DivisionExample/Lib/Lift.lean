import KanonCore.Proof
import DivisionExample.Statements
import DivisionExample.Bool

/-!
# Refinement by congruence

Refining the operands of a node refines the node: the congruence lemmas of the
nodes, with which `kanon_congr` (Kanon's) proves that the specs are monotone
(`Lifts.lean`), so that a call of a rule function on terms that refine others
refines its spec on those. The proof is the same for every node: refinement
keeps the types of the operands, and the operations are monotone (poison in,
poison out, or the same value).
-/

namespace DivisionExample

open Kanon Kanon.Sem BoolMod

/-! ## The operations are monotone -/

theorem addV_mono {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (addV a b) (addV a' b') := by
  intro v e
  unfold addV at e
  split at e
  · rw [ha _ rfl, hb _ rfl]; exact e
  · cases e

theorem ltV_mono {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (ltV a b) (ltV a' b') := by
  intro v e
  unfold ltV at e
  split at e
  · rw [ha _ rfl, hb _ rfl]; exact e
  · cases e

theorem divV_mono {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (divV a b) (divV a' b') := by
  intro v e
  unfold divV at e
  split at e
  · rw [ha _ rfl, hb _ rfl]; exact e
  · cases e

theorem sq1V_mono {a a' : Option Val} (ha : OLe a a') : OLe (sq1V a) (sq1V a') := by
  intro v e
  unfold sq1V at e
  split at e
  · rw [ha _ rfl]; exact e
  · cases e

theorem evOp1_mono (op : Op1) {a a' : Option Val} (ha : OLe a a') :
    OLe (evOp1 op a) (evOp1 op a') := by
  cases op
  · exact pnot_mono ha
  · exact sq1V_mono ha

theorem evOp2_mono (op : Op2) {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (evOp2 op a b) (evOp2 op a' b') := by
  cases op
  · exact pand_mono ha hb
  · exact por_mono ha hb
  · exact peq_mono ha hb
  · exact addV_mono ha hb
  · exact ltV_mono ha hb
  · exact divV_mono ha hb

theorem evOp3_mono (op : Op3) {a a' b b' c c' : Option Val} (ha : OLe a a') (hb : OLe b b')
    (hc : OLe c c') : OLe (evOp3 op a b c) (evOp3 op a' b' c') := by
  cases op; exact pite_mono ha hb hc

/-! ## Congruence -/

theorem Refines.op1 {op : Op1} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Op1 op a) t) (.mk (.Op1 op a') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · -- typing: the operand keeps its type
    simp only [sem, Term.WT] at w ⊢
    obtain ⟨wa, sa⟩ := ha.syn w.2
    simp only [sem] at sa
    exact ⟨⟨by rw [sa]; exact w.1, wa⟩, rfl⟩
  · -- values: the operation is monotone
    simp only [sem, Term.WT, ev] at w e ⊢
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

/-- The type of an `ite` is that of its branches, which the spec of `b_ite`
writes `ty if_`: it is the type of the refined branch on the right. -/
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
    exact evOp3_mono op (ha.ev w.2.1 ρ) (hb.ev w.2.2.1 ρ) (hc.ev w.2.2.2 ρ) v e

attribute [kanon_congr_lemma] Refines.op1 Refines.op2 Refines.op3

end DivisionExample
