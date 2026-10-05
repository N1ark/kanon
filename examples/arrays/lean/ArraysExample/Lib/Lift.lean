import KanonCore.Proof
import ArraysExample.Statements

/-!
# Refinement by congruence

Refining the operands of a node refines the node: the congruence lemmas of the
nodes, with which `kanon_congr` proves that the specs are monotone
(`Lifts.lean`). The operations are monotone: poison in, poison out.
-/

namespace ArraysExample

open Kanon Kanon.Sem

theorem evOp1_mono (op : Op1) {a a' : Option Val} (ha : OLe a a') :
    OLe (evOp1 op a) (evOp1 op a') := by
  intro v e; cases op
  cases a with
  | none => cases e
  | some x => rw [ha x rfl]; exact e

theorem evOp2_mono (op : Op2) {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (evOp2 op a b) (evOp2 op a' b') := by
  intro v e; cases op
  cases a with
  | none => cases e
  | some x => cases b with
    | none => cases x <;> cases e
    | some y => rw [ha x rfl, hb y rfl]; exact e

theorem evOp3_mono (op : Op3) {a a' b b' c c' : Option Val} (ha : OLe a a') (hb : OLe b b')
    (hc : OLe c c') : OLe (evOp3 op a b c) (evOp3 op a' b' c') := by
  intro v e; cases op
  cases a with
  | none => cases e
  | some x => cases b with
    | none => cases x <;> cases e
    | some y => cases c with
      | none => cases x <;> cases y <;> cases e
      | some z => rw [ha x rfl, hb y rfl, hc z rfl]; exact e

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

theorem Refines.op3 {op : Op3} {a a' b b' c c' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') (hc : Refines c c') :
    Refines (.mk (.Op3 op a b c) t) (.mk (.Op3 op a' b' c') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [sem, Term.WT] at w ⊢
    obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.1
    obtain ⟨wc, sc⟩ := hc.syn w.2.2.2
    simp only [sem] at sa sb sc
    exact ⟨⟨by rw [sa, sb, sc]; exact w.1, wa, wb, wc⟩, rfl⟩
  · simp only [sem, Term.WT, ev] at w e ⊢
    exact evOp3_mono op (ha.ev w.2.1 ρ) (hb.ev w.2.2.1 ρ) (hc.ev w.2.2.2 ρ) v e

attribute [kanon_congr_lemma] Refines.op1 Refines.op2 Refines.op3

end ArraysExample
