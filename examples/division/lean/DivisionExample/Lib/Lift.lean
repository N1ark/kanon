import KanonCore.Proof
import DivisionExample.Statements

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

open Kanon Kanon.Sem

/-! ## The operations are monotone (those of the int module are, `DivMod`) -/

theorem evOp1_mono (op : Op1) {a a' : Option Val} (ha : OLe a a') :
    OLe (evOp1 op a) (evOp1 op a') := by
  cases op
  exact DivMod.sq1V_mono ha

theorem evOp2_mono (op : Op2) {a a' b b' : Option Val} (ha : OLe a a') (hb : OLe b b') :
    OLe (evOp2 op a b) (evOp2 op a' b') := by
  cases op
  · exact DivMod.addV_mono ha hb
  · exact DivMod.divV_mono ha hb

/-! ## Congruence -/

/-- The language has one type, so that the types of two terms are equal. -/
theorem ty_eq (x y : Ty) : x = y := by cases x; cases y; rfl

theorem Refines.op1 {op : Op1} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Op1 op a) t) (.mk (.Op1 op a') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · -- typing: the operand keeps its type
    simp only [sem, Term.WT] at w ⊢
    exact ⟨⟨by rw [ty_eq a'.ty a.ty]; exact w.1, (ha.syn w.2).1⟩, trivial⟩
  · -- values: the operation is monotone
    simp only [sem, Term.WT, ev] at w e ⊢
    exact evOp1_mono op (ha.ev w.2 ρ) v e

theorem Refines.op2 {op : Op2} {a a' b b' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') : Refines (.mk (.Op2 op a b) t) (.mk (.Op2 op a' b') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [sem, Term.WT] at w ⊢
    exact ⟨⟨by rw [ty_eq a'.ty a.ty, ty_eq b'.ty b.ty]; exact w.1, (ha.syn w.2.1).1, (hb.syn w.2.2).1⟩, trivial⟩
  · simp only [sem, Term.WT, ev] at w e ⊢
    exact evOp2_mono op (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

attribute [kanon_congr_lemma] Refines.op1 Refines.op2

end DivisionExample
