import IntsExample.Lib.Rule

/-!
# Hand-written proofs

`kanon_auto` (`Lib/Rule.lean`) proves every arm of this language and the
commutativity of `+`, so no proof is needed here. A proof written by hand
replaces `kanon_auto` for the statement it proves (`@[kanon_arm]`): the one
below, of the commutativity of `+`, shows how. Its statement, `Op2.Plus.comm.Stmt`
(`Statements.lean`), is that `a + b` is refined by `b + a`, at any type `t`.
-/

namespace IntsExample

open Kanon

/-- `a + b` is refined by `b + a`. -/
@[kanon_arm] theorem plus_comm : Op2.Plus.comm.Stmt := by
  intro a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · -- typing: `b + a` is well-typed, of the type `t`, when `a + b` is
    simp only [sem, Term.WT, Op2.WT] at w ⊢
    exact ⟨⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩, rfl⟩
  · -- values: the sum of two integers commutes, and is otherwise poison
    simp only [sem, ev, evOp2] at e ⊢
    unfold addV at e ⊢
    split at e
    · next x y ha hb => cases e; rw [ha, hb, Int.add_comm]
    · cases e

end IntsExample
