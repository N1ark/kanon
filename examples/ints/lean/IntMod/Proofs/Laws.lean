import IntMod.Statements
import IntMod.Lib.Lift

/-!
# Hand-written proofs

The generated proofs of the arms of the int module use its tactic `kanon_int`
(`Lib/Rule.lean`); a proof written by hand replaces it for the statement it
proves (`@[kanon_arm]`). The one below is of the commutativity of `+`: its
statement, `Plus.comm.Stmt` (`Statements.lean`), is that `a + b` is refined by
`b + a`, at any sort `t`, in any language `L` that uses the module.
-/

namespace IntMod

open Kanon

/-- `a + b` is refined by `b + a`. -/
@[kanon_arm] theorem plus_comm : Plus.comm.Stmt := by
  intro S _ _ L _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · -- typing: `b + a` is well-typed, of the sort `t`, when `a + b` is
    rw [L.WT_Plus] at w ⊢
    exact ⟨⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩, by rw [L.ty_node, L.ty_node]⟩
  · -- values: the sum of two integers commutes, and is otherwise poison
    rw [Sem.ev_Plus] at e ⊢
    rw [addV_comm]; exact e

end IntMod
