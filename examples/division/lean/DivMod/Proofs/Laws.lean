import DivMod.Statements
import DivMod.Lib.Lift

/-!
# The commutativity of `+`, by hand

A proof written by hand replaces `kanon_auto` for the statement it proves
(`@[kanon_arm]`): here, of the commutativity of `+`. Its statement,
`Plus.comm.Stmt` (`Statements.lean`), is that `a + b` is refined by `b + a`, at
any sort `t`, in any language `L` that uses the module. The generated
`Soundness/Laws.lean` imports this file.
-/

namespace DivMod

open Kanon

/-- `a + b` is refined by `b + a`. -/
@[kanon_arm] theorem plus_comm : Plus.comm.Stmt := by
  intro S _ _ B L _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · -- typing: `b + a` is well-typed, of the sort `t`, when `a + b` is
    rw [L.WT_Plus] at w ⊢
    exact ⟨⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩, by rw [B.ty_node, B.ty_node]⟩
  · -- values: the sum of two integers commutes, and is otherwise poison
    rw [Sem.ev_Plus] at e ⊢
    rw [addV_comm]; exact e

end DivMod
