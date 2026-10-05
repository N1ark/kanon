import NumMod.Statements
import NumMod.Lib.Lift

/-! The commutativity of `+`, proved once for both languages. -/

namespace NumMod

open Kanon

/-- `a + b` is refined by `b + a`. -/
@[kanon_arm] theorem add_comm : Add.comm.Stmt := by
  intro S _ _ B LBool L _ _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_Add] at w ⊢
    exact ⟨⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Add] at e ⊢
    simp only [addV] at e ⊢
    rw [op2_comm (fun m n => by rw [Int.add_comm])]; exact e

end NumMod
