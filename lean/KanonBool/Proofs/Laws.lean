import KanonBool.Statements
import KanonBool.Lib.Lift

/-! The commutativity of the operators `&&`, `||` and `==` of the bool module. -/

namespace KanonBool

open Classical Kanon

@[kanon_arm] theorem And.comm.proof : And.comm.Stmt := by
  intro S _ _ L _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_And] at w
    exact ⟨(L.WT_And _ _ _).2 ⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_And] at e ⊢; rw [pand_comm]; exact e

@[kanon_arm] theorem Or.comm.proof : Or.comm.Stmt := by
  intro S _ _ L _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_Or] at w
    exact ⟨(L.WT_Or _ _ _).2 ⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Or] at e ⊢; rw [por_comm]; exact e

@[kanon_arm] theorem Eq.comm.proof : Eq.comm.Stmt := by
  intro S _ _ L _ a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_Eq] at w
    exact ⟨(L.WT_Eq _ _ _).2 ⟨⟨w.1.1.symm, w.1.2⟩, w.2.2, w.2.1⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Eq] at e ⊢; rw [peq_comm]; exact e

end KanonBool
