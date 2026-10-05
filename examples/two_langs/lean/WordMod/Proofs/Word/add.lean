import WordMod.Statements.Word.add
import WordMod.Lib.Rule

/-! The arm of `add` that drops the flags of a sum: they do not change its
typing nor its value. -/

namespace WordMod

open Kanon

@[kanon_arm] theorem add_plain : Word.add.r_plain.main.Stmt := by
  intro S _ _ B LBool LCfg L _ _ _ O _ f n a b _
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · simp only [Word.add.spec] at w ⊢
    exact ⟨(L.WT_WAdd _ _ _ _ _).2 ((L.WT_WAdd _ _ _ _ _).1 w), by rw [B.ty_node, B.ty_node]⟩
  · simp only [Word.add.spec, Sem.ev_WAdd] at e ⊢
    exact e

end WordMod
