import NumMod.Statements.Num.less
import NumMod.Lib.Rule

/-!
# The arm `0 lt b` of `Num.less`, for `b` a positive literal

Its guard calls the helper `is_pos`, which matches a literal and is `false` on
any other term: over the interface, its equation (`num_is_pos_eq`) matches with
the matcher of `Num` (`asNum`), whose law (`asNum_sound`) gives back the literal.
-/

namespace NumMod

open Kanon

@[kanon_arm] theorem less_pos : Num.less.r_pos.main.Stmt := by
  intro S _ _ B LBool L _ _ O hO b z t h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, h⟩ := h
  rw [L.num_is_pos_eq] at h
  rcases hy : L.asNum b with _ | y
  · simp [hy, Kanon.firstSome] at h
  · simp [hy, Kanon.firstSome] at h
    obtain ⟨t', rfl⟩ : ∃ t', b = B.node (L.NumK y) t' := ⟨_, L.asNum_sound b y hy⟩
    refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · simp [Num.less.spec, L.WT_Lt, L.WT_Num, LBool.WT_Bool, KanonBool.Sem.v_true_eq, B.ty_node]
        at w ⊢
    · simp only [Num.less.spec, Sem.ev_Lt, Sem.ev_Num, op2, Sem.toInt_vint, Option.bind_some,
        Option.map_some, Option.some.injEq] at e
      rw [KanonBool.Sem.v_true_eq, KanonBool.Sem.ev_Bool, ← e]
      simp [h]

end NumMod
