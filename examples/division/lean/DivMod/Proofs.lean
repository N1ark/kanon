import Generated.DivMod.Statements.Int.div
import Generated.DivMod.Statements.Int.sq1

/-!
# The arms that the default tactic does not prove

The subsort `TNonzero` asks for them: the arm `a / a = 1` assumes that its
divisor is not zero (the quotient by zero is zero), and `sq1` must return a
term that is not zero (`Nonzero`), its spec as its only rule.
-/

namespace DivMod

open Kanon

/-- `a / a` is refined by `1`, when `a` is not zero. -/
@[kanon_arm] theorem Int.div.r_self.main.proof : Int.div.r_self.main.Stmt := by
  intro S _ _ O hO v1 v2 hs hg
  simp only [decide_eq_true_eq] at hg
  subst hg
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [Int.div.spec, WT_mk, Node.wt, Node.All] at w ⊢
  · have hw : S.WT v1 := by
      simp only [Int.div.spec, WT_mk, Node.wt, Node.All] at w
      exact w.2.1
    simp only [Int.div.spec, ev_mk, Node.map, Node.eval, op2_eq_some] at e ⊢
    obtain ⟨m, n, hm, hn, rfl⟩ := e
    rw [hm] at hn
    simp only [Option.some.injEq, Embed.inj_eq_iff] at hn
    subst hn
    have hne : m ≠ 0 := hs ρ m (by rw [Kanon.Sem.eval_eq_ev hw, hm])
    rw [Int.ediv_self hne]

/-- The square of an integer plus one is not zero. -/
theorem nonzero_sq1 {S : Kanon.Sem} [Lang S] (v : S.Term) (t : S.Ty) :
    Nonzero (mk (.Sq1 v) t) := by
  intro ρ z h
  have w := Kanon.Sem.eval_WT h
  rw [Kanon.Sem.eval_eq_ev w, ev_mk] at h
  simp only [Node.map, Node.eval, op1_eq_some, Option.some.injEq, Embed.inj_eq_iff] at h
  obtain ⟨x, -, rfl⟩ := h
  have : 0 ≤ x * x := by
    rcases Int.le_total 0 x with h0 | h0
    · exact Int.mul_nonneg h0 h0
    · exact Int.mul_nonneg_of_nonpos_of_nonpos h0 h0
  omega

@[kanon_arm] theorem Int.sq1.spec_post.proof : Int.sq1.spec_post.Stmt :=
  fun v => nonzero_sq1 v _

@[kanon_arm] theorem Int.sq1.r_default.main.post.proof : Int.sq1.r_default.main.post.Stmt :=
  fun _ _ v => nonzero_sq1 v _

end DivMod
