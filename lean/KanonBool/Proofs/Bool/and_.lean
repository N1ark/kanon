import KanonBool.Statements.Bool.and_
import KanonBool.Lib.Rule

/-! The arms of `Bool.and_` that `kanon_bool` does not prove: `a == x && a == y`
is false for `x` and `y` surely different, with the equalities in either order. -/

namespace KanonBool

open Classical Kanon

/-- `a == x && a == y` (with the equalities in either order) refines `false`,
for `x` and `y` surely different. -/
theorem refines_and_eq_neq {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty]
    {L : Syntax S} [Sem L] {p1 q1 p2 q2 x y a : S.Term} {t1 t2 : S.Ty}
    (o1 : (p1 = a ∧ q1 = x) ∨ (p1 = x ∧ q1 = a)) (o2 : (p2 = a ∧ q2 = y) ∨ (p2 = y ∧ q2 = a))
    (hn : L.bool_sure_neq x y = true) :
    S.Refines (L.node (L.AndK (L.node (L.EqK p1 q1) t1) (L.node (L.EqK p2 q2) t2)) L.TBool)
      L.bool_v_false := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [(Sem.v_false_eq (L := L)), L.WT_Bool, L.ty_node]
  simp only [L.WT_And, L.WT_Eq, L.ty_node] at w
  obtain ⟨⟨h1, -⟩, w1, w1'⟩ := w.2.1
  obtain ⟨⟨h2, -⟩, w2, w2'⟩ := w.2.2
  simp only [(Sem.v_false_eq (L := L)), Sem.ev_And, Sem.ev_Eq, Sem.ev_Bool] at e ⊢
  rw [pand_eq_some] at e
  rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e1, e2, -⟩
  · rfl
  · rfl
  rw [peq_eq_some] at e1 e2
  obtain ⟨u1, u1', e1, e1', hu1⟩ := e1
  obtain ⟨u2, u2', e2, e2', hu2⟩ := e2
  rw [Sem.vbool_eq_iff, eq_comm, decide_eq_true_iff] at hu1 hu2
  subst hu1 hu2
  have hx : S.ty x = S.ty a ∧ S.WT x ∧ ∃ u, S.ev ρ x = some u ∧ S.ev ρ a = some u := by
    rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h1, w1', u1, e1', e1⟩
    · exact ⟨h1.symm, w1, u1, e1, e1'⟩
  have hy : S.ty y = S.ty a ∧ S.WT y ∧ ∃ u, S.ev ρ y = some u ∧ S.ev ρ a = some u := by
    rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h2, w2', u2, e2', e2⟩
    · exact ⟨h2.symm, w2, u2, e2, e2'⟩
  obtain ⟨tx, wx, ux, ex, ea⟩ := hx
  obtain ⟨ty, wy, uy, ey, ea'⟩ := hy
  rw [ea] at ea'; cases ea'
  exact (Sem.sure_neq_sound (L := L) ρ x y ux hn (tx.trans ty.symm) wx wy ex ey).elim

@[kanon_arm] theorem Bool.and_.r_eq_neq.main.proof : Bool.and_.r_eq_neq.main.Stmt := by
  intro S _ _ L _ O hO a x t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) h2

@[kanon_arm] theorem Bool.and_.r_eq_neq.swap2.proof : Bool.and_.r_eq_neq.swap2.Stmt := by
  intro S _ _ L _ O hO a x t1 y b t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inl ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) h2

@[kanon_arm] theorem Bool.and_.r_eq_neq.swap1.proof : Bool.and_.r_eq_neq.swap1.Stmt := by
  intro S _ _ L _ O hO x a t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inr ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) h2

@[kanon_arm] theorem Bool.and_.r_eq_neq.swap1_swap2.proof :
    Bool.and_.r_eq_neq.swap1_swap2.Stmt := by
  intro S _ _ L _ O hO x a t1 y b t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inr ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) h2

end KanonBool
