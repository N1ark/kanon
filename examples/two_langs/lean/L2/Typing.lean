import L2.Generated.Semantics

/-!
# The values of the sorts

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms.
-/

namespace L2

open Classical Kanon

theorem ev_ty (ρ : Env) : ∀ (e : Term) (v : Val), e.WT → ev ρ e = some v → v.Of e.ty
  | .l2 (.Var x) t, v, _, h => by
    rw [ev_l2] at h
    simp only [Node.map, Node.eval, Option.bind_eq_some_iff] at h
    obtain ⟨u, -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  | .bool (.Ite g a b) t, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at h
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩
    · show v.Of t; rw [w.1.2.2]; exact ev_ty ρ a v w.2.2.1 h
    · show v.Of t; rw [w.1.2.2, ← w.1.2.1]; exact ev_ty ρ b v w.2.2.2 h
  | .bool (.Bool _) t, v, w, h | .bool (.Not _) t, v, w, h | .bool (.And _ _) t, v, w, h
  | .bool (.Or _ _) t, v, w, h | .bool (.Eq _ _) t, v, w, h
  | .bool (.Distinct _) t, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pnot_eq_some, KanonBool.pand_eq_some,
      KanonBool.por_eq_some, KanonBool.peq_eq_some, KanonBool.pdistinct_eq_some,
      Option.some.injEq] at h
    have ht : t = .bool .TBool := by
      first | exact w.1 | exact w.1.2 | exact w.1.2.2 | (obtain ⟨_, h, -⟩ := w.1; exact h)
    subst ht
    simp only [show (KanonBool.Values.vbool (D := dom)).inj = Val.bool from rfl] at h
    obtain ⟨b, rfl⟩ : ∃ b, v = .bool b := by grind
    rfl
  | .num n t, v, w, h => by
    show v.Of t
    rw [WT_num] at w; rw [ev_num] at h
    cases n <;> simp only [NumMod.Node.wt, NumMod.Node.All] at w <;>
      simp only [NumMod.Node.map, NumMod.Node.eval, NumMod.op2_eq_some, Option.some.injEq] at h
    · subst h; exact w.1
    all_goals obtain ⟨_, _, -, -, rfl⟩ := h
    all_goals exact w.1.2.2
  | .neg (.Neg a) t, v, w, h => by
    show v.Of t
    rw [WT_neg] at w; rw [ev_neg] at h
    simp only [NegMod.Node.wt, NegMod.Node.All] at w
    simp only [NegMod.Node.map, NegMod.Node.eval, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact w.1.2

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | bool b => cases b
                · exact .inr rfl
                · exact .inl rfl
    | int _ => cases this

instance : NumMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | int z => exact ⟨z, rfl⟩
    | bool _ => cases this

end L2
