import L5.Semantics

/-!
# The values of the sorts

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms, in every environment: a quantifier evaluates its body in others.
-/

namespace L5

open Classical Kanon

theorem ev_ty : ∀ (e : Term) (ρ : Env) (v : Val), e.WT → ev ρ e = some v → v.Of e.ty
  | .l5 (.Var x) t, ρ, v, _, h => by
    rw [ev_l5] at h
    simp only [Node.map, Node.eval, Option.bind_eq_some_iff] at h
    obtain ⟨u, -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  | .bool (.Ite g a b) t, ρ, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at h
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩
    · show v.Of t; rw [w.1.2.2]; exact ev_ty a ρ v w.2.2.1 h
    · show v.Of t; rw [w.1.2.2, ← w.1.2.1]; exact ev_ty b ρ v w.2.2.2 h
  | .bool (.Bool _) t, ρ, v, w, h | .bool (.Not _) t, ρ, v, w, h
  | .bool (.And _ _) t, ρ, v, w, h | .bool (.Or _ _) t, ρ, v, w, h
  | .bool (.Eq _ _) t, ρ, v, w, h | .bool (.Distinct _) t, ρ, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pnot_eq_some,
      KanonBool.pand_eq_some, KanonBool.por_eq_some, KanonBool.peq_eq_some,
      KanonBool.pdistinct_eq_some, Option.some.injEq] at h
    have ht : t = .bool .TBool := by
      first | exact w.1 | exact w.1.2 | exact w.1.2.2 | (obtain ⟨_, h, -⟩ := w.1; exact h)
    subst ht
    simp only [show (KanonBool.Values.vbool (D := dom)).inj = Val.bool from rfl] at h
    obtain ⟨b, rfl⟩ : ∃ b, v = .bool b := by grind
    rfl
  | .pack (.Pack l) t, ρ, v, w, h => by
    rw [WT_pack] at w; rw [ev_pack] at h
    simp only [PackMod.Node.wt, PackMod.pack_wt] at w
    simp only [PackMod.Node.map, PackMod.Node.eval, Option.map_eq_some_iff] at h
    obtain ⟨vs, -, rfl⟩ := h
    obtain ⟨⟨e, he, -⟩, -⟩ := w
    exact ⟨e, he⟩
  | .pack (.Some_ bs body) t, ρ, v, w, h => by
    rw [WT_pack] at w; rw [ev_pack] at h
    simp only [PackMod.Node.wt] at w
    simp only [PackMod.Node.map, PackMod.Node.eval, PackMod.someV] at h
    split at h
    · cases h; show Val.Of (.bool _) t; exact w.1.1
    · cases h

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | bool b => cases b
                · exact .inr rfl
                · exact .inl rfl
    | pack _ => obtain ⟨_, h⟩ := this; cases h

instance : PackMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | pack vs => exact ⟨vs, rfl⟩
    | bool _ => cases this

end L5
