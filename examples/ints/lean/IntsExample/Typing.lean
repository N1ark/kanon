import IntsExample.Generated.Semantics

/-!
# The values of the sorts

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms: the values of the sorts of the bool and int modules are booleans and
integers.
-/

namespace IntsExample

open Classical Kanon

theorem ev_ty (ρ : Env) : ∀ (e : Term) (v : Val), e.WT → ev ρ e = some v → v.ty = e.ty
  | .lang (.Var x) t, v, _, h => by
    rw [ev_lang] at h
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
    · rw [ev_ty ρ a v w.2.2.1 h, w.1.2.2]; rfl
    · rw [ev_ty ρ b v w.2.2.2 h, w.1.2.1, w.1.2.2]; rfl
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
  | .int n t, v, w, h => by
    rw [WT_int] at w; rw [ev_int] at h
    cases n <;> simp only [IntMod.Node.wt, IntMod.Node.All] at w <;>
      simp only [IntMod.Node.map, IntMod.Node.eval, IntMod.op2_eq_some, Option.some.injEq] at h
    · subst h; simp only [Val.ty, w.1]; rfl
    all_goals obtain ⟨_, _, -, -, rfl⟩ := h
    all_goals simp only [Val.ty, w.1.2.2]; rfl

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    cases s; cases v with
    | bool b => cases b
                · exact .inr rfl
                · exact .inl rfl
    | int _ => cases this.trans h

instance : IntMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    cases s; cases v with
    | int z => exact ⟨z, rfl⟩
    | bool _ => cases this.trans h

end IntsExample
