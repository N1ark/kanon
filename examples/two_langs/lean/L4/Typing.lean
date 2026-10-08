import L4.Generated.Semantics

/-!
# The values of the sorts

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms.
-/

namespace L4

open Classical Kanon

theorem ev_ty (ρ : Env) : ∀ (e : Term) (v : Val), e.WT → ev ρ e = some v → v.Of e.ty
  | .l4 (.Var x) t, v, _, h => by
    rw [ev_l4] at h
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
  | .word (.WRound _ _ a) t, v, w, h | .word (.WExt _ a) t, v, w, h => by
    show v.Of t
    rw [WT_word] at w; rw [ev_word] at h
    simp only [WordMod.Node.wt, WordMod.Node.All] at w
    simp only [WordMod.Node.map, WordMod.Node.eval] at h
    have := ev_ty ρ a v w.2 h
    first
      | (obtain ⟨⟨_, h1, -, h2⟩, -⟩ := w; rw [h1] at this; rw [h2])
      | (obtain ⟨⟨h1, h2⟩, -⟩ := w; rw [h1] at this; rw [h2])
    cases v with
    | bool _ => cases this
    | int _ => exact ⟨_, rfl⟩
  | .word (.WAdd _ _ a b) t, v, w, h => by
    show v.Of t
    rw [WT_word] at w; rw [ev_word] at h
    simp only [WordMod.Node.wt, WordMod.Node.All] at w
    simp only [WordMod.Node.map, WordMod.Node.eval] at h
    rw [WordMod.addV_eq_some] at h
    obtain ⟨_, _, -, -, rfl⟩ := h
    exact ⟨_, w.1.2.2⟩
  | .word (.Wd _ _) t, v, w, h | .word (.WBlob _ _) t, v, w, h | .word (.WFit _) t, v, w, h => by
    show v.Of t
    rw [WT_word] at w; rw [ev_word] at h
    simp only [WordMod.Node.wt, WordMod.Node.All] at w
    simp only [WordMod.Node.map, WordMod.Node.eval, Option.some.injEq] at h
    subst h
    first | exact ⟨_, w.1⟩ | exact ⟨_, w.1.1⟩

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | bool b => cases b
                · exact .inr rfl
                · exact .inl rfl
    | int _ => obtain ⟨_, h⟩ := this; cases h

instance : WordMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | int z => exact ⟨z, rfl⟩
    | bool _ => cases this

end L4
