import ArraysExample.Generated.Semantics

/-!
# The values of the sorts

Well-typed terms evaluate to values of their sort: integers for `TInt`,
arrays for `TVec`.
-/

namespace ArraysExample

open Classical Kanon Vec

/-- The sort of a value. -/
def Val.ty : Val → Ty
  | .int _ => .vec .TInt
  | .vec _ => .vec .TVec

theorem ev_ty (ρ : Env) : ∀ (e : Term) (v : Val), e.WT → ev ρ e = some v → v.ty = e.ty
  | .vec n t, v, w, h => by
    rw [WT_vec] at w; rw [ev_vec] at h
    have hv : ∀ z (a : Array Int), (Values.vint (D := dom)).inj z = .int z ∧
        (Values.vvec (D := dom)).inj a = .vec a := fun _ _ => ⟨rfl, rfl⟩
    cases n <;> simp only [Node.wt, Node.All] at w <;>
      simp only [Node.map, Node.eval, lenV, getV, setV, Option.some.injEq,
        Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    · subst h; simp only [w.1, Term.ty]; rfl
    · subst h; simp only [w.1, Term.ty]; rfl
    · obtain ⟨_, _, rfl⟩ := h; simp [Val.ty, w.1.2, Term.ty]; rfl
    · obtain ⟨_, _, _, _, h⟩ := h; split at h <;> cases h; simp [Val.ty, w.1.2.2, Term.ty]; rfl
    · obtain ⟨_, _, _, _, _, _, h⟩ := h; split at h <;> cases h
      simp [Val.ty, w.1.2.2.2, Term.ty]; rfl

instance : Vec.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty ρ e v w he
    cases s <;> cases v
    · exact ⟨_, rfl⟩
    · cases this.trans h
    · cases this.trans h
    · exact ⟨_, rfl⟩

end ArraysExample
