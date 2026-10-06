import KanonCore.Sem

/-!
# Embeddings

How a module sees a language: its sorts and the values it needs are embedded in
the types and values of the language (`Embed`), and its nodes, over the terms
of the language, in its terms (`NodeEmbed`). A language gives them by its
constructors, so that their laws hold by `rfl`.
-/

namespace Kanon

/-- `A` embedded in `B`: an injection and its partial inverse. -/
structure Embed (A B : Type) where
  inj : A → B
  proj : B → Option A
  proj_inj : ∀ a, proj (inj a) = some a
  inj_proj : ∀ b a, proj b = some a → inj a = b

attribute [simp] Embed.proj_inj

namespace Embed
variable {A B : Type} (e : Embed A B)

@[simp] theorem inj_eq_iff {a a' : A} : e.inj a = e.inj a' ↔ a = a' :=
  ⟨fun h => by simpa [e.proj_inj] using congrArg e.proj h, fun h => h ▸ rfl⟩

theorem proj_eq_some_iff {b : B} {a : A} : e.proj b = some a ↔ b = e.inj a :=
  ⟨fun h => (e.inj_proj b a h).symm, fun h => h ▸ e.proj_inj a⟩

/-- The values of `B` that `proj` reads back. -/
theorem proj_cases (b : B) : e.proj b = none ∨ ∃ a, e.proj b = some a ∧ b = e.inj a := by
  rcases h : e.proj b with _ | a
  · exact .inl rfl
  · exact .inr ⟨a, rfl, (e.inj_proj b a h).symm⟩
end Embed

/-- The nodes `N` of a module, over the terms of a language of semantics `S`,
embedded in its terms, at a sort. -/
structure NodeEmbed (N : Type → Type) (S : Sem) where
  inj : N S.Term → S.Ty → S.Term
  proj : S.Term → Option (N S.Term)
  ty_inj : ∀ n t, S.ty (inj n t) = t
  proj_inj : ∀ n t, proj (inj n t) = some n
  inj_proj : ∀ e n, proj e = some n → inj n (S.ty e) = e

attribute [simp] NodeEmbed.ty_inj NodeEmbed.proj_inj

namespace NodeEmbed
variable {N : Type → Type} {S : Sem} (E : NodeEmbed N S)

theorem exists_of_proj {e : S.Term} {n : N S.Term} (h : E.proj e = some n) :
    ∃ t, e = E.inj n t := ⟨_, (E.inj_proj e n h).symm⟩

@[simp] theorem inj_eq_iff {n n' : N S.Term} {t t' : S.Ty} :
    E.inj n t = E.inj n' t' ↔ n = n' ∧ t = t' := by
  constructor
  · intro h
    have h1 := congrArg E.proj h
    have h2 := congrArg S.ty h
    simp only [E.proj_inj, Option.some.injEq, E.ty_inj] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl
end NodeEmbed

/-! ## Refinement of the children of a node -/

/-- Two lists related elementwise: the relation of the list children of two
nodes (`Node.Rel`). -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b l l'} : R a b → Forall₂ R l l' → Forall₂ R (a :: l) (b :: l')

@[simp] theorem forall₂_nil {α β : Type} {R : α → β → Prop} : Forall₂ R [] [] := .nil

@[simp] theorem forall₂_cons {α β : Type} {R : α → β → Prop} {a b l l'} :
    Forall₂ R (a :: l) (b :: l') ↔ R a b ∧ Forall₂ R l l' :=
  ⟨fun h => by cases h; exact ⟨by assumption, by assumption⟩, fun ⟨h, t⟩ => .cons h t⟩

theorem Forall₂.refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) : ∀ l, Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (h a) (Forall₂.refl h l)

namespace Sem
variable {S : Sem}

/-- Refined lists of terms: their elements are well-typed, of the same types,
and their values refined. -/
theorem forall₂_refines {l l' : List S.Term} (h : Forall₂ S.Refines l l')
    (w : ∀ x ∈ l, S.WT x) :
    (∀ x ∈ l', S.WT x) ∧ (∀ e, (∀ x ∈ l, S.ty x = e) → ∀ x ∈ l', S.ty x = e) ∧
      ∀ ρ, Forall₂ OLe (l.map (S.ev ρ)) (l'.map (S.ev ρ)) := by
  induction h with
  | nil => simp
  | @cons a a' l l' ha _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at w ⊢
    obtain ⟨wa, wl⟩ := w
    obtain ⟨ih1, ih2, ih3⟩ := ih wl
    obtain ⟨wa', sa⟩ := ha.syn wa
    refine ⟨⟨wa', ih1⟩, fun e ⟨he, hl⟩ => ⟨sa.trans he, ih2 e hl⟩, fun ρ => ?_⟩
    simp only [List.map_cons, forall₂_cons]
    exact ⟨ha.ev wa ρ, ih3 ρ⟩

@[simp] theorem forall₂_refines_refl (l : List S.Term) : Forall₂ S.Refines l l :=
  Forall₂.refl (fun _ => Refines.refl) l

/-- The values of a list of children, if none is poison, refined. -/
theorem OLe.mapM {α : Type} {l l' : List (Option α)} (h : Forall₂ OLe l l') :
    OLe (l.mapM id) (l'.mapM id) := by
  induction h with
  | nil => exact OLe.refl _
  | @cons a a' l l' ha _ ih =>
    intro v e
    simp only [List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff] at e ⊢
    obtain ⟨x, hx, xs, hxs, e⟩ := e
    exact ⟨x, ha _ hx, xs, ih _ hxs, e⟩

end Sem

end Kanon
