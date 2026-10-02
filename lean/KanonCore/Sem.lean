import KanonCore.Refinement

/-!
# The semantics of a language, generically

A language gives its terms, types, values and environments, the typing of its
terms (`ty`, `WT`) and their evaluation (`ev`, assuming well-typedness), as a
`Kanon.Sem`. The value of a term (`eval`, poison for ill-typed terms) and the
refinement of terms (`Refines`) are defined here once, with their generic facts.

A language defines its `sem : Kanon.Sem` as a reducible definition, its `eval`
and `Refines` as abbreviations of `sem.eval` and `sem.Refines`, so that the
lemmas below apply to them directly, and the instance
`Refinement Refines := Sem.refinement`. The projections of `sem` (`sem.WT t`,
`sem.ev ρ t`, …) that these lemmas produce reduce to the language's own
definitions by `simp only` or `dsimp only`.
-/

namespace Kanon

/-- The semantics of a language. -/
structure Sem where
  Term : Type
  Ty : Type
  Val : Type
  Env : Type
  /-- The type of a term. -/
  ty : Term → Ty
  /-- Syntactic well-typedness. -/
  WT : Term → Prop
  /-- Evaluation, assuming well-typedness; `none` for poison. -/
  ev : Env → Term → Option Val

namespace Sem

variable {S : Sem}

open Classical in
/-- The value of a term; `none` for poison. -/
noncomputable def eval (S : Sem) (ρ : S.Env) (t : S.Term) : Option S.Val :=
  if S.WT t then S.ev ρ t else none

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
def Refines (S : Sem) (spec r : S.Term) : Prop :=
  (S.WT spec → S.WT r ∧ S.ty r = S.ty spec) ∧
    ∀ ρ v, S.eval ρ spec = some v → S.eval ρ r = some v

/-- `a` is poison or equal to `b`. -/
def OLe {α : Type} (a b : Option α) : Prop := ∀ v, a = some v → b = some v

@[simp] theorem OLe.refl {α : Type} (a : Option α) : OLe a a := fun _ h => h
@[simp] theorem OLe.none {α : Type} (a : Option α) : OLe none a := fun _ h => by cases h

theorem eval_WT {ρ t v} (h : S.eval ρ t = some v) : S.WT t := by
  unfold eval at h; split at h <;> simp_all

theorem eval_eq_ev {ρ t} (h : S.WT t) : S.eval ρ t = S.ev ρ t := by
  simp [eval, h]

theorem Refines.refl {t : S.Term} : S.Refines t t :=
  ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.trans {a b c : S.Term} (h1 : S.Refines a b) (h2 : S.Refines b c) :
    S.Refines a c := by
  refine ⟨fun w => ?_, fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩
  obtain ⟨wb, sb⟩ := h1.1 w
  obtain ⟨wc, sc⟩ := h2.1 wb
  exact ⟨wc, sc.trans sb⟩

/-- Refinement is a preorder. A language declares it as an instance for its
`Refines` (`instance : Refinement Refines := Sem.refinement`), as instances are
not found through the type `S.Term` of the generic one. -/
theorem refinement : Refinement S.Refines := ⟨Refines.refl, Refines.trans⟩

theorem Refines.syn {a b : S.Term} (h : S.Refines a b) (w : S.WT a) :
    S.WT b ∧ S.ty b = S.ty a :=
  h.1 w

theorem Refines.sem {a b : S.Term} (h : S.Refines a b) (ρ : S.Env) :
    OLe (S.eval ρ a) (S.eval ρ b) :=
  h.2 ρ

/-- The value half of a refinement, on well-typed terms. -/
theorem Refines.ev {a b : S.Term} (h : S.Refines a b) (w : S.WT a) (ρ : S.Env) :
    OLe (S.ev ρ a) (S.ev ρ b) := fun v e => by
  have := h.2 ρ v (by rw [eval_eq_ev w]; exact e)
  rwa [eval_eq_ev (h.1 w).1] at this

theorem ty_refines {a a' : S.Term} (ha : S.Refines a a') (w : S.WT a) : S.ty a' = S.ty a :=
  (ha.syn w).2

/-- To prove a refinement, one may use the typing half in the value half. -/
theorem Refines.intro {a b : S.Term} (syn : S.WT a → S.WT b ∧ S.ty b = S.ty a)
    (sem : ∀ ρ v, S.WT a → S.WT b → S.ev ρ a = some v → S.ev ρ b = some v) :
    S.Refines a b := by
  refine ⟨syn, fun ρ v e => ?_⟩
  have w := eval_WT e
  have w' := (syn w).1
  rw [eval_eq_ev w] at e; rw [eval_eq_ev w']
  exact sem ρ v w w' e

/-- `Refines.intro`, with the value half on the values of the terms (`eval`)
rather than on their evaluation (`ev`). -/
theorem Refines.intro_eval {a b : S.Term} (syn : S.WT a → S.WT b ∧ S.ty b = S.ty a)
    (sem : ∀ ρ v, S.WT a → S.WT b → S.eval ρ a = some v → S.eval ρ b = some v) :
    S.Refines a b :=
  ⟨syn, fun ρ v e => sem ρ v (eval_WT e) (syn (eval_WT e)).1 e⟩

/-- A term refines anything when it is ill-typed. -/
theorem Refines.of_WT {s r : S.Term} (h : S.WT s → S.Refines s r) : S.Refines s r := by
  by_cases w : S.WT s
  · exact h w
  · exact ⟨fun h => absurd h w, fun ρ v e => absurd (eval_WT e) w⟩

/-- `Refines.trans`, with the lifting first so that it determines the middle
term. -/
theorem Refines.of_lift {s m r : S.Term} (hl : S.Refines m r) (hm : S.Refines s m) :
    S.Refines s r :=
  Refines.trans hm hl

end Sem

end Kanon
