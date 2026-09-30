/-!
# Languages, generically (trial)

A language gives its operators, types and values, the typing of its operators
and their semantics. Terms, their evaluation and refinement are defined once
for every language; modules (such as soteria's `Kanon/Core/Bool.lean`) give
their rules and proofs for any language that includes them.
-/

namespace Kanon.Core

/-- Two lists related pointwise. -/
inductive Pointwise {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pointwise R [] []
  | cons {a b as bs} : R a b → Pointwise R as bs → Pointwise R (a :: as) (b :: bs)

structure Lang where
  Op : Type
  Ty : Type
  Val : Type
  [decOp : DecidableEq Op]
  [decTy : DecidableEq Ty]
  /-- The typing of an operator: the types of its operands, and of its result. -/
  wt : Op → List Ty → Ty → Prop
  /-- The values of a type. -/
  hasTy : Val → Ty → Prop
  /-- The semantics of an operator, on operands that may be poison (`none`). -/
  den : Op → List (Option Val) → Option Val
  /-- Poison operands can only make the result poison. -/
  den_mono : ∀ {o vs ws v}, Pointwise (fun a b => ∀ x, a = some x → b = some x) vs ws →
    den o vs = some v → den o ws = some v

attribute [instance] Lang.decOp Lang.decTy

variable {L : Lang}

inductive Term (L : Lang) where
  | var (x : Nat) (ty : L.Ty)
  | app (op : L.Op) (args : List (Term L)) (ty : L.Ty)

def Term.ty : Term L → L.Ty
  | .var _ t | .app _ _ t => t

mutual
def Term.WT : Term L → Prop
  | .var _ _ => True
  | .app op args t => L.wt op (Term.tys args) t ∧ Term.WTs args

def Term.WTs : List (Term L) → Prop
  | [] => True
  | a :: as => a.WT ∧ Term.WTs as

def Term.tys : List (Term L) → List L.Ty
  | [] => []
  | a :: as => a.ty :: Term.tys as
end

abbrev Env (L : Lang) := Nat → Option L.Val

mutual
def ev (ρ : Env L) : Term L → Option L.Val
  | .var x _ => ρ x
  | .app op args _ => L.den op (evs ρ args)

def evs (ρ : Env L) : List (Term L) → List (Option L.Val)
  | [] => []
  | a :: as => ev ρ a :: evs ρ as
end

open Classical in
/-- The value of a term; `none` for poison. -/
noncomputable def eval (ρ : Env L) (t : Term L) : Option L.Val :=
  if t.WT then ev ρ t else none

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
def Refines (spec r : Term L) : Prop :=
  (spec.WT → r.WT ∧ r.ty = spec.ty) ∧ ∀ ρ v, eval ρ spec = some v → eval ρ r = some v

theorem Refines.refl {t : Term L} : Refines t t := ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.trans {a b c : Term L} (h1 : Refines a b) (h2 : Refines b c) :
    Refines a c :=
  ⟨fun w => let ⟨wb, eb⟩ := h1.1 w; let ⟨wc, ec⟩ := h2.1 wb; ⟨wc, ec.trans eb⟩,
   fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩

theorem Refines.tys : ∀ {as bs : List (Term L)}, Pointwise Refines as bs → Term.WTs as →
    Term.WTs bs ∧ Term.tys bs = Term.tys as
  | [], [], .nil, _ => ⟨trivial, rfl⟩
  | _ :: _, _ :: _, .cons hab h, w => by
    simp only [Term.WTs, Term.tys] at w ⊢
    obtain ⟨wb, eb⟩ := hab.1 w.1
    obtain ⟨ws, es⟩ := Refines.tys h w.2
    exact ⟨⟨wb, ws⟩, by rw [eb, es]⟩

theorem Refines.evs {ρ : Env L} : ∀ {as bs : List (Term L)}, Pointwise Refines as bs →
    Term.WTs as → Pointwise (fun a b => ∀ x, a = some x → b = some x) (evs ρ as) (evs ρ bs)
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons hab h, w => by
    simp only [Term.WTs] at w
    refine .cons (fun x hx => ?_) (Refines.evs h w.2)
    have := hab.2 ρ x (by simp [eval, w.1, hx])
    simpa [eval, (hab.1 w.1).1] using this

@[simp] theorem ty_app {o : L.Op} {as t} : (Term.app o as t).ty = t := rfl

@[simp] theorem WT_app {o : L.Op} {as t} :
    (Term.app o as t).WT ↔ L.wt o (Term.tys as) t ∧ Term.WTs as := Iff.rfl

@[simp] theorem WTs_nil : Term.WTs ([] : List (Term L)) := trivial
@[simp] theorem WTs_cons {a : Term L} {as} : Term.WTs (a :: as) ↔ a.WT ∧ Term.WTs as := Iff.rfl
@[simp] theorem tys_nil : Term.tys ([] : List (Term L)) = [] := rfl
@[simp] theorem tys_cons {a : Term L} {as} : Term.tys (a :: as) = a.ty :: Term.tys as := rfl

/-- Refinement is a congruence. -/
theorem Refines.app {o : L.Op} {t : L.Ty} {as bs : List (Term L)}
    (h : Pointwise Refines as bs) : Refines (.app o as t) (.app o bs t) := by
  refine ⟨fun w => ?_, fun ρ v e => ?_⟩
  · simp only [Term.WT] at w
    obtain ⟨ws, es⟩ := Refines.tys h w.2
    exact ⟨⟨by rw [es]; exact w.1, ws⟩, rfl⟩
  · by_cases w : (Term.app o as t).WT
    · have w' := w
      simp only [Term.WT] at w'
      obtain ⟨ws, es⟩ := Refines.tys h w'.2
      have wb : (Term.app o bs t).WT := ⟨by rw [es]; exact w'.1, ws⟩
      simp only [eval, w, wb, ite_true, ev] at e ⊢
      exact L.den_mono (Refines.evs h w'.2) e
    · simp [eval, w] at e

@[simp] theorem eval_of_WT {ρ : Env L} {t : Term L} (w : t.WT) : eval ρ t = ev ρ t := by
  simp [eval, w]

end Kanon.Core
