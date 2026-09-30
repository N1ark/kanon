import BoolExample.Model
import BoolExample.Typing

/-!
# The semantics of terms, and refinement

`eval ρ t` is the value of the term `t` under the environment `ρ`, a boolean,
or `none` for *poison*:

- ill-typed terms (see `Term.WT`) are poison, and so are the variables that
  `ρ` does not give a value;
- `not` and `==` are poison when an operand is, and `ite` only evaluates the
  branch it selects;
- `&&` and `||` are "parallel": a `false` (resp. `true`) operand wins over a
  poisoned one, so that, e.g., `ite g false e` is `not g && e`.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`): whenever the raw node is well-typed, the result is
well-typed, of the same type, and whenever the raw node evaluates to a value,
the result evaluates to the same value.
-/

noncomputable section

namespace BoolExample

open Classical Kanon

/-! ## Well-typed terms -/

/-! The typing of the operators, `Unop.WT`, `Binop.WT` and `Triop.WT`, is
generated from the declarations of the nodes in `Typing.lean`. -/

mutual
/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Bool _) t => t = .TBool
  | .mk (.Unop op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Binop op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Triop op a b c) t => op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT
  | .mk (.Nop .Distinct l) t => t = .TBool ∧ ∃ e, Term.WTList e l

/-- All the terms are well-typed, of the type `e`. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty = e ∧ x.WT ∧ Term.WTList e xs
end

/-! ## Evaluation -/

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := Int → Option Bool

/-- Parallel conjunction. -/
def pand : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Parallel disjunction. -/
def por : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

def evUnop : Unop → Option Bool → Option Bool
  | .Not, a => a.map (!·)

def evBinop : Binop → Option Bool → Option Bool → Option Bool
  | .And, a, b => pand a b
  | .Or, a, b => por a b
  | .Eq, some a, some b => some (a == b)
  | .Eq, _, _ => none

def evTriop : Triop → Option Bool → Option Bool → Option Bool → Option Bool
  | .Ite, some true, a, _ => a
  | .Ite, some false, _, b => b
  | .Ite, none, _, _ => none

mutual
/-- Evaluation, assuming well-typedness. -/
def ev (ρ : Env) : Term → Option Bool
  | .mk (.Var v) _ => ρ v
  | .mk (.Bool b) _ => some b
  | .mk (.Unop op a) _ => evUnop op (ev ρ a)
  | .mk (.Binop op a b) _ => evBinop op (ev ρ a) (ev ρ b)
  | .mk (.Triop op a b c) _ => evTriop op (ev ρ a) (ev ρ b) (ev ρ c)
  | .mk (.Nop .Distinct l) _ => (evList ρ l).map (fun vs => decide vs.Nodup)

/-- The values of a list of terms, if none is poison. -/
def evList (ρ : Env) : List Term → Option (List Bool)
  | [] => some []
  | t :: ts =>
      match ev ρ t, evList ρ ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- The value of a term; `none` for poison. -/
def eval (ρ : Env) (t : Term) : Option Bool :=
  if t.WT then ev ρ t else none

/-! ## Refinement -/

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
def Refines (spec r : Term) : Prop :=
  (spec.WT → r.WT ∧ r.ty = spec.ty) ∧ ∀ ρ v, eval ρ spec = some v → eval ρ r = some v

theorem Refines.refl {t : Term} : Refines t t :=
  ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.trans {a b c : Term} (h1 : Refines a b) (h2 : Refines b c) : Refines a c :=
  ⟨fun w => let ⟨wb, eb⟩ := h1.1 w; let ⟨wc, ec⟩ := h2.1 wb; ⟨wc, ec.trans eb⟩,
   fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩

instance : Kanon.Refinement Refines := ⟨Refines.refl, Refines.trans⟩

/-! ## Assumptions on the oracles -/

/-- What the proofs assume of the oracles: that sorting by tags permutes a
list. The hash-consing order `tag_le` is arbitrary. -/
structure Oracle.Compat (orc : Oracle) : Prop where
  sort_by_tag : ∀ l, (orc.sort_by_tag l).Perm l

end BoolExample

end
