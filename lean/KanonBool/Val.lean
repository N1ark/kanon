import KanonCore.Sem
import KanonCore.ProofAttr

/-!
# The operations of the bool module on values

The values of a language are its own; `vb : Bool → V` gives its booleans. The
bool module evaluates its nodes with the operations below, which a language may
use directly in its evaluation (`ev`), where `none` is poison:

- `pand` and `por` are "parallel": a `false` (resp. `true`) operand wins over a
  poisoned one, as it would over any value of the unspecified one;
- `pnot` and `peq` are poison when an operand is, and `peq` compares values;
- `pite` only evaluates the branch it selects.
-/

namespace KanonBool

open Classical
open Kanon.Sem (OLe)

variable {V : Type} (vb : Bool → V)

/-- Parallel conjunction: `false` wins over poison. -/
noncomputable def pand (a b : Option V) : Option V :=
  if a = some (vb false) ∨ b = some (vb false) then some (vb false)
  else if a = some (vb true) ∧ b = some (vb true) then some (vb true)
  else none

/-- Parallel disjunction: `true` wins over poison. -/
noncomputable def por (a b : Option V) : Option V :=
  if a = some (vb true) ∨ b = some (vb true) then some (vb true)
  else if a = some (vb false) ∧ b = some (vb false) then some (vb false)
  else none

/-- Negation. -/
noncomputable def pnot (a : Option V) : Option V :=
  if a = some (vb true) then some (vb false)
  else if a = some (vb false) then some (vb true)
  else none

/-- Equality of values. -/
noncomputable def peq : Option V → Option V → Option V
  | some x, some y => some (vb (decide (x = y)))
  | _, _ => none

/-- The conditional, which only evaluates the branch it selects. -/
noncomputable def pite (g a b : Option V) : Option V :=
  if g = some (vb true) then a else if g = some (vb false) then b else none

/-- `Distinct`: whether the values are pairwise different. -/
noncomputable def pdistinct (vs : Option (List V)) : Option V :=
  vs.map fun vs => vb (decide vs.Nodup)

/-! The operations are unfolded once the values of their operands are known
(`kanon_val`). -/
attribute [kanon_val] pand por pnot pite

variable {vb}

/-! ## The operations by cases -/

section
variable {a b g : Option V} {x y : V}

theorem pand_eq_some :
    pand vb a b = some x ↔
      (a = some (vb false) ∧ x = vb false) ∨ (b = some (vb false) ∧ x = vb false) ∨
        (a = some (vb true) ∧ b = some (vb true) ∧ x = vb true) := by
  unfold pand; (repeat' split) <;> grind

theorem por_eq_some :
    por vb a b = some x ↔
      (a = some (vb true) ∧ x = vb true) ∨ (b = some (vb true) ∧ x = vb true) ∨
        (a = some (vb false) ∧ b = some (vb false) ∧ x = vb false) := by
  unfold por; (repeat' split) <;> grind

theorem pnot_eq_some :
    pnot vb a = some x ↔
      (a = some (vb true) ∧ x = vb false) ∨ (a = some (vb false) ∧ x = vb true) := by
  unfold pnot; (repeat' split) <;> grind

theorem peq_eq_some : peq vb a b = some x ↔ ∃ u w, a = some u ∧ b = some w ∧ x = vb (decide (u = w)) := by
  unfold peq; split <;> simp_all [eq_comm]

theorem pite_eq_some :
    pite vb g a b = some x ↔ (g = some (vb true) ∧ a = some x) ∨
      (g = some (vb false) ∧ g ≠ some (vb true) ∧ b = some x) := by
  unfold pite; (repeat' split) <;> simp_all

@[kanon_val] theorem peq_some : peq vb (some x) (some y) = some (vb (decide (x = y))) := rfl
@[kanon_val] theorem peq_none_l : peq vb none b = none := rfl
@[kanon_val] theorem peq_none_r : peq vb a none = none := by cases a <;> rfl
@[kanon_val] theorem pdistinct_none : pdistinct vb none = none := rfl
@[kanon_val] theorem pdistinct_some {vs : List V} :
    pdistinct vb (some vs) = some (vb (decide vs.Nodup)) := rfl

end

/-! ## Conditionals, lifted out of the operations -/

section
variable {c : Prop} [Decidable c] {a b x y : Option V}

@[kanon_val] theorem pand_ite_l :
    pand vb (if c then a else b) x = if c then pand vb a x else pand vb b x := by split <;> rfl
@[kanon_val] theorem pand_ite_r :
    pand vb x (if c then a else b) = if c then pand vb x a else pand vb x b := by split <;> rfl
@[kanon_val] theorem por_ite_l :
    por vb (if c then a else b) x = if c then por vb a x else por vb b x := by split <;> rfl
@[kanon_val] theorem por_ite_r :
    por vb x (if c then a else b) = if c then por vb x a else por vb x b := by split <;> rfl
@[kanon_val] theorem pnot_ite :
    pnot vb (if c then a else b) = if c then pnot vb a else pnot vb b := by split <;> rfl
@[kanon_val] theorem peq_ite_l :
    peq vb (if c then a else b) x = if c then peq vb a x else peq vb b x := by split <;> rfl
@[kanon_val] theorem peq_ite_r :
    peq vb x (if c then a else b) = if c then peq vb x a else peq vb x b := by split <;> rfl

end

/-! ## Commutativity -/

theorem pand_comm (a b : Option V) : pand vb a b = pand vb b a := by
  unfold pand; (repeat' split) <;> grind

theorem por_comm (a b : Option V) : por vb a b = por vb b a := by
  unfold por; (repeat' split) <;> grind

theorem peq_comm (a b : Option V) : peq vb a b = peq vb b a := by
  cases a <;> cases b <;> simp [peq, eq_comm]

/-! ## Monotonicity in poison -/

theorem pand_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (pand vb a b) (pand vb a' b') := by
  intro v e
  rw [pand_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr (.inl ⟨hb _ h, rfl⟩)
  · exact .inr (.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem por_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (por vb a b) (por vb a' b') := by
  intro v e
  rw [por_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr (.inl ⟨hb _ h, rfl⟩)
  · exact .inr (.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem pnot_mono {a a' : Option V} (ha : OLe a a') : OLe (pnot vb a) (pnot vb a') := by
  intro v e
  rw [pnot_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr ⟨ha _ h, rfl⟩

theorem peq_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (peq vb a b) (peq vb a' b') := by
  intro v e
  rw [peq_eq_some] at *
  obtain ⟨u, w, h1, h2, rfl⟩ := e
  exact ⟨u, w, ha _ h1, hb _ h2, rfl⟩

theorem pite_mono {g g' a a' b b' : Option V} (hg : OLe g g') (ha : OLe a a') (hb : OLe b b') :
    OLe (pite vb g a b) (pite vb g' a' b') := by
  intro v e
  rw [pite_eq_some] at e ⊢
  rcases e with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨hg _ h1, ha _ h2⟩
  · refine .inr ⟨hg _ h1, ?_, hb _ h3⟩
    rw [hg _ h1]; rw [h1] at h2; exact h2

theorem pdistinct_mono {a a' : Option (List V)} (ha : OLe a a') :
    OLe (pdistinct vb a) (pdistinct vb a') := by
  intro v e
  cases a with
  | none => cases e
  | some vs => rw [ha vs rfl]; exact e

end KanonBool
