/-!
# Options, as the generated models use them

The alternatives of a rule are guarded results (`whenSome`), and a rule
function tries its rules in turn (`firstSome`).
-/

namespace Kanon

/-- A guarded result, as the alternatives of `[@cases]` rules are written. -/
def whenSome {α : Type} (c : Bool) (a : α) : Option α := if c then some a else none

/-- The first of a list of options that is [some]. -/
def firstSome {α : Type} : List (Option α) → Option α
  | [] => none
  | o :: os => o <|> firstSome os

@[simp] theorem firstSome_nil' {α : Type} : firstSome ([] : List (Option α)) = none := rfl

@[simp] theorem firstSome_some {α : Type} {a : α} {l : List (Option α)} :
    firstSome (some a :: l) = some a := rfl

@[simp] theorem firstSome_none {α : Type} {l : List (Option α)} :
    firstSome (none :: l) = firstSome l := rfl

theorem orElse_some {α} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all

theorem whenSome_eq_some {α} {c : Bool} {a r : α} (h : whenSome c a = some r) :
    c = true ∧ a = r := by
  cases c <;> simp_all [whenSome]

/-- A property of the first option that is `some`, or else of the default. -/
theorem getD_firstSome_nil {α} {P : α → Prop} {d : α} (h : P d) :
    P ((firstSome ([] : List (Option α))).getD d) := h

theorem getD_firstSome_cons {α} {P : α → Prop} {d : α} {o : Option α} {l : List (Option α)}
    (h : ∀ r, o = some r → P r) (t : P ((firstSome l).getD d)) :
    P ((firstSome (o :: l)).getD d) := by
  cases o with
  | none => simpa [firstSome] using t
  | some r => simpa [firstSome] using h r rfl

end Kanon
