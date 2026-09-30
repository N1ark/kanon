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

theorem orElse_some {α} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all

theorem whenSome_eq_some {α} {c : Bool} {a r : α} (h : whenSome c a = some r) :
    c = true ∧ a = r := by
  cases c <;> simp_all [whenSome]

end Kanon
