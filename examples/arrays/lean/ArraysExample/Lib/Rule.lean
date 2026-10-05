import ArraysExample.Lifts
import ArraysExample.Model.Vec.in_bounds

/-!
# The default proof of an arm

`kanon_auto` proves the arms that have no hand-written proof (`Proofs/`): Kanon's
rule tactic `kanon_rule` (`KanonCore.Proof`), given the lemmas of the language by
attributes: the typing and the evaluation of the nodes, the operations on
values, the helper `in_bounds`, and the possible values of a term.
-/

namespace ArraysExample

open Kanon

attribute [kanon_wt] Term.WT Op1.WT Op2.WT Op3.WT
attribute [kanon_ev] ev evOp1 evOp2 evOp3
attribute [kanon_val] lenV getV setV inBounds
attribute [kanon_lits] Vec.in_bounds ty

/-- The values of a well-typed integer. -/
theorem ev_int {ρ : Env} {t : Term} (w : t.WT) (h : t.ty = .TInt) :
    ev ρ t = none ∨ ∃ z, ev ρ t = some (.int z) ∨ ∃ a, ev ρ t = some (.vec a) := by
  rcases e : ev ρ t with _ | (z | a)
  · exact .inl rfl
  · exact .inr ⟨z, .inl rfl⟩
  · exact .inr ⟨0, .inr ⟨a, rfl⟩⟩

/-- The values of any term. -/
theorem ev_opt {ρ : Env} {t : Term} :
    ev ρ t = none ∨ (∃ z, ev ρ t = some (.int z)) ∨ ∃ a, ev ρ t = some (.vec a) := by
  rcases ev ρ t with _ | (z | a) <;> simp

attribute [kanon_atom_cases] ev_opt

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end ArraysExample
