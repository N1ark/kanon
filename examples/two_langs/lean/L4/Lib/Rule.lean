import L4.Lifts
import L4.Lang

/-!
# The default proof of an arm, over the terms of the language

For the arm that the language proves itself (that of `Word.double_closed`,
which its module marks `[@lean_closed]`): Kanon's rule tactic `kanon_rule`,
whose `kanon_refl` unfolds its spec, the helper `Word.twice`.
-/

namespace L4

open Kanon

attribute [kanon_wt] Term.WT Op1.WT Op2.WT Op3.WT
attribute [kanon_ev] ev evOp1 evOp2 evOp3
attribute [kanon_val] WordMod.addV Option.bind_some Option.bind_none Option.map_some
  Option.map_none
attribute [kanon_lits] v_true v_false ty

/-- The values of any term. -/
theorem ev_opt {ρ : Env} {t : Term} : ev ρ t = none ∨ ∃ v, ev ρ t = some v := by
  cases ev ρ t <;> simp

/-- A value as an integer. -/
theorem toInt_cases {v : Val} : v.toInt = none ∨ ∃ z, v.toInt = some z ∧ v = .int z := by
  cases v <;> simp [Val.toInt]

@[kanon_val] theorem toInt_int (z : Int) : (Val.int z).toInt = some z := rfl

attribute [kanon_atom_cases] ev_opt toInt_cases

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end L4
