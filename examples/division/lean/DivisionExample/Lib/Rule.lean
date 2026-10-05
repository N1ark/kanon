import DivisionExample.Lifts
import DivisionExample.Model.mk_commut_binop
import DivisionExample.Model.Int.add

/-!
# The default proof of an arm

`kanon_auto` proves the arms that have no hand-written proof (`Proofs/`):
here, Kanon's rule tactic `kanon_rule` (`KanonCore.Proof`), given the lemmas of
the language by attributes:

- the typing (`kanon_wt`) and the evaluation (`kanon_ev`) of the nodes, and the
  operations on values (`kanon_val`), which it unfolds;
- the primitives and helpers that the bodies of the rules use (`kanon_lits`,
  `kanon_body`);
- the possible values of a term (`kanon_atom_cases`), on which it splits.

`Nodes.lean` (generated) states, from `kanon_wt` and `kanon_ev`, the typing and
the evaluation of each node (`kanon_node_wt`, `kanon_node_ev`). This file imports
the models of the helpers it tags, and nothing else of the model.
-/

namespace DivisionExample

open Kanon

attribute [kanon_wt] Term.WT Op1.WT Op2.WT
attribute [kanon_ev] ev evOp1 evOp2
attribute [kanon_val] addV
attribute [kanon_lits] Int.add ty
attribute [kanon_body] mk_commut_binop

/-- The values of a well-typed integer. -/
theorem ev_int {ρ : Env} {t : Term} (w : t.WT) (h : t.ty = .TInt) :
    ev ρ t = none ∨ ∃ z, ev ρ t = some (.int z) := by
  rcases e : ev ρ t with _ | v
  · exact .inl rfl
  · cases v with
    | int z => exact .inr ⟨z, rfl⟩

/-- The values of any term. -/
theorem ev_opt {ρ : Env} {t : Term} : ev ρ t = none ∨ ∃ v, ev ρ t = some v := by
  cases ev ρ t <;> simp

attribute [kanon_atom_cases] ev_int ev_opt

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end DivisionExample
