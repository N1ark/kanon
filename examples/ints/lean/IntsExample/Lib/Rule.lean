import IntsExample.Lifts

/-!
# The default proof of an arm

`kanon_auto` proves the arms that have no hand-written proof (`Proofs.lean`):
here, Kanon's rule tactic `kanon_rule` (`KanonCore.Proof`), given the lemmas of
the language by attributes:

- the typing (`kanon_wt`) and the evaluation (`kanon_ev`) of the nodes, and the
  operations on values (`kanon_val`), which it unfolds;
- the primitives and helpers that the bodies of the rules use (`kanon_lits`,
  `kanon_body`);
- the possible values of a term (`kanon_atom_cases`), on which it splits.
-/

namespace IntsExample

open Kanon

attribute [kanon_wt] Term.WT Op1.WT Op2.WT Op3.WT OpN.WT
attribute [kanon_ev] ev evOp1 evOp2 evOp3 evOpN
attribute [kanon_val] addV ltV
attribute [kanon_lits] v_true v_false add ty
attribute [kanon_body] mk_commut_binop of_bool

/-- The values of a well-typed integer. -/
theorem ev_int {ρ : Env} {t : Term} (w : t.WT) (h : t.ty = .TInt) :
    ev ρ t = none ∨ ∃ z, ev ρ t = some (.int z) := by
  rcases e : ev ρ t with _ | v
  · exact .inl rfl
  · have := ev_ty ρ t v w e
    cases v <;> simp_all [Val.ty]

/-- The values of a well-typed boolean. -/
theorem ev_bool {ρ : Env} {t : Term} (w : t.WT) (h : t.ty = .TBool) :
    ev ρ t = none ∨ ∃ b, ev ρ t = some (.bool b) := by
  rcases e : ev ρ t with _ | v
  · exact .inl rfl
  · have := ev_ty ρ t v w e
    cases v <;> simp_all [Val.ty]

/-- The values of any term. -/
theorem ev_opt {ρ : Env} {t : Term} : ev ρ t = none ∨ ∃ v, ev ρ t = some v := by
  cases ev ρ t <;> simp

attribute [kanon_atom_cases] ev_int ev_bool ev_opt

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end IntsExample
