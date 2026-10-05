import DivMod.Lifts

/-!
# The default proof of an arm

`kanon_auto` proves the arms of the module that have no hand-written proof
(`Proofs/`): Kanon's rule tactic `kanon_rule` (`KanonCore.Proof`), which works
over the interface of the module as over the terms of a language, given the
laws of the interface and of `Sem` by attributes:

- the typing (`kanon_wt`) and the evaluation (`kanon_ev`) of the nodes, and the
  operations on values (`kanon_val`), which it unfolds;
- the helpers that the bodies of the rules use (`kanon_lits`);
- the possible values of a term, and of a value as an integer
  (`kanon_atom_cases`), on which it splits.
-/

namespace DivMod

open Kanon

attribute [kanon_wt] Kanon.Base.ty_node Syntax.WT_Int Syntax.WT_Plus Syntax.WT_Div Syntax.WT_Sq1
attribute [kanon_ev] Sem.ev_Int Sem.ev_Plus Sem.ev_Div Sem.ev_Sq1
attribute [kanon_val] addV divV sq1V Sem.toInt_vint Sem.vint_eq_iff Option.bind_some
  Option.map_some
attribute [kanon_lits] Syntax.int_add_eq
attribute [kanon_atom_cases] Sem.ev_opt Sem.toInt_cases

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end DivMod
