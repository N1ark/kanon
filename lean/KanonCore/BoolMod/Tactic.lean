import KanonCore.BoolMod.Lang

/-!
# The rule tactic of the bool module

`kanon_bool` proves most arms of the rules of the module: it takes the guard,
lifts the calls to the rule functions to their specs, and proves the typing of
the refinement with the typing of the nodes, and its values by case analysis on
the values of the operands.
-/

namespace Kanon.BoolMod

open Classical Kanon Lean Meta Elab Tactic

/-- The typing and evaluation of the nodes of the module. -/
macro "kanon_bool_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Lang.vtrue, Lang.vfalse, Lang.mkNot, Lang.mkAnd, Lang.mkOr, Lang.mkEq, Lang.mkIte,
    Lang.mkDistinct, Lang.ty_mk, Lang.WT_lit, Lang.WT_not, Lang.WT_and, Lang.WT_or, Lang.WT_eq,
    Lang.WT_ite, Lang.WT_distinct, Lang.ev_lit, Lang.ev_not, Lang.ev_and, Lang.ev_or,
    Lang.ev_eq, Lang.ev_ite, Lang.ev_distinct, List.mapM_cons, List.mapM_nil, true_and,
    and_true] $[$loc]?)

/-- Splits the goal on the values of the operands: booleans for the
well-typed booleans, any value otherwise. -/
elab "kanon_bool_cases" : tactic =>
  Kanon.Proof.caseAllAtoms (some #[``Lang.ev_cases, ``Lang.ev_opt])

set_option hygiene false in
/-- Proves a refinement between the terms of a language, built with the nodes of
the module from its operands. -/
macro "kanon_bool_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro ?_ ?_
  · intro w
    kanon_bool_simp at w ⊢
    (try kanon_split)
    (try subst_vars)
    (try simp_all)
  · intro ρ v w w' e
    kanon_bool_simp at w w' e ⊢
    (try kanon_split)
    (try subst_vars)
    kanon_bool_cases
    all_goals (try simp [pand, por, pnot, peq, pite, pdistinct, Lang.vbool_eq_iff] at e ⊢)
    all_goals (try subst e)
    all_goals first
      | (simp_all [pand, por, pnot, peq, pite, pdistinct, Lang.vbool_eq_iff]; done)
      | (split at e <;> simp_all [pand, por, pnot, peq, pite, pdistinct, Lang.vbool_eq_iff])))

/-- Proves an arm of the module: takes its guard, splits the conditionals of its
body, lifts the calls of the body to their specs, and proves the refinement. -/
macro "kanon_bool" : tactic => `(tactic| (
  intros
  (try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at *)
  (try kanon_split)
  (try subst_vars)
  (try simp only [Lang.of_bool])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals first
    | exact Sem.Refines.refl
    | exact Lang.refines_and_comm
    | exact Lang.refines_or_comm
    | exact Lang.refines_eq_comm
    | kanon_bool_sem))

end Kanon.BoolMod
