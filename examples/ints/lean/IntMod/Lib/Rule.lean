import IntMod.Lifts
import KanonBool.Lib.Rule

/-!
# The rule tactic of the int module

`kanon_int` proves the arms of the int module, over its interface, as
`kanon_bool` does those of the bool module (whose nodes the arms also use): it
takes the guard, unfolds the spec, lifts the calls to the rule functions, and
proves the refinement by the typing and the evaluation of the nodes, splitting
on the values of the operands, and on whether they are integers. It is the
default proof of the arms of the module (`kanon_auto`).
-/

namespace IntMod

open Classical Kanon

/-- The typing and evaluation of the nodes of the int and bool modules, and
their helpers. -/
macro "kanon_int_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Kanon.Base.ty_node, KanonBool.Syntax.WT_Bool, KanonBool.Syntax.WT_Not,
    KanonBool.Syntax.WT_And, KanonBool.Syntax.WT_Or, KanonBool.Syntax.WT_Eq,
    KanonBool.Syntax.WT_Ite, KanonBool.Sem.ev_Bool, KanonBool.Sem.ev_Not,
    KanonBool.Sem.ev_And, KanonBool.Sem.ev_Or, KanonBool.Sem.ev_Eq, KanonBool.Sem.ev_Ite,
    KanonBool.Sem.v_true_eq, KanonBool.Sem.v_false_eq, KanonBool.Syntax.bool_of_bool_eq,
    IntMod.Syntax.WT_Int, IntMod.Syntax.WT_Plus, IntMod.Syntax.WT_Lt, IntMod.Sem.ev_Int,
    IntMod.Sem.ev_Plus, IntMod.Sem.ev_Lt, IntMod.Syntax.int_add_eq,
    KanonBool.Syntax.TBool_eq_comm, apply_ite, ite_true, ite_false, true_and, and_true]
    $[$loc]?)

/-- The operations on values, unfolded. -/
macro "kanon_int_val" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [IntMod.addV, IntMod.ltV, KanonBool.pand, KanonBool.por, KanonBool.pnot,
    KanonBool.peq, KanonBool.pite, IntMod.Sem.toInt_vint, Option.bind_some, Option.bind_none,
    Option.map_some, Option.map_none, Option.some.injEq] $[$loc]?)

/-- Splits the goal on the values of the operands, and on whether they are
integers. -/
elab "kanon_int_cases" : tactic =>
  Kanon.Proof.caseAllAtoms
    (some #[``KanonBool.Sem.ev_cases, ``KanonBool.Sem.ev_opt, ``IntMod.Sem.toInt_cases])

set_option hygiene false in
/-- Proves a refinement between terms built with the nodes of the modules. -/
macro "kanon_int_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro ?_ ?_
  · intro w
    kanon_int_simp at w ⊢
    (try kanon_split)
    (try subst_vars)
    (try grind)
  · intro ρ v w w' e
    kanon_int_simp at w w' e ⊢
    (try kanon_split)
    (try subst_vars)
    (try simp only [KanonBool.Syntax.TBool_eq_comm] at *)
    kanon_int_cases
    all_goals (try kanon_int_val at e ⊢)
    kanon_int_cases
    all_goals (try kanon_int_val at e ⊢)
    all_goals (try subst e)
    all_goals first
      | (simp_all [IntMod.addV, IntMod.ltV, KanonBool.pnot, KanonBool.peq, KanonBool.pite,
          IntMod.Sem.toInt_vint, KanonBool.Sem.vbool_eq_iff, IntMod.Sem.vint_eq_iff, Int.add_comm]; done)
      | omega
      | (split at e <;> simp_all [IntMod.addV, IntMod.ltV, KanonBool.peq,
          IntMod.Sem.toInt_vint, KanonBool.Sem.vbool_eq_iff, IntMod.Sem.vint_eq_iff])))

/-- Proves an arm of the module. -/
macro "kanon_int" : tactic => `(tactic| (
  intro _
  intros
  (try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at *)
  (try kanon_split)
  (try subst_vars)
  (try simp only [KanonBool.Syntax.bool_of_bool_eq, IntMod.Syntax.int_add_eq])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec])
  all_goals first
    | kanon_refl
    | (kanon_comm; done)
    | kanon_int_sem))

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_int)

end IntMod
