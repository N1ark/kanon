import NumMod.Lifts
import KanonBool.Lib.Rule

/-!
# The rule tactic of the num module

`kanon_num` proves the arms of the num module, over its interface, as
`kanon_bool` does those of the bool module (whose nodes the arms also use): it
takes the guard, unfolds the spec, lifts the calls to the rule functions, and
proves the refinement by the typing and the evaluation of the nodes, splitting
on the values of the operands, and on whether they are integers. It is the
default proof of the arms of the module (`kanon_auto`).
-/

namespace NumMod

open Classical Kanon

/-- The typing and evaluation of the nodes of the num and bool modules, and
their helpers. -/
macro "kanon_num_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Kanon.Base.ty_node, KanonBool.Syntax.WT_Bool, KanonBool.Syntax.WT_Not,
    KanonBool.Syntax.WT_And, KanonBool.Syntax.WT_Or, KanonBool.Syntax.WT_Eq,
    KanonBool.Syntax.WT_Ite, KanonBool.Sem.ev_Bool, KanonBool.Sem.ev_Not,
    KanonBool.Sem.ev_And, KanonBool.Sem.ev_Or, KanonBool.Sem.ev_Eq, KanonBool.Sem.ev_Ite,
    KanonBool.Sem.v_true_eq, KanonBool.Sem.v_false_eq, KanonBool.Syntax.bool_of_bool_eq,
    NumMod.Syntax.WT_Num, NumMod.Syntax.WT_Add, NumMod.Syntax.WT_Lt, NumMod.Syntax.WT_Max,
    NumMod.Sem.ev_Num, NumMod.Sem.ev_Add, NumMod.Sem.ev_Lt, NumMod.Sem.ev_Max,
    KanonBool.Syntax.TBool_eq_comm, apply_ite, ite_true, ite_false, true_and, and_true]
    $[$loc]?)

/-- The operations on values, unfolded. -/
macro "kanon_num_val" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [NumMod.op2, KanonBool.pand, KanonBool.por, KanonBool.pnot, KanonBool.peq,
    KanonBool.pite, NumMod.Sem.toInt_vint, Option.bind_some, Option.bind_none, Option.map_some,
    Option.map_none, Option.some.injEq] $[$loc]?)

/-- Splits the goal on the values of the operands, and on whether they are
integers. -/
elab "kanon_num_cases" : tactic =>
  Kanon.Proof.caseAllAtoms
    (some #[``KanonBool.Sem.ev_cases, ``KanonBool.Sem.ev_opt, ``NumMod.Sem.toInt_cases])

set_option hygiene false in
/-- Proves a refinement between terms built with the nodes of the modules. -/
macro "kanon_num_sem" : tactic => `(tactic| (
  refine Kanon.Sem.Refines.intro ?_ ?_
  · intro w
    kanon_num_simp at w ⊢
    (try kanon_split)
    (try subst_vars)
    (try grind)
  · intro ρ v w w' e
    kanon_num_simp at w w' e ⊢
    (try kanon_split)
    (try subst_vars)
    (try simp only [KanonBool.Syntax.TBool_eq_comm] at *)
    kanon_num_cases
    all_goals (try kanon_num_val at e ⊢)
    kanon_num_cases
    all_goals (try kanon_num_val at e ⊢)
    all_goals (try subst e)
    all_goals first
      | (simp_all [NumMod.op2, KanonBool.pnot, KanonBool.peq, KanonBool.pite,
          NumMod.Sem.toInt_vint, KanonBool.Sem.vbool_eq_iff, NumMod.Sem.vint_eq_iff,
          Int.add_comm]; done)
      | omega
      | (split at e <;> simp_all [NumMod.op2, KanonBool.peq, NumMod.Sem.toInt_vint,
          KanonBool.Sem.vbool_eq_iff, NumMod.Sem.vint_eq_iff])))

/-- Proves an arm of the module. -/
macro "kanon_num" : tactic => `(tactic| (
  intro _
  intros
  (try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at *)
  (try kanon_split)
  (try subst_vars)
  (try simp only [KanonBool.Syntax.bool_of_bool_eq])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec])
  all_goals first
    | kanon_refl
    | (kanon_comm; done)
    | kanon_num_sem))

attribute [kanon_tactic "kanon_num"] Num.add.spec Num.less.spec Num.max.spec Syntax

end NumMod
