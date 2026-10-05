import KanonBool.Lifts

/-!
# The rule tactic of the bool module

`kanon_bool` proves most arms of the rules of the module, over its interface: it
takes the guard, unfolds the spec, lifts the calls to the rule functions to their
specs, and proves the typing of the refinement with the typing of the nodes, and
its values by case analysis on the values of the operands. It is the tactic of
every rule function of the module (`kanon_tactic`); the other arms are proved in
`Proofs/`.
-/

namespace KanonBool

open Classical Kanon Lean Meta Elab Tactic

/-- The sort of booleans on the right of equations, which the typing of the
nodes may give on either side. -/
theorem Syntax.TBool_eq_comm {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty]
    {L : Syntax S} {x : S.Ty} : L.TBool = x ↔ x = L.TBool := eq_comm

/-- The typing and evaluation of the nodes of the module, and its literals. -/
macro "kanon_bool_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Kanon.Base.ty_node, Syntax.WT_Bool, Syntax.WT_Not, Syntax.WT_And, Syntax.WT_Or,
    Syntax.WT_Eq, Syntax.WT_Ite, Syntax.WT_Distinct, Sem.ev_Bool, Sem.ev_Not, Sem.ev_And,
    Sem.ev_Or, Sem.ev_Eq, Sem.ev_Ite, Sem.ev_Distinct, Sem.v_true_eq, Sem.v_false_eq,
    List.mapM_cons, List.mapM_nil, List.forall_mem_cons, List.not_mem_nil,
    forall_const, false_implies, implies_true, Syntax.TBool_eq_comm, true_and, and_true]
    $[$loc]?)

/-- Splits the goal on the values of the operands: booleans for the
well-typed booleans, any value otherwise. -/
elab "kanon_bool_cases" : tactic =>
  Kanon.Proof.caseAllAtoms (some #[``Sem.ev_cases, ``Sem.ev_opt])

set_option hygiene false in
/-- Proves a refinement between terms built with the nodes of the module from
their operands. -/
macro "kanon_bool_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro ?_ ?_
  · intro w
    kanon_bool_simp at w ⊢
    (try kanon_split)
    (try subst_vars)
    (try grind)
  · intro ρ v w w' e
    kanon_bool_simp at w w' e ⊢
    (try kanon_split)
    (try subst_vars)
    (try simp only [Syntax.TBool_eq_comm] at *)
    kanon_bool_cases
    all_goals (try simp [pand, por, pnot, peq, pite, pdistinct, Sem.vbool_eq_iff] at e ⊢)
    all_goals (try subst e)
    all_goals first
      | (simp_all [pand, por, pnot, peq, pite, pdistinct, Sem.vbool_eq_iff]; done)
      | (split at e <;> simp_all [pand, por, pnot, peq, pite, pdistinct, Sem.vbool_eq_iff])))

/-- Proves an arm of the module: takes its guard, unfolds its spec, splits the
conditionals of its body, lifts the calls of the body to their specs, and
proves the refinement. -/
macro "kanon_bool" : tactic => `(tactic| (
  intro _
  intros
  (try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at *)
  (try kanon_split)
  (try subst_vars)
  (try simp only [Syntax.bool_of_bool_eq])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec])
  all_goals first
    | kanon_refl
    | (kanon_comm; done)
    | kanon_bool_sem))

attribute [kanon_tactic "kanon_bool"] Bool.and_.spec Bool.or_.spec Bool.not_.spec
  Bool.ite.spec Bool.eq.spec Bool.eq_untyped.spec Bool.distinct.spec

end KanonBool
