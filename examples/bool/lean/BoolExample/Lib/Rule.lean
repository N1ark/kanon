import Lean
import BoolExample.Lifts

/-!
# The proofs of the arms

`kanon_auto`, the default proof of an arm, proves `Refines spec body` by:

1. taking the guard of the arm (`equal a b` is `a = b`, `sure_neq a b` says
   that `a` and `b` are different literals) and substituting the equalities;
2. unfolding the spec and the helpers of the body, and splitting its
   conditionals;
3. lifting the calls of the body to the rule functions (`O.f args`) to their
   specs (`kanon_lift`, by the lemmas `lift_f` of `Lifts.lean`), so that the
   rest of the proof is about raw terms;
4. proving the typing half of the refinement by `simp`, and its value half by
   case analysis on the values of the *atoms*, the subterms that the rule does
   not inspect (`kanon_cases`): each is `none`, `some false` or `some true`.

`kanon_comm` proves that swapping the operands of commutative operators
refines, for the arms that the generated proofs derive from their swapped
version.
-/

namespace BoolExample

open Kanon

/-! ## Meta-level tactics -/

section

open Lean Meta Elab Tactic

private def isAtom (e : Expr) : Bool :=
  !e.hasLooseBVars && e.isAppOfArity ``BoolExample.ev 2 &&
    !(e.getArg! 1).isAppOf ``BoolExample.Term.mk

/-- Generalizes the atoms `ev ρ x` of the goal and hypotheses, and splits on
their values: `none`, `some false` or `some true`. -/
partial def caseAtoms (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  let mut cand : Option Expr := (← instantiateMVars (← g.getType)).find? isAtom
  for d in hyps do
    if cand.isNone then
      cand := (← instantiateMVars d.type).find? isAtom
  let some a := cand | return [g]
  let (_, fvs, g) ← g.generalizeHyp #[{ expr := a, xName? := `a }] (hyps.map (·.fvarId))
  let mut res := []
  for sg in ← g.cases fvs[0]! do
    match sg.ctorName with
    | ``Option.some =>
      for sg' in ← sg.mvarId.cases sg.fields[0]!.fvarId! do
        res := res ++ (← caseAtoms sg'.mvarId)
    | _ => res := res ++ (← caseAtoms sg.mvarId)
  return res

/-- Splits on the boolean variables (the values of literals in patterns). -/
partial def caseBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isConstOf ``Bool then
      return ← (← g.cases d.fvarId).toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← caseBools sg.mvarId)
  return [g]

/-- Splits on the values of the atoms, and on the boolean variables. -/
elab "kanon_cases" : tactic => liftMetaTactic fun g => do
  (← caseAtoms g).foldlM (init := []) fun acc g => return acc ++ (← caseBools g)

/-- Destructs the conjunctions and existentials of the hypotheses. -/
partial def splitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
      return ← (← g.cases d.fvarId).toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitHyps sg.mvarId)
  return [g]

elab "kanon_split" : tactic => liftMetaTactic splitHyps

end

/-! ## Typing and commutativity -/

/-- The language has a single type, so its typing constraints always hold. -/
@[simp] theorem Ty.eq_iff (a b : Ty) : a = b ↔ True := iff_true_intro (Ty.eq_all a b)

theorem Refines.comm {op : Binop} {a b : Term} {t : Ty} (hc : op.Comm) :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op b a) t) := by
  refine Refines.intro (fun w => ⟨?_, rfl⟩) (fun ρ v _ _ e => ?_)
  · simp only [Term.WT] at w ⊢
    exact ⟨by cases op <;> simp_all [Binop.WT], w.2.2, w.2.1⟩
  · simp only [ev] at e ⊢
    cases op <;> kanon_cases <;> simp_all [evBinop, pand, por, Bool.beq_comm]

theorem Refines.comm_congr {op : Binop} {a a' b b' : Term} {t : Ty} (hc : op.Comm)
    (ha : Refines a a') (hb : Refines b b') :
    Refines (.mk (.Binop op a b) t) (.mk (.Binop op b' a') t) :=
  (Refines.binop ha hb).trans (Refines.comm hc)

/-- Proves `Refines s s'`, where `s'` is `s` with the operands of some
commutative operators swapped. -/
macro_rules
  | `(tactic| kanon_comm) => `(tactic| first
      | exact Refines.refl
      | (apply Refines.binop <;> kanon_comm)
      | (apply Refines.comm_congr <;> first | trivial | kanon_comm)
      | (apply Refines.unop <;> kanon_comm)
      | (apply Refines.triop <;> kanon_comm))

/-! ## Guards -/

theorem sure_neq_iff {a b : Term} :
    sure_neq a b = true ↔
      ∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y := by
  rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
  cases ka <;> cases kb <;> simp [sure_neq, ty, firstSome]

/-! ## Lifting -/

section

open Lean Meta Elab Tactic

/-- Proves `Refines ?S body`, where `?S` is `body` with every call `O.f args`
replaced by `f.spec args`, by the lemmas `Lib.lift_f`. -/
partial def liftGoal : TacticM Unit := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let lem := match ty.getArg! 1 |>.getAppFn with
    | .const (.str (.str root "Ops") f) _ => some (root ++ `Lib ++ Name.mkSimple ("lift_" ++ f))
    | _ => none
  match lem with
  | some l =>
    evalTactic (← `(tactic| apply $(mkIdent l) ‹Ops.Sound _›))
    for g' in ← getGoals do
      unless ← g'.isAssigned do
        setGoals [g']
        liftGoal
    setGoals []
  | none => evalTactic (← `(tactic| exact Refines.refl))

elab "kanon_lift" : tactic => do
  let mut rest := []
  for g in ← getGoals do
    setGoals [g]
    liftGoal
    rest := rest ++ (← getGoals)
  setGoals rest

end

/-- `Refines.trans`, with the lifting first, so that it determines the middle
term. -/
theorem Refines.of_lift {s m r : Term} (hl : Refines m r) (hm : Refines s m) : Refines s r :=
  hm.trans hl

/-! ## The default proof of the arms -/

/-- Proves a refinement between raw terms, from its typing half and from its
value half, by case analysis on the values of the atoms. -/
macro "kanon_sem" : tactic => `(tactic| first
  | exact Refines.refl
  | (kanon_comm; done)
  | (apply Refines.intro
     · intro w
       simp_all [Term.WT, Term.WTList, Unop.WT, Binop.WT, Triop.WT, v_true, v_false]
     · intro ρ v w w' e
       simp only [ev, evList, v_true, v_false] at e ⊢
       kanon_cases
       all_goals simp_all [evUnop, evBinop, evTriop, pand, por]))

/-- The default proof of an arm. -/
macro "kanon_rule" : tactic => `(tactic| (
  intro O hO
  intros
  (try simp only [equal, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, sure_neq_iff] at *)
  (try kanon_split)
  (try subst_vars)
  simp only [kanon_spec, ty, mk_commut_binop, of_bool]
  (repeat' split)
  all_goals (try (apply Refines.of_lift; case hl => kanon_lift))
  all_goals (try simp only [kanon_spec, ty])
  all_goals kanon_sem))

macro_rules | `(tactic| kanon_auto) => `(tactic| kanon_rule)

end BoolExample
