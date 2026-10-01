import KanonCore.Tactics
import KanonCore.Sem
import KanonCore.ProofAttr

/-!
# The rule tactics, for any language

The tactics that prove the arms of the rules, given the semantics of the
language as a `Kanon.Sem` (whose `Refines` the statements of the arms use) and
its lemmas, by the attributes of `KanonCore.ProofAttr`:

- `kanon_split` destructs the conjunctions and existentials of the hypotheses;
- `kanon_cases` splits on the values of the atoms of the goal and hypotheses,
  with the `kanon_atom_cases` lemmas;
- `kanon_lift` / `kanon_lift_body` lift the calls `O.f args` of the body of a
  rule, in the namespace `R` of the model, to their specs `f.spec args`, with
  the lemmas `R.Lib.lift_f` that Kanon generates;
- `kanon_rule_lift` takes the guard of an arm, unfolds its spec, splits the
  conditionals of its body, lifts its calls, and closes the refinements that are
  reflexivity or commutativity (or `kanon_rule_close`, which the language may
  give);
- `kanon_rule` then proves the typing half of the refinement (`kanon_wt`) and
  reduces its value half to the values of the atoms (`kanon_sem_core`), closing
  what `simp_all` and `omega` can (`kanon_sem`, `kanon_close`);
- `kanon_congr` and `kanon_comm` (declared by `KanonCore.Tactics`) prove
  refinements by congruence, with the `kanon_congr_lemma` and
  `kanon_comm_lemma` lemmas, and the side goals left to `kanon_congr_side` and
  `kanon_comm_side`, which the language may give.
-/

namespace Kanon.Proof

open Lean Meta Elab Tactic

/-! ## Splitting the hypotheses -/

/-- Destructs the conjunctions and existentials of the hypotheses. -/
partial def splitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitHyps sg.mvarId)
  return [g]

elab "kanon_split" : tactic => liftMetaTactic splitHyps

/-! ## Splitting on the values of the atoms -/

/-- The subterms of `e` without loose bound variables, outermost first. -/
partial def closedSubterms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.hasLooseBVars then acc else acc.push e
  match e with
  | .app f a => closedSubterms a (closedSubterms f acc)
  | .lam _ t b _ | .forallE _ t b _ => closedSubterms b (closedSubterms t acc)
  | .letE _ t v b _ => closedSubterms b (closedSubterms v (closedSubterms t acc))
  | .mdata _ b => closedSubterms b acc
  | .proj _ _ b => closedSubterms b acc
  | _ => acc

/-- The hypothesis of the context of type `t`, if any. -/
def findHyp (t : Expr) : MetaM (Option Expr) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if ← isDefEq (← instantiateMVars d.type) t then return some d.toExpr
  return none

/-- The atom of the `kanon_atom_cases` lemma `n`: the left-hand side of the
first equation of its conclusion, over the variables `mvs` of `n`. -/
def atomPattern (n : Name) : MetaM (Option (Expr × Array Expr × Expr)) := do
  let c ← mkConstWithFreshMVarLevels n
  let (mvs, _, concl) ← forallMetaTelescopeReducing (← inferType c)
  let some eq := concl.find? (·.isAppOfArity ``Eq 3) | return none
  return some (c, mvs, eq.getArg! 1)

/-- The head of the atom of the lemma `n` (a constant, or `none` for a
variable), and its number of arguments. -/
def atomHead (n : Name) : MetaM (Option (Option Name × Nat)) := withNewMCtxDepth do
  let some (_, _, pat) ← atomPattern n | return none
  match pat.getAppFn with
  | .const c _ => return some (some c, pat.getAppNumArgs)
  | .mvar _ => return some (none, pat.getAppNumArgs)
  | _ => return none

/-- Whether `a` has the head `h` (see `atomHead`). -/
def hasHead (a : Expr) : Option Name × Nat → Bool
  | (some c, k) => a.isAppOfArity c k
  | (none, k) => a.getAppFn.isFVar && a.getAppNumArgs == k

/-- The proof, by the `kanon_atom_cases` lemma `n`, of the possible values of
the atom `a`, if `a` is the atom of `n` and the hypotheses of `n` are in the
context. -/
def atomCase (n : Name) (a : Expr) : MetaM (Option Expr) := withNewMCtxDepth do
  let some (c, mvs, pat) ← atomPattern n | return none
  -- a variable head must have the type of the pattern's
  if pat.getAppFn.isMVar then
    unless ← isDefEq (← inferType pat.getAppFn) (← inferType a.getAppFn) do return none
  unless ← isDefEq pat a do return none
  for mv in mvs do
    if ← mv.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType mv)
    unless ← isProp t do return none
    let some h ← findHyp t | return none
    unless ← isDefEq mv h do return none
  let pf ← instantiateMVars (mkAppN c mvs)
  if pf.hasExprMVar then return none
  return some pf

/-- Whether `e` is an application of a constructor. -/
def isCtorApp (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  return (← getEnv).isConstructor n

/-- The first atom of the goal or of the hypotheses that a `kanon_atom_cases`
lemma splits, with the proof of its possible values. Atoms are not applied to
constructors (which their evaluation unfolds). -/
def findAtomCase (g : MVarId) : MetaM (Option (Expr × Expr)) := g.withContext do
  let lemmas ← (kanonLemmas (← getEnv) `kanon_atom_cases).filterMapM fun n =>
    return (← atomHead n).map (n, ·)
  if lemmas.isEmpty then return none
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut seen : Std.HashSet Expr := {}
  for e in exprs do
    for s in closedSubterms e #[] do
      unless s.isApp && !seen.contains s do continue
      seen := seen.insert s
      if ← s.getAppArgs.anyM isCtorApp then continue
      for (n, h) in lemmas do
        unless hasHead s h do continue
        if let some pf ← atomCase n s then return some (s, pf)
  return none

/-- The `rcases` pattern of a disjunction of (existentials of) equations, which
substitutes the equations. -/
partial def casesPattern (e : Expr) (inner := false) : String :=
  if e.isAppOfArity ``Or 2 then
    let p := s!"{casesPattern (e.getArg! 0) true} | {casesPattern (e.getArg! 1) true}"
    if inner then s!"({p})" else p
  else if e.isAppOfArity ``Exists 2 then
    match e.getArg! 1 with
    | .lam _ _ b _ => s!"⟨_, {casesPattern b true}⟩"
    | _ => "_"
  else if e.isAppOfArity ``And 2 then
    s!"⟨{casesPattern (e.getArg! 0) true}, {casesPattern (e.getArg! 1) true}⟩"
  else if e.isAppOfArity ``Eq 3 then "rfl"
  else "_"

/-- Splits the main goal on the values of its first atom, if any. -/
def caseAtom : TacticM Bool := do
  let g ← getMainGoal
  let some (a, pf) ← findAtomCase g | return false
  let ty ← instantiateMVars (← inferType pf)
  let (_, g) ← (← g.assert `kanon_hc ty pf).intro1P
  let g ← g.withContext do
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.fvarId
    let (_, _, g) ← g.generalizeHyp #[{ expr := a, xName? := `a }] hyps
    pure g
  replaceMainGoal [g]
  let tac := s!"rcases kanon_hc with {casesPattern ty}"
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `tactic tac)
  evalTactic stx
  return true

/-- Splits the main goal on the values of all its atoms. -/
partial def caseAtoms : TacticM Unit := do
  if ← caseAtom then
    let gs ← getGoals
    let mut out := []
    for g in gs do
      setGoals [g]
      caseAtoms
      out := out ++ (← getGoals)
    setGoals out

elab "kanon_cases" : tactic => do
  let mut out := []
  for g in ← getGoals do
    setGoals [g]
    caseAtoms
    out := out ++ (← getGoals)
  setGoals out

/-! ## Lifting the calls to rule functions to their specs

The body of a rule calls rule functions through `O`, which only refine their
specs. `kanon_lift` proves `Refines S body`, where `S` is `body` with every
call `O.f args` replaced by `f.spec args` (it is found by unification, with the
lemma `R.Lib.lift_f` that Kanon generates for the function `R.Ops.f`), so that
the rest of a proof is about raw terms only. -/

/-- The lifting lemma of the head of `e`, a call `O.f args` of a rule function. -/
def liftLemma? (e : Expr) : MetaM (Option Name) := do
  let .const (.str (.str ns "Ops") f) _ := e.getAppFn | return none
  let l := Name.mkStr (ns ++ `Lib) ("lift_" ++ f)
  return if (← getEnv).contains l then some l else none

partial def liftGoal : TacticM Unit := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some rhs := ty.getAppArgs.back? | throwError "kanon_lift: not a refinement"
  match ← liftLemma? rhs with
  | some l =>
    evalTactic (← `(tactic| apply $(mkCIdent l) (by assumption)))
    for g' in ← getGoals do
      unless ← g'.isAssigned do
        setGoals [g']
        liftGoal
    setGoals []
  | none => evalTactic (← `(tactic| exact Kanon.Sem.Refines.refl))

elab "kanon_lift" : tactic => do
  let mut rest := []
  for g in ← getGoals do
    setGoals [g]
    liftGoal
    rest := rest ++ (← getGoals)
  setGoals rest

/-- Replaces the goal `Refines s body` by `Refines s S`, with the calls of
`body` lifted to their specs in `S`. -/
macro "kanon_lift_body" : tactic =>
  `(tactic| (apply Kanon.Sem.Refines.of_lift; case hl => kanon_lift))

/-! ## Congruence -/

/-- `kanon_apply_lemmas [a, …] tac`: applies the first lemma of the attributes
`a, …` (in turn) after which `tac` succeeds on all the new goals. -/
elab "kanon_apply_lemmas " "[" attrs:ident,* "]" tac:tactic : tactic => do
  let g :: rest ← getGoals | throwError "kanon_apply_lemmas: no goal"
  let env ← getEnv
  for a in attrs.getElems do
    for n in kanonLemmas env a.getId.eraseMacroScopes do
      let s ← saveState
      try
        let gs ← g.apply (← mkConstWithFreshMVarLevels n)
        let mut out := []
        for g' in gs do
          unless ← g'.isAssigned do
            setGoals [g']
            evalTactic tac
            out := out ++ (← getGoals)
        setGoals (out ++ rest)
        return
      catch _ => s.restore
  throwError "kanon_apply_lemmas: no lemma applies"

/-- The side goals of `kanon_congr`, given by the language with `macro_rules`. -/
syntax "kanon_congr_side" : tactic

/-- The side goals of `kanon_comm`, given by the language with `macro_rules`. -/
syntax "kanon_comm_side" : tactic

/-- Proves `Refines s s'`, where `s'` is `s` with some of its subterms replaced
by terms that refine them (hypotheses of the context). -/
macro_rules
  | `(tactic| kanon_congr) => `(tactic| first
      | exact Kanon.Sem.Refines.refl
      | assumption
      | kanon_apply_lemmas [kanon_congr_lemma]
          (first
            | (intro _; rfl)
            | kanon_congr_side
            | kanon_congr))

/-- Proves `Refines s s'` for terms that only differ by the order of the
operands of commutative operators. -/
macro_rules
  | `(tactic| kanon_comm) => `(tactic| first
      | exact Kanon.Sem.Refines.refl
      | kanon_apply_lemmas [kanon_congr_lemma, kanon_comm_lemma]
          (first
            | kanon_comm_side
            | kanon_comm
            | (intro _; rfl)))

/-! ## The rule tactics -/

/-- The primitives and literals, unfolded. -/
macro "kanon_lits" : tactic => `(tactic| try simp only [kanon_lits] at *)

/-- The guards, as propositions. -/
macro "kanon_guards" : tactic => `(tactic|
  simp only [kanon_guards, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at *)

/-- Closes the refinements left by `kanon_rule_lift` in a way of the language,
given with `macro_rules`. -/
syntax "kanon_rule_close" : tactic

/-- The first steps of the proof of an arm: takes its guard, unfolds its spec,
splits the conditionals of its body, lifts the calls of the body to their
specs, and closes the refinement if it is one of reflexivity or commutativity
(or `kanon_rule_close`). -/
macro "kanon_rule_lift" : tactic => `(tactic| (
  intro _
  intros
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  simp only [kanon_spec, kanon_body]
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try first
    | exact Kanon.Sem.Refines.refl
    | (kanon_comm; done)
    | kanon_rule_close)))

/-- The typing lemmas of the nodes. -/
macro "kanon_wt_simp" : tactic => `(tactic| try
  simp only [kanon_wt, true_and, and_true] at *)

/-- Proves the typing half of a refinement between raw terms. -/
macro "kanon_wt" : tactic => `(tactic| (
  intro w
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  (try simp_all)))

set_option hygiene false in
/-- The value half of a refinement between raw terms (`Sem.Refines.intro`),
split on the values of its atoms; its hypothesis is `e`. -/
macro "kanon_sem_core" : tactic => `(tactic| (
  intro ρ v w w' e
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_ev] at e ⊢)
  kanon_cases
  all_goals (try simp only [kanon_val] at e ⊢)
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at e ⊢)
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))))

/-- Closes a goal on integers and booleans. -/
macro "kanon_close" : tactic => `(tactic| first
  | (simp_all; done)
  | (simp_all; omega)
  | omega)

set_option hygiene false in
/-- The value half: `kanon_sem_core`, then `kanon_close`, splitting the
conditionals if need be. -/
macro "kanon_sem" : tactic => `(tactic| (
  kanon_sem_core
  all_goals first
    | kanon_close
    | ((repeat' split at e) <;> (repeat' split) <;> kanon_close)
    | skip))

/-- Proves the statement of an arm, as far as it can. -/
macro "kanon_rule" : tactic => `(tactic| (
  kanon_rule_lift
  all_goals (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · kanon_wt
    · kanon_sem)))

end Kanon.Proof
