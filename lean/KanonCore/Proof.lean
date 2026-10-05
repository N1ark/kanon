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
  the lemmas `R.Lib.lift_f` that Kanon generates, leaving their hypotheses that
  are not refinements (`P v'`, for an operand at a subsort);
- `kanon_rule_lift` takes the guard of an arm, unfolds its spec, splits the
  conditionals of its body, lifts its calls, and closes the refinements that are
  reflexivity or commutativity (or `kanon_rule_close`, which the language may
  give, or a `kanon_close_lemma`);
- `kanon_rule` then proves the typing half of each refinement (`kanon_wt`) and
  reduces its value half to the values of the atoms (`kanon_sem_core`), closing
  what `simp_all` and `omega` can (`kanon_sem`, `kanon_close`);
- `kanon_close_lemmas` closes a goal by a `kanon_close_lemma` lemma, which
  `kanon_rule_lift` and `kanon_sem` try last;
- `kanon_congr` (declared by `KanonCore.Tactics`) proves refinements by
  congruence, with the `kanon_congr_lemma` lemmas, and the side goals that are
  not `_ → t = t` left to `kanon_congr_side`, which the language may give (it
  must close them), as it may give
  `kanon_congr_pre`, which `kanon_congr` first applies to each refinement;
- `kanon_comm` proves refinements up to the order of the operands of
  commutative operators, by congruence and the `kanon_comm_lemma` lemmas (the
  commutativity of the operators, `Op.comm.ok`, which the generated proofs
  tag).
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
  -- the other arguments must be determined by the hypotheses
  for mv in mvs do
    if ← mv.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType mv)
    unless ← isProp t do continue
    let some h ← findHyp t | return none
    unless ← isDefEq mv h do return none
  let pf ← instantiateMVars (mkAppN c mvs)
  if pf.hasExprMVar then return none
  return some pf

/-- Whether `e` is an application of a constructor. -/
def isCtorApp (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  return (← getEnv).isConstructor n

/-- The first atom of the goal or of the hypotheses that one of the lemmas `ls`
(by default, the `kanon_atom_cases` lemmas) splits, with the proof of its
possible values. Atoms applied to constructors, which their evaluation usually
unfolds, come last. -/
def findAtomCase (g : MVarId) (ls : Option (Array Name) := none) :
    MetaM (Option (Expr × Expr)) := g.withContext do
  let ls := ls.getD (kanonLemmas (← getEnv) `kanon_atom_cases)
  let lemmas ← ls.filterMapM fun n => return (← atomHead n).map (n, ·)
  if lemmas.isEmpty then return none
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let atomCase? (s : Expr) : MetaM (Option (Expr × Expr)) := do
    for (n, h) in lemmas do
      unless hasHead s h do continue
      if let some pf ← atomCase n s then return some (s, pf)
    return none
  let mut seen : Std.HashSet Expr := {}
  let mut onCtors := #[]
  for e in exprs do
    for s in closedSubterms e #[] do
      unless s.isApp && !seen.contains s do continue
      seen := seen.insert s
      if ← s.getAppArgs.anyM isCtorApp then
        onCtors := onCtors.push s
        continue
      if let some r ← atomCase? s then return some r
  for s in onCtors do
    if let some r ← atomCase? s then return some r
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
def caseAtom (ls : Option (Array Name) := none) : TacticM Bool := do
  let g ← getMainGoal
  let some (a, pf) ← findAtomCase g ls | return false
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
partial def caseAtoms (ls : Option (Array Name) := none) : TacticM Unit := do
  if ← caseAtom ls then
    let gs ← getGoals
    let mut out := []
    for g in gs do
      setGoals [g]
      caseAtoms ls
      out := out ++ (← getGoals)
    setGoals out

/-- Splits all the goals on the values of their atoms. -/
def caseAllAtoms (ls : Option (Array Name) := none) : TacticM Unit := do
  let mut out := []
  for g in ← getGoals do
    setGoals [g]
    caseAtoms ls
    out := out ++ (← getGoals)
  setGoals out

elab "kanon_cases" : tactic => caseAllAtoms

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

/-- Lifts the main goal, a refinement `Refines S body`, by the lifting lemmas
of the calls of `body`. Returns the hypotheses of these lemmas that are not
refinements (that an argument of a function at a subsort satisfies its
predicate, `P v'`), which are left to the caller. -/
partial def liftGoal : TacticM (List MVarId) := do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Kanon.Sem.Refines 3 do return [g]
  match ← liftLemma? (ty.getArg! 2) with
  | some l =>
    evalTactic (← `(tactic| apply $(mkCIdent l) (by assumption)))
    let mut out := []
    for g' in ← getGoals do
      unless ← g'.isAssigned do
        setGoals [g']
        out := out ++ (← liftGoal)
    return out
  | none =>
    evalTactic (← `(tactic| exact Kanon.Sem.Refines.refl))
    return []

/-- Lifts each goal, leaving the hypotheses that are not refinements. -/
elab "kanon_lift" : tactic => do
  let mut rest := []
  for g in ← getGoals do
    setGoals [g]
    rest := rest ++ (← liftGoal)
  setGoals rest

/-- Replaces the goal `Refines s body` by `Refines s S`, with the calls of
`body` lifted to their specs in `S`. The hypotheses of the lifting lemmas that
are not refinements (`P v'`, for a function with an operand at a subsort) are
left after it; as they only hold of well-typed terms, they are then proved
under the hypothesis `kw : WT s` that the spec is well-typed. -/
elab "kanon_lift_body" : tactic => do
  let lift : TacticM (List MVarId × List MVarId) := do
    evalTactic (← `(tactic| apply Kanon.Sem.Refines.of_lift))
    let gs ← getGoals
    let some hl ← gs.findM? (fun g => return (← g.getTag) == `hl)
      | throwError "kanon_lift_body: no goal"
    setGoals [hl]
    let side ← liftGoal
    let rest ← gs.filterM fun g => return g != hl && !(← g.isAssigned)
    return (rest, side)
  let s ← saveState
  let (rest, side) ← lift
  if side.isEmpty then setGoals rest
  else
    s.restore
    evalTactic (← `(tactic| refine Kanon.Sem.Refines.of_WT (fun $(mkIdent `kw) => ?_)))
    let (rest, side) ← lift
    setGoals (rest ++ side)

/-- `kanon_on_refines tac` runs `tac` on the main goal if it is a refinement,
and leaves it otherwise (the hypotheses left by `kanon_lift_body`). -/
elab "kanon_on_refines " tac:tactic : tactic => do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  if ty.isAppOfArity ``Kanon.Sem.Refines 3 then evalTactic tac

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

/-- The side goals of `kanon_congr`, given by the language with `macro_rules`:
it is tried on each hypothesis of a congruence lemma, before `kanon_congr`
itself, and must close it. -/
syntax "kanon_congr_side" : tactic

/-- What `kanon_congr` does first to a refinement, before applying a congruence
lemma (e.g. rewriting the types of the refined terms in it), given by the
language with `macro_rules`. -/
syntax "kanon_congr_pre" : tactic

/-- Proves `Refines s s'`, where `s'` is `s` with some of its subterms replaced
by terms that refine them (hypotheses of the context). -/
macro_rules
  | `(tactic| kanon_congr) => `(tactic| first
      | exact Kanon.Sem.Refines.refl
      | assumption
      | ((try kanon_congr_pre)
         first
           | exact Kanon.Sem.Refines.refl
           | kanon_apply_lemmas [kanon_congr_lemma]
               (first
                 | (intro _; rfl)
                 | (kanon_congr_side; done)
                 | kanon_congr)))

/-- `kanon_swap_lemmas tac`: proves `R s s'` by transitivity, from the first
`kanon_comm_lemma` lemma `R s (op b a)` (for `s = op a b`) after which `tac`
proves `R (op b a) s'`. -/
elab "kanon_swap_lemmas " tac:tactic : tactic => do
  let g :: rest ← getGoals | throwError "kanon_swap_lemmas: no goal"
  for n in kanonLemmas (← getEnv) `kanon_comm_lemma do
    let s ← saveState
    try
      setGoals [g]
      evalTactic (← `(tactic| refine Kanon.Sem.Refines.trans ($(mkCIdent n) ..) ?_))
      evalTactic tac
      setGoals ((← getGoals) ++ rest)
      return
    catch _ => s.restore
  throwError "kanon_swap_lemmas: no lemma applies"

/-- Refinement up to commutativity. -/
syntax "kanon_comm" : tactic

/-- Proves `Refines s s'` for terms that only differ by the order of the
operands of commutative operators: by congruence (`kanon_congr_lemma`) and the
commutativity of the operators (`kanon_comm_lemma`). -/
macro_rules
  | `(tactic| kanon_comm) => `(tactic| first
      | exact Kanon.Sem.Refines.refl
      | kanon_apply_lemmas [kanon_congr_lemma]
          (first
            | (intro _; rfl)
            | (kanon_congr_side; done)
            | kanon_comm)
      | kanon_swap_lemmas (first
          | exact Kanon.Sem.Refines.refl
          | kanon_apply_lemmas [kanon_congr_lemma]
              (first
                | (intro _; rfl)
                | (kanon_congr_side; done)
                | kanon_comm)))

/-! ## Closing by lemmas -/

/-- The side goals of `kanon_close_lemmas` that are not hypotheses of the
context: `omega`, and what the language gives with `macro_rules`. -/
syntax "kanon_close_side" : tactic

macro_rules | `(tactic| kanon_close_side) => `(tactic| omega)

/-- The statements proved by `pf : c`: `c`, the symmetric of an equation or
equivalence, and the conjuncts of a conjunction. -/
partial def closeForms (pf c : Expr) : MetaM (List (Expr × Expr)) := do
  let c ← instantiateMVars c
  if c.isAppOfArity ``And 2 then
    return (← closeForms (← mkAppM ``And.left #[pf]) (c.getArg! 0)) ++
      (← closeForms (← mkAppM ``And.right #[pf]) (c.getArg! 1))
  if c.isAppOfArity ``Eq 3 || c.isAppOfArity ``Iff 2 then
    let pf' ← mkAppM (if c.isAppOfArity ``Eq 3 then ``Eq.symm else ``Iff.symm) #[pf]
    return [(pf, c), (pf', ← inferType pf')]
  return [(pf, c)]

/-- Proves the hypotheses `mvs` of a lemma, once its conclusion is unified with
the goal: its instances by synthesis, its propositions by the hypotheses of the
context (first those that its conclusion determines), or by `side`. -/
def closeHyps (mvs : Array Expr) (bis : Array BinderInfo) (side : MVarId → TacticM Bool) :
    TacticM Bool := do
  let mut open_ := #[]
  for mv in mvs, bi in bis do
    if ← mv.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType mv)
    if bi.isInstImplicit then
      unless ← isDefEq mv (← synthInstance t) do return false
    else if (← isProp t) && !t.hasExprMVar then
      match ← findHyp t with
      | some h => unless ← isDefEq mv h do return false
      | none => open_ := open_.push mv
    else open_ := open_.push mv
  for mv in open_ do
    if ← mv.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType mv)
    unless ← isProp t do continue
    if let some h ← findHyp t then
      unless ← isDefEq mv h do return false
  for mv in open_ do
    if ← mv.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType mv)
    unless (← isProp t) && !t.hasExprMVar do return false
    unless ← side mv.mvarId! do return false
  return true

/-- Closes `g` by the `kanon_close_lemma` lemma `n`, if one of the statements
it proves (`closeForms`) is `g` and its hypotheses can be proved. -/
def closeByLemma (g : MVarId) (n : Name) (side : MVarId → TacticM Bool) : TacticM Bool :=
  g.withContext do
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels n
    let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType c)
    let target ← instantiateMVars (← g.getType)
    for (pf, t) in ← closeForms (mkAppN c mvs) concl do
      let s' ← saveState
      if ← withTransparency .instances (isDefEq t target) then
        if ← closeHyps mvs bis side then
          let pf ← instantiateMVars pf
          unless pf.hasExprMVar do
            g.assign pf
            return true
      s'.restore
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Closes `g` by the first `kanon_close_lemma` lemma that proves it, the
hypotheses of the lemma that are not in the context being proved by
`kanon_close_side`, or else (unless `nested`) by a lemma in turn. -/
partial def closeGoal (g : MVarId) (nested := false) : TacticM Bool := do
  let side (mv : MVarId) : TacticM Bool := do
    let s ← saveState
    try
      if (← Tactic.run mv (evalTactic (← `(tactic| kanon_close_side)))).isEmpty then
        return true
      s.restore
    catch _ => s.restore
    if nested then return false
    closeGoal mv true
  for n in kanonLemmas (← getEnv) `kanon_close_lemma do
    if ← closeByLemma g n side then return true
  return false

/-- Closes the main goal by a `kanon_close_lemma` lemma. -/
elab "kanon_close_lemmas" : tactic => do
  unless ← closeGoal (← getMainGoal) do
    throwError "kanon_close_lemmas: no lemma closes the goal"
  replaceMainGoal []

/-! ## The rule tactics -/

/-- The primitives and literals, unfolded. -/
macro "kanon_lits" : tactic => `(tactic| try simp only [kanon_lits] at *)

/-- The guards, as propositions: their boolean structure first, so that the
lemmas of the language (`kanon_guards`) then rewrite propositions rather than
the propositions of `decide`s, which would leave their instances behind. -/
macro "kanon_guards" : tactic => `(tactic| first
  | (simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at *
     try simp only [kanon_guards, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
       Bool.not_eq_true', decide_eq_false_iff_not] at *)
  | simp only [kanon_guards, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at *)

/-- Closes the refinements left by `kanon_rule_lift` in a way of the language,
given with `macro_rules`. -/
syntax "kanon_rule_close" : tactic

/-- The first steps of the proof of an arm: takes its guard, unfolds its spec,
splits the conditionals of its body, lifts the calls of the body to their
specs, and closes the refinement if it is one of reflexivity or commutativity
(or `kanon_rule_close`, or a `kanon_close_lemma`). -/
macro "kanon_rule_lift" : tactic => `(tactic| (
  intro _
  intros
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_spec, kanon_body])
  (repeat' split)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try first
    | exact Kanon.Sem.Refines.refl
    | (kanon_comm; done)
    | kanon_rule_close
    | kanon_close_lemmas)))

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

/-- Closes a goal on integers and booleans (with the `kanon_close_simp` lemmas),
or by a `kanon_close_lemma`. -/
macro "kanon_close" : tactic => `(tactic| first
  | (simp_all [kanon_close_simp]; first | done | omega)
  | omega
  | kanon_close_lemmas)

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
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    · kanon_wt
    · kanon_sem)))

end Kanon.Proof
