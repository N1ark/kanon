import KanonCore.Attr
import KanonCore.Refinement
import KanonCore.Embed

/-!
# The tactics of the generated proofs

The generated proofs use the tactics below. `kanon_arm` and `kanon_proof%` are
defined here; `kanon_auto` and `kanon_congr` are given by `KanonCore.Proof`
with `macro_rules`:

- `kanon_auto`: the default proof of an arm, and of the commutativity of an
  operator;
- `kanon_congr`: `R s s'`, where `s'` is `s` with some of its subterms replaced
  by terms that refine them (hypotheses of the context).

The arms that only swap the operands of commutative operators are proved from
the commutativity of the operators (`C.comm.ok`) and `kanon_congr`.
-/

/-- The default proof of an arm. -/
syntax "kanon_auto" : tactic

/-- Refinement by congruence. -/
syntax "kanon_congr" : tactic

namespace Kanon.Tactic

open Lean Meta Elab Tactic

/-- Replaces each variable `v` with a hypothesis `E.proj v = some n`, for a
node embedding `E`, by `E.inj n t`: the matches of the model on the nodes of
the modules, read back as the nodes they matched. -/
partial def projToInj : TacticM Unit := do
  let progress ← withMainContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, _) := ty.eq? | continue
      let lhs ← whnfR lhs
      let isProj := lhs.isAppOfArity ``NodeEmbed.proj 4 ||
        (lhs.getAppNumArgs == 1 && match lhs.getAppFn with
          | .proj ``NodeEmbed 1 _ => true
          | _ => false)
      unless isProj && lhs.appArg!.isFVar do continue
      let g ← (← getMainGoal).rename d.fvarId `kanon_hp
      replaceMainGoal [g]
      let h := mkIdent `kanon_hp
      let e := mkIdent `kanon_he
      evalTactic (← `(tactic| (
        have $e := Kanon.NodeEmbed.exists_of_proj _ $h
        clear $h
        obtain ⟨_, $e⟩ := $e
        subst $e)))
      return true
    return false
  if progress then projToInj

/-- `kanon_proj`: see `projToInj`. -/
elab "kanon_proj" : tactic => projToInj

/-- Splits the match at the head of the left-hand side of `h : lhs = rhs`,
repeatedly: the nested matches of an alternative of the model, and not the
conditionals of its result. -/
partial def splitMatches (h : Name) : TacticM Unit := do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let isMatch ← g.withContext do
      let some d := (← getLCtx).findFromUserName? h | return false
      let some (_, lhs, _) := (← instantiateMVars d.type).eq? | return false
      let lhs := lhs.consumeMData
      return (← Meta.isMatcherApp lhs) || lhs.isAppOf ``ite || lhs.isAppOf ``dite
    if isMatch then
      let s ← saveState
      try
        evalTactic (← `(tactic| split at $(mkIdent h):ident))
        splitMatches h
      catch _ => s.restore
    out := out ++ (← getGoals)
  setGoals out

elab "kanon_split_matches " h:ident : tactic => splitMatches h.getId

end Kanon.Tactic

/-- Closes `R spec res` from `h : <an alternative of a rule> = some res`, with
`p` the proof of the statement of that alternative: splits its matches, reads
the nodes they matched back (`kanon_proj`), takes its guard (`whenSome`), and
applies `p`. The cases where a pattern does not match are closed by `cases`
(`h : none = some res`). -/
macro "kanon_arm " h:ident p:term : tactic => `(tactic| (
  (try dsimp only at $h:ident)
  kanon_split_matches $h
  all_goals first
    | (cases $h:ident; done)
    | (kanon_proj
       obtain ⟨hg, heq⟩ := Kanon.whenSome_eq_some $h:ident
       subst heq
       apply $p <;> assumption)))

open Lean in
/-- The closest namespace, enclosing `ns`, of the statement of the arm `x`. -/
partial def Kanon.armRoot (env : Environment) (x ns : Name) : Option Name :=
  if env.contains (ns ++ x ++ `Stmt) then some ns
  else if ns.isAnonymous then none
  else armRoot env x ns.getPrefix

open Lean in
/-- The rule function of the arm `x`: `f` for `f.r_rule.arm`,
`f.r_rule.arm.post` and `f.spec_post`, where `f` may be qualified (`M.f`);
`none` for the commutativity of an operator (`C.comm`). -/
def Kanon.armFn : Name → Option Name
  | .str (.str (.str f r) _) "post" =>
    if !f.isAnonymous && r.startsWith "r_" then some f else none
  | .str f "spec_post" => if f.isAnonymous then none else some f
  | .str (.str f r) _ => if !f.isAnonymous && r.startsWith "r_" then some f else none
  | _ => none

open Lean Elab Term in
/-- `kanon_proof% X`, in the namespace `R` of a module: the proof of the
statement `R.X.Stmt` of an arm (or of the commutativity of an operator,
`X = C.comm`), by its hand-written proof (`kanon_arm`) if there is one, and
otherwise by the tactic of its function (`kanon_tactic` on its spec, or on the
module's `Ops`), or `kanon_auto`. -/
elab "kanon_proof% " x:ident : term => do
  let env ← getEnv
  let some ns := Kanon.armRoot env x.getId (← getCurrNamespace)
    | throwError "kanon_proof%: unknown arm {x.getId}"
  let n := ns ++ x.getId
  if let some p := (Kanon.kanonArmExt.getState env).find? n then return mkConst p
  let tacs := Kanon.kanonTacticExt.getState env
  let tac ← match ((Kanon.armFn x.getId).bind fun f => tacs.find? (ns ++ f ++ `spec)).orElse
      fun _ => tacs.find? (ns ++ `Ops) with
    | some t => do
      let t ← ofExcept (Parser.runParserCategory env `tactic t)
      `(tactic| first | ($(⟨t⟩):tactic; done) | kanon_auto)
    | none => `(tactic| kanon_auto)
  let seq ← `(Lean.Parser.Tactic.tacticSeq| $tac:tactic)
  elabTermEnsuringType (← `(by $seq)) (some (mkConst (n ++ `Stmt)))
