import KanonCore.Node
import KanonCore.Model
import KanonCore.Sem

/-!
# The interfaces of the modules proved once

A module whose declarations say `[@@@lean_module "R"]` is proved once, for
every language that uses it, over its *interface*: Kanon generates, in
`R/Syntax.lean`, the structure `R.Syntax B L₁ … Lₙ` of what the module needs of
the terms `B : Kanon.Base S` of a language with semantics `S : Kanon.Sem` (its
sorts, the kinds of its nodes, their typing, their matchers, its primitives and
helpers, with their laws). It has the fields of the module only, and takes the
interfaces `Lᵢ` of the modules it uses as parameters, so that a module that two
others use (a diamond) is one parameter, whose lemmas apply as they are; the
module's own `R/Sem.lean` adds what it needs of the semantics (the class
`R.Sem L`, given the instances of those of the `Lᵢ`). Each language then gives
an instance of these structures, whose laws hold by definition (`kanon_law`).

- `Kanon.Base S`: the kinds of terms and the term of a kind at a sort, which
  every interface is over;
- `Kanon.OpsBase S`: the oracle `tag_le`, which the rule functions of every
  module may use;
- `kanon_law`: the proof of a law of an interface for a language, by its
  definitions.
-/

namespace Kanon

/-- The terms of a language, for the interfaces of its modules: its kinds of
terms, and the term of a kind at a sort (`Term.mk`). -/
structure Base (S : Sem) where
  /-- The kinds of terms. -/
  Kind : Type
  /-- The term of a kind, at a sort. -/
  node : Kind → S.Ty → S.Term
  ty_node : ∀ k t, S.ty (node k t) = t

/-- What the rule functions of every module may use: the oracle `tag_le`. -/
structure OpsBase (S : Sem) where
  /-- The order of the operands of commutative operators. -/
  tag_le : S.Term → S.Term → Bool

end Kanon

/-- Lemmas with which `kanon_law` proves the laws of an interface that do not
hold by definition (e.g. the typing of a list of terms, in a language that
defines it by recursion). -/
register_simp_attr kanon_law

namespace Kanon.Generic

open Lean Meta Elab Tactic

/-- Replaces the goal by the goal with the definitions applied to the
constructors of its syntax unfolded (see `Kanon.Node.unfold`). -/
elab "kanon_unfold" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let (e, r, pf) ← Kanon.Node.unfold (← instantiateMVars (← g.getType))
    let g ← g.replaceTargetDefEq e
    replaceMainGoal [← g.replaceTargetEq r pf]

/-- What the reduction of `e` is stuck on: a variable, or a term that is not a
constructor application. -/
partial def stuckOn (e : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel = 0 then return none
  let e ← whnf e
  if e.isFVar then return some e
  match e.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.recInfo r) =>
      let some major := e.getAppArgs[r.getMajorIdx]? | return none
      let major ← whnf major
      if major.isFVar then return some major
      match major.getAppFn with
      | .const c _ => if (← getEnv).isConstructor c then return none else stuckOn major (fuel - 1)
      | _ => return some major
    | _ =>
      match ← reduceMatcher? e with
      | .stuck e' => stuckOn e' (fuel - 1)
      | _ => return none
  | .proj _ _ s => stuckOn s (fuel - 1)
  | _ => return none

/-- The first discriminant of a match of `e` (outermost first) that is stuck:
what its reduction is stuck on. -/
partial def stuckDiscr (e : Expr) : MetaM (Option Expr) := do
  if (← matchMatcherApp? e).isSome then
    if let .stuck d ← reduceMatcher? e then
      if let some x ← stuckOn d then return some x
  for a in e.getAppArgs do
    if let some d ← stuckDiscr a then return some d
  match e with
  | .lam _ _ b _ | .forallE _ _ b _ | .letE _ _ _ b _ =>
    if b.hasLooseBVars then return none else stuckDiscr b
  | .mdata _ b | .proj _ _ b => stuckDiscr b
  | _ => return none

/-- Proves `lhs = rhs` where both sides compute the same thing with different
matches (a helper of the model of a language, and its body over an interface):
by `rfl` once the stuck discriminants of the matches of `lhs` are split. -/
partial def bridge (fuel : Nat) : TacticM Unit := do
  let s ← saveState
  try
    evalTactic (← `(tactic| rfl))
    return
  catch _ => s.restore
  if fuel = 0 then throwError "kanon_bridge: out of fuel"
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "kanon_bridge: not an equation"
  let some d ← g.withContext (stuckDiscr lhs) | throwError "kanon_bridge: no match to split"
  let gs ← g.withContext do
    if d.isFVar then
      return (← g.cases d.fvarId!).toList.map (·.mvarId)
    else
      let (xs, g') ← g.generalize #[{ expr := d, xName? := `kanon__d }]
      let some x := xs[0]? | throwError "kanon_bridge: generalize"
      return (← g'.cases x).toList.map (·.mvarId)
  for g' in gs do
    setGoals [g']
    bridge (fuel - 1)

/-- `kanon_bridge f`: proves the equation of a helper `f` of the model of a
language with its body over the interface of its module (whose matches are
other ones): unfolds `f` on the left, then splits the matches. -/
elab "kanon_bridge " f:ident : tactic => do
  evalTactic (← `(tactic| intros))
  let s ← saveState
  try
    evalTactic (← `(tactic| rfl))
    return
  catch _ => s.restore
  evalTactic (← `(tactic| conv => lhs; unfold $f:ident))
  bridge 16

end Kanon.Generic

/-- Proves a law of the interface of a module for a language: by definition,
or once the definitions of the language are unfolded at its nodes, with the
`kanon_law` lemmas (which may close it before any unfolding). -/
macro "kanon_law" : tactic => `(tactic| (
  intros
  first
    | rfl
    | exact Iff.rfl
    | ((try simp only [kanon_law]) <;>
       (kanon_unfold
        (try simp only [kanon_law]) <;>
        first
          | rfl
          | exact Iff.rfl
          | (simp only [and_assoc]; done)
          | (simp [kanon_law, and_assoc]; done)))))
