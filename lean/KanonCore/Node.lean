import Lean

/-!
# The lemmas of the nodes

`Nodes.lean`, which Kanon generates, states for each node of the language its
typing and its evaluation, in terms of those of its operands:

```
kanon_node_lemma kanon_node_ev Nodes.Op2.Plus.ev (ρ : sem.Env) (a1 a2 : Term) (t : Ty) :
  sem.ev ρ (Term.mk (Kind.Op2 Op2.Plus a1 a2) t)
```

is the theorem `Nodes.Op2.Plus.ev : ∀ ρ a1 a2 t, ev ρ (Term.mk …) = addV (ev ρ a1) (ev ρ a2)`,
tagged `kanon_node_ev`. Its right-hand side is computed once, from the
definitions of the language: the left-hand side, its projections reduced
(`sem.ev` is the language's `ev`), with the definitions applied to the node or
to its parts unfolded (`ev` at an `Op2` node, then `evOp2` at `Op2.Plus`), until
none is. The proofs of the arms then rewrite the nodes they meet with these
lemmas (the simp sets `kanon_node_wt` and `kanon_node_ev`) rather than unfold the
whole of the typing and of the evaluation.
-/

/-- The typing of each node, in terms of its operands (`Nodes.lean`). -/
register_simp_attr kanon_node_wt

/-- The evaluation of each node, in terms of its operands (`Nodes.lean`). -/
register_simp_attr kanon_node_ev

namespace Kanon.Node

open Lean Meta Elab Command Term

/-- The inductive types of the constructors in `e`: the types of the syntax of
the language, for the node of a lemma. -/
def ctorTypes (env : Environment) (e : Expr) : NameSet :=
  e.foldConsts {} fun c s =>
    match env.find? c with
    | some (.ctorInfo ci) => s.insert ci.induct
    | _ => s

/-- The definitions that `e` applies to a constructor of one of the `types`. -/
partial def toUnfold (env : Environment) (types : NameSet) (e : Expr) (acc : NameSet) :
    NameSet :=
  let ofType (a : Expr) : Bool :=
    match a.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.ctorInfo ci) => types.contains ci.induct
      | _ => false
    | _ => false
  let acc :=
    match e.getAppFn with
    | .const f _ =>
      match env.find? f with
      | some (.defnInfo _) => if e.getAppArgs.any ofType then acc.insert f else acc
      | _ => acc
    | _ => acc
  match e with
  | .app f a => toUnfold env types a (toUnfold env types f acc)
  | .lam _ t b _ | .forallE _ t b _ => toUnfold env types b (toUnfold env types t acc)
  | .letE _ t v b _ => toUnfold env types b (toUnfold env types v (toUnfold env types t acc))
  | .mdata _ b | .proj _ _ b => toUnfold env types b acc
  | _ => acc

/-- `e'`, `e` with its projections reduced, and `r` with the proof of
`e' = r`: `e'` with the definitions applied to the constructors of `e`'s
syntax unfolded, repeatedly. -/
def unfold (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let congr ← getSimpCongrTheorems
  let (e, _) ← dsimp e (← Simp.mkContext (simpTheorems := #[]) (congrTheorems := congr))
  let env ← getEnv
  let types := ctorTypes env e
  let mut cur := e
  let mut pf ← mkEqRefl e
  for _ in [0:16] do
    let fs := toUnfold env types cur {}
    if fs.isEmpty then break
    let thms ← fs.toList.foldlM (fun (s : SimpTheorems) f => s.addDeclToUnfold f) {}
    let (r, _) ← simp cur (← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := congr))
    if r.expr == cur then break
    pf ← mkEqTrans pf (← r.getProof)
    cur := r.expr
  return (e, cur, pf)

/-- `kanon_node_lemma s n binders : e`: the theorem `n : ∀ binders, e' = r` (see
`unfold`), in the simp set `s`. It fails if nothing unfolds. -/
syntax (name := kanonNodeLemma)
  "kanon_node_lemma " ident ppSpace ident (ppSpace bracketedBinder)* " : " term : command

@[command_elab kanonNodeLemma] def elabNodeLemma : CommandElab := fun stx => do
  let `(kanon_node_lemma $s:ident $n:ident $bs:bracketedBinder* : $e:term) := stx
    | throwUnsupportedSyntax
  let declName := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    Term.elabBinders bs fun xs => do
      let e ← Term.elabTerm e none
      Term.synthesizeSyntheticMVarsNoPostponing
      let (e, r, pf) ← unfold (← instantiateMVars e)
      if r == e then throwError "kanon_node_lemma: nothing unfolds in{indentExpr e}"
      let type ← instantiateMVars (← mkForallFVars xs (← mkEq e r))
      let value ← instantiateMVars (← mkLambdaFVars xs pf)
      addDecl (.thmDecl { name := declName, levelParams := [], type, value })
  let attr ← ofExcept <| Parser.runParserCategory (← getEnv) `command
    s!"attribute [{s.getId}] {declName}"
  elabCommand attr

end Kanon.Node
