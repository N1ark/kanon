import Lean

/-!
# The lemmas of the nodes

`Nodes.lean`, which Kanon generates, states for each node of the language its
typing and its evaluation, in terms of those of its operands:

```
@[kanon_node_wt] theorem Op2.Plus.wt (a b : Term) (t : Ty) :
    kanon_unfold_eq% kanon_wt (sem.WT (Term.mk (Kind.Op2 Op2.Plus a b) t)) := by
  simp only [kanon_wt]
```

The right-hand side is computed once, by `kanon_unfold_eq%`, from the lemmas
that the language gives the rule tactics (the simp sets `kanon_wt` and
`kanon_ev`), so that the proofs of the arms rewrite the nodes they meet with
these lemmas (the simp sets `kanon_node_wt` and `kanon_node_ev`) rather than
unfold the whole of the typing and of the evaluation.
-/

/-- The typing of each node, in terms of its operands (`Nodes.lean`). -/
register_simp_attr kanon_node_wt

/-- The evaluation of each node, in terms of its operands (`Nodes.lean`). -/
register_simp_attr kanon_node_ev

open Lean Meta Elab Term

/-- `kanon_unfold_eq% s e`: the equation `e' = r`, where `e'` is `e` with its
projections reduced (`sem.WT t` is the language's `Term.WT t`) and `r` is `e'`
simplified by the simp set `s` (`simp only [s]`). It fails if `s` does not
simplify `e`. -/
elab "kanon_unfold_eq% " s:ident e:term : term => do
  let e ← instantiateMVars (← elabTerm e none)
  let congr ← getSimpCongrTheorems
  let (e, _) ← dsimp e (← Simp.mkContext (simpTheorems := #[]) (congrTheorems := congr))
  let some ext ← getSimpExtension? s.getId
    | throwError "kanon_unfold_eq%: unknown simp set {s.getId}"
  let ctx ← Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := congr)
  let (r, _) ← simp e ctx
  if r.expr == e then
    throwError "kanon_unfold_eq%: {s.getId} does not simplify{indentExpr e}"
  mkEq e r.expr
