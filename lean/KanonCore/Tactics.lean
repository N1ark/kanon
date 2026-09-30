import KanonCore.Attr
import KanonCore.Refinement

/-!
# The tactics of the generated proofs

The generated proofs use the tactics below. `kanon_arm` and `kanon_proof%` are
defined here; the language gives the others, which depend on its semantics,
with `macro_rules`:

- `kanon_auto`: the default proof of an arm;
- `kanon_comm`: `R s s'` for terms that only differ by the order of the
  operands of commutative operators;
- `kanon_congr`: `R s s'`, where `s'` is `s` with some of its subterms replaced
  by terms that refine them (hypotheses of the context).
-/

/-- The default proof of an arm, given by the language with `macro_rules`. -/
syntax "kanon_auto" : tactic

/-- Refinement up to commutativity, given by the language with `macro_rules`. -/
syntax "kanon_comm" : tactic

/-- Refinement by congruence, given by the language with `macro_rules`. -/
syntax "kanon_congr" : tactic

/-- Closes `R spec res` from `h : <one alternative> = some res`, with `p` the
proof of that alternative: splits its match (unless its pattern always matches,
so that the conditionals of its body are not split instead), takes its guard
(`whenSome`, also for unguarded alternatives), and applies `p`, whose conclusion
must then match the goal. -/
macro "kanon_arm " h:ident p:term : tactic => `(tactic| first
  | (obtain ⟨hg, heq⟩ := Kanon.whenSome_eq_some $h:ident
     subst heq
     apply $p <;> assumption)
  | ((try split at $h:ident)
     all_goals first
       | (simp at $h:ident; done)
       | (obtain ⟨hg, heq⟩ := Kanon.whenSome_eq_some $h:ident
          subst heq
          apply $p <;> assumption)))

open Lean in
/-- The closest namespace, enclosing `ns`, of the statement of the arm `x`. -/
partial def Kanon.armRoot (env : Environment) (x ns : Name) : Option Name :=
  if env.contains (ns ++ x ++ `Stmt) then some ns
  else if ns.isAnonymous then none
  else armRoot env x ns.getPrefix

open Lean Elab Term in
/-- `kanon_proof% X`, in the namespace `R` of the model: the proof of the
statement `R.X.Stmt` of an arm, by its hand-written proof (`kanon_arm`) if there
is one, and otherwise by the tactic of its function (`kanon_tactic`), or
`kanon_auto`. -/
elab "kanon_proof% " x:ident : term => do
  let env ← getEnv
  -- the namespace of the model: the closest enclosing one that has the arm
  let some ns := Kanon.armRoot env x.getId (← getCurrNamespace)
    | throwError "kanon_proof%: unknown arm {x.getId}"
  let n := ns ++ x.getId
  if let some p := (Kanon.kanonArmExt.getState env).find? n then return mkConst p
  let f := x.getId.components.head!
  let tac ← match (Kanon.kanonTacticExt.getState env).find? (ns ++ f ++ `spec) with
    | some t => do
      let t ← ofExcept (Parser.runParserCategory env `tactic t)
      `(tactic| first | ($(⟨t⟩):tactic; done) | kanon_auto)
    | none => `(tactic| kanon_auto)
  let seq ← `(Lean.Parser.Tactic.tacticSeq| $tac:tactic)
  elabTermEnsuringType (← `(by $seq)) (some (mkConst (n ++ `Stmt)))
