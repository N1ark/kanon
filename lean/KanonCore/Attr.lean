import Lean

/-!
# The attributes of proofs

- `kanon_spec`: the specs of the rule functions (`f.spec`), which the rule
  tactics unfold;
- `kanon_tactic "tac"`, on the spec of a rule function: the tactic that proves
  its arms;
- `kanon_arm`, on a theorem: a hand-written proof of the statement of an arm,
  or of the commutativity of an operator.
-/

/-- The specs of the rule functions (`f.spec`), unfolded by the rule tactics. -/
register_simp_attr kanon_spec

open Lean

namespace Kanon

/-- The tactics given to rule functions by `kanon_tactic`, by their spec. -/
initialize kanonTacticExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, t) => m.insert n t
    addImportedFn := mkStateFromImportedEntries (fun m (n, t) => m.insert n t) {}
  }

/-- The hand-written proofs of arms given by `kanon_arm`, by arm. -/
initialize kanonArmExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, p) => m.insert n p
    addImportedFn := mkStateFromImportedEntries (fun m (n, p) => m.insert n p) {}
  }

end Kanon

/-- `attribute [kanon_tactic "tac"] f.spec`: the arms of the rule function `f` are
proved by the tactic `tac` (and otherwise by `kanon_auto`), unless they have a
hand-written proof. The tactic is a string, parsed where it is used, as the
arguments of attributes are macro-expanded. -/
syntax (name := kanon_tactic) "kanon_tactic " str : attr

/-- `@[kanon_arm] theorem ... : f.r_rule.arm.Stmt`: a hand-written proof of an arm,
which its generated proof then uses; likewise for the commutativity of an
operator (`Op.comm.Stmt`). -/
syntax (name := kanon_arm) "kanon_arm" : attr

initialize registerBuiltinAttribute {
  name := `kanon_tactic
  descr := "the tactic that proves the arms of a rule function, given on its spec"
  add := fun decl stx _ => do
    unless decl.getString! == "spec" do
      throwError "kanon_tactic: {decl} is not the spec of a rule function"
    if (Kanon.kanonTacticExt.getState (← getEnv)).contains decl then
      throwError "kanon_tactic: {decl} already has a tactic"
    let some tac := stx[1].isStrLit? | throwError "kanon_tactic: expected a string"
    if let .error e := Parser.runParserCategory (← getEnv) `tactic tac then
      throwError "kanon_tactic: {e}"
    modifyEnv (Kanon.kanonTacticExt.addEntry · (decl, tac))
}

initialize registerBuiltinAttribute {
  name := `kanon_arm
  descr := "a hand-written proof of the statement `X.Stmt` of an arm `X`"
  add := fun decl _ _ => do
    let some info := (← getEnv).find? decl | throwError "kanon_arm: unknown {decl}"
    let .const stmt [] := info.type
      | throwError "kanon_arm: {decl} does not prove the statement of an arm"
    let arm := stmt.getPrefix
    -- `R.f.r_rule.arm.Stmt` (or `R.Op.C.comm.Stmt`), in the namespace `R` of the model
    unless stmt.getString! == "Stmt" && arm.components.length ≥ 4 do
      throwError "kanon_arm: {decl} does not prove the statement of an arm"
    if let some p := (Kanon.kanonArmExt.getState (← getEnv)).find? arm then
      throwError "kanon_arm: {arm} is already proved by {p}"
    modifyEnv (Kanon.kanonArmExt.addEntry · (arm, decl))
}
