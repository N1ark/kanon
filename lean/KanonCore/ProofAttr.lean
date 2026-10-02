import Lean

/-!
# The attributes that a language plugs into the rule tactics

The rule tactics of `KanonCore.Proof` are the same for every language; a
language gives them its lemmas by tagging them.

Simp sets, used in this order by the tactics:
- `kanon_guards`: the guards of the rules, to propositions (`equal`, …);
- `kanon_body`: unfolded in the bodies of the rules, with their specs
  (`kanon_spec`);
- `kanon_lits`: the literals and primitives;
- `kanon_wt`: the typing of the nodes;
- `kanon_ev`: the evaluation of the nodes;
- `kanon_val`: the operations on values, once the atoms are split.

Lemmas:
- `kanon_atom_cases`: the possible values of an atom, the left-hand side of
  the first equation of its conclusion (e.g. `ev ρ t`, for a hypothesis-free
  `ev_opt : ev ρ t = none ∨ ∃ v, ev ρ t = some v`, or one with hypotheses such as
  `ev_int : t.WT → t.ty = .TInt → ev ρ t = none ∨ ∃ z, ev ρ t = some (.int z)`).
  `kanon_cases` uses, for each atom, the first of them (in the order they are
  tagged) whose hypotheses are in the context (and determine its other
  arguments);
- `kanon_congr_lemma`: refining the operands of a node refines the node
  (`Refines a a' → … → Refines (op a …) (op a' …)`), for `kanon_congr` and
  `kanon_comm`;
- `kanon_comm_lemma`: the same, swapping the operands of commutative operators,
  for `kanon_comm`;
- `kanon_close_lemma`: a lemma that closes the goals that are its conclusion
  (or the symmetric of an equation, or one of its conjuncts), its hypotheses
  being in the context or proved by `kanon_close_side`, for
  `kanon_close_lemmas`.
-/

register_simp_attr kanon_guards
register_simp_attr kanon_body
register_simp_attr kanon_lits
register_simp_attr kanon_wt
register_simp_attr kanon_ev
register_simp_attr kanon_val

open Lean

namespace Kanon

/-- The lemmas given to the rule tactics, by attribute, in the order they are
tagged. -/
initialize kanonLemmaExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (a, n) => m.insert a (((m.find? a).getD #[]).push n)
    addImportedFn := mkStateFromImportedEntries
      (fun m (a, n) => m.insert a (((m.find? a).getD #[]).push n)) {}
  }

/-- The lemmas tagged with the attribute `attr`, in the order they are tagged. -/
def kanonLemmas (env : Environment) (attr : Name) : Array Name :=
  ((kanonLemmaExt.getState env).find? attr).getD #[]

/-- Registers the attribute `attr`, which adds a lemma to the set `attr`. -/
def registerKanonLemmaAttr (attr : Name) (descr : String) : IO Unit :=
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun decl _ _ => do
      unless (← getEnv).contains decl do throwError "{attr}: unknown {decl}"
      modifyEnv (kanonLemmaExt.addEntry · (attr, decl))
  }

end Kanon

/-- `@[kanon_atom_cases]`: the possible values of an atom, for `kanon_cases`. -/
syntax (name := kanon_atom_cases) "kanon_atom_cases" : attr
/-- `@[kanon_congr_lemma]`: a congruence lemma of a node, for `kanon_congr` and
`kanon_comm`. -/
syntax (name := kanon_congr_lemma) "kanon_congr_lemma" : attr
/-- `@[kanon_comm_lemma]`: a congruence lemma of a node that swaps the operands
of a commutative operator, for `kanon_comm`. -/
syntax (name := kanon_comm_lemma) "kanon_comm_lemma" : attr
/-- `@[kanon_close_lemma]`: a lemma that closes the goals it concludes, for
`kanon_close_lemmas`. -/
syntax (name := kanon_close_lemma) "kanon_close_lemma" : attr

initialize
  Kanon.registerKanonLemmaAttr `kanon_atom_cases
    "the possible values of an atom, for kanon_cases"
  Kanon.registerKanonLemmaAttr `kanon_congr_lemma
    "a congruence lemma of a node, for kanon_congr and kanon_comm"
  Kanon.registerKanonLemmaAttr `kanon_comm_lemma
    "a congruence lemma of a node that swaps commutative operands, for kanon_comm"
  Kanon.registerKanonLemmaAttr `kanon_close_lemma
    "a lemma that closes the goals it concludes, for kanon_close_lemmas"
