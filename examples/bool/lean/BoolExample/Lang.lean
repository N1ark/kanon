import KanonBool.Sem
import BoolExample.Interface.Bool

/-!
# The language, for the bool module

Kanon's library proves the rules of the bool module once (`KanonBool`), for any
language that gives its interface (`KanonBool.Syntax`, which Kanon generates for
the language: `boolSyntax`, in `Interface.lean`) and what the module needs of its
semantics (`KanonBool.Sem`): here, the terms are variables and the nodes of the
module, and the values are booleans. The evaluation of the nodes holds by
definition (with `evList_eq` for `Distinct`); the language proves that the terms
that `Bool.sure_neq` tells apart have different values.
-/

namespace BoolExample

open Classical Kanon KanonBool

@[kanon_law] theorem evList_eq (ρ : Env) : ∀ l, evList ρ l = l.mapM (ev ρ)
  | [] => rfl
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ρ ts]
    cases ev ρ t <;> cases ts.mapM (ev ρ) <;> rfl

theorem sure_neq_iff {a b : Term} :
    Bool.sure_neq a b = true ↔
      ∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y := by
  rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
  cases ka <;> cases kb <;> simp [Bool.sure_neq, ty, firstSome]

/-- What the bool module needs of the semantics. -/
noncomputable instance boolSem : KanonBool.Sem (S := sem) boolSyntax where
  vbool := id
  vbool_inj := fun _ _ h => h
  ev_bool := fun _ _ v _ _ _ => ⟨v, rfl⟩
  sure_neq_sound := fun ρ a b u h _ _ _ ea eb => by
    obtain ⟨x, y, t, t', rfl, rfl, hxy⟩ := sure_neq_iff.1 h
    simp only [ev, Option.some.injEq] at ea eb
    exact hxy (ea.trans eb.symm)

end BoolExample
