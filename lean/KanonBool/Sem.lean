import KanonBool.Syntax
import KanonBool.Val

/-!
# What the bool module needs of the semantics of a language

The rules of the bool module (`modules/bool.kn`) are proved once, for every
language that uses it, over its interface `L : KanonBool.Syntax S` (generated, in
`Syntax.lean`: the sort `TBool`, the kinds of the nodes, their typing and
matchers, the primitives `v_true` and `v_false`, the helpers) and what the
proofs need of the semantics `S` of the language, `KanonBool.Sem L`:

- the booleans among its values (`vbool`), which are different;
- the evaluation of the nodes, by the operations of `KanonBool.Val`, which the
  language uses in its own evaluation (so that these laws hold by definition:
  `kanon_law` proves them, unless the language gives another proof);
- the primitives `v_true` and `v_false`, which are the literals;
- that well-typed booleans evaluate to booleans (`ev_bool`), and that the
  terms that the extensible helper `sure_neq` tells apart, which the modules
  above it extend, have different values (`sure_neq_sound`): the language
  proves them.

It is a class, so that the modules above, whose `Sem` extends it, give it.
`Oracle.Compat` is what the rules assume of the oracle `sort_by_tag`.
-/

namespace KanonBool

open Classical Kanon

/-- What the bool module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} (L : Syntax B) where
  /-- The boolean values. -/
  vbool : Bool → S.Val
  vbool_inj : Function.Injective vbool := by intro _ _ h; cases h; rfl
  ev_Bool : ∀ ρ b t, S.ev ρ (B.node (L.BoolK b) t) = some (vbool b) := by kanon_law
  ev_Not : ∀ ρ a t, S.ev ρ (B.node (L.NotK a) t) = pnot vbool (S.ev ρ a) := by kanon_law
  ev_And : ∀ ρ a b t, S.ev ρ (B.node (L.AndK a b) t) =
    pand vbool (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Or : ∀ ρ a b t, S.ev ρ (B.node (L.OrK a b) t) =
    por vbool (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Eq : ∀ ρ a b t, S.ev ρ (B.node (L.EqK a b) t) =
    peq vbool (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Ite : ∀ ρ g a b t, S.ev ρ (B.node (L.IteK g a b) t) =
    pite vbool (S.ev ρ g) (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Distinct : ∀ ρ l t, S.ev ρ (B.node (L.DistinctK l) t) =
    pdistinct vbool (l.mapM (S.ev ρ)) := by kanon_law
  v_true_eq : L.bool_v_true = B.node (L.BoolK true) L.TBool := by kanon_law
  v_false_eq : L.bool_v_false = B.node (L.BoolK false) L.TBool := by kanon_law
  /-- Well-typed booleans evaluate to booleans. -/
  ev_bool : ∀ ρ t v, S.WT t → S.ty t = L.TBool → S.ev ρ t = some v → ∃ b, v = vbool b
  /-- Surely different terms of the same type have different values. -/
  sure_neq_sound : ∀ ρ a b u, L.bool_sure_neq a b = true → S.ty a = S.ty b → S.WT a →
    S.WT b → S.ev ρ a = some u → S.ev ρ b = some u → False

/-- What the rules assume of the oracle `sort_by_tag`, for the interface `L`: it
permutes. -/
structure Oracle.Compat {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    (L : Syntax B) (sort_by_tag : List S.Term → List S.Term) : Prop where
  sort_by_tag : ∀ l, (sort_by_tag l).Perm l

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} {L : Syntax B} [Sem L]

theorem vbool_eq_iff {a b : Bool} : vbool L a = vbool L b ↔ a = b := vbool_inj.eq_iff

/-- The values of a well-typed boolean. -/
theorem ev_cases {ρ : S.Env} {t : S.Term} (w : S.WT t) (h : S.ty t = L.TBool) :
    S.ev ρ t = none ∨ S.ev ρ t = some (vbool L true) ∨ S.ev ρ t = some (vbool L false) := by
  rcases e : S.ev ρ t with _ | v
  · exact .inl rfl
  · obtain ⟨b, rfl⟩ := ev_bool ρ t v w h e
    cases b <;> simp

end Sem

/-- The values of any term. -/
theorem Sem.ev_opt {S : Kanon.Sem} {ρ : S.Env} {t : S.Term} :
    S.ev ρ t = none ∨ ∃ v, S.ev ρ t = some v := by
  cases S.ev ρ t <;> simp

end KanonBool
