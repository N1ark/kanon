import KanonBool.Lang

/-!
# The primitives of the bool module, and what its rules assume

The literals `v_true` and `v_false`; what the extensible helper `sure_neq`
satisfies (the terms it tells apart do not have the same value), which the
modules that extend it prove of their cases; and what the oracle `sort_by_tag`
satisfies (it permutes a list).
-/

namespace KanonBool

open Kanon

variable {S : Kanon.Sem} [Lang S]

/-- The literal `true`. -/
def v_true : S.Term := mk (.Bool true) (sort .TBool)

/-- The literal `false`. -/
def v_false : S.Term := mk (.Bool false) (sort .TBool)

attribute [kanon_lits] v_true v_false

/-- What `sure_neq a b` says when it is `true`: `a` and `b`, well-typed and of
the same type, never have the same value. -/
def Bool.sure_neq.post (a b : S.Term) (r : Bool) : Prop :=
  r = true → S.WT a → S.WT b → S.ty a = S.ty b →
    ∀ ρ u, S.ev ρ a = some u → S.ev ρ b = some u → False

/-- What the rules assume of the oracle `sort_by_tag`: it permutes. -/
structure Oracle.Compat (sort_by_tag : List S.Term → List S.Term) : Prop where
  sort_by_tag : ∀ l, (sort_by_tag l).Perm l

end KanonBool
