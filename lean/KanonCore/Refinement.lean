import KanonCore.Option

/-!
# Refinement

The generated proofs only need the refinement relation of a language (the
result of a smart constructor refines the raw node it simplifies) to be a
preorder: each language gives an instance of `Refinement` for its relation.
-/

namespace Kanon

/-- A refinement relation: reflexive and transitive. -/
class Refinement {T : Type} (R : T → T → Prop) : Prop where
  refl : ∀ {t}, R t t
  trans : ∀ {a b c}, R a b → R b c → R a c

namespace Refinement

variable {T : Type} {R : T → T → Prop} [Refinement R]

/-- A rule function with no rule returns its spec. -/
theorem firstSome_nil {spec : T} : R spec ((firstSome ([] : List (Option T))).getD spec) :=
  refl

/-- A rule function is sound when each of its rules is. -/
theorem firstSome_cons {spec : T} {o : Option T} {l : List (Option T)}
    (h : ∀ r, o = some r → R spec r) (t : R spec ((firstSome l).getD spec)) :
    R spec ((firstSome (o :: l)).getD spec) := by
  cases o with
  | none => simpa [firstSome] using t
  | some r => simpa [firstSome] using h r rfl

end Refinement

end Kanon
