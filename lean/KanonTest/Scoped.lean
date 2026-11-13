import KanonCore.Proof

/-! The lemma attributes of the tactics may be `scoped`: a close lemma given in
the namespace `M.f` of a rule function is used in the proofs of its arms
(`theorem M.f.r_a.main.ok`, elaborated in that namespace) only. -/

namespace KanonTest.Scoped

set_option linter.unusedVariables false

/-- An opaque function, so that only the lemma below knows about it. -/
@[irreducible] def g (n : Int) : Int := n + 1

theorem g_pos {n : Int} (h : 0 ≤ n) : 0 < g n := by unfold g; omega

namespace M.f
attribute [scoped kanon_close_lemma] g_pos
end M.f

namespace M

theorem f.r_a.main.ok (n : Int) (h : 0 ≤ n) : 0 < g n := by kanon_close_lemmas

theorem g.r_a.main.ok (n : Int) (h : 0 ≤ n) : 0 < g n ∨ True := by
  fail_if_success (left; kanon_close_lemmas)
  exact .inr trivial

end M

example (n : Int) (h : 0 ≤ n) : 0 < g n ∨ True := by
  fail_if_success (left; kanon_close_lemmas)
  exact .inr trivial

section
attribute [local kanon_close_lemma] g_pos

example (n : Int) (h : 0 ≤ n) : 0 < g n := by kanon_close_lemmas
end

example (n : Int) (h : 0 ≤ n) : 0 < g n ∨ True := by
  fail_if_success (left; kanon_close_lemmas)
  exact .inr trivial

end KanonTest.Scoped
