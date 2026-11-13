import KanonCore.Proof

/-! `kanon_close_lemmas` proves `decide P = decide Q` by a lemma `P ↔ Q`, and
`kanon_close` tries the lemmas again once `simp_all` has rewritten the goal. -/

namespace KanonTest.CloseDecide

/-- An opaque function, so that only the lemma below knows about it. -/
@[irreducible] def g (n : Int) : Int := n + 1

theorem g_lt_g {m n : Int} : g m < g n ↔ m < n := by unfold g; omega

attribute [kanon_close_lemma] g_lt_g

example (m n : Int) : decide (g m < g n) = decide (m < n) := by kanon_close_lemmas
example (m n : Int) : decide (m < n) = decide (g m < g n) := by kanon_close_lemmas

example (m n : Int) (b : Bool) (h : b = decide (g m < g n)) : b = decide (m < n) := by
  fail_if_success kanon_close_lemmas
  kanon_close

example (m n : Int) : (if g m < g n then true else false) = decide (m < n) := by
  kanon_close

end KanonTest.CloseDecide
