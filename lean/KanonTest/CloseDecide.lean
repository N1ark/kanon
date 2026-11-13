import KanonCore.Proof

/-! `kanon_close_lemmas` proves `decide P = decide Q` by a lemma `P ↔ Q`, and
`decide P = true` (or `false`) by a lemma `P` (or `¬P`), and `kanon_close`
tries the lemmas again once `simp_all` has rewritten the goal. -/

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

theorem g_pos {n : Int} (h : 0 ≤ n) : 0 < g n := by unfold g; omega
theorem g_ne_zero {n : Int} (h : 0 ≤ n) : ¬g n = 0 := by unfold g; omega

attribute [kanon_close_lemma] g_pos g_ne_zero

example (n : Int) (h : 0 ≤ n) : decide (0 < g n) = true := by kanon_close_lemmas
example (n : Int) (h : 0 ≤ n) : true = decide (0 < g n) := by kanon_close_lemmas
example (n : Int) (h : 0 ≤ n) : decide (g n = 0) = false := by kanon_close_lemmas

/-- `h` unfolds to `g`: `simp only [h]` rewrites the proposition of the
`decide`, and not its instance. -/
def h (n : Int) : Int := g n

example (n : Int) (hn : 0 ≤ n) : decide (0 < h n) = true := by
  simp only [h]
  kanon_close_lemmas

end KanonTest.CloseDecide
