import KanonCore.Proof

/-! `kanon_close_lemmas` closes goals that are negations, disequalities or
defined predicates, by lemmas that conclude them. -/

namespace KanonTest.CloseNeg

/-- A defined predicate, which unfolds to a negation. -/
def Pos (n : Int) : Prop := ¬n ≤ 0

/-- An opaque function, so that only the lemmas below know about it. -/
@[irreducible] def g (n : Int) : Int := n + 1

theorem g_pos {n : Int} (h : 0 ≤ n) : Pos (g n) := by unfold Pos g; omega
theorem g_ne {n : Int} (h : 0 ≤ n) : g n ≠ 0 := by unfold g; omega
theorem g_not_le {n : Int} (h : 0 ≤ n) : ¬g n ≤ 0 := by unfold g; omega

attribute [kanon_close_lemma] g_pos g_ne g_not_le

example (n : Int) (h : 0 ≤ n) : Pos (g n) := by kanon_close_lemmas
example (n : Int) (h : 0 ≤ n) : g n ≠ 0 := by kanon_close_lemmas
example (n : Int) (h : 0 ≤ n) : ¬g n ≤ 0 := by kanon_close_lemmas

end KanonTest.CloseNeg
