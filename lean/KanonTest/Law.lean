import KanonCore.Generic

/-! `kanon_law` proves a law that its `kanon_law` lemmas alone prove, with
nothing left to unfold. -/

namespace KanonTest.Law

def P (n : Nat) : Prop := n = n

@[kanon_law] theorem P_iff (n : Nat) : P n ↔ True := by simp [P]

example (n : Nat) : P n ↔ True := by kanon_law

end KanonTest.Law
