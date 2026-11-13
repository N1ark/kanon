import KanonCore.Proof

/-! `kanon_close_lemmas` synthesizes the instances of a lemma once its
hypotheses determine their types: here the type `α`, which the conclusion
does not mention. -/

namespace KanonTest.CloseInst

class Size (α : Type) where
  size : α → Nat

instance : Size String := ⟨String.length⟩

def Big {α : Type} [Size α] (a : α) : Prop := 10 < Size.size a

theorem lt_of_big {α : Type} [Size α] {a : α} {n : Nat} (h : Big a) (hn : Size.size a ≤ n) :
    10 < n := by
  unfold Big at h; omega

attribute [local kanon_close_lemma] lt_of_big

example (s : String) (n : Nat) (h : Big s) (hn : Size.size s ≤ n) : 10 < n := by
  kanon_close_lemmas

end KanonTest.CloseInst
