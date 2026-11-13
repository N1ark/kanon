import KanonCore.Proof

/-! `kanon_clean` clears the hypotheses that are `True` or repeated, which
`kanon_sem_core` runs on what it leaves. -/

namespace KanonTest.Clean

set_option linter.unusedVariables false

open Kanon

example (a b : Nat) (h1 : a = b) (h2 : True) (h3 : a = b) : a = b := by
  kanon_clean
  fail_if_success have := h2
  fail_if_success have := h3
  exact h1

/-- A repeated hypothesis that another depends on is kept. -/
example (p : Prop) (h1 : p) (h2 : p) (h3 : h2 = h2) : p := by
  kanon_clean
  exact h2

@[reducible] def sem : Kanon.Sem where
  Term := Nat
  Ty := Unit
  Val := Nat
  Env := Unit
  ty _ := ()
  WT _ := True
  ev _ t := if t = 0 then none else some t
  size _ := 0

example (a : Nat) : sem.Refines a (a + 0) := by
  refine Sem.Refines.intro (fun _ => ⟨trivial, rfl⟩) ?_
  kanon_sem_core
  -- the typing hypotheses `w w' : True` are gone
  all_goals fail_if_success have := w
  all_goals fail_if_success have := w'
  all_goals simp_all

end KanonTest.Clean
