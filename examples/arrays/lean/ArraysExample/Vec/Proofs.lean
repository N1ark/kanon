import ArraysExample.Vec.Statements

/-!
# The arm `Set (_, j, x)[j] = x` of `Vec.get`, by hand

Reading the element that was just set gives it back: when the read is not
poison, the write was in bounds (`setV`), and `arrayGet_arraySet_same` of
Kanon's library gives the element.
-/

namespace ArraysExample.Vec

open Kanon

@[kanon_arm] theorem get_set_same : Vec.get.r_set_same.main.Stmt := by
  intro S _ _ O hO i u j x t h
  simp only [decide_eq_true_eq] at h
  subst h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · simp only [Vec.get.spec, WT_mk, Node.wt, Node.All, ty_mk] at w ⊢
    exact ⟨w.2.1.2.2.2, w.2.1.1.2.2.1⟩
  · simp only [Vec.get.spec, ev_mk, Node.map, Node.eval, setV, getV, Option.bind_eq_some_iff,
      Embed.proj_eq_some_iff] at e
    obtain ⟨a', ⟨_, ⟨a, ⟨_, hu, rfl⟩, i', ⟨_, hi, rfl⟩, y, ⟨_, hy, rfl⟩, hs⟩, rfl⟩, k,
      ⟨_, hk, rfl⟩, e⟩ := e
    rw [hi] at hk
    simp only [Option.some.injEq, Embed.inj_eq_iff] at hk
    subst hk
    split at hs
    · rename_i hin
      simp only [Option.some.injEq, Embed.inj_eq_iff] at hs
      subst hs
      have hin' : inBounds (arraySet a i' y) i' := by
        unfold inBounds at *; rw [arrayLength_arraySet]; exact hin
      simp only [hin', ite_true, Option.some.injEq] at e
      rw [← e, arrayGet_arraySet_same a i' y hin]
      exact hy
    · cases hs

end ArraysExample.Vec
