import Generated.PackMod.Lang

/-!
# What the rules of the pack module need of a language

The primitive `used_names` reads the terms of a language (the names that occur
free in them), so each language gives it, with what the rules need of it: it
keeps some of the names, and dropping the others does not change the value of
a quantifier. They are the class `Laws` (`[@@@lean_laws]` in `pack.knl`),
which the proofs of the module assume and each language proves.
-/

namespace PackMod

open Kanon

/-- A well-typed quantifier: its names are distinct, and its body a well-typed
boolean. -/
theorem WT_some {S : Kanon.Sem} [KanonBool.Lang S] [Lang S] {names : List (String × S.Ty)}
    {body : S.Term} {t : S.Ty} (w : S.WT (mk (.Some_ names body) t)) :
    t = KanonBool.sort .TBool ∧ (names.map Prod.fst).Nodup ∧
      S.ty body = KanonBool.sort .TBool ∧ S.WT body := by
  rw [WT_mk] at w
  simp only [Node.wt, some_wt, Node.All] at w
  exact ⟨w.1.1, w.1.2.1, w.1.2.2, w.2⟩

/-- What the pack module needs a language to give and prove. -/
class Laws (S : Kanon.Sem) [KanonBool.Lang S] [Lang S] where
  /-- The names among `names` that occur free in `body`. -/
  used_names : List (String × S.Ty) → S.Term → List (String × S.Ty)
  used_sublist : ∀ names body, (used_names names body).Sublist names
  /-- The names that `used_names` drops do not change a quantifier. -/
  ev_used : ∀ ρ names body t, S.WT (mk (.Some_ names body) t) →
    S.ev ρ (mk (.Some_ names body) t) = S.ev ρ (mk (.Some_ (used_names names body) body) t)

variable {S : Kanon.Sem} [KanonBool.Lang S] [Lang S] [Laws S]

/-- The primitive `used_names`, the language's. -/
def used_names (names : List (String × S.Ty)) (body : S.Term) : List (String × S.Ty) :=
  Laws.used_names names body

end PackMod
