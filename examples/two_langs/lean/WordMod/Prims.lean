import Generated.WordMod.Lang

/-!
# What the rules of the word module assume of its oracles

`wsum` sums, and `wcheck` is anything.
-/

namespace WordMod

/-- What the rules assume of the oracles `wsum` and `wcheck`. -/
structure Oracle.Compat {S : Kanon.Sem} (wsum : Int → Int → Int) (wcheck : Int → Option Int) :
    Prop where
  wsum : ∀ x y, wsum x y = x + y

end WordMod
