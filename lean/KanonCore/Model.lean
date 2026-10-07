import KanonCore.Option
import KanonCore.Array

/-!
# What the model needs

The generated model of the rules (`Ops.lean`, `Model/`) is written with
`whenSome` and `firstSome` (`KanonCore.Option`) and the functions on arrays
(`KanonCore.Array`), and nothing else of Kanon's library: a language's
`Prims.lean` imports this module, rather than `KanonCore`, so that its model is
built without Lean's meta-programming library, which is long to import.
-/
