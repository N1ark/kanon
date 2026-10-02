import IntsExample.Types

/-!
# The abstract types of the language

`lang.knl` declares the types of the language, which Kanon generates in
`Types.lean` and `Syntax.lean`, except for the abstract ones, which are defined
here. The only abstract type of this language, `var`, is Lean's `String`
(`[@lean "String"]`), so there is nothing to define.
-/
