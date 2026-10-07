The generated OCaml calls Zarith as `Z`: a Kanon module named `Z` would hide it
from the code that comes after, such as the tests, so a file may not be named
`z`.

  $ cat > lang.knl <<'KN'
  > use "z"
  > KN
  $ cat > z.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > KN
  $ cat > z.kn <<'KN'
  > fn add (x y : int) : int = x + y
  > KN
  $ kanon ocaml lang.knl
  ./z.knl:1:5: the module Z has the name of a generated module
  [1]
