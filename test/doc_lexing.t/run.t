A documentation comment is copied into OCaml comments, which OCaml reads token
by token: character literals, identifiers with primes, quoted strings, with an
extension too, and openers of comments must not change where the comment ends.

  $ cat > lang.knl <<'KN'
  > (** Quotes: '*" and the character '}' next to "quotes, a quoted {%ext|
  >     string, {id| too, and the opener (*) *) of a comment. *)
  > sort TInt
  > (** An identifier x' with a prime, next to a quote x'" and a number 5". *)
  > node Int of int : TInt
  > KN
  $ kanon ocaml-types lang.knl > t.ml
  $ ocamlfind ocamlc -package zarith -c t.ml
