A double quote in a documentation comment, with no match, is turned into a
character literal; right after a letter, OCaml would read that
letter and the quote as an identifier and open a string: the comment would not
end.

  $ cat > lang.knl <<'KN'
  > (** The inch sign" is odd. *)
  > sort TInt
  > node Int of int : TInt
  > KN
  $ touch lang.kn
  $ kanon ocaml out lang.knl lang.kn && cp out/Generated/types.ml t.ml
  $ ocamlfind ocamlc -package zarith -c t.ml
