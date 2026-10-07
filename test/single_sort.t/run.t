A language with one sort has no other sort to match in the sorts that Kanon
reads from terms: the generated OCaml has no case for them, which the warning
on unused cases (an error in the dune dev profile) would reject.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort TBv of nat
  > node Bv of int * nat (v, n) : TBv n
  > node Concat : TBv n -> TBv m -> TBv (n + m)
  > KN
  $ cat > m.kn <<'KN'
  > fn mk (a b : t) : t = Concat (a, b)
  > fn size (v : TBv n) : int = n
  > KN
  $ kanon ocaml-types lang.knl > t.ml
  $ kanon ocaml lang.knl > r.ml
  $ ocamlfind ocamlc -package zarith -warn-error +11 -c t.ml r.ml 2>&1 | grep -B3 Error || true
