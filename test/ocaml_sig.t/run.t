`kanon ocaml --sig DIR FILE...` writes `DIR/Generated/sig.ml`: the tags and
the signature `S` of the typed interface of the modules of the files, which
names no module of a language. Its terms and sorts are abstract, an abstract
type is its `[@ocaml]` type, and a record or a variant is an abstract type of
`S`. Here the files are a skeleton, which uses the modules.

  $ cat > m.knl <<'KN'
  > type name [@ocaml "string"]
  > type flags = { wrap : bool }
  > sort TInt
  > node Int of int : TInt
  > node Add of flags (f) : TInt -> TInt -> TInt
  > node Var of name
  > KN
  $ cat > m.kn <<'KN'
  > rule add : Add (f, v1, v2)
  > KN
  $ cat > skel.knl <<'KN'
  > [@@@traversals]
  > use "m"
  > KN
  $ kanon ocaml --sig out skel.knl
  $ ls out/Generated
  sig.ml
  $ grep -n "^open\|^module\|type raw\|type flags\|val \(add\|mk_var\|map_children\) " out/Generated/sig.ml
  4:module Tag = struct
  9:module type S = sig
  11:  type raw
  12:  type raw_ty
  21:  type flags
  57:  val map_children : (raw -> raw) -> raw -> raw
  72:    val mk_var : string -> 'a ty -> 'a t
  73:    val add : flags -> [< Tag.tint ] t -> [< Tag.tint ] t -> [> Tag.tint ] t
  $ kanon ocaml --sig --check out skel.knl

The typed interface of a language that has those modules satisfies it,
though the language has more: here a module of its own, with a sort.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Types"]
  > [@@@ocaml_rules "Rules"]
  > [@@@traversals]
  > use "m"
  > sort TReal
  > node Real of int : TReal
  > KN
  $ kanon ocaml lang lang.knl && cp out/Generated/sig.ml lang/Generated/*.ml .
  $ cat > check.ml <<'ML'
  > module _ (L : Typed.S) : Sig.S = L
  > ML
  $ ocamlfind ocamlc -package zarith -c types.ml rules.ml typed.ml sig.ml check.ml
