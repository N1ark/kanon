The typed interface of a language with the bool module. A primitive may give
the sort of its result, as a function does, and its OCaml implementation
(`[@ocaml "e"]`, an expression in the scope of the types): the language then
does not implement it. The bool module does so for `v_true`, `v_false` and
`sort_by_tag`, and the int module below for `zero`.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Types"]
  > [@@@ocaml_rules "Rules"]
  > [@@@traversals]
  > use builtin "bool"
  > use "int"
  > KN
  $ cat > int.knl <<'KN'
  > use builtin "bool"
  > sort TInt
  > node Int of int : TInt
  > node Lt : TInt -> TInt -> TBool
  > KN
  $ cat > int.kn <<'KN'
  > prim zero : TInt [@ocaml "node (Int Z.zero) TInt"]
  > rule lt : Lt (v1, v2)
  > fn value (v : t) : int = match v with Int z -> z | _ -> 0
  > KN
  $ kanon ocaml out lang.knl && cp out/Generated/types.ml out/Generated/rules.ml out/Generated/typed.ml .

The interface has the primitives and the functions whose result is annotated
with a sort or has no term; `eq_untyped`, which is `[@untyped]`, takes terms of
any tags; with `[@@@traversals]`, it has the traversals:

  $ grep -n "val \(v_true\|v_false\|zero\|value\|eq_untyped\|equal\|compare\|hash\|type_of\|map_children\|resimplify\) " typed.ml
  39:  val type_of : 'a t -> 'a ty
  42:  val equal : 'a t -> 'b t -> bool
  45:  val compare : 'a t -> 'b t -> int
  48:  val hash : 'a t -> int
  57:  val map_children : (raw -> raw) -> raw -> raw
  62:  val resimplify : raw -> raw
  72:    val v_true : [> Tag.tbool ] t
  73:    val v_false : [> Tag.tbool ] t
  79:    val eq_untyped : _ t -> _ t -> [> Tag.tbool ] t
  107:    val zero : [> Tag.tint ] t
  109:    val value : _ t -> Z.t
  $ cat > main.ml <<'ML'
  > module T = (Typed.Derived : Typed.S)
  > open T
  > let one = Int.mk_int Z.one
  > let () =
  >   assert (equal (Bool.eq one one) Bool.v_true);
  >   assert (equal (Bool.eq_untyped one Bool.v_true) Bool.v_false);
  >   assert (compare one one = 0 && hash one = hash (Int.mk_int Z.one));
  >   assert (not (equal Int.zero one));
  >   assert (Bool.is_tbool (type_of Bool.v_false));
  >   assert (Int.value one = Z.one);
  >   let lt = untyped (Int.lt Int.zero one) in
  >   assert (resimplify lt == lt);
  >   print_endline "ok"
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg types.ml rules.ml typed.ml main.ml -o main.exe && ./main.exe
  ok
