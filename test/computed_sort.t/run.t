`(C x : e)` builds the node `C` at a sort. The sort is a sort constructor applied
to arguments, `(Tuple vs : TTuple (types_of vs))`, or any expression of type
`ty`: a variable, a call of a function or of a primitive.

  $ cat > lang.knl <<'EOF'
  > [@@@ocaml_prims "Prims"]
  > use "rules"
  > type var [@ocaml "string"] [@lean "String"]
  > sort TInt
  > sort TTuple of ty list
  > node Int of int : TInt
  > notation Int
  > node Var of var
  > node Tuple of t list : TTuple tys
  > node Field of int * t
  > node Proj of int (i) : TTuple tys -> TInt
  > EOF
  $ cat > rules.kn <<'EOF'
  > prim var_ty : var -> ty
  > fn nth_ty (tys : ty list) (i : int) : ty =
  >   match tys with
  >   | [] -> TInt
  >   | t :: r -> if i = 0 then t else nth_ty r (i - 1)
  > fn types_of (vs : t list) : ty list =
  >   match vs with
  >   | [] -> []
  >   | v :: r -> type_of v :: types_of r
  > fn field_ty (v : t) (i : int) : ty =
  >   match type_of v with
  >   | TTuple tys -> nth_ty tys i
  >   | _ -> TInt
  > fn mk_tuple (vs : t list) : t = (Tuple vs : TTuple (types_of vs))
  > fn mk_var (x : var) (s : ty) : t = (Var x : s)
  > fn mk_var_of (x : var) : t = (Var x : var_ty x)
  > fn mk_field (i : int) (v : t) : t = (Field (i, v) : field_ty v i)
  > fn mk_nested (i : int) (v : t) : t = (Field (i, v) : (nth_ty (types_of [v]) i))
  > rule proj : Proj (i, v) =
  >   | any: _ -> (Proj (i, v) : field_ty v i)
  > EOF

OCaml: the sort is the expression.

  $ kanon ocaml lang.knl | grep -n 'node'
  29:    (node (Tuple (vs)) (TTuple ((types_of vs))))
  31:let[@inline] mk_var (x : var) (s : ty) : t = (node (Var (x)) s)
  33:let[@inline] mk_var_of (x : var) : t = (node (Var (x)) (Prims.var_ty x))
  36:    (node (Field (i, v)) (field_ty v i))
  39:    (node (Field (i, v)) (nth_ty (types_of (v :: [])) i))
  47:    | _ -> (node (Op1 ((Proj (i)), v)) (field_ty v i))

Lean: the sort is the translated expression.

  $ kanon lean-model lang.knl | grep -n 'Term.mk'
  43:  (Term.mk (Kind.Tuple vs) (Ty.TTuple (types_of vs)))
  46:  (Term.mk (Kind.Var x) s)
  49:  (Term.mk (Kind.Var x) (var_ty x))
  52:  (Term.mk (Kind.Field i v) (field_ty v i))
  55:  (Term.mk (Kind.Field i v) (nth_ty (types_of (v :: [])) i))
  63:  (Term.mk (Kind.Op1 (Op1.Proj i) v) Ty.TInt)
  68:    (whenSome true ((Term.mk (Kind.Op1 (Op1.Proj i) v) (field_ty v i)))))

The sort of a node is a `ty`: anything else is an error at the sort.

  $ for sort in 'x' '1' 'types_of []' 'sorrt' '(types_of [])'; do
  >   cat > bad.kn <<EOF
  > fn bad (x : var) : t = (Var x : $sort)
  > EOF
  >   echo "=== $sort"
  >   kanon ocaml lang.knl bad.kn
  > done
  === x
  bad.kn:1:32: type mismatch: expected ty, got var
  === 1
  bad.kn:1:32: type mismatch: expected ty, got int
  === types_of []
  bad.kn:1:32: type mismatch: expected ty, got ty list
  === sorrt
  bad.kn:1:32: unbound variable sorrt
  === (types_of [])
  bad.kn:1:33: type mismatch: expected ty, got ty list
  [1]

The arguments of a sort constructor are checked as before.

  $ cat > bad.kn <<'EOF'
  > fn bad (x : var) (s : ty) : t = (Var x : TTuple s)
  > EOF
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:48: type mismatch: expected ty list, got ty
  [1]

An operator keeps the check of its typing when it is built at a sort
constructor, and the check is skipped for a computed sort.

  $ cat > bad.kn <<'EOF'
  > fn bad (v : t) : t = (Proj (0, v) : TTuple [])
  > EOF
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:36: Proj is a term of sort TInt, by its typing, not TTuple
  [1]
