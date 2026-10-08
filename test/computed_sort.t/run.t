`(C x : e)` builds the node `C` at a sort. The sort is a sort constructor applied
to arguments, `(Tuple vs : TTuple (types_of vs))`, or any expression of type
`ty`: a variable, a call of a function or of a primitive.

  $ cat > lang.knl <<'EOF'
  > [@@@ocaml_prims "Prims"]
  > [@@@ocaml_rules "Rules"]
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
  33:      (node (Tuple (vs)) (TTuple ((rules_types_of vs))))
  35:  let[@inline] rules_mk_var (x : var) (s : ty) : t = (node (Var (x)) s)
  38:      (node (Var (x)) (Prims.var_ty x))
  41:      (node (Field (i, v)) (rules_field_ty v i))
  44:      (node (Field (i, v)) (rules_nth_ty (rules_types_of (v :: [])) i))
  52:      | _ -> (node (Op1 ((Proj (i)), v)) (rules_field_ty v i))

Lean: the sort is the translated expression.

  $ kanon lean-model lang.knl | grep -n 'mk (\.'
  96:  (Kanon.mk (.Tuple vs) (Kanon.sort (.TTuple (Kanon.Rules.Rules.types_of vs))))
  99:  (Kanon.mk (.Var x) s)
  102:  (Kanon.mk (.Var x) (Kanon.Rules.var_ty x))
  105:  (Kanon.mk (.Field i v) (Kanon.Rules.Rules.field_ty v i))
  108:  (Kanon.mk (.Field i v) (Kanon.Rules.Rules.nth_ty (Kanon.Rules.Rules.types_of (v :: ([] : (List S.Term)))) i))
  119:  (Kanon.mk (.Proj i v) (Kanon.sort .TInt))
  127:    (whenSome true ((Kanon.mk (.Proj i v) (Kanon.Rules.Rules.field_ty v i)))))

The ocaml-typed backend types a rule by the typing of its node, not by the sort
that its body builds: `proj` returns a `tint`.

  $ kanon ocaml-typed lang.knl | grep -n 'val proj'
  58:    val proj : Z.t -> [< Tag.ttuple ] t -> [> Tag.tint ] t

The sort of a node is a `ty`: anything else is an error at the sort.

  $ for sort in 'x' '1' 'Rules.types_of []' 'sorrt' '(Rules.types_of [])'; do
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
  === Rules.types_of []
  bad.kn:1:32: type mismatch: expected ty, got ty list
  === sorrt
  bad.kn:1:32: unbound variable sorrt
  === (Rules.types_of [])
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

`(C x : t)` with the name of a type is a type annotation, not a sort. A type
constraint on an expression is read as an expression first: a parenthesised
type there is a syntax error (put it on a `let`).

  $ cat > ann.kn <<'EOF'
  > fn ann (x : var) : t = (Var x : t)
  > fn ints (l : int list) : int list = (l : int list)
  > EOF
  $ kanon ocaml lang.knl ann.kn
  ann.kn:1:24: Var has no typing, which would give the sort of its term
  [1]
  $ cat > bad.kn <<'EOF'
  > fn bad (l : int list) : int = let x = (l : (int * bool) list) in 0
  > EOF
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:56: syntax error
  [1]
