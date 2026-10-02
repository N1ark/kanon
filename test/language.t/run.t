The version of kanon:

  $ kanon --version
  0.1.0

A language of integers, whose operators are symbols. An operator is read as in
OCaml, as long as possible, and its first character gives its precedence: from
the lowest, ≤ (a non-ASCII character) compares, ^^ concatenates, +. adds and *.
multiplies, and the prefix ~ applies first. On integers, the operators are
built in.

  $ cat > ops.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > 
  > node Int of int : TInt [@literal int]
  > node Neg : TInt -> TInt
  > node Add : TInt -> TInt -> TInt [@comm] [@fold add_z] [@unit 0]
  > node Mul : TInt -> TInt -> TInt [@fold mul_z Int]
  > node Cat : TInt -> TInt -> TInt
  > node Le : TInt -> TInt -> TBool [@fold le_z of_bool]
  > node Bool of bool : TBool [@literal bool]
  > sort TInt
  > sort TBool
  > 
  > prefix "~" = Neg, neg
  > infix "+." = Add, add
  > infix "*." = Mul, mul
  > infix "^^" = Cat, cat
  > infix "≤" = Le, le
  > KN
  $ cat > ops.kn <<'KN'
  > prim of_bool : bool -> t
  > 
  > fn add_z (x y : int) : int = x + y
  > fn mul_z (x y : int) : int = x * y
  > fn le_z (x y : int) : bool = x <= y
  > 
  > rule neg : Neg v =
  >   | twice: ~(~x) -> x
  > rule add : Add (v1, v2)
  > rule mul : Mul (v1, v2)
  > rule cat : Cat (v1, v2)
  > rule le : Le (v1, v2)
  > 
  > fn f (a b c : t) : t = a +. b *. c ^^ ~a ≤ c
  > fn g (x y : int) : bool = x + y * 2 < 3 - -x
  > KN
  $ kanon ocaml ops.knl ops.kn | sed -n '/ f (a/,$p'
  let[@inline] f (a : t) (b : t) (c : t) : t =
      (le (cat (add a (mul b c)) (neg a)) c)
  
  let[@inline] g (x : Z.t) (y : Z.t) : bool =
      (Z.lt (Z.add x (Z.mul y (Z.of_int (2)))) (Z.sub (Z.of_int (3)) (Z.neg x)))
  
  

The laws of [@literal int] literals: the results of [@fold] are lifted by the
node of their type (Int, for add_z), or by the function or node given after
it (Int, of_bool).

  $ kanon ocaml ops.knl ops.kn | sed -n '/let add/,/^$/p;/let mul/,/^$/p;/let le/,/^$/p'
  let add (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TInt), (TInt)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | ({ kind = Int (i1); _ }, { kind = Int (i2); _ }) ->
        (node (Int ((add_z i1 i2))) TInt)
      | (x, { kind = Int (kanon__2); _ })
        when (((Z.equal kanon__2 Z.zero))) ->
        x
      | ({ kind = Int (kanon__2); _ }, x)
        when (((Z.equal kanon__2 Z.zero))) ->
        x
      | _ -> (node (mk_commut_binop Add v1 v2) TInt)
      ))
  
  let mul (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TInt), (TInt)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | ({ kind = Int (i1); _ }, { kind = Int (i2); _ }) ->
        (node (Int ((mul_z i1 i2))) TInt)
      | _ -> (node (Op2 (Mul, v1, v2)) TInt)
      ))
  
  let le (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TInt), (TInt)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | ({ kind = Int (i1); _ }, { kind = Int (i2); _ }) ->
        (Prims.of_bool (le_z i1 i2))
      | _ -> (node (Op2 (Le, v1, v2)) TBool)
      ))
  

Some operators are not declared, or not of their kind:

  $ cat > bad.knl <<'KN'
  > infix "~~" = Neg, neg
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:7: ~~ is not an infix operator, nor a word
  [1]
  $ cat > bad.knl <<'KN'
  > prefix "+" = Neg, neg
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:8: + is not a prefix operator: -, not, or a symbol that starts with !, ~ or ?
  [1]
  $ cat > bad.knl <<'KN'
  > infix "<>" = Le, le
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:7: <> is built in, at every type
  [1]
  $ cat > bad.kn <<'KN'
  > fn h (a b : t) : t = a <*> b
  > KN
  $ kanon ocaml ops.knl ops.kn bad.kn
  bad.kn:1:21: <*> is not an operator on terms
  [1]
  $ cat > bad.kn <<'KN'
  > fn h (a b : int) : int = a <- b
  > KN
  $ kanon ocaml ops.knl ops.kn bad.kn
  bad.kn:1:27: <- is reserved
  [1]

= and <> are built in, at every type but the abstract types marked [@noeq]:
on terms, they compare hash-consed terms (their tags in OCaml).

  $ cat > eq.knl <<'KN'
  > type var [@ocaml "string"] [@noeq]
  > KN
  $ cat > eq.kn <<'KN'
  > fn same (a b : t) (l : t list) : bool = a = b || l <> [ a ]
  > KN
  $ kanon ocaml ops.knl eq.knl ops.kn eq.kn | sed -n '/ same /,$p'
  let[@inline] same (a : t) (b : t) (l : (t list)) : bool =
      ((Int.equal a.tag b.tag) || (not ((List.equal equal_t) l (a :: []))))
  
  
  $ cat > bad.kn <<'KN'
  > fn h (a b : var) : bool = a = b
  > KN
  $ kanon ocaml ops.knl eq.knl ops.kn bad.kn
  bad.kn:1:26: equality is not allowed at type var
  [1]

Sorts and nodes have the same constructors, but a sort is not a term, nor a
node a sort.

  $ cat > bad.kn <<'KN'
  > fn h (a : t) : t = TInt
  > KN
  $ kanon ocaml ops.knl ops.kn bad.kn
  bad.kn:1:19: TInt is a sort, not a node
  [1]
  $ cat > bad.knl <<'KN'
  > node Odd : TInt -> Neg
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:19: Neg is a node, not a sort
  [1]
  $ cat > bad.knl <<'KN'
  > node TInt
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:5: node TInt is declared twice
  [1]
  $ cat > bad.knl <<'KN'
  > sort TSeq : TInt
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:10: sort TSeq: sorts have no typing
  [1]

The terms (t, whose kinds are kind), their sorts (ty) and the types of the
operators of each arity (op1, op2, ..., opn) are generated from the nodes and
sorts: a language does not declare them.

  $ kanon ocaml-types ops.knl | sed -n '/kind =/,/^and t =/p'
  type kind =
    | Int of Z.t
    | Bool of bool
    | Op1 of op1 * t
    | Op2 of op2 * t * t
  
  and op1 =
    | Neg
  
  and op2 =
    | Add
    | Mul
    | Cat
    | Le
  
  and ty =
    | TInt
    | TBool
  
  and t = {
  $ for t in t kind ty op2 opn; do echo "type $t = A" > bad.knl; kanon ocaml ops.knl bad.knl ops.kn; done
  bad.knl:1:5: type t is generated from the nodes
  bad.knl:1:5: type kind is generated from the nodes
  bad.knl:1:5: type ty is generated from the sorts
  bad.knl:1:5: type op2 is generated from the nodes
  bad.knl:1:5: type opn is generated from the nodes
  [1]

A node whose typing has a list as its only operand sort is an operator of any
number of operands, whose elements all have that sort.

  $ cat > nary.knl <<'KN'
  > node Max : TInt list -> TInt
  > node Same : a list -> TBool
  > KN
  $ cat > nary.kn <<'KN'
  > rule max : Max l =
  >   | one: [ x ] -> x
  > rule same : Same l
  > KN
  $ kanon ocaml ops.knl nary.knl ops.kn nary.kn | sed -n '/ max /,$p'
  let[@inline] max (l : (t list)) : t =
      (match l with
      | (x :: []) -> x
      | _ -> (node (OpN (Max, l)) TInt)
      )
  
  let[@inline] same (l : (t list)) : t =
      (match l with
      | _ -> (node (OpN (Same, l)) TBool)
      )
  
  
  $ echo 'node Bad : TInt list -> TInt -> TInt' > bad.knl
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:11: Bad: s list is only allowed as the only operand sort
  [1]

Literals give their type, and boolean literals have no function: [@fold f lift]
makes the term of a boolean. [@ite] and [@distrib_ite] are gone.

  $ echo 'node B of bool [@literal]' > bad.knl
  $ kanon ocaml bad.knl
  bad.knl:1:15: [@literal] needs the type of the literals: [@literal bool], [@literal int] or [@literal t]
  [1]
  $ echo 'node B of bool [@literal bool] [@to_term of_bool]' > bad.knl
  $ kanon ocaml bad.knl
  bad.knl:1:31: boolean literals have no [@to_term]: [@fold f lift] gives the function that makes the term of a boolean
  [1]
  $ cat > bad.knl <<'KN'
  > node Ite : TBool -> a -> a -> a [@ite]
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:34: unknown attribute [@ite]
  [1]

Literals whose values have an abstract type ([@literal t]) need a constant for
the term of a law, which Kanon cannot build.

  $ cat > bv.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > type bv [@ocaml "Bv.t"]
  > node BitVec of int [@literal bv] [@to_term lit] [@of_term of_lit]
  > node BvMul : TBv -> TBv -> TBv [@zero 0]
  > sort TBv
  > KN
  $ kanon ocaml bv.knl
  bv.knl:4:38: the constant 0 is not declared: the literals of bv values have no term that Kanon could build
  [1]
  $ cat >> bv.knl <<'KN'
  > constant 0 (v) = zero_of v
  > KN
  $ cat > bv.kn <<'KN'
  > prim lit : bv -> t
  > prim of_lit : t -> bv
  > prim zero_of : t -> t
  > rule bv_mul : BvMul (v1, v2)
  > KN
  $ kanon ocaml bv.knl bv.kn | sed -n '/let bv_mul/,$p'
  let bv_mul (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBv), (TBv)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | (_, ({ kind = BitVec (kanon__2); _ } as z))
        when (((Z.equal kanon__2 Z.zero))) ->
        (Prims.zero_of z)
      | _ -> (node (Op2 (BvMul, v1, v2)) TBv)
      ))
  
  

A unit or a zero may be a named constant, built at the sort of the other
operand, which the derived rule compares with = (a guard).

  $ cat > ones.knl <<'KN'
  > node BvAnd : TBv -> TBv -> TBv [@comm] [@unit ones] [@zero 0]
  > constant ones (v) = ones_of v
  > KN
  $ cat > ones.kn <<'KN'
  > prim ones_of : t -> t
  > rule bv_and : BvAnd (v1, v2)
  > KN
  $ kanon ocaml bv.knl ones.knl bv.kn ones.kn | sed -n '/let bv_and/,/^$/p'
  let bv_and (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBv), (TBv)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | (x, y) when ((Int.equal y.tag (Prims.ones_of x).tag)) -> x
      | (y, x) when ((Int.equal y.tag (Prims.ones_of x).tag)) -> x
      | (_, ({ kind = BitVec (kanon__2); _ } as z))
        when (((Z.equal kanon__2 Z.zero))) ->
        (Prims.zero_of z)
      | (({ kind = BitVec (kanon__2); _ } as z), _)
        when (((Z.equal kanon__2 Z.zero))) ->
        (Prims.zero_of z)
      | _ -> (node (mk_commut_binop BvAnd v1 v2) TBv)
      ))
  
  $ sed 's/unit ones/unit twos/' ones.knl > bad.knl
  $ kanon ocaml bv.knl bad.knl bv.kn ones.kn
  bad.knl:1:46: expected the literal 0, 1, true or false, or a constant: twos is not declared
  [1]

The rules call the primitives in the module of [@@@ocaml_prims], which the
language must name, and the types of ocaml-types need the OCaml types of the
abstract types.

  $ grep -v ocaml_prims bv.knl > noprims.knl
  $ kanon ocaml noprims.knl bv.kn
  bv.kn:1:5: lit is a primitive: [@@@ocaml_prims "M"], in the declaration of the language, names the OCaml module that implements the primitives
  [1]
  $ sed 's/ \[@ocaml "Bv.t"\]//' bv.knl > noocaml.knl
  $ kanon ocaml-types noocaml.knl
  noocaml.knl:2:5: type bv is abstract: [@ocaml "M.t"] gives its OCaml type
  [1]
  $ cat > bad.knl <<'KN'
  > type pair [@noeq] = { left : int; right : int }
  > KN
  $ kanon ocaml-types bv.knl bad.knl
  bad.knl:1:12: [@noeq] applies to abstract types
  [1]
