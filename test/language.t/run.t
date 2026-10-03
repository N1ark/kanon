The version of kanon:

  $ kanon --version
  0.2.0

A language of integers, whose operators are symbols. An operator is read as in
OCaml, as long as possible, and its first character gives its precedence: from
the lowest, ≤ (a non-ASCII character) compares, ^^ concatenates, +. adds and *.
multiplies, and the prefix ~ applies first. On integers, the operators are
built in, and the other operators on values that are not terms are the
functions named last in their declarations (z_land for &&&).

  $ cat > ops.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > 
  > node Int of int : TInt
  > node Neg : TInt -> TInt
  > node Add : TInt -> TInt -> TInt [@comm] [@fold add_z] [@unit 0]
  > node Mul : TInt -> TInt -> TInt [@fold mul_z Int]
  > node Cat : TInt -> TInt -> TInt
  > node Le : TInt -> TInt -> TBool [@fold le_z of_bool]
  > node Bool of bool : TBool
  > node Land : TInt -> TInt -> TInt
  > sort TInt
  > sort TBool
  > notation Int
  > notation Bool
  > 
  > prefix "~" = Neg, neg
  > infix "+." = Add, add
  > infix "*." = Mul, mul
  > infix "^^" = Cat, cat
  > infix "≤" = Le, le
  > infix "&&&" = Land, land, z_land
  > KN
  $ cat > ops.kn <<'KN'
  > prim of_bool : bool -> t
  > prim z_land : int -> int -> int
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
  > rule land : Land (v1, v2)
  > 
  > fn f (a b c : t) : t = a +. b *. c ^^ ~a ≤ c
  > fn g (x y : int) : bool = x + y * 2 < 3 - -x
  > fn masked (x y : int) (a b : t) : t = if x &&& y = 0 then a &&& b else a
  > KN
  $ kanon ocaml ops.knl ops.kn | sed -n '/ f (a/,$p'
  let[@inline] f (a : t) (b : t) (c : t) : t =
      (le (cat (add a (mul b c)) (neg a)) c)
  
  let[@inline] g (x : Z.t) (y : Z.t) : bool =
      (Z.lt (Z.add x (Z.mul y (Z.of_int (2)))) (Z.sub (Z.of_int (3)) (Z.neg x)))
  
  let[@inline] masked (x : Z.t) (y : Z.t) (a : t) (b : t) : t =
      (if ((Z.equal (Prims.z_land x y) Z.zero)) then (land a b) else a)
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

A word declared infix is an operator at the level of *, as OCaml's mod and
land: 0 == l lor r is 0 == (l lor r), and k < 1 lsl (n - 1) is
k < (1 lsl (n - 1)).

  $ cat > words.knl <<'KN'
  > node Lor : TInt -> TInt -> TInt
  > node Shl : TInt -> TInt -> TInt
  > node Eqi : TInt -> TInt -> TBool
  > infix "lor" = Lor, lor_, z_lor
  > infix "lsl" = Shl, shl, z_lsl
  > infix "==" = Eqi, eqi
  > KN
  $ cat > words.kn <<'KN'
  > prim z_lor : int -> int -> int
  > prim z_lsl : int -> int -> int
  > rule lor_ : Lor (v1, v2)
  > rule shl : Shl (v1, v2)
  > rule eqi : Eqi (v1, v2) =
  >   | zero_or: 0 == l lor r -> Bool false
  > fn small (k n : int) : bool = k < 1 lsl (n - 1)
  > fn is_or (a l r : t) : t = a == l lor r
  > KN
  $ kanon ocaml ops.knl words.knl ops.kn words.kn | sed -n '/let eqi/,$p'
  let eqi (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TInt), (TInt)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | ({ kind = Int (kanon__1); _ }, { kind = Op2 ((Lor), l, r); _ })
        when (((Z.equal kanon__1 Z.zero))) ->
        (node (Bool (false)) TBool)
      | _ -> (node (Op2 (Eqi, v1, v2)) TBool)
      ))
  
  let[@inline] small (k : Z.t) (n : Z.t) : bool =
      (Z.lt k (Prims.z_lsl Z.one (Z.sub n Z.one)))
  
  let[@inline] is_or (a : t) (l : t) (r : t) : t = (eqi a (lor_ l r))
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_lor (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Lor, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_lor (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Lor, _, _); _ } -> true | _ -> false
  
  let as_shl (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Shl, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_shl (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Shl, _, _); _ } -> true | _ -> false
  
  let as_eqi (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Eqi, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_eqi (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Eqi, _, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

A symbolic operator may end with a word, if it is declared: <u is an operator
(at the level of <), distinct from < and from the application of u: a <u b is
not a < u b, and x<y is not changed by the declaration. The prefix operators
and the patterns have them too, and a symbol that is not declared with its word
is read as the symbol, then the word.

  $ cat > suffix.knl <<'KN'
  > node Ult : TInt -> TInt -> TBool
  > node Ule : TInt -> TInt -> TBool
  > node Pu : TInt -> TInt
  > infix "<u" = Ult, ult, z_ult
  > infix "<=u" = Ule, ule
  > prefix "!u" = Pu, pu
  > KN
  $ cat > suffix.kn <<'KN'
  > prim z_ult : int -> int -> bool
  > rule ult : Ult (v1, v2) =
  >   | same: a <u b when false -> a <=u b
  > rule ule : Ule (v1, v2)
  > rule pu : Pu v
  > fn u (x : int) : int = x
  > fn lt_t (a b : t) : t = a <u b
  > fn lt_z (x y : int) : bool = x <u y
  > fn lt_app (x y : int) : bool = x < u y
  > fn lt_tight (x y : int) : bool = x<u y
  > fn lt_plain (x y : int) : bool = x<y
  > fn prefixed (a b : t) : t = !u a <=u b
  > KN
  $ kanon ocaml ops.knl suffix.knl ops.kn suffix.kn | sed -n '/ lt_t (a/,$p'
  let[@inline] lt_t (a : t) (b : t) : t = (ult a b)
  
  let[@inline] lt_z (x : Z.t) (y : Z.t) : bool = (Prims.z_ult x y)
  
  let[@inline] lt_app (x : Z.t) (y : Z.t) : bool = (Z.lt x (u y))
  
  let[@inline] lt_tight (x : Z.t) (y : Z.t) : bool = (Prims.z_ult x y)
  
  let[@inline] lt_plain (x : Z.t) (y : Z.t) : bool = (Z.lt x y)
  
  let[@inline] prefixed (a : t) (b : t) : t = (ule (pu a) b)
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_ult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Ult, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_ult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Ult, _, _); _ } -> true | _ -> false
  
  let as_ule (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Ule, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_ule (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Ule, _, _); _ } -> true | _ -> false
  
  let as_pu (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Pu, x1); _ } -> Some x1 | _ -> None
  
  let is_pu (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Pu, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

A symbol that does not start an operator cannot have a suffix:

  $ cat > badsuffix.knl <<'KN'
  > infix ".u" = Le, le
  > KN
  $ kanon ocaml ops.knl badsuffix.knl ops.kn
  badsuffix.knl:1:7: .u is not an infix operator, nor a word
  [1]

A suffix that is not declared is not read as part of the symbol:

  $ cat > nosuffix.kn <<'KN'
  > fn u (x : int) : int = x
  > fn lt_u (x y : int) : bool = x <u y
  > KN
  $ kanon ocaml ops.knl ops.kn nosuffix.kn | sed -n '/ lt_u/,$p'
  let[@inline] lt_u (x : Z.t) (y : Z.t) : bool = (Z.lt x (u y))
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

The laws of integer literals, written with the notation Int: the results of
[@fold] are lifted by the notation of their type (Int, for add_z), or by the
function or node given after it (Int, of_bool).

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
  $ cat > bad.knl <<'KN'
  > infix "**" = Mul, mul, z_land
  > infix "*" = Mul, mul, z_land
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:2:7: * is built in on int: it cannot also be the function z_land
  [1]
  $ cat > bad.kn <<'KN'
  > fn h (a b : bool) : bool = a &&& b
  > KN
  $ kanon ocaml ops.knl ops.kn bad.kn
  bad.kn:1:27: &&& is not defined on bool, bool: its function z_land takes int, int
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
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  
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
    | Land
  
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
  
  let as_int (t : t) =
    match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
  
  let is_int (t : t) =
    match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, x1); _ } -> Some x1 | _ -> None
  
  let is_neg (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Neg, _); _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
  
  let as_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_mul (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Mul, _, _); _ } -> true | _ -> false
  
  let as_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_cat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Cat, _, _); _ } -> true | _ -> false
  
  let as_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_le (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Le, _, _); _ } -> true | _ -> false
  
  let as_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_land (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Land, _, _); _ } -> true | _ -> false
  
  let as_max (t : t) =
    match[@warning "-11"] t with { kind = OpN (Max, xs); _ } -> Some xs | _ -> None
  
  let is_max (t : t) =
    match[@warning "-11"] t with { kind = OpN (Max, _); _ } -> true | _ -> false
  
  let as_same (t : t) =
    match[@warning "-11"] t with { kind = OpN (Same, xs); _ } -> Some xs | _ -> None
  
  let is_same (t : t) =
    match[@warning "-11"] t with { kind = OpN (Same, _); _ } -> true | _ -> false
  
  let as_tint (t : ty) =
    match[@warning "-11"] t with TInt -> Some () | _ -> None
  
  let is_tint (t : ty) = match[@warning "-11"] t with TInt -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  
  $ echo 'node Bad : TInt list -> TInt -> TInt' > bad.knl
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:11: Bad: s list is only allowed as the only operand sort
  [1]

The literals of patterns stand for the nodes of the notations: true and false
for the notation of bool, 0, 1, ... for that of int, and #x and #_ for either.
When several notations may stand for a literal, the sort of its position
chooses: that of an operand of a node, of an operand of a spec, or of a
parameter of a function, which may be annotated with its sort. Here, BitVec
stores the unsigned integer of a bit-vector, whose width is in its sort.

  $ cat > bv.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > node Bool of bool : TBool
  > node BitVec of int : TBitVector n
  > notation Bool
  > notation BitVec
  > node BvAdd : TBitVector n -> TBitVector n -> TBitVector n [@comm]
  >     [@fold z_add] [@unit 0]
  > node BvConcat : TBitVector n -> TBitVector m -> TBitVector (n + m)
  >     [@fold z_concat]
  > node BvUlt : TBitVector n -> TBitVector n -> TBool [@fold z_ult]
  > sort TBitVector of nat [@get size]
  > sort TBool
  > infix "+" = BvAdd, bv_add
  > infix "++" = BvConcat, bv_concat
  > KN
  $ cat > bv.kn <<'KN'
  > prim size_of : ty -> int
  > prim wrap : int -> int -> int
  > fn size (v : t) : int [@ty_only] = size_of (type_of v)
  > fn z_add (s _ : ty) (l r : int) : int = wrap (size_of s) (l + r)
  > fn z_concat (_ s : ty) (l r : int) : int = l * size_of s + r
  > fn z_ult (l r : int) : bool = l < r
  > 
  > (* a literal of width n: built at its sort, which its typing does not give *)
  > fn lit (n z : int) : t = (BitVec (wrap n z) : TBitVector n)
  > 
  > fn msb (v : TBitVector n) : int =
  >   match v with
  >   | #z when z > 0 -> z
  >   | 0 -> n - 1
  >   | _ + #k -> k
  >   | _ -> n
  > 
  > rule bv_add : BvAdd ((v1 : TBitVector n), v2) =
  >   | max: x + #k when k = n -> x + lit n 0
  > rule bv_concat : BvConcat (v1, v2)
  > rule bv_ult : BvUlt (v1, v2) =
  >   | zero: _, 0 -> Bool false
  >   | true_: _, _ when false -> Bool true
  > KN
  $ kanon ocaml bv.knl bv.kn | sed -n '/ lit /,$p'
  let[@inline] lit (n : Z.t) (z : Z.t) : t =
      (node (BitVec ((Prims.wrap n z))) (TBitVector ((Z.to_int n))))
  
  let msb (v : t) : Z.t =
      (let n = (size v) in
      (assert ((match v.ty with
               | (TBitVector (kanon__v_n)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v with
      | { kind = BitVec (z); _ } when ((Z.gt z Z.zero)) -> z
      | { kind = BitVec (kanon__1); _ }
        when (((Z.equal kanon__1 Z.zero))) ->
        (Z.sub n Z.one)
      | { kind = Op2 ((BvAdd), _, { kind = BitVec (k); _ }); _ } -> k
      | { kind = Op2 ((BvAdd), { kind = BitVec (k); _ }, _); _ } -> k
      | _ -> n
      )))
  
  let rec bv_add (v1 : t) (v2 : t) : t =
      (let n = (size v1) in
      (assert ((match v1.ty, v2.ty with
               | ((TBitVector (kanon__n)), (TBitVector (kanon__s1)))
                 when (let kanon__n = Z.of_int kanon__n in
                 let kanon__s1 = Z.of_int kanon__s1 in
                 ((Z.equal kanon__s1 kanon__n))) ->
                 true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | (({ kind = BitVec (i1); _ } as lit_i1), ({ kind = BitVec (i2); _ } as lit_i2)) ->
        (node (BitVec ((z_add lit_i1.ty lit_i2.ty i1 i2))) v1.ty)
      | (x, { kind = BitVec (kanon__2); _ })
        when (((Z.equal kanon__2 Z.zero))) ->
        x
      | ({ kind = BitVec (kanon__2); _ }, x)
        when (((Z.equal kanon__2 Z.zero))) ->
        x
      | (x, { kind = BitVec (k); _ })
        when (((Z.equal k n))) ->
        (bv_add x (lit n Z.zero))
      | ({ kind = BitVec (k); _ }, x)
        when (((Z.equal k n))) ->
        (bv_add x (lit n Z.zero))
      | _ -> (node (mk_commut_binop BvAdd v1 v2) v1.ty)
      )))
  
  let bv_concat (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBitVector (kanon__n)), (TBitVector (kanon__m))) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | (({ kind = BitVec (i1); _ } as lit_i1), ({ kind = BitVec (i2); _ } as lit_i2)) ->
        (node (BitVec ((z_concat lit_i1.ty lit_i2.ty i1 i2))) (TBitVector ((Z.to_int (Z.add (size v1) (size v2))))))
      | _ ->
        (node (Op2 (BvConcat, v1, v2)) (TBitVector ((Z.to_int (Z.add (size v1) (size v2))))))
      ))
  
  let bv_ult (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBitVector (kanon__n)), (TBitVector (kanon__s1)))
                 when (let kanon__n = Z.of_int kanon__n in
                 let kanon__s1 = Z.of_int kanon__s1 in
                 ((Z.equal kanon__s1 kanon__n))) ->
                 true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | ({ kind = BitVec (i1); _ }, { kind = BitVec (i2); _ }) ->
        (node (Bool ((z_ult i1 i2))) TBool)
      | (_, { kind = BitVec (kanon__2); _ })
        when (((Z.equal kanon__2 Z.zero))) ->
        (node (Bool (false)) TBool)
      | (_, _) when (false) -> (node (Bool (true)) TBool)
      | _ -> (node (Op2 (BvUlt, v1, v2)) TBool)
      ))
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_bitvec (t : t) =
    match[@warning "-11"] t with { kind = BitVec (p1); _ } -> Some p1 | _ -> None
  
  let is_bitvec (t : t) =
    match[@warning "-11"] t with { kind = BitVec (_); _ } -> true | _ -> false
  
  let as_bvadd (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvAdd, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvadd (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvAdd, _, _); _ } -> true | _ -> false
  
  let as_bvconcat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvConcat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvconcat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvConcat, _, _); _ } -> true | _ -> false
  
  let as_bvult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvUlt, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvUlt, _, _); _ } -> true | _ -> false
  
  let as_tbitvector (t : ty) =
    match[@warning "-11"] t with TBitVector (p1) -> Some p1 | _ -> None
  
  let is_tbitvector (t : ty) =
    match[@warning "-11"] t with TBitVector (_) -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

A literal that several notations may stand for, at a position whose sort is
unknown, or whose sort is none of theirs, is an error; a node is built at a
sort that its typing allows; and the sort of a literal node that its typing
does not determine is given.

  $ cat > bad.kn <<'KN'
  > fn h (a : t) : int = match a with #x -> 0 | _ -> 1
  > KN
  $ kanon ocaml bv.knl bv.kn bad.kn
  bad.kn:1:34: #x may be a literal of Bool or BitVec, and the sort of this position is unknown; write the node (Bool x or BitVec x)
  [1]
  $ echo 'sort TOther' > bad.knl
  $ cat > bad.kn <<'KN'
  > fn h (a : TOther) : int = match a with #x -> 0 | _ -> 1
  > KN
  $ kanon ocaml bv.knl bad.knl bv.kn bad.kn
  bad.kn:1:39: #x: none of the notations Bool, BitVec has the sort TOther of this position; write the node (Bool x or BitVec x)
  [1]
  $ cat > bad.kn <<'KN'
  > fn h (z : int) : t = (BitVec z : TBool)
  > KN
  $ kanon ocaml bv.knl bv.kn bad.kn
  bad.kn:1:33: BitVec is a term of sort TBitVector, by its typing, not TBool
  [1]
  $ cat > bad.kn <<'KN'
  > fn h (z : int) : t = BitVec z
  > KN
  $ kanon ocaml bv.knl bv.kn bad.kn
  bad.kn:1:21: BitVec: the sort of its result is not determined; build it at a sort, (BitVec ... : S args)
  [1]

The notations replace the attributes of literals; a notation is a leaf node of
one int or bool. [@ite] and [@distrib_ite] are gone.

  $ echo 'node B of bool : TBool [@literal bool] [@to_term of_bool]' > bad.knl
  $ kanon ocaml bad.knl
  bad.knl:1:25: [@literal] is gone: [notation B] makes the literals of patterns stand for a leaf node of one int or bool
  [1]
  $ printf 'node B of bool : TBool\nnotation B\nnotation B\n' > bad.knl
  $ kanon ocaml bad.knl
  bad.knl:3:9: notation B is declared twice
  [1]
  $ printf 'node B : TBool -> TBool\nnotation B\nsort TBool\n' > bad.knl
  $ kanon ocaml bad.knl
  bad.knl:2:9: notation B: B is not a leaf node of one int or bool
  [1]
  $ cat > bad.knl <<'KN'
  > node Ite : TBool -> a -> a -> a [@ite]
  > KN
  $ kanon ocaml ops.knl bad.knl ops.kn
  bad.knl:1:34: unknown attribute [@ite]
  [1]

A unit or a zero may be a named constant, built at the sort of the other
operand, which the derived rule compares with = (a guard); a literal unit or
zero is the node of its notation, built at the sort of the spec unless a
constant gives it.

  $ cat > ones.knl <<'KN'
  > node BvAnd : TBitVector n -> TBitVector n -> TBitVector n [@comm]
  >     [@unit ones] [@zero 0]
  > constant ones (v) = ones_of v
  > KN
  $ cat > ones.kn <<'KN'
  > prim ones_of : t -> t
  > rule bv_and : BvAnd (v1, v2)
  > KN
  $ kanon ocaml bv.knl ones.knl bv.kn ones.kn | sed -n '/let bv_and/,/^$/p'
  let bv_and (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBitVector (kanon__n)), (TBitVector (kanon__s1)))
                 when (let kanon__n = Z.of_int kanon__n in
                 let kanon__s1 = Z.of_int kanon__s1 in
                 ((Z.equal kanon__s1 kanon__n))) ->
                 true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | (x, y) when ((Int.equal y.tag (Prims.ones_of x).tag)) -> x
      | (y, x) when ((Int.equal y.tag (Prims.ones_of x).tag)) -> x
      | (_, { kind = BitVec (kanon__2); _ })
        when (((Z.equal kanon__2 Z.zero))) ->
        (node (BitVec (Z.zero)) v1.ty)
      | ({ kind = BitVec (kanon__2); _ }, _)
        when (((Z.equal kanon__2 Z.zero))) ->
        (node (BitVec (Z.zero)) v1.ty)
      | _ -> (node (mk_commut_binop BvAnd v1 v2) v1.ty)
      ))
  
  $ sed 's/unit ones/unit twos/' ones.knl > bad.knl
  $ kanon ocaml bv.knl bad.knl bv.kn ones.kn
  bad.knl:2:11: expected the literal 0, 1, true or false, or a constant: twos is not declared
  [1]

The variables of the sorts of the parameters are bound once, on entry (when
the body uses them), so that a pattern may rebind a parameter: here [n] stays
the width of the outer [v]. The spec of a rule reads them from its parameters.

  $ cat > shadow.knl <<'KN'
  > node BvExtend of nat (k) : TBitVector n -> TBitVector (n + k)
  > node FloatOfBv of int : TBitVector n -> TFloat
  > node FloatOfBits of nat (w) : TBitVector w -> TFloat
  > sort TFloat
  > KN
  $ cat > shadow.kn <<'KN'
  > fn msb_of (v : TBitVector n) : int =
  >   match v with
  >   | BvExtend (_, v) when n > 3 -> msb_of v
  >   | _ -> n - 1
  > 
  > rule bv_extend : BvExtend (k, (v : TBitVector n)) =
  >   | extend: BvExtend (j, v) when n > 3 -> BvExtend (k + j, v)
  > 
  > rule float_of (v : TBitVector n) : FloatOfBv (2 * n, v)
  > 
  > rule float_of_bits (v : TBitVector n) : FloatOfBits (n, v)
  > KN
  $ kanon ocaml bv.knl shadow.knl bv.kn shadow.kn | sed -n '/let rec msb_of/,$p'
  let rec msb_of (v : t) : Z.t =
      (let n = (size v) in
      (assert ((match v.ty with
               | (TBitVector (kanon__v_n)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v with
      | { kind = Op1 ((BvExtend (_)), v); _ }
        when ((Z.gt n (Z.of_int (3)))) ->
        (msb_of v)
      | _ -> (Z.sub n Z.one)
      )))
  
  let bv_extend (k : Z.t) (v : t) : t =
      (let n = (size v) in
      (assert ((match v.ty with
               | (TBitVector (kanon__n)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v with
      | { kind = Op1 ((BvExtend (j)), v); _ }
        when ((Z.gt n (Z.of_int (3)))) ->
        let j = Z.of_int j in
        (node (Op1 ((BvExtend ((Z.to_int (Z.add k j)))), v)) (TBitVector ((Z.to_int (Z.add (size v) (Z.add k j))))))
      | _ ->
        (node (Op1 ((BvExtend ((Z.to_int k))), v)) (TBitVector ((Z.to_int (Z.add (size v) k)))))
      )))
  
  let float_of (v : t) : t =
      (let n = (size v) in
      (assert ((match v.ty with
               | (TBitVector (kanon__n)) -> true
               | _ -> false
               ) [@warning "-11"]);
      (match v with
      | _ -> (node (Op1 ((FloatOfBv ((Z.mul (Z.of_int (2)) n))), v)) TFloat)
      )))
  
  let float_of_bits (v : t) : t =
      (let n = (size v) in
      (assert ((match v.ty with
               | (TBitVector (kanon__s1))
                 when (let kanon__s1 = Z.of_int kanon__s1 in
                 ((Z.equal kanon__s1 n))) ->
                 true
               | _ -> false
               ) [@warning "-11"]);
      (match v with
      | _ -> (node (Op1 ((FloatOfBits ((Z.to_int n))), v)) TFloat)
      )))
  
  let as_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (p1); _ } -> Some p1 | _ -> None
  
  let is_bool (t : t) =
    match[@warning "-11"] t with { kind = Bool (_); _ } -> true | _ -> false
  
  let as_bitvec (t : t) =
    match[@warning "-11"] t with { kind = BitVec (p1); _ } -> Some p1 | _ -> None
  
  let is_bitvec (t : t) =
    match[@warning "-11"] t with { kind = BitVec (_); _ } -> true | _ -> false
  
  let as_bvadd (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvAdd, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvadd (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvAdd, _, _); _ } -> true | _ -> false
  
  let as_bvconcat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvConcat, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvconcat (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvConcat, _, _); _ } -> true | _ -> false
  
  let as_bvult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvUlt, x1, x2); _ } -> Some (x1, x2) | _ -> None
  
  let is_bvult (t : t) =
    match[@warning "-11"] t with { kind = Op2 (BvUlt, _, _); _ } -> true | _ -> false
  
  let as_bvextend (t : t) =
    match[@warning "-11"] t with { kind = Op1 (BvExtend (p1), x1); _ } -> Some (p1, x1) | _ -> None
  
  let is_bvextend (t : t) =
    match[@warning "-11"] t with { kind = Op1 (BvExtend (_), _); _ } -> true | _ -> false
  
  let as_floatofbv (t : t) =
    match[@warning "-11"] t with { kind = Op1 (FloatOfBv (p1), x1); _ } -> Some (p1, x1) | _ -> None
  
  let is_floatofbv (t : t) =
    match[@warning "-11"] t with { kind = Op1 (FloatOfBv (_), _); _ } -> true | _ -> false
  
  let as_floatofbits (t : t) =
    match[@warning "-11"] t with { kind = Op1 (FloatOfBits (p1), x1); _ } -> Some (p1, x1) | _ -> None
  
  let is_floatofbits (t : t) =
    match[@warning "-11"] t with { kind = Op1 (FloatOfBits (_), _); _ } -> true | _ -> false
  
  let as_tbitvector (t : ty) =
    match[@warning "-11"] t with TBitVector (p1) -> Some p1 | _ -> None
  
  let is_tbitvector (t : ty) =
    match[@warning "-11"] t with TBitVector (_) -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  let as_tfloat (t : ty) =
    match[@warning "-11"] t with TFloat -> Some () | _ -> None
  
  let is_tfloat (t : ty) =
    match[@warning "-11"] t with TFloat -> true | _ -> false
  
  
  $ kanon lean-statements bv.knl shadow.knl bv.kn shadow.kn | sed -n '/bv_extend.r_extend.main.Stmt/,/^$/p'
  def bv_extend.r_extend.main.Stmt : Prop :=
    ∀ (O : Ops), O.Sound →
    ∀ (k : Int) (j : Int) (v : Term) (t__4 : Ty),
    (decide ((size (Term.mk (Kind.Op1 (Op1.BvExtend j) v) t__4)) > (3 : Int))) = true →
    Refines (bv_extend.spec k (Term.mk (Kind.Op1 (Op1.BvExtend j) v) t__4))
    ((Term.mk (Kind.Op1 (Op1.BvExtend (k + j)) v) (Ty.TBitVector ((size v) + (k + j)))))
  

The rules call the primitives in the module of [@@@ocaml_prims], which the
language must name, and the types of ocaml-types need the OCaml types of the
abstract types.

  $ grep -v ocaml_prims bv.knl > noprims.knl
  $ kanon ocaml noprims.knl bv.kn
  bv.kn:1:5: size_of is a primitive: [@@@ocaml_prims "M"], in the declaration of the language, names the OCaml module that implements the primitives
  [1]
  $ echo 'type bv' > noocaml.knl
  $ kanon ocaml-types bv.knl noocaml.knl
  noocaml.knl:1:5: type bv is abstract: [@ocaml "M.t"] gives its OCaml type
  [1]
  $ cat > bad.knl <<'KN'
  > type pair [@noeq] = { left : int; right : int }
  > KN
  $ kanon ocaml-types bv.knl bad.knl
  bad.knl:1:12: [@noeq] applies to abstract types
  [1]
