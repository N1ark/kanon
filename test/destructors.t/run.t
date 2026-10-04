The ocaml backend generates, for every node and every sort, a function
`as_foo`, which gives the arguments of a term built by the node `Foo` (its
parameters, then its operands, as in a pattern) in an option, and a test
`is_foo`. The name is that of the constructor, in lowercase. They come after
the rules.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "P"]
  > sort TBv of nat
  > sort TBool
  > node Lit of int * nat (v, n) : TBv n
  > node Add of bool (c) : TBv n -> TBv n -> TBv n
  > node Not : TBool -> TBool
  > node Concat : (TBv 8) list -> TBv 8
  > node Unit : TBool
  > KN
  $ cat > rules.kn <<'KN'
  > rule add : Add (c, v1, v2)
  > rule not_ : Not v
  > rule concat : Concat vs
  > KN
  $ kanon ocaml lang.knl rules.kn | sed -n '/^let as_lit/,$p'
  let as_lit (t : t) =
    match[@warning "-11"] t with { kind = Lit (p1, p2); _ } -> Some (p1, p2) | _ -> None
  
  let is_lit (t : t) =
    match[@warning "-11"] t with { kind = Lit (_, _); _ } -> true | _ -> false
  
  let as_unit (t : t) =
    match[@warning "-11"] t with { kind = Unit; _ } -> Some () | _ -> None
  
  let is_unit (t : t) =
    match[@warning "-11"] t with { kind = Unit; _ } -> true | _ -> false
  
  let as_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add (p1), x1, x2); _ } -> Some (p1, x1, x2) | _ -> None
  
  let is_add (t : t) =
    match[@warning "-11"] t with { kind = Op2 (Add (_), _, _); _ } -> true | _ -> false
  
  let as_not (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Not, x1); _ } -> Some x1 | _ -> None
  
  let is_not (t : t) =
    match[@warning "-11"] t with { kind = Op1 (Not, _); _ } -> true | _ -> false
  
  let as_concat (t : t) =
    match[@warning "-11"] t with { kind = OpN (Concat, xs); _ } -> Some xs | _ -> None
  
  let is_concat (t : t) =
    match[@warning "-11"] t with { kind = OpN (Concat, _); _ } -> true | _ -> false
  
  let as_tbv (t : ty) =
    match[@warning "-11"] t with TBv (p1) -> Some p1 | _ -> None
  
  let is_tbv (t : ty) =
    match[@warning "-11"] t with TBv (_) -> true | _ -> false
  
  let as_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> Some () | _ -> None
  
  let is_tbool (t : ty) =
    match[@warning "-11"] t with TBool -> true | _ -> false
  
  

A function or a primitive may not have the name of a destructor, nor may two
constructors that differ by their case have the same one:

  $ cat > clash.kn <<'KN'
  > fn is_add (x : int) : int = x
  > KN
  $ kanon ocaml lang.knl rules.kn clash.kn
  clash.kn:1:0: is_add is the destructor of Add: rename the function
  [1]
  $ cat > clash.kn <<'KN'
  > prim as_not : int -> int
  > KN
  $ kanon ocaml lang.knl rules.kn clash.kn
  clash.kn:1:5: as_not is the destructor of Not: rename the primitive
  [1]
  $ cat > twice.knl <<'KN'
  > node Lit2 of int : TBool
  > node LIT2 of int : TBool
  > KN
  $ kanon ocaml lang.knl twice.knl rules.kn
  kanon: as_lit2 is the destructor of LIT2, which is also Lit2
  [1]
