A subsort is a sort of the same arguments as its parent, which a node may use
in its typing: `subsort TNonzero of nat : TBitVector n`. It has no constructor
of its own and no other meaning in OCaml: the generated types and rules are
those of the parent, so that a subsort in a typing is the sort of its parent.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "rules"
  > sort TBitVector of nat [@get size]
  > subsort TNonzero of nat : TBitVector n
  > subsort TZero of nat : TBitVector n
  > sort TBool
  > node BitVec of int * nat (v, n) : TBitVector n [@ctor mk_bv]
  > node Zero of nat (n) : TZero n [@ctor mk_zero]
  > node Div of bool : TBitVector n -> TNonzero n -> TBitVector n
  > node Ult : TBitVector n -> TBitVector n -> TBool
  > KN
  $ cat > rules.kn <<'KN'
  > prim size : t -> int
  > rule bv_div : Div (signed, v1, v2)
  > KN
  $ kanon ocaml-types lang.knl | sed -n '/^type kind/,/^and t =/p'
  type kind =
    | BitVec of Z.t * int
    | Zero of int
    | Op2 of op2 * t * t
  
  and op2 =
    | Div of bool
    | Ult
  
  and ty =
    | TBitVector of int
    | TBool
  
  and t = {
  $ kanon ocaml lang.knl | sed -n '/let bv_div/,/^$/p'
  let bv_div (signed : bool) (v1 : t) (v2 : t) : t =
      (assert ((match v1.ty, v2.ty with
               | ((TBitVector (kanon__n)), (TBitVector (kanon__s1)))
                 when (let kanon__n = Z.of_int kanon__n in
                 let kanon__s1 = Z.of_int kanon__s1 in
                 ((Z.equal kanon__s1 kanon__n))) ->
                 true
               | _ -> false
               ) [@warning "-11"]);
      (match v1, v2 with
      | _ -> (node (Op2 ((Div (signed)), v1, v2)) v1.ty)
      ))
  

The checks of a subsort declaration: its arguments are those of its parent
sort, which it applies to variables, and it is the sort of an operand or of a
result only.

  $ check() { printf '%s\n' 'sort TBitVector of nat' 'sort TBool' "$@" > bad.knl; kanon ocaml-types bad.knl > /dev/null; }
  $ check 'subsort A of int : TBitVector n'
  bad.knl:3:8: subsort A: its arguments must be those of TBitVector (nat)
  [1]
  $ check 'subsort A of nat : TBitVector 32'
  bad.knl:3:19: subsort A: its parent TBitVector must be applied to the arguments of the subsort, as distinct variables
  [1]
  $ check 'subsort A of nat * nat : TBitVector (n, n)'
  bad.knl:3:8: subsort A: its arguments must be those of TBitVector (nat)
  [1]
  $ check 'subsort A of nat : TBool'
  bad.knl:3:8: subsort A: its arguments must be those of TBool (none)
  [1]
  $ check 'subsort A of nat : TBitVector n' 'subsort B of nat : A n'
  bad.knl:4:19: A is a subsort: the parent of a subsort is a sort
  [1]
  $ check 'subsort A of nat : TSeq n'
  bad.knl:3:19: unknown sort TSeq
  [1]
  $ check 'subsort A of nat (n) : TBitVector n'
  bad.knl:3:17: subsort A: a subsort has no argument names nor condition: its arguments are those of its parent
  [1]
  $ check 'subsort A of nat'
  bad.knl:3:8: subsort A: expected its parent sort: subsort A of args : Parent args
  [1]
  $ check 'subsort A of nat : TBitVector n [@foo]'
  bad.knl:3:34: unknown attribute [@foo]
  [1]
  $ check 'subsort TBitVector of nat : TBitVector n'
  bad.knl:3:8: subsort TBitVector is declared twice
  [1]
  $ check 'subsort A of nat : TBitVector n' 'subsort A of nat : TBitVector n'
  bad.knl:4:8: subsort A is declared twice
  [1]
  $ check 'subsort A of nat : TBitVector n' 'node Foo : TBitVector (A n) -> TBool'
  bad.knl:4:23: A is a subsort: it is the sort of an operand or of a result, not an argument of a sort
  [1]
