The `ocaml` backend generates printers in the types: `pp` for the terms, `pp_ty`
for the sorts and `pp_foo` for each declared type. A node of a notation is its
literal, a node of an infix or a prefix operator without parameters is in its
notation, in parentheses, and any other node is its name, applied to its
arguments. A value of an abstract type is printed by its `[@pp]`, or else is
`<foo>`.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Types"]
  > type var [@ocaml "string"] [@pp "Format.pp_print_string"]
  > type loc [@ocaml "int"]
  > type flag = On | Off of int
  > type cell = { key : var; flag : flag; next : cell option }
  > sort TInt
  > sort TBool
  > sort TBv of nat
  > sort TPair of ty * ty
  > node Var of var
  > node Int of int : TInt
  > notation Int
  > node At of loc
  > node Plus : TInt -> TInt -> TInt
  > node Neg : TInt -> TInt
  > node Not : TBool -> TBool
  > node Bool of bool : TBool
  > node Add of bool (c) : TInt -> TInt -> TInt
  > node Sum : TInt list -> TInt
  > node Mix of (int * t) option * t array * cell * unit : TInt
  > infix "+" = Plus, plus
  > prefix "-" = Neg, neg
  > prefix "not" = Not, not_
  > infix "+." = Add true, add true
  > KN
  $ cat > rules.kn <<'KN'
  > rule plus : Plus (v1, v2)
  > rule neg : Neg v
  > rule not_ : Not v
  > rule add : Add (c, v1, v2)
  > KN
  $ kanon ocaml out lang.knl rules.kn && sed -n '/^let rec pp /,$p' out/Generated/types.ml
  let rec pp (ft : Stdlib.Format.formatter) (a : t) : unit =
    match a.kind with
    | Var (p1) -> Stdlib.Format.fprintf ft "@[<hov 2>Var(%a)@]" pp_var p1
    | Int (p1) -> Z.pp_print ft p1
    | At (p1) -> Stdlib.Format.fprintf ft "@[<hov 2>At(%a)@]" pp_loc p1
    | Bool (p1) ->
        Stdlib.Format.fprintf ft "@[<hov 2>Bool(%a)@]" Stdlib.Format.pp_print_bool p1
    | Mix (p1, p2, p3, p4) ->
        Stdlib.Format.fprintf ft "@[<hov 2>Mix(%a,@ %a,@ %a,@ %a)@]" (kanon__pp_option (fun ft (a1, a2) -> Stdlib.Format.fprintf ft "@[<hov 1>(%a,@ %a)@]" Z.pp_print a1 pp a2)) p1 (fun ft a -> kanon__pp_seq "[|" "|]" pp ft (Stdlib.Iarray.to_list a)) p2 pp_cell p3 (fun ft () -> Stdlib.Format.pp_print_string ft "()") p4
    | Op2 (Plus, x1, x2) ->
        Stdlib.Format.fprintf ft "@[<hov 1>(%a %s@ %a)@]" pp x1 "+" pp x2
    | Op1 (Neg, x1) -> Stdlib.Format.fprintf ft "@[<hov 1>(%s%a)@]" "-" pp x1
    | Op1 (Not, x1) ->
        Stdlib.Format.fprintf ft "@[<hov 1>(%s%a)@]" "not " pp x1
    | Op2 (Add (p1), x1, x2) ->
        Stdlib.Format.fprintf ft "@[<hov 2>Add(%a,@ %a,@ %a)@]" Stdlib.Format.pp_print_bool p1 pp x1 pp x2
    | OpN (Sum, x1) ->
        Stdlib.Format.fprintf ft "@[<hov 2>Sum(%a)@]" (kanon__pp_seq "[" "]" pp) x1
  
  and pp_var (ft : Stdlib.Format.formatter) (a : var) : unit =
    Format.pp_print_string ft a
  
  and pp_loc (ft : Stdlib.Format.formatter) (a : loc) : unit =
    Stdlib.Format.pp_print_string ft "<loc>"
  
  and pp_flag (ft : Stdlib.Format.formatter) (a : flag) : unit =
    match a with
    | On -> Stdlib.Format.pp_print_string ft "On"
    | Off (x1) -> Stdlib.Format.fprintf ft "@[<hov 2>Off(%a)@]" Z.pp_print x1
  
  and pp_cell (ft : Stdlib.Format.formatter) (a : cell) : unit =
    Stdlib.Format.fprintf ft "@[<hv 2>{ key = %a;@ flag = %a;@ next = %a }@]" pp_var a.key pp_flag a.flag (kanon__pp_option pp_cell) a.next
  
  and pp_ty (ft : Stdlib.Format.formatter) (a : ty) : unit =
    match a with
    | TInt -> Stdlib.Format.pp_print_string ft "TInt"
    | TBool -> Stdlib.Format.pp_print_string ft "TBool"
    | TBv (x1) ->
        Stdlib.Format.fprintf ft "@[<hov 2>TBv(%a)@]" Stdlib.Format.pp_print_int x1
    | TPair (x1, x2) ->
        Stdlib.Format.fprintf ft "@[<hov 2>TPair(%a,@ %a)@]" pp_ty x1 pp_ty x2

They print as follows:

  $ cp out/Generated/types.ml types.ml
  $ cat > main.ml <<'ML'
  > open Types
  > let int n = node (Int (Z.of_int n)) TInt
  > let x = node (Var "x") TInt
  > let cell = { key = "k"; flag = Off (Z.of_int 3); next = Some { key = "l"; flag = On; next = None } }
  > let terms =
  >   [ node (Op2 (Plus, x, int (-1))) TInt;
  >     node (Op1 (Neg, node (Op1 (Neg, x)) TInt)) TInt;
  >     node (Op1 (Not, node (Bool true) TBool)) TBool;
  >     node (Op2 (Add true, x, int 1)) TInt;
  >     node (OpN (Sum, [ x; int 2 ])) TInt;
  >     node (OpN (Sum, [])) TInt;
  >     node (At 7) TInt;
  >     node (Mix (Some (Z.one, x), Iarray.of_list [ x; x ], cell, ())) TInt ]
  > let () =
  >   List.iter (Format.printf "%a@." pp) terms;
  >   List.iter (Format.printf "%a@." pp_ty) [ TInt; TBv 32; TPair (TBv 8, TBool) ]
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg types.ml main.ml -o main.exe && ./main.exe
  (Var(x) + -1)
  (-(-Var(x)))
  (not Bool(true))
  Add(true, Var(x), 1)
  Sum([Var(x); 2])
  Sum([])
  At(<loc>)
  Mix(Some((1, Var(x))), [|Var(x); Var(x)|],
    { key = k;
      flag = Off(3);
      next = Some({ key = l; flag = On; next = None }) }, ())
  TInt
  TBv(32)
  TPair(TBv(8), TBool)

`[@pp]` is for abstract types, whose printer it is:

  $ cat > bad.knl <<'KN'
  > type cell [@pp "pp_cell"] = { key : int }
  > KN
  $ kanon ocaml out bad.knl
  bad.knl:1:12: [@pp] applies to abstract types
  [1]
