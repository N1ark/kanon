`[@@@traversals]` makes the `ocaml` backend generate the traversals of the terms
and of the sorts, which `[@@@ocaml_types]`' types and the rules need in scope.
The children of a node are the values of type `t` in its arguments: directly, in
a list, an array, an option, a tuple, or in a type of the language (a record, a
variant), left to right.

  $ cat > lang.knl <<'KN'
  > [@@@traversals]
  > use "rules"
  > type var [@ocaml "string"] [@lean "String"]
  > type item = Raw of t | Pair of t * var | Nothing
  > type cell = { key : var; item : item; next : cell option }
  > sort TInt
  > sort TSeq of ty
  > node Int of int : TInt
  > node Var of var
  > node Neg : TInt -> TInt
  > node Seq of t list (vs) : TSeq (Rules.first_ty vs)
  > node Cells of cell : TInt
  > node Lam of var * t
  > KN
  $ cat > rules.kn <<'KN'
  > fn first_ty (vs : t list) : ty = match vs with | [] -> TInt | v :: _ -> type_of v
  > rule neg : Neg v =
  >   | not: Neg x -> x
  > KN

The traversals come after the destructors. A node with a smart constructor
(`Neg`: the rule function `neg`) is rebuilt through it; the others are rebuilt
raw, at the sort that their typing gives from the new children (`Seq`), or, if
they have no typing, at the sort of the term that they replace (`Lam`):

  $ kanon ocaml lang.knl | sed -n '/^let\[@inline\] kanon__rebuild/,/^let as_/p'
  let[@inline] kanon__rebuild_Seq (p1 : (t list)) : t =
      (node (Seq (p1)) (TSeq ((rules_first_ty p1))))
  
  let[@inline] kanon__rebuild_Cells (p1 : cell) : t = (node (Cells (p1)) TInt)
  
  let[@inline] kanon__rebuild_Lam (s : ty) (p1 : var) (p2 : t) : t =
      (node (Lam (p1, p2)) s)
  
  let[@inline] kanon__rebuild_Neg (x1 : t) : t = (rules_neg x1)
  
  let as_int (t : t) =

The generated functions, over the language: each child is mapped in order, and
the types of the language get a function of their own.

  $ kanon ocaml lang.knl | sed -n '/^let rec kanon__map_item/,/^let as_/p'
  let rec kanon__map_item f (x : item) : item =
    match x with
    | Raw (a1) ->
        let y_a1 = f a1 in
        Raw (y_a1)
    | Pair (a1, a2) ->
        let y_a1 = f a1 in
        Pair (y_a1, a2)
    | Nothing ->
        Nothing
  
  and kanon__map_cell f (x : cell) : cell =
    let y_x_item = (kanon__map_item f) x.item in
    let y_x_next = (Option.map (kanon__map_cell f)) x.next in
    { x with item = y_x_item; next = y_x_next }
  
  let rec kanon__iter_item f (x : item) : unit =
    match x with
    | Raw (a1) ->
        f a1
    | Pair (a1, a2) ->
        f a1
    | Nothing ->
        ()
  
  and kanon__iter_cell f (x : cell) : unit =
    (kanon__iter_item f) x.item; (Option.iter (kanon__iter_cell f)) x.next
  
  let rec kanon__exists_item f (x : item) : bool =
    match x with
    | Raw (a1) ->
        f a1
    | Pair (a1, a2) ->
        f a1
    | Nothing ->
        false
  
  and kanon__exists_cell f (x : cell) : bool =
    (kanon__exists_item f) x.item || (function Some x -> (kanon__exists_cell f) x | None -> false) x.next
  
  let map_children (f : t -> t) (v : t) : t =
    match v with
    | { kind = Seq (p1); _ } ->
        let y_p1 = (List.map f) p1 in
        kanon__rebuild_Seq y_p1
    | { kind = Cells (p1); _ } ->
        let y_p1 = (kanon__map_cell f) p1 in
        kanon__rebuild_Cells y_p1
    | { kind = Lam (p1, p2); _ } ->
        let y_p2 = f p2 in
        kanon__rebuild_Lam v.ty p1 y_p2
    | { kind = Op1 (Neg, x1); _ } ->
        let y_x1 = f x1 in
        kanon__rebuild_Neg y_x1
    | _ -> v
  
  let iter_children (f : t -> unit) (v : t) : unit =
    match v with
    | { kind = Seq (p1); _ } ->
        (List.iter f) p1
    | { kind = Cells (p1); _ } ->
        (kanon__iter_cell f) p1
    | { kind = Lam (p1, p2); _ } ->
        f p2
    | { kind = Op1 (Neg, x1); _ } ->
        f x1
    | _ -> ()
  
  let exists_child (f : t -> bool) (v : t) : bool =
    match v with
    | { kind = Seq (p1); _ } ->
        (List.exists f) p1
    | { kind = Cells (p1); _ } ->
        (kanon__exists_cell f) p1
    | { kind = Lam (p1, p2); _ } ->
        f p2
    | { kind = Op1 (Neg, x1); _ } ->
        f x1
    | _ -> false
  
  let for_all_child (f : t -> bool) (v : t) : bool =
    not (exists_child (fun c -> not (f c)) v)
  
  let map_ty_children (f : ty -> ty) (v : ty) : ty =
    match v with
    | TSeq (p1) ->
        let y_p1 = f p1 in
        TSeq (y_p1)
    | _ -> v
  
  let iter_ty_children (f : ty -> unit) (v : ty) : unit =
    match v with
    | TSeq (p1) ->
        f p1
    | _ -> ()
  
  let exists_ty_child (f : ty -> bool) (v : ty) : bool =
    match v with
    | TSeq (p1) ->
        f p1
    | _ -> false
  
  let for_all_ty_child (f : ty -> bool) (v : ty) : bool =
    not (exists_ty_child (fun c -> not (f c)) v)
  
  

The sorts have children too:

  $ kanon ocaml lang.knl | sed -n '/^let map_ty_children/,/^let iter_ty/p'
  let map_ty_children (f : ty -> ty) (v : ty) : ty =
    match v with
    | TSeq (p1) ->
        let y_p1 = f p1 in
        TSeq (y_p1)
    | _ -> v
  
  let iter_ty_children (f : ty -> unit) (v : ty) : unit =

A language without the attribute has none of this:

  $ grep -v traversals lang.knl > plain.knl
  $ kanon ocaml plain.knl | grep -c "children"
  0
  [1]

A node that cannot be rebuilt, because its typing does not give its sort from its
arguments, is an error at the node:

  $ cat > bad.knl <<'KN'
  > [@@@traversals]
  > sort TTuple of ty list
  > node Tuple of t list : TTuple tys
  > KN
  $ echo > none.kn
  $ kanon ocaml bad.knl none.kn
  bad.knl:3:5: traversals: the node Tuple cannot be rebuilt: Tuple: the sort of its result is not determined; build it at a sort, (Tuple ... : S args)
  [1]
