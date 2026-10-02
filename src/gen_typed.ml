(** The [ocaml-typed] backend: the OCaml interface of the smart constructors of
    a language, where terms are typed by ghost tags: [module type S] has
    [[< tag ] t] operands and [[> tag ] t] results, whose tags come from the
    sorts of the typing of each node ([[@ghost]] on a sort), or from its own
    annotation ([[@ghost "t1" ... "tn"]] on a node, which refines them). The
    implementation of [S] is written by hand, and checked by OCaml against it.
    The refinements are trusted: nothing proves them. *)

open Syntax

let pf = Format.fprintf
let list = Gen_ocaml.list

(** The ghost tag of a term (or of a sort): a polymorphic variant type, by its
    text (["sint"], ["sint sseq"]), a sort variable, or none that Kanon knows,
    for which any term does. *)
type tag = Tag of string | Var of string | Unknown

(** The bare name of the tag type declared as [decl] (["'a sseq"]: [sseq]), and
    its number of parameters. *)
let tag_decl decl =
  let words = String.split_on_char ' ' decl in
  let name = List.nth words (List.length words - 1) in
  let vars =
    List.length (List.filter (fun w -> String.contains w '\'') words)
  in
  (name, vars)

(** The number of parameters of the ghost tag type [name], if it is declared. *)
let tag_arity name =
  List.find_map
    (fun (d, _) ->
      let n, k = tag_decl d in
      if n = name then Some k else None)
    !lang.ghost_tags

(** The tag of the sort [s] of a typing: the ghost of its head constructor,
    applied to the tags of the sorts that are its arguments if the tag type has
    parameters; a sort variable of [vars] is itself. *)
let rec tag_of_sort vars (s : expr) =
  match s.e with
  | EVar x when List.mem_assoc x vars -> Var x
  | EConstr (c, args) -> (
      match List.assoc_opt c.c_name !lang.sort_ghosts with
      | None -> Unknown
      | Some g -> (
          let g, _ = tag_decl g in
          match tag_arity g with
          | None | Some 0 -> Tag g
          | Some k ->
              let inner =
                List.concat
                  (List.map2
                     (fun a e ->
                       match a with
                       | Arg TSty -> (
                           match tag_of_sort vars e with
                           | Tag t -> [ t ]
                           | Var x -> [ "'" ^ x ]
                           | Unknown -> [ "_" ])
                       | _ -> [])
                     c.c_args args)
              in
              let inner = List.filteri (fun i _ -> i < k) inner in
              let inner =
                inner @ List.init (k - List.length inner) (fun _ -> "_")
              in
              Tag
                (match inner with
                | [ a ] -> Fmt.str "%s %s" a g
                | l -> Fmt.str "(%s) %s" (String.concat ", " l) g)))
  | _ -> Unknown

(** The tag of an annotation of a node: a type variable, or a tag type. *)
let tag_of_annotation s =
  if String.length s > 0 && s.[0] = '\'' && not (String.contains s ' ') then
    Var (String.sub s 1 (String.length s - 1))
  else Tag s

(** The type of a term with the tag [tag]: [[< tag ] t] for an operand, and
    [[> tag ] t] for a result, over the type [t] ([ty] for a sort). *)
let term ~operand ~t ft = function
  | Tag s -> pf ft "[%s %s ] %s" (if operand then "<" else ">") s t
  | Var x -> pf ft "'%s %s" x t
  | Unknown -> pf ft "_ %s" t

(** The OCaml type of a value that is not a term, in the signature, where a term
    nested in it has any tag. *)
let rec value_ty ft = function
  | TTerm -> pf ft "_ t"
  | TTuple l -> pf ft "(%a)" (list ~sep:" * " value_ty) l
  | TOption t -> pf ft "(%a option)" value_ty t
  | TList t -> pf ft "(%a list)" value_ty t
  | t -> Gen_ocaml.ocaml_ty ft t

(** The tags of the operands and of the result of the node [c], whose typing is
    [typing], if it has one. A node has [Some n] operands, [None] when it is
    n-ary, with one tag for all. *)
let node_tags ~loc (c : constr) (typing : typing option) =
  let from_typing () =
    match typing with
    | None -> ([], Unknown)
    | Some t ->
        let tags = List.map (tag_of_sort t.t_vars) t.t_sorts in
        let ops = List.filteri (fun i _ -> i < List.length tags - 1) tags in
        (ops, List.nth tags (List.length tags - 1))
  in
  match List.assoc_opt c.c_name !lang.node_ghosts with
  | Some tags ->
      let tags = List.map tag_of_annotation tags in
      let n = List.length tags in
      let expected =
        match typing with
        | None -> None
        | Some t -> Some (List.length t.t_sorts)
      in
      if expected <> None && expected <> Some n then
        raise
          (Check.Error
             ( loc,
               Fmt.str "%s: [@@ghost] has %d tags, but the typing of %s has %d"
                 c.c_name n c.c_name (Option.get expected) ));
      (List.filteri (fun i _ -> i < n - 1) tags, List.nth tags (n - 1))
  | None -> from_typing ()

(** The parameters of a node, as plain arguments. *)
let arg_ty ft = function Small -> pf ft "int" | Arg t -> value_ty ft t

(** One declaration [val name : args -> res], preceded by its doc. *)
let last_doc = ref false

let val_ ft ~doc name args res =
  (* a comment between two items would be ambiguous: documented items are set
     apart by blank lines *)
  pf ft "@ ";
  if doc <> None || !last_doc then pf ft "@ ";
  last_doc := doc <> None;
  pf ft "%a@[<hov 2>val %s :@ %a@]" Gen_ocaml.doc doc name
    (Format.pp_print_list
       ~pp_sep:(fun ft () -> pf ft " ->@ ")
       (fun ft pp -> pp ft))
    (args @ [ res ])

(** The node of the spec of a rule function: the operator, or the leaf. *)
let spec_node (f : fn) =
  match Option.map (fun (e : expr) -> e.e) f.spec with
  | Some (ENode ({ e = EConstr (_, { e = EConstr (o, _); _ } :: _); _ }, _)) ->
      Some o
  | Some (ENode ({ e = EConstr (k, _); _ }, _)) -> Some k
  | _ -> None

let sort_val_name (c : constr) =
  let n = c.c_name in
  let n =
    if
      String.length n > 1
      && n.[0] = 'T'
      && Char.equal n.[1] (Char.uppercase_ascii n.[1])
      && n.[1] <> '_'
    then String.sub n 1 (String.length n - 1)
    else n
  in
  "t_" ^ String.lowercase_ascii n

(** The [val] of the sort [c], which makes the sorts of its terms: its arguments
    are plain, or the sorts that its tag type is over. *)
let sort_val ft (c : constr) =
  let g =
    Option.map
      (fun g -> fst (tag_decl g))
      (List.assoc_opt c.c_name !lang.sort_ghosts)
  in
  let vars = Option.bind g tag_arity |> Option.value ~default:0 in
  let names = [ "a"; "b"; "c"; "d" ] in
  let nth i =
    if i < List.length names then List.nth names i else Fmt.str "a%d" i
  in
  let next = ref 0 in
  let args =
    List.map
      (fun a ft ->
        match a with
        | Arg TSty ->
            if !next < vars then (
              let x = nth !next in
              incr next;
              pf ft "'%s ty" x)
            else pf ft "_ ty"
        | a -> arg_ty ft a)
      c.c_args
  in
  let tag =
    match g with
    | None -> Unknown
    | Some g -> (
        match vars with
        | 0 -> Tag g
        | 1 -> Tag ("'a " ^ g)
        | k ->
            Tag
              (Fmt.str "(%s) %s"
                 (String.concat ", " (List.init k (fun i -> "'" ^ nth i)))
                 g))
  in
  val_ ft ~doc:c.c_doc (sort_val_name c) args (fun ft ->
      term ~operand:false ~t:"ty" ft tag)

(** The [val] of a smart constructor: the leading parameters, then the operands.
    [params] are the types of its parameters, and [operands] the kinds of its
    operands: [`One] for a term, [`List] for the list of an n-ary node. *)
let smart ft ~doc ~name params ~(operands : [ `One | `List ] list) (ops, res) =
  let ops_tags = ref ops in
  let next () =
    match !ops_tags with
    | t :: rest ->
        ops_tags := rest;
        t
    | [] -> Unknown
  in
  let nary = List.exists (fun o -> o = `List) operands in
  let operands =
    List.map
      (fun o ft ->
        let tag =
          if nary then match ops with t :: _ -> t | [] -> Unknown else next ()
        in
        match o with
        | `One -> term ~operand:true ~t:"t" ft tag
        | `List -> pf ft "%a list" (term ~operand:true ~t:"t") tag)
      operands
  in
  val_ ft ~doc name (params @ operands) (fun ft ->
      term ~operand:false ~t:"t" ft res)

let program ~sources ft (p : program) =
  let node_typing (c : constr) = List.assoc_opt c.c_name !Check.node_typings in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  Option.iter (pf ft "open %s@ @ ") !lang.ocaml_types;
  pf ft "@[<v 2>module type S = sig@ (** {2 Ghost tags} *)";
  let item text = pf ft "@ @ %s" text in
  pf ft "@ @ @[<v 2>module T : sig";
  List.iter (fun (n, def) -> pf ft "@ type %s = %s" n def) !lang.ghost_tags;
  pf ft "@]@ end@ @ open T";
  item "(** {2 Types} *)";
  item
    "(** A sort of terms, phantom-typed by the tag of its terms. *)\n\
    \  type +'a ty";
  item "(** A term, phantom-typed by its tag. *)\n  type +'a t";
  item
    "(** The untyped terms and sorts: instantiated with [with type raw = ...]. \
     *)\n\
    \  type raw\n\
    \  type raw_ty";
  item "(** {2 Escape hatches} *)";
  item "(** Forgets the tag of a term. *)\n  val untyped : 'a t -> raw";
  item
    "(** Trusts the tag of a term: its type is not checked. *)\n\
    \  val type_ : raw -> 'a t";
  item "(** Changes the tag of a term: unchecked. *)\n  val cast : 'a t -> 'b t";
  item "(** Forgets the tag of a sort. *)\n  val untype_type : 'a ty -> raw_ty";
  item
    "(** Trusts the tag of a sort: unchecked. *)\n\
    \  val type_type : raw_ty -> 'a ty";
  item "(** {2 Sorts} *)";
  last_doc := true;
  List.iter
    (fun (c : constr) -> if c.c_res = TSty then sort_val ft c)
    !lang.constrs;
  item "(** {2 Smart constructors} *)";
  last_doc := true;
  let emitted = ref [] in
  List.iter
    (fun (f : fn) ->
      match spec_node f with
      | None -> ()
      | Some c ->
          emitted := f.name :: !emitted;
          let tags = node_tags ~loc:f.floc c (node_typing c) in
          let operands =
            List.filter_map
              (fun (_, t) ->
                match t with
                | TTerm -> Some `One
                | TList TTerm -> Some `List
                | _ -> None)
              f.params
          in
          let params =
            List.filter_map
              (fun (_, t) ->
                match t with
                | TTerm | TList TTerm -> None
                | t -> Some (fun ft -> value_ty ft t))
              f.params
          in
          smart ft
            ~doc:(if f.fdoc <> None then f.fdoc else c.c_doc)
            ~name:f.name params ~operands tags)
    p.fns;
  List.iter
    (fun (node, name) ->
      match find_constr node with
      | Some c when not (List.mem name !emitted) ->
          let typing = node_typing c in
          let params = List.map (fun a ft -> arg_ty ft a) c.c_args in
          let operands =
            match typing with
            | Some t when t.t_nary -> [ `List ]
            | Some t -> List.init (List.length t.t_sorts - 1) (fun _ -> `One)
            | None -> []
          in
          smart ft ~doc:c.c_doc ~name params ~operands
            (node_tags ~loc:Location.none c typing)
      | _ -> ())
    !lang.node_ctors;
  pf ft "@]@ end@]@."
