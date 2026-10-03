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
  | TSty -> pf ft "raw_ty"
  | TTuple l -> pf ft "(%a)" (list ~sep:" * " value_ty) l
  | TOption t -> pf ft "(%a option)" value_ty t
  | TList t -> pf ft "(%a list)" value_ty t
  | TApp (n, [ t ]) -> pf ft "(%a %s)" value_ty t n
  | TApp (n, l) -> pf ft "((%a) %s)" (list ~sep:", " value_ty) l n
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

(** The outermost node of the spec of a rule function, with its parameters and
    its operands: the operator, or the leaf. A spec that is not a node (a call
    of a function) has none. *)
let spec_head (f : fn) =
  match Option.map (fun (e : expr) -> e.e) f.spec with
  | Some
      (ENode
         ({ e = EConstr (_, { e = EConstr (o, pargs); _ } :: operands); _ }, _))
    ->
      Some (o, pargs, operands)
  | Some (ENode ({ e = EConstr (k, pargs); _ }, _)) -> Some (k, pargs, [])
  | _ -> None

(** The index of [x] in [l], if [x] is one of its variables. *)
let index_of_var x l =
  let rec go i = function
    | [] -> None
    | ({ e = EVar y; _ } : expr) :: _ when y = x -> Some i
    | _ :: rest -> go (i + 1) rest
  in
  go 0 l

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

(** The ghost tag types that [text] mentions: the names in it that are not a
    constructor, a type variable or a qualified name. *)
let mentions text =
  let n = String.length text in
  let is_id c =
    (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9')
    || c = '_'
    || c = '\''
  in
  let rec go i acc =
    if i >= n then acc
    else if is_id text.[i] then (
      let j = ref i in
      while !j < n && is_id text.[!j] do
        incr j
      done;
      let word = String.sub text i (!j - i) in
      let prev = if i = 0 then ' ' else text.[i - 1] in
      let acc =
        if prev = '`' || prev = '.' || word.[0] = '\'' then acc else word :: acc
      in
      go !j acc)
    else go (i + 1) acc
  in
  go 0 []

(** The declarations of the ghost tag types, in the order of their declaration
    except that a type comes after those that it mentions (a type that mentions
    itself, as [any sseq] in [any], is fine). Types that mention each other are
    an error. *)
let ordered_tags () =
  let decls =
    List.map (fun (d, text) -> (fst (tag_decl d), (d, text))) !lang.ghost_tags
  in
  let deps (name, (_, text)) =
    let words = mentions text in
    List.filter (fun m -> m <> name && List.mem m words) (List.map fst decls)
  in
  let out = ref [] in
  let rec visit path ((name, decl) as d) =
    if not (List.mem_assoc name !out) then (
      if List.mem name path then
        raise
          (Check.Error
             ( List.assoc (fst decl) !lang.ghost_locs,
               Fmt.str "ghost tag types are defined in terms of each other: %s"
                 (String.concat " -> " (List.rev (name :: path))) ));
      List.iter (fun m -> visit (name :: path) (m, List.assoc m decls)) (deps d);
      out := !out @ [ (name, decl) ])
  in
  List.iter (visit []) decls;
  List.map snd !out

let program ~sources ft (p : program) =
  let tags = ordered_tags () in
  let node_typing (c : constr) = List.assoc_opt c.c_name !Check.node_typings in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  Option.iter (pf ft "open %s@ @ ") !lang.ocaml_types;
  pf ft "@[<v 2>module type S = sig@ (** {2 Ghost tags} *)";
  let item text = pf ft "@ @ %s" text in
  pf ft "@ @ @[<v 2>module T : sig";
  List.iter (fun (n, def) -> pf ft "@ type %s = %s" n def) tags;
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
      if f.spec <> None then (
        emitted := f.name :: !emitted;
        let head = spec_head f in
        let is_operand (_, t) = t = TTerm || t = TList TTerm in
        let operand_params = List.filter is_operand f.params in
        let ops, res =
          match f.fghost with
          | Some tags ->
              let tags = List.map tag_of_annotation tags in
              let n = List.length tags in
              (List.filteri (fun i _ -> i < n - 1) tags, List.nth tags (n - 1))
          | None -> (
              match head with
              | None -> (List.map (fun _ -> Unknown) operand_params, Unknown)
              | Some (c, _, operands) ->
                  let ops, res = node_tags ~loc:f.floc c (node_typing c) in
                  let op i =
                    Option.value (List.nth_opt ops i) ~default:Unknown
                  in
                  let op i =
                    (* the operands of an n-ary node have one tag *)
                    match node_typing c with
                    | Some t when t.t_nary -> op 0
                    | _ -> op i
                  in
                  ( List.map
                      (fun (x, _) ->
                        match index_of_var x operands with
                        | Some i -> op i
                        | None -> Unknown)
                      operand_params,
                    res ))
        in
        let operands =
          List.map
            (fun (_, t) -> if t = TTerm then `One else `List)
            operand_params
        in
        (* a [nat] parameter of the node is an [int], and an [int] a [Z.t] *)
        let param (x, t) =
          let small =
            match head with
            | Some (c, pargs, _) -> (
                match index_of_var x pargs with
                | Some i -> List.nth_opt c.c_args i = Some Small
                | None -> false)
            | None -> false
          in
          if small then fun ft -> arg_ty ft Small else fun ft -> value_ty ft t
        in
        let params =
          List.map param (List.filter (fun p -> not (is_operand p)) f.params)
        in
        let doc =
          (* the doc of the node, if the rule is its smart constructor *)
          match (f.fdoc, head) with
          | None, Some (c, pargs, operands)
            when List.map (fun (a : expr) -> a.e) (pargs @ operands)
                 = List.map (fun (x, _) -> EVar x) f.params ->
              c.c_doc
          | doc, _ -> doc
        in
        smart ft ~doc ~name:f.name params ~operands (ops, res)))
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
