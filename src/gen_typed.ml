(** The [ocaml-typed] backend: the OCaml interface of the smart constructors of
    a language, where terms are typed by ghost tags: [module type S] has
    [[< tag ] t] operands and [[> tag ] t] results. The tag of a term is that of
    its sort, which Kanon generates (see {!tag_types}): the tag of a subsort is
    a refinement of the tag of its parent. [Ghost] implements the phantom types
    of [S]: its escape hatches are the identity. The rest of [S] is the rules,
    and the leaf nodes and sorts, whose implementation is written by hand. The
    refinements are trusted: nothing proves them. *)

open Syntax

let pf = Format.fprintf
let list = Gen_ocaml.list

(** The ghost tag of a term (or of a sort): the tag type of its sort or of its
    subsort, a sort variable, or none that Kanon knows, for which any term does.
*)
type tag = Tag of string | Var of string | Unknown

(** The name of the tag type of the sort or subsort [c]: its name in lowercase.
*)
let tag_name c = String.lowercase_ascii c

(** The tag of the sort [s] of a typing, written as the subsort [sub]: the tag
    of the subsort, else that of its head constructor, or a sort variable of
    [vars]. *)
let tag_of_sort vars (s : expr) sub =
  match (sub, s.e) with
  | Some ss, _ -> Tag (tag_name ss)
  | None, EVar x when List.mem_assoc x vars -> Var x
  | None, EConstr (c, _) -> Tag (tag_name c.c_name)
  | None, _ -> Unknown

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

(** The tags of the operands and of the result of the node [c], from its typing,
    if it has one. A node has [Some n] operands, [None] when it is n-ary, with
    one tag for all. *)
let node_tags (typing : typing option) =
  match typing with
  | None -> ([], Unknown)
  | Some t ->
      let tags = List.map2 (tag_of_sort t.t_vars) t.t_sorts t.t_subs in
      let ops = List.filteri (fun i _ -> i < List.length tags - 1) tags in
      (ops, List.nth tags (List.length tags - 1))

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
    are plain, or sorts of any tag. *)
let sort_val ft (c : constr) =
  let args =
    List.map
      (fun a ft -> match a with Arg TSty -> pf ft "_ ty" | a -> arg_ty ft a)
      c.c_args
  in
  val_ ft ~doc:c.c_doc (sort_val_name c) args (fun ft ->
      term ~operand:false ~t:"ty" ft (Tag (tag_name c.c_name)))

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

(** The tag types of the sorts, in the module [Tag]: one for each subsort, the
    variant of its name, and one for each sort, the variant of its name and the
    tag types of its subsorts, which come first. Two sorts whose names differ by
    their case have the same tag type: an error. *)
let tag_types () =
  let sorts = List.filter (fun (c : constr) -> c.c_res = TSty) !lang.constrs in
  let names =
    List.map (fun (c : constr) -> c.c_name) sorts
    @ List.map (fun (s : subsort) -> s.ss_name) !lang.subsorts
  in
  let rec check = function
    | [] -> ()
    | n :: rest -> (
        match List.find_opt (fun m -> tag_name m = tag_name n) rest with
        | Some m ->
            raise
              (Check.Error
                 ( Location.none,
                   Fmt.str "%s and %s have the same tag type, %s" n m
                     (tag_name n) ))
        | None -> check rest)
  in
  check names;
  List.concat_map
    (fun (c : constr) ->
      let subs =
        List.filter (fun (s : subsort) -> s.ss_parent = c.c_name) !lang.subsorts
      in
      List.map
        (fun (s : subsort) -> (tag_name s.ss_name, [ Fmt.str "`%s" s.ss_name ]))
        subs
      @ [
          ( tag_name c.c_name,
            Fmt.str "`%s" c.c_name
            :: List.map (fun s -> tag_name s.ss_name) subs );
        ])
    sorts

(** The destructors of the node or sort [c] in the signature: the arguments of
    the terms that [c] builds (see {!Gen_ocaml.destructor}), where its operands
    have the tags of its typing, and the test. *)
let destructor ft (c : constr) typing =
  let suffix = Gen_ocaml.destructor_suffix c in
  let ty = if c.c_res = TSty then "ty" else "t" in
  let params = List.map (fun a ft -> arg_ty ft a) c.c_args in
  let operands =
    match (c.c_res, typing) with
    | TSty, _ | _, None -> []
    | _, Some (t : typing) ->
        let ops, _ = node_tags typing in
        let n = List.length t.t_sorts - 1 in
        if t.t_nary then
          [
            (fun ft ->
              pf ft "%a list" (term ~operand:false ~t:"t") (List.hd ops));
          ]
        else
          List.init n (fun i ft ->
              term ~operand:false ~t:"t" ft (List.nth ops i))
  in
  let tuple =
    match params @ operands with
    | [] -> fun ft -> pf ft "unit"
    | [ x ] -> x
    | l ->
        fun ft ->
          pf ft "(%a)"
            (Format.pp_print_list
               ~pp_sep:(fun ft () -> pf ft " * ")
               (fun ft pp -> pp ft))
            l
  in
  let input ft = pf ft "_ %s" ty in
  val_ ft ~doc:None ("as_" ^ suffix) [ input ] (fun ft ->
      pf ft "%t option" tuple);
  val_ ft ~doc:None ("is_" ^ suffix) [ input ] (fun ft -> pf ft "bool")

(** The implementation of the phantom types of [S], and of what follows from
    them: the terms and sorts are those of the language, whatever their tags, so
    that the escape hatches are the identity (and need no [Obj.magic]: the types
    are equal, and [S] hides it). The sorts are made by their constructors. *)
let ghost ft () =
  pf ft "@ @ %a@ " Gen_ocaml.ocaml_doc
    "The phantom types of [S], over the types of the language, with the escape \
     hatches, which are the identity, and the sorts: [module Typed : S = \
     struct include Ghost include Rules ... end] only needs what is not \
     generated, such as the leaf nodes.";
  pf ft "@[<v 2>module Ghost = struct";
  pf ft "@ type raw = t@ type raw_ty = ty@ type nonrec 'a t = raw@ ";
  pf ft "type nonrec 'a ty = raw_ty@ @ ";
  pf ft "let untyped : 'a t -> raw = Fun.id@ ";
  pf ft "let type_ : raw -> 'a t = Fun.id@ ";
  pf ft "let cast : 'a t -> 'b t = Fun.id@ ";
  pf ft "let untype_type : 'a ty -> raw_ty = Fun.id@ ";
  pf ft "let type_type : raw_ty -> 'a ty = Fun.id";
  List.iter
    (fun (c : constr) ->
      if c.c_res = TSty then
        let vars = List.mapi (fun i _ -> Fmt.str "a%d" (i + 1)) c.c_args in
        let ctor =
          match vars with
          | [] -> c.c_name
          | l -> Fmt.str "%s (%s)" c.c_name (String.concat ", " l)
        in
        pf ft "@ let %s %s= %s" (sort_val_name c)
          (String.concat "" (List.map (fun x -> x ^ " ") vars))
          ctor)
    !lang.constrs;
  pf ft "@]@ end"

let program ~sources ft (p : program) =
  Gen_ocaml.check_destructors p;
  let tags = tag_types () in
  let node_typing (c : constr) = List.assoc_opt c.c_name !Check.node_typings in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  Option.iter (pf ft "open %s@ @ ") !lang.ocaml_types;
  pf ft
    "(** The ghost tag types of the sorts: a sort that has subsorts has their \
     variants too, which a term of the sort may be. *)@ ";
  pf ft "@[<v 2>module Tag = struct";
  List.iter
    (fun (n, variants) ->
      pf ft "@ type %s = [ %s ]" n (String.concat " | " variants))
    tags;
  pf ft "@]@ end@ @ ";
  pf ft "@[<v 2>module type S = sig@ open Tag";
  let item text = pf ft "@ @ %s" text in
  item "(** {2 Types} *)";
  item
    "(** The untyped terms and sorts, of the types of the language. *)\n\
    \  type raw = t\n\
    \  type raw_ty = ty";
  item
    "(** A sort of terms, phantom-typed by the tag of its terms. *)\n\
    \  type +'a ty";
  item "(** A term, phantom-typed by its tag. *)\n  type +'a t";
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
        let head = Check.spec_head f in
        let is_operand (_, t) = t = TTerm || t = TList TTerm in
        let operand_params = List.filter is_operand f.params in
        let ops, res =
          match head with
          | None -> (List.map (fun _ -> Unknown) operand_params, Unknown)
          | Some (c, _, operands) ->
              let ops, res = node_tags (node_typing c) in
              let op i = Option.value (List.nth_opt ops i) ~default:Unknown in
              let op i =
                (* the operands of an n-ary node have one tag *)
                match node_typing c with
                | Some t when t.t_nary -> op 0
                | _ -> op i
              in
              ( List.map
                  (fun (x, _) ->
                    match Check.index_of_var x operands with
                    | Some i -> op i
                    | None -> Unknown)
                  operand_params,
                res )
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
                match Check.index_of_var x pargs with
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
          smart ft ~doc:c.c_doc ~name params ~operands (node_tags typing)
      | _ -> ())
    !lang.node_ctors;
  item "(** {2 Destructors} *)";
  last_doc := true;
  List.iter (fun c -> destructor ft c (node_typing c)) (Gen_ocaml.destructed ());
  pf ft "@]@ end";
  ghost ft ();
  pf ft "@]@."
