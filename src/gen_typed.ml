(** The [ocaml-typed] backend: the typed interface of the smart constructors of
    a language. A term [ 'a t ] has a phantom parameter, a polymorphic variant
    (a tag) that says what is known of the term: [module type S] has
    [[< tag ] t] operands and [[> tag ] t] results. The tag of a term is that of
    its sort, which Kanon generates (see {!tag_types}): the tag of a subsort is
    a refinement of the tag of its parent. [S] is organised like the language,
    one module per Kanon module (per file). [Derived] is the implementation of
    [S]: the rules, whose types are those of [S] but for the phantom parameter,
    which [S] hides; what it does not have are the leaf nodes ([[@ctor]]),
    written by hand. The refinements are trusted: nothing proves them. *)

open Syntax

let pf = Format.fprintf
let list = Gen_ocaml.list

(** The tag of a term (or of a sort): the tag type of its sort or of its
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

(** The type of a term with the tag [tag]: [[< Tag.tag ] t] for an operand, and
    [[> Tag.tag ] t] for a result, over the type [t] ([ty] for a sort). *)
let term ~operand ~t ft = function
  | Tag s -> pf ft "[%s Tag.%s ] %s" (if operand then "<" else ">") s t
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
  | TArray t -> pf ft "(%a Iarray.t)" value_ty t
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

(** The argument of a constructor of the types, as the destructors return it: a
    [nat] is an [int]. *)
let arg_ty ft = function Small -> pf ft "int" | Arg t -> value_ty ft t

(** An item of the interface: [val name : sig_], or [let name = impl] in its
    implementation, which the leaf nodes (written by hand) do not have. *)
type item = {
  name : string;
  doc : string option;
  sig_ : Format.formatter -> unit;
  impl : (Format.formatter -> unit) option;
}

let arrow args res ft =
  Format.pp_print_list
    ~pp_sep:(fun ft () -> pf ft " ->@ ")
    (fun ft pp -> pp ft)
    ft (args @ [ res ])

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

(** The item of the sort [c], which makes the sorts of its terms: its arguments
    are those of its constructor, or sorts of any tag. *)
let sort_item (c : constr) =
  let args =
    List.map
      (fun a ft -> match a with Arg TSty -> pf ft "_ ty" | a -> arg_ty ft a)
      c.c_args
  in
  let vars = List.mapi (fun i _ -> Fmt.str "a%d" (i + 1)) c.c_args in
  let ctor =
    match vars with
    | [] -> c.c_name
    | l -> Fmt.str "%s (%s)" c.c_name (String.concat ", " l)
  in
  {
    name = sort_val_name c;
    doc = c.c_doc;
    sig_ =
      arrow args (fun ft ->
          term ~operand:false ~t:"ty" ft (Tag (tag_name c.c_name)));
    impl =
      Some
        (fun ft ->
          if vars = [] then pf ft "%s" ctor
          else
            pf ft "@[<hov 2>fun %s->@ %s@]"
              (String.concat "" (List.map (fun x -> x ^ " ") vars))
              ctor);
  }

(** The item of a smart constructor: the leading parameters, then the operands.
    [params] are the types of its parameters, and [operands] the kinds of its
    operands: [`One] for a term, [`List] for the list of an n-ary node. It is
    the rule function [name] if [impl]. *)
let smart ~doc ~name ~impl params ~(operands : [ `One | `List ] list) (ops, res)
    =
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
  {
    name;
    doc;
    sig_ =
      arrow (params @ operands) (fun ft -> term ~operand:false ~t:"t" ft res);
    impl = (if impl then Some (fun ft -> pf ft "Kanon_rules.%s" name) else None);
  }

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

(** The destructors of the node or sort [c]: the arguments of the terms that [c]
    builds (see {!Gen_ocaml.destructor}), where its operands have the tags of
    its typing, and the test. *)
let destructor_items (c : constr) typing =
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
  let rules name ft = pf ft "Kanon_rules.%s" name in
  [
    {
      name = "as_" ^ suffix;
      doc = None;
      sig_ = arrow [ input ] (fun ft -> pf ft "%t option" tuple);
      impl = Some (rules ("as_" ^ suffix));
    };
    {
      name = "is_" ^ suffix;
      doc = None;
      sig_ = arrow [ input ] (fun ft -> pf ft "bool");
      impl = Some (rules ("is_" ^ suffix));
    };
  ]

(** The OCaml name of the Kanon module of the file of [loc]: the name of the
    file, capitalised, without its extension ([bitvec.kn] and [bitvec.knl] are
    [Bitvec]; [use builtin "bool"] is [Bool]). *)
let module_of (loc : Location.t) =
  let file = loc.loc_start.pos_fname in
  let stem = Filename.remove_extension (Filename.basename file) in
  let stem =
    if String.starts_with ~prefix:"+" stem then
      String.sub stem 1 (String.length stem - 1)
    else stem
  in
  let valid =
    stem <> ""
    && (match stem.[0] with 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false)
    && String.for_all
         (function
           | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
           | _ -> false)
         stem
  in
  if not valid then
    raise
      (Check.Error
         ( loc,
           Fmt.str "%s: the name of a file of a module is an OCaml module name"
             file ));
  let m = String.capitalize_ascii stem in
  if List.mem m [ "Tag"; "S"; "Derived"; "Kanon_rules" ] then
    raise
      (Check.Error
         (loc, Fmt.str "the module %s has the name of a module of ocaml-typed" m));
  m

(** The items of the typed interface, by Kanon module, in order: for each
    module, its sorts, its smart constructors, and its destructors. *)
let modules (p : program) =
  let node_typing (c : constr) = List.assoc_opt c.c_name !Check.node_typings in
  let mods : (string * item list ref) list ref = ref [] in
  let add m it =
    match List.assoc_opt m !mods with
    | Some l -> l := !l @ [ it ]
    | None -> mods := !mods @ [ (m, ref [ it ]) ]
  in
  List.iter
    (fun (c : constr) ->
      if c.c_res = TSty then add (module_of c.c_loc) (sort_item c))
    !lang.constrs;
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
        (* the parameters have the types that the rule function declares *)
        let params =
          List.filter_map
            (fun (_, t) ->
              if t = TTerm || t = TList TTerm then None
              else Some (fun ft -> value_ty ft t))
            f.params
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
        add (module_of f.floc)
          (smart ~doc ~name:f.name ~impl:true params ~operands (ops, res))))
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
          add (module_of c.c_loc)
            (smart ~doc:c.c_doc ~name ~impl:false params ~operands
               (node_tags typing))
      | _ -> ())
    !lang.node_ctors;
  List.iter
    (fun (c : constr) ->
      List.iter (add (module_of c.c_loc)) (destructor_items c (node_typing c)))
    (Gen_ocaml.destructed ());
  List.map (fun (m, l) -> (m, !l)) !mods

(** Prints [items], one per line, with a blank line around those that are
    documented (a comment between two items would be ambiguous). *)
let print_items ft ~(print : Format.formatter -> item -> unit) items =
  let prev_doc = ref false in
  List.iteri
    (fun i it ->
      pf ft "@ ";
      if i > 0 && (it.doc <> None || !prev_doc) then pf ft "@ ";
      prev_doc := it.doc <> None;
      print ft it)
    items

let print_sig ft it =
  pf ft "%a@[<hov 2>val %s :@ %t@]" Gen_ocaml.doc it.doc it.name it.sig_

let print_impl ft it =
  match it.impl with
  | Some impl ->
      pf ft "%a@[<hov 2>let %s =@ %t@]" Gen_ocaml.doc it.doc it.name impl
  | None -> ()

(** The signature [S] and the module [Derived]. *)
let interface ft mods =
  let mod_doc m =
    Fmt.str "The Kanon module %s." (String.uncapitalize_ascii m)
  in
  pf ft "%a@ " Gen_ocaml.ocaml_doc
    "The typed interface of the language, organised like it: a module per \
     Kanon module (per file). A term of type [_ t] has a phantom parameter, \
     one of the tags of [Tag], that says what Kanon knows of the term, and the \
     smart constructors check it at compile time. The tag is not data: a term \
     is the same value as its untyped term, [raw].";
  pf ft "@[<v 2>module type S = sig";
  pf ft "@ %a@ type raw = t@ type raw_ty = ty@ " Gen_ocaml.ocaml_doc
    "The terms and sorts of the types of the language, without tag.";
  pf ft "@ %a@ type +'a t@ @ %a@ type +'a ty@ " Gen_ocaml.ocaml_doc
    "A term, whose phantom parameter is its tag." Gen_ocaml.ocaml_doc
    "A sort of terms of the tag [ 'a ].";
  pf ft "@ %a@ val untyped : 'a t -> raw" Gen_ocaml.ocaml_doc
    "Forgets the tag of a term: the same value.";
  pf ft "@ @ %a@ val type_ : raw -> 'a t" Gen_ocaml.ocaml_doc
    "Trusts the tag of a term: unchecked.";
  pf ft "@ @ %a@ val cast : 'a t -> 'b t" Gen_ocaml.ocaml_doc
    "Changes the tag of a term: unchecked.";
  pf ft "@ @ %a@ val untype_type : 'a ty -> raw_ty" Gen_ocaml.ocaml_doc
    "Forgets the tag of a sort.";
  pf ft "@ @ %a@ val type_type : raw_ty -> 'a ty" Gen_ocaml.ocaml_doc
    "Trusts the tag of a sort: unchecked.";
  List.iter
    (fun (m, items) ->
      pf ft "@ @ %a@ @[<v 2>module %s : sig" Gen_ocaml.ocaml_doc (mod_doc m) m;
      print_items ft ~print:print_sig items;
      pf ft "@]@ end")
    mods;
  pf ft "@]@ end@ @ ";
  pf ft "%a@ " Gen_ocaml.ocaml_doc
    "The implementation of [S], from the rules, with the types of [S] visible: \
     [type 'a t = raw]. [S] hides it, since a visible equality would make \
     every tag the same type. What it does not define are the leaf nodes, \
     written by hand: [module Typed : S = struct include Derived ... end].";
  pf ft "@[<v 2>module Derived = struct";
  pf ft "@ module Kanon_rules = %s" (Option.get !lang.ocaml_rules);
  pf ft "@ type raw = t@ type raw_ty = ty@ type nonrec 'a t = raw@ ";
  pf ft "type nonrec 'a ty = raw_ty@ @ ";
  pf ft "let[@inline] untyped (x : 'a t) : raw = x@ ";
  pf ft "let[@inline] type_ (x : raw) : 'a t = x@ ";
  pf ft "let[@inline] cast (x : 'a t) : 'b t = x@ ";
  pf ft "let[@inline] untype_type (x : 'a ty) : raw_ty = x@ ";
  pf ft "let[@inline] type_type (x : raw_ty) : 'a ty = x";
  List.iter
    (fun (m, items) ->
      pf ft "@ @ @[<v 2>module %s = struct" m;
      print_items ft ~print:print_impl
        (List.filter (fun it -> it.impl <> None) items);
      pf ft "@]@ end")
    mods;
  pf ft "@]@ end"

let program ~sources ft (p : program) =
  Gen_ocaml.check_destructors p;
  if !lang.ocaml_rules = None then
    raise
      (Check.Error
         ( Location.none,
           "ocaml-typed: [@@@ocaml_rules \"M\"], in the declaration of the \
            language, names the OCaml module of the rules (the output of kanon \
            ocaml), which the implementation is made of" ));
  let tags = tag_types () in
  let mods = modules p in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  Option.iter (pf ft "open %s@ @ ") !lang.ocaml_types;
  pf ft
    "(** The tags of the terms, one polymorphic variant type per sort and per \
     subsort, with the sort in lowercase as its name. A sort that has subsorts \
     has their variants too, which a term of the sort may be. The types may be \
     joined, in a group of tags of the user: [type scalar = [ Tag.tbitvec | \
     Tag.tfloat ]]. *)@ ";
  pf ft "@[<v 2>module Tag = struct";
  List.iter
    (fun (n, variants) ->
      pf ft "@ type %s = [ %s ]" n (String.concat " | " variants))
    tags;
  pf ft "@]@ end@ @ ";
  interface ft mods;
  pf ft "@]@."
