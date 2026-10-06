(** Lean backend.

    Every module (a [.knl] file and its [.kn] file) is modelled and proved once,
    for every language that uses it, under its root [R] ([[@@@lean_root "R"]],
    or else [L.M] for the module [M] of a language of root [L]):

    - [R/Types.lean]: its data types;
    - [R/Node.lean]: its sorts [R.Srt] and its nodes [R.Node T], over the terms
      [T] of a language, with [Node.map], [Node.All] and [Node.Rel];
    - [R/Sem.lean], by hand: the values it needs of a language ([R.Values]),
      the meaning of its nodes ([R.Node.eval]) and its primitives;
    - [R/Lang.lean]: the typing of its nodes ([Node.wt]), and what the module
      needs of a language [S] ([R.Lang S]: its nodes and sorts embedded in the
      terms and types of [S], typed and evaluated as the module says);
    - [R/Prims.lean], by hand: the primitives over terms and sorts, the
      predicates of its subsorts, what its oracles satisfy and what its
      extensible helpers satisfy;
    - [R/Model.lean]: its rule functions, oracles and extensible helpers as the
      record [R.Ops S], its specs, helpers and rules;
    - [R/Statements.lean]: the statements of its arms, and the lifting lemmas;
    - [R/Proofs.lean], by hand: the proofs that the tactics do not find;
    - [R/Soundness.lean]: the proofs of its arms and of its rules.

    A language of root [L] ties the knot: [L/Syntax.lean] (its sorts [Ty] and
    terms [Term], a case per module), [L/Val.lean] (by hand: its values and
    the instances of the [Values] of its modules), [L/Semantics.lean] (typing,
    evaluation, and the instances of the [Lang] of its modules, by [rfl]) and
    [L/Rules.lean] (its rule functions, from the rules of every module, and
    the proof that they are sound). *)

open Syntax

let pf = Format.fprintf

let list ?(sep = ", ") pp ft l =
  Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "%s" sep) pp ft l

let keywords =
  [
    "by";
    "at";
    "fun";
    "from";
    "have";
    "show";
    "let";
    "if";
    "then";
    "else";
    "do";
    "match";
    "with";
    "in";
    "end";
    "open";
    "theorem";
    "def";
    "where";
    "deriving";
    "instance";
    "structure";
    "class";
    "example";
    "calc";
    "mut";
    "return";
    "for";
    "unless";
    "import";
    "section";
    "namespace";
    "variable";
    "universe";
    "private";
    "protected";
    "partial";
    "noncomputable";
    "mutual";
    "inductive";
    "extends";
    "abbrev";
    "macro";
    "syntax";
    "notation";
    "local";
    "attribute";
    "Type";
    "Prop";
    "Sort";
    "obtain";
    "using";
    "fin";
  ]

let id x = if List.mem x keywords then "«" ^ x ^ "»" else x

(** The Lean name of a function: its canonical name, [Bitvec.add], which Lean
    reads as the name [add] in the namespace [Bitvec] of its module. *)
let qn n = String.concat "." (List.map id (String.split_on_char '.' n))

(** The name of a field of a structure ([Ops], [Ops.Sound]), which has no dot:
    the flat name, [bitvec_add]. *)
let fld n = id (flat_name n)

(** [text] without what would end or open a (nested) comment in Lean: [-/] and
    [/-] get a space inside. *)
let escape_comment text =
  let replace sub by s =
    let n = String.length sub in
    let b = Buffer.create (String.length s) in
    let rec go i =
      if i < String.length s then
        if i + n <= String.length s && String.sub s i n = sub then (
          Buffer.add_string b by;
          go (i + n))
        else (
          Buffer.add_char b s.[i];
          go (i + 1))
    in
    go 0;
    Buffer.contents b
  in
  text |> replace "-/" "- /" |> replace "/-" "/ -"

(** The documentation comment of an item, if it has one. *)
let doc ft = function
  | None -> ()
  | Some text ->
      pf ft "%a@ "
        (Gen_ocaml.doc_comment ~opening:"/--" ~closing:"-/"
           ~escape:escape_comment)
        text

let uniq l =
  List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [ x ]) [] l

(** What cannot be modelled in Lean: reported at [loc]. *)
let unsupported loc fmt =
  Fmt.kstr
    (fun s -> raise (Check.Error (loc, s ^ ": not supported in Lean")))
    fmt

(* ---------------------------------------------------------------- *)
(* Classification *)

(** A rule function, a helper that the model gives the record [O] of the rule
    functions (as it calls them, an oracle or an extensible helper), a plain
    helper, or an extensible helper ([[@extensible]]), which each language puts
    together from the cases of its modules. *)
type kind = Rule | OHelper | Pure | Ext

type ctx = { prims : prim list; kinds : (string * kind) list; fns : fn list }

let fn_kind ctx f = List.assoc f ctx.kinds
let is_oracle ctx f = List.exists (fun p -> p.pname = f && p.oracle) ctx.prims
let is_prim ctx f = List.exists (fun p -> p.pname = f) ctx.prims

(** The program without its [[@no_lean]] functions and primitives, which Lean
    does not see: nothing that it models calls them (see [Check.program]). *)
let modelled (p : program) =
  {
    p with
    prims = List.filter (fun (q : prim) -> not q.pno_lean) p.prims;
    fns = List.filter (fun (f : fn) -> not f.no_lean) p.fns;
  }

let classify (p : program) =
  let is_oracle f = List.exists (fun q -> q.pname = f && q.oracle) p.prims in
  let kinds =
    ref
      (List.map
         (fun f ->
           ( f.name,
             if Option.is_some f.spec then Rule
             else if f.extensible then Ext
             else Pure ))
         p.fns)
  in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun f ->
        if List.assoc f.name !kinds = Pure then
          let needs_o =
            List.exists
              (fun g ->
                is_oracle g
                ||
                match List.assoc_opt g !kinds with
                | Some (Rule | OHelper | Ext) -> true
                | _ -> false)
              (Gen_ocaml.calls [] f.body)
          in
          if needs_o then (
            kinds := (f.name, OHelper) :: List.remove_assoc f.name !kinds;
            changed := true))
      p.fns
  done;
  { prims = p.prims; kinds = !kinds; fns = p.fns }

(* ---------------------------------------------------------------- *)
(* Modules *)

(** The modules that each module uses, by name, as the command line reads them
    (see {!Loader.load}). *)
let module_uses : (string * string list) list ref = ref []

(** The modules built into kanon: their Lean files are in Kanon's library, and
    the languages that use them do not generate them. *)
let builtin_modules : string list ref = ref []

(** The module of the first file of the command line: the language, whose root
    is that of the model of the language. *)
let root_module : string option ref = ref None

(** The module of an item declared at [loc]. *)
let module_of_loc (loc : Location.t) =
  try Check.module_of_loc loc with Check.Error _ -> None

(** The module of the function, primitive or constant [name]. *)
let module_of_name name = Option.map fst (split_name name)

(** The root of the Lean files of the module [m]: its [[@@@lean_root]], or else
    that of the language (for the language's own module), or that of the
    language and its name. *)
let rec module_root m =
  match List.assoc_opt m !lang.lean_roots with
  | Some r -> r
  | None ->
      if !root_module = None || !root_module = Some m then "Kanon"
      else lang_root () ^ "." ^ m

and lang_root () =
  match !root_module with Some m -> module_root m | None -> "Kanon"

let constr_module (c : constr) =
  match module_of_loc c.c_loc with
  | Some m -> m
  | None -> invalid_arg ("gen_lean: no module for " ^ c.c_name)

let constr_root c = module_root (constr_module c)
let name_root name = module_root (Option.get (module_of_name name))

(** The Lean name of the function [name], from anywhere: [R.Bitvec.add]. *)
let fn_ref name = name_root name ^ "." ^ qn name

(** The Lean name of the primitive [name], from anywhere: [R.add]. *)
let prim_ref name = name_root name ^ "." ^ id (plain_name name)

(** The modules whose nodes, sorts and functions each module refers to, by
    module (see [compute_refs]). *)
let module_refs : (string * string list) list ref = ref []

(** Records the modules that each module refers to in [p]: in its functions, in
    the cases it adds to the functions of others (and those functions), and in
    the typing of its nodes. *)
let compute_refs (p : program) =
  let refs = ref [] in
  let add m d =
    match (m, d) with
    | Some m, Some d when m <> d && not (List.mem (m, d) !refs) ->
        refs := (m, d) :: !refs
    | _ -> ()
  in
  let constr m (c : constr) = add m (module_of_loc c.c_loc) in
  let rec pat m (q : pat) =
    match q.p with
    | PConstr (c, l) ->
        constr m c;
        List.iter (pat m) l
    | PAs (q, _) | PSome q -> pat m q
    | PTuple l -> List.iter (pat m) l
    | PCons (a, b) | POr (a, b) | PComm (a, b) ->
        pat m a;
        pat m b
    | PRecord fs -> List.iter (fun (_, q) -> pat m q) fs
    | _ -> ()
  in
  let rec expr m (e : expr) =
    let go = expr m in
    match e.e with
    | EConstr (c, l) ->
        constr m c;
        List.iter go l
    | ECall (f, l) ->
        add m (module_of_name f);
        List.iter go l
    | ELocalCall (_, l) | ETuple l | EArray l -> List.iter go l
    | ENode (a, b) | EBinop (_, a, b) | ECons (a, b) | EAssert (a, b) ->
        go a;
        go b
    | EUnop (_, a) | ESome a | EField (a, _) -> go a
    | EIf (a, b, c) ->
        go a;
        go b;
        go c
    | ERecord l -> List.iter (fun (_, e) -> go e) l
    | ELet (q, a, b) ->
        pat m q;
        go a;
        go b
    | ELetFun (_, _, a, b) ->
        go a;
        go b
    | EMatch (scruts, cases) ->
        List.iter go scruts;
        List.iter
          (fun (c : case) ->
            let m' =
              match module_of_loc c.cloc with Some m' -> Some m' | None -> m
            in
            (* a case that a module adds to a function of another *)
            if m' <> m then add m' m;
            pat m' c.pat;
            Option.iter (expr m') c.guard;
            expr m' c.body)
          cases
    | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> ()
  in
  List.iter
    (fun (f : fn) ->
      let m = module_of_name f.name in
      Option.iter (expr m) f.spec;
      expr m f.body)
    p.fns;
  List.iter
    (fun (t : typing) ->
      let m = module_of_loc t.t_constr.c_loc in
      List.iter (expr m) t.t_sorts;
      Option.iter (expr m) t.t_when)
    (p.typing @ p.leaf_typing);
  module_refs :=
    List.map
      (fun m ->
        (m, List.filter_map (fun (a, d) -> if a = m then Some d else None) !refs))
      (List.sort_uniq compare (List.map fst !refs))

(** The modules that [m] uses or refers to. *)
let deps m =
  Option.value ~default:[] (List.assoc_opt m !module_uses)
  @ Option.value ~default:[] (List.assoc_opt m !module_refs)
  |> List.filter (fun d -> d <> m)
  |> List.sort_uniq compare

(** The modules that [m] uses, directly or not, each after those it uses, and
    [m] last. A module cannot use itself, through others: the Lean files of
    each would import the other's. *)
let closure m =
  let rec go path acc d =
    if List.mem d path then
      let cycle = List.rev (d :: path) in
      let cycle =
        let rec from = function x :: l when x <> d -> from l | l -> l in
        from cycle
      in
      raise
        (Check.Error
           ( Location.none,
             Printf.sprintf "the modules use each other: %s; merge them"
               (String.concat " -> " cycle) ))
    else if List.mem d acc then acc
    else List.fold_left (go (d :: path)) acc (deps d) @ [ d ]
  in
  go [] [] m

(** The modules of the language, each after those it uses. *)
let all_modules () =
  let roots =
    (match !root_module with Some m -> [ m ] | None -> [])
    @ List.map fst !module_uses
  in
  List.fold_left
    (fun acc m -> acc @ List.filter (fun d -> not (List.mem d acc)) (closure m))
    [] roots

let in_module m (loc : Location.t) = module_of_loc loc = Some m

(** A node: its constructor (the kind of a leaf, or an operator), and the types
    of its arguments and of its operands. *)
type gnode = { gc : constr; gpayload : ty list; goperands : ty list }

let gnodes () =
  List.filter_map
    (fun (c : constr) ->
      if c.c_res = TKind && not (List.mem c.c_name !lang.node_kinds) then
        Some { gc = c; gpayload = List.map arg_ty c.c_args; goperands = [] }
      else
        match Check.node_of_op c with
        | Some (_, operands) ->
            Some
              {
                gc = c;
                gpayload = List.map arg_ty c.c_args;
                goperands = operands;
              }
        | None -> None)
    !lang.constrs

let find_gnode (c : constr) =
  List.find (fun n -> n.gc.c_name = c.c_name && n.gc.c_res = c.c_res) (gnodes ())

let module_nodes m = List.filter (fun n -> in_module m n.gc.c_loc) (gnodes ())

let module_sorts m =
  List.filter
    (fun (c : constr) -> c.c_res = TSty && in_module m c.c_loc)
    !lang.constrs

let module_subsorts m =
  List.filter
    (fun ss -> in_module m ss.ss_loc && ss.ss_lean <> None)
    !lang.subsorts

let has_nodes m = module_nodes m <> []
let has_sorts m = module_sorts m <> []

(** Whether [m] has a class [Lang]: whether it has nodes or sorts. *)
let has_lang m = has_nodes m || has_sorts m

(** The modules among [m] and those it uses that have a class [Lang]. *)
let lang_mods m = List.filter has_lang (closure m)

(** Whether the type [t] mentions terms or sorts. *)
let uses_term t = mentions TTerm t || mentions TSty t || mentions TKind t

(** Whether the primitive [q] is over terms or sorts: then it is defined in
    [Prims.lean], after the class [Lang]; else in [Sem.lean], where the typing
    of the nodes may use it. *)
let prim_over_terms (q : prim) = List.exists uses_term (q.pret :: q.pargs)

(* ---------------------------------------------------------------- *)
(* Types *)

(** The Lean name of a type of the language: its Kanon name, CamelCased. *)
let lean_name s =
  String.concat ""
    (List.map String.capitalize_ascii (String.split_on_char '_' s))

(** The types that Kanon generates: those of the kinds, of the sorts, and of
    the operators of each arity. *)
let generated_decl (d : decl) =
  Some d.d_name = decl_name TKind
  || Some d.d_name = decl_name TSty
  || List.exists
       (fun k ->
         match find_constr k with
         | Some { c_args = Arg (TData t) :: _; _ } -> t = d.d_name
         | _ -> false)
       !lang.node_kinds

(** The Lean name of a type: its [[@lean]] name, else its Kanon name,
    CamelCased. *)
let decl_lean_name (d : decl) =
  match d.d_lean with Some n -> n | None -> lean_name d.d_name

let constrs_of (d : decl) =
  List.filter (fun c -> decl_name c.c_res = Some d.d_name) !lang.constrs

let is_abstract (d : decl) = d.d_fields = [] && constrs_of d = []

(** Whether [d] is defined by hand in Lean: an abstract type without a [[@lean]]
    name of an existing type. *)
let by_hand (d : decl) = is_abstract d && d.d_lean = None

let decl_module (d : decl) = module_of_loc d.d_loc

(** The Lean name of the type [d]: qualified by the root of its module, but for
    an existing type that [[@lean]] names. *)
let qual_lean_name (d : decl) =
  match decl_module d with
  | Some m when not (is_abstract d && d.d_lean <> None) ->
      module_root m ^ "." ^ decl_lean_name d
  | _ -> decl_lean_name d

(** How terms and sorts are printed: [S.Term] and [S.Ty] in the files of a
    module, [Term] and [Ty] in those of a language. *)
let term_ty = ref "S.Term"

let sort_ty = ref "S.Ty"

let rec lean_ty ft = function
  | TInt -> pf ft "Int"
  | TBool -> pf ft "Bool"
  | TUnit -> pf ft "Unit"
  | TTerm -> pf ft "%s" !term_ty
  | TSty -> pf ft "%s" !sort_ty
  | TKind -> unsupported Location.none "the type of kinds"
  | TData _ as t -> pf ft "%s" (qual_lean_name (decl_of_ty t))
  | TTuple l -> pf ft "(%a)" (list ~sep:" × " lean_ty) l
  | TOption t -> pf ft "(Option %a)" lean_ty t
  | TList t -> pf ft "(List %a)" lean_ty t
  | TArray t -> pf ft "(Array %a)" lean_ty t

let ty_str t = Fmt.str "%a" lean_ty t

(** Whether [c] is a constructor of a data type (not a sort nor a kind of
    terms). *)
let is_data (c : constr) =
  match c.c_res with
  | TData t -> (
      match find_decl t with Some d -> not (generated_decl d) | None -> false)
  | _ -> false

let lean_constr (c : constr) = Fmt.str "%a.%s" lean_ty c.c_res c.c_name

(** The node constructor [C] applied to [args]: [.C a b]. *)
let ctor_app name args =
  if args = [] then "." ^ name
  else "(." ^ name ^ " " ^ String.concat " " args ^ ")"

let app f args =
  if args = [] then f else "(" ^ String.concat " " (f :: args) ^ ")"

let tuple l =
  match l with [] -> "()" | [ x ] -> x | _ -> "(" ^ String.concat ", " l ^ ")"

(* ---------------------------------------------------------------- *)
(* Printing contexts *)

(** The module whose files are printed: the record [O] of its rule functions
    is its [Ops]. *)
let self : string option ref = ref None

let with_self m k =
  let saved = !self in
  self := Some m;
  Fun.protect ~finally:(fun () -> self := saved) k

(** The modules whose [Ops] the [Ops] of [m] extends: those it uses that have
    a model and that no other of them uses. *)
let has_model_ref : (string -> bool) ref = ref (fun _ -> true)

let ops_parents m =
  let ds = List.filter !has_model_ref (List.filter (( <> ) m) (closure m)) in
  List.filter
    (fun d ->
      not
        (List.exists (fun d' -> d' <> d && List.mem d (closure d')) ds))
    ds

let ops_parent d = "to" ^ d ^ "Ops"
let sound_parent d = "to" ^ d ^ "Sound"

(** The projections from the [Ops] of [m] to those of [d], which it extends:
    [".toNegOps.toNumOps"]; [sound] for those of their [Ops.Sound]. *)
let ops_path ?(sound = false) m d =
  let rec go m =
    if m = d then Some []
    else
      List.find_map
        (fun p ->
          Option.map
            (fun l -> (if sound then sound_parent p else ops_parent p) :: l)
            (go p))
        (ops_parents m)
  in
  match go m with
  | Some l -> String.concat "" (List.map (fun x -> "." ^ x) l)
  | None -> invalid_arg (Printf.sprintf "gen_lean: %s does not extend %s" m d)

(** The record of the rule functions of the module that is printed, as those of
    the module [d]. *)
let o_of d =
  match !self with Some m -> "O" ^ ops_path m d | None -> "O"

(** How the sorts are printed: by the embeddings [sM] of the typing of the
    nodes, or by [R.sort]. *)
let in_typing = ref false

(** The name of the embedding of the sorts of the module [m] in the typing of
    the nodes. *)
let sort_param m = "s" ^ m

(** The sort constructor [c] applied to [args]. *)
let sort_term (c : constr) args =
  if !in_typing then
    Printf.sprintf "(%s %s)" (sort_param (constr_module c)) (ctor_app c.c_name args)
  else Printf.sprintf "(%s.sort %s)" (constr_root c) (ctor_app c.c_name args)

(** The term of the node [c] over [args], at the sort [t]. *)
let node_term (c : constr) args t =
  Printf.sprintf "(%s.mk %s %s)" (constr_root c) (ctor_app c.c_name args) t

(* ---------------------------------------------------------------- *)
(* Patterns *)

let rec pat ft (p : pat) =
  match p.p with
  | PAny -> pf ft "_"
  | PVar x -> pf ft "%s" (id x)
  | PAs (q, x) -> pf ft "%s@%a" (id x) pat q
  | POr _ | PComm _ -> failwith "gen_lean: or-pattern after desugaring"
  | PInt z -> pf ft "(%s : Int)" (Z.to_string z)
  | PBool b -> pf ft "%b" b
  | PUnit -> pf ft "()"
  | PTuple l -> pf ft "(%a)" (list pat) l
  | PSome q -> pf ft "(some %a)" pat q
  | PNone -> pf ft "none"
  | PNil -> pf ft "[]"
  | PCons (h, t) -> pf ft "(%a :: %a)" pat h pat t
  | PRecord fs ->
      let field (f, _) =
        match List.assoc_opt f fs with
        | Some p -> Fmt.str "%a" pat p
        | None -> "_"
      in
      pf ft "⟨%s⟩"
        (String.concat ", " (List.map field (decl_of_ty p.pty).d_fields))
  | PConstr (c, _) when not (is_data c) ->
      unsupported p.ploc "the pattern of %s here" c.c_name
  | PConstr (c, args) -> (
      match args with
      | [] -> pf ft "%s" (lean_constr c)
      | _ -> pf ft "(%s %a)" (lean_constr c) (list ~sep:" " pat) args)

(** A node pattern [p] (of a term): its node, and the patterns of its arguments
    and operands; or a pattern of a sort, and those of its arguments. *)
let node_pat (p : pat) =
  match p.p with
  | PConstr (k, args) when p.pty = TTerm ->
      if List.mem k.c_name !lang.node_kinds then
        match args with
        | { p = PConstr (o, oargs); _ } :: operands -> Some (o, oargs @ operands)
        | _ -> unsupported p.ploc "an operator pattern that is not a constructor"
      else Some (k, args)
  | PConstr (k, args) when k.c_res = TSty -> Some (k, args)
  | _ -> None

(** Whether [p] matches a node, or a sort. *)
let rec has_node_pat (p : pat) =
  Option.is_some (node_pat p)
  ||
  match p.p with
  | PConstr (_, l) | PTuple l -> List.exists has_node_pat l
  | PAs (q, _) | PSome q -> has_node_pat q
  | PCons (h, t) -> has_node_pat h || has_node_pat t
  | PRecord fs -> List.exists (fun (_, q) -> has_node_pat q) fs
  | POr (a, b) | PComm (a, b) -> has_node_pat a || has_node_pat b
  | _ -> false

(** Whether a pattern matches every value of its type. *)
let rec irrefutable (p : pat) =
  match p.p with
  | PAny | PVar _ | PUnit -> true
  | PAs (q, _) -> irrefutable q
  | PTuple l -> List.for_all irrefutable l
  | PRecord fs -> List.for_all (fun (_, q) -> irrefutable q) fs
  | _ -> false

(** Whether a pattern matches every value of its type, once its nodes are
    variables (see [translate]). *)
let rec irrefutable_flat (p : pat) =
  Option.is_some (node_pat p)
  ||
  match p.p with
  | PAny | PVar _ | PUnit -> true
  | PAs (q, _) -> irrefutable_flat q
  | PTuple l -> List.for_all irrefutable_flat l
  | PRecord fs -> List.for_all (fun (_, q) -> irrefutable_flat q) fs
  | _ -> false

let pat_names p = List.map fst (Check.binders p)

(* ---------------------------------------------------------------- *)
(* Expressions *)

(** Variables printed as given terms: the scrutinees and [as] binders of an
    arm, in its statement. *)
let subst : (string * string) list ref = ref []

(** [k ()] with the variables [xs] bound, hence not substituted. *)
let binding xs k =
  let saved = !subst in
  subst := List.filter (fun (x, _) -> not (List.mem x xs)) saved;
  Fun.protect ~finally:(fun () -> subst := saved) k

(** Whether the rule being printed is a rule function's: its cases are guarded
    results ([whenSome]). *)
let cases_style = ref false

let rec expr ctx ft (e : expr) =
  let expr = expr ctx in
  match e.e with
  | EVar x -> (
      match List.assoc_opt x !subst with
      | Some t -> pf ft "%s" t
      | None -> pf ft "%s" (id x))
  | EInt z -> pf ft "(%s : Int)" (Z.to_string z)
  | EBool b -> pf ft "%b" b
  | EUnit -> pf ft "()"
  | EUnreachable -> pf ft "default"
  | EConstr (c, args) when c.c_res = TSty ->
      pf ft "%s" (sort_term c (List.map (Fmt.str "%a" expr) args))
  | EConstr (c, []) when is_data c -> pf ft "%s" (lean_constr c)
  | EConstr (c, args) when is_data c ->
      pf ft "(%s %a)" (lean_constr c) (list ~sep:" " expr) args
  | EConstr (c, _) -> unsupported e.eloc "the constructor %s here" c.c_name
  | ENode ({ e = EConstr (k, args); eloc; _ }, t) ->
      let node, args =
        if List.mem k.c_name !lang.node_kinds then
          match args with
          | { e = EConstr (o, oargs); _ } :: operands -> (o, oargs @ operands)
          | _ -> unsupported eloc "an operator that is not a constructor"
        else (k, args)
      in
      pf ft "%s"
        (node_term node
           (List.map (Fmt.str "%a" expr) args)
           (Fmt.str "%a" expr t))
  | ENode
      ( {
          e = ECall ("mk_commut_binop", [ { e = EConstr (o, oargs); _ }; l; r ]);
          _;
        },
        t ) ->
      let s = Fmt.str "%a" expr in
      let k a b = node_term o (List.map s oargs @ [ s a; s b ]) (s t) in
      pf ft "@[<hv>(if %s.tag_le %s %s@ then %s@ else %s)@]" (o_of_base ())
        (s l) (s r) (k l r) (k r l)
  | ENode _ -> unsupported e.eloc "a node of a computed kind"
  | ECall ("type_of", [ a ]) -> pf ft "(S.ty %a)" expr a
  | ECall ("array_length", [ a ]) -> pf ft "(arrayLength %a)" expr a
  | ECall ("array_get", [ a; i ]) -> pf ft "(arrayGet %a %a)" expr a expr i
  | ECall ("array_set", [ a; i; v ]) ->
      pf ft "(arraySet %a %a %a)" expr a expr i expr v
  | ECall ("array_of_list", [ l ]) -> pf ft "(List.toArray %a)" expr l
  | ECall ("array_to_list", [ a ]) -> pf ft "(Array.toList %a)" expr a
  | ECall ("tag_le", args) ->
      pf ft "(%s.tag_le %a)" (o_of_base ()) (list ~sep:" " expr) args
  | ECall (f, args) ->
      let f =
        if is_oracle ctx f then "O." ^ fld f
        else if is_prim ctx f then prim_ref f
        else
          match fn_kind ctx f with
          | Rule | Ext -> "O." ^ fld f
          | OHelper ->
              fn_ref f ^ " " ^ o_of (Option.get (module_of_name f))
          | Pure -> fn_ref f
      in
      if args = [] then pf ft "%s" f
      else pf ft "(%s %a)" f (list ~sep:" " expr) args
  | ELocalCall (f, args) -> pf ft "(%s %a)" (id f) (list ~sep:" " expr) args
  | EUnop (Neg, a) -> pf ft "(- %a)" expr a
  | EUnop (Not, a) -> pf ft "(! %a)" expr a
  | EBinop (op, a, b) -> (
      let infix s = pf ft "(%a %s %a)" expr a s expr b in
      let dec s = pf ft "(decide (%a %s %a))" expr a s expr b in
      match op with
      | Add -> infix "+"
      | Sub -> infix "-"
      | Mul -> infix "*"
      | Lt -> dec "<"
      | Le -> dec "≤"
      | Gt -> dec ">"
      | Ge -> dec "≥"
      | Eq -> dec "="
      | Ne -> dec "≠"
      | And -> infix "&&"
      | Or -> infix "||")
  | EIf (c, a, b) ->
      pf ft "@[<hv>(if %a@ then %a@ else %a)@]" expr c expr a expr b
  | ELet ({ p = PVar x; _ }, rhs, body) ->
      pf ft "@[<v>(let %s := %a;@ %a)@]" (id x) expr rhs
        (fun ft () -> binding [ x ] (fun () -> expr ft body))
        ()
  | ELet (p, _, _) when has_node_pat p ->
      unsupported e.eloc "a let that matches a node"
  | ELet (p, rhs, body) ->
      pf ft "@[<v>(match %a with@ | %a =>@;<1 2>%a)@]" expr rhs pat p
        (fun ft () -> binding (pat_names p) (fun () -> expr ft body))
        ()
  | ELetFun (f, params, fbody, body) ->
      pf ft "@[<v>(let %s := fun %a =>@;<1 2>%a;@ %a)@]" (id f)
        (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %a)" (id x) lean_ty t))
        params
        (fun ft () ->
          binding (f :: List.map fst params) (fun () -> expr ft fbody))
        ()
        (fun ft () -> binding [ f ] (fun () -> expr ft body))
        ()
  | EMatch (scruts, cases) -> match_ ctx ft (scruts, cases)
  | ETuple l -> pf ft "(%a)" (list expr) l
  | ESome e -> pf ft "(some %a)" expr e
  | ENone -> pf ft "none"
  | ENil -> pf ft "[]"
  | ECons (h, t) -> pf ft "(%a :: %a)" expr h expr t
  | EArray l -> pf ft "#[%a]" (list expr) l
  | ERecord fs ->
      let d = decl_of_ty e.ety in
      pf ft "({ %a } : %a)"
        (list (fun ft (f, _) -> pf ft "%s := %a" f expr (List.assoc f fs)))
        d.d_fields lean_ty e.ety
  | EField (e, f) -> pf ft "%a.%s" expr e f
  | EAssert (_, body) -> expr ft body

(** The record of the model, for [tag_le]. *)
and o_of_base () = "O"

(** The patterns of the case [c] of a match on [scruts]. *)
and case_pats (scruts : expr list) (c : case) =
  match (scruts, c.pat.p) with
  | [ _ ], _ -> [ c.pat ]
  | _, PTuple l -> l
  | _, PAny -> List.map (fun _ -> c.pat) scruts
  | _ -> unsupported c.cloc "a match on a tuple"

(** A case of a match on [scruts], as nested Lean matches: the first on the
    scrutinees, in which the patterns of nodes (and sorts) are replaced by the
    projections of their modules ([R.proj v = some (.C x y)]), and the nodes
    inside those by further matches, on the variables that the outer ones bind
    to them ([kanon__n1], …). Each layer is a list of discriminants, with their
    patterns, and whether these may fail. *)
and translate ctx (scruts : expr list) (c : case) =
  let n = ref 0 in
  let fresh () =
    incr n;
    Printf.sprintf "kanon__n%d" !n
  in
  let str pp x = Fmt.str "%a" pp x in
  let rec flat (q : pat) =
    match (q.p, node_pat q) with
    | _, Some _ ->
        let x = fresh () in
        (x, [ (x, q) ])
    | PAs (q', x), _ when Option.is_some (node_pat q') ->
        (id x, [ (id x, q') ])
    | _ when not (has_node_pat q) -> (str pat q, [])
    | PAs (q', x), _ ->
        let p', l = flat q' in
        (Printf.sprintf "%s@%s" (id x) p', l)
    | PTuple qs, _ ->
        let ps, ls = List.split (List.map flat qs) in
        ("(" ^ String.concat ", " ps ^ ")", List.concat ls)
    | PSome q', _ ->
        let p', l = flat q' in
        ("(some " ^ p' ^ ")", l)
    | PCons (h, t), _ ->
        let ph, lh = flat h and pt, lt = flat t in
        (Printf.sprintf "(%s :: %s)" ph pt, lh @ lt)
    | PConstr (k, qs), _ ->
        let ps, ls = List.split (List.map flat qs) in
        ( Printf.sprintf "(%s)" (String.concat " " (lean_constr k :: ps)),
          List.concat ls )
    | _ -> unsupported q.ploc "a pattern of nodes inside a value"
  in
  (* the match of a node (or a sort) [q] of the term [d], and what it leaves
     to match *)
  let matcher d (q : pat) =
    let k, args = Option.get (node_pat q) in
    let ps, ls = List.split (List.map flat args) in
    let proj = if k.c_res = TSty then "sortProj" else "proj" in
    ( ( Printf.sprintf "(%s.%s %s)" (constr_root k) proj d,
        "some " ^ ctor_app k.c_name ps,
        true ),
      List.concat ls )
  in
  let rec layers pending =
    match pending with
    | [] -> []
    | _ ->
        let ms = List.map (fun (d, q) -> matcher d q) pending in
        List.map fst ms :: layers (List.concat_map snd ms)
  in
  let first, pending =
    List.split
      (List.map2
         (fun (sc : expr) (q : pat) ->
           let s = str (expr ctx) sc in
           match (q.p, node_pat q) with
           | _, Some _ ->
               let m, l = matcher s q in
               ([ m ], l)
           | PAs (q', x), _ when Option.is_some (node_pat q') ->
               let m, l = matcher s q' in
               ([ m; (s, id x, false) ], l)
           | _ ->
               let p, l = flat q in
               ([ (s, p, not (irrefutable_flat q)) ], l))
         scruts (case_pats scruts c))
  in
  match List.concat first :: layers (List.concat pending) with
  | [] :: rest -> rest
  | l -> l

(** The nested matches [ls] (see [translate]), then [rhs], or [none] when a
    pattern fails. *)
and nest ft (ls, rhs) =
  match ls with
  | [] -> rhs ft ()
  | l :: rest ->
      let d = String.concat ", " (List.map (fun (d, _, _) -> d) l) in
      let p = String.concat ", " (List.map (fun (_, p, _) -> p) l) in
      let wild = String.concat ", " (List.map (fun _ -> "_") l) in
      if List.exists (fun (_, _, r) -> r) l then
        pf ft "@[<hv 2>(match %s with@ | %s =>@ %a@ | %s => none)@]" d p nest
          (rest, rhs) wild
      else pf ft "@[<hv 2>(match %s with@ | %s =>@ %a)@]" d p nest (rest, rhs)

(** A case's result: [some body], under its guard. *)
and guarded ctx (c : case) ft () =
  binding (pat_names c.pat) (fun () ->
      match c.guard with
      | None when !cases_style ->
          pf ft "@[<hv>(whenSome true@ (%a))@]" (expr ctx) c.body
      | None -> pf ft "some (%a)" (expr ctx) c.body
      | Some g when !cases_style ->
          pf ft "@[<hv>(whenSome %a@ (%a))@]" (expr ctx) g (expr ctx) c.body
      | Some g ->
          pf ft "@[<hv>(if %a@ then some (%a)@ else none)@]" (expr ctx) g
            (expr ctx) c.body)

(** A case as an alternative: its nested matches, then its guarded result. *)
and case_alt ctx scruts ft (c : case) =
  nest ft (translate ctx scruts c, guarded ctx c)

(** A match: each case is an alternative of its own, returning [none] when its
    pattern or guard fails, and the first case that applies gives the result.
    A last case that always applies is the default. *)
and match_ ctx ft (scruts, (cases : case list)) =
  let alts, default =
    match List.rev cases with
    | ({ guard = None; _ } as c) :: rest when irrefutable c.pat ->
        ( List.rev rest,
          fun ft () ->
            let rhs ft () =
              binding (pat_names c.pat) (fun () -> expr ctx ft c.body)
            in
            nest ft (translate ctx scruts c, rhs) )
    | _ -> (cases, fun ft () -> pf ft "Inhabited.default")
  in
  match alts with
  | [] -> default ft ()
  | _ ->
      pf ft "@[<hv 2>((firstSome [%a]).getD@ %a)@]"
        (Format.pp_print_list
           ~pp_sep:(fun ft () -> pf ft ",@ ")
           (case_alt ctx scruts))
        alts default ()

(* ---------------------------------------------------------------- *)
(* Rules *)

(** A rule function's body: a prefix of [let]s and [assert]s, then a match whose
    consecutive cases with the same name form the rules. *)
let rec split_body (e : expr) : (expr -> expr) * expr list * case list list =
  match e.e with
  | ELet (p, rhs, body) ->
      let pre, s, r = split_body body in
      ((fun x -> { e with e = ELet (p, rhs, pre x) }), s, r)
  | EAssert (_, body) -> split_body body
  | EMatch (scruts, cases) ->
      let groups =
        List.fold_left
          (fun acc (c : case) ->
            match acc with
            | (g :: _ as grp) :: rest when g.rule = c.rule ->
                (grp @ [ c ]) :: rest
            | _ -> [ c ] :: acc)
          [] cases
        |> List.rev
      in
      ((fun x -> x), scruts, groups)
  | _ ->
      ( (fun x -> x),
        [],
        [
          [
            {
              pat = { p = PAny; pty = TUnit; ploc = e.eloc; pid = 0 };
              guard = None;
              body = e;
              rule = Some "main";
              cloc = e.eloc;
              alt = [];
            };
          ];
        ] )

let rule_name (f : fn) (grp : case list) =
  match (List.hd grp).rule with
  | Some r -> r
  | None ->
      raise
        (Check.Error ((List.hd grp).cloc, Fmt.str "%s: unnamed rule" f.name))

let params ft (f : fn) =
  list ~sep:" "
    (fun ft (x, t) -> pf ft "(%s : %a)" (id x) lean_ty t)
    ft f.params

let args ft (f : fn) =
  list ~sep:" " (fun ft (x, _) -> pf ft "%s" (id x)) ft f.params

let arrow ft (f : fn) =
  List.iter (fun (_, t) -> pf ft "%a → " lean_ty t) f.params;
  lean_ty ft f.ret

(** The assumptions on the operands of the rule function [f]: from the subsorts
    in the typing of the node of its spec, the operands whose subsort has a Lean
    predicate [P], with [P], and whether the operand is a list. A rule function
    is stated for the terms that satisfy them (see {!pre_prop}). *)
let preconditions (f : fn) =
  List.filter_map
    (fun (x, (ss : subsort), is_list) ->
      Option.map (fun p -> (x, p, is_list)) ss.ss_lean)
    (fst (Check.fn_subsorts f))

(** The Lean predicate that the result of the rule function [f] must satisfy:
    the one of the subsort in the typing of the node of its spec, if it has one.
*)
let postcondition (f : fn) =
  Option.bind (snd (Check.fn_subsorts f)) (fun (ss : subsort) -> ss.ss_lean)

(** The name of the hypothesis that the operand [x] satisfies its predicate. *)
let hyp_name x = "hs_" ^ x

(** The statement of an assumption: [P x], where [text x] is how the statement
    refers to the operand [x], and [P y] for every element [y] of a list. *)
let pre_prop ~text (x, p, is_list) =
  let p =
    match List.find_opt (fun ss -> ss.ss_lean = Some p) !lang.subsorts with
    | Some ss -> (
        match module_of_loc ss.ss_loc with
        | Some m -> module_root m ^ "." ^ p
        | None -> p)
    | None -> p
  in
  if is_list then Fmt.str "(∀ y ∈ %s, %s y)" (text x) p
  else Fmt.str "%s %s" p (text x)

(** The assumptions of [f] on its own parameters, each followed by an arrow. *)
let pre_arrows ft (f : fn) =
  List.iter (fun pre -> pf ft "%s → " (pre_prop ~text:id pre)) (preconditions f)

(** The assumptions of [f] as the binders of hypotheses, on parameters whose
    names are [rename]d, each after a space. *)
let pre_binders ?(rename = Fun.id) ft (f : fn) =
  List.iter
    (fun ((x, _, _) as pre) ->
      pf ft " (%s : %s)" (hyp_name x)
        (pre_prop ~text:(fun x -> id (rename x)) pre))
    (preconditions f)

(** The names of the hypotheses of the assumptions of [f], each after a space.
*)
let pre_names ft (f : fn) =
  List.iter (fun (x, _, _) -> pf ft " %s" (hyp_name x)) (preconditions f)


let rules (f : fn) =
  let pre, scruts, groups = split_body f.body in
  List.map (fun g -> (pre, scruts, g)) groups

(* ---------------------------------------------------------------- *)
(* [[@cases]]: one statement per alternative ("arm") of a rule *)

(** An arm's statement: its binders (name, Lean type), the substitution of the
    scrutinees and pattern aliases, and for each substituted name the [pid] of
    the pattern it stands for. *)
type arm = {
  a_case : case;
  a_binders : (string * string) list;
  a_subst : (string * (string * int)) list;
  a_body_subst : (string * string) list;
      (** [a_subst] without the names that the pattern rebinds *)
  a_lets : (string * expr) list;
      (** the [let]s before the match (the variables of the sorts of the
          parameters), which the statement substitutes *)
}


(** The term a pattern matches, with its wildcards named after their [pid]. *)
let pat_term (p : pat) =
  let binders = ref [] and subst = ref [] in
  let bind x t = binders := !binders @ [ (x, t) ] in
  let rec go (p : pat) =
    match p.p with
    | PAny ->
        let x = Printf.sprintf "w__%d" p.pid in
        bind x (ty_str p.pty);
        x
    | PVar x ->
        bind (id x) (ty_str p.pty);
        id x
    | PAs (q, x) ->
        let t = go q in
        subst := (x, (t, q.pid)) :: !subst;
        t
    | PInt z -> Printf.sprintf "(%s : Int)" (Z.to_string z)
    | PBool b -> string_of_bool b
    | PUnit -> "()"
    | PTuple l -> "(" ^ String.concat ", " (List.map go l) ^ ")"
    | PSome q -> "(some " ^ go q ^ ")"
    | PNone -> "none"
    | PNil -> "[]"
    | PCons (h, t) ->
        let h = go h in
        "(" ^ h ^ " :: " ^ go t ^ ")"
    | PRecord fs ->
        let field (f, t) =
          match List.assoc_opt f fs with
          | Some q -> go q
          | None ->
              let x = Printf.sprintf "%s__%d" f p.pid in
              bind x (ty_str t);
              x
        in
        "⟨"
        ^ String.concat ", " (List.map field (decl_of_ty p.pty).d_fields)
        ^ "⟩"
    | PConstr (c, args) when p.pty = TTerm ->
        let node, args =
          match node_pat p with Some (n, a) -> (n, a) | None -> (c, args)
        in
        let args = List.map go args in
        let t = Printf.sprintf "t__%d" p.pid in
        bind t (ty_str TSty);
        node_term node args t
    | PConstr (c, _) when not (is_data c) ->
        unsupported p.ploc "the pattern of %s here" c.c_name
    | PConstr (c, args) ->
        let args = List.map go args in
        if args = [] then lean_constr c
        else "(" ^ String.concat " " (lean_constr c :: args) ^ ")"
    | POr _ | PComm _ -> failwith "gen_lean: or-pattern after desugaring"
  in
  let t = go p in
  (t, !binders, !subst)

let cases_error (f : fn) loc fmt =
  Fmt.kstr (fun s -> raise (Check.Error (loc, f.name ^ ": " ^ s))) fmt

let arm_of (f : fn) scruts (c : case) : arm =
  let scrut_params =
    List.map
      (fun (e : expr) ->
        match e.e with
        | EVar x when List.mem_assoc x f.params -> x
        | _ -> cases_error f e.eloc "[@cases] matches on parameters only")
      scruts
  in
  let pats =
    match (scrut_params, c.pat.p) with
    | [ _ ], _ -> [ c.pat ]
    | _, PTuple l -> l
    | _, PAny -> List.map (fun _ -> c.pat) scrut_params
    | _ -> cases_error f c.cloc "unexpected pattern"
  in
  let substituted = ref [] and binders = ref [] and subst = ref [] in
  List.iter2
    (fun x (p : pat) ->
      match p.p with
      | PAny -> ()
      | PVar y -> subst := (y, (id x, p.pid)) :: !subst
      | _ ->
          let t, bs, sb = pat_term p in
          substituted := x :: !substituted;
          binders := !binders @ bs;
          subst := ((x, (t, p.pid)) :: sb) @ !subst)
    scrut_params pats;
  let params =
    List.filter_map
      (fun (x, t) ->
        if List.mem x !substituted then None else Some (id x, ty_str t))
      f.params
  in
  List.iter
    (fun (x, _) ->
      if List.mem_assoc x params then
        cases_error f c.cloc "pattern variable %s shadows a parameter" x)
    !binders;
  (* in the guard and body, pattern variables shadow the scrutinees they are
     part of *)
  let names = List.map fst !binders in
  let body_subst =
    List.filter_map
      (fun (x, (t, _)) -> if List.mem (id x) names then None else Some (x, t))
      !subst
  in
  {
    a_case = c;
    a_binders = params @ !binders;
    a_subst = !subst;
    a_body_subst = body_subst;
    a_lets = [];
  }

(** Arms of a rule function, per rule. *)
let arms (f : fn) =
  List.map
    (fun (pre, scruts, grp) ->
      let rec lets (e : expr) =
        match e.e with
        | ELet ({ p = PVar x; _ }, rhs, b) -> (x, rhs) :: lets b
        | EUnit -> []
        | _ ->
            cases_error f f.floc
              "[@cases]: a destructuring let before the match"
      in
      let a_lets = lets (pre { f.body with e = EUnit }) in
      ( rule_name f grp,
        List.map (fun c -> { (arm_of f scruts c) with a_lets }) grp ))
    (rules f)

(** Whether [x] occurs in [e] other than as the argument of [ty] or [size] (when
    [ty_ok]), where it is not rebound. *)
let rec occurs ~ty_ok x (e : expr) =
  let go = occurs ~ty_ok x in
  match e.e with
  | EVar y -> x = y
  | ECall (f, [ { e = EVar y; _ } ]) when y = x && List.mem f !lang.ty_only ->
      not ty_ok
  | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> false
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l | EArray l ->
      List.exists go l
  | ENode (a, b) | EBinop (_, a, b) | ECons (a, b) | EAssert (a, b) ->
      go a || go b
  | EUnop (_, a) | ESome a | EField (a, _) -> go a
  | EIf (a, b, c) -> go a || go b || go c
  | ERecord l -> List.exists (fun (_, e) -> go e) l
  | ELet (p, a, b) -> go a || ((not (List.mem x (pat_names p))) && go b)
  | ELetFun (g, ps, a, b) ->
      ((not (List.mem x (g :: List.map fst ps))) && go a) || (g <> x && go b)
  | EMatch (scruts, cases) ->
      List.exists go scruts
      || List.exists
           (fun (c : case) ->
             (not (List.mem x (pat_names c.pat)))
             && (Option.fold ~none:false ~some:go c.guard || go c.body))
           cases

(** Whether [x] occurs in the result [e] other than as a term that the result is
    built from: by itself, or as an operand of a raw node, under the branches of
    conditionals and the bodies of [let]s, or in a function that only reads the
    type of a term. A result in which the term [x] is swapped by commutativity
    is then refined by commutativity and congruence (with the same conditions,
    the types of the swapped terms being the same). *)
let rec occurs_unsafe x (e : expr) =
  let ty_only = occurs ~ty_ok:true x in
  match e.e with
  | EVar _ -> false
  | ENode ({ e = EConstr (_, args); _ }, sort) ->
      List.exists
        (fun (a : expr) ->
          if a.ety = TTerm then occurs_unsafe x a else ty_only a)
        args
      || ty_only sort
  | EIf (c, a, b) -> ty_only c || occurs_unsafe x a || occurs_unsafe x b
  | ELet (p, a, b) ->
      ty_only a || ((not (List.mem x (pat_names p))) && occurs_unsafe x b)
  | _ -> ty_only e

(** The swaps of commutative operands that turn [pb] into [pa], two alternatives
    of a pattern: the nodes swapped, as [(qa, qb, op)] for the subpatterns [qa]
    of [pa] and [qb] of [pb] and their operator [op], inner nodes first. Raises
    [Exit] if the patterns differ otherwise. *)
let rec swaps (pa : pat) (pb : pat) =
  let all la lb =
    if List.length la <> List.length lb then raise Exit
    else List.concat (List.map2 swaps la lb)
  in
  if pa.pid <> pb.pid then raise Exit;
  match (pa.p, pb.p) with
  | PConstr (c, [ op; x; y ]), PConstr (c', [ op'; x'; y' ])
    when c = c' && x.pid <> x'.pid -> (
      match op.p with
      | PConstr (o, _) when is_commutative o.c_name ->
          swaps op op' @ swaps x y' @ swaps y x' @ [ (pa, pb, o) ]
      | _ -> raise Exit)
  | PConstr (c, la), PConstr (c', lb) when c = c' -> all la lb
  | PTuple la, PTuple lb -> all la lb
  | PAs (q, x), PAs (q', x') when x = x' -> swaps q q'
  | PSome q, PSome q' -> swaps q q'
  | PCons (h, t), PCons (h', t') -> all [ h; t ] [ h'; t' ]
  | PRecord fa, PRecord fb when List.map fst fa = List.map fst fb ->
      all (List.map snd fa) (List.map snd fb)
  | d, d' when d = d' -> []
  | _ -> raise Exit

(** The pids of the nodes of a pattern. *)
let rec pids (p : pat) =
  p.pid
  ::
  (match p.p with
  | PAs (q, _) | PSome q -> pids q
  | PTuple l | PConstr (_, l) -> List.concat_map pids l
  | PCons (h, t) -> pids h @ pids t
  | PRecord fs -> List.concat_map (fun (_, q) -> pids q) fs
  | _ -> [])

(** The commutative operator of the spec of [f], if it is the node of one over
    the scrutinees [scruts] of its rules. *)
let spec_comm (f : fn) scruts =
  let names l =
    List.sort compare
      (List.map (fun (e : expr) -> match e.e with EVar x -> x | _ -> "") l)
  in
  match (Option.get f.spec).e with
  | ENode ({ e = EConstr (_, [ { e = EConstr (o, _); _ }; x; y ]); _ }, _)
    when is_commutative o.c_name && names [ x; y ] = names scruts ->
      Some o
  | _ -> None

(** How the arm [a] is derived from another by commutativity, if it is: from the
    arm [b] of the same source case that takes the same or-pattern choices and
    no [[@comm]] swap, when [a]'s guard and body do not depend on the swaps (a
    variable may stand for a different parameter in each, when the arguments of
    the function are swapped). Gives [b], the arguments of its statement, the
    operator of the spec if the arguments of the function are swapped, and the
    nested swaps (see [swaps]). *)
let derived_from (f : fn) (grp : arm list) (a : arm) =
  let c = a.a_case in
  if not (List.exists (fun (_, i, comm, _) -> comm && i = 1) c.alt) then None
  else
    let norm l = List.sort compare l in
    let base_alt =
      norm
        (List.map
           (fun (p, i, comm, n) ->
             if comm then (p, 0, comm, "") else (p, i, comm, n))
           c.alt)
    in
    match
      List.find_opt
        (fun b -> b.a_case.cloc = c.cloc && norm b.a_case.alt = base_alt)
        grp
    with
    | None -> None
    | Some b -> (
        let names =
          List.sort_uniq compare
            (List.map fst a.a_subst @ List.map fst b.a_subst)
        in
        let is_param (arm : arm) t = List.mem_assoc t arm.a_binders in
        (* the guard and body, under the [let]s before the match that they use,
           which read the parameters *)
        let with_lets (e : expr) =
          List.fold_right
            (fun (x, (rhs : expr)) (e : expr) ->
              if occurs ~ty_ok:false x e then
                let p =
                  { p = PVar x; pty = rhs.ety; ploc = rhs.eloc; pid = 0 }
                in
                { e with e = ELet (p, rhs, e) }
              else e)
            a.a_lets e
        in
        let e = with_lets c.body and g = Option.map with_lets c.guard in
        (* the variables that stand for a swapped term in the body *)
        let swapped = ref false in
        let independent x =
          match (List.assoc_opt x a.a_subst, List.assoc_opt x b.a_subst) with
          | Some (t, _), Some (t', _) when t = t' -> true
          | Some (t, _), Some (t', _) when is_param a t && is_param b t' -> true
          | Some (_, p), Some (_, p') when p = p' ->
              (not (Option.fold ~none:false ~some:(occurs ~ty_ok:true x) g))
              && ((not (occurs ~ty_ok:true x e))
                 ||
                 (swapped := true;
                  not (occurs_unsafe x e)))
          | Some (_, p), Some (_, p') ->
              let ty_ok = p = p' in
              not
                (occurs ~ty_ok x e
                || Option.fold ~none:false ~some:(occurs ~ty_ok x) g)
          | Some _, None | None, Some _ ->
              (* a parameter matched in one arm and not the other *)
              not
                (occurs ~ty_ok:false x e
                || Option.fold ~none:false ~some:(occurs ~ty_ok:false x) g)
          | None, None -> false
        in
        (* the parameter of [b] that a variable stands for is the one it stands
           for in [a] *)
        let arg (y, _) =
          match
            List.find_opt
              (fun (x, (t, _)) -> t = y && List.mem_assoc x a.a_subst)
              b.a_subst
          with
          | Some (x, _) when is_param b y -> fst (List.assoc x a.a_subst)
          | _ when not (is_param a y) -> (
              (* a parameter matched by [_], which is the other one in [a] *)
              match
                List.filter (fun (z, _) -> not (is_param b z)) a.a_binders
              with
              | [ (z, _) ] -> z
              | _ -> y)
          | _ -> y
        in
        let scruts =
          match rules f with (_, scruts, _) :: _ -> scruts | [] -> []
        in
        let shape =
          try
            match (c.pat.p, b.a_case.pat.p) with
            | PTuple [ x; y ], PTuple [ x'; y' ] when x.pid <> x'.pid ->
                if c.pat.pid <> b.a_case.pat.pid then raise Exit;
                Option.map
                  (fun o -> (Some o, swaps x y' @ swaps y x'))
                  (spec_comm f scruts)
            | _ -> Some (None, swaps c.pat b.a_case.pat)
          with Exit -> None
        in
        match shape with
        | Some (top, nested) when List.for_all independent names ->
            Some (b, List.map arg b.a_binders, top, nested, !swapped)
        | _ -> None)

(** The Lean function of one rule of [f], of the module that is printed: its
    cases are alternatives, the first that applies giving the result. *)
let rule_def ctx ft (f : fn) (pre, scruts, grp) =
  cases_style := true;
  Fun.protect ~finally:(fun () -> cases_style := false) @@ fun () ->
  let name = rule_name f grp in
  let rec lets ft (e : expr) =
    match e.e with
    | ELet ({ p = PVar x; _ }, rhs, b) ->
        pf ft "let %s := %a;@ %a" (id x) (expr ctx) rhs lets b
    | ELet _ -> failwith "gen_lean: destructuring let before a rule match"
    | _ ->
        Format.pp_print_list
          ~pp_sep:(fun ft () -> pf ft "@ <|> ")
          (case_alt ctx scruts) ft grp
  in
  pf ft "@[<v 2>def %s.r_%s (O : Ops S) %a : Option S.Term :=@ %a@]@ @ "
    (qn f.name) (id name) params f lets
    (pre { (List.hd grp).body with e = EUnit })

(** The names of the arms of a rule: the names of the choices that produced each
    (see [Check.alternatives]), in the order of the source, prefixed with the
    index of its source case if the rule has several, or [main]. *)
let arm_names (arms : arm list) =
  let clocs =
    List.fold_left
      (fun l (a : arm) ->
        if List.mem a.a_case.cloc l then l else l @ [ a.a_case.cloc ])
      [] arms
  in
  List.map
    (fun (a : arm) ->
      let alt = List.sort compare a.a_case.alt in
      let swaps = List.filter (fun (_, _, comm, _) -> comm) alt in
      let choices =
        List.filter_map
          (fun ((_, _, comm, n) as c) ->
            if n = "" then None
            else if comm && List.length swaps > 1 then
              let rec index k = function
                | x :: _ when x = c -> k
                | _ :: l -> index (k + 1) l
                | [] -> assert false
              in
              Some (n ^ string_of_int (index 1 swaps))
            else Some n)
          alt
      in
      let case =
        if List.length clocs < 2 then []
        else
          let rec index k = function
            | l :: _ when l = a.a_case.cloc -> k
            | _ :: ls -> index (k + 1) ls
            | [] -> assert false
          in
          [ Printf.sprintf "c%d" (index 1 clocs) ]
      in
      match case @ choices with [] -> "main" | l -> String.concat "_" l)
    arms

let arm_name f r arms i =
  Printf.sprintf "%s.r_%s.%s" (qn f.name) (id r)
    (id (List.nth (arm_names arms) i))

(* ---------------------------------------------------------------- *)
(* Files *)

(** A generated Lean file: the root of its module and its path under it
    ([["Model"]] for [R.Model]), and its contents. *)
type file = {
  froot : string;
  path : string list;
  contents : Format.formatter -> unit;
}

(** The path of the file of the module at [path] under the root [r], relative to
    the directory of the root. *)
let file_name_at r path =
  String.concat "/" (String.split_on_char '.' r @ path) ^ ".lean"

(** The path of a generated file, relative to the directory of its root. *)
let file_name (f : file) = file_name_at f.froot f.path

(** The Lean module of the file at [path] under the root [r]. *)
let lean_module r path = String.concat "." (r :: List.map id path)

(** Whether the hand-written file at [path] under the root [r] exists (given by
    the command line). *)
let has_file : (string -> string list -> bool) ref = ref (fun _ _ -> false)

(** The file at [path] under the root [r], from [sources], that imports
    [imports] and has [body] in the namespace [r]. *)
let lean_file ~sources r path imports body =
  {
    froot = r;
    path;
    contents =
      (fun ft ->
        pf ft "@[<v>-- Generated by kanon from %a. Do not edit.@ "
          (list Format.pp_print_string)
          sources;
        List.iter (fun i -> pf ft "import %s@ " i) (uniq imports);
        pf ft
          "@ set_option linter.unusedVariables false@ set_option \
           linter.unusedSimpArgs false@ set_option maxHeartbeats 1000000@ @ \
           noncomputable section@ @ namespace %s@ @ open Classical Kanon@ @ "
          r;
        body ft;
        pf ft "end %s@]@." r);
  }

(** The sources of the files of the module [m]: its declarations and its rules.
*)
let module_sources m =
  let base = String.uncapitalize_ascii m in
  [ base ^ ".knl"; base ^ ".kn" ]

(** The binders of the statements over the languages that have the module [m]:
    [{S : Kanon.Sem} [D.Lang S] … [M.Lang S]]. *)
let lang_binders m =
  String.concat " "
    ("{S : Kanon.Sem}"
    :: List.map
         (fun d -> Printf.sprintf "[%s.Lang S]" (module_root d))
         (lang_mods m)
    @ List.map
        (fun d -> Printf.sprintf "[%s.Typed S]" (module_root d))
        (List.filter has_sorts (lang_mods m)))

(** The line that declares [lang_binders] as variables. *)
let variables ft m =
  pf ft "variable %s@ @ "
    (String.concat " "
       ("{S : Kanon.Sem}"
       :: List.map
            (fun d -> Printf.sprintf "[%s.Lang S]" (module_root d))
            (lang_mods m)))

(** [set_option maxHeartbeats n in], before a generated proof of an arm of [f]
    (of a law, for [None]): that of [f] ([[@lean_heartbeats n]]), or else that
    of the language ([[@@@lean_heartbeats n]]). *)
let heartbeats (f : fn option) ft =
  let n =
    match f with
    | Some { heartbeats = Some n; _ } -> n
    | _ -> !lang.lean_heartbeats
  in
  pf ft "set_option maxHeartbeats %d in@ " n

(* ---------------------------------------------------------------- *)
(* The typing of the nodes *)

let rec expr_vars (e : expr) =
  match e.e with
  | EVar x -> [ x ]
  | EConstr (_, l) | ECall (_, l) -> List.concat_map expr_vars l
  | EBinop (_, a, b) -> expr_vars a @ expr_vars b
  | EUnop (_, a) -> expr_vars a
  | _ -> []

(** The variables that are the width of a type (its [nat] arguments), which are
    positive. *)
let rec widths (e : expr) =
  match e.e with
  | EConstr (c, args) ->
      List.concat
        (List.map2
           (fun a (x : expr) ->
             match (a, x.e) with Small, EVar v -> [ v ] | _ -> widths x)
           c.c_args args)
  | _ -> []

let rec conjuncts (e : expr) =
  match e.e with EBinop (And, a, b) -> conjuncts a @ conjuncts b | _ -> [ e ]

let prop ctx (e : expr) =
  let op = function
    | Lt -> Some "<"
    | Le -> Some "≤"
    | Gt -> Some ">"
    | Ge -> Some "≥"
    | Eq -> Some "="
    | Ne -> Some "≠"
    | _ -> None
  in
  match e.e with
  | EBinop (o, a, b) when Option.is_some (op o) ->
      Fmt.str "%a %s %a" (expr ctx) a (Option.get (op o)) (expr ctx) b
  | _ -> Fmt.str "%a = true" (expr ctx) e


(** The sort of the result of an operator in its typing predicate. *)
let result_name = "kanon__t"

(** The sorts of the [n] operands and of the result of an operator in its typing
    predicate, named so as not to clash with the variables of its typing:
    [kanon__a], [kanon__b], ..., [kanon__t]. *)
let typing_names n =
  List.init n (fun i ->
      Printf.sprintf "kanon__%c" (Char.chr (Char.code 'a' + i)))
  @ [ result_name ]

(** The conditions under which the operands and result of an operator (see
    [typing_names]) have the sorts of [ty]. A variable that stands for a whole
    sort is the first operand (or result) of that sort; operands of a same sort
    with variables are equal; the other variables are existentially quantified,
    only around the one equation that uses them if they are not used elsewhere,
    and positive when they are widths that the condition does not constrain. *)
let typing_rhs ?names ctx (ty : typing) =
  let names =
    Option.value names ~default:(typing_names (List.length ty.t_sorts - 1))
  in
  let params = List.filter (( <> ) "_") ty.t_params in
  (* a width is positive, unless the condition constrains it *)
  let widths =
    let cond = Option.fold ~none:[] ~some:expr_vars ty.t_when in
    List.filter
      (fun v -> not (List.mem v cond))
      (uniq (List.concat_map widths ty.t_sorts))
  in
  let reps = ref [] and bound = ref [] and conjs = ref [] and seen = ref [] in
  let str e =
    let saved = !subst in
    subst := !reps;
    Fun.protect
      ~finally:(fun () -> subst := saved)
      (fun () -> Fmt.str "%a" (expr ctx) e)
  in
  let exists_vars e =
    List.filter
      (fun v -> (not (List.mem_assoc v !reps)) && not (List.mem v params))
      (uniq (expr_vars e))
  in
  let add text vars = conjs := !conjs @ [ (text, vars) ] in
  let prop e =
    let saved = !subst in
    subst := !reps;
    Fun.protect ~finally:(fun () -> subst := saved) (fun () -> prop ctx e)
  in
  let cond () =
    Option.iter
      (fun w -> List.iter (fun c -> add (prop c) (exists_vars c)) (conjuncts w))
      ty.t_when
  in
  let last = List.length names - 1 in
  List.iteri
    (fun i (name, (s : expr)) ->
      (* the condition, between the operands and the result *)
      if i = last then cond ();
      match s.e with
      | EVar x when List.mem_assoc x !reps ->
          add (name ^ " = " ^ List.assoc x !reps) []
      | EVar x when not (List.mem_assoc x !bound) -> reps := (x, name) :: !reps
      | _ -> (
          let vs = exists_vars s and r = str s in
          match List.find_opt (fun (_, r') -> r' = r) !seen with
          | Some (name', _) when vs <> [] -> add (name ^ " = " ^ name') []
          | _ ->
              List.iter
                (fun v ->
                  if not (List.mem_assoc v !bound) then
                    bound := !bound @ [ (v, List.length !conjs) ])
                vs;
              add (name ^ " = " ^ r) vs;
              seen := !seen @ [ (name, r) ]))
    (List.combine names ty.t_sorts);
  let conjs = !conjs in
  let last v =
    List.fold_left max 0
      (List.mapi (fun i (_, vs) -> if List.mem v vs then i else 0) conjs)
  in
  let tight (v, k) = last v = k in
  let pos v = "0 < " ^ v in
  let binders vs =
    let tys = List.map (fun v -> ty_str (List.assoc v ty.t_vars)) vs in
    match uniq tys with
    | [ t ] -> String.concat " " vs ^ " : " ^ t
    | _ ->
        String.concat " "
          (List.map2 (fun v t -> Printf.sprintf "(%s : %s)" v t) vs tys)
  in
  let long = List.filter (fun b -> not (tight b)) !bound |> List.map fst in
  let body =
    List.map pos (List.filter (fun p -> List.mem p widths) params)
    @ List.map pos (List.filter (fun v -> List.mem v widths) long)
    @ List.mapi
        (fun i (text, _) ->
          match List.filter (fun b -> tight b && snd b = i) !bound with
          | [] -> text
          | bs ->
              let vs = List.map fst bs in
              Printf.sprintf "(∃ %s, %s)" (binders vs)
                (String.concat " ∧ "
                   (List.map pos (List.filter (fun v -> List.mem v widths) vs)
                   @ [ text ])))
        conjs
  in
  let body = if body = [] then "True" else String.concat " ∧ " body in
  if long = [] then body else Printf.sprintf "∃ %s, %s" (binders long) body

(* ---------------------------------------------------------------- *)
(* The files of a module *)

(** The rule functions. *)
let rule_fns ctx = List.filter (fun f -> fn_kind ctx f.name = Rule) ctx.fns

(** The functions of the module [m] of the kinds [kinds]. *)
let module_fns ctx m kinds =
  List.filter
    (fun (f : fn) ->
      module_of_name f.name = Some m && List.mem (fn_kind ctx f.name) kinds)
    ctx.fns

let module_prims ctx m =
  List.filter
    (fun (q : prim) -> (not q.oracle) && module_of_name q.pname = Some m)
    ctx.prims

let module_oracles ctx m =
  List.filter
    (fun (q : prim) -> q.oracle && module_of_name q.pname = Some m)
    ctx.prims

(** Whether the module [m] has a model: whether it is the language's, or has
    nodes, sorts, functions or primitives. A module of data types only has
    none. *)
let has_model ctx m =
  !root_module = Some m
  || has_lang m
  || List.exists (fun (f : fn) -> module_of_name f.name = Some m) ctx.fns
  || List.exists (fun (q : prim) -> module_of_name q.pname = Some m) ctx.prims

(** The module of the case [c] of [f]: that of its declaration, if it uses the
    module of [f] (an [extend]), else that of [f] (a case derived from a law of
    the node of its spec). *)
let case_module (f : fn) (c : case) =
  let fm = Option.get (module_of_name f.name) in
  match module_of_loc c.cloc with
  | Some m when List.mem fm (closure m) -> m
  | _ -> fm

(** The arms of the rule function [f] that the module [m] proves, by rule. *)
let module_arms m (f : fn) =
  List.filter_map
    (fun (r, arms) ->
      let mine = List.exists (fun a -> case_module f a.a_case = m) arms in
      if mine then Some (r, arms) else None)
    (arms f)

(** The rules of [f] that the module [m] gives. *)
let module_rules m (f : fn) =
  List.filter
    (fun (_, _, grp) -> case_module f (List.hd grp) = m)
    (rules f)

(** The commutative nodes of [m]. *)
let module_comm m =
  List.filter_map
    (fun name ->
      let op = Option.get (find_constr name) in
      if in_module m op.c_loc then
        match Check.node_of_op op with
        | Some (_, [ _; _ ]) -> Some (find_gnode op)
        | _ -> None
      else None)
    !lang.commutative

(** The cases of the extensible helper [f], with the module of each, and its
    last case, which always applies. *)
let ext_cases (f : fn) =
  match f.body.e with
  | EMatch (scruts, cases) -> (
      match List.rev cases with
      | ({ guard = None; _ } as last) :: rest when irrefutable last.pat ->
          (scruts, List.rev rest, last)
      | _ ->
          raise
            (Check.Error
               ( f.floc,
                 f.name
                 ^ ": an extensible helper ends with a case that always \
                    applies" )))
  | _ ->
      raise
        (Check.Error (f.floc, f.name ^ ": an extensible helper is a match"))

(** The cases of [f] that the module [m] adds, with their names. *)
let module_ext_cases m (f : fn) =
  let _, cases, _ = ext_cases f in
  List.filter (fun (c : case) -> case_module f c = m) cases
  |> List.mapi (fun i c -> (Printf.sprintf "c%d" (i + 1), c))

(** The names of the arguments of the node [n]: those of its typing for the
    arguments that it names, then [x1] … for the others, [a1] … for its
    children and [l1] … for its lists of children. *)
let node_names (p : program) (n : gnode) =
  let ty =
    List.find_opt
      (fun (t : typing) ->
        t.t_constr.c_name = n.gc.c_name && t.t_constr.c_res = n.gc.c_res)
      (p.typing @ p.leaf_typing)
  in
  let reserved = [ "t"; "ty"; "S"; "L"; "O"; "v"; "e"; "n"; "x"; "l"; "ρ" ] in
  List.mapi
    (fun i t ->
      match t with
      | TTerm -> Printf.sprintf "a%d" (i + 1)
      | TList TTerm -> Printf.sprintf "l%d" (i + 1)
      | t when uses_term t ->
          unsupported n.gc.c_loc "the argument %a of the node %s" pp_ty t
            n.gc.c_name
      | _ -> (
          match ty with
          | Some ty
            when i < List.length ty.t_params && List.nth ty.t_params i <> "_"
            ->
              let x = List.nth ty.t_params i in
              if List.mem x reserved then "kanon__" ^ x else id x
          | _ -> Printf.sprintf "x%d" (i + 1)))
    (n.gpayload @ n.goperands)

let node_typing (p : program) (n : gnode) =
  List.find_opt
    (fun (t : typing) ->
      t.t_constr.c_name = n.gc.c_name && t.t_constr.c_res = n.gc.c_res)
    (p.typing @ p.leaf_typing)

(** The types that the module [m] declares, callees first, but those that Kanon
    generates. *)
let module_decls m =
  let seen = Hashtbl.create 17 and out = ref [] in
  let rec decls_of_ty = function
    | TData _ as t -> [ decl_of_ty t ]
    | TTuple l -> List.concat_map decls_of_ty l
    | TOption t | TList t | TArray t -> decls_of_ty t
    | _ -> []
  in
  let rec visit (d : decl) =
    if not (Hashtbl.mem seen d.d_name) then (
      Hashtbl.add seen d.d_name ();
      List.iter visit
        (List.concat_map decls_of_ty
           (List.map snd d.d_fields
           @ List.concat_map
               (fun c -> List.map arg_ty c.c_args)
               (constrs_of d)));
      out := d :: !out)
  in
  List.iter visit !lang.decls;
  List.filter
    (fun d -> decl_module d = Some m && not (generated_decl d))
    (List.rev !out)

let has_types m = List.exists (fun d -> not (is_abstract d)) (module_decls m)
let has_hand_types m = List.exists by_hand (module_decls m)

(** The files of the types of the modules [ms]: [R.Types] and [R.Abstract],
    those that they have. *)
let types_imports ms =
  List.concat_map
    (fun m ->
      let r = module_root m in
      (if has_types m then [ r ^ ".Types" ] else [])
      @ if has_hand_types m then [ r ^ ".Abstract" ] else [])
    ms

let lean_decl ft (d : decl) =
  let name = decl_lean_name d in
  doc ft d.d_doc;
  (match d.d_fields with
  | [] ->
      pf ft "@[<v 2>inductive %s where" name;
      List.iter
        (fun c ->
          pf ft "@ %a| %s" doc c.c_doc c.c_name;
          if c.c_args <> [] then
            pf ft " : %a%s"
              (list ~sep:"" (fun ft a -> pf ft "%a → " lean_ty (arg_ty a)))
              c.c_args name)
        (constrs_of d)
  | fields ->
      pf ft "@[<v 2>structure %s where" name;
      List.iter (fun (f, t) -> pf ft "@ %s : %a" f lean_ty t) fields);
  pf ft "@]@   deriving DecidableEq, Repr, Inhabited@ @ "

(** [Types.lean]: the types that the module [m] declares, but its abstract
    types, which it defines by hand ([Abstract.lean], which may use these). *)
let types_file m =
  let own = List.filter (fun d -> not (is_abstract d)) (module_decls m) in
  List.iter
    (fun (d : decl) ->
      if List.exists uses_term (List.map snd d.d_fields)
         || List.exists
              (fun c -> List.exists (fun a -> uses_term (arg_ty a)) c.c_args)
              (constrs_of d)
      then unsupported d.d_loc "the type %s, which holds terms" d.d_name)
    own;
  let r = module_root m in
  {
    froot = r;
    path = [ "Types" ];
    contents =
      (fun ft ->
        pf ft "@[<v>-- Generated by kanon from %a. Do not edit.@ @ "
          (list Format.pp_print_string)
          (module_sources m);
        let imports =
          types_imports (List.filter (( <> ) m) (closure m))
          @ List.filter_map
              (fun d ->
                if by_hand d then Some (r ^ ".Abstract") else None)
              []
        in
        List.iter (fun i -> pf ft "import %s@ " i) imports;
        if imports <> [] then pf ft "@ ";
        pf ft "namespace %s@ @ " r;
        List.iter (lean_decl ft) own;
        pf ft "end %s@]@." r);
  }

(** The argument of a node constructor: a child, a list of children, or a value
    of its type. *)
let arg_kind = function
  | TTerm -> `Child
  | TList TTerm -> `Children
  | t -> `Value t

(** [Node.lean]: the sorts and the nodes of [m]. *)
let node_file (p : program) m =
  let r = module_root m in
  let nodes = module_nodes m and sorts = module_sorts m in
  lean_file ~sources:(module_sources m) r [ "Node" ]
    ("KanonCore.Embed" :: types_imports (closure m))
  @@ fun ft ->
  if sorts <> [] then (
    pf ft "/-- The sorts of the module. -/@ @[<v 2>inductive Srt where";
    List.iter
      (fun (c : constr) ->
        pf ft "@ %a| %s%s" doc c.c_doc c.c_name
          (String.concat ""
             (List.mapi
                (fun i a ->
                  Fmt.str " (x%d : %a)" (i + 1) lean_ty (arg_ty a))
                c.c_args)))
      sorts;
    pf ft "@]@   deriving DecidableEq, Repr, Inhabited@ @ ");
  if nodes <> [] then (
    let args n =
      List.map2
        (fun x t ->
          match arg_kind t with
          | `Child -> (x, "T")
          | `Children -> (x, "(List T)")
          | `Value t -> (x, ty_str t))
        (node_names p n) (n.gpayload @ n.goperands)
    in
    pf ft
      "/-- The nodes of the module, over the terms `T` of a language. -/@ \
       @[<v 2>inductive Node (T : Type) where";
    List.iter
      (fun n ->
        pf ft "@ %a| %s%s" doc n.gc.c_doc n.gc.c_name
          (String.concat ""
             (List.map (fun (x, t) -> Printf.sprintf " (%s : %s)" x t) (args n))))
      nodes;
    pf ft "@]@ @ namespace Node@ @ variable {T U : Type}@ @ ";
    let pat n xs = ctor_app n.gc.c_name xs in
    let names n = node_names p n in
    let kinds n = List.map arg_kind (n.gpayload @ n.goperands) in
    pf ft "/-- The node with its children mapped by `f`. -/@ ";
    pf ft "@[<v 2>def map (f : T → U) : Node T → Node U";
    List.iter
      (fun n ->
        let xs = names n in
        pf ft "@ | %s => %s" (pat n xs)
          (ctor_app n.gc.c_name
             (List.map2
                (fun x k ->
                  match k with
                  | `Child -> "(f " ^ x ^ ")"
                  | `Children -> "(" ^ x ^ ".map f)"
                  | `Value _ -> x)
                xs (kinds n))))
      nodes;
    pf ft "@]@ @ ";
    pf ft "/-- Every child of the node satisfies `P`. -/@ ";
    pf ft "@[<v 2>def All (P : T → Prop) : Node T → Prop";
    List.iter
      (fun n ->
        let xs = names n in
        let conj =
          List.concat
            (List.map2
               (fun x k ->
                 match k with
                 | `Child -> [ "P " ^ x ]
                 | `Children -> [ "(∀ y ∈ " ^ x ^ ", P y)" ]
                 | `Value _ -> [])
               xs (kinds n))
        in
        pf ft "@ | %s => %s" (pat n xs)
          (if conj = [] then "True" else String.concat " ∧ " conj))
      nodes;
    pf ft "@]@ @ ";
    pf ft
      "/-- The nodes have the same arguments, and their children are related \
       by `R`. -/@ ";
    pf ft "@[<v 2>def Rel (R : T → U → Prop) : Node T → Node U → Prop";
    List.iter
      (fun n ->
        let xs = names n in
        let ys = List.map (fun x -> x ^ "'") xs in
        let conj =
          List.concat
            (List.map2
               (fun (x, y) k ->
                 match k with
                 | `Child -> [ Printf.sprintf "R %s %s" x y ]
                 | `Children -> [ Printf.sprintf "Kanon.Forall₂ R %s %s" x y ]
                 | `Value _ -> [ Printf.sprintf "%s = %s" x y ])
               (List.combine xs ys) (kinds n))
        in
        pf ft "@ | %s, %s => %s" (pat n xs) (pat n ys)
          (if conj = [] then "True" else String.concat " ∧ " conj))
      nodes;
    if List.length nodes > 1 then pf ft "@ | _, _ => False";
    pf ft "@]@ @ end Node@ @ ")

(** The modules among [m] and those it uses that have sorts: the embeddings of
    their sorts are the parameters of the typing of the nodes of [m]. *)
let sort_mods m = List.filter has_sorts (closure m)

(** The invariant of a sort or a node ([[@lean_inv "P"]]), if it has one. *)
let inv_of (c : constr) = List.assoc_opt c.c_name !lang.lean_invs

(** The pairs of modules among [m] and those it uses whose nodes (or sorts)
    are told apart in the class [Lang] of [m]: those that no module that [m]
    uses tells apart. *)
let disjoint_pairs has m =
  let cl = List.filter has (closure m) in
  let provided a b =
    List.exists
      (fun d -> d <> m && List.mem a (closure d) && List.mem b (closure d))
      cl
  in
  List.concat_map
    (fun a ->
      List.filter_map
        (fun b -> if a <> b && not (provided a b) then Some (a, b) else None)
        cl)
    cl

(** [Lang.lean]: the typing of the nodes of [m], and what the module needs of a
    language. *)
let lang_file ctx (p : program) m =
  let r = module_root m in
  let nodes = module_nodes m and sorts = module_sorts m in
  let deps = List.filter (( <> ) m) (lang_mods m) in
  lean_file ~sources:(module_sources m) r [ "Lang" ]
    ([ r ^ ".Node"; r ^ ".Sem"; "KanonCore.Proof" ]
    @ List.map (fun d -> module_root d ^ ".Lang") deps)
  @@ fun ft ->
  let sparams = List.map sort_param (sort_mods m) in
  (* the typing *)
  if nodes <> [] then (
    pf ft
      "/-- The typing of the nodes of the module, at the sorts of a language \
       (by the embeddings@ of the sorts of the modules), given the types of \
       their children (`ty`). -/@ ";
    pf ft "@[<v 2>def Node.wt {T Ty : Type} %s(ty : T → Ty) : Node T → Ty → Prop"
      (String.concat ""
         (List.map2
            (fun s d -> Printf.sprintf "(%s : %s.Srt → Ty) " s (module_root d))
            sparams (sort_mods m)));
    in_typing := true;
    Fun.protect ~finally:(fun () -> in_typing := false) @@ fun () ->
    with_self m @@ fun () ->
    List.iter
      (fun n ->
        let xs = node_names p n in
        let ops = List.filteri (fun i _ -> i >= List.length n.gpayload) xs in
        let nary =
          List.exists (function TList TTerm -> true | _ -> false) n.goperands
        in
        let typing =
          match node_typing p n with
          | None -> []
          | Some ty when nary ->
              [
                Printf.sprintf "(∃ e, (%s) ∧ ∀ x ∈ %s, ty x = e)"
                  (typing_rhs ~names:[ "e"; "t" ] ctx ty)
                  (List.hd ops);
              ]
          | Some ty ->
              [
                "("
                ^ typing_rhs
                    ~names:(List.map (fun a -> "ty " ^ a) ops @ [ "t" ])
                    ctx ty
                ^ ")";
              ]
        in
        let inv (c : constr) =
          Option.map
            (fun q ->
              if constr_module c <> m then
                unsupported c.c_loc
                  "the invariant of %s on the nodes of another module"
                  c.c_name;
              Printf.sprintf "%s %s" q (ctor_app n.gc.c_name xs))
            (inv_of c)
        in
        let sort_inv =
          match node_typing p n with
          | Some ty -> (
              match (List.hd (List.rev ty.t_sorts)).e with
              | EConstr (c, _) -> inv c
              | _ -> None)
          | None -> None
        in
        let conj =
          typing @ Option.to_list (inv n.gc) @ Option.to_list sort_inv
        in
        pf ft "@ | %s, t => %s" (ctor_app n.gc.c_name xs)
          (if conj = [] then "True" else String.concat " ∧ " conj))
      nodes;
    pf ft "@]@ @ ");
  (* the class *)
  let node_of d = if d = m then "node" else module_root d ^ ".Lang.node" in
  let srt_of d = if d = m then "srt" else module_root d ^ ".Lang.srt" in
  let wt_args () =
    String.concat ""
      (List.map (fun d -> srt_of d ^ ".inj ") (sort_mods m))
  in
  pf ft
    "/-- What the module needs of a language `S`: its nodes and sorts embedded \
     in the terms and types@ of `S`, which types and evaluates them as the \
     module says. -/@ ";
  pf ft "@[<v 2>class Lang (S : Kanon.Sem)%s extends Values S.toDom where"
    (String.concat ""
       (List.map (fun d -> Printf.sprintf " [%s.Lang S]" (module_root d)) deps));
  if nodes <> [] then pf ft "@ node : Kanon.NodeEmbed Node S";
  if sorts <> [] then pf ft "@ srt : Kanon.Embed Srt S.Ty";
  if nodes <> [] then (
    pf ft
      "@ WT_inj : ∀ n t, S.WT (node.inj n t) ↔ Node.wt %sS.ty n t ∧ n.All S.WT"
      (wt_args ());
    pf ft
      "@ ev_inj : ∀ ρ n t, S.ev ρ (node.inj n t) = Node.eval ρ t (n.map (S.ev \
       ρ))");
  List.iter
    (fun (a, b) ->
      pf ft "@ proj_%s_inj_%s : ∀ n t, %s.proj (%s.inj n t) = none" a b
        (node_of a) (node_of b))
    (disjoint_pairs has_nodes m);
  List.iter
    (fun (a, b) ->
      pf ft "@ sortProj_%s_inj_%s : ∀ s, %s.proj (%s.inj s) = none" a b
        (srt_of a) (srt_of b))
    (disjoint_pairs has_sorts m);
  pf ft "@]@ @ ";
  (* the lemmas *)
  pf ft "section@ @ variable {S : Kanon.Sem}%s [L : Lang S]@ @ "
    (String.concat ""
       (List.map (fun d -> Printf.sprintf " [%s.Lang S]" (module_root d)) deps));
  let wt_args = wt_args () in
  if nodes <> [] then (
    pf ft
      "/-- The term of a node of the module. -/@ abbrev mk (n : Node S.Term) \
       (t : S.Ty) : S.Term := L.node.inj n t@ @ ";
    pf ft
      "/-- The node of the module that a term is, if it is one. -/@ abbrev \
       proj (e : S.Term) : Option (Node S.Term) := L.node.proj e@ @ ";
    pf ft
      "@@[simp, kanon_wt] theorem ty_mk (n : Node S.Term) (t : S.Ty) : S.ty \
       (mk n t) = t :=@   L.node.ty_inj n t@ @ ";
    pf ft
      "@@[kanon_wt] theorem WT_mk (n : Node S.Term) (t : S.Ty) :@   S.WT (mk n \
       t) ↔ Node.wt %sS.ty n t ∧ n.All S.WT :=@   L.WT_inj n t@ @ "
      (String.concat ""
         (List.map
            (fun d ->
              if d = m then "L.srt.inj " else module_root d ^ ".Lang.srt.inj ")
            (sort_mods m)));
    pf ft
      "@@[kanon_ev] theorem ev_mk (ρ : S.Env) (n : Node S.Term) (t : S.Ty) \
       :@   S.ev ρ (mk n t) = Node.eval ρ t (n.map (S.ev ρ)) :=@   L.ev_inj \
       ρ n t@ @ ";
    pf ft
      "@@[simp] theorem proj_mk (n : Node S.Term) (t : S.Ty) : proj (mk n t) = \
       some n :=@   L.node.proj_inj n t@ @ ";
    pf ft
      "@@[simp] theorem mk_inj_iff {n n' : Node S.Term} {t t' : S.Ty} :@   mk \
       n t = mk n' t' ↔ n = n' ∧ t = t' :=@   L.node.inj_eq_iff@ @ ");
  ignore wt_args;
  if sorts <> [] then (
    pf ft
      "/-- The sort of the language of a sort of the module. -/@ abbrev sort \
       (s : Srt) : S.Ty := L.srt.inj s@ @ ";
    pf ft
      "/-- The sort of the module that a sort is, if it is one. -/@ abbrev \
       sortProj (τ : S.Ty) : Option Srt := L.srt.proj τ@ @ ";
    pf ft
      "@@[simp] theorem sortProj_sort (s : Srt) : sortProj (S := S) (sort s) = \
       some s :=@   L.srt.proj_inj s@ @ ";
    pf ft
      "@@[simp] theorem sort_inj_iff {s s' : Srt} : sort (S := S) s = sort s' ↔ \
       s = s' :=@   L.srt.inj_eq_iff@ @ ";
    pf ft
      "/-- Equations of sorts, oriented. -/@ @@[simp, kanon_wt] theorem \
       sort_eq_ty {s : Srt} {x : S.Term} : sort s = S.ty x ↔ S.ty x = sort s \
       :=@   eq_comm@ @ ");
  List.iter
    (fun (a, b) ->
      let ra = module_root a and rb = module_root b in
      pf ft
        "@@[simp] theorem proj_%s_mk_%s (n : %s.Node S.Term) (t : S.Ty) :@   \
         %s.proj (%s.mk n t) = none :=@   L.proj_%s_inj_%s n t@ @ "
        a b rb ra rb a b)
    (disjoint_pairs has_nodes m);
  List.iter
    (fun (a, b) ->
      let ra = module_root a and rb = module_root b in
      pf ft
        "@@[simp] theorem sortProj_%s_sort_%s (s : %s.Srt) :@   %s.sortProj \
         (%s.sort s) = none :=@   L.sortProj_%s_inj_%s s@ @ "
        a b rb ra rb a b;
      pf ft
        "@@[simp] theorem sort_%s_ne_%s (s : %s.Srt) (s' : %s.Srt) :@   \
         %s.sort (S := S) s ≠ %s.sort s' := fun h => by@   have := \
         sortProj_%s_sort_%s s'; rw [← h] at this; simp at this@ @ "
        a b ra rb ra rb a b)
    (disjoint_pairs has_sorts m);
  if nodes <> [] then (
    let wt = Fmt.str "Node.wt %sS.ty" (String.concat "" (List.map (fun d -> if d = m then "L.srt.inj " else module_root d ^ ".Lang.srt.inj ") (sort_mods m))) in
    pf ft
      "/-- Refined children: the node is typed and evaluated as refined. -/@ \
       theorem Node.rel_refines {n n' : Node S.Term} (h : n.Rel S.Refines n') \
       (w : n.All S.WT) :@   n'.All S.WT ∧ (∀ t, %s n t → %s n' t) ∧@     ∀ \
       ρ, (n.map (S.ev ρ)).Rel Kanon.Sem.OLe (n'.map (S.ev ρ)) := by@   cases \
       n <;> cases n' <;> simp only [Node.Rel, Node.All, Node.wt, Node.map] at \
       h w ⊢ <;>@     kanon_rel_refines@ @ "
      wt wt;
    pf ft
      "/-- Refining the children of a node refines it, at the same sort \
       (when it is well-typed). -/@ @@[kanon_congr_lemma] theorem mk_congr \
       {n n' : Node S.Term} {t t' : S.Ty} (h : n.Rel S.Refines n')@     (ht : \
       S.WT (mk n t) → t' = t) : S.Refines (mk n t) (mk n' t') := by@   \
       refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> \
       obtain rfl := (ht w).symm <;>@     rw [WT_mk] at w@   · obtain ⟨h1, h2, -⟩ := \
       Node.rel_refines h w.2@     exact ⟨(WT_mk _ _).2 ⟨h2 t w.1, h1⟩, by \
       simp only [ty_mk]⟩@   · rw [ev_mk] at e ⊢@     exact Node.eval_mono ρ t \
       ((Node.rel_refines h w.2).2.2 ρ) v e@ @ ");
  pf ft "end@ @ ";
  if nodes <> [] then
    pf ft
      "attribute [kanon_wt] Node.wt Node.All@ attribute [kanon_ev] Node.map \
       Node.eval@ attribute [kanon_rel] Node.Rel@ @ ";
  if sorts <> [] then (
    pf ft
      "/-- The values of the terms of the sorts of the module, in a language \
       `S`: those that the module@ gives its sorts (`Srt.val`). Each \
       language proves it. -/@ @[<v 2>class Typed (S : Kanon.Sem)%s [Lang \
       S] : Prop where@ ev_sort : ∀ ρ e v (s : Srt), S.WT e → S.ty e = \
       sort s → S.ev ρ e = some v →@   Srt.val s v@]@ @ "
      (String.concat ""
         (List.map (fun d -> Printf.sprintf " [%s.Lang S]" (module_root d)) deps));
    pf ft
      "/-- The values of a well-typed term of a sort of the module. -/@ \
       @@[kanon_atom_cases] theorem ev_cases {S : Kanon.Sem}%s [Lang S] \
       [Typed S] {ρ : S.Env}@     {e : S.Term} {s : Srt} (w : S.WT e) (h : \
       S.ty e = sort s) :@   S.ev ρ e = none ∨ ∃ v, S.ev ρ e = some v ∧ \
       Srt.val s v := by@   rcases he : S.ev ρ e with _ | v@   · exact .inl \
       rfl@   · exact .inr ⟨v, rfl, Typed.ev_sort ρ e v s w h he⟩@ @ \
       attribute [kanon_val] Srt.val@ @ "
      (String.concat ""
         (List.map (fun d -> Printf.sprintf " [%s.Lang S]" (module_root d)) deps)))

(** The parameter a recursive helper recurses on: the first variable its body
    matches on. *)
let rec decreasing (f : fn) (e : expr) =
  match e.e with
  | ELet (_, _, b) | EAssert (_, b) | ELetFun (_, _, _, b) -> decreasing f b
  | EMatch (scruts, _) ->
      List.find_map
        (fun (s : expr) ->
          match s.e with
          | EVar x when List.mem_assoc x f.params -> Some x
          | _ -> None)
        scruts
  | _ -> None

let fn_def ctx ft (f : fn) ~o ~recursive =
  pf ft "%a@[<v 2>def %s%s %a : %a :=@ %a@]@ " doc f.fdoc (qn f.name)
    (if o then " (O : Ops S)" else "")
    params f lean_ty f.ret (expr ctx) f.body;
  (if recursive then
     match decreasing f f.body with
     | Some x when List.assoc x f.params = TTerm ->
         unsupported f.floc "%s: a recursion on terms" f.name
     | Some x ->
         pf ft
           "termination_by sizeOf %s@ decreasing_by all_goals ((try simp_wf) <;> \
            omega)@ "
           (id x)
     | None -> ());
  pf ft "@ "

(** The calls of [e] to the rule functions, oracles, extensible helpers and
    helpers that need them, if any. *)
let calls_o ctx (e : expr) =
  List.exists
    (fun g ->
      is_oracle ctx g
      ||
      match List.assoc_opt g ctx.kinds with
      | Some (Rule | OHelper | Ext) -> true
      | _ -> false)
    (Gen_ocaml.calls [] e)

(** [Model.lean]: the record [Ops] of the rule functions, oracles and
    extensible helpers of [m], its specs, helpers, rules, and what the proofs
    assume of the model ([Ops.Sound]). *)
let model_file ctx (p : program) m =
  ignore p;
  let r = module_root m in
  let parents = ops_parents m in
  let rules = module_fns ctx m [ Rule ] in
  let oracles = module_oracles ctx m in
  let exts = module_fns ctx m [ Ext ] in
  let imports =
    (if has_lang m then [ r ^ ".Lang" ] else [])
    @ (if !has_file r [ "Sem" ] then [ r ^ ".Sem" ] else [])
    @ (if !has_file r [ "Prims" ] then [ r ^ ".Prims" ] else [])
    @ List.map (fun d -> module_root d ^ ".Model") parents
    @ types_imports (closure m)
    @ [ "KanonCore.Model"; "KanonCore.Attr"; "KanonCore.Embed" ]
  in
  lean_file ~sources:(module_sources m) r [ "Model" ] imports @@ fun ft ->
  with_self m @@ fun () ->
  pf ft
    "/-- The rule functions, oracles and extensible helpers of the module, in \
     the model of a@ language. -/@ ";
  pf ft "@[<v 2>structure Ops (S : Kanon.Sem) extends %s"
    (match parents with
    | [] -> "Kanon.OpsBase S"
    | ps ->
        String.concat ", "
          (List.map
             (fun d ->
               Printf.sprintf "%s : %s.Ops S" (ops_parent d) (module_root d))
             ps));
  if rules <> [] || oracles <> [] || exts <> [] then pf ft " where";
  List.iter
    (fun f -> pf ft "@ %a%s : %a" doc f.fdoc (fld f.name) arrow f)
    (rules @ exts);
  List.iter
    (fun (q : prim) ->
      pf ft "@ %a%s : %a%a" doc q.pdoc (fld q.pname)
        (fun ft () -> List.iter (fun t -> pf ft "%a → " lean_ty t) q.pargs)
        () lean_ty q.pret)
    oracles;
  pf ft "@]@ @ ";
  variables ft m;
  (* the helpers *)
  let helpers =
    Gen_ocaml.sccs
      (List.filter
         (fun (f : fn) ->
           module_of_name f.name = Some m
           && List.mem (fn_kind ctx f.name) [ Pure; OHelper ])
         ctx.fns)
  in
  List.iter
    (fun group ->
      let o = fn_kind ctx (List.hd group).name = OHelper in
      match group with
      | [ f ] when not (Gen_ocaml.is_recursive [ f ]) ->
          fn_def ctx ft f ~o ~recursive:false
      | _ ->
          pf ft "mutual@ @ ";
          List.iter (fn_def ctx ft ~o ~recursive:true) group;
          pf ft "end@ @ ")
    helpers;
  let plain =
    List.filter_map
      (function
        | [ f ] when not (Gen_ocaml.is_recursive [ f ]) -> Some f | _ -> None)
      helpers
  in
  if plain <> [] then
    pf ft "@[<hv 2>attribute [kanon_body]%a@]@ @ "
      (fun ft -> List.iter (fun (f : fn) -> pf ft "@ %s" (qn f.name)))
      plain;
  (* the cases of extensible helpers *)
  List.iter
    (fun (f : fn) ->
      if fn_kind ctx f.name = Ext then (
        let scruts, _, last = ext_cases f in
        List.iter
          (fun (name, (c : case)) ->
            if calls_o ctx c.body || Option.fold ~none:false ~some:(calls_o ctx) c.guard
            then
              unsupported c.cloc
                "a case of the extensible helper %s that calls a rule function, \
                 an oracle or an extensible helper"
                f.name;
            pf ft "@[<v 2>def %s.%s %a : Option %a :=@ %a@]@ @ " (qn f.name) name
              params f lean_ty f.ret (case_alt ctx scruts) c;
            pf ft "attribute [kanon_body] %s.%s@ @ " (qn f.name) name)
          (module_ext_cases m f);
        if module_of_name f.name = Some m then
          pf ft "@[<v 2>def %s.default %a : %a :=@ %a@]@ @ " (qn f.name) params
            f lean_ty f.ret
            (fun ft () ->
              nest ft
                ( translate ctx scruts last,
                  fun ft () ->
                    binding (pat_names last.pat) (fun () ->
                        expr ctx ft last.body) ))
            ();
        if module_of_name f.name = Some m then
          pf ft "attribute [kanon_body] %s.default %s.post@ @ " (qn f.name)
            (qn f.name)))
    ctx.fns;
  (* the specs *)
  List.iter
    (fun f ->
      pf ft "%a@[<v 2>def %s.spec %a : S.Term :=@ %a@]@ @ " doc f.fdoc
        (qn f.name) params f (expr ctx) (Option.get f.spec))
    rules;
  if rules <> [] then
    pf ft "@[<v 2>attribute [kanon_spec]%a@]@ @ "
      (fun ft -> List.iter (fun f -> pf ft "@ %s.spec" (qn f.name)))
      rules;
  (* the rules *)
  List.iter
    (fun f -> List.iter (rule_def ctx ft f) (module_rules m f))
    (rule_fns ctx);
  (* soundness *)
  pf ft
    "/-- What the proofs assume of the model: its rule functions refine their \
     specs, its oracles@ and extensible helpers do what they are assumed to \
     do. -/@ ";
  pf ft "@[<v 2>structure Ops.Sound (O : Ops S) : Prop%s"
    (match parents with
    | [] -> ""
    | ps ->
        " extends "
        ^ String.concat ", "
            (List.map
               (fun d ->
                 Printf.sprintf "%s : %s.Ops.Sound O.%s" (sound_parent d)
                   (module_root d) (ops_parent d))
               ps));
  if rules <> [] || oracles <> [] || exts <> [] then pf ft " where";
  List.iter
    (fun f ->
      pf ft "@ %s : ∀ %a, %aS.Refines (%s.spec %a) (O.%s %a)" (fld f.name) params
        f pre_arrows f (qn f.name) args f (fld f.name) args f;
      Option.iter
        (fun post ->
          pf ft "@ %s_post : ∀ %a, %a%s (O.%s %a)" (fld f.name) params f
            pre_arrows f
            (pre_prop ~text:Fun.id ("", post, false)
            |> String.trim)
            (fld f.name) args f)
        (postcondition f))
    rules;
  if oracles <> [] then
    pf ft "@ %s_orc : Oracle.Compat %s" (String.uncapitalize_ascii m)
      (String.concat " "
         (List.map (fun (q : prim) -> "O." ^ fld q.pname) oracles));
  List.iter
    (fun f ->
      pf ft "@ %s : ∀ %a, %s.post %a (O.%s %a)" (fld f.name) params f
        (qn f.name) args f (fld f.name) args f)
    exts;
  pf ft "@]@ @ "

(** The Lean name of the predicate [p] of a subsort. *)
let pred_ref p = String.trim (pre_prop ~text:(fun _ -> "") ("", p, false))

(** The user functions that [e] calls. *)
let rec calls (e : expr) =
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> []
  | ECall (f, l) -> f :: List.concat_map calls l
  | EConstr (_, l) | ELocalCall (_, l) | ETuple l | EArray l ->
      List.concat_map calls l
  | ENode (a, b) | EBinop (_, a, b) | ECons (a, b) | EAssert (a, b) ->
      calls a @ calls b
  | EUnop (_, a) | ESome a | EField (a, _) -> calls a
  | EIf (a, b, c) -> calls a @ calls b @ calls c
  | ERecord l -> List.concat_map (fun (_, e) -> calls e) l
  | ELet (_, a, b) | ELetFun (_, _, a, b) -> calls a @ calls b
  | EMatch (scruts, cases) ->
      List.concat_map calls scruts
      @ List.concat_map
          (fun (c : case) ->
            Option.fold ~none:[] ~some:calls c.guard @ calls c.body)
          cases

(** The statement of an arm, of the module [m]: under its guard, the spec at
    the matched arguments is refined by the body (or, for [post], the body
    satisfies the postcondition of [f]). *)
let arm_stmt ?(post = false) ctx m ft f r arms i (a : arm) =
  let c = a.a_case in
  let with_subst s k =
    subst := s;
    Fun.protect ~finally:(fun () -> subst := []) k
  in
  pf ft "@[<v 2>def %s%s.Stmt : Prop :=@ ∀ %s (O : Ops S), O.Sound →@ "
    (arm_name f r arms i)
    (if post then ".post" else "")
    (lang_binders m);
  if a.a_binders <> [] then
    pf ft "∀ %a,@ "
      (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %s)" x t))
      a.a_binders;
  List.iter
    (fun pre ->
      pf ft "%s →@ "
        (with_subst
           (List.map (fun (x, (t, _)) -> (x, t)) a.a_subst)
           (fun () ->
             pre_prop
               ~text:(fun x ->
                 Fmt.str "%a" (expr ctx) { c.body with e = EVar x })
               pre)))
    (preconditions f);
  let lets =
    List.map
      (fun (x, rhs) ->
        ( x,
          with_subst
            (List.map (fun (x, (t, _)) -> (x, t)) a.a_subst)
            (fun () -> Fmt.str "%a" (expr ctx) rhs) ))
      a.a_lets
  in
  let a = { a with a_body_subst = a.a_body_subst @ lets } in
  with_subst a.a_body_subst (fun () ->
      Option.iter (fun g -> pf ft "%a = true →@ " (expr ctx) g) c.guard);
  let spec_args =
    with_subst
      (List.map (fun (x, (t, _)) -> (x, t)) a.a_subst)
      (fun () ->
        List.map
          (fun (x, _) -> Fmt.str "%a" (expr ctx) { c.body with e = EVar x })
          f.params)
  in
  let body ft () = with_subst a.a_body_subst (fun () -> expr ctx ft c.body) in
  if post then
    pf ft "%s@ (%a)@]@ @ "
      (pred_ref (Option.get (postcondition f)))
      body ()
  else
    pf ft "S.Refines (%s.spec %s)@ (%a)@]@ @ " (fn_ref f.name)
      (String.concat " " spec_args)
      body ()

(** The rule functions of [m] and of the modules it uses. *)
let visible_rules ctx m =
  List.filter
    (fun (f : fn) ->
      List.mem (Option.get (module_of_name f.name)) (closure m))
    (rule_fns ctx)

(** [Statements.lean]: the lifting lemmas of the rule functions that [m] sees,
    and the statements of the commutativity of its operators, of its arms, of
    the postconditions and of the cases of extensible helpers. *)
let statements_file ctx m =
  let r = module_root m in
  let parents = ops_parents m in
  lean_file ~sources:(module_sources m) r [ "Statements" ]
    ([ r ^ ".Model"; "KanonCore.Proof" ]
    @ List.map (fun d -> module_root d ^ ".Statements") parents)
  @@ fun ft ->
  with_self m @@ fun () ->
  (* the lifting lemmas *)
  pf ft "namespace Lib@ @ variable %s {O : Ops S}@ @ " (lang_binders m);
  List.iter
    (fun (f : fn) ->
      let term (_, t) = t = TTerm in
      let prime (x, t) = if term (x, t) then id x ^ "'" else id x in
      let helpers =
        List.filter
          (fun g ->
            List.exists
              (fun (h : fn) -> h.name = g && fn_kind ctx g = Pure)
              ctx.fns)
          (calls (Option.get f.spec))
        |> List.sort_uniq compare |> List.map fn_ref
      in
      pf ft "@[<v 2>theorem lift_%s (hO : O.Sound)" (fld f.name);
      List.iter
        (fun (x, t) ->
          if term (x, t) then pf ft " {%s %s' : S.Term}" (id x) (id x)
          else pf ft " {%s : %a}" (id x) lean_ty t)
        f.params;
      List.iter
        (fun (x, t) ->
          if term (x, t) then
            pf ft "@ (h_%s : S.Refines %s %s')" x (id x) (id x))
        f.params;
      pre_binders
        ~rename:(fun x ->
          if term (x, List.assoc x f.params) then x ^ "'" else x)
        ft f;
      pf ft " :@ S.Refines (%s.spec %s) (O.%s %s) :=@ " (fn_ref f.name)
        (String.concat " " (List.map (fun (x, _) -> id x) f.params))
        (fld f.name)
        (String.concat " " (List.map prime f.params));
      let fm = Option.get (module_of_name f.name) in
      if fm <> m then
        pf ft "%s.Lib.lift_%s (O := O%s) hO%s%s%a@]@ @ " (module_root fm)
          (fld f.name) (ops_path m fm)
          (ops_path ~sound:true m fm)
          (String.concat ""
             (List.filter_map
                (fun (x, t) -> if term (x, t) then Some (" h_" ^ x) else None)
                f.params))
          pre_names f
      else if List.exists term f.params then
        pf ft
          "Kanon.Sem.Refines.trans (by simp only [%s]; kanon_congr) (hO.%s \
           %s%a)@]@ @ "
          (String.concat ", " ("kanon_spec" :: helpers))
          (fld f.name)
          (String.concat " " (List.map prime f.params))
          pre_names f
      else
        pf ft "hO.%s %s%a@]@ @ " (fld f.name)
          (String.concat " " (List.map prime f.params))
          pre_names f)
    (visible_rules ctx m);
  pf ft "end Lib@ @ ";
  (* commutativity *)
  List.iter
    (fun n ->
      let xs =
        List.mapi (fun i _ -> Printf.sprintf "x%d" (i + 1)) n.gpayload
      in
      pf ft
        "/-- The operands of `%s` commute. -/@ @[<v 2>def %s.comm.Stmt : Prop \
         :=@ ∀ %s %s(a b : S.Term) (t : S.Ty),@ S.Refines %s@ %s@]@ @ "
        n.gc.c_name n.gc.c_name (lang_binders m)
        (String.concat ""
           (List.map2
              (fun x t -> Printf.sprintf "(%s : %s) " x (ty_str t))
              xs n.gpayload))
        (node_term n.gc (xs @ [ "a"; "b" ]) "t")
        (node_term n.gc (xs @ [ "b"; "a" ]) "t"))
    (module_comm m);
  (* the arms *)
  List.iter
    (fun f ->
      List.iter
        (fun (r, arms) ->
          List.iteri
            (fun i a ->
              if case_module f a.a_case = m then (
                arm_stmt ctx m ft f r arms i a;
                if postcondition f <> None then
                  arm_stmt ~post:true ctx m ft f r arms i a))
            arms)
        (module_arms m f))
    (rule_fns ctx);
  (* the postconditions of the specs *)
  List.iter
    (fun f ->
      Option.iter
        (fun post ->
          pf ft
            "/-- The spec of `%s` satisfies `%s`. -/@ @[<v 2>def \
             %s.spec_post.Stmt : Prop :=@ ∀ %s, ∀ %a, %a%s (%s.spec %a)@]@ @ "
            f.name post (qn f.name) (lang_binders m) params f pre_arrows f
            (pred_ref post) (qn f.name) args f)
        (postcondition f))
    (module_fns ctx m [ Rule ]);
  (* the cases of the extensible helpers *)
  List.iter
    (fun (f : fn) ->
      if fn_kind ctx f.name = Ext then (
        List.iter
          (fun (name, _) ->
            pf ft
              "@[<v 2>def %s.%s.Stmt : Prop :=@ ∀ %s, ∀ %a (r : %a), %s.%s %a = \
               some r →@ %s.post %a r@]@ @ "
              (qn f.name) name (lang_binders m) params f lean_ty f.ret
              (qn f.name) name args f (fn_ref f.name) args f)
          (module_ext_cases m f);
        if module_of_name f.name = Some m then
          pf ft
            "@[<v 2>def %s.default.Stmt : Prop :=@ ∀ %s, ∀ %a, %s.post %a \
             (%s.default %a)@]@ @ "
            (qn f.name) (lang_binders m) params f (qn f.name) args f
            (qn f.name) args f))
    ctx.fns

(** The proof of the arm [a] of the rule [r] of [f], of the module [m]: by
    [kanon_proof%], or from the arm it is derived from by commutativity. *)
let arm_proof m ft (f : fn) r arms i (a : arm) =
  let hb = heartbeats (Some f) in
  let derived = if preconditions f = [] then derived_from f arms a else None in
  match derived with
  | None ->
      pf ft
        "%ttheorem %s.ok : %s.Stmt :=@   no_implicit_lambda%% (kanon_proof%% \
         %s)@ @ "
        hb (arm_name f r arms i) (arm_name f r arms i) (arm_name f r arms i)
  | Some (b, args, top, nested, swapped) ->
      let j =
        let rec find k = function
          | x :: _ when x == b -> k
          | _ :: l -> find (k + 1) l
          | [] -> assert false
        in
        find 0 arms
      in
      let hg = if a.a_case.guard = None then "" else " hg" in
      let term q =
        let t, _, _ = pat_term q in
        t
      in
      let comm (o : constr) =
        Printf.sprintf "%s.%s.comm.ok .." (constr_root o) o.c_name
      in
      pf ft "%t@[<v 2>theorem %s.ok : %s.Stmt := by@ intro S%s O hO%a%s@ " hb
        (arm_name f r arms i) (arm_name f r arms i)
        (String.concat ""
           (List.map (fun _ -> " _")
              (lang_mods m @ List.filter has_sorts (lang_mods m))))
        (fun ft -> List.iter (fun (x, _) -> pf ft " %s" x))
        a.a_binders hg;
      (* each swapped node of [a] refines that of [b], inner ones first: by
         commutativity, and congruence for the swaps inside *)
      List.iter
        (fun ((qa : pat), qb, o) ->
          let inner =
            List.exists
              (fun ((qa' : pat), _, _) ->
                qa'.pid <> qa.pid && List.mem qa'.pid (pids qa))
              nested
          in
          pf ft "@[<hv 2>have : S.Refines %s@ %s :=@ " (term qa) (term qb);
          if inner then
            pf ft "Kanon.Sem.Refines.trans (%s) (by kanon_congr)@]@ " (comm o)
          else pf ft "%s@]@ " (comm o))
        nested;
      if swapped then
        pf ft
          "@[<hv 2>refine Kanon.Sem.Refines.trans ?_@ (Kanon.Sem.Refines.trans \
           (%s.ok O hO%a%s)@ (by (try dsimp only); (repeat' apply \
           Kanon.Refinement.ite_congr) <;> first | exact \
           Kanon.Sem.Refines.refl | kanon_comm))@]@ "
          (arm_name f r arms j)
          (fun ft -> List.iter (pf ft " %s"))
          args hg
      else
        pf ft "@[<hv 2>refine Kanon.Sem.Refines.trans ?_@ (%s.ok O hO%a%s)@]@ "
          (arm_name f r arms j)
          (fun ft -> List.iter (pf ft " %s"))
          args hg;
      pf ft "simp only [%s.spec, Kanon.NodeEmbed.ty_inj]@ " (fn_ref f.name);
      Option.iter
        (fun o -> pf ft "refine Kanon.Sem.Refines.trans (%s) ?_@ " (comm o))
        top;
      pf ft "kanon_congr@]@ @ "

(** [Soundness.lean]: the proofs of the statements of [m], and of its rules. *)
let soundness_file ctx m =
  let r = module_root m in
  let comm_deps =
    List.filter
      (fun d -> d <> m && module_comm d <> [] && has_model ctx d)
      (closure m)
  in
  lean_file ~sources:(module_sources m) r [ "Soundness" ]
    (((r ^ ".Statements")
     :: (if !has_file r [ "Proofs" ] then [ r ^ ".Proofs" ] else []))
    @ List.map (fun d -> module_root d ^ ".Soundness") comm_deps)
  @@ fun ft ->
  with_self m @@ fun () ->
  List.iter
    (fun n ->
      pf ft
        "%t@@[kanon_comm_lemma] theorem %s.comm.ok : %s.comm.Stmt :=@   \
         no_implicit_lambda%% (kanon_proof%% %s.comm)@ @ "
        (heartbeats None) n.gc.c_name n.gc.c_name n.gc.c_name)
    (module_comm m);
  List.iter
    (fun (f : fn) ->
      let post = postcondition f in
      List.iter
        (fun (r, arms) ->
          List.iteri
            (fun i a ->
              if case_module f a.a_case = m then (
                arm_proof m ft f r arms i a;
                if post <> None then
                  pf ft "%ttheorem %s.post.ok : %s.post.Stmt :=@   \
                         no_implicit_lambda%% (kanon_proof%% %s.post)@ @ "
                    (heartbeats (Some f)) (arm_name f r arms i)
                    (arm_name f r arms i) (arm_name f r arms i)))
            arms)
        (module_arms m f);
      List.iter
        (fun (_, _, grp) ->
          let rule = rule_name f grp in
          let arms = List.assoc rule (arms f) in
          let n = Printf.sprintf "%s.r_%s" (qn f.name) (id rule) in
          let thm name concl suffix =
            pf ft
              "@[<v 2>theorem %s.%s %s (O : Ops S) (hO : O.Sound) %a%a (res : \
               S.Term)@   (h : %s O %a = some res) : %s := by@ simp only [%s] \
               at h@ repeat' (replace h := Kanon.orElse_some h; rcases h with h | h)"
              n name (lang_binders m) params f (pre_binders ?rename:None) f n
              args f concl n;
            List.iteri
              (fun i _ ->
                pf ft "@ · kanon_arm h (%s%s.ok O hO)" (arm_name f rule arms i)
                  suffix)
              arms;
            pf ft "@]@ @ "
          in
          thm "sound"
            (Fmt.str "S.Refines (%s.spec %a) res" (fn_ref f.name) args f)
            "";
          Option.iter
            (fun p -> thm "post_sound" (pred_ref p ^ " res") ".post")
            post)
        (module_rules m f))
    (rule_fns ctx);
  List.iter
    (fun f ->
      if postcondition f <> None then
        pf ft "%ttheorem %s.spec_post.ok : %s.spec_post.Stmt :=@   \
               no_implicit_lambda%% (kanon_proof%% %s.spec_post)@ @ "
          (heartbeats (Some f)) (qn f.name) (qn f.name) (qn f.name))
    (module_fns ctx m [ Rule ]);
  List.iter
    (fun (f : fn) ->
      if fn_kind ctx f.name = Ext then (
        List.iter
          (fun (name, _) ->
            let x = Printf.sprintf "%s.%s" (qn f.name) name in
            pf ft
              "%ttheorem %s.ok : %s.Stmt :=@   no_implicit_lambda%% \
               (kanon_proof%% %s)@ @ "
              (heartbeats None) x x x)
          (module_ext_cases m f);
        if module_of_name f.name = Some m then
          let x = qn f.name ^ ".default" in
          pf ft
            "%ttheorem %s.ok : %s.Stmt :=@   no_implicit_lambda%% \
             (kanon_proof%% %s)@ @ "
            (heartbeats None) x x x))
    ctx.fns

(* ---------------------------------------------------------------- *)
(* The files of a language *)

(** The constructor of the terms (or the sorts) of a language for the nodes (or
    sorts) of the module [m]: its name, uncapitalised. *)
let lang_ctor m = id (String.uncapitalize_ascii m)

(** [Syntax.lean]: the sorts and the terms of the language. *)
let syntax_file ~sources ms =
  let r = lang_root () in
  let sorted = List.filter has_sorts ms and noded = List.filter has_nodes ms in
  lean_file ~sources r [ "Syntax" ]
    (List.map (fun m -> module_root m ^ ".Node") (List.filter has_lang ms))
  @@ fun ft ->
  pf ft "/-- The sorts of the language: those of its modules. -/@ ";
  pf ft "@[<v 2>inductive Ty where";
  List.iter
    (fun m -> pf ft "@ | %s (s : %s.Srt)" (lang_ctor m) (module_root m))
    sorted;
  pf ft "@]@   deriving DecidableEq, Repr@ @ ";
  pf ft "/-- The terms of the language: the nodes of its modules, at a sort. -/@ ";
  pf ft "@[<v 2>inductive Term where";
  List.iter
    (fun m ->
      pf ft "@ | %s (n : %s.Node Term) (t : Ty)" (lang_ctor m) (module_root m))
    noded;
  pf ft "@]@ @ ";
  pf ft "/-- The sort of a term. -/@ @[<v 2>def Term.ty : Term → Ty@ | %s => t@]@ @ "
    (String.concat " | "
       (List.map (fun m -> "." ^ lang_ctor m ^ " _ t") noded));
  (match sorted with
  | m :: _ -> pf ft "instance : Inhabited Ty := ⟨.%s default⟩@ " (lang_ctor m)
  | [] -> ());
  (* a term: a node without children *)
  (match
     List.find_map
       (fun m ->
         List.find_map
           (fun n ->
             if List.exists uses_term (n.gpayload @ n.goperands) then None
             else
               Some
                 (Printf.sprintf ".%s %s default" (lang_ctor m)
                    (ctor_app n.gc.c_name
                       (List.map (fun _ -> "default") n.gpayload))))
           (module_nodes m))
       noded
   with
  | Some t -> pf ft "instance : Inhabited Term := ⟨%s⟩@ @ " t
  | None -> ())

(** [Semantics.lean]: the typing and the evaluation of the terms, by those of
    the modules, and the instances of the classes [Lang] of the modules, whose
    laws hold by definition. *)
let semantics_file ~sources (p : program) ms =
  let r = lang_root () in
  let noded = List.filter has_nodes ms in
  let langs = List.filter has_lang ms in
  let lists =
    List.exists
      (fun m ->
        List.exists
          (fun n -> List.mem (TList TTerm) (n.gpayload @ n.goperands))
          (module_nodes m))
      noded
  in
  lean_file ~sources r [ "Semantics" ]
    ((r ^ ".Val") :: List.map (fun m -> module_root m ^ ".Lang") langs)
  @@ fun ft ->
  let all m = "all" ^ m and evm m = "ev" ^ m in
  let children n =
    List.combine (node_names p n) (List.map arg_kind (n.gpayload @ n.goperands))
  in
  (* typing *)
  pf ft "mutual@ @ /-- The typing of the terms. -/@ @[<v 2>def Term.WT : Term → Prop";
  List.iter
    (fun m ->
      pf ft "@ | .%s n t => %s.Node.wt %sTerm.ty n t ∧ %s n" (lang_ctor m)
        (module_root m)
        (String.concat ""
           (List.map (fun d -> "Ty." ^ lang_ctor d ^ " ") (sort_mods m)))
        (all m))
    noded;
  pf ft "@]@ @ ";
  List.iter
    (fun m ->
      pf ft "@[<v 2>def %s : %s.Node Term → Prop" (all m) (module_root m);
      List.iter
        (fun n ->
          let ch = children n in
          let conj =
            List.filter_map
              (fun (x, k) ->
                match k with
                | `Child -> Some (x ^ ".WT")
                | `Children -> Some ("allList " ^ x)
                | `Value _ -> None)
              ch
          in
          pf ft "@ | %s => %s"
            (ctor_app n.gc.c_name (List.map fst ch))
            (if conj = [] then "True" else String.concat " ∧ " conj))
        (module_nodes m);
      pf ft "@]@ @ ")
    noded;
  if lists then
    pf ft
      "@[<v 2>def allList : List Term → Prop@ | [] => True@ | x :: xs => x.WT \
       ∧ allList xs@]@ @ ";
  pf ft "end@ @ ";
  (* evaluation *)
  pf ft
    "mutual@ @ /-- The evaluation of the terms. -/@ @[<v 2>def ev (ρ : Env) : \
     Term → Option Val";
  List.iter
    (fun m ->
      pf ft "@ | .%s n t => %s.Node.eval (D := dom) ρ t (%s ρ n)" (lang_ctor m)
        (module_root m) (evm m))
    noded;
  pf ft "@]@ @ ";
  List.iter
    (fun m ->
      pf ft "@[<v 2>def %s (ρ : Env) : %s.Node Term → %s.Node (Option Val)"
        (evm m) (module_root m) (module_root m);
      List.iter
        (fun n ->
          let ch = children n in
          pf ft "@ | %s => %s"
            (ctor_app n.gc.c_name (List.map fst ch))
            (ctor_app n.gc.c_name
               (List.map
                  (fun (x, k) ->
                    match k with
                    | `Child -> "(ev ρ " ^ x ^ ")"
                    | `Children -> "(evList ρ " ^ x ^ ")"
                    | `Value _ -> x)
                  ch)))
        (module_nodes m);
      pf ft "@]@ @ ")
    noded;
  if lists then
    pf ft
      "@[<v 2>def evList (ρ : Env) : List Term → List (Option Val)@ | [] => \
       []@ | x :: xs => ev ρ x :: evList ρ xs@]@ @ ";
  pf ft "end@ @ ";
  if lists then (
    pf ft
      "theorem allList_iff : ∀ l, allList l ↔ ∀ x ∈ l, Term.WT x@   | [] => \
       by simp [allList]@   | x :: xs => by simp [allList, allList_iff xs]@ @ ";
    pf ft
      "theorem evList_eq (ρ : Env) : ∀ l, evList ρ l = l.map (ev ρ)@   | [] \
       => rfl@   | x :: xs => by rw [evList, evList_eq ρ xs]; rfl@ @ ");
  List.iter
    (fun m ->
      let rm = module_root m in
      pf ft
        "theorem %s_iff (n : %s.Node Term) : %s n ↔ n.All Term.WT := by@   \
         cases n <;> simp [%s, %s.Node.All%s]@ @ "
        (all m) rm (all m) (all m) rm
        (if lists then ", allList_iff" else "");
      pf ft
        "theorem %s_eq (ρ : Env) (n : %s.Node Term) : %s ρ n = n.map (ev ρ) := \
         by@   cases n <;> simp only [%s, %s.Node.map%s]@ @ "
        (evm m) rm (evm m) (evm m) rm
        (if lists then ", evList_eq" else ""))
    noded;
  (* the semantics *)
  pf ft
    "/-- The semantics of the language. -/@ @[<v 2>@@[reducible] def sem : \
     Kanon.Sem where@ toDom := dom@ Term := Term@ ty := Term.ty@ WT := \
     Term.WT@ ev := ev@]@ @ ";
  pf ft
    "/-- The value of a term; `none` for poison. -/@ abbrev eval : Env → Term \
     → Option Val := sem.eval@ @ ";
  pf ft
    "/-- `r` refines `spec`: it has the same type, and the same value whenever \
     `spec` is not poison. -/@ abbrev Refines : Term → Term → Prop := \
     sem.Refines@ @ instance : Refinement Refines := Sem.refinement@ @ ";
  (* the instances *)
  let single l = List.length l < 2 in
  List.iter
    (fun m ->
      let rm = module_root m and c = lang_ctor m in
      pf ft "@[<v 2>instance inst%sLang : %s.Lang sem where" m rm;
      pf ft "@ toValues := inferInstanceAs (%s.Values dom)" rm;
      if has_nodes m then (
        pf ft
          "@ @[<v 2>node := {@ inj := .%s@ proj := fun e => match e with | \
           .%s n _ => some n%s@ ty_inj := fun _ _ => rfl@ proj_inj := fun _ _ \
           => rfl@ inj_proj := by intro e n h; cases e <;> cases h <;> rfl }@]"
          c c
          (if single noded then "" else " | _ => none");
        pf ft
          "@ WT_inj n t := by show (_ ∧ all%s n) ↔ _; rw [all%s_iff]; exact \
           Iff.rfl"
          m m;
        pf ft
          "@ ev_inj ρ n t := congrArg (%s.Node.eval (D := dom) ρ t) (ev%s_eq ρ \
           n)"
          rm m);
      if has_sorts m then
        pf ft
          "@ @[<v 2>srt := {@ inj := .%s@ proj := fun s => match s with | .%s \
           s => some s%s@ proj_inj := fun _ => rfl@ inj_proj := by intro b a h; \
           cases b <;> cases h <;> rfl }@]"
          c c
          (if single (List.filter has_sorts ms) then "" else " | _ => none");
      List.iter
        (fun (a, b) -> pf ft "@ proj_%s_inj_%s _ _ := rfl" a b)
        (disjoint_pairs has_nodes m);
      List.iter
        (fun (a, b) -> pf ft "@ sortProj_%s_inj_%s _ := rfl" a b)
        (disjoint_pairs has_sorts m);
      pf ft "@]@ @ ")
    langs

(** [Rules.lean]: the rule functions of the language, from the rules of its
    modules, its extensible helpers, from their cases, its oracles and what it
    assumes of them, and the proof that the model is sound. *)
let rules_file ~sources ctx ms =
  let r = lang_root () in
  let root = Option.get !root_module in
  let models = List.filter (has_model ctx) ms in
  lean_file ~sources r [ "Rules" ]
    (((r ^ ".Semantics")
     :: (if !has_file r [ "Typing" ] then [ r ^ ".Typing" ] else []))
    @ List.map (fun m -> module_root m ^ ".Soundness") models)
  @@ fun ft ->
  term_ty := "Term";
  sort_ty := "Ty";
  Fun.protect ~finally:(fun () ->
      term_ty := "S.Term";
      sort_ty := "S.Ty")
  @@ fun () ->
  let o_to m = "O" ^ ops_path root m and h_to m = "hO" ^ ops_path ~sound:true root m in
  let oracles =
    List.concat_map (fun m -> List.map (fun q -> (m, q)) (module_oracles ctx m)) models
  in
  pf ft
    "/-- The oracles that the model is parameterised by. -/@ @[<v 2>structure \
     Oracle where@ tag_le : Term → Term → Bool";
  List.iter
    (fun (_, (q : prim)) ->
      pf ft "@ %a%s : %a%a" doc q.pdoc (fld q.pname)
        (fun ft () -> List.iter (fun t -> pf ft "%a → " lean_ty t) q.pargs)
        () lean_ty q.pret)
    oracles;
  pf ft "@]@ @ ";
  let orc_mods = List.filter (fun m -> module_oracles ctx m <> []) models in
  pf ft
    "/-- What the proofs assume of the oracles: what each module assumes of \
     its own. -/@ @[<v 2>structure Oracle.Compat (orc : Oracle) : Prop";
  if orc_mods <> [] then pf ft " where";
  List.iter
    (fun m ->
      pf ft "@ %s : %s.Oracle.Compat (S := sem) %s" (String.uncapitalize_ascii m)
        (module_root m)
        (String.concat " "
           (List.map (fun (q : prim) -> "orc." ^ fld q.pname) (module_oracles ctx m))))
    orc_mods;
  pf ft "@]@ @ ";
  (* extensible helpers *)
  let exts = List.filter (fun (f : fn) -> fn_kind ctx f.name = Ext) ctx.fns in
  List.iter
    (fun (f : fn) ->
      let fm = Option.get (module_of_name f.name) in
      let _, cases, _ = ext_cases f in
      let alts =
        List.concat_map
          (fun m ->
            List.filter_map
              (fun (name, (c : case)) ->
                if List.memq c cases then Some (m, name, c) else None)
              (module_ext_cases m f))
          models
      in
      (* in the order of the cases *)
      let alts =
        List.filter_map
          (fun (c : case) ->
            List.find_opt (fun (_, _, c') -> c' == c) alts)
          cases
      in
      pf ft "@[<v 2>def %s %a : %a :=@ (firstSome [%s]).getD (%s.default (S := sem) %a)@]@ @ "
        (qn f.name) params f lean_ty f.ret
        (String.concat ", "
           (List.map
              (fun (m, name, _) ->
                Fmt.str "%s.%s.%s (S := sem) %a" (module_root m) (qn f.name) name args f)
              alts))
        (fn_ref f.name) args f;
      pf ft
        "@[<v 2>theorem %s.sound %a :@   %s.post (S := sem) %a (%s %a) := by@ \
         unfold %s"
        (qn f.name) params f (fn_ref f.name) args f (qn f.name) args f
        (qn f.name);
      List.iter
        (fun (m, name, _) ->
          pf ft
            "@ refine Kanon.getD_firstSome_cons (fun r h => %s.%s.%s.ok (S := \
             sem) %a r h) ?_"
            (module_root m) (qn f.name) name args f)
        alts;
      pf ft "@ exact Kanon.getD_firstSome_nil (%s.default.ok (S := sem) %a)@]@ @ "
        (fn_ref f.name) args f;
      ignore fm)
    exts;
  (* the rule functions *)
  List.iter
    (fun (f : fn) ->
      let rs =
        List.map
          (fun ((_, _, grp) as rule) ->
            let m = case_module f (List.hd grp) in
            (m, rule_name f grp, rule))
          (rules f)
      in
      pf ft "@[<v 2>def %s.step (O : Ops sem) %a : Term :=@ (firstSome [%s]).getD@   (%s.spec (S := sem) %a)@]@ @ "
        (qn f.name) params f
        (String.concat ", "
           (List.map
              (fun (m, rule, _) ->
                Fmt.str "%s.%s.r_%s (S := sem) %s %a" (module_root m) (qn f.name)
                  (id rule) (o_to m) args f)
              rs))
        (fn_ref f.name) args f;
      pf ft
        "@[<v 2>theorem %s.step_sound (O : Ops sem) (hO : O.Sound) %a%a :@   \
         Refines (%s.spec (S := sem) %a) (%s.step O %a) := by@ unfold %s.step"
        (qn f.name) params f (pre_binders ?rename:None) f (fn_ref f.name) args f
        (qn f.name) args f (qn f.name);
      List.iter
        (fun (m, rule, _) ->
          pf ft
            "@ refine Kanon.Refinement.firstSome_cons (fun res h => \
             %s.%s.r_%s.sound (S := sem) %s %s %a%a res h) ?_"
            (module_root m) (qn f.name) (id rule) (o_to m) (h_to m) args f
            pre_names f)
        rs;
      pf ft "@ exact Kanon.Refinement.firstSome_nil@]@ @ ";
      Option.iter
        (fun p ->
          let fm = Option.get (module_of_name f.name) in
          pf ft
            "@[<v 2>theorem %s.step_post (O : Ops sem) (hO : O.Sound) %a%a :@   \
             %s (S := sem) (%s.step O %a) := by@ unfold %s.step"
            (qn f.name) params f (pre_binders ?rename:None) f (pred_ref p)
            (qn f.name) args f (qn f.name);
          List.iter
            (fun (m, rule, _) ->
              pf ft
                "@ refine Kanon.getD_firstSome_cons (fun res h => \
                 %s.%s.r_%s.post_sound (S := sem) %s %s %a%a res h) ?_"
                (module_root m) (qn f.name) (id rule) (o_to m) (h_to m) args f
                pre_names f)
            rs;
          pf ft "@ exact Kanon.getD_firstSome_nil (%s.spec_post.ok (S := sem) %a%a)@]@ @ "
            (fn_ref f.name) args f pre_names f;
          ignore fm)
        (postcondition f))
    (rule_fns ctx);
  (* the model *)
  let rfs = rule_fns ctx in
  pf ft
    "/-- The rule functions as their specs, without simplification. -/@ \
     @[<v 2>def opsRaw (orc : Oracle) : Ops sem :=@ { tag_le := orc.tag_le";
  List.iter
    (fun (_, (q : prim)) -> pf ft ",@   %s := orc.%s" (fld q.pname) (fld q.pname))
    oracles;
  List.iter (fun (f : fn) -> pf ft ",@   %s := %s" (fld f.name) (qn f.name)) exts;
  List.iter
    (fun (f : fn) ->
      pf ft ",@   %s := fun %a => %s.spec (S := sem) %a" (fld f.name) args f
        (fn_ref f.name) args f)
    rfs;
  pf ft " }@]@ @ ";
  pf ft
    "/-- One step of the rule functions, over those of `O`. -/@ @[<v 2>def \
     opsStep (O : Ops sem) : Ops sem :=@ { O with";
  pf ft "%s"
    (String.concat ","
       (List.map
          (fun (f : fn) ->
            Fmt.str "\n    %s := %s.step O" (fld f.name) (qn f.name))
          rfs));
  pf ft " }@]@ @ ";
  pf ft
    "/-- The rule functions, with `n` steps of fuel. -/@ @[<v 2>def opsN (orc \
     : Oracle) : Nat → Ops sem@ | 0 => opsRaw orc@ | n + 1 => opsStep (opsN \
     orc n)@]@ @ ";
  let sound_fields ~raw =
    List.concat_map
      (fun (f : fn) ->
        (if raw then
           [ Fmt.str "%s := fun %a%a => Kanon.Sem.Refines.refl" (fld f.name)
               args f pre_names f ]
         else [ Fmt.str "%s := %s.step_sound _ hO" (fld f.name) (qn f.name) ])
        @
        match postcondition f with
        | None -> []
        | Some _ ->
            if raw then
              [ Fmt.str "%s_post := fun %a%a => %s.spec_post.ok (S := sem) %a%a"
                  (fld f.name) args f pre_names f (fn_ref f.name) args f pre_names f ]
            else [ Fmt.str "%s_post := %s.step_post _ hO" (fld f.name) (qn f.name) ])
      rfs
    @ List.map
        (fun m ->
          Fmt.str "%s_orc := %s" (String.uncapitalize_ascii m)
            (if raw then "h." ^ String.uncapitalize_ascii m
             else "hO." ^ String.uncapitalize_ascii m ^ "_orc"))
        orc_mods
    @ List.map
        (fun (f : fn) ->
          Fmt.str "%s := %s"  (fld f.name)
            (if raw then qn f.name ^ ".sound" else "hO." ^ fld f.name))
        exts
  in
  let fields l =
    if l = [] then "{}" else "{ " ^ String.concat ",\n      " l ^ " }"
  in
  pf ft
    "/-- Every rule function refines its spec, for any amount of fuel. -/@ \
     @[<v 2>theorem opsN_sound (orc : Oracle) (h : orc.Compat) : ∀ n, (opsN \
     orc n).Sound@ | 0 =>@   %s@ | n + 1 =>@   have hO := opsN_sound orc h \
     n@   %s@]@ @ "
    (fields (sound_fields ~raw:true))
    (fields (sound_fields ~raw:false))

(* ---------------------------------------------------------------- *)
(* The tree of the Lean files *)

(** The generated Lean files, by part, in order: each part, [model] say, is
    printed by the backend [lean-model]. [has_proof r path] says whether the
    hand-written file at [path] under the root [r] exists. A language whose
    first file is built into kanon ([+bool.knl]) is a module alone: only its
    files are generated. *)
let parts ~module_only ~lang:lang_sources ~has_proof (prog : program Lazy.t) =
  has_file := has_proof;
  let prog' = lazy (modelled (Lazy.force prog)) in
  let ctx = lazy (classify (Lazy.force prog')) in
  let init =
    lazy
      (compute_refs (Lazy.force prog');
       has_model_ref := has_model (Lazy.force ctx))
  in
  let modules () =
    Lazy.force init;
    List.filter (fun m -> not (List.mem m !builtin_modules) || module_only)
      (all_modules ())
  in
  let each f () = List.concat_map f (modules ()) in
  let ctx () = Lazy.force init; Lazy.force ctx in
  let p () = Lazy.force prog' in
  let module_parts =
    [
      ("types", each (fun m -> if has_types m then [ types_file m ] else []));
      ("node", each (fun m -> if has_lang m then [ node_file (p ()) m ] else []));
      ( "lang",
        each (fun m -> if has_lang m then [ lang_file (ctx ()) (p ()) m ] else [])
      );
      ( "model",
        each (fun m ->
            if has_model (ctx ()) m then [ model_file (ctx ()) (p ()) m ] else [])
      );
      ( "statements",
        each (fun m ->
            if has_model (ctx ()) m then [ statements_file (ctx ()) m ] else [])
      );
      ( "soundness",
        each (fun m ->
            if has_model (ctx ()) m then [ soundness_file (ctx ()) m ] else [])
      );
    ]
  in
  let sources = lang_sources in
  let language_parts =
    [
      ("syntax", fun () -> [ syntax_file ~sources (Lazy.force init; all_modules ()) ]);
      ( "semantics",
        fun () -> [ semantics_file ~sources (p ()) (Lazy.force init; all_modules ()) ] );
      ("rules", fun () -> [ rules_file ~sources (ctx ()) (Lazy.force init; all_modules ()) ]);
    ]
  in
  if module_only then module_parts else module_parts @ language_parts
