(** Lean backend.

    Functions with a [[@spec]] are rule functions. Each of their rules becomes a
    Lean function [f.r.name : Ops -> args -> Option Term] (the rule's patterns
    and guard, returning its right-hand side), in which the calls to rule
    functions go through the record [O : Ops]. [f.step O] tries the rules in
    order and falls back to the spec; [opsN orc n] ties the knot with [n] steps
    of fuel (fuel 0 being the raw specs).

    Helpers that call rule functions or oracles take [O] as a parameter; the
    other helpers are plain Lean functions.

    Three files are generated: [Model.lean] (the above), [Statements.lean]
    (soundness of [Ops], one statement per rule, and the commutativity of each
    commutative operator) and [Soundness.lean] (soundness of [opsN], from the
    proofs [f.r.name.proof] of the rule statements, written by hand). *)

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
    "at";
    "obtain";
    "using";
    "fin";
  ]

let id x = if List.mem x keywords then "«" ^ x ^ "»" else x

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

(* ---------------------------------------------------------------- *)
(* Classification *)

type kind = Rule | OHelper | Pure
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
         (fun f -> (f.name, if Option.is_some f.spec then Rule else Pure))
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
                | Some (Rule | OHelper) -> true
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
(* Types *)

(** The Lean name of a type of the language: its Kanon name, CamelCased. *)
let lean_name s =
  String.concat ""
    (List.map String.capitalize_ascii (String.split_on_char '_' s))

(** The Lean name of a type: [Kind] for the kinds of terms, the name of the kind
    constructor of their operators for the types of operators ([Op2], [OpN]),
    else its Kanon name, CamelCased. *)
let decl_lean_name (d : decl) =
  if decl_name TKind = Some d.d_name then "Kind"
  else
    match
      List.find_opt
        (fun k ->
          match find_constr k with
          | Some { c_args = Arg (TData t) :: _; _ } -> t = d.d_name
          | _ -> false)
        !lang.node_kinds
    with
    | Some k -> k
    | None -> lean_name d.d_name

let rec lean_ty ft = function
  | TInt -> pf ft "Int"
  | TBool -> pf ft "Bool"
  | TUnit -> pf ft "Unit"
  | TTerm -> pf ft "Term"
  | (TKind | TSty | TData _) as t ->
      let d = decl_of_ty t in
      pf ft "%s" (Option.value ~default:(decl_lean_name d) d.d_lean)
  | TTuple l -> pf ft "(%a)" (list ~sep:" × " lean_ty) l
  | TOption t -> pf ft "(Option %a)" lean_ty t
  | TList t -> pf ft "(List %a)" lean_ty t
  | TApp (n, _) ->
      raise
        (Check.Error
           ( (decl_of_ty (TData n)).d_loc,
             Fmt.str
               "type %s is parametrised: parametrised abstract types are not \
                supported in Lean"
               n ))

let lean_constr (c : constr) = Fmt.str "%a.%s" lean_ty c.c_res c.c_name

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
  | PConstr (c, args) ->
      let inner ft () =
        match args with
        | [] -> pf ft "%s" (lean_constr c)
        | _ -> pf ft "(%s %a)" (lean_constr c) (list ~sep:" " pat) args
      in
      if p.pty = TTerm then pf ft "(Term.mk %a _)" inner () else inner ft ()

(* ---------------------------------------------------------------- *)
(* Expressions *)

(** Variables printed as given terms: the scrutinees and [as] binders of a
    [[@cases]] alternative, in its statement. *)
let subst : (string * string) list ref = ref []

(** [k ()] with the variables [xs] bound, hence not substituted. *)
let binding xs k =
  let saved = !subst in
  subst := List.filter (fun (x, _) -> not (List.mem x xs)) saved;
  Fun.protect ~finally:(fun () -> subst := saved) k

(** Whether the rule being printed belongs to a [[@cases]] function. *)
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
  | EConstr (c, []) -> pf ft "%s" (lean_constr c)
  | EConstr (c, args) ->
      pf ft "(%s %a)" (lean_constr c) (list ~sep:" " expr) args
  | ENode (k, t) -> pf ft "(Term.mk %a %a)" expr k expr t
  | ECall ("type_of", [ a ]) -> pf ft "(ty %a)" expr a
  | ECall (f, args) ->
      let f =
        if is_oracle ctx f then "O.orc." ^ f
        else if is_prim ctx f then f
        else
          match fn_kind ctx f with
          | Rule -> "O." ^ f
          | OHelper -> f ^ " O"
          | Pure -> f
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
  | EMatch (scruts, cases)
    when e.ety = TSty || (List.rev cases |> List.hd).body.e = EUnreachable ->
      sort_match ctx ft (scruts, cases)
  | EMatch (scruts, cases) -> match_ ctx ft (scruts, cases)
  | ETuple l -> pf ft "(%a)" (list expr) l
  | ESome e -> pf ft "(some %a)" expr e
  | ENone -> pf ft "none"
  | ENil -> pf ft "[]"
  | ECons (h, t) -> pf ft "(%a :: %a)" expr h expr t
  | ERecord fs ->
      let d = decl_of_ty e.ety in
      pf ft "({ %a } : %s)"
        (list (fun ft (f, _) -> pf ft "%s := %a" f expr (List.assoc f fs)))
        d.d_fields (decl_lean_name d)
  | EField (e, f) -> pf ft "%a.%s" expr e f
  | EAssert (_, body) -> expr ft body

and pat_names p = List.map fst (Check.binders p)

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

(** Whether a pattern matches every value of its type. *)
and irrefutable (p : pat) =
  match p.p with
  | PAny | PVar _ | PUnit -> true
  | PAs (q, _) -> irrefutable q
  | PTuple l -> List.for_all irrefutable l
  | PRecord fs -> List.for_all (fun (_, q) -> irrefutable q) fs
  | _ -> false

(** How a match on [scruts] is printed: on several discriminants when possible
    (so that Lean sees the recursion on each of them), else on a tuple. *)
and discriminants ctx (scruts, (cases : case list)) =
  let multi =
    List.length scruts > 1
    && List.for_all
         (fun (c : case) ->
           match c.pat.p with PTuple _ | PAny -> true | _ -> false)
         cases
  in
  let d ft () =
    if multi || List.length scruts = 1 then list (expr ctx) ft scruts
    else pf ft "(%a)" (list (expr ctx)) scruts
  in
  let p ft (q : pat) =
    match q.p with
    | PTuple l when multi -> list pat ft l
    | PAny when multi -> list (fun ft _ -> pf ft "_") ft scruts
    | _ -> pat ft q
  in
  let wild ft () =
    if multi then list (fun ft _ -> pf ft "_") ft scruts else pf ft "_"
  in
  (d, p, wild)

(** A match on sorts, which Kanon builds to infer the sort of a node and whose
    cases have no guard: a plain Lean match. *)
and sort_match ctx ft (scruts, cases) =
  let d, p, _ = discriminants ctx (scruts, cases) in
  let case ft (c : case) =
    pf ft "@ @[<hv 2>| %a =>@ %a@]" p c.pat
      (fun ft () -> binding (pat_names c.pat) (fun () -> expr ctx ft c.body))
      ()
  in
  pf ft "@[<hv 2>(match %a with%a)@]" d () (fun ft -> List.iter (case ft)) cases

(** A match with guards: each case is a Lean match of its own, returning [none]
    when its pattern or guard fails, and the first case that applies gives the
    result. A last case that always applies is the default. *)
and match_ ctx ft (scruts, cases) =
  let d, p, wild = discriminants ctx (scruts, cases) in
  let alt ft (c : case) =
    let rhs = guarded ctx c in
    if irrefutable c.pat then
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat rhs ()
    else
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a@ | %a => none)@]" d () p c.pat
        rhs () wild ()
  in
  let alts, default =
    match List.rev cases with
    | ({ guard = None; _ } as c) :: rest when irrefutable c.pat ->
        ( List.rev rest,
          fun ft () ->
            pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat
              (fun ft () ->
                binding (pat_names c.pat) (fun () -> expr ctx ft c.body))
              () )
    | _ -> (cases, fun ft () -> pf ft "Inhabited.default")
  in
  match alts with
  | [] -> default ft ()
  | _ ->
      pf ft "@[<hv 2>((firstSome [%a]).getD@ %a)@]"
        (Format.pp_print_list ~pp_sep:(fun ft () -> pf ft ",@ ") alt)
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

(** The Lean function for one rule. *)
let rule_def ctx ft (f : fn) (pre, scruts, grp) =
  cases_style := f.cases;
  Fun.protect ~finally:(fun () -> cases_style := false) @@ fun () ->
  let name = rule_name f grp in
  let d, p, wild = discriminants ctx (scruts, grp) in
  let alt ft (c : case) =
    let rhs = guarded ctx c in
    if scruts = [] then rhs ft ()
    else if irrefutable c.pat then
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a)@]" d () p c.pat rhs ()
    else
      pf ft "@[<hv 2>(match %a with@ | %a =>@ %a@ | %a => none)@]" d () p c.pat
        rhs () wild ()
  in
  let rec lets ft (e : expr) =
    match e.e with
    | ELet ({ p = PVar x; _ }, rhs, b) ->
        pf ft "let %s := %a;@ %a" (id x) (expr ctx) rhs lets b
    | ELet _ -> failwith "gen_lean: destructuring let before a rule match"
    | _ -> Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "@ <|> ") alt ft grp
  in
  pf ft "@[<v 2>def %s.r_%s (O : Ops) %a : Option Term :=@ %a@]@ @ " f.name
    (id name) params f lets
    (pre { (List.hd grp).body with e = EUnit })

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

let ty_str t = Fmt.str "%a" lean_ty t

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
    | PConstr (c, args) ->
        let args = List.map go args in
        let inner =
          if args = [] then lean_constr c
          else "(" ^ String.concat " " (lean_constr c :: args) ^ ")"
        in
        if p.pty = TTerm then (
          let t = Printf.sprintf "t__%d" p.pid in
          bind t (ty_str TSty);
          "(Term.mk " ^ inner ^ " " ^ t ^ ")")
        else inner
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
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l ->
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
        let independent x =
          match (List.assoc_opt x a.a_subst, List.assoc_opt x b.a_subst) with
          | Some (t, _), Some (t', _) when t = t' -> true
          | Some (t, _), Some (t', _) when is_param a t && is_param b t' -> true
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
            Some (b, List.map arg b.a_binders, top, nested)
        | _ -> None)

(* ---------------------------------------------------------------- *)
(* Files *)

(** The Lean namespace of the model, and the root of its modules. *)
let root () = !lang.lean_root

(** The module [m] of the model. *)
let md m = root () ^ "." ^ m

(** The parameters of the semantics, as binders, implicit binders, and
    arguments. *)
let sem_binders () =
  String.concat ""
    (List.map (fun (x, t) -> Printf.sprintf "(%s : %s) " x t) !lang.lean_params)

let sem_implicits () =
  String.concat ""
    (List.map (fun (x, t) -> Printf.sprintf "{%s : %s} " x t) !lang.lean_params)

let sem_args () =
  String.concat "" (List.map (fun (x, _) -> " " ^ x) !lang.lean_params)

let header ~sources ft imports =
  pf ft "@[<v>-- Generated by kanon from %a. Do not edit.@ "
    (list Format.pp_print_string)
    sources;
  List.iter (fun i -> pf ft "import %s@ " i) imports;
  pf ft
    "@ set_option linter.unusedVariables false@ set_option maxHeartbeats \
     1000000@ @ noncomputable section@ @ namespace %s@ @ open Classical Kanon@ \
     @ "
    (root ())

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

let fn_def ctx ft (f : fn) ~o ~kw ~recursive =
  pf ft "%a@[<v 2>%s %s%s %a : %a :=@ %a@]@ " doc f.fdoc kw (id f.name)
    (if o then " (O : Ops)" else "")
    params f lean_ty f.ret (expr ctx) f.body;
  (if recursive then
     match decreasing f f.body with
     | Some x ->
         pf ft
           "termination_by sizeOf %s@ decreasing_by all_goals (simp_wf; \
            omega)@ "
           (id x)
     | None -> ());
  pf ft "@ "

let defs ctx ft kind ~o =
  List.iter
    (fun group ->
      let group = List.filter (fun f -> fn_kind ctx f.name = kind) group in
      match group with
      | [] -> ()
      | [ f ] when not (Gen_ocaml.is_recursive [ f ]) ->
          fn_def ctx ft f ~o ~kw:"def" ~recursive:false
      | _ ->
          pf ft "mutual@ @ ";
          List.iter (fn_def ctx ft ~o ~kw:"def" ~recursive:true) group;
          pf ft "end@ @ ")
    (Gen_ocaml.sccs ctx.fns)

let rule_fns ctx = List.filter (fun f -> fn_kind ctx f.name = Rule) ctx.fns

let model ~sources ft (p : program) =
  let p = modelled p in
  let ctx = classify p in
  header ~sources ft [ md "Signatures" ];
  (* oracles *)
  pf ft
    "/-- The primitives that the model is parameterised by. -/@ @[<v \
     2>structure Oracle where";
  List.iter
    (fun (q : prim) ->
      if q.oracle then (
        pf ft "@ %a%s : " doc q.pdoc q.pname;
        List.iter (fun t -> pf ft "%a → " lean_ty t) q.pargs;
        lean_ty ft q.pret))
    p.prims;
  pf ft "@]@ @ ";
  defs ctx ft Pure ~o:false;
  (* Ops *)
  pf ft
    "/-- The rule functions, as used by the rules. -/@ @[<v 2>structure Ops \
     where@ orc : Oracle";
  List.iter
    (fun f -> pf ft "@ %a%s : %a" doc f.fdoc f.name arrow f)
    (rule_fns ctx);
  pf ft "@]@ @ ";
  defs ctx ft OHelper ~o:true;
  (* specs *)
  List.iter
    (fun f ->
      pf ft "%a@[<v 2>@@[kanon_spec] def %s.spec %a : Term :=@ %a@]@ @ " doc
        f.fdoc f.name params f (expr ctx) (Option.get f.spec))
    (rule_fns ctx);
  (* rules and steps *)
  List.iter
    (fun f ->
      let rs = rules f in
      List.iter (rule_def ctx ft f) rs;
      pf ft
        "@[<v 2>def %s.step (O : Ops) %a : Term :=@ (firstSome [%a]).getD \
         (%s.spec %a)@]@ @ "
        f.name params f
        (list (fun ft r ->
             pf ft "%s.r_%s O %a" f.name
               (id
                  (rule_name f
                     (let _, _, g = r in
                      g)))
               args f))
        rs f.name args f)
    (rule_fns ctx);
  let fields ft mk =
    List.iter (fun f -> pf ft ",\n    %s := %a" f.name mk f) (rule_fns ctx)
  in
  pf ft "@[<v 2>def opsRaw (orc : Oracle) : Ops :=@ { orc := orc%a }@]@ @ "
    fields (fun ft f -> pf ft "fun %a => %s.spec %a" args f f.name args f);
  pf ft "@[<v 2>def opsStep (O : Ops) : Ops :=@ { orc := O.orc%a }@]@ @ " fields
    (fun ft f -> pf ft "%s.step O" f.name);
  pf ft
    "@[<v 2>def opsN (orc : Oracle) : Nat → Ops@ | 0 => opsRaw orc@ | n + 1 => \
     opsStep (opsN orc n)@]@ @ ";
  pf ft "end %s@]@." (root ())

(* ---------------------------------------------------------------- *)
(* Commutativity: one statement per commutative operator, from which the arms
   that swap its operands are proved *)

(** The commutative operators, with the kind of their nodes. *)
let comm_ops () =
  List.filter_map
    (fun name ->
      let op = Option.get (find_constr name) in
      match Check.node_of_op op with
      | Some (kc, [ _; _ ]) -> Some (op, kc)
      | _ -> None)
    !lang.commutative

(** The statement that the operands of [op] commute, without its [.Stmt]:
    [Binop.Plus.comm]. *)
let comm_name (op : constr) = lean_constr op ^ ".comm"

(** The statement that the operands of [op] commute: its node over [a] and [b]
    is refined by its node over [b] and [a], at any sort. *)
let comm_stmt ft ((op : constr), (kc : constr)) =
  let fresh x =
    if List.mem_assoc x !lang.lean_params then "kanon__" ^ x else x
  in
  let a = fresh "a" and b = fresh "b" and t = fresh "t" in
  let xs =
    List.mapi
      (fun i arg -> (fresh (Printf.sprintf "x%d" (i + 1)), arg_ty arg))
      op.c_args
  in
  let o =
    if xs = [] then lean_constr op
    else
      Printf.sprintf "(%s %s)" (lean_constr op)
        (String.concat " " (List.map fst xs))
  in
  let node x y =
    Printf.sprintf "(Term.mk (%s %s %s %s) %s)" (lean_constr kc) o x y t
  in
  pf ft
    "/-- The operands of `%s` commute. -/@ @[<v 2>def %s.Stmt : Prop :=@ ∀ \
     %s%a(%s %s : Term) (%s : %a),@ Refines%s %s@ %s@]@ @ "
    (lean_constr op) (comm_name op) (sem_binders ())
    (fun ft -> List.iter (fun (x, ty) -> pf ft "(%s : %a) " x lean_ty ty))
    xs a b t lean_ty TSty (sem_args ()) (node a b) (node b a)

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
      (* the swaps are numbered if there are several *)
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
  Printf.sprintf "%s.r_%s.%s" f.name (id r) (id (List.nth (arm_names arms) i))

(** The statement of an arm: under its guard, the spec at the matched arguments
    is refined by the body. *)
let arm_stmt ctx ft f r arms i (a : arm) =
  let c = a.a_case in
  let with_subst s k =
    subst := s;
    Fun.protect ~finally:(fun () -> subst := []) k
  in
  pf ft "@[<v 2>def %s.Stmt : Prop :=@ ∀ %s(O : Ops), O.Sound%s →@ "
    (arm_name f r arms i) (sem_binders ()) (sem_args ());
  if a.a_binders <> [] then
    pf ft "∀ %a,@ "
      (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %s)" x t))
      a.a_binders;
  (* the assumptions on the operands, over the scrutinees *)
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
  (* the [let]s before the match, over the scrutinees *)
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
  pf ft "Refines%s (%s.spec %s)@ (%a)@]@ @ " (sem_args ()) f.name
    (String.concat " " spec_args)
    (fun ft () -> with_subst a.a_body_subst (fun () -> expr ctx ft c.body))
    ()

let statements ~sources ft (p : program) =
  let p = modelled p in
  let ctx = classify p in
  header ~sources ft [ md "Semantics" ];
  pf ft
    "/-- Every rule function refines its spec. -/@ @[<v 2>structure Ops.Sound \
     %s(O : Ops) : Prop where@ orc : O.orc.Compat%s"
    (sem_binders ()) (sem_args ());
  List.iter
    (fun f ->
      pf ft "@ %s : ∀ %a, %aRefines%s (%s.spec %a) (O.%s %a)" f.name params f
        pre_arrows f (sem_args ()) f.name args f f.name args f)
    (rule_fns ctx);
  pf ft "@]@ @ ";
  List.iter (comm_stmt ft) (comm_ops ());
  List.iter
    (fun f ->
      List.iter
        (fun r ->
          let _, _, g = r in
          let n = id (rule_name f g) in
          pf ft
            "@[<v 2>def %s.r_%s.Stmt : Prop :=@ ∀ %s(O : Ops), O.Sound%s →@ ∀ \
             %a (res : Term), %a%s.r_%s O %a = some res →@ Refines%s (%s.spec \
             %a) res@]@ @ "
            f.name n (sem_binders ()) (sem_args ()) params f pre_arrows f f.name
            n args f (sem_args ()) f.name args f)
        (rules f);
      if f.cases then
        List.iter
          (fun (r, arms) ->
            List.iteri (fun i a -> arm_stmt ctx ft f r arms i a) arms)
          (arms f))
    (rule_fns ctx);
  List.iter
    (fun f ->
      Option.iter
        (fun p ->
          pf ft
            "/-- What `%s` returns, a rule or its spec, satisfies `%s`: to \
             prove by hand, with `@@[kanon_arm]`. -/@ @[<v 2>def \
             %s.post.main.Stmt : Prop :=@ ∀ %s(O : Ops), O.Sound%s →@ ∀ %a, \
             %a%s (%s.step O %a)@]@ @ "
            f.name p f.name (sem_binders ()) (sem_args ()) params f pre_arrows f
            p f.name args f)
        (postcondition f))
    (rule_fns ctx);
  pf ft "end %s@]@." (root ())

(** The user functions that [e] calls. *)
let rec calls (e : expr) =
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> []
  | ECall (f, l) -> f :: List.concat_map calls l
  | EConstr (_, l) | ELocalCall (_, l) | ETuple l -> List.concat_map calls l
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

(** One lemma per rule function: its spec is monotone in its term arguments, so
    a call of the function on terms that refine others refines the spec on
    those. *)
let lifts ~sources ft (p : program) =
  let p = modelled p in
  let ctx = classify p in
  header ~sources ft [ md "Lib.Lift" ];
  pf ft "namespace Lib@ @ variable %s{O : Ops}@ @ " (sem_implicits ());
  List.iter
    (fun f ->
      let term (_, t) = t = TTerm in
      let prime (x, t) = if term (x, t) then id x ^ "'" else id x in
      let helpers =
        List.filter
          (fun g -> List.exists (fun (h : fn) -> h.name = g) ctx.fns)
          (calls (Option.get f.spec))
        |> List.sort_uniq compare
      in
      pf ft "@[<v 2>theorem lift_%s (hO : O.Sound%s)" f.name (sem_args ());
      List.iter
        (fun (x, t) ->
          if term (x, t) then pf ft " {%s %s' : Term}" (id x) (id x)
          else pf ft " {%s : %a}" (id x) lean_ty t)
        f.params;
      List.iter
        (fun (x, t) ->
          if term (x, t) then
            pf ft "@ (h_%s : Refines%s %s %s')" x (sem_args ()) (id x) (id x))
        f.params;
      (* the assumptions are on the arguments of the call *)
      pre_binders
        ~rename:(fun x ->
          if term (x, List.assoc x f.params) then x ^ "'" else x)
        ft f;
      pf ft " :@ Refines%s (%s.spec %s) (O.%s %s) :=@ " (sem_args ()) f.name
        (String.concat " " (List.map (fun (x, _) -> id x) f.params))
        f.name
        (String.concat " " (List.map prime f.params));
      if List.exists term f.params then
        pf ft
          "Refinement.trans (by simp only [%s]; kanon_congr) (hO.%s %s%a)@]@ @ "
          (String.concat ", " ("kanon_spec" :: helpers))
          f.name
          (String.concat " " (List.map prime f.params))
          pre_names f
      else
        pf ft "hO.%s %s%a@]@ @ " f.name
          (String.concat " " (List.map prime f.params))
          pre_names f)
    (rule_fns ctx);
  pf ft "end Lib@ @ end %s@]@." (root ())

(** Whether the case at [loc] is one of the bool module built into kanon
    ([use builtin "bool"]), or derived from its laws: Kanon's Lean library
    proves its arms once, for any language ([Kanon.BoolMod]). *)
let in_bool_module (loc : Location.t) =
  List.mem loc.loc_start.pos_fname [ "+bool.kn"; "+bool.knl" ]

(** [x] applied to the parameters of the semantics, as an argument. *)
let with_sem_args x =
  if !lang.lean_params = [] then x else "(" ^ x ^ sem_args () ^ ")"

(** The rule functions, oracles and helpers of the bool module in the model, for
    the proofs of its arms by Kanon's library ([Kanon.BoolMod.Ops]), with the
    proof of what these proofs assume of them, from [O.Sound]. *)
let bool_ops ft =
  pf ft
    "/-- The rule functions, oracles and helpers of the bool module in the \
     model, for the proofs@ of its arms by Kanon's library (`Kanon.BoolMod`). \
     -/@ ";
  pf ft
    "@[<v 2>def Ops.bool %s(O : Ops) : BoolMod.Ops %s where@ b_and := O.b_and@ \
     b_or := O.b_or@ b_not := O.b_not@ b_ite := O.b_ite@ sem_eq := O.sem_eq@ \
     tag_le := O.orc.tag_le@ sort_by_tag := O.orc.sort_by_tag@ at_most_one := \
     at_most_one@ distinct_check_one := distinct_check_one@ distinct_check := \
     distinct_check@]@ @ "
    (sem_binders ()) (with_sem_args "boolLang");
  pf ft
    "@[<v 2>theorem Ops.Sound.bool %s{O : Ops} (hO : O.Sound%s) : %s.Sound \
     where@ b_and := hO.b_and@ b_or := hO.b_or@ b_not := hO.b_not@ b_ite := \
     hO.b_ite@ sem_eq := hO.sem_eq@ sort_by_tag := hO.orc.sort_by_tag@ \
     at_most_one _ _ _ := rfl@ distinct_check_one_nil _ := by@   dsimp only \
     [Ops.bool]; rw [distinct_check_one]; rfl@ distinct_check_one_cons _ _ _ \
     := by@   dsimp only [Ops.bool]; rw [distinct_check_one]; rfl@ \
     distinct_check_nil := by@   dsimp only [Ops.bool]; rw [distinct_check]; \
     rfl@ distinct_check_cons _ _ := by@   dsimp only [Ops.bool]; rw \
     [distinct_check]; split <;> simp_all [firstSome]@]@ @ "
    (sem_implicits ()) (sem_args ()) (with_sem_args "O.bool")

(** The proof that the operands of [op] commute, a lemma of [kanon_comm]: by
    Kanon's library for the operators of the bool module ([bool]), else by
    [kanon_proof%]. *)
let comm_proof ~bool ft ((op : constr), _) =
  let n = comm_name op in
  match
    List.assoc_opt op.c_name [ ("And", "and"); ("Or", "or"); ("Eq", "eq") ]
  with
  | Some l when bool ->
      pf ft
        "@[<v 2>@@[kanon_comm_lemma] theorem %s.ok : %s.Stmt :=@ fun%s _ _ _ \
         => BoolMod.Lang.refines_%s_comm (L := %s)@]@ @ "
        n n (sem_args ()) l (with_sem_args "boolLang")
  | _ ->
      pf ft
        "@@[kanon_comm_lemma] theorem %s.ok : %s.Stmt := kanon_proof%% %s@ @ " n
        n n

(** The proofs of the rules of a [[@cases]] function from those of its arms, and
    of the arms derived by commutativity. *)
let cases_proofs ft (f : fn) =
  List.iter
    (fun (r, arms) ->
      List.iteri
        (fun i a ->
          (* the operands of a swapped arm are other terms than those of the arm
             that it is derived from, which the assumptions are about *)
          let derived =
            if preconditions f = [] then derived_from f arms a else None
          in
          match derived with
          | _ when in_bool_module a.a_case.cloc ->
              (* proved once, by Kanon's library *)
              pf ft
                "@[<v 2>theorem %s.ok : %s.Stmt :=@ fun%s O hO => BoolMod.%s \
                 %s %s hO.bool@]@ @ "
                (arm_name f r arms i) (arm_name f r arms i) (sem_args ())
                (arm_name f r arms i) (with_sem_args "boolLang")
                (with_sem_args "O.bool")
          | None ->
              (* a hand-written [.proof] if there is one, else the default
                 tactic *)
              pf ft "theorem %s.ok : %s.Stmt := kanon_proof%% %s@ @ "
                (arm_name f r arms i) (arm_name f r arms i)
                (arm_name f r arms i)
          | Some (b, args, top, nested) ->
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
              let comm o = Fmt.str "%s.ok%s .." (comm_name o) (sem_args ()) in
              pf ft "@[<v 2>theorem %s.ok : %s.Stmt := by@ intro%s O hO%a%s@ "
                (arm_name f r arms i) (arm_name f r arms i) (sem_args ())
                (fun ft -> List.iter (fun (x, _) -> pf ft " %s" x))
                a.a_binders hg;
              (* each swapped node of [a] refines that of [b], inner ones first:
                 by commutativity, and congruence for the swaps inside *)
              List.iter
                (fun ((qa : pat), qb, o) ->
                  let inner =
                    List.exists
                      (fun ((qa' : pat), _, _) ->
                        qa'.pid <> qa.pid && List.mem qa'.pid (pids qa))
                      nested
                  in
                  pf ft "@[<hv 2>have : Refines%s %s@ %s :=@ " (sem_args ())
                    (term qa) (term qb);
                  if inner then
                    pf ft "Refinement.trans (%s) (by kanon_congr)@]@ " (comm o)
                  else pf ft "%s@]@ " (comm o))
                nested;
              pf ft
                "@[<hv 2>refine Refinement.trans ?_@ (%s.ok%s O hO%a%s)@]@ \
                 simp only [%s.spec%s]@ "
                (arm_name f r arms j) (sem_args ())
                (fun ft -> List.iter (pf ft " %s"))
                args hg f.name
                (if List.mem "type_of" (calls (Option.get f.spec)) then
                   ", ty, Term.ty_mk"
                 else "");
              Option.iter
                (fun o -> pf ft "refine Refinement.trans (%s) ?_@ " (comm o))
                top;
              pf ft "kanon_congr@]@ @ ")
        arms;
      (* the alternatives come out of [repeat' rcases] in order *)
      pf ft
        "@[<v 2>theorem %s.r_%s.proof : %s.r_%s.Stmt := by@ intro%s O hO %a \
         res%a h@ simp only [%s.r_%s] at h@ repeat' rcases orElse_some h with \
         h | h@ %a@]@ @ "
        f.name (id r) f.name (id r) (sem_args ()) args f pre_names f f.name
        (id r)
        (Format.pp_print_list
           ~pp_sep:(fun ft () -> pf ft "@ ")
           (fun ft i ->
             pf ft "· kanon_arm h (%s.ok%s O hO)" (arm_name f r arms i)
               (sem_args ())))
        (List.init (List.length arms) Fun.id))
    (arms f)

let soundness ~sources ~proofs ft (p : program) =
  let p = modelled p in
  let ctx = classify p in
  let proofs =
    if List.exists (fun f -> f.cases) (rule_fns ctx) then
      md "Lib.Rule" :: proofs
    else proofs
  in
  header ~sources ft (md "Statements" :: proofs);
  let bool =
    List.exists
      (fun f ->
        f.cases
        && List.exists
             (fun (_, arms) ->
               List.exists (fun a -> in_bool_module a.a_case.cloc) arms)
             (arms f))
      (rule_fns ctx)
  in
  if bool then bool_ops ft;
  List.iter (comm_proof ~bool ft) (comm_ops ());
  List.iter (fun f -> if f.cases then cases_proofs ft f) (rule_fns ctx);
  List.iter
    (fun f ->
      if postcondition f <> None then
        pf ft
          "theorem %s.post.main.ok : %s.post.main.Stmt := kanon_proof%% \
           %s.post.main@ @ "
          f.name f.name f.name)
    (rule_fns ctx);
  List.iter
    (fun f ->
      pf ft
        "@[<v 2>theorem %s.step_sound %s(O : Ops) (hO : O.Sound%s) %a%a :@ \
         Refines%s (%s.spec %a) (%s.step O %a) := by@ unfold %s.step@ "
        f.name (sem_binders ()) (sem_args ()) params f
        (pre_binders ?rename:None) f (sem_args ()) f.name args f f.name args f
        f.name;
      List.iter
        (fun r ->
          let _, _, g = r in
          let n = id (rule_name f g) in
          pf ft
            "refine Refinement.firstSome_cons (fun res h => %s.r_%s.proof%s O \
             hO %a res%a h) ?_@ "
            f.name n (sem_args ()) args f pre_names f)
        (rules f);
      pf ft "exact Refinement.firstSome_nil@]@ @ ")
    (rule_fns ctx);
  pf ft
    "/-- Every rule function refines its spec, for any amount of fuel. -/@ \
     @[<v 2>theorem opsN_sound %s(orc : Oracle) (h : orc.Compat%s) :@ ∀ n, \
     (opsN orc n).Sound%s@ | 0 =>\n\
    \    { orc := h"
    (sem_binders ()) (sem_args ()) (sem_args ());
  List.iter
    (fun f ->
      pf ft ",\n      %s := fun %a%a => Refinement.refl" f.name args f pre_names
        f)
    (rule_fns ctx);
  pf ft
    " }\n  | n + 1 =>\n    have hO := opsN_sound%s orc h n\n    { orc := hO.orc"
    (sem_args ());
  List.iter
    (fun f ->
      pf ft ",\n      %s := %s.step_sound%s _ hO" f.name f.name (sem_args ()))
    (rule_fns ctx);
  pf ft " }@]@ @ end %s@]@." (root ())

(* ---------------------------------------------------------------- *)
(* The types of the language

   Two files define them: [Types.lean], the types that neither use terms nor
   abstract types, and [Syntax.lean], the others, the types that use terms being
   mutually inductive with [Term]. The abstract types are defined by hand in
   between, in [Abstract.lean]. *)

let constrs_of (d : decl) =
  List.filter (fun c -> decl_name c.c_res = Some d.d_name) !lang.constrs

let is_abstract (d : decl) = d.d_fields = [] && constrs_of d = []

(** The types that [d] is defined with. *)
let components (d : decl) =
  List.map snd d.d_fields
  @ List.concat_map (fun c -> List.map arg_ty c.c_args) (constrs_of d)

let rec decls_of_ty = function
  | (TKind | TSty | TData _) as t -> [ decl_of_ty t ]
  | TApp (_, l) as t -> decl_of_ty t :: List.concat_map decls_of_ty l
  | TTuple l -> List.concat_map decls_of_ty l
  | TOption t | TList t -> decls_of_ty t
  | TInt | TBool | TUnit | TTerm -> []

let rec uses_term = function
  | TTerm -> true
  | TTuple l | TApp (_, l) -> List.exists uses_term l
  | TOption t | TList t -> uses_term t
  | _ -> false

(** The declared types, callees first, and otherwise in declaration order. *)
let sorted_decls () =
  let seen = Hashtbl.create 17 and out = ref [] in
  let rec visit (d : decl) =
    if not (Hashtbl.mem seen d.d_name) then (
      Hashtbl.add seen d.d_name ();
      List.iter visit (List.concat_map decls_of_ty (components d));
      out := d :: !out)
  in
  List.iter visit !lang.decls;
  List.rev !out

(** Whether [d] is defined, directly or not, with [p] types. *)
let reaches p (d : decl) =
  let rec go seen (d : decl) =
    p d
    || List.exists
         (fun (e : decl) ->
           (not (List.mem e.d_name seen)) && go (d.d_name :: seen) e)
         (List.concat_map decls_of_ty (components d))
  in
  go [] d

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
  pf ft "@]@ "

let lean_header ~sources ft imports =
  pf ft "@[<v>-- Generated by kanon from %a. Do not edit.@ @ "
    (list Format.pp_print_string)
    sources;
  List.iter (fun i -> pf ft "import %s@ " i) imports;
  if imports <> [] then pf ft "@ ";
  pf ft "namespace %s@ @ " (root ())

let deriving ft () = pf ft "  deriving DecidableEq, Repr, Inhabited@ @ "

(** [T.Comm]: the constructors of [T] that are commutative operators. *)
let comm_def ft (d : decl) =
  let cs = constrs_of d in
  let comm = List.filter (fun c -> is_commutative c.c_name) cs in
  if comm <> [] then (
    let name = decl_lean_name d in
    pf ft
      "/-- The operators whose operands commute (`[@@comm]`). -/@ @[<v 2>def \
       %s.Comm : %s → Prop@ | %a => True"
      name name
      (list ~sep:" | " (fun ft c ->
           pf ft ".%s%s" c.c_name
             (String.concat "" (List.map (fun _ -> " _") c.c_args))))
      comm;
    if List.length comm < List.length cs then pf ft "@ | _ => False";
    pf ft "@]@ @ ")

(** A type of the language, and its facts. *)
let lean_decl_full ft (d : decl) =
  lean_decl ft d;
  deriving ft ();
  comm_def ft d

(** [Types.lean]. *)
let types ~sources ft =
  lean_header ~sources ft [];
  List.iter
    (fun d ->
      if
        (not (is_abstract d))
        && not
             (reaches
                (fun e -> is_abstract e || List.exists uses_term (components e))
                d)
      then lean_decl_full ft d)
    (sorted_decls ());
  pf ft "end %s@]@." (root ())

(** [Syntax.lean]: the other types, and the terms. *)
let syntax ~sources ft =
  lean_header ~sources ft [ md "Abstract" ];
  let others =
    List.filter
      (fun d ->
        (not (is_abstract d))
        && reaches
             (fun e -> is_abstract e || List.exists uses_term (components e))
             d)
      (sorted_decls ())
  in
  let mutual, plain =
    List.partition
      (reaches (fun e -> List.exists uses_term (components e)))
      others
  in
  List.iter (lean_decl_full ft) plain;
  pf ft "mutual@ ";
  List.iter (lean_decl ft) mutual;
  pf ft "@[<v 2>inductive Term where@ | mk (kind : %a) (ty : %a)@]@ end@ @ "
    lean_ty TKind lean_ty TSty;
  pf ft
    "def Term.kind : Term → %a@   | .mk k _ => k@ @ def Term.ty : Term → %a@   \
     | .mk _ t => t@ @ "
    lean_ty TKind lean_ty TSty;
  pf ft
    "@@[simp] theorem Term.kind_mk (k : %a) (t : %a) : (Term.mk k t).kind = k \
     := rfl@ @@[simp] theorem Term.ty_mk (k : %a) (t : %a) : (Term.mk k t).ty \
     = t := rfl@ @ "
    lean_ty TKind lean_ty TSty lean_ty TKind lean_ty TSty;
  (* the default of a type is its first constructor that does not use terms *)
  List.iter
    (fun d ->
      match
        List.find_opt
          (fun c -> not (List.exists (fun a -> uses_term (arg_ty a)) c.c_args))
          (constrs_of d)
      with
      | Some c ->
          pf ft "instance : Inhabited %s := ⟨.%s%s⟩@ " (decl_lean_name d)
            c.c_name
            (String.concat "" (List.map (fun _ -> " default") c.c_args))
      | None -> ())
    mutual;
  pf ft "instance : Inhabited Term := ⟨.mk default default⟩@ @ end %s@]@."
    (root ())

(** [Signatures.lean]: checks that [Prims.lean] defines the primitives (other
    than the oracles, which are fields of [Oracle]), with their types. *)
let signatures ~sources ft (p : program) =
  let p = modelled p in
  lean_header ~sources ft [ md "Prims" ];
  pf ft
    "/-! The primitives of the rules, with the types they are declared with. \
     -/@ @ noncomputable section@ @ ";
  List.iter
    (fun (q : prim) ->
      if not q.oracle then (
        pf ft "example : ";
        List.iter (fun t -> pf ft "%a → " lean_ty t) q.pargs;
        pf ft "%a := %s@ " lean_ty q.pret q.pname))
    p.prims;
  pf ft "@ end@ @ end %s@]@." (root ())

(* ---------------------------------------------------------------- *)
(* [Typing.lean]: the typing of the operators *)

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

let uniq l =
  List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [ x ]) [] l

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
let typing_rhs ctx (ty : typing) =
  let names = typing_names (List.length ty.t_sorts - 1) in
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
  List.iter2
    (fun name (s : expr) ->
      (* the condition, between the operands and the result *)
      if name = result_name then cond ();
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
    names ty.t_sorts;
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

(** [Typing.lean]: the typing predicates [OpK.WT] of the types of operators,
    over the sorts of the operands and of the result; the operands of an n-ary
    operator ([OpN]) all have its first sort. *)
let typing_file ~sources ft (p : program) =
  let p = modelled p in
  let ctx = classify p in
  header ~sources ft [ md "Prims" ];
  let types = uniq (List.map (fun t -> t.t_constr.c_res) p.typing) in
  List.iter
    (fun res ->
      let tys = List.filter (fun t -> t.t_constr.c_res = res) p.typing in
      let names = typing_names (List.length (List.hd tys).t_sorts - 1) in
      pf ft "@[<v 2>def %a.WT : %a → %sProp" lean_ty res lean_ty res
        (String.concat "" (List.map (fun _ -> "Ty → ") names));
      let alts =
        List.map
          (fun ty ->
            let rhs = typing_rhs ctx ty in
            let used =
              uniq
                (List.concat_map expr_vars ty.t_sorts
                @ Option.fold ~none:[] ~some:expr_vars ty.t_when)
            in
            let pat =
              String.concat ""
                (List.map
                   (fun x -> if List.mem x used then " " ^ id x else " _")
                   ty.t_params)
            in
            ( Printf.sprintf ".%s%s, %s" ty.t_constr.c_name pat
                (String.concat ", " names),
              rhs ))
          tys
      in
      (* consecutive operators with the same typing share it *)
      let rec groups = function
        | [] -> []
        | (p, r) :: rest -> (
            match groups rest with
            | (ps, r') :: g when r' = r -> (p :: ps, r) :: g
            | g -> ([ p ], r) :: g)
      in
      (* one alternative per line, when several share a typing *)
      List.iter
        (fun (ps, r) ->
          List.iter (fun p -> pf ft "@ | %s" p) ps;
          pf ft " =>@;<1 4>%s" r)
        (groups alts);
      pf ft "@]@ @ ")
    types;
  pf ft "end %s@]@." (root ())
