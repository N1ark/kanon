(** Front-end: converts the OCaml parse tree of a Kanon file into typed Kanon
    ({!Syntax}), rejecting anything outside of the language. *)

open Ppxlib
open Syntax

exception Error of Location.t * string

let error loc fmt = Fmt.kstr (fun s -> raise (Error (loc, s))) fmt

(* ---------------------------------------------------------------- *)
(* Several errors at once

   The command line stops at the first error. The language server instead
   collects the errors of the parts of a language that are checked
   independently (its items, its functions), as long as what the other parts
   depend on could be built: the checks are done in phases, and a phase only
   starts if the previous ones had no error, so that an error does not cause
   others. *)

(** The errors collected so far, when they are ([None] on the command line). *)
let collected : (Location.t * string) list option ref = ref None

(** A phase had errors. *)
exception Stop

(** [attempt f] is [Some (f ())], or [None] if [f] fails while errors are
    collected, which records its error. *)
let attempt f =
  match !collected with
  | None -> Some (f ())
  | Some l -> (
      try Some (f ())
      with Error (loc, msg) ->
        collected := Some ((loc, msg) :: l);
        None)

(** The end of a phase: stops if it had errors. *)
let checkpoint () =
  match !collected with Some (_ :: _) -> raise Stop | _ -> ()

(** The errors of [f x], in the order they were found, without duplicates. *)
let collect_errors f x =
  collected := Some [];
  let errors =
    Fun.protect
      ~finally:(fun () -> collected := None)
      (fun () ->
        match f x with
        | () | (exception Stop) -> Option.get !collected
        | exception Error (loc, msg) -> (loc, msg) :: Option.get !collected)
  in
  List.fold_left
    (fun acc e -> if List.mem e acc then acc else acc @ [ e ])
    [] (List.rev errors)

let pp_loc ft (loc : Location.t) =
  let p = loc.loc_start in
  Fmt.pf ft "%s:%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

(* ---------------------------------------------------------------- *)
(* Types *)

(** The file of the functions that Kanon gives the language (see [comm_fns]),
    which may name the type of kinds. *)
let kanon_file = "<kanon>"

(** The type of the declaration [name] of the language. *)
let ty_of_decl = function "kind" -> TKind | "ty" -> TSty | s -> TData s

let ty_of_name = function
  | "int" -> Some TInt
  | "bool" -> Some TBool
  | "unit" -> Some TUnit
  | "t" -> Some TTerm
  | "kind" -> None
  | s when Option.is_some (find_decl s) -> Some (ty_of_decl s)
  | _ -> None

let rec ty_of_core (ct : core_type) : Syntax.ty =
  match ct.ptyp_desc with
  | Ptyp_constr ({ txt = Lident "kind"; loc }, [])
    when loc.loc_start.pos_fname = kanon_file ->
      TKind
  | Ptyp_constr ({ txt = Lident s; _ }, []) when Option.is_some (ty_of_name s)
    ->
      Option.get (ty_of_name s)
  | Ptyp_constr ({ txt = Lident "list"; _ }, [ t ]) -> TList (ty_of_core t)
  | Ptyp_constr ({ txt = Lident "option"; _ }, [ t ]) -> TOption (ty_of_core t)
  | Ptyp_tuple l -> TTuple (List.map ty_of_core l)
  | _ -> error ct.ptyp_loc "unsupported type"

(** Types of the arguments and result of an arrow type. *)
let rec arrow_of_core (ct : core_type) =
  match ct.ptyp_desc with
  | Ptyp_arrow (Nolabel, a, r) ->
      let args, ret = arrow_of_core r in
      (ty_of_core a :: args, ret)
  | _ -> ([], ty_of_core ct)

let rec ty_equal a b =
  match (a, b) with
  | TTuple l1, TTuple l2 ->
      List.length l1 = List.length l2 && List.for_all2 ty_equal l1 l2
  | TOption a, TOption b | TList a, TList b -> ty_equal a b
  | _ -> a = b

(** The fields of a record type, with their types. *)
let record_fields = function TData _ as t -> (decl_of_ty t).d_fields | _ -> []

let expect loc ~expected ty =
  if not (ty_equal expected ty) then
    error loc "type mismatch: expected %a, got %a" pp_ty expected pp_ty ty

(* ---------------------------------------------------------------- *)
(* Environments *)

type sig_ = { args : Syntax.ty list; ret : Syntax.ty }

(** What is known of the sorts of the terms of a position (of a pattern, or of a
    variable): the head constructor of their sort ([TBitVector]), or of the
    sorts of the components of a tuple, or of the elements of a list of terms.
    The literals of patterns are resolved with it (see [resolve_notation]). *)
type psort = Unknown | Head of string | Tuple of psort list | Elems of psort

type env = {
  vars : (string * Syntax.ty) list;
  sorts : (string * psort) list;  (** of the variables, when it is known *)
  locals : (string * sig_) list;
  globals : (string * sig_) list;  (** functions and primitives *)
}

let find_global env loc name =
  match List.assoc_opt name env.globals with
  | Some s -> s
  | None -> error loc "unknown function %s" name

(* ---------------------------------------------------------------- *)
(* Patterns *)

(** Whether the function being checked is a [[@cases]] one, where [[@comm]] only
    swaps the operands of commutative operators. *)
let cases_mode = ref false

let pid_counter = ref 0

let next_pid () =
  incr pid_counter;
  !pid_counter

let rule_name_of_attrs (attrs : attributes) =
  List.find_map
    (fun (a : attribute) ->
      if a.attr_name.txt = "r" then
        match a.attr_payload with
        | PStr
            [
              { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_ident id; _ }, _); _ };
            ] ->
            Some (Longident.name id.txt)
        | _ -> error a.attr_loc "expected [@r name]"
      else None)
    attrs

let constr_args ?(any = fun _ -> false) loc (c : constr) (arg : 'a option)
    (split : 'a -> 'a list option) =
  let n = List.length c.c_args in
  let args =
    match arg with
    | None -> []
    | Some a when n > 1 && any a -> List.init n (fun _ -> a)
    | Some a when n > 1 -> (
        match split a with
        | Some l -> l
        | None -> error loc "constructor %s expects %d arguments" c.c_name n)
    | Some a -> [ a ]
  in
  if List.length args <> n then
    error loc "constructor %s expects %d arguments" c.c_name n;
  args

let split_ppat (p : pattern) =
  match p.ppat_desc with Ppat_tuple l -> Some l | _ -> None

let split_pexp (e : expression) =
  match e.pexp_desc with Pexp_tuple l -> Some l | _ -> None

(** Operators are node constructors: [Add (c, l, r)] stands for
    [Op2 (Add c, l, r)], [Not p] for [Op1 (Not, p)], etc. (see
    [Syntax.lang.node_kinds]). *)
let node_of_op (op : constr) =
  List.find_map
    (fun k ->
      let kc = Option.get (find_constr k) in
      match kc.c_args with
      | Arg t :: operands when t = op.c_res ->
          Some (kc, List.map arg_ty operands)
      | _ -> None)
    !lang.node_kinds

(** Whether a pattern matches anything: [_], or a tuple of blanks, at any depth
    (see {!Syntax.is_catch_all}, on converted patterns). *)
let rec is_blank (p : pattern) =
  match p.ppat_desc with
  | Ppat_any -> true
  | Ppat_tuple l -> List.for_all is_blank l
  | _ -> false

(** The cases that [extend] added, by location, and the function they extend,
    which must not be left out as unreachable. *)
let extension_cases : (Location.t * string) list ref = ref []

let has_attr name (attrs : attributes) =
  List.exists (fun (a : attribute) -> a.attr_name.txt = name) attrs

let strip_attr name (p : pattern) =
  {
    p with
    ppat_attributes =
      List.filter
        (fun (a : attribute) -> a.attr_name.txt <> name)
        p.ppat_attributes;
  }

(** How many times each variable is bound in the pattern of the case being
    checked. *)
let case_vars : (string, int) Hashtbl.t = Hashtbl.create 8

let count_vars (p : pattern) =
  Hashtbl.reset case_vars;
  let add x =
    Hashtbl.replace case_vars x
      (1 + Option.value ~default:0 (Hashtbl.find_opt case_vars x))
  in
  object
    inherit Ast_traverse.iter as super

    method! pattern p =
      (match p.ppat_desc with
      | Ppat_var { txt; _ } | Ppat_alias (_, { txt; _ }) -> add txt
      | _ -> ());
      super#pattern p
  end
    #pattern
    p

(** The typings of the nodes, from which the sorts of the terms that rules build
    are inferred, and the literals of patterns resolved. *)
let node_typings : (string * typing) list ref = ref []

(** The sorts of the components of the position [s], if it is a tuple of [n]. *)
let components n = function
  | Tuple l when List.length l = n -> l
  | _ -> List.init n (fun _ -> Unknown)

let elements = function Elems s -> s | _ -> Unknown

(** The sorts of the operands of the node [name] at a position of sort [sort],
    from its typing: the head constructors of their sorts, where a variable
    stands for the head of [sort] if it is the result of the node. *)
let operand_sorts name sort n_operands =
  match List.assoc_opt name !node_typings with
  | Some t when List.length t.t_sorts > 1 ->
      let result = List.nth t.t_sorts (List.length t.t_sorts - 1) in
      let head (s : Syntax.expr) =
        match (s.e, result.e, sort) with
        | EConstr (c, _), _, _ -> Head c.c_name
        | EVar x, EVar y, Head h when x = y -> Head h
        | _ -> Unknown
      in
      if t.t_nary then [ Elems (head (List.hd t.t_sorts)) ]
      else List.filteri (fun i _ -> i < n_operands) (List.map head t.t_sorts)
  | _ -> List.init n_operands (fun _ -> Unknown)

(** The head constructor of the sort of the result of the node [c], in its
    typing, if it is not a variable. *)
let result_head c =
  match List.assoc_opt c !lang.raw_typing with
  | Some rt -> (
      match List.rev rt.rt_sorts with
      | { pexp_desc = Pexp_construct ({ txt = Lident h; _ }, _); _ } :: _ ->
          Some h
      | _ -> None)
  | None -> None

(** The type of the argument of the notation [c]: [int] or [bool]. *)
let notation_ty c =
  match find_constr c with Some { c_args = [ Arg t ]; _ } -> t | _ -> TInt

(** The notation that the literal [what] of a pattern stands for: among the
    notations of its kind ([`Int] for numerals, [`Bool] for [true] and [false],
    [`Any] for [#x]), the only one, or else the one whose result has the head
    [sort], the sort of the position, if it is known. *)
let resolve_notation loc ~what ~lit ~sort =
  let cands =
    List.filter
      (fun c ->
        match lit with
        | `Any -> true
        | `Int -> notation_ty c = TInt
        | `Bool -> notation_ty c = TBool)
      !lang.notations
  in
  let arg =
    match what.[0] with
    | '#' -> String.sub what 1 (String.length what - 1)
    | _ -> what
  in
  let nodes cs = String.concat " or " (List.map (fun c -> c ^ " " ^ arg) cs) in
  let names cs = String.concat ", " cs in
  match (cands, sort) with
  | [], _ ->
      error loc
        "%s: no notation stands for %s; declare one with notation C, for a \
         leaf node C of one %s"
        what
        (match lit with
        | `Int -> "integers"
        | `Bool -> "booleans"
        | `Any -> "literals")
        (match lit with
        | `Bool -> "bool"
        | `Int -> "int"
        | `Any -> "int or bool")
  | [ c ], _ -> c
  | cs, Head h -> (
      match List.filter (fun c -> result_head c = Some h) cs with
      | [ c ] -> c
      | [] ->
          error loc
            "%s: none of the notations %s has the sort %s of this position; \
             write the node (%s)"
            what (names cs) h (nodes cs)
      | cs ->
          error loc
            "%s: the notations %s have the sort %s of this position; write the \
             node (%s)"
            what (names cs) h (nodes cs))
  | cs, _ ->
      error loc
        "%s may be a literal of %s, and the sort of this position is unknown; \
         write the node (%s)"
        what (String.concat " or " cs) (nodes cs)

(** The variables bound at positions of known sorts by the patterns converted
    since it was last emptied. *)
let pat_sorts : (string * psort) list ref = ref []

(** Whether swapping two operands matches the same terms: when they are
    wildcards or variables bound nowhere else. *)
let swap_is_trivial (a : Syntax.pat) (b : Syntax.pat) =
  let once (p : Syntax.pat) =
    match p.p with
    | PAny -> true
    | PVar x -> Option.value ~default:1 (Hashtbl.find_opt case_vars x) = 1
    | _ -> false
  in
  once a && once b

(** Converts a pattern at the expected type. The operands of commutative
    operators are matched in either order. *)
let rec pat ?(sort = Unknown) (expected : Syntax.ty) (p : pattern) : Syntax.pat
    =
  let comm ~explicit (q : Syntax.pat) =
    let swapped =
      match q.p with
      | PTuple [ a; b ] when explicit -> Some (PTuple [ b; a ])
      | PConstr (c, [ op; a; b ]) when List.mem c.c_name !lang.node_kinds -> (
          match op.p with
          | PConstr (o, _) when is_commutative o.c_name ->
              if explicit || not (swap_is_trivial a b) then
                Some (PConstr (c, [ op; b; a ]))
              else None
          | PConstr (o, _) when explicit && !cases_mode ->
              error p.ppat_loc "[@comm]: %s is not commutative" o.c_name
          | PConstr _ when explicit -> Some (PConstr (c, [ op; b; a ]))
          | _ when explicit -> error p.ppat_loc "[@comm]: unknown operator"
          | _ -> None)
      | _ when explicit ->
          error p.ppat_loc "[@comm] applies to pairs and binary operators"
      | _ -> None
    in
    match swapped with
    | Some s -> { q with p = PComm (q, { q with p = s }); pid = next_pid () }
    | None -> q
  in
  if has_attr "comm" p.ppat_attributes then
    (* [p [@comm]]: the components of a pair in either order *)
    comm ~explicit:true (pat' ~sort expected (strip_attr "comm" p))
  else comm ~explicit:false (pat' ~sort expected p)

and pat' ~sort (expected : Syntax.ty) (p : pattern) : Syntax.pat =
  let loc = p.ppat_loc in
  let mk d = { p = d; pty = expected; ploc = loc; pid = next_pid () } in
  (* the literal [arg] of the notation that [what] resolves to *)
  let literal ~what ~lit (arg : pattern) =
    let c = Option.get (find_constr (resolve_notation loc ~what ~lit ~sort)) in
    mk (PConstr (c, [ pat (arg_ty (List.hd c.c_args)) arg ]))
  in
  match p.ppat_desc with
  | Ppat_constant (Pconst_integer (s, None)) when expected = TTerm ->
      literal ~what:s ~lit:`Int p
  | Ppat_construct ({ txt = Lident (("true" | "false") as b); _ }, None)
    when expected = TTerm ->
      literal ~what:b ~lit:`Bool p
  | Ppat_construct ({ txt = Lident "#"; _ }, Some (_, arg)) ->
      if expected <> TTerm then
        error loc "a literal #x matches a term, not a value of type %a" pp_ty
          expected;
      let what =
        match arg.ppat_desc with Ppat_var x -> "#" ^ x.txt | _ -> "#_"
      in
      literal ~what ~lit:`Any arg
  | Ppat_construct ({ txt = Lident name; _ }, arg)
    when (expected = TTerm || expected = TKind)
         && Option.fold ~none:false
              ~some:(fun c -> Option.is_some (node_of_op c))
              (find_constr name) ->
      let op = Option.get (find_constr name) in
      let kc, operand_tys = Option.get (node_of_op op) in
      let nparams = List.length op.c_args in
      let n = nparams + List.length operand_tys in
      let args =
        match arg with
        | None -> error loc "%s: missing operands" name
        | Some (_, ({ ppat_desc = Ppat_any; _ } as a)) ->
            List.init n (fun _ -> a)
        | Some (_, a) when n = 1 -> [ a ]
        | Some (_, { ppat_desc = Ppat_tuple l; _ }) when List.length l = n -> l
        | Some _ -> error loc "%s expects %d arguments" name n
      in
      let params = List.filteri (fun i _ -> i < nparams) args in
      let operands = List.filteri (fun i _ -> i >= nparams) args in
      let params = List.map2 (fun a p -> pat (arg_ty a) p) op.c_args params in
      let op_pat =
        {
          p = PConstr (op, params);
          pty = op.c_res;
          ploc = loc;
          pid = next_pid ();
        }
      in
      let sorts = operand_sorts name sort (List.length operand_tys) in
      let operands =
        List.map2
          (fun (t, sort) p -> pat ~sort t p)
          (List.combine operand_tys sorts)
          operands
      in
      mk (PConstr (kc, op_pat :: operands))
  | Ppat_any -> mk PAny
  | Ppat_var { txt; _ } ->
      if sort <> Unknown then pat_sorts := (txt, sort) :: !pat_sorts;
      mk (PVar txt)
  | Ppat_alias (p, { txt; _ }) ->
      if sort <> Unknown then pat_sorts := (txt, sort) :: !pat_sorts;
      mk (PAs (pat ~sort expected p, txt))
  | Ppat_or (p1, p2) ->
      let p1 = pat ~sort expected p1 and p2 = pat ~sort expected p2 in
      let b1 = binders p1 and b2 = binders p2 in
      let sort = List.sort_uniq compare in
      if sort (List.map fst b1) <> sort (List.map fst b2) then
        error loc "or-pattern alternatives bind different variables";
      List.iter
        (fun (x, (t, small)) ->
          let t', small' = List.assoc x b2 in
          expect loc ~expected:t t';
          if small <> small' then
            error loc "variable %s bound at different integer kinds" x)
        b1;
      mk (POr (p1, p2))
  | Ppat_constant (Pconst_integer (s, None)) ->
      expect loc ~expected TInt;
      mk (PInt (Z.of_string s))
  | Ppat_tuple l -> (
      match expected with
      | TTuple tys when List.length tys = List.length l ->
          mk
            (PTuple
               (List.map2
                  (fun (t, sort) p -> pat ~sort t p)
                  (List.combine tys (components (List.length l) sort))
                  l))
      | _ -> error loc "unexpected tuple pattern at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident (("true" | "false") as b); _ }, None) ->
      expect loc ~expected TBool;
      mk (PBool (b = "true"))
  | Ppat_construct ({ txt = Lident "()"; _ }, None) ->
      expect loc ~expected TUnit;
      mk PUnit
  | Ppat_construct ({ txt = Lident "None"; _ }, None) -> (
      match expected with
      | TOption _ -> mk PNone
      | _ -> error loc "None at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident "Some"; _ }, Some (_, p)) -> (
      match expected with
      | TOption t -> mk (PSome (pat t p))
      | _ -> error loc "Some at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident "[]"; _ }, None) -> (
      match expected with
      | TList _ -> mk PNil
      | _ -> error loc "[] at type %a" pp_ty expected)
  | Ppat_construct
      ( { txt = Lident "::"; _ },
        Some (_, { ppat_desc = Ppat_tuple [ h; tl ]; _ }) ) -> (
      match expected with
      | TList t ->
          mk (PCons (pat ~sort:(elements sort) t h, pat ~sort expected tl))
      | _ -> error loc ":: at type %a" pp_ty expected)
  | Ppat_construct ({ txt = Lident name; loc = cloc }, arg) -> (
      match find_constr name with
      | None -> error cloc "unknown constructor %s" name
      | Some c ->
          (* kind constructors can be matched against terms *)
          let ok =
            ty_equal c.c_res expected || (c.c_res = TKind && expected = TTerm)
          in
          if (not ok) && c.c_res = TSty && expected = TTerm then
            error cloc "%s is a sort, not a node" name;
          if not ok then
            error loc "constructor %s has type %a, expected %a" name pp_ty
              c.c_res pp_ty expected;
          let is_any (p : pattern) = p.ppat_desc = Ppat_any in
          let args =
            constr_args ~any:is_any loc c (Option.map snd arg) split_ppat
          in
          let args = List.map2 (fun a p -> pat (arg_ty a) p) c.c_args args in
          List.iter2
            (fun a (p : Syntax.pat) ->
              match (a, p.p) with
              | Small, (PAny | PVar _ | PInt _) -> ()
              | Small, _ ->
                  error p.ploc
                    "only variables, wildcards and literals can match \
                     machine-integer fields"
              | _ -> ())
            c.c_args args;
          mk (PConstr (c, args)))
  | Ppat_record (fields, _) ->
      let known = record_fields expected in
      if known = [] then
        error loc "unexpected record pattern at type %a" pp_ty expected;
      let fields =
        List.map
          (fun (({ txt; loc } : longident loc), p) ->
            let f = Longident.name txt in
            match List.assoc_opt f known with
            | Some t -> (f, pat t p)
            | None -> error loc "unknown field %s" f)
          fields
      in
      mk (PRecord fields)
  | Ppat_constraint (p, ct) ->
      expect loc ~expected (ty_of_core ct);
      pat ~sort expected p
  | _ -> error loc "unsupported pattern"

(** Variables bound by a pattern, with their type and whether they are bound to
    a machine-integer field. *)
and binders (p : Syntax.pat) : (string * (Syntax.ty * bool)) list =
  match p.p with
  | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> []
  | PVar x -> [ (x, (p.pty, false)) ]
  | PAs (p', x) -> (x, (p.pty, false)) :: binders p'
  | POr (p1, _) | PComm (p1, _) -> binders p1
  | PTuple l -> List.concat_map binders l
  | PSome p -> binders p
  | PCons (a, b) -> binders a @ binders b
  | PRecord l -> List.concat_map (fun (_, p) -> binders p) l
  | PConstr (c, args) ->
      List.concat
        (List.map2
           (fun a p ->
             match (a, p.p) with
             | Small, PVar x -> [ (x, (TInt, true)) ]
             | _ -> binders p)
           c.c_args args)

(** The variables bound by the sorts of the operands of the spec of the rule
    being checked (see [sort_binds]), and the values they stand for. *)
let sort_vars : (string * Syntax.expr) list ref = ref []

let no_shadow env loc x =
  if List.mem_assoc x env.globals then
    error loc "%s shadows a global function" x;
  if List.mem_assoc x !sort_vars then
    error loc "%s shadows a variable of the sort of an operand" x

(** The location of the first binding of [x] in [p], if any. *)
let rec binder_loc x (p : Syntax.pat) =
  match p.p with
  | PVar y -> if x = y then Some p.ploc else None
  | PAs (q, y) -> if x = y then Some p.ploc else binder_loc x q
  | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> None
  | PSome q -> binder_loc x q
  | POr (a, _) | PComm (a, _) -> binder_loc x a
  | PTuple l | PConstr (_, l) -> List.find_map (binder_loc x) l
  | PCons (a, b) -> List.find_map (binder_loc x) [ a; b ]
  | PRecord l -> List.find_map (fun (_, q) -> binder_loc x q) l

let add_binders ?(sorts = []) env p =
  let bs =
    List.fold_left
      (fun acc (x, b) -> if List.mem_assoc x acc then acc else acc @ [ (x, b) ])
      [] (binders p)
  in
  List.iter
    (fun (x, _) ->
      no_shadow env (Option.value (binder_loc x p) ~default:p.ploc) x)
    bs;
  {
    env with
    vars = List.map (fun (x, (t, _)) -> (x, t)) bs @ env.vars;
    sorts =
      List.map
        (fun (x, _) ->
          (x, Option.value (List.assoc_opt x sorts) ~default:Unknown))
        bs
      @ env.sorts;
  }

(** The sort of the terms of the expression [e], when it is a variable (or a
    tuple of them) whose sort is known. *)
let rec sort_of env (e : expression) =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } ->
      Option.value (List.assoc_opt x env.sorts) ~default:Unknown
  | Pexp_tuple l -> Tuple (List.map (sort_of env) l)
  | _ -> Unknown

(** Converts the pattern [p], at the type [t] and the sort [sort], and adds its
    binders to [env]. *)
let bind_pat env ?sort t p =
  pat_sorts := [];
  let p = pat ?sort t p in
  (p, add_binders ~sorts:!pat_sorts env p)

(** Types on which [=] and [<>] are allowed: all but the abstract types marked
    [[@noeq]], whose equalities in OCaml and in Lean may differ, and the types
    made of them. On terms, [=] is the equality of hash-consed terms. *)
let rec eq_ty = function
  | TInt | TBool | TUnit | TTerm | TKind -> true
  | (TSty | TData _) as t -> (decl_of_ty t).d_eq
  | TTuple l -> List.for_all eq_ty l
  | TOption t | TList t -> eq_ty t

(* ---------------------------------------------------------------- *)
(* Desugaring of patterns

   A case is compiled to one case per alternative of its or-patterns (so a
   guard that fails on one alternative lets the next alternative be tried).
   Each alternative is then made linear and free of integer literals: a
   repeated variable is renamed and constrained to be equal to its first
   occurrence ([=], which is the equality of hash-consed terms on terms), and a
   literal becomes a variable constrained to be equal to it. These constraints are checked, in order,
   before the guard. *)

let rec product = function
  | [] -> [ [] ]
  | x :: xs ->
      let rest = product xs in
      List.concat_map (fun a -> List.map (fun r -> a :: r) rest) x

(** A name for what a pattern matches: its head constructor, or operator. *)
let rec pat_head (p : Syntax.pat) =
  match p.p with
  | PConstr (c, op :: _) when List.mem c.c_name !lang.node_kinds -> pat_head op
  | PConstr (c, _) -> String.uncapitalize_ascii c.c_name
  | PAs (q, _) -> pat_head q
  | PBool b -> string_of_bool b
  | PInt _ -> "int"
  | PTuple l -> String.concat "_" (List.map pat_head l)
  | PSome _ -> "some"
  | PNone -> "none"
  | PNil -> "nil"
  | PCons _ -> "cons"
  | PAny | PVar _ | PUnit | PRecord _ -> "any"
  | POr _ | PComm _ -> ""

(** The alternatives of a pattern, each with the choices made (see
    [Syntax.case.alt]). A side of an or-pattern is named after its head, with
    its index if both sides have the same head (and not named if it is itself an
    or-pattern); the swapped side of a [[@comm]] pattern is named [swap]. *)
let rec alternatives (p : Syntax.pat) :
    (Syntax.pat * (int * int * bool * string) list) list =
  let mk d = { p with p = d } in
  let one d = [ (mk d, []) ] in
  let prod l =
    List.map
      (fun choices -> (List.map fst choices, List.concat_map snd choices))
      (product (List.map alternatives l))
  in
  match p.p with
  | PAny | PVar _ | PInt _ | PBool _ | PUnit | PNone | PNil -> one p.p
  | POr (a, b) | PComm (a, b) ->
      let comm = match p.p with PComm _ -> true | _ -> false in
      let name i q =
        if comm then if i = 1 then "swap" else ""
        else if pat_head a = pat_head b then pat_head q ^ string_of_int (i + 1)
        else pat_head q
      in
      let side i q =
        List.map
          (fun (q, t) -> (q, (p.pid, i, comm, name i q) :: t))
          (alternatives q)
      in
      side 0 a @ side 1 b
  | PAs (q, x) -> List.map (fun (q, t) -> (mk (PAs (q, x)), t)) (alternatives q)
  | PTuple l -> List.map (fun (l, t) -> (mk (PTuple l), t)) (prod l)
  | PSome q -> List.map (fun (q, t) -> (mk (PSome q), t)) (alternatives q)
  | PCons (a, b) ->
      List.map
        (function [ a; b ], t -> (mk (PCons (a, b)), t) | _ -> assert false)
        (prod [ a; b ])
  | PRecord fs ->
      List.map
        (fun (ps, t) -> (mk (PRecord (List.combine (List.map fst fs) ps)), t))
        (prod (List.map snd fs))
  | PConstr (c, args) ->
      List.map (fun (l, t) -> (mk (PConstr (c, l)), t)) (prod args)

(* A repeated variable keeps its name at its occurrence of smallest [pid], and
   fresh names are made from [pid]s: the alternatives of a [[@comm]] pattern
   then name the same subpatterns the same way, whatever their order, and
   generated names are stable (pids are numbered per case). The constraints are
   ordered by [pid] too. *)
let linearize (p : Syntax.pat) : Syntax.pat * Syntax.expr list =
  let keeper = Hashtbl.create 8 and conds = ref [] in
  let rec collect (p : Syntax.pat) =
    let note x =
      match Hashtbl.find_opt keeper x with
      | Some q when q <= p.pid -> ()
      | _ -> Hashtbl.replace keeper x p.pid
    in
    match p.p with
    | PVar x -> note x
    | PAs (q, x) ->
        note x;
        collect q
    | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> ()
    | POr _ | PComm _ -> assert false
    | PTuple l | PConstr (_, l) -> List.iter collect l
    | PSome q -> collect q
    | PCons (a, b) ->
        collect a;
        collect b
    | PRecord fs -> List.iter (fun (_, q) -> collect q) fs
  in
  collect p;
  let fresh (p : Syntax.pat) = Printf.sprintf "kanon__%d" p.pid in
  let v loc t x = { e = EVar x; ety = t; eloc = loc } in
  let eq (p : Syntax.pat) t a b =
    let d =
      if eq_ty t then EBinop (Eq, a, b)
      else error p.ploc "non-linear pattern at type %a" pp_ty t
    in
    conds := (p.pid, { e = d; ety = TBool; eloc = p.ploc }) :: !conds
  in
  let bind (p : Syntax.pat) x =
    if Hashtbl.find keeper x = p.pid then x
    else
      let x' = fresh p in
      eq p p.pty (v p.ploc p.pty x) (v p.ploc p.pty x');
      x'
  in
  let rec go (p : Syntax.pat) : Syntax.pat =
    let mk d = { p with p = d } in
    match p.p with
    | PAny | PBool _ | PUnit | PNone | PNil -> p
    | PVar x -> mk (PVar (bind p x))
    | PInt z ->
        let x = fresh p in
        eq p TInt (v p.ploc TInt x) { e = EInt z; ety = TInt; eloc = p.ploc };
        mk (PVar x)
    | PAs (q, x) ->
        let q = go q in
        mk (PAs (q, bind p x))
    | POr _ | PComm _ -> assert false
    | PTuple l -> mk (PTuple (List.map go l))
    | PSome q -> mk (PSome (go q))
    | PCons (a, b) ->
        let a = go a in
        mk (PCons (a, go b))
    | PRecord fs -> mk (PRecord (List.map (fun (f, p) -> (f, go p)) fs))
    | PConstr (c, args) -> mk (PConstr (c, List.map go args))
  in
  let p = go p in
  (p, List.map snd (List.sort (fun (a, _) (b, _) -> compare a b) !conds))

let conj (l : Syntax.expr list) : Syntax.expr option =
  match l with
  | [] -> None
  | x :: xs ->
      Some
        (List.fold_left
           (fun acc (y : Syntax.expr) ->
             { e = EBinop (And, acc, y); ety = TBool; eloc = y.eloc })
           x xs)

(* ---------------------------------------------------------------- *)
(* Expressions *)

(** The operators built into Kanon, on integers and booleans, with the types of
    their operands and of their result. The prefix [-] and [not] are built in
    too, and [=] and [<>] are at every type (see [eq_ty]). *)
let builtin_ops =
  [
    ("+", (TInt, TInt, Add));
    ("-", (TInt, TInt, Sub));
    ("*", (TInt, TInt, Mul));
    ("<", (TInt, TBool, Lt));
    ("<=", (TInt, TBool, Le));
    (">", (TInt, TBool, Gt));
    (">=", (TInt, TBool, Ge));
    ("&&", (TBool, TBool, And));
    ("||", (TBool, TBool, Or));
  ]

(** What the lexer reads [sym] as: an infix symbol, a word, a prefix symbol, or
    [-], which is both infix and prefix. *)
let op_kind sym =
  let open Kanon_parser in
  let lb = Lexing.from_string sym in
  let token () =
    try Some (Kanon_lexer.token lb) with Kanon_lexer.Error _ -> None
  in
  let first = token () in
  match (first, token ()) with
  | ( Some
        ( PLUS | STAR | ANDAND | BARBAR | CMPOP _ | CONCATOP _ | ADDOP _
        | MULOP _ | POWOP _ ),
      Some EOF ) ->
      `Infix
  | Some (LID _ | INFIXWORD _), Some EOF
    when match sym.[0] with 'a' .. 'z' -> true | _ -> false ->
      `Word
  | Some (NOT | PREFIXOP _), Some EOF -> `Prefix
  | Some MINUS, Some EOF -> `Minus
  | _ -> `None

(** Whether [sym] is an operator on [arity] operands: an infix symbol, a word
    declared infix, or a prefix symbol. The parser gives the prefix [-] its
    OCaml name, [~-]. *)
let is_operator ~arity sym =
  match op_kind sym with
  | `Infix -> arity = 2
  | `Word -> arity = 2 && Hashtbl.mem infix_words sym
  | `Prefix -> arity = 1
  | `Minus -> arity = 2
  | `None -> false

(** How an operator is written. *)
let op_name ~arity op =
  if arity = 1 then "prefix " ^ if op = "~-" then "-" else op else op

(** The built-in meaning of the operator [op] on [arity] operands: the type of
    its operands, and of its result. *)
let builtin_op ~arity op =
  match (arity, op) with
  | 2, _ -> Option.map (fun (a, r, _) -> (a, r)) (List.assoc_opt op builtin_ops)
  | 1, "not" -> Some (TBool, TBool)
  | 1, "~-" -> Some (TInt, TInt)
  | _ -> None

(** Whether the operator [op] on [arity] operands has a function on the operands
    that are not terms. *)
let has_value_fn op ~arity =
  match find_operator ~arity op with
  | Some { on_value = Some _; _ } -> true
  | _ -> false

(** The function of the operator [op] on the operands of types [tys], which are
    not terms: the third component of its declaration, if it takes them. *)
let value_fn env loc op tys =
  let arity = List.length tys in
  match find_operator ~arity op with
  | Some { on_value = Some f; _ } ->
      let s = find_global env loc f in
      if List.length s.args = arity && List.for_all2 ty_equal s.args tys then
        Some (f, s.ret)
      else None
  | _ -> None

(** The error of the operator [op] on operands of types [tys], which have no
    meaning. *)
let value_error env loc op tys =
  let arity = List.length tys in
  let pp = Fmt.(list ~sep:(any ", ") pp_ty) in
  match find_operator ~arity op with
  | Some { on_value = Some f; _ } ->
      let s = find_global env loc f in
      error loc "%s is not defined on %a: its function %s takes %a"
        (op_name ~arity op) pp tys f pp s.args
  | _ -> error loc "%s is not defined on %a" (op_name ~arity op) pp tys

(* ---------------------------------------------------------------- *)
(* The sorts of the nodes built in rules *)

(** Counter of the variables that name the arguments of nodes in their sorts,
    reset for each function. *)
let atom_counter = ref 0

let rec expr_vars (e : Syntax.expr) =
  match e.e with
  | EVar x -> [ x ]
  | EConstr (_, l) | ECall (_, l) | ETuple l -> List.concat_map expr_vars l
  | EBinop (_, a, b) -> expr_vars a @ expr_vars b
  | EUnop (_, a) -> expr_vars a
  | EInt _ | EBool _ | EUnit -> []
  | _ -> error e.eloc "unsupported expression in a sort"

let rec subst_vars f (e : Syntax.expr) : Syntax.expr =
  let go = subst_vars f in
  match e.e with
  | EVar x -> Option.value ~default:e (f x)
  | EConstr (c, l) -> { e with e = EConstr (c, List.map go l) }
  | ECall (g, l) -> { e with e = ECall (g, List.map go l) }
  | ETuple l -> { e with e = ETuple (List.map go l) }
  | EBinop (o, a, b) -> { e with e = EBinop (o, go a, go b) }
  | EUnop (o, a) -> { e with e = EUnop (o, go a) }
  | EInt _ | EBool _ | EUnit -> e
  | _ -> error e.eloc "unsupported expression in a sort"

let rec same_expr (a : Syntax.expr) (b : Syntax.expr) =
  let all l m = List.length l = List.length m && List.for_all2 same_expr l m in
  match (a.e, b.e) with
  | EVar x, EVar y -> x = y
  | EInt x, EInt y -> Z.equal x y
  | EBool x, EBool y -> x = y
  | EUnit, EUnit -> true
  | EConstr (c, l), EConstr (d, m) -> c.c_name = d.c_name && all l m
  | ECall (f, l), ECall (g, m) -> f = g && all l m
  | ETuple l, ETuple m -> all l m
  | EBinop (o, a, b), EBinop (p, c, d) ->
      o = p && same_expr a c && same_expr b d
  | EUnop (o, a), EUnop (p, b) -> o = p && same_expr a b
  | _ -> false

(** Whether a spec is being checked: specs compute the arguments of their nodes
    as many times as their sorts need them. *)
let in_spec = ref false

(** Whether [e] is cheap to compute twice: it calls no function. *)
let rec is_atom (e : Syntax.expr) =
  !in_spec
  ||
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> true
  | EConstr (_, l) | ETuple l -> List.for_all is_atom l
  | ECall _ -> false
  | EBinop (_, a, b) -> is_atom a && is_atom b
  | EUnop (_, a) | EField (a, _) -> is_atom a
  | _ -> false

let type_of (e : Syntax.expr) =
  { e = ECall ("type_of", [ e ]); ety = TSty; eloc = e.eloc }

(** The term of the node [name] over [params] and [operands], which [build]
    makes a kind of, at the sort that its typing gives it: the sort of its
    result when it only depends on the parameters, else the sort of an operand
    that has the same sort, else the sort of the result over the variables of
    the sorts of the operands, which it then matches. The arguments that the
    sort needs are bound first, outside specs, when they call functions, so that
    they are computed once. *)
let node_term loc ~name ~build (params : Syntax.expr list)
    (operands : Syntax.expr list) : Syntax.expr =
  let t =
    match List.assoc_opt name !node_typings with
    | Some t -> t
    | None -> error loc "%s has no typing, which would give its sort" name
  in
  let n_ops = List.length t.t_sorts - 1 in
  let result = List.nth t.t_sorts n_ops in
  (* the sort of an operand, which the sort of the result may depend on; not
     that of a list of operands *)
  let op_sorts =
    if t.t_nary then [] else List.filteri (fun i _ -> i < n_ops) t.t_sorts
  in
  let is_var x = List.mem_assoc x t.t_vars in
  let bindings = ref [] in
  let atom (e : Syntax.expr) =
    if is_atom e then e
    else (
      incr atom_counter;
      let x = Printf.sprintf "kanon__a%d" !atom_counter in
      bindings := (x, e) :: !bindings;
      { e with e = EVar x })
  in
  let params = Array.of_list params and operands = Array.of_list operands in
  let used = expr_vars result in
  let param x =
    match List.find_index (( = ) x) t.t_params with
    | Some i when x <> "_" ->
        params.(i) <- atom params.(i);
        Some params.(i)
    | _ -> None
  in
  let operand i =
    operands.(i) <- atom operands.(i);
    operands.(i)
  in
  let fv = List.sort_uniq compare (List.filter is_var used) in
  let sort =
    if fv = [] then subst_vars param result
    else
      (* the operands of the same sort as the result, atoms first *)
      let same =
        List.filteri (fun i _ -> i < Array.length operands) op_sorts
        |> List.mapi (fun i s -> (i, s))
        |> List.filter_map (fun (i, s) ->
            if same_expr result s then Some i else None)
      in
      let same =
        match List.find_opt (fun i -> is_atom operands.(i)) same with
        | None -> List.nth_opt same 0
        | i -> i
      in
      match same with
      | Some i -> type_of (operand i)
      | None ->
          (* the variables of the result read by the getters of the sorts of the
             operands ([[@get]]) *)
          let getters = Hashtbl.create 4 in
          List.iteri
            (fun i (s : Syntax.expr) ->
              match s.e with
              | EConstr (c, [ { e = EVar x; _ } ])
                when i < Array.length operands
                     && List.mem x fv
                     && not (Hashtbl.mem getters x) -> (
                  match List.assoc_opt c.c_name !lang.sort_getters with
                  | Some g ->
                      Hashtbl.add getters x
                        {
                          e = ECall (g, [ operand i ]);
                          ety = List.assoc x t.t_vars;
                          eloc = loc;
                        }
                  | None -> ())
              | _ -> ())
            op_sorts;
          if List.for_all (Hashtbl.mem getters) fv then
            subst_vars
              (fun x ->
                if is_var x then Hashtbl.find_opt getters x else param x)
              result
          else
            (* the variables of the result, bound by the sorts of the
               operands *)
            let svar x = "kanon__" ^ x in
            let bound = Hashtbl.create 4 in
            let rec spat (s : Syntax.expr) : Syntax.pat =
              let mk d = { p = d; pty = s.ety; ploc = s.eloc; pid = 0 } in
              match s.e with
              | EVar x when is_var x && not (Hashtbl.mem bound x) ->
                  Hashtbl.add bound x ();
                  mk (PVar (svar x))
              | EConstr (c, args) when c.c_res = TSty ->
                  mk (PConstr (c, List.map spat args))
              | _ -> mk PAny
            in
            let scruts = ref [] in
            List.iteri
              (fun i s ->
                if
                  i < Array.length operands
                  && List.exists
                       (fun x -> is_var x && not (Hashtbl.mem bound x))
                       (List.filter (fun x -> List.mem x fv) (expr_vars s))
                then scruts := !scruts @ [ (operand i, spat s) ])
              op_sorts;
            List.iter
              (fun x ->
                if not (Hashtbl.mem bound x) then
                  error loc
                    "%s: the sort of its result is not determined; build it at \
                     a sort, (%s ... : S args)"
                    name name)
              fv;
            let body =
              subst_vars
                (fun x ->
                  if is_var x then
                    Some
                      {
                        e = EVar (svar x);
                        ety = List.assoc x t.t_vars;
                        eloc = loc;
                      }
                  else param x)
                result
            in
            let scrut_exprs = List.map (fun (o, _) -> type_of o) !scruts in
            let pats = List.map snd !scruts in
            let pat =
              match pats with
              | [ p ] -> p
              | _ ->
                  {
                    p = PTuple pats;
                    pty = TTuple (List.map (fun _ -> TSty) pats);
                    ploc = loc;
                    pid = 0;
                  }
            in
            let case pat body =
              { pat; guard = None; body; rule = None; cloc = loc; alt = [] }
            in
            let any = { pat with p = PAny } in
            {
              e =
                EMatch
                  ( scrut_exprs,
                    [ case pat body; case any (List.hd scrut_exprs) ] );
              ety = TSty;
              eloc = loc;
            }
  in
  let node =
    {
      e =
        ENode
          ( {
              e = build (Array.to_list params) (Array.to_list operands);
              ety = TKind;
              eloc = loc;
            },
            sort );
      ety = TTerm;
      eloc = loc;
    }
  in
  List.fold_left
    (fun body (x, rhs) ->
      {
        e = ELet ({ p = PVar x; pty = rhs.ety; ploc = loc; pid = 0 }, rhs, body);
        ety = TTerm;
        eloc = loc;
      })
    node !bindings

(** Whether the function being checked is a rule, which builds the nodes of
    commutative operators with their operands in order (see [comm_fns]). *)
let ordered = ref false

let rec expr env ?expected (e : expression) : Syntax.expr =
  let loc = e.pexp_loc in
  let mk ety d =
    Option.iter (fun expected -> expect loc ~expected ety) expected;
    { e = d; ety; eloc = loc }
  in
  (* an operator on terms, if one of its operands is a term *)
  let term_op op (args : Syntax.expr list) =
    let o =
      match find_operator ~arity:(List.length args) op with
      | Some o -> o
      | None ->
          error loc "%s is not an operator on terms"
            (op_name ~arity:(List.length args) op)
    in
    let f = o.smart in
    let s = find_global env loc f in
    (* the leading arguments, in the global scope *)
    let pre = List.map (expr { env with vars = []; locals = [] }) o.pre in
    List.iter
      (fun (a : Syntax.expr) -> expect a.eloc ~expected:TTerm a.ety)
      args;
    let tys = List.map (fun (a : Syntax.expr) -> a.ety) (pre @ args) in
    if
      List.length s.args <> List.length tys
      || (not (List.for_all2 ty_equal s.args tys))
      || s.ret <> TTerm
    then
      error loc "%s: %s is not a smart constructor for these arguments"
        (op_name ~arity:(List.length args) op)
        f;
    mk TTerm (ECall (f, pre @ args))
  in
  let is_term (a : Syntax.expr) = a.ety = TTerm in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } when List.mem_assoc x !sort_vars ->
      let v = List.assoc x !sort_vars in
      mk v.ety v.e
  | Pexp_ident { txt = Lident x; _ } -> (
      match List.assoc_opt x env.vars with
      | Some t -> mk t (EVar x)
      | None -> (
          match List.assoc_opt x env.globals with
          | Some { args = []; ret } -> mk ret (ECall (x, []))
          | _ -> error loc "unbound variable %s" x))
  | Pexp_constant (Pconst_integer (s, None)) -> mk TInt (EInt (Z.of_string s))
  | Pexp_construct ({ txt = Lident (("true" | "false") as b); _ }, None) ->
      mk TBool (EBool (b = "true"))
  | Pexp_construct ({ txt = Lident "()"; _ }, None) -> mk TUnit EUnit
  | Pexp_construct ({ txt = Lident "None"; _ }, None) -> (
      match expected with
      | Some (TOption _ as t) -> mk t ENone
      | _ -> error loc "cannot infer the type of None")
  | Pexp_construct ({ txt = Lident "Some"; _ }, Some a) ->
      let inner =
        match expected with Some (TOption t) -> Some t | _ -> None
      in
      let a = expr env ?expected:inner a in
      mk (TOption a.ety) (ESome a)
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> (
      match expected with
      | Some (TList _ as t) -> mk t ENil
      | _ -> error loc "cannot infer the type of []")
  | Pexp_construct
      ({ txt = Lident "::"; _ }, Some { pexp_desc = Pexp_tuple [ h; tl ]; _ })
    ->
      let inner = match expected with Some (TList t) -> Some t | _ -> None in
      let h = expr env ?expected:inner h in
      let tl = expr env ~expected:(TList h.ety) tl in
      mk tl.ety (ECons (h, tl))
  | Pexp_construct ({ txt = Lident name; _ }, arg)
    when match Option.bind (find_constr name) node_of_op with
         | None -> false
         | Some (_, operands) ->
             let op = Option.get (find_constr name) in
             let nargs =
               match arg with
               | None -> 0
               | Some { pexp_desc = Pexp_tuple l; _ } -> List.length l
               | Some _ -> 1
             in
             nargs = List.length op.c_args + List.length operands ->
      let op = Option.get (find_constr name) in
      let kc, operand_tys = Option.get (node_of_op op) in
      let args =
        match arg with
        | Some { pexp_desc = Pexp_tuple l; _ } -> l
        | Some a -> [ a ]
        | None -> []
      in
      let nparams = List.length op.c_args in
      let params = List.filteri (fun i _ -> i < nparams) args in
      let operands = List.filteri (fun i _ -> i >= nparams) args in
      let params =
        List.map2 (fun a e -> expr env ~expected:(arg_ty a) e) op.c_args params
      in
      let operands =
        List.map2 (fun t e -> expr env ~expected:t e) operand_tys operands
      in
      let build params operands =
        let op = { e = EConstr (op, params); ety = op.c_res; eloc = loc } in
        match operands with
        | [ l; r ] when !ordered && is_commutative name ->
            ECall ("mk_commut_binop", [ op; l; r ])
        | _ -> EConstr (kc, op :: operands)
      in
      if expected = Some TKind then mk TKind (build params operands)
      else mk TTerm (node_term loc ~name ~build params operands).e
  | Pexp_construct ({ txt = Lident name; loc = cloc }, arg) -> (
      match find_constr name with
      | None -> error cloc "unknown constructor %s" name
      | Some c -> (
          let args = constr_args loc c arg split_pexp in
          let args =
            List.map2 (fun a e -> expr env ~expected:(arg_ty a) e) c.c_args args
          in
          match List.assoc_opt name !node_typings with
          | Some t when c.c_res = TKind && expected <> Some TKind ->
              (* a node of kind: the term, at its sort *)
              let n = List.length args - (List.length t.t_sorts - 1) in
              let params = List.filteri (fun i _ -> i < n) args in
              let operands = List.filteri (fun i _ -> i >= n) args in
              let build params operands = EConstr (c, params @ operands) in
              mk TTerm (node_term loc ~name ~build params operands).e
          | None when c.c_res = TKind && expected <> Some TKind ->
              error cloc
                "%s has no typing, which would give the sort of its term" name
          | _ when c.c_res = TSty && expected = Some TTerm ->
              error cloc "%s is a sort, not a node" name
          | _ -> mk c.c_res (EConstr (c, args))))
  | Pexp_apply
      ({ pexp_desc = Pexp_ident { txt = Lident op; loc = fn_loc }; _ }, args)
    -> (
      let args =
        List.map
          (function
            | Nolabel, a -> a
            | _, (a : expression) ->
                error a.pexp_loc "labelled arguments are not supported")
          args
      in
      match (op, args) with
      | ("=" | "<>"), [ a; b ] ->
          let a = expr env a in
          let b = expr env ~expected:a.ety b in
          if not (eq_ty a.ety) then
            error loc "equality is not allowed at type %a" pp_ty a.ety;
          mk TBool (EBinop ((if op = "=" then Eq else Ne), a, b))
      | op, [ a; b ] when is_operator ~arity:2 op -> (
          let a = expr env a in
          let b = expr env b in
          if is_term a || is_term b then term_op op [ a; b ]
          else
            match value_fn env loc op [ a.ety; b.ety ] with
            | Some (f, ret) -> mk ret (ECall (f, [ a; b ]))
            | None -> (
                (* the built-in meaning, if it is the only one *)
                match List.assoc_opt op builtin_ops with
                | Some (arg, ret, o)
                  when (not (has_value_fn op ~arity:2))
                       || (ty_equal a.ety arg && ty_equal b.ety arg) ->
                    expect a.eloc ~expected:arg a.ety;
                    expect b.eloc ~expected:arg b.ety;
                    mk ret (EBinop (o, a, b))
                | _ -> value_error env loc op [ a.ety; b.ety ]))
      | op, [ a ] when is_operator ~arity:1 op -> (
          let a = expr env a in
          if is_term a then term_op op [ a ]
          else
            match value_fn env loc op [ a.ety ] with
            | Some (f, ret) -> mk ret (ECall (f, [ a ]))
            | None -> (
                match builtin_op ~arity:1 op with
                | Some (arg, ret)
                  when (not (has_value_fn op ~arity:1)) || ty_equal a.ety arg ->
                    expect a.eloc ~expected:arg a.ety;
                    mk ret (EUnop ((if op = "not" then Not else Neg), a))
                | _ -> value_error env loc op [ a.ety ]))
      | f, args -> (
          let check_args (s : sig_) =
            if List.length s.args <> List.length args then
              error loc "%s expects %d arguments, got %d" f (List.length s.args)
                (List.length args);
            List.map2 (fun t a -> expr env ~expected:t a) s.args args
          in
          match List.assoc_opt f env.locals with
          | Some s -> mk s.ret (ELocalCall (f, check_args s))
          | None ->
              let s = find_global env fn_loc f in
              mk s.ret (ECall (f, check_args s))))
  | Pexp_ifthenelse (c, a, Some b) ->
      let c = expr env ~expected:TBool c in
      let a = expr env ?expected a in
      let b = expr env ~expected:a.ety b in
      mk a.ety (EIf (c, a, b))
  | Pexp_let (Nonrecursive, [ vb ], body) -> (
      match vb.pvb_expr.pexp_desc with
      | Pexp_function (params, ret, Pfunction_body fbody) ->
          let name =
            match vb.pvb_pat.ppat_desc with
            | Ppat_var { txt; _ } -> txt
            | _ -> error vb.pvb_loc "expected a function name"
          in
          no_shadow env vb.pvb_pat.ppat_loc name;
          List.iter
            (fun p ->
              no_shadow env (param_loc p) (fst (param_of p));
              Option.iter
                (fun (_, (s : expression)) ->
                  error s.pexp_loc
                    "only the parameters of functions (fn) have sorts, not \
                     those of local functions")
                (param_sort p))
            params;
          let params = List.map param_of params in
          let ret = Option.map ret_of ret in
          let fenv = { env with vars = params @ env.vars } in
          let fbody = expr fenv ?expected:ret fbody in
          let s = { args = List.map snd params; ret = fbody.ety } in
          let body =
            expr { env with locals = (name, s) :: env.locals } ?expected body
          in
          mk body.ety (ELetFun (name, params, fbody, body))
      | _ ->
          let annot =
            match vb.pvb_constraint with
            | Some (Pvc_constraint { typ; locally_abstract_univars = [] }) ->
                Some (ty_of_core typ)
            | None -> None
            | _ -> error vb.pvb_loc "unsupported binding constraint"
          in
          let rhs = expr env ?expected:annot vb.pvb_expr in
          let p, benv =
            bind_pat env ~sort:(sort_of env vb.pvb_expr) rhs.ety vb.pvb_pat
          in
          let body = expr benv ?expected body in
          mk body.ety (ELet (p, rhs, body)))
  | Pexp_match (scrut, cases) ->
      let scruts =
        match scrut.pexp_desc with
        | Pexp_tuple l -> List.map (expr env) l
        | _ -> [ expr env scrut ]
      in
      let cases =
        List.concat_map
          (case env ?expected ~sort:(sort_of env scrut) scruts)
          cases
      in
      let ety =
        match cases with
        | [] -> error loc "empty match"
        | c :: rest ->
            List.iter
              (fun c' -> expect c'.cloc ~expected:c.body.ety c'.body.ety)
              rest;
            c.body.ety
      in
      mk ety (EMatch (scruts, cases))
  | Pexp_tuple l ->
      let tys = match expected with Some (TTuple t) -> Some t | _ -> None in
      let l =
        match tys with
        | Some tys when List.length tys = List.length l ->
            List.map2 (fun t e -> expr env ~expected:t e) tys l
        | _ -> List.map (expr env) l
      in
      mk (TTuple (List.map (fun e -> e.ety) l)) (ETuple l)
  | Pexp_record (fields, None) ->
      let names =
        List.map
          (fun (({ txt; _ } : longident loc), _) -> Longident.name txt)
          fields
      in
      let d =
        match
          List.find_opt
            (fun d ->
              d.d_fields <> []
              && List.sort compare (List.map fst d.d_fields)
                 = List.sort compare names)
            !lang.decls
        with
        | Some d -> d
        | None -> error loc "no record type has exactly these fields"
      in
      let fields =
        List.map2
          (fun f (_, e) -> (f, expr env ~expected:(List.assoc f d.d_fields) e))
          names fields
      in
      mk (TData d.d_name) (ERecord fields)
  | Pexp_field (e, { txt = Lident f; loc = floc }) -> (
      match
        List.find_opt (fun d -> List.mem_assoc f d.d_fields) !lang.decls
      with
      | None -> error floc "unknown field %s" f
      | Some d ->
          let e = expr env ~expected:(TData d.d_name) e in
          mk (List.assoc f d.d_fields) (EField (e, f)))
  | Pexp_sequence ({ pexp_desc = Pexp_assert c; _ }, body) ->
      let c = expr env ~expected:TBool c in
      let body = expr env ?expected body in
      mk body.ety (EAssert (c, body))
  | Pexp_constraint (e, ct) ->
      let t = ty_of_core ct in
      Option.iter (fun expected -> expect loc ~expected t) expected;
      expr env ~expected:t e
  | Pexp_extension
      ( { txt = "kanon.sort"; _ },
        PStr
          [
            { pstr_desc = Pstr_eval (k, _); _ };
            { pstr_desc = Pstr_eval (s, _); _ };
          ] ) -> (
      (* [(C args : S args)]: the node [C], built at the sort [S args] *)
      let is_node c =
        match find_constr c with
        | Some c -> c.c_res = TKind || Option.is_some (node_of_op c)
        | None -> false
      in
      match (k.pexp_desc, s.pexp_desc) with
      | ( Pexp_construct ({ txt = Lident c; _ }, _),
          Pexp_construct ({ txt = Lident h; _ }, sarg) )
        when is_node c ->
          let sarity =
            match sarg with
            | None -> 0
            | Some { pexp_desc = Pexp_tuple l; _ } -> List.length l
            | Some _ -> 1
          in
          (match List.assoc_opt c !node_typings with
          | Some t -> (
              match (List.nth t.t_sorts (List.length t.t_sorts - 1)).e with
              | EConstr (h', _) when h'.c_name <> h ->
                  error s.pexp_loc
                    "%s is a term of sort %s, by its typing, not %s" c h'.c_name
                    h
              | EConstr (_, args) when List.length args <> sarity ->
                  error s.pexp_loc "the sort %s has %d arguments" h
                    (List.length args)
              | _ -> ())
          | None -> ());
          let kind = expr env ~expected:TKind k in
          let sort = expr env ~expected:TSty s in
          mk TTerm (ENode (kind, sort))
      | Pexp_construct ({ txt = Lident c; _ }, _), _ when is_node c ->
          error s.pexp_loc "expected a sort, C args"
      | _ ->
          error loc
            "only the operands of a spec, the parameters of functions and \
             nodes, (C args : S args), are annotated with a sort")
  | Pexp_extension
      ( { txt = "kanon.at"; _ },
        PStr
          [
            { pstr_desc = Pstr_eval (k, _); _ };
            { pstr_desc = Pstr_eval (spec, _); _ };
          ] ) -> (
      (* the literal [k], at the sort that its typing gives it, or else at the
         sort of the node [spec] (see [law_cases]) *)
      let determined =
        match k.pexp_desc with
        | Pexp_construct ({ txt = Lident c; _ }, _) -> (
            match List.assoc_opt c !node_typings with
            | Some { t_sorts = [ result ]; t_vars; _ } ->
                List.for_all
                  (fun x -> not (List.mem_assoc x t_vars))
                  (expr_vars result)
            | _ -> false)
        | _ -> false
      in
      if determined then expr env ?expected k
      else
        let k = expr env ~expected:TKind k in
        match (expr env ~expected:TTerm spec).e with
        | ENode (_, sort) -> mk TTerm (ENode (k, sort))
        | _ ->
            error loc "the spec of this rule is not a node over its parameters")
  | _ -> error loc "unsupported expression"

and case env ?expected ~sort scruts (c : Ppxlib.case) : Syntax.case list =
  let loc = c.pc_lhs.ppat_loc in
  (* the rule name is written after the pattern; when the pattern is a tuple
     without parentheses, it is attached to its last component *)
  let rule, lhs =
    match rule_name_of_attrs c.pc_lhs.ppat_attributes with
    | Some r -> (Some r, strip_attr "r" c.pc_lhs)
    | None -> (
        match c.pc_lhs.ppat_desc with
        | Ppat_tuple l -> (
            let rev = List.rev l in
            let last = List.hd rev in
            match rule_name_of_attrs last.ppat_attributes with
            | Some r ->
                let last = strip_attr "r" last in
                ( Some r,
                  {
                    c.pc_lhs with
                    ppat_desc = Ppat_tuple (List.rev (last :: List.tl rev));
                  } )
            | None -> (None, c.pc_lhs))
        | _ -> (None, c.pc_lhs))
  in
  (* numbered per case, so that the generated names are stable *)
  pid_counter := 0;
  count_vars lhs;
  let sty =
    match scruts with
    | [ s ] -> s.ety
    | _ -> TTuple (List.map (fun s -> s.ety) scruts)
  in
  let pat, env = bind_pat env ~sort sty lhs in
  let guard = Option.map (expr env ~expected:TBool) c.pc_guard in
  let body = expr env ?expected c.pc_rhs in
  List.map
    (fun (p, alt) ->
      let pat, conds = linearize p in
      {
        pat;
        guard = conj (conds @ Option.to_list guard);
        body;
        rule;
        cloc = loc;
        alt;
      })
    (alternatives pat)

and param_of (p : function_param) =
  match p.pparam_desc with
  | Pparam_val
      ( Nolabel,
        None,
        {
          ppat_desc =
            Ppat_constraint ({ ppat_desc = Ppat_var { txt; _ }; _ }, ct);
          _;
        } ) ->
      (txt, ty_of_core ct)
  | _ -> error p.pparam_loc "parameters must be of the form (x : ty)"

(** The sort of the parameter [(x : S args)] of a function, a term: [x] and
    [S args]. *)
and param_sort (p : function_param) =
  match p.pparam_desc with
  | Pparam_val
      ( _,
        _,
        {
          ppat_desc =
            Ppat_constraint
              ({ ppat_desc = Ppat_var { txt; _ }; _ }, { ptyp_attributes; _ });
          _;
        } ) ->
      List.find_map
        (fun (a : attribute) ->
          match a.attr_payload with
          | PStr [ { pstr_desc = Pstr_eval (s, _); _ } ]
            when a.attr_name.txt = "kanon.sort" ->
              Some (txt, s)
          | _ -> None)
        ptyp_attributes
  | _ -> None

(** The location of the name of a parameter. *)
and param_loc (p : function_param) =
  match p.pparam_desc with
  | Pparam_val
      ( _,
        _,
        { ppat_desc = Ppat_constraint ({ ppat_desc = Ppat_var v; _ }, _); _ } )
    ->
      v.loc
  | _ -> p.pparam_loc

and ret_of = function
  | Pconstraint ct -> ty_of_core ct
  | Pcoerce _ -> failwith "unsupported coercion"

(* ---------------------------------------------------------------- *)
(* Matching the spec of a rule *)

(** Whether [x] occurs in [e], other than as the argument of a function that
    only reads its type (see [ty_only]), or in the spec that gives the sort of a
    literal (whose operands, of a commutative node, have the same sort). *)
let mention x (e : expression) =
  let found = ref None in
  object
    inherit Ast_traverse.iter as super

    method! expression e =
      match e.pexp_desc with
      | Pexp_extension
          ( { txt = "kanon.at"; _ },
            PStr [ { pstr_desc = Pstr_eval (k, _); _ }; _ ] ) ->
          super#expression k
      | Pexp_apply
          ( { pexp_desc = Pexp_ident { txt = Lident f; _ }; _ },
            [ (_, { pexp_desc = Pexp_ident _; _ }) ] )
        when List.mem f !lang.ty_only ->
          ()
      | Pexp_ident { txt = Lident y; loc } when y = x ->
          if !found = None then found := Some loc
      | _ -> super#expression e
  end
    #expression
    e;
  !found

let mentions x e = Option.is_some (mention x e)

(** Whether two patterns are equal up to a renaming of their variables. *)
let alpha_equal (p : pattern) (q : pattern) =
  let ren = Hashtbl.create 8 in
  let var x y =
    match Hashtbl.find_opt ren x with
    | Some y' -> y = y'
    | None ->
        Hashtbl.add ren x y;
        true
  in
  let rec go (p : pattern) (q : pattern) =
    match (p.ppat_desc, q.ppat_desc) with
    | Ppat_any, Ppat_any -> true
    | Ppat_var x, Ppat_var y -> var x.txt y.txt
    | Ppat_alias (p, x), Ppat_alias (q, y) -> go p q && var x.txt y.txt
    | Ppat_or (p1, p2), Ppat_or (q1, q2) -> go p1 q1 && go p2 q2
    | Ppat_tuple l1, Ppat_tuple l2 ->
        List.length l1 = List.length l2 && List.for_all2 go l1 l2
    | Ppat_construct (c, a), Ppat_construct (d, b) -> (
        Longident.name c.txt = Longident.name d.txt
        &&
        match (a, b) with
        | None, None -> true
        | Some (_, a), Some (_, b) -> go a b
        | _ -> false)
    | Ppat_constant a, Ppat_constant b -> a = b
    | _ -> false
  in
  go p q
  && List.length
       (List.sort_uniq compare (Hashtbl.fold (fun _ y l -> y :: l) ren []))
     = Hashtbl.length ren

(** The node of the spec of a rule, and the variables that are its last two
    operands. *)
let spec_node (spec : expression) =
  match spec.pexp_desc with
  | Pexp_construct ({ txt = Lident n; _ }, arg) ->
      let args =
        match arg with
        | Some { pexp_desc = Pexp_tuple l; _ } -> l
        | Some a -> [ a ]
        | None -> []
      in
      let var (e : expression) =
        match e.pexp_desc with
        | Pexp_ident { txt = Lident x; _ } -> Some x
        | _ -> None
      in
      let operands =
        match List.rev args with
        | b :: a :: _ -> (
            match (var a, var b) with
            | Some a, Some b -> Some (a, b)
            | _ -> None)
        | _ -> None
      in
      Some (n, operands)
  | _ -> None

let binop loc op (a : expression) b =
  let open Ast_builder.Default in
  pexp_apply ~loc (evar ~loc op) [ (Nolabel, a); (Nolabel, b) ]

(** The expression of the constant pattern [p]. *)
let rec expr_of_pat (p : pattern) =
  let open Ast_builder.Default in
  let loc = p.ppat_loc in
  match p.ppat_desc with
  | Ppat_constant c -> pexp_constant ~loc c
  | Ppat_construct (c, arg) ->
      pexp_construct ~loc c (Option.map (fun (_, a) -> expr_of_pat a) arg)
  | Ppat_tuple l -> pexp_tuple ~loc (List.map expr_of_pat l)
  | _ ->
      error loc "the parameters of a node in the case of a rule are constants"

(** In a rule whose spec is a commutative node [op (v1, v2)], the cases of
    [match v1, v2 with] match the operands in either order, unless their pattern
    is symmetric (the same up to renaming, once swapped). The cases must then
    name the operands rather than use [v1] and [v2] (other than as the argument
    of [type_of] and [[@ty_only]] functions).

    A case [p op q], where [op] is the node of the spec, stands for [p, q], when
    the parameters of the spec are those that [op] fixes, if any. *)
let rec spec_match (spec : expression) (e : expression) =
  let node, operands =
    match spec_node spec with Some (n, o) -> (n, o) | None -> ("", None)
  in
  (* the case [p, q], swapped if [op] is commutative *)
  let pair (c : Ppxlib.case) (p : pattern) (q : pattern) =
    let lhs = c.pc_lhs in
    count_vars lhs;
    let once (p : pattern) =
      match p.ppat_desc with
      | Ppat_any -> true
      | Ppat_var { txt; _ } -> Hashtbl.find case_vars txt = 1
      | _ -> false
    in
    let symmetric =
      alpha_equal
        { lhs with ppat_desc = Ppat_tuple [ p; q ] }
        { lhs with ppat_desc = Ppat_tuple [ q; p ] }
    in
    let swap =
      is_commutative node
      && (not (has_attr "comm" lhs.ppat_attributes))
      && (not (once p && once q))
      && not symmetric
    in
    if swap then
      Option.iter
        (fun (a, b) ->
          List.iter
            (fun x ->
              match
                List.find_map (mention x)
                  (Option.to_list c.pc_guard @ [ c.pc_rhs ])
              with
              | Some loc ->
                  error loc
                    "the operands match in either order: name them rather than \
                     %s"
                    x
              | None -> ())
            [ a; b ])
        operands;
    let comm =
      {
        attr_name = { txt = "comm"; loc = lhs.ppat_loc };
        attr_payload = PStr [];
        attr_loc = lhs.ppat_loc;
      }
    in
    {
      c with
      pc_lhs =
        {
          lhs with
          ppat_desc = Ppat_tuple [ p; q ];
          ppat_attributes = (lhs.ppat_attributes @ if swap then [ comm ] else []);
        };
    }
  in
  let is_var x (e : expression) =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident y; _ } -> x = y
    | _ -> false
  in
  match e.pexp_desc with
  | Pexp_sequence (a, b) ->
      { e with pexp_desc = Pexp_sequence (a, spec_match spec b) }
  | Pexp_match (({ pexp_desc = Pexp_tuple [ a; b ]; _ } as scrut), cases)
    when match operands with
         | Some (x, y) -> is_var x a && is_var y b
         | None -> false ->
      let case (c : Ppxlib.case) =
        let lhs = c.pc_lhs in
        match lhs.ppat_desc with
        | Ppat_tuple [ p; q ] -> pair c p q
        (* [p op q], the node of the spec over the patterns of its operands *)
        | Ppat_construct
            ({ txt = Lident n; _ }, Some (_, { ppat_desc = Ppat_tuple l; _ }))
          when n = node -> (
            match List.rev l with
            | q :: p :: params -> (
                let c = pair c p q in
                (* the parameters of the node that the case fixes, which the
                   parameters of the spec must equal *)
                let spec_params =
                  match spec.pexp_desc with
                  | Pexp_construct (_, Some { pexp_desc = Pexp_tuple a; _ }) ->
                      List.filteri (fun i _ -> i < List.length a - 2) a
                  | _ -> []
                in
                if List.length spec_params <> List.length params then
                  error lhs.ppat_loc "the check of the spec is not matched";
                let fixed =
                  List.filter_map
                    (fun ((a : expression), (p : pattern)) ->
                      match p.ppat_desc with
                      | Ppat_any -> None
                      | _ -> Some (binop p.ppat_loc "=" a (expr_of_pat p)))
                    (List.combine spec_params (List.rev params))
                in
                match fixed @ Option.to_list c.pc_guard with
                | [] -> c
                | g :: gs ->
                    let guard =
                      List.fold_left (fun a b -> binop b.pexp_loc "&&" a b) g gs
                    in
                    { c with pc_guard = Some guard })
            | _ -> error lhs.ppat_loc "the check of the spec is not matched")
        | _ -> c
      in
      { e with pexp_desc = Pexp_match (scrut, List.map case cases) }
  | _ -> e

(** A rule whose cases may not all apply ends with the rule [default], which
    builds its spec: [| default: _ -> spec]. *)
let rec with_default (spec : expression) (e : expression) =
  match e.pexp_desc with
  | Pexp_sequence (a, b) ->
      { e with pexp_desc = Pexp_sequence (a, with_default spec b) }
  | Pexp_match (s, cases) -> (
      match List.rev cases with
      | { pc_lhs; pc_guard = None; _ } :: _ when is_blank pc_lhs -> e
      | _ ->
          let open Ast_builder.Default in
          let loc = { spec.pexp_loc with loc_ghost = true } in
          let r =
            attribute ~loc ~name:{ txt = "r"; loc }
              ~payload:(PStr [ pstr_eval ~loc (evar ~loc "default") [] ])
          in
          let default =
            case
              ~lhs:{ (ppat_any ~loc) with ppat_attributes = [ r ] }
              ~guard:None ~rhs:spec
          in
          { e with pexp_desc = Pexp_match (s, cases @ [ default ]) })
  | _ -> e

(* ---------------------------------------------------------------- *)
(* The declaration of the language *)

(** The string of an attribute [[@a "s"]], and its location. *)
let string_attr_loc (a : attribute) =
  match a.attr_payload with
  | PStr
      [
        {
          pstr_desc =
            Pstr_eval
              ( {
                  pexp_desc = Pexp_constant (Pconst_string (s, _, _));
                  pexp_loc;
                  _;
                },
                _ );
          _;
        };
      ] ->
      (s, pexp_loc)
  | _ -> error a.attr_loc "expected [@%s \"...\"]" a.attr_name.txt

let string_attr a = fst (string_attr_loc a)

(** The strings of an attribute [[@a "s1" ... "sn"]], with their locations. *)
let attr_args (a : attribute) =
  let str (e : expression) =
    match e.pexp_desc with
    | Pexp_constant (Pconst_string (s, _, _)) -> (s, e.pexp_loc)
    | _ -> error a.attr_loc "expected [@%s \"...\" ...]" a.attr_name.txt
  in
  match a.attr_payload with
  | PStr [] -> []
  | PStr [ { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_tuple l; _ }, _); _ } ]
    ->
      List.map str l
  | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> [ str e ]
  | _ -> error a.attr_loc "expected [@%s \"...\" ...]" a.attr_name.txt

let strings_attr a = List.map fst (attr_args a)

let check_attrs allowed (attrs : attributes) =
  List.iter
    (fun (a : attribute) ->
      if not (List.mem a.attr_name.txt allowed) then
        error a.attr_name.loc "unknown attribute [@%s]" a.attr_name.txt)
    attrs

let find_attr name (attrs : attributes) =
  List.find_opt (fun (a : attribute) -> a.attr_name.txt = name) attrs

(** [[@no_lean]] is for [fn] and [prim] items only: [what] says what the item
    is, and why it is modelled. *)
let reject_no_lean what (attrs : attributes) =
  Option.iter
    (fun (a : attribute) ->
      error a.attr_name.loc
        "%s and cannot be [@no_lean]: only fn and prim items can be" what)
    (find_attr "no_lean" attrs)

(** The doc comment among [attrs], which the parser adds as [[@ocaml.doc "..."]]
    to a documented item, and the other attributes. *)
let take_doc (attrs : attributes) =
  let docs, others =
    List.partition (fun (a : attribute) -> a.attr_name.txt = "ocaml.doc") attrs
  in
  (Option.map string_attr (List.nth_opt docs 0), others)

(** The list sort [s list] of an operand of a typing, written [a list],
    [TBool list] or [(TBitVector n) list]: [s]. *)
let list_sort (e : expression) =
  match e.pexp_desc with
  | Pexp_apply
      ( s,
        [ (Nolabel, { pexp_desc = Pexp_ident { txt = Lident "list"; _ }; _ }) ]
      ) ->
      Some s
  | Pexp_construct
      (c, Some { pexp_desc = Pexp_ident { txt = Lident "list"; _ }; _ }) ->
      Some { e with pexp_desc = Pexp_construct (c, None) }
  | _ -> None

(** The sorts of the typing of the node [cd], if it has one, with [s] for an
    operand of sort [s list], and whether the node is n-ary: its only operand
    sort is a list. *)
let typing_sorts (cd : constructor_declaration) =
  match find_attr "sorts" cd.pcd_attributes with
  | None -> None
  | Some a -> (
      let sorts =
        match a.attr_payload with
        | PStr
            [
              { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_tuple l; _ }, _); _ };
            ] ->
            l
        | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> [ e ]
        | _ -> error a.attr_loc "unexpected [@sorts]"
      in
      match sorts with
      | [ s; r ] when Option.is_some (list_sort s) ->
          Some ([ Option.get (list_sort s); r ], true)
      | _ ->
          List.iteri
            (fun i (s : expression) ->
              if Option.is_some (list_sort s) then
                error s.pexp_loc
                  (if i = List.length sorts - 1 then
                     "%s: the result of a node is a term, not a list"
                   else "%s: s list is only allowed as the only operand sort")
                  cd.pcd_name.txt)
            sorts;
          Some (sorts, false))

(** The number of operands of the node [cd]: [Some k] for an operator of [k]
    operands, [Some 0] for a leaf (whose typing gives only the sort of its
    result, if it has one), and [None] for an n-ary operator. *)
let node_arity (cd : constructor_declaration) =
  match typing_sorts cd with
  | None -> Some 0
  | Some (_, true) -> None
  | Some (sorts, false) -> Some (List.length sorts - 1)

(** The type of the operators of [arity] operands ([op2]), and the constructor
    of the terms they make ([Op2]). *)
let op_type = function
  | Some k -> (Printf.sprintf "op%d" k, Printf.sprintf "Op%d" k)
  | None -> ("opn", "OpN")

(** The attributes that declare the laws of an operator. *)
let law_attrs = [ "fold"; "unit"; "zero"; "idem"; "invol" ]

let law_of_attr (a : attribute) =
  match a.attr_name.txt with
  | "fold" -> (
      match strings_attr a with
      | [ f ] -> Some (Fold (f, None))
      | [ f; lift ] -> Some (Fold (f, Some lift))
      | _ -> error a.attr_loc "expected [@fold f] or [@fold f lift]")
  | "unit" -> Some (Unit (string_attr a))
  | "zero" -> Some (Zero (string_attr a))
  | "idem" -> Some Idem
  | "invol" -> Some Invol
  | _ -> None

let law_name = function
  | Fold _ -> "fold"
  | Unit _ -> "unit"
  | Zero _ -> "zero"
  | Idem -> "idem"
  | Invol -> "invol"

(** Whether [c], in a [[@unit c]] or [[@zero c]] law, is a literal, rather than
    a named constant. *)
let is_literal c = List.mem c [ "0"; "1"; "true"; "false" ]

(** The sort of the operand [i] of the node [n], in its typing: its head
    constructor, if it has one. *)
let operand_head n i =
  match List.assoc_opt n !lang.raw_typing with
  | Some rt -> (
      match List.nth_opt rt.rt_sorts i with
      | Some { pexp_desc = Pexp_construct ({ txt = Lident h; _ }, _); _ } ->
          Head h
      | _ -> Unknown)
  | None -> Unknown

(** The notation of the literal [c] of a [[@unit c]] or [[@zero c]] law on the
    binary operator [n]: at the sort of its right operand. *)
let law_notation loc n c =
  resolve_notation loc ~what:c
    ~lit:(if c = "true" || c = "false" then `Bool else `Int)
    ~sort:(operand_head n 1)

(** Checks the literal or constant [c] of a [[@unit c]] or [[@zero c]] law on
    [n]: a literal has a notation, and a named constant is declared. *)
let law_literal loc n c =
  if is_literal c then ignore (law_notation loc n c)
  else if not (List.mem_assoc c !lang.constants) then
    error loc
      "expected the literal 0, 1, true or false, or a constant: %s is not \
       declared"
      c

let check_law (name, law, loc, arg_loc) =
  let operands =
    match Option.bind (find_constr name) node_of_op with
    | Some (_, operands) -> List.length operands
    | None -> error loc "[@%s]: %s is not an operator" (law_name law) name
  in
  let expect n =
    if operands <> n then
      error loc "[@%s]: %s is not a %s operator" (law_name law) name
        (if n = 1 then "unary" else "binary")
  in
  match law with
  | Fold _ -> ()
  | Unit c | Zero c ->
      expect 2;
      law_literal arg_loc name c
  | Idem -> expect 2
  | Invol -> expect 1

(** The location from the start of the first of [l] to the end of the last, or
    [default] if [l] is empty. *)
let span_of (l : Location.t list) default =
  match l with
  | [] -> default
  | first :: _ ->
      let last = List.nth l (List.length l - 1) in
      { first with loc_end = last.loc_end }

(** Reads the declaration of the constructor [cd] of a type whose constructors
    have the type [res], into the language. [comm_locs] collects the locations
    of the [[@comm]] attributes. *)
let constructor ~comm_locs res (cd : constructor_declaration) =
  let name = cd.pcd_name.txt and loc = cd.pcd_loc in
  let c_doc, attrs = take_doc cd.pcd_attributes in
  (* the attributes of the literals before [notation] *)
  List.iter
    (fun (a : attribute) ->
      if List.mem a.attr_name.txt [ "literal"; "to_term"; "of_term"; "raw" ]
      then
        error a.attr_name.loc
          "[@%s] is gone: [notation %s] makes the literals of patterns stand \
           for a leaf node of one int or bool"
          a.attr_name.txt name)
    attrs;
  reject_no_lean "a sort or a node is part of the Lean model" attrs;
  check_attrs ([ "comm"; "params"; "sorts"; "when"; "get" ] @ law_attrs) attrs;
  let payload n =
    Option.map
      (fun (a : attribute) ->
        match a.attr_payload with
        | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> e
        | _ -> error a.attr_loc "unexpected [@%s]" n)
      (find_attr n attrs)
  in
  let items (e : expression option) =
    match e with
    | Some { pexp_desc = Pexp_tuple l; _ } -> l
    | Some e -> [ e ]
    | None -> []
  in
  let attr_loc n =
    Option.fold ~none:loc
      ~some:(fun (a : attribute) -> a.attr_loc)
      (find_attr n attrs)
  in
  (match typing_sorts cd with
  | Some (rt_sorts, rt_nary) ->
      lang :=
        {
          !lang with
          raw_typing =
            !lang.raw_typing
            @ [
                ( name,
                  {
                    rt_params = items (payload "params");
                    rt_sorts;
                    rt_nary;
                    rt_when = payload "when";
                    rt_loc = attr_loc "sorts";
                  } );
              ];
        }
  | None -> (
      match (find_attr "params" attrs, find_attr "when" attrs) with
      | Some a, _ | None, Some a ->
          error a.attr_loc "%s: argument names and conditions need sorts" name
      | None, None -> ()));
  if Option.is_some (find_constr name) then
    error cd.pcd_name.loc "constructor %s is declared twice" name;
  let args =
    match cd.pcd_args with
    | Pcstr_tuple l ->
        List.map
          (fun (ct : core_type) ->
            match ct.ptyp_desc with
            | Ptyp_constr ({ txt = Lident "nat"; _ }, []) -> Small
            | _ -> Arg (ty_of_core ct))
          l
    | Pcstr_record _ -> error loc "unsupported constructor"
  in
  let c = { c_name = name; c_res = res; c_args = args; c_doc } in
  let l = !lang in
  let l = { l with constrs = l.constrs @ [ c ] } in
  let l =
    match find_attr "comm" attrs with
    | Some a ->
        comm_locs := (name, a.attr_loc) :: !comm_locs;
        { l with commutative = l.commutative @ [ name ] }
    | None -> l
  in
  let l =
    {
      l with
      laws =
        l.laws
        @ List.filter_map
            (fun (a : attribute) ->
              Option.map
                (fun law ->
                  let arg_loc =
                    match attr_args a with [ (_, l) ] -> l | _ -> a.attr_loc
                  in
                  (name, law, a.attr_loc, arg_loc))
                (law_of_attr a))
            attrs;
    }
  in
  let l =
    match find_attr "get" attrs with
    | Some a -> (
        match (res, args, strings_attr a) with
        | TSty, [ _ ], [ f ] ->
            { l with sort_getters = l.sort_getters @ [ (name, f) ] }
        | _ -> error a.attr_loc "[@get f] applies to sorts with one argument")
    | None -> l
  in
  lang := l

(** Reads the declaration [e] of an operator on terms, whose attribute [a] is
    [[@infix "op"]] or [[@prefix "op"]], into the language. *)
let operator ((e : expression), (a : attribute), op_doc) =
  let loc = e.pexp_loc in
  let sym, sym_loc = string_attr_loc a in
  let sym, arity =
    match (a.attr_name.txt, op_kind sym) with
    | "infix", _ when sym = "<>" ->
        error sym_loc "<> is built in, at every type"
    | "infix", (`Infix | `Word | `Minus) -> (sym, 2)
    | "infix", _ -> error sym_loc "%s is not an infix operator, nor a word" sym
    | _, `Minus -> ("~-", 1)
    | _, `Prefix -> (sym, 1)
    | _ ->
        error sym_loc
          "%s is not a prefix operator: -, not, or a symbol that starts with \
           !, ~ or ?"
          sym
  in
  if Option.is_some (find_operator ~arity sym) then
    error sym_loc "operator %s is declared twice" (op_name ~arity sym);
  let ident (e : expression) =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident f; _ } -> f
    | _ -> error e.pexp_loc "expected a function name"
  in
  let node, smart, on_value =
    match e.pexp_desc with
    | Pexp_tuple [ n; s ] -> (n, s, None)
    | Pexp_tuple [ n; s; b ] -> (n, s, Some b)
    | _ ->
        error loc
          "expected: node, smart constructor[, primitive on literal values]"
  in
  (* the node, with its parameters or none *)
  let node, params =
    match node.pexp_desc with
    | Pexp_construct ({ txt = Lident n; _ }, arg) -> (
        match find_constr n with
        | Some c -> (
            (match node_of_op c with
            | Some (_, operands) when List.length operands = arity -> ()
            | _ -> error node.pexp_loc "%s is not a node of arity %d" n arity);
            let params =
              match arg with
              | None -> []
              | Some { pexp_desc = Pexp_tuple l; _ } -> l
              | Some e -> [ e ]
            in
            match params with
            | _ :: _ when List.length params <> List.length c.c_args ->
                error node.pexp_loc "%s has %d parameters" n
                  (List.length c.c_args)
            | _ -> (n, params))
        | None -> error node.pexp_loc "%s is not a node of arity %d" n arity)
    | _ -> error node.pexp_loc "expected a node constructor"
  in
  let on_value = Option.map ident on_value in
  let smart, pre =
    match smart.pexp_desc with
    | Pexp_apply (f, args) -> (ident f, List.map snd args)
    | _ -> (ident smart, [])
  in
  lang :=
    {
      !lang with
      operators =
        !lang.operators
        @ [
            {
              sym;
              arity;
              node;
              params;
              smart;
              pre;
              on_value;
              op_loc = sym_loc;
              op_doc;
            };
          ];
    }

(** Whether [name] is a type that Kanon generates, which a language cannot
    declare: [t] (the terms, whose kinds are named [kind]), [ty] and the types
    of operators, [op1], [op2], ..., [opn]. *)
let generated_type name =
  List.mem name [ "t"; "kind"; "ty"; "opn" ]
  || (String.length name > 2
     && String.sub name 0 2 = "op"
     && String.for_all
          (function '0' .. '9' -> true | _ -> false)
          (String.sub name 2 (String.length name - 2)))

(** A type of the language, without constructors yet. *)
let new_decl ?(loc = Location.none) ?doc ?ocaml ?lean ?(eq = true) ?equal ?hash
    name =
  {
    d_name = name;
    d_ocaml = ocaml;
    d_lean = lean;
    d_eq = eq;
    d_equal = equal;
    d_hash = hash;
    d_fields = [];
    d_loc = loc;
    d_doc = doc;
  }

(** Reads the declaration of a language, which the rules are then checked
    against. The terms are generated from its nodes, and their types from its
    sorts. *)
let language (str : structure) =
  let tds, ops =
    List.partition_map Fun.id
      (List.filter_map
         (fun (si : structure_item) ->
           attempt (fun () ->
               match si.pstr_desc with
               | Pstr_type (_, [ td ]) -> Either.Left td
               | Pstr_eval (e, attrs) -> (
                   match take_doc attrs with
                   | doc, [ a ]
                     when List.mem a.attr_name.txt
                            [ "infix"; "prefix"; "constant"; "notation" ] ->
                       Right (e, a, doc)
                   | _ ->
                       error si.pstr_loc
                         "unsupported item in a language declaration")
               | Pstr_attribute a -> (
                   match (a.attr_name.txt, strings_attr a) with
                   | "lean_root", [ r ] ->
                       lang := { !lang with lean_root = r };
                       Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a, None)
                   | "lean_param", [ x; t ] ->
                       lang :=
                         {
                           !lang with
                           lean_params = !lang.lean_params @ [ (x, t) ];
                         };
                       Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a, None)
                   | "ocaml_types", [ m ] ->
                       lang := { !lang with ocaml_types = Some m };
                       Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a, None)
                   | "ocaml_prims", [ m ] ->
                       lang := { !lang with ocaml_prims = Some m };
                       Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a, None)
                   | _ ->
                       error a.attr_name.loc "unknown attribute [@@@@@@%s]"
                         a.attr_name.txt)
               | _ ->
                   error si.pstr_loc
                     "unsupported item in a language declaration"))
         str)
  in
  let ops, constants =
    List.partition
      (fun (_, (a : attribute), _) ->
        List.mem a.attr_name.txt [ "infix"; "prefix" ])
      ops
  in
  (* the nodes and sorts of the modules, in order *)
  let nodes, tds =
    List.partition
      (fun (td : type_declaration) -> has_attr "node" td.ptype_attributes)
      tds
  in
  let nodes =
    List.fold_left
      (fun nodes (td : type_declaration) ->
        Option.value ~default:nodes
          (attempt (fun () ->
               match td.ptype_kind with
               | Ptype_variant [ cd ] ->
                   let sort = has_attr "sort" td.ptype_attributes in
                   if
                     List.exists
                       (fun (_, cd') -> cd'.pcd_name.txt = cd.pcd_name.txt)
                       nodes
                   then
                     error cd.pcd_name.loc "%s %s is declared twice"
                       (if sort then "sort" else "node")
                       cd.pcd_name.txt;
                   if sort then
                     Option.iter
                       (fun (a : attribute) ->
                         error a.attr_loc "sort %s: sorts have no typing"
                           cd.pcd_name.txt)
                       (find_attr "sorts" cd.pcd_attributes);
                   nodes @ [ (sort, cd) ]
               | _ -> error td.ptype_loc "expected a node")))
      [] nodes
  in
  let sorts, nodes = List.partition fst nodes in
  let sorts = List.map snd sorts in
  (* the nodes, with their numbers of operands *)
  let nodes =
    List.filter_map
      (fun (_, cd) -> attempt (fun () -> (node_arity cd, cd)))
      nodes
  in
  checkpoint ();
  (* the declared types first, so that they can refer to each other, then the
     generated ones *)
  let decls =
    List.filter_map
      (fun (td : type_declaration) ->
        attempt (fun () ->
            let name = td.ptype_name.txt and loc = td.ptype_name.loc in
            let doc, tattrs = take_doc td.ptype_attributes in
            reject_no_lean "a type is part of the Lean model" tattrs;
            check_attrs [ "ocaml"; "lean"; "noeq"; "equal"; "hash" ] tattrs;
            (match ty_of_name name with
            | Some (TInt | TBool | TUnit) ->
                error loc "%s is a built-in type" name
            | _ -> ());
            if generated_type name then
              error loc "type %s is generated from the %s" name
                (if name = "ty" then "sorts" else "nodes");
            if Option.is_some (find_decl name) then
              error loc "type %s is declared twice" name;
            (* only abstract types have their own equality and hash; the OCaml
               type of a record or variant, which is optional, is re-exported
               (see [Gen_ocaml.type_def]) *)
            if td.ptype_kind <> Ptype_abstract then
              List.iter
                (fun n ->
                  Option.iter
                    (fun (a : attribute) ->
                      error a.attr_name.loc "[@%s] applies to abstract types" n)
                    (find_attr n td.ptype_attributes))
                [ "noeq"; "equal"; "hash" ];
            let attr n =
              Option.map string_attr (find_attr n td.ptype_attributes)
            in
            let d =
              new_decl ~loc ?doc ?ocaml:(attr "ocaml") ?lean:(attr "lean")
                ~eq:(not (has_attr "noeq" td.ptype_attributes))
                ?equal:(attr "equal") ?hash:(attr "hash") name
            in
            lang := { !lang with decls = !lang.decls @ [ d ] };
            (d, td)))
      tds
  in
  checkpoint ();
  (* the arities of the operators: [1], [2], ..., then n-ary *)
  let arities =
    List.sort_uniq
      (fun a b ->
        match (a, b) with
        | Some a, Some b -> compare a b
        | None, None -> 0
        | None, _ -> 1
        | _, None -> -1)
      (List.filter_map
         (fun (k, _) -> if k = Some 0 then None else Some k)
         nodes)
  in
  lang :=
    {
      !lang with
      decls =
        !lang.decls
        @ [ new_decl "kind" ]
        @ List.map (fun k -> new_decl (fst (op_type k))) arities
        @ [ new_decl "ty" ];
    };
  let decls =
    List.map
      (fun (d, (td : type_declaration)) ->
        match td.ptype_kind with
        | Ptype_record fields ->
            ( {
                d with
                d_fields =
                  List.filter_map
                    (fun (l : label_declaration) ->
                      attempt (fun () ->
                          (l.pld_name.txt, ty_of_core l.pld_type)))
                    fields;
              },
              td )
        | _ -> (d, td))
      decls
  in
  lang :=
    {
      !lang with
      decls =
        List.map
          (fun (d : decl) ->
            Option.value ~default:d
              (List.find_map
                 (fun ((d' : decl), _) ->
                   if d'.d_name = d.d_name then Some d' else None)
                 decls))
          !lang.decls;
    };
  (* a field determines its record type *)
  ignore
    (List.fold_left
       (fun seen ((_ : decl), (td : type_declaration)) ->
         match td.ptype_kind with
         | Ptype_record ls ->
             List.fold_left
               (fun seen (l : label_declaration) ->
                 if List.mem l.pld_name.txt seen then
                   ignore
                     (attempt (fun () ->
                          error l.pld_name.loc "field %s is declared twice"
                            l.pld_name.txt));
                 l.pld_name.txt :: seen)
               seen ls
         | _ -> seen)
       [] decls);
  checkpoint ();
  (* the [[@comm]] attributes, for the check that their operators are binary *)
  let comm_locs = ref [] in
  let constructor res cd =
    ignore (attempt (fun () -> constructor ~comm_locs res cd))
  in
  List.iter
    (fun (d, (td : type_declaration)) ->
      match td.ptype_kind with
      | Ptype_variant cds -> List.iter (constructor (TData d.d_name)) cds
      | Ptype_abstract | Ptype_record _ -> ()
      | Ptype_open ->
          ignore (attempt (fun () -> error td.ptype_loc "unsupported type")))
    decls;
  (* the terms: the leaf nodes, then the operators of each arity, [Op2 of op2 *
     t * t], which their nodes stand for *)
  List.iter (fun (k, cd) -> if k = Some 0 then constructor TKind cd) nodes;
  List.iter
    (fun k ->
      let op, c = op_type k in
      let operands =
        match k with
        | Some k -> List.init k (fun _ -> Arg TTerm)
        | None -> [ Arg (TList TTerm) ]
      in
      (match List.find_opt (fun (_, cd) -> cd.pcd_name.txt = c) nodes with
      | Some (_, cd) ->
          ignore
            (attempt (fun () ->
                 error cd.pcd_name.loc
                   "%s is the constructor of the terms of the operators of %s" c
                   op))
      | None -> ());
      lang :=
        {
          !lang with
          constrs =
            !lang.constrs
            @ [
                {
                  c_name = c;
                  c_res = TKind;
                  c_args = Arg (TData op) :: operands;
                  c_doc = None;
                };
              ];
          node_kinds = !lang.node_kinds @ [ c ];
        })
    arities;
  List.iter
    (fun (k, cd) ->
      if k <> Some 0 then constructor (TData (fst (op_type k))) cd)
    nodes;
  List.iter (constructor TSty) sorts;
  checkpoint ();
  (* then the notations of literals, and the operators on terms *)
  let notations, constants =
    List.partition
      (fun (_, (a : attribute), _) -> a.attr_name.txt = "notation")
      constants
  in
  List.iter
    (fun ((e : expression), _, _) ->
      ignore
        (attempt (fun () ->
             match e.pexp_desc with
             | Pexp_construct ({ txt = Lident c; loc }, None) -> (
                 if List.mem c !lang.notations then
                   error loc "notation %s is declared twice" c;
                 match find_constr c with
                 | Some { c_res = TKind; c_args = [ Arg (TInt | TBool) ]; _ }
                   when not (List.mem c !lang.node_kinds) ->
                     lang := { !lang with notations = !lang.notations @ [ c ] }
                 | Some _ ->
                     error loc
                       "notation %s: %s is not a leaf node of one int or bool" c
                       c
                 | None -> error loc "notation %s: unknown node %s" c c)
             | _ -> error e.pexp_loc "expected notation C")))
    notations;
  List.iter (fun op -> ignore (attempt (fun () -> operator op))) ops;
  (* the constants of the laws, functions of a term or not *)
  List.iter
    (fun ((e : expression), (a : attribute), doc) ->
      ignore
        (attempt (fun () ->
             match a.attr_name.txt with
             | "constant" ->
                 let c, cloc = string_attr_loc a in
                 if List.mem_assoc c !lang.constants then
                   error cloc "constant %s is declared twice" c;
                 let constant =
                   match e.pexp_desc with
                   | Pexp_function
                       ( [
                           {
                             pparam_desc =
                               Pparam_val
                                 ( Nolabel,
                                   None,
                                   { ppat_desc = Ppat_var { txt = v; _ }; _ } );
                             _;
                           };
                         ],
                         None,
                         Pfunction_body body ) ->
                       (Some v, body)
                   | _ -> (None, e)
                 in
                 lang :=
                   {
                     !lang with
                     constants = !lang.constants @ [ (c, constant) ];
                     constant_docs =
                       !lang.constant_docs
                       @ Option.to_list (Option.map (fun d -> (c, d)) doc);
                   }
             | _ -> ())))
    constants;
  checkpoint ();
  let loc = match str with si :: _ -> si.pstr_loc | [] -> Location.none in
  List.iter
    (fun c ->
      match Option.bind (find_constr c) node_of_op with
      | Some (_, [ TTerm; TTerm ]) -> ()
      | _ ->
          let loc = Option.value (List.assoc_opt c !comm_locs) ~default:loc in
          ignore
            (attempt (fun () ->
                 error loc "[@comm]: %s is not a binary operator" c)))
    !lang.commutative;
  List.iter (fun l -> ignore (attempt (fun () -> check_law l))) !lang.laws

(** The pattern of the parameter [e] of the node of an operator. *)
let rec pat_of_param (e : expression) =
  let mk d =
    {
      ppat_desc = d;
      ppat_loc = e.pexp_loc;
      ppat_loc_stack = [];
      ppat_attributes = [];
    }
  in
  match e.pexp_desc with
  | Pexp_constant c -> mk (Ppat_constant c)
  | Pexp_construct (c, arg) ->
      mk (Ppat_construct (c, Option.map (fun a -> ([], pat_of_param a)) arg))
  | Pexp_tuple l -> mk (Ppat_tuple (List.map pat_of_param l))
  | _ -> error e.pexp_loc "the parameter of a node of an operator is a constant"

(** Replaces the operators in patterns ([a + b]) with the nodes that the
    language declares for them. The parameters of a node (e.g. the overflow
    check of [Add]) are those of the operator, if any, or else unconstrained. *)
let desugar_ops =
  object
    inherit Ast_traverse.map as super

    method! pattern p =
      let p = super#pattern p in
      let mk d =
        {
          ppat_desc = d;
          ppat_loc = p.ppat_loc;
          ppat_loc_stack = [];
          ppat_attributes = [];
        }
      in
      match p.ppat_desc with
      | Ppat_construct ({ txt = Lident sym; loc }, Some (vars, arg))
        when is_operator ~arity:1 sym || is_operator ~arity:2 sym -> (
          let arity, operands =
            match arg.ppat_desc with
            | Ppat_tuple l when not (is_operator ~arity:1 sym) -> (2, l)
            | _ -> (1, [ arg ])
          in
          match find_operator ~arity sym with
          | None ->
              error loc "%s is not an operator on terms" (op_name ~arity sym)
          | Some o ->
              let c = Option.get (find_constr o.node) in
              let params =
                match o.params with
                | [] -> List.map (fun _ -> mk Ppat_any) c.c_args
                | ps -> List.map pat_of_param ps
              in
              let args = params @ operands in
              let arg = match args with [ a ] -> a | l -> mk (Ppat_tuple l) in
              {
                p with
                ppat_desc =
                  Ppat_construct ({ txt = Lident o.node; loc }, Some (vars, arg));
              })
      | _ -> p
  end

(* ---------------------------------------------------------------- *)
(* Top-level *)

let spec_of_attrs (attrs : attributes) =
  List.find_map
    (fun (a : attribute) ->
      if a.attr_name.txt = "spec" then
        match a.attr_payload with
        | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> Some e
        | _ -> error a.attr_loc "expected [@spec expr]"
      else None)
    attrs

(** The parameters of a rule whose spec is a node over variables,
    [C (x1, ..., xn)]: the variables, at the types of the arguments of [C]. *)
let spec_params rname (spec : expression) =
  let fail (loc : Location.t) =
    error loc
      "%s: a rule declares its parameters unless its spec is a node over \
       variables"
      rname
  in
  let loc = spec.pexp_loc in
  match spec.pexp_desc with
  | Pexp_construct ({ txt = Lident n; loc = cloc }, arg) ->
      let c =
        match find_constr n with
        | Some c -> c
        | None -> error cloc "unknown constructor %s" n
      in
      let tys =
        List.map arg_ty c.c_args
        @ match node_of_op c with Some (_, ops) -> ops | None -> []
      in
      let args =
        match arg with
        | Some { pexp_desc = Pexp_tuple l; _ } -> l
        | Some a -> [ a ]
        | None -> []
      in
      if List.length args <> List.length tys then
        error loc "%s has %d arguments" n (List.length tys);
      List.map2
        (fun (a : expression) t ->
          match a.pexp_desc with
          | Pexp_ident { txt = Lident x; _ } -> (x, t)
          | _ -> fail a.pexp_loc)
        args tys
  | _ -> fail loc

type raw_fn = {
  rname : string;
  rparams : (string * Syntax.ty) list;
  rret : Syntax.ty;
  rspec : expression option;
  rcases : bool;
  rty_only : bool;  (** [[@ty_only]] *)
  rbody : expression;
  rsorts : (string * expression) list;
      (** the sorts of the operands of the spec and of the parameters of
          functions, [(v : s)] *)
  runtyped : bool;
      (** [[@untyped]]: the rule also simplifies ill-typed specs, so the sorts
          of their operands are not asserted *)
  rloc : Location.t;
  rname_loc : Location.t;  (** of the name of the function *)
  rparam_locs : Location.t list;  (** of the names of its parameters *)
  rattrs : attributes;
  rdoc : string option;
}

(** The location of the attribute [name] of [r], or else of its name. *)
let rattr_loc (r : raw_fn) name =
  match find_attr name r.rattrs with
  | Some a -> a.attr_loc
  | None -> r.rname_loc

(** The spec without the sorts of its operands, and those sorts. *)
let spec_sorts (spec : expression) =
  let sorts = ref [] in
  let strip =
    object
      inherit Ast_traverse.map as super

      method! expression e =
        match e.pexp_desc with
        | Pexp_extension
            ( { txt = "kanon.sort"; _ },
              PStr
                [
                  { pstr_desc = Pstr_eval (v, _); _ };
                  { pstr_desc = Pstr_eval (s, _); _ };
                ] ) -> (
            match v.pexp_desc with
            | Pexp_ident { txt = Lident x; _ } ->
                sorts := !sorts @ [ (x, s) ];
                v
            | _ -> error e.pexp_loc "only variables are annotated with a sort")
        | _ -> super#expression e
    end
  in
  let spec = strip#expression spec in
  (spec, !sorts)

let raw_fn (vb : value_binding) =
  let loc = vb.pvb_loc in
  let rname_loc = vb.pvb_pat.ppat_loc in
  let rname =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt; _ } -> txt
    | _ -> error rname_loc "expected a function name"
  in
  let rdoc, rattrs = take_doc vb.pvb_attributes in
  if Option.is_some (spec_of_attrs vb.pvb_attributes) then (
    reject_no_lean "a rule is proved in Lean" rattrs;
    check_attrs [ "spec"; "cases"; "untyped" ] rattrs)
  else check_attrs [ "ty_only"; "no_lean" ] rattrs;
  let rspec, rsorts =
    match spec_of_attrs vb.pvb_attributes with
    | Some spec ->
        let spec, sorts = spec_sorts spec in
        (Some spec, sorts)
    | None -> (None, [])
  in
  let rcases = has_attr "cases" vb.pvb_attributes in
  let rty_only = has_attr "ty_only" vb.pvb_attributes in
  let runtyped = has_attr "untyped" vb.pvb_attributes in
  if runtyped && rsorts <> [] then
    error (Option.get (find_attr "untyped" vb.pvb_attributes)).attr_loc
      "%s: an [@untyped] rule does not annotate the sorts of its spec" rname;
  (* the cases of a rule match the terms (and lists of terms) among its
     parameters *)
  let body rparams (e : expression) =
    match e.pexp_desc with
    | Pexp_match
        ( {
            pexp_desc = Pexp_extension ({ txt = "kanon.operands"; _ }, _);
            pexp_loc = loc;
            _;
          },
          cases ) ->
        let open Ast_builder.Default in
        let terms =
          List.filter_map
            (fun (x, t) ->
              match t with
              | TTerm | TList TTerm -> Some (evar ~loc x)
              | _ -> None)
            rparams
        in
        let scrut = match terms with [ t ] -> t | l -> pexp_tuple ~loc l in
        { e with pexp_desc = Pexp_match (scrut, cases) }
    | _ -> e
  in
  match vb.pvb_expr.pexp_desc with
  | Pexp_function (params, Some ret, Pfunction_body rbody) ->
      let rparams = List.map param_of params in
      (* the sorts of the parameters, after those of the operands of the spec *)
      let rsorts = rsorts @ List.filter_map param_sort params in
      let rparam_locs = List.map param_loc params in
      (match rspec with
      | Some spec when rcases -> (
          match spec_params rname spec with
          | ps when ps = rparams ->
              error
                (span_of rparam_locs rname_loc)
                "%s: its parameters are those of its spec, implicitly" rname
          | _ | (exception Error _) -> ())
      | _ -> ());
      let rbody = body rparams rbody in
      {
        rname;
        rparams;
        rret = ret_of ret;
        rspec;
        rcases;
        rty_only;
        rbody;
        rsorts;
        runtyped;
        rloc = loc;
        rname_loc;
        rparam_locs;
        rattrs;
        rdoc;
      }
  | Pexp_function _ ->
      error rname_loc "%s: the return type must be annotated" rname
  | _ -> (
      match vb.pvb_constraint with
      | Some (Pvc_constraint { typ; locally_abstract_univars = [] }) ->
          let rparams =
            match rspec with
            | Some spec when rcases -> spec_params rname spec
            | _ -> []
          in
          (* the operands of the spec *)
          let rparam_locs =
            match rspec with
            | Some { pexp_desc = Pexp_construct (_, Some args); _ }
              when rparams <> [] ->
                let args =
                  match args with
                  | { pexp_desc = Pexp_tuple l; _ } -> l
                  | a -> [ a ]
                in
                List.map (fun (a : expression) -> a.pexp_loc) args
            | _ -> []
          in
          {
            rname;
            rparams;
            rret = ty_of_core typ;
            rspec;
            rcases;
            rty_only;
            rbody = body rparams vb.pvb_expr;
            rsorts;
            runtyped;
            rloc = loc;
            rname_loc;
            rparam_locs;
            rattrs;
            rdoc;
          }
      | _ ->
          error rname_loc "%s: constants must be annotated with their type"
            rname)

(* ---------------------------------------------------------------- *)
(* The laws of operators *)

(** The node of the spec [C (x1, ..., xn)] of a rule function, when its
    arguments are the parameters of the function, in order. *)
let spec_head (r : raw_fn) =
  match r.rspec with
  | Some { pexp_desc = Pexp_construct ({ txt = Lident n; _ }, arg); _ } ->
      let args =
        match arg with
        | Some { pexp_desc = Pexp_tuple l; _ } -> l
        | Some a -> [ a ]
        | None -> []
      in
      let var (e : expression) =
        match e.pexp_desc with
        | Pexp_ident { txt = Lident x; _ } -> Some x
        | _ -> None
      in
      if List.map var args = List.map (fun (x, _) -> Some x) r.rparams then
        Some n
      else None
  | _ -> None

(** The rule function of the node [n]: the one whose spec is [n] over its
    parameters. *)
let rule_of_node loc raws n =
  match List.filter (fun r -> r.rcases && spec_head r = Some n) raws with
  | [ r ] -> r
  | [] -> error loc "no rule function has the spec %s over its parameters" n
  | _ -> error loc "several rule functions have the spec %s" n

let law_order = function
  | Fold _ -> 0
  | Unit _ -> 1
  | Zero _ -> 2
  | Idem -> 3
  | Invol -> 4

(** The name of the rule of a case, if any (see [case]). *)
let case_rule (c : Ppxlib.case) =
  match (rule_name_of_attrs c.pc_lhs.ppat_attributes, c.pc_lhs.ppat_desc) with
  | Some r, _ -> Some r
  | None, Ppat_tuple l ->
      rule_name_of_attrs (List.hd (List.rev l)).ppat_attributes
  | None, _ -> None

(** The location of the name of the rule of a case (its pattern, if it has
    none). *)
let case_rule_loc (c : Ppxlib.case) =
  let attrs =
    match c.pc_lhs.ppat_desc with
    | Ppat_tuple l ->
        c.pc_lhs.ppat_attributes @ (List.hd (List.rev l)).ppat_attributes
    | _ -> c.pc_lhs.ppat_attributes
  in
  match find_attr "r" attrs with
  | Some a -> a.attr_loc
  | None -> c.pc_lhs.ppat_loc

(** Adds the rules derived from the laws of each operator (see [Syntax.law]) to
    its rule function, before its own rules, in the order of [law_order]. In the
    rule function [f (p1, ..., v1, v2)] of a binary operator [op]:
    - [[@fold g lift]]: [lits: C i1, C i2 -> lift (g pk ... pn s1 s2 i1 i2)],
      where [g] takes the last parameters [pk ... pn] of the node, then, if its
      parameters before the values of the literals have type [ty], the sorts
      [s1], [s2] of the literal operands, then the values of the literals, named
      after the first letter of their type ([i1], [i2] for [int]s, [i] for a
      unary operator). [C] is the notation of the type of a value, at the sort
      of its operand (see [resolve_notation]), or else the only leaf node of one
      value of that type. [lift], a function or a node, makes a term of the
      result; by default, the notation (or node) of its type at the sort of the
      result of the node, and nothing for a term. A node is built at the sort of
      its typing, or else at the sort of the spec;
    - [[@unit c]], for a literal [c]: [unit_c: x, c -> x] if [op] is commutative
      (it then also matches [c, x]), and otherwise [unit_c: _, c -> v1];
    - [[@zero c]], for a literal [c]: [zero_c: _, c -> c], where [c] stands for
      the term of the literal: the one that the language declares for it, at the
      sort of [v1] ([constant c (v) = e]), or else its notation, at the sort of
      the operand, built as above;
    - [[@unit c]], for a named constant [c]: [unit_c: x, y when y = c(x) -> x],
      where [c(x)] is the constant at the sort of [x], matched in either order
      if [op] is commutative ([[@comm]]);
    - [[@zero c]], for a named constant [c]: [zero_c: _, y when y = c(y) -> y],
      likewise;
    - [[@idem]]: [same: v, v -> v].

    In that of a unary operator [Op], over [v]:
    - [[@invol]]: [op: Op x -> x], named after [Op].

    The literals [0] and [1] are named [zero] and [one] in the names of the
    rules ([unit_zero], [zero_one]), and [true], [false] and the constants by
    themselves ([unit_true], [zero_ones]). *)
let law_cases globals raws =
  let open Ast_builder.Default in
  let derive raws n =
    let laws =
      List.filter_map
        (fun (m, law, loc, arg_loc) ->
          if m = n then Some (law, loc, arg_loc) else None)
        !lang.laws
      |> List.stable_sort (fun (a, _, _) (b, _, _) ->
          compare (law_order a) (law_order b))
    in
    let r = rule_of_node ((fun (_, l, _) -> l) (List.hd laws)) raws n in
    let op = Option.get (find_constr n) in
    let nparams = List.length op.c_args in
    let params = List.map fst r.rparams in
    let node_params = List.filteri (fun i _ -> i < nparams) params in
    let operands = List.filteri (fun i _ -> i >= nparams) params in
    let lit_name = function "0" -> "zero" | "1" -> "one" | c -> c in
    let case (law, loc, arg_loc) =
      let var x = evar ~loc x in
      let app f args = eapply ~loc (var f) args in
      (* [n (_, ..., _, ps)] *)
      let node_pat ps =
        let args = List.map (fun _ -> ppat_any ~loc) op.c_args @ ps in
        ppat_construct ~loc (Located.lident ~loc n)
          (Some (match args with [ a ] -> a | l -> ppat_tuple ~loc l))
      in
      let lit_pat c =
        if c = "true" || c = "false" then pbool ~loc (c = "true")
        else ppat_constant ~loc (Pconst_integer (c, None))
      in
      let v1 = var (List.hd operands) in
      (* the node [c] over [arg], at the sort that its typing gives it, or else
         at the sort of the spec *)
      let node_at c arg =
        pexp_extension ~loc
          ( { txt = "kanon.at"; loc },
            PStr
              [
                pstr_eval ~loc
                  (pexp_construct ~loc (Located.lident ~loc c) (Some arg))
                  [];
                pstr_eval ~loc (Option.get r.rspec) [];
              ] )
      in
      (* the term of the literal or constant [c]: its constant, at the sort of
         the operand [at], or else its node *)
      let lit_term ?(at = v1) c =
        match List.assoc_opt c !lang.constants with
        | Some (None, e) -> e
        | Some (Some v, e) ->
            object
              inherit Ast_traverse.map as super

              method! expression e =
                match e.pexp_desc with
                | Pexp_ident { txt = Lident x; _ } when x = v -> at
                | _ -> super#expression e
            end
              #expression
              e
        | None ->
            let lit =
              if c = "true" || c = "false" then ebool ~loc (c = "true")
              else eint ~loc (int_of_string c)
            in
            node_at (law_notation arg_loc n c) lit
      in
      (* the node of one argument of type [t] at a position of sort [sort]: the
         notation of [int]s or [bool]s, or else the only leaf node of one [t] *)
      let node_of ~what ~sort t =
        match t with
        | TInt | TBool ->
            resolve_notation arg_loc ~what
              ~lit:(if t = TInt then `Int else `Bool)
              ~sort
        | _ -> (
            match
              List.filter
                (fun c -> c.c_res = TKind && c.c_args = [ Arg t ])
                !lang.constrs
            with
            | [ c ] -> c.c_name
            | [] ->
                error arg_loc "%s: no leaf node has one argument of type %a"
                  what pp_ty t
            | cs ->
                error arg_loc "%s: several leaf nodes have one %a: %s" what
                  pp_ty t
                  (String.concat ", " (List.map (fun c -> c.c_name) cs)))
      in
      (* [y = c], at the sort of [x], for a named constant [c] *)
      let is_constant c y x =
        Some (eapply ~loc (var "=") [ var y; lit_term ~at:(var x) c ])
      in
      let rule, pats, guard, comm, body =
        match law with
        | Fold (g, lift) ->
            let what = Printf.sprintf "[@fold %s]" g in
            let s =
              match List.assoc_opt g globals with
              | Some s -> s
              | None -> error arg_loc "[@fold]: unknown function %s" g
            in
            let arity = List.length operands in
            let nargs = List.length s.args in
            if nargs < arity then
              error loc "%s: %s does not take the literals of %s" what g n;
            let tys = List.filteri (fun i _ -> i >= nargs - arity) s.args in
            (* the sorts of the literal operands, in the parameters of type [ty]
               right before their values *)
            let n_sorts =
              let rec count i =
                if
                  i < arity
                  && i < nargs - arity
                  && List.nth s.args (nargs - arity - 1 - i) = TSty
                then count (i + 1)
                else i
              in
              count 0
            in
            if n_sorts > 0 && n_sorts < arity then
              error arg_loc
                "%s: %s takes the sorts of %d operands, which %s has %d of" what
                g n_sorts n arity;
            let k = nargs - arity - n_sorts in
            if k > nparams then
              error arg_loc "%s: %s does not take the literals of %s" what g n;
            let xs =
              match tys with
              | t :: _ ->
                  let x = String.sub (Fmt.str "%a" pp_ty t) 0 1 in
                  if arity = 1 then [ x ]
                  else List.init arity (fun i -> x ^ string_of_int (i + 1))
              | [] -> []
            in
            (* the terms of the literals, whose sorts [f] takes *)
            let terms = List.map (fun x -> "lit_" ^ x) xs in
            let args = List.filteri (fun i _ -> i >= nparams - k) node_params in
            let sorts =
              if n_sorts = 0 then []
              else List.map (fun x -> app "type_of" [ var x ]) terms
            in
            let e =
              eapply ~loc (var g) (List.map var args @ sorts @ List.map var xs)
            in
            let lift =
              match lift with
              | Some l -> Some l
              | None when s.ret = TTerm -> None
              | None ->
                  Some
                    (node_of ~what
                       ~sort:
                         (match result_head n with
                         | Some h -> Head h
                         | None -> Unknown)
                       s.ret)
            in
            let body =
              match lift with
              | None -> e
              | Some l when match l.[0] with 'A' .. 'Z' -> true | _ -> false ->
                  node_at l e
              | Some f -> app f [ e ]
            in
            ( (if arity = 1 then "lit" else "lits"),
              List.mapi
                (fun i (t, x) ->
                  let p =
                    ppat_construct ~loc
                      (Located.lident ~loc
                         (node_of ~what ~sort:(operand_head n i) t))
                      (Some (pvar ~loc x))
                  in
                  if n_sorts = 0 then p
                  else ppat_alias ~loc p { txt = List.nth terms i; loc })
                (List.combine tys xs),
              None,
              false,
              body )
        | (Unit c | Zero c) when not (is_literal c) -> (
            (* the other operand, compared with the constant, in either order if
               [op] is commutative *)
            let comm = is_commutative n in
            match law with
            | Unit _ ->
                ( "unit_" ^ c,
                  [ pvar ~loc "x"; pvar ~loc "y" ],
                  is_constant c "y" "x",
                  comm,
                  var "x" )
            | _ ->
                ( "zero_" ^ c,
                  [ ppat_any ~loc; pvar ~loc "y" ],
                  is_constant c "y" "y",
                  comm,
                  var "y" ))
        | Unit c when is_commutative n ->
            ( "unit_" ^ lit_name c,
              [ pvar ~loc "x"; lit_pat c ],
              None,
              false,
              var "x" )
        | Unit c ->
            ("unit_" ^ lit_name c, [ ppat_any ~loc; lit_pat c ], None, false, v1)
        | Zero c -> (
            match List.assoc_opt c !lang.constants with
            | Some (Some _, _) ->
                (* the constant at the sort of the literal, which is that of
                   either operand *)
                ( "zero_" ^ lit_name c,
                  [
                    ppat_any ~loc;
                    ppat_alias ~loc (lit_pat c) { txt = "z"; loc };
                  ],
                  None,
                  false,
                  lit_term ~at:(var "z") c )
            | _ ->
                ( "zero_" ^ lit_name c,
                  [ ppat_any ~loc; lit_pat c ],
                  None,
                  false,
                  lit_term c ))
        | Idem ->
            ("same", [ pvar ~loc "v"; pvar ~loc "v" ], None, false, var "v")
        | Invol ->
            ( String.lowercase_ascii n,
              [ node_pat [ pvar ~loc "x" ] ],
              None,
              false,
              var "x" )
      in
      (* the patterns of the operands, in the shape of the scrutinee *)
      let lhs (scrut : expression) =
        let matched = ref [] in
        let operand (e : expression) =
          match e.pexp_desc with
          | Pexp_ident { txt = Lident x; _ } when List.mem x operands ->
              matched := x :: !matched;
              List.assoc x (List.combine operands pats)
          | _ -> ppat_any ~loc
        in
        let p =
          match scrut.pexp_desc with
          | Pexp_tuple l -> ppat_tuple ~loc (List.map operand l)
          | Pexp_apply
              ( { pexp_desc = Pexp_ident { txt = Lident sym; _ }; _ },
                [ (_, a); (_, b) ] )
            when Option.is_some (find_operator ~arity:2 sym) ->
              node_pat [ operand a; operand b ]
          | _ -> operand scrut
        in
        if List.sort compare !matched <> List.sort compare operands then
          error loc "[@%s]: %s does not match on the operands of %s"
            (law_name law) r.rname n;
        let name =
          attribute ~loc ~name:{ txt = "r"; loc }
            ~payload:(PStr [ pstr_eval ~loc (var rule) [] ])
        in
        let comm =
          if comm then
            [ attribute ~loc ~name:{ txt = "comm"; loc } ~payload:(PStr []) ]
          else []
        in
        { p with ppat_attributes = name :: comm }
      in
      (rule, fun scrut -> case ~lhs:(lhs scrut) ~guard ~rhs:body)
    in
    let derived = List.map case laws in
    let rec body (e : expression) =
      match e.pexp_desc with
      | Pexp_sequence (a, b) -> { e with pexp_desc = Pexp_sequence (a, body b) }
      | Pexp_match (scrut, cases) ->
          List.iter
            (fun c ->
              match case_rule c with
              | Some x when List.mem_assoc x derived ->
                  error (case_rule_loc c)
                    "rule %s is derived from the laws of %s" x n
              | _ -> ())
            cases;
          let derived = List.map (fun (_, c) -> c scrut) derived in
          { e with pexp_desc = Pexp_match (scrut, derived @ cases) }
      | _ -> error r.rname_loc "%s: the laws of %s need a match" r.rname n
    in
    List.map
      (fun r' ->
        if r'.rname = r.rname then { r with rbody = body r.rbody } else r')
      raws
  in
  List.fold_left
    (fun raws n ->
      Option.value (attempt (fun () -> derive raws n)) ~default:raws)
    raws
    (List.sort_uniq compare (List.map (fun (n, _, _, _) -> n) !lang.laws))

(* ---------------------------------------------------------------- *)
(* The typing of operators *)

(** Checks the typing [rt] of the operator [c], in the environment of the rules.
    A variable is free when it is neither an argument of [c] nor global: where a
    sort is expected it stands for any sort, and as the argument of a
    constructor of [ty] for any value of the argument's type. *)
let typing env0 ~nparams (c : constr) (rt : raw_typing) : typing =
  let loc = rt.rt_loc in
  let args = List.filteri (fun i _ -> i < nparams) c.c_args in
  let params =
    List.map
      (fun (e : expression) ->
        match e.pexp_desc with
        | Pexp_ident { txt = Lident x; _ } -> x
        | _ -> error e.pexp_loc "expected a name")
      rt.rt_params
  in
  let params = if params = [] then List.map (fun _ -> "_") args else params in
  if List.length params <> nparams then
    error
      (span_of (List.map (fun (e : expression) -> e.pexp_loc) rt.rt_params) loc)
      "%s has %d arguments" c.c_name nparams;
  let penv =
    List.concat
      (List.map2
         (fun x a -> if x = "_" then [] else [ (x, arg_ty a) ])
         params args)
  in
  let vars = ref [] in
  let is_free x =
    (not (List.mem_assoc x penv)) && not (List.mem_assoc x env0.globals)
  in
  let var loc x t =
    (match List.assoc_opt x !vars with
    | Some t' -> expect loc ~expected:t' t
    | None -> vars := !vars @ [ (x, t) ]);
    { e = EVar x; ety = t; eloc = loc }
  in
  let env () = { env0 with vars = penv @ !vars } in
  let rec sort (e : expression) : Syntax.expr =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident x; _ } when is_free x -> var e.pexp_loc x TSty
    | Pexp_construct ({ txt = Lident n; _ }, arg) -> (
        match find_constr n with
        | Some ({ c_res = TSty; _ } as tc) ->
            let args = constr_args e.pexp_loc tc arg split_pexp in
            let args =
              List.map2
                (fun a (e : expression) ->
                  match (e.pexp_desc, arg_ty a) with
                  | Pexp_ident { txt = Lident x; _ }, t when is_free x ->
                      var e.pexp_loc x t
                  | _, TSty -> sort e
                  | _, t -> expr (env ()) ~expected:t e)
                tc.c_args args
            in
            { e = EConstr (tc, args); ety = TSty; eloc = e.pexp_loc }
        | Some c when c.c_res = TKind || Option.is_some (node_of_op c) ->
            error e.pexp_loc "%s is a node, not a sort" n
        | _ -> error e.pexp_loc "%s is not a sort" n)
    | _ -> error e.pexp_loc "expected a sort"
  in
  let sorts = List.map sort rt.rt_sorts in
  let cond = Option.map (expr (env ()) ~expected:TBool) rt.rt_when in
  {
    t_constr = c;
    t_params = params;
    t_vars = !vars;
    t_sorts = sorts;
    t_nary = rt.rt_nary;
    t_when = cond;
  }

(** The typings of the nodes: of the operands that are terms and of the result,
    or of the result alone. *)
let typings env0 =
  List.filter_map
    (fun (n, (rt : raw_typing)) ->
      attempt @@ fun () ->
      let c = Option.get (find_constr n) in
      (* the operands of a node are those of its typing (see [node_arity]) *)
      if c.c_res <> TKind && Option.is_none (node_of_op c) then
        error rt.rt_loc "%s: only nodes have a typing" n;
      let nparams = List.length c.c_args in
      (n, typing env0 ~nparams c rt))
    !lang.raw_typing

(** Whether a typing is that of an operator on terms, over its operands. *)
let operator_typing (t : typing) =
  match node_of_op t.t_constr with
  | Some (_, operands) -> List.length t.t_sorts = List.length operands + 1
  | None -> false

(** Adds the cases of each [extend rule f] item to the rule function [f], which
    an earlier item defines: before its rule [r] for [extend rule f before r],
    and otherwise last, but before a final catch-all case [_]. Likewise for
    [extend fn f] and the function [f]. The cases go into the match in tail
    position of [f]'s body, behind [let]s, sequences and the right operands of
    [||] and [&&]. *)
let extend_rules (str : structure) =
  extension_cases := [];
  let splice loc f before (ext : Ppxlib.case list) (cs : Ppxlib.case list) =
    extension_cases :=
      List.map (fun (c : Ppxlib.case) -> (c.pc_lhs.ppat_loc, f)) ext
      @ !extension_cases;
    ignore
      (List.fold_left
         (fun names c ->
           match case_rule c with
           | Some r when List.mem r names ->
               error (case_rule_loc c) "extend %s: %s already has a rule %s" f f
                 r
           | Some r -> r :: names
           | None -> names)
         (List.filter_map case_rule cs)
         ext);
    match before with
    | Some (r, rloc) -> (
        let rec go = function
          | c :: cs when case_rule c = Some r -> Some (ext @ (c :: cs))
          | c :: cs -> Option.map (List.cons c) (go cs)
          | [] -> None
        in
        match go cs with
        | Some cs -> cs
        | None -> error rloc "extend %s: %s has no rule %s" f f r)
    | None -> (
        match List.rev cs with
        | ({ pc_lhs; pc_guard = None; _ } as last) :: rest when is_blank pc_lhs
          ->
            List.rev rest @ ext @ [ last ]
        | _ -> cs @ ext)
  in
  let rec insert loc f before ext (e : expression) =
    match e.pexp_desc with
    | Pexp_sequence (a, b) ->
        { e with pexp_desc = Pexp_sequence (a, insert loc f before ext b) }
    | Pexp_let (r, vbs, b) ->
        { e with pexp_desc = Pexp_let (r, vbs, insert loc f before ext b) }
    | Pexp_apply
        ( ({ pexp_desc = Pexp_ident { txt = Lident ("||" | "&&"); _ }; _ } as op),
          [ a; (l, b) ] ) ->
        {
          e with
          pexp_desc = Pexp_apply (op, [ a; (l, insert loc f before ext b) ]);
        }
    | Pexp_match (s, cs) ->
        { e with pexp_desc = Pexp_match (s, splice loc f before ext cs) }
    | _ -> error loc "extend %s: %s does not end with a match" f f
  in
  let extend items (si : structure_item) =
    match si.pstr_desc with
    | Pstr_eval
        ( {
            pexp_desc = Pexp_function ([], None, Pfunction_cases (ext, _, _));
            _;
          },
          attrs )
      when has_attr "extend" attrs ->
        (* at the name of the extended function *)
        let f, loc = string_attr_loc (Option.get (find_attr "extend" attrs)) in
        let before = Option.map string_attr_loc (find_attr "before" attrs) in
        let fn = has_attr "fn" attrs in
        let rec go = function
          | ({ pstr_desc = Pstr_value (r, [ vb ]); _ } as item) :: items
            when (match vb.pvb_pat.ppat_desc with
                   | Ppat_var { txt; _ } -> txt = f
                   | _ -> false)
                 && Option.is_some (spec_of_attrs vb.pvb_attributes) <> fn -> (
              match vb.pvb_expr.pexp_desc with
              | Pexp_function (ps, ret, Pfunction_body body) ->
                  let body = insert loc f before ext body in
                  let pvb_expr =
                    {
                      vb.pvb_expr with
                      pexp_desc = Pexp_function (ps, ret, Pfunction_body body);
                    }
                  in
                  {
                    item with
                    pstr_desc = Pstr_value (r, [ { vb with pvb_expr } ]);
                  }
                  :: items
              | _ ->
                  (* a rule whose parameters are those of its spec *)
                  let pvb_expr = insert loc f before ext vb.pvb_expr in
                  {
                    item with
                    pstr_desc = Pstr_value (r, [ { vb with pvb_expr } ]);
                  }
                  :: items)
          | item :: items -> item :: go items
          | [] ->
              error loc "extend %s: no %s %s is defined before" f
                (if fn then "fn" else "rule")
                f
        in
        go items
    | _ -> si :: items
  in
  (* an item that cannot be added is left out, when errors are collected *)
  List.rev
    (List.fold_left
       (fun items si ->
         Option.value (attempt (fun () -> extend items si)) ~default:items)
       [] str)

(** The check that the spec of the rule [r] is well-typed: that the sorts of its
    operands have the shapes that the typing of its node and their annotations
    give them, and that the side condition of the typing holds. The generated
    OCaml asserts it, and the proofs assume it. *)
let spec_check globals (r : raw_fn) (spec : expression option) :
    expression option =
  let open Ast_builder.Default in
  let loc = { r.rloc with loc_ghost = true } in
  let counter = ref 0 in
  let fresh () =
    incr counter;
    Printf.sprintf "kanon__s%d" !counter
  in
  let guards = ref [] in
  let is_sort c =
    match find_constr c with Some c -> c.c_res = TSty | None -> false
  in
  (* operators and global functions are not variables *)
  let is_global x =
    List.mem_assoc x globals
    || not (match x.[0] with 'a' .. 'z' | '_' -> true | _ -> false)
  in
  (* the pattern of the sort [s], whose variables [is_var] are named [name]
     where they first appear, and otherwise compared with [subst] *)
  let rec conv ~is_var ~name ~subst bound (s : expression) : pattern =
    let go = conv ~is_var ~name ~subst bound in
    let other () =
      let f = fresh () in
      guards :=
        !guards @ [ eapply ~loc (evar ~loc "=") [ evar ~loc f; subst s ] ];
      pvar ~loc f
    in
    match s.pexp_desc with
    | Pexp_ident { txt = Lident x; _ }
      when is_var x && not (Hashtbl.mem bound x) ->
        Hashtbl.add bound x ();
        pvar ~loc (name x)
    | Pexp_construct ({ txt = Lident c; _ }, arg) when is_sort c ->
        ppat_construct ~loc (Located.lident ~loc c)
          (Option.map
             (fun (a : expression) ->
               match a.pexp_desc with
               | Pexp_tuple l -> ppat_tuple ~loc (List.map go l)
               | _ -> go a)
             arg)
    | _ -> other ()
  in
  let subst f =
    object
      inherit Ast_traverse.map as super

      method! expression e =
        match e.pexp_desc with
        | Pexp_ident { txt = Lident x; _ } -> (
            match f x with Some e' -> e' | None -> e)
        | _ -> super#expression e
    end
  in
  let scruts = ref [] and pats = ref [] in
  let checked = ref [] in
  let check (v : expression) p =
    (match v.pexp_desc with
    | Pexp_ident { txt = Lident x; _ } -> checked := (x, p) :: !checked
    | _ -> ());
    scruts := !scruts @ [ eapply ~loc (evar ~loc "type_of") [ v ] ];
    pats := !pats @ [ p ]
  in
  (* whether two patterns of sorts have the same shape, up to their variables *)
  let rec same_shape (p : pattern) (q : pattern) =
    match (p.ppat_desc, q.ppat_desc) with
    | (Ppat_var _ | Ppat_any), (Ppat_var _ | Ppat_any) -> true
    | Ppat_construct (c, a), Ppat_construct (d, b) -> (
        c.txt = d.txt
        &&
        match (a, b) with
        | None, None -> true
        | Some (_, a), Some (_, b) -> same_shape a b
        | _ -> false)
    | Ppat_tuple l, Ppat_tuple m ->
        List.length l = List.length m && List.for_all2 same_shape l m
    | _ -> false
  in
  (* the typing of the node of the spec *)
  (match Option.map (fun (s : expression) -> s.pexp_desc) spec with
  | Some (Pexp_construct ({ txt = Lident n; _ }, arg)) -> (
      match List.assoc_opt n !lang.raw_typing with
      | Some rt when List.length rt.rt_sorts > 1 ->
          let args =
            match arg with
            | Some { pexp_desc = Pexp_tuple l; _ } -> l
            | Some a -> [ a ]
            | None -> []
          in
          let n_ops = List.length rt.rt_sorts - 1 in
          let nparams = List.length args - n_ops in
          let params = List.filteri (fun i _ -> i < nparams) args in
          let operands = List.filteri (fun i _ -> i >= nparams) args in
          let is_ident (e : expression) =
            match e.pexp_desc with Pexp_ident _ -> true | _ -> false
          in
          (* the operands built by the spec are well-typed; the elements of a
             list of operands are not checked *)
          if (not rt.rt_nary) && List.for_all is_ident operands then (
            let param_names =
              List.map
                (fun (e : expression) ->
                  match e.pexp_desc with
                  | Pexp_ident { txt = Lident x; _ } -> x
                  | _ -> "_")
                rt.rt_params
            in
            let param x =
              match List.find_index (( = ) x) param_names with
              | Some i when x <> "_" -> List.nth_opt params i
              | _ -> None
            in
            let is_var x = param x = None && (not (is_global x)) && x <> "_" in
            let name x = "kanon__" ^ x in
            let sub =
              subst (fun x ->
                  match param x with
                  | Some e -> Some e
                  | None when is_var x -> Some (evar ~loc (name x))
                  | None -> None)
            in
            let bound = Hashtbl.create 4 in
            List.iteri
              (fun i o ->
                check o
                  (conv ~is_var ~name ~subst:sub#expression bound
                     (List.nth rt.rt_sorts i)))
              operands;
            Option.iter
              (fun w -> guards := !guards @ [ sub#expression w ])
              rt.rt_when)
      | _ -> ())
  | _ -> ());
  (* the annotations of the operands, and of the parameters *)
  let bound = Hashtbl.create 4 in
  let is_var x = not (is_global x) in
  let name x = "kanon__v_" ^ x in
  let sub =
    subst (fun x -> if is_var x then Some (evar ~loc (name x)) else None)
  in
  List.iter
    (fun (v, s) ->
      let n_guards = List.length !guards in
      let p = conv ~is_var ~name ~subst:sub#expression bound s in
      (* unless the typing of the node already checks it *)
      match List.assoc_opt v !checked with
      | Some q when List.length !guards = n_guards && same_shape p q -> ()
      | _ -> check (evar ~loc v) p)
    r.rsorts;
  let trivial (p : pattern) =
    match p.ppat_desc with Ppat_var _ | Ppat_any -> true | _ -> false
  in
  if !guards = [] && List.for_all trivial !pats then None
  else
    let tuple = function [ x ] -> x | l -> pexp_tuple ~loc l in
    let ptuple = function [ x ] -> x | l -> ppat_tuple ~loc l in
    let guard =
      match !guards with
      | [] -> None
      | g :: gs ->
          Some
            (List.fold_left
               (fun a b -> eapply ~loc (evar ~loc "&&") [ a; b ])
               g gs)
    in
    Some
      (pexp_match ~loc (tuple !scruts)
         [
           case ~lhs:(ptuple !pats) ~guard ~rhs:(ebool ~loc true);
           case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:(ebool ~loc false);
         ])

(** The variables that the annotations of the operands of a spec bind, which
    stand for the matching parts of their sorts. *)
let sort_binds env (r : raw_fn) =
  List.concat_map
    (fun (v, (s : expression)) ->
      let open Ast_builder.Default in
      let loc = s.pexp_loc in
      let rec to_pat (s : expression) : pattern =
        match s.pexp_desc with
        | Pexp_ident { txt = Lident x; _ }
          when not (List.mem_assoc x env.globals) ->
            pvar ~loc x
        | Pexp_construct (c, arg) ->
            ppat_construct ~loc c
              (Option.map
                 (fun (a : expression) ->
                   match a.pexp_desc with
                   | Pexp_tuple l -> ppat_tuple ~loc (List.map to_pat l)
                   | _ -> to_pat a)
                 arg)
        | _ -> ppat_any ~loc
      in
      match s.pexp_desc with
      | Pexp_construct
          ( { txt = Lident c; _ },
            Some { pexp_desc = Pexp_ident { txt = Lident x; _ }; _ } )
        when List.mem_assoc c !lang.sort_getters ->
          (* read by the getter of the sort *)
          let g = List.assoc c !lang.sort_getters in
          [ (x, expr env (eapply ~loc (evar ~loc g) [ evar ~loc v ])) ]
      | _ ->
          let p = pat TSty (to_pat s) in
          let scrut =
            expr env ~expected:TSty
              (eapply ~loc (evar ~loc "type_of") [ evar ~loc v ])
          in
          let rec only x (q : Syntax.pat) : Syntax.pat =
            match q.p with
            | PVar y when y <> x -> { q with p = PAny }
            | PConstr (c, l) -> { q with p = PConstr (c, List.map (only x) l) }
            | PTuple l -> { q with p = PTuple (List.map (only x) l) }
            | _ -> q
          in
          List.map
            (fun (x, (t, _)) ->
              let case pat body =
                { pat; guard = None; body; rule = None; cloc = loc; alt = [] }
              in
              ( x,
                {
                  e =
                    EMatch
                      ( [ scrut ],
                        [
                          case (only x p) { e = EVar x; ety = t; eloc = loc };
                          case { p with p = PAny }
                            { e = EUnreachable; ety = t; eloc = loc };
                        ] );
                  ety = t;
                  eloc = loc;
                } ))
            (binders p))
    r.rsorts

(* ---------------------------------------------------------------- *)
(* Pruning redundant cases *)

(** Whether the (linearized) pattern [p] matches everything that [q] matches: a
    conservative check, which gives up on what it does not know. *)
let rec subsumes (p : Syntax.pat) (q : Syntax.pat) =
  let all l m = List.length l = List.length m && List.for_all2 subsumes l m in
  match (p.p, q.p) with
  | (PAny | PVar _), _ -> true
  | _ when is_catch_all p -> true
  | PAs (p, _), _ -> subsumes p q
  | _, PAs (q, _) -> subsumes p q
  | PBool a, PBool b -> a = b
  | PInt a, PInt b -> Z.equal a b
  | PUnit, PUnit | PNone, PNone | PNil, PNil -> true
  | PSome p, PSome q -> subsumes p q
  | PCons (a, b), PCons (c, d) -> subsumes a c && subsumes b d
  | PTuple l, PTuple m -> all l m
  | PConstr (c, l), PConstr (d, m) -> c.c_name = d.c_name && all l m
  | PRecord l, PRecord m ->
      List.for_all
        (fun (f, p) ->
          match List.assoc_opt f m with Some q -> subsumes p q | None -> false)
        l
  | _ -> false

(** The cases of [cases] that an earlier case without a guard does not already
    match: the others can never be taken. Guards are not looked into, so a case
    with a guard (which includes the repeated variables and the integer literals
    of its pattern, see [linearize]) covers nothing. *)
let prune_cases (cases : Syntax.case list) =
  let kept =
    List.rev
      (List.fold_left
         (fun kept (c : Syntax.case) ->
           if
             List.exists
               (fun (k : Syntax.case) -> k.guard = None && subsumes k.pat c.pat)
               kept
           then kept
           else c :: kept)
         [] cases)
  in
  (* a case added by [extend] is never left out without a word *)
  List.iter
    (fun (loc, f) ->
      if
        List.exists (fun (c : Syntax.case) -> c.cloc = loc) cases
        && not (List.exists (fun (c : Syntax.case) -> c.cloc = loc) kept)
      then
        error loc
          "extend %s: this case is unreachable (an earlier case of %s matches \
           everything it does), so it was not added"
          f f)
    !extension_cases;
  kept

(** [e] without the cases that its matches can never take. *)
let rec prune (e : Syntax.expr) : Syntax.expr =
  let go = prune in
  let d =
    match e.e with
    | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> e.e
    | EConstr (c, l) -> EConstr (c, List.map go l)
    | ENode (a, b) -> ENode (go a, go b)
    | ECall (f, l) -> ECall (f, List.map go l)
    | ELocalCall (f, l) -> ELocalCall (f, List.map go l)
    | EUnop (o, a) -> EUnop (o, go a)
    | EBinop (o, a, b) -> EBinop (o, go a, go b)
    | EIf (a, b, c) -> EIf (go a, go b, go c)
    | ELet (p, a, b) -> ELet (p, go a, go b)
    | ELetFun (f, ps, a, b) -> ELetFun (f, ps, go a, go b)
    | EMatch (scruts, cases) ->
        EMatch
          ( List.map go scruts,
            prune_cases
              (List.map
                 (fun (c : Syntax.case) ->
                   { c with guard = Option.map go c.guard; body = go c.body })
                 cases) )
    | ETuple l -> ETuple (List.map go l)
    | ESome a -> ESome (go a)
    | ECons (a, b) -> ECons (go a, go b)
    | ERecord l -> ERecord (List.map (fun (f, e) -> (f, go e)) l)
    | EField (a, f) -> EField (go a, f)
    | EAssert (a, b) -> EAssert (go a, go b)
  in
  { e with e = d }

(** Parses the Kanon file [file], read from [lexbuf]. *)
let parse ~file lexbuf : structure =
  Lexing.set_filename lexbuf file;
  let at p = { loc_start = p; loc_end = p; loc_ghost = false } in
  (* where the last token, and the one before it, are doc comments *)
  let cur = ref None and prev = ref None in
  let token lb =
    let t = Kanon_lexer.token lb in
    prev := !cur;
    (cur := match t with Kanon_parser.DOC _ -> Some lb.lex_start_p | _ -> None);
    t
  in
  try Kanon_parser.file token lexbuf with
  | Kanon_lexer.Error (p, msg) -> raise (Error (at p, msg))
  | Syntax.Misplaced_doc (loc, msg) -> raise (Error (loc, msg))
  | Kanon_parser.Error -> (
      match (!cur, !prev) with
      | Some p, _ | None, Some p ->
          raise
            (Error
               ( at p,
                 "misplaced doc comment: it must come right before a fn, rule, \
                  node, sort, type, prim, oracle, infix, prefix or constant" ))
      | None, None -> raise (Error (at lexbuf.lex_start_p, "syntax error")))

let parse_file file : structure =
  let ic = open_in_bin file in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> parse ~file (Lexing.from_channel ic))

(** Parses the contents [s] of the Kanon file [file]. *)
let parse_string ~file s : structure = parse ~file (Lexing.from_string s)

(** The functions that the language gets from Kanon: if it has commutative
    operators, [mk_commut_binop op l r] is the node of [op] over [l] and [r] in
    the order of their hash-consing tags, given by the oracle [tag_le], which
    rules use to build the nodes of commutative operators. *)
let comm_fns () =
  match !lang.commutative with
  | [] -> []
  | c :: _ ->
      let op = Option.get (find_constr c) in
      let kc, _ = Option.get (node_of_op op) in
      let ty = match op.c_res with TData t -> t | _ -> assert false in
      parse_string ~file:kanon_file
        (Printf.sprintf
           "oracle tag_le : t -> t -> bool\n\
           \            fn mk_commut_binop (op : %s) (l r : t) : kind =\n\
           \             if tag_le l r then %s (op, l, r) else %s (op, r, l)\n"
           ty kc.c_name kc.c_name)

(** The sorts of the parameters of [r] that are terms, as far as they are known:
    from the typing of the node of its spec, for its operands, and from their
    annotations. *)
let param_sorts (r : raw_fn) =
  let head (s : expression) =
    match s.pexp_desc with
    | Pexp_construct ({ txt = Lident c; _ }, _) -> Head c
    | _ -> Unknown
  in
  let from_typing =
    match r.rspec with
    | Some { pexp_desc = Pexp_construct ({ txt = Lident n; _ }, arg); _ }
      when r.rcases -> (
        let args =
          match arg with
          | Some { pexp_desc = Pexp_tuple l; _ } -> l
          | Some a -> [ a ]
          | None -> []
        in
        match List.assoc_opt n !node_typings with
        | Some t when List.length t.t_sorts > 1 ->
            let n_ops = List.length t.t_sorts - 1 in
            let operands =
              List.filteri (fun i _ -> i >= List.length args - n_ops) args
            in
            let sort (s : Syntax.expr) =
              let h =
                match s.e with EConstr (c, _) -> Head c.c_name | _ -> Unknown
              in
              if t.t_nary then Elems h else h
            in
            List.concat
              (List.map2
                 (fun (o : expression) s ->
                   match o.pexp_desc with
                   | Pexp_ident { txt = Lident x; _ } -> [ (x, sort s) ]
                   | _ -> [])
                 operands
                 (List.filteri (fun i _ -> i < n_ops) t.t_sorts))
        | _ -> [])
    | _ -> []
  in
  List.map (fun (x, s) -> (x, head s)) r.rsorts @ from_typing

(** Whether the variable [x] occurs in [e] (which does not shadow it). *)
let rec uses x (e : Syntax.expr) =
  let go = uses x in
  match e.e with
  | EVar y -> x = y
  | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> false
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l ->
      List.exists go l
  | ENode (a, b)
  | EBinop (_, a, b)
  | ECons (a, b)
  | EAssert (a, b)
  | ELet (_, a, b)
  | ELetFun (_, _, a, b) ->
      go a || go b
  | EUnop (_, a) | ESome a | EField (a, _) -> go a
  | EIf (a, b, c) -> go a || go b || go c
  | ERecord l -> List.exists (fun (_, e) -> go e) l
  | EMatch (scruts, cases) ->
      List.exists go scruts
      || List.exists
           (fun (c : case) ->
             Option.fold ~none:false ~some:go c.guard || go c.body)
           cases

(** Checks the raw function [r], in the global environment [env0]. *)
let check_fn env0 globals r =
  atom_counter := 0;
  List.iter2
    (fun (x, _) loc -> no_shadow env0 loc x)
    r.rparams
    (if List.length r.rparam_locs = List.length r.rparams then r.rparam_locs
     else List.map (fun _ -> r.rname_loc) r.rparams);
  let env = { env0 with vars = r.rparams; sorts = param_sorts r } in
  if r.rcases && Option.is_none r.rspec then
    error r.rname_loc "%s: [@cases] needs a spec" r.rname;
  cases_mode := r.rcases;
  let rbody =
    let asserted check body =
      match check with
      | Some c ->
          let loc = c.pexp_loc in
          Ast_builder.Default.(pexp_sequence ~loc (pexp_assert ~loc c) body)
      | None -> body
    in
    match r.rspec with
    | Some spec when r.rcases ->
        let body = spec_match spec (with_default spec r.rbody) in
        asserted
          (if r.runtyped then None else spec_check globals r (Some spec))
          body
    | _ ->
        (* the sorts of the parameters *)
        asserted
          (if r.rsorts = [] then None else spec_check globals r None)
          r.rbody
  in
  (* the variables of the sorts of the parameters: read from them in the spec,
     and bound once, on entry, in the body, where the parameters may be
     shadowed *)
  let binds = sort_binds env r in
  sort_vars := binds;
  let spec =
    Option.map
      (fun (s : expression) ->
        if r.rret <> TTerm then
          error s.pexp_loc "%s: only term-returning functions have a spec"
            r.rname;
        in_spec := true;
        let s = expr env ~expected:TTerm s in
        in_spec := false;
        s)
      r.rspec
  in
  ordered := Option.is_some spec;
  sort_vars :=
    List.map (fun (x, (v : Syntax.expr)) -> (x, { v with e = EVar x })) binds;
  let body = expr env ~expected:r.rret rbody in
  let body =
    let bind (body : Syntax.expr) =
      List.fold_right
        (fun (x, (rhs : Syntax.expr)) (body : Syntax.expr) ->
          if uses x body then
            {
              body with
              e =
                ELet
                  ( { p = PVar x; pty = rhs.ety; ploc = rhs.eloc; pid = 0 },
                    rhs,
                    body );
            }
          else body)
        binds body
    in
    (* before the check of the sorts of the parameters, which may use them *)
    bind body
  in
  cases_mode := false;
  ordered := false;
  sort_vars := [];
  {
    name = r.rname;
    params = r.rparams;
    ret = r.rret;
    spec;
    cases = r.rcases;
    body = prune body;
    floc = r.rloc;
    fdoc = r.rdoc;
    no_lean = has_attr "no_lean" r.rattrs;
  }

(** The number of errors collected so far. *)
let errors_so_far () = List.length (Option.value !collected ~default:[])

(** The end of a phase that started with [n] errors: stops if it had errors. *)
let checkpoint_since n = if errors_so_far () > n then raise Stop

let program (str : structure) : program =
  let str = extend_rules (comm_fns () @ str) in
  (* the functions whose operators could not be replaced, which are not checked
     further *)
  let skip = ref [] in
  let str =
    List.map
      (fun (si : structure_item) ->
        match attempt (fun () -> desugar_ops#structure_item si) with
        | Some si -> si
        | None ->
            (match si.pstr_desc with
            | Pstr_value
                (_, [ { pvb_pat = { ppat_desc = Ppat_var { txt; _ }; _ }; _ } ])
              ->
                skip := txt :: !skip
            | _ -> ());
            si)
      str
  in
  let start = errors_so_far () in
  let prims, raws =
    List.fold_left
      (fun (prims, raws) (si : structure_item) ->
        Option.value ~default:(prims, raws)
          (attempt (fun () ->
               match si.pstr_desc with
               | Pstr_primitive vd ->
                   let pargs, pret = arrow_of_core vd.pval_type in
                   ( ( {
                         pname = vd.pval_name.txt;
                         pargs;
                         pret;
                         oracle = vd.pval_prim = [ "oracle" ];
                         ploc = vd.pval_name.loc;
                         pdoc = fst (take_doc vd.pval_attributes);
                         pno_lean =
                           (let oracle = vd.pval_prim = [ "oracle" ] in
                            let attrs = snd (take_doc vd.pval_attributes) in
                            if oracle then
                              reject_no_lean
                                "an oracle is a parameter of the Lean model"
                                attrs;
                            check_attrs [ "no_lean" ] attrs;
                            has_attr "no_lean" attrs);
                       },
                       vd.pval_name.loc )
                     :: prims,
                     raws )
               | Pstr_value (_, [ vb ]) -> (prims, raw_fn vb :: raws)
               | Pstr_value _ -> error si.pstr_loc "one function per let"
               | _ -> error si.pstr_loc "unsupported top-level item")))
      ([], []) str
  in
  let prims = List.rev prims and raws = List.rev raws in
  let globals =
    (("type_of", { args = [ TTerm ]; ret = TSty })
    :: List.map
         (fun (p, _) -> (p.pname, { args = p.pargs; ret = p.pret }))
         prims)
    @ List.map
        (fun r -> (r.rname, { args = List.map snd r.rparams; ret = r.rret }))
        raws
  in
  (* the definitions after the first of a name, at their names *)
  let defs =
    (("type_of", Location.none) :: List.map (fun (p, l) -> (p.pname, l)) prims)
    @ List.map (fun r -> (r.rname, r.rname_loc)) raws
  in
  List.iter
    (fun n ->
      match List.filter (fun (m, _) -> m = n) defs with
      | _ :: (_ :: _ as again) ->
          List.iter
            (fun (_, loc) ->
              ignore (attempt (fun () -> error loc "%s is defined twice" n)))
            again
      | _ -> ())
    (List.sort_uniq compare (List.map fst defs)
    |> List.sort (fun a b ->
        compare
          (List.find_index (fun (m, _) -> m = a) defs)
          (List.find_index (fun (m, _) -> m = b) defs)));
  let prims = List.map fst prims in
  checkpoint_since start;
  lang :=
    {
      !lang with
      ty_only =
        "type_of"
        :: List.filter_map
             (fun r -> if r.rty_only then Some r.rname else None)
             raws;
    };
  List.iter
    (fun r ->
      if r.rty_only then
        match r.rparams with
        | [ (x, TTerm) ] when not (mentions x r.rbody) -> ()
        | _ ->
            ignore
              (attempt (fun () ->
                   error (rattr_loc r "ty_only")
                     "%s: [@ty_only] functions take one term, and only read \
                      its type"
                     r.rname)))
    raws;
  let env0 = { vars = []; sorts = []; locals = []; globals } in
  (* the functions of the operators on values, which do not compete with their
     built-in meanings *)
  List.iter
    (fun (o : operator) ->
      Option.iter
        (fun f ->
          ignore
            (attempt (fun () ->
                 let s =
                   match List.assoc_opt f globals with
                   | Some s -> s
                   | None -> error o.op_loc "%s: unknown function %s" o.sym f
                 in
                 match builtin_op ~arity:o.arity o.sym with
                 | Some (arg, _) when List.for_all (ty_equal arg) s.args ->
                     error o.op_loc
                       "%s is built in on %a: it cannot also be the function %s"
                       (op_name ~arity:o.arity o.sym)
                       pp_ty arg f
                 | _ -> ())))
        o.on_value)
    !lang.operators;
  let raws = law_cases globals raws in
  let start = errors_so_far () in
  let typings = typings env0 in
  checkpoint_since start;
  node_typings := typings;
  let fns =
    List.filter_map
      (fun r ->
        if List.mem r.rname !skip then None
        else
          let reset () =
            cases_mode := false;
            ordered := false;
            sort_vars := [];
            in_spec := false
          in
          match attempt (fun () -> check_fn env0 globals r) with
          | Some f -> Some f
          | None ->
              reset ();
              None)
      raws
  in
  (* what Lean models does not call what it does not *)
  let hidden =
    List.filter_map
      (fun (f : fn) -> if f.no_lean then Some f.name else None)
      fns
    @ List.filter_map
        (fun (p : prim) -> if p.pno_lean then Some p.pname else None)
        prims
  in
  let check_calls what (e : Syntax.expr) =
    ignore
      (Syntax.fold_calls
         (fun () g loc ->
           if List.mem g hidden then
             ignore
               (attempt (fun () ->
                    error loc "%s calls %s, which is [@no_lean]" what g)))
         () e)
  in
  List.iter
    (fun (f : fn) ->
      if not f.no_lean then (
        let what =
          Printf.sprintf "%s %s"
            (if Option.is_some f.spec then "rule" else "fn")
            f.name
        in
        Option.iter (check_calls what) f.spec;
        check_calls what f.body))
    fns;
  List.iter
    (fun (_, (t : typing)) ->
      let what = Printf.sprintf "the typing of %s" t.t_constr.c_name in
      List.iter (check_calls what) t.t_sorts;
      Option.iter (check_calls what) t.t_when)
    typings;
  { prims; fns; typing = List.filter operator_typing (List.map snd typings) }

(** The language before any declaration. *)
let initial_lang = !lang

(** The errors of the declaration of a language, as far as they can be found
    independently: [language] stops at the first. *)
let language_errors str = collect_errors language str

(** The errors of the rules of a language, as far as they can be found
    independently (those of each function, once the signatures of all are
    known): [program] stops at the first. *)
let program_errors str = collect_errors (fun s -> ignore (program s)) str

(** Restores the state of the checker, and the infix words of the lexer, to
    those before any file is read, to check another language (in the language
    server). *)
let reset () =
  lang := initial_lang;
  Hashtbl.reset infix_words;
  cases_mode := false;
  pid_counter := 0;
  Hashtbl.reset case_vars;
  sort_vars := [];
  node_typings := [];
  atom_counter := 0;
  in_spec := false;
  ordered := false
