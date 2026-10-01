(** Front-end: converts the OCaml parse tree of a Kanon file into typed Kanon
    ({!Syntax}), rejecting anything outside of the language. *)

open Ppxlib
open Syntax

exception Error of Location.t * string

let error loc fmt = Fmt.kstr (fun s -> raise (Error (loc, s))) fmt

let pp_loc ft (loc : Location.t) =
  let p = loc.loc_start in
  Fmt.pf ft "%s:%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

(* ---------------------------------------------------------------- *)
(* Types *)

let ty_of_name = function
  | "int" -> Some TInt
  | "bool" -> Some TBool
  | "unit" -> Some TUnit
  | "t" -> Some TTerm
  | "kind" -> Some TKind
  | "ty" -> Some TSty
  | s when Option.is_some (find_decl s) -> Some (TData s)
  | _ -> None

let rec ty_of_core (ct : core_type) : Syntax.ty =
  match ct.ptyp_desc with
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

type env = {
  vars : (string * Syntax.ty) list;
  locals : (string * sig_) list;
  globals : (string * sig_) list;  (** functions and primitives *)
}

let find_global env loc name =
  match List.assoc_opt name env.globals with
  | Some s -> s
  | None -> error loc "unknown function %s" name

(* ---------------------------------------------------------------- *)
(* Patterns *)

(** Whether the function being checked is a [[@cases]] one, where [C x], for [C]
    the constructor of integer literals, binds [x] to the literal's value. *)
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

(** Operators can be used directly as node constructors: [Add (c, l, r)] stands
    for [Binop (Add c, l, r)], [Not p] for [Unop (Not, p)], etc. (see
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
let rec pat (expected : Syntax.ty) (p : pattern) : Syntax.pat =
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
    comm ~explicit:true (pat' expected (strip_attr "comm" p))
  else comm ~explicit:false (pat' expected p)

and pat' (expected : Syntax.ty) (p : pattern) : Syntax.pat =
  let loc = p.ppat_loc in
  let mk d = { p = d; pty = expected; ploc = loc; pid = next_pid () } in
  let lit_node kname arg_pat =
    let c = Option.get (find_constr kname) in
    mk
      (PConstr
         ( c,
           [
             {
               p = arg_pat;
               pty = arg_ty (List.hd c.c_args);
               ploc = loc;
               pid = next_pid ();
             };
           ] ))
  in
  match p.ppat_desc with
  | Ppat_constant (Pconst_integer (s, None))
    when expected = TTerm && Option.is_some !lang.lit_node ->
      lit_node (Option.get !lang.lit_node) (PInt (Z.of_string s))
  | Ppat_construct ({ txt = Lident (("true" | "false") as b); _ }, None)
    when expected = TTerm && Option.is_some !lang.lit_bool ->
      lit_node (Option.get !lang.lit_bool) (PBool (b = "true"))
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
      let operands = List.map2 pat operand_tys operands in
      mk (PConstr (kc, op_pat :: operands))
  | Ppat_any -> mk PAny
  | Ppat_var { txt; _ } -> mk (PVar txt)
  | Ppat_alias (p, { txt; _ }) -> mk (PAs (pat expected p, txt))
  | Ppat_or (p1, p2) ->
      let p1 = pat expected p1 and p2 = pat expected p2 in
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
          mk (PTuple (List.map2 pat tys l))
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
      | TList t -> mk (PCons (pat t h, pat expected tl))
      | _ -> error loc ":: at type %a" pp_ty expected)
  | Ppat_construct
      ({ txt = Lident name; _ }, Some (_, { ppat_desc = Ppat_var x; _ }))
    when !cases_mode
         && expected = TTerm
         && Some name = !lang.lit_node
         && not !lang.lit_int ->
      mk (PLit x.txt)
  | Ppat_construct ({ txt = Lident name; _ }, arg) -> (
      match find_constr name with
      | None -> error loc "unknown constructor %s" name
      | Some c ->
          (* kind constructors can be matched against terms *)
          let ok =
            ty_equal c.c_res expected || (c.c_res = TKind && expected = TTerm)
          in
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
          (fun (({ txt; _ } : longident loc), p) ->
            let f = Longident.name txt in
            match List.assoc_opt f known with
            | Some t -> (f, pat t p)
            | None -> error loc "unknown field %s" f)
          fields
      in
      mk (PRecord fields)
  | Ppat_constraint (p, ct) ->
      expect loc ~expected (ty_of_core ct);
      pat expected p
  | _ -> error loc "unsupported pattern"

(** Variables bound by a pattern, with their type and whether they are bound to
    a machine-integer field. *)
and binders (p : Syntax.pat) : (string * (Syntax.ty * bool)) list =
  match p.p with
  | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> []
  | PVar x -> [ (x, (p.pty, false)) ]
  | PLit x -> [ (x, (lit_value_ty (), false)) ]
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

(** Variables bound by [PLit] patterns: the pattern binds them to the literal
    term, and the backends rebind them to its value. *)
let rec lit_binders (p : Syntax.pat) : string list =
  match p.p with
  | PLit x -> [ x ]
  | PAny | PVar _ | PInt _ | PBool _ | PUnit | PNone | PNil -> []
  | PAs (q, _) | PSome q -> lit_binders q
  | POr (a, _) | PComm (a, _) -> lit_binders a
  | PTuple l | PConstr (_, l) -> List.concat_map lit_binders l
  | PCons (a, b) -> lit_binders a @ lit_binders b
  | PRecord l -> List.concat_map (fun (_, q) -> lit_binders q) l

(** The variables bound by the sorts of the operands of the spec of the rule
    being checked (see [sort_binds]), and the values they stand for. *)
let sort_vars : (string * Syntax.expr) list ref = ref []

let no_shadow env loc x =
  if List.mem_assoc x env.globals then
    error loc "%s shadows a global function" x;
  if List.mem_assoc x !sort_vars then
    error loc "%s shadows a variable of the sort of an operand" x

let add_binders env p =
  let bs =
    List.fold_left
      (fun acc (x, b) -> if List.mem_assoc x acc then acc else acc @ [ (x, b) ])
      [] (binders p)
  in
  List.iter (fun (x, _) -> no_shadow env p.ploc x) bs;
  { env with vars = List.map (fun (x, (t, _)) -> (x, t)) bs @ env.vars }

(** Types on which [=] and [<>] are allowed: structural equality coincides in
    OCaml and Lean. *)
let rec eq_ty = function
  | TInt | TBool | TUnit -> true
  | (TKind | TSty | TData _) as t -> (decl_of_ty t).d_eq
  | TTuple l -> List.for_all eq_ty l
  | TOption t -> eq_ty t
  | TTerm | TList _ -> false

(* ---------------------------------------------------------------- *)
(* Desugaring of patterns

   A case is compiled to one case per alternative of its or-patterns (so a
   guard that fails on one alternative lets the next alternative be tried).
   Each alternative is then made linear and free of integer literals: a
   repeated variable is renamed and constrained to be equal to its first
   occurrence ([equal] for terms), and a literal becomes a variable
   constrained to be equal to it. These constraints are checked, in order,
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
  | PLit _ -> "lit"
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
  | PAny | PVar _ | PLit _ | PInt _ | PBool _ | PUnit | PNone | PNil -> one p.p
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
    | PLit _ | PAny | PInt _ | PBool _ | PUnit | PNone | PNil -> ()
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
      match t with
      | TTerm -> ECall ("equal", [ a; b ])
      | t when eq_ty t -> EBinop (Arith Eq, a, b)
      | t -> error p.ploc "non-linear pattern at type %a" pp_ty t
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
  let lits = Hashtbl.create 8 in
  let rec go (p : Syntax.pat) : Syntax.pat =
    let mk d = { p with p = d } in
    match p.p with
    | PAny | PBool _ | PUnit | PNone | PNil -> p
    | PVar x -> mk (PVar (bind p x))
    | PLit x ->
        if Hashtbl.mem lits x || Hashtbl.mem keeper x then
          error p.ploc "%s: repeated literal variable" x;
        Hashtbl.add lits x ();
        p
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
             { e = EBinop (Arith And, acc, y); ety = TBool; eloc = y.eloc })
           x xs)

(* ---------------------------------------------------------------- *)
(* Expressions *)

let int_ops = [ ("+", Add); ("-", Sub); ("*", Mul) ]
let cmp_ops = [ ("<", Lt); ("<=", Le); (">", Gt); (">=", Ge) ]

let bit_ops =
  [ ("land", Land); ("lor", Lor); ("lxor", Lxor); ("lsl", Lsl); ("asr", Asr) ]

(** The operators of the grammar. The parser gives prefix operators their OCaml
    names. *)
let infix_ops =
  [
    "+";
    "-";
    "*";
    "land";
    "lor";
    "lxor";
    "lsl";
    "lsr";
    "asr";
    "++";
    "&&";
    "||";
    "==";
  ]

(** Whether [sym] is a word declared as an infix operator, other than those of
    the grammar. *)
let is_infix_word sym =
  Hashtbl.mem infix_words sym && not (List.mem sym infix_ops)

let is_infix sym = List.mem sym infix_ops || is_infix_word sym
let prefix_ops = [ ("-", "~-"); ("~", "lognot"); ("not", "not") ]

(** How an operator is written. *)
let op_name op =
  match List.find_opt (fun (_, o) -> o = op) prefix_ops with
  | Some (p, _) -> "prefix " ^ p
  | None -> op

(** The operators that may have a meaning on the values of literals: those of
    the grammar below, and the infix words. *)
let value_ops =
  [ "+"; "-"; "*"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"; "~-"; "lognot" ]

let is_value_op sym = List.mem sym value_ops || is_infix_word sym

(** The operator [op] on the values of literals: its primitive. *)
let value_op env loc op ~arity =
  let v = lit_value_ty () in
  match find_operator ~arity op with
  | Some { on_value = Some f; _ } ->
      let s = find_global env loc f in
      if s.args <> List.init arity (fun _ -> v) || s.ret <> v then
        error loc "%s: %s is not an operation on %a values" (op_name op) f pp_ty
          v;
      f
  | _ -> error loc "%s is not defined on %a values" (op_name op) pp_ty v

(** The value of a literal where a term is expected is the literal
    ([[@to_term]]). *)
let lift (e : Syntax.expr) =
  match lit_fn "to_term" with
  | Some f when is_lit_value e.ety ->
      { e with e = ECall (f, [ e ]); ety = TTerm }
  | _ -> e

(* ---------------------------------------------------------------- *)
(* The sorts of the nodes built in rules *)

(** The typings of the nodes, from which the sorts of the terms that rules build
    are inferred. *)
let node_typings : (string * typing) list ref = ref []

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
  let op_sorts = List.filteri (fun i _ -> i < n_ops) t.t_sorts in
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
                  error loc "%s: the sort of its result is not determined" name)
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
    match (expected, ety) with
    | Some TTerm, t when is_lit_value t && Option.is_some (lit_fn "to_term") ->
        lift { e = d; ety; eloc = loc }
    | _ ->
        Option.iter (fun expected -> expect loc ~expected ety) expected;
        { e = d; ety; eloc = loc }
  in
  (* an operator on terms, if one of its operands is a term *)
  let term_op op (args : Syntax.expr list) =
    let o =
      match find_operator ~arity:(List.length args) op with
      | Some o -> o
      | None -> error loc "%s is not an operator on terms" (op_name op)
    in
    let f = o.smart in
    let s = find_global env loc f in
    (* the leading arguments, in the global scope *)
    let pre = List.map (expr { env with vars = []; locals = [] }) o.pre in
    let args = List.map lift args in
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
        (op_name op) f;
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
  | Pexp_construct ({ txt = Lident name; _ }, arg) -> (
      match find_constr name with
      | None -> error loc "unknown constructor %s" name
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
          | _ -> mk c.c_res (EConstr (c, args))))
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident op; _ }; _ }, args) -> (
      let args =
        List.map
          (function
            | Nolabel, a -> a
            | _, (a : expression) ->
                error a.pexp_loc "labelled arguments are not supported")
          args
      in
      match (op, args) with
      | ("+" | "-" | "*"), [ a; b ] -> (
          let a = expr env a in
          let b = expr env b in
          match a.ety with
          | _ when is_term a || is_term b -> term_op op [ a; b ]
          | t when is_lit_value t ->
              (* arithmetic on the values of literals *)
              expect b.eloc ~expected:t b.ety;
              let f = value_op env loc op ~arity:2 in
              mk t (ECall (f, [ a; b ]))
          | _ ->
              expect a.eloc ~expected:TInt a.ety;
              expect b.eloc ~expected:TInt b.ety;
              mk TInt (EBinop (Arith (List.assoc op int_ops), a, b)))
      | ("<" | "<=" | ">" | ">="), [ a; b ] ->
          let a = expr env ~expected:TInt a and b = expr env ~expected:TInt b in
          mk TBool (EBinop (Arith (List.assoc op cmp_ops), a, b))
      | ("=" | "<>"), [ a; b ] ->
          let a = expr env a in
          let b = expr env ~expected:a.ety b in
          if not (eq_ty a.ety) then
            error loc "structural equality is not allowed at type %a" pp_ty
              a.ety;
          mk TBool (EBinop (Arith (if op = "=" then Eq else Ne), a, b))
      | ("&&" | "||"), [ a; b ] ->
          let a = expr env a in
          let b = expr env b in
          if is_term a || is_term b then term_op op [ a; b ]
          else (
            expect a.eloc ~expected:TBool a.ety;
            expect b.eloc ~expected:TBool b.ety;
            mk TBool (EBinop (Arith (if op = "&&" then And else Or), a, b)))
      | ("==" | "++"), [ a; b ] -> term_op op [ expr env a; expr env b ]
      | op, [ a; b ] when is_infix_word op -> (
          let a = expr env a in
          let b = expr env b in
          match a.ety with
          | _ when is_term a || is_term b -> term_op op [ a; b ]
          | t when is_lit_value t ->
              expect b.eloc ~expected:t b.ety;
              let f = value_op env loc op ~arity:2 in
              mk t (ECall (f, [ a; b ]))
          | t -> error loc "%s is not defined on %a" op pp_ty t)
      | ("land" | "lor" | "lxor" | "lsl" | "lsr" | "asr"), [ a; b ] -> (
          let a = expr env a in
          let b = expr env b in
          match (a.ety, op) with
          | _ when is_term a || is_term b -> term_op op [ a; b ]
          | t, _ when is_lit_value t ->
              (* bitwise operations on the values of literals *)
              expect b.eloc ~expected:t b.ety;
              let f = value_op env loc op ~arity:2 in
              mk t (ECall (f, [ a; b ]))
          | _ ->
              expect a.eloc ~expected:TInt a.ety;
              expect b.eloc ~expected:TInt b.ety;
              if op = "lsr" then error loc "lsr is not defined on integers";
              mk TInt (EBinop (Bit (List.assoc op bit_ops), a, b)))
      | "not", [ a ] ->
          let a = expr env a in
          if is_term a then term_op op [ a ]
          else (
            expect a.eloc ~expected:TBool a.ety;
            mk TBool (EUnop (Not, a)))
      | ("~-" | "-"), [ a ] -> (
          let a = expr env a in
          match a.ety with
          | TTerm -> term_op "~-" [ a ]
          | t when is_lit_value t ->
              let f = value_op env loc "~-" ~arity:1 in
              mk t (ECall (f, [ a ]))
          | _ ->
              expect a.eloc ~expected:TInt a.ety;
              mk TInt (EUnop (Neg, a)))
      | "lognot", [ a ] -> (
          let a = expr env a in
          match a.ety with
          | TTerm -> term_op op [ a ]
          | t when is_lit_value t ->
              let f = value_op env loc op ~arity:1 in
              mk t (ECall (f, [ a ]))
          | _ ->
              expect a.eloc ~expected:TInt a.ety;
              mk TInt (EUnop (Lognot, a)))
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
              let s = find_global env loc f in
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
          let params = List.map (param_of loc) params in
          List.iter (no_shadow env loc) (name :: List.map fst params);
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
          let p = pat rhs.ety vb.pvb_pat in
          let body = expr (add_binders env p) ?expected body in
          mk body.ety (ELet (p, rhs, body)))
  | Pexp_match (scrut, cases) ->
      let scruts =
        match scrut.pexp_desc with
        | Pexp_tuple l -> List.map (expr env) l
        | _ -> [ expr env scrut ]
      in
      let cases = List.concat_map (case env ?expected scruts) cases in
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
  | Pexp_field (e, { txt = Lident f; _ }) -> (
      match
        List.find_opt (fun d -> List.mem_assoc f d.d_fields) !lang.decls
      with
      | None -> error loc "unknown field %s" f
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
  | Pexp_extension ({ txt = "kanon.sort"; _ }, _) ->
      error loc "only the operands of a spec are annotated with their sort"
  | Pexp_extension
      ( { txt = "kanon.at"; _ },
        PStr
          [
            { pstr_desc = Pstr_eval (k, _); _ };
            { pstr_desc = Pstr_eval (spec, _); _ };
          ] ) -> (
      (* the literal [k], at the sort of the node [spec] (see [law_cases]) *)
      let k = expr env ~expected:TKind k in
      match (expr env ~expected:TTerm spec).e with
      | ENode (_, sort) -> mk TTerm (ENode (k, sort))
      | _ -> error loc "the spec of this rule is not a node over its parameters"
      )
  | _ -> error loc "unsupported expression"

and case env ?expected scruts (c : Ppxlib.case) : Syntax.case list =
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
  let pat = pat sty lhs in
  let env = add_binders env pat in
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

and param_of loc (p : function_param) =
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
  | _ -> error loc "parameters must be of the form (x : ty)"

and ret_of = function
  | Pconstraint ct -> ty_of_core ct
  | Pcoerce _ -> failwith "unsupported coercion"

(* ---------------------------------------------------------------- *)
(* Matching the spec of a rule *)

(** Whether [x] occurs in [e], other than as the argument of a function that
    only reads its type (see [ty_only]). *)
let mentions x (e : expression) =
  let found = ref false in
  object
    inherit Ast_traverse.iter as super

    method! expression e =
      match e.pexp_desc with
      | Pexp_apply
          ( { pexp_desc = Pexp_ident { txt = Lident f; _ }; _ },
            [ (_, { pexp_desc = Pexp_ident _; _ }) ] )
        when List.mem f !lang.ty_only ->
          ()
      | Pexp_ident { txt = Lident y; _ } when y = x -> found := true
      | _ -> super#expression e
  end
    #expression
    e;
  !found

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
              if
                mentions x c.pc_rhs
                || Option.fold ~none:false ~some:(mentions x) c.pc_guard
              then
                error lhs.ppat_loc
                  "the operands match in either order: name them rather than %s"
                  x)
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
      | { pc_lhs = { ppat_desc = Ppat_any; _ }; pc_guard = None; _ } :: _ -> e
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

let string_attr (a : attribute) =
  match a.attr_payload with
  | PStr
      [
        {
          pstr_desc =
            Pstr_eval
              ({ pexp_desc = Pexp_constant (Pconst_string (s, _, _)); _ }, _);
          _;
        };
      ] ->
      s
  | _ -> error a.attr_loc "expected [@%s \"...\"]" a.attr_name.txt

(** The strings of an attribute [[@a "s1" ... "sn"]]. *)
let strings_attr (a : attribute) =
  let str (e : expression) =
    match e.pexp_desc with
    | Pexp_constant (Pconst_string (s, _, _)) -> s
    | _ -> error a.attr_loc "expected [@%s \"...\" ...]" a.attr_name.txt
  in
  match a.attr_payload with
  | PStr [] -> []
  | PStr [ { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_tuple l; _ }, _); _ } ]
    ->
      List.map str l
  | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> [ str e ]
  | _ -> error a.attr_loc "expected [@%s \"...\" ...]" a.attr_name.txt

let check_attrs allowed (attrs : attributes) =
  List.iter
    (fun (a : attribute) ->
      if not (List.mem a.attr_name.txt allowed) then
        error a.attr_loc "unknown attribute [@%s]" a.attr_name.txt)
    attrs

let find_attr name (attrs : attributes) =
  List.find_opt (fun (a : attribute) -> a.attr_name.txt = name) attrs

(** [[@literal t]] on the constructor of integer literals: the type of their
    values, or [None] for [[@literal int]], where they are integers. *)
let int_literal (attrs : attributes) =
  match find_attr "literal" attrs with
  | Some a -> (
      match strings_attr a with
      | [ "int" ] -> None
      | [ t ] -> (
          match find_decl t with
          | Some _ -> Some t
          | None -> error a.attr_loc "[@literal]: unknown type %s" t)
      | _ -> error a.attr_loc "expected [@literal \"t\"] or [@literal \"int\"]")
  | None -> None

(** The attributes that declare the laws of an operator. *)
let law_attrs = [ "fold"; "unit"; "zero"; "idem"; "invol"; "distrib_ite" ]

let law_of_attr (a : attribute) =
  match a.attr_name.txt with
  | "fold" -> Some (Fold (string_attr a))
  | "unit" -> Some (Unit (string_attr a))
  | "zero" -> Some (Zero (string_attr a))
  | "idem" -> Some Idem
  | "invol" -> Some Invol
  | "distrib_ite" -> Some Distrib_ite
  | _ -> None

let law_name = function
  | Fold _ -> "fold"
  | Unit _ -> "unit"
  | Zero _ -> "zero"
  | Idem -> "idem"
  | Invol -> "invol"
  | Distrib_ite -> "distrib_ite"

(** The literal [c] of a [[@unit c]] or [[@zero c]] law, which the language
    declares with [constant]. *)
let law_literal loc c =
  match c with
  | ("0" | "1") when Option.is_some !lang.lit_node && not !lang.lit_int ->
      if not (List.mem_assoc c !lang.constants) then
        error loc "the constant %s is not declared" c
  | ("true" | "false") when Option.is_some !lang.lit_bool ->
      if not (List.mem_assoc c !lang.constants) then
        error loc "the constant %s is not declared" c
  | _ -> error loc "expected the literal 0, 1, true or false"

let check_law (name, law, loc) =
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
      law_literal loc c
  | Idem -> expect 2
  | Invol | Distrib_ite -> expect 1

(** Reads the declaration of a language, which the rules are then checked
    against. *)
let language (str : structure) =
  let tds, ops =
    List.partition_map
      (fun (si : structure_item) ->
        match si.pstr_desc with
        | Pstr_type (_, [ td ]) -> Left td
        | Pstr_eval (e, [ a ])
          when List.mem a.attr_name.txt [ "infix"; "prefix"; "constant" ] ->
            Right (e, a)
        | Pstr_attribute a -> (
            match (a.attr_name.txt, strings_attr a) with
            | "lean_root", [ r ] ->
                lang := { !lang with lean_root = r };
                Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a)
            | "lean_param", [ x; t ] ->
                lang :=
                  { !lang with lean_params = !lang.lean_params @ [ (x, t) ] };
                Right (Ast_builder.Default.eunit ~loc:a.attr_loc, a)
            | _ -> error a.attr_loc "unknown attribute [@@@%s]" a.attr_name.txt)
        | _ -> error si.pstr_loc "unsupported item in a language declaration")
      str
  in
  let ops, constants =
    List.partition
      (fun (_, (a : attribute)) ->
        List.mem a.attr_name.txt [ "infix"; "prefix" ])
      ops
  in
  (* the nodes of the modules, placed where the types name them *)
  let nodes, tds =
    List.partition
      (fun (td : type_declaration) -> has_attr "node" td.ptype_attributes)
      tds
  in
  let nodes =
    List.fold_left
      (fun nodes (td : type_declaration) ->
        match td.ptype_kind with
        | Ptype_variant [ cd ] ->
            if List.mem_assoc cd.pcd_name.txt nodes then
              error cd.pcd_loc "node %s is declared twice" cd.pcd_name.txt;
            nodes @ [ (cd.pcd_name.txt, cd) ]
        | _ -> error td.ptype_loc "expected a node")
      [] nodes
  in
  let placed = ref [] in
  (* in [kind], rather than in a type of operators, a node has its operands as
     arguments, after its own *)
  let in_kind (n : constructor_declaration) =
    match (find_attr "sorts" n.pcd_attributes, n.pcd_args) with
    | ( Some { attr_payload = PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]; _ },
        Pcstr_tuple args ) ->
        let operands =
          match e.pexp_desc with Pexp_tuple l -> List.length l - 1 | _ -> 0
        in
        let t =
          Ast_builder.Default.ptyp_constr ~loc:n.pcd_loc
            { txt = Lident "t"; loc = n.pcd_loc }
            []
        in
        {
          n with
          pcd_args = Pcstr_tuple (args @ List.init operands (fun _ -> t));
        }
    | _ -> n
  in
  let place ty (cd : constructor_declaration) =
    match List.assoc_opt cd.pcd_name.txt nodes with
    | None -> cd
    | Some n ->
        let name = cd.pcd_name.txt in
        if cd.pcd_args <> Pcstr_tuple [] || cd.pcd_attributes <> [] then
          error cd.pcd_loc "%s is declared by a node, and placed by its name"
            name;
        if List.mem name !placed then
          error cd.pcd_loc "node %s is placed twice" name;
        placed := name :: !placed;
        if ty = "kind" then in_kind n else n
  in
  let tds =
    List.map
      (fun (td : type_declaration) ->
        match td.ptype_kind with
        | Ptype_variant cds ->
            {
              td with
              ptype_kind =
                Ptype_variant (List.map (place td.ptype_name.txt) cds);
            }
        | _ -> td)
      tds
  in
  (* the nodes that the types do not name, placed by what they are, in the order
     of the modules: an operator on [k] operands in the type of the operators of
     the [[@operators]] kind constructor with [k] terms, a sort that the typings
     use in [ty], and the others in [kind] *)
  let operator_types =
    List.concat_map
      (fun (td : type_declaration) ->
        match (td.ptype_name.txt, td.ptype_kind) with
        | "kind", Ptype_variant cds ->
            List.filter_map
              (fun (cd : constructor_declaration) ->
                match cd.pcd_args with
                | Pcstr_tuple
                    ({ ptyp_desc = Ptyp_constr ({ txt = Lident op; _ }, []); _ }
                    :: operands)
                  when has_attr "operators" cd.pcd_attributes
                       && List.for_all
                            (fun (t : core_type) ->
                              match t.ptyp_desc with
                              | Ptyp_constr ({ txt = Lident "t"; _ }, []) ->
                                  true
                              | _ -> false)
                            operands ->
                    Some (List.length operands, op)
                | _ -> None)
              cds
        | _ -> [])
      tds
  in
  let sorts_used =
    let used = ref [] in
    let collect =
      object
        inherit Ast_traverse.iter as super

        method! expression e =
          (match e.pexp_desc with
          | Pexp_construct ({ txt = Lident c; _ }, _) -> used := c :: !used
          | _ -> ());
          super#expression e
      end
    in
    List.iter
      (fun (_, (cd : constructor_declaration)) ->
        List.iter
          (fun (a : attribute) ->
            if List.mem a.attr_name.txt [ "sorts"; "when" ] then
              collect#payload a.attr_payload)
          cd.pcd_attributes)
      nodes;
    !used
  in
  let target name (cd : constructor_declaration) =
    let operands =
      match find_attr "sorts" cd.pcd_attributes with
      | Some { attr_payload = PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]; _ }
        -> (
          match e.pexp_desc with Pexp_tuple l -> List.length l - 1 | _ -> 0)
      | _ -> 0
    in
    match List.assoc_opt operands operator_types with
    | Some op when operands > 0 -> op
    | _ -> if List.mem name sorts_used then "ty" else "kind"
  in
  let auto =
    List.filter_map
      (fun (name, cd) ->
        if List.mem name !placed then None
        else (
          placed := name :: !placed;
          Some (target name cd, cd)))
      nodes
  in
  let tds =
    List.map
      (fun (td : type_declaration) ->
        let ty = td.ptype_name.txt in
        match
          List.filter_map (fun (t, cd) -> if t = ty then Some cd else None) auto
        with
        | [] -> td
        | added ->
            let added = if ty = "kind" then List.map in_kind added else added in
            let cds =
              match td.ptype_kind with
              | Ptype_variant cds -> cds
              | Ptype_abstract -> []
              | _ -> error td.ptype_loc "%s: expected a variant type" ty
            in
            { td with ptype_kind = Ptype_variant (cds @ added) })
      tds
  in
  List.iter
    (fun (t, (cd : constructor_declaration)) ->
      if
        not
          (List.exists
             (fun (td : type_declaration) -> td.ptype_name.txt = t)
             tds)
      then
        error cd.pcd_loc "node %s: the language has no type %s" cd.pcd_name.txt
          t)
    auto;
  (* the types first, so that they can refer to each other *)
  let decls =
    List.map
      (fun (td : type_declaration) ->
        let name = td.ptype_name.txt and loc = td.ptype_loc in
        check_attrs [ "ocaml"; "lean"; "noeq"; "equal" ] td.ptype_attributes;
        (match ty_of_name name with
        | Some (TInt | TBool | TUnit | TTerm) ->
            error loc "%s is a built-in type" name
        | _ -> ());
        if Option.is_some (find_decl name) then
          error loc "type %s is declared twice" name;
        let d =
          {
            d_name = name;
            d_ocaml =
              Option.fold ~none:name ~some:string_attr
                (find_attr "ocaml" td.ptype_attributes);
            d_lean =
              Option.map string_attr (find_attr "lean" td.ptype_attributes);
            d_eq = not (has_attr "noeq" td.ptype_attributes);
            d_equal =
              Option.map string_attr (find_attr "equal" td.ptype_attributes);
            d_fields = [];
          }
        in
        lang := { !lang with decls = !lang.decls @ [ d ] };
        d)
      tds
  in
  let decls =
    List.map2
      (fun d (td : type_declaration) ->
        match td.ptype_kind with
        | Ptype_record fields ->
            {
              d with
              d_fields =
                List.map
                  (fun (l : label_declaration) ->
                    (l.pld_name.txt, ty_of_core l.pld_type))
                  fields;
            }
        | _ -> d)
      decls tds
  in
  lang := { !lang with decls };
  (* a field determines its record type *)
  ignore
    (List.fold_left
       (fun seen (td : type_declaration) ->
         match td.ptype_kind with
         | Ptype_record ls ->
             List.fold_left
               (fun seen (l : label_declaration) ->
                 if List.mem l.pld_name.txt seen then
                   error l.pld_loc "field %s is declared twice" l.pld_name.txt;
                 l.pld_name.txt :: seen)
               seen ls
         | _ -> seen)
       [] tds);
  List.iter2
    (fun d (td : type_declaration) ->
      (match td.ptype_kind with
      | Ptype_variant cds ->
          let res = Option.get (ty_of_name d.d_name) in
          List.iter
            (fun (cd : constructor_declaration) ->
              let name = cd.pcd_name.txt and loc = cd.pcd_loc in
              let attrs = cd.pcd_attributes in
              check_attrs
                ([
                   "comm";
                   "literal";
                   "to_term";
                   "of_term";
                   "raw";
                   "ite";
                   "operators";
                   "params";
                   "sorts";
                   "when";
                   "get";
                 ]
                @ law_attrs)
                attrs;
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
              if Option.is_some (payload "sorts") then
                lang :=
                  {
                    !lang with
                    raw_typing =
                      !lang.raw_typing
                      @ [
                          ( name,
                            {
                              rt_params = items (payload "params");
                              rt_sorts = items (payload "sorts");
                              rt_when = payload "when";
                              rt_loc = loc;
                            } );
                        ];
                  }
              else if
                Option.is_some (payload "params")
                || Option.is_some (payload "when")
              then error loc "%s: argument names and conditions need sorts" name;
              if Option.is_some (find_constr name) then
                error loc "constructor %s is declared twice" name;
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
              let c = { c_name = name; c_res = res; c_args = args } in
              let l = !lang in
              let l = { l with constrs = l.constrs @ [ c ] } in
              let l =
                if has_attr "comm" attrs then
                  { l with commutative = l.commutative @ [ name ] }
                else l
              in
              let l =
                {
                  l with
                  laws =
                    l.laws
                    @ List.filter_map
                        (fun (a : attribute) ->
                          Option.map
                            (fun law -> (name, law, a.attr_loc))
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
                    | _ ->
                        error a.attr_loc
                          "[@get \"f\"] applies to sorts with one argument")
                | None -> l
              in
              let l =
                if has_attr "operators" attrs then (
                  if res <> TKind then
                    error loc "[@operators] applies to kind constructors";
                  match args with
                  | Arg (TData _) :: _ ->
                      { l with node_kinds = l.node_kinds @ [ name ] }
                  | _ -> error loc "[@operators]: expected an operator argument")
                else l
              in
              let fns =
                List.filter_map
                  (fun (a : attribute) ->
                    match a.attr_name.txt with
                    | ("to_term" | "of_term" | "raw") as n -> (
                        match (n, strings_attr a) with
                        | ("to_term" | "of_term"), [ f ] -> Some (n, f)
                        | "raw", [ f; p ] -> Some ("raw:" ^ f, p)
                        | _ -> error a.attr_loc "unexpected [@%s]" n)
                    | _ -> None)
                  attrs
              in
              let l =
                if has_attr "literal" attrs then
                  match (res, args) with
                  | TKind, [ Arg TBool ] when l.lit_bool = None ->
                      {
                        l with
                        lit_bool = Some name;
                        lit_fns =
                          l.lit_fns
                          @ List.map
                              (function
                                | "to_term", f -> ("bool_to_term", f)
                                | _, _ ->
                                    error loc
                                      "boolean literals only have [@to_term]")
                              fns;
                      }
                  | TKind, [ Arg TInt ] when l.lit_node = None -> (
                      match int_literal attrs with
                      | None ->
                          if fns <> [] then
                            error loc "integer literals have no functions";
                          { l with lit_node = Some name; lit_int = true }
                      | Some v ->
                          {
                            l with
                            lit_node = Some name;
                            lit_value = v;
                            lit_fns = l.lit_fns @ fns;
                          })
                  | _ ->
                      error loc
                        "[@literal]: expected the only kind constructor of \
                         bool or of int literals"
                else if fns <> [] then
                  error loc "only literals have [@to_term], [@of_term], [@raw]"
                else l
              in
              let l =
                if has_attr "ite" attrs then
                  if l.ite <> None then error loc "[@ite] is declared twice"
                  else { l with ite = Some name }
                else l
              in
              lang := l)
            cds
      | Ptype_abstract | Ptype_record _ -> ()
      | Ptype_open -> error td.ptype_loc "unsupported type");
      (* the typings of the constructors of a type of operators are all given,
         or none *)
      match td.ptype_kind with
      | Ptype_variant cds when d.d_name <> "kind" ->
          let typed (cd : constructor_declaration) =
            List.mem_assoc cd.pcd_name.txt !lang.raw_typing
          in
          if List.exists typed cds then
            List.iter
              (fun (cd : constructor_declaration) ->
                if not (typed cd) then
                  error cd.pcd_loc
                    "%s has no typing, unlike the other constructors of %s"
                    cd.pcd_name.txt d.d_name)
              cds
      | _ -> ())
    decls tds;
  (* then the operators on terms *)
  List.iter
    (fun ((e : expression), (a : attribute)) ->
      let loc = e.pexp_loc in
      let sym = string_attr a in
      let sym, arity =
        if a.attr_name.txt = "infix" then (
          if not (is_infix sym) then
            error a.attr_loc "%s is not an infix operator, nor a word" sym;
          (sym, 2))
        else
          match List.assoc_opt sym prefix_ops with
          | Some s -> (s, 1)
          | None -> error a.attr_loc "%s is not a prefix operator" sym
      in
      if Option.is_some (find_operator ~arity sym) then
        error loc "operator %s is declared twice" (op_name sym);
      let ident (e : expression) =
        match e.pexp_desc with
        | Pexp_ident { txt = Lident f; _ } -> f
        | _ -> error e.pexp_loc "expected a function name"
      in
      let node, smart, on_value =
        match e.pexp_desc with
        | Pexp_tuple [ n; s ] -> (n, s, None)
        | Pexp_tuple [ n; s; b ] -> (n, s, Some (ident b))
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
                | _ ->
                    error node.pexp_loc "%s is not a node of arity %d" n arity);
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
            | None -> error node.pexp_loc "%s is not a node of arity %d" n arity
            )
        | _ -> error node.pexp_loc "expected a node constructor"
      in
      if Option.is_some on_value && not (is_value_op sym) then
        error loc "%s is not defined on literal values" (op_name sym);
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
            @ [ { sym; arity; node; params; smart; pre; on_value } ];
        })
    ops;
  (* the constants of the laws *)
  List.iter
    (fun ((e : expression), (a : attribute)) ->
      match a.attr_name.txt with
      | "constant" -> (
          let c = string_attr a in
          if List.mem_assoc c !lang.constants then
            error e.pexp_loc "constant %s is declared twice" c;
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
              lang :=
                { !lang with constants = !lang.constants @ [ (c, (v, body)) ] }
          | _ -> error e.pexp_loc "expected constant \"c\" (v) = e")
      | _ -> ())
    constants;
  let loc = match str with si :: _ -> si.pstr_loc | [] -> Location.none in
  List.iter
    (fun t ->
      if Option.is_none (find_decl t) then error loc "type %s is not declared" t)
    [ "kind"; "ty" ];
  List.iter
    (fun c ->
      match Option.bind (find_constr c) node_of_op with
      | Some (_, [ _; _ ]) -> ()
      | _ -> error loc "[@comm]: %s is not a binary operator" c)
    !lang.commutative;
  List.iter check_law !lang.laws

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

(** Replaces the operators in patterns ([a + b], [#x]) with the nodes that the
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
      | Ppat_construct ({ txt = Lident "#"; loc }, arg) -> (
          match !lang.lit_node with
          | Some c ->
              {
                p with
                ppat_desc = Ppat_construct ({ txt = Lident c; loc }, arg);
              }
          | None -> error p.ppat_loc "the language has no integer literals")
      | Ppat_construct ({ txt = Lident sym; loc }, Some (vars, arg))
        when is_infix sym || List.mem sym (List.map snd prefix_ops) -> (
          let arity, operands =
            match arg.ppat_desc with
            | Ppat_tuple l when is_infix sym -> (2, l)
            | _ -> (1, [ arg ])
          in
          match find_operator ~arity sym with
          | None ->
              error p.ppat_loc "%s is not an operator on terms" (op_name sym)
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
let spec_params loc rname (spec : expression) =
  let fail () =
    error loc
      "%s: a rule declares its parameters unless its spec is a node over \
       variables"
      rname
  in
  match spec.pexp_desc with
  | Pexp_construct ({ txt = Lident n; _ }, arg) ->
      let c =
        match find_constr n with
        | Some c -> c
        | None -> error loc "unknown constructor %s" n
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
          | _ -> fail ())
        args tys
  | _ -> fail ()

type raw_fn = {
  rname : string;
  rparams : (string * Syntax.ty) list;
  rret : Syntax.ty;
  rspec : expression option;
  rcases : bool;
  rty_only : bool;  (** [[@ty_only]] *)
  rbody : expression;
  rsorts : (string * expression) list;
      (** the sorts of the operands of the spec, [(v : s)] *)
  runtyped : bool;
      (** [[@untyped]]: the rule also simplifies ill-typed specs, so the sorts
          of their operands are not asserted *)
  rloc : Location.t;
}

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
  let rname =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt; _ } -> txt
    | _ -> error loc "expected a function name"
  in
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
    error loc "%s: an [@untyped] rule does not annotate the sorts of its spec"
      rname;
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
      let rparams = List.map (param_of loc) params in
      (match rspec with
      | Some spec when rcases -> (
          match spec_params loc rname spec with
          | ps when ps = rparams ->
              error loc "%s: its parameters are those of its spec, implicitly"
                rname
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
      }
  | Pexp_function _ -> error loc "%s: the return type must be annotated" rname
  | _ -> (
      match vb.pvb_constraint with
      | Some (Pvc_constraint { typ; locally_abstract_univars = [] }) ->
          let rparams =
            match rspec with
            | Some spec when rcases -> spec_params loc rname spec
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
          }
      | _ -> error loc "%s: constants must be annotated with their type" rname)

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
  | Distrib_ite -> 5

(** The name of the rule of a case, if any (see [case]). *)
let case_rule (c : Ppxlib.case) =
  match (rule_name_of_attrs c.pc_lhs.ppat_attributes, c.pc_lhs.ppat_desc) with
  | Some r, _ -> Some r
  | None, Ppat_tuple l ->
      rule_name_of_attrs (List.hd (List.rev l)).ppat_attributes
  | None, _ -> None

(** Adds the rules derived from the laws of each operator (see [Syntax.law]) to
    its rule function, before its own rules, in the order of [law_order]. In the
    rule function [f (p1, ..., v1, v2)] of a binary operator [op]:
    - [[@fold g]]: [lits: #l, #r -> g pk ... pn l r], where [g] takes the last
      parameters [pk ... pn] of the node, then its literals: the values of
      integer literals (of type [t], see [lit_value]) are bound to [l] and [r]
      ([t] for a unary operator), and the others to the first letter of their
      type ([f1], [f2] or [f] for floats); a boolean result is lifted with the
      [[@to_term]] of boolean literals, a result of another type with its
      literal, at the sort of the spec;
    - [[@unit c]]: [c: x, c -> x] if [op] is commutative (it then also matches
      [c, x]), and otherwise [c: _, c -> v1];
    - [[@zero c]]: [c: _, c -> c], where [c] stands for the term that the
      language declares for it, at the type of [v1] ([constant "c" (v) = e]);
    - [[@idem]]: [same: v, v -> v].

    In that of a unary operator [Op], over [v]:
    - [[@invol]]: [op: Op x -> x], named after [Op];
    - [[@distrib_ite]]: [ite: Ite (b, l, r) -> ite b (f (..., l)) (f (..., r))],
      where [Ite] is the node marked [[@ite]], and [ite] its rule function.

    The literals [0], [1], [true] and [false] name their rules [zero], [one],
    [true_] and [false_]. *)
let law_cases globals raws =
  let open Ast_builder.Default in
  let derive raws n =
    let laws =
      List.filter_map
        (fun (m, law, loc) -> if m = n then Some (law, loc) else None)
        !lang.laws
      |> List.stable_sort (fun (a, _) (b, _) ->
          compare (law_order a) (law_order b))
    in
    let r = rule_of_node (snd (List.hd laws)) raws n in
    let op = Option.get (find_constr n) in
    let nparams = List.length op.c_args in
    let params = List.map fst r.rparams in
    let node_params = List.filteri (fun i _ -> i < nparams) params in
    let operands = List.filteri (fun i _ -> i >= nparams) params in
    let lit_name = function "0" -> "zero" | "1" -> "one" | c -> c ^ "_" in
    let case (law, loc) =
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
      (* the term of the constant [c], at the type of the first operand *)
      let lit_term c =
        let v, e = List.assoc c !lang.constants in
        object
          inherit Ast_traverse.map as super

          method! expression e =
            match e.pexp_desc with
            | Pexp_ident { txt = Lident x; _ } when x = v -> v1
            | _ -> super#expression e
        end
          #expression
          e
      in
      (* the kind constructor of the literals of type [t] *)
      let lit_constr t =
        match t with
        | t when is_lit_value t -> Option.get !lang.lit_node
        | TBool when Option.is_some !lang.lit_bool -> Option.get !lang.lit_bool
        | TData _ -> (
            match
              List.find_opt
                (fun c -> c.c_res = TKind && c.c_args = [ Arg t ])
                !lang.constrs
            with
            | Some c -> c.c_name
            | None -> error loc "[@fold]: no literals of type %a" pp_ty t)
        | _ -> error loc "[@fold]: no literals of type %a" pp_ty t
      in
      let rule, pats, body =
        match law with
        | Fold g ->
            let s =
              match List.assoc_opt g globals with
              | Some s -> s
              | None -> error loc "[@fold]: unknown function %s" g
            in
            let arity = List.length operands in
            let k = List.length s.args - arity in
            if k < 0 || k > nparams then
              error loc "[@fold]: %s does not take the literals of %s" g n;
            let tys = List.filteri (fun i _ -> i >= k) s.args in
            let xs =
              match tys with
              | t :: _ when is_lit_value t && arity = 1 -> [ !lang.lit_value ]
              | t :: _ when is_lit_value t && arity = 2 -> [ "l"; "r" ]
              | t :: _ ->
                  let x = String.sub (Fmt.str "%a" pp_ty t) 0 1 in
                  if arity = 1 then [ x ]
                  else List.init arity (fun i -> x ^ string_of_int (i + 1))
              | [] -> []
            in
            let args = List.filteri (fun i _ -> i >= nparams - k) node_params in
            let e = app g (List.map var (args @ xs)) in
            let body =
              match s.ret with
              | t when is_lit_value t -> e
              | TBool -> (
                  match lit_fn "bool_to_term" with
                  | Some f -> app f [ e ]
                  | None ->
                      error loc
                        "[@fold]: the boolean literals have no [@to_term]")
              | TData _ as t ->
                  (* the literal, at the sort of the spec *)
                  pexp_extension ~loc
                    ( { txt = "kanon.at"; loc },
                      PStr
                        [
                          pstr_eval ~loc
                            (pexp_construct ~loc
                               (Located.lident ~loc (lit_constr t))
                               (Some e))
                            [];
                          pstr_eval ~loc (Option.get r.rspec) [];
                        ] )
              | _ -> e
            in
            ( (if arity = 1 then "lit" else "lits"),
              List.map2
                (fun t x ->
                  ppat_construct ~loc
                    (Located.lident ~loc (lit_constr t))
                    (Some (pvar ~loc x)))
                tys xs,
              body )
        | Unit c when is_commutative n ->
            (lit_name c, [ pvar ~loc "x"; lit_pat c ], var "x")
        | Unit c -> (lit_name c, [ ppat_any ~loc; lit_pat c ], v1)
        | Zero c -> (lit_name c, [ ppat_any ~loc; lit_pat c ], lit_term c)
        | Idem -> ("same", [ pvar ~loc "v"; pvar ~loc "v" ], var "v")
        | Invol ->
            (String.lowercase_ascii n, [ node_pat [ pvar ~loc "x" ] ], var "x")
        | Distrib_ite ->
            let ite_node =
              match !lang.ite with
              | Some n -> n
              | None -> error loc "[@distrib_ite]: no node is declared [@ite]"
            in
            let ite = (rule_of_node loc raws ite_node).rname in
            let branch x = app r.rname (List.map var (node_params @ [ x ])) in
            ( "ite",
              [
                ppat_construct ~loc
                  (Located.lident ~loc ite_node)
                  (Some
                     (ppat_tuple ~loc
                        [ pvar ~loc "b"; pvar ~loc "l"; pvar ~loc "r" ]));
              ],
              app ite [ var "b"; branch "l"; branch "r" ] )
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
        { p with ppat_attributes = [ name ] }
      in
      (rule, fun scrut -> case ~lhs:(lhs scrut) ~guard:None ~rhs:body)
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
                  error c.pc_lhs.ppat_loc
                    "rule %s is derived from the laws of %s" x n
              | _ -> ())
            cases;
          let derived = List.map (fun (_, c) -> c scrut) derived in
          { e with pexp_desc = Pexp_match (scrut, derived @ cases) }
      | _ -> error r.rloc "%s: the laws of %s need a match" r.rname n
    in
    List.map
      (fun r' ->
        if r'.rname = r.rname then { r with rbody = body r.rbody } else r')
      raws
  in
  List.fold_left derive raws
    (List.sort_uniq compare (List.map (fun (n, _, _) -> n) !lang.laws))

(* ---------------------------------------------------------------- *)
(* The typing of operators *)

(** The names of the operands and of the result in the Lean typing predicates,
    which the arguments and variables of typings may not use. *)
let typing_names = [ "a"; "b"; "c"; "t" ]

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
    error loc "%s has %d arguments" c.c_name nparams;
  let penv =
    List.concat
      (List.map2
         (fun x a -> if x = "_" then [] else [ (x, arg_ty a) ])
         params args)
  in
  List.iter
    (fun (x, _) ->
      if List.mem x typing_names then
        error loc "%s: reserved name %s" c.c_name x)
    penv;
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
                      if List.mem x typing_names then
                        error e.pexp_loc "%s: reserved name %s" c.c_name x;
                      var e.pexp_loc x t
                  | _, TSty -> sort e
                  | _, t -> expr (env ()) ~expected:t e)
                tc.c_args args
            in
            { e = EConstr (tc, args); ety = TSty; eloc = e.pexp_loc }
        | _ -> error e.pexp_loc "%s is not a constructor of ty" n)
    | _ -> error e.pexp_loc "expected a sort"
  in
  let sorts = List.map sort rt.rt_sorts in
  let cond = Option.map (expr (env ()) ~expected:TBool) rt.rt_when in
  {
    t_constr = c;
    t_params = params;
    t_vars = !vars;
    t_sorts = sorts;
    t_when = cond;
  }

(** The typings of the nodes: of the operands that are terms and of the result,
    or of the result alone. *)
let typings env0 =
  List.map
    (fun (n, (rt : raw_typing)) ->
      let c = Option.get (find_constr n) in
      let sorts = List.length rt.rt_sorts in
      let nparams =
        match node_of_op c with
        | Some (_, operands) ->
            if
              sorts <> 1
              && (sorts <> List.length operands + 1
                 || not (List.for_all (( = ) TTerm) operands))
            then
              error rt.rt_loc
                "%s: expected the sorts of %d operands and the result, or of \
                 the result"
                n (List.length operands);
            List.length c.c_args
        | None when c.c_res = TKind -> List.length c.c_args - (sorts - 1)
        | None -> error rt.rt_loc "%s: only nodes have a typing" n
      in
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
  let splice loc f before (ext : Ppxlib.case list) (cs : Ppxlib.case list) =
    ignore
      (List.fold_left
         (fun names c ->
           match case_rule c with
           | Some r when List.mem r names ->
               error c.pc_lhs.ppat_loc "extend %s: %s already has a rule %s" f f
                 r
           | Some r -> r :: names
           | None -> names)
         (List.filter_map case_rule cs)
         ext);
    match before with
    | Some r -> (
        let rec go = function
          | c :: cs when case_rule c = Some r -> Some (ext @ (c :: cs))
          | c :: cs -> Option.map (List.cons c) (go cs)
          | [] -> None
        in
        match go cs with
        | Some cs -> cs
        | None -> error loc "extend %s: %s has no rule %s" f f r)
    | None -> (
        match List.rev cs with
        | ({ pc_lhs = { ppat_desc = Ppat_any; _ }; pc_guard = None; _ } as last)
          :: rest ->
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
        let loc = si.pstr_loc in
        let f = string_attr (Option.get (find_attr "extend" attrs)) in
        let before = Option.map string_attr (find_attr "before" attrs) in
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
  List.rev (List.fold_left extend [] str)

(** The check that the spec of the rule [r] is well-typed: that the sorts of its
    operands have the shapes that the typing of its node and their annotations
    give them, and that the side condition of the typing holds. The generated
    OCaml asserts it, and the proofs assume it. *)
let spec_check globals (r : raw_fn) (spec : expression) : expression option =
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
  (match spec.pexp_desc with
  | Pexp_construct ({ txt = Lident n; _ }, arg) -> (
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
          (* the operands built by the spec are well-typed *)
          if List.for_all is_ident operands then (
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
  (* the annotations of the operands *)
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
  | PAs (p, _), _ -> subsumes p q
  | _, PAs (q, _) -> subsumes p q
  | PLit _, PLit _ -> true
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
  try Kanon_parser.file Kanon_lexer.token lexbuf with
  | Kanon_lexer.Error (p, msg) -> raise (Error (at p, msg))
  | Kanon_parser.Error -> raise (Error (at lexbuf.lex_start_p, "syntax error"))

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
      parse_string ~file:"<kanon>"
        (Printf.sprintf
           "oracle tag_le : t -> t -> bool\n\
           \            fn mk_commut_binop (op : %s) (l r : t) : kind =\n\
           \             if tag_le l r then %s (op, l, r) else %s (op, r, l)\n"
           ty kc.c_name kc.c_name)

let program (str : structure) : program =
  let str = desugar_ops#structure (extend_rules (comm_fns () @ str)) in
  let prims, raws =
    List.fold_left
      (fun (prims, raws) (si : structure_item) ->
        match si.pstr_desc with
        | Pstr_primitive vd ->
            let pargs, pret = arrow_of_core vd.pval_type in
            ( {
                pname = vd.pval_name.txt;
                pargs;
                pret;
                oracle = vd.pval_prim = [ "oracle" ];
              }
              :: prims,
              raws )
        | Pstr_value (_, [ vb ]) -> (prims, raw_fn vb :: raws)
        | Pstr_value _ -> error si.pstr_loc "one function per let"
        | _ -> error si.pstr_loc "unsupported top-level item")
      ([], []) str
  in
  let prims = List.rev prims and raws = List.rev raws in
  let globals =
    (("type_of", { args = [ TTerm ]; ret = TSty })
    :: List.map (fun p -> (p.pname, { args = p.pargs; ret = p.pret })) prims)
    @ List.map
        (fun r -> (r.rname, { args = List.map snd r.rparams; ret = r.rret }))
        raws
  in
  let names = List.map fst globals in
  List.iter
    (fun n ->
      if List.length (List.filter (( = ) n) names) > 1 then
        error Location.none "%s is defined twice" n)
    names;
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
            error r.rloc
              "%s: [@ty_only] functions take one term, and only read its type"
              r.rname)
    raws;
  let env0 = { vars = []; locals = []; globals } in
  let raws = law_cases globals raws in
  let typings = typings env0 in
  node_typings := typings;
  let fns =
    List.map
      (fun r ->
        atom_counter := 0;
        List.iter (fun (x, _) -> no_shadow env0 r.rloc x) r.rparams;
        let env = { env0 with vars = r.rparams } in
        if r.rcases && Option.is_none r.rspec then
          error r.rloc "%s: [@cases] needs a spec" r.rname;
        cases_mode := r.rcases;
        let rbody =
          match r.rspec with
          | Some spec when r.rcases -> (
              let body = spec_match spec (with_default spec r.rbody) in
              match if r.runtyped then None else spec_check globals r spec with
              | Some c ->
                  let loc = c.pexp_loc in
                  Ast_builder.Default.(
                    pexp_sequence ~loc (pexp_assert ~loc c) body)
              | None -> body)
          | _ ->
              if r.rsorts <> [] then
                error r.rloc "%s: only the operands of a rule's spec have sorts"
                  r.rname;
              r.rbody
        in
        let spec =
          Option.map
            (fun s ->
              if r.rret <> TTerm then
                error r.rloc "%s: only term-returning functions have a spec"
                  r.rname;
              in_spec := true;
              let s = expr env ~expected:TTerm s in
              in_spec := false;
              s)
            r.rspec
        in
        ordered := Option.is_some spec;
        sort_vars := sort_binds env r;
        let body = expr env ~expected:r.rret rbody in
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
        })
      raws
  in
  { prims; fns; typing = List.filter operator_typing (List.map snd typings) }
