(** Abstract syntax of Kanon, the rule language in which smart constructors are
    written, over a value language that is declared (see {!lang}). *)

type ty =
  | TInt  (** mathematical integers: [Z.t] in OCaml, [Int] in Lean *)
  | TBool
  | TUnit
  | TTerm  (** the terms of the language, [t] *)
  | TKind
      (** the kind of a term, generated from the nodes: the leaf nodes, then the
          operators by arity ([Op2 of op2 * t * t]), which Kanon names [kind]
          internally (users cannot) *)
  | TSty  (** the type of a term, [ty], generated from the sorts *)
  | TData of string
      (** the other types: those of operators of each arity ([op1], [op2], ...,
          [opn]), generated from the nodes, and those declared by the language
          (enums, records and abstract types) *)
  | TTuple of ty list
  | TOption of ty
  | TList of ty
  | TArray of ty
      (** immutable arrays, [t array]: [Iarray.t] in OCaml, [Array] in Lean *)

(** A doc comment where it cannot be attached: its location, and the message. *)
exception Misplaced_doc of Location.t * string

let rec pp_ty ft = function
  | TInt -> Fmt.string ft "int"
  | TBool -> Fmt.string ft "bool"
  | TUnit -> Fmt.string ft "unit"
  | TTerm -> Fmt.string ft "t"
  | TKind -> Fmt.string ft "kind"
  | TSty -> Fmt.string ft "ty"
  | TData s -> Fmt.string ft s
  | TTuple l -> Fmt.(parens (list ~sep:(any " * ") pp_ty)) ft l
  | TOption t -> Fmt.pf ft "%a option" pp_ty t
  | TList t -> Fmt.pf ft "%a list" pp_ty t
  | TArray t -> Fmt.pf ft "%a array" pp_ty t

(** An argument of a constructor. [Small] integers are OCaml [int]s (widths,
    indices), as opposed to [Z.t]s; in Kanon both have type [int]. *)
type arg = Arg of ty | Small

let arg_ty = function Arg t -> t | Small -> TInt

type constr = {
  c_name : string;  (** the Kanon (and OCaml and Lean) name *)
  c_res : ty;
  c_args : arg list;
  c_doc : string option;
      (** the doc comment of a node or a sort ([(** ... *)] before [node] or
          [sort]) *)
}

(** A type of the language: generated ([kind], [ty] and the types of operators),
    or declared (enums, records and abstract types). *)
type decl = {
  d_name : string;
  d_ocaml : string option;
      (** [[@ocaml]]: the OCaml type of an abstract type, or the one that a
          record or a variant re-exports *)
  d_lean : string option;
      (** the Lean type, if it is not the Kanon name, CamelCased ([[@lean]]) *)
  d_eq : bool;
      (** whether [=] and [<>] are allowed at this type: not at an abstract type
          marked [[@noeq]] *)
  d_equal : string option;
      (** the OCaml function that decides [=] at an abstract type, if it is not
          [Stdlib.( = )] ([[@equal]]) *)
  d_hash : string option;
      (** the OCaml function that hashes an abstract type, if it is not
          [Hashtbl.hash] ([[@hash]]) *)
  d_fields : (string * ty) list;  (** the fields of a record type, in order *)
  d_loc : Location.t;  (** of its name *)
  d_doc : string option;  (** the doc comment before [type] *)
}

(** A subsort, [subsort TNonzero of nat : TBitVector n]: a sort of the same
    arguments as its parent, whose terms are known to satisfy a predicate that
    only Lean gives a meaning to. It has no constructor in [ty]: a typing that
    mentions it is the typing of its parent, and records the subsort. *)
type subsort = {
  ss_name : string;
  ss_args : arg list;  (** those of its parent *)
  ss_parent : string;  (** the parent sort *)
  ss_lean : string option;
      (** [[@lean "P"]]: the Lean predicate on terms, [P : Term -> Prop], that
          the terms of the subsort satisfy *)
  ss_doc : string option;
  ss_loc : Location.t;  (** of its name *)
}

(** An operator on terms, e.g. [+]: in expressions it calls its smart
    constructor [smart], with the leading arguments [pre]; in patterns it
    matches its [node], with the parameters [params] (any parameters if there
    are none); on operands that are not terms, of the types of its arguments, it
    is the function [on_value]. *)
type operator = {
  sym : string;
      (** as parsed: ["+"], ["&&"], ["urem"], ...; ["~-"] for the prefix [-] *)
  arity : int;
  node : string;
  params : Ppxlib.expression list;
  smart : string;
  pre : Ppxlib.expression list;
  on_value : string option;
  op_loc : Location.t;  (** of its symbol, in its declaration *)
  op_doc : string option;  (** the doc comment before [infix] or [prefix] *)
}

(** The operators declared with a word, which the lexer reads as operators from
    their declaration on: a word, an infix operator at the level of [*]
    ([infix "urem" = ...]), or a symbol followed by a word ([infix "<u" = ...],
    [prefix "!u" = ...]), at the level of its symbol. *)
let infix_words : (string, unit) Hashtbl.t = Hashtbl.create 8

(** The typing of an operator [C], as declared ([C (x, y) : s1 -> s2 when e]),
    before it is checked with the rules (see {!typing}). *)
type raw_typing = {
  rt_params : Ppxlib.expression list;
  rt_sorts : Ppxlib.expression list;
  rt_nary : bool;
      (** the only operand sort was [s list]: the operands are a list of terms
          of sort [s], the first of [rt_sorts] *)
  rt_subs : string option list;
      (** the subsort that each of [rt_sorts] was written as, which they have
          the parent of *)
  rt_when : Ppxlib.expression option;
  rt_loc : Location.t;
}

(** An algebraic law of an operator, declared by an attribute on its
    constructor, from which Kanon derives the first rules of the operator's rule
    function (see [Check.law_cases]). *)
type law =
  | Fold of string * string option
      (** [[@fold f lift]]: constant folding with [f], whose result [lift] (a
          function or a node) makes a term, if it is not one already *)
  | Unit of string
      (** [[@unit c]]: the literal or the constant [c] is a (right) unit *)
  | Zero of string
      (** [[@zero c]]: the literal or the constant [c] is (right) absorbing *)
  | Idem  (** [[@idem]]: [x op x = x] *)
  | Invol  (** [[@invol]]: [op (op x) = x] *)

(** The language that the rules are written in: its types, constructors and
    operators, as declared in its [.knl] file. *)
type lang = {
  decls : decl list;
  constrs : constr list;
  commutative : string list;
      (** the binary operators whose operands commute, which patterns match in
          either order: in [[@cases]] functions, [[@comm]] may only swap theirs,
          and the swapped alternative is proved from the other by commutativity
      *)
  subsorts : subsort list;
  node_kinds : string list;
      (** the kind constructors of the operators of each arity, whose first
          argument is an operator, which then stands for the node:
          [Add (c, l, r)] for [Op2 (Add c, l, r)] *)
  notations : string list;
      (** [notation C]: the leaf nodes of one [int] or [bool], which the
          literals of patterns stand for ([0], [true], [#x]) *)
  sort_getters : (string * string) list;
      (** the functions that read the argument of the sort of a term, declared
          by [[@get f]] on the constructors of sorts with one argument *)
  constants : (string * (string option * Ppxlib.expression)) list;
      (** [constant c (v) = e]: the term of the literal or the named constant
          [c] ([0], [true], [ones], ...), at the sort of the term [v] if there
          is one, for the laws [[@unit c]] and [[@zero c]] *)
  constant_docs : (string * string) list;
      (** the doc comments before [constant], by constant (only of those that
          have one) *)
  ty_only : string list;
      (** the functions of a term that only read its type: [type_of], and the
          helpers marked [[@ty_only]] *)
  lean_root : string;
      (** [[@@@lean_root "R"]]: the namespace of the Lean model, and the root of
          its modules *)
  lean_params : (string * string) list;
      (** [[@@@lean_param "x" "T"]]: the parameters of the semantics *)
  ocaml_types : string option;
      (** [[@@@ocaml_types "M"]]: the OCaml module of the types, which the rules
          open *)
  ocaml_prims : string option;
      (** [[@@@ocaml_prims "M"]]: the OCaml module of the primitives *)
  operators : operator list;
  raw_typing : (string * raw_typing) list;
  laws : (string * law * Location.t * Location.t) list;
      (** the laws of the operators, in the order of their declaration, with the
          locations of their attributes and of their arguments (of their
          attributes, if they have none) *)
}

let lang =
  ref
    {
      decls = [];
      constrs = [];
      commutative = [];
      subsorts = [];
      node_kinds = [];
      notations = [];
      sort_getters = [];
      constants = [];
      constant_docs = [];
      ty_only = [ "type_of" ];
      lean_root = "Kanon";
      lean_params = [];
      ocaml_types = None;
      ocaml_prims = None;
      operators = [];
      raw_typing = [];
      laws = [];
    }

let find_constr name = List.find_opt (fun c -> c.c_name = name) !lang.constrs
let find_subsort name = List.find_opt (fun s -> s.ss_name = name) !lang.subsorts
let find_decl name = List.find_opt (fun d -> d.d_name = name) !lang.decls

(** The name of the declaration of a type of the language. *)
let decl_name = function
  | TKind -> Some "kind"
  | TSty -> Some "ty"
  | TData s -> Some s
  | _ -> None

let decl_of_ty t =
  match Option.bind (decl_name t) find_decl with
  | Some d -> d
  | None -> Fmt.failwith "type %a is not declared by the language" pp_ty t

let find_operator ~arity sym =
  List.find_opt (fun o -> o.sym = sym && o.arity = arity) !lang.operators

let is_commutative name = List.mem name !lang.commutative

type unop = Neg | Not
type binop = Add | Sub | Mul | Lt | Le | Gt | Ge | Eq | Ne | And | Or

type pat = {
  p : pat_desc;
  pty : ty;
  ploc : Location.t;
  pid : int;
      (** unique to the pattern node, and shared by its copy in the swapped
          alternative of a [[@comm]] pattern *)
}

and pat_desc =
  | PAny
  | PVar of string
  | PAs of pat * string
  | POr of pat * pat
  | PComm of pat * pat  (** [p [@comm]]: [p], or [p] with operands swapped *)
  | PInt of Z.t
  | PBool of bool
  | PUnit
  | PTuple of pat list
  | PConstr of constr * pat list
      (** a constructor of kind type, matched against a term, matches its kind
      *)
  | PSome of pat
  | PNone
  | PNil
  | PCons of pat * pat
  | PRecord of (string * pat) list  (** partial records *)

(** Whether [p] matches anything: [_], or a tuple of blanks, at any depth, which
    is strictly equivalent. [x, _] and [_ as x] are not blank. *)
let rec is_catch_all (p : pat) =
  match p.p with
  | PAny -> true
  | PTuple l -> List.for_all is_catch_all l
  | _ -> false

type expr = { e : expr_desc; ety : ty; eloc : Location.t }

and expr_desc =
  | EVar of string
  | EInt of Z.t
  | EBool of bool
  | EUnit
  | EConstr of constr * expr list
  | ENode of expr * expr
      (** a raw node: its kind and its sort, which Kanon infers from the typing
          of the node *)
  | ECall of string * expr list  (** global function or primitive *)
  | ELocalCall of string * expr list
  | EUnop of unop * expr
  | EBinop of binop * expr * expr
  | EIf of expr * expr * expr
  | ELet of pat * expr * expr
  | ELetFun of string * (string * ty) list * expr * expr
  | EMatch of expr list * case list
  | ETuple of expr list
  | ESome of expr
  | ENone
  | ENil
  | ECons of expr * expr
  | EArray of expr list  (** [[| a; b |]] *)
  | ERecord of (string * expr) list
  | EField of expr * string
  | EAssert of expr * expr
  | EUnreachable
      (** a value that the typing of the spec rules out: [assert false] in
          OCaml, [default] in Lean *)

and case = {
  pat : pat;  (** of tuple type when there are several scrutinees *)
  guard : expr option;
  body : expr;
  rule : string option;
  cloc : Location.t;
  alt : (int * int * bool * string) list;
      (** the alternative of the source case: for each or-pattern (and [[@comm]]
          pattern, flagged) taken, its [pid], the side chosen, and a name for
          that side (see [Check.alternatives]) *)
}

type fn = {
  name : string;
  params : (string * ty) list;
  ret : ty;
  spec : expr option;
      (** for rule functions, the raw term the result must refine *)
  cases : bool;
      (** [[@cases]]: literals are bound to their values, and the rules are
          proved per alternative *)
  body : expr;
  floc : Location.t;
  fdoc : string option;  (** the doc comment before [fn] or [rule] *)
  no_lean : bool;
      (** [[@no_lean]]: a helper that is generated in OCaml but not modelled in
          Lean *)
}

type prim = {
  pname : string;
  pargs : ty list;
  pret : ty;
  oracle : bool;
  ploc : Location.t;  (** of its name *)
  pdoc : string option;  (** the doc comment before [prim] or [oracle] *)
  pno_lean : bool;  (** [[@no_lean]]: a primitive that Lean does not define *)
}

(** Folds [f] over the calls of global functions and primitives in [e], with
    their locations, in the order they are met (a call before its arguments). *)
let rec fold_calls f acc (e : expr) =
  let go = fold_calls f in
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> acc
  | ECall (g, args) -> List.fold_left go (f acc g e.eloc) args
  | EConstr (_, l) | ELocalCall (_, l) | ETuple l | EArray l ->
      List.fold_left go acc l
  | ENode (a, b) | EBinop (_, a, b) | ECons (a, b) | EAssert (a, b) ->
      go (go acc a) b
  | ELet (_, a, b) | ELetFun (_, _, a, b) -> go (go acc a) b
  | EUnop (_, a) | ESome a | EField (a, _) -> go acc a
  | EIf (a, b, c) -> go (go (go acc a) b) c
  | ERecord l -> List.fold_left (fun acc (_, e) -> go acc e) acc l
  | EMatch (scruts, cases) ->
      let acc = List.fold_left go acc scruts in
      List.fold_left
        (fun acc (c : case) ->
          let acc = Option.fold ~none:acc ~some:(go acc) c.guard in
          go acc c.body)
        acc cases

(** The typing of a node: its operands, then its result, have the sorts
    [t_sorts] (terms of type [ty] over [t_vars], which are existentially
    quantified, and the arguments [t_params] of the node), under the condition
    [t_when]. A typing may give only the sort of the result. *)
type typing = {
  t_constr : constr;
  t_params : string list;  (** one per argument, [_] if it is unnamed *)
  t_vars : (string * ty) list;
  t_sorts : expr list;
  t_nary : bool;
      (** the operands are a list, whose elements all have the first sort *)
  t_subs : string option list;
      (** the subsort that each of [t_sorts] was written as: the sort of that
          position is then its parent *)
  t_when : expr option;
}

type program = { prims : prim list; fns : fn list; typing : typing list }
