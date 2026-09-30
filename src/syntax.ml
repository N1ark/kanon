(** Abstract syntax of Kanon, the rule language in which smart constructors are
    written, over a value language that is declared (see {!lang}). *)

type ty =
  | TInt  (** mathematical integers: [Z.t] in OCaml, [Int] in Lean *)
  | TBool
  | TUnit
  | TTerm  (** the terms of the language *)
  | TKind  (** the kind of a term *)
  | TSty  (** the type of a term *)
  | TData of string
      (** the other types declared by the language: operators, enums, records
          and abstract types *)
  | TTuple of ty list
  | TOption of ty
  | TList of ty

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

(** An argument of a constructor. [Small] integers are OCaml [int]s (widths,
    indices), as opposed to [Z.t]s; in Kanon both have type [int]. *)
type arg = Arg of ty | Small

let arg_ty = function Arg t -> t | Small -> TInt

type constr = {
  c_name : string;  (** the Kanon (and OCaml and Lean) name *)
  c_res : ty;
  c_args : arg list;
}

(** A type declared by the language: [kind], [ty], operators, enums, records and
    abstract types. *)
type decl = {
  d_name : string;
  d_ocaml : string;  (** the OCaml type *)
  d_lean : string option;
      (** the Lean type, if it is not the Kanon name, CamelCased ([[@lean]]) *)
  d_eq : bool;  (** whether [=] and [<>] are allowed at this type *)
  d_equal : string option;
      (** the function of the primitives that decides [=] in OCaml, if it is not
          [Stdlib.( = )] ([[@equal]]) *)
  d_fields : (string * ty) list;  (** the fields of a record type, in order *)
}

(** An operator on terms, e.g. [+]: in expressions it calls its smart
    constructor [smart], with the leading arguments [pre]; in patterns it
    matches its [node], with any parameters; on the values of literals (see
    [lit_value]) it is the primitive [on_value]. *)
type operator = {
  sym : string;
      (** as parsed: ["+"], ["&&"], ...; ["~-"], ["lognot"] and ["not"] for the
          prefix [-], [~] and [not] *)
  arity : int;
  node : string;
  smart : string;
  pre : Ppxlib.expression list;
  on_value : string option;
}

(** The typing of an operator [C], as declared ([C (x, y) : s1 -> s2 when e]),
    before it is checked with the rules (see {!typing}). *)
type raw_typing = {
  rt_params : Ppxlib.expression list;
  rt_sorts : Ppxlib.expression list;
  rt_when : Ppxlib.expression option;
  rt_loc : Location.t;
}

(** An algebraic law of an operator, declared by an attribute on its
    constructor, from which Kanon derives the first rules of the operator's rule
    function (see [Check.law_cases]). *)
type law =
  | Fold of string  (** [[@fold "f"]]: constant folding with [f] *)
  | Unit of string  (** [[@unit "c"]]: the literal [c] is a (right) unit *)
  | Zero of string  (** [[@zero "c"]]: the literal [c] is (right) absorbing *)
  | Idem  (** [[@idem]]: [x op x = x] *)
  | Invol  (** [[@invol]]: [op (op x) = x] *)
  | Distrib_ite
      (** [[@distrib_ite]]: [op (Ite (b, l, r)) = Ite (b, op l, op r)] *)

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
  node_kinds : string list;
      (** the kind constructors whose first argument is an operator, which then
          stands for the node: [Add (c, l, r)] for [Binop (Add c, l, r)] *)
  lit_bool : string option;  (** the kind constructor of boolean literals *)
  lit_node : string option;
      (** the kind constructor of integer literals, which integer patterns and
          [#x] match *)
  lit_int : bool;
      (** [[@literal "int"]]: in rules, [#x] binds the argument of the literals
          of [lit_node], an [int], rather than their value *)
  lit_value : string;
      (** [[@literal "t"]]: the type of the values of the literals of
          [lit_node], which [#x] binds in rules *)
  lit_fns : (string * string) list;
      (** the functions of those literals, declared by attributes on the
          constructors of literals: [to_term] (a value where a term is
          expected), [of_term] (the primitive that reads the value of a
          literal), [bool_to_term] (a boolean result of [[@fold]]) and, for
          [raw:f], the primitive that computes [f] on a literal rather than on
          its value *)
  constants : (string * (string * Ppxlib.expression)) list;
      (** [constant "c" (v) = e]: the term of the literal [c] at the type of the
          term [v], for the laws [[@unit "c"]] and [[@zero "c"]] *)
  ite : string option;
      (** [[@ite]]: the node of conditionals, for [[@distrib_ite]] *)
  ty_only : string list;
      (** the functions of a term that only read its type: [ty], and the helpers
          marked [[@ty_only]] *)
  lean_root : string;
      (** [[@@@lean_root "R"]]: the namespace of the Lean model, and the root of
          its modules *)
  lean_params : (string * string) list;
      (** [[@@@lean_param "x" "T"]]: the parameters of the semantics *)
  operators : operator list;
  raw_typing : (string * raw_typing) list;
  laws : (string * law * Location.t) list;
      (** the laws of the operators, in the order of their declaration *)
}

let lang =
  ref
    {
      decls = [];
      constrs = [];
      commutative = [];
      node_kinds = [];
      lit_bool = None;
      lit_node = None;
      lit_int = false;
      lit_value = "";
      lit_fns = [];
      constants = [];
      ite = None;
      ty_only = [ "ty" ];
      lean_root = "Kanon";
      lean_params = [];
      operators = [];
      raw_typing = [];
      laws = [];
    }

let find_constr name = List.find_opt (fun c -> c.c_name = name) !lang.constrs
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

(** The type of the values of literals, where [#x] binds them. *)
let lit_value_ty () = TData !lang.lit_value

(** Whether [t] is the type of the values of literals. *)
let is_lit_value t =
  Option.is_some !lang.lit_node && (not !lang.lit_int) && t = lit_value_ty ()

(** A function of the literals (see [lit_fns]). *)
let lit_fn name = List.assoc_opt name !lang.lit_fns

let find_operator ~arity sym =
  List.find_opt (fun o -> o.sym = sym && o.arity = arity) !lang.operators

let is_commutative name = List.mem name !lang.commutative

type unop = Neg | Not | Lognot

type binop = Add | Sub | Mul | Lt | Le | Gt | Ge | Eq | Ne | And | Or
and bitop = Land | Lor | Lxor | Lsl | Asr

type binop' = Arith of binop | Bit of bitop

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
  | PLit of string
      (** in [[@cases]] functions, [C x], where [C] builds integer literals: a
          literal, whose value is bound to [x] *)

type expr = { e : expr_desc; ety : ty; eloc : Location.t }

and expr_desc =
  | EVar of string
  | EInt of Z.t
  | EBool of bool
  | EUnit
  | EConstr of constr * expr list
  | ENode of expr * expr  (** [kind <| ty] *)
  | ECall of string * expr list  (** global function or primitive *)
  | ELocalCall of string * expr list
  | EUnop of unop * expr
  | EBinop of binop' * expr * expr
  | EIf of expr * expr * expr
  | ELet of pat * expr * expr
  | ELetFun of string * (string * ty) list * expr * expr
  | EMatch of expr list * case list
  | ETuple of expr list
  | ESome of expr
  | ENone
  | ENil
  | ECons of expr * expr
  | ERecord of (string * expr) list
  | EField of expr * string
  | EAssert of expr * expr

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
}

type prim = { pname : string; pargs : ty list; pret : ty; oracle : bool }

(** The typing of an operator: its operands, then its result, have the sorts
    [t_sorts] (terms of type [ty] over [t_vars], which are existentially
    quantified, and the arguments [t_params] of the operator), under the
    condition [t_when]. *)
type typing = {
  t_constr : constr;
  t_params : string list;  (** one per argument, [_] if it is unnamed *)
  t_vars : (string * ty) list;
  t_sorts : expr list;
  t_when : expr option;
}

type program = { prims : prim list; fns : fn list; typing : typing list }
