(* The grammar of Kanon. It builds an OCaml parse tree, which [Check] then
   converts to typed Kanon: rules become functions with [[@spec]] and [[@cases]]
   attributes, and rule names [[@r]] attributes on their patterns. In the
   declaration of a language, types are OCaml type declarations, nodes are types
   [node] with a [[@node]] attribute, and operators [[@infix]] or [[@prefix]]
   expressions; [extend rule f] and [extend fn f] items are [function]s of the
   cases they add to [f], with [[@extend]], [[@before]] and [[@fn]] attributes.
   *)

%{
open Ppxlib

let mkloc (s, e) = { loc_start = s; loc_end = e; loc_ghost = false }
let lid loc s = { txt = Lident s; loc }
let exp loc d = { pexp_desc = d; pexp_loc = loc; pexp_loc_stack = []; pexp_attributes = [] }
let pat loc d = { ppat_desc = d; ppat_loc = loc; ppat_loc_stack = []; ppat_attributes = [] }
let typ loc d = { ptyp_desc = d; ptyp_loc = loc; ptyp_loc_stack = []; ptyp_attributes = [] }
let ident loc s = exp loc (Pexp_ident (lid loc s))
let apply loc f args = exp loc (Pexp_apply (f, List.map (fun a -> (Nolabel, a)) args))
let binop loc op a b = apply loc (ident loc op) [ a; b ]
let econstr loc c arg = exp loc (Pexp_construct (lid loc c, arg))
let pconstr loc c arg = pat loc (Ppat_construct (lid loc c, Option.map (fun p -> ([], p)) arg))
let tuple_or_one mk = function [ x ] -> x | l -> mk l

let attr loc name payload =
  { attr_name = { txt = name; loc }; attr_payload = PStr payload; attr_loc = loc }

let eval_item loc e = { pstr_desc = Pstr_eval (e, []); pstr_loc = loc }
let string loc s = exp loc (Pexp_constant (Pconst_string (s, loc, None)))

let param loc (x, t) =
  {
    pparam_loc = loc;
    pparam_desc =
      Pparam_val (Nolabel, None, pat loc (Ppat_constraint (pat loc (Ppat_var { txt = x; loc }), t)));
  }

(* A function: its parameters, if any, and its result type, if given. *)
let fn_expr loc params ret body =
  match params with
  | [] -> body
  | _ ->
      exp loc
        (Pexp_function
           (List.map (param loc) params, Option.map (fun t -> Pconstraint t) ret, Pfunction_body body))

let binding loc ?(attrs = []) p params ret body =
  {
    pvb_pat = p;
    pvb_expr = fn_expr loc params ret body;
    pvb_constraint =
      (match (params, ret) with
      | [], Some typ -> Some (Pvc_constraint { locally_abstract_univars = []; typ })
      | _ -> None);
    pvb_attributes = attrs;
    pvb_loc = loc;
  }

let item loc d = { pstr_desc = d; pstr_loc = loc }

let use_item loc m =
  item loc (Pstr_extension (({ txt = "kanon.use"; loc }, PStr [ eval_item loc (string loc m) ]), []))

(* [node C ...] in the declaration of a language: a type [node] with the only
   constructor [C], which [Check] places where [C] appears in a type *)
let node_decl loc c =
  {
    ptype_name = { txt = "node"; loc };
    ptype_params = [];
    ptype_cstrs = [];
    ptype_kind = Ptype_variant [ c ];
    ptype_private = Public;
    ptype_manifest = None;
    ptype_attributes = [ attr loc "node" [] ];
    ptype_loc = loc;
  }

let prim loc name t kind =
  item loc
    (Pstr_primitive
       { pval_name = { txt = name; loc }; pval_type = t; pval_prim = [ kind ]; pval_attributes = []; pval_loc = loc })

let rec elist loc = function
  | [] -> econstr loc "[]" None
  | x :: l -> econstr loc "::" (Some (exp loc (Pexp_tuple [ x; elist loc l ])))

let rec plist loc = function
  | [] -> pconstr loc "[]" None
  | x :: l -> pconstr loc "::" (Some (pat loc (Ppat_tuple [ x; plist loc l ])))

(* An operator on terms in a pattern, which [Check] replaces with the node that
   the language declares for it. *)
let pnode loc op args = pconstr loc op (Some (tuple_or_one (fun l -> pat loc (Ppat_tuple l)) args))

(* The payload of an attribute [[@a "s1" ... "sn"]] *)
let strings loc = function
  | [] -> []
  | [ s ] -> [ eval_item loc (string loc s) ]
  | l -> [ eval_item loc (exp loc (Pexp_tuple (List.map (string loc) l))) ]

let neg loc (e : expression) =
  match e.pexp_desc with
  | Pexp_constant (Pconst_integer (s, None)) -> exp loc (Pexp_constant (Pconst_integer ("-" ^ s, None)))
  | _ -> apply loc (ident loc "~-") [ e ]
%}

%token <string> LID UID INT STRING
%token AS ASR ASSERT BEFORE CONSTANT ELSE EXTEND FALSE FN IF IN INFIX LAND LET LOR LSL LSR LXOR MATCH NODE NOT OF
%token ORACLE PREFIX PRIM
%token RULE THEN TRUE TYPE USE WHEN WITH
%token LBRACKETAT LBRACKETATATAT COLONCOLON ARROW LE GE NE ANDAND BARBAR
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COMMA SEMI COLON BAR EQ LT GT PLUS MINUS STAR DOT
%token EQEQ PLUSPLUS HASH TILDE UNDERSCORE EOF

(* the bodies of [let], [match] and [if] extend as far as possible *)
%nonassoc below_SEMI
%nonassoc SEMI
%nonassoc below_BAR
%nonassoc BAR
%nonassoc below_COMMA
%nonassoc COMMA
%nonassoc below_BARBAR
%nonassoc BARBAR

%start <Ppxlib.structure> file

%%

file:
  | items = list(item) EOF { items }

item:
  (* [use +m] or [use "path"]: the module [m] built into kanon, or the module
     whose files are [path.knl] and [path.kn] (see [Main]) *)
  | USE PLUS m = LID { use_item (mkloc $loc) ("+" ^ m) }
  | USE m = STRING { use_item (mkloc $loc) m }
  | PRIM x = LID COLON t = typ { prim (mkloc $loc) x t "" }
  | ORACLE x = LID COLON t = typ { prim (mkloc $loc) x t "oracle" }
  | FN x = LID ps = params ret = option(preceded(COLON, typ)) attrs = list(decl_attr) EQ body = seq_expr
    { let loc = mkloc $loc in
      item loc (Pstr_value (Nonrecursive, [ binding loc ~attrs (pat loc (Ppat_var { txt = x; loc })) ps ret body ])) }
  | RULE x = LID ps = params COLON spec = cons_expr rattrs = list(decl_attr) body = option(preceded(EQ, seq_expr))
    { let loc = mkloc $loc in
      (* a rule without a body only has the rules from laws and [default] *)
      let body = match body with Some b -> b | None -> exp loc Pexp_unreachable in
      let attrs = [ attr loc "spec" [ eval_item loc spec ]; attr loc "cases" [] ] @ rattrs in
      let t = typ loc (Ptyp_constr (lid loc "t", [])) in
      item loc (Pstr_value (Nonrecursive, [ binding loc ~attrs (pat loc (Ppat_var { txt = x; loc })) ps (Some t) body ])) }
  | EXTEND fn = extended x = LID before = option(preceded(BEFORE, rule_name)) EQ BAR? cs = cases
    { let loc = mkloc $loc in
      let attrs =
        attr loc "extend" [ eval_item loc (string loc x) ]
        :: Option.to_list (Option.map (fun r -> attr loc "before" [ eval_item loc (string loc r) ]) before)
        @ (if fn then [ attr loc "fn" [] ] else [])
      in
      item loc (Pstr_eval (exp loc (Pexp_function ([], None, Pfunction_cases (cs, loc, []))), attrs)) }
  | NODE c = constr_decl
    { let loc = mkloc $loc in
      item loc (Pstr_type (Recursive, [ node_decl loc c ])) }
  | TYPE x = LID attrs = list(decl_attr) kind = option(preceded(EQ, type_kind))
    { let loc = mkloc $loc in
      item loc
        (Pstr_type
           ( Recursive,
             [
               {
                 ptype_name = { txt = x; loc = mkloc $loc(x) };
                 ptype_params = [];
                 ptype_cstrs = [];
                 ptype_kind = Option.value ~default:Ptype_abstract kind;
                 ptype_private = Public;
                 ptype_manifest = None;
                 ptype_attributes = attrs;
                 ptype_loc = loc;
               };
             ] )) }
  | INFIX op = STRING EQ e = seq_expr
    { let loc = mkloc $loc in
      item loc (Pstr_eval (e, [ attr loc "infix" [ eval_item loc (string loc op) ] ])) }
  | PREFIX op = STRING EQ e = seq_expr
    { let loc = mkloc $loc in
      item loc (Pstr_eval (e, [ attr loc "prefix" [ eval_item loc (string loc op) ] ])) }
  | CONSTANT c = STRING LPAREN v = LID RPAREN EQ e = seq_expr
    { let loc = mkloc $loc in
      let v = { pparam_loc = loc; pparam_desc = Pparam_val (Nolabel, None, pat loc (Ppat_var { txt = v; loc })) } in
      let f = exp loc (Pexp_function ([ v ], None, Pfunction_body e)) in
      item loc (Pstr_eval (f, [ attr loc "constant" [ eval_item loc (string loc c) ] ])) }
  | LBRACKETATATAT a = LID ss = list(STRING) RBRACKET
    { let loc = mkloc $loc in
      item loc (Pstr_attribute (attr loc a (strings loc ss))) }

(* ---------------------------------------------------------------- *)
(* Declarations of the language *)

decl_attr:
  | LBRACKETAT a = LID ss = list(STRING) RBRACKET { attr (mkloc $loc) a (strings (mkloc $loc) ss) }

type_kind:
  | BAR? cs = separated_nonempty_list(BAR, constr_decl) { Ptype_variant cs }
  | LBRACE fs = separated_nonempty_list(SEMI, label_decl) RBRACE { Ptype_record fs }

(* [C of a * b (x, y) : s1 -> s2 when e]: the names of the arguments, the
   sorts of the operands and result, and a side condition, as [[@params]],
   [[@sorts]] and [[@when]] attributes *)
constr_decl:
  | c = UID args = loption(preceded(OF, separated_nonempty_list(STAR, typ_app)))
    ps = option(constr_params) sorts = option(preceded(COLON, separated_nonempty_list(ARROW, app_expr)))
    g = option(preceded(WHEN, expr)) attrs = list(decl_attr)
    { let loc = mkloc $loc in
      let tuple l = tuple_or_one (fun l -> exp loc (Pexp_tuple l)) l in
      let typing =
        Option.to_list (Option.map (fun ps -> attr loc "params" [ eval_item loc (tuple ps) ]) ps)
        @ Option.to_list (Option.map (fun ss -> attr loc "sorts" [ eval_item loc (tuple ss) ]) sorts)
        @ Option.to_list (Option.map (fun g -> attr loc "when" [ eval_item loc g ]) g)
      in
      {
        pcd_name = { txt = c; loc = mkloc $loc(c) };
        pcd_vars = [];
        pcd_args = Pcstr_tuple args;
        pcd_res = None;
        pcd_loc = loc;
        pcd_attributes = typing @ attrs;
      } }

constr_params:
  | LPAREN ps = separated_nonempty_list(COMMA, constr_param) RPAREN { ps }

constr_param:
  | x = LID { ident (mkloc $loc) x }
  | UNDERSCORE { ident (mkloc $loc) "_" }

label_decl:
  | f = LID COLON t = typ
    { {
        pld_name = { txt = f; loc = mkloc $loc(f) };
        pld_mutable = Immutable;
        pld_type = t;
        pld_loc = mkloc $loc;
        pld_attributes = [];
      } }

(* ---------------------------------------------------------------- *)
(* Functions *)

params:
  | ps = list(param_group) { List.concat ps }

param_group:
  | LPAREN xs = nonempty_list(LID) COLON t = typ RPAREN { List.map (fun x -> (x, t)) xs }

(* ---------------------------------------------------------------- *)
(* Types *)

typ:
  | t = typ_tuple { t }
  | a = typ_tuple ARROW r = typ { typ (mkloc $loc) (Ptyp_arrow (Nolabel, a, r)) }

typ_tuple:
  | ts = separated_nonempty_list(STAR, typ_app) { tuple_or_one (fun l -> typ (mkloc $loc) (Ptyp_tuple l)) ts }

typ_app:
  | x = LID { typ (mkloc $loc) (Ptyp_constr (lid (mkloc $loc) x, [])) }
  | LPAREN t = typ RPAREN { t }
  | t = typ_app x = LID { typ (mkloc $loc) (Ptyp_constr (lid (mkloc $loc) x, [ t ])) }

(* ---------------------------------------------------------------- *)
(* Expressions *)

seq_expr:
  | e = expr %prec below_SEMI { e }
  | a = expr SEMI b = seq_expr { exp (mkloc $loc) (Pexp_sequence (a, b)) }

expr:
  | e = tuple_expr { e }
  | e = open_expr { e }

(* the expressions that extend as far as possible to the right *)
open_expr:
  | LET p = let_pat EQ rhs = seq_expr IN body = seq_expr
    { let loc = mkloc $loc in
      let p, ps, ret = p in
      exp loc (Pexp_let (Nonrecursive, [ binding loc p ps ret rhs ], body)) }
  | MATCH e = seq_expr WITH BAR? cs = cases { exp (mkloc $loc) (Pexp_match (e, cs)) }
  | IF c = seq_expr THEN a = expr ELSE b = expr { exp (mkloc $loc) (Pexp_ifthenelse (c, a, Some b)) }

let_pat:
  | f = LID ps = nonempty_list(param_group) ret = option(preceded(COLON, typ))
    { let loc = mkloc $loc in (pat loc (Ppat_var { txt = f; loc }), List.concat ps, ret) }
  | p = pattern { (p, [], None) }
  | p = pattern COLON t = typ { (p, [], Some t) }

cases:
  | c = case %prec below_BAR { [ c ] }
  | c = case BAR cs = cases { c :: cs }

case:
  | c = case_body { c }
  | r = rule_name COLON c = case_body
    { let loc = mkloc $loc(r) in
      let r = attr loc "r" [ eval_item loc (ident loc r) ] in
      { c with pc_lhs = { c.pc_lhs with ppat_attributes = c.pc_lhs.ppat_attributes @ [ r ] } } }

extended:
  | RULE { false }
  | FN { true }

rule_name:
  | r = LID { r }
  | NOT { "not" }
  | EXTEND { "extend" }

case_body:
  | p = pattern g = option(preceded(WHEN, seq_expr)) ARROW e = seq_expr { { pc_lhs = p; pc_guard = g; pc_rhs = e } }

tuple_expr:
  | es = tuple_items { tuple_or_one (fun l -> exp (mkloc $loc) (Pexp_tuple l)) es }

tuple_items:
  | e = or_expr %prec below_COMMA { [ e ] }
  | e = or_expr COMMA es = tuple_items { e :: es }

or_expr:
  | e = and_expr %prec below_BARBAR { e }
  | a = and_expr BARBAR b = or_rhs { binop (mkloc $loc) "||" a b }

or_rhs:
  | e = or_expr { e }
  | e = open_expr { e }

and_expr:
  | e = cmp_expr { e }
  | a = cmp_expr ANDAND b = and_rhs { binop (mkloc $loc) "&&" a b }

and_rhs:
  | e = and_expr { e }
  | e = open_expr { e }

cmp_expr:
  | e = cons_expr { e }
  | a = cmp_expr op = cmp_op b = cons_expr { binop (mkloc $loc) op a b }

cmp_op:
  | EQ { "=" }
  | NE { "<>" }
  | LT { "<" }
  | LE { "<=" }
  | GT { ">" }
  | GE { ">=" }
  | EQEQ { "==" }

cons_expr:
  | e = add_expr { e }
  | a = add_expr COLONCOLON b = cons_expr
    { let loc = mkloc $loc in econstr loc "::" (Some (exp loc (Pexp_tuple [ a; b ]))) }

add_expr:
  | e = mul_expr { e }
  | a = add_expr PLUS b = mul_expr { binop (mkloc $loc) "+" a b }
  | a = add_expr MINUS b = mul_expr { binop (mkloc $loc) "-" a b }
  | a = add_expr PLUSPLUS b = mul_expr { binop (mkloc $loc) "++" a b }

mul_expr:
  | e = pow_expr { e }
  | a = mul_expr op = mul_op b = pow_expr { binop (mkloc $loc) op a b }

mul_op:
  | STAR { "*" }
  | LAND { "land" }
  | LOR { "lor" }
  | LXOR { "lxor" }

pow_expr:
  | e = unary_expr { e }
  | a = unary_expr LSL b = pow_expr { binop (mkloc $loc) "lsl" a b }
  | a = unary_expr ASR b = pow_expr { binop (mkloc $loc) "asr" a b }
  | a = unary_expr LSR b = pow_expr { binop (mkloc $loc) "lsr" a b }

unary_expr:
  | e = app_expr { e }
  | MINUS e = unary_expr { neg (mkloc $loc) e }
  | TILDE e = unary_expr { apply (mkloc $loc) (ident (mkloc $loc) "lognot") [ e ] }

app_expr:
  | e = simple_expr { e }
  | f = LID args = nonempty_list(simple_expr) { apply (mkloc $loc) (ident (mkloc $loc(f)) f) args }
  | c = UID arg = simple_expr { econstr (mkloc $loc) c (Some arg) }
  | ASSERT e = simple_expr { exp (mkloc $loc) (Pexp_assert e) }
  | NOT e = simple_expr { apply (mkloc $loc) (ident (mkloc $loc) "not") [ e ] }

simple_expr:
  | x = LID { ident (mkloc $loc) x }
  | c = UID { econstr (mkloc $loc) c None }
  | TRUE { econstr (mkloc $loc) "true" None }
  | FALSE { econstr (mkloc $loc) "false" None }
  | i = INT { exp (mkloc $loc) (Pexp_constant (Pconst_integer (i, None))) }
  | LPAREN RPAREN { econstr (mkloc $loc) "()" None }
  | LPAREN e = seq_expr RPAREN { e }
  | LPAREN e = seq_expr COLON t = typ RPAREN { exp (mkloc $loc) (Pexp_constraint (e, t)) }
  (* [(v : TBitVector n)], the sort of an operand of a spec *)
  | LPAREN e = seq_expr COLON c = UID arg = option(simple_expr) RPAREN
    { let loc = mkloc $loc in
      exp loc (Pexp_extension ({ txt = "kanon.sort"; loc }, PStr [ eval_item loc e; eval_item loc (econstr loc c arg) ])) }
  | LBRACKET es = separated_list(SEMI, expr) RBRACKET { elist (mkloc $loc) es }
  | LBRACE fs = separated_nonempty_list(SEMI, field_expr) RBRACE { exp (mkloc $loc) (Pexp_record (fs, None)) }
  | e = simple_expr DOT f = LID { exp (mkloc $loc) (Pexp_field (e, lid (mkloc $loc(f)) f)) }

field_expr:
  | f = LID EQ e = expr { (lid (mkloc $loc(f)) f, e) }

(* ---------------------------------------------------------------- *)
(* Patterns *)

pattern:
  | p = or_pat { p }
  | p = pattern AS x = LID { pat (mkloc $loc) (Ppat_alias (p, { txt = x; loc = mkloc $loc(x) })) }

or_pat:
  | p = tuple_pat { p }
  | a = or_pat BAR b = tuple_pat { pat (mkloc $loc) (Ppat_or (a, b)) }

tuple_pat:
  | ps = separated_nonempty_list(COMMA, attr_pat) { tuple_or_one (fun l -> pat (mkloc $loc) (Ppat_tuple l)) ps }

attr_pat:
  | p = or_node_pat { p }
  | p = attr_pat LBRACKETAT a = LID RBRACKET
    { { p with ppat_attributes = p.ppat_attributes @ [ attr (mkloc $loc(a)) a [] ] } }

(* operators on terms, as in expressions *)
or_node_pat:
  | p = and_node_pat { p }
  | a = and_node_pat BARBAR b = or_node_pat { pnode (mkloc $loc) "||" [ a; b ] }

and_node_pat:
  | p = eq_node_pat { p }
  | a = eq_node_pat ANDAND b = and_node_pat { pnode (mkloc $loc) "&&" [ a; b ] }

eq_node_pat:
  | p = cons_pat { p }
  | a = cons_pat EQEQ b = cons_pat { pnode (mkloc $loc) "==" [ a; b ] }

cons_pat:
  | p = add_pat { p }
  | a = add_pat COLONCOLON b = cons_pat
    { let loc = mkloc $loc in pconstr loc "::" (Some (pat loc (Ppat_tuple [ a; b ]))) }

add_pat:
  | p = mul_pat { p }
  | a = add_pat PLUS b = mul_pat { pnode (mkloc $loc) "+" [ a; b ] }
  | a = add_pat MINUS b = mul_pat { pnode (mkloc $loc) "-" [ a; b ] }
  | a = add_pat PLUSPLUS b = mul_pat { pnode (mkloc $loc) "++" [ a; b ] }

mul_pat:
  | p = pow_pat { p }
  | a = mul_pat STAR b = pow_pat { pnode (mkloc $loc) "*" [ a; b ] }
  | a = mul_pat LAND b = pow_pat { pnode (mkloc $loc) "land" [ a; b ] }
  | a = mul_pat LOR b = pow_pat { pnode (mkloc $loc) "lor" [ a; b ] }
  | a = mul_pat LXOR b = pow_pat { pnode (mkloc $loc) "lxor" [ a; b ] }

pow_pat:
  | p = unary_pat { p }
  | a = unary_pat LSL b = pow_pat { pnode (mkloc $loc) "lsl" [ a; b ] }
  | a = unary_pat LSR b = pow_pat { pnode (mkloc $loc) "lsr" [ a; b ] }
  | a = unary_pat ASR b = pow_pat { pnode (mkloc $loc) "asr" [ a; b ] }

unary_pat:
  | p = app_pat { p }
  | MINUS p = unary_pat
    { match p.ppat_desc with
      | Ppat_constant (Pconst_integer (i, None)) -> pat (mkloc $loc) (Ppat_constant (Pconst_integer ("-" ^ i, None)))
      | _ -> pnode (mkloc $loc) "~-" [ p ] }
  | TILDE p = unary_pat { pnode (mkloc $loc) "lognot" [ p ] }
  | NOT p = unary_pat { pnode (mkloc $loc) "not" [ p ] }

app_pat:
  | p = simple_pat { p }
  | c = UID arg = simple_pat { pconstr (mkloc $loc) c (Some arg) }

simple_pat:
  | UNDERSCORE { pat (mkloc $loc) Ppat_any }
  | x = LID { pat (mkloc $loc) (Ppat_var { txt = x; loc = mkloc $loc }) }
  | c = UID { pconstr (mkloc $loc) c None }
  | TRUE { pconstr (mkloc $loc) "true" None }
  | FALSE { pconstr (mkloc $loc) "false" None }
  | i = INT { pat (mkloc $loc) (Ppat_constant (Pconst_integer (i, None))) }
  | HASH x = LID { pconstr (mkloc $loc) "#" (Some (pat (mkloc $loc(x)) (Ppat_var { txt = x; loc = mkloc $loc(x) }))) }
  | HASH UNDERSCORE { pconstr (mkloc $loc) "#" (Some (pat (mkloc $loc) Ppat_any)) }
  | LPAREN RPAREN { pconstr (mkloc $loc) "()" None }
  | LPAREN p = pattern RPAREN { p }
  | LPAREN p = pattern COLON t = typ RPAREN { pat (mkloc $loc) (Ppat_constraint (p, t)) }
  | LBRACKET ps = separated_list(SEMI, pattern) RBRACKET { plist (mkloc $loc) ps }
  | LBRACE fs = field_pats RBRACE { let fs, closed = fs in pat (mkloc $loc) (Ppat_record (fs, closed)) }

field_pats:
  | f = field_pat { ([ f ], Closed) }
  | f = field_pat SEMI UNDERSCORE { ([ f ], Open) }
  | f = field_pat SEMI fs = field_pats { let l, c = fs in (f :: l, c) }

field_pat:
  | f = LID EQ p = pattern { (lid (mkloc $loc(f)) f, p) }
