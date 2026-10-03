(* The grammar of Kanon. It builds an OCaml parse tree, which [Check] then
   converts to typed Kanon: rules become functions with [[@spec]] and [[@cases]]
   attributes, and rule names [[@r]] attributes on their patterns. In the
   declaration of a language, types are OCaml type declarations, nodes are types
   [node] with a [[@node]] attribute (and sorts with a [[@sort]] one too), and
   operators [[@infix]] or [[@prefix]] expressions; [extend rule f] and [extend fn f] items are [function]s of the
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

(** Whether [s] is a word, which an infix operator may be. *)
let is_word s =
  s <> ""
  && (match s.[0] with 'a' .. 'z' -> true | _ -> false)
  && String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true | _ -> false) s

(** Declares [op], if it is a word, as an operator that the lexer reads in the
    rest of the files ([urem]): it is an identifier otherwise. *)
let declare_word_op op = if is_word op then Hashtbl.replace Syntax.infix_words op ()

(* [oploc] is the location of the operator, [loc] that of the expression *)
let binop loc oploc op a b = apply loc (ident oploc op) [ a; b ]

(* [cloc] is the location of the constructor, [loc] that of the expression *)
let econstr ?cloc loc c arg = exp loc (Pexp_construct (lid (Option.value cloc ~default:loc) c, arg))
let pconstr ?cloc loc c arg =
  pat loc (Ppat_construct (lid (Option.value cloc ~default:loc) c, Option.map (fun p -> ([], p)) arg))
(* The type that the expression [e] reads as, [int list] or [t], if any: a
   constraint [(e : t)] is parsed as an expression, since [(C x : f y)] has an
   expression for sort. *)
let rec typ_of_expr (e : expression) =
  let constr x t = typ e.pexp_loc (Ptyp_constr (lid e.pexp_loc x, t)) in
  match e.pexp_desc with
  | Pexp_ident { txt = Lident x; _ } -> Some (constr x [])
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident "*"; _ }; _ }, [ (_, a); (_, b) ]) -> (
      match (typ_of_expr a, typ_of_expr b) with
      | Some ({ ptyp_desc = Ptyp_tuple l; _ } as ta), Some tb when a.pexp_loc.loc_start = e.pexp_loc.loc_start ->
          Some { ta with ptyp_desc = Ptyp_tuple (l @ [ tb ]); ptyp_loc = e.pexp_loc }
      | Some ta, Some tb -> Some (typ e.pexp_loc (Ptyp_tuple [ ta; tb ]))
      | _ -> None)
  | Pexp_apply (f, args) ->
      List.fold_left
        (fun acc (_, (a : expression)) ->
          match (acc, a.pexp_desc) with
          | Some t, Pexp_ident { txt = Lident x; _ } -> Some (typ e.pexp_loc (Ptyp_constr (lid a.pexp_loc x, [ t ])))
          | _ -> None)
        (typ_of_expr f) args
  | _ -> None

let tuple_or_one mk = function [ x ] -> x | l -> mk l

let attr loc name payload =
  { attr_name = { txt = name; loc }; attr_payload = PStr payload; attr_loc = loc }

(* an attribute whose name is at [nloc] *)
let named_attr loc nloc name payload =
  { attr_name = { txt = name; loc = nloc }; attr_payload = PStr payload; attr_loc = loc }

let eval_item loc e = { pstr_desc = Pstr_eval (e, []); pstr_loc = loc }
let string loc s = exp loc (Pexp_constant (Pconst_string (s, loc, None)))

(* the positions of the contents of a string token, without its quotes *)
let unquote ((s : Lexing.position), (e : Lexing.position)) =
  ({ s with pos_cnum = s.pos_cnum + 1 }, { e with pos_cnum = max (s.pos_cnum + 1) (e.pos_cnum - 1) })

(* a parameter [(x : t)], where [x] is at [xpos] *)
let param (x, xpos, (t : core_type)) =
  let xloc = mkloc xpos in
  let loc = { xloc with loc_end = t.ptyp_loc.loc_end } in
  {
    pparam_loc = loc;
    pparam_desc =
      Pparam_val (Nolabel, None, pat loc (Ppat_constraint (pat xloc (Ppat_var { txt = x; loc = xloc }), t)));
  }

(* A function: its parameters, if any, and its result type, if given. *)
let fn_expr loc params ret body =
  match params with
  | [] -> body
  | _ ->
      exp loc
        (Pexp_function
           (List.map param params, Option.map (fun t -> Pconstraint t) ret, Pfunction_body body))

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

(* [use "m"], with the module at [mloc] *)
let use_item loc mloc m =
  item loc (Pstr_extension (({ txt = "kanon.use"; loc }, PStr [ eval_item loc (string mloc m) ]), []))

(* [node C ...] in the declaration of a language: a type [node] with the only
   constructor [C], which [Check] places where [C] appears in a type; [sort C
   ...] is the same, marked [[@sort]] *)
let node_decl ?(sort = false) loc c =
  {
    ptype_name = { txt = "node"; loc };
    ptype_params = [];
    ptype_cstrs = [];
    ptype_kind = Ptype_variant [ c ];
    ptype_private = Public;
    ptype_manifest = None;
    ptype_attributes = attr loc "node" [] :: (if sort then [ attr loc "sort" [] ] else []);
    ptype_loc = loc;
  }

let prim loc (name, nloc) t attrs kind =
  item loc
    (Pstr_primitive
       { pval_name = { txt = name; loc = nloc }; pval_type = t; pval_prim = [ kind ]; pval_attributes = attrs; pval_loc = loc })

(* the doc comment [d], at [dloc], of an item that it documents: an
   [ocaml.doc] attribute of the item, or of the constructor of a node or a sort *)
let with_doc d dloc (si : structure_item) =
  let doc = attr dloc "ocaml.doc" [ eval_item dloc (string dloc d) ] in
  let desc =
    match si.pstr_desc with
    | Pstr_value (r, [ vb ]) -> Pstr_value (r, [ { vb with pvb_attributes = vb.pvb_attributes @ [ doc ] } ])
    | Pstr_primitive vd -> Pstr_primitive { vd with pval_attributes = vd.pval_attributes @ [ doc ] }
    | Pstr_type (r, [ ({ ptype_kind = Ptype_variant [ cd ]; ptype_name = { txt = "node"; _ }; _ } as td) ])
      when List.exists (fun (a : attribute) -> a.attr_name.txt = "node") td.ptype_attributes ->
        let cd = { cd with pcd_attributes = cd.pcd_attributes @ [ doc ] } in
        Pstr_type (r, [ { td with ptype_kind = Ptype_variant [ cd ] } ])
    | Pstr_type (r, [ td ]) -> Pstr_type (r, [ { td with ptype_attributes = td.ptype_attributes @ [ doc ] } ])
    | Pstr_eval (e, attrs) -> Pstr_eval (e, attrs @ [ doc ])
    | _ -> assert false
  in
  { si with pstr_desc = desc }

let misplaced loc what =
  raise (Syntax.Misplaced_doc (loc, "a doc comment cannot document " ^ what))

let rec elist loc = function
  | [] -> econstr loc "[]" None
  | x :: l -> econstr loc "::" (Some (exp loc (Pexp_tuple [ x; elist loc l ])))

let rec plist loc = function
  | [] -> pconstr loc "[]" None
  | x :: l -> pconstr loc "::" (Some (pat loc (Ppat_tuple [ x; plist loc l ])))

(* An operator on terms in a pattern, which [Check] replaces with the node that
   the language declares for it; [oploc] is the location of the operator. *)
let pnode loc oploc op args = pconstr ~cloc:oploc loc op (Some (tuple_or_one (fun l -> pat loc (Ppat_tuple l)) args))

(* The payload of an attribute [[@a "s1" ... "sn"]], each string at its own
   location *)
let strings loc = function
  | [] -> []
  | [ (s, l) ] -> [ eval_item loc (string (mkloc l) s) ]
  | l -> [ eval_item loc (exp loc (Pexp_tuple (List.map (fun (s, l) -> string (mkloc l) s) l))) ]

let neg loc oploc (e : expression) =
  match e.pexp_desc with
  | Pexp_constant (Pconst_integer (s, None)) -> exp loc (Pexp_constant (Pconst_integer ("-" ^ s, None)))
  | _ -> apply loc (ident oploc "~-") [ e ]
%}

%token <string> LID UID INT STRING INFIXWORD
(* the text of a doc comment [(** ... *)], which documents the item that follows *)
%token <string> DOC
(* the operators, by precedence (see the lexer) *)
%token <string> CMPOP CONCATOP ADDOP MULOP POWOP PREFIXOP
%token AS ASSERT BEFORE BUILTIN CONSTANT ELSE EXTEND FALSE FN IF IN INFIX LET MATCH NODE NOT NOTATION OF
%token ORACLE PREFIX PRIM
%token RULE SORT THEN TRUE TYPE USE WHEN WITH
%token LBRACKETAT LBRACKETATATAT COLONCOLON ARROW ANDAND BARBAR
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COMMA SEMI COLON BAR EQ PLUS MINUS UMINUS STAR DOT
%token HASH UNDERSCORE EOF

(* the bodies of [let], [match] and [if] extend as far as possible *)
%nonassoc below_SEMI
%nonassoc SEMI
%nonassoc below_BAR
%nonassoc BAR
%nonassoc below_COMMA
%nonassoc COMMA
%nonassoc below_BARBAR
%nonassoc BARBAR
(* [!x.f] is [!(x.f)] *)
%nonassoc below_DOT
%nonassoc DOT

%start <Ppxlib.structure> file

%%

file:
  | items = items EOF { List.rev items }
  | items = items d = DOC EOF { ignore items; raise (Syntax.Misplaced_doc (mkloc $loc(d), "this doc comment is not followed by an item to document")) }

(* left-recursive, so that a doc comment can end the file *)
items:
  | { [] }
  | l = items i = item { i :: l }

(* a doc comment documents the item that follows it: [fn], [rule], [node],
   [sort], [type], [prim], [oracle], [infix], [prefix] and [constant] *)
item:
  | i = documented_item { i }
  | d = DOC i = documented_item { with_doc d (mkloc $loc(d)) i }
  | i = other_item { i }
  | d = DOC other_item { misplaced (mkloc $loc(d)) "this item: only fn, rule, node, sort, type, prim, oracle, infix, prefix and constant can have one" }

other_item:
  (* [use builtin "m"] or [use "path"]: the module [m] built into kanon, which
     the loader names [+m], or the module whose files are [path.knl] and
     [path.kn] (see [Main]) *)
  | USE BUILTIN m = STRING { use_item (mkloc $loc) (mkloc (unquote $loc(m))) ("+" ^ m) }
  | USE m = STRING { use_item (mkloc $loc) (mkloc (unquote $loc(m))) m }
  | EXTEND fn = extended x = LID before = option(before) EQ BAR? cs = cases
    { let loc = mkloc $loc in
      (* the payloads are at the names of the function and of the rule *)
      let attrs =
        attr loc "extend" [ eval_item loc (string (mkloc $loc(x)) x) ]
        :: Option.to_list (Option.map (fun (r, rloc) -> attr loc "before" [ eval_item loc (string (mkloc rloc) r) ]) before)
        @ (if fn then [ attr loc "fn" [] ] else [])
      in
      item loc (Pstr_eval (exp loc (Pexp_function ([], None, Pfunction_cases (cs, loc, []))), attrs)) }
  (* [notation C]: the constructor [C], with a [[@notation]] attribute *)
  | NOTATION c = UID
    { let loc = mkloc $loc in
      item loc (Pstr_eval (econstr (mkloc $loc(c)) c None, [ attr loc "notation" [] ])) }
  | LBRACKETATATAT a = LID ss = list(attr_string) RBRACKET
    { let loc = mkloc $loc in
      item loc (Pstr_attribute (named_attr loc (mkloc $loc(a)) a (strings loc ss))) }

documented_item:
  | PRIM x = LID COLON t = typ attrs = list(decl_attr) { prim (mkloc $loc) (x, mkloc $loc(x)) t attrs "" }
  | ORACLE x = LID COLON t = typ attrs = list(decl_attr) { prim (mkloc $loc) (x, mkloc $loc(x)) t attrs "oracle" }
  | FN x = LID ps = params ret = option(preceded(COLON, typ)) attrs = list(decl_attr) EQ body = seq_expr
    { let loc = mkloc $loc and xloc = mkloc $loc(x) in
      item loc (Pstr_value (Nonrecursive, [ binding loc ~attrs (pat xloc (Ppat_var { txt = x; loc = xloc })) ps ret body ])) }
  | RULE x = LID ps = params COLON spec = concat_expr rattrs = list(decl_attr) body = option(rule_body)
    { let loc = mkloc $loc in
      (* the cases of a rule match the operands of its spec ([kanon.operands],
         see [Check.raw_fn]); a rule without a body only has the rules from laws
         and [default] *)
      let operands = exp loc (Pexp_extension ({ txt = "kanon.operands"; loc }, PStr [])) in
      let body =
        match body with
        | Some (`Cases cs) -> exp loc (Pexp_match (operands, cs))
        | Some (`Expr e) -> e
        | None -> exp loc (Pexp_match (operands, []))
      in
      let attrs = [ attr loc "spec" [ eval_item loc spec ]; attr loc "cases" [] ] @ rattrs in
      (* the result type, which the source does not write *)
      let tloc = { loc with loc_ghost = true } in
      let t = typ tloc (Ptyp_constr (lid tloc "t", [])) in
      let xloc = mkloc $loc(x) in
      item loc (Pstr_value (Nonrecursive, [ binding loc ~attrs (pat xloc (Ppat_var { txt = x; loc = xloc })) ps (Some t) body ])) }
  | NODE c = constr_decl
    { let loc = mkloc $loc in
      item loc (Pstr_type (Recursive, [ node_decl loc c ])) }
  | SORT c = constr_decl
    { let loc = mkloc $loc in
      item loc (Pstr_type (Recursive, [ node_decl ~sort:true loc c ])) }
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
      declare_word_op op;
      item loc (Pstr_eval (e, [ attr loc "infix" [ eval_item loc (string (mkloc (unquote $loc(op))) op) ] ])) }
  | PREFIX op = STRING EQ e = seq_expr
    { let loc = mkloc $loc in
      item loc (Pstr_eval (e, [ attr loc "prefix" [ eval_item loc (string (mkloc (unquote $loc(op))) op) ] ])) }
  (* [constant c (v) = e], a function of [v], or [constant c = e], where [c] is
     a literal or a name (or a string, as before) *)
  | CONSTANT c = constant_name v = option(delimited(LPAREN, param_name, RPAREN)) EQ e = seq_expr
    { let loc = mkloc $loc in
      let f =
        match v with
        | None -> e
        | Some (v, vpos) ->
            let vloc = mkloc vpos in
            let v = { pparam_loc = vloc; pparam_desc = Pparam_val (Nolabel, None, pat vloc (Ppat_var { txt = v; loc = vloc })) } in
            exp loc (Pexp_function ([ v ], None, Pfunction_body e))
      in
      let c, cpos = c in
      item loc (Pstr_eval (f, [ attr loc "constant" [ eval_item loc (string (mkloc cpos) c) ] ])) }

(* ---------------------------------------------------------------- *)
(* Declarations of the language *)

(* the name of an attribute is at its own location, as is each argument *)
decl_attr:
  | LBRACKETAT a = LID ss = list(attr_arg) RBRACKET
    { named_attr (mkloc $loc) (mkloc $loc(a)) a (strings (mkloc $loc) ss) }

attr_string:
  | s = STRING { (s, unquote $loc) }

constant_name:
  | s = attr_string { s }
  | s = LID { (s, $loc) }
  | i = INT { (i, $loc) }
  | TRUE { ("true", $loc) }
  | FALSE { ("false", $loc) }

(* the arguments of attributes: strings, or names (of functions and of
   constructors) and literals, unquoted *)
attr_arg:
  | s = attr_string { s }
  | s = LID { (s, $loc) }
  | s = UID { (s, $loc) }
  | i = INT { (i, $loc) }
  | TRUE { ("true", $loc) }
  | FALSE { ("false", $loc) }

type_kind:
  | BAR? cs = separated_nonempty_list(BAR, constr_decl) { Ptype_variant cs }
  | LBRACE fs = separated_nonempty_list(SEMI, label_decl) RBRACE { Ptype_record fs }

(* [C of a * b (x, y) : s1 -> s2 when e]: the names of the arguments, the
   sorts of the operands and result, and a side condition, as [[@params]],
   [[@sorts]] and [[@when]] attributes *)
constr_decl:
  | c = UID args = loption(preceded(OF, separated_nonempty_list(STAR, typ_app)))
    ps = option(constr_params) sorts = option(preceded(COLON, separated_nonempty_list(ARROW, typing_sort)))
    g = option(preceded(WHEN, expr)) attrs = list(decl_attr)
    { let loc = mkloc $loc in
      let tuple l = tuple_or_one (fun l -> exp loc (Pexp_tuple l)) l in
      (* the attributes are at the names, the sorts and the condition *)
      let typing =
        Option.to_list (Option.map (fun ps -> attr (mkloc $loc(ps)) "params" [ eval_item loc (tuple ps) ]) ps)
        @ Option.to_list (Option.map (fun ss -> attr (mkloc $loc(sorts)) "sorts" [ eval_item loc (tuple ss) ]) sorts)
        @ Option.to_list (Option.map (fun (g : expression) -> attr g.pexp_loc "when" [ eval_item loc g ]) g)
      in
      {
        pcd_name = { txt = c; loc = mkloc $loc(c) };
        pcd_vars = [];
        pcd_args = Pcstr_tuple args;
        pcd_res = None;
        pcd_loc = loc;
        pcd_attributes = typing @ attrs;
      } }

(* a sort, or a list of terms of a sort: [a list] and [TBool list] are
   applications, as is [(TBitVector n) list] *)
typing_sort:
  | e = app_expr { e }
  | LPAREN e = seq_expr RPAREN l = LID { apply (mkloc $loc) e [ ident (mkloc $loc(l)) l ] }

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
  | LPAREN xs = nonempty_list(param_name) COLON t = typ RPAREN { List.map (fun (x, l) -> (x, l, t)) xs }
  (* [(v : TBitVector n)]: terms of a sort, the type [t] with a [[@kanon.sort]]
     attribute *)
  | LPAREN xs = nonempty_list(param_name) COLON c = UID arg = option(simple_expr) RPAREN
    { let sloc = mkloc ($startpos(c), $endpos(arg)) in
      let s = econstr ~cloc:(mkloc $loc(c)) sloc c arg in
      let tloc = { sloc with loc_ghost = true } in
      let t = { (typ tloc (Ptyp_constr (lid tloc "t", []))) with ptyp_attributes = [ attr sloc "kanon.sort" [ eval_item sloc s ] ] } in
      List.map (fun (x, l) -> (x, l, t)) xs }

param_name:
  | x = LID { (x, $loc) }
  | UNDERSCORE { ("_", $loc) }

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
  | t = typ_app x = LID { typ (mkloc $loc) (Ptyp_constr (lid (mkloc $loc(x)) x, [ t ])) }

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
    { let loc = mkloc $loc(f) in (pat loc (Ppat_var { txt = f; loc }), List.concat ps, ret) }
  | p = pattern { (p, [], None) }
  | p = pattern COLON t = typ { (p, [], Some t) }

rule_body:
  | EQ BAR cs = cases { `Cases cs }
  | EQ e = seq_expr { `Expr e }

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

before:
  | BEFORE r = rule_name { (r, $loc(r)) }

rule_name:
  | r = LID { r }
  | r = INFIXWORD { r }
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
  | a = and_expr op = BARBAR b = or_rhs { binop (mkloc $loc) (mkloc $loc(op)) "||" a b }

or_rhs:
  | e = or_expr { e }
  | e = open_expr { e }

and_expr:
  | e = cmp_expr { e }
  | a = cmp_expr op = ANDAND b = and_rhs { binop (mkloc $loc) (mkloc $loc(op)) "&&" a b }

and_rhs:
  | e = and_expr { e }
  | e = open_expr { e }

cmp_expr:
  | e = concat_expr { e }
  | a = cmp_expr op = cmp_op b = concat_expr { binop (mkloc $loc) (mkloc $loc(op)) op a b }

cmp_op:
  | EQ { "=" }
  | op = CMPOP { op }

concat_expr:
  | e = cons_expr { e }
  | a = cons_expr op = CONCATOP b = concat_expr { binop (mkloc $loc) (mkloc $loc(op)) op a b }

cons_expr:
  | e = add_expr { e }
  | a = add_expr COLONCOLON b = cons_expr
    { let loc = mkloc $loc in econstr loc "::" (Some (exp loc (Pexp_tuple [ a; b ]))) }

add_expr:
  | e = mul_expr { e }
  | a = add_expr op = add_op b = mul_expr { binop (mkloc $loc) (mkloc $loc(op)) op a b }

add_op:
  | PLUS { "+" }
  | MINUS { "-" }
  | op = ADDOP { op }

mul_expr:
  | e = pow_expr { e }
  | a = mul_expr op = mul_op b = pow_expr { binop (mkloc $loc) (mkloc $loc(op)) op a b }

mul_op:
  | STAR { "*" }
  | op = MULOP { op }
  (* the words declared infix, as OCaml's [mod] or [land] *)
  | op = INFIXWORD { op }

pow_expr:
  | e = unary_expr { e }
  | a = unary_expr op = POWOP b = pow_expr { binop (mkloc $loc) (mkloc $loc(op)) op a b }

unary_expr:
  | e = app_expr { e }
  | op = UMINUS e = unary_expr { neg (mkloc $loc) (mkloc $loc(op)) e }

app_expr:
  | e = simple_expr { e }
  | f = LID args = nonempty_list(simple_expr) { apply (mkloc $loc) (ident (mkloc $loc(f)) f) args }
  | c = UID arg = simple_expr { econstr ~cloc:(mkloc $loc(c)) (mkloc $loc) c (Some arg) }
  | ASSERT e = simple_expr { exp (mkloc $loc) (Pexp_assert e) }
  | op = NOT e = simple_expr { apply (mkloc $loc) (ident (mkloc $loc(op)) "not") [ e ] }

simple_expr:
  | x = LID { ident (mkloc $loc) x }
  | c = UID { econstr (mkloc $loc) c None }
  | TRUE { econstr (mkloc $loc) "true" None }
  | FALSE { econstr (mkloc $loc) "false" None }
  | i = INT { exp (mkloc $loc) (Pexp_constant (Pconst_integer (i, None))) }
  | LPAREN RPAREN { econstr (mkloc $loc) "()" None }
  | LPAREN e = seq_expr RPAREN { e }
  (* [(e : a)]: either [e] of the type [a], or, when [a] is not a type, a term
     of a sort: [(v : TBitVector n)] is the sort of an operand of a spec,
     [(C x : S args)] or [(C x : f y)] the node [C] built at a sort *)
  | LPAREN e = seq_expr COLON a = or_expr RPAREN
    { let loc = mkloc $loc in
      let sort () = exp loc (Pexp_extension ({ txt = "kanon.sort"; loc }, PStr [ eval_item loc e; eval_item loc a ])) in
      match a.pexp_desc with
      | Pexp_construct _ -> sort ()
      | _ -> (
          match typ_of_expr a with
          | None -> sort ()
          | Some t ->
              (* [(C x : s)] is a type constraint, or a node at the sort [s]: [Check] decides *)
              let attrs = match e.pexp_desc with Pexp_construct _ -> [ attr loc "kanon.sortexpr" [ eval_item loc a ] ] | _ -> [] in
              { (exp loc (Pexp_constraint (e, t))) with pexp_attributes = attrs }) }
  | LBRACKET es = separated_list(SEMI, expr) RBRACKET { elist (mkloc $loc) es }
  | LBRACE fs = separated_nonempty_list(SEMI, field_expr) RBRACE { exp (mkloc $loc) (Pexp_record (fs, None)) }
  | e = simple_expr DOT f = LID { exp (mkloc $loc) (Pexp_field (e, lid (mkloc $loc(f)) f)) }
  | op = PREFIXOP e = simple_expr %prec below_DOT { apply (mkloc $loc) (ident (mkloc $loc(op)) op) [ e ] }

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
  | a = and_node_pat op = BARBAR b = or_node_pat { pnode (mkloc $loc) (mkloc $loc(op)) "||" [ a; b ] }

and_node_pat:
  | p = cmp_pat { p }
  | a = cmp_pat op = ANDAND b = and_node_pat { pnode (mkloc $loc) (mkloc $loc(op)) "&&" [ a; b ] }

cmp_pat:
  | p = concat_pat { p }
  | a = cmp_pat op = cmp_pat_op b = concat_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ a; b ] }

cmp_pat_op:
  | op = CMPOP { op }

concat_pat:
  | p = cons_pat { p }
  | a = cons_pat op = CONCATOP b = concat_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ a; b ] }

cons_pat:
  | p = add_pat { p }
  | a = add_pat COLONCOLON b = cons_pat
    { let loc = mkloc $loc in pconstr loc "::" (Some (pat loc (Ppat_tuple [ a; b ]))) }

add_pat:
  | p = mul_pat { p }
  | a = add_pat op = add_op b = mul_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ a; b ] }

mul_pat:
  | p = pow_pat { p }
  | a = mul_pat op = mul_op b = pow_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ a; b ] }

pow_pat:
  | p = unary_pat { p }
  | a = unary_pat op = POWOP b = pow_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ a; b ] }

unary_pat:
  | p = app_pat { p }
  | op = UMINUS p = unary_pat
    { match p.ppat_desc with
      | Ppat_constant (Pconst_integer (i, None)) -> pat (mkloc $loc) (Ppat_constant (Pconst_integer ("-" ^ i, None)))
      | _ -> pnode (mkloc $loc) (mkloc $loc(op)) "~-" [ p ] }
  | op = NOT p = unary_pat { pnode (mkloc $loc) (mkloc $loc(op)) "not" [ p ] }

app_pat:
  | p = simple_pat { p }
  | c = UID arg = simple_pat { pconstr ~cloc:(mkloc $loc(c)) (mkloc $loc) c (Some arg) }

simple_pat:
  | UNDERSCORE { pat (mkloc $loc) Ppat_any }
  | x = LID { pat (mkloc $loc) (Ppat_var { txt = x; loc = mkloc $loc }) }
  | c = UID { pconstr (mkloc $loc) c None }
  | TRUE { pconstr (mkloc $loc) "true" None }
  | FALSE { pconstr (mkloc $loc) "false" None }
  | i = INT { pat (mkloc $loc) (Ppat_constant (Pconst_integer (i, None))) }
  | h = HASH x = LID { pconstr ~cloc:(mkloc $loc(h)) (mkloc $loc) "#" (Some (pat (mkloc $loc(x)) (Ppat_var { txt = x; loc = mkloc $loc(x) }))) }
  | HASH UNDERSCORE { pconstr (mkloc $loc) "#" (Some (pat (mkloc $loc) Ppat_any)) }
  | LPAREN RPAREN { pconstr (mkloc $loc) "()" None }
  | LPAREN p = pattern RPAREN { p }
  | LPAREN p = pattern COLON t = typ RPAREN { pat (mkloc $loc) (Ppat_constraint (p, t)) }
  | LBRACKET ps = separated_list(SEMI, pattern) RBRACKET { plist (mkloc $loc) ps }
  | LBRACE fs = field_pats RBRACE { let fs, closed = fs in pat (mkloc $loc) (Ppat_record (fs, closed)) }
  | op = PREFIXOP p = simple_pat { pnode (mkloc $loc) (mkloc $loc(op)) op [ p ] }

field_pats:
  | f = field_pat { ([ f ], Closed) }
  | f = field_pat SEMI UNDERSCORE { ([ f ], Open) }
  | f = field_pat SEMI fs = field_pats { let l, c = fs in (f :: l, c) }

field_pat:
  | f = LID EQ p = pattern { (lid (mkloc $loc(f)) f, p) }
