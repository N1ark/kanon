(** The names of a Kanon file, for the language server: every occurrence of a
    name in the parse tree of the file, with what it refers to, a local variable
    (a parameter, a pattern variable, ...) or a global definition (a function, a
    node, an operator, ...), following the scoping of the language.

    The parse tree is the one of {!Kanon_parser}, before {!Check} desugars it:
    rule cases are a [match] on [[%kanon.operands]], their names [[@r]]
    attributes on their patterns, operators in patterns constructors named after
    the operator, [#x] the constructor ["#"], and operators in expressions
    applications of identifiers named after them. *)

open Ppxlib

type span = int * int

(** What binds a local variable. *)
type binder_kind =
  | Param of string  (** a parameter of the function *)
  | Spec_operand of string * string
      (** an operand of the spec of the rule, the node of the spec *)
  | Pattern_var
  | Literal_var  (** [#x]: the argument of a literal *)
  | Let_var
  | Let_fn  (** [let f (x : t) = ... in] *)
  | Sort_var of string  (** a variable of a sort, and what binds it *)
  | Node_param of string  (** a named argument of the node *)
  | Constant_param of string  (** the [v] of [constant "c" (v)] *)

type binder = {
  name : string;
  file : string;
  span : span;  (** of its binding occurrence *)
  kind : binder_kind;
  ty : string option;  (** its type, when it is known from the source *)
  note : string option;  (** more about it, e.g. the sort of an operand *)
}

(** A name of the language. *)
type global =
  | Value of string  (** a function or a primitive *)
  | Constr of string  (** a node or a constructor *)
  | Type of string
  | Op of string * int
      (** an operator, as parsed (["~-"] for the prefix [-]), and its arity *)
  | Label of string * string  (** the rule [r] of the function [f] *)
  | Module of string list
      (** the module of a [use], by its files ([+bool.knl] for
          [use builtin "bool"]), existing or not *)

type target = Local of binder | Global of global

type occ = {
  span : span;
  target : target;
  decl : bool;  (** a binding or a definition *)
  in_pattern : bool;
}

(** What the analysis of a file needs to know of its language. *)
type ctx = {
  file : string;
  src : string;  (** the text that was parsed *)
  is_global : string -> bool;  (** a function or a primitive *)
  node_sig : string -> (string list * string list) option;
      (** the types of the arguments of a node or constructor, and its sorts *)
  fn_params : string -> binder list;
      (** the variables of the function [f] that the cases of [extend rule f]
          see: its parameters, and the variables of the sorts of its spec *)
}

let span (loc : Location.t) = (loc.loc_start.pos_cnum, loc.loc_end.pos_cnum)

let text ctx (loc : Location.t) =
  let a, b = span loc in
  let a = max 0 a and b = min b (String.length ctx.src) in
  if b <= a then "" else String.sub ctx.src a (b - a)

(** The types built into Kanon, or generated from the nodes and sorts, which
    have no definition. *)
let builtin_types =
  [ "int"; "bool"; "unit"; "t"; "ty"; "list"; "option"; "nat" ]

(** The constructors built into Kanon. *)
let builtin_constrs = [ "true"; "false"; "()"; "[]"; "::"; "None"; "Some"; "#" ]

(** The operators built into Kanon at every type, which the language cannot
    declare. *)
let builtin_ops = [ "="; "<>" ]

(** Whether [sym], as parsed, is a prefix operator: ["~-"] (the prefix [-]),
    [not], and the symbols that start with [!] (but [!=]), [~] or [?]. *)
let is_prefix_sym sym =
  sym = "not"
  || (sym <> "!="
     && sym <> ""
     && match sym.[0] with '!' | '~' | '?' -> true | _ -> false)

(** The operator [sym] as written in its declaration: [-] for ["~-"]. *)
let written_sym = function "~-" -> "-" | s -> s

(** The operator [op] of a declaration [infix "op"] or [prefix "op"], as parsed.
*)
let parsed_sym ~prefix op = if prefix && op = "-" then "~-" else op

let is_upper s = s <> "" && match s.[0] with 'A' .. 'Z' -> true | _ -> false

let is_word s =
  s <> ""
  && String.for_all
       (function
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
         | _ -> false)
       s

(** The type of the argument of a constructor, in Kanon ([nat] is an [int]). *)
let arg_type t = if t = "nat" then "int" else t

(** The analysis of a file: the occurrences of its names, in the order of the
    source. *)
let analyze ctx (str : structure) : occ list =
  let occs = ref [] in
  let add ?(decl = false) ?(in_pattern = false) loc target =
    let ((a, b) as span) = span loc in
    if b > a && not loc.Location.loc_ghost then
      occs := { span; target; decl; in_pattern } :: !occs
  in
  let global ?decl ?in_pattern loc g = add ?decl ?in_pattern loc (Global g) in
  let binder ?ty ?note kind name (loc : Location.t) =
    let b = { name; file = ctx.file; span = span loc; kind; ty; note } in
    add ~decl:true
      ~in_pattern:(kind = Pattern_var || kind = Literal_var)
      loc (Local b);
    b
  in
  let rec typ (t : core_type) =
    match t.ptyp_desc with
    | Ptyp_constr ({ txt = Lident x; loc }, args) ->
        if not (List.mem x builtin_types) then global loc (Type x);
        List.iter typ args
    | Ptyp_tuple l -> List.iter typ l
    | Ptyp_arrow (_, a, b) ->
        typ a;
        typ b
    | _ -> ()
  in
  (* the variables in scope: name and binder, innermost first *)
  let lookup env x =
    List.find_map
      (fun (y, b) -> if y = x && b.kind <> Let_fn then Some b else None)
      env
  in
  let lookup_fn env x =
    List.find_map
      (fun (y, b) -> if y = x && b.kind = Let_fn then Some b else None)
      env
  in
  let ident env x loc =
    match lookup env x with
    | Some b -> add loc (Local b)
    | None -> global loc (Value x)
  in
  let constr ?in_pattern c loc =
    if not (List.mem c builtin_constrs) then
      if is_upper c then global ?in_pattern loc (Constr c)
      else global ?in_pattern loc (Op (c, if is_prefix_sym c then 1 else 2))
  in
  (* the operator that [f args] applies, if it is one: the application of an
     operator is that of an identifier after its first operand (or of a prefix
     operator, which is not a name) *)
  let operator f (floc : Location.t) (args : expression list) =
    match args with
    | _ when List.mem f builtin_ops -> None
    | [ _ ] when is_prefix_sym f -> Some (f, 1)
    | [ a; _ ] when floc.loc_start.pos_cnum > a.pexp_loc.loc_start.pos_cnum ->
        Some (f, 2)
    | _ -> None
  in
  (* the binders of a pattern: a variable bound twice, or in both alternatives
     of an or-pattern, is the same variable, bound where it first appears *)
  let pattern ?ty ~kind (p : pattern) =
    let bound = ref [] in
    let var ?ty kind x loc =
      match List.assoc_opt x !bound with
      | Some b -> add ~in_pattern:true loc (Local b)
      | None -> bound := !bound @ [ (x, binder ?ty kind x loc) ]
    in
    let rec go ?ty (p : pattern) =
      match p.ppat_desc with
      | Ppat_var { txt; loc } -> var ?ty kind txt loc
      | Ppat_alias (q, { txt; loc }) ->
          go q;
          var ?ty kind txt loc
      | Ppat_construct
          ({ txt = Lident "#"; _ }, Some (_, { ppat_desc = Ppat_var v; _ })) ->
          var Literal_var v.txt v.loc
      | Ppat_construct ({ txt = Lident c; loc }, arg) ->
          constr ~in_pattern:true c loc;
          Option.iter (fun (_, a) -> go a) arg
      | Ppat_tuple l -> List.iter (fun q -> go q) l
      | Ppat_or (a, b) ->
          go a;
          go b
      | Ppat_record (fs, _) -> List.iter (fun (_, q) -> go q) fs
      | Ppat_constraint (q, t) ->
          typ t;
          go ~ty:(text ctx t.ptyp_loc) q
      | _ -> ()
    in
    go ?ty p;
    !bound
  in
  let label f (attrs : attributes) =
    List.iter
      (fun (a : attribute) ->
        match (a.attr_name.txt, a.attr_payload) with
        | ( "r",
            PStr
              [
                {
                  pstr_desc =
                    Pstr_eval ({ pexp_desc = Pexp_ident { txt; _ }; _ }, _);
                  _;
                };
              ] ) ->
            Option.iter
              (fun f ->
                global ~decl:true a.attr_loc (Label (f, Longident.name txt)))
              f
        | _ -> ())
      attrs
  in
  let rec expr env (e : expression) =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident x; loc } -> ident env x loc
    | Pexp_construct ({ txt = Lident c; loc }, arg) ->
        constr c loc;
        Option.iter (expr env) arg
    | Pexp_apply
        ({ pexp_desc = Pexp_ident { txt = Lident f; loc = floc }; _ }, args) ->
        let args = List.map snd args in
        (match operator f floc args with
        | Some (sym, arity) -> global floc (Op (sym, arity))
        | None when List.mem f builtin_ops -> ()
        | None -> (
            match lookup_fn env f with
            | Some b -> add floc (Local b)
            | None -> global floc (Value f)));
        List.iter (expr env) args
    | Pexp_apply (f, args) ->
        expr env f;
        List.iter (fun (_, a) -> expr env a) args
    | Pexp_let (_, [ vb ], body) -> (
        match vb.pvb_expr.pexp_desc with
        | Pexp_function (params, ret, Pfunction_body fbody) ->
            let name, nloc =
              match vb.pvb_pat.ppat_desc with
              | Ppat_var { txt; loc } -> (txt, loc)
              | _ -> ("", vb.pvb_pat.ppat_loc)
            in
            let ps = fn_params (Param name) params in
            Option.iter (function Pconstraint t -> typ t | _ -> ()) ret;
            expr (List.rev ps @ env) fbody;
            let header =
              text ctx
                {
                  vb.pvb_loc with
                  loc_end =
                    (match ret with
                    | Some (Pconstraint t) -> t.ptyp_loc.loc_end
                    | _ -> (
                        match List.rev params with
                        | p :: _ -> p.pparam_loc.loc_end
                        | [] -> nloc.loc_end));
                }
            in
            let b = binder ~ty:header Let_fn name nloc in
            expr ((name, b) :: env) body
        | _ ->
            expr env vb.pvb_expr;
            let ty =
              match vb.pvb_constraint with
              | Some (Pvc_constraint { typ = t; _ }) ->
                  typ t;
                  Some (text ctx t.ptyp_loc)
              | _ -> None
            in
            (* [let x : t = e]: the type of [x] *)
            let bs = pattern ?ty ~kind:Let_var vb.pvb_pat in
            expr (List.rev bs @ env) body)
    | Pexp_let (_, vbs, body) ->
        List.iter (fun vb -> expr env vb.pvb_expr) vbs;
        expr env body
    | Pexp_match (s, cases) ->
        expr env s;
        List.iter (case None env) cases
    | Pexp_ifthenelse (c, a, b) ->
        expr env c;
        expr env a;
        Option.iter (expr env) b
    | Pexp_sequence (a, b) ->
        expr env a;
        expr env b
    | Pexp_tuple l -> List.iter (expr env) l
    | Pexp_record (fs, w) ->
        List.iter (fun (_, e) -> expr env e) fs;
        Option.iter (expr env) w
    | Pexp_field (e, _) -> expr env e
    | Pexp_constraint (e, t) ->
        expr env e;
        typ t
    | Pexp_assert e -> expr env e
    | Pexp_function (params, _, body) -> (
        let ps = fn_params (Param "") params in
        let env = List.rev ps @ env in
        match body with
        | Pfunction_body b -> expr env b
        | Pfunction_cases (cs, _, _) -> List.iter (case None env) cs)
    | _ -> ()
  and case f env (c : Ppxlib.case) =
    label f c.pc_lhs.ppat_attributes;
    (match c.pc_lhs.ppat_desc with
    | Ppat_tuple (_ :: _ as l) ->
        label f (List.nth l (List.length l - 1)).ppat_attributes
    | _ -> ());
    let bs = pattern ~kind:Pattern_var c.pc_lhs in
    let env = List.rev bs @ env in
    Option.iter (expr env) c.pc_guard;
    expr env c.pc_rhs
  (* the parameters [(x : t)] of a function, as binders, in order *)
  and fn_params kind (params : function_param list) =
    List.filter_map
      (fun (p : function_param) ->
        match p.pparam_desc with
        | Pparam_val
            ( _,
              _,
              {
                ppat_desc = Ppat_constraint ({ ppat_desc = Ppat_var v; _ }, t);
                _;
              } ) ->
            typ t;
            Some (v.txt, binder ~ty:(text ctx t.ptyp_loc) kind v.txt v.loc)
        | Pparam_val (_, _, { ppat_desc = Ppat_var v; _ }) ->
            Some (v.txt, binder kind v.txt v.loc)
        | _ -> None)
      params
  in
  (* a sort, in a spec or a typing: its free names are variables, bound where
     they first appear (in [bound]) *)
  let rec sort ~what ~bound ~env ?ty (e : expression) =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident x; loc } -> (
        match lookup (!bound @ env) x with
        | Some b -> add loc (Local b)
        | None when ctx.is_global x -> global loc (Value x)
        | None ->
            let ty = Option.value ty ~default:"ty" in
            bound := (x, binder ~ty (Sort_var what) x loc) :: !bound)
    | Pexp_construct ({ txt = Lident c; loc }, arg) ->
        constr c loc;
        let args =
          match arg with
          | Some { pexp_desc = Pexp_tuple l; _ } -> l
          | Some a -> [ a ]
          | None -> []
        in
        let tys =
          match ctx.node_sig c with Some (tys, _) -> tys | None -> []
        in
        List.iteri
          (fun i a ->
            let ty = Option.map arg_type (List.nth_opt tys i) in
            sort ~what ~bound ~env ?ty a)
          args
    | Pexp_apply
        ({ pexp_desc = Pexp_ident { txt = Lident f; loc = floc }; _ }, args) ->
        let args = List.map snd args in
        (match operator f floc args with
        | Some (sym, arity) -> global floc (Op (sym, arity))
        | None when List.mem f builtin_ops -> ()
        | None -> global floc (Value f));
        List.iter (sort ~what ~bound ~env ~ty:"int") args
    | Pexp_tuple l -> List.iter (sort ~what ~bound ~env ?ty) l
    | _ -> expr (!bound @ env) e
  in
  (* the attributes of a node or constructor that name functions or types *)
  let decl_attrs (attrs : attributes) =
    List.iter
      (fun (a : attribute) ->
        let args =
          match a.attr_payload with
          | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> (
              match e.pexp_desc with Pexp_tuple l -> l | _ -> [ e ])
          | _ -> []
        in
        let names =
          List.filter_map
            (fun (e : expression) ->
              match e.pexp_desc with
              | Pexp_constant (Pconst_string (s, _, _)) -> Some (s, e.pexp_loc)
              | _ -> None)
            args
        in
        match (a.attr_name.txt, names) with
        | ("fold" | "get"), _ ->
            (* functions, and the nodes that lift the results of [[@fold]] *)
            List.iter
              (fun (s, loc) ->
                if is_upper s then global loc (Constr s)
                else if is_word s then global loc (Value s))
              names
        | _ -> ())
      attrs
  in
  (* a node, or a constructor of a type *)
  let constructor (cd : constructor_declaration) =
    let name = cd.pcd_name.txt in
    global ~decl:true cd.pcd_name.loc (Constr name);
    let tys =
      match cd.pcd_args with
      | Pcstr_tuple l ->
          List.iter typ l;
          List.map (fun (t : core_type) -> text ctx t.ptyp_loc) l
      | Pcstr_record ls ->
          List.iter (fun (l : label_declaration) -> typ l.pld_type) ls;
          []
    in
    decl_attrs cd.pcd_attributes;
    let payload n =
      List.find_map
        (fun (a : attribute) ->
          match a.attr_payload with
          | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]
            when a.attr_name.txt = n ->
              Some (match e.pexp_desc with Pexp_tuple l -> l | _ -> [ e ])
          | _ -> None)
        cd.pcd_attributes
    in
    (* the typing: the names of the arguments, then the sorts and the
       condition *)
    let params =
      List.concat
        (List.mapi
           (fun i (e : expression) ->
             match e.pexp_desc with
             | Pexp_ident { txt = Lident x; loc } when x <> "_" ->
                 let ty = Option.map arg_type (List.nth_opt tys i) in
                 [ (x, binder ?ty (Node_param name) x loc) ]
             | _ -> [])
           (Option.value (payload "params") ~default:[]))
    in
    let bound = ref [] in
    let what = Printf.sprintf "the typing of `%s`" name in
    List.iter
      (sort ~what ~bound ~env:params)
      (Option.value (payload "sorts") ~default:[]);
    List.iter
      (expr (!bound @ params))
      (Option.value (payload "when") ~default:[])
  in
  let string_payload name (attrs : attributes) =
    List.find_map
      (fun (a : attribute) ->
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
            ]
          when a.attr_name.txt = name ->
            Some (s, pexp_loc)
        | _ -> None)
      attrs
  in
  let rec item (si : structure_item) =
    match si.pstr_desc with
    | Pstr_value (_, [ vb ]) -> (
        let name, nloc =
          match vb.pvb_pat.ppat_desc with
          | Ppat_var { txt; loc } -> (txt, loc)
          | _ -> ("", vb.pvb_pat.ppat_loc)
        in
        global ~decl:true nloc (Value name);
        let spec =
          List.find_map
            (fun (a : attribute) ->
              match a.attr_payload with
              | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]
                when a.attr_name.txt = "spec" ->
                  Some e
              | _ -> None)
            vb.pvb_attributes
        in
        Option.iter
          (function
            | Pvc_constraint { typ = t; _ } -> typ t | Pvc_coercion _ -> ())
          vb.pvb_constraint;
        let params, ret, body =
          match vb.pvb_expr.pexp_desc with
          | Pexp_function (params, ret, Pfunction_body b) -> (params, ret, b)
          | _ -> ([], None, vb.pvb_expr)
        in
        let ps = fn_params (Param name) params in
        Option.iter (function Pconstraint t -> typ t | _ -> ()) ret;
        (* the variables of the sorts of the parameters, [(v : TBitVector n)] *)
        let bound = ref [] in
        List.iter
          (fun (p : function_param) ->
            match p.pparam_desc with
            | Pparam_val
                ( _,
                  _,
                  {
                    ppat_desc =
                      Ppat_constraint
                        ({ ppat_desc = Ppat_var v; _ }, { ptyp_attributes; _ });
                    _;
                  } ) ->
                List.iter
                  (fun (a : attribute) ->
                    match a.attr_payload with
                    | PStr [ { pstr_desc = Pstr_eval (s, _); _ } ]
                      when a.attr_name.txt = "kanon.sort" ->
                        let what = Printf.sprintf "the sort of `%s`" v.txt in
                        sort ~what ~bound ~env:[] s
                    | _ -> ())
                  ptyp_attributes
            | _ -> ())
          params;
        let env = List.rev ps @ List.rev !bound in
        let env =
          match spec with
          | None -> env
          | Some spec when params <> [] ->
              expr env spec;
              env
          | Some spec -> List.rev (spec_operands name spec) @ env
        in
        match body.pexp_desc with
        | Pexp_match
            ( {
                pexp_desc = Pexp_extension ({ txt = "kanon.operands"; _ }, _);
                _;
              },
              cases ) ->
            List.iter
              (case (if Option.is_some spec then Some name else None) env)
              cases
        | _ -> expr env body)
    | Pstr_extension
        ( ( { txt = "kanon.use"; _ },
            PStr
              [
                {
                  pstr_desc =
                    Pstr_eval
                      ( {
                          pexp_desc = Pexp_constant (Pconst_string (m, _, _));
                          pexp_loc;
                          _;
                        },
                        _ );
                  _;
                };
              ] ),
          _ ) ->
        (* the module of [use "m"] or [use builtin "m"], at its name *)
        global pexp_loc
          (Module (snd (Loader.module_files (Filename.dirname ctx.file) m)))
    | Pstr_primitive vd ->
        global ~decl:true vd.pval_name.loc (Value vd.pval_name.txt);
        typ vd.pval_type
    | Pstr_type
        ( _,
          [
            {
              ptype_name = { txt = "node"; _ };
              ptype_kind = Ptype_variant [ cd ];
              ptype_attributes;
              _;
            };
          ] )
      when List.exists
             (fun (a : attribute) -> a.attr_name.txt = "node")
             ptype_attributes ->
        constructor cd
    | Pstr_type (_, tds) ->
        List.iter
          (fun (td : type_declaration) ->
            global ~decl:true td.ptype_name.loc (Type td.ptype_name.txt);
            match td.ptype_kind with
            | Ptype_variant cds -> List.iter constructor cds
            | Ptype_record ls ->
                List.iter (fun (l : label_declaration) -> typ l.pld_type) ls
            | _ -> ())
          tds
    | Pstr_eval (e, attrs) -> (
        let op =
          match string_payload "infix" attrs with
          | Some (op, loc) -> Some (op, loc, false)
          | None ->
              Option.map
                (fun (op, loc) -> (op, loc, true))
                (string_payload "prefix" attrs)
        in
        match
          (op, string_payload "constant" attrs, string_payload "extend" attrs)
        with
        | Some (op, loc, prefix), _, _ ->
            global ~decl:true loc
              (Op (parsed_sym ~prefix op, if prefix then 1 else 2));
            expr [] e
        | None, Some (c, _), _ -> (
            match e.pexp_desc with
            | Pexp_function
                ( [
                    {
                      pparam_desc =
                        Pparam_val (_, _, { ppat_desc = Ppat_var v; _ });
                      _;
                    };
                  ],
                  _,
                  Pfunction_body body ) ->
                let b = binder ~ty:"t" (Constant_param c) v.txt v.loc in
                expr [ (v.txt, b) ] body
            | _ -> expr [] e)
        | None, None, Some (f, floc) -> (
            global floc (Value f);
            let is_rule =
              not
                (List.exists
                   (fun (a : attribute) -> a.attr_name.txt = "fn")
                   attrs)
            in
            Option.iter
              (fun (r, rloc) -> global rloc (Label (f, r)))
              (string_payload "before" attrs);
            let env = List.rev_map (fun b -> (b.name, b)) (ctx.fn_params f) in
            match e.pexp_desc with
            | Pexp_function (_, _, Pfunction_cases (cs, _, _)) ->
                List.iter (case (if is_rule then Some f else None) env) cs
            | _ -> expr env e)
        | None, None, None -> expr [] e)
    | _ -> ()
  (* the operands of the spec [C (x1, ..., xn)] of the rule [f], which are its
     parameters, with the variables of their sorts *)
  and spec_operands f (spec : expression) =
    match spec.pexp_desc with
    | Pexp_construct ({ txt = Lident c; loc }, arg) ->
        constr c loc;
        let args =
          match arg with
          | Some { pexp_desc = Pexp_tuple l; _ } -> l
          | Some a -> [ a ]
          | None -> []
        in
        let tys, sorts =
          match ctx.node_sig c with Some s -> s | None -> ([], [])
        in
        let nparams = List.length tys in
        let bound = ref [] in
        let operand i (v : expression) ?annot () =
          match v.pexp_desc with
          | Pexp_ident { txt = Lident x; loc } ->
              let ty, sort =
                if i < nparams then
                  (Option.map arg_type (List.nth_opt tys i), None)
                else (Some "t", List.nth_opt sorts (i - nparams))
              in
              let note =
                match (annot, sort) with
                | Some a, _ -> Some (Printf.sprintf "a term of sort `%s`" a)
                | None, Some s -> Some (Printf.sprintf "a term of sort `%s`" s)
                | None, None -> None
              in
              [ (x, binder ?ty ?note (Spec_operand (f, c)) x loc) ]
          | _ ->
              expr [] v;
              []
        in
        let ops =
          List.concat
            (List.mapi
               (fun i (a : expression) ->
                 match a.pexp_desc with
                 | Pexp_extension
                     ( { txt = "kanon.sort"; _ },
                       PStr
                         [
                           { pstr_desc = Pstr_eval (v, _); _ };
                           { pstr_desc = Pstr_eval (s, _); _ };
                         ] ) ->
                     let bs = operand i v ~annot:(text ctx s.pexp_loc) () in
                     let what =
                       Printf.sprintf "the sort of `%s`"
                         (match bs with (x, _) :: _ -> x | [] -> "")
                     in
                     sort ~what ~bound ~env:[] s;
                     bs
                 | _ -> operand i a ())
               args)
        in
        ops @ List.rev !bound
    | _ ->
        expr [] spec;
        []
  in
  List.iter item str;
  List.sort (fun (a : occ) b -> compare a.span b.span) !occs

(** The variables of the function [f] of [str] that the cases of [extend rule f]
    see: its parameters, or the operands of its spec, and the variables of their
    sorts. *)
let fn_binders ctx (str : structure) f =
  List.find_map
    (fun (si : structure_item) ->
      match si.pstr_desc with
      | Pstr_value
          (_, [ { pvb_pat = { ppat_desc = Ppat_var { txt; _ }; _ }; _ } ])
        when txt = f ->
          Some
            (List.filter_map
               (fun o ->
                 match o.target with
                 | Local b when o.decl -> (
                     match b.kind with
                     | (Param g | Spec_operand (g, _)) when g = f -> Some b
                     | Sort_var _ -> Some b
                     | _ -> None)
                 | _ -> None)
               (analyze { ctx with fn_params = (fun _ -> []) } [ si ]))
      | _ -> None)
    str
  |> Option.value ~default:[]
