(** OCaml backend. The output defines every Kanon function, in terms of a module
    [P] of primitives, which must be in scope where it is included. Terms are
    hash-consed ([Hc]) records [{ kind; ty }]. It is not meant to be read. *)

open Syntax

let pf = Format.fprintf

(** The module that defines a type of the language, with a trailing dot: where
    its constructors and fields are. *)
let module_of t =
  let ty = (decl_of_ty t).d_ocaml in
  let last = List.hd (List.rev (String.split_on_char ' ' ty)) in
  match String.rindex_opt last '.' with
  | Some i -> String.sub last 0 (i + 1)
  | None -> ""

let constr_path (c : constr) = module_of c.c_res

(** The module of the fields [kind] and [ty] of terms: that of their kind. *)
let term_path () = module_of TKind

let rec ocaml_ty ft = function
  | TInt -> pf ft "Z.t"
  | TBool -> pf ft "bool"
  | TUnit -> pf ft "unit"
  | TTerm -> pf ft "t"
  | (TKind | TSty | TData _) as t -> pf ft "%s" (decl_of_ty t).d_ocaml
  | TTuple l ->
      pf ft "(%a)"
        (Format.pp_print_list ~pp_sep:(fun ft () -> pf ft " * ") ocaml_ty)
        l
  | TOption t -> pf ft "(%a option)" ocaml_ty t
  | TList t -> pf ft "(%a list)" ocaml_ty t

let list ?(sep = ", ") pp ft l =
  Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "%s" sep) pp ft l

(* ---------------------------------------------------------------- *)
(* Patterns *)

(** Machine-integer variables bound by a pattern, which the body sees as [Z.t]s.
*)
let small_binders p =
  Check.binders p
  |> List.filter_map (fun (x, (_, small)) -> if small then Some x else None)

let rec pat ft (p : pat) =
  match p.p with
  | PAny -> pf ft "_"
  | PVar x -> pf ft "%s" x
  | PLit x ->
      let c = Option.get (find_constr (Option.get !lang.lit_node)) in
      pf ft "({ Hc.node = { %skind = %s%s _; _ }; _ } as %s)" (term_path ())
        (constr_path c) c.c_name x
  | PAs (p', x) -> pf ft "(%a as %s)" pat p' x
  | POr (a, b) | PComm (a, b) -> pf ft "(%a | %a)" pat a pat b
  | PInt z -> pf ft "%s" (Z.to_string z)
  | PBool b -> pf ft "%b" b
  | PUnit -> pf ft "()"
  | PTuple l -> pf ft "(%a)" (list pat) l
  | PSome p -> pf ft "(Some %a)" pat p
  | PNone -> pf ft "None"
  | PNil -> pf ft "[]"
  | PCons (h, t) -> pf ft "(%a :: %a)" pat h pat t
  | PRecord fields ->
      pf ft "{ %a; _ }"
        (list ~sep:"; " (fun ft (f, q) ->
             pf ft "%s%s = %a" (module_of p.pty) f pat q))
        fields
  | PConstr (c, args) ->
      let inner ft () =
        match args with
        | [] -> pf ft "%s%s" (constr_path c) c.c_name
        | _ -> pf ft "%s%s (%a)" (constr_path c) c.c_name (list pat) args
      in
      if p.pty = TTerm then
        pf ft "{ Hc.node = { %skind = %a; _ }; _ }" (term_path ()) inner ()
      else pf ft "(%a)" inner ()

(* ---------------------------------------------------------------- *)
(* Expressions *)

(** The primitives that compute a function on the value of a literal directly on
    the literal ([[@raw f p]]), by function. *)
let raw_prims () =
  List.filter_map
    (fun (k, p) ->
      if String.starts_with ~prefix:"raw:" k then
        Some (String.sub k 4 (String.length k - 4), p)
      else None)
    !lang.lit_fns

(** Whether [x] occurs in [e], ignoring shadowing. With [~decoded], only counts
    the occurrences of the literal [x] that need its value, that is not those as
    the last argument of the functions that have a [raw_prims], which read it
    from the term. *)
let rec mentions ?(decoded = false) x (e : expr) =
  let go = mentions ~decoded x in
  match e.e with
  | EVar y -> x = y
  | ECall (f, args) when decoded && List.mem_assoc f (raw_prims ()) -> (
      match List.rev args with
      | { e = EVar y; _ } :: l when y = x -> List.exists go l
      | _ -> List.exists go args)
  | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> false
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l ->
      List.exists go l
  | ENode (a, b) | EBinop (_, a, b) | ECons (a, b) | EAssert (a, b) ->
      go a || go b
  | ELet (_, a, b) | ELetFun (_, _, a, b) -> go a || go b
  | EUnop (_, a) | ESome a | EField (a, _) -> go a
  | EIf (a, b, c) -> go a || go b || go c
  | ERecord l -> List.exists (fun (_, e) -> go e) l
  | EMatch (scruts, cases) ->
      List.exists go scruts
      || List.exists
           (fun (c : case) ->
             Option.fold ~none:false ~some:go c.guard || go c.body)
           cases

let int_lit ft z =
  if Z.equal z Z.zero then pf ft "Z.zero"
  else if Z.equal z Z.one then pf ft "Z.one"
  else if Z.equal z Z.minus_one then pf ft "Z.minus_one"
  else if Z.fits_int z then pf ft "(Z.of_int (%s))" (Z.to_string z)
  else pf ft "(Z.of_string %S)" (Z.to_string z)

type ctx = {
  prims : string list;
  consts : string list;
  raw : string list;  (** literal binders that are not decoded *)
}

let rec expr ctx ft (e : expr) =
  let expr = expr ctx in
  match e.e with
  | EVar x -> pf ft "%s" x
  | EInt z -> int_lit ft z
  | EBool b -> pf ft "%b" b
  | EUnit -> pf ft "()"
  | EUnreachable -> pf ft "(assert false)"
  | EConstr (c, []) -> pf ft "%s%s" (constr_path c) c.c_name
  | EConstr (c, args) ->
      let arg ft (a, e) =
        match a with
        | Small -> pf ft "(Z.to_int %a)" expr e
        | Arg _ -> expr ft e
      in
      pf ft "(%s%s (%a))" (constr_path c) c.c_name (list arg)
        (List.combine c.c_args args)
  | ENode (k, t) -> pf ft "(P.node %a %a)" expr k expr t
  | ECall ("equal", [ a; b ]) ->
      pf ft "(Int.equal %a.Hc.tag %a.Hc.tag)" expr a expr b
  | ECall ("type_of", [ a ]) -> pf ft "%a.Hc.node.%sty" expr a (term_path ())
  | ECall ("tag_le", [ a; b ]) ->
      pf ft "(Int.compare %a.Hc.tag %a.Hc.tag <= 0)" expr a expr b
  | ECall (f, args)
    when List.mem_assoc f (raw_prims ())
         &&
         match List.rev args with
         | { e = EVar x; _ } :: _ -> List.mem x ctx.raw
         | _ -> false ->
      pf ft "(P.%s%a)"
        (List.assoc f (raw_prims ()))
        (fun ft -> List.iter (fun a -> pf ft " %a" expr a))
        args
  | ECall (f, []) ->
      if List.mem f ctx.prims then pf ft "P.%s" f
      else if List.mem f ctx.consts then pf ft "%s" f
      else pf ft "(%s ())" f
  | ECall (f, args) ->
      let f = if List.mem f ctx.prims then "P." ^ f else f in
      pf ft "(%s %a)" f (list ~sep:" " expr) args
  | ELocalCall (f, args) -> pf ft "(%s %a)" f (list ~sep:" " expr) args
  | EUnop (Neg, a) -> pf ft "(Z.neg %a)" expr a
  | EUnop (Not, a) -> pf ft "(not %a)" expr a
  | EUnop (Lognot, a) -> pf ft "(Z.lognot %a)" expr a
  | EBinop (Arith op, a, b) -> (
      let z name = pf ft "(Z.%s %a %a)" name expr a expr b in
      let cmp c = pf ft "(P.zcompare %a %a %s 0)" expr a expr b c in
      match op with
      | Add -> z "add"
      | Sub -> z "sub"
      | Mul -> z "mul"
      | Lt -> cmp "<"
      | Le -> cmp "<="
      | Gt -> cmp ">"
      | Ge -> cmp ">="
      | Eq | Ne ->
          let neg = if op = Ne then "not " else "" in
          let eq =
            match a.ety with
            | TInt -> "P.zequal"
            | TBool -> "Bool.equal"
            | TSty -> "P.equal_ty"
            | TData _ as t when Option.is_some (decl_of_ty t).d_equal ->
                "P." ^ Option.get (decl_of_ty t).d_equal
            | _ -> "Stdlib.( = )"
          in
          pf ft "(%s(%s %a %a))" neg eq expr a expr b
      | And -> pf ft "(%a && %a)" expr a expr b
      | Or -> pf ft "(%a || %a)" expr a expr b)
  | EBinop (Bit op, a, b) -> (
      match op with
      | Land -> pf ft "(Z.logand %a %a)" expr a expr b
      | Lor -> pf ft "(Z.logor %a %a)" expr a expr b
      | Lxor -> pf ft "(Z.logxor %a %a)" expr a expr b
      | Lsl -> pf ft "(Z.shift_left %a (Z.to_int %a))" expr a expr b
      | Asr -> pf ft "(Z.shift_right %a (Z.to_int %a))" expr a expr b)
  | EIf (c, a, b) ->
      pf ft "@[<hv>(if %a@ then %a@ else %a)@]" expr c expr a expr b
  | ELet (p, rhs, body) ->
      pf ft "@[<v>(let %a = %a in@ %a%a)@]" pat p expr rhs (small_lets body) p
        (in_scope ctx p body) body
  | ELetFun (f, params, fbody, body) ->
      pf ft "@[<v>(let %s %a =@;<1 2>%a in@ %a)@]" f
        (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %a)" x ocaml_ty t))
        params expr fbody expr body
  | EMatch (scruts, cases) ->
      pf ft "@[<v>(match %a with@ %a)@]" (list expr) scruts
        (list ~sep:"" (case ctx))
        cases
  | ETuple l -> pf ft "(%a)" (list expr) l
  | ESome e -> pf ft "(Some %a)" expr e
  | ENone -> pf ft "None"
  | ENil -> pf ft "[]"
  | ECons (h, t) -> pf ft "(%a :: %a)" expr h expr t
  | ERecord fields ->
      let m = module_of e.ety in
      pf ft "{ %a }"
        (list ~sep:"; " (fun ft (f, e) -> pf ft "%s%s = %a" m f expr e))
        fields
  | EField (r, f) -> pf ft "%a.%s%s" expr r (module_of r.ety) f
  | EAssert (c, body) -> pf ft "@[<v>(assert %a;@ %a)@]" expr c expr body

(** Converts the binders of [p] that [e] uses. *)
and small_lets e ft p =
  List.iter
    (fun x -> pf ft "let %s = Z.of_int %s in@ " x x)
    (List.filter (fun x -> mentions x e) (small_binders p));
  List.iter
    (fun x -> pf ft "let %s = P.%s %s in@ " x (Option.get (lit_fn "of_term")) x)
    (List.filter (fun x -> mentions ~decoded:true x e) (Check.lit_binders p))

(** Prints [e], in the scope of the binders of [p]. *)
and in_scope ctx p e =
  let raw =
    List.filter
      (fun x -> not (mentions ~decoded:true x e))
      (Check.lit_binders p)
  in
  let shadowed x = List.mem_assoc x (Check.binders p) in
  expr { ctx with raw = raw @ List.filter (fun x -> not (shadowed x)) ctx.raw }

and case ctx ft (c : case) =
  let guard ft = function
    | None -> ()
    | Some g ->
        pf ft "@ when (%a%a)" (small_lets g) c.pat (in_scope ctx c.pat g) g
  in
  pf ft "@[<hv 2>| %a%a ->@ %a%a@]@ " pat c.pat guard c.guard
    (small_lets c.body) c.pat
    (in_scope ctx c.pat c.body)
    c.body

(* ---------------------------------------------------------------- *)
(* Call graph *)

let rec calls acc (e : expr) =
  let go = calls in
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> acc
  | ECall (f, args) -> List.fold_left go (f :: acc) args
  | EConstr (_, l) | ELocalCall (_, l) | ETuple l -> List.fold_left go acc l
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

(** Strongly connected components of the call graph, callees first (Tarjan). *)
let sccs (fns : fn list) : fn list list =
  let names = List.map (fun f -> f.name) fns in
  let succs =
    List.map
      (fun f ->
        ( f.name,
          List.sort_uniq compare
            (List.filter (fun g -> List.mem g names) (calls [] f.body)) ))
      fns
  in
  let index = Hashtbl.create 97 and low = Hashtbl.create 97 in
  let on_stack = Hashtbl.create 97 in
  let stack = ref [] and counter = ref 0 and result = ref [] in
  let rec visit v =
    Hashtbl.replace index v !counter;
    Hashtbl.replace low v !counter;
    incr counter;
    stack := v :: !stack;
    Hashtbl.replace on_stack v ();
    List.iter
      (fun w ->
        if not (Hashtbl.mem index w) then (
          visit w;
          Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find low w)))
        else if Hashtbl.mem on_stack w then
          Hashtbl.replace low v
            (min (Hashtbl.find low v) (Hashtbl.find index w)))
      (List.assoc v succs);
    if Hashtbl.find low v = Hashtbl.find index v then
      let rec pop acc =
        match !stack with
        | w :: rest ->
            stack := rest;
            Hashtbl.remove on_stack w;
            if w = v then w :: acc else pop (w :: acc)
        | [] -> assert false
      in
      result := pop [] :: !result
  in
  List.iter (fun v -> if not (Hashtbl.mem index v) then visit v) names;
  (* [result] has callers first *)
  List.rev_map
    (fun scc ->
      (* keep source order within a component *)
      List.filter (fun f -> List.mem f.name scc) fns)
    !result

(** The number of nodes of [e]. *)
let rec weight (e : expr) =
  match e.e with
  | EVar _ | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable
  | EConstr (_, []) ->
      1
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l ->
      List.fold_left (fun n e -> n + weight e) 1 l
  | ENode (a, b)
  | EBinop (_, a, b)
  | ECons (a, b)
  | EAssert (a, b)
  | ELet (_, a, b)
  | ELetFun (_, _, a, b) ->
      1 + weight a + weight b
  | EUnop (_, a) | ESome a | EField (a, _) -> 1 + weight a
  | EIf (a, b, c) -> 1 + weight a + weight b + weight c
  | ERecord l -> List.fold_left (fun n (_, e) -> n + weight e) 1 l
  | EMatch (scruts, cases) ->
      List.fold_left
        (fun n (c : case) ->
          n + weight c.body + Option.fold ~none:0 ~some:weight c.guard)
        (List.fold_left (fun n e -> n + weight e) 1 scruts)
        cases

let is_recursive (fns : fn list) =
  match fns with [ f ] -> List.mem f.name (calls [] f.body) | _ -> true

(* ---------------------------------------------------------------- *)
(* Top-level *)

let fn ctx ft (f : fn) =
  let params ft = function
    | [] when List.mem f.name ctx.consts -> ()
    | [] -> pf ft " ()"
    | ps -> List.iter (fun (x, t) -> pf ft " (%s : %a)" x ocaml_ty t) ps
  in
  pf ft "%s%a : %a =@;<1 2>%a" f.name params f.params ocaml_ty f.ret (expr ctx)
    f.body

(** The primitives that [expr] compiles inline, rather than calling them on [P].
*)
let inline_prims = [ "equal"; "type_of"; "tag_le" ]

(** The functions of [P] that [expr] calls, other than the primitives, with
    their types; those on the values of literals only if the language has them.
*)
let helpers (p : Syntax.program) =
  let ty t = Fmt.str "%a" ocaml_ty t in
  [
    ("node", Fmt.str "%s -> %s -> %s" (ty TKind) (ty TSty) (ty TTerm));
    ("zcompare", "Z.t -> Z.t -> int");
    ("zequal", "Z.t -> Z.t -> bool");
    ("equal_ty", Fmt.str "%s -> %s -> bool" (ty TSty) (ty TSty));
  ]
  @
  if Option.is_none !lang.lit_node || !lang.lit_int then []
  else
    let v = lit_value_ty () in
    Option.fold ~none:[]
      ~some:(fun f -> [ (f, Fmt.str "%s -> %s -> bool" (ty v) (ty v)) ])
      (decl_of_ty v).d_equal
    @ List.map
        (fun (f, raw) ->
          (* the type of [f], on the literal rather than its value *)
          match
            List.find_map
              (fun (q : prim) ->
                if q.pname = f then Some (q.pargs, q.pret) else None)
              p.Syntax.prims
          with
          | Some (args, ret) ->
              let args = List.rev (TTerm :: List.tl (List.rev args)) in
              (raw, String.concat " -> " (List.map ty args @ [ ty ret ]))
          | None -> Fmt.failwith "[@raw]: unknown function %s" f)
        (raw_prims ())

(** Checks that [P] defines the primitives and helpers, with their types. *)
let prim_sigs ft (p : program) =
  pf ft "@[<v 2>module _ : sig";
  List.iter (fun (f, t) -> pf ft "@ val %s : %s" f t) (helpers p);
  List.iter
    (fun q ->
      if not (List.mem q.pname inline_prims) then (
        pf ft "@ val %s : " q.pname;
        List.iter (fun t -> pf ft "%a -> " ocaml_ty t) q.pargs;
        ocaml_ty ft q.pret))
    p.prims;
  pf ft "@]@ end = P@ @ "

let program ~sources ft (p : program) =
  let groups = sccs p.fns in
  let consts =
    List.concat_map
      (function
        | [ f ] when f.params = [] && not (is_recursive [ f ]) -> [ f.name ]
        | _ -> [])
      groups
  in
  let ctx = { prims = List.map (fun p -> p.pname) p.prims; consts; raw = [] } in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  pf ft "[@@@@@@warning \"-a\"]@ @ ";
  pf ft "open P@ @ ";
  prim_sigs ft p;
  List.iter
    (fun group ->
      let kw =
        match group with
        | _ when is_recursive group -> "let rec"
        | [ f ] when f.params <> [] && weight f.body <= 12 -> "let[@inline]"
        | _ -> "let"
      in
      List.iteri
        (fun i f ->
          pf ft "@[<hv 2>%s %a@]@ @ " (if i = 0 then kw else "and") (fn ctx) f)
        group)
    groups;
  pf ft "@]@."

(* ---------------------------------------------------------------- *)
(* Checking the OCaml types *)

(** Checks that the OCaml types of the language have its declared constructors
    and record fields, with their declared arguments, and no others: it matches
    every value of each type. It is included next to the output of {!program},
    where the same types are in scope, and has no runtime cost. *)
let lang_check ~sources ft =
  let arg ft = function Small -> pf ft "int" | Arg t -> ocaml_ty ft t in
  let typed ft a = pf ft "(_ : %a)" arg a in
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  pf ft "@[<v 2>module _ = struct@ [@@@@@@warning \"-a@@8@@9\"]@ open P";
  List.iter
    (fun d ->
      let t = TData d.d_name in
      let m = module_of t in
      let constrs =
        List.filter (fun c -> decl_name c.c_res = Some d.d_name) !lang.constrs
      in
      pf ft "@ @[<v 2>let _ : %a -> unit =" ocaml_ty t;
      match (constrs, d.d_fields) with
      | [], [] -> pf ft " fun _ -> ()@]"
      | [], fields ->
          pf ft "@ fun { %a } -> ()@]"
            (list ~sep:"; " (fun ft (f, t) ->
                 pf ft "%s%s = %a" m f typed (Arg t)))
            fields
      | _ ->
          pf ft " function";
          List.iter
            (fun c ->
              match c.c_args with
              | [] -> pf ft "@ | %s%s -> ()" m c.c_name
              | [ a ] -> pf ft "@ | %s%s %a -> ()" m c.c_name typed a
              | args -> pf ft "@ | %s%s (%a) -> ()" m c.c_name (list typed) args)
            constrs;
          pf ft "@]")
    !lang.decls;
  pf ft "@]@ end@]@."
