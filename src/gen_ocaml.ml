(** OCaml backends. {!types} defines the types of the language, standalone (with
    Zarith): terms are hash-consed records [{ kind; ty; tag }]. {!program}
    defines every Kanon function, where these types are in scope, and calls the
    primitives in the module of [[@@@ocaml_prims]]. The output is not meant to
    be read. *)

open Syntax

let pf = Format.fprintf

(** The keywords of OCaml, which a name of the language may be (those of Kanon
    are not names). *)
let keywords =
  [
    "and";
    "as";
    "assert";
    "asr";
    "begin";
    "class";
    "constraint";
    "do";
    "done";
    "downto";
    "else";
    "end";
    "exception";
    "external";
    "false";
    "for";
    "fun";
    "function";
    "functor";
    "if";
    "in";
    "include";
    "inherit";
    "initializer";
    "land";
    "lazy";
    "let";
    "lor";
    "lsl";
    "lsr";
    "lxor";
    "match";
    "method";
    "mod";
    "module";
    "mutable";
    "new";
    "nonrec";
    "object";
    "of";
    "open";
    "or";
    "private";
    "rec";
    "sig";
    "struct";
    "then";
    "to";
    "true";
    "try";
    "type";
    "val";
    "virtual";
    "when";
    "while";
    "with";
  ]

(** The OCaml identifier of the name [x]: a keyword is a raw identifier. *)
let id x = if List.mem x keywords then "\\#" ^ x else x

(** The OCaml type of [t], where the types of {!types} are in scope: a declared
    type has its Kanon name, and the kinds of terms (the constructors of [t])
    are [kind]. *)
let rec ocaml_ty ft = function
  | TInt -> pf ft "Z.t"
  | TBool -> pf ft "bool"
  | TUnit -> pf ft "unit"
  | TTerm -> pf ft "t"
  | (TKind | TSty | TData _) as t -> pf ft "%s" (id (decl_of_ty t).d_name)
  | TTuple l ->
      pf ft "(%a)"
        (Format.pp_print_list ~pp_sep:(fun ft () -> pf ft " * ") ocaml_ty)
        l
  | TOption t -> pf ft "(%a option)" ocaml_ty t
  | TList t -> pf ft "(%a list)" ocaml_ty t
  | TArray t -> pf ft "(%a Iarray.t)" ocaml_ty t

(** The OCaml type of the argument of a constructor: a [nat] is an [int]. *)
let ocaml_arg ft = function Small -> pf ft "int" | Arg t -> ocaml_ty ft t

let list ?(sep = ", ") pp ft l =
  Format.pp_print_list ~pp_sep:(fun ft () -> pf ft "%s" sep) pp ft l

(** The lines of [text], as a documentation comment: [(** ... *)] in OCaml,
    [/-- ... -/] in Lean ([opening] and [closing]), where [escape] makes the
    text safe to put in a comment. The lines are aligned in a box. *)
let doc_comment ~opening ~closing ~escape ft text =
  pf ft "@[<v>%s %a %s@]" opening
    (Format.pp_print_list
       ~pp_sep:(fun ft () -> pf ft "@ ")
       Format.pp_print_string)
    (String.split_on_char '\n' (escape text))
    closing

(** [text] without what would end or open a comment, or start a string, in an
    OCaml comment: the closing and opening delimiters get a space inside, an
    unbalanced double quote becomes a character literal, and a quoted string
    opening (a brace, an identifier, a bar) gets a space after the brace. *)
let escape_ocaml_comment text =
  let n = String.length text in
  let b = Buffer.create n in
  let at i = if i < n then text.[i] else '\000' in
  (* a quote as a character literal, apart from the identifier before it, which
     would take its first quote *)
  let char_quote () =
    let l = Buffer.length b in
    (if l > 0 then
       match Buffer.nth b (l - 1) with
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' ->
           Buffer.add_char b ' '
       | _ -> ());
    Buffer.add_string b "'\"'"
  in
  let rec close j =
    if j >= n then None
    else if text.[j] = '\\' then close (j + 2)
    else if text.[j] = '"' then Some j
    else close (j + 1)
  in
  let rec go instr i stop =
    if i < stop then
      match text.[i] with
      | '*' when at (i + 1) = ')' ->
          Buffer.add_string b "* )";
          go instr (i + 2) stop
      | '(' when at (i + 1) = '*' ->
          Buffer.add_string b "( *";
          go instr (i + 2) stop
      | '\'' when at (i + 1) = '"' && at (i + 2) = '\'' ->
          char_quote ();
          go instr (i + 3) stop
      | '\\' when instr && (at (i + 1) = '"' || at (i + 1) = '\\') ->
          Buffer.add_char b '\\';
          Buffer.add_char b (at (i + 1));
          go instr (i + 2) stop
      | '"' -> (
          match close (i + 1) with
          | Some j when j < stop ->
              Buffer.add_char b '"';
              go true (i + 1) j;
              Buffer.add_char b '"';
              go instr (j + 1) stop
          | _ ->
              char_quote ();
              go instr (i + 1) stop)
      | '{' ->
          Buffer.add_char b '{';
          let rec id j =
            if j < n && (('a' <= text.[j] && text.[j] <= 'z') || text.[j] = '_')
            then id (j + 1)
            else j
          in
          if at (id (i + 1)) = '|' then Buffer.add_char b ' ';
          go instr (i + 1) stop
      | c ->
          Buffer.add_char b c;
          go instr (i + 1) stop
  in
  go false 0 n;
  Buffer.contents b

let ocaml_doc ft text =
  doc_comment ~opening:"(**" ~closing:"*)" ~escape:escape_ocaml_comment ft text

(** The documentation comment before an item, if it has one, and a line break.
*)
let doc ft = function None -> () | Some text -> pf ft "%a@ " ocaml_doc text

(** The documentation comment after an item, if it has one: OCaml attaches the
    comments of constructors and of signature items that way. *)
let doc_after ft = function
  | None -> ()
  | Some text -> pf ft " %a" ocaml_doc text

(** The equality at type [t], as an OCaml function: on terms, of their tags; on
    the declared types, the generated [equal_d] (see {!types}). *)
let rec equal_fn ft = function
  | TInt -> pf ft "Z.equal"
  | TBool -> pf ft "Stdlib.Bool.equal"
  | TUnit -> pf ft "Stdlib.Unit.equal"
  | TTerm -> pf ft "equal_t"
  | (TKind | TSty | TData _) as t -> pf ft "equal_%s" (decl_of_ty t).d_name
  | TTuple l ->
      let xs p = List.mapi (fun i _ -> Printf.sprintf "%s%d" p (i + 1)) l in
      pf ft "(fun (%s) (%s) -> %a)"
        (String.concat ", " (xs "a"))
        (String.concat ", " (xs "b"))
        (list ~sep:" && " (fun ft (t, (a, b)) ->
             pf ft "%a %s %s" equal_fn t a b))
        (List.combine l (List.combine (xs "a") (xs "b")))
  | TOption t -> pf ft "(Stdlib.Option.equal %a)" equal_fn t
  | TList t -> pf ft "(Stdlib.List.equal %a)" equal_fn t
  | TArray t -> pf ft "(Stdlib.Iarray.equal %a)" equal_fn t

(** [hash_combine (... (hash_combine h1 h2) ...) hn], for the hashes [l],
    printed by [pp]. *)
let combine pp ft l =
  (* the last hash first *)
  let rec go ft = function
    | [] -> pf ft "0"
    | [ x ] -> pp ft x
    | x :: l -> pf ft "@[<hov 2>hash_combine@ (%a)@ (%a)@]" go l pp x
  in
  go ft (List.rev l)

(** The hash at type [t], as an OCaml function, compatible with [equal_fn]:
    terms are hashed by their tags, and the hashes of the components of a value
    combined with [hash_combine] (see {!types}). *)
let rec hash_fn ft = function
  | TInt -> pf ft "Z.hash"
  | TBool -> pf ft "Stdlib.Bool.to_int"
  | TUnit -> pf ft "(fun () -> 0)"
  | TTerm -> pf ft "hash_t"
  | (TKind | TSty | TData _) as t -> pf ft "hash_%s" (decl_of_ty t).d_name
  | TTuple l ->
      let xs = List.mapi (fun i _ -> Printf.sprintf "x%d" (i + 1)) l in
      pf ft "(fun (%s) -> %a)" (String.concat ", " xs)
        (combine (fun ft (t, x) -> pf ft "%a %s" hash_fn t x))
        (List.combine l xs)
  | TOption t ->
      pf ft "(function None -> 0 | Some x -> hash_combine 1 (%a x))" hash_fn t
  | TList t ->
      pf ft "(Stdlib.List.fold_left (fun acc x -> hash_combine acc (%a x)) 0)"
        hash_fn t
  | TArray t ->
      pf ft "(Stdlib.Iarray.fold_left (fun acc x -> hash_combine acc (%a x)) 0)"
        hash_fn t

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
  | PVar x -> pf ft "%s" (id x)
  | PAs (p', x) -> pf ft "(%a as %s)" pat p' (id x)
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
        (list ~sep:"; " (fun ft (f, q) -> pf ft "%s = %a" (id f) pat q))
        fields
  | PConstr (c, args) ->
      let inner ft () =
        match args with
        | [] -> pf ft "%s" c.c_name
        | _ -> pf ft "%s (%a)" c.c_name (list pat) args
      in
      if p.pty = TTerm then pf ft "{ kind = %a; _ }" inner ()
      else pf ft "(%a)" inner ()

(* ---------------------------------------------------------------- *)
(* Expressions *)

(** Whether [x] occurs in [e], ignoring shadowing. *)
let rec mentions x (e : expr) =
  let go = mentions x in
  match e.e with
  | EVar y -> x = y
  | EInt _ | EBool _ | EUnit | ENone | ENil | EUnreachable -> false
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l | EArray l ->
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

(** The module of the primitives ([[@@@ocaml_prims]]). *)
let prims_module () =
  match !lang.ocaml_prims with
  | Some m -> m
  | None -> invalid_arg "Gen_ocaml: the language has no [@@@ocaml_prims]"

type ctx = {
  prims : string list;  (** in the module of [[@@@ocaml_prims]] *)
  consts : string list;
  public : bool;
      (** the functions are called by their path in the rules module, [Int.add],
          instead of by their name in [Kanon_flat], [int_add] *)
}

(** The OCaml name of the function [f], as [ctx] calls it. *)
let fn_name ctx f =
  if not ctx.public then flat_name f
  else
    match split_name f with
    | Some (m, x) -> m ^ "." ^ id x
    | None -> "Kanon_flat." ^ f

let rec expr ctx ft (e : expr) =
  let expr = expr ctx in
  match e.e with
  | EVar x -> pf ft "%s" (id x)
  | EInt z -> int_lit ft z
  | EBool b -> pf ft "%b" b
  | EUnit -> pf ft "()"
  | EUnreachable -> pf ft "(assert false)"
  | EConstr (c, []) -> pf ft "%s" c.c_name
  | EConstr (c, args) ->
      let arg ft (a, e) =
        match a with
        | Small -> pf ft "(Z.to_int %a)" expr e
        | Arg _ -> expr ft e
      in
      pf ft "(%s (%a))" c.c_name (list arg) (List.combine c.c_args args)
  | ENode (k, t) -> pf ft "(node %a %a)" expr k expr t
  | ECall ("type_of", [ a ]) -> pf ft "%a.ty" expr a
  | EArray l -> pf ft "([|%a|] : _ Iarray.t)" (list ~sep:"; " expr) l
  | ECall ("array_length", [ a ]) ->
      pf ft "(Z.of_int (Stdlib.Iarray.length %a))" expr a
  | ECall ("array_get", [ a; i ]) ->
      pf ft "(Stdlib.Iarray.get %a (Z.to_int %a))" expr a expr i
  | ECall ("array_set", [ a; i; v ]) ->
      pf ft
        "@[<v>(let a = %a and i = Z.to_int %a and v = %a in@ let c = \
         Stdlib.Iarray.to_array a in@ c.(i) <- v;@ Stdlib.Iarray.of_array c)@]"
        expr a expr i expr v
  | ECall ("array_of_list", [ l ]) -> pf ft "(Stdlib.Iarray.of_list %a)" expr l
  | ECall ("array_to_list", [ a ]) -> pf ft "(Stdlib.Iarray.to_list %a)" expr a
  | ECall ("tag_le", [ a; b ]) ->
      pf ft "(Stdlib.Int.compare %a.tag %a.tag <= 0)" expr a expr b
  | ECall (f, []) ->
      if List.mem f ctx.prims then
        pf ft "%s.%s" (prims_module ()) (id (plain_name f))
      else if List.mem f ctx.consts then pf ft "%s" (fn_name ctx f)
      else pf ft "(%s ())" (fn_name ctx f)
  | ECall (f, args) ->
      let f =
        if List.mem f ctx.prims then prims_module () ^ "." ^ id (plain_name f)
        else fn_name ctx f
      in
      pf ft "(%s %a)" f (list ~sep:" " expr) args
  | ELocalCall (f, args) -> pf ft "(%s %a)" (id f) (list ~sep:" " expr) args
  | EUnop (Neg, a) -> pf ft "(Z.neg %a)" expr a
  | EUnop (Not, a) -> pf ft "(not %a)" expr a
  | EBinop (op, a, b) -> (
      let z name = pf ft "(Z.%s %a %a)" name expr a expr b in
      match op with
      | Add -> z "add"
      | Sub -> z "sub"
      | Mul -> z "mul"
      | Lt -> z "lt"
      | Le -> z "leq"
      | Gt -> z "gt"
      | Ge -> z "geq"
      | Eq | Ne ->
          let neg = if op = Ne then "not " else "" in
          if a.ety = TTerm then
            pf ft "(%sStdlib.Int.equal %a.tag %a.tag)" neg expr a expr b
          else pf ft "(%s(%a %a %a))" neg equal_fn a.ety expr a expr b
      | And -> pf ft "(%a && %a)" expr a expr b
      | Or -> pf ft "(%a || %a)" expr a expr b)
  | EIf (c, a, b) ->
      pf ft "@[<hv>(if %a@ then %a@ else %a)@]" expr c expr a expr b
  | ELet (p, rhs, body) ->
      pf ft "@[<v>(let %a = %a in@ %a%a)@]" pat p expr rhs (small_lets body) p
        expr body
  | ELetFun (f, params, fbody, body) ->
      pf ft "@[<v>(let %s %a =@;<1 2>%a in@ %a)@]" (id f)
        (list ~sep:" " (fun ft (x, t) -> pf ft "(%s : %a)" (id x) ocaml_ty t))
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
      pf ft "{ %a }"
        (list ~sep:"; " (fun ft (f, e) -> pf ft "%s = %a" (id f) expr e))
        fields
  | EField (r, f) -> pf ft "%a.%s" expr r (id f)
  | EAssert (c, body) ->
      (* the check of the sorts of a spec has a last case [_], which is unused
         when [ty] has only the sorts that it matches *)
      pf ft "@[<v>(assert (%a [@@warning \"-11\"]);@ %a)@]" expr c expr body

(** Converts the binders of [p] that [e] uses. *)
and small_lets e ft p =
  List.iter
    (fun x -> pf ft "let %s = Z.of_int %s in@ " (id x) (id x))
    (List.filter (fun x -> mentions x e) (small_binders p))

and case ctx ft (c : case) =
  let guard ft = function
    | None -> ()
    | Some g -> pf ft "@ when (%a%a)" (small_lets g) c.pat (expr ctx) g
  in
  pf ft "@[<hv 2>| %a%a ->@ %a%a@]@ " pat c.pat guard c.guard
    (small_lets c.body) c.pat (expr ctx) c.body

(* ---------------------------------------------------------------- *)
(* Call graph *)

let calls acc e = fold_calls (fun acc g _ -> g :: acc) acc e

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
  | ECall (_, l) | EConstr (_, l) | ELocalCall (_, l) | ETuple l | EArray l ->
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
    | ps -> List.iter (fun (x, t) -> pf ft " (%s : %a)" (id x) ocaml_ty t) ps
  in
  pf ft "%s%a : %a =@;<1 2>%a" (flat_name f.name) params f.params ocaml_ty f.ret
    (expr ctx) f.body

(** The primitives that [expr] compiles inline. *)
let inline_prims = [ "type_of"; "tag_le" ]

(** The primitives that [expr] calls in the module of the primitives, with their
    types and docs. *)
let prim_fns (p : program) =
  let ty t = Fmt.str "%a" ocaml_ty t in
  List.filter_map
    (fun q ->
      if List.mem q.pname inline_prims then None
      else
        Some
          ( plain_name q.pname,
            String.concat " -> " (List.map ty (q.pargs @ [ q.pret ])),
            q.pdoc ))
    p.prims

(** Checks that the language names the module of its primitives, if it has any.
*)
let check_prims (p : program) =
  match (prim_fns p, !lang.ocaml_prims) with
  | (f, _, _) :: _, None ->
      let loc =
        match List.find_opt (fun q -> plain_name q.pname = f) p.prims with
        | Some q -> q.ploc
        | None -> Location.none
      in
      raise
        (Check.Error
           ( loc,
             Fmt.str
               "%s is a primitive: [@@@@@@ocaml_prims \"M\"], in the \
                declaration of the language, names the OCaml module that \
                implements the primitives"
               f ))
  | _ -> ()

(** The nodes and the sorts of the language, whose destructors [as_foo] and
    [is_foo] the backend generates: the leaves and operators that the user
    declared, and the sorts (and not the kinds built by Kanon, nor the
    constructors of the other types). *)
let destructed () =
  List.filter
    (fun (c : constr) ->
      c.c_res = TSty
      || (c.c_res = TKind && not (List.mem c.c_name !lang.node_kinds))
      || Option.is_some (Check.node_of_op c))
    !lang.constrs

(** The suffix of the destructors of the node or sort [c]: its name in
    lowercase. *)
let destructor_suffix (c : constr) = String.lowercase_ascii c.c_name

(** Checks that two functions do not have the same OCaml name ([Bitvec.add_x]
    and [Bitvec_add.x] are both [bitvec_add_x]), nor two primitives (the module
    of the primitives implements them by their name without their module: rename
    one of [Int.size] and [Bitvec.size]). *)
let check_names (p : program) =
  let dup what loc name = function
    | Some other when other <> name ->
        raise
          (Check.Error
             ( loc,
               Fmt.str "%s and %s are both the %s %s" other name what
                 (if what = "function" then flat_name name else plain_name name)
             ))
    | _ -> ()
  in
  let seen = Hashtbl.create 16 in
  let check what key loc name =
    dup what loc name (Hashtbl.find_opt seen (what, key));
    Hashtbl.replace seen (what, key) name
  in
  List.iter
    (fun (f : fn) -> check "function" (flat_name f.name) f.floc f.name)
    p.fns;
  List.iter
    (fun (q : prim) -> check "primitive" (plain_name q.pname) q.ploc q.pname)
    p.prims

(** The destructors of [c]: [as_foo], which is the arguments of [c] (its
    parameters, then its operands, as in a pattern) in an option, and [is_foo].
*)
let destructors (c : constr) =
  let suffix = destructor_suffix c in
  let vars k x = List.init k (fun i -> Fmt.str "%s%d" x (i + 1)) in
  let tuple = function
    | [] -> "()"
    | [ x ] -> x
    | l -> "(" ^ String.concat ", " l ^ ")"
  in
  let params = vars (List.length c.c_args) "p" in
  (* the operands of an operator, and the type of the scrutinee *)
  let operands, ty =
    match (c.c_res, Check.node_of_op c) with
    | TSty, _ -> ([], "ty")
    | _, Some (kc, operands) ->
        ( (match kc.c_args with
          | [ _; Arg (TList _) ] -> [ "xs" ]
          | _ -> vars (List.length operands) "x"),
          "t" )
    | _, None -> ([], "t")
  in
  (* the pattern of [c], whose variables are [names] or blanks *)
  let pat ~blank =
    let name x = if blank then "_" else x in
    let ctor =
      match params with
      | [] -> c.c_name
      | l -> Fmt.str "%s (%s)" c.c_name (String.concat ", " (List.map name l))
    in
    match (c.c_res, Check.node_of_op c) with
    | TSty, _ -> ctor
    | _, Some (kc, _) ->
        Fmt.str "{ kind = %s (%s); _ }" kc.c_name
          (String.concat ", " (ctor :: List.map name operands))
    | _, None -> Fmt.str "{ kind = %s; _ }" ctor
  in
  [
    ( "as_" ^ suffix,
      fun ft ->
        pf ft
          "@[<hv 2>let as_%s (t : %s) =@ match[@@warning \"-11\"] t with %s -> \
           Some %s | _ -> None@]"
          suffix ty (pat ~blank:false)
          (tuple (params @ operands)) );
    ( "is_" ^ suffix,
      fun ft ->
        pf ft
          "@[<hv 2>let is_%s (t : %s) =@ match[@@warning \"-11\"] t with %s -> \
           true | _ -> false@]"
          suffix ty (pat ~blank:true) );
  ]

(** The name of the function that makes the sort [c] in its module: [t_] and the
    name of [c] in lowercase, without its [T] when it has one ([TBitVector] is
    [t_bitvector]). *)
let sort_val_name (c : constr) =
  let n = c.c_name in
  let n =
    if
      String.length n > 1
      && n.[0] = 'T'
      && Char.equal n.[1] (Char.uppercase_ascii n.[1])
      && n.[1] <> '_'
    then String.sub n 1 (String.length n - 1)
    else n
  in
  "t_" ^ String.lowercase_ascii n

(** The function of the sort [c]: its arguments are those of its constructor. *)
let sort_ctor ft (c : constr) =
  let vars = List.mapi (fun i a -> (Fmt.str "a%d" (i + 1), a)) c.c_args in
  let param ft (x, a) = pf ft " (%s : %a)" x ocaml_arg a in
  pf ft "let %s%a : ty = %s" (sort_val_name c) (list ~sep:"" param) vars
    (match vars with
    | [] -> c.c_name
    | l -> Fmt.str "%s (%s)" c.c_name (String.concat ", " (List.map fst l)))

(** The module of the generated OCaml where the declaration at [loc] is: the
    Kanon module of its file (see {!Check.module_of_loc}), which may not be the
    name of a module that the output defines, [reserved] or [Kanon_flat]. *)
let module_of ?(reserved = []) (loc : Location.t) =
  let m = Option.value (Check.module_of_loc loc) ~default:"Kanon" in
  if List.mem m ("Kanon_flat" :: reserved) then
    raise
      (Check.Error
         (loc, Fmt.str "the module %s has the name of a generated module" m));
  m

(** An item of a module of the rules: [let name = ...], which [print] prints,
    declared at [loc]; a [block] has several lines. *)
type entry = {
  name : string;
  loc : Location.t;
  doc : string option;
  block : bool;
  is_fn : bool;
  print : Format.formatter -> unit;
}

(** The items of the modules of the rules, by Kanon module, in order of
    declaration: the functions of the sorts, the functions of the language (in
    [Kanon_flat], which the module aliases), and the destructors of the nodes
    and sorts. A name is that of one item of its module: if two have the same,
    one would hide the other. *)
let module_entries ?reserved (p : program) =
  let mods : (string * entry list ref) list ref = ref [] in
  let add m (e : entry) =
    match List.assoc_opt m !mods with
    | Some l ->
        (match List.find_opt (fun (o : entry) -> o.name = e.name) !l with
        | Some o ->
            raise
              (Check.Error
                 ( (if o.is_fn then o.loc else e.loc),
                   Fmt.str
                     "%s.%s: the module has two items of this name (a \
                      function, a destructor or the function of a sort): \
                      rename one of them"
                     m e.name ))
        | None -> ());
        l := !l @ [ e ]
    | None -> mods := !mods @ [ (m, ref [ e ]) ]
  in
  List.iter
    (fun (c : constr) ->
      if c.c_res = TSty then
        add
          (module_of ?reserved c.c_loc)
          {
            name = sort_val_name c;
            loc = c.c_loc;
            doc = c.c_doc;
            block = false;
            is_fn = false;
            print = (fun ft -> sort_ctor ft c);
          })
    !lang.constrs;
  List.iter
    (fun (f : fn) ->
      match split_name f.name with
      | Some (m, x) ->
          ignore (module_of ?reserved f.floc);
          add m
            {
              name = x;
              loc = f.floc;
              doc = f.fdoc;
              block = false;
              is_fn = true;
              print =
                (fun ft ->
                  pf ft "let %s = Kanon_flat.%s" (id x) (flat_name f.name));
            }
      | None -> ())
    p.fns;
  List.iter
    (fun (c : constr) ->
      List.iter
        (fun (name, print) ->
          add
            (module_of ?reserved c.c_loc)
            {
              name;
              loc = c.c_loc;
              doc = None;
              block = true;
              is_fn = false;
              print;
            })
        (destructors c))
    (destructed ());
  List.map (fun (m, l) -> (m, !l)) !mods

(** The header of the generated files of rules: the warnings, and the types of
    the language, opened from their module if they are not in scope. *)
let header ~sources ft =
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  (* every warning but unused match cases, which Kanon prunes *)
  pf ft "[@@@@@@warning \"-a+11\"]@ @ ";
  Option.iter (pf ft "open %s@ @ ") !lang.ocaml_types

(** Checks that the module of the primitives defines them, with their types. *)
let prim_sigs ft (p : program) =
  match prim_fns p with
  | [] -> ()
  | fns ->
      pf ft "@[<v 2>module _ : sig";
      (* a comment between two items would be ambiguous: documented items are
         set apart by blank lines *)
      ignore
        (List.fold_left
           (fun prev (f, t, d) ->
             if prev || d <> None then pf ft "@ ";
             pf ft "@ %aval %s : %s" doc d (id f) t;
             d <> None)
           false fns);
      pf ft "@]@ end = %s@ @ " (prims_module ())

(* ---------------------------------------------------------------- *)
(* Traversals *)

(** What a traversal does with the children, which [f] is applied to: [Map]
    rebuilds, [Iter] calls [f] for its effect, [Exists] is [true] when [f] is
    for one of them (the others are not looked at). *)
type act = Map | Iter | Exists

let act_name = function Map -> "map" | Iter -> "iter" | Exists -> "exists"

(** The name of the function that traverses the declared type [d], looking for
    values of the type [target] ([TTerm] or [TSty]). *)
let trav_name act target d =
  Printf.sprintf "kanon__%s_%s%s" (act_name act)
    (if target = TSty then "ty_" else "")
    d

(** The OCaml function, as text, of one argument, that applies [act] to the
    children of a value of the type [ty], those of the type [target], or none if
    [ty] has none. [f] is the function of the user, applied to each child, in
    the order of the arguments (the elements of a list or an array from the
    first, the components of a tuple from the left, the fields of a record in
    their order). *)
let rec mapper act target ty : string option =
  if not (Syntax.mentions target ty) then None
  else
    match ty with
    | t when t = target -> Some "f"
    | TList t ->
        Option.map
          (fun m ->
            match act with
            | Map -> Printf.sprintf "(kanon__list_map %s)" m
            | Iter -> Printf.sprintf "(List.iter %s)" m
            | Exists -> Printf.sprintf "(List.exists %s)" m)
          (mapper act target t)
    | TArray t ->
        Option.map
          (fun m ->
            match act with
            | Map -> Printf.sprintf "(kanon__iarray_map %s)" m
            | Iter -> Printf.sprintf "(Iarray.iter %s)" m
            | Exists -> Printf.sprintf "(Iarray.exists %s)" m)
          (mapper act target t)
    | TOption t ->
        Option.map
          (fun m ->
            match act with
            | Map ->
                Printf.sprintf
                  "(function Some x as o -> let y = %s x in if y == x then o \
                   else Some y | None -> None)"
                  m
            | Iter -> Printf.sprintf "(Option.iter %s)" m
            | Exists ->
                Printf.sprintf "(function Some x -> %s x | None -> false)" m)
          (mapper act target t)
    | TTuple l ->
        let ms = List.map (mapper act target) l in
        let a i = Printf.sprintf "a%d" (i + 1)
        and b i = Printf.sprintf "b%d" (i + 1) in
        let pat = String.concat ", " (List.mapi (fun i _ -> a i) l) in
        Some
          (match act with
          | Map ->
              let some f =
                List.concat (List.mapi (fun i m -> Option.to_list (f i m)) ms)
              in
              Printf.sprintf "(fun ((%s) as p) -> %sif %s then p else (%s))" pat
                (String.concat ""
                   (some (fun i ->
                        Option.map (fun m ->
                            Printf.sprintf "let %s = %s %s in " (b i) m (a i)))))
                (String.concat " && "
                   (some (fun i ->
                        Option.map (fun _ ->
                            Printf.sprintf "%s == %s" (b i) (a i)))))
                (String.concat ", "
                   (List.mapi (fun i m -> if m = None then a i else b i) ms))
          | Iter ->
              Printf.sprintf "(fun (%s) -> %s)" pat
                (String.concat "; "
                   (List.concat
                      (List.mapi
                         (fun i m ->
                           match m with
                           | Some m -> [ Printf.sprintf "%s %s" m (a i) ]
                           | None -> [])
                         ms)))
          | Exists ->
              Printf.sprintf "(fun (%s) -> %s)" pat
                (String.concat " || "
                   (List.concat
                      (List.mapi
                         (fun i m ->
                           match m with
                           | Some m -> [ Printf.sprintf "%s %s" m (a i) ]
                           | None -> [])
                         ms))))
    | TData d -> Some (Printf.sprintf "(%s f)" (trav_name act target d))
    | _ -> None

(** The body of [act] on the constructor [name] with the arguments [args], named
    [vars] ([(variable, type, kind of the argument)]), which [rebuild] makes the
    result of for [Map], from the names of the arguments: the children are done
    in order, whatever the evaluation order of OCaml. If [f] returns every child
    unchanged ([==]), [Map] returns [orig] and rebuilds nothing. *)
let trav_body ?(indent = "      ") act target ~orig ~rebuild
    (args : (string * ty * [ `Small | `Arg ]) list) =
  let ms = List.map (fun (x, t, _) -> (x, mapper act target t)) args in
  let var x =
    "y_"
    ^ String.concat ""
        (List.filter_map
           (function
             | '.' -> Some "_"
             | '\\' | '#' -> None
             | c -> Some (String.make 1 c))
           (List.of_seq (String.to_seq x)))
  in
  match act with
  | Map ->
      let mapped =
        List.filter_map (fun (x, m) -> Option.map (fun m -> (x, m)) m) ms
      in
      if mapped = [] then orig
      else
        String.concat ""
          (List.map
             (fun (x, m) ->
               Printf.sprintf "let %s = %s %s in\n%s" (var x) m x indent)
             mapped)
        ^ Printf.sprintf "if %s then %s else "
            (String.concat " && "
               (List.map
                  (fun (x, _) -> Printf.sprintf "%s == %s" (var x) x)
                  mapped))
            orig
        ^ rebuild
            (List.map2
               (fun (x, m) (_, _, k) ->
                 let v = if m = None then x else var x in
                 (v, k))
               ms args)
  | Iter ->
      String.concat "; "
        (List.concat_map
           (function
             | x, Some m -> [ Printf.sprintf "%s %s" m x ] | _, None -> [])
           ms)
  | Exists ->
      String.concat " || "
        (List.concat_map
           (function
             | x, Some m -> [ Printf.sprintf "%s %s" m x ] | _, None -> [])
           ms)

(** The functions that traverse the types of the language that contain values of
    the type [target], in one recursive group for each [act]. *)
let decl_traversals ft target =
  let decls =
    List.filter
      (fun (d : decl) ->
        (not (Check.generated_type d.d_name))
        && Syntax.mentions target (TData d.d_name))
      !lang.decls
  in
  List.iter
    (fun act ->
      List.iteri
        (fun i (d : decl) ->
          let name = trav_name act target d.d_name in
          let res =
            match act with
            | Map -> id d.d_name
            | Iter -> "unit"
            | Exists -> "bool"
          in
          let body =
            if d.d_fields <> [] then
              let args =
                List.map (fun (f, t) -> ("x." ^ id f, t, `Arg)) d.d_fields
              in
              trav_body ~indent:"  " act target ~orig:"x"
                ~rebuild:(fun vs ->
                  Printf.sprintf "{ x with %s }"
                    (String.concat "; "
                       (List.concat
                          (List.map2
                             (fun (f, _) (v, _) ->
                               if v = "x." ^ id f then []
                               else [ Printf.sprintf "%s = %s" (id f) v ])
                             d.d_fields vs))))
                args
            else
              let cases =
                List.filter_map
                  (fun (c : constr) ->
                    if c.c_res <> TData d.d_name then None
                    else
                      let args =
                        List.mapi
                          (fun i a ->
                            ( Printf.sprintf "a%d" (i + 1),
                              arg_ty a,
                              match a with Small -> `Small | Arg _ -> `Arg ))
                          c.c_args
                      in
                      let pat =
                        match args with
                        | [] -> c.c_name
                        | l ->
                            Printf.sprintf "%s (%s)" c.c_name
                              (String.concat ", "
                                 (List.map (fun (x, _, _) -> x) l))
                      in
                      let body =
                        trav_body act target ~orig:"x"
                          ~rebuild:(fun vs ->
                            match vs with
                            | [] -> c.c_name
                            | l ->
                                Printf.sprintf "%s (%s)" c.c_name
                                  (String.concat ", " (List.map fst l)))
                          args
                      in
                      let body =
                        if body = "" then
                          match act with
                          | Map -> "x"
                          | Iter -> "()"
                          | Exists -> "false"
                        else body
                      in
                      Some (Printf.sprintf "  | %s ->\n      %s" pat body))
                  !lang.constrs
              in
              "match x with\n" ^ String.concat "\n" cases
          in
          let body =
            if body = "" then
              match act with Map -> "x" | Iter -> "()" | Exists -> "false"
            else body
          in
          pf ft "%s"
            (Printf.sprintf "%s %s f (x : %s) : %s =\n  %s\n\n"
               (if i = 0 then "let rec" else "and")
               name (id d.d_name) res body))
        decls)
    [ Map; Iter; Exists ]

(** The nodes, with the types of their parameters and of their operands. *)
let trav_nodes () =
  List.filter_map
    (fun (c : constr) ->
      if
        (c.c_res = TKind && not (List.mem c.c_name !lang.node_kinds))
        || Option.is_some (Check.node_of_op c)
      then
        Some
          (c, match Check.node_of_op c with Some (_, ops) -> ops | None -> [])
      else None)
    !lang.constrs

(** The traversals of the terms and of the sorts, generated for the language
    that has [[@@@traversals]]: for every node, a case of [map_children],
    [iter_children] and [exists_child], and for every sort constructor one of
    [map_ty_children], ... The children of a node are the values of type [t] in
    its parameters and operands (see {!mapper}). *)
let traversals ft =
  let nodes = trav_nodes () in
  (* the maps of the lists and arrays return their argument if [f] returns each
     element unchanged; the array one only if the language has arrays, which
     need OCaml 5.4 *)
  pf ft "%s"
    "let rec kanon__list_map f l =\n\
    \  match l with\n\
    \  | [] -> l\n\
    \  | x :: r ->\n\
    \      let y = f x in\n\
    \      let s = kanon__list_map f r in\n\
    \      if y == x && s == r then l else y :: s\n\n";
  let rec has_array = function
    | TArray _ -> true
    | TList t | TOption t -> has_array t
    | TTuple l -> List.exists has_array l
    | _ -> false
  in
  if
    List.exists
      (fun (c : constr) -> List.exists (fun a -> has_array (arg_ty a)) c.c_args)
      !lang.constrs
    || List.exists
         (fun (d : decl) -> List.exists (fun (_, t) -> has_array t) d.d_fields)
         !lang.decls
    || List.exists (fun (_, ops) -> List.exists has_array ops) nodes
  then
    pf ft "%s"
      "let rec kanon__iarray_map_from f a i =\n\
      \  if i = Stdlib.Iarray.length a then a\n\
      \  else\n\
      \    let x = Stdlib.Iarray.get a i in\n\
      \    let y = f x in\n\
      \    if y == x then kanon__iarray_map_from f a (i + 1)\n\
      \    else\n\
      \      Stdlib.Iarray.init (Stdlib.Iarray.length a) (fun j ->\n\
      \          if j < i then Stdlib.Iarray.get a j\n\
      \          else if j = i then y\n\
      \          else f (Stdlib.Iarray.get a j))\n\n\
       let kanon__iarray_map f a = kanon__iarray_map_from f a 0\n\n";
  decl_traversals ft TTerm;
  decl_traversals ft TSty;
  let node_case act (c, operands) =
    let params = List.map (fun a -> arg_ty a) c.c_args in
    let kinds =
      List.map (function Small -> `Small | Arg _ -> `Arg) c.c_args
    in
    let ps = List.mapi (fun i t -> (Printf.sprintf "p%d" (i + 1), t)) params in
    let xs =
      List.mapi (fun i t -> (Printf.sprintf "x%d" (i + 1), t)) operands
    in
    let args =
      List.map2 (fun (x, t) k -> (x, t, k)) ps kinds
      @ List.map (fun (x, t) -> (x, t, `Arg)) xs
    in
    if List.for_all (fun (_, t, _) -> mapper act TTerm t = None) args then None
    else
      let ctor =
        match ps with
        | [] -> c.c_name
        | l ->
            Printf.sprintf "%s (%s)" c.c_name
              (String.concat ", " (List.map fst l))
      in
      let pat =
        match Check.node_of_op c with
        | Some (kc, _) ->
            Printf.sprintf "{ kind = %s (%s); _ }" kc.c_name
              (String.concat ", " (ctor :: List.map fst xs))
        | None -> Printf.sprintf "{ kind = %s; _ }" ctor
      in
      let typed = List.mem_assoc c.c_name !Check.node_typings in
      let body =
        trav_body act TTerm ~orig:"v"
          ~rebuild:(fun vs ->
            Printf.sprintf "kanon__rebuild_%s%s%s" c.c_name
              (if typed then "" else " v.ty")
              (String.concat ""
                 (List.map
                    (fun (v, k) ->
                      if k = `Small then Printf.sprintf " (Z.of_int %s)" v
                      else " " ^ v)
                    vs)))
          args
      in
      Some (Printf.sprintf "  | %s ->\n      %s\n" pat body)
  in
  let map_doc =
    "One level: [f] on each direct child, in order; does not recurse. [v] \
     itself if [f] returns every child unchanged ([==]), else [v] rebuilt."
  and iter_doc =
    "One level: [f] on each direct child, in order; does not recurse."
  and exists_doc =
    "One level: whether [f] holds for a direct child, from the left; does not \
     recurse."
  and for_all_doc =
    "One level: whether [f] holds for every direct child, from the left; does \
     not recurse."
  in
  let fn_terms doc act name ty_f res default =
    pf ft "%s"
      (Printf.sprintf
         "(** %s *)\n\
          let %s (f : %s) (v : t) : %s =\n\
         \  match v with\n\
          %s  | _ -> %s\n\n"
         doc name ty_f res
         (String.concat "" (List.filter_map (node_case act) nodes))
         default)
  in
  fn_terms map_doc Map "map_children" "t -> t" "t" "v";
  fn_terms iter_doc Iter "iter_children" "t -> unit" "unit" "()";
  fn_terms exists_doc Exists "exists_child" "t -> bool" "bool" "false";
  pf ft "%s"
  @@ Printf.sprintf "(** %s *)\n%s" for_all_doc
       "let for_all_child (f : t -> bool) (v : t) : bool =\n\
       \  not (exists_child (fun c -> not (f c)) v)\n\n";
  (* the sorts *)
  let sorts = List.filter (fun (c : constr) -> c.c_res = TSty) !lang.constrs in
  let sort_case act (c : constr) =
    let args =
      List.mapi
        (fun i a ->
          ( Printf.sprintf "p%d" (i + 1),
            arg_ty a,
            match a with Small -> `Small | Arg _ -> `Arg ))
        c.c_args
    in
    if List.for_all (fun (_, t, _) -> mapper act TSty t = None) args then None
    else
      let pat =
        match args with
        | [] -> c.c_name
        | l ->
            Printf.sprintf "%s (%s)" c.c_name
              (String.concat ", " (List.map (fun (x, _, _) -> x) l))
      in
      let body =
        trav_body act TSty ~orig:"v"
          ~rebuild:(fun vs ->
            Printf.sprintf "%s (%s)" c.c_name
              (String.concat ", " (List.map fst vs)))
          args
      in
      Some (Printf.sprintf "  | %s ->\n      %s\n" pat body)
  in
  let fn_sorts doc act name ty_f res default =
    pf ft "%s"
      (Printf.sprintf
         "(** %s *)\n\
          let %s (f : %s) (v : ty) : %s =\n\
         \  match v with\n\
          %s  | _ -> %s\n\n"
         doc name ty_f res
         (String.concat "" (List.filter_map (sort_case act) sorts))
         default)
  in
  fn_sorts map_doc Map "map_ty_children" "ty -> ty" "ty" "v";
  fn_sorts iter_doc Iter "iter_ty_children" "ty -> unit" "unit" "()";
  fn_sorts exists_doc Exists "exists_ty_child" "ty -> bool" "bool" "false";
  pf ft "%s"
  @@ Printf.sprintf "(** %s *)\n%s" for_all_doc
       "let for_all_ty_child (f : ty -> bool) (v : ty) : bool =\n\
       \  not (exists_ty_child (fun c -> not (f c)) v)\n\n"

let program ~sources ft (p : program) =
  check_prims p;
  let groups = sccs p.fns in
  let consts =
    List.concat_map
      (function
        | [ f ] when f.params = [] && not (is_recursive [ f ]) -> [ f.name ]
        | _ -> [])
      groups
  in
  let ctx =
    { prims = List.map (fun p -> p.pname) p.prims; consts; public = false }
  in
  let mods = module_entries p in
  check_names p;
  header ~sources ft;
  prim_sigs ft p;
  pf ft "%a@ " ocaml_doc
    "The functions of the language, in one recursive group, by their flat \
     name: the module in lowercase, an underscore, and the name. The modules \
     below are their names. Not meant to be used.";
  pf ft "@[<v 2>module Kanon_flat = struct";
  List.iteri
    (fun n group ->
      let kw =
        match group with
        | _ when is_recursive group -> "let rec"
        | [ f ] when f.params <> [] && weight f.body <= 12 -> "let[@inline]"
        | _ -> "let"
      in
      List.iteri
        (fun i f ->
          if n > 0 && i = 0 then pf ft "@ ";
          pf ft "@ @[<hv 2>%s %a@]" (if i = 0 then kw else "and") (fn ctx) f)
        group)
    groups;
  pf ft "@]@ end@ @ ";
  if !lang.traversals then (
    pf ft "%a@ open Kanon_flat@ @ " ocaml_doc
      "The traversals of the terms and sorts, which are not in a module.";
    traversals ft);
  List.iter
    (fun (m, entries) ->
      pf ft "%a@ " ocaml_doc
        (Fmt.str "The Kanon module %s." (String.uncapitalize_ascii m));
      pf ft "@[<v 2>module %s = struct" m;
      let prev = ref false in
      List.iteri
        (fun i (e : entry) ->
          pf ft "@ ";
          if i > 0 && (e.block || e.doc <> None || !prev) then pf ft "@ ";
          prev := e.block || e.doc <> None;
          doc ft e.doc;
          e.print ft)
        entries;
      pf ft "@]@ end@ @ ")
    mods;
  pf ft "@]@."

(* ---------------------------------------------------------------- *)
(* The types *)

(** The constructors of the declared type [d]. *)
let constrs_of (d : decl) =
  List.filter (fun c -> decl_name c.c_res = Some d.d_name) !lang.constrs

(** Checks that the abstract types have OCaml types ([[@ocaml]]); [t] and [ty]
    may be empty instead. *)
let check_abstract (d : decl) =
  if
    constrs_of d = []
    && d.d_fields = []
    && d.d_ocaml = None
    && not (d.d_name = "kind" || d.d_name = "ty")
  then
    raise
      (Check.Error
         ( d.d_loc,
           Fmt.str "type %s is abstract: [@ocaml \"M.t\"] gives its OCaml type"
             d.d_name ))

(** The OCaml definition of the declared type [d], after [type] or [and]: an
    abstract type is its [[@ocaml]] type, and a record or a variant with an
    [[@ocaml]] type re-exports it, so that OCaml checks that they agree. *)
let type_def ft (d : decl) =
  let reexport ft = Option.iter (pf ft " %s =") in
  let arg ft = function Small -> pf ft "int" | Arg t -> ocaml_ty ft t in
  match (constrs_of d, d.d_fields, d.d_ocaml) with
  | [], [], Some o -> pf ft "%s = %s" (id d.d_name) o
  | [], [], None -> pf ft "%s = |" (id d.d_name)
  | [], fields, o ->
      pf ft "%s =%a {" (id d.d_name) reexport o;
      List.iter (fun (f, t) -> pf ft "@ %s : %a;" (id f) ocaml_ty t) fields;
      pf ft "@;<1 -2>}"
  | cs, _, o ->
      pf ft "%s =%a" (id d.d_name) reexport o;
      List.iter
        (fun c ->
          match c.c_args with
          | [] -> pf ft "@ | %s%a" c.c_name doc_after c.c_doc
          | args ->
              pf ft "@ | %s of %a%a" c.c_name (list ~sep:" * " arg) args
                doc_after c.c_doc)
        cs

(** The equality [equal_d] and the hash [hash_d] of the type [d], in a recursive
    definition: structural, but of the tags of terms, and on abstract types,
    [[@equal]] (or [Stdlib.( = )]) and [[@hash]] (or [Hashtbl.hash]). A
    constructor is hashed by its index, combined with its arguments. *)
let eq_hash_def ft (d : decl) =
  let n = d.d_name in
  let ty = id n in
  (* the arguments of the constructor [c], as variables [x1], [x2], ... *)
  let args x (c : constr) =
    List.mapi (fun i a -> (a, Printf.sprintf "%s%d" x (i + 1))) c.c_args
  in
  let pat x (c : constr) =
    match args x c with
    | [] -> c.c_name
    | [ (_, a) ] -> Printf.sprintf "%s %s" c.c_name a
    | l ->
        Printf.sprintf "%s (%s)" c.c_name (String.concat ", " (List.map snd l))
  in
  let equal ft = function
    | Small, a, b -> pf ft "Int.equal %s %s" a b
    | Arg t, a, b -> pf ft "%a %s %s" equal_fn t a b
  in
  let hash ft = function
    | `Index i -> pf ft "%d" i
    | `Arg (Small, x) -> pf ft "%s" x
    | `Arg (Arg t, x) -> pf ft "%a %s" hash_fn t x
  in
  let conj ft =
    pf ft "@[<hov>%a@]"
      (Format.pp_print_list ~pp_sep:(fun ft () -> pf ft " &&@ ") equal)
  in
  match (constrs_of d, d.d_fields) with
  | [], [] when d.d_ocaml = None ->
      (* an empty type *)
      pf ft "and equal_%s (_ : %s) (_ : %s) = true@ @ and hash_%s (_ : %s) = 0"
        n ty ty n ty
  | [], [] ->
      pf ft
        "and equal_%s (a : %s) (b : %s) = %s a b@ @ and hash_%s (a : %s) = %s a"
        n ty ty
        (Option.value d.d_equal ~default:"Stdlib.( = )")
        n ty
        (Option.value d.d_hash ~default:"Hashtbl.hash")
  | [], fields ->
      let fs x = List.map (fun (f, t) -> (Arg t, x ^ "." ^ id f)) fields in
      pf ft "@[<hv 2>and equal_%s (a : %s) (b : %s) =@ %a@]@ @ " n ty ty conj
        (List.map2 (fun (t, a) (_, b) -> (t, a, b)) (fs "a") (fs "b"));
      pf ft "@[<hv 2>and hash_%s (a : %s) =@ %a@]" n ty (combine hash)
        (List.map (fun a -> `Arg a) (fs "a"))
  | cs, _ ->
      pf ft "@[<v 2>and equal_%s (a : %s) (b : %s) =@ match (a, b) with" n ty ty;
      List.iter
        (fun c ->
          pf ft "@ @[<hv 4>| %s, %s ->@ %a@]" (pat "a" c) (pat "b" c)
            (fun ft -> function [] -> pf ft "true" | l -> conj ft l)
            (List.map2
               (fun (t, a) (_, b) -> (t, a, b))
               (args "a" c) (args "b" c)))
        cs;
      if List.length cs > 1 then pf ft "@ | _ -> false";
      pf ft "@]@ @ @[<v 2>and hash_%s (a : %s) =@ match a with" n ty;
      List.iteri
        (fun i c ->
          match args "a" c with
          | [] -> pf ft "@ | %s -> %d" (pat "a" c) i
          | l ->
              pf ft "@ @[<hv 4>| %s ->@ %a@]" (pat "a" c) (combine hash)
                (`Index i :: List.map (fun a -> `Arg a) l))
        cs;
      pf ft "@]"

(** The types of the language, standalone: one recursive group, with terms
    hash-consed records [{ kind; ty; tag }], where [kind] are the leaf nodes and
    the operators of each arity; their equalities and hashes; and [node], the
    hash-consed term of a kind and a type, in a table of ephemerons keyed on the
    terms (which equalities and hashes ignore their tags). The tags of terms are
    unique, and increase with their creation. The table is not safe across
    domains (TODO). *)
let types ~sources ft =
  List.iter check_abstract !lang.decls;
  pf ft "@[<v>(* Generated by kanon from %a. Do not edit. *)@ @ "
    (list Format.pp_print_string)
    sources;
  pf ft "[@@@@@@warning \"-a\"]@ @ ";
  List.iteri
    (fun i d ->
      pf ft "%a@[<v 2>%s %a@]@ @ " doc d.d_doc
        (if i = 0 then "type" else "and")
        type_def d)
    !lang.decls;
  pf ft "@[<v 2>and t = {@ kind : kind;@ ty : ty;@ tag : int;@;<1 -2>}@]@ @ ";
  pf ft "let hash_combine x y = (x * 65599) + y@ @ ";
  pf ft "let rec equal_t (a : t) (b : t) = Int.equal a.tag b.tag@ @ ";
  pf ft "and hash_t (a : t) = a.tag@ @ ";
  List.iter (fun d -> pf ft "%a@ @ " eq_hash_def d) !lang.decls;
  pf ft "(* Not safe across domains (TODO). *)@ ";
  pf ft "@[<v 2>let node : kind -> ty -> t =@ ";
  pf ft "@[<v 2>let module H = Ephemeron.K1.Make (struct@ type nonrec t = t@ ";
  pf ft
    "let equal (a : t) (b : t) = equal_kind a.kind b.kind && equal_ty a.ty \
     b.ty@ ";
  pf ft "let hash (a : t) = hash_combine (hash_kind a.kind) (hash_ty a.ty)@]@ ";
  pf ft "end) in@ let table = H.create 1024 and tags = ref 0 in@ ";
  pf ft "@[<v 2>fun kind ty ->@ let v : t = { kind; ty; tag = -1 } in@ ";
  pf ft "@[<v>match H.find table v with@ | t -> t@ ";
  pf ft "@[<v 2>| exception Not_found ->@ ";
  pf ft "let t = { v with tag = !tags } in@ incr tags;@ H.add table t t;@ ";
  pf ft "t@]@]@]@]@]@."
