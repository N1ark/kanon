(** Differential-testing backend. For every rule function, the output gives,
    from random arguments, its spec (the raw term), a call to it, and the name
    of the rule that fires, to be compared by evaluation. Like the output of
    {!Gen_ocaml}, it is meant to be included where the rule functions and the
    types of the language are in scope. *)

open Syntax

let pf = Format.fprintf

(** The expression that draws a value of type [t] from the source [src], if the
    source can produce one. *)
let rec draw t : (Format.formatter -> unit) option =
  let all f l =
    let l = List.map f l in
    if List.for_all Option.is_some l then Some (List.map Option.get l) else None
  in
  match t with
  | TInt -> Some (fun ft -> pf ft "(src.int ())")
  | TBool -> Some (fun ft -> pf ft "(src.bool ())")
  | TTerm -> Some (fun ft -> pf ft "(src.term ())")
  | TList TTerm -> Some (fun ft -> pf ft "(src.terms ())")
  | TTuple l ->
      Option.map
        (fun l ft -> pf ft "(%a)" (Gen_ocaml.list (fun ft d -> d ft)) l)
        (all draw l)
  | TData _ -> (
      match (decl_of_ty t).d_fields with
      | _ :: _ as fields ->
          Option.map
            (fun l ft ->
              pf ft "{ %a }"
                (Gen_ocaml.list ~sep:"; " (fun ft (f, d) -> pf ft "%s = %t" f d))
                (List.combine (List.map fst fields) l))
            (all (fun (_, t) -> draw t) fields)
      | [] -> (
          let constrs = List.filter (fun c -> c.c_res = t) !lang.constrs in
          match constrs with
          | _ :: _ when List.for_all (fun c -> c.c_args = []) constrs ->
              Some
                (fun ft ->
                  pf ft "(match src.choose %d with %a)" (List.length constrs)
                    (Gen_ocaml.list ~sep:" " (fun ft (i, c) ->
                         pf ft "| %s -> %s"
                           (if i = List.length constrs - 1 then "_"
                            else string_of_int i)
                           c.c_name))
                    (List.mapi (fun i c -> (i, c)) constrs))
          | _ -> None))
  | TUnit | TKind | TSty | TOption _ | TList _ -> None

(** The name of the rule of [body] that fires, where [body] is the body of a
    rule function. *)
let rec fired ctx ft (e : expr) =
  match e.e with
  | EAssert (c, body) ->
      pf ft "@[<v>(assert %a;@ %a)@]" (Gen_ocaml.expr ctx) c (fired ctx) body
  | EMatch (scruts, cases) ->
      let case ft (c : case) =
        let guard ft = function
          | None -> ()
          | Some g ->
              pf ft "@ when (%a%a)" (Gen_ocaml.small_lets g) c.pat
                (Gen_ocaml.expr ctx) g
        in
        pf ft "@[<hv 2>| %a%a ->@ %S@]@ " Gen_ocaml.pat c.pat guard c.guard
          (Option.value ~default:"main" c.rule)
      in
      pf ft "@[<v>(match %a with@ %a)@]"
        (Gen_ocaml.list (Gen_ocaml.expr ctx))
        scruts
        (Gen_ocaml.list ~sep:"" case)
        cases
  | _ -> pf ft "\"main\""

(** The names of the rules of [body], in order. *)
let rec rule_names (e : expr) =
  match e.e with
  | EAssert (_, body) -> rule_names body
  | EMatch (_, cases) ->
      List.fold_left
        (fun acc (c : case) ->
          let r = Option.value ~default:"main" c.rule in
          if List.mem r acc then acc else acc @ [ r ])
        [] cases
  | _ -> [ "main" ]

let rule_fn ctx ft (f : fn) (spec : expr) draws =
  pf ft "@[<v 2>( %S,@ [ %a ],@ fun src ->@ " f.name
    (Gen_ocaml.list ~sep:"; " (fun ft r -> pf ft "%S" r))
    (rule_names f.body);
  List.iter2 (fun (x, _) d -> pf ft "let %s = %t in@ " x d) f.params draws;
  pf ft "@[<v 2>{@ spec = (fun () -> %a);@ " (Gen_ocaml.expr ctx) spec;
  pf ft "call = (fun () -> %s%a);@ " f.name
    (fun ft -> List.iter (fun (x, _) -> pf ft " %s" x))
    f.params;
  pf ft "fired = (fun () -> %a);@]@ })@]" (fired ctx) f.body

let program ~sources ft (p : program) =
  Gen_ocaml.check_prims p;
  let consts =
    List.concat_map
      (function
        | [ f ] when f.params = [] && not (Gen_ocaml.is_recursive [ f ]) ->
            [ f.name ]
        | _ -> [])
      (Gen_ocaml.sccs p.fns)
  in
  let ctx = { Gen_ocaml.prims = List.map (fun p -> p.pname) p.prims; consts } in
  let rules = List.filter (fun f -> Option.is_some f.spec) p.fns in
  let drawable (f : fn) = List.map (fun (_, t) -> draw t) f.params in
  let tested, skipped =
    List.partition (fun f -> List.for_all Option.is_some (drawable f)) rules
  in
  Gen_ocaml.header ~sources ft;
  pf ft
    "@[<v 2>type source = {@ int : unit -> Z.t;@ bool : unit -> bool;@ term : \
     unit -> t;@ terms : unit -> t list;@ choose : int -> int;@]@ }@ @ ";
  pf ft
    "@[<v 2>type test = {@ spec : unit -> t;@ call : unit -> t;@ fired : unit \
     -> string;@]@ }@ @ ";
  pf ft
    "@[<v 2>let rule_fns : (string * string list * (source -> test)) list = [@ ";
  List.iter
    (fun f ->
      rule_fn ctx ft f (Option.get f.spec) (List.map Option.get (drawable f));
      pf ft ";@ ")
    tested;
  pf ft "@]]@ @ ";
  pf ft "let untested = [ %a ]@ @]@."
    (Gen_ocaml.list ~sep:"; " (fun ft f -> pf ft "%S" f.name))
    skipped
