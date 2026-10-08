(** Reading Kanon files with the modules they use, for the command line and the
    language server. *)

(** A file named [+name] on the command line that is not built into kanon.
    ([use builtin "name"] uses the file [+name], see [module_files].) *)
exception No_builtin of string

(** A [use] whose module has no file: the location of the [use], and the
    message. *)
exception Missing of Ppxlib.Location.t * string

(** The name of the built-in module file that [f] names ([+name]), if any. *)
let builtin f =
  if String.starts_with ~prefix:"+" f then
    Some (String.sub f 1 (String.length f - 1))
  else None

(** [read f] is the contents of [f] if the caller has it (an editor buffer),
    else it is read from the disk. *)
let parse_file ~read f =
  match builtin f with
  | None -> (
      match read f with
      | Some s -> Check.parse_string ~file:f s
      | None -> (
          try Check.parse_file f
          with Sys_error m ->
            let prefix = f ^ ": " in
            raise
              (Check.Error
                 ( Location.none,
                   if String.starts_with ~prefix m then m else prefix ^ m ))))
  | Some name -> (
      match List.assoc_opt name Builtin.files with
      | Some s -> Check.parse_string ~file:f s
      | None -> raise (No_builtin f))

(** The name of the file [f] in the headers of the generated files. *)
let source_name f = Filename.basename (Option.value (builtin f) ~default:f)

let exists ~read f =
  match builtin f with
  | Some name -> List.mem_assoc name Builtin.files
  | None -> Option.is_some (read f) || Sys.file_exists f

(** [p] without its [.] and [..] segments, if it is absolute, so that a file has
    one name (relative paths are kept as given, for the messages). *)
let normalize p =
  if Filename.is_relative p then p
  else
    let parts =
      List.fold_left
        (fun acc s ->
          match (s, acc) with
          | ("" | "."), _ -> acc
          | "..", _ :: acc -> acc
          | "..", [] -> []
          | s, _ -> s :: acc)
        []
        (String.split_on_char '/' p)
    in
    "/" ^ String.concat "/" (List.rev parts)

(** The name of the file [f] that is the same for every path to it. *)
let canonical f =
  if Option.is_some (builtin f) then f
  else if Filename.is_relative f then
    normalize (Filename.concat (Sys.getcwd ()) f)
  else normalize f

(** The file names of the module [m] used from the directory [dir], existing or
    not: its declarations, then its rules. *)
let module_files dir m =
  let base =
    if String.starts_with ~prefix:"+" m || not (Filename.is_relative m) then m
    else Filename.concat dir m
  in
  (base, [ normalize (base ^ ".knl"); normalize (base ^ ".kn") ])

(** The modules that [items] use, with the locations of their [use]s, and
    [items] without their [use]s. *)
let uses (items : Ppxlib.structure) =
  List.partition_map
    (fun (si : Ppxlib.structure_item) ->
      match si.pstr_desc with
      | Pstr_extension
          ( ( { txt = "kanon.use"; _ },
              PStr
                [
                  {
                    pstr_desc =
                      Pstr_eval
                        ( {
                            pexp_desc = Pexp_constant (Pconst_string (m, _, _));
                            _;
                          },
                          _ );
                    _;
                  };
                ] ),
            _ ) ->
          Left (m, si.pstr_loc)
      | _ -> Right si)
    items

(** The declarations and the rules of [files] and of the modules they use, as
    [(file, items)] lists, in order. [resolve f] is the file that the file [f]
    of a module stands for ([f] by default), and [on_parse f items] is called on
    each file once it is parsed, with its [use]s. *)
let load ?(read = fun _ -> None) ?(resolve = Fun.id) ?(on_parse = fun _ _ -> ())
    files =
  let loaded = Hashtbl.create 8 in
  let decls = ref [] and rules = ref [] in
  let rec file f =
    if not (Hashtbl.mem loaded (canonical f)) then (
      Hashtbl.add loaded (canonical f) ();
      let str = parse_file ~read f in
      on_parse f str;
      let ms, items = uses str in
      let is_decl = Filename.check_suffix f ".knl" in
      if is_decl then decls := !decls @ [ (f, items) ];
      List.iter (use (Filename.dirname f)) ms;
      if not is_decl then rules := !rules @ [ (f, items) ])
  and use dir (m, loc) =
    let base, fs = module_files dir m in
    match List.filter (exists ~read) (List.map resolve fs) with
    | [] ->
        raise
          (Missing
             ( loc,
               match builtin m with
               | Some name ->
                   Printf.sprintf
                     "use builtin %S: kanon has no built-in module %s (it has \
                      %s)"
                     name name
                     (String.concat ", "
                        (List.sort_uniq compare
                           (List.map
                              (fun (n, _) ->
                                Printf.sprintf "%S"
                                  (Filename.remove_extension n))
                              Builtin.files)))
               | None -> Printf.sprintf "use %S: no %s.knl or %s.kn" m base base
             ))
    | fs -> List.iter file fs
  in
  List.iter file (List.map normalize files);
  (!decls, !rules)
