(** The command line of kanon, [kanon BACKEND FILE...] (see {!Main}), as a
    function, for kanon and for its web runtime. *)

(** The parts of the generated Lean files (see {!Gen_lean.parts}), whose
    backends are [lean-PART]. *)
let lean_parts ~module_only ~lang ~has_proof prog =
  Gen_lean.parts ~module_only ~lang ~has_proof prog

(** The backends that write on standard output, in the order of the usage. *)
let backends =
  [ "ocaml-types"; "ocaml"; "ocaml-typed"; "ocaml-tests" ]
  @ List.map
      (fun (part, _) -> "lean-" ^ part)
      (lean_parts ~module_only:false ~lang:[]
         ~has_proof:(fun _ _ -> false)
         (lazy (assert false)))

(** The end of the command, with its exit code. *)
exception Exit_code of int

let usage err =
  Format.fprintf err "%s@."
    ("usage: kanon ("
    ^ String.concat " | " backends
    ^ ") FILE...\n\
      \       kanon lean-all [--check] DIR FILE...\n\
      \       kanon lsp\n\
      \       kanon --version\n\
       Files use modules with use \"path\", or use builtin \"name\" for those \
       built into kanon: "
    ^ String.concat ", "
        (List.sort_uniq compare
           (List.map
              (fun (n, _) -> Printf.sprintf "%S" (Filename.remove_extension n))
              Builtin.files)));
  raise (Exit_code 2)

(** What [f] prints on a formatter, as a string. *)
let to_string f =
  let b = Buffer.create 4096 in
  let ft = Format.formatter_of_buffer b in
  f ft;
  Format.pp_print_flush ft ();
  Buffer.contents b

(** The contents of a generated file. *)
let contents (f : Gen_lean.file) = to_string f.contents

let read_file name = In_channel.with_open_bin name In_channel.input_all

(** The kind of the file [p], which is [S_LNK] for a symbolic link (not
    followed), or [None] if there is no such file. *)
let kind p =
  match (Unix.lstat p).Unix.st_kind with
  | k -> Some k
  | exception Unix.Unix_error _ -> None

(** The files under the directory [d], recursively, with the symbolic links and
    the other special files, which are not followed. *)
let rec tree_files d =
  List.concat_map
    (fun n ->
      let p = Filename.concat d n in
      match kind p with
      | Some Unix.S_DIR -> tree_files p
      | Some _ -> [ p ]
      | None -> [])
    (List.sort compare (Array.to_list (Sys.readdir d)))

(** Removes [p] and what is under it, without following symbolic links. *)
let rec remove_tree p =
  match kind p with
  | Some Unix.S_DIR ->
      Array.iter (fun n -> remove_tree (Filename.concat p n)) (Sys.readdir p);
      Sys.rmdir p
  | Some _ -> Sys.remove p
  | None -> ()

let rec mkdir_p d =
  if not (Sys.file_exists d) then (
    mkdir_p (Filename.dirname d);
    Sys.mkdir d 0o755)

let fail fmt =
  Format.kasprintf (fun s -> raise (Check.Error (Location.none, s))) fmt

(** Fails unless [dir/rel] is a place where kanon may delete and write: [dir] is
    a directory, and none of the parts of [rel] that exist is a symbolic link or
    a file, so that kanon deletes nothing outside [dir]. *)
let check_generated_dir dir rel =
  if Sys.file_exists dir && not (Sys.is_directory dir) then
    fail "%s is not a directory" dir;
  ignore
    (List.fold_left
       (fun (p, exists) part ->
         let p = Filename.concat p part in
         if not exists then (p, false)
         else
           match kind p with
           | None -> (p, false)
           | Some Unix.S_DIR -> (p, true)
           | Some Unix.S_LNK ->
               fail "%s is a symbolic link: kanon does not follow it" p
           | Some _ -> fail "%s is not a directory" p)
       (dir, true)
       (String.split_on_char '/' rel))

(** [generated_all ~cmd ~check ~err dir trees], for the command [cmd], writes
    [trees] under [dir]: each is a directory [rel], relative to [dir], that is
    entirely generated, and the files [(name, text)] that it has, with the
    [name] relative to [dir]. Each directory is deleted, with all that it holds
    and nothing else, then written again, but only once all the places are known
    to be safe. With [check], nothing is written: it is whether each directory
    is exactly as it would be written, and the files that are missing, out of
    date, or that kanon would not write are reported on [err]. *)
let generated_all ~cmd ~check ~err dir
    (trees : (string * (string * string) list) list) =
  List.iter (fun (rel, _) -> check_generated_dir dir rel) trees;
  let ok = ref true in
  let report fmt =
    ok := false;
    Format.fprintf err ("kanon: " ^^ fmt ^^ "@.")
  in
  List.iter
    (fun (rel, files) ->
      let root = Filename.concat dir rel in
      if check then (
        let names = Hashtbl.create 64 in
        List.iter
          (fun (name, text) ->
            let name = Filename.concat dir name in
            Hashtbl.replace names name ();
            (* dune's sandboxes are made of symbolic links to files *)
            if not (Sys.file_exists name) then
              report "%s is missing (run kanon %s)" name cmd
            else if try read_file name <> text with Sys_error _ -> true then
              report "%s is not up to date (run kanon %s)" name cmd)
          files;
        if Sys.file_exists root then
          List.iter
            (fun name ->
              if not (Hashtbl.mem names name) then
                report "%s is no longer generated (run kanon %s)" name cmd)
            (tree_files root))
      else (
        remove_tree root;
        List.iter
          (fun (name, text) ->
            let name = Filename.concat dir name in
            mkdir_p (Filename.dirname name);
            Out_channel.with_open_bin name (fun oc ->
                Out_channel.output_string oc text))
          files))
    trees;
  !ok

(** [kanon lean-all [--check] DIR]: writes the generated Lean files [files]
    under [dir], each in the directory [Generated] of the directory of its root
    (see {!generated_all}). *)
let lean_all ~check ~err dir (files : Gen_lean.file list) =
  let seen = Hashtbl.create 64 in
  List.iter
    (fun (f : Gen_lean.file) ->
      let name = Gen_lean.file_name f in
      if Hashtbl.mem seen name then
        fail
          "two modules write the Lean file %s: give them different roots with \
           [@@@lean_root]"
          name
      else Hashtbl.add seen name ())
    files;
  let roots =
    List.sort_uniq compare (List.map (fun (f : Gen_lean.file) -> f.froot) files)
  in
  let texts = List.map (fun f -> (f, contents f)) files in
  generated_all ~cmd:"lean-all" ~check ~err dir
    (List.map
       (fun root ->
         ( Gen_lean.generated_dir root,
           List.filter_map
             (fun ((f : Gen_lean.file), text) ->
               if f.froot = root then Some (Gen_lean.file_name f, text)
               else None)
             texts ))
       roots)

(** [run args out err] runs [kanon args] (without [lsp]), writing on [out] and
    [err] for standard output and error, and is its exit code. Exceptions other
    than the errors of the files are raised. *)
let run args out err =
  try
    match args with
    | [ "--version" ] ->
        Format.fprintf out "%s@." Version.version;
        0
    | backend :: args -> (
        let target, files =
          match (backend, args) with
          | ("lean-all" | "ocaml-all"), "--check" :: dir :: files ->
              (Some (true, dir), files)
          | ("lean-all" | "ocaml-all"), dir :: files ->
              (Some (false, dir), files)
          | ("lean-all" | "ocaml-all"), [] -> usage err
          | _ -> (None, args)
        in
        try
          if files = [] then usage err;
          Gen_lean.module_uses := [];
          Gen_lean.builtin_modules := [];
          Gen_lean.root_module := None;
          Gen_lean.module_files := [];
          let on_parse f str =
            match Check.module_of_file ~loc:Location.none f with
            | Some m ->
                if !Gen_lean.root_module = None then
                  Gen_lean.root_module := Some m;
                if Option.is_some (Loader.builtin f) then
                  Gen_lean.builtin_modules := m :: !Gen_lean.builtin_modules;
                let uses =
                  List.filter_map
                    (fun (u, _) -> Check.module_of_file ~loc:Location.none u)
                    (fst (Loader.uses str))
                in
                let old =
                  Option.value ~default:[]
                    (List.assoc_opt m !Gen_lean.module_uses)
                in
                Gen_lean.module_uses :=
                  (m, old @ uses) :: List.remove_assoc m !Gen_lean.module_uses;
                let fs =
                  Option.value ~default:[]
                    (List.assoc_opt m !Gen_lean.module_files)
                in
                Gen_lean.module_files :=
                  (m, fs @ [ Loader.source_name f ])
                  :: List.remove_assoc m !Gen_lean.module_files
            | None -> ()
          in
          let langs, files =
            try Loader.load ~on_parse files with
            | Loader.No_builtin f ->
                Format.fprintf err "kanon: %s: no such built-in module file@." f;
                usage err
            | Loader.Missing (_, msg) ->
                Format.fprintf err "kanon: %s@." msg;
                raise (Exit_code 1)
          in
          if langs = [] then usage err;
          Check.language (List.concat_map snd langs);
          let prog =
            lazy
              (if files = [] then usage err;
               Check.program (List.concat_map snd files))
          in
          let lang = List.map (fun (f, _) -> Loader.source_name f) langs in
          let sources = List.map (fun (f, _) -> Loader.source_name f) files in
          (* a module built into kanon, given alone: only its own files *)
          let module_only =
            match langs with
            | (f, _) :: _ -> Option.is_some (Loader.builtin f)
            | [] -> false
          in
          let lean has_proof =
            lean_parts ~module_only ~lang ~has_proof
              (lazy (Check.program (List.concat_map snd files)))
          in
          match (target, backend) with
          | Some (check, dir), _ ->
              let has_proof r path =
                Sys.file_exists
                  (Filename.concat dir (Gen_lean.hand_file_name r path))
              in
              let files =
                List.concat_map (fun (_, gen) -> gen ()) (lean has_proof)
              in
              if lean_all ~check ~err dir files then 0 else 1
          | None, "ocaml-types" ->
              Gen_ocaml.types ~sources:lang out;
              0
          | None, "ocaml" ->
              Gen_ocaml.program ~sources out (Lazy.force prog);
              0
          | None, "ocaml-typed" ->
              Gen_typed.program ~sources:(lang @ sources) out (Lazy.force prog);
              0
          | None, "ocaml-tests" ->
              Gen_tests.program ~sources out (Lazy.force prog);
              0
          | None, _ -> (
              match
                List.assoc_opt backend
                  (List.map
                     (fun (part, gen) -> ("lean-" ^ part, gen))
                     (lean (fun _ _ -> false)))
              with
              | Some gen ->
                  (* the files of a part of several, each after its name *)
                  let files = gen () in
                  List.iteri
                    (fun i (f : Gen_lean.file) ->
                      if List.length files > 1 then
                        Format.fprintf out "%s-- %s@.@."
                          (if i > 0 then "\n" else "")
                          (Gen_lean.file_name f);
                      Format.fprintf out "%s@?" (contents f))
                    files;
                  0
              | None -> usage err)
        with Check.Error (loc, msg) ->
          if loc = Location.none then Format.fprintf err "kanon: %s@." msg
          else Format.fprintf err "%a: %s@." Check.pp_loc loc msg;
          1)
    | [] -> usage err
  with Exit_code code -> code
