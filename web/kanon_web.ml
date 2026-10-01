(** Kanon in a web page (in a Web Worker): the API [globalThis.kanon] that the
    site uses (see README.md), over the language server and the command line of
    kanon, which run on a virtual file system. *)

open Js_of_ocaml

(** The directory of the user's files, the current directory of [run]. *)
let root = "/sandbox"

(** [Unix.stat] and [Unix.lstat], which the language server uses to find the
    files of its workspace, on the devices in memory (stubs.js). *)
external fake_device_stat : unit -> unit = "kanon_fake_device_stat"

(** Devices in memory, at [root] and at the directory where the language server
    writes the built-in modules, in node as in a browser (where all files are in
    memory anyway). *)
let () =
  List.iter
    (fun d -> Sys_js.mount ~path:(d ^ "/") (fun ~prefix:_ ~path:_ -> None))
    [ root; Filename.dirname Lsp_server.builtin_dir ];
  fake_device_stat ()

(** The messages that the language server sends, last first. *)
let sent = ref []

let () = Lsp_rpc.output := fun s -> sent := s :: !sent

(** The messages sent by [f ()], in order. *)
let collect f =
  sent := [];
  (try f () with e -> prerr_endline ("kanon: " ^ Printexc.to_string e));
  let l = List.rev !sent in
  sent := [];
  Js.array (Array.of_list (List.map Js.string l))

(** [path] with [root] for its directory, if it is relative. *)
let absolute path =
  if Filename.is_relative path then Filename.concat root path else path

let rec mkdir_p d =
  if not (Sys.file_exists d) then (
    mkdir_p (Filename.dirname d);
    Sys.mkdir d 0o755)

let write_file path contents =
  let path = Loader.normalize (absolute path) in
  mkdir_p (Filename.dirname path);
  Out_channel.with_open_bin path (fun oc -> output_string oc contents)

let read_file path =
  try Some (In_channel.with_open_bin (absolute path) In_channel.input_all)
  with Sys_error _ -> None

let rec list_files dir =
  List.concat_map
    (fun n ->
      let p = Filename.concat dir n in
      if Sys.is_directory p then list_files p else [ p ])
    (List.sort compare
       (Array.to_list (try Sys.readdir dir with Sys_error _ -> [||])))

(** [kanon (args ())], with its exit code, standard output and standard error.
*)
let run args =
  let out = Buffer.create 65536 and err = Buffer.create 256 in
  let fout = Format.formatter_of_buffer out
  and ferr = Format.formatter_of_buffer err in
  let code =
    try
      let args = args () in
      Check.reset ();
      Sys.chdir root;
      Cli.run args fout ferr
    with e ->
      (* as kanon reports an exception that escapes *)
      Format.pp_print_flush ferr ();
      Buffer.add_string err
        ("Fatal error: exception " ^ Printexc.to_string e ^ "\n");
      2
  in
  Format.pp_print_flush fout ();
  Format.pp_print_flush ferr ();
  (code, Buffer.contents out, Buffer.contents err)

(** Raises a JavaScript [Error]. *)
let js_error msg =
  Js.Js_error.raise_
    (Js.Js_error.of_error
       (Js.Unsafe.new_obj
          (Js.Unsafe.get Js.Unsafe.global "Error")
          [| Js.Unsafe.inject (Js.string msg) |]))

(** [f], with its OCaml exceptions as JavaScript errors. *)
let guard f =
  try f () with
  | Js.Js_error.Exn _ as e -> raise e
  | e -> js_error (Printexc.to_string e)

let version = Version.v

let api =
  let open Js.Unsafe in
  let strings l = inject (Js.array (Array.of_list (List.map Js.string l))) in
  obj
    [|
      ("version", inject (Js.string version));
      ("root", inject (Js.string root));
      ( "writeFile",
        inject
          (Js.wrap_callback (fun path contents ->
               guard (fun () ->
                   write_file (Js.to_string path) (Js.to_string contents)))) );
      ( "removeFile",
        inject
          (Js.wrap_callback (fun path ->
               guard (fun () -> Sys.remove (absolute (Js.to_string path))))) );
      ( "readFile",
        inject
          (Js.wrap_callback (fun path ->
               match read_file (Js.to_string path) with
               | Some s -> Js.some (Js.string s)
               | None -> Js.null)) );
      ( "listFiles",
        inject
          (Js.wrap_callback (fun dir ->
               strings (list_files (absolute (Js.to_string dir))))) );
      ( "lsp",
        inject
          (Js.wrap_callback (fun message ->
               collect (fun () ->
                   match Yojson.Safe.from_string (Js.to_string message) with
                   | msg ->
                       (* the server would exit: the page does not *)
                       if Lsp_rpc.member "method" msg <> `String "exit" then
                         Lsp_server.handle msg
                   | exception Yojson.Json_error e ->
                       prerr_endline ("kanon: bad message: " ^ e)))) );
      ("check", inject (Js.wrap_callback (fun () -> collect Lsp_server.check)));
      ( "run",
        inject
          (Js.wrap_callback (fun args ->
               let code, stdout, stderr =
                 run (fun () ->
                     List.map Js.to_string (Array.to_list (Js.to_array args)))
               in
               obj
                 [|
                   ("code", inject code);
                   ("stdout", inject (Js.string stdout));
                   ("stderr", inject (Js.string stderr));
                 |])) );
      ("backends", strings Cli.backends);
      ( "builtins",
        obj
          (Array.of_list
             (List.map (fun (f, s) -> (f, inject (Js.string s))) Builtin.files))
      );
    |]

let () =
  Js.Unsafe.set Js.Unsafe.global "kanon" api;
  let ready = Js.Unsafe.get Js.Unsafe.global "onkanonready" in
  if Js.typeof ready = Js.string "function" then
    ignore (Js.Unsafe.fun_call ready [||])
