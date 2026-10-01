(** JSON-RPC over standard input and output, with the [Content-Length] framing
    of the Language Server Protocol. *)

let log fmt =
  if Option.is_some (Sys.getenv_opt "KANON_LSP_LOG") then
    Format.kfprintf (fun ft -> Format.fprintf ft "@.") Format.err_formatter fmt
  else Format.ifprintf Format.err_formatter fmt

(** The bytes read from standard input and not yet consumed. *)
let pending = Buffer.create 65536

let chunk = Bytes.create 65536

(** Reads what is available on standard input, waiting for it; [false] at the
    end of the input. *)
let fill () =
  match Unix.read Unix.stdin chunk 0 (Bytes.length chunk) with
  | 0 -> false
  | n ->
      Buffer.add_subbytes pending chunk 0 n;
      true
  | exception Unix.Unix_error (EINTR, _, _) -> true

(** The offset of the end of the header of a message in [s], if any. *)
let header_end s =
  let rec go i =
    if i + 4 > String.length s then None
    else if s.[i] = '\r' && String.sub s i 4 = "\r\n\r\n" then Some i
    else go (i + 1)
  in
  go 0

(** The first message of [pending], if it is complete: its body, and the length
    of the message. *)
let split () =
  let s = Buffer.contents pending in
  match header_end s with
  | None -> None
  | Some h ->
      let length =
        List.find_map
          (fun line ->
            match String.index_opt line ':' with
            | Some i
              when String.lowercase_ascii (String.trim (String.sub line 0 i))
                   = "content-length" ->
                int_of_string_opt
                  (String.trim
                     (String.sub line (i + 1) (String.length line - i - 1)))
            | _ -> None)
          (String.split_on_char '\n' (String.sub s 0 h))
      in
      let length = Option.value length ~default:0 in
      let total = h + 4 + length in
      if String.length s < total then None
      else Some (String.sub s (h + 4) length, total)

let consume n =
  let s = Buffer.contents pending in
  Buffer.clear pending;
  Buffer.add_substring pending s n (String.length s - n)

(** The next message, waiting for it; [None] at the end of the input. A body
    that is not JSON is skipped. *)
let rec read () =
  match split () with
  | Some (body, n) -> (
      consume n;
      match Yojson.Safe.from_string body with
      | json -> Some json
      | exception Yojson.Json_error e ->
          log "kanon lsp: bad message: %s" e;
          read ())
  | None -> if fill () then read () else None

(** Whether a message can be read without waiting. *)
let ready () =
  Option.is_some (split ())
  ||
  match Unix.select [ Unix.stdin ] [] [] 0. with
  | [], _, _ -> false
  | _ ->
      (* readable: data, or the end of the input, which [read] reports *)
      ignore (fill ());
      true
  | exception Unix.Unix_error (EINTR, _, _) -> false

(** Where the messages are sent, as JSON text: by default, on standard output,
    framed with their length. *)
let output =
  ref (fun body ->
      Printf.printf "Content-Length: %d\r\n\r\n%s%!" (String.length body) body)

let send (json : Yojson.Safe.t) = !output (Yojson.Safe.to_string json)

let respond id result =
  send (`Assoc [ ("jsonrpc", `String "2.0"); ("id", id); ("result", result) ])

let respond_error id code message =
  send
    (`Assoc
       [
         ("jsonrpc", `String "2.0");
         ("id", id);
         ("error", `Assoc [ ("code", `Int code); ("message", `String message) ]);
       ])

let notify meth params =
  send
    (`Assoc
       [
         ("jsonrpc", `String "2.0"); ("method", `String meth); ("params", params);
       ])

(** {1 JSON} *)

let member k : Yojson.Safe.t -> Yojson.Safe.t = function
  | `Assoc l -> Option.value (List.assoc_opt k l) ~default:`Null
  | _ -> `Null

let to_string = function `String s -> Some s | _ -> None
let to_int = function `Int i -> Some i | _ -> None
let to_list = function `List l -> l | _ -> []

(** The members of [l] whose values are not [None]. *)
let obj l : Yojson.Safe.t =
  `Assoc (List.filter_map (fun (k, v) -> Option.map (fun v -> (k, v)) v) l)

(** {1 URIs} *)

(** The path of a [file:] URI, decoding its escapes. *)
let path_of_uri uri =
  let s =
    if String.starts_with ~prefix:"file://" uri then
      String.sub uri 7 (String.length uri - 7)
    else uri
  in
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let rec go i =
    if i < n then
      if s.[i] = '%' && i + 2 < n then (
        match int_of_string_opt ("0x" ^ String.sub s (i + 1) 2) with
        | Some c ->
            Buffer.add_char b (Char.chr c);
            go (i + 3)
        | None ->
            Buffer.add_char b '%';
            go (i + 1))
      else (
        Buffer.add_char b s.[i];
        go (i + 1))
  in
  go 0;
  Buffer.contents b

let uri_of_path p =
  let b = Buffer.create (String.length p + 7) in
  Buffer.add_string b "file://";
  String.iter
    (fun c ->
      match c with
      | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '-' | '.' | '_' | '~' | '/' ->
          Buffer.add_char b c
      | c -> Buffer.add_string b (Printf.sprintf "%%%02X" (Char.code c)))
    p;
  Buffer.contents b
