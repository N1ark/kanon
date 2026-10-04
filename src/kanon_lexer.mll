{
open Kanon_parser

exception Error of Lexing.position * string

let keywords =
  [
    ("as", AS);
    ("assert", ASSERT);
    ("before", BEFORE);
    ("builtin", BUILTIN);
    ("constant", CONSTANT);
    ("else", ELSE);
    ("extend", EXTEND);
    ("false", FALSE);
    ("fn", FN);
    ("if", IF);
    ("in", IN);
    ("infix", INFIX);
    ("let", LET);
    ("match", MATCH);
    ("node", NODE);
    ("not", NOT);
    ("notation", NOTATION);
    ("of", OF);
    ("oracle", ORACLE);
    ("prefix", PREFIX);
    ("prim", PRIM);
    ("rule", RULE);
    ("sort", SORT);
    ("subsort", SUBSORT);
    ("then", THEN);
    ("true", TRUE);
    ("type", TYPE);
    ("use", USE);
    ("when", WHEN);
    ("with", WITH);
  ]

(* Reads the lexeme again, with another rule. *)
let rewind (lexbuf : Lexing.lexbuf) =
  lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
  lexbuf.lex_curr_p <- lexbuf.lex_start_p

(* The token of an operator with a word suffix, [<u]: the level of an operator
   is given by its symbol, as for an operator without a suffix. *)
let word_op s =
  match s.[0] with
  | '=' | '<' | '>' | '|' | '&' | '$' | '!' | '\128' .. '\255' -> Some (CMPOP s)
  | '@' | '^' -> Some (CONCATOP s)
  | '+' | '-' -> Some (ADDOP s)
  | '*' when String.length s > 1 && s.[1] = '*' -> Some (POWOP s)
  | '*' | '/' | '%' -> Some (MULOP s)
  | _ -> None

let is_op_char = function
  | '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>'
  | '?' | '@' | '^' | '|' | '~' | '#' | '\128' .. '\255' -> true
  | _ -> false

(* The length of the symbol at the start of [s] *)
let symbol_length s =
  let rec go i = if i < String.length s && is_op_char s.[i] then go (i + 1) else i in
  go 0

(* Whether the lexeme starts after nothing, a space or an opening bracket *)
let left_ok (lexbuf : Lexing.lexbuf) =
  let i = lexbuf.lex_start_pos in
  i = 0
  || match Bytes.get lexbuf.lex_buffer (i - 1) with
     | ' ' | '\t' | '\r' | '\n' | '(' | '[' | '{' | ',' | ';' -> true
     | _ -> false

(* Whether the lexeme is followed by nothing, a space or a closing bracket *)
let right_ok (lexbuf : Lexing.lexbuf) =
  let i = lexbuf.lex_curr_pos in
  i >= lexbuf.lex_buffer_len
  || match Bytes.get lexbuf.lex_buffer i with
     | ' ' | '\t' | '\r' | '\n' | ')' | ']' | '}' | ',' | ';' -> true
     | _ -> false
}

let ident_char = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let lid = ['a'-'z' '_'] ident_char*
let uid = ['A'-'Z'] ident_char*

(* Operators are read as in OCaml, as long as possible, and their first
   character gives their precedence. The bytes of non-ASCII characters (UTF-8)
   are symbols, so that [≤] or [⊕] are operators, at the level of
   comparisons. *)
let utf8 = ['\128'-'\255']
let op_char =
  ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~' '#']
  | utf8


rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "(**)" { token lexbuf }
  | "(**" {
      let start = lexbuf.lex_start_p in
      let buf = Buffer.create 64 in
      doc start buf 0 lexbuf;
      lexbuf.lex_start_p <- start;
      match String.trim (Buffer.contents buf) with
      | "" -> token lexbuf
      | s -> DOC s }
  | "(*" { comment lexbuf.lex_start_p 0 lexbuf; token lexbuf }
  | ['0'-'9']+ as i { INT i }
  | '"' ([^ '"' '\\' '\n']* as s) '"' { STRING s }
  | "_" { UNDERSCORE }
  | lid as s {
      match List.assoc_opt s keywords with
      | Some k -> k
      | None -> if Hashtbl.mem Syntax.infix_words s then INFIXWORD s else LID s }
  | uid '.' lid as s { QLID s }
  | uid as s { UID s }
  | op_char+ (['a'-'z'] ident_char*)? {
      let s = Lexing.lexeme lexbuf in
      let left = left_ok lexbuf in
      rewind lexbuf;
      operator s left lexbuf }
  | "[|" { LBRACKETBAR }
  | "|]" { BARRBRACKET }
  | "[@@@" { LBRACKETATATAT }
  | "[@" { LBRACKETAT }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ',' { COMMA }
  | ';' { SEMI }
  | eof { EOF }
  | _ as c { raise (Error (lexbuf.lex_start_p, Printf.sprintf "unexpected character %C" c)) }

(* The operator [s], a symbol and the word that directly follows it, if any,
   which is [left] if what precedes it is a space or an opening bracket. It is
   surrounded by spaces (or brackets), but for a prefix operator, [-] or one
   that starts with [!], [~] or [?], which is directly followed by its operand,
   and for [.], [#] and [:], which are not operators. Otherwise [x<y] is not
   [x < y]: it is an error. *)
and operator s left = parse
  | "" {
      let start = lexbuf.lex_start_p in
      let k = symbol_length s in
      let bad () =
        raise (Error (start, Printf.sprintf "the operator %s must be surrounded by spaces" (String.sub s 0 k)))
      in
      let t = symbol lexbuf in
      match t with
      | COLON | DOT | HASH -> t
      | MINUS | PREFIXOP _ ->
          if not left then bad ()
          else if right_ok lexbuf then t
          else if t = MINUS then UMINUS
          else t
      | _ ->
          if k < String.length s then (
            let w = String.length s - k in
            lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos + w;
            lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_cnum = lexbuf.lex_curr_p.pos_cnum + w };
            match word_op s with
            | Some t when left && right_ok lexbuf -> t
            | _ -> bad ())
          else if left && right_ok lexbuf then t
          else bad () }

(* The symbolic operators, as long as possible *)
and symbol = parse
  | ':' { COLON }
  | '.' { DOT }
  | '#' { HASH }
  | "::" { COLONCOLON }
  | "->" { ARROW }
  | "<-" { raise (Error (lexbuf.lex_start_p, "<- is reserved")) }
  | "&&" { ANDAND }
  | "||" { BARBAR }
  | '=' { EQ }
  | '|' { BAR }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | "!=" { CMPOP "!=" }
  | ['=' '<' '>' '|' '&' '$'] op_char* as s { CMPOP s }
  | utf8 op_char* as s { CMPOP s }
  | ['@' '^'] op_char* as s { CONCATOP s }
  | ['+' '-'] op_char* as s { ADDOP s }
  | "**" op_char* as s { POWOP s }
  | ['*' '/' '%'] op_char* as s { MULOP s }
  | ['!' '~' '?'] op_char* as s { PREFIXOP s }
  | _ as c { raise (Error (lexbuf.lex_start_p, Printf.sprintf "unexpected character %C" c)) }

(* [start] is the start of the outermost comment, where an unterminated
   comment is reported *)
and comment start depth = parse
  | "*)" { if depth > 0 then comment start (depth - 1) lexbuf }
  | "(*" { comment start (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment start depth lexbuf }
  | eof { raise (Error (start, "unterminated comment")) }
  | _ { comment start depth lexbuf }

(* A doc comment [(** ... *)], whose text is added to [buf]; the comments in it
   are part of the text *)
and doc start buf depth = parse
  | "*)" { if depth > 0 then (Buffer.add_string buf "*)"; doc start buf (depth - 1) lexbuf) }
  | "(*" { Buffer.add_string buf "(*"; doc start buf (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; Buffer.add_char buf '\n'; doc start buf depth lexbuf }
  | eof { raise (Error (start, "unterminated comment")) }
  | _ as c { Buffer.add_char buf c; doc start buf depth lexbuf }
