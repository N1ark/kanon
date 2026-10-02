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
    ("then", THEN);
    ("true", TRUE);
    ("type", TYPE);
    ("use", USE);
    ("when", WHEN);
    ("with", WITH);
  ]
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
  | "(*" { comment lexbuf.lex_start_p 0 lexbuf; token lexbuf }
  | ['0'-'9']+ as i { INT i }
  | '"' ([^ '"' '\\' '\n']* as s) '"' { STRING s }
  | "_" { UNDERSCORE }
  | lid as s {
      match List.assoc_opt s keywords with
      | Some k -> k
      | None -> if Hashtbl.mem Syntax.infix_words s then INFIXWORD s else LID s }
  | uid as s { UID s }
  | "[@@@" { LBRACKETATATAT }
  | "[@" { LBRACKETAT }
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
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ',' { COMMA }
  | ';' { SEMI }
  | ':' { COLON }
  | '.' { DOT }
  | '#' { HASH }
  | eof { EOF }
  | _ as c { raise (Error (lexbuf.lex_start_p, Printf.sprintf "unexpected character %C" c)) }

(* [start] is the start of the outermost comment, where an unterminated
   comment is reported *)
and comment start depth = parse
  | "*)" { if depth > 0 then comment start (depth - 1) lexbuf }
  | "(*" { comment start (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment start depth lexbuf }
  | eof { raise (Error (start, "unterminated comment")) }
  | _ { comment start depth lexbuf }
