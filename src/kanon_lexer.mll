{
open Kanon_parser

exception Error of Lexing.position * string

let keywords =
  [
    ("as", AS);
    ("asr", ASR);
    ("assert", ASSERT);
    ("before", BEFORE);
    ("constant", CONSTANT);
    ("else", ELSE);
    ("extend", EXTEND);
    ("false", FALSE);
    ("fn", FN);
    ("if", IF);
    ("in", IN);
    ("infix", INFIX);
    ("land", LAND);
    ("let", LET);
    ("lor", LOR);
    ("lsl", LSL);
    ("lsr", LSR);
    ("lxor", LXOR);
    ("match", MATCH);
    ("node", NODE);
    ("not", NOT);
    ("of", OF);
    ("oracle", ORACLE);
    ("prefix", PREFIX);
    ("prim", PRIM);
    ("rule", RULE);
    ("then", THEN);
    ("true", TRUE);
    ("type", TYPE);
    ("when", WHEN);
    ("with", WITH);
  ]
}

let ident_char = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let lid = ['a'-'z' '_'] ident_char*
let uid = ['A'-'Z'] ident_char*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "(*" { comment 0 lexbuf; token lexbuf }
  | ['0'-'9']+ as i { INT i }
  | '"' ([^ '"' '\\' '\n']* as s) '"' { STRING s }
  | "_" { UNDERSCORE }
  | lid as s { match List.assoc_opt s keywords with Some k -> k | None -> LID s }
  | uid as s { UID s }
  | "[@@@" { LBRACKETATATAT }
  | "[@" { LBRACKETAT }
  | "::" { COLONCOLON }
  | "==" { EQEQ }
  | "++" { PLUSPLUS }
  | "->" { ARROW }
  | "<=" { LE }
  | ">=" { GE }
  | "<>" { NE }
  | "&&" { ANDAND }
  | "||" { BARBAR }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ',' { COMMA }
  | ';' { SEMI }
  | ':' { COLON }
  | '|' { BAR }
  | '=' { EQ }
  | '<' { LT }
  | '>' { GT }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '.' { DOT }
  | '#' { HASH }
  | '~' { TILDE }
  | eof { EOF }
  | _ as c { raise (Error (lexbuf.lex_start_p, Printf.sprintf "unexpected character %C" c)) }

and comment depth = parse
  | "*)" { if depth > 0 then comment (depth - 1) lexbuf }
  | "(*" { comment (depth + 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment depth lexbuf }
  | eof { raise (Error (lexbuf.lex_start_p, "unterminated comment")) }
  | _ { comment depth lexbuf }
