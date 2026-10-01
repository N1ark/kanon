// The external scanner of Kanon: comments [(* ... *)], which nest, as in
// src/kanon_lexer.mll.

#include "tree_sitter/parser.h"

enum TokenType { COMMENT };

void *tree_sitter_kanon_external_scanner_create(void) { return NULL; }

void tree_sitter_kanon_external_scanner_destroy(void *payload) {}

unsigned tree_sitter_kanon_external_scanner_serialize(void *payload, char *buffer) { return 0; }

void tree_sitter_kanon_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {}

static void advance(TSLexer *lexer) { lexer->advance(lexer, false); }

bool tree_sitter_kanon_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
  if (!valid_symbols[COMMENT]) return false;
  while (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\n' ||
         lexer->lookahead == '\r')
    lexer->advance(lexer, true);
  if (lexer->lookahead != '(') return false;
  advance(lexer);
  if (lexer->lookahead != '*') return false;
  advance(lexer);
  unsigned depth = 1;
  while (depth > 0) {
    if (lexer->eof(lexer)) {
      // an unterminated comment extends to the end of the file
      lexer->mark_end(lexer);
      lexer->result_symbol = COMMENT;
      return true;
    }
    if (lexer->lookahead == '(') {
      advance(lexer);
      if (lexer->lookahead == '*') {
        advance(lexer);
        depth++;
      }
    } else if (lexer->lookahead == '*') {
      advance(lexer);
      if (lexer->lookahead == ')') {
        advance(lexer);
        depth--;
      }
    } else {
      advance(lexer);
    }
  }
  lexer->mark_end(lexer);
  lexer->result_symbol = COMMENT;
  return true;
}
