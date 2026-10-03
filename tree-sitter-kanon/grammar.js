/**
 * @file The tree-sitter grammar of Kanon, the rule language of the `.kn` and
 * `.knl` files. It follows src/kanon_parser.mly, with one difference: an infix
 * operator declared as a word (`infix "urem" = ...`) is an identifier, since
 * the grammar cannot see the declarations of the other files; it is parsed as
 * an operator wherever an identifier cannot be (between two patterns, or after
 * an operand that is not a name), and as an argument otherwise.
 *
 * Symbolic operators are lexed as in OCaml: a sequence of the characters of
 * OP_CHAR (maximal munch), whose first character gives its precedence. An
 * operator that Kanon reads with a word suffix (`infix "<u"`, `a <u b`) is, to
 * the grammar, the symbol followed by an identifier, for the same reason: it
 * parses as `a < u b` in an expression (an application), and is not parsed in
 * a pattern, which has no applications.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const PREC = {
  seq: 1,
  open: 2,
  tuple: 3,
  or: 4,
  and: 5,
  cmp: 6,
  concat: 7,
  cons: 8,
  add: 9,
  mul: 10,
  pow: 11,
  unary: 12,
  app: 13,
  prefix: 14,
  field: 15,
};

// patterns: [p as x], [p | q], [p, q], [p [@a]], then the operators
const PAT = {
  alias: 1,
  or: 2,
  tuple: 3,
  attr: 4,
  or_op: 5,
  and_op: 6,
  cmp: 7,
  concat: 8,
  cons: 9,
  add: 10,
  mul: 11,
  pow: 12,
  unary: 13,
  app: 14,
};

// A character of a symbolic operator: `#` (but not first) and the non-ASCII
// characters too, so that `≤` is an operator.
const OP_CHAR = '([!$%&*+\\-./:<=>?@^|~#]|[^\\x00-\\x7F])';
const op = (first) => new RegExp(first + OP_CHAR + '*');
const op1 = (first) => new RegExp(first + OP_CHAR + '+');

// The infix operators, from the lowest precedence to the highest, by their
// first character, as in OCaml. The reserved `=`, `|`, `->`, `::` and `.` are
// the literal tokens, which tree-sitter prefers to a regex of the same length.
const INFIX = [
  ['or', prec.right, ['||']],
  ['and', prec.right, ['&&']],
  ['cmp', prec.left, ['=', '!=', op('[<>$&]'), op1('='), op1('\\|'), op('[^\\x00-\\x7F]')]],
  ['concat', prec.right, [op('[@^]')]],
  ['cons', prec.right, ['::']],
  ['add', prec.left, ['+', '-', op1('[+-]')]],
  ['mul', prec.left, ['*', op('\\*([!$%&+\\-./:<=>?@^|~#]|[^\\x00-\\x7F])'), op('[/%]')]],
  ['pow', prec.right, [op('\\*\\*')]],
];

// [!x], [~x], [?x]: prefix operators of the highest precedence
const PREFIX = op('[!~?]');

const sep1 = (rule, sep) => seq(rule, repeat(seq(sep, rule)));

const typeIdentifier = $ => alias($.identifier, $.type_identifier);
const fieldIdentifier = $ => alias($.identifier, $.field_identifier);

module.exports = grammar({
  name: 'kanon',

  externals: $ => [$.comment],

  extras: $ => [/\s/, $.comment],

  word: $ => $.identifier,

  supertypes: $ => [$._item, $._expression, $._pattern, $._type],

  conflicts: $ => [[$._type_application, $._simple_expression]],

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.use_declaration,
      $.primitive_declaration,
      $.function_definition,
      $.rule_definition,
      $.extend_definition,
      $.node_declaration,
      $.sort_declaration,
      $.notation_declaration,
      $.type_definition,
      $.operator_declaration,
      $.constant_declaration,
      $.floating_attribute,
    ),

    // ------------------------------------------------------------------
    // Items

    use_declaration: $ => seq(
      'use',
      field('module', choice($.builtin_module, $.string)),
    ),

    // [use builtin "bool"]: a module built into kanon
    builtin_module: $ => seq('builtin', field('name', $.string)),

    primitive_declaration: $ => seq(
      field('kind', choice('prim', 'oracle')),
      field('name', $.identifier),
      ':',
      field('type', $._type),
      repeat($.attribute),
    ),

    function_definition: $ => seq(
      'fn',
      field('name', $.identifier),
      repeat(field('parameter', $.parameter)),
      optional(seq(':', field('return_type', $._type))),
      repeat($.attribute),
      '=',
      field('body', $._sequence_or_expression),
    ),

    rule_definition: $ => seq(
      'rule',
      field('name', $.identifier),
      repeat(field('parameter', $.parameter)),
      ':',
      field('spec', $._spec),
      repeat($.attribute),
      optional(seq(
        '=',
        choice(
          seq('|', field('cases', $.cases)),
          field('body', $._sequence_or_expression),
        ),
      )),
    ),

    _spec: $ => choice(
      $._simple_expression,
      $.application_expression,
      $.constructor_expression,
    ),

    extend_definition: $ => seq(
      'extend',
      field('kind', choice('rule', 'fn')),
      field('name', $.identifier),
      optional(seq('before', field('before', $.rule_name))),
      '=',
      optional('|'),
      field('cases', $.cases),
    ),

    node_declaration: $ => seq('node', $.constructor_declaration),

    // [sort TBitVector of nat [@get size]]
    sort_declaration: $ => seq('sort', $.constructor_declaration),

    // [notation BitVec]: the literal patterns of a leaf node
    notation_declaration: $ => seq('notation', field('node', $.constructor)),

    type_definition: $ => seq(
      'type',
      optional(field('parameters', $.type_parameters)),
      field('name', typeIdentifier($)),
      repeat($.attribute),
      optional(seq('=', field('body', choice($.variant_declaration, $.record_declaration)))),
    ),

    // ['a box], [('a, 'b) pair]: the parameters of an abstract type
    type_parameters: $ => choice(
      $.type_variable,
      seq('(', sep1($.type_variable, ','), ')'),
    ),

    type_variable: $ => /'[a-z_][A-Za-z0-9_']*/,

    variant_declaration: $ => seq(
      optional('|'),
      sep1($.constructor_declaration, '|'),
    ),

    // [C of a * b (x, y) : s1 -> s2 when e [@attr]]
    constructor_declaration: $ => seq(
      field('name', $.constructor),
      optional(seq('of', sep1(field('argument', $._type_application), '*'))),
      optional(field('parameters', $.constructor_parameters)),
      optional(seq(':', field('sorts', $.sorts))),
      optional(seq('when', field('condition', $._expression))),
      repeat($.attribute),
    ),

    constructor_parameters: $ => seq(
      '(',
      sep1(choice($.identifier, $.wildcard), ','),
      ')',
    ),

    sorts: $ => sep1($._sort, '->'),

    _sort: $ => choice(
      $._simple_expression,
      $.application_expression,
      $.constructor_expression,
      $.list_sort,
    ),

    // [a list], [(TBitVector n) list]: the sort of the operands of an n-ary node
    list_sort: $ => prec(PREC.app + 1, seq(
      field('element', choice($.identifier, $.parenthesized_expression)),
      'list',
    )),

    record_declaration: $ => seq(
      '{',
      sep1($.field_declaration, ';'),
      optional(';'),
      '}',
    ),

    field_declaration: $ => seq(
      field('name', fieldIdentifier($)),
      ':',
      field('type', $._type),
    ),

    // [infix "+" = Add, bv_add unchecked, lit_add], [prefix "-" = ...]
    operator_declaration: $ => seq(
      field('kind', choice('infix', 'prefix')),
      field('operator', $.string),
      '=',
      field('body', $._sequence_or_expression),
    ),

    // [constant 0 (v) = bv_zero (size v)], [constant ones (v) = ...],
    // [constant true = v_true], [constant "0" = ...]
    constant_declaration: $ => seq(
      'constant',
      field('literal', choice($.string, $.identifier, $.number, $.boolean)),
      optional(seq('(', field('parameter', $.identifier), ')')),
      '=',
      field('body', $._sequence_or_expression),
    ),

    // [[@@@lean_root "R"]]
    floating_attribute: $ => seq(
      '[@@@',
      field('name', $.attribute_name),
      repeat($.string),
      ']',
    ),

    // [[@ocaml "Binop.t"]], [[@fold lit_add]], [[@unit 1]]
    attribute: $ => seq(
      '[@',
      field('name', $.attribute_name),
      repeat(field('argument', choice($.string, $.attribute_argument, $.number, $.boolean))),
      ']',
    ),

    attribute_name: $ => $._name,

    attribute_argument: $ => $._name,

    _name: $ => choice($.identifier, $.constructor),

    // ------------------------------------------------------------------
    // Functions and rules

    // [(v1 v2 : t)], or [(v : TBitVector n)], a term of that sort
    parameter: $ => seq(
      '(',
      repeat1(field('name', $.identifier)),
      ':',
      choice(field('type', $._type), field('sort', $._sort_annotation)),
      ')',
    ),

    cases: $ => prec.right(sep1($.case, '|')),

    // [r: p when g -> e], the rule [r] of a rule function, or a case of a
    // match
    case: $ => seq(
      optional(seq(field('label', $.rule_name), ':')),
      field('pattern', $._pattern),
      optional(seq('when', field('guard', $._sequence_or_expression))),
      '->',
      field('body', $._sequence_or_expression),
    ),

    // rule names may be [not], [extend] or infix words
    rule_name: $ => choice($.identifier, 'not', 'extend'),

    // ------------------------------------------------------------------
    // Types

    _type: $ => choice($.function_type, $.tuple_type, $._type_application),

    function_type: $ => prec.right(seq(
      field('domain', choice($.tuple_type, $._type_application)),
      '->',
      field('range', $._type),
    )),

    tuple_type: $ => seq(
      $._type_application,
      repeat1(seq('*', $._type_application)),
    ),

    _type_application: $ => choice(
      typeIdentifier($),
      $.parenthesized_type,
      $.type_application,
    ),

    // [t list], [(var * ty) list], [(t, int) pair]
    type_application: $ => seq(
      field('argument', choice($._type_application, $.type_arguments)),
      field('constructor', typeIdentifier($)),
    ),

    type_arguments: $ => seq('(', $._type, repeat1(seq(',', $._type)), ')'),

    parenthesized_type: $ => seq('(', $._type, ')'),

    // ------------------------------------------------------------------
    // Expressions

    _sequence_or_expression: $ => choice($._expression, $.sequence_expression),

    sequence_expression: $ => prec.right(PREC.seq, seq(
      field('left', $._expression),
      ';',
      field('right', $._sequence_or_expression),
    )),

    _expression: $ => choice($._tuple_element, $.tuple_expression),

    _tuple_element: $ => choice(
      $._simple_expression,
      $.application_expression,
      $.constructor_expression,
      $.assert_expression,
      $.unary_expression,
      $.binary_expression,
      $.let_expression,
      $.match_expression,
      $.if_expression,
    ),

    let_expression: $ => prec.right(PREC.open, seq(
      'let',
      field('binding', $.let_binding),
      'in',
      field('body', $._sequence_or_expression),
    )),

    let_binding: $ => choice(
      seq(
        field('name', $.identifier),
        repeat1(field('parameter', $.parameter)),
        optional(seq(':', field('return_type', $._type))),
        '=',
        field('body', $._sequence_or_expression),
      ),
      seq(
        field('pattern', $._pattern),
        optional(seq(':', field('type', $._type))),
        '=',
        field('body', $._sequence_or_expression),
      ),
    ),

    match_expression: $ => prec.right(PREC.open, seq(
      'match',
      field('value', $._sequence_or_expression),
      'with',
      optional('|'),
      field('cases', $.cases),
    )),

    if_expression: $ => prec.right(PREC.open, seq(
      'if',
      field('condition', $._sequence_or_expression),
      'then',
      field('consequence', $._expression),
      'else',
      field('alternative', $._expression),
    )),

    tuple_expression: $ => prec(PREC.tuple, seq($._tuple_element, ',', $._tuple_rest)),

    // the remaining components of a tuple (rather than a [repeat1], which
    // would lose the precedence of the tuple)
    _tuple_rest: $ => prec.right(PREC.tuple, seq(
      $._tuple_element,
      optional(seq(',', $._tuple_rest)),
    )),

    binary_expression: $ => choice(
      ...INFIX.map(([level, assoc, ops]) => assoc(PREC[level], seq(
        field('left', $._tuple_element),
        field('operator', choice(...ops.map(o => alias(o, $.operator)))),
        field('right', $._tuple_element),
      ))),
      // [a urem b], an operator declared by [infix "urem"], after an
      // operand that cannot be applied to it (see the header)
      prec.left(PREC.mul, seq(
        field('left', $._tuple_element),
        field('operator', alias($.identifier, $.infix_word)),
        field('right', $._tuple_element),
      )),
    ),

    unary_expression: $ => prec(PREC.unary, seq(
      field('operator', alias('-', $.operator)),
      field('operand', $._tuple_element),
    )),

    // [~x], [!x]
    prefix_expression: $ => prec(PREC.prefix, seq(
      field('operator', alias(PREFIX, $.operator)),
      field('operand', $._simple_expression),
    )),

    application_expression: $ => prec(PREC.app, seq(
      field('function', $.identifier),
      $._arguments,
    )),

    // the arguments of an application, as many as possible (rather than a
    // [repeat1], which would lose the precedence of the application)
    _arguments: $ => prec.right(seq(
      field('argument', $._simple_expression),
      optional($._arguments),
    )),

    constructor_expression: $ => prec(PREC.app, seq(
      field('constructor', $.constructor),
      field('argument', $._simple_expression),
    )),

    // [assert e], [not e]
    assert_expression: $ => prec(PREC.app, seq(
      field('operator', choice('assert', 'not')),
      field('argument', $._simple_expression),
    )),

    _simple_expression: $ => choice(
      $.identifier,
      $.constructor,
      $.boolean,
      $.number,
      $.unit,
      $.parenthesized_expression,
      $.typed_expression,
      $.list_expression,
      $.record_expression,
      $.field_expression,
      $.prefix_expression,
    ),

    parenthesized_expression: $ => seq('(', $._sequence_or_expression, ')'),

    // [(e : t)], or [(v : TBitVector n)], the sort of an operand of a spec,
    // or [(Field (i, v) : field_ty v i)], a node built at a computed sort
    typed_expression: $ => seq(
      '(',
      field('expression', $._sequence_or_expression),
      ':',
      choice(
        field('type', $._type),
        field('sort', $._sort_annotation),
        field('computed_sort', choice($.application_expression, $.parenthesized_expression)),
      ),
      ')',
    ),

    _sort_annotation: $ => choice($.constructor, $.constructor_expression),

    list_expression: $ => seq(
      '[',
      optional(seq(sep1($._expression, ';'), optional(';'))),
      ']',
    ),

    record_expression: $ => seq(
      '{',
      sep1($.field_initializer, ';'),
      optional(';'),
      '}',
    ),

    field_initializer: $ => seq(
      field('field', fieldIdentifier($)),
      '=',
      field('value', $._expression),
    ),

    field_expression: $ => prec(PREC.field, seq(
      field('record', $._simple_expression),
      '.',
      field('field', fieldIdentifier($)),
    )),

    // ------------------------------------------------------------------
    // Patterns

    _pattern: $ => choice(
      $.alias_pattern,
      $.or_pattern,
      $.tuple_pattern,
      $._tuple_pattern_element,
    ),

    _tuple_pattern_element: $ => choice(
      $._simple_pattern,
      $.attributed_pattern,
      $.binary_pattern,
      $.unary_pattern,
      $.constructor_pattern,
    ),

    alias_pattern: $ => prec.left(PAT.alias, seq(
      field('pattern', $._pattern),
      'as',
      field('name', $.identifier),
    )),

    or_pattern: $ => prec.left(PAT.or, seq(
      field('left', $._pattern),
      '|',
      field('right', $._pattern),
    )),

    tuple_pattern: $ => prec(PAT.tuple, seq($._tuple_pattern_element, ',', $._tuple_pattern_rest)),

    _tuple_pattern_rest: $ => prec.right(PAT.tuple, seq(
      $._tuple_pattern_element,
      optional(seq(',', $._tuple_pattern_rest)),
    )),

    // [(1, ~v) [@comm]]
    attributed_pattern: $ => prec.left(PAT.attr, seq(
      field('pattern', $._tuple_pattern_element),
      $.attribute,
    )),

    // operators on terms, as in expressions, but for [=], which ends the
    // pattern of a [let]
    binary_pattern: $ => choice(
      ...INFIX.map(([level, assoc, ops]) => assoc(PAT[level === 'or' ? 'or_op' : level === 'and' ? 'and_op' : level], seq(
        field('left', $._tuple_pattern_element),
        field('operator', choice(...ops.filter(o => o !== '=').map(o => alias(o, $.operator)))),
        field('right', $._tuple_pattern_element),
      ))),
      prec.left(PAT.mul, seq(
        field('left', $._tuple_pattern_element),
        field('operator', alias($.identifier, $.infix_word)),
        field('right', $._tuple_pattern_element),
      )),
    ),

    unary_pattern: $ => prec(PAT.unary, seq(
      field('operator', choice(alias('-', $.operator), 'not')),
      field('operand', $._tuple_pattern_element),
    )),

    // [~x], [!x]
    prefix_pattern: $ => seq(
      field('operator', alias(PREFIX, $.operator)),
      field('operand', $._simple_pattern),
    ),

    constructor_pattern: $ => prec(PAT.app, seq(
      field('constructor', $.constructor),
      field('argument', $._simple_pattern),
    )),

    _simple_pattern: $ => choice(
      $.wildcard,
      $.identifier,
      $.constructor,
      $.boolean,
      $.number,
      $.literal_pattern,
      $.unit,
      $.parenthesized_pattern,
      $.typed_pattern,
      $.list_pattern,
      $.record_pattern,
      $.prefix_pattern,
    ),

    // [#x], [#_]: an integer literal, binding its value
    literal_pattern: $ => seq('#', field('name', choice($.identifier, $.wildcard))),

    parenthesized_pattern: $ => seq('(', $._pattern, ')'),

    typed_pattern: $ => seq(
      '(',
      field('pattern', $._pattern),
      ':',
      choice(field('type', $._type), field('sort', $._sort_annotation)),
      ')',
    ),

    list_pattern: $ => seq(
      '[',
      optional(seq(sep1($._pattern, ';'), optional(';'))),
      ']',
    ),

    record_pattern: $ => seq(
      '{',
      sep1($.field_pattern, ';'),
      optional(seq(';', $.wildcard)),
      optional(';'),
      '}',
    ),

    field_pattern: $ => seq(
      field('field', fieldIdentifier($)),
      '=',
      field('pattern', $._pattern),
    ),

    // ------------------------------------------------------------------
    // Lexemes

    identifier: _ => /[a-z_][a-zA-Z0-9_']*/,

    constructor: _ => /[A-Z][a-zA-Z0-9_']*/,

    wildcard: _ => '_',

    number: _ => /[0-9]+/,

    boolean: _ => choice('true', 'false'),

    unit: _ => seq('(', ')'),

    string: $ => seq('"', optional($.string_content), '"'),

    string_content: _ => token.immediate(/[^"\\\n]+/),
  },
});
