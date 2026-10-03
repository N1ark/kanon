; The highlighting of Kanon. No two patterns capture the same node, so that the
; order of the patterns does not matter: Zed takes the last capture of a node,
; but `tree-sitter highlight` (and the highlight tests of the grammar) the
; first. Variables are left to the default colour.

; Names
; -----

(constructor) @constructor

((type_identifier) @type
  (#not-any-of? @type "t" "int" "nat" "bool" "unit" "list" "option"))

((type_identifier) @type.builtin
  (#any-of? @type.builtin "t" "int" "nat" "bool" "unit" "list" "option"))

(type_variable) @type

(field_identifier) @property

(wildcard) @variable.special

; Definitions

(function_definition
  name: (identifier) @function)

(rule_definition
  name: (identifier) @function)

(extend_definition
  name: (identifier) @function)

(primitive_declaration
  name: (identifier) @function)

(let_binding
  name: (identifier) @function)

(parameter
  name: (identifier) @variable.parameter)

(constructor_parameters
  (identifier) @variable.parameter)

(constant_declaration
  parameter: (identifier) @variable.parameter)

; Calls

((application_expression
  function: (identifier) @function)
  (#not-eq? @function "type_of"))

((application_expression
  function: (identifier) @function.builtin)
  (#eq? @function.builtin "type_of"))

; [infix "+" = Add, bv_add unchecked, lit_add]: the smart constructor and the
; primitive on values
(operator_declaration
  body: (tuple_expression
    (identifier) @function))

; Rules
; -----

(rule_name
  [
    (identifier)
    "not"
    "extend"
  ] @label)

; [#x] binds the value of an integer literal
(literal_pattern
  "#" @punctuation.special)

; Attributes
; ----------

[
  "[@"
  "[@@@"
] @attribute

(attribute
  "]" @attribute)

(floating_attribute
  "]" @attribute)

(attribute_name
  (_) @attribute)

; the unquoted arguments of attributes are mostly functions ([@fold z_add],
; [@get size], [@fold z_lt Bool])
(attribute_argument
  (identifier) @function)

(attribute_argument
  (constructor) @constructor)


; Literals
; --------

(number) @number

(boolean) @boolean

(unit) @constant.builtin

(attribute
  argument: (string) @string)

(floating_attribute
  (string) @string)

(use_declaration
  module: (string) @string.special)

(builtin_module
  name: (string) @string.special.symbol)

; the operators and literals that the language declares
(operator_declaration
  operator: (string) @string.special.symbol)

(constant_declaration
  literal: (string) @string.special.symbol)

; [constant ones (v) = ...]: a named constant, for [@unit ones]
(constant_declaration
  literal: (identifier) @constant)

; [node Distinct : a list -> TBool]
(list_sort
  "list" @type.builtin)

((comment) @comment
  (#not-match? @comment "^\\(\\*\\*[^*]"))

; [(** ... *)]
((comment) @comment.doc
  (#match? @comment.doc "^\\(\\*\\*[^*]"))

; Keywords and operators
; ----------------------

[
  "use"
  "builtin"
  "prim"
  "oracle"
  "fn"
  "rule"
  "before"
  "node"
  "sort"
  "notation"
  "type"
  "of"
  "infix"
  "prefix"
  "constant"
  "let"
  "in"
  "match"
  "with"
  "if"
  "then"
  "else"
  "when"
  "as"
  "assert"
] @keyword

; [extend] and [not] may also name rules
(extend_definition
  "extend" @keyword)

(assert_expression
  "not" @keyword.operator)

(unary_pattern
  "not" @keyword.operator)

; the operators of expressions and patterns, and an infix word ([a urem b])
(operator) @operator

(infix_word) @keyword.operator

; [=] of declarations, [*] of types
[
  "="
  "*"
  "->"
] @operator

; Punctuation
; -----------

[
  "("
  ")"
  "{"
  "}"
] @punctuation.bracket

(list_expression
  [
    "["
    "]"
  ] @punctuation.bracket)

(list_pattern
  [
    "["
    "]"
  ] @punctuation.bracket)

[
  ","
  ";"
  ":"
  "."
  "|"
] @punctuation.delimiter
