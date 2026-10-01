; The items of a file, with the rules of the rule functions under them, and
; the constructors of the types under them.

(use_declaration
  "use" @context
  module: (_) @name) @item

(floating_attribute
  "[@@@" @context
  name: (_) @name) @item

(type_definition
  "type" @context
  name: (_) @name) @item

(variant_declaration
  (constructor_declaration
    name: (_) @name) @item)

(field_declaration
  name: (_) @name) @item

(node_declaration
  "node" @context
  (constructor_declaration
    name: (_) @name)) @item

(operator_declaration
  kind: _ @context
  operator: (_) @name) @item

(constant_declaration
  "constant" @context
  literal: (_) @name) @item

(primitive_declaration
  kind: _ @context
  name: (_) @name) @item

(function_definition
  "fn" @context
  name: (_) @name) @item

(rule_definition
  "rule" @context
  name: (_) @name
  ":" @context
  spec: (_) @context.extra) @item

(extend_definition
  "extend" @context
  kind: _ @context
  name: (_) @name) @item

; the rules of a rule function, or of an extension of one
(case
  label: (_) @name) @item
