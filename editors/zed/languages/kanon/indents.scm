; The lines of these nodes after the first are indented: the cases of a rule
; under it, the body of a function or of a case on the next line, the
; attributes of a node that do not fit on its line. As in OCaml, the cases of
; a [match] are not indented under it.
[
  (function_definition)
  (rule_definition)
  (extend_definition)
  (primitive_declaration)
  (node_declaration)
  (sort_declaration)
  (subsort_declaration)
  (type_definition)
  (operator_declaration)
  (constant_declaration)
  (case)
  (let_binding)
  (field_initializer)
] @indent

(_
  "("
  ")" @end) @indent

(_
  "["
  "]" @end) @indent

(_
  "[@"
  "]" @end) @indent

(_
  "{"
  "}" @end) @indent
