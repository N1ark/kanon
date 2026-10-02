; Functions: rule functions, helpers and extensions, and the rules of a rule
; function. Classes: types, nodes and sorts.

(function_definition
  body: (_) @function.inside) @function.around

(rule_definition
  cases: (_) @function.inside) @function.around

(rule_definition
  body: (_) @function.inside) @function.around

(extend_definition
  cases: (_) @function.inside) @function.around

(primitive_declaration) @function.around

(case
  body: (_) @function.inside) @function.around

(type_definition
  body: (_) @class.inside) @class.around

(node_declaration
  (constructor_declaration) @class.inside) @class.around

(sort_declaration
  (constructor_declaration) @class.inside) @class.around

(comment) @comment.inside

(comment)+ @comment.around
