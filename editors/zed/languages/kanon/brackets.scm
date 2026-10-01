("(" @open
  ")" @close)

("[" @open
  "]" @close)

("{" @open
  "}" @close)

(attribute
  "[@" @open
  "]" @close)

(floating_attribute
  "[@@@" @open
  "]" @close)

(("\"" @open
  "\"" @close)
  (#set! rainbow.exclude))
