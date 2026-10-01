// OCaml (CodeMirror's legacy mode) and Lean (a small stream language:
// keywords, comments, strings, numbers), for the generated code, as CodeMirror
// languages and as static HTML.

import { StreamLanguage, type StringStream } from "@codemirror/language";
import { oCaml } from "@codemirror/legacy-modes/mode/mllike";
import { classHighlighter, highlightCode } from "@lezer/highlight";
import { escapeHtml } from "../util";

export const ocamlLanguage = StreamLanguage.define(oCaml);

const leanKeywords = new Set(
  (
    "abbrev axiom by calc class deriving def do else end example exact export fun have " +
    "if import in inductive instance let macro macro_rules match mutual namespace " +
    "noncomputable open partial private protected section set_option show simp " +
    "structure syntax then theorem universe variable where with at from rfl intro " +
    "intros rcases obtain cases induction rw simp_all omega decide repeat first " +
    "elab sorry"
  ).split(" "),
);

interface LeanState {
  comment: number; // the depth of nested /- -/ comments
}

function leanToken(stream: StringStream, state: LeanState): string | null {
  if (state.comment > 0) {
    while (!stream.eol()) {
      if (stream.match("/-")) state.comment++;
      else if (stream.match("-/")) {
        if (--state.comment === 0) break;
      } else stream.next();
    }
    return "comment";
  }
  if (stream.eatSpace()) return null;
  if (stream.match("--")) {
    stream.skipToEnd();
    return "comment";
  }
  if (stream.match("/-")) {
    state.comment = 1;
    return leanToken(stream, state) ?? "comment";
  }
  if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return "string";
  if (stream.match(/^(?:0x[0-9a-fA-F]+|\d+(?:\.\d+)?)/)) return "number";
  if (stream.match(/^@\[[^\]]*\]/)) return "meta";
  if (stream.match(/^[A-Za-z_À-ɏͰ-Ͽ][\w'!?.À-ɏͰ-Ͽ₀-₉]*/)) {
    const w = stream.current();
    if (leanKeywords.has(w)) return "keyword";
    if (/^[A-Z]/.test(w)) return "typeName";
    return "variableName";
  }
  if (stream.match(/^(?:[:=<>|&+\-*/∀∃→←↔∧∨¬≠≤≥⟨⟩·]+)/)) return "operator";
  stream.next();
  return null;
}

export const leanLanguage = StreamLanguage.define<LeanState>({
  name: "lean",
  startState: () => ({ comment: 0 }),
  copyState: (s) => ({ ...s }),
  token: leanToken,
  languageData: { commentTokens: { line: "--", block: { open: "/-", close: "-/" } } },
});

export type CodeLanguage = "ocaml" | "lean";

export function languageOf(backend: string): CodeLanguage {
  return backend.startsWith("lean") ? "lean" : "ocaml";
}

/** Static HTML of highlighted OCaml or Lean, with CodeMirror's token classes
 * (tok-keyword, ...). */
export function highlightStatic(lang: CodeLanguage, code: string): string {
  const language = lang === "lean" ? leanLanguage : ocamlLanguage;
  const tree = language.parser.parse(code);
  let html = "";
  highlightCode(
    code,
    tree,
    classHighlighter,
    (text, classes) => {
      html += classes ? `<span class="${classes}">${escapeHtml(text)}</span>` : escapeHtml(text);
    },
    () => {
      html += "\n";
    },
  );
  return html;
}
