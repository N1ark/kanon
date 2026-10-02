// Highlighting of Kanon by its tree-sitter grammar (tree-sitter-kanon, built to
// WebAssembly by `npm run grammar`) and the highlighting query of the Zed
// extension, imported from the repository. A capture `keyword.operator` gives
// the classes `ts-keyword ts-keyword-operator`, so that the theme may style a
// capture or any of its prefixes.

import { Language, Parser, Query, type Node, type Tree } from "web-tree-sitter";
import treeSitterWasm from "web-tree-sitter/tree-sitter.wasm?url";
import highlights from "../../../editors/zed/languages/kanon/highlights.scm?raw";
import { escapeHtml } from "../lib/util";

export interface KanonSyntax {
  parser: Parser;
  query: Query;
}

let loading: Promise<KanonSyntax | null> | undefined;

/** The parser and the highlighting query, or null if they could not be
 * loaded (the code is then shown plain). */
export function loadKanonSyntax(): Promise<KanonSyntax | null> {
  loading ??= (async () => {
    try {
      await Parser.init({ locateFile: () => treeSitterWasm });
      const language = await Language.load(new URL("tree-sitter-kanon.wasm", document.baseURI).href);
      const parser = new Parser();
      parser.setLanguage(language);
      return { parser, query: new Query(language, highlights) };
    } catch (e) {
      console.warn("Kanon highlighting is unavailable:", e);
      return null;
    }
  })();
  return loading;
}

const classCache = new Map<string, string>();

/** The classes of a capture: `string.special.symbol` is
 * `ts-string ts-string-special ts-string-special-symbol`. */
export function captureClasses(name: string): string {
  let c = classCache.get(name);
  if (c === undefined) {
    const parts = name.split(".");
    c = parts.map((_, i) => "ts-" + parts.slice(0, i + 1).join("-")).join(" ");
    classCache.set(name, c);
  }
  return c;
}

export interface Span {
  from: number;
  to: number;
  name: string;
}

/** The captures of the tree, or of its rows `fromRow` to `toRow` (excluded),
 * sorted by position, the outer ones first. Tree-sitter nodes nest, and so do
 * these spans; of the captures of the same node, the last one wins (as in
 * Zed). The range is in rows: the indices of web-tree-sitter's queries are
 * bytes, but those of its nodes are UTF-16 code units, like JavaScript's. */
export function captures(syntax: KanonSyntax, root: Node, fromRow?: number, toRow?: number): Span[] {
  const byRange = new Map<string, Span>();
  const range =
    fromRow === undefined ? {} : { startPosition: { row: fromRow, column: 0 }, endPosition: { row: toRow ?? fromRow + 1, column: 0 } };
  for (const c of syntax.query.captures(root, range)) {
    const { startIndex, endIndex } = c.node;
    if (endIndex <= startIndex) continue;
    byRange.set(`${startIndex}:${endIndex}`, { from: startIndex, to: endIndex, name: c.name });
  }
  return [...byRange.values()].sort((a, b) => a.from - b.from || b.to - a.to);
}

/** The HTML of highlighted Kanon code. */
export function highlightKanon(syntax: KanonSyntax, text: string): string {
  const tree: Tree | null = syntax.parser.parse(text);
  if (!tree) return escapeHtml(text);
  try {
    return spansHtml(text, captures(syntax, tree.rootNode));
  } finally {
    tree.delete();
  }
}

/** The contexts in which a fragment of Kanon is parsed (an item, an expression, a case, a
 * pattern, attributes, a signature, a parameter, a typing), as a prefix and a suffix. */
const FRAGMENT_CONTEXTS: [string, string][] = [
  ["", ""],
  ["", " = _x"],
  ["fn _f = ", ""],
  ["rule _r : _x = | _l: ", ""],
  ["rule _r : _x = | _l: ", " -> _x"],
  ["type _t ", ""],
  ["prim ", ""],
  ["fn _f ", " = _x"],
  ["node _X : ", ""],
];

/** The HTML of a highlighted fragment of Kanon (inline code: `Int 0`, `x + 0 -> x`,
 * `[@fold f]`): highlighted in the first context in which it parses without errors, or else
 * alone. */
export function highlightKanonFragment(syntax: KanonSyntax, text: string): string {
  for (const [pre, post] of FRAGMENT_CONTEXTS) {
    const tree: Tree | null = syntax.parser.parse(pre + text + post);
    if (!tree) continue;
    try {
      if (tree.rootNode.hasError) continue;
      const from = pre.length;
      const to = from + text.length;
      const spans = captures(syntax, tree.rootNode)
        .filter((s) => s.from >= from && s.to <= to)
        .map((s) => ({ ...s, from: s.from - from, to: s.to - from }));
      return spansHtml(text, spans);
    } finally {
      tree.delete();
    }
  }
  return highlightKanon(syntax, text);
}

/** The HTML of `text` with the nested spans of its captures. */
function spansHtml(text: string, spans: Span[]): string {
  let html = "";
  let pos = 0;
  const open: Span[] = [];
  const closeUntil = (p: number) => {
    while (open.length && open[open.length - 1].to <= p) {
      const s = open.pop()!;
      html += escapeHtml(text.slice(pos, s.to)) + "</span>";
      pos = s.to;
    }
  };
  for (const s of spans) {
    closeUntil(s.from);
    // a span that would cross an open one (not expected) is left out
    if (open.length && s.to > open[open.length - 1].to) continue;
    html += escapeHtml(text.slice(pos, s.from)) + `<span class="${captureClasses(s.name)}">`;
    pos = s.from;
    open.push(s);
  }
  closeUntil(Infinity);
  return html + escapeHtml(text.slice(pos));
}
