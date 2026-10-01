// CodeMirror: the theme, the extensions of Kanon files (tree-sitter
// highlighting, the features of the language server) and of the generated code.

import { autocompletion, closeBrackets, closeBracketsKeymap, completionKeymap, type CompletionContext, type CompletionResult } from "@codemirror/autocomplete";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { bracketMatching, indentOnInput, indentUnit, syntaxHighlighting } from "@codemirror/language";
import { lintGutter, lintKeymap } from "@codemirror/lint";
import { highlightSelectionMatches, search, searchKeymap } from "@codemirror/search";
import { EditorState, StateEffect, StateField, type Extension, type Text } from "@codemirror/state";
import {
  Decoration,
  EditorView,
  ViewPlugin,
  crosshairCursor,
  drawSelection,
  highlightActiveLine,
  highlightActiveLineGutter,
  hoverTooltip,
  keymap,
  lineNumbers,
  rectangularSelection,
  type DecorationSet,
  type ViewUpdate,
} from "@codemirror/view";
import { classHighlighter } from "@lezer/highlight";
import type { KanonSyntax } from "../highlight/kanon";
import { kanonHighlighting } from "../highlight/kanon-cm";
import { leanLanguage, ocamlLanguage, type CodeLanguage } from "../highlight/languages";
import { renderMarkdown } from "../markdown";
import type { LspClient, Position, Range } from "../runtime/lsp";
import { debounce } from "../util";

export function toOffset(doc: Text, p: Position): number {
  const line = doc.line(Math.max(1, Math.min(p.line + 1, doc.lines)));
  return Math.min(line.from + Math.max(0, p.character), line.to);
}

export function toPosition(doc: Text, offset: number): Position {
  const line = doc.lineAt(offset);
  return { line: line.number - 1, character: offset - line.from };
}

export function toOffsets(doc: Text, r: Range): { from: number; to: number } {
  const from = toOffset(doc, r.start);
  return { from, to: Math.max(from, toOffset(doc, r.end)) };
}

export const theme = EditorView.theme({
  "&": { height: "100%", backgroundColor: "var(--bg)", color: "var(--fg)", fontSize: "13.5px" },
  ".cm-scroller": { fontFamily: "var(--mono)", lineHeight: "1.55" },
  ".cm-content": { caretColor: "var(--fg)" },
  ".cm-cursor, .cm-dropCursor": { borderLeftColor: "var(--fg)" },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground, ::selection": { backgroundColor: "var(--selection) !important" },
  ".cm-gutters": { backgroundColor: "var(--surface)", color: "var(--muted)", borderRight: "1px solid var(--border)" },
  ".cm-activeLine": { backgroundColor: "color-mix(in srgb, var(--surface-2) 55%, transparent)" },
  ".cm-activeLineGutter": { backgroundColor: "var(--surface-2)", color: "var(--fg)" },
  ".cm-matchingBracket, &.cm-focused .cm-matchingBracket": { backgroundColor: "var(--highlight)", outline: "none" },
  ".cm-selectionMatch": { backgroundColor: "var(--highlight)" },
  ".cm-tooltip": { backgroundColor: "var(--surface)", color: "var(--fg)", border: "1px solid var(--border)", borderRadius: "6px", boxShadow: "0 4px 14px rgba(0,0,0,.15)" },
  ".cm-tooltip-autocomplete > ul > li[aria-selected]": { backgroundColor: "var(--accent)", color: "var(--accent-fg)" },
  ".cm-completionDetail": { fontStyle: "normal", color: "var(--muted)", marginLeft: "1em" },
  ".cm-tooltip-autocomplete > ul > li[aria-selected] .cm-completionDetail": { color: "inherit" },
  ".cm-panels": { backgroundColor: "var(--surface)", color: "var(--fg)" },
  ".cm-panels.cm-panels-bottom": { borderTop: "1px solid var(--border)" },
  ".cm-searchMatch": { backgroundColor: "var(--highlight)", outline: "1px solid var(--border)" },
  ".cm-diagnostic-error": { borderLeftColor: "var(--error)" },
  ".cm-lintRange-error": {
    backgroundImage: "none",
    textDecoration: "underline wavy var(--error)",
    textDecorationSkipInk: "none",
    textUnderlineOffset: "3px",
  },
  ".cm-lsp-highlight": { backgroundColor: "var(--highlight)", borderRadius: "2px" },
  ".cm-definition-link": { textDecoration: "underline", cursor: "pointer" },
});

const basics: Extension = [
  lineNumbers(),
  highlightActiveLineGutter(),
  history(),
  drawSelection(),
  EditorState.allowMultipleSelections.of(true),
  indentOnInput(),
  indentUnit.of("  "),
  bracketMatching(),
  rectangularSelection(),
  crosshairCursor(),
  highlightActiveLine(),
  highlightSelectionMatches(),
  search({ top: true }),
  theme,
];

/** What the language features of a file need from the sandbox. */
export interface LspHost {
  lsp(): LspClient | null;
  /** The URI of the file. */
  uri(): string;
  /** Sends the pending changes to the server, before a request. */
  flush(): Promise<void>;
  syntax: KanonSyntax | null;
  goToDefinition(view: EditorView, pos: number): void;
  findReferences(view: EditorView, pos: number): void;
  rename(view: EditorView, pos: number): void;
}

const COMPLETION_TYPES: Record<number, string> = {
  2: "method",
  3: "function",
  4: "class",
  5: "property",
  6: "variable",
  7: "type",
  9: "namespace",
  10: "property",
  12: "constant",
  13: "enum",
  14: "keyword",
  20: "enum",
  21: "constant",
  22: "type",
  24: "operator",
  25: "type",
};

function completion(host: LspHost) {
  return async (ctx: CompletionContext): Promise<CompletionResult | null> => {
    const lsp = host.lsp();
    if (!lsp || !lsp.has("completionProvider")) return null;
    const word = ctx.matchBefore(/[\w']+/);
    if (!word && !ctx.explicit) return null;
    await host.flush();
    const r = await lsp.request("textDocument/completion", {
      textDocument: { uri: host.uri() },
      position: toPosition(ctx.state.doc, ctx.pos),
      context: { triggerKind: 1 },
    });
    const items: any[] = Array.isArray(r) ? r : (r?.items ?? []);
    if (ctx.aborted) return null;
    return {
      from: word ? word.from : ctx.pos,
      validFor: /^[\w']*$/,
      options: items.map((it) => ({
        label: it.label,
        apply: it.insertText ?? it.textEdit?.newText ?? it.label,
        type: COMPLETION_TYPES[it.kind] ?? "text",
        detail: it.detail,
        info: typeof it.documentation === "string" ? it.documentation : it.documentation?.value,
        boost: it.kind === 14 ? -1 : 0,
      })),
    };
  };
}

function hover(host: LspHost) {
  return hoverTooltip(async (view, pos) => {
    const lsp = host.lsp();
    if (!lsp || !lsp.has("hoverProvider")) return null;
    await host.flush();
    const r = await lsp.request("textDocument/hover", {
      textDocument: { uri: host.uri() },
      position: toPosition(view.state.doc, pos),
    });
    if (!r?.contents) return null;
    const c = r.contents;
    const md = typeof c === "string" ? c : Array.isArray(c) ? c.map((x) => (typeof x === "string" ? x : "```" + x.language + "\n" + x.value + "\n```")).join("\n\n") : c.kind === "plaintext" ? c.value.replace(/[*_`]/g, "\\$&") : c.value;
    if (!md.trim()) return null;
    const range = r.range ? toOffsets(view.state.doc, r.range) : { from: pos, to: pos };
    return {
      pos: range.from,
      end: range.to,
      above: true,
      create() {
        const dom = document.createElement("div");
        dom.className = "cm-lsp-hover";
        dom.innerHTML = renderMarkdown(md, host.syntax);
        return { dom };
      },
    };
  }, { hoverTime: 350 });
}

const setHighlights = StateEffect.define<DecorationSet>();
const highlightField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(v, tr) {
    v = tr.docChanged ? Decoration.none : v.map(tr.changes);
    for (const e of tr.effects) if (e.is(setHighlights)) v = e.value;
    return v;
  },
  provide: (f) => EditorView.decorations.from(f),
});
const highlightMark = Decoration.mark({ class: "cm-lsp-highlight" });

/** The occurrences of the symbol at the cursor (textDocument/documentHighlight). */
function documentHighlights(host: LspHost) {
  return [
    highlightField,
    ViewPlugin.fromClass(
      class {
        request = debounce(async (view: EditorView) => {
          const lsp = host.lsp();
          if (!lsp?.has("documentHighlightProvider")) return;
          const sel = view.state.selection.main;
          if (!sel.empty) return;
          const doc = view.state.doc;
          await host.flush();
          const r: any[] | null = await lsp.request("textDocument/documentHighlight", {
            textDocument: { uri: host.uri() },
            position: toPosition(doc, sel.head),
          });
          if (view.state.doc !== doc) return;
          const marks = (r ?? [])
            .map((h) => toOffsets(doc, h.range))
            .filter((x) => x.to > x.from)
            .sort((a, b) => a.from - b.from)
            .map((x) => highlightMark.range(x.from, x.to));
          view.dispatch({ effects: setHighlights.of(Decoration.set(marks)) });
        }, 250);
        update(u: ViewUpdate) {
          if (u.selectionSet || u.docChanged) {
            if (u.view.state.field(highlightField).size) u.view.dispatch({ effects: setHighlights.of(Decoration.none) });
            this.request(u.view);
          }
        }
        destroy() {
          this.request.cancel();
        }
      },
    ),
  ];
}

/** Ctrl or Cmd-click: go to the definition. */
function clickToDefinition(host: LspHost) {
  return EditorView.domEventHandlers({
    mousedown(e, view) {
      if (!(e.ctrlKey || e.metaKey) || e.button !== 0) return false;
      const pos = view.posAtCoords({ x: e.clientX, y: e.clientY });
      if (pos === null) return false;
      e.preventDefault();
      host.goToDefinition(view, pos);
      return true;
    },
  });
}

/** The extensions of a Kanon file. */
export function kanonExtensions(host: LspHost, readOnly: boolean, onChange: (u: ViewUpdate) => void): Extension {
  const at = (f: (view: EditorView, pos: number) => void) => (view: EditorView) => {
    f(view, view.state.selection.main.head);
    return true;
  };
  return [
    basics,
    host.syntax ? kanonHighlighting(host.syntax) : [],
    readOnly ? [EditorState.readOnly.of(true)] : [closeBrackets()],
    lintGutter(),
    autocompletion({ override: [completion(host)], activateOnTyping: true, icons: true }),
    hover(host),
    documentHighlights(host),
    clickToDefinition(host),
    keymap.of([
      { key: "F12", run: at(host.goToDefinition) },
      { key: "Mod-b", run: at(host.goToDefinition) },
      { key: "Shift-F12", run: at(host.findReferences) },
      { key: "F2", run: at(host.rename) },
      ...closeBracketsKeymap,
      ...defaultKeymap,
      ...searchKeymap,
      ...historyKeymap,
      ...completionKeymap,
      ...lintKeymap,
      indentWithTab,
    ]),
    EditorState.languageData.of(() => [{ commentTokens: { block: { open: "(*", close: "*)" } } }]),
    EditorView.updateListener.of(onChange),
  ];
}

/** The extensions of the generated code: read-only, highlighted. */
export function outputExtensions(lang: CodeLanguage): Extension {
  return [
    basics,
    EditorState.readOnly.of(true),
    lang === "lean" ? leanLanguage : ocamlLanguage,
    syntaxHighlighting(classHighlighter),
    keymap.of([...defaultKeymap, ...searchKeymap]),
  ];
}
