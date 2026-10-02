// Inline code that names its language, in purr's spelling (`inlineCodeLang`): a code span of the
// pages whose text ends in `{:kanon}`, `{:lean}` or `{:ocaml}` loses that suffix and is
// highlighted as a block of that language is (`Code.svelte`), Kanon as a fragment (an expression,
// a pattern, attributes, …: see `highlightKanonFragment`). In a Svelte page, the suffix is
// written in a string, as braces are Svelte's: <code>{`rule f : Not v{:kanon}`}</code>.

import { inlineCodeLang } from "purr";
import { highlightKanonFragment, loadKanonSyntax } from "./kanon";
import { highlightStatic } from "./languages";

/** Highlights the inline code of `root` (its `code` outside of `pre`) that names its language. */
export function highlightInlineCode(root: HTMLElement): void {
  const kanon: [HTMLElement, string][] = [];
  for (const el of root.querySelectorAll<HTMLElement>("code")) {
    if (el.closest("pre")) continue;
    const span = inlineCodeLang(el.textContent ?? "");
    if (!span) continue;
    el.classList.add(`language-${span.lang}`);
    el.textContent = span.code;
    if (span.lang === "ocaml" || span.lang === "lean") el.innerHTML = highlightStatic(span.lang, span.code);
    else if (span.lang === "kanon") kanon.push([el, span.code]);
  }
  if (kanon.length === 0) return;
  // plain until the grammar has loaded, as blocks are
  loadKanonSyntax().then((syntax) => {
    if (syntax) for (const [el, code] of kanon) el.innerHTML = highlightKanonFragment(syntax, code);
  });
}
