// The little markdown of the language server's hovers: fenced code blocks
// (Kanon highlighted by tree-sitter), paragraphs, `code`, *emphasis* and
// **strong**. Everything else is text.

import { highlightKanon, type KanonSyntax } from "./highlight/kanon";
import { highlightStatic } from "./highlight/languages";
import { escapeHtml } from "./util";

function inline(s: string): string {
  return escapeHtml(s)
    .replace(/`([^`]+)`/g, "<code>$1</code>")
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[^\w*])\*([^*\s][^*]*)\*(?![\w*])/g, "$1<em>$2</em>")
    .replace(/(^|[^\w])_([^_\s][^_]*)_(?!\w)/g, "$1<em>$2</em>");
}

export function renderMarkdown(md: string, syntax: KanonSyntax | null): string {
  const out: string[] = [];
  const lines = md.replace(/\r\n/g, "\n").split("\n");
  let para: string[] = [];
  const flush = () => {
    if (para.length) out.push(`<p>${inline(para.join("\n"))}</p>`);
    para = [];
  };
  for (let i = 0; i < lines.length; i++) {
    const fence = /^\s*```\s*([\w-]*)\s*$/.exec(lines[i]);
    if (fence) {
      flush();
      const code: string[] = [];
      for (i++; i < lines.length && !/^\s*```\s*$/.test(lines[i]); i++) code.push(lines[i]);
      const text = code.join("\n");
      const lang = fence[1] || "kanon";
      const html =
        lang === "kanon" && syntax
          ? highlightKanon(syntax, text)
          : lang === "ocaml" || lang === "lean"
            ? highlightStatic(lang, text)
            : escapeHtml(text);
      out.push(`<pre class="code">${html}</pre>`);
    } else if (lines[i].trim() === "") flush();
    else para.push(lines[i]);
  }
  flush();
  return out.join("");
}
