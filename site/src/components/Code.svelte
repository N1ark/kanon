<script lang="ts">
  // A block of code with a copy button: Kanon highlighted by tree-sitter once its grammar has
  // loaded (plain until then), OCaml and Lean by CodeMirror's modes.
  import { IconButton, copyText, toast } from "purr";
  import { Check, Copy } from "purr/icons";
  import { highlightKanon, loadKanonSyntax } from "../highlight/kanon";
  import { highlightStatic } from "../highlight/languages";
  import { escapeHtml } from "../lib/util";

  interface Props {
    code: string;
    lang?: "kanon" | "ocaml" | "lean" | "text";
    /** Accessible name of the copy button. */
    copyLabel?: string;
  }

  const { code, lang = "kanon", copyLabel = "Copy the code" }: Props = $props();

  let html = $state("");
  $effect(() => {
    const text = code.replace(/\n$/, "");
    if (lang === "ocaml" || lang === "lean") {
      html = highlightStatic(lang, text);
      return;
    }
    html = escapeHtml(text);
    if (lang !== "kanon") return;
    let live = true;
    loadKanonSyntax().then((syntax) => {
      if (live && syntax) html = highlightKanon(syntax, text);
    });
    return () => (live = false);
  });

  let copied = $state(false);
  let timer: ReturnType<typeof setTimeout> | undefined;

  async function copy() {
    if (!(await copyText(code))) {
      toast("Couldn't reach the clipboard", { kind: "error" });
      return;
    }
    copied = true;
    clearTimeout(timer);
    timer = setTimeout(() => (copied = false), 1200);
  }
</script>

<div class="block">
  <pre class="code" data-lang={lang}><code>{@html html}</code></pre>
  <div class="copy">
    <IconButton label={copied ? "Copied" : copyLabel} onclick={copy}>
      {#if copied}<Check />{:else}<Copy />{/if}
    </IconButton>
  </div>
</div>

<style>
  .block {
    position: relative;
    min-width: 0;
    margin: var(--md-block, var(--sp-4)) 0;
    border: 1px solid var(--border);
    border-radius: var(--radius-lg);
    background: var(--code-bg);
  }
  pre {
    padding-right: calc(var(--sp-5) * 2 + var(--btn));
  }
  /* `.md pre` styles a bare block; this one is framed by `.block`. */
  .block :global(pre.code) {
    margin: 0;
    border: none;
    background: none;
  }
  .block :global(pre.code code) {
    padding: 0;
    background: none;
    font-size: inherit;
  }
  .copy {
    position: absolute;
    top: var(--sp-2);
    right: var(--sp-2);
    opacity: 0;
    transition: opacity var(--dur);
  }
  .block:is(:hover, :focus-within) .copy {
    opacity: 1;
  }
  @media (hover: none) {
    .copy {
      opacity: 1;
    }
  }
</style>
