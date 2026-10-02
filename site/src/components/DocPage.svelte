<script lang="ts">
  // The layout of the pages to read, the tutorial and the reference: the bar, a table of contents
  // of the headings of the article (following the one in view), and the article.
  import {
    ContextMenuHost,
    DialogHost,
    TableOfContents,
    ToastHost,
    headingsIn,
    type TocItem,
  } from "purr";
  import type { Snippet } from "svelte";
  import { highlightInlineCode } from "../highlight/inline";
  import Header from "./Header.svelte";

  interface Props {
    page: "tutorial" | "proving" | "reference";
    /** The headings of the table of contents. */
    headings?: string;
    children: Snippet;
  }

  const { page, headings = "h2", children }: Props = $props();

  let article = $state<HTMLElement | null>(null);
  let toc = $state<TocItem[]>([]);
  let current = $state<string | undefined>();

  $effect(() => {
    if (!article) return;
    toc = headingsIn(article, { selector: headings });
    const seen = new IntersectionObserver(
      (entries) => {
        for (const e of entries) if (e.isIntersecting) current = e.target.id;
      },
      { rootMargin: "-10% 0px -75% 0px" },
    );
    article.querySelectorAll(headings.split(",").map((h) => `${h.trim()}[id]`).join(",")).forEach((h) => seen.observe(h));
    return () => seen.disconnect();
  });

  $effect(() => {
    if (article) highlightInlineCode(article);
  });
</script>

<ContextMenuHost />
<DialogHost />
<ToastHost />

<Header {page} />

<div class="layout">
  <aside class="toc">
    <TableOfContents items={toc} title="Contents" {current} />
  </aside>

  <article class="md" bind:this={article}>
    {@render children()}
  </article>
</div>

<style>
  .layout {
    display: grid;
    grid-template-columns: 14rem minmax(0, 1fr);
    gap: calc(var(--sp-5) * 2);
    max-width: 1240px;
    margin: 0 auto;
    padding: 0 calc(var(--sp-5) * 2) calc(var(--sp-5) * 4);
  }
  .toc {
    position: sticky;
    top: calc(var(--btn) + var(--sp-5) * 3);
    align-self: start;
    max-height: calc(100vh - var(--btn) - var(--sp-5) * 4);
    overflow-y: auto;
    margin-top: calc(var(--sp-5) * 3);
  }
  article {
    --md-block: 0.8em;
    --md-line-height: 1.65;
    --md-h1: 2.2em;
    --md-h2: 1.5em;
    min-width: 0;
    padding-top: calc(var(--sp-5) * 2);
    font-size: var(--fs-lg);
  }
  /* The prose keeps a readable measure; the examples take the width. */
  article > :global(:not(figure)) {
    max-width: 46rem;
  }
  /* Operators are read character by character: `!=` is not `≠`, which is an operator too. */
  article :global(:is(code, pre)) {
    font-variant-ligatures: none;
  }
  /* The first column of a table names an attribute or a law: it never wraps (the table scrolls). */
  article :global(td:first-child code) {
    white-space: nowrap;
  }
  article :global(:is(h2, h3)) {
    scroll-margin-top: calc(var(--btn) + var(--sp-5) * 2);
  }
  article :global(h2) {
    padding-bottom: var(--sp-2);
    border-bottom: 1px solid var(--border);
  }
  @media (max-width: 1000px) {
    .layout {
      grid-template-columns: minmax(0, 1fr);
      padding: 0 var(--sp-5) calc(var(--sp-5) * 3);
    }
    .toc {
      display: none;
    }
  }
</style>
