<script lang="ts">
  // The bar of the pages: the name, the switch between the tutorial, the reference and the
  // sandbox, the theme and the repository.
  import { IconButton, Segmented, liveTheme, tooltip } from "purr";
  import { GithubLogo, Moon, Sun } from "purr/icons";
  import type { Snippet } from "svelte";
  import { toggleTheme } from "../lib/theme";

  type Page = "tutorial" | "reference" | "sandbox";

  interface Props {
    page: Page;
    /** After the switch: the page's status. */
    children?: Snippet;
  }

  const { page, children }: Props = $props();

  const PAGES: { id: Page; label: string }[] = [
    { id: "tutorial", label: "Tutorial" },
    { id: "reference", label: "Reference" },
    { id: "sandbox", label: "Sandbox" },
  ];
  const HREF: Record<Page, string> = {
    tutorial: "./",
    reference: "reference.html",
    sandbox: "sandbox.html",
  };
</script>

<header class="bar">
  <a class="brand" href="./">Kanon</a>
  <nav aria-label="Site">
    <Segmented
      label="Page"
      options={PAGES}
      value={page}
      onchange={(id) => (location.href = HREF[id])}
    />
  </nav>
  <span class="status">{@render children?.()}</span>
  <IconButton
    label={liveTheme.dark ? "Light theme" : "Dark theme"}
    size="lg"
    onclick={toggleTheme}
  >
    {#if liveTheme.dark}<Sun />{:else}<Moon />{/if}
  </IconButton>
  <a
    class="btn btn--icon btn--ghost btn--lg"
    href="https://github.com/N1ark/kanon"
    aria-label="Kanon on GitHub"
    use:tooltip={"Kanon on GitHub"}><GithubLogo /></a
  >
</header>

<style>
  .bar {
    position: sticky;
    top: 0;
    z-index: var(--z-chrome);
    display: flex;
    align-items: center;
    gap: var(--gap-4);
    min-width: 0;
    padding: var(--sp-2) var(--sp-4);
    border-bottom: 1px solid var(--border);
    background: var(--bg2);
  }
  .brand {
    padding: 0 var(--sp-2);
    font-size: var(--fs-xl);
    font-weight: 700;
    letter-spacing: -0.02em;
    color: var(--theme2);
    text-decoration: none;
  }
  .status {
    display: flex;
    align-items: center;
    justify-content: flex-end;
    gap: var(--gap-3);
    flex: 1;
    min-width: 0;
  }
</style>
