<script lang="ts">
  // One side of an example's generated code: a backend of one language, picked from a segmented
  // control (or a menu, when there are many), and its output, computed when the example is seen.
  import { Button, Segmented, Spinner, menu } from "purr";
  import { CaretDown } from "purr/icons";
  import { untrack } from "svelte";
  import Code from "../components/Code.svelte";
  import type { Example } from "../examples";
  import { languageOf } from "../highlight/languages";
  import { KanonRuntime } from "../runtime/client";
  import type { RunResult } from "../runtime/protocol";
  import { run } from "./runs";

  interface Props {
    example: Example;
    title: string;
    backends: string[];
    initial: string;
    /** Starts generating once true. */
    visible: boolean;
  }

  const { example, title, backends: all, initial, visible }: Props = $props();

  let available = $state<string[] | null>(null);
  const backends = $derived(available ? all.filter((b) => available!.includes(b)) : all);
  let backend = $state(untrack(() => initial));
  let result = $state<RunResult | null>(null);
  let failure = $state<string | null>(null);

  // the backends that the runtime has
  KanonRuntime.load()
    .then((rt) => (available = rt.info.backends))
    .catch(() => {});

  $effect(() => {
    if (!visible) return;
    const b = backend;
    let live = true;
    result = null;
    failure = null;
    run(example, b)
      .then((r) => live && (result = r))
      .catch((e) => live && (failure = `The Kanon runtime is unavailable: ${(e as Error).message}`));
    return () => (live = false);
  });

  const short = (b: string) => b.replace(/^(ocaml|lean)-/, "") || b;
  const usage = $derived(result?.code !== 0 && result?.stderr.startsWith("usage:"));
</script>

<section class="pane" aria-label={title}>
  <header>
    <span class="title">{title}</span>
    {#if backends.length <= 4}
      <Segmented
        label="{title} backend"
        size="sm"
        options={backends.map((b) => ({ id: b, label: short(b) }))}
        bind:value={backend}
      />
    {:else}
      <Button
        size="sm"
        aria-haspopup="menu"
        onclick={(e) =>
          menu.showFor(
            e.currentTarget,
            backends.map((b) => ({ label: b, checked: b === backend, run: () => (backend = b) })),
            `${title} backend`,
            "bottom-end",
          )}
      >
        <span class="mono">{backend}</span>
        <CaretDown />
      </Button>
    {/if}
  </header>
  <div class="body">
    {#if failure}
      <p class="note error">{failure}</p>
    {:else if !result}
      <p class="note"><Spinner size="1em" label="Generating" /> Generating with kanon…</p>
    {:else if usage}
      <p class="note">This backend needs the rules of the language (<code>.kn</code> files).</p>
    {:else if result.code !== 0}
      <pre class="note error">{result.stderr.trim()}</pre>
    {:else}
      <Code code={result.stdout} lang={languageOf(backend)} copyLabel="Copy the generated code" />
    {/if}
  </div>
</section>

<style>
  .pane {
    display: flex;
    flex-direction: column;
    min-width: 0;
  }
  header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: var(--gap-4);
    min-height: calc(var(--btn) + var(--sp-2) * 2);
    padding: var(--sp-2) var(--sp-2) var(--sp-2) var(--sp-4);
    border-bottom: 1px solid var(--border);
    background: var(--bg2);
  }
  .title {
    font-size: var(--fs-micro);
    font-weight: 600;
    letter-spacing: 0.06em;
    text-transform: uppercase;
    color: var(--muted);
  }
  .body {
    height: 26rem;
    overflow: auto;
    background: var(--code-bg);
  }
  .body :global(.block) {
    margin: 0;
    border: none;
    border-radius: 0;
  }
  .note {
    display: flex;
    align-items: center;
    gap: var(--gap-3);
    margin: 0;
    padding: var(--sp-4) var(--sp-5);
    color: var(--muted);
  }
  .error {
    color: var(--danger);
    white-space: pre-wrap;
    font-family: var(--mono);
    font-size: var(--fs-sm);
  }
  @media (max-width: 760px) {
    .body {
      height: 20rem;
    }
  }
</style>
