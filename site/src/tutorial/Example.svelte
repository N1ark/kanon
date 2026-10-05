<script lang="ts">
  // A step of the tutorial: the files of an example language, and the OCaml and the Lean that
  // Kanon generates from them, side by side, computed once the example scrolls into view.
  import { Segmented } from "purr";
  import { ArrowSquareOut } from "purr/icons";
  import Code from "../components/Code.svelte";
  import { exampleById } from "../examples";
  import OutputPane from "./OutputPane.svelte";

  interface Props {
    id: string;
    /** The backends shown first. */
    ocaml?: string;
    lean?: string;
  }

  const { id, ocaml = "ocaml", lean = "lean-model" }: Props = $props();

  const example = $derived(exampleById(id)!);
  let file = $state(0);
  let element = $state<HTMLElement | null>(null);
  let visible = $state(false);

  $effect(() => {
    if (!element) return;
    const io = new IntersectionObserver(
      (entries) => {
        if (entries.some((e) => e.isIntersecting)) {
          visible = true;
          io.disconnect();
        }
      },
      { rootMargin: "600px 0px" },
    );
    io.observe(element);
    return () => io.disconnect();
  });

  const OCAML = ["ocaml-types", "ocaml", "ocaml-typed", "ocaml-tests"];
  const LEAN = [
    "lean-types",
    "lean-syntax",
    "lean-signatures",
    "lean-typing",
    "lean-model",
    "lean-statements",
    "lean-lifts",
    "lean-nodes",
    "lean-interface",
    "lean-soundness",
    "lean-modules",
  ];
</script>

<figure class="example" bind:this={element} data-example={id}>
  <header>
    <Segmented
      label="Files of {example.title}"
      size="sm"
      options={example.files.map(([name], i) => ({ id: String(i), label: name }))}
      bind:value={() => String(file), (v: string) => (file = Number(v))}
    />
    <a class="btn btn--sm" href="sandbox.html#example={id}">Open in sandbox <ArrowSquareOut /></a>
  </header>
  <div class="source">
    <Code code={example.files[file][1]} />
  </div>
  <div class="generated">
    <OutputPane {example} title="OCaml" backends={OCAML} initial={ocaml} {visible} />
    <OutputPane {example} title="Lean" backends={LEAN} initial={lean} {visible} />
  </div>
</figure>

<style>
  .example {
    margin: calc(var(--md-block) * 2) 0;
    border: 1px solid var(--border);
    border-radius: var(--radius-lg);
    overflow: hidden;
    background: var(--bg);
  }
  header {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: var(--gap-4);
    padding: var(--sp-2) var(--sp-3);
    border-bottom: 1px solid var(--border);
    background: var(--bg2);
  }
  .source {
    max-height: 24rem;
    overflow: auto;
    background: var(--code-bg);
  }
  .source :global(.block) {
    margin: 0;
    border: none;
    border-radius: 0;
  }
  .generated {
    display: grid;
    grid-template-columns: minmax(0, 1fr) minmax(0, 1fr);
    border-top: 1px solid var(--border);
  }
  .generated > :global(* + *) {
    border-left: 1px solid var(--border);
  }
  @media (max-width: 900px) {
    .generated {
      grid-template-columns: minmax(0, 1fr);
    }
    .generated > :global(* + *) {
      border-left: none;
      border-top: 1px solid var(--border);
    }
  }
</style>
