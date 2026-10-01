<script lang="ts">
  // The files of the sandbox as tabs: click to edit, double-click or the context menu to rename,
  // the cross to delete (or to close a built-in module's file). A tab counts its errors.
  import { Badge, IconButton, menu, tooltip } from "purr";
  import { LockSimple, PencilSimple, Plus, Trash, X } from "purr/icons";
  import { tick } from "svelte";
  import type { FileEntry, Workspace } from "./workspace.svelte";

  interface Props {
    ws: Workspace;
  }

  const { ws }: Props = $props();

  let list = $state<HTMLElement | null>(null);

  function contextMenu(e: MouseEvent, f: FileEntry) {
    if (f.builtinPath) return;
    menu.show(
      e,
      [
        { label: "Rename…", icon: PencilSimple, run: () => ws.renameFile(f) },
        { label: "Delete", icon: Trash, danger: true, run: () => ws.closeFile(f) },
      ],
      f.name,
    );
  }

  function keydown(e: KeyboardEvent, f: FileEntry) {
    const i = ws.files.indexOf(f);
    if (e.key === "ArrowRight" || e.key === "ArrowLeft") {
      const n = ws.files.length;
      const g = ws.files[(i + (e.key === "ArrowRight" ? 1 : n - 1)) % n];
      ws.switchTo(g);
      tick().then(() => list?.querySelector<HTMLElement>("[aria-selected=true]")?.focus());
    } else if (e.key === "F2") ws.renameFile(f);
  }
</script>

<div class="tabs">
  <div class="list" role="tablist" aria-label="Files" bind:this={list}>
    {#each ws.files as f (f)}
      {@const errors = ws.errorsIn(f)}
      <div class="tab" class:is-current={f === ws.active} class:builtin={f.builtinPath}>
        <button
          type="button"
          role="tab"
          class="name"
          aria-selected={f === ws.active}
          tabindex={f === ws.active ? 0 : -1}
          onclick={() => ws.switchTo(f)}
          ondblclick={() => ws.renameFile(f)}
          oncontextmenu={(e) => contextMenu(e, f)}
          onkeydown={(e) => keydown(e, f)}
          use:tooltip={f.builtinPath ? `${f.name}: a built-in module, read-only` : null}
        >
          {#if f.builtinPath}<LockSimple />{/if}
          {f.name}
          {#if errors}<Badge count={errors} tone="danger" />{/if}
        </button>
        <IconButton
          label={f.builtinPath ? `Close ${f.name}` : `Delete ${f.name}`}
          size="sm"
          danger={!f.builtinPath}
          onclick={() => ws.closeFile(f)}><X /></IconButton
        >
      </div>
    {/each}
  </div>
  <IconButton label="New file" onclick={() => ws.addFile()}><Plus /></IconButton>
</div>

<style>
  .tabs {
    display: flex;
    align-items: center;
    gap: var(--gap-2);
    min-width: 0;
    padding-right: var(--sp-3);
    border-bottom: 1px solid var(--border);
    background: var(--bg2);
  }
  .list {
    display: flex;
    min-width: 0;
    overflow-x: auto;
    scrollbar-width: none;
  }
  .tab {
    position: relative;
    display: flex;
    align-items: center;
    gap: var(--gap-1);
    flex: none;
    padding: 0 var(--sp-2) 0 0;
    border-right: 1px solid var(--border);
    color: var(--muted);
  }
  .tab.is-current {
    background: var(--bg);
    color: var(--color2);
  }
  .tab.is-current::after {
    content: "";
    position: absolute;
    inset: 0 0 auto;
    height: 2px;
    background: var(--theme);
  }
  .name {
    display: flex;
    align-items: center;
    gap: var(--gap-3);
    height: calc(var(--btn) + var(--sp-3));
    padding: 0 var(--sp-2) 0 var(--sp-4);
    font-family: var(--mono);
    font-size: var(--fs-sm);
  }
  .is-current .name {
    font-weight: 600;
  }
  .builtin .name {
    font-style: italic;
  }
  .name:focus-visible {
    outline-offset: -2px;
  }
  @media (hover: hover) {
    .tab:not(.is-current):hover {
      background: var(--bg3);
      color: var(--color2);
    }
  }
</style>
