<script lang="ts">
  // Under the editor: the problems of every file, and the references found with Shift+F12 when
  // the server provides them. A row opens its location.
  import { EmptyState, Segmented, Spinner } from "purr";
  import { CheckCircle, Info, Warning, WarningCircle } from "purr/icons";
  import type { Location } from "../runtime/lsp";
  import { severity, type Workspace } from "./workspace.svelte";

  interface Props {
    ws: Workspace;
  }

  const { ws }: Props = $props();

  const problems = $derived(
    ws.files.flatMap((f) =>
      (ws.diagnostics.get(ws.uriOf(f)) ?? []).map((d) => ({ file: f, d, uri: ws.uriOf(f) })),
    ),
  );
  const refs = $derived(ws.references ?? []);
  const options = $derived([
    { id: "problems" as const, label: `Problems (${problems.length})` },
    ...(ws.has("referencesProvider")
      ? [{ id: "references" as const, label: `References (${refs.length})` }]
      : []),
  ]);

  const at = (l: Location) => `${l.range.start.line + 1}:${l.range.start.character + 1}`;
</script>

<div class="panel">
  <div class="head">
    <Segmented label="Panel" size="sm" {options} bind:value={ws.panel} />
  </div>
  <ul class="list">
    {#if ws.panel === "problems"}
      {#each problems as { file, d, uri } (`${uri}:${d.range.start.line}:${d.range.start.character}:${d.message}`)}
        {@const sev = severity(d)}
        <li>
          <button
            type="button"
            class="row-item"
            onclick={() => ws.openLocation({ uri, range: d.range })}
          >
            <span class="icon {sev}" aria-label={sev}>
              {#if sev === "error"}<WarningCircle weight="fill" />{:else if sev === "warning"}<Warning
                  weight="fill"
                />{:else}<Info />{/if}
            </span>
            <span class="loc mono">{file.name}:{at({ uri, range: d.range })}</span>
            <span class="msg truncate">{d.message}</span>
          </button>
        </li>
      {:else}
        <li>
          {#if ws.status === "loading"}
            <p class="wait"><Spinner size="1em" /> Starting the language server…</p>
          {:else}
            <EmptyState inline icon={CheckCircle} text="No problems" />
          {/if}
        </li>
      {/each}
    {:else}
      {#each refs as loc, i (i)}
        <li>
          <button type="button" class="row-item" onclick={() => ws.openLocation(loc)}>
            <span class="loc mono">{ws.nameOf(loc.uri)}:{at(loc)}</span>
            <span class="msg truncate mono">{ws.lineAt(loc)}</span>
          </button>
        </li>
      {:else}
        <li><EmptyState inline text="No references" /></li>
      {/each}
    {/if}
  </ul>
</div>

<style>
  .panel {
    display: flex;
    flex-direction: column;
    height: 100%;
    min-height: 0;
    background: var(--bg2);
  }
  .head {
    display: flex;
    align-items: center;
    padding: var(--sp-2) var(--sp-3);
  }
  .list {
    flex: 1;
    min-height: 0;
    margin: 0;
    padding: 0 var(--sp-2) var(--sp-2);
    overflow: auto;
    list-style: none;
  }
  .row-item {
    gap: var(--gap-4);
  }
  .icon {
    display: inline-flex;
    font-size: var(--icon-md);
  }
  .icon.error {
    color: var(--danger);
  }
  .icon.warning {
    color: var(--warn);
  }
  .icon.info {
    color: var(--info);
  }
  .loc {
    flex: none;
    color: var(--muted);
  }
  .msg {
    flex: 1;
  }
  .wait {
    display: flex;
    align-items: center;
    gap: var(--gap-3);
    margin: 0;
    padding: var(--sp-2) var(--sp-3);
    color: var(--muted);
  }
</style>
