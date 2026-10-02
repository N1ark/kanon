// The example languages (examples/index.json): the templates of the sandbox
// and the steps of the tutorial, with their sources imported from the
// repository at build time.

import manifest from "../examples/index.json";

const sources = import.meta.glob(
  ["../examples/*/*.kn", "../examples/*/*.knl", "../../examples/bool/lang.knl", "../../modules/*.kn", "../../modules/*.knl", "../../test/tiny.t/*.kn", "../../test/tiny.t/*.knl"],
  { query: "?raw", import: "default", eager: true },
) as Record<string, string>;

export interface Example {
  id: string;
  title: string;
  description?: string;
  template?: boolean;
  /** The files, by name, in order. */
  files: [string, string][];
}

export const examples: Example[] = manifest.examples.map((e) => ({
  ...e,
  files: Object.entries(e.files as unknown as Record<string, string>).map(([name, path]) => {
    const text = sources[`../${path}`];
    if (text === undefined) throw new Error(`examples/index.json: ${path} is not imported (see src/examples.ts)`);
    return [name, text];
  }),
}));

export const exampleById = (id: string) => examples.find((e) => e.id === id);

/** The root files of a language: its .knl files that no other file uses (e.g.
 * lang.knl), as the language server finds them. */
export function roots(files: Iterable<[string, string]>): string[] {
  const all = [...files];
  const used = new Set<string>();
  for (const [, text] of all)
    for (const m of text.matchAll(/^\s*use\s+"([^"]+)"/gm)) {
      used.add(`${m[1]}.knl`);
      used.add(`${m[1]}.kn`);
    }
  return all.map(([n]) => n).filter((n) => n.endsWith(".knl") && !used.has(n));
}
