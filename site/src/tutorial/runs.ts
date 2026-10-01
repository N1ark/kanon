// The runs of kanon behind the tutorial's examples, one at a time: the files of an example are
// written to the runtime's directory while it runs, and each output is computed once.

import { roots, type Example } from "../examples";
import { KanonRuntime } from "../runtime/client";
import type { RunResult } from "../runtime/protocol";

let queue: Promise<unknown> = Promise.resolve();
let written: Example | undefined;
const results = new Map<string, Promise<RunResult>>();

export function run(ex: Example, backend: string): Promise<RunResult> {
  const key = `${ex.id}:${backend}`;
  let r = results.get(key);
  if (!r) {
    r = queue.then(async () => {
      const rt = await KanonRuntime.load();
      const dir = rt.info.root;
      if (written !== ex) {
        if (written) for (const [name] of written.files) await rt.removeFile(`${dir}/${name}`);
        for (const [name, text] of ex.files) await rt.writeFile(`${dir}/${name}`, text);
        written = ex;
      }
      return rt.run([backend, `${dir}/${roots(ex.files)[0]}`]);
    });
    queue = r.catch(() => {});
    results.set(key, r);
  }
  return r;
}
