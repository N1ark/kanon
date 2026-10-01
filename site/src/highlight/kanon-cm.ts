// The tree-sitter highlighting of Kanon in CodeMirror: a view plugin that keeps
// the syntax tree of the document, reparses it incrementally on edits, and
// decorates the visible ranges with the classes of the captures.

import { RangeSetBuilder, type Text } from "@codemirror/state";
import { Decoration, EditorView, ViewPlugin, type DecorationSet, type ViewUpdate } from "@codemirror/view";
import type { Point, Tree } from "web-tree-sitter";
import { captureClasses, captures, type KanonSyntax } from "./kanon";

function point(doc: Text, pos: number): Point {
  const line = doc.lineAt(pos);
  return { row: line.number - 1, column: pos - line.from };
}

const marks = new Map<string, Decoration>();
const mark = (name: string) => {
  let m = marks.get(name);
  if (!m) marks.set(name, (m = Decoration.mark({ class: captureClasses(name) })));
  return m;
};

export function kanonHighlighting(syntax: KanonSyntax) {
  return ViewPlugin.fromClass(
    class {
      tree: Tree | null;
      decorations: DecorationSet;

      constructor(view: EditorView) {
        this.tree = syntax.parser.parse(view.state.doc.toString());
        this.decorations = this.build(view);
      }

      update(u: ViewUpdate) {
        if (u.docChanged && this.tree) {
          // the changes, last first, so that the positions before each are
          // those of the old document
          const changes: [number, number, number, number][] = [];
          u.changes.iterChanges((fromA, toA, fromB, toB) => changes.push([fromA, toA, fromB, toB]));
          for (const [fromA, toA, fromB, toB] of changes.reverse()) {
            const start = point(u.startState.doc, fromA);
            const inserted = u.state.doc.sliceString(fromB, toB);
            const lines = inserted.split("\n");
            this.tree.edit({
              startIndex: fromA,
              oldEndIndex: toA,
              newEndIndex: fromA + inserted.length,
              startPosition: start,
              oldEndPosition: point(u.startState.doc, toA),
              newEndPosition:
                lines.length === 1
                  ? { row: start.row, column: start.column + inserted.length }
                  : { row: start.row + lines.length - 1, column: lines[lines.length - 1].length },
            });
          }
          const old = this.tree;
          this.tree = syntax.parser.parse(u.state.doc.toString(), old);
          old.delete();
        }
        if (u.docChanged || u.viewportChanged) this.decorations = this.build(u.view);
      }

      build(view: EditorView): DecorationSet {
        const b = new RangeSetBuilder<Decoration>();
        if (!this.tree) return b.finish();
        const doc = view.state.doc;
        const spans = view.visibleRanges.flatMap(({ from, to }) =>
          captures(syntax, this.tree!.rootNode, doc.lineAt(from).number - 1, doc.lineAt(to).number).filter(
            (s) => s.to > from && s.from < to,
          ),
        );
        // the visible ranges may share captures
        const seen = new Set<string>();
        for (const s of spans.sort((a, b) => a.from - b.from || b.to - a.to)) {
          const key = `${s.from}:${s.to}`;
          if (seen.has(key)) continue;
          seen.add(key);
          b.add(s.from, s.to, mark(s.name));
        }
        return b.finish();
      }

      destroy() {
        this.tree?.delete();
      }
    },
    { decorations: (v) => v.decorations },
  );
}
