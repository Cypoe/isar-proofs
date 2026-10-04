---
type: decision
id: 0010
provenance: host/phi_rel.py (render_rel); host/dialect.py (--set,
  rel-bundle detection, _graph_of); editor/vscode-phi/extension.js
  (phi-bundle: filesystem, view dropdown); frag 0009
ts: 2026-10-12
tags: [dialect-bridge, canonical-plex, projection, render_rel,
  editable-views, interpreter-shape]
---
# .plex is the document; surfaces are views; the bridge is the
# interpreter's shape

Three commitments landed together, because they're one idea:

1. **The `.plex` bundle is canonical.** `.phi` surface text is a
   derived, regenerable projection — never the store.  Saving a
   surface re-parses, schema-checks, and re-bundles; the surface
   file on disk is a working view, and `*.rel.plex` is the
   artifact of record (gitignored, always rebuilt).
2. **The inverse projection is real.** `phi_rel.render_rel` prints
   the full `phi.rel/1` vocabulary back to patent surface text,
   and `parse(render(g)) == g` is standing evidence in the
   selftest — verified on `stdlib.phi` and all three patent files,
   all 55 rels bit-stable through the round-trip.
3. **The bridge is read+write, and it is the shape of the emitted
   interpreter.** `dialect.py --set phi.rel` takes surface text on
   stdin and atomically rewrites the bundle (tmp + os.replace);
   a refused surface leaves the file byte-identical.  The
   `PROJECTIONS`/`SETTERS` dispatch is exactly the runtime model a
   native `phi` interpreter needs: open bundle → project view →
   accept edit → rebundle.  When cogen lands, *this* is what gets
   specialized — the interpreter is the intermediary, not a
   separate tool (same position the Python seed holds vs. the
   emitted host).

## Detection is content-based where it matters

A `.plex` whose REALIZATION rows declare `dialect: phi.rel/1`
detects as `rel-bundle` and gains the full view set — `phi.rel`
(surface text), `rel-graph`, `schema`, `eval`, `bundle`, `file` —
while a stage bundle still detects as `bundle`.  `_graph_of`
normalizes "the rel-graph behind --file" across `.phi`,
graph-json, and `.plex`, so `schema` and `eval` run identically
on the bundle and on the surface that derived it.

## What the extension does now

- **View dropdown**: a status-bar chip (`view: X`) bound per
  document.  QuickPick lists the detected file's `views`; the
  choice sticks and re-renders.
- **`phi-bundle:` filesystem**: opening a `.plex` rel-bundle as
  `phi.rel` gives a real editable text document.  Save goes
  through `writeFile → --set → atomic rebundle`; a schema refusal
  throws `FileSystemError`, the doc stays dirty, the bundle is
  untouched.  That is projectional editing in the strict sense:
  the store is the bundle, the text is the view.
- **`.phi` save rebundles**: every save of a surface file writes
  its sibling `X.rel.plex` (status bar reports rels/bytes, or the
  refusal).  The corpus stays text-editable while the canonical
  artifact is always fresh.
- Refusals remain data everywhere: `SchemaRefusal` text appears
  as diagnostics, status messages, and `{"ok": false}` envelopes
  — never as a silent fallback or a crash.

## Trade-offs stated

- `--set` refuses an *empty* surface (a legal parse, but writing
  a 0-rel bundle destroys the document — observed live during
  testing when empty stdin wrote 232 bytes over a corpus bundle).
- `render_rel` normalizes: `UNIFY a b` prints as `a = b`, lists
  print as `[a, b]`, `ATOM(8,n)` prints bare `n`.  The invariant
  is *graph* round-trip, not text round-trip — the patent files
  are not byte-reproduced, their graphs are.
- `phi-bundle:` is `isCaseSensitive`, minimal stat (mtime =
  access time); watching/external-change events are not pushed.
  Fine for a single-user edit loop.
- The extension still isn't packaged — same VSIX deferral as
  frag 0009.
- `WRITABLE` has one member (`phi.rel`).  Other dialects get a
  write verb only when they declare a renderer — no fake saves.
