---
type: decision
id: 0009
provenance: host/dialect.py; editor/vscode-phi/{extension.js,render.js,
  package.json}; host/toolchain.json (dialect selftest);
  megaplan P10 tail (projectional editor)
ts: 2026-10-12
tags: [dialect-bridge, vscode, projection, editor, declared-vs-realized]
---
# The editor projects through the toolchain; nothing is parsed twice

`host/dialect.py` is the routing bridge the downstream tooling
asked for: one stateless CLI that projects any stage file through
the existing host modules and answers JSON.

    python host/dialect.py --file X --as auto      # detect + views
    python host/dialect.py --file X --as phi.rel   # .phi -> rel-graph
    python host/dialect.py --file X --as schema    # admissibility
    python host/dialect.py --file X --as eval --call add \
        --args '[{"atom":[8,2]},{"atom":[8,3]}]'   # bounded RUN
    python host/dialect.py --file X --as bundle    # .plex sections
    python host/dialect.py --file X --as spec      # status card

Output contract is uniform: `{"dialect", "ok", "data"|"error"}` —
refusals surface as data, never as stack traces the consumer has
to guess at.

## Why a bridge instead of extension-side parsing

The discipline the whole project rests on — semantics live in
declared data and host modules, not in scattered reimplementations —
applies to the editor twice over. A JS parser for `.phi` would be a
second grammar that silently drifts from `phi_rel.parse_rel`. So the
extension never parses: it shells out to `dialect.py` and renders
the JSON. The editor is a viewport; the toolchain stays the one
truth. When a projection refuses, the refusal the user sees is the
same `SchemaRefusal` text `rel_schema` raised.

## What the extension projects

`editor/vscode-phi/` (plain JS, no build step):

- **phi.rel: Project Dialect** — detects the file's dialect, offers
  its switchable views (`phi.rel → rel-graph | schema | eval |
  file`), renders the chosen projection in a webview: rel signatures
  with direction arrows and shape badges, clauses as collapsible
  goal lists, schema verdicts, bundle section inventories with
  REALIZATION rows, spec status cards.
- **phi.rel: Run Rel Query** — `--as eval` behind an input box;
  args are rel-graph term nodes, the same JSON the parser emits.
- **Spec Status tree** — `host/specs/*.json` as a live registry:
  layer/axis/status per spec, pass-icon for realized, hollow circle
  for declared. Progress is visible because status is data.
- **Rel Graph tree** — the open `.phi`'s relations (sig arity,
  direction, shape) projected in the sidebar.
- **Diagnostics** — on save of `.phi`, the schema projection runs;
  a refusal becomes an editor diagnostic naming the violated
  invariant.

## Trade-offs stated

- Eval defaults to `n=1` (committed read). `--n N` widens it, but
  N past the real solution count diverges honestly — that's the
  RUN quotient, not a bug, and the bridge says so in its docstring.
- Diagnostics are whole-document: `RelError`/`SchemaRefusal` carry
  invariant names but not source spans. Line-accurate squiggles
  need the parser to thread token positions into refusal data —
  a real next step, deliberately not faked now.
- The extension is unpackaged (folder + `package.json`); install is
  "Extensions: Install from VSIX" later or a symlink into
  `%USERPROFILE%\.vscode\extensions`. VSIX packaging is tooling
  overhead deferred until the projection surface stabilizes.
- `file`/`auto` detection is extension- and JSON-shape-based —
  a `.phi` that isn't phi.rel/1 still detects as `phi.rel` and the
  refusal comes from the parser, which is the honest place for it.

## Status honesty

`phi.rel` and `schema-rel` stay `status: declared` in their specs —
the bridge is host-side routing, not an emitted leg. The selftest
`dialect` is registered fast-tier: it drives every projection
through the `PROJECTIONS` dispatch (the same code path the editor
shells out to), including a forged unbound-call graph that must be
refused — the bridge reports refusals as data, and that's tested.
