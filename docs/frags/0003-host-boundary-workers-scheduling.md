---
type: refactor
id: 0003
provenance: gates_nanopass suite 24/24; emit_chain.run_emit_bundle /
  emit_frames workers; host/gates/* host/benches/* layout;
  battery.py selector paths; basis.py retired
ts: 2026-10-08
tags: [phase8, cleanup, package-boundary, workers, scheduling]
---
# host/ is a package; workers=N is scheduling

## What changed

- **`host/` gets a boundary.**  Gates live in `host/gates/`,
  benches in `host/benches/`; the flat `host/*.py` layer is the
  module surface only.  `toolchain.json` names suites and
  selftests by host-relative path (`gates/spec_check`,
  `benches/diag`); `battery.py` sanitizes the `/` for log files
  and matches `--only` selectors against the path form.
- **`gates_nanopass.py` (1097 lines) split by evidence family**:
  `np_common` (shared helpers), `np_gates_record` (programOf:
  frags, passes, trie, sentinels), `np_gates_streams`
  (arena-boundary: bounded batches, pins, blob store, staged
  link, ir egress), `np_gates_emit` (emit chain: manifest, staged
  frames, fixpoint, serialized DAG), `np_gates_kernel`
  (container: bundle format, MT equiv, .plex ingest, layer legs).
  The runner keeps the original 24-gate order and gains
  `--only=a,b` substring selection.
- **`workers=N` wired through the emit chain.**  `emit_frames`'s
  staged path propagates it to the term/bytes/ir runners;
  `run_emit_bundle` uses it twice — a chunk pool inside one
  stage's sliced root table, and dep-level parallelism across
  independent stages (levels computed from DEPS rows — declared
  data, not inference).
- **`basis.py` retired** — a deprecated re-export shim with zero
  importers.  Dead imports/`R1`/`sidx`/`struct`/`hashlib`
  leftovers removed from the split modules; the seed's
  `spec_check` drift (default-toolchain lookup stranded in
  `_emit` instead of `emit`) was repaired in place.

## Why

The user's organizing rule: apart from `seed/`, Python is either
a gate, a bench, or a host module — and each lives where its role
says.  `workers` exists because the serialized DAG made
independence explicit: DEPS rows declare which stages may run
concurrently, `slice_ir` chunking declares which roots are
independent *inside* a stage.  Both are scheduling questions
asked of data — exactly the split Phase 8b set up.

## Subtleties worth remembering

- **Parallelism is two levels, both declared.**  Within a stage:
  the root table is sliced and chunks stride across exes (order
  preserved — `pool.map` returns in submission order).  Across
  stages: `lvl[i] = 1 + max(lvl[d] for d in deps[i])`; each level
  runs concurrently, results keyed by stage name.  `emit.assemble`
  can never precede `emit.program` — DEPS forbids it, not the
  executor's care.
- **Failure propagates through pools.**  An rc=4 inside a chunk
  pool still triggers span-halving (the `NotRealized` escapes the
  `pool.map` into the same retry loop the serial path uses); a
  stage failure aborts the level, which aborts the replay.
- **The import shim is the real boundary.**  Moved modules add
  one `dirname` to `_HOST`; gate modules also add `seed/` — the
  monolith got `seed` transitively through `emit_chain`, the
  split modules can't rely on import order.  pyflakes caught the
  three missing names (`seed` in streams, `rts` in emit) that
  runtime order had hidden.
- **Selftest names are paths.**  `toolchain.json`'s suite/module
  fields are host-relative (`gates/xisa_gate`), so subdirectory
  moves only needed the rename — no resolver change.  The one
  real hazard was log filenames (`gates/x` isn't a filename);
  sanitization lives in `battery.py` where names become paths.

## Evidence

- `run_emit_bundle(workers=4)` replay: **byte-identical** to
  `emit_native` (3584 B) at ~2.3x serial wall — scheduling only,
  output invariant.
- Split suite: 21/24 on first run (three import-order bugs —
  `seed` in np_gates_streams, `rts` in np_gates_emit — fixed and
  re-run green via `--only`), 24/24 total.
- `battery --only gates/spec_check`: 1 pass, log path sanitized.
- `spec_check` green after the `emit()` lookup repair (the drift
  predated the move; fixed honestly rather than waived).
- pyflakes clean on all split modules; `compileall` clean on
  `host/gates`, `host/benches`.
