---
type: feature
id: 0002
provenance: gates_nanopass gate 24; emit_chain.run_emit_bundle /
  emit_schedule_streams / _pack_recipe; plex_bundle KIND_MAP;
  spec_term.slice_ir
ts: 2026-10-08
tags: [phase8, emit, schedule, dag, bundle, map]
---
# The staged DAG is fully serialized

## What changed

`emit.plex` now carries **every** stage's executable stream —
including the two that used to be resolved Python-side:

- `emit.assemble`: one `encodeOf item resv` root per prep position,
  in order.  Frames concat to `.text` directly — no pass-2 replay,
  no substitution bookkeeping at consume time.  The resv closure
  (symtab, loc map, end4) is baked into each rel-sensitive query
  seed-side from the Python oracles (`python_link`, `isa.encode`).
- `emit.pack`: `_pack_recipe` serialized — literal header chunks as
  already-NF bytelist queries, computed fields (`ALIGN*`, `B4ADD`,
  `ZEROFILL`, `PADLIST`, `U64`) as roots, and the section splices
  as **KIND_MAP rows** (`stage_idx, at, src_stage, src_frame`;
  `0xFFFFFFFF` = all frames).

`run_emit_bundle` is now a pure executor: dep closure of
`schedule.output` -> topological order -> each stage on its
declared runner -> MAP-declared concat.  It never resolves a stage,
never recomputes an artifact.  `_pack_recipe` is shared element
data between the `.plex` bake and `pack_staged` — one recipe, two
realizations.

## Why

Previously the bundle serialized only the leaf stages; Python
re-derived assemble's two passes and pack's 47-chunk interleave at
replay.  That was the last place the *consumer* — not the author —
decided what the schedule computes.  Now the DAG is honest data:
STAGES/DEPS/QUERIES/MAP rows plus streams, and any host that can
depack PIR + spawn runners can execute it.  It is also the surface
parallel scheduling needs — dep-level independence is declared,
`workers=N` becomes scheduling, not semantics.

## Subtleties worth remembering

- **Bounded execution is slicing, not repacking.**  The bump arena
  accumulates across a stream's roots (~550 encode roots OOMed at
  rc=4).  `spec_term.slice_ir` projects a root-range substream —
  postorder preserved, digests position-independent — so the
  executor halves the span on rc=4 without changing root content
  or order.  Arena pressure is a scheduling property, answered by
  scheduling.
- **fs-gating lives in the term, so it lives in the mirror.**
  `routine_expr` wraps `st_s`/`build_ds` in `fs ? frag : NIL` —
  `_schedule_items` applies the same skip.  Emitting both
  unconditionally produced 509 baked roots vs 493 decoded items;
  the count audit caught it exactly as designed.
- **Frags are pre-xform.**  The term carries raw builder output;
  `_mt_xform` is an emitted-program view, not the term's.  Two
  honest quotients: `_emit_parts` (emitted, post-xform) vs
  `_schedule_items` (term, raw).
- **Audit is cheap but real.**  Replay refuses when decoded
  program items no longer enumerate the baked encode roots
  (count-level correspondence — a forged stream set is corrupt,
  not an alternate image).  A fuse_s program stream swapped into
  a default bundle refuses on this audit.
- **Structural completeness is checked before execution.**  A
  dep-closure stage with no stream, a MAP row outside STAGES, a
  MAP `at` beyond the stream's root count, a MAP src that isn't a
  declared dep — all refuse up front; src frame bounds refuse at
  assembly.
- **passes need mirrors.**  A pass without a `_PASS_PY` entry
  refuses at bake time rather than silently shipping un-passed
  items — the seed-side item list must be the term's output, not a
  guess.

## Evidence

- `emit.plex` replay == `emit_native` byte-identical (3584 B) —
  gate 24.
- All six stage rows are `pir-stream`; MAP rows land at pack
  positions 47/48/49 (idata, datab, .text) exactly as the recipe
  declares — gate 24.
- Forges refuse: MAP src frame out of range; dep-closure stage
  with no stream; program/assemble streams out of correspondence —
  gate 24.
- `slice_ir` round-trip: sliced roots unpack to identical digests.
- `pack_staged` == `python_pack` through the shared recipe
  (2048 B mini image).
- Python's residue is now: spawn subprocesses, concat frames,
  write the file, compare bytes.
