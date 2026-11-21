---
id: 057
type: decision
ts: 2026-10-08
tags: [nanopass, phase8b, emit-plex, schedule, dag, map-section]
provenance: gates_nanopass gate 24; emit_chain run_emit_bundle /
  emit_schedule_streams / _pack_recipe; plex_bundle KIND_MAP;
  spec_term.slice_ir; docs/frags/0002
---
# 057 — Phase 8b: the staged DAG is fully serialized

## Decision

`emit.plex` (dialect `plex.emit/2`) now carries **every** stage's
executable stream.  The two stages that were `derived` — resolved
by the Python consumer at replay — are baked at write time:

- **emit.assemble**: one `encodeOf item resv` root per prep
  position, in program order.  Output = concat frames = `.text`;
  no pass-1/pass-2 replay at consume time.  rel-sensitive items
  carry their resv-closed query: merged symtab (from
  `python_link`), local label map and end4 (from the `isa.encode`
  length oracle) — schedule data authored seed-side, proven by the
  kernels' own frames.
- **emit.pack**: `_pack_recipe` serialized.  Literals ride as
  already-NF bytelist queries (format constants are data), the
  ALIGN/B4ADD/ZEROFILL/PADLIST/U64 fields are numeral-arg roots
  (unreduced args — confluence makes embedding the numeral
  identical to embedding its value), and the three section
  splices are **KIND_MAP rows** `(stage_idx, at, src_stage,
  src_frame)` u32×4, `0xFFFFFFFF` = all frames.

`run_emit_bundle` is a pure executor: dep closure of
`schedule.output` → topological order → each stage on its declared
runner (`exe.term`/`exe.bytes`/`exe.ir`) → MAP-declared concat.
No stage resolution, no recompute.  `_pack_recipe` is shared
element data between the `.plex` bake and `pack_staged` — one
recipe, two realizations.

## Design points an expert should not lose

- **slice_ir, not repacking.**  ~550 encode roots in one stream
  OOM the bump arena (roots share a live set across a call).
  `spec_term.slice_ir` projects root-range substreams — postorder
  preserved, content digests position-independent — so the
  executor halves span on rc=4.  Arena pressure is a scheduling
  property answered by scheduling; the schedule's roots never
  change.
- **The term's fs-gating is the mirror's contract.**  `st_s`/
  `build_ds` are `fs ? frag : NIL` in `routine_expr`;
  `_schedule_items` applies the same skip.  Emitting both gave
  509 baked roots vs 493 decoded items — the correspondence audit
  caught it.
- **Two honest quotients of the same routine set.**  `_emit_parts`
  (emitted program, post-`_mt_xform`) vs `_schedule_items`
  (term-level, raw frags — the term carries pre-xform output).
- **Correspondence is audited, not assumed.**  Replay refuses when
  decoded program items don't enumerate the baked roots
  (count-level); structural completeness — missing stream, MAP
  bounds, src-is-dep — refuses before execution; src frame bounds
  refuse at assembly.  A forged bundle is corrupt, not an
  alternate image.
- **passes need mirrors.**  `_PASS_PY` mirrors term-level pass
  applications (`peephole` = the single `PEEPHOLE_PASS`, not the
  fixpoint); an unmirrored pass refuses at bake.

## Evidence (gate 24)

- Replay **byte-identical** to `emit_native` — 3584 B.
- All six stage rows `pir-stream`; MAP rows at pack positions
  47/48/49 = idata, datab, .text — the recipe as wire data.
- Forges refuse: MAP src frame out of range; dep-closure stage
  without a stream; fuse_s program stream in a default bundle
  (audit).
- `pack_staged == python_pack` (2048 B mini) through the shared
  recipe; `slice_ir` digests preserved.

## Honest boundary

- Python's residue is now: spawn subprocesses, concat frames,
  write the file, compare bytes — mechanical, not semantic.
- Dep edges are *executed* in topo order but scheduling is still
  serial; `workers=N` parallel execution is now purely a
  scheduling question (deps declared).
- Kernel-side DAG execution — the emitted host reading the DAG
  itself — remains the interpreted contract (G9 territory), a
  separate output.  Compiled vs interpreted stays split.
