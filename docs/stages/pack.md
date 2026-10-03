---
type: stage
id: emit.pack
provenance: emit_chain._pack_recipe / _pack_stream /
  pack_staged; plex_bundle KIND_MAP; gates 19, 21, 24
ts: 2026-10-08
tags: [phase8, emit, stage, pack, map]
---
# emit.pack — the container recipe as a stream + MAP rows

**What it is.** `_pack_recipe` serialized: an ordered element
list — literal header chunks, computed fields, and stage-frame
splices — realized as a `pir-stream` plus KIND_MAP rows
`(stage_idx, at_stream_idx, src_stage_idx, src_frame)`;
`0xFFFFFFFF` (`MAP_ALL`) splices every frame of a source stage.

**Term signature.** Literals ride as already-NF `bytelist_term`
queries (format constants are data, not computed answers).
Computed fields are roots: `ALIGN*`, `B4ADD`, `ZEROFILL`,
`PADLIST`, `U64` — the PE64 writer's arithmetic as bounded
kernel work. Stage elements produce no root — they are MAP
declarations the executor resolves by frame splice.

**Consumers.** `schedule.output` — the terminal stage. Its
frames + splices concat to the PE64 image. `pack_staged` (the
`emit_frames` path) shares `_pack_recipe` element-for-element:
one recipe, two realizations (staged vs serialized bundle).

**Checkpoint key.** The pack stream's BYTES span digest; MAP
rows are validated structurally before any execution (index
bounds, `at` within the stream's root count, src stage inside
the dep closure) — a malformed MAP is an invalid bundle, not a
runtime error.

**Evidence.** `pack_staged` == `python_pack` (mini 2048B, gate
19), MAP rows at positions 47/48/49 exactly (24), replay ==
emit_native (21/24), forges refuse (MAP frame OOR, missing
dep-closure stream, out-of-correspondence program stream).
