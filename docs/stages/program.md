---
type: stage
id: emit.program
provenance: emit_chain.emit_schedule_streams / _schedule_items;
  gates 13, 19, 21, 24
ts: 2026-10-08
tags: [phase8, emit, stage, program]
---
# emit.program — the emitted program as boundary data

**What it is.** The itemization of the kernel image's routine
fragments, emitted as a term-egress stream: one `routineOf name
fixed` query per routine in the composed leg order, on a
term-egress kernel. Each frame decodes (`decode_frag`) to the
routine's emitted items — instruction records, label markers,
data-slot contributions.

**Term signature.** `routineOf(name, fixed, ir_ctx) -> frag NF`.
The seed-side mirror is `_schedule_items`: raw `_BUILDERS[name]`
items with `routine_expr`'s fs-gating (`st_s`/`build_ds` only
under their fuse_s conditions) and per-frag pass chains. The
two views are deliberately different quotients: the term carries
raw builder output; `_emit_parts` is the post-`_mt_xform`
emitted view.

**Consumers.** `emit.assemble`'s dep edge — the program stream
enumerates what assemble must encode (audit: non-label item
count == assemble root count). Provenance, not computation:
the baked assemble stream is self-sufficient; the program stream
is the correspondence witness.

**Checkpoint key.** `routine_pin_key(name, fixed, ir_ctx)` —
content-addressed by the routine's term, its fixed constants,
and the IR-context flag. Per-routine invalidation (gate 2) rides
this: a changed routine re-pins only its own key.

**Evidence.** frags concat == monolithic (gate 1), per-routine
invalidation (2), identity chain transparency (4), program/
assemble stream audit at replay (24).
