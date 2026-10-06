---
type: frag
id: 0022
provenance: host/emit_chain.py _prog_axes + freduce/gc=sweep kernels
ts: 2025-01-01
tags: [self-host, fixpoint, emit, plex.v3, gc-sweep, freduce, monolith]
---

# 0022 — monolithic emit.term self-hosts: H2 == H1 == H0 on plex.v3

## What landed

The full emit chain as ONE term — `pack2Of (assembleOf program
(linkOf ..))` — was previously the semantic oracle only: pack2's
concat-spine live set exhausted a bump arena (rc=4, >200s at mini
scale). Under `reclaim="redirect"` + `gc="sweep"` + the spine-stack
`freduce`, it now completes in-kernel and the fixpoint closes on
the emitted binary itself:

```
seed.py        -> H0  (9728B IR kernel: plex.v3+bytes+redirect+sweep,
                       arena 4GB, persist 1GB)
H0 < emit.plex -> H1  byte-identical  (89.4s, 575,515,425 steps,
                                       27 collections)
H1 < emit.plex -> H2  byte-identical  (90.3s, identical step count)
```

The bundle is specs-as-data: plex.v3 ingest validates the archive
natively, KIND_PIR carries emit.term, freduce normalizes it to the
image bytelist, bytes egress emits the frame. Python's residue is
spawn + one frame parse + file write — the documented residue of
`run_emit_bundle`, now reduced to one invocation and no splice
(the monolith IS the splice).

## Bug found: `dialect` was missing from `fixed`

`_emit_layout`/`pack_emit_program`/`emit_image` shared a
`_prog_axes` exclusion set containing `dialect` — but dialect is a
*builder-generation* axis (`ir_read`/`ir_sloop` emit `plexleft`
clamp/dec only under plex.v3), not a λ-bound or pack-time axis.
Result: `routine_expr` rebuilt ingest routines with `_R_SENT`'s
`"pir"` — emit.term could never emit a plex.v3 kernel (a 6593-byte
.text divergence: the missing clamp code shifted every following
rel32). Latent because no fixpoint had been attempted on a plex
record. Fix: `dialect` moved into `fixed` at all three sites; the
staged path was unaffected (it uses the real R via
`_schedule_items`) — and emit.program's decode-audit would have
caught the mismatch had a plex record gone staged.

## Honest edges

- The 9728B-record monolith needs ~4GB arena + 1GB persist to
  complete — the staged schedule remains the tight-arena and MT
  path (gc=sweep refuses threads>1; the schedule strides chunks
  across workers).
- `steps=` counts identical between H0's and H1's runs —
  observational equivalence on the emitted program, not just
  bit-parity.
- 90s self-emit is the number to beat; it's bounded by eval
  throughput on a single thread — the staged schedule is where
  MT enters (coarse frames), and kernel-side schedule execution
  (a `plex.emit/2` dialect leg) is where spawn/splice residue
  would leave Python entirely.
- gates: emit frames / self-hosting fixpoint / emit.plex replay /
  emit schedule all PASS — the dialect pin is a no-op for pir
  records.
