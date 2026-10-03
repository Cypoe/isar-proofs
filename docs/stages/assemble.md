---
type: stage
id: emit.assemble
provenance: emit_chain._assemble_stream / assemble_staged;
  spec_term.encode_query; gates 19, 21, 24
ts: 2026-10-08
tags: [phase8, emit, stage, assemble]
---
# emit.assemble — one encodeOf root per prep position

**What it is.** Since Phase 8b, a baked `pir-stream`: one
`encodeOf item resv` root per non-label prep position, in
program order. The output frames concatenate directly to
`.text` — no pass-2 replay, no fixup bookkeeping at consume
time.

**Term signature.** `encodeOf(item, resv) -> bytes NF` on a
bytes-egress kernel. `resv` is the resolution closure baked
seed-side: merged symtab, the local label map (`loc`), `end4`
(end-relative base). Rel-sensitive items carry their closed
query; plain items encode without one. The shape mirrors
`assemble_staged`'s pass-2 resolver exactly — same `_resvmk`
construction, two realizations (live two-pass vs baked stream).

**Consumers.** `emit.pack` — MAP row `(pack, 49, assemble,
MAP_ALL)` splices all frames as `.text`. The bundle executor's
audit cross-checks its root count against the program stage's
non-label items.

**Checkpoint key.** Stream digest (`emit_bundle_streams`
extracts each stream by digest-referenced BYTES span). Within
the stream, `slice_ir` root ranges are the scheduling unit —
the bump arena accumulates across roots, so a large stream
executes in halved chunks rather than one call (rc=4 boundary).

**Evidence.** replay byte-identical (21/24), MAP position and
full splice (24), program/assemble root-count audit (24),
corruption forge refusal (21).
