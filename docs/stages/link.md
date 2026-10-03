---
type: stage
id: emit.link
provenance: emit_chain.link_staged / BlobStore; gates 12, 16,
  19, 21, 24
ts: 2026-10-08
tags: [phase8, emit, stage, link, blob-seam]
---
# emit.link — section byte projections + merged symtab

**What it is.** The linker stage split in two artifacts: section
builders run once and export their NF byte projections (`ib`
imports block, `db` data block); the symtab they each produce is
merged kernel-side (`APPEND iat data` = last-match dict order)
and leaves the kernel as an **ir-egress PIR blob** — Python
receives an opaque blob and a digest, never a decoded table.

**Term signature.** Section NF bytes are bytelist roots on a
bytes-egress kernel. The merged symtab is a `symbolsOf`-style
join evaluated on the ir kernel; the seam's contract is
`digest_ir_blob` — Merkle root equality, not structural
re-decode.

**Consumers.** `emit.assemble` needs the merged symtab to close
rel items (the resv closure baked into each encode root);
`emit.pack` splices `ib`/`db` frames verbatim via MAP rows
at positions 47/48. `emit.symtab` is a separate stage row —
the blob travels as its own artifact.

**Checkpoint key.** The blob store (`BlobStore`) pins stream
blobs by content digest — `pack_ir_keyed` Merkle roots; the
store's `pin_named` registers named artifacts (per-routine
pins, the merged symtab blob) so later stages splice by
reference.

**Evidence.** split-link == dict join (gate 12), link blob
seam == dict join incl. miss paths (16), blob-store disk
round-trip (11), MAP splice positions (24).
