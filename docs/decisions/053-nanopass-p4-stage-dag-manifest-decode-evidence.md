# 053 — nanopass phase 4: stage-DAG manifest + decode evidence + emit_ir

## Status

implemented (4a manifest + replay, 4b decode instrumentation,
4c `emit_ir` kernel egress, 4d link-seam blob cutover).

`emit_image(workdir=..., decompose_asm=True)` now writes
`manifest.json` beside the artifacts: `plex.stage-manifest/1`
records every stage as data — content-keyed artifact name, the
resolved runner label, dep edges, and per-stage query blob refs
(`blobs/b<tok>.ir` + root digest).  `replay_emit(workdir)` resolves
the image purely by addressing: missing artifact →
`NotRealized` (emit, don't replay).  Verified on the real emit
(`emit_work/p3c`): 30 stages, replay byte-identical
(`bacc6505`).

## Pin-ownership fix (phase-3b, commit 0f710fb)

`pins[id(t)]` did not own `t`.  `digest_of` built throwaway query
terms for keying and dropped them; CPython reused the freed
addresses, so unrelated later terms could false-positive a pin and
splice a wrong blob into a packed stream — observed first as 26
resolver-miss bytes (rel32 = `-end`), then as pass-1 exe OOM
(rc=4) at single-root depth on a cold emit.  Pin entries now hold
the term.  Cold emit after the fix: byte-identical, ~460s; warm:
**1.4s** (digest sidecars skip all term rebuilds; 10.7s before).

## decode evidence (4b)

`_DECODE_COUNT` + `_decode(kind, fn, *a)` wrap the remaining
Python semantic crossings on the emit path: `frag` (program.*
NFs → item lists), `bytesyms` (link sections), `program`
(peephole path), `bytecells` (monolithic pack NF).  The manifest
records the per-emit delta.  Under `exe_default` + byte-egress
kernels `bytecells` is already 0 — the kernel decodes its own
byte-list NF; the others wait on `emit_ir`.

## Runner identity

Runners carry `.kind`/`.exe`: `exe.term:<file>` (packed-IR kernel),
`exe.bytes:<file>` (byte-egress kernel), `graph.lo` (oracle).  The
manifest's runner field is provenance — replay re-enters
`emit_image`, which re-resolves runners by name; the label says
*who* served the stage, not a dispatch handle.

## 4c — `emit_ir` kernel egress (landed)

`io=("stdin","ir")` is the third IR realization axis.  The kernel's
`r_ir_reduce` egress tail dispatches on `R.io[1]`: `emit_ir` walks
each reduced root and writes one `[u32le len][PIR blob]` frame —
the stage's output is already the next stage's packed input, no
term rebuild in between.

**Dedup is identity, not structural — deliberately.**  The earlier
draft required a `(tag,l,r)` hash-cons table to match Python's
canonical stream byte-for-byte.  Wrong constraint: Merkle digests
fold child *digests*, not stream positions, so a blob that keeps
duplicate equal subtrees still computes the canonical root digest.
`spec_term.digest_ir_blob` proves it — one linear pass over records
yields the same keys `pack_ir_keyed` mints.  Identity dedup is a
cell-number table (`ei_tab[(node-irarena)/24] = idx+1`, 8B slots in
a fresh zeroed VirtualAlloc per root — arena cell reuse across roots
makes per-root zeroing *required*).  What it costs: spliced-in blobs
can't dedup INTO each other, so kernel streams can be larger than
canonical; byte size is free, content key is fixed.

**Walk order** matches `_pack_ir_all`'s postorder left-then-right;
record emission composes `<BII` as tag byte + one qword store
`li | ri<<32` (the ISA has no dword register store — qword writes
with clean zero-extension do the pair atomically).  FWD cells are
`repr`-resolved per visit under redirect reclaim; tags outside
0..6 (STK/FWD/EG_MARK/junk) refuse rc=3.  Buffer bound is exact:
emitted nodes ≤ reachable cells ≤ `(rbp-irarena)/24` — no
`count_nodes` pre-pass needed.

Wire: per-root blob = `PIR\0 | v1 | nn | nr=1 | root_idx | records`.
`make_blob_runner` (emit_chain) mirrors the bytes runner — same
frame parser, frames validated through `digest_ir_blob`, runner
kind `exe.ir`.  Verified: 4-root batch round-trips, each blob
re-emits the identical NF line through the stdout kernel, digests
match canonical re-pack; truncated/garbage streams refuse.

## 4d — link seam cutover (last decode_* crossing)

`BlobStore.blob_term(blob)` registers a *byte-side* blob under a
placeholder `T(VAR)` — pin entry carries the blob's own node bytes
+ canonical root digest (`st.blob_pin_entry`); the placeholder is a
VAR leaf so an unpinned pack emits a var record the depacker maps
to a hole — loud failure, never silent splice.  Registered pins are
seen by every runner holding `store.pins`.

`link_staged` blob mode (run_ir + run_bytes + store present):
section queries run on the ir-egress kernel → `pair(bytes,syms)`
blobs → placeholders; section BYTES are kernel projections
`(ph KK)` on the byte-egress kernel (its emit_bytes decodes the
byte-list NF natively); the merged symtab is a kernel APPEND over
`(ph _KI)` projections emitted as another blob.  `link.sections`
checkpoints `(idata, datab, symtab_blob)`; `assemble_staged`
re-registers the blob via `blob_term` — content identity survives
checkpoint round-trips, no term is ever built at the seam.

Measured on the production emit (p4_blob_rb): image 6656B
`bacc6505f91d01f2` oracle-identical, `bytesyms: 0`, warm resume
3.0s.  The kernel-emitted symtab NF is *shape*-different from
`symtab_term`'s canonical build (LO leaves pair applications
unreduced in argument positions) but observationally identical —
resolver probes (rel hit, rip sym, miss → 0-end) byte-match.

**Decode taxonomy** (what the counters actually measure):
`bytesyms`/`bytecells` were *value* crossings — data shipped
through Python.  Both are now 0 on the exe path.  `frag`/`program`
are *enumeration* crossings — the items list shapes the per-insn
query DAG (checkpoint granularity, bounded batches); eliminating
them requires the kernel emitting follow-on queries, which is the
self-application endpoint, not a seam fix.  26 frag decodes on a
cold emit are the honest count of DAG enumeration.

## Caveats

- `replay_emit` is *address resolution*, not stage re-execution —
  full manifest replay (stage produce() driven by recorded runner
  kinds) is the Phase-6 bundle-loader contract.
- Manifest stages cover the decompose path; the non-decompose
  fall-through has no checkpointed artifacts to name.
