# 052 — nanopass phase 3: content-addressed blobs + split link + exe-shaped emit

## Status

implemented — `spec_term.py` (`_pack_ir_all` blob splice,
`pin_term`/`unpack_ir_pin`, `_STAGE_TERMS` memoized stage constants
`link_term`/`idata_term`/`data_term`/`pack2_term`,
`routine_pin_key`/`const_pin_key`/`program_pin_key`),
`emit_chain.py` (`BlobStore`, `link_staged`, `_batch_bounded`
module-level, `exe_default`, lazy pinning), `gates_nanopass.py`
(12 gates, all green).

End-to-end: `emit_image(Rb, workdir=p3_ir, rt=X86_64_WIN64_IR,
exe_default=True)` → **6656B, byte-identical** to
`emit_native("native.x86_64.pe.ir", R=Rb)` (sha bacc6505f91d01f2).
Every stage ran on the emitted kernels; graph.lo was not touched.
Warm emit (all checkpoints hit): **10.7s**.

## Model

The stage blobs are content-addressed data, not recomputed text:

- `BlobStore(dir)` — named pins land at `b<sha256(key)>.ir` +
  `.meta` (full canonical digest, provenance key, timestamp).  A
  second process reloading the blob registers a splice entry whose
  packed stream is digest-identical — cross-process reuse verified.
- `pin_term(t, pins)` — serializes a term once, returns the raw
  Merkle root digest; `pack_ir`/`pack_ir_keyed` splice the stored
  blob verbatim at any node whose `id()` is pinned.  Digests are
  position-independent, so a spliced stream's Merkle keys equal the
  unpinned walk's — checkpoint compatibility holds by construction.
- Pins are a pure performance overlay — registered lazily inside
  miss paths only (`program.<name>` misses pin their routine,
  `link_staged` pins idata/data terms, monolithic pack pins
  `pack2`).  A fully-checkpointed warm emit never builds a constant
  it won't pack — `bracket(pack2_src)` alone is ~22s and was being
  paid per emit.

## link split

`linkOf` → `idataOf IMPORTS` + `dataOf drva SLOTS` as two term
queries in ONE batch stream; `drva = ALIGN4096(0x1000 + |idata|)`
is computable at the seam (`target_pe64.data_rva` — the same
oracle builder; boundary arithmetic, same class as text_base).
The symtab merge is the seam dict-join mirroring linkOf's
`APPEND iat_syms data_syms`.  Gate: `link_staged` == `decode_link`
at mini scale, and byte-equal at production scale (249B+360B,
44 syms).  Measured: 81s cold on `_rs.exe` vs 202s monolithic —
and 6.3s when the `nf_terms` digest cache hits.

## exe_default — runner selection as data

`emit_image(..., exe_default=True)` routes byte seams to the emitted
redirect+bytes kernel (`_rb.exe` pool) and term-NF seams to the
packed-IR kernel (`_rs.exe`), both splice-aware via the store.
Explicit `stage_runs`/`bytes_run`/`term_run` still win per stage.
`decompose_pack` gained a `None` sentinel resolving True under
exe_default — the monolithic pack2 query on a single kernel process
crawls (concat-heavy live set, >4min observed) while the chunked
pack* seam does the same emit in ~5s on the pool.  `rt=` or a
non-baked `routines` selection now auto-enables `decompose_asm` —
the record IS the staged-path intent; `passes` still requires it
explicitly.

## Found and fixed

- `pack2_query_t`/`linkasm_query` re-bracketed 1.3MB sources on
  every call (~22s each, fresh T objects defeat hash-consing) —
  now memoized in `_STAGE_TERMS`.
- `_rebase_ir_nodes` wrote through a read-only `np.frombuffer`
  view — `.copy()`.
- Node indices after a splice must come from the serialized node
  count (`len(digs)`), not the hash-cons memo — a pinned blob
  inserts 0 memo entries but n stream nodes; `len(memo)` minted
  indices that lagged the stream and corrupted parents.
- Oracle call discipline: `emit_native` defaults to `Realization()`
  — `native.x86_64.pe.ir` with default R emits the *stdout* variant
  (4608B); the redirect+bytes oracle needs `R=Rb` (6656B).  The io
  axis lives in the routine list via `names_for`, so the realization
  is part of the oracle identity.

## Numbers (IR emit, workdir=p3_ir, exe_default)

| stage | host | cold | cached |
|---|---|---|---|
| program.* × 26 | `_rs.exe` 1 batch | 182s (367K steps) | ckpt |
| link* (idata+data) | `_rs.exe` 1 batch | 81s | 6.3s (nf_terms) |
| assemble* 478+884 | `_rb.exe` pool | ~55s | ckpt |
| pack* 6656B | `_rb.exe` pool | ~5s | ckpt |
| warm emit | — | — | **10.7s** |

Warm cost is now `_ck_keys` itself — 26 keyed `routine_query`
packs (~0.2s each) guarding builder-side ambient-state drift.
That's the honest trade: term-digest keying catches a builder
reading mutable globals; a pure source-hash would not.

## Caveats

- Spliced blobs can't dedup INTO the query spine — packed bytes can
  grow slightly; the win is the skipped walk, not wire size.
- Persist-zone sharing (Phase 3c) was verified already-real rather
  than built: the redirect kernel's `[permend, irstart)` zone pays
  a shared input subtree's collapse once per stream by design.
- The `nf_terms`/`nf_bytes` runner caches key on packed digests —
  they observe phase-3 blobs natively.  Next: the `.plex` v3 bundle
  wraps these artifacts with the ADR-0006 role sections.
