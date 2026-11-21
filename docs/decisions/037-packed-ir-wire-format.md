# 037 — Packed IR: canonical binary term serialization

Full spec in `docs/adr/0005-packed-ir-node-format.md` (committed
`bf8d71e`); `pack_ir`/`unpack_ir` live in `host/spec_term.py`.

## Why it exists

Python was a *runtime* dependency on every stage seam — token-stream
marshal (`bc_decompile`/`_parse_native_out`) cost ~4.5s per encodeOf
query, ~80% of the win64 assemble wall.  Packed IR is the seam's real
format: flat `(tag u8 | l u32 | r u32)` node records, postorder
(children < parents — single-pass load), hash-consed on `(tag,l,r)`,
tag byte = `seed.Tag` numbering (the emitted kernel's own), multi-root
header, `VAR=0xFE` for probes.

## Measured (encodeOf query, win64-class term)

- token marshal: 1.31MB / 4.5s (spawn+parse extra)
- pack_ir: 143KB / 0.43s · unpack_ir: 16ms
- → ~10× smaller, ~10× faster produce, ~280× faster consume

## Properties that matter downstream

- **Canonical**: equal NFs → identical bytes → content-addressable.
  The Merkle/package layer (research note `typed-ir-packages-trm-…`)
  sits directly on this.
- **Sharing survives** `export_tree`'s unsharing — dedup is
  structural, not identity-based.
- **Native consumer is trivial**: depacker ≈ `arena[i] = mk(tag,l,r)`
  — ~50 lines replacing the exe's stdin token parser.
- The `.plex` wire container and bytechunk rule are a different layer
  (artifact envelope / byte-payload encoding) — packed IR is the term
  payload that goes inside, not a competitor.

## What it does NOT fix

The naive reducer's O(term)-per-step copying (72GB `LENB4`) is an
evaluator problem — marshal-free.  Levers: native sharing arena or
Futamura-2 specialization.  Separate axis.

## Landed (a8e47a4)

The native consumer is done — `routines_x86_64_win64` carries a second
record `X86_64_WIN64_IR` (toolchain `native.x86_64.pe.ir`, dialect
`packed.ir` — all declared in toolchain.json): depack is one forward
pass (node i at base+i*24, index→pointer is arithmetic), the heap is a
reserved commit-ahead arena with `VirtualFree MEM_DECOMMIT` between
roots (batch peak = largest query, not the sum), fuel is per-root,
`steps=`/`alloc=` are batch totals.  Verified: SKKI -> I in 10 steps /
59 allocs — identical to the token kernel; win64 emit_chain byte-exact
with assemble* on the IR seam (263s vs ~2000s token marshal).

Two real bugs the first run flushed out: duplicate labels silently
resolved (depack's `ir_rloop` collided with reduce's — assembler now
raises on dups), and `build_ds` clobbers r13/r14/r15 (recovered by
recompute, not push).  ISA gained `mov_r32_m32` for u32 zero-extend
loads (the `and rax,0xFFFFFFFF` idiom does NOT mask — imm32
sign-extends).

## Stream-of-streams + pool + Merkle keys (0cfe6d9)

The wire is now **concatenated self-describing stream elements**, not
one blob: kernel loops `16B header (read-exactly) → 4nr+9nn body →
depack → per-root reduce → release region → next`.  Per-stream region
holds `[root idx | records | cells | root ptrs]`; the derived-S
template moved to a permanent entry-built region (survives per-root
arena resets AND per-stream frees).  Pipe EOF is ReadFile-FALSE/
ERROR_BROKEN_PIPE — clean at a stream boundary, exit3 mid-element.

`pack_ir` rewritten iterative (id-memo + structural memo): the 243-
query union pack went **105.9s → 0.3s** — the recursive walk was the
real marshal residue.  `pack_ir_keyed` adds per-root **Merkle
digests** in the same walk (`h = sha256(tag‖h(l)‖h(r))`,
position-independent = canonical content key in any graph) — that is
the memo/package-layer primitive.

`make_ir_runner(workers, cache_dir)`: one keyed walk → cache hits by
digest (`emit_work/nf_cache`) → misses repack into strided per-worker
multi-root streams → N exes concurrently.  `ISAR_AUDIT=1` prints
roots/hits/misses/workers/pack_s/wire/exe_s/pool_wall/steps/wall per
batch — the always-on counters.

**Measured win64**: 3584B byte-exact; assemble* 643 encodes = 157s
summed exe work → **16.6s pool wall** (~9.5×/12), stage 38s; pack*
rides the IR seam too.  Runner is built per-realization (fuse_s legs
must use the fuse_s kernel — a hidden bug the checkpoints masked).

Bugs flushed: r12 was both the header granule and the reduce-root
register (stream 2+ wrote headers into live term cells → moved to
`irhdr` slot); pipe EOF-as-FALSE was misread as malformed.

## Next

Audit counters at IR granularity → per-rule redex histogram variant
for the CUDA-sizing baseline → asm/fasmg emit dialect (third
syntactic witness) → CUDA grid consumer of the same stream unit →
Futamura-2 specialization → .o/debug-sym emission.  IR checkpoints in
emit_work (terms, not pickles) still open.
