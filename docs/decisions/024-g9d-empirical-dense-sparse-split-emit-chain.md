# 024 — G9d design: empirical dense-fold vs sparse-relational split for program → assemble → pack

Status: symbolsOf landed and green (isar-proofs, post-`9fe0a8e`).
Design note + implementation findings.

## What the record already said

No prior document decomposed `program → assemble → pack` into
dense-fold vs sparse-relational parts — the split was unwritten because
it was unknown.  The load-bearing pieces were on record:

- 016: chain shape `resolve → isa.assemble → target.pack`, records as data.
- 017: bounded Church folds only (Y/fixpoint diverges under cd); the
  ENCS encoder is table data (`predicates → field-ops`).
- 011/013/014: fasmg is differential byte oracle and eventual
  quotient-map *target*, never the seed's substrate.
- ARCHAEOLOGY_TOOLCHAIN §3–4: assembler re-derived as a quotient map
  over ISA signature/encoding tables; host description and program
  description both data.
- PLEX_UNIFIED_RFC :67: `Tensor → dialect emitter → byte stream → port`
  — the old-world pipeline sketch.  axiomatic_kernel_spec: the sparse
  4×4 basis + T-tensor + U-table = substrate model (that level is
  already realized — the basis IS the invariant quotient).

## The empirical split (from the real code, not speculation)

**Sparse-relational** — assoc structures, the same machinery G9c
already proved (SPECGET / EQSTR):

- `tgt.symbols` — name→RVA map (assoc + small `i*8` arithmetic)
- label map — name→addr assoc written in assemble pass 1, read pass 2
- ENCS row dispatch — ordered predicate→field-ops lookup per insn

**Dense-fold** — list construction + bounded iteration:

- `rts.program(R)` — cons-emission of a ~600-insn static list,
  R-parameterized variants (`fuse_s` selects routines).  No arithmetic;
  data + selection.
- assemble pass 1 — fold over the insn list, `pos += len(encode(insn))`
- assemble pass 2 — fold emitting bytes, `rel32 = addr − end`
- `pack` — header assembly: `_align`, field byte-packs, blob concat

**Genuinely new term-level machinery: small-numeral arithmetic only**
(`+`, `−`, `≤`, align).  Every *computed* quantity is small
(offsets/sizes/displacements ≤ ~64K — Church-feasible); every *large*
quantity (`IMAGE_BASE`, RVAs, 64-bit immediates) travels as byte-list
data — you never need `0x1122334455667788` as a magnitude, only its
little-endian byte decomposition, which is already the encoding.

## Design rules bought by the append divergence

- **Bounds must be measured from the data, never padded.**  The
  APPEND/REVONTO divergence fired at ~5+ excess nil-iterations over an
  unforced nested application.  assemble's two-pass structure sidesteps
  this *by construction*: both passes bound by the insn list itself
  (structural, exact), ENCS walk bounded by table size (exact), and the
  only numerals are measured lengths.
- Sparse-relational parts keep their assoc representation end-to-end;
  dense folds are the traversal/emission layer over them.

## Lift order (agreed direction)

1. `tgt.symbols` + `pack` header-data path — smallest new vocabulary
   (arith on small constants, byte assembly).
2. `program` — pure cons-emission, no arithmetic.
3. `assemble` — real unary `+`/`−`, hardest piece; the arithmetic
   vocabulary gets proven here.

## Why not compile fasmg through the working plex-agent dialect

- Witness collapse: fasmg is the differential byte oracle; making it
  the implementation makes byte-compare self-agreement (vacuous).
- Smuggling, precisely: fasmg's tables and macro strategy are a frozen
  compiler, not data the term walks — strategy must be a parameter.
- Seed minimality: a compiled-fasmg path drags the plex-agent VM host
  in as a runtime dependency; the seed stops being a seed.
- fasmg wasn't rejected — it was assigned its role (oracle, eventual
  quotient-map target; decision 010's "realize under observation first").

## Deferred note

When the emit chain is re-implemented "for real" (self-hosting), the
plx structure / sparse-tensor-graph model is the target machinery —
should be blazingly fast in principle, though even torch-backed
realizations carry large constant overheads.  Realistic again at that
point, not now.

## Implementation findings — numeral probing (the expensive lesson)

`symbolsOf` emits addresses as Church numerals (the boundary held:
`rel32 = addr − end` is the only arithmetic consumer; literals stay
byte-lists).  Bases are `_num_src` MUL-compositions (`16×16×16×3` =
0x3000) so the source stays small; offsets are `8 SUCC o` / `ADD o sz`
— measured bounds, no padding.  Gate: lo+native+cd on mini + real
`x86_64.win64.lo` — all exact, `nf_lo == nf_nat`, ~80s for both cases.

Decoding a computed numeral to an int was the hard part — three dead
ends and the working probe, all measured:

- **Marker-cell probe** `n (cons M) z` → n cons cells, decode by
  per-cell projection: ~10^5 allocs/cell on MUL-composed literals —
  O(n²), hit ~100GB on a 12296-valued address (native and lo alike).
  The cell construction apparently re-pays the accumulated chain.
- **App-spine probe** `n (C I M) z` → `app(·,M)^n z`: correct shape,
  but **no closed base survives n applications** — the base is
  arg-fed: `B` fires its rule at 3, `K` at 2, `I` at 1 (`KK` already
  at `KK I` = K).  Only VAR atoms are inert — and VARs can't cross to
  the native exe (`_tokens_of_term` has no VAR).
- **Per-layer subprocess probes**: `reduce_native` spawns the exe per
  call — 25k spawns for one address is not a decoder, it's a DOS.
- **Working probe**: `n VF VX` (fresh VAR args) → right spine
  `app(VF, app(VF, … VX))` — the numeral's own machinery unfolds
  inertly, count is an O(n) pointer walk, zero per-cell reduction.
  Must reduce on **graph.cd** (~24 allocs/VF): graph.lo re-descends
  the growing spine — ~quadratic allocs (384 → 83k on lo vs 8k on cd).

Same lesson as the append divergence, one level up: **the probe shape
determines the evaluation order**, and the wrong order turns an O(n)
readback into O(n²).  cd is the right order for spine-accumulating
unfolds; lo for the fold-consuming direction.
