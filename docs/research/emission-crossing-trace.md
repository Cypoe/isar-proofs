# Emission-path trace — where Python is the semantic bus

Counted crossings in one complete emission (`native.x86_64.pe.ir`,
`reclaim=redirect`, `io=("stdin","bytes")`), direct vs staged.

## Direct path — `seed.emit(R, tc)`

```
resolve tc          Python: toolchain record -> modules (catalog lookup — OK, metadata)
rts.program(R)      Python builds Program items (insn list) — SEMANTIC (construction)
tgt.symbols(...)    Python builds {name: rva} table — SEMANTIC (layout values)
isa.assemble(...)   Python encodes machine code, rel32 resolution — SEMANTIC (the ISA map)
tgt.pack(...)       Python builds PE headers/sections — SEMANTIC (container layout)
```

Every stage is a Python semantic constructor.  This is the oracle path
the staged chain gates against byte-for-byte.

## Staged path — `emit_image(R)`

```
program_query(R)    R -> term (marshalling: ints/strings -> terms — ingress, OK)
programOf reduce    term-level; nf -> decode_program -> items (Python decode at seam)
link_query(im,sl)   imports/slots -> terms (ingress); linkOf reduce ->
                    decode_link -> (idata, datab, syms) (Python decode at seam)
assemble_staged     per-insn encodeOf terms, Python fold bookkeeping
                    (pos/loc cursors) — boundary glue, each reduction small
pack_staged/pack2   chunk lets via term reductions; Python joins bytes
```

## The semantic-bus crossings (Python constructs values mid-pipeline)

1. `decode_program` / `decode_link` / `decode_symbols` /
   `_decode_bytecells` — NF → Python objects between stages.  This is
   the bus: stage N's NF is decoded by Python, re-encoded for stage N+1.
2. `assemble_staged` — per-insn `encodeOf` queries; Python carries the
   fold state (pos/loc/symtab lookups) between item reductions.
3. `pack_staged` — Python mirrors `_pack_body`'s chunk list and drives
   each derived chunk (aligns, adds, zerofills) as a tiny reduction.
4. `seed.emit` wholesale — the reference implementation itself.

The already-encoded handoffs that exist today: `pack_ir_keyed` blobs
(to the exe), `[u32le len][bytes]` frames out of `io=bytes`, and the
`emit_work` checkpoint files (content-keyed stage artifacts on disk —
literal persisted seams).

## What "no Python between stages" needs next

- A consumer that reads `pack_ir` / `[len][bytes]` frames directly —
  the emitted host (exe) already does this for the *batch* seam
  (proven: `io=bytes` kernel after the 049 layout fix).
- Stage chaining inside one host: link's `(idata, datab, syms)` NF must
  feed assemble without a Python decode.  `assemble_query_t` +
  `pack2_query_t` already take terms — the non-decomposed staged path
  at spec_term.py:~713-726 composes in term space; the decomposed path
  is where Python re-enters (it's the throughput workaround for
  monolithic folds, documented in 048).
- `symbolsOf`/`dataOf`/`idataOf`/`linkOf`/`packOf`/`pack2Of` now take
  layout params (`drva`) as term arguments — the quotient-map data is
  explicit in the term, not in Python constants.
```

## Correction note (049 follow-up)

The real-scale staged run that reported `staged==direct: False` was
a harness mismatch, not a layout or stage defect: `programOf` is
generated from `routines_x86_64_win64.ROUTINES` at sentinel
defaults, parameterizing only `fuse_s/fuel/rbb/cb/nb`.  It cannot
emit the IR kernel (io=bytes, reclaim=redirect) — the staged chain
degraded the realization silently while `emit_native` produced the
correct IR image.  `emit_image` now raises `NotRealized` for
non-default fields outside the parameterized envelope; the
real-scale byte-equality re-run uses `Realization()` on both sides.

Scope boundary this exposes: the generated program term is bound to
the `.lo` ROUTINES set.  Staging the IR kernel requires either
additional splice axes in `program_expr` (io, reclaim) or a
programOf generated per routines record.
