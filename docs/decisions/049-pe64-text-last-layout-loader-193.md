# 049 — pe64 layout: .text last, computed section RVAs (CreateProcess 193 fix)

## Status

implemented — `target_pe64.py` (layout/symbols/pack), `spec_term.py`
(idata/data/syms/link/pack term sources), `emit_chain.py` (pack_staged
mirror, emit_image text_base), `seed.py`, `opt_peephole.py`,
`target_elf64.py`/`target_c.py` (uniform `text_rva` interface).

## Defect

`native.x86_64.pe.ir` exes with `io=("stdin","bytes")` failed
CreateProcess with WinError 193 (STATUS_INVALID_IMAGE_FORMAT) while
`LoadLibraryEx` mapped them fine.  Root cause was structural, not
code: the old fixed-slot layout `.text`@0x1000 / `.idata`@0x2000 /
`.data`@0x3000 overlapped whenever `.text` VirtualSize exceeded its
4 KiB slot (redirect+bytes kernel = 0x12b6 → spans 0x1000–0x22b6,
colliding with `.idata`@0x2000).

## Constraint discovered (empirical, bisected)

Windows requires the first section to begin at VA = SectionAlignment
(0x1000) — contiguous coverage right after the headers.  Simply moving
`.text` last and leaving a hole at [0x1000,0x2000) is ALSO rejected;
section-header order alone does not matter.  `.text` bytes are fully
position-independent (every label/symbol ref encodes rel32), so it may
go last — but the sections must tile from 0x1000 with no gaps.

## New layout

```
.idata @ 0x1000                              (fixed)
.data  @ align4096(0x1000 + len(idata))      (= 0x2000 for sane tables)
.text  @ align4096(drva + len(data))         — last, unbounded
```

`build_data`/`symbols` take the computed `drva`; `Target.text_base`
(int) becomes `Target.text_rva(imports, data_slots)` (callable) on all
targets — pe64 computes it, elf64/c return constants.  Term side:
`dataOf`/`symbolsOf` take `drva` as an argument; `linkOf`/`packOf`
derive it in-stage via `ALIGN4096 (B4ADD 0x1000 (LENB4 idata))`;
`pack2Of` derives `trva` the same way.  `_pack_body` emits headers and
raw sections in VA order (.idata, .data, .text).

## Verified

- `reclaim=redirect` + `io=stdout` and `io=bytes` exes: load + run
  (bytes mode frames `[u32le len][bytes]` correctly; exit5 on non-list
  NF as specified).
- `emit_mini_image` staged == `_mini_oracle` direct — byte-identical
  image under the new layout.
- TinyLisp suite `--exe --workers 4`: 125/125 through the new-layout
  IR exe (canonical packed-IR path).

## Why not alternatives

- Bigger fixed slots (.idata@0x8000): same file churn, same cap —
  arbitrary bound, eventually wrong again.
- `.text` first + post-assemble relocation (`assemble_obj` exists):
  adds a reloc-apply stage to BOTH emitters for a 3-section image —
  over-engineered; .text-last is the standard linker answer.

## Follow-up: staged-chain scope (the `False` result was harness misuse)

The first real-scale staged emit reported `staged==direct: False` —
not a layout defect.  `programOf` is generated from
`routines_x86_64_win64.ROUTINES` with sentinels varying only
`fuse_s`/`fuel` — **reclaim/io/audit are baked at generation time**.
The staged chain can only emit the term-mode `.lo` kernel
(io=stdout, reclaim=none); an `R` outside that envelope used to be
silently downgraded to the default program while `emit_native`
correctly produced the IR kernel — structurally impossible to match.

`emit_image` now raises `NotRealized` for non-default fields outside
the parameterized set {fs, fuel, rbb, cb, nb, stack_reserve,
peephole} — a realization downgrade must be loud, not silent.

Real-scale spot-checks that DID pass under the new layout:
`pack_staged` == `python_pack` on the real redirect kernel's
sections (4608B term-mode image).  Full-chain real-scale byte
equality is re-running against the correct oracle
(`emit_image(Realization())` vs `emit_native()`).

Open item: staging the IR kernel (bytes-ingress, reclaim=redirect)
needs `programOf` regenerated with additional splice axes (io,
reclaim) or a per-routines-record program generator — currently the
generated program term is bound to the `.lo` ROUTINES set.

## Real-scale byte-equality: PASSED

`emit_image(Realization())` == `emit_native()` — **byte-identical
3584B** PE image through the full staged chain (program→link→
assemble*→pack*), with the byte-egress kernel on the decomposed
seams: `assemble*` 553 encodes in 35.2s and `pack*` in 5.1s on the
exe worker pool (vs 5107s/39.7s on graph.lo — ~145x).  program/link
stage artifacts checkpointed under `emit_work/real/`.  The earlier
`False` was the IR-realization harness mismatch described above.
