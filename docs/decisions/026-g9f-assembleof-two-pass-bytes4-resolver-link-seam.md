# 026 — G9f: encodeOf + assembleOf; bytes4 arithmetic; the resolver IS the link seam

Status: landed, suite-green (post-`f67c8d7`). Emit stage 4 of
`resolve → program → assemble → pack`.  `isa.encode` and
`isa.assemble` now exist as term-level `ENCODE`/`_ASSEMBLE` in
`host/spec_term.py`; `spec_term.py` is fully green (14 pathOf + 14
resolveOf + 2 symbolsOf + 5 programOf + 6 encodeOf + 2 assembleOf + 14
residual × 4 witnesses).

## encodeOf — the ENCS table as data, not code

`isa.encode` is lifted as a *field-spec interpreter*: ENCS is encoded
as a static nibble-trie (name → list of (fieldop, args) records), REG
the same (name → (code, needREX)).  `interpret` walks the seven field
ops (`op`, `oprd`, `rex`, `modrm`, `sib`, `disp`, `imm`) and three
predicates (`i8`, `i32`, `m64`) over operand tags — the encoding
decisions stay *data*, observed from the table, never re-encoded
procedures.  Verified on a 26-instance sweep covering every field-shape
class (reg-reg, disp0/8/32, SIB, rbp/r12 edge cases, rip-relative,
imm8/32/64, oprd, group-ext, byte regs, rel32) — all exact vs
`isa.encode`.

## assembleOf — two passes, one resolver

`ASM ENC ZRV prog sym base` over `programOf`'s fragment list:

- **Pass 1** folds fragments→items accumulating `(pos4, localmap,
  prep_rev)`; labels record `base+pos`, insns encode with the zero
  resolver `ZRV` for *length only* (rel32 is always 4 bytes whatever
  the value — the honest use of the encode nibble-length).
- **Pass 2** folds prepared `(item, off4, len4)` records; `end4 =
  base+off+len`; `resv nm = sym[nm] | loc[nm] | (0−end4)`, then re-encodes
  with the real resolver and conses emitted bytes.
- Result `pair(bytes, localmap)`.

**The resolver is the link seam**: `symbols` (injected assoc map,
from `symbolsOf` now, from a real linker over objects later) shadows
`local` — exactly `isa.assemble`'s `symbols.get(n, local.get(n,0))`.
A proper linker phase only produces richer symbol tables; assemble's
signature doesn't change.

## bytes4 — the arithmetic representation

Addresses/positions/displacements are **4 byte-cell lists** (u32,
little-endian, carry-out discarded = mod 2³²): `B4ADD`/`B4SUB` are
constant-width ripple ops over the verified `ADDBC` byte adder.
Numeral subtraction would be O(n·m) through PRED chains — fatal for
the ~157 rel/sym operands in the real routines.  This forced the G9d
`symbolsOf` rep change: symbol values are subtracted by the resolver,
so per the recorded boundary rule ("is it ever added/subtracted →
bytes") they are bytes4, not Church numerals.

## The bug that looked like a reducer pathology

Days of "graph explosion" (34M allocs on a single `ret`, dead-code
suspicion, freeze/path-copying analysis of `_step_body`) traced to a
**parse-level mis-grouping**, not a semantics or runtime bug:

    is_lbl label_case insn_case        — WRONG
    is_lbl (label_case) (insn_case)    — right

Both case bodies are *applications* (`label_case` = `acc (\p0.\r0.…)`,
`insn_case` = `(\enc.M) (ENC it ZRV)`).  Bare in the bool spine they
split into separate tokens: `is_lbl` got `acc`, the `(\p0.\r0.…)`
lambda, and `(\enc.M)` as three args, with `ENC it ZRV` applied to the
mis-selected lambda — feeding a combinator term into `B4ADD` as a
"list", which the ripple fold destructures forever into garbage.  Same
fix in `emitstep`'s `is_lbl acc (insn_emit)`.

Lesson, symmetric to 025's shape-determines-order: **in a
combinator-syntax DSL, an unparenthesized application in argument
position is silent semantic corruption, not a syntax error** — it
parses, selects the wrong spine, and the failure surfaces as apparent
non-termination deep in innocent machinery.  Bisection by alloc-rate
trajectory (chunks of 2k steps) located it faster than any amount of
NF inspection at exploded sizes.

## Evidence

- `[[ret]]` → `c3`, `{}` — 31k steps.
- `[[label top, call_rel32 bot, ret, label bot, ret]]` @0x1000 →
  `e801000000c3c3`, `{top:4096, bot:4102}` — 350k steps, 57s.
- **mini gate** (10 items/2 frags: fwd+bwd rel32, rip-sym, mem disp8,
  `mid` shadowed by symbol 0x7777, base 0x1000) →
  `e872670000554889e5488b0538220000488b5c2408e8e6ffffff488b0d566700005dc3`,
  `{start:4096, mid:4105}` — 1.22M steps, 132M allocs, ~28GB, ~430s.
  All exact vs `isa.assemble`.

## Caps discipline

`run_native`/`run_elf`/`reduce_native`/`_reduce_via` take a `timeout`
parameter — a wall-clock **test-run** guard (default 600s), explicitly
*not* toolchain semantics; actual toolchain runs pass `None`.  The
principled bound for a real run is the realization's own fuel, never a
subprocess cap.

> **Re-check (flagged 2026-10):** the minute/second cap is a *test-only*
> device, full stop.  For any actual run the bound — *if one exists at
> all* — is a **proven fuel budget** (a step/termination measure that
> yields a proven NF in degenerate cases), never wall-clock seconds.
> The current `timeout=600` default is correct for the suite; whether a
> fuel bound should exist at all, and where, is an open item to revisit.

## What's next

`pack` — the container writer (PE64 headers, section layout, checksum)
consuming `(bytes, localmap)` + the symbol table.  Then the full chain
`resolve → program → assemble → pack` end-to-end, and the separate
linker phase that produces the symbol table `assemble` now consumes.
