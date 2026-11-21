# 025 — G9e: programOf at term level; per-routine fragments bound pending depth

Status: landed green (isar-proofs, post-`a606dbf`). Emit stage 3 of
`resolve → program → assemble → pack`.

## What programOf is

`routines.program(R)` at term level — one generated constant

    λfs λfuel λrbb λcb λnb. <fragment list>

over exactly the Realization fields that data-flow into the insn
stream: fuse_s (Church bool selecting variant fragments), fuel (Maybe
bytes8 — `λn.λj.n` | `λn.λj. j v`), and read_buf_bytes / chunk_bytes /
node_bytes as bytes8 immediates.  `order` is fixed by the routines
record itself (x86_64.win64.lo) and `abi` is guarded by emit() outside
program — both stay out of the minimal signature.

The skeleton is *generated*, not re-encoded: each routine builder runs
under sentinel Realizations (sentinel ints become bound vars in the
skeleton) and `difflib` regions locate the fuse_s/fuel variant spans —
the strategy stays data, observed from the real module.

## Output shape: list of routine fragments, not one flat list

The deciding empirical fact.  A single flat ~540-cell cons spine
leaves the pending emission redex at the bottom of the accumulating
structure: every lo rewrite path-copies ~all ancestors → quadratic
allocs (measured ~10M allocs by 40k steps, >16GB, native exe the
same).  Nesting the output as `Scott-list[routine → Scott-list[item]]`
— which is the honest shape anyway, since `program()` is literally
`p += builder(R, ctx)` over ROUTINES — bounds pending depth to
~routines+routine-size (~85 cells): ~80k steps / ~11M allocs on lo,
~92 rounds / ~280k allocs on cd.

Same lesson as the G9d numeral probes and the append divergence:
**probe/emission shape determines evaluation order, and the wrong
order turns O(n) work into O(n²).**  The dense-fold parts of the emit
chain need fragment boundaries wherever the emitter accumulates.

## Operand encoding (the "tighter instruction shape" answer)

Uniform tagged union `["r"|"imm"|"l"|"p"|"m", …]` — assemble decodes
by tag string, no shape-punning.  Immediates and mem displacements are
bytes8 leaves (packed little-endian, never added/subtracted — the G9d
boundary); "l"/"p" payloads stay nibble-string names — SPECGET keys
into the G9d symbol map and the assemble pass-1 label map.

## Witness matrix

lo + cd + python oracle on five Realization cases (default, fuse_s,
fuel, data-substitution, fuel+fuse) — all exact.  **Native is not
gated**: the ~80k-step reduce exceeds the exe's 600s subprocess cap
(the default exe additionally pays `translate_to_basis` on the input —
~25MB token text).  Throughput ceiling of the fixed-fuel exe, not a
correctness gap; nf_lo == nf_nat is pinned by resolveOf/symbolsOf on
smaller terms exercising the same machinery.

## What's next (superseded — all landed)

`assemble`/`pack`/`link`/`program` evaluation all landed —
`asm_eval` (51e560c), `program_eval` (bea1a4a, see 032).  Next per the
agreed order: host classification, then the C-target dialect.
