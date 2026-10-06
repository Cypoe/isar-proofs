---
type: frag
id: 0018
provenance: plexus/rel.rs + phi2/maps/assemble_x86_win64 + host/target_*
ts: 2025-01-01
tags: [cogen, emit-chain, x86, pe64, interpreter-squared, rel-rs]
---

# 0018 — real-target assemble map, clean-exit PE64, the interpreter² wall

## What landed

`phi2/maps/assemble_x86_win64.phi` (18 rels) — a pc-threaded x86-64
assembly map for the Win64 PE target:

- `assemble2<ops, pc8>` threads the program counter as an 8-nibble LE
  list on the corpus's own `nibble_add`; `call_mrip` computes
  `disp32 = symtab(sym) − (text_rva + pc + 6)` in-corpus through a
  declared borrow-subtractor (`nibble_sub`/`nibble_pred` — the mirror
  of std's `nibble_succ`/`nibble_add`).
- `symtab` is declared data: `text_rva=0x3000`,
  `iat_ExitProcess=0x1038` — the constants `target_pe64.pack`
  computes for `imports=("ExitProcess",), slots=(("_",8),)`.
- Encodings as clauses-as-data: `ret/nop/int3`, `push/pop`,
  `mov_ri`, `sub_ri8` (48 83 /5 ib), `xor32` (31 /r via
  `modrm_rr32`), `call_mrip` (FF 15 disp32).
- `nibs2bytes`/`shl4`/`bplus`/`len_nl` — byte↔nibble-list coercions
  as declared rows, no peano walks (nibble depth ≤16).

Two corpus-semantics bugs found en route: `nibble_sub`'s base clause
must *drop* the top borrow (two's-complement wrap IS the disp
semantics — refusing it made every negative fixup diverge), and
`nibble_sub_b` needs a `b≠0` guard on re-pull (`pred(0)=15` would
enumerate a phantom branch).

## The emit seam closes

`_cogen_emit.py`: decode the enc'd byte-tree → `.text` →
`target_pe64.pack` / `target_elf64.pack` / `pack_obj` → run.

```
decoded .text: 48 83 ec 28 31 c9 ff 15 2c e0 ff ff (00)
             = sub rsp,40 ; xor ecx,ecx ; call [rip+iat_ExitProcess]
isa_x86_64.encode(same ops): byte-identical ✓  (independent witness)
pe64/elf64/.o: all three writers validate ✓
run cogen_exit.exe: rc=0 — real ExitProcess(0) through the IAT
```

The clean-exit program was assembled by the .plex map, decoded,
packed by the declared-layout writers, and executed on Windows —
returning 0 through a real Win32 call whose address came from
in-corpus nibble subtraction.

## The interpreter² wall, measured

`eval<menv> 'call assemble src` on the 29-rel rt env in rel.rs:

| src | relcalls | walks | lifts | time |
|-----|----------|-------|-------|------|
| `[ret]` (1 insn) | 372K | 81M | 8.3M | 49.7s |
| clean-exit (3 insns) | — | — | — | >15min, killed |
| toy map, `[push rbp;ret]` (5-rel env) | ~4K | — | — | 0.3s |

The wall is per-*call*, not per-instruction: each inner map goal
through `eval<menv>` pays a linear `env_find` over 29 fat enc'd
clause lists plus a `lift` of deep nibble-table spines. The corpus
eval is the *specification* of interpretation, deliberately naive —
so the honest split is:

- **direct `apply<mapg2>`**: the dev/realization path — 0.46s for the
  clean-exit program, will scale to the real src.
- **`eval<menv>` through the corpus**: once-per-milestone
  confirmation. For rt-probe expectations the witness computes the
  answer directly (`enc_t(direct_assemble(ops))` — verified identical
  to the interpreter² sol on the toy path).

## Honest edges

- `rel.rs` needed a 1GiB worker stack for interpreter² recursion
  (`plex_rel` now spawns it; BINDS counter not ported to the
  persistent subst — reads 0).
- Map covers ~9 forms; the real seed program needs 38 — the next
  coverage pass should generate `enc2` rows from the mined
  ENCS/FIELDS table data rather than hand-writing clauses.
- At ~50s/insn interpreter² scale, the 505-insn real program is not
  eval<menv>-feasible without clause-template compilation
  (kill per-activation `lift` dict-walks) — or it stays the
  milestone-only leg.
