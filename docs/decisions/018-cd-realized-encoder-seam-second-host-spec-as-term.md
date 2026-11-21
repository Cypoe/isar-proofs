# 018 — cd realized, encoder seam proven, second host, spec-as-term

Date: 2026-07 (session after 017). Commits: 4e547e7, 611db72, cb13499,
4c2e0e1, a55451a (isar-proofs); 57d24ec, c118ca5 (isa-physics handoff).

## World model

Four claims became executable in one session:

1. **Strategies are data, not branches.** `order="cd"` is a second routines
   module (`routines_x86_64_win64_cd`), not a flag inside the lo module.
   Recursive development + per-head dispatch: every redex present at a
   development's start contracts in one pass; contractum-born redexes defer
   — the mark-set semantics without touching tag dispatch. Rounds are a
   distinct unit: stderr says `rounds=`, never `steps=`. Disjoint + nested
   redexes contract in one round; NFs equal graph.cd / hreduce.cd.

2. **"Core knows no ISA" is shared code, not a pattern.** `enc_core.interpret`
   takes the combiner: x86 joins byte chunks, aarch64 folds (value,lsb,width)
   slices via `word32` with set-bit-disjointness asserts. The x86 image is
   byte-identical after extraction — that IS the proof. aarch64 gated on
   llvm-mc two-pass (masked show-encoding + objcopy .text for branch imm
   byte equality). A rel-width corruption invisible to pass 1 was caught
   by pass 2 — the weak oracle would have missed it.

3. **Host realization is data.** elf64 + `x86_64.linux.lo` routines: same
   encoder, same lo algorithm, syscall ABI (mmap chunks instead of
   VirtualAlloc). Cross-ABI gate: win64 exe | linux ELF under WSL | graph.lo
   — identical NF, steps, AND alloc on every probe. Real bug found: mmap
   clobbers rsi/rdi where VirtualAlloc preserved them; save/restore inside
   grow_heap restored the invariant the ABI provided implicitly.

4. **The catalog is consumable by the kernel (G9a).** toolchain.json → basis
   term (structural: Scott pair-lists, nibble-selector strings, `C I` null —
   inert everywhere, no S). `pathOf` query = assoc fold + nibble-string eq,
   bounded Church iteration only (no fixpoint combinator — cd terminates).
   14 queries × 4 witnesses agree, including the unknown-name negative.

## Membrane

- `("p",label)` in generic mem forms now hard-refuses (was silent disp=0;
  two live mis-encodings found via xdu). Resolver-aware paths are the only
  label routes — same discipline aarch64 inherits (rel field only).
- **Full-spec graph.cd is hours-scale** at ~23k-node spec terms — each round
  re-walks the residual (superlinear). G9a's honest move: cd gates named
  projections. The fixpoint wave needs a memoized/shared cd round, not a
  smaller spec. This is a known executor limit, not a semantic limit.
- spec_term is the heaviest battery suite (~11 min) — honest term work.
- Remaining declared: riscv64 ISA, uefi/macho/flat targets, uefi routines,
  aarch64 routines, lambda.bracket native alphabet, phi.rel, axes
  {arena, reclaim, explicit stack, memory io, uefi abi}, syscall-trace.
- G9 proper (specialize → regenerate emit(R)) remains open; the spec is now
  a consumable object, which was the precondition.
