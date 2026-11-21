# 058 — native gc='sweep': dual-range persist-aware mark/sweep

Decision: reclamation for `reclaim='redirect'` is a native
Schorr–Waite mark/sweep collector, not a shape change.  Swept
space is **two ranges on two different 24-lattices**:
persist `[pcur0, pcur)` (absolute-aligned base) and reduction
arena `[irstart, rbx)` (page-aligned base).  Roots: conservative
stack+register scan, plus — IR only — the input region
`[permend, pcur0)` scanned field-wise because input cells FWD
into persist.

## Invariants this must hold

- **Input/persist cells never point `>= irstart`** — the arena is
  decommitted per root (`ir_bloop`), so `mkapp_p` may only pop
  `flhead_p`, never the arena freelist.  `_fr` write-backs
  already guard this.
- **`flhead` resets per root** (its cells die with the decommit);
  `flhead_p` does not.
- **Every allocator call is a full register hazard** — freelist
  pop and `VirtualAlloc` both run under live `rcx/rdx/r8–r11`.
  The collector pushes all 13 cell-capable registers; grow paths
  save the volatile set around `VirtualAlloc`; pops save `rcx`.
- **`v<C` acyclicity is emergent, not checked** — under
  bump-alloc every child is older than its parent.  Freelist
  reuse was the latent break; it is sound only because marking
  is complete at collect time (verified by freecheck/birthlog
  audits before the pop fix).
- **`nfree > nalloc` in one collect is impossible** — the tell
  that caught a dropped `cmp` orphaning a `jb` on stale flags.
  Worth a gate someday.
- `x86` has no `jae` in our ISA — unsigned `a >= b` is
  `cmp b,a; jbe`.  Flag-reading branches after `mov` are wrong
  by construction (`mov` doesn't set flags).

## Evidence

- `rfold maps=[asm]` (eval<menv>, mfuel=32768): **completes**,
  1.226e9 steps → `[]`; persist zone cycles ~13× (nfree=141M on
  nalloc≈150M @ the 100M cap).  Was: exit4 at 256MB persist.
- `cross_verify`: 139 probes, 0 divergences.
- Semantic verdict on `[]` is pending a Python-witness run —
  plausibly correct (single-map fold of `assemble_x86` over a
  raw spec term).  Honest stream, not a masked failure.
