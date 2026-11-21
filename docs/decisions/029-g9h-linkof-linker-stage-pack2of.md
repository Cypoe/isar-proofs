# 029 — G9h: linkOf — the linker stage; the link seam closes

Status: implemented, probe-verified (mini + win64), suite pending.

Emit stage 6.  Until now the symbol table `assemble` consumes was
injected by hand (`symtab_term(dict)`), while `packOf` recomputed
`idataOf`/`dataOf` internally — two independent computations of the
same symbol facts.  `linkOf` makes the linker real: the section
builders run **once**, export their symtabs, and the merged table
feeds both consumers.

## The stage

```
L = linkOf IMPORTS SLOTS         -> pair(pair(idata, datab), syms)
A = assembleOf PROG (L (K I)) base              — symtab from the link
P = pack2Of (A K) (L K K) (L K (K I)) stackres  — sections from the link
```

- `linkOf` = `idr = idataOf imports`, `dat = dataOf slots`, result
  `pair(pair(idr K, dat K), APPEND (idr (K I)) (dat (K I)))`.
- Merge order mirrors the oracle exactly: `_ALOOK` is FOLDL
  last-match, so `APPEND iat_syms data_syms` puts data last —
  `out = dict(iat); out.update(ds)` in `target.symbols`.
- `pack2Of` = `packOf`'s body refactored: `_pack_body()` shared,
  `idata`/`datab` become λ params instead of `(idr K)`/`(dat K)`
  projections.  Sections arrive built — nothing recomputes.

## Why this is the honest linker

A real linker merges *object-level* export tables; it does not
recompute symbol addresses from a spec.  `symbolsOf` (G9d) remains
correct — it is the same map computed statically from counts — but
`linkOf` derives it from the actually-emitted sections, which is the
ground truth the assembler should resolve against.  The two must
agree (and do, byte-for-byte); the gate cross-checks both against
`target_pe64` functions.

It also removes the duplicate reduction: `packOf` re-ran
`idataOf`/`dataOf` inside its body.  In the linked pipeline the
sections exist once and flow to both sides of the seam.

## Evidence

- `linkOf` mini: idata 99B + data 8B + merged symtab
  `{iat_ExitProcess: 0x2028, x: 0x3000}` — exact vs oracle,
  39.8k lo steps.
- `linkOf` win64: real IMPORTS + DATA_SLOTS — see
  `_probe_g9h_win64.py`.
- `linkasm` mini: `assembleOf PROG (linkOf … (K I)) 0x1000` — a
  program with real rip-relative refs to `x` (data sym) and
  `iat_ExitProcess` (iat sym) — 20B text, byte-exact vs
  `isa.assemble` fed the link-derived table, 710k lo steps.
- `pack2Of` mini: `pack2Of text idata datab stackres` — 2048B image
  byte-identical to `target_pe64.pack`, 184.8k lo steps (~32k cheaper
  than packOf mini — the section rebuild skipped).

## Boundaries

- `cd` on pack2Of deferred like packOf (image-sized NF — measured
  >5000s CPU in 027; same class, not a correctness question).
- The full `link → assemble → pack` chain in one arena hits the same
  arena-resident composition wall as G9g's e2e — the honest model is
  staged: serialize each stage's NF at the boundary
  (`_probe_g9g_e2e_staged.py` proved the pattern).  `linkasm` gates
  the symtab-consumer half in one arena because assemble's NF is
  small; the pack consumer half gates on literal linked sections.
- `linkOf`'s output shape `pair(pair(idata, datab), syms)` is the
  natural section-bundle; pack2Of's projections are `(L K K)` /
  `(L K (K I))`.
