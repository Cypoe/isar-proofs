# 028 — Quotient boundaries measured; HDev_total measure designed

Status: measured + designed.  Follow-up to 027's quadratic finding:
which of the claimed n! permutation quotients are real, which are
already implemented, and where the line to genuine sequential work
sits.  Plus the termination measure for the deferred `HDev_total`.

## The three quotient classes (measured, `_probe_quotient.py`)

**(a) Structural quotient — hash-consing already does it.**
`CONS zf_n zf_n` (two identical producer subterms) costs only a
*constant* +123 steps over a single `zf_n` at every size
(379→502, 659→782, 1176→1299 at n=128/256/512).  The second
occurrence rides the first's development through forwarding —
identical states are one node (`_app_intern`).

**(b) Redex-order quotient — cd's fixpoint already does it.**
Independent producers `PAIR zf n, zf 2n` (deliberately *different*
terms, so sharing can't do the work): cd rounds stay flat
(45/53/54 at n=64/128/256) — both develop inside the same rounds.
k=4 different-sized producers: 53→56 rounds flat.  The k! development
orders collapse to one — measured, not argued.

**Boundary — sequential dependency has no quotient.**
`JOIN [zf n, zf 2n]` (the fold is ordered: `APPEND h (join t)`):
~13·n rounds, 0.86M→51.6M allocs.  Same producer content as (b),
but the order is real — no quotient exists to collapse.

**Sharing-leak metric**: unique interned pairs vs allocations.
`JOIN zf256 zf512` → 51.6M allocs vs 27.9k unique (~1850×
duplication): `mk_app` falls back to fresh nodes when an interned hit
is pending or drifted — the structural quotient leaks exactly where
ancestors are mid-rewrite.  That's the arena-quadratic mechanism,
orthogonal to permutations: the emitted prefix never leaves the
reduction context.  Fix = emission that exits the spine
(streaming/port), per 027.

## Mapping to the user's claims

- State machine → quotient kills n! state orders: **real and already
  realized** — cd *is* the redex-order quotient.
- Instruction sequences / fixed-target jumps (each instruction a
  state): the label→address map is the canonical quotient —
  order-independent by construction.  This is what the linker stage
  computes.
- Function parameter permutations (6 orders of 3 params): argument
  *evaluation* order is quotiented by cd (parallel rounds).  Argument
  *order as representation* → canonical ordering, a link-time
  canonicalization (same class as `symsOf`'s sorted symbol order).
- Tail recursion = state machine: semantically yes, but in this
  reducer each iteration allocates into the arena and old states are
  never freed — the quotient exists in the math, the arena retains the
  residue.  That's 027's quadratic — retention, not permutation.
- Stack recursion: continuation = explicit second state machine;
  same quotient, same retention caveat.

**Honest verdict**: the n!-permutation speedup is real and already
implemented where it applies.  The remaining quadratic is not
permutations — it is retention.  n!-class wins still open are in
*generation-time* enumeration (canonical state numbering, sorted
tables, link-time canonical order) where we control representation.

## Staged e2e plumbing (done)

`_probe_g9g_e2e_staged.py`: `assemble → export NF bytes → fresh arena
→ pack`.  The byte-list NF is the honest object-file seam — arenas
don't leak across stages.

```
assemble: 479291 steps, arena 32.9M nodes (~110s)
text seam: 12B match=True
pack:     220040 steps, arena 238.5M nodes (~918s)
MATCH — pack(NF(assemble ASM_LINK)) == target_pe64.pack(asm_bytes)
```

Peak = max(stage arenas), not sum — the composition problem from 027
closes architecturally, not just on hardware.

## HDev_total — the termination measure

`src/ISAR/HeapDev.lean` has `HDev` (the relation, one constructor per
`Graph.cd` clause), `HDev_wf`, `HDev_sound`, `HDevChain` — but no
totality.  `DevRel_total` (GraphDev.lean:652) proves the dag-level
version by `Nat.strongRecOn i` — node index, since children always
have smaller indices in an append-only table.

At heap level that fails: `cd` recurses on `repr`-resolved children,
and redirects forward old nodes to *fresh, higher-index* outputs.
Naive `(RSubSet h i).card` also fails — resolved-descendant sets can
grow when a shared subterm's forward splices a fresh output subtree
into a sibling.

**The measure that works — the unsealed descendant cone:**

```
μ(h, i, D) = | RSubSet h i \ DoneCone h D |
DoneCone h D = ⋃_{d ∈ D} ({d} ∪ RSubSet h d)
```

Strict decrease at every recursive premise, because:

1. A non-`hit` call is only ever on an *old, unsealed* node whose rep
   is unchanged — if the target had been forwarded this round its rep
   would be a sealed output and `cd` returns the memo hit.  So every
   recursing target was already a resolved-descendant of `i` in `h`.
2. Fresh nodes and interned nodes only enter resolved subtrees
   *below a sealed output* (redirect targets are always just-sealed
   `HDev` outputs — `insert o D₁` in every constructor) → inside the
   done-cone, excluded from μ.
3. Hence an unsealed `h₁`-resolved-descendant of the premise target
   traces an all-unforwarded path — already a resolved-descendant of
   `i` in `h`, unsealed.
4. The premise target itself is in `i`'s unsealed cone but not in its
   own (acyc) → strict.

Base case: `hit` / atom / var.  Statement:

```
HDev_total : HeapWf h → i < h.len → ∃ h' o D', HDev ∅ h i h' o D'
```

by strong recursion on μ with `h`, `D` universally quantified in the
motive (same trick as `DevRel_total` — premises run in grown heaps).

This is the principled fuel: not a wall-clock cap and not a guessed
bound — the seal discipline is exactly what makes it well-founded.

## Open proof obligations for the Lean formalization

- `DoneCone` + the path-persistence lemma: an `h₁`-resolved path to an
  unsealed old node uses only unforwarded intermediates → is an
  `h`-path.  Needs the invariant that a derivation's redirects source
  inside the input's subtree and target that subtree's outputs.
- The `hit` discipline lemma: recursing targets have `repr` unchanged
  and unsealed.
- Then `HDev_total` by strongRecOn on μ — constructor-by-constructor
  case work mirroring `DevRel_total`'s shape.
