# 067 — final-root input-tier reducts allocate in the dynamic arena

## Context

Frag 0028 froze §7 on the persist-zone wall: input cells are
permanent, their FWD'd reducts live in `[pcur, pend)`, and the
whole input region was scanned as roots every collection —
everything an input cell ever produced stayed pinned forever. For
a single metacircular-eval root the pinned closure *is* the
derivation; 16 GiB still OOM'd.

Instrumented experiment (frag 0029): precise marking (scan only
`[irj, irnroots)` root-table entries, traverse-through-input,
clear input marks post-collect) moved the death point +0.01% —
the live set genuinely reaches any cap. The pin was the allocator
*policy*, not marking precision.

## Decision

The persist zone exists solely because input cells may not point
above `irstart` — the dynamic arena is decommitted between roots,
so a FWD into it would dangle for later roots (decision 044/054).
The **final** root has no later root: nothing can ever follow its
input-cell FWDs after stream end, and nothing decommits its arena
mid-eval. Therefore `r_mkapp_p` gates on `irj == irnroots-1`:

- `irj < irnroots-1` → persist allocator + FWD, unchanged
  (cross-root memoization, decision 054 semantics preserved);
- `irj == irnroots-1` → ordinary dynamic `mkapp`; reducts are
  normal GC'd cells.

The gate uses `r8` (scratch at `mkapp_p` call sites) — `rcx` is
caller-live across the freelist dance; using it AV'd multi-root
streams.

## Measured

`ret16 @256MiB`: was rc=4 @1.207G steps/656s/gc=977; now rc=2
@2G steps/33s/gc=9, persist untouched. Full-src `pass1` fuel-caps
cleanly @33.8s (2G steps, 4GiB arena) and survived >35G steps
unbounded where it previously died at every persist cap.

## Trade-offs stated

- Multi-root streams still pay persist on non-final roots —
  intended; that is where memoization earns.
- The last root loses cross-stream memoization it could never
  have used — pure win.
- GC is now precise-marking + two sweeps + an input-mark clear
  pass; slightly more mark work per collect, vastly fewer
  collects.

## Direction noted (not implemented)

The base term being a combinator graph was a Lean-proof shorthand,
not the substrate target. The substrate should *host* reduction
models (incl. inet-shaped objects with local reclaim); SKI/BCKW is
one hosted strategy, not the model. That is the honest lever on
per-step cost and on removing the persist/dynamic split entirely.
