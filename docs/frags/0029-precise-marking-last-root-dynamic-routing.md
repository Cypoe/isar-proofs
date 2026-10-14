---
type: frag
id: 0029
provenance: devin-cli
ts: 2026-10-14
tags: [phi2, eval, gc-sweep, redirect, persist, marking,
       last-root, megaplan-7, decision-066, decision-067]
---

# 0029 — precise marking measured the wall; last-root dynamic routing removed it (single-root persist was the whole pathology)

## Sequence (instrument → measure → fix)

1. `stats_p` + `pfree=` landed (commit `1f12034`): concede/fuel
   exits stopped exiting blind.
2. **Hypothesis A** — the persist zone is mostly dead-but-pinned
   structure (all input cells scanned as roots). Fixed marking to
   scan only the remaining-roots table window
   `[irroots+8·irj, +8·irnroots)`, traverse *through* input cells
   (mark but never sweep — their `+4` mark dwords are clean by
   depack), clear input marks post-collect. New counters:
   `plive` (reachable persist cells), `plast` (persist cells freed
   by last collect), `pfwd` (live persist FWD cells).
3. **Measured — hypothesis A refuted.** `ret16 @256MiB` died at
   1,207,265,443 steps vs 1,207,140,891 under blanket rooting
   (+0.01%); `plive=268,435,440` = cap−16, `plast=0`. The bundle is
   one connected term, so every input cell stays reachable and the
   memo table is genuinely live. 66% of live persist cells were
   FWD routing cells (`pfwd`), but path compression would not have
   moved the death point.
4. **The real fix (hypothesis B):** the persist zone exists only
   because input cells must not point above `irstart` — the
   dynamic arena is decommitted between roots. The *final* root of
   a stream has no successor that could read a stale FWD, so its
   input-tier reducts can allocate in the ordinary GC'd arena.
   `r_mkapp_p` now branches on `irj == irnroots-1`: non-final roots
   keep persist allocation + FWD (cross-root memoization intact),
   the final root jumps to `r_mkapp`.
   (First version clobbered `rcx` — live across `mkapp_p` call
   sites — AV'd on multi-root streams; switched to `r8`.)

## Before / after (same binary class, same inputs)

| run | before (blanket roots, all-persist) | after |
|---|---|---|
| `ret16 @256MiB persist, fuel 2G` | rc=4 @ 1.207G steps, 656s, gc=977 | rc=2 @ 2G, 33.2s, gc=9, `pfree=268435456` untouched |
| `pass1` full-src @4GiB arena | rc=4 in persist at every cap ≤16GiB | rc=2 fuel-cap @ 33.8s, gc=9, live-dyn ≈135M cells |
| `pass1` full-src unbounded | rc=4 @ 24,891s (16GiB) | alive at ~35G+ steps when wall-killed @600s — sublinear live growth |

Multi-root probes (roots=1,2,3,5): correct outputs, `pfree`
shrinks only across non-final roots — memoization preserved where
it pays. Nanopass 35/35, battery 31/31, fixtures regenerated.

## What changed and what did not

- Changed: the §7 wall is now **time, not space**. ~410M
  reductions/source-op × 774 items ≈ ~320G steps ≈ hours at
  ~30–60M steps/s. That is the metacircular step expansion of
  `eval.phi` on `machine_term`, identical in the Python witness —
  not a leak.
- Unchanged: input cells still FWD into persist for non-final
  roots; the invariant `v < irstart` still holds for any cell that
  can outlive its root; refusal semantics and gate corpus
  untouched.

## Verdict

Hypothesis A was tested and refuted by `plive`; hypothesis B is
confirmed by `pfree=268435456`/`plive=0` across the former death
points. The persist zone was being used as a general heap for a
single giant root — a shape it was never designed for. §7 is
re-opened as a *runtime* criterion, not a space bound.
