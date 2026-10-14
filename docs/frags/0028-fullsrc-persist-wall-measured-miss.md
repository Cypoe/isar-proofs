---
type: frag
id: 0028
provenance: devin-cli
ts: 2026-10-13
tags: [phi2, eval, pass1, assemble, full-src, persist, redirect,
       gc-sweep, oom, megaplan-7, freeze, decision-066]
---

# 0028 — full-src verdict: pass1 OOMs on the persist zone at 16 GiB; the wall is pinned input-descended closures, not sizing; MEGAPLAN §7 misses

## What was measured

After frag 0027 cleared the substitution quadratic (~410M/op
marginal, linear through 8 ops, fasmg-verified), the full-src
criterion was attempted on the 769-item program (2811 B oracle
`.text`, 81 labels, env=33 rels for `pass1`, 54 for `assemble`) —
`machine_term(8192)` + ir exe, `reclaim="redirect"`, `gc="sweep"`,
`fuel=None`, take-1.

| run | persist | arena | result |
|---|---|---|---|
| `assemble` full-src | 2.147 GiB (imm32 max) | 32 GiB | rc=4 @ 1923.1 s |
| `pass1` full-src | 2.147 GiB | 32 GiB | rc=4 @ 1841.3 s |
| `pass1` full-src | 1 GiB | 32 GiB | rc=4 @ 277.0 s |
| `pass1` full-src | 16 GiB | 64 GiB | rc=4 @ 24890.9 s |

All four `exit4` with empty stderr; the dynamic arena stayed
near-empty (working set flat at persist size — the zone commits
eagerly at depack). The OOM is the persist allocator's
collect-then-concede path, not `ir_arena_bytes`.

## The mechanism (corrected 2026-10-13 after `pfree` instrumentation)

My first read — "superlinear frontier growth" fitted from three
wall-times — was wrong. Instrumented stderr (`stats_p` on
exit2/exit4, `pfree=pend−pcur`) shows the real picture:

- The zone **saturates early and stays saturated**: `pass1 ret64`
  @1 GiB hits `pfree=16` by 500M steps and pins there through 2G+
  steps (gc=89, still alive — `flhead_p` recycling keeps pace).
  `fullsrc pass1` @2.1 GiB hits `pfree=8` by 1G steps.
- `alloc ≈ 1.5×steps`, `free ≈ alloc` — the dynamic GC reclaims
  essentially everything; the dynamic arena is near-empty the whole
  run. All real pressure lives below `irstart`.
- `ret16` @256 MiB: `steps=1.2G alloc=1.8G gc=977 free=1.8G
  pfree=16` — the concede is the first collect that frees ~nothing.

Root cause is in the mark phase: `gc_collect` treats the **entire
input region `[permend, pcur0)` as roots** ("input cells FWD into
the persist zone, so their fields are roots"). Every input cell is
a permanent root → every input-descended reduct is pinned forever.
live-persist = the cumulative closure of everything the eval has
forced out of the input graph — monotone, unbounded. For a
metacircular eval the program-under-interpretation *is* input data,
so the pinned closure is the whole derivation.

That is the pay-once design working as built — it exists for
*streams of small roots* (shared M/env amortizing across a batch).
A single 774-item take-1 root is exactly the shape it cannot serve:
the memoized closure grows for the whole run, so **no finite cap
suffices** — the three OOM wall-times (277s@1G, 1841s@2.1G,
24891s@16G) are just when the pinned closure crossed each cap.

`assemble` is ~3.2× `pass1`'s steps at probe scale — strictly
harder, not run at full-src.

## What changed on the way

The 2.147 GiB cap was itself an accident: `pend = pcur +
persist_bytes` used `add_r64_imm` (signed imm32). Widened to
`mov_r64_imm` + `add_r64_r64` (commit `4720a08`, goldens refreshed
byte-coherently, nanopass 35/35). That fix mattered — it proved the
wall is the *growth rate*, not the ceiling: at 16 GiB the run
survived 13.5× longer and still conceded.

## The §7 verdict

**MEGAPLAN §7 misses.** Native `assemble` for the full-src program
under `gc=sweep` does not complete: the declared-realization space
(reclaim=redirect is the only gc=sweep leg; persist_bytes and
ir_arena_bytes are the only memory axes) has no point that carries
769 sequential ops in one take-1 stream. The next move is a
retention-model change — input-tier routing, stream/root splitting,
or a reclaim leg that does not pin input-reachable reducts — and
each of those is new substrate, which the freeze protocol forbids.

Frozen honestly:

- fixtures: `telemetry/phi2_repr_cost/rows.jsonl` rows tagged
  `trie-persist-wall` (this table, machine-readable)
- the trie strategy itself is proven at probe scale (frag 0027):
  the quadratic is cleared, emission is byte-verified — the wall is
  downstream of the substitution decision
- still open, unrelated: frag 0016 interpreter² `'nvar` limit

## What this does NOT claim

- No claim that pass1's search is exponential — step counts are
  consistent with ~linear ops × growing frontier; the OOM is
  *space*, and the space curve is what kills it.
- No claim the criterion is unreachable in principle — only under
  the current realization set. A reclaim leg without the
  persist-pin, or multi-root scheduling, is a design decision above
  this frag.

## Postscript 2026-10-14 — resolved by frag 0029

The "pinned closure" was confirmed but *not* as dead structure —
`plive` proved the memo table genuinely reachable at concede. The
fix was upstream of marking: route the **final** root's
input-tier reducts into the dynamic arena (no future root can read
its FWDs). Persist is untouched on single-root evals; the §7 bound
moved from space to time. See frag 0029.
