---
type: decision
id: 0006
provenance: host/emit_chain.py write_emit_bundle/run_emit_bundle;
  the regimes bound from the cordis-koru staging note;
  host/challenges.py emit-threshold-*
ts: 2026-10-08
tags: [schedule, workers, regimes, declared-data, challenges]
---
# The parallel/serial threshold is bundle data, not an executor mood

## The regimes bound

The note's cost model:

    T_parallel(n) = T_setup + W(n)/(p·η) + T_merge
    T_serial(n)   = W(n)

Parallelism wins only when

    W(n) > (T_setup + T_merge) / (1 − 1/pη)

For small bodies the spawn/merge costs dominate.  Phase 8c wired
`workers=N` through the emit chain, but the decision was still a
bare `workers > 1 and len(group) > 1` — an executor mood, not a
contract.  The scheduler knew the bound; nothing declared it.

## What landed

`write_emit_bundle` serializes `schedule.min_parallel_roots=16`
into REALIZATION next to `schedule.output` — the threshold is
bundle data, forged/forgivable like every other row.  Replay
(`run_emit_bundle`) reads it once and applies it at both pool
sites:

- `_run_stage` pools sliced root chunks only when the stream's
  root count clears the threshold (chunks exist post-rc=4
  halving — arena-bounded slicing, unchanged semantics).
- Dep-level pooling engages only when some member stage's stream
  clears it — a level of small stages serializes because spawn
  cost dominates.

Every stage's ev line now carries `pool=True|False` — scheduling
is observable evidence, diffable like any other outcome.

The default `16` is a placeholder in the honest sense: it lives
in the bundle where `bench.py` measurements can replace it (the
regimes formula with measured `T_setup`/`T_merge`/`η`), not in a
constant the executor hides.

## Evidence

- `emit-threshold-pool` / `emit-threshold-serial` — forged
  bundles with `min_parallel_roots` below/above every stage's
  roots; observed `pool=` flags prove the bound is honored under
  `workers=4` in both directions.  The serial challenge's first
  draft encoded the expectation inverted (`"pool=False" in ev`
  means serial happened, i.e. `pool` observed True) — the
  recorded-outcome discipline caught my own probe, which is the
  point of the catalog.
- Semantics unchanged: output bytes are scheduling-independent;
  the audit (program items ↔ assemble roots) still gates the
  image.  Both challenges return the full ev for inspection.

## Boundary

This covers the *bundle executor*.  `emit_frames(staged)` keeps
caller-supplied `workers` — direct API scheduling is the
caller's choice; declared-data scheduling is the archive's.
The seed-side executor (G9 spec-as-term) inherits the same row
when it learns to read it.
