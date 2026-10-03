---
type: feature
id: 0004
provenance: challenges catalog 34/34; spec_project render_matrix;
  bench_last.json; .devin/hooks.v1.json; docs/stages/*
ts: 2026-10-08
tags: [phase9, enforcement, challenges, matrix, bench, hooks]
---
# The enforcement flywheel

## What changed

Phase 9 turns the 7/8 status quo into the enforced standard —
every claim replayable, every refusal named, every measure a
number in a file.

- **`host/challenges.py` — the standing challenge catalog.**
  34 named reproducible entries: the v3 refusal matrix as 16
  named cases + a valid control, emit.plex forges (MAP
  out-of-range, missing dep-closure stream, alien program
  stream, corrupted span, widened caps, truncated header),
  axis-mode refusals (threads-on-token, bogus dialect,
  mark-sweep), and `toolchain._negative_cases` spec mutations.
  Each entry carries a *recorded expected outcome* (rc,
  refusal prefix, validation failure) diffed against the
  observed one — drift is loud, never a boolean.  Registered
  as obligation CH1 (staging/seam, tier full).
- **`docs/MATRIX.md` — the emit-target triplet matrix**, generated
  by `spec_project.render_matrix` alongside GATES/CATALOG:
  24 toolchain rows × dialect/isa/routines/target slots
  (✓ realized / ○ declared / — unregistered) plus the
  obligation-family × live-cell coverage table from
  battery_last.json.  Drift-checked by the same mechanism.
- **`host/bench.py` — measures, not assertions.**  steps/s and
  alloc on the redirect kernel, MT scaling (threads 1/2/4 —
  parity is the MT-equiv gate's job; this is only a number),
  mini emit wall with the oracle check folded in, declared
  arena vs peak RSS, and every registered bench module run as
  a suite with headline output captured → `bench_last.json`.
- **`docs/stages/` — the four stage contracts**: program, link,
  assemble, pack — term signature, consumers, checkpoint key
  shape, evidence produced.
- **`.devin/hooks.v1.json` + root `AGENTS.md` — writeup-driven
  development made structural.**  SessionStart injects the
  contract; a Stop hook nags when engine files changed without
  a `docs/frags/` entry (non-blocking — a question isn't a
  feature; the norm is in AGENTS.md).

## Subtleties worth remembering

- **Expected values are shapes, not strings.**  A challenge
  records `{rc: 3}` or `{refuses: prefix}` — enough structure
  to catch both silent-success and wrong-refusal drift, loose
  enough that message wording can evolve.
- **`_rss_of_run` deadlock.**  First bench hang was a pipe
  deadlock: the child blocked on stdin while the parent polled
  RSS — write+close stdin *before* polling, always.
- **Bench probes are sized to the kernel.**  At ~4.8K st/s a
  16×4KB stream is minutes; 8×512B (~81K steps) is a stable
  measure in ~17s.  The measure's job is comparability, not
  stress — stress is what gates forge.
- **`native.c` reads "realized" in the matrix** — status derives
  from component modules importing, same as CATALOG.  The C
  second-host question (can it read .plex, pick its own C
  dialect) is a different axis and stays deferred.

## Evidence

- `python host/challenges.py`: 34/34, 0 drift (v3 17/17,
  emit 6/6, axis 3/3, spec 8/8).
- `python host/bench.py --json`: steps_per_s ≈ 4.8K,
  mt_scale 1.0/1.7/…, emit_wall 84s → 2048B oracle-true,
  peak RSS 6MB vs 2GB reserved arena.
- `python host/spec_project.py`: GATES/CATALOG/MATRIX in sync.
- `python host/battery.py --only gates/spec_check`: pass;
  CH1 row present in the obligation table.
- Both hooks emit valid `hookSpecificOutput` JSON.
