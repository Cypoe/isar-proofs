# 035 — Behavioral cross-verification: three witnesses, observations not artifacts

Commit `723cfde` — `host/cross_verify.py` + the fixes it forced out.

## Shape

139 probes (named goldens + all depth-2 app trees over `IKBWC` +
edge cases: underflow, empty, bad byte, >granule stream) through
three witnesses, compared as **observations** (stdout NF tokens,
stderr `steps=`/`alloc=`, rc, divergence-class):

- **PE ↔ C** — byte-identical on every probe, both builds
  (default, fuse_s). The strongest leg.
- **graph.lo ↔ C** — NF + steps on default build, NF only on fuse_s.
- **fuel axis** — fuel=5 on SKKI → rc=2 identical partial stats.

## Findings the suite forced out (why it's worth running)

1. **Parse skip-set**: the native exe's `r_parse` accepts only
   `space tab CR LF` — `,` → exit(3). Python `bc_compile` skips `,`
   too — host-side laxness, NOT the exe contract. `routines_c`
   initially mirrored the Python set; fixed to the native set.
   Principle reaffirmed: the running programs are the contract,
   not the most convenient parser.

2. **`tree WWW` = dupβ fixed point**: `W W W → W W W` — true
   divergence under `fuel=None`. Runs bounded by a 15 s test guard
   (same discipline as `run_native`/`run_exe` already document),
   compared as a `TIMEOUT` observation. Identical non-termination
   is part of the equivalence claim.

3. **graph.lo is a third IStepBasis witness**, not `reduce.py`'s
   IStep: `graph_runtime.Graph` fires dupβ/swapβ and expands
   `S → derived_s` on import — the same rule family as the DEFAULT
   build (S K K I → 10 steps on both; fuse_s gives 2 — primitive
   sβ, cheaper by design).

4. **NF quotient normalization**: graph exports through
   `quote_surface` — an intact `ds` subtree prints as `S`, kernels
   decompile the raw `B W C @` tree. Same term; both sides are
   re-quoted before comparing (e.g. `K ds I → S` probe).

5. **Underflow parse drift**: graph's `_parse_native_out` pads a
   1-element stack without building the app node — same NF, fewer
   steps. Parse-level difference; steps compared only on
   non-underflowing probes, NF always.

## Status

`OK cross_verify (0 divergences)`. The second host is now
behaviorally equivalent to the PE host on the whole probed
observation space — including error paths and divergence.

Next: seed emits its own host (the bootstrap-closing stage).
