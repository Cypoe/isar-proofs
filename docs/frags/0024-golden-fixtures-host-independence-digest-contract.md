---
type: frag
id: 0024
provenance: devin-cli
ts: 2026-10-06
tags: [fixtures, gates, host-independence, digest, gc, contract]
---

# 0024 — golden fixtures; gates compare snapshots not live oracles; digest regime + gc axis into the contract

## What landed

`host/gates/fixtures.py` + `host/gates/fixtures/` — the pexec
landing's outputs committed as golden fixtures:

- `pexec.exe` (13824B) — the emitted schedule executor itself,
  runable as pure data
- `bundle.default.plex` (726232B) — the emit.plex wire fixture
- `image.default.bin` / `image.fuse_s.bin` (4608B) /
  `image.ir.bin` (9216B) — oracle images per record
- `manifest.json` — sha256 + size + producing record per fixture

`fixtures.golden(name)` raises `NotRealized` naming the missing
fixture axis when a snapshot is absent — never a silent recompute;
`refresh_goldens()` regenerates from `emit_native` and propagates
the oracle's own refusals.  Gates compare against fixtures; the
oracle is the refresh path only.

## Gate changes

- `gate_pexec_schedule`: emitted executor must equal the committed
  `pexec.exe` (emit-pipeline drift check), then the committed
  executor + committed bundle must produce `image.default` —
  no host emission inside the execution path.  Refusal probes
  unchanged.
- `gate_emit_bundle` / `gate_emit_schedule` /
  `gate_selfhost_fixpoint` (staged leg): oracle comparison ->
  `golden("image.default")`.  The fixpoint's pickup leg keeps the
  live oracle — a changed Realization has no fixture by
  definition; the oracle is the point there.
- NEW `emit host independence` gate: the phi2/rel.rs status table
  as checklist rows — verified rows run fixture artifacts
  standalone; open rows (gc off-win64, corpus batch primitives,
  program-level observational equivalence beyond image+step
  parity) must stay NAMED: a missing refusal or a silently-changed
  corpus fails the gate.

## Contract changes

- `streams.digest=sha256` declared in the emit bundle's
  REALIZATION rows (decision 064 as data).  `emit_bundle_streams`
  dispatches on it: unknown or undeclared digest regime refuses
  naming the axis; sha256 verifies every span.  Kernel executors
  keep structure-only checking — declared, not silent.
- `gc` registered as a strategy axis in `toolchain.json`:
  `{none: realized, sweep: realized}` — the collector is realized
  on `x86_64.win64` only (the deployment leg); other routine
  modules refuse `gc!=none` by name.  `reclaim.mark-sweep` stays
  `declared` — it names the reclaim-axis variant; `gc` is the
  layering axis on `reclaim=redirect`.

## Decision

`065` — corpus batch primitives (`byte_add`/`byte_sub`): admissible
only as declared corpus rels with a Lean congruence obligation vs
the nibble chains; no engine-level pattern recognition (smuggled
semantics); deferred until the rel.rs GC port makes interpreter-
squared probes measurable end-to-end.

## Honest edges

- The fixture exe is a committed binary: gates trust it because
  refresh regenerates it from the oracle — drift between source
  and fixture is caught by `gate_pexec_schedule`'s emit-side check
  only while the emit pipeline stays exercised; a toolchain edit
  that changes emitted bytes forces a deliberate refresh.
- `image.ir` fixture is 9216B (the plain redirect+bytes+sweep
  record) — the 9728B image from the fixpoint session carried
  bumped arena/persist constants; the fixture documents its own
  record.
- Running-program equivalence stays open: evidence is byte
  equality + identical step counts on the fixpoint legs; the
  systematic observation harness for emitted artifact chains is
  `cross_verify`'s regime, not yet applied per-record.
