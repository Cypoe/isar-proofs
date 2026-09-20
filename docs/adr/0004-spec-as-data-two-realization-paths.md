# ADR-004: Spec-as-data toolchain; two realization paths; transducer program class

**Status**: Accepted
**Date**: 2026-09-20
**Commits**: `e5f368d`, `5a1221c`, `3e3be7c`, `22e7408` · memory decision 017

---

## Context

After the seed split (decision 016) the toolchain catalog was Python literals in
`host/toolchain.py`, and "native emission" meant exactly one thing: the reducer
runtime compiled to a PE. Two distinctions needed to become architecture, not
convention:

1. **Spec vs realization.** What is realized must be derived, never asserted —
   and the declarations must be *data* a bootstrap can eventually consume, not a
   Python module only the host can read.
2. **Two paths.** A PLEX program that declares its own byte-level behaviour can
   be realized two ways: compiled to native code (`native` — no reducer, no
   tags, no ISAR terms in the image) or encoded as a basis term and reduced
   live (`runtime` — graph piece, operEq). Dynamic input is handled by
   compiling the declared transducer behaviour, never by embedding an
   arbitrary-term interpreter in emitted code.

## Decision

- `host/toolchain.json` is the single declarations source: dialects, ISAs,
  routine sets, targets, pieces, `paths` (native/runtime with meaning, regime,
  covers/uncovered), strategy axes, regimes, obligations, witnesses. **No
  `status` key exists** — `toolchain.load()` derives it by importing the
  declared `module`/`record`. Refusal names the missing component.
- `docs/GATES.md` / `docs/CATALOG.md` are generated projections of the spec and
  the last battery JSON; `spec_project.py` drift-checks them in the battery
  (Koru: every obligation matrix cell is a canonical test). `spec_check.py`
  enforces the transform-owns-interpretation seam over the seed's §0–§3.
- First program class on both paths: **finite nibble transducers**
  (`programs/xdu/*.json`, dialect `xdu.json`). Equivalence = stdout bytes + rc.
  `host/xdu_gate.py` compares direct table interpretation, native exe, graph.lo
  and graph.cd — 73/73 cells including >64 KiB granule crossings.
- The ISA encoder is data-driven: `ENCS` rows are `(predicates → field-ops)`
  alternatives; the ~10-line `_interpret` core knows field/predicate names, no
  instruction families. Byte-identical output, fasmg oracle green.
- Witness 3: `lambda.lstep` (Python mirror of Lean `LStep`, weak β on named
  NExpr + saturated-comb heads) as a cube column, plus `lean.eval` — a batched
  `lake env lean` oracle comparing `compile`/`reduceFuel` NFs, gated behind
  `--with-lean` (one ~25 s invocation per batch).

## Consequences

- New components realize themselves: a module exporting the declared record
  flips its spec status automatically; nothing else edits.
- Falsified sketches recorded: `S h t` is not inert (graph.lo expands `derived_s`)
  → output spine is `C h t` / `B^k I` / `K` nil / last element = rc; a Y-fixpoint
  transducer diverges under `graph.cd` → bounded Church iteration.
- Scope honesty: native covers `xdu.json` only; counting and byte alphabets are
  declared uncovered; runtime-path gate corpus ≤ 32 B (`--deep` extends);
  P2/P3 Futamura still need a β-level `specTerm`; second ISA still needed to
  prove the encoder seam is generic.
