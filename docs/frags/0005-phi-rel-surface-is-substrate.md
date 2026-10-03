---
type: decision
id: 0005
provenance: specs/surface-phi.rel.json; isa-physics
  patent/phi-lang (boot, boot-mlir, phi-stdlib); the cordis-koru
  staging note
ts: 2026-10-08
tags: [surface, phi.rel, substrate, dialects, koru, schema]
---
# phi.rel is the substrate speaking, not a desugar target

## The correction that decided it

I framed the surface question as "rel → bracket abstraction on
the SKI kernel."  Wrong level.  SKI is a *view* — the shorthand
Lean happened to prove with, and the view the seed emits — but
the combinators fall out of the relational substrate (matrices +
U + Join + Π), exactly as the SQL- and torch-hosted demos showed.
Bracketing `rel` into SKI would smuggle a privileged basis back
in through the surface.

## What the spec declares

`host/specs/surface-phi.rel.json` — the 13th contract file,
`status: declared`, surface layer, `bytes → rel-graph`:

- **Clauses are relation extensions** — `| guard { body }` is a
  guarded union of alternatives, not committed-choice function
  bodies.  Non-determinism is just a relation with multiple
  outputs; **determinism is a quotient picked per call** —
  `RUN(g,1)` committed read vs `RUN(g,0)` stream, the same
  `norm`/`stream`/`find` split the patent phi-lang already has.
- **Direction is declared, not inferred** — `<->` reversible
  composition, `<=>` contraction (lossy), `->` directed mode
  (in→out query view).  Calling a directed rel ungrounded is a
  mode violation → refuse.
- **Kernel vocabulary is substrate ops** — `{FRESH, UNIFY,
  MATCH, APPLY, CHOICE, RUN}` — not combinators.  No primitive
  arithmetic: ops are relations (phi-stdlib model — nibble
  carry chains as contractions).
- **Recursion shape is data** — koru's restricted vocabulary
  (`self|pairwise|step|reduce`) becomes a per-rel declaration:
  the lowering contract picks a kernel form or refuses.  Shape
  undeclared on a recursive rel → refuse.  This is `K` from the
  domain tuple (lowering contracts) made literal.

## The schema lifecycle it fits

The Tauri/Rust five-stage maps onto what already exists:
declaration (spec files, toolchain.json) → transform
(`validate()` → frozen records) → phantom validation
(`layers.compose` refuses invalid axis combos — invalid
artifacts can't be *constructed*) → runtime descriptor
(realized records, REALIZATION rows) → dispatch
(`resolve()`/`by_name`, refusal by default).  The gap left:
constructors that still produce check-then-reject artifacts
(`emit_sections` will serialize an incomplete schedule —
validity caught at replay).  Closing it = only exposing
schedule constructors whose composition is valid by type.

## The regimes note is an executor contract

`W(n) > (T_setup + T_merge)/(1 − 1/pη)` — `workers` shouldn't be
unconditional: `_run_stage` knows the root count; the threshold
belongs as declared cost data (a `schedule.work_threshold`
bundle field), decided by data, measured by bench.py — not a
hidden executor heuristic.

## Evidence

- `layers.load_specs()` accepts the file; `phi.rel` surfaces as
  declared alongside lisp/lambda/xdu.
- Reference vocabulary exists upstream: `patent/phi-lang`
  (isa-physics) — boot, `boot-mlir.py` MLIR lowering,
  `phi-stdlib.phi` deriving arithmetic from contractions.
- `toolchain.json` already carries `phi.rel` as "spec only, no
  parser" — the spec file is the contract it points to.
- Deferred honestly: the parser (`phi_rel.parse_rel`), the
  substrate evaluator leg (JOIN+NORM in the emitted kernel —
  the runtime/interpreter contract, separate from compile),
  schema-as-phi.rel for toolchain.json (G9 spec-as-term).
