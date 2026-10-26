---
type: frag
id: 0034
provenance: devin-cli
ts: 2026-10-27
tags: [koru, host2, witness, runK-twin, kv-wire, fixtures, clang,
       self-host, bootstrap]
---

# 0034 — host2: the koru-side host pipeline, witnessed fixpoint runs natively

## What landed

`host2/` — a second host tree beside `host/` (the plex/ISAR
pipeline). Koru's own substrate, and deliberately almost no logic:

- `host2/run.py` — the **runK witness twin**: a Python transcription
  of `ISAR.FlowDialect` (`runK`/`evalKE`/`evalKBin`/`evalKUn`/
  `evalKBuiltin`, oracle, `asKResult`) operating **directly on .kv
  wire values** — no decoded AST classes, the wire form IS the data.
  Every refusal shape mirrors its Lean arm: rational floats with
  `d=0` refusal, `/` zero-denominator refusal, `%`-on-floats refusal,
  unbounded ints, short-circuit `and`/`or`/`cond`, first-binding env /
  last-binding cell-field, fuel-as-cap, catchall-refuses-in-bare.

- `tools/DumpKoruFixtures.lean` — the canonical .kv **writer**: prints
  the fixture JSON (programs + per-case `quoteProg`/`evalKProg`/
  `emitC99`/`runK kEmit` expectations). Regenerate with
  `lake env lean --run tools/DumpKoruFixtures.lean >
  host2/specs/koru-fixtures.json`. Generated, never hand-edited.

- `host2/kwire.py` — the reader/validator: refuses malformed nodes by
  name (unknown ctor, wrong shape, path included).

- `host2/quote.py` — the `quoteProg` twin (same tag table).

- `host2/fixtures.py` — the gate. **28/28 pass** on first run:
  `quote` byte-equality on all 8 corpus members, `eval` decision
  agreement, `kemit` — *our* quote feeding `kEmit`-as-data under *our*
  runK, matching `runK kEmit` under Lean — plus the **cc leg**: clang
  compiles the emitted C and the binary's exit code equals the
  literal (`5`, and `-3` via `0xFFFFFFFD`).

- `host2/spec.py` — own registry record (`HOST2`); the `koru.flow`
  toolchain note names the tree. Not a `module:` row — host/ resolves
  on its own sys.path and host2 is a separate root.

## Why this shape

host2 owns exactly one piece of logic — the evaluator. `kEmit` is
**data** loaded from the fixture file and run inside it; emission is
never reimplemented in Python. That's the invariant-layer contract at
substrate altitude: the Python evaluator is the handwritten bootstrap
whose job is to die when a machine-checked-compiled evaluator
replaces it — same role the C99 bootstrap plays for the compiler.

Witness discipline holds end to end: the fixture file is the only
thing that crosses (generated data); host2 reproduces decisions
independently; `kEmit` ran outside `native_decide` for the first
time and produced byte-identical C and identical refusals.

## What it does NOT claim

- The cc leg proves *executability*, not machine-checked-ness —
  clang is a stock compiler; the CompCert-acceptance of the emitted
  fragment is a subset contract, not a discharged proof that any
  particular binary is verified. (`zig cc` is the fallback path.)
- The corpus is still the declared 8-member one — `SelfHostingC99`
  at `∀ src` strength stays a Lean obligation; host2 witnesses the
  same corpus the theorem checks, nothing more.
- No `.k` surface, no oracle-fixture rows yet (asserted-leaf cases
  exist in the Lean fixtures but aren't named programs to dump —
  a recorded expansion path), no unquote.
- host2's `run.py` is a *witness*, not the semantics — if it and
  runK ever disagree, the Lean module wins and the twin is wrong;
  the gate exists precisely to catch that.

## Next honest rungs

- Subset growth: each new `emitC99` match arm ⇒ mirrored `kEmit`
  conjunct + corpus rows + regenerated fixtures — the gate scales
  mechanically.
- The harder bootstrap: an evaluator written *in the flow language*
  (so `kEmit` stops depending on host2 entirely) — that is the
  `H0 → H1` shape the plex chain established.
