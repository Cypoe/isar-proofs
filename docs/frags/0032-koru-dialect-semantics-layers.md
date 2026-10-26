---
type: frag
id: 0032
provenance: devin-cli
ts: 2026-10-27
tags: [koru, dialect, flowdialect, korudialect, flowkernel, lean4,
       fuel-mono, grammar-layer, self-host-obligation, scaffold]
---

# 0032 — Koru dialect: real eval semantics + declared layer registry

## What landed

Two new verify-only modules and a host-side mirror, opening the Koru
dialect story proper (the frag-0030 codec rung's named next step):

- `src/ISAR/FlowDialect.lean` — the flow semantics. A faithful port
  of `w:/src/koru/verify/semantics/FlowKernel.lean` onto the
  `FlowView` wire grammar (`KVal`/`KExpr`/`KArm`/`KFlow`/`KCallable`/
  `KProg`): `runK` (the fuel-stepped call machine: invoke/flow/loop/
  dispatchTag/dispatchBare/armTry/armWalk), `evalKProg`, `KOracle`
  (asserted thunk leaves — the declared trust boundary), and
  `runK_mono` (fuel is a resource cap, never a semantics change —
  same single-induction proof shape as the reference). 15
  `native_decide` fixtures pin decided results AND refusals: arith
  chain, tagged dispatch, when-skip, no-match, type error, div-zero,
  oracle hit/miss, bind-on-void, catchall-in-bare, void+arms,
  terminal-void, a `#label` jump loop, rational float add, zero
  denominator.

- `src/ISAR/KoruDialect.lean` — the dialect as declared layers:
  `KEncoding` (codec + round-trip law — realized via FlowView),
  `KGrammar` (`wfProg`, the decidable static walls: entry/head/
  invoke resolution, `jump` names its enclosing `preLabel`),
  `KSurface` (`.k` parse — total refusal, declared-not-realized),
  `KBackend` (`koruC99` row — total refusal). `koruLayers` is the
  instance; `SelfHosting`/`SelfHostingC99` state the compiler
  fixpoint at full strength (refusal agreement included) with a
  productivity conjunct so the claim can't be vacuous.

- `host/koru/` — the declared host mirror: `encoding.TAG`/`BINOP`/
  `UNOP`/`BUILTINS` tables (the wire format as data), `grammar.
  WALLS`/`DYNAMIC` (which refusals live at which layer), `syntax`,
  `targets` (c99 row), `spec.KORU_FLOW` — all unrealized legs refuse
  with `NotRealized` naming the leg; no second evaluator or codec
  is written (the Lean module is the semantics — witnesses stay
  independent). `toolchain.json` gains a `koru.flow` dialect row;
  `host/specs/dialect-koru.flow.json` is the contract spec.

## Declared divergences (wire-level choices, each a refusal not a guess)

- Wire floats `float n d` are exact rationals, not IEEE: `asKRat`
  normalizes denominators positive and refuses `d = 0`; `/` refuses
  a zero quotient denominator; `%` on floats refuses outright.
  Documented in the module header — the walker's `fmod` has no
  honest rational analogue on unnormalized pairs.
- `Int` unbounded (same bound as the reference kernel — no i64 wrap).
- `evalKProg` is oracle-free by default; asserted leaves are an
  explicit `KOracle` argument.

## What it does NOT claim

- `FlowEvalCongruent` is stated, not discharged: on every `TTerm`
  OperEq-equal to `encProg p`, a hypothesized `iskEval` must agree
  with `evalKProg` — refusals included. `flowEvalDialect` shows the
  discharge: evaluator + result decoder + congruence yield a real
  `Dialect` with `Obs = Option KResult` (noncomputable — the decode
  picks `Quotient.out`, and the congruence is stated over ALL reps
  precisely because `out` picks one).
- No `.k` parser, no C99 emitter, no compiler-as-KProg — the rows
  exist so their refusals are named.
- The port is faithful to the *reference kernel*, which is itself
  checked against `comptime_eval.zig` — that chain of custody is
  the reference kernel's, restated here, not re-audited.

## Why this shape

The invariant-layer contract at dialect altitude: encoding and
grammar are realized where proofs exist, surface and emission are
declared with refusal paths, and the two expensive rungs (eval
congruence, self-host fixpoint) are stated as propositions whose
discharge shape is already written — obligations, not vibes.
