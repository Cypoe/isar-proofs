---
type: frag
id: 0033
provenance: devin-cli
ts: 2026-10-27
tags: [koru, self-host, fixpoint, quotation, emitC99, comPcert-subset,
       lean4, corpus-witness]
---

# 0033 — Koru emit: quotation + realized C99 subset + witnessed fixpoint

## What landed

The `SelfHosting` obligation's first discharged rung — a compiler
written in the flow language, checked to agree with an independent
emitter, refusals included:

- `src/ISAR/KoruEmit.lean` — three artefacts:
  - **Quotation** (`quoteProg : KProg → KVal`): the same tagged
    structure as `encProg` (tags 1–31) materialized as wire
    *values* — `cell [("tag", int), ("kids", arr)]` nodes, named
    pairs, `arr` lists — so a compiler program navigates its source
    as data with `field`/`index`/`len`/`eq`. This is the calling
    convention: `emitCall` presents `src` to `comp` as a quoted arg.
  - **`kEmit`**: the emission logic *as a `KProg`* — one bare `emit`
    callable whose expr shape-checks the quoted source (tag/length/
    name navigation, each check mirroring an `emitC99` match arm)
    and concatenates the C text. Refusal agreement is structural:
    failed navigation produces `none` exactly where the reference
    match fails, not by assertion.
  - **`koru_emit_fixpoint`**: `SelfHostingOn` — `SelfHosting`
    restricted to `koruEmitCorpus` — discharged by `native_decide`
    (fuel 64): `runK` of `kEmit` on every corpus member equals
    `emitC99` — accepted C text byte-for-byte, all seven refusal
    shapes `none`.

- `emitC99` in `src/ISAR/KoruDialect.lean` — the `koruC99` row's
  first realization. Declared subset: a single-entry graph
  `[("main", .bare (.lit (.int i)))]`, entry `main`, empty args →
  `int main(void) { return i; }`. The emitted fragment is deep
  inside the **CompCert-accepted** C subset (no VLA/`_Complex`/…)
  so the machine-checked leg `KProg → C99 → CompCert → machine
  code` stays checkable end to end — per the standing correction
  that the backend must produce machine-checkable C, not merely
  C-flavored text.

- Two additive builtins in `FlowDialect.evalKBuiltin`: `len`
  (`arr → int`) and `intToString` (`int → str`, decimal). A
  compiler program must inspect list lengths and render integers,
  and the wire had no other way. Strictly additive: previously
  deciding programs decide identically; only previously-refusing
  calls now decide. Documented in the module header + three
  `native_decide` fixtures (decide + wrong-type refuse).

- Host mirror updated honestly: `koru.flow` row, spec, and
  `targets.emit` now say the C99 backend is **realized (subset) in
  Lean** — the host refusal no longer claims `emit = fun _ => none`;
  it refuses to *reimplement* (independent witnesses), naming where
  the realized emitter lives.

## What it does NOT claim

- `SelfHostingC99` stays stated at **full strength** — the `∀ src`
  discharge is the compiler-correctness theorem, a later rung. The
  corpus check is the honest witness, same discipline as the
  corpus-facing FlowCheck leg.
- The subset is tiny by design: one program shape, one emitted C
  skeleton. Growth is mechanical (more match arms on both sides,
  same agreement discipline); the refusal contract is the point.
- No string-payload emission: the wire has no char-level ops to
  C-escape safely — the escape row is a recorded obligation.
- No `unquote` round-trip: `kEmit` navigates the quotation
  directly; `unquote` is only needed for host tooling.
- `FlowEvalCongruent` (TTerm-resident evaluator) is untouched —
  still the other stated obligation.
- No handwritten C bootstrap exists yet — `kEmit` runs inside
  `runK`, i.e. the self-reference is evaluator-level, not yet a
  `seed → H0 → H1 → H2`-style chain.

## Why this shape

The fixpoint's hard part is not the subset's size but the
agreement discipline: `comp`-as-data (`quoteProg`), `comp`-as-program
(`kEmit`), an independent reference (`emitC99`), and a finite check
that makes the agreement *checked* rather than believed — the
Futamura shape at honest scope, and the pattern every subset
extension inherits.
