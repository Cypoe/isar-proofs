---
type: frag
id: 0037
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, koruc-parity, flow-corpus, wire-rows, refusal]
---

# 0037 — koruc-parity: generated `.k` is real koru, catchall goes wire-level

## What changed

Every generated `host2/specs/corpus/*.k` now passes `koruc -c` — the
full-language authority's own frontend, not just host2's parser. The
blast surfaced five real divergences; each is now either spelled
correctly or refused with the same axis koruc names:

- **Declared contracts.** koruc enforces `PARSE006` (unknown param on
  a declared tor) and `KORU021` (undeclared branch). Generated files
  now carry `tor tick {n: i64}` + `| go i64` rows; korufe's lower
  checks args ⊆ declared params and arm branches ⊆ declared branches
  — only when a decl exists; decl-less impls stay implicit events.
- **Punning.** `x: x` refuses upstream (`PARSE005`); the generator
  emits `sign(x)` when the value puns to the param, and korufe
  refuses redundant labels plus duplicate labels. Non-pun
  positionals resolve by index against the callee's decl.
- **One-variant unions.** `| go i64` alone under a tor refuses
  upstream (`PARSE003`); single-tag producers declare a second
  never-produced `stop` branch — honest union shape.
- **Bare `when <cond>`** is the guard spelling; glued `when(` is
  call-shaped upstream (silently unguarded → SHAPE002) and refuses
  here too.
- **`@builtin(...)`** is koru's builtin spelling — admitted inside
  expressions where `name(...)` is a call (KORU104). `kemit.k` now
  spells `@len`/`@intToString`, and `refused` in `KoruEmit.lean`
  moved from `(0).x` (call-shaped upstream) to `src.__missing` —
  same `evalKE → none` refusal, parseable surface.
- **`_` discard** for bound-but-unused arm bindings (KORU100).

## The honest casualty: catchall has no surface

`|* -> v` refuses upstream — a bare residual "takes no binding";
koru spells it `|* Meta e |>` (residual *record* through a
metatype), which the wire's catchall flag does not carry. So the
catchall semantics — tagged dispatch skipping it, bare dispatch
refusing on it — remain pinned by `FlowDialect` proofs and gated
through **wire rows**: `cases.json` rows that carry the generated
`[flow-eval]` claim verbatim (`"claim"`) instead of a `.k` file.
korufe refuses `|*` and `| *` at parse, naming the metatype axis
and the retired-deref glyph.

`flow-catchall-tag` and `flow-catchall-bare` are the two wire rows.

## Gate

`python host2/check.py` → **95 pass, 0 fail**: two fewer parse/lower
legs (wire rows), seven new parity probes (`| *`, `|* ->`, `x: x`,
one-variant union, `when(`, declared-param, declared-branch).
`ISAR.KoruEmit` rebuilds clean; `koru_flow_evals` still pins.

## Position

The generated corpus is now *actually* real koru — not a dialect
that resembles it. What still is not koru: nothing in `corpus/`.
The subset's declared surface boundary is koruc-parity refuse-first;
anything outside (metatype residuals, `! as`, `{{}}` interp,
top-level flows) refuses with a named axis, and `realizations.json`'s
parse row records koruc as authority.
