---
type: frag
id: 0044
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, klex, emitprog, compcert, frontend-as-data, selfhost]
---

# 0044 — klex: a koru-spelled lexer, compiled through ccomp

The domain-expressiveness rung behind korufe-as-data: can a koru
program — over the vocabulary `emitProgC` already compiles — do
real frontend work? `kLex` is a lexer spelled in koru that scans an
`arr(int)` of char codes and produces token sexpr text. No new
builtins, no new value forms, no host-side logic: the host crosses
bytes↔int-array at the boundary (data crossing); the koru program
performs all scanning logic.

## The program

`kLex` (`ISAR.kLex` in `KoruEmit.lean`) is a real multi-callable
program — `peek`, `lex`, `digits`, `atom-end`, `main` — covering
whitespace, `()`, operators, decimal numbers, atoms, and malformed
input (explicit `(bad idx code)` token, not silent refuse). Output
is text produced by `++`/`intToString` — the wire needs no array
append, which the expression domain doesn't have anyway.

Surface shape (`901_klex/input.k`, generated): `[]const i64` array
params, ordered guard arms over a `#label` head call, `|> @call(...)`
tail invokes threading all state explicitly.

## Design constraint that fell out: state rides arguments, not env

First pass used `@label` jump-loops and refused on every non-empty
input. `krun`'s jump semantics re-enter the flow with new head-args
but **preserve the flow env** — loop state has to ride
head-args→payload→head-args, a single result payload. Packing
`{i, out}` into a cell is impossible: `KExpr` has no dynamic
cell-literal node (neither does the authority's `FlowKernel.Expr`).
Restructure: tail *invocation* instead of jumps — `|> @scan(...)`
with all state explicit in the argument list. Same semantics for a
per-char scan; recursion depth becomes the honest named boundary
(fuel row per case).

## Wire: `krun --args`

Cases carry `args` (a `chars` int-array) rather than a quoted
program — new `krun --args` mode prints the claim's entry-args cell
on stdout so the compiled binary reads the same stdin shape as
`--quote`. korufe's param-type reader was widened for koru's real
`[]const T` spelling (authority probe: `koruc` accepts; our witness
must too, nominal types are not kernel-checked).

## Conformance partition — named, not silent

klex claims use `@len`/`@intToString` — our extension builtins the
authority's FlowKernel cannot decide (its table: `as`, `intCast`,
`truncate`, `divTrunc`, `rem`, `mod`). Rather than failing
conformance, check.py now partitions: claims mentioning extension
builtins leave the FlowCheck corpus and are reported as
`witness.extension` — 9 claims, declared axis. `900_kemit`'s claim
still passes conformance only because it asserts `refuse`.

## Gate

`host2.check`: **466 pass / 0 fail / 0 skip** (was 402 at H2).

- `901_klex` authority (`koruc -c`), parse/lower/claim: all pass;
  expected values computed by `evalKProg`, never hand-written.
- `kl.build` (clang c99) + `kl.ccv` (CompCert i386) on
  `emitProgC(kLex)`; `gen.stamp.klex` binds the artifact to
  `input.k` by FNV-1a.
- 7 input rows × `kl` (clang binary ≡ interpreted `krun`) +
  `klv` (ccomp binary ≡ interpreted): token streams identical —
  e.g. `(1 + 22)` → `(lparen) (num 1) (op 43) (num 22) (rparen) `,
  `x$` → `(atom 0 1) (bad 1 36) `.

Two codegen nits surfaced and fixed in `KoruProgEmit`: no-bind arms
emitted unused `r`/`ee` params and prelude helpers (`k_field`,
`k_index`) are dead when the program lacks that expr form —
`(void)` marks in the emitted prelude/arm prologue, -Werror clean.

## Honest boundaries

- The lexer's token set is the claim wire's own grammar, deliberately
  — it is the first TU of a koru-spelled frontend, not a lexer for
  the full koru surface.
- `len`/`intToString` remain extension builtins — evaluated by
  `evalKProg`/krun identically but outside the authority's decidable
  table; `witness.extension` reports the count rather than hiding it.
- Recursion depth is input-bounded (one invoke per char); fuel rows
  per case name the boundary, `run_mono` keeps decided results
  honest.
- Compiled-vs-interpreted is still observational equivalence over
  the 7-row corpus — `∀ src` remains the G rung.
