---
type: frag
id: 0041
provenance: devin-cli
ts: 2026-10-27
tags: [koru, host2, kemit, compcert, selfhost, machine-checked, uneg-divergence]
---

# 0041 — a real compiler in koru, and the first machine-checked leg

Two rungs landed together:

1. **kEmit widened from `return <int>` to a genuine compiler program** —
   a koru program (9 callables) that recursively renders closed int
   expressions to C99, interpreted by `krun --emit`.
2. **The CompCert leg is wired** — emitted C goes through CompCert 3.5's
   verified compile (`ccomp -S`, i386) then links and runs, so the
   observable (exit code) of machine-checked output is compared per case.

## The compiler shape (KoruEmit.kEmit)

`tests/200_emit/100_kemit/input.k` is no longer a bare expression. It is
a multi-callable koru program — declaration rows, guarded dispatch arms,
`|>` chains, nested continuations:

```
tor emit {src: program} -> string      # qnode 30 shape gate
tor render {e: expr} -> string         # recursive walk over the quotation
tor op-str {op: int} -> string         # op-number -> C symbol table
tor join4 / paren-neg / wrap / ident / tag-num / idnum
```

`render` dispatches on the quoted expression tag (8=lit, 10=bin, 11=un),
recurses through `|>` continuation steps on the `kids` cell fields, and
refuses every unrecognized shape by dispatch miss. `emit` validates the
`program` quotation (single graph entry, no args) then
`render |> wrap` produces `int main(void) { return <expr>; }`.

`emitC99` in KoruDialect.lean was widened in lockstep: closed exprs over
lit | bin{+,-,*,/,%} | neg, nested. `ktdiv`/`ktmod` already truncate
toward zero — identical to C `/` `%` on ints — so the rendering is
observationally exact, not approximate.

The fixpoint `SelfHostingOn emitC99 emitCall renderC99 koruEmitCorpus`
still proves `runK kEmit (quote src) ≡ emitC99 src`, now over **19**
corpus members: 8 accepts (int, bin, nested, div, mod, uneg, unested,
plus the wire-routed `emit-neg-lit`) and 11 named refusals (entry, args,
graph arity, var, op, unop, cond, child-callable, float, str, thunk).

## The unary-neg divergence — a real bug the widening exposed

Koru surface `-4` is **not** a literal: `parsePrimary` builds
`unary{negate}` unconditionally — negative integer literals are
*unspellable* in koru. korufe had been folding `-<int>` into `lit -4`,
a silent divergence from koruc that also corrupted the quotation (the
AST the emitter walks didn't match what the semantics would see).

Fix: removed the fold. `-4` now parses as `negate(4)` in korufe, the
printer emits `-(4)` for `un neg (lit 4)`, and `kValSrc`/`kExprSrc`
panic on negative literals rather than emitting unspellable surface.
The corpus member that *is* a negative literal moved to
`tests/900_wire/000_emit_neg_lit` — a wire-only row asserting the
emission layer still handles `lit -3` when it arrives as data.

This is the kind of thing the authority-parity discipline exists for:
the refusal axis was inside our own frontend, not the semantics.

## The CompCert leg

`assembly.json` gained a realized `compcert` row: docker
`ysli/compcert@sha256:4ecfb4eb…` (CompCert 3.5, i386) runs
`ccomp -S` — the verified compile to i386 assembly. The image carries
no i386 link runtime, so a second declared image (`ccrun-build`,
i386 gcc 12.2.0, pinned by digest) assembles, links, and executes.

The `.ccv` gate leg per accepted emit case:

```
emit.c --(ccomp -S)--> emit.s --(i386 gcc)--> exe --> run
  exit code == claim expect's low byte
```

The verified span is honestly bounded: **CompCert's correctness theorem
covers C→assembly. The assemble/link/run step is unverified gcc.** The
catalog rows say exactly this — `verified_span` on the compcert row,
and `compcert_amd64` stays deferred (the image targets i386 only).

## Observation note: two exit-code views

`tests/200_emit/006_accept_uneg`: clang/cc leg reports `exit
4294967292` (Windows DWORD), the i386 ccv leg reports `exit 252` (shell
low byte). Same `-4`, two observation functions — both recorded in the
leg output rather than normalized away, since the wire's `expect` is
the value and each backend's observation regime is its own row.

## Status

- `host2.check`: **215 pass / 0 fail / 0 skip** — every accepted emit
  case now runs through clang *and* CompCert→i386.
- `lake build Host2` clean; companions pin the widened quote table.
- Still corpus-bounded (`SelfHostingOn`), still interpreted
  (`krun --emit`), still a closed-expr subset. The universal rungs —
  `SelfHostingC99` at ∀-src, a koru-spelled frontend, `cref` stdout
  refinement — remain named-deferred in `spec.py`.
- The seed→H0→H1→H2 loop: kemit is a koru-spelled compiler evaluated
  under a *handwritten* evaluator whose output now passes a
  machine-checked backend. H1 is still missing: nothing koru-spelled
  has executed the compiler itself as compiled code.
