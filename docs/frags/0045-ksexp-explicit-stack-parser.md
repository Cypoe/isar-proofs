---
type: frag
id: 0045
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, ksexp, emitprog, compcert, frontend-as-data, parser]
---

# 0045 — ksexp: the first parser-shaped flow, compiled through ccomp

The second frontend TU: `kSexp` validates and annotates the claim
wire's own grammar — `(`, `)`, atoms, numbers, op code points,
whitespace — and emits a span-tagged tree as text:

    (a (b c) d)  →  (seq (atom 1 2) (seq (atom 4 5) (atom 6 7)) (atom 9 10))

Still zero new builtins: `cond`, `index`, `len`, `intToString`,
`++`, ordered dispatch, invoke tails — the same vocabulary as kLex.

## The subset shaped the design twice

* **No pair-return.** Recursive-descent `parse-expr` would need
  `{tree, next-i}` back; the kernel cannot construct cells
  dynamically (neither can the authority's `FlowKernel.Expr`).
  But sexpr text is self-delimiting, so the parser is an
  **explicit-stack machine**: `depth` is the stack register,
  `(` pushes (`(seq ` + depth+1), `)` pops.  The call-stack a
  recursive parser would hide is declared data — the honest shape
  for a dispatch-driven calculus, and it composes with the
  invoke-tail state discipline kLex already established.
* **No `chr`/slice.** Nodes print as *spans* `(atom start end)` —
  like real parse trees carrying source locations; a downstream
  stage re-indexes the char array.  Numbers likewise `(num i j)`
  — kLex's value-folding stays downstream's choice, not baked in.

## Structure enforced, not just balanced

Four refusal shapes decided in-band as `(bad pos code)`:

- `x` — bare token at depth 0 → `(bad 0 120)`
- `)` — underflow → `(bad 0 41)`
- `(a) (b)` — second top-level form (`seen` flag) →
  `(seq (atom 1 2)) (bad 4 40)`
- `(a b` — EOF mid-list → `(seq (atom 1 2) (atom 3 4) (bad 4 -1)`

`need` is the sibling-spacing flag; `seen` enforces the
single-top-level-form contract the wire reader assumes.

## check.py generalized

`emit_args` was klex-specific; it is now a per-leaf mechanism:
an `emit_prog`+`emit_args` row carries `"gen":"<name>"`, the gate
derives `specs/gen/<name>.c`, and leg suffixes are the name's first
two letters (`kl`, `ks`, …).  Adding the next compiled component
is a generator row, not a check.py edit — the same
data-not-logic contract the rest of the tree keeps.

## Gate

`host2.check`: **537 pass / 0 fail / 0 skip** (was 466).

- `902_ksexp` authority (`koruc -c`), parse/lower/claim: pass.
- `gen.stamp.ksexp`, `ks.build` (clang c99), `ks.ccv` (CompCert
  i386): pass — `emitProgC(kSexp)` compiles through both toolchains.
- 8 structural rows × `ks` + `ksv`: compiled ≡ interpreted on every
  row including all four `(bad …)` shapes.

One real bug surfaced during generation: the `(op` emit missed its
closing paren — the corpus caught it (`902_ksexp_ws` expect
mismatch), fixed in `kSexpScan`'s op arm.

## Honest boundaries

- The parser is a structural validator/normalizer with span
  annotation — it does not lower to `KProg`/AST data (that needs
  pair-return or dynamic cell construction, a real kernel axis,
  not a spelling problem).
- `len`/`intToString` remain extension builtins; `witness.extension`
  accounts them by name.
- Recursion depth is input-bounded as in kLex — fuel per row names
  it.
- Corpus-bounded observational equivalence still — `∀ src` is G.
