---
type: frag
id: 0038
provenance: devin-cli
ts: 2026-10-26
tags: [koru, host2, ported-corpus, tu-split, lean-companions, oracle-leaves]
---

# 0038 — real koru programs ported, host2 split into TUs + Lean companions

## What changed

Three real koru programs live in `host2/specs/ported/<name>/input.k`
— folder-per-example, matching koru's own `examples/` convention —
each with a `cases.json` catalog carrying its entries and oracle
leaves (bend-style: several cases against one file, effects as
declared data):

- `lantern` — w:/src/koru's real example, `describe(room)` +
  `cond(expr: room)` spelled verbatim; the foreign tors (`cond`,
  `print-ln`) become `tor` decls + `cases.json` oracle leaves —
  effects enter through the wire's declared leaf boundary, not
  hidden host calls. Exercises tagged dispatch (then/else) and a
  `|>` chain: `describe(r): d |> print-ln(d) |> delve()`, where
  the retbind `d` threads through the chain.
- `greet` — minimal multi-case: two entries over one file.
- `bench` — recursive `fib` + `sum` guards, fuel-bounded.

`check.py` iterates every `ported/*/cases.json` plus `corpus/`
and runs `koruc -c` per ported file (path declared in
`realizations.json`). **119 pass / 0 fail** — real koru programs
parse, lower, eval, and agree with the authority.

## The `|>` honest shape

Koru surface `|>` chains are *unconditional residue* (ast_printer:
`branch.len==0 && !catchall`); the wire cannot spell an unnamed
arm — `dispatchBare` refuses unnamed/catchall arms outright
(koru's own FlowKernel.lean says the same). Subset decision, now
gated: a `|>`-derived arm lowers to the decorated name `_chain`.
Bare results run it unconditionally (koru-faithful); a tagged
result skips it and the wire refuses — chains over tagged
producers are a named gap, never flattened. `krun/eval.lean`
pins this with `native_decide`: `(tag _chain)` under a bare
result binds the payload and walks the node.

`|` rows after a `|>` step refuse — koru scopes them by
indentation, an axis korufe doesn't track; refusing beats
guessing the column.

## The implementation split

`korufe.c` (2100 lines) → `src/korufe/` translation units:
`util` (alloc/Buf) · `lex` (tokens) · `parse` (surface→C-AST) ·
`astio` (canon ast.json read+write) · `lower` (AST→claim +
declared-contract checks) · `main` (the two legs), all sharing
`korufe.h`.

`krun.c` (1850 lines) → `src/krun/`: `sx` (wire grammar) ·
`wire` (total decoders) · `eval` (the runK twin) · `quote`
(the quoteProg twin) · `main`, sharing `krun.h`.

Same compiler, same `-std=c99 -Werror`, same binaries — check.py
builds the TU lists; the monoliths are deleted.

## Lean companions

Every `.c` has a `.lean` beside it, compiled by the new `Host2`
lean_lib (`globs = ["korufe.+", "krun.+"]`, `needs = ["ISAR"]`).
Two levels of pin:

- `krun/eval.lean` imports `ISAR.FlowDialect` and carries
  `native_decide` theorems — the call-tag numbering, arm-dispatch
  order, and the `_chain` contract are checked, not narrated.
- `krun/quote.lean` imports `ISAR.KoruEmit` and pins the C
  functions to their Lean twins by name (qnode/qpair/tags).
- The rest are structured contracts-as-docstrings: token tables,
  arm grammars, refusal axes — data the C file must honor, kept
  compilable so drift fails the build.

`lake build Host2`: 12 modules clean.

## Honest position

- Oracle leaves are the trust boundary, declared in each
  `cases.json`; the ported programs are real koru, the *effect
  implementations* are leaf assertions — same contract as the
  generated corpus.
- The companions pin structure + the load-bearing semantics;
  they are not (yet) a proof that eval.c *is* runK — that
  witness stays the byte-for-byte claim check vs the Lean model.
- The split is mechanical: section-banner boundaries, no
  semantics moved. If a TU ever grows its own logic the
  companion is where the twin must be written first.

## Verify

`python host2/check.py` → 119/0/0 · `lake build Host2` clean ·
`koruc -c` on all ported files · battery + spec_project synced.
