---
type: frag
id: 0046
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, kast, ast-race, koruc, emitprog, frontend-as-data]
---

# 0046 — kast: koru-surface AST producer, raced against koruc

The first real AST producer and the first leg that races a
koru-spelled component against the authority's own machine:
`kAst` parses koru *surface* (`tor`/`=`/`|`/`when`/`->`/`|>`/`=>`/
`#label`/`@jump`/`import`) from a char array and emits flat node
rows `(kind i j …)`; `check.py`'s `*.kar` legs run
`koruc --ast-json` on the same source, project it into the same row
vocabulary, and diff.

Result: all 7 corpus rows agree — `ast race: N rows agree` for
decl/flow/ctor/imp/term/empty, and refusal parity on the malformed
source (`koruc` refuses; our rows carry `(bad i c)`).

## Why the race is honest

The authority's AST is a different *projection*: flat
`{type,name,location}` objects where conditions, argument values,
and impl bodies are stored as **raw source text**. Since the
authority itself keeps expression content as spans-of-source, our
row contract — structure + spans, no expression AST — is faithful,
not a shortcut. The normalizer (`ast_norm_rows` in `check.py`)
replays the same boundary conventions the scanner uses:
line/col → byte offset, `word`/EOL/token-delimited spans, leading
whitespace excluded, trailing included.

Two projections deliberately kept on our side:

- `(ret i j)` — the authority *drops* `-> T` return annotations
  entirely; the normalizer re-derives the span because a `->` on
  an accepted `tor` line is unambiguous.
- injected `import std/compiler` — dropped where the location's
  own text isn't an `import` token (the location keeps it honest).

## Bugs the gate surfaced (each a real boundary)

1. **PARSE006 positional args**: an `invoke` arm passed env vars
   `j`/`ne` positionally into `top` — they were only needed inside
   the `out:` expression, which evaluates in the *caller* env.
   Bare args must name a callee parameter.
2. **KORU100 unused bindings**: the authority requires `_` on
   discarded arm binds. `kArmSrc` now emits `_` when the bind
   isn't free in the guard or node (cont arms can't see it —
   matching koruc's own check).
3. **`k_field` collision**: a flow named `field` emits C symbol
   `k_field`, colliding with the prelude's `Val *k_field`. Renamed
   `field`/`field2`/`field3` → `fld`/`fld2`/`fld3`.
4. **`bputf` truncation in korufe**: `vsnprintf` into `tmp[128]`
   silently cut `(str "…")` expect values longer than ~122 chars,
   producing *malformed claims* — claims under ~40KB happened to
   fit, the two longest kast expects didn't. Two-pass sizing fix
   in `util.c`. A witness-side bug found by growing the corpus —
   the failure mode was "claim won't parse", not "value wrong".

## Status

`emitProgC(kAst)` compiles under clang `-Werror` and CompCert
(`ka.build`, `ka.ccv`); all `*.ka`/`*.kav` legs re-decide the same
rows; gate at 607/0/0.
