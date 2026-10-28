---
type: frag
id: 0047
provenance: host2 check.py kw legs + ISAR.KoruEmit retbind flows
ts: 2025-06-09
tags: [kast, race, retbind, nested-cont, authority, gate]
---

# kast: retbind widening + the wide corpus race

`kAst` now covers retbind chains (`| a |> f(x): b |> g(b)`) and the
race is no longer a 7-row fixture: **every `input.k` in
`specs/tests/` goes through the compiled parser and
`koruc --ast-json`, normalized to the same flat `(kind span …)`
wire — 44 files, row-identical, refusal parity both directions.**

`kw.200_emit.903_kast` is the self-parse: 14KB of koru surface,
1972 rows agree.  `kw.200_emit.900_kemit` (100 rows) carries the
retbind chains that were the last named subset axis.

## What changed

- **retbind**: `argnext`'s `)`-close routes through `postcall` —
  `: name` → `(rbind w we)`, then `|>` re-enters `arm-step`, so
  `: a |> : b` chains recurse.  The authority's `--ast-json` drops
  the bound name entirely (`binding: null` on a nested anonymous
  cont) — both sides derive `(rbind)` from source instead.
- **nested conts**: the normalizer walks `continuations`
  recursively — anonymous `|>`-chain conts emit step rows with no
  `(cont)` row; named nested arms (`| else |> if(g) | then => … |
  else => …`) emit full `(cont)`/step rows by location.  Same
  "prefix × own" shape as the fence's proposed walker — the
  position just arrived here first, on the witness side.
- **`["if"]` projection**: `-> if(c) a else b` is an invocation in
  the authority's schema but the else-tail isn't in args; the
  normalizer projects it to `(step expr v0 cle)` only when the step
  rides `->`.  `|> if(g)` keeps invoke shape on both sides.
- **byte frames**: the earlier `+2/+4` span drift was the
  normalizer mixing codepoint `find`/`word_end` with byte `loff` —
  everything now scans `src.encode("utf-8")`.  Zig's `[]const u8`
  locations and the int-array wire were byte-honest all along.
- **strings in `parens_args`**: `"` toggles an `ins` flag in the
  normalizer, matching `toargend`'s existing flag — a `"("` inside
  a literal no longer unbalances depth.  `toarrow`'s
  token-in-condition-strings blind spot stays a named axis and is
  symmetric on both sides, so identical mis-parses still race green.

## The resource axis this surfaced

emitProgC compiles each invoke to a C call — no tail-call
flattening — so `|>` chains and per-arm dispatch are mutual
recursion: ~7 frames per link, ~10 per arm, and the 14KB self-parse
blows the 1MB default stack.  The `kw` leg builds a second binary
with `-Wl,/STACK:67108864`.  Host-resource limit, not a parse
limit: fuel and decidedness are untouched.  The honest fix is a
trampolined/goto emission for intra-SCC invokes in emitProgC —
named, not yet taken.

## The s-expr verdict

The question was whether the s-expr wire bought anything over JSON
for the race.  **JSON was always sufficient**: `koruc --ast-json`
carries every node kind we need, byte-honest locations, and raw
source text for conditions/args/impl bodies.  The ~250-line
normalizer isn't a JSON tax — it re-derives spans from the
authority's *raw-text* fields, a semantic projection no format
change would remove.  What the s-expr wire bought is different:
it's the value domain the koru-spelled program natively consumes
(stdin cells, `xval`), and the flat `(kind i j …)` row text is
that wire serialized.  JSON answers the authority question;
s-expr is the internal representation.  They were never competing.
