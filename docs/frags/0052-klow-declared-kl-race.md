---
type: frag
id: 0052
provenance: ISAR.KoruEmit kLow + host2 check.py kl/kli legs + upstream literal decode pin
ts: 2025-10-29
tags: [klow, reify, ast-json, declared-data, string-semantics, authority, gate]
---

# klow declared: ISAR.kLow, 904_klow leaf, kl/kli races

`klow` is no longer a scratch draft — the surface program is
transliterated into `ISAR.kLow` (84 callables + `kLowDecls` in
`KoruEmit.lean`), the fixture generator emits
`200_emit/904_klow/input.k` and `specs/gen/klow.c`, and check.py
races both lanes across the corpus:

- `kl` — emitProgC-compiled klow (wide-stack build) fed
  `klow_flat(rows)` + source bytes must emit a document
  parsed-JSON-deep-equal to `korufe --reify`'s, with refusal
  parity.
- `kli` — the same program through the interpreted lane
  (`korufe --lower` → claim → `krun`).  Interpreter recursion per
  scanned byte stays the named trampolining axis (0047): the 5
  self-parse-size files skip, never fake.

Supporting races landed in the same run: `kw` (compiled `kast`
row wire vs `koruc --ast-json` on every corpus file),
`kr` (`korufe FILE` ≡ `korufe --reify - FILE` byte-identical),
`kwj` (readable ast-json), `kwc` (canonical ast-canon).

Gate: **881 pass / 0 fail / 5 skip**.

## Correction to 0051: where the decode lives

0051 said "`parse.c` — `unesc` decodes the upstream set".  That
was wrong in placement.  The authority's *AST* keeps the raw
token between quotes (`expression_parser.zig` dupe()s the slice
into `literal.string`; the canon writer prints it verbatim), and
the decode happens only when a literal becomes a *value* — the
upstream regression pins `print.ln("a\\\"b")` printing `a\"b`.

korufe now mirrors that split exactly:

- `parse.c` — `e->s` stores the **raw** token (`xstrndup`, no
  decode).  `astio.c`'s `literal.string` then matches the
  authority byte-for-byte on `\\`, `\"`, `\u00` spellings — the
  kwc race that caught all of this.
- `lower.c` — `str_val` decodes the upstream set (`\"` `\\` `\n`
  `\t` `\r`; unknown escapes keep both bytes) at the one boundary
  where a literal becomes a value: the `(str …)` wire atom.
  `bput_sxstr` re-escapes for the reader.

So three representations stay distinct and each layer is honest
about which one it holds: **source token** (raw, in the AST),
**runtime value** (decoded, in wire atoms and eval), **JSON
document bytes** (structural quotes are real `"`; payload
spellings are data).

`check.py`'s `parens_args` normalizer learned the same `\`-skip
lesson `kAstToArgEnd` did — `\"` inside a string token is data,
not a delimiter (that bug, not koruc, produced the divergent
`904_klow` arg span that started the hunt).

## What the transliteration pinned

- `kExprSrc` precedence fix — a `.cond` operand inside `.bin`
  now carries parens (`else x` greedily swallows a trailing
  `a ++ b`), and the then-branch too (`if c if … else …` has no
  surface reading).  Regenerated `902_ksexp` fixtures spell the
  same programs unambiguously.
- `koruStrEsc` — the inverse of the upstream decode set; serves
  BOTH the koru source printer (`kValSrc .str`) and wire
  `(str …)` atoms (`sxStrLit`), since krun's sx reader decodes
  the identical escapes.  `.str` values in `ISAR` decls are the
  decoded runtime values — same semantics as wire atoms and
  `emitProgC` C literals (whose `cstrBody` escapes independently).
- `klow_flat` — the declared text→six-int row projection lives
  in check.py as data; `KLOW_KIND`/`KLOW_SUB` tables spell what
  klow.k's dispatch arms spell literally.
- `904_klow` carries only the emit_prog row (`fuel:4000000`,
  `emit_args`); per-input rows+src derive at check time from
  kast's own wire — no second hand-encoded row set can drift.

## Trade-offs stated

- `.str` in ISAR decls = decoded value, not source spelling.
  Programs that want a literal `\\` in *source* can't spell one
  differently than the value's `\\`-escape — but the generated
  fixture never needs that distinction, and the surface file it
  emits round-trips through both frontends.
- `kli` skips on the 5 biggest files are a *resource* axis
  (trampoline depth), not a semantic gap: `kl` handles even the
  21 KB self-parse at wide-stack.  The named axis stays named.
