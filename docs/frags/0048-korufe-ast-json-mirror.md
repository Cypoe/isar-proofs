---
type: frag
id: 0048
provenance: korufe --ast-json + check.py kwj legs
ts: 2025-06-09
tags: [korufe, ast-json, mirror, authority, gate, interop]
---

# korufe --ast-json: the C lane mirrors the authority's readable AST

`korufe` gains `--ast-json FILE.k` — the *readable* authority
schema (`{module_annotations, items}`, the same envelope `koruc
--ast-json` emits) as a second serialization next to the existing
canonical output. The `kwj` gate legs race it against
`koruc --ast-json` on every corpus `input.k`: **44 files, deep-equal
JSON** modulo the path-dependent `location.file` (koruc echoes the
argv path; the basename is the portable part).

## What the mirror actually required

The readable view is a *semantic projection*, not a printer:

- **Positional arg names** — a probe showed koruc writes an
  unlabeled arg's `name` as its *value text* (`f(g())` →
  `name:"g()"`). No decl lookup, no pun detection: named keeps the
  name, positional echoes the value.
- **Per-cont locations** — `ArmD` gained `line` (the `|`/`|>`
  token's line); conts previously inherited the flow's line.
- **Retbind is lossy in the view** — anonymous chain conts emit
  `binding: null` upstream even though korufe's model keeps the
  name (`Inv.retbind`). The canon stays the lossless document.
- **Expression printer conformance** — the authority's rules are
  derivable and finite: outermost binary bare, nested wrapped;
  `!(`/`−(` operands wrapped; field/index bases wrapped only for
  literal/operator bases (`s.kids[0]` bare, `({x: 3}).x` wrapped);
  `label_jump` drops its args; a `-&gt; if(c) a else b` produce is
  modeled as an `["if"]` invocation.
- **Synthesized `__type_ref`** — branch payloads carry the declared
  payload type as a pseudo-field; `parse.c` now captures `btypes`.

## Why two evidence boundaries

`kw` (rows) and `kwj` (JSON) now prove different things:

- **kwj** proves the *C frontend* emits the same authority-facing
  document as zig — this is the interop lane: JSON is the shared
  contract between the Z authority, the C+Lean lane
  (`korufe → canon → --lower → krun`), and the typed-koru lane.
- **kw** proves the *koru-spelled* parser (kast) sees the same
  structure — rows are the internal wire the compiled program
  consumes via stdin cells. The row normalizer re-derives spans
  from raw-text fields; the JSON race needs no such re-derivation
  because both sides emit the same schema.

They are not redundant: a JSON-only race would leave the row wire
unchecked; a row-only race would leave the C lane's authority
contract unproven.

## Trade-offs

- `zexpr` re-derives the authority's *serialization* rules — not
  ported zig code (the witness stays zig; conformance is at the
  output contract). If upstream changes its printer, `kwj` fails
  loudly by design.
- The view is one more schema to maintain — kept deliberately
  separate from the canon writer, which remains the lossless
  `--lower` input.
- Gate: `host2.check` 696 pass / 0 fail / 0 skip.
