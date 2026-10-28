---
type: frag
id: 0050
provenance: korufe --reify + check.py kr legs
ts: 2025-06-09
tags: [korufe, reify, row-wire, kast, gate, koru-typed-lane]
---

# korufe --reify: rows → the internal document — the koru lane runs end-to-end

`korufe` gains `--reify ROWS.txt FILE.k` (`-` = stdin): the flat
`(kind off off …)` row wire that `kast` emits is reified back into
the same `Item` tree the C parser produces, then serialized with
`write_ast_json` — the `--lower` input. The `kr` gate legs race it:

    reify(kast(FILE.k), FILE.k)  ≡  korufe FILE.k

**44/44 byte-identical** — not claim-level equivalence but
*document-level identity*: the koru-spelled parser's output,
reified, is the same internal document the C parser emits. Rows
were always the real interchange; JSON (either mirror) is the
authority-facing interface.

## The lane this completes

```
input.k --kast(koru, compiled)--> rows --reify--> ast.json
        --lower--> claim --> krun
```

The koru-typed lane now reaches execution: parse in koru, rows as
the interchange document, lower in C. `korufe --lower` is
unchanged — reify emits the same document it already consumed.

## What the row wire actually carries (and how reify reads it)

Rows are byte-span-indexed — every field is `(kind lo hi)` into
the `.k` source. Reification is slicing + state machine:

- `(flw p nj)` + `(call ej ee)` — kind-3 vs kind-4 flows decided
  positionally: `ej == p` means the head call *is* the item name
  (`name(args)` → `impl_of:null`); `ej > p` means `name = call(…)`
  (`impl_of` = own tor).
- `(cont)` rows are always flow-level siblings — korufe's parser
  flattens same-line `| b` continuations to siblings, so reify
  does the same. (Upstream nests them — the kwc race is what keeps
  this honest: no corpus file carries the divergent shape yet.)
- `(step invoke)`/`(step jump)` disambiguate by *position*, not
  content: no open arm → head-level anon arm (`head: b |> step`
  links are flow-level siblings); arm expecting a node → the arm's
  own node; arm already invoke-stepped → anon chain link nested as
  `chain_tail->conts[0]` — korufe's exact nesting.
- `(rbind w)` does double duty, matching `parse_inv` + the chain
  rule: it sets `last_inv->retbind` *and* stages `pend` — the bind
  that rides forward into the next link's `bind` field.
- Expression spans (`(arg)`, `(cond)`, `(step expr)`, `(ctor)`,
  `(impl)`) are sliced, trimmed at the first top-level `|`/`=>`/`->`
  delimiter (to-EOL spans can carry a same-line tail), then
  re-parsed through `expr_from_src` — the same entry point `--lower`
  uses on its JSON fields. Re-parse → same KExpr → `expr_src_b`
  prints it identically → byte-identical documents.

## Refusal parity (named axes, all refuse identically)

- `(bad …)` rows — the wire's own refusal propagates.
- `(rbind)` dangling at `(cont)`/flow-end — korufe's
  "`inv: bind` has no continuation" refusal.
- `(cont)` after an anon-`>`-arm — korufe's "`|` dispatch under a
  `|>` chain needs indentation scoping" gap.
- `(step)` after produce/ctor/terminal — no koru spelling.
- Rows out of context (`(arg)` with no invocation, `(fld)` outside
  a decl) — structural refusal, not a guess.

## Trade-offs stated

- Reify targets *korufe's* document, not upstream's — the contract
  is "reify ≡ C-parse", and the C-parse ≡ zig is what kwc already
  proves. Two races, no redundancy.
- `expr_tail` trimming is a robustness guess for same-line
  `| a -> x | b` shapes the corpus doesn't carry — the axis is
  named, the race can't yet reach it.
- `(imp)`/`(ret)`/`(brd)` types take first-token / comment-stripped
  slices — qualified `a/b:c` paths and spaced `[] const T` spellings
  are unexercised; `[]const i64` (spaced inside the type) is handled
  by `span_type`, which stops only at `//`.
- The reifier lives in C inside korufe — a koru-spelled `klow`
  (rows→ast.json in koru itself) now has a complete oracle: emit
  what `--reify` emits, byte for byte.

## Gate

784 pass / 0 fail / 0 skip (44 kw + 44 kr + 44 kwj + 44 kwc + the
existing legs). Four evidence boundaries, one corpus: rows prove
the koru parser's structure, kr proves reification is lossless,
kwj/kwc prove the C lane mirrors the authority at both projection
levels.
