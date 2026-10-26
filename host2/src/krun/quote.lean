import ISAR.KoruEmit

/-! # krun/quote.c — the quoteProg twin, pinned

`quote_prog(Prog) -> Val` materializes `qnode 30`: the decoded wire
program re-encoded as wire VALUE so a compiler `.k` (kemit.k) can
inspect its own input — the `src` argument of the emit call.  This
is the calling convention of `krun FILE --emit SRC`: the compiler
is data, the C binary only interprets.

## Structure (mirrors ISAR.KoruEmit.qnode/qpair exactly)

- `qnode tag kids` = `cell [("tag", int tag), ("kids", arr kids)]`
- `qpair name v`   = `cell [("name", str name), ("v", v)]`
- `Option`: `none → node 23 []`, `some v → node 24 [v]`
- tag table = `encProg`'s (`FlowView`), tags 1–31 — the C side
  keeps the same numbering inline; any drift vs
  `ISAR.KoruEmit.quoteProg` is a witness bug, not a design choice.

## Function ↔ Lean twin map (declared)

| C                    | Lean                       |
|----------------------|----------------------------|
| `qnode/qpair`        | `KoruEmit.qnode/qpair`     |
| `quote_val`          | `KoruEmit.quoteVal`        |
| `quote_expr`         | `KoruEmit.quoteExpr`       |
| `quote_arm/node`     | `KoruEmit.quoteArm/Node`   |
| `quote_flow`         | `KoruEmit.quoteFlow`       |
| `quote_prog`         | `KoruEmit.quoteProg`       | -/
