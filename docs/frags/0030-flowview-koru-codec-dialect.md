---
type: frag
id: 0030
provenance: devin-cli
ts: 2026-10-17
tags: [isar, lean4, dialect-kernel, koru, flowview, codec,
       round-trip, terminal-kernel, verification-path]
---

# 0030 — FlowView: a Koru-flow `Dialect` prototype with a proved tagged-tree codec

## What landed

`src/ISAR/FlowView.lean` — a Koru flow-program view into the `TTerm`
substrate, following `TRSView`/`BytecodeView`:

- **Grammar.** `KVal`, `KBinOp`, `KUnOp`, `KExpr`, `KArmNode`, `KArm`,
  `KFlow`, `KCallable`, `KProg` — the wire-expressible subset of the
  Koru flow-walker's program shape (values, expressions, arms with
  branch/catchall/bind/cond/node/continuations, heads, callables,
  whole programs with graph + entry + args).
- **Codec.** `encX` encoders into `TTerm` (`I`/`K`/`S`/`app` only):
  natural tags as right-leaning `I`-spines (`tn`), lists as `K`-headed
  cons cells with `S`-nil, data as `app (tn tag) (encList kids)` —
  tag/cons disjointness is structural (`K`-heads never parse as tags).
- **Refusal.** Fuel-bounded decoders (`decValF`, `decExprF`, …,
  `decProg`) return `none` on malformed shapes — refusal is a value,
  not a tactic. Fuel bound is the encoded tree's own size (`tsize`),
  the same "measured spine" accounting the emit leg landed.
- **Round trips.** `decProg_encProg : decProg (encProg p) = some p`
  and the per-level lemmas behind it, proved by induction on fuel —
  the IH must generalize over values because `KVal`/`KExpr` are
  nested through `List`, and `induction` can't run a nested recursor.
- **Dialect.** `Flow_Dialect : Dialect` with `Obs = TTermObs`
  (encoding tree modulo substrate `OperEq`), `eval = ⟦encProg p⟧`,
  `decode = trs_decode`, `preserves` reduced to
  `decode_raw_trs_encode` — the BytecodeView shape, honestly.

## What it does *not* claim

The `Dialect.preserves` field witnesses that decode∘encode is the
identity **on encodings** — i.e., the codec is an embedding of
`KProg` into `TTerm`. It says nothing about *evaluation*: whether
SKI-reduction of `encProg p` computes what the Koru flow walker
computes is unproved and unclaimed. That claim needs an ISK-level
evaluator — a `TTerm`-resident interpreter of the flow grammar — and
a congruence proof against `FlowKernel`. Deliberately deferred; the
comment block above `Flow_Dialect` says so in the file.

## Trade-offs taken

- **Quotient-free decode.** `decode` returns `TTermObs` directly
  rather than lifting a `decProg`-typed observation — the observation
  space is the substrate's own, so the lift's well-definedness is
  `trs_encode_decode_raw` for free. A `KProg`-valued decode would
  need `decProg` total on classes (it's partial — refusal is the
  point), or a quotient-by-decode-fiber construction that buys no
  theorem strength at this rung.
- **Fuel everywhere.** Decoders are `f`-bounded and `termination_by`
  is explicit (`decKidsOf`'s `mapM`-mediated recursion hides the
  decrease otherwise). `tsize` is the certificate shape: the fuel a
  program needs is a function of its own encoding.
- **`decNamedValP` split.** The `cell` arm's pair-decoder is a
  named def taking the value-decoder as an argument — not for reuse
  but because `decKidsOf_encList`'s rewrite must match the decoded
  term syntactically, and an inline do-block lambda unfolds into a
  `match`-form the rewrite can't see. Named decode arms are the
  proof-visible interface.

## Why it matters for the Koru path

This is the dialect-route prototype the verification plan calls the
N²→N move: once `KProg → TTerm` is a proved embedding with a refused
decoder, every emitter that lowers to the substrate inherits the
observational-equality backbone — congruence between emitters factors
through the shared observation instead of being proved pairwise.
Today's instance is deliberately weak (codec fidelity, not eval
congruence); the next rung is the ISK evaluator.
