/-! # krun/wire.c — total decoders Sx → AST, pinned

Mirror of FlowCheck's `sxVal / sxExpr / sxArmNode / sxArmFields /
sxArm / sxFlowBody / sxDecl / sxNamed / sxLeaf / sxThunkResult /
sxExpected / claimFields`: every decoder is total, malformed
structure is a rejection (0/NULL), never an approximation.

## Contract the C file upholds

- duplicate claim/arm fields refuse outright
- `(result refuse)` is an EXPECTATION marker only — a decided
  program under an expected-refuse claim is drift, and vice versa
- unknown claim fields refuse — including `(residue ...)`, which
  koru's emitClaim writes for the comptime-fold residue but the
  wire grammar does not carry
- `(arm ...)` fields: `(tag t)` | `catchall`, `(bind n)`,
  `(when e)`, `(node n)`, `(conts ...)` — an unnamed surface `|>`
  chain arrives already decorated `(tag _chain)` from korufe;
  wire.c does not invent names
- leaf result `(tag b [v])` | `(bare v)` | `(void)` —
  `KResult = {branch, payload}` exactly
- entry args and leaf args are `(name value)` tuples; the wire
  never sees positional args (korufe resolves them at lower) -/
