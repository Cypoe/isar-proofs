/-! # korufe/lower.c — ast.json + case row → [flow-eval] claim

The quotient leg: canon AST plus the case row (entry/fuel/args/
oracle/expect) becomes the lower-layer wire claim.  Nothing here
is authored logic the wire doesn't decide — lowering is a total
map, refusal names the axis.

## Declared-contract checks (koruc parity at the lower boundary)

`DeclSeen` collects `tor` decls + impls first:

- decl exists → invoke arg names ⊆ params (PARSE006), arm branch
  names ⊆ declared branches (KORU021, incl. "available: (none)"),
  `=>` targets ⊆ enclosing impl's branches, `@label` must name the
  flow's own `#label`, entry args ⊆ entry params, oracle leaves:
  name declared, args ⊆ params, tag ∈ branches, impls can't leaf
- NO decl → implicit event, unconstrained (koru-legal: impls and
  invokes without tors are admitted); the wire decides at eval
- positional/pun args resolve through the callee decl: trailing
  ident of the expr must name a param (pun) or bind positionally;
  redundant `x: x` refuses upstream in parse

## Emission rules

- `=> b` (no payload) → `(ctor b (lit (cell)))` — named divergence:
  empty-cell payload, matching koru's `payload:{fields:[]}`
- unnamed `|>` chain arm → `(tag _chain)` — decorative name: bare
  dispatch runs it unconditionally (koru-faithful); a tagged
  producer skips it and the wire refuses — chains over tagged
  results are a named gap, not silently flattened
- decl-only names → `(def n thunk)` — the foreign-callable kind;
  their only behavior comes from `cases.json` oracle leaves
- head args must be named by the time they reach the wire
  (positional → decl-resolved names) -/
