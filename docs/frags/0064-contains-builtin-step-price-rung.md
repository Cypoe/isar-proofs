---
type: frag
id: 0064
provenance: devin-cli
ts: 2026-11-18
tags: [koru, host2, kemitp, builtin, contains, performance,
       arena, byte-identity]
---

# 0064 — `contains` builtin: membership becomes one step; 60K-node
stress 55s/40GB → 1.3s/767MB

## What landed

`contains(hay, needle) → bool` — a `strstr`-shaped additive
string builtin — landed in all five lanes, same pattern as the
`chars` family (frag 0060):

- `FlowDialect.evalKBuiltin` (`String.contains`; refuses non-str
  args like the rest of the table)
- `host2/src/krun/eval.c` `kbi` (`strstr` on flattened ropes)
- `host2/src/korufe/lower.c` builtin whitelist
- `KoruProgEmit`'s emitted `kbi` runtime (`extern char *strstr`
  added to the shared `prelude` extern block — the freestanding
  lane declares libc prototypes, no hosted headers, so the
  declaration is data in the prelude string)
- `KoruEmit.kWirWbl` (wire-name validation)

`ep-mems {set,name}` — the `|a|b|`-sentinel membership check used
by reachables (`ep-gr*` closure) and the emit scans
(`ep-gfw`/`ep-gbo`) — is now a single `contains` invoke.  The
`ep-mi`/`ep-mo` char-loop tors are deleted; the spelled-out
per-character scan was the last O(len)-steps-per-lookup site.

Additive in the gate sense: programs that decided before decide
identically (the set string and frontier logic are untouched —
only the membership primitive changed); the only new accepts are
programs that call `contains` directly, which previously refused
at the whitelist.

## Why — pex-lane syndrome in miniature

Frag 0060's frontier rewrite fixed *asymptotics* (O(depth·G²·L)
→ O(G²·L) once) but not the *step price*: every char compared
by `ep-mi`/`ep-mo` was a full callable invoke, and the compiled
repr retains an env frame + `Res` per invoke (frag 0055's arena,
no reclamation).  At G=1400 callables the closure + emit scans
were ~150M char-steps × ~250B retained ≈ ~40GB.  The builtin
makes each membership check one retained step.

## Measured (actual output)

```
kwir        41s (pre-0060) → 1.4s (frontier) → 0.33s
big (60K-node 4×-kchain composed program, 4.4MB quote):
  ~55s / ~40GB peak (frontier) → 1.3s / ~767MB peak
  output 5,408,947B vs emitProgC 5,408,946B
  — diff: one trailing empty line, content identical
host2.check: 1003 pass, 0 fail, 14 skip
  (all 10 kp.* legs green incl. compiled-vs-gen byte identity on
   kast/kchain/kemit/klex/klow/ksexp/kwir; skips are the
   documented interpreter-stack axis + witness.flowcheck, which
   needs a koru toolchain this machine lacks)
```

~43× faster and ~52× less resident memory than the frontier-only
run — better than the ~4s/~3GB estimate, because the estimate
assumed the remaining builtin-call overhead would dominate; at
one step per check the dominant cost is the emit walk itself.

## Trade-offs and the remaining walls

- The residual cost is now the emit walk's own per-step
  allocation (decl traversal, `dc` fold — frag 0060's O(S·D̄)
  fold is still spelled per node) and the O(G²·L) scan count in
  `ep-gfw`/`ep-gbo`.  Both are now *bounded by* retained
  allocations, so the next wall is positional set repr
  (`push`/`set` on arrays — still absent from `KBinOp`, still a
  named axis) or arena reclamation in the compiled repr, not
  more string builtins.
- `contains` semantics are byte-level substring (`strstr`), not
  a set abstraction — it works here because set members are
  `|`-sentinel-wrapped, so `|x|` cannot substring-match `|xy|`.
  Callers must keep the sentinel discipline; the builtin does
  not enforce it.
- The `ep-gv`/`dc` pair still cannot memoize (`{n',text}` pairs
  are not expressible — frag 0060's composite-return wall) —
  unchanged.
- For the eventual koru-written production compiler this is the
  rung that matters more than the asymptotics: supercompiled
  self-interpretation inherits this repr's step price, and
  spelled-out char loops are exactly what a supercompiler cannot
  amortize (each is a distinct control state).  Named builtins
  are the honest boundary — the dialect declares what the
  runtime implements natively.
