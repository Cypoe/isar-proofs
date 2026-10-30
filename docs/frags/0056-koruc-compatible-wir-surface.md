---
type: frag
id: 0056
provenance: devin-cli
ts: 2026-10-30
tags: [koru, host2, kwir, koruc, dialect, boundary, claim]
---

# 0056 — koruc pairing: the `_` respell, two dead arms, and the real dialect gap

Question asked: how does production koruc pair against the same
program? Answer measured, then made possible:

**Frontend numbers on `906_kwir/input.k` (the koru-spelled lowerer):**

| lane | time | result |
|------|------|--------|
| korufe parse → ast.json | 0.30s | 587KB internal ast |
| korufe --lower → claim | 0.06s | 122KB claim text |
| koruc --ast-json | 0.11s | 1.6MB ast |
| koruc -c | 0.76s | accept |
| koruc --deep-check (22 passes) | 39.8s | **pass after respell** |

**The first pairing refused.** `koruc --deep-check` on the original
wir.k: KORU021 — `| ws c` / `| dn _` labeled continuation arms on
tors that return **bare** (`-> i64`/`-> string`). korufe tolerates
label-shaped arms under bare dispatch — the label is cosmetic,
order + `when` decides. Production koru's shape checker treats
named branches on bare returns as the one-variant-union twin and
requires `| _` (produce sugar) or `: name` binds.

**The respell is observationaly invisible under korufe.** All 169
tors in wir.k return bare — zero tagged unions — so no arm label
is ever matched (tag dispatch needs a tagged producer). Rewriting
all 372 `| <label>` arms to `| _` preserves korufe semantics
exactly: `is_catchall` stays false, branch `"_"` is a literal tag
name, bare dispatch tries arms in the same order. Gate: 866/0/34,
906 graph byte-identical to `korufe --lower` (72,226 chars).

**koruc's checker found two genuinely dead arms.** `wops` and
`wpun3b` each had an unguarded arm followed by another unguarded
arm — unreachable even under korufe's ordered dispatch (the first
unguarded arm always wins). Deleted; SHAPE002 requires exactly
"guarded chain + one unguarded fallback" per level.

**It also exposed a latent emit bug.** `whco1` special-cased
`nm == "_"` → `" (arm catchall"` — written under the assumption
`_` is a catchall marker. korufe never produces is_catchall on
this surface (its parser refuses `|*` entirely); `_` is a plain
branch and the claim says `(tag _)`. The arm never fired before
because no corpus input used `| _` branches. Removed.

**What remains open:** koruc's emitted `main` runs
`koru_start_flow` — no stdin-cell driver, so the native-binary
race (koruc-compiled kwir vs emitProgC-compiled kwir_wiw vs
korufe --lower) needs a koru-side input adapter: either a cell
sexpr reader spelled in koru, or args embedded via the program's
own entry mechanism. That adapter is the next real boundary
artifact if the three-way race is wanted.

**The dialect gap, named:** korufe's `dispatchBare` is ordered
arms on bare results with cosmetic labels; koruc requires
declared outcomes for tag matching and pipeline binds for bare
returns. The witness surface now sits in their intersection —
which is precisely the fragment a disjoint-guard/inet analysis
would target: if arms are `| _` + `when` chains + one fallback,
order is already the only observable dispatch signal.
