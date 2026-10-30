---
type: frag
id: 0058
provenance: devin-cli
ts: 2026-10-30
tags: [koru, koruc, upstream, disjointness, permutation, quotient]
---

# 0058 — upstream pins landed, dispatch table, permutation proof

Follow-up to 0057's two rungs.

## Upstream report (koruc emitter holes)

Koru's convention is *tests are the spec* — a defect report is a
pinned regression test, not prose. Three tests added under
`tests/regression/000_CORE_LANGUAGE/020_EVENTS_FLOWS/` in the
`W:\src\koru` clone (uncommitted; the tree carries user work):

- `020_069_when_guard_on_union_arm` — `| sval v when g => X`.
  **Green at HEAD `5fb3807`** — the kdrv-era defect (capture and
  continuation dropped under `when`) is fixed for the produce shape.
- `020_070_arrow_expr_on_union_arm_discards` — `| sval v -> v * 2`.
  **Still broken**: deep-check accepts, the emitter lowers it to
  `_ = v * 2;` inside `.sval => |v|`, handler implicitly returns.
  Emit site: `emitter_helpers.zig:412` `bare_return_active` — the
  produce-step lowering only maps `->` to `return` on bare-return
  events; union arms fall through to the generic discard. Sibling of
  the already-pinned 020_067 (call shape), same missing case.
- `020_071_when_guard_pipeline_continuation` — `| sval v when g |>
  nxt(v)`. Refused KORU022 naming `bad` — the guarded pipeline arm
  swallows the following arms' scope, so the diagnostic names the
  wrong axis (`shape_checker.zig:1417`).

Session report at `friction/session-devin-union-arm-produce.md`
(same format as the earlier `session-devin-relay-probe.md`), with
three more friction rows worth upstreaming: `print.ln` truncates
>64KB outputs silently, `++` reads as a runtime concat it isn't, and
non-TCO `|>`-handler recursion makes stack depth payload-bounded.

## Dispatch table — the unordered fragment as data

`disjoint.py --table` emits `dispatch_table.sexpr`: every tor's arm
set with per-arm `(var (lo hi)…)` interval constraints, `fallback`
markers, and `(partial)` flags where the guard had clauses the model
couldn't reduce. The catchall verdict *is* the certificate: any
consumer may dispatch those sets in any order — or in parallel — as
long as fallback fires only when no guard holds.

Honest recount (the 0057 summary over-aggregated): of 76 catchall
sets, **70 are single-guard+fallback** — disjointness is vacuous;
the claim reduces to "fallback-last". Only **6 sets carry a real
multi-guard disjointness claim** (wmb1, wss, wen, wemv, wcls, wdk).
The 20 ordered sets split into 2 proven overlaps (priority dispatch)
+ 18 env-undecidable (loop bounds) — `w-wk`'s table shows the real
structure: disjoint k-points interleaved with priority pairs
(k==7∧pend≥0 vs k==7).

## Permutation falsification — passed

`permute.py` deranges every guarded arm inside the 6 multi-guard
catchall sets (rotation — no arm keeps its slot), leaves ordered/
trivial sets and fallbacks byte-identical → `transform.py` →
`koruc build` → same-wire race:

| wire | unpermuted claim | permuted output |
|------|------------------|-----------------|
| 906  | order unobservable in those sets | **byte-identical** (122173B) |
| 905  | same | **byte-identical** (228554B) |

If the interval analysis had a false positive, a moved arm would
change the emitted graph on any input where both guards can hold.
It didn't — the unordered-fragment claim is now both a proof
(interval disjointness) and a measurement (permutation invariance
on the real corpus).

The quotient picture this feeds: ordered first-match and unordered
value-dispatch are observationally equivalent exactly where the
constraints are pairwise disjoint; `dispatch_table.sexpr` is the
certificate format a quotient-map consumer (inet dispatcher, DNF
dispatch synthesis) can read directly.

Artifacts: `_scratch/kdrv/{permute.py, wir_perm.k, wirn_perm.k,
dispatch_table.sexpr, out_perm.txt, out_perm905.txt}` +
`../out_auth905.txt`.
