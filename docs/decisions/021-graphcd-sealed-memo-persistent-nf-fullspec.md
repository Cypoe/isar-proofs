# 021 — graph.cd: sealed per-round memo + persistent NF marks → full-spec feasible

Follow-up to 018/020. The full-spec `graph.cd` blocker is removed; the
mechanism is exactly what `HeapDev.HDev` models.

## What changed (host/graph_runtime.py)

1. **Seal**: after `cd(i)` produces `out`, write `_cd_memo[out] = out`
   in addition to `_cd_memo[i] = out`. This is `HDev`'s `insert o D₁`:
   a node reached again through `repr` in the same round returns its
   result — residual redexes in `out` are contractum-born and belong to
   the next round. Before this, a second visit re-developed `out`
   (over-development, `cd(cd t)`-ish): sound by `Join` but not `cdIter`
   and it wasted work.

2. **Persistent NF marks**: `cd` now populates `self._nf` (the set
   `step` already maintains). Rule: in the non-redex `app` clause,
   mark `out` iff `_nf[cf] ∧ _nf[cx] ∧ ¬isRedexR(out)`. Marked nodes
   are skipped by `cd` forever (never cleared per round).

   Soundness: `_nf[i]` ⟹ readback(i) is NF ⟹ every descendant rep of
   `i` has NF readback ⟹ none can ever be a redirect source ⟹ `i`'s
   readback is frozen ⟹ `cd(i) = i` permanently. This is the honest
   persistent-memo subset: only the frozen readback carries across
   rounds.

   Two pitfalls found empirically (first version produced a fake
   fixpoint at round 57 — caught by decode mismatch):
   - `cf == f` is NOT proof of NF: `f` may resolve to a sealed result
     whose readback has residuals. The mark must be hereditary on
     `_nf`, not on pointer equality.
   - `app nf nf` can still be a redex: `cd(f)` may produce a redex
     head (e.g. `I norm → norm`), so `app norm x` is live. Hence the
     `_is_redex_r` resolved-head guard.

## Evidence

- Full-spec `pathOf` query (previously hours-scale): ~10–12k honest
  cdIter rounds in ~2.5s after ~5s import; result dag 40 nodes, 0
  redexes, decodes correctly for all 14 queries.
- `routines_x86_64_win64_cd` probes: `graph.cd=N` now equals the native
  mirror's round count on every probe — the documented "graph.cd can
  report FEWER rounds" over-development is gone (the seal).
- xdu_gate 73/73, observational_suite, graph_congruence green.

## Gate status

- spec_term now runs graph.cd on the FULL spec (projection removed);
  G9a registered in toolchain.json obligations.
- G9 proper (specialize → regenerate emit(R)) remains open; the spec is
  now consumable AND the executor scales — both preconditions are in.

## Open (Lean)

- `HDev_total`: existence of a derivation needs a termination measure.
  The naive `tsize (heapUnfold h i)` fails — sequential clauses recurse
  in grown heaps where redirects make readbacks non-monotone. Real
  work; the host's termination is meanwhile gated empirically.
- `HDevChain`: round parity ↔ `cdIter n`. With the seal the host is
  exact `cdIter` per round, so the chain should be provable per-round
  once totality lands.
