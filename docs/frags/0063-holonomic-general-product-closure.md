---
type: frag
id: 0063
provenance: devin-cli
ts: 2026-11-07
tags: [koru, holonomic, closure, leibniz, lean, certcomp]
---

# 0063 — General-order holonomic product closure (m*n) in Lean

Second half of the general closure arc. `isHolonomic_add` (order ≤ m+n)
landed in `9eddc07`; `760a2ae` adds `isHolonomic_mul` (order ≤ m·n),
bringing Lean's coverage to the same generality as zig `certClosure`'s
`via=sum` / `via=prod` lanes — doubly solid, not just per-instance.

## Proof architecture (product)

- `iteratedDeriv_fun_mul` — the iterated Leibniz rule, proved by induction
  on the derivative order through `iteratedDeriv_succ` + `deriv_fun_mul` +
  Pascal's rule (`Nat.choose_succ_succ`). Mathlib has no
  `iteratedDeriv_mul`; the two-sided binomial-index reindexing is done by
  hand (`Finset.sum_range_succ'` + `C(n,n+1)=0` truncation).
- `prodJetCoord c d qf qg k (a,b)` — the `ℝ(X)`-coordinate of `(f·g)⁽ᵏ⁾` at
  basis pair `(a,b)`: `Σᵢ C(k,i)·(f⁽ⁱ⁾-coord at a)·(g⁽ᵏ⁻ⁱ⁾-coord at b)`,
  reusing `jetCoord` from the sum case.
- `m·n+1` vectors in `Fin(m·n) → ℝ⟮X⟯` are dependent (same
  `finrank`-cardinality argument via `finProdFinEquiv`), and the generic
  `isHolonomic_of_ratFunc_relation` clears denominators, extends off the
  finite bad set `lead.roots ∪ lead.roots` by continuity, and trims to a
  certificate.

## Honest caveats

- Order bound is `≤ m·n`, not minimal — same non-minimality the zig side
  documents (`frag-a-companion-basis-elimination-can-emit-a-nonminimal-ode`).
- `satisfiesODE` certificates are the input interface; the correspondence
  between a Lean `HolonomicCertificate` and zig's emitted `OdeCert` blob is
  the remaining un-mirrored axis (per-instance residual checking, the
  `CertCheck` lane, is where that correspondence gets receipts).
- Degenerate orders work out: `order = 0` forces `f ≡ 0`, so `f·g ≡ 0`
  takes the zero-law certificate — the empty jet basis degenerates the
  relation argument cleanly (no special-casing needed in the proof).

## Zig-side doc

`koru_std/sym.certcomp.kz`'s "Lean coverage is narrower" comment updated
to name `isHolonomic_add` / `isHolonomic_mul` — the stale wording was
introduced in the `23d3d57d2` honesty pass and was correct *then*.
