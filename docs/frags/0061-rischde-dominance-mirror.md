---
type: frag
id: 0061
provenance: devin-cli
ts: 2026-11-04
tags: [koru, lean, mathlib, risch, sym, mirror, decide-integral]
---

# 0061 — RischDE: the dominance argument the zig solver stands on

New module `src/ISAR/RischDE.lean` (103 lines, imported via
`src/ISAR.lean`) formalizes the polynomial-degree facts behind
koru's `std/sym:decide-integral` exponential Risch lane
(koru-quantity@2d376fe91, `koru_std/sym.certgen.kz`).

## What is proved

For `D, A, T, F : K[X]` over a field `K`, `charZero`, with the
linear operator `L(T) = D*T' + A*T`:

- `linDE_apply_natDegree` — `deg A ≥ deg D` and `T ≠ 0` ⇒
  `deg L(T) = deg T + deg A` **exactly**. This is the dominance
  step: `deg(D*T') ≤ deg D + deg T − 1 < deg T + deg A`, so the
  `A*T` term cannot be canceled. This is the fact the zig solver's
  "null is a proof" contract stands on — a failed top-down
  coefficient solve under the forced degree is a *proof* of
  non-elementarity, not a heuristic miss.
- `linDE_degree_forced` — `L(T) = F`, `deg A ≥ deg D` ⇒
  `deg T = deg F − deg A` (when `F ≠ 0`).
- `linDE_unsolvable_of_deg_lt` — `deg F < deg A` ⇒ no solution.
- `linDE_unique` — kernel of `L` is trivial ⇒ the solution, when
  it exists, is unique.

## Why this module

B3c (koru) generalized the exponential Risch lane from
`R' + G'R = F` to the cleared-denominator equation
`D*T' + (G'D − D')T = F*D²` with `D = gcd(d, d')` — Rothstein's
denominator bound. Both instances satisfy the dominance hypothesis
(`deg A ≥ deg D`; in the D=1 case `deg G' ≥ 0`), so one Lean
lemma covers both. The pole-counting half of the bound
(`ν_p(R) = ν_p(F) − 1`, simple poles unreachable) is stated and
used in zig but **not yet mirrored** — it lives over `RatFunc` /
valuations, a larger formalization surface, and is the honest next
gap.

## Trade-offs and refusals

- Only `natDegree` statements, not `degree` — the zig side reasons
  about `-1` (zero poly) via `degIdx`; staying in `ℕ` keeps the
  mirror faithful without a subtraction layer.
- `charZero` is assumed; koru's ground ring is `ℚ(i)`, so the
  hypothesis is satisfied at the use site.
- Imports are narrowed to the specific polynomial derivative /
  degree modules rather than root `Mathlib` — the root olean is
  not built in this toolchain cache, and narrow imports are better
  hygiene anyway.

Verification: `lake env lean src/ISAR/RischDE.lean` clean under
leanprover/lean4:v4.31.0 against the cached mathlib oleans.
