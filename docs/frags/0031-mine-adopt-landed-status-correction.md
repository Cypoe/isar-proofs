---
type: frag
id: 0031
provenance: devin-cli (session review + run of host/mine_adopt.py)
ts: 2026-10-21
tags: [mine-adopt, quotient-map, oper-eq, admission-gate,
       toolchain-json, status-correction]
---

# 0031 — Mine-adopt is landed and gated; STATUS was stale

## What this frag records

`STATUS.md` listed "Mine-adopt — `try_adopt`: OperEq match a known
QuotientMap (identity / bytecode / fasm) or refuse (explicit map
required)" under *Where to go next*. It is not next — it landed in
`f85f592` (Phase 4a Quotient Maps) and is wired:

- `host/mine_adopt.py` — `try_adopt` (candidate encode adopted iff a
  single known QuotientMap OperEq-matches it on every surface) and
  `try_adopt_piece` (HostPiece adopted iff its NF agrees with a
  reference piece on every probe). Six checks, all green:
  identity/bytecode/fasm encodes adopt; `always_K` encode refuses
  ("no known QuotientMap matches under operEqRegime; define an
  explicit map"); `graph.lo` piece adopts; spurious `always_K` piece
  refuses naming the divergent probe.
- `host/toolchain.json` — `selftests[8] = mine_adopt`,
  `selftests[29] = gates/observational_suite`,
  `regimes/operEq/module = observation_regime`,
  `obligations[6]` covers piece adoption.
- `host/gates/observational_suite.py` exercises both accept and refuse
  paths as a suite gate.

This is the admission-gate altitude of the resolver schema (signature
→ congruence → identity → process → gate) at map level: adopt a
candidate only through a witness (OperEq match against a pinned map),
else refuse naming the axis. The koru-os sibling — row + arm-binding
admission with named refusals — is the same gate at OS altitude.

## Honest bound

Adoption is **probe-sampled, not proved**. `try_adopt` checks NF
agreement on a finite surface list (`default_probes` = 5 terms;
dialect paths use their GOLDENS). A candidate that agrees on the
probes and diverges elsewhere would adopt — OperEq over an infinite
term space cannot be decided by sampling. The correct strengthening
when a map matters enough: a per-map Lean proof that `encode`
commutes with NF (the `QuotientMapO`/`ObservationRegime` structures
exist; the per-map commutation does not). Until then the frag's claim
is M-class: measured on the catalog's surfaces, not V.

`fuel` is explicit and bounded — adoption can also refuse on
non-termination of the candidate's NF, which is the right failure
mode.

## What remains open (not this frag)

- Per-map NF-commutation proofs for adopted maps (Lean; do when a
  map's adoption must outlive sampling, e.g. maps produced by cogen).
- Growing `known_maps()` as dialects land — each new map extends the
  catalog the gate can adopt against; maps not in the catalog refuse,
  which is the point.
