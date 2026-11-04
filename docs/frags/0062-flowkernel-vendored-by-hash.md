---
type: frag
id: 0062
provenance: devin-cli
ts: 2026-11-04
tags: [koru, flowkernel, flowdialect, vendor, drift, gate, invariants]
---

# 0062 — FlowKernel vendored by hash; the path comment becomes a checked link

Fable's review named the shape: *"one kernel, two repos, hand-synced —
`FlowKernel.lean` lives in koru `verify/semantics/` and is re-typed as
`FlowDialect.runK` here with a path comment as the only link. Either
repo can drift silently."* The fix chosen: **vendor by hash**, not a
lake dependency — upstream (korulang) should not be asked to absorb
the whole isar-proofs tree.

## The two-ended mechanism

- **koru side** (koru-quantity@19979d580): invariant row
  `flowkernel-mirror-not-drift`, `git-gate` unsampled — the check is
  one hash. `checks/flowkernel_mirror.pin` holds the source's
  LF-normalized sha256; `check_flowkernel_mirror.py` recomputes and
  fails the commit until port + re-pin land together.
- **isar side** (`4ba3102`): `upstream-sha256:` line in
  `FlowDialect.lean`'s docstring; `host/gates/flowkernel_drift.py`
  recomputes it over the reachable koru checkout; obligation `GFK`
  (env tier) wires it into the battery via a new `koru-src`
  `tool_present` axis — named skip `env: missing koru-src` when no
  checkout is reachable, never a silent pass.

## Details that matter

- The pin is **LF-normalized** (`\r\n` stripped before hashing):
  the two checkouts on this machine already disagree on line endings
  — `file` shows CRLF on `w:/src/koru`, LF on the WSL clone. Content
  was identical modulo endings; a raw-bytes pin would false-fire
  across the autocrlf boundary.
- The koru check's drift message names the remedy and prints the
  re-pin command — refusal that teaches, per house style.
- Battery tier is `env` + `requires: ["koru-src"]`: the obligation
  skips with a named reason on machines without a koru checkout
  rather than fabricating a pass or a hard failure.

Verified: `battery --only GFK` → PASS (0.0s, w:\src\koru);
koru check → `at pin`; tampered pin → drift verdict + remedy text,
rc=1.
