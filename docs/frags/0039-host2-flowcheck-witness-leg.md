---
type: frag
id: 0039
provenance: devin-cli
ts: 2026-10-26
tags: [koru, host2, flowcheck, independent-witness, lean]
---

# 0039 — the authority's kernel re-decides every claim (eval.c-is-runK witness)

## What changed

`check.py` gained the witness leg frag 0038 named as missing. Every
emitted `[flow-eval]` claim — generated corpus + ported programs +
wire rows — is re-decided by the **authority's** mechanized
semantics: `w:/src/koru/verify/semantics/FlowCheck.lean` running
over `FlowKernel.lean`, corpus mode. Not our port, not our
evaluator — the upstream checker consumes our wire verbatim.

- `conformance` corpus: all non-forged claims, dedup'd (upstream
  counts byte-identical duplicates as drift violations). **27
  lines, 0 bad.**
- `forged` corpus: rows flagged `"forged"` (currently
  `case-forged`'s wrong-expectation claim) run under `--forged` —
  all must REJECT. **1 line, 0 bad.**

The toolchain is declared data: `koru/flowcheck` row in
`realizations.json` carries the FlowKernel/FlowCheck paths and
`leanprover/lean4:v4.31.0`. `check.py` compiles
`FlowKernel.olean` into `build/flowcheck-oleans/` (mtime-cached),
then `elan run <tc> lean --run FlowCheck.lean <corpus>` with
`LEAN_PATH` pointed at the olean. Missing elan/toolchain/files =
skip, never fail — same contract as the koruc leg.

## Why this closes the gap

Frag 0038's honest position said the companions pin structure but
don't prove `eval.c` *is* `runK` — the byte-for-byte claim check
was still C-vs-authored-expectations. Now there are **two
independent evaluators agreeing on the same wire**: C-krun (a
port of the kernel) and upstream-FlowKernel (the kernel itself).
Agreement on 27 claims including `_chain`-decorated arms, tagged
dispatch, oracle leaves, guards, jumps, and refuse-expectations is
the strongest available statement short of a verified extraction.

## Honest position

- FlowCheck itself is the authority's surface; its own
  `checkLine` theorems (`wire_arith`, `wire_thunk`, `wire_refuse`)
  pin the decode path, and `run_mono` makes single-fuel checking
  sound for decided claims. Refusal claims remain
  budget-relative — their honesty note, now ours.
- `FlowCheck`'s third mode, `--cref <emitted.c>` (kernel-rendered
  stdout == emitted C writes), is **not** wired: our emit leg
  writes exit DWORDs, not stdout — likely outside its rendered
  subset. If the C backend ever prints, that's the next witness.
- The witness validates *claims*, not the `.k`→claim lowering —
  korufe's fidelity is still the `koruc -c` authority leg +
  parse/print/parse round trip.

## Verify

`python host2/check.py` → **121 pass, 0 fail, 0 skip**
(was 119; +2 witness legs). `lake build Host2` clean, battery
31/31, spec_project in sync.
