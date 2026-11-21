# 043 — Registry-first: theorem families × evidence kinds; battery driven by toolchain.json

Commits: `8b1306d` (docs), `cd9556b` (registry + battery), `4c8120d` (gates G9b-emit, G10–G13; peephole axis).

## Decision

- **Every obligation in `host/toolchain.json` carries two orthogonal tags:**
  - `family` is the claim: `quotient | staging | cost | selection`.
  - `evidence` is the kind of support: `congruence | seam | cost | selection | lean | structural`.
  - It also carries `regime` (required unless the evidence is structural or lean), `tier` (`fast|full|env`, with env ⇔ `requires` non-empty), and an optional `timeout_s`.
- **`toolchain.validate()` is the honesty gate:**
  - A cost claim needs an explicit `cost_model {work, C, baseline, scope}`.
  - Any `wall` or `qemu` measure is rejected, so tempo never lands in the catalog as pseudo-Jones.
  - `lean_decls` is required iff the evidence is `lean`.
  - Benches must declare `claim: none…`.
  - Seven in-memory negative cases must each be rejected.
- **Registry sections:**
  - `obligations`
  - `selftests` (component checks, no claim; replaces `HOST_SUITES`)
  - `benches` (graph_bench, lambda_bench, diag, compare_lo_cd; they also exit nonzero on NF mismatch but are registered as reports)
  - `demos`
- **Lean entries:**
  - L0 is quotient.
  - L1 is cost, labelled **size-Jones (static)**: `pe_cost = term_size` on an abstract PESetup. It is not runtime Tw,C.
  - L2 is staging.
  - Renaming `JonesOptimal` → `SizeJonesOptimal` is deferred to its own commit, done the next time `Futamura.lean` is touched.
- **Selection** has no entry: `choose` is a strategy, so selection is NotRealized. **Runtime cost** is NotRealized too.
- **Classification choices:**
  - Plain native-vs-graph agreement is filed under family `quotient`, because there is no separate realization-soundness family.
  - `structural` was added so that G0, G0b and G6 are not mislabelled as seam or congruence.

## Battery protocol

- **Exit codes:** 0 pass, 1 fail, 77 whole suite skipped for environment reasons.
- **Partial skips:** `SKIP` lines inside a passing suite give `PASS*`, never plain ✓. This was the silent-skip-as-pass bug in lean_eval, futamura_cube, congruence and emit_chain.
- **Run list:** comes from the registry. Tier-filtered suites are NOT-RUN and are not recorded, so they render as `·`. "skip" is reserved for missing env tools and exit 77.
- **WSL tools:** `wsl:`-prefixed requires are probed inside WSL (qemu-*, ld).
- **Output:** streams live and is teed to `seed/build/battery_logs/<suite>.log`, with a 60 s heartbeat. The first `--tier all` run was invisible for hours because of stdout block-buffering plus `capture_output`.
- **`--only a,b`** merges records into `battery_last.json`. Each record carries `commit` (+dirty) and `at`, shown as the `run` column in GATES.md.
- **Status is per suite:** G9a–h and G9b-emit share `spec_term`, whose standalone run takes about 5.2 h.

## New gates

| id | suite | family / evidence | regime |
|---|---|---|---|
| G9b-emit | spec_term: residual exe vs pooled instantiation | staging / congruence | operEq |
| G10 | emit_chain: `emit_image(R) == seed.emit(R)` | staging / seam | bytes |
| G11 | cross_verify: PE↔C, graph↔C | quotient / congruence | stdout+stderr+rc |
| G12 | xisa_gate: 3 ISAs identical (plain / fuse / audit / fuel / invalid; n=28 tower = 81915 steps). Never records QEMU time. | quotient / congruence | stdout+stderr+rc |
| G13 | elfo_gate: reloc-patched `.o` text == exec text (and unpatched ≠ exec); relocs 7/14/14; optional WSL `ld` link-and-run leg | staging / seam | bytes |

## Finding

G10 caught a real seam break from `99dc32d`: the peephole was applied only on the seed route. See the revision in 042. This is the concrete payoff of registering seams.

## Deferred

- Package split, done only now that the registry drives the battery.
- pytest, only if CI or IDE discovery needs it.
- Scratch triage: list, then attic, then delete.
- A term-level `peepholeOf` stage.
- Per-obligation status inside multi-gate suites.
- CUDA behavioral and tempo gates (the `ir_cuda` witness stays declared, no gate).
