# AGENTS.md — isar-proofs

Formal verification repo: Lean 4 theorem modules (`src/ISAR/` —
**verify-only, never touch semantics**) plus the Python
host/compiler infrastructure (`host/`, `seed/`).

## Layout

- `seed/` — the self-contained seed (`seed.py` emits
  `native.x86_64.pe`; stdlib-only, no imports from `host/`)
- `host/` — module surface: `emit_chain`, `spec_term`,
  `plex_bundle`, `layers`, `toolchain`, `routines_*`, `isa_*`,
  `target_*`, dialects, evaluators
- `host/gates/` — gate suites (`gates_nanopass.py` runner +
  `np_gates_{record,streams,emit,kernel}`; `spec_check`,
  `caps_gate`, `xdu_gate`, `elfo_gate`, `futamura_cube`, …)
- `host/benches/` — measurement modules (`diag`, `lambda_bench`,
  `graph_bench`, `compare_lo_cd`)
- `host/challenges.py` — standing challenge catalog (generators,
  replayed, diffed against recorded outcomes)
- `host/bench.py` — measure harness → `seed/build/bench_last.json`
- `host/battery.py` — obligation orchestrator →
  `seed/build/battery_last.json`

## Contract (the anti-smuggling rules)

1. **Data crosses boundaries, logic never does.** Quotient maps,
   tables, wire formats as literals. An algorithm where a table
   belongs = boundary drawn wrong.
2. **Refuse by default, name the axis.** Unsupported combination →
   `toolchain.NotRealized` naming the axis/leg, never a silent
   default or fallback.
3. **No silent success on malformed input.** Truncated, forged,
   out-of-correspondence inputs refuse at the earliest structural
   check.
4. **Composition is declared data.** Kernel legs
   (`layers.LEGS`), the emit DAG (STAGES/DEPS/MAP rows), and the
   toolchain spec (`toolchain.json`) are data; Python interprets,
   never hardcodes the chain.
5. **Witnesses stay independent.** Oracles compare
   implementations byte-for-byte or NF-for-NF; never port a
   witness into the implementation's path.
6. **stdlib only** in `host/` and `seed/` (psutil permitted in
   `benches/` measures only).

## Verification

```bash
python host/battery.py --tier fast     # fast obligations (~30s)
python host/gates/gates_nanopass.py    # full nanopass suite (24 gates)
python host/gates/gates_nanopass.py --only=emit,link   # subsets
python host/challenges.py --json       # refusal catalog
python host/bench.py --json            # measures (not obligations)
python host/spec_project.py            # generated-doc drift check
```

## Writeup discipline (koru frags)

**A landed feature/decision gets a frag in `docs/frags/`** —
`{type, id, provenance, ts, tags}` frontmatter, atomic, honest
about trade-offs and refusals. Stage contracts live in
`docs/stages/`; derived tables in `docs/{GATES,CATALOG,MATRIX}.md`
are **generated — never hand-edit** (regenerate with
`python host/spec_project.py --write`).

## Never

- Comment out or weaken a failing gate to go green.
- Infer gate pass status — only tool output counts.
- Add a realized component without its obligation row, or a
  declared component without its refusal path.
- Move/retire a module without updating `toolchain.json` and
  checking `python host/battery.py --tier fast`.
