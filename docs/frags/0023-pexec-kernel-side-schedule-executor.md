type: frag
id: 0023
provenance: host/routines_x86_64_win64.py r_pexec + _LEGS_IR +
  host/specs/container-plex.emit.json + np_gates_emit
  gate_pexec_schedule
ts: 2025-01-01
tags: [self-host, plex.emit, schedule, executor, dep-closure,
  map-splice, kernel]
---

# 0023 — pexec: the schedule executor is a kernel dialect leg

## What landed

`dialect="plex.emit"` realizes kernel-side execution of the staged
emit DAG — the whole of `run_emit_bundle`'s orchestration moved
into the emitted binary. `pexec` consumes a `.plex` emit bundle
in-process:

- v3 header + directory validation (same contract as plex_read);
- REALIZATION must claim `dialect="plex.emit/2"`;
- dependency closure of the declared output stage off DEPS rows;
- every needed stage in declared order: `"off:len"` QUERIES token
  → BYTES-pool span (emit.term rides the KIND_PIR section) → PIR
  span check `len == 16+4·nr+9·nn` → `ir_depack` → `freduce` per
  root → frames stored in a native index;
- `emit_bytes` gains a store mode: frames append to `fr_idx`
  instead of stdout; eval-only stages (exe.term/exe.ir runners)
  reduce without materializing;
- MAP rows splice as positional inserts — own frames `[cur, at)`,
  then source stage's frame(s) (`src_frame=0xFFFFFFFF` splices a
  whole stream), then the tail;
- the image goes out as one `[u32 len][bytes]` frame.

Legs: container row `Impl(("pexec",), slots=DATA_SLOTS_PE)`; the
encoding leg emits nothing for plex.emit — stage streams are
archive spans, not stdin. Cross-axis refusals live in
`routine_names_ir`: plex.emit requires `io=("stdin","bytes")` and
is serial (`threads>1` refuses — per-stage parallelism is a
schedule realization, not the executor's).

## Numbers

```
route                    wall    steps
staged native (pexec)    1.1s    36.6M     default record
staged python (spawn×5) 27.9s    same DAG
monolith (emit.term)    22.6s   153.6M
IR record via pexec      3.9s   142.8M
pexec record via pexec   7.7s   221.4M
```

## Fixpoint on the executor itself

```
seed.emit        -> pexec.exe (13824B, dialect=plex.emit)
pexec < emit_pexec.plex -> H1   byte-identical to seed oracle
H1    < emit_pexec.plex -> H2   byte-identical to H1
                                (221,393,535 steps both legs)
```

A `dialect="plex.emit"` bundle contains the pexec program itself
as data — the emitted executor executes its own spec. Python's
staged-route residue is now spawn + file write.

## Pickup

A `fuse_s=True` bundle — a program the emitted executor never
contained — compiles byte-identical to `seed.emit` in 1.1s. The
kernel is the fixed substrate; the bundle is the moving spec.

## Bugs found in the instrumented bring-up

- decimal token accumulator computed `11·x + d` (an extra add);
  masked on `off` by emit.program's leading `"0:"` token.
- `.data` slot `pe_done` collided with `peval`'s code label in the
  assembler's flat namespace — a conditional jump landed in data;
  renamed `pe_sdone`. Only collision.
- `edi` (MAP `src_frame`) was loaded before the `pe_own` loop —
  `pe_copy`'s `rep_movsb` clobbers `rdi`; re-read at `pe_ownd`.
- pipe EOF arrives as `ReadFile` FALSE + `ERROR_BROKEN_PIPE`;
  bounded-stdin read treats FALSE as the EOF boundary.

## Honest edges

- Serial only — dep-order is sequential in-kernel; MT still means
  the Python spawn route or a future schedule-level realization.
- No digest verification in-kernel (Python replay sha256-checks
  stream payloads; pexec checks structure — forged-but-well-formed
  streams reduce, malformed ones refuse rc=3).
- Gates: `kernel plex.emit schedule exec` PASS (byte-identity vs
  emit_native + three refusal probes); layer-chain tuple, spec
  conformance set, leg_values all updated; fast battery 31/31.
