# 064 — plex.emit dialect leg: schedule execution lives in the kernel

## Context

After frag 0022 closed the monolithic fixpoint (H2 == H1 == H0 on
plex.v3), the staged route still ran its dep-order + frame-splice
orchestration in Python (`run_emit_bundle` spawned a reducer per
stage and concatenated frames). The user asked for the staged
route to go fully kernel-side: "Full kernel-side schedule
execution (plex.emit/2 dialect leg — dep-order + MAP splice as
asm driver) would remove even the spawn/splice residue."

## Decision

`plex.emit` is a third container-dialect leg on `_LEGS_IR`,
implemented by `r_pexec` — not a runtime mode, not a Python
driver. The schedule stays data (STAGES/DEPS/QUERIES/MAP rows);
the kernel interprets it natively:

- dep closure of `schedule.output` off DEPS; declared-order
  execution (STAGES rows are already topological);
- per stage: QUERIES token `off:len` → BYTES-pool span
  (emit.term → KIND_PIR section), PIR span check, depack,
  freduce, frame store in `fr_idx`;
- emit_bytes store mode appends frames instead of writing stdout;
  eval-only runners (exe.term/exe.ir) reduce without emitting;
- MAP rows are positional splices over the output stage's frames;
- one `[u32 len][bytes]` egress frame.

Alternatives considered: (a) keep Python orchestration — rejected,
that was the residue to remove; (b) run stages concurrently
in-kernel — refused instead (`threads>1` NotRealized): schedule
parallelism is a separate realization, not silently merged into
the serial executor.

## Contract

- `io=("stdin","bytes")` only; serial; `reclaim`/`gc` free.
- Refusals are structural and early: archive validation, dialect
  claim, dep-closure membership, token/span relations, frame
  bounds — rc=3 (rc=5 on output overflow).
- pexec does NOT verify stream digests — Python replay keeps the
  sha256 audit; the kernel checks structure only.

## Outcome

byte-identical to `emit_native` and to `seed.emit` oracles on
default, fuse_s, IR, and pexec records; self-hosting fixpoint
H2==H1 on the executor itself (7.7s/leg); 25× the Python-orchestrated
staged route on the default record. Gate:
`kernel plex.emit schedule exec`.
