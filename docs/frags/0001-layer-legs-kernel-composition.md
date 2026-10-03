---
type: feature
id: 0001
provenance: gates_nanopass gate 23; layers.py; routines_x86_64_win64._LEGS_*
ts: 2026-10-08
tags: [phase8, layers, composition-as-data, kernel, dialects]
---
# Kernel composition is legs, not tuples

## What changed

A kernel image is now an **ordered sequence of legs**, each gated by
one realization axis — declared in `host/layers.py` and per-target
`LEGS_*` tables.  `routine_names_ir`, `program`, `data_slots_ir` no
longer select by if-chains and tuple surgery; they call
`layers.compose` / `compose_slots` and every axis value without a
declared row refuses, naming the axis and the leg.

```
head -> container(dialect) -> encoding -> driver(threads)
     -> stats -> worker(threads) -> depack(threads)
     -> core_a -> s_prim(fuse_s) -> core_b
     -> persist(reclaim) -> basis_tpl(fuse_s) -> egress(io)
```

The `ROUTINES*` tuples remain — re-documented as the family's routine
**vocabulary** (what `program_query_rt` enumerates, what the
`Routines` record advertises), not the composition.

## Why

The old `routine_names_ir` was eight hand-enumerated tuples plus
`names[:1] + ("plex_read",) + names[1:]` string surgery.  Two legs
already proved the pattern was right — `ir_spawn` sits in `ir_reduce`'s
slot under MT exactly the way `plex_read` sits after `ir_entry` under
dialect=plex.v3 — but the table shape was implicit.  Making it data
means new dialects/egresses/drivers are **declared rows**, not edits
to selection logic.  That is the stratification the emit chain and
the .plex contract already assume: every layer is bounded read ->
validate/refuse -> quotient to the next representation, and the chain
is the same shape at kernel granularity that STAGES/DEPS is at stage
granularity.

## Subtleties worth remembering

- **Order is contract, not topology.**  The MT tuple interleaves
  differently than ST (ir_spawn takes ir_reduce's slot; mt_worker +
  ir_depack move after exits) — legs are positional segments, so each
  permutation is declared rather than sorted.  Same for `.data`:
  slot contributions carry `slot_rank` (reclaim 10, container 20,
  threads 30, egress 40) because layout order differs from emission
  order.
- **st_s and build_ds are two legs, not alternatives.**  They sit at
  different positions (step cluster vs tail); fuse_s gates each.
- **Slots can be parameter-shaped.**  MT's ctx block sizes and the
  egress bytes-subset are callables `R -> slots` — declared data
  whose shape depends on the record.
- **MT + ir egress contributes no .data.**  All ei_* state is ctx
  fields; emit_ir's ei_len frame-write path is ST-only and never
  emitted under threads>1.  The gate pins this so a "helpful" EI
  contribution can't sneak back.
- **Spec files are the contract half.**  `host/specs/*.json` — one
  tiny file per dialect value (container/encoding/egress/surface/
  target), with in/out shapes, status, refusal contract.  Specs are
  what a leg row *claims to realize*; conformance checks they agree.
  Bundling them into archives is deliberately deferred (natural
  resolution later).
- **Build-time, not runtime.**  The kernel is still a compiled
  routine list — composition happens in the emit, not in the image.
  A kernel that reads a chain spec and assembles itself is the
  interpreted contract (G9), a separate output.

## Evidence

- Composed lists == frozen tuples for all 11 record combos
  (ST/MT x text/bytes/ir, plex.v3 x2, fuse_s x2, token) — gate 23.
- `.data` parity across 10 slot combos incl. MT+bytes subset and
  MT+ir empty — gate 23.
- Emitted bytes kernel sha `bacc6505f91d01f2` — identical to the
  fixpoint oracle produced pre-refactor.
- Refusals name axis + leg ("dialect='bogus' not realized by layer
  'container'") — gate 23.
- New strictness (flagged): threads>1 on the token record now refuses
  at the driver leg instead of silently emitting a serial kernel.
