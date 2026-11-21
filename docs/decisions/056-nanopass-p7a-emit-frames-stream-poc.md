---
id: 056
type: decision
ts: 2026-10-07
tags: [nanopass, phase7a, emit-frames, self-hosting, stream-schedule]
provenance: gates_nanopass gates 19-20; emit_chain emit_term/emit_frames/_run_stream
---
# 056 — Phase 7a: emit program as streams on the emitted host

## Decision

The emit-term POC is NOT one monolithic root.  It is an explicit
bounded-roots schedule plus Python byte-splicing, in two forms:

- **unstaged (mini scale)** — stream A `[link·KK·KK, link·KK·KI,
  asm·KK]` + stream B (pack chunks): the persist zone pays `link`
  once across roots (measured: 548K steps / 1.9s link+asm in one
  stream).
- **staged (real scale)** — the same stages decomposed exactly the
  way `emit_image`'s exe path does: program frag queries on a
  term-egress kernel → link blob seam on an ir-egress kernel
  (symtab a PIR blob, never Python-decoded) → per-item `encodeOf`
  roots on a bytes-egress kernel → pack chunk roots.  Every
  β-reduction runs on emitted kernels; Python does term
  construction, loc bookkeeping, and the splice.

`emit_term(…)` is the factored pure composition (the semantic form
— unusable as a schedule, kept as the equality oracle).
`emit_frames(…)` executes the schedule and returns
`(image, evidence)` with per-stream stats and decode counts.

## Evidence — the fixpoint chain is landed

- Mini unstaged: **2048B == `_mini_oracle`** (independent
  python_link/python_assemble/python_pack — cross-realization
  observation).
- `.lo` staged: **3584B == `emit_native`** — the emitted kernel
  evaluated the full emit of the naive kernel image.
- **Fixpoint — H1 == H0**: `emit_frames(Rb, rt=X86_64_WIN64_IR,
  staged=True)` produced **6656B byte-identical** to the on-disk
  bytes kernel, sha `bacc6505f91d01f2` (the plan's oracle
  fingerprint).  26 frags / 367K steps (program), symtab 37KB PIR
  blob (link), 1142 items → 4793B .text (assemble), ~112K steps
  (pack).  ~7.3 min wall.
- Behavioral: H1 runs a probe stream byte-identically to H0 —
  frames and the rc=5 non-byte-list refusal.
- Pickup: `stack_reserve` 64→32MB produced H1′ (sha `71382daf…`),
  **!= H0**, == `seed.emit(Rb2)` oracle, works as a kernel — the
  change was picked up, not served stale.

## Bugs found by the chain

- The staged path originally resolved `routines` only for the
  monolithic query — the staged enumeration silently used default
  `ROUTINES` (749 items → a valid but wrong 4608B image).  The
  fixpoint comparison caught it; `_emit_layout` now shares the
  rt/names_for/data_slots/text_base resolution across all paths.
- `assemble_staged`'s blob-syms-without-store refusal raised a
  bare `NotRealized` (latent NameError) — fixed to
  `toolchain.NotRealized`.

## Why not the monolithic root (measured)

- `pack2` concat spine: 280B input → 279K steps / 73s; the
  composed emit term exceeded 200s at mini scale — byte-list
  concat's live set is unbounded, no intra-root GC.
- `.lo` monolithic `asm` root: rc=4 at 43.8s even at 48GB arena +
  ~2GB persist.
- Multi-root persist reuse verified: shared stage subterms are
  paid once — the bounded-roots schedule is the architecture
  working as designed.

## emit.plex — the schedule serialized (update)

`write_emit_bundle`/`run_emit_bundle` landed: the archive is
`dialect=plex.emit/2` and carries the schedule AS DATA —

- canonical `emit.term` monolith as the primary PIR payload
  (semantic/equality oracle);
- stage streams as digest-referenced spans in the BYTES pool:
  `emit.program` (frag queries, term-egress), `emit.link`
  (`[idata·KK, datab·KK]`), `emit.symtab` (`APPEND` over KI
  projections, ir-egress — crosses as an opaque PIR blob);
- STAGES rows for all six stages (assemble/pack `derived`),
  DEPS edges assemble←{program,link,symtab}, pack←{link,assemble};
- REALIZATION records imports/slots/text_base/routines_list.

`run_emit_bundle` enforces dialect + caps ⊆ record BEFORE stream
extraction, verifies every stream digest, then drives the staged
schedule — result **3584B == emit_native** (sha 6daa770cbc0e).
Gate 21 `gate_emit_bundle` covers replay equality + corruption
digest refusal + widened-caps refusal.

## Kernel-side ingest — `.plex` is no longer a Python-only envelope (update)

`Realization.dialect` is a program-axis field; `"plex.v3"` selects
`r_plex_read` in front of `r_ir_read` in the emitted kernel — the
same composition slot `ir_spawn` uses under MT, so dialects slot in
as record axes compiled through the same emitted host, not new
loaders.  The routine validates header (magic/ver/hsize%8/hsize≥dir),
walks 32B dir rows (type/arity/`ln==rows·a·t` via div-quot+rem,
off%8, off≥hsize, off+ln≤file), selects the UNIQUE `KIND_PIR` row,
and clamps `r_ir_read`'s bounded reads to `plexleft` — a
declared-short span truncates mid-stream → rc=3, trailing bytes →
rc=3.  `KIND_PIR` (type 3) joined `plex_bundle`; `write_emit_bundle`
now stores the canonical emit.term there so a `plex.v3` kernel can
ingest emit.plex's payload directly.  Gate 22 `gate_plex_ingest`:
valid bundle == raw-PIR frames, 15-case refusal matrix → rc=3, MT
`.ir.mt` parity.  Unknown dialects refuse at `program_ir`.

## Honest boundary

- The emit program as *data* is now both forms: the canonical
  term (oracle) and the resolved stage streams (executable).
  The SCHEDULE is serialized including the derived stages —
  per-item roots and the pack splice map landed in 057 (Phase
  8b, gate 24); kernel-side scheduling remains the Phase-8/9
  DAG.
- Program enumeration and symtab/loc bookkeeping are seed-side
  boundary work — declared, counted in `_DECODE_COUNT`.
- Term- and ir-egress legs run on sibling realizations of the
  same kernel record — the honest claim is "the emitted kernel
  family evaluates the whole emit", not "one exe mode does all".
- This is not G9: spec_term.py/emit_chain.py remain the seed.
