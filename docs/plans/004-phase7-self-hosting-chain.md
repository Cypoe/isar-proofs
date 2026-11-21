---
agent: devin-local
created: 2026-10-06
status: Phase 7 complete (7a+7b+7c, gates 19-22); Phase 8 in motion — kernel layer legs landed: composition from declared data (layers.py + LEGS_* + specs/*.json, gate 23)
---
# Phase 7 — self-hosting chain (seed → H0 → H1 → H2, pickup H1' → H2')

## What was skipped

The agreed ordering was:

> stage eval lemmas → host classification → C-target dialect → C reducer
> kernel as second host → cross-verification Python-vs-clang → **the seed
> starts emitting its own host**

We landed P1–P6 (query-engine emit, term-level programOf, unified
runtime, seam cutover, MT kernel, .plex v3) but never crossed the
emission boundary: **no emitted host has ever produced a host**.  Every
image so far was produced by Python orchestrating stage queries.  The
C-target dialect / C reducer kernel (second host for Python-vs-clang
cross-verification) is the *other* skipped item — scoped below as
Phase 7.5, but it is a cross-verification axis, not a blocker for the
win_x86_64 chain.

## The claim and its honest boundary

H0 is the emitted `x86_64.win64.ir` bytes kernel (the production
`bacc6505` oracle image).  The emit itself is already ONE reducible
term — `emit_image`'s monolithic path builds
`pack2_query(assemble_query(program_nf, link_nf), …)` and reduces it.
Feeding that term to a bytes-egress kernel yields the image bytes.

So the chain is: **the emit program is data; the host is the evaluator.**

- seed (spec_term.py) builds + packs `T_emit` — term construction is
  serialization, not semantics; Python stays the seed/wire layer.
- H0 ingests `emit.plex`, reduces `T_emit`, egresses image bytes.
- H1 == H0 (byte-identical — same deterministic term, same kernel;
  PE emit is already deterministic, `bacc6505` stable across sessions).
- H2 == H1 proves stability, not quining.

**This does NOT prove G9.**  `emit_chain.py`/`spec_term.py` are not
regenerated — the Python term-builder remains the seed.  The claim is
"host reproduces host given the emit program as data", which is the
deployed-product shape from the contract: Load → bind → Run.

## Steps

### 7a — emit-term export (`emit_chain.py`) — POC landed at mini scale

**Measured facts that shaped the design** (all on the redirect kernel):

- `asm_q` whole-stage fold, `.lo` program: ~505K steps / ~807K alloc /
  1.5s — fine as ONE root.
- `link_q` projections: ~87–174K steps, 2.9–4.4s — fine.
- `pack2` concat spine: 280B synthetic → **279K steps / 73s**, and the
  composed monolithic emit term did not finish in 200s at ANY scale —
  the byte-list concat's live set grows unboundedly with no intra-root
  GC (exactly why `pack_staged` exists; even `LENB4` alone is OOM-class
  as a term).
- `.lo` monolithic `asm` root inside `emit_frames`: rc=4 at 43.8s even
  with 48GB arena + ~2GB persist — real scale needs per-item roots
  (the documented reason `assemble_staged` exists).
- Persist-zone cross-root FWD reuse VERIFIED: a 3-root stream
  `[link·KK·KK, link·KK·KI, asm·KK]` runs link+asm in 1.9s/548K steps —
  root 3 hits link's FWD written by root 1.

**Landed POC shape** — `emit_term()` factored (pure composition,
returned before `run=`), `emit_frames()` = executable schedule:

- stream A: `[link·KK·KK, link·KK·KI, asm·KK]` — all semantic folds
  kernel-side, persist zone pays `link` once across roots;
- stream B: pack's derived chunks as roots — the `pack_staged` recipe
  (`_ALIGN512/_B4ADD/_U64/_ZEROFILL/_PADLIST` numerals) — bounded terms;
- Python does ONLY term construction + length metadata + byte splice —
  same discipline pack_staged declares; section-size fields are
  `len().to_bytes(4)` (b4 numerals are NF, no kernel work needed).
- Mini scale: **2048B byte-identical to `_mini_oracle`** (independent
  python_link/python_assemble/python_pack — cross-realization
  observation).  Gate 19 `gate_emit_frames` incl. refusal leg
  (non-byte-list root → rc=5 → NotRealized).

**Landfall — the fixpoint chain is verified** (decision 056):

- `.lo` staged: 3584B == emit_native
- **H1 == H0**: 6656B == on-disk bytes kernel, sha bacc6505f91d01f2
- H1 behavioral probe + rc=5 refusal parity with H0
- Pickup: stack_reserve change → H1′ != H0, == seed.emit(Rb2)
- Chain-caught bug: staged enumeration silently used default
  ROUTINES → `_emit_layout` now shares rt resolution everywhere
- Gate 20 `gate_selfhost_fixpoint` covers all legs

- `write_emit_bundle(path, R, schedule=True)` — LANDED: emit.plex is
  a `plex.emit/2` archive carrying the canonical `emit.term` PIR
  payload PLUS the stage-level schedule as data: `emit_schedule_streams`
  produces `emit.program` (frag queries, term-egress), `emit.link`
  (`[idata·KK, datab·KK]` byte projections), `emit.symtab`
  (`APPEND` over KI projections, ir-egress) as digest-referenced
  spans in the BYTES pool; STAGES rows declare all six stages
  (assemble/pack marked `derived`), DEPS edges encode
  assemble←{program,link,symtab}, pack←{link,assemble};
  REALIZATION records imports/slots/text_base/routines_list so the
  replay resolves layout without re-deriving the record.
- `emit_bundle_streams(b)` — digest-verified stream extraction;
  span OOB or digest mismatch → NotRealized.
- `run_emit_bundle(path)` — LANDED: reads emit.plex, enforces
  dialect + caps ⊆ routines record (checked BEFORE streams — a
  header-level property), drives the schedule: program frags →
  items (decode crossing counted), link byte projections, symtab
  as opaque PIR blob spliced into pass-2 encode queries, per-item
  encodeOf roots, pack chunk roots.  Result: **3584B byte-identical
  to emit_native** (sha 6daa770cbc0e).  Gate 21 `gate_emit_bundle`
  covers stage/dep assertions, replay equality, corrupted-stream
  digest refusal, widened-caps refusal.
- Still honestly in Python: assemble/pack are `derived` — the
  replay resolves per-item roots + loc bookkeeping exactly as
  emit_frames(staged) does.  Kernel-side schedule resolution is
  the Phase-8 DAG, not this seam.

### 7b — kernel-side .plex v3 depacker (`routines_x86_64_win64.py`) — LANDED (gate 22)

- `Realization.dialect` program-axis field — `"plex.v3"` selects
  `r_plex_read` in front of `r_ir_read` (same composition slot
  `ir_spawn` uses under MT).  `routine_names_ir` dispatches on it;
  unknown dialects refuse at `program_ir` construction.
- `r_plex_read`: reads the 12B v3 header (bounded), validates
  magic/ver=3/hsize%8/hsize≥dir_end, reads the directory exactly,
  walks 32B rows — type ∈ {0,1,2,3}, arity ≥1, ln == rows·arity·type
  (overflow-free via div: quot==rows & rem==0), off%8==0,
  off ≥ hsize, off+ln ≤ file — and selects the UNIQUE KIND_PIR
  row.  Its span becomes `plexdir/plexoff/plexlen/plexnp/plexleft`;
  `r_ir_read`'s header+body reads clamp to `plexleft` under
  dialect=plex.v3 so a declared-short span truncates mid-stream →
  refuse, and trailing bytes beyond the PIR payload → refuse.
- `plex_bundle.KIND_PIR` (type 3): `write_emit_bundle` stores the
  canonical emit.term in its own section; `emit_bundle_streams`
  resolves `emit.term`'s `0:len` token against it (not the BYTES
  pool).  `dialect` added to `_prog_axes`/`strategy_axes`.
- Verified (gate 22 `gate_plex_ingest`): valid bundle → rc=0,
  frames byte-identical to raw-PIR kernel on the same payload;
  refusal matrix → rc=3 for bad magic, ver≠3, hsize%8, hsize<dir,
  truncated dir, bad section type, arity=0, ln≠rows·a·t, off%8,
  off<hsize, dup PIR, PIR len>file, missing PIR, declared-short,
  trailing junk; MT `.ir.mt` kernel parity (rc=0, equal frames).

### 7c — chain gates (`gates_nanopass.py` gate 19, or a `selfhost_gate`)

- **fixpoint**: `H0 < emit.plex > H1.bin`; `H1.bin == H0` bytes.
- **stability**: `H1 < emit.plex > H2.bin`; `H2 == H1`.
- **pickup**: seed change (e.g. a Realization field, or an added
  pass/routine — "modify an emission rule", plan criterion 8) →
  `emit'.plex`; `H1 < emit'.plex > H1'`; `H1' != H1`, valid PE;
  `H1' < emit'.plex > H2'`; `H2' == H1'`.
- **behavioral**: `H1'` reduces the probe corpus (SKI goldens, lisp
  mini) byte-identically to `H1` — the new host works, not just exists.
- **refusals**: malformed bundles refused by the kernel itself.
- Evidence category: cross-realization observation + construction-seam
  byte comparison (tag both in the gate print per the contract).

### 7d — decision note 056 + HANDOFF

## Phase 7.5 — C-target dialect + second host (the skipped cross-verify)

- New target record (C emission as text) + C reducer kernel routines —
  the emit chain already targets records, so this is "new target record,
  same stage machinery" per the original ordering.
- Value: an independent toolchain (clang) cross-verifies the same emit
  semantics — a *different* evidence category than self-hosting, which
  is self-referential by construction.  Behavioral equivalence
  Python-vs-clang-vs-kernel on the probe corpus.
- Not a blocker for Phase 7; slots after it or in parallel.

## Effort/risk notes

- Emit term size: program.items packed was ~1.3MB; the full emit term
  will be several MB packed — inside arena bounds, depack is linear.
- Wall time: the monolithic emit as ONE kernel process could be
  tens of minutes (no exe-pool batching).  It's a proof artifact, run
  per-gate, not CI.  The staged-DAG variant (multiple roots = the
  stage queries, dep edges as data) unlocks MT scheduling later —
  Phase 8+ material, not needed for the fixpoint.
- The depacker must refuse, not reinterpret — a bundle is the *input
  contract*; ambiguity is a bug report, not a heuristic opportunity.

# Phase 8 — final shape + cleanup in motion (scope only)

Phase 7 is POC-only: one monolithic emit term proves the fixpoint.
Phase 8 replaces it with the real shape AND starts the cleanup wave —
from here the status quo is what enforcement will later measure
against.

## 8a — LANDED (first slice): kernel layer legs (gate 23)

`host/layers.py` + per-target `LEGS_*` tables: a kernel image is an
ordered sequence of legs, each gated by ONE realization axis
(container<-dialect, driver<-threads, egress<-io, basis<-fuse_s,
persist<-reclaim).  `routine_names_ir`/`program`/`data_slots_ir` are
compose calls now — the eight hand-enumerated tuples and the
names[:1]+insert surgery are gone.  `ROUTINES*` tuples stay as the
declared vocabulary (program_query_rt enumeration, record catalog).
specs/*.json — 12 tiny contract files (container/encoding/egress/
surface/target layers; in/out shapes, status, refusal contract);
bundling them into archives is deferred (natural resolution later).
Build-time composition only — a runtime chain-spec interpreter is
the G9 contract, a separate output.  Verified: composed lists ==
frozen tuples (11 combos), .data parity (10 combos incl. MT+ir
empty-EI), emitted bytes kernel == fixpoint oracle bacc6505f91d01f2,
refusals name axis+leg.  New strictness: threads>1 on the token
record refuses (was silent ST emit).  Frag: docs/frags/0001.

## 8b — staged DAG in the bundle (the real shape)

- Stage queries as MULTIPLE roots inside `emit.plex`; dep edges as
  data (the v3 DEPS section already encodes them); kernel-side
  topo scheduling replaces Python's `emit_image` loop.  Dep-level
  parallelism unlocks the MT kernel's actual role: `program.*` frags
  and independent section builds run across workers in one stream.
- Checkpoint keys become bundle rows — a changed stage misses its
  deps' descendants only, kernel-side.  Content keys already exist;
  what's new is the kernel resolving availability, not just deps.
- Python's residue shrinks to: build bundle → move file → compare
  output.  Exactly "Python only moved the file" (criterion 5).

## 8b — cleanup wave in motion

- Harness split (runs/asserts/measures) STARTS: `host/battery.py`
  orchestrator + per-gate standalone reruns; new `host/bench.py`
  (steps/s, emit wall, arena, MT scaling → `bench_last.json`).
- `host/` package boundary: no sys.path tricks in gates.
- Stale-path retirements get gated, not just noted — every removal
  has a gate proving the replacement covers it.

# Phase 9 — enforcement cement (scope only, after Phase 8)

The status-quo proven in 7/8 becomes the enforced standard — every
step re-run here as the acceptance pass.

## 9a — repro re-runs per test

Every gate/challenge/bench is a named reproducible entry with a fixed
command and recorded expected output; `battery.py` replays the whole
catalog and diffs (not just booleans — actual expected values).

## 9b — per-stage writeups + emit-target triplet matrix

- `docs/stages/` — program/link/assemble/pack: term signature,
  consumers, checkpoint key shape, evidence produced.
- `docs/MATRIX.md` generated from toolchain.json + battery JSON:
  rows = triplets (x86_64-win64-pe, x86_64-linux-elf, aarch64-…,
  riscv64-…, cuda, pe64.uefi), columns = gate/probe families —
  realized/refused/declared, drift-checked like GATES.md.

## 9c — gates/challenges + benches as the flywheel

- Standing challenge catalog (arbiters-challenge model: generators
  replayed, catalog grows): refusals, widened caps, malformed
  bundles, mode changes — each a named reproducible entry.
- Benches become CI-visible numbers, not anecdotes.

## 9d — koru-style frags cemented in hooks/AGENTS.md

- `docs/frags/` atomic writeups `{type,id,provenance,ts,tags}` —
  one per feature/lesson ("shadow-space clobbered r10", "dep order
  is declared not topological").  The narrative series IS the docs.
- The flywheel: repo hooks + AGENTS.md rules REQUIRE a frag per
  landed feature/decision — writeup-driven development enforced
  structurally, not by discipline.

## Deferred with a shape — C second-host

Not a blocker anywhere.  The interesting version isn't "port the
kernel to C": it's the C host generated *from* toolchain.json —
the spec already declares the routines/dialect/caps, so a C target
record could let the host pick its own C dialect to compile.  And if
the .plex depacker from 7b is expressible in the C dialect, the C
host reads bundles too — same input contract, third evidence
category (clang vs emitted vs Python).  Defer until Phase 9 is
stable; the toolchain.json→C path is what makes it worth doing at
all rather than a port.

## 8a — harness split: what RUNS vs what ASSERTS vs what MEASURES

- **runs**: `host/battery.py` stays the orchestrator; add a `repro`
  entry so every gate/challenge reruns standalone
  (`python host/battery.py --only gate18` or per-gate `__main__`).
- **asserts**: gates_*.py (18 nanopass, caps, xdu, seed G0–G8) —
  enumerate into one registry; each gate declares its evidence
  category (the contract requires this anyway).
- **measures**: NEW `host/bench.py` — steps/s, emit wall time, arena
  footprint, MT scaling table; writes `bench_last.json` like
  `battery_last.json`; numbers are evidence class "performance
  measurement" — explicitly not equivalence claims.

## 8b — emit-target triplet matrix

- Matrix = toolchain records × {realized, refused, declared}: rows are
  triplets (`x86_64-win64-pe`, `x86_64-linux-elf`, `aarch64-…`,
  `riscv64-…`, `cuda`, `pe64.uefi`), columns are the gate/probe
  families.  Generated `docs/MATRIX.md` from toolchain.json + battery
  JSON (same drift-check pattern as GATES.md).

## 8c — writeups per feature/stage (the koru model)

- `docs/frags/` — atomic docs with `{type, id, provenance, ts, tags}`
  frontmatter (koru `concepts/frag-*.md` shape, 348 files there):
  types like {feature, stage, gate, decision, belief, bench}.
  Each phase artifact gets one frag: "the emit term is data",
  "shadow-space clobbered r10", "dep order is declared not
  topological", …  The narrative series IS the documentation.
- Per-stage writeups (`docs/stages/`): program/link/assemble/pack —
  what the stage is, its term signature, who consumes its NF, its
  checkpoint key shape.

## 8d — challenges + repro corpus

- Standing challenge set replayed per release (arbiters-challenge
  style: challenges are generators, catalogs grow): refusal cases,
  widened caps, malformed bundles, mode changes — each a named
  reproducible entry, not an inline gate case.
- Lisp corpus + SKI goldens stay the behavioral witness set.

## 8e — packaging

- `isar-proofs` stays the repo; `host/` becomes an importable package
  boundary (explicit `__init__`, no sys.path tricks in gates);
  CLI entry points for emit/replay/bench; requirements = stdlib only
  (hard rule stays).
