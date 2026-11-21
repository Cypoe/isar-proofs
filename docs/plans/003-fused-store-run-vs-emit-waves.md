---
agent: devin-local
session: nosy-asiago
created: 2026-09-19T03:35:07Z
---
# Fused store: one bundle, two ingest roles (run vs emit), gated waves

Unify terms, data, capabilities and proofs as one relation store (COO; PIR is its canonical subset), distinguish ingest-to-run from ingest-to-emit as binding times of the same host, and land it in gated waves where each wave reruns only its own suites.

## 0. Fused model (settled)

- **One store.** A bundle is one COO relation store, sectioned by TLV under an interned symbol schema.
- **PIR is COO with invariants.** Rows are `(i, tag, l, r)` with implicit value 1. The table is functional in `i`, topologically sorted (`l, r < i`) and hash-consed (ADR-0005 lines 36–70).
- **Everything else is a relation in the same store:** kernel matrices, bytechunks, nibble numbers, symbol interning, catalog/`Realization`/dialect maps/ISA encodings/relocations, **capabilities** (`ExtendedCapability`, 192 bits, `isa-physics/plex-agent/src/dialect/capability.py` lines 25–49), and proofs (wire TLV 0x0006).
- **The real distinction is how a relation is executed:**
  - **rewrite** is reduction on the node relation, and it is the proved semantics;
  - **join** is indexed lookup on data relations. A join is admissible only as a fused rule with an `OperEq` argument, following the `fuse_s` precedent.
- **Non-unit values are nibble-exact** (`plex/lib/symbolic/arbitrary_precision.py`). IEEE is only a declared realization for a numeric dialect.

## 1. Ingest to run vs ingest to emit

The same host, the same store and the same reducer serve both. They differ in binding time, egress, capability surface and the kind of claim.

| | ingest → **run** (runtime / OS) | ingest → **emit** (target host / dialect) |
|---|---|---|
| catalog path | `paths.runtime`: "term reduced live by a host piece" (`toolchain.json`) | `paths.native`: "behaviour compiled to code; no reducer in the image" (covers only `xdu.json`) |
| Futamura | P0: the host runs the operation | P1/P2: the host runs the **realizer** with the operation as static data |
| egress | observations on ports (NF tokens, stats, rc) | **bytes**: an artifact (image / `.o` / C / fasm text = a dialect decode) |
| claim | congruence under `O` on the declared ports | seam (`bytes`) on the artifact, plus downstream congruence of the artifact when it is run |
| capabilities | the operation's ports: stdin, stdout, stderr, scratch, payload | minimal: read the bundle, write the artifact, scratch. No exec, no extra devices. |
| OS variant | SASOS / UEFI host: caps bound to apertures instead of syscalls (`plexus/crates/plex-os/src/exo.rs`, `sasos_alloc.rs`). Already declared: `x86_64.uefi.lo`, `pe64.uefi`, abi `uefi` = declared | the emitter needs no OS services beyond a byte stream, so it can run inside any runtime host, including the SASOS one |

**Consequence:** emitting *is* running a particular bundle whose output port carries bytes. **Native byte egress is the pivot that turns a runtime into an emitter.** A dialect decode (e.g. fasm or C text) is the same egress mechanism with a different output map.

Running a `.plex` "directly" is already true for PIR. The IR kernel has no parser: depacking is address arithmetic over `cells + i*24`, with validation once at load → `exit3` (ADR-0005 lines 96–105; `r_ir_depack` at `routines_x86_64_win64.py:838`). Full mmap-and-run requires stored rows to equal arena cells: zero depack, at 24 B vs 9 B per node. That trade-off is decided in the ADR (W6).

## 2. Verified evidence

| claim | evidence |
|---|---|
| Python reduces in the staged chain | `emit_chain._graph_run` (`emit_chain.py:81–90`) is a Python `Graph`; `_l0_nf` (`spec_term.py:2514`) is a Python l0 stepper, used for projections in `emit_image` |
| Python decodes at seams | `decode_program` (`spec_term.py:2701`), `decode_link` (`:2281`), `_decode_bytecells` (`:2676`) |
| Python owns the per-instruction fold | `assemble_staged` (`emit_chain.py:453`) and `pack_staged` (`:559`) |
| byte egress is decode-by-observation | `_decode_bytecell` applies the cell to `K`/`KI`, then the selector to 16 VAR markers (`spec_term.py:2658–2673`); bytes are `PAIR nibLo nibHi` Scott lists (`:324–346`) |
| kernels only print NF tokens | `r_emit_nf` (`routines_x86_64_win64.py:564`): "postfix decompile I K S B W C @" |
| the res graft does an aperture check | `routines_x86_64_win64.py:1187–1199`: `cmp rax, r12; jb …; cmp [rax], IR_HOLE` |
| capability surfaces exist, but only implicitly | `IMPORTS` (`routines_x86_64_win64.py:31–33`; IR adds `VirtualFree`, `:1322`); linux `SYS_read/write/mmap/exit` at `routines_x86_64_linux_lo.py:59` (0, 1, 9, 60), aarch64 and riscv64 `:64` (63, 64, 222, 93) |
| memory, not Python, is the monolithic wall | decision 036: win64 monolithic `assembleOf` past about 85 GB before compaction; LO live set about 65 GB; naive exe on `LENB4` gives a 72 GB arena. Decision 030: retention, not drift. `reclaim`: only `none` is realized |
| a permanent region already exists | ADR-0005 lines 115–118: the derived-S template lives in a permanent region; the arena resets per root |
| the cost of spec_term's `pathOf` | `spec_term.py:2884–2910`: every one of 25 names runs **Python** lo + `seed.reduce_native` (**token marshal** of the full 71K-node spec) + **Python** cd |
| there is no CUDA gate | `ir_cuda.cu` header: same stdin/stdout contract, one thread per root, alloc accounting mirrors the kernel. It is referenced by no non-probe `host/*.py`. nvcc is installed (`CUDA\v12.1`). Decision 038: "cuda worker pending commit" |
| scratch is now tracked | `9831de6` "probes commit" (73 files). Tracked scratch: 77 `_*` at root, 17 `host/_*`, 41 `scratch/`. All recoverable from `9831de6` |
| three incompatible PLEX headers | `plex/core/format.py`, `plexus/crates/plex-core/src/wire.rs`, `plex-agent/src/dialect/bundle.py` (see `research/plex-wire-provenance.md`) |

### New gate-honesty finding (must be fixed first)

**G10 compares seed.emit against a cached staged image, not a fresh one.** `emit_chain.main --win64` calls `emit_image(..., workdir=emit_work/<tag>)` (`emit_chain.py:790–794`). The `_ck` checkpoints (`program.items`, `link.sections`, `text.bin`, `image.bin`) are keyed **by filename only** (`_ck` at `~:357`). The earlier failure line `3584B == 3584B (0s)` shows the staged side came entirely from cache.

So G10's recent pass means "`seed.emit` equals the staged image frozen in the last cold run". It does not mean the staged chain was re-derived. If staged terms change, a stale cache gives a **false pass**.

## 3. Waves

Each wave lists the only suites it reruns. Measured times: seed 289 s, emit_chain 276 s (warm cache), cross_verify 130 s, xisa 3 s, elfo 1 s, opt_peephole seconds. Per-gate spec_term times are unknown until W0b.

### W0 — gate honesty and cheap reruns (prerequisite for everything)

- **W0a. Key the G10 checkpoints by content.**
  - Each `_ck` key = sha256 over the stage's input identity: the `pack_ir_keyed` digest of the stage query term, `repr(R)`, and `text_base`.
  - Cache hits print `[ckpt hit <key8>]`.
  - A `--cold` flag uses a temp workdir.
  - The G10 record states the cache provenance.
  - **Decided: keyed + periodic cold.** A separate obligation, `G10-cold`, runs `emit_chain --win64 --cold`. It is tier `full`, flagged as a release gate, and never part of the per-change reruns.
  - Rerun: `emit_chain` (warm). The first keyed run is cold by construction, because no keys exist yet: a one-time cost, run in the background.
- **W0b. Per-gate selectors in spec_term.**
  - Add `--gate G9a,G9c,…` so `main` runs only the selected sections. The sections are already delimited (`spec_term.py:2884, 2912, 2954, 2994, 3031, 3080`, plus G9h, G9b, G9b-emit and the ADR-005 block).
  - Each obligation gets `args: ["--gate", "<id>"]`.
  - The battery runs an obligation per args set when a suite declares `per_gate: true`, and records status **per obligation id**.
  - Battery log lines get timestamps, which yields per-gate times.
  - Rerun: each selector once on its own section, to verify the selector works (cost = that gate only).
- **W0c. Proof check.** A deliberately stale checkpoint (a temp copy with a mutated routine constant) must FAIL G10 with the key-mismatch message. This is an in-memory or temp-dir test, not a repo edit.

### W1 — native byte egress (runtime → emitter pivot)

- **Mechanism.** A kernel output mode, `Realization.io = ("stdin", "bytes")`, declared in the `io` axis next to `stdin/stdout`. After a root's NF, walk the Scott byte list by **observation**, mirroring `_decode_bytecell`:
  - reduce `cell K` and `cell KI`;
  - apply each selector to 16 inert marker cells (reuse `IR_HOLE` cells, which already exist in the res path, `routines_x86_64_win64.py:1025`);
  - write the resulting byte.
- **Why observation rather than structural shape matching:** it is `O`'s decode (the QuotientMap decode), so it is independent of NF shape. `_cell_parts`' fixed-shape path is only a Python fast path (`spec_term.py:2568–2580`).
- **G16** (staging / congruence, regime `bytes`): `exe_bytes(PIR(t)) == _decode_bytecells(nf(t))` for byte-list corpora:
  - `bytelist_term` of random and edge bytes (0x00, 0xFF, empty);
  - the pack2Of **mini** NF;
  - one win64 section.
- **emit_chain** uses byte egress for the `pack*` stage, which removes crossing 6. G10 must stay green.
- Reruns: G16 (new, seconds to minutes), `emit_chain`.

### W2 — capability section and cap-subset gate

- **Declaration.** Each routines entry in `toolchain.json` declares `caps`: ports `stdin:R`, `stdout:W`, `stderr:W`, `scratch:RW+grow`, `payload:R`, plus OS bindings (`imports` / `syscalls`).
- **G18** (quotient / structural, tier fast):
  - for every realized toolchain, the **used** set, collected from the routines `Program` data (IAT imports; `SYS_*` immediates at syscall sites), must be ⊆ the declared caps;
  - emitter-role hosts must additionally have caps ⊆ {stdin R, stdout W, stderr W, scratch}.
- This makes "legal for this host" checkable, which the brief's acceptance criterion requires.
- Rerun: G18 only (seconds).

### Decided order

W0 → W1 (egress) → W2 (caps) → W4 (`peepholeOf`) → W5 (CUDA) → W3 spike (mini only) with the W6 ADR alongside. W7 stays a milestone.

### W3 — NF write-back and native stage driver (decided: mini-only spike + measurements)

**Goal:** remove crossings 3–5 (`_l0_nf` glue, `decode_program`/`decode_link`, the Python `assemble_staged` fold) without the monolithic memory wall.

**Open problem, stated honestly:** the decomposition is **data-dependent**. The number of per-instruction encodes is known only after the program NF, so a static multi-root stream cannot express it.

Spike:
1. **NF protocol.** A root's NF is either `DONE bytes` or `MORE [queries]`. The driver appends each NF to a **permanent region**, the same mechanism as the derived-S template (ADR-0005 lines 115–118), so later roots can reference it via a new `REF k` node tag (forward reference to an earlier root only; validated at load).
2. **Memory.** The per-root arena reset stays. Only NFs are retained, which bounds peak memory to the largest single stage plus the retained NFs. This must be measured against decision 036 numbers before committing.

Deliverables: ADR-006 draft; spike on the **mini** image (`emit_mini_image`) only; gate = mini image byte-equal to `_mini_oracle()` with zero Python decoding.

Win64 comes later. It has to be measured first, because the numbers from decisions 030 and 036 predict the retained-NF sizes.

### W4 — term-level `peepholeOf` (the H′ modification test)

- `peepholeOf` mirrors the `opt_peephole` rules over the item list: fallthrough jmp, unreachable after jmp/ret, jump threading, self-move.
- **G9i** (staging / seam, regime `bytes`): `decode_program(peepholeOf(programOf R)) == opt_peephole.optimize(program(R))`, on lo, for mini and win64 default. Its own obligation, not bundled into the long spec_term run.
- Remove the `NotRealized` refusal in `emit_image` for `R.peephole`. **G10** then gains a `peephole=True` leg that equals `seed.emit(R(peephole=True))`.
- Reruns: G9i and `emit_chain`.

### W5 — CUDA behavioural gate

- **G17** (quotient / congruence, regime `operEq` NF + `steps`/`alloc`, tier env, requires `nvcc` + GPU): `ir_cuda.exe` vs `native.x86_64.pe.ir` on identical PIR batches.
  - Batches: the G9b instances, the xisa probe corpus as PIR, fuel and malformed cases.
  - Checks for missing work: roots in == NF lines out, fuel → rc 2, malformed → rc 3, plus the `FUSE_S` build.
  - **No tempo claim.** Timing belongs to the cost family and needs Tw,C.
- The build goes through the existing `_build_cuda.bat` convention.
- Rerun: G17 only.

### W6 — bundle ADR (design only, no code)

ADR-006 covers:
- the canonical `.plex` header (choose one of the three, or declare a successor, with migration notes);
- sections as COO relations: PIR nodes, roots, symbols, caps, data relations, proofs;
- the mmap-and-run layout trade-off (9 B vs 24 B);
- the run-vs-emit roles from §1.

### W7 — bootstrap milestone (depends on W1 + W3 + W6)

- `H₀` = the seed emits a host with the bundle reader, the stage driver and byte egress.
- **G14:** `H₁ = H₀(bundle)`, `H₂ = H₁(bundle)`, and `H₁ == H₂ == seed.emit(R_host)`, plus probe congruence.
- **G15:** `H₁(bundle + peepholeOf) == seed.emit(R(peephole=True))`, and H′ is a fixed point. The seed route is the independent oracle, which defeats the trivial-copier objection.

### Independent tracks (any time)

- **Scratch triage.** `git rm` of the tracked scratch after you confirm the list: 77 root `_*`, 17 `host/_*`, 41 `scratch/`. Everything is recoverable from `9831de6`. Commit it separately, then move the bench/eval/demo layout toward bend's directory shape (`gates/ bench/ evals/ demos/ tests/`), driven by the registry tags.
- **spec_term cost.** Move the per-name native witness from token marshal (`seed.reduce_native`) to the IR batch path (`emit_chain.reduce_batch_native`, already used by G9b), keeping one independent reduction per name. The Python lo/cd witnesses stay per name, because that per-name independence *is* the congruence claim. A join fused-rule is a research item gated on an `OperEq` proof.

## 4. Verification discipline

- **No full `--tier all`** except as a release gate. Each wave runs `battery --only` over its own suites or obligations and merges records with the commit stamp.
- **Correctness-critical checks stay mine:** G10 cache provenance, the egress corpus, the cap-subset used-set extraction and the G17 comparison fields.
- **Every new gate gets a negative case** that must fail: a stale checkpoint, a corrupted byte, an undeclared import, CUDA fuel or malformed input.

## 5. Risks

- **W3 might not beat the memory wall.** Mitigation: a mini-only spike plus a measurement before any win64 claim.
- **Egress by observation costs 3 small reductions per byte.** Acceptable for images of about 4 KB. Measure on win64 before relying on it.
- **Per-gate spec_term selectors can hide cross-section coupling** (shared setup). Mitigation: a selector-run union must equal the full-run legs, checked once.
- **Scratch deletion is destructive.** It needs your explicit confirmation of the list, even though `9831de6` makes it recoverable.
