<!-- Generated from host/toolchain.json — do not edit. -->

# Obligations (gates)

| id | family | evidence | regime | tier | suite | what | witnesses | live |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| G0 | quotient | structural | — | full | seed | signature algebra: matrix identities + app/mul homomorphism + Lean-literal cross-check | — | skip |
| G0b | staging | structural | — | full | seed | signature-free emission: no matrix byte patterns, no s-beta in default .text | native.x86_64.pe | skip |
| G1 | staging | seam | bytes | env | seed | encoder byte-equality vs fasmg: per-row + whole .text, both builds | native.x86_64.pe, native.x86_64.pe.fuse_s | skip |
| G2 | quotient | congruence | operEq | full | seed | basis mirror vs graph.lo (full alphabet) + fused mirror vs reduce.py | graph.lo, tree.surface | skip |
| G3 | quotient | congruence | operEq | full | seed | native exe probes, both builds: stream boundary + Church deep terms | native.x86_64.pe, native.x86_64.pe.fuse_s, graph.lo | skip |
| G4 | quotient | congruence | operEq | full | seed | strategy variations (geometry, fuse_s) + cd refusal + fuel | native.x86_64.pe | skip |
| G5 | quotient | congruence | operEq | full | seed | host registration: choose -> cpu, native_realize, piece adoption — choose is a strategy, not selection-optimality | native.x86_64.pe, native.x86_64.pe.fuse_s, graph.lo | skip |
| G6 | staging | structural | — | fast | spec_check | seams: seed section 0-3 contains no catalog names (transform owns interpretation) | — | ✓ |
| G6b | staging | congruence | operEq | fast | futamura_cube | cube: P0 == P1 across witnesses including graph.cd | tree.surface, graph.lo, graph.cd, native.x86_64.pe, native.x86_64.pe.fuse_s | ✓* |
| G8 | staging | congruence | stdout+rc | full | xdu_gate | native == runtime on stdout+rc (nibble transducer plex) | graph.lo, graph.cd, native.x86_64.pe | skip |
| G9 | quotient | congruence | operEq | fast | lambda_eval | witness 3: lambda LStep evaluator + Lean #eval spot oracle (G9 = lambda witness 3; unrelated to G9a–h spec-as-term) | lambda.lstep, lean.eval | ✓ |
| G9a | staging | congruence | operEq | full | spec_term | catalog-as-term: pathOf over toolchain.json (full spec) agrees across witnesses | graph.lo, graph.cd, native.x86_64.pe, python.walk | skip |
| G9b | staging | congruence | operEq | full | spec_term | specialize pathOf against the static catalog (P1 shape); residual instances agree with direct queries | graph.lo, graph.cd, native.x86_64.pe, python.walk | skip |
| G9c | staging | congruence | operEq | full | spec_term | resolveOf: emit stage 1 (toolchain.resolve) at term level — entry -> field names -> sections -> {module,record}; result = Scott list of 8 field strings ('!' = NotRealized shadow) | graph.lo, graph.cd, native.x86_64.pe, python.walk | skip |
| G9d | staging | congruence | operEq | full | spec_term | symbolsOf: target.symbols at term level — imports/data-slots folds -> Scott assoc map name -> bytes4 RVA ('iat_' prefix by literal cons; i*8 and cumulative offsets as real bytes4 ripple arithmetic — the rep the assemble resolver subtracts) | graph.lo, graph.cd, native.x86_64.pe, python.walk | skip |
| G9e | staging | seam | bytes | full | spec_term | programOf: routines.program(R) at term level — generated λfs λfuel λrbb λcb λnb skeleton, per-routine fragment list, variant regions diffed from real builder outputs; immediates as bytes8 leaves; native deferred (exceeds exe 600s cap) | graph.lo, graph.cd, python.walk | skip |
| G9f | staging | seam | bytes | full | spec_term | encodeOf + assembleOf: isa.encode (ENCS nibble-trie + field interpreter) and isa.assemble's two-pass fold at term level — pass-1 label map (bytes4 pos = base+off), pass-2 resolver (symbols shadow locals = the link seam) emitting rel32 via B4SUB; gate on the mini program (fwd/bwd rel32, rip-sym, mem disp, shadowing, nonzero base); native deferred (same exe throughput ceiling) | graph.lo, graph.cd, python.walk | skip |
| G9g | staging | seam | bytes | full | spec_term | dataOf + idataOf + packOf: target_pe64's container writer at term level — build_data/build_idata folds (zero-fill + IAT records, lengths measured by LENB4) and the 448B PE64 header as literal chunks spliced with computed bytes4 fields; pads via PADLIST (rem=len&511 nibble-mask, rem TAIL z512) and JOIN right-assoc concat (linear emission); dataOf/idataOf gated lo+cd, packOf byte-for-byte vs target_pe64.pack on lo only (cd deferred: persistent-NF sweeps on image-sized NFs exceed routine-gate budget, >5k CPU s measured); native deferred | graph.lo, graph.cd, python.walk | skip |
| G9h | staging | seam | bytes | full | spec_term | linkOf + pack2Of + linkasm: the linker stage — section builders run once and export their symtabs; linkOf merges them into the global table assemble's resolver consumes (APPEND iat data = ALOOK last-match / dict.update order); pack2Of takes linked sections as inputs (no rebuild); linkasm assembles against the link-derived symtab end-to-end.  linkOf gated lo+cd at both scales; pack2Of lo+oracle (same measured cd deferral as packOf — image-sized NF); linkasm lo+oracle (composed-stage cd deferred — >50GB measured, the 027/028 retention pathology) | graph.lo, graph.cd, python.walk | skip |
| L0 | quotient | lean | — | env | lake | QuotientMap soundness + OperEq equivalence (Lean) | — | skip |
| L1 | cost | lean | — | env | lake | [size-Jones (static) — not runtime Tw,C] JonesOptimal over pe_cost = term_size on abstract PESetup, proved for JonesIdPE | — | skip |
| L2 | staging | lean | — | env | lake | Futamura projections 1-3 + square commutation over PESetup (Lean) | — | skip |

## Selftests

| module | tier | requires | args | live |
| --- | --- | --- | --- | --- |
| bytecode_dialect | fast | — | — | ✓ |
| fasm_dialect | fast | — | — | ✓ |
| graph_congruence | fast | — | — | ✓* |
| graph_runtime | fast | — | — | ✓ |
| host_pieces | fast | — | — | ✓ |
| isa_c | fast | — | — | ✓ |
| isa_fasmg | fast | — | — | ✓ |
| lambda_dialect | fast | — | — | ✓ |
| mine_adopt | fast | — | — | ✓ |
| observation_regime | fast | — | — | ✓ |
| opt_peephole | fast | — | — | ✓ |
| quotient_map | fast | — | — | ✓ |
| reduce | fast | — | — | ✓ |
| routines_aarch64_linux_lo | fast | — | — | ✓ |
| routines_riscv64_linux_lo | fast | — | — | ✓ |
| routines_x86_64_win64 | fast | — | — | ✓ |
| routines_x86_64_win64_cd | fast | — | — | ✓ |
| routines_x86_64_win64_xdu | fast | — | — | ✓ |
| spec_project | full | — | — | skip |
| strategy | fast | — | — | ✓ |
| target_pe64 | fast | — | — | ✓ |
| tower | fast | — | — | ✓ |
| xdu_dialect | fast | — | — | ✓ |
| cogen | full | — | — | skip |
| observational_suite | full | — | — | skip |
| toolchain | full | — | — | skip |
| congruence | env | lake | — | skip |
| lambda_congruence | env | lake | — | skip |
| lean_eval | env | lake | --with-lean | skip |
| isa_x86_64 | env | fasmg | — | skip |
| isa_aarch64 | env | llvm-mc | — | skip |
| isa_riscv64 | env | llvm-mc, llvm-objcopy | — | skip |
| routines_c | env | clang | — | skip |
| routines_x86_64_linux_lo | env | wsl | — | skip |
| target_c | env | clang | — | skip |
| target_elf64 | env | wsl | — | skip |
| target_fasmg | env | fasmg | — | skip |

## Benches

| name | module | measures | claim |
| --- | --- | --- | --- |
| graph_bench | graph_bench | tree_ms, graph_ms, tree_steps, graph_steps, alloc | none — report, not a cost obligation |
| compare_lo_cd | compare_lo_cd | ms_lo, steps_lo, ms_cd, rounds_cd | none — report, not a cost obligation |
| lambda_bench | lambda_bench | ms, b, i | none — report, not a cost obligation |
| diag | diag | wall_ms, rss, engine NF agreement | none — report, not a cost obligation |

## Demos

| name | entry | what |
| --- | --- | --- |
| xdu-programs | programs/xdu | sample xdu.json plex programs (drop0/echo/hexdump/toggle) — inputs for the native xdu path |
| zoo-explorer | zoo/explorer.html | Formal Systems Zoo — static interactive explorer page |

live column: `✓` pass, `✓*` pass with skipped legs, `✗` fail, `skip` whole-suite skip (env/tier), `·` no battery record
(battery_last.json: battery_last.json)
