<!-- Generated from host/toolchain.json — do not edit. -->

# Obligations (gates)

| id | suite | what | witnesses | live |
| --- | --- | --- | --- | --- |
| G0 | seed | signature algebra: matrix identities + app/mul homomorphism + Lean-literal cross-check | — | ✓ |
| G0b | seed | signature-free emission: no matrix byte patterns, no s-beta in default .text | native.x86_64.pe | ✓ |
| G1 | seed | encoder byte-equality vs fasmg: per-row + whole .text, both builds | native.x86_64.pe, native.x86_64.pe.fuse_s | ✓ |
| G2 | seed | basis mirror vs graph.lo (full alphabet) + fused mirror vs reduce.py | graph.lo, tree.surface | ✓ |
| G3 | seed | native exe probes, both builds: stream boundary + Church deep terms | native.x86_64.pe, native.x86_64.pe.fuse_s, graph.lo | ✓ |
| G4 | seed | strategy variations (geometry, fuse_s) + cd refusal + fuel | native.x86_64.pe | ✓ |
| G5 | seed | host registration: choose -> cpu, native_realize, piece adoption | native.x86_64.pe, native.x86_64.pe.fuse_s, graph.lo | ✓ |
| G6 | spec_check | seams: seed section 0-3 contains no catalog names (transform owns interpretation) | — | ✓ |
| G6b | futamura_cube | cube: P0 == P1 across witnesses including graph.cd | tree.surface, graph.lo, graph.cd, native.x86_64.pe, native.x86_64.pe.fuse_s | ✓ |
| G8 | xdu_gate | native == runtime on stdout+rc (nibble transducer plex) | graph.lo, graph.cd, native.x86_64.pe | ✓ |
| G9 | lambda_eval | witness 3: lambda LStep evaluator + Lean #eval spot oracle | lambda.lstep, lean.eval | ✓ |
| G9a | spec_term | catalog-as-term: pathOf over toolchain.json (full spec) agrees across witnesses | graph.lo, graph.cd, native.x86_64.pe, python.walk | ✓ |
| G9b | spec_term | specialize pathOf against the static catalog (P1 shape); residual instances agree with direct queries | graph.lo, graph.cd, native.x86_64.pe, python.walk | ✓ |
| G9c | spec_term | resolveOf: emit stage 1 (toolchain.resolve) at term level — entry -> field names -> sections -> {module,record}; result = Scott list of 8 field strings ('!' = NotRealized shadow) | graph.lo, graph.cd, native.x86_64.pe, python.walk | ✓ |
| G9d | spec_term | symbolsOf: target.symbols at term level — imports/data-slots folds -> Scott assoc map name -> bytes4 RVA ('iat_' prefix by literal cons; i*8 and cumulative offsets as real bytes4 ripple arithmetic — the rep the assemble resolver subtracts) | graph.lo, graph.cd, native.x86_64.pe, python.walk | ✓ |
| G9e | spec_term | programOf: routines.program(R) at term level — generated λfs λfuel λrbb λcb λnb skeleton, per-routine fragment list, variant regions diffed from real builder outputs; immediates as bytes8 leaves; native deferred (exceeds exe 600s cap) | graph.lo, graph.cd, python.walk | ✓ |
| G9f | spec_term | encodeOf + assembleOf: isa.encode (ENCS nibble-trie + field interpreter) and isa.assemble's two-pass fold at term level — pass-1 label map (bytes4 pos = base+off), pass-2 resolver (symbols shadow locals = the link seam) emitting rel32 via B4SUB; gate on the mini program (fwd/bwd rel32, rip-sym, mem disp, shadowing, nonzero base); native deferred (same exe throughput ceiling) | graph.lo, graph.cd, python.walk | ✓ |
| G9g | spec_term | dataOf + idataOf + packOf: target_pe64's container writer at term level — build_data/build_idata folds (zero-fill + IAT records, lengths measured by LENB4) and the 448B PE64 header as literal chunks spliced with computed bytes4 fields; pads via PADLIST (rem=len&511 nibble-mask, rem TAIL z512) and JOIN right-assoc concat (linear emission); dataOf/idataOf gated lo+cd, packOf byte-for-byte vs target_pe64.pack on lo only (cd deferred: persistent-NF sweeps on image-sized NFs exceed routine-gate budget, >5k CPU s measured); native deferred | graph.lo, graph.cd, python.walk | ✓ |
| G9h | spec_term | linkOf + pack2Of + linkasm: the linker stage — section builders run once and export their symtabs; linkOf merges them into the global table assemble's resolver consumes (APPEND iat data = ALOOK last-match / dict.update order); pack2Of takes linked sections as inputs (no rebuild); linkasm assembles against the link-derived symtab end-to-end.  linkOf gated lo+cd at both scales; pack2Of lo+oracle (same measured cd deferral as packOf — image-sized NF); linkasm lo+oracle (composed-stage cd deferred — >50GB measured, the 027/028 retention pathology) | graph.lo, graph.cd, python.walk | ✓ |

live column: `✓` suite ok, `✗` suite failed, `·` no battery record
(battery_last.json: battery_last.json)
