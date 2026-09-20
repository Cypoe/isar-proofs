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
| G9 | lambda_eval | witness 3: lambda LStep evaluator + Lean #eval spot oracle | lambda.lstep, lean.eval | · |

live column: `✓` suite ok, `✗` suite failed, `·` no battery record
(battery_last.json: battery_last.json)
