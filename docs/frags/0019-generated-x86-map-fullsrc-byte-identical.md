---
type: frag
id: 0019
provenance: host/gen_x86_map.py + phi2/maps/assemble_x86_win64 + plexus/rel.rs
ts: 2025-01-01
tags: [cogen, emit-chain, x86, pe64, generated-map, full-src, rel-rs]
---

# 0019 — generated x86 map: full-src byte-identical, runnable PE

## What landed

`host/gen_x86_map.py` — a row→clause translator that synthesizes
`phi2/maps/assemble_x86_win64.phi` (56 rels, ~380KB) mechanically
from `host/isa_x86_64.py`'s mined tables (INSN/ENCS/FIELDS/PREDS +
register tables) and `target_pe64.symbols` — replacing the 18-rel
hand-written map. No per-form hand-writing: one `enc2`/`enc2_len`
alternative per ENCS row, ordered alternatives made exclusive via
explicit flag rels (`se8f`/`i32f`/`accf`/`nlzf`/`nlff` totals, not
negation-as-failure).

## Verified

- **Full-src byte-identical**: `routines_x86_64_win64.program(R)` —
  568 items / 505 insns / 38 form shapes / 63 labels — assembled by
  the map on rel.rs in **64s**: 2053 bytes, byte-identical to
  `isa_x86_64.assemble`. `pass1` label offsets: 63/63 correct.
- **Runnable PE**: the map-produced `.text` packed through
  `target_pe64.pack` → `_blobs/mapg_seed.exe` is **byte-identical**
  to `seed.emit()`'s output (4096B) and runs: rc=0, `I`,
  `steps=0 alloc=20` — same as the native seed.
- All 38 exercised form shapes give exactly 1 length solution
  (deterministic encode path); clean-exit path re-verified
  end-to-end (rc=0 through the real-layout IAT at 0x1078).

## Notable semantics found en route

- **`nibble_add_b` latent corpus bug**: recursive clause missing its
  `b≠0` guard → phantom wraparound second solution at `b=0`;
  diverges on re-pull. Fix chosen: the map is self-contained — a
  local guarded ripple adder (`nl_add`/`nadd_b`/`nadd_h`) plus a
  declared `rflo` table (regfield<<3 + rmlo, 64 rows) replace the
  corpus adder and builtin `add` (which crashes on re-pull in the
  Python witness).
- **`_mem_modrm` needs a 7-way exclusive partition**: disp=0 splits
  on base-lo {∉{4,5}, =4(SIB), =5(rbp/r13→disp8)}; nonzero splits
  on {se8, !se8} × {lo4?, else}. The earlier 4-case version was
  ambiguous (`disp=0 & lo∉{4,5}` matched two clauses).
- **REX correctness**: `w` role applies the *row's* W flag
  (`0x40 + 8·w`, passed per-row as `vb`), `hx4` must emit
  `ATOM(4,·)` (bplus's counter is nibble-typed), REX suppression
  preserves 0x40 only when no referenced operand is a needing
  byte-reg (`rnx` over R/B-referenced operands only).
- **Guard positions can't hold calls**: `rel<args> = pat` in a
  clause guard parses as `call_term` inside unify — `enc_env`
  can't encode it. Move to body goals (3 sites: accf, phi, rex_w).

## Cost/honesty notes

- The Python witness's superlinearity was **subst dict-splat**:
  `unify` bound vars via `{**s, k: v}` — an O(|subst|) copy per
  bind while the subst grows with spine depth → O(n²). Profile:
  22.1s of 30.5s in unify's own body (n=30 pass1). Replaced with
  a persistent int-keyed Patricia trie (`_PMap`, O(log n) ops —
  the same persistent-map discipline as rel.rs's im::HashMap):
  pass1 n=30 → 3.2s, n=120 → 14s (linear ~0.11s/item), and the
  **full 568-item assemble now completes in the Python witness:
  450.8s, 2053B, byte-identical** (needed a 128MB-stack thread —
  the 568-deep generator nesting is the remaining C-stack wall).
  Side effect: interpreter² probes ~2× faster too.
- For comparison, the native staged emit
  (`emit_chain._assemble_stream`) needs no substitution at all:
  one independent `encodeOf` root per item, oracle-predicted
  lengths, resv-closed symtab/loc data inside each frame —
  "frames concat to .text directly, no substitution bookkeeping".
  That is the O(n) architecture the relational map mirrors on a
  spine fold (pass1's pc-threading is the only serial
  dependency).
- `dialect.py` selftest's stale `rels==27` (predated this work)
  updated to the true stdlib count 30 — gate restored, battery
  fast tier: 31/31.
