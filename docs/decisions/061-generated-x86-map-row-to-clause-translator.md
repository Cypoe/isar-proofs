# 061 — x86 map is now generated: row→clause translator, full-src byte-identical

## Decision

`phi2/maps/assemble_x86_win64.phi` is **generated**, not
hand-written: `host/gen_x86_map.py` translates
`host/isa_x86_64.py`'s mined tables (INSN/ENCS/FIELDS/PREDS,
register tables) plus `target_pe64.symbols` into 56 rels. Each
ENCS alternative becomes one `enc2`/`enc2_len` clause; ordered
alternatives are made exclusive with total flag rels
(`se8f`/`i32f`/`accf`/`nlzf`/`nlff`), never negation-as-failure.
Operands: `'i(nl8)` imms, `'m(base,dnl)`, `'p(sym)`, `'l(label)`;
arithmetic is nibble-list throughout; fixups share one formula
`disp = target − (trva + pc + len)` for both local labels and
IAT/data symbols.

Verified: full `routines_x86_64_win64.program(R)` (568 items,
505 insns, 38 form shapes, 63 labels) assembles in 64s on rel.rs
to 2053 bytes **byte-identical** to `isa_x86_64.assemble`;
packed PE is byte-identical to `seed.emit()` output and runs
(rc=0, `I`, `steps=0 alloc=20`).

## Reasoning

- The hand map was ~9 forms; the program needs 38 of 50 declared.
  `enc_core.interpret` is already a table interpreter — the honest
  move was translating its data, not porting its loop.
- Corpus hygiene: captured std bundles stay untouched despite two
  latent defects found (`nibble_add_b` missing its `b≠0` guard →
  phantom sol + re-pull divergence; builtin `add` crashes on
  re-pull). The map carries a local guarded `nl_add`/`nadd_*` and
  a declared `rflo` table instead.
- `_mem_modrm`'s disp cases required a 7-way exclusive partition
  (disp0×{plain,sib,rbp-r13} + se8×{plain,sib} + disp32×{plain,sib});
  a 4-case version was ambiguous (disp=0 matched both nlz and se8
  clauses).
- `enc_env` encodability constraint surfaced: calls in guard
  position (`rel<args> = pat` between `|` and `{`) parse as
  `call_term`-in-unify — unencodable. Calls live in bodies only.

## Cost ledger

- Python witness: the superlinearity was `unify`'s `{**s,k:v}`
  dict-splat (O(|subst|)/bind → O(n²) on spine folds). `_PMap`
  (persistent Patricia trie, matching rel.rs's im::HashMap
  discipline) restores linear scaling — full-src now completes
  in the Python witness too: 450.8s, byte-identical (rel.rs: 64s).
  The residual C-stack wall (568-deep generator nesting) is
  worked around by a 128MB-stack thread.
- The native staged emit is O(n) by construction instead:
  `emit_chain._assemble_stream` emits one independent `encodeOf`
  root per item — oracle-predicted lengths, resv-closed fixup
  data inside each frame, "no substitution bookkeeping".
- interpreter² (`eval<menv>` on the ~80-rel map env) remains the
  milestone leg, beyond current budget (~50s/insn measured at 29
  rels, larger env now).

## Consequences

- New ISA form = add rows to `isa_x86_64.ENCS`, regenerate:
  `python host/gen_x86_map.py > phi2/maps/assemble_x86_win64.phi`
  then `python host/dialect.py --set phi.rel --file
  phi2/maps/assemble_x86_win64.plex < phi2/maps/assemble_x86_win64.phi`.
- `_rel_fullsrc.py` exports the 568-item probe with oracle-derived
  `expected_sols`; `_fullsrc_emit.py` decodes→packs→runs the PE.
- `dialect.py` selftest's stale `rels==27` corrected to 30
  (stdlib grew in an earlier commit without the assert) —
  `battery --tier fast` is 31/31.
