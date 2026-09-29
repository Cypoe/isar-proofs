# wip/lean — folded

All work files have been folded into `src/ISAR/`:

- `_hdev_total_work.lean` → `HeapDev.lean`, before `HDevChain`
  (`HSteps`/`oldSub` measure machinery; `HDev_total` itself remains
  the open target per decision 028).
- `_decide_probe.lean` → `SpecVocabulary.lean` (`nibadd_table`,
  `nibcarry_table` — the license for a fused nibble-add rule).
- `_spec_adder_work.lean` → `SpecVocabulary.lean` (`fold_read` was
  `fold_read_sc`; `b4add_b4cla_basis`).

Kept: `_spec_assoc_work.lean` — fully folded, kept as the shape
reference cited by `src/ISAR/SpecVocabulary.lean`.
