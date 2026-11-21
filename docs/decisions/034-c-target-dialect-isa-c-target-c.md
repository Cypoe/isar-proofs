# 034 — C-target dialect: isa_c + target_c records, native.c toolchain

Status: landed `327bb00` (host/isa_c.py, host/target_c.py,
toolchain.json, CATALOG.md).

## The slot

The emit chain `rts.program(R) -> isa.assemble -> tgt.pack` is
unchanged — C plugs into the same two record slots:

- `isa_c` (`C_ISA`, realized): C11 statements as data in the same
  `(label|i)` Program shape. Forms: `fn/end/if/elif/else/while/for/
  decl/assign/do/ret/break/continue/raw/note`. `assemble` emits
  indented source bytes + a label->byte-offset table; `symbols`/`base`
  are accepted and ignored — resolution is nominal.
- `target_c` (`C`, realized): `pack` wraps assembled text into a
  complete translation unit (banner + `#include` lines from `imports`
  + `static unsigned char` arrays from `data_slots` + text).
  `symbols()` returns the identity name table — C has no
  assembler-time addresses; `text_base=0`, `os="hosted"`,
  `abi="c11"`, `ext=".c"`.
- `routines c.hosted.lo` + toolchain `native.c`: **declared, not
  realized** — `routines_c` IS the second host (next stage). The
  loader refuses it honestly: `routines 'c.hosted.lo' not realized`.

## Verified

- `isa_c.main()` / `target_c.main()`: assemble -> pack -> clang ->
  run, rc=42, stdout `ok`. `find_cc` prefers clang, falls back
  gcc/cl (clang 18.1.8 present).
- `spec_term`: `pathOf native.c` -> `'runtime'` (220k lo steps);
  `resolveOf` -> `['bytecode_dialect','bytecode_map','isa_c','C_ISA',
  '!','!','target_c','C']` — the unrealized routines link shadows as
  `!` (the NotRealized shadow at term level).
- `toolchain.py`, `cogen.py`, `spec_check.py`, `spec_project.py` all
  green; CATALOG.md regenerated.

## Consequence for the kernel

`native.c` is `path: "runtime"` — the emitted artifact contains a
reducer reading `bytecode.postfix` from stdin, same contract as the
PE reducer. That is what makes cross-verification cheap: identical
stdin bytes to Python host and clang-built C host, compare
stdout+NF+stats. The kernel (`routines_c.program(R)`) must therefore
read the same token alphabet `I K S B W C @` and print the same
stats line shape as reduce.py/the PE reducer.
