# 060 — real-target map + emit seam closes; interpreter² demoted to milestone leg

## Decision

`phi2/maps/assemble_x86_win64.phi` is the real-target assembly map:
pc-threaded, rip-relative fixups resolved in-corpus via nibble-domain
borrow subtraction against declared `symtab` constants mirroring
`target_pe64.pack`'s layout. `_cogen_emit.py` closes
decode→pack→diff→run for both the toy and clean-exit programs —
`cogen_exit.exe` returns 0 via a real `ExitProcess` IAT call whose
displacement was computed inside the corpus.

For rt-map probes, `expected_sols` are recorded as
`enc_t(direct mapg2 assemble)` — verified term-identical to the
`eval<menv>` sol on the toy path. The Python witness cannot afford
interpreter² on the 29-rel env (minutes per instruction).

## Reasoning

- One `ret` through `eval<menv>` on the rt env = 372K relcalls /
  81M walks / 49.7s in rel.rs. The interpreter² constant is
  ~100× the toy env's. At 505 insns this is hours — not a dev loop.
- The corpus `eval` is the *specification* of interpretation —
  deliberately naive. Optimizing the map to suit it inverts the
  invariant: maps stay honest, engines get faster.
- Symtab constants are declared data mirroring the writer's layout;
  the byte-for-byte diff is the drift check between them (per
  contract: composition is declared data; refusal names the axis).

## Consequences

- `rel.rs` gains a 1GiB worker stack in `plex_rel` for interpreter²
  recursion depth.
- Next: widen `enc2` to the seed program's 38 forms — generate rows
  from mined ENCS/FIELDS data (`enc_core.interpret` is already
  table-driven; a row→clause translator is the synthesized-map move).
- If interpreter² must run the real src: clause-template compilation
  in rel.rs is the structural fix (kill per-activation `lift`).
