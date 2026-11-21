# 050 — nanopass phase 1: per-routine query-engine program stage

## Status

implemented — `spec_term.py` (`routine_expr`, `routine_of`,
`pass_term`/`PASS_TABLE`, `routine_query`, `decode_frag` extracted
from `decode_program`), `emit_chain.py` (`emit_image` gains
`routines`/`passes`; `decompose_asm` program stage runs per-routine
queries with per-fragment `_ck` checkpoints; `_ck_keys` emits
`program.<name>` keys), `gates_nanopass.py` (4 gates).

## Model

The program stage is now a query engine over fragments rather than
one monolithic fold:

- `routine_expr(name)` — `λfs λfuel λrbb λcb λnb. <frag>` for a
  single routine; same sentinel-diff splice machinery as
  `program_expr`, scoped to one builder call.  fs-conditional
  routines (`st_s` iff `fuse_s`, `build_ds` iff not) keep the
  conditional in-term — the frag is emitted or NIL, never a
  different signature.
- `routine_of(name)` — `bracket(routine_expr)` memoized per name;
  each routine's constant builds lazily and independently.
- `routine_query(name, R, passes)` — the fragment application plus
  the routine's pass chain (`passes` in pipeline order, applied as
  `p2(p1(frag))`).  Every pass is a real term reduction; the spine
  is data at the boundary.
- `PASS_TABLE`/`pass_term` — named frag→frag pass terms as data:
  `id` (I) and `peephole` (`λf. snd(PEEPHOLE_PASS u r s f)`).
  Unknown names raise ValueError — a misspelled pass must not
  silently become identity.

The monolithic `programOf`/`linkOf` stay — they are now the
equality oracle for the query-engine path.

## Gates (`host/gates_nanopass.py`, 4/4)

1. **frag-concat == monolithic** — 23 per-routine frags decode and
   concatenate to exactly `decode_program(program_query)`: 553
   items, identical (84,506 steps monolithic vs 224,486 summed
   per-routine — per-frag queries lose cross-routine sharing but
   bound the live set per reduction; batching on the exe pool is
   the trade).
2. **per-routine invalidation** — swapping one builder changes
   exactly `program.<name>`, `program.items`, `text.bin`,
   `image.bin`; all other frag keys and `link.sections` unchanged.
3. **pass refusal** — unknown pass names raise; a pass returning a
   malformed item (`["bogus"]` tag) fails `decode_frag` with
   `bad item tag` rather than smuggling shape downstream.
4. **id chain transparent** — `passes=("id","id")` decodes
   identical to no passes.

Byte-equality exercised end-to-end: `emit_image(Realization(),
decompose_asm, decompose_pack, workdir, bytes_run=_rb.exe pool)` ==
`emit_native()` — byte-identical 3584 B, per-fragment checkpoints
`program.<name>.<key>` all written under `emit_work/p1/`.

## Boundaries / non-claims

- Per-routine totals (~2.7× the monolithic program steps) pay for
  re-derivation of shared subterms; the win is independent,
  checkpointable, bounded-live-set reductions — and the term
  ingress is per-frag so `pack_ir` no longer walks one ~12M-node
  constant per emit.
- `R.peephole` remains a whole-program pass: per-routine frag NFs
  are re-consed into programOf's frag-list shape for the seamed
  fixpoint (`peephole_fixpoint_seamed`), since labels/dispatch can
  cross routine boundaries.  Per-frag checkpoints then hold the
  PRE-pass items (the pass's real input); the `program.items` key
  carries the peephole marker as before.
- `passes`/non-default `routines` with `decompose_asm=False` raise
  `NotRealized` — the monolithic assemble path has no chain entry
  point, so silent no-op is refused.
- Frag-level `peephole` pass exists in `PASS_TABLE` and is correct
  (verified on `mkapp_p`), but in-term peephole is ~94K steps on a
  2-item frag on graph.lo — production use goes through the seamed
  driver or the exe pool, not the in-term fold.

## Next

Phase 2: `programOf` generated per routines-record (routine-list +
io selector as term-level record data) — unblocks staging the
redirect+bytes IR kernel, which is the self-emission path.
