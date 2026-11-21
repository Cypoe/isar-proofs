# 039 — Residual-as-payload: the Futamura-2 artifact is an exe with a static blob

## Decision

`x86_64.win64.res` realizes the specialized program as **code + static data**:
the residual term's `pack_ir` bytes are baked into `.data` via
`Realization.payload` (initialized data slots, `(name, size, init)` 3-tuples),
and the kernel depacks it once at entry into a permanent cell region.
`IR_VAR` records (0xFE) — still rejected on the wire — depack to hole cells
(tag 8, `l=varidx`).

Per dynamic argument (one packed-IR root per stream element, same wire
contract as `x86_64.win64.ir`), a **graft loop** copies the residual into the
bump arena: `remap(child) = child inside [rescells, +24*resn) ? (hole -> arg
else +delta) : verbatim`. No division — the mkapp run is contiguous so the
out-twin of a residual cell is a constant pointer offset. Leaf cells copy via
`mkleaf(tag)`, apps via `mkapp(l', r')`; both count in `nalloc`.

## What this is not

- Not evaluation: `v1` stays a live hole; the exe takes the dynamic input at
  runtime. Graft = structural substitution `residual[1 := arg]`, done by the
  emitted program, not by Python.
- Not constant-emitting: the payload is the unreduced residual; reduction
  happens per-arg inside the same reducer core the token/IR kernels use.

## Verified

- `K v1 K` residual, args `{I, S, (S K)K, I I}`: byte-identical NF lines vs
  `reducer_ir.exe` on the instantiated batch (`steps=12` both).
- G9b residual (747K tree nodes -> 96,635B payload -> 101,888B PE): all 20
  names through `res_g9b.exe` in 3.0s, `steps=5,784,576` — identical step
  count and NFs vs the pooled instantiation path.
- `fuel=1` -> rc 2; `VAR` on the wire / garbage -> rc 3; fuse_s variant
  byte-identical vs `reducer_ir_fuse.exe`.
- `native.x86_64.res.fasmg` assembles the same program through fasmg:
  identical NFs/stats (behavioral witness, encodings differ legally).

## Accounting note

`alloc` differs structurally from the depack-an-instance path: the res kernel
counts `resn` depack cells once + `resn` graft cells per root, while the IR
kernel counts depacked cells of the fully-instantiated term. Same basis,
different construction — documented, not a semantic difference.

## Permanent gate

`spec_term.main()` G9b-emit block emits `emit_work/res_g9b.exe` and compares
each NF line against `reduce_batch_native` output under `quote_surface`
(basis view -> surface view).

## Files

- `host/routines_x86_64_win64.py`: `r_res_entry`, `r_res_depack`,
  `r_res_reduce`, `r_res_remap`, `ROUTINES_RES`, `data_slots_res`,
  `X86_64_WIN64_RES`; `IR_HOLE=8`.
- `seed/seed.py`: `Realization.payload`; `emit()` resolves callable
  `data_slots`.
- `host/target_pe64.py`: `build_data` writes init bytes + zero-fill tail.
- `host/target_fasmg.py`: `symbols` tuple-safe; `pack` emits `db`/`rb`.
- `host/toolchain.json`: `x86_64.win64.res`, `native.x86_64.res`,
  `native.x86_64.res.fasmg`.

## Trap hit during bring-up

`("p", sym)` loads need `lea_r64_rip` (address-of) vs `mov_r64_rip`
(load-through) — the payload slot holds the *bytes*, not a pointer.
And routine emission is fall-through: a routine ending in `call` must end
with an explicit `jmp` or it falls into the next emitted label.
