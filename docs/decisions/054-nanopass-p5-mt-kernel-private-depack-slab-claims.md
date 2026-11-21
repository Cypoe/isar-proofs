# 054 — nanopass phase 5: multithreaded IR kernel (private depack + slab claims)

## Status

implemented and behaviorally gated.  `Realization.threads > 1` selects
the separate routines record `x86_64.win64.ir.mt` behind the toolchain
record `native.x86_64.pe.ir.mt`; `threads == 1` keeps the serial
`x86_64.win64.ir` program byte-for-byte (the MT scaling expressions
collapse at T=1).

## Design

Every routine has ONE source; the MT program is the same builder corpus
run through `_mt_xform`, which rewrites `("p",slot)` operands in the
thread-executed routines (`_MT_THREADED`) to `("m","r10",off)` ctx
fields.  r10 = the worker's `MT_CTX` block (192B, `mtctxs` array in
.data).  Main gets `ctx[T]` so xform'd vocab builders are valid
pre-spawn.  `("p","permend")` in depack alone remaps to `cellbase` —
same slot name, per-worker semantics.

- `ir_spawn` (main): reset `slabtop = permend`, zero ctx blocks, alloc
  per-thread output buffers, partition the stream's roots into T
  contiguous ranges, `CreateThread` per worker, `WaitForMultipleObjects`
  (bWaitAll), aggregate `nalloc`/`irsteps`/`dec`, `CloseHandle`, flush
  buffers in worker order = root order.
- `mt_worker` (thread proc): `lock xadd [slabtop], mtslab` claims a
  private slab inside the reserved arena (`ir_arena_bytes * threads`),
  depacks THE WHOLE STREAM into its claim (cells are private — no
  shared-mutable graph, no cross-worker FWD), reduces `[irj,jend)`,
  appends frames to its private output buffer, `ExitThread`.
- `grow_heap_ir` MT arm: commit-ahead inside the claim; at span end,
  claim another slab via the same `lock xadd`.
- `emit_bytes`/`emit_ir` MT arms: append `[u32 len][payload]` to the
  private buffer instead of WriteFile — egress stays ordered.

## The bug that cost a day: Win64 shadow space

`_mt_xform` brackets every `call_mrip` in threaded routines because
WinAPI calls clobber r10 (`mov r10,rcx` in the syscall stub).  The
bracket originally saved r10 at `[rsp]` after `sub rsp,0x10` — **inside
the callee's 0x20-byte shadow space**, which `VirtualAlloc`'s stub
legally writes (argument home addresses).  The restore reloaded a
kernel-written value (the arena base), so every post-call ctx write
went to `arena+off`: `irroots`/`nalloc` landed in arena memory, and the
root loop read garbage `irj/jend` → instant `mt_wdone` → clean
`ExitThread(0)` with zero work done.  Symptom: rc=0, empty stdout,
steps=0 — no crash, no error path, just silent non-execution.  Found by
a debug-API breakpoint at `ir_binit` reading live r10.  Fix: save at
`[rsp+0x20]` after `sub rsp,0x30` — above the callee's shadow, still
16-aligned at the call.

(The earlier entry crash was the same class: unwrapped `VirtualAlloc`
in `ir_entry` clobbered r10 between `lea` and ctx writes; re-lea after
the call.)

## Verified

`gate_mt_equiv` (gate 17): for io in stdout/bytes/ir x blobs in
{multi-root stream, two streams, empty} x T in {2,4} vs T=1 —
stdout bytes and rc identical everywhere; `steps` identical except
bytes-probe decode; `alloc` always differs (per-worker depack
duplicates the stream's cells — the honest cost of isolation).
Empty input → rc=3 on all variants.  `ir` frames are valid PIR
(29/92/173B roots) identical across T.  `dec` counters identical.

Steps divergence under bytes mode is real and explained: pack_ir
hash-conses shared subterms (e.g. list tails), and the serial kernel's
shared persist zone lets root r+1 hit FWDs written by root r's probe —
per-worker private depack forfeits exactly that cross-root reuse.
Observed +297 steps at T=2, +1160 at T=4 on the byte-list corpus.
This is a stat, not observable output; the equivalence contract is
stdout+rc.

## ISA / term-level additions

`add_m64_imm`, `lock_xadd_rip` (RIP-relative — `("p",slabtop)` can't go
through ModRM), and a `raw` field tag in the nibble encoding (mirrored
into `spec_term`'s F0..F7 dispatch so `encode_query` accepts it).

## Boundaries

- MAXIMUM_WAIT_OBJECTS: `threads > 64` refuses at program level;
  `threads <= 1`, `audit`, non-lo order, non-redirect/non-none reclaim
  all refuse too.  MT imports (`CreateThread`, `WaitForMultipleObjects`,
  `CloseHandle`, `ExitThread`) live only in the MT record's caps —
  no smuggling into serial records.
- Workers never share mutable state: each depacks the whole stream
  privately (O(T x stream) cell duplication, bounded by the scaled
  arena reservation).
- The spawn/flush main path is NOT xform'd — it owns shared slots.
