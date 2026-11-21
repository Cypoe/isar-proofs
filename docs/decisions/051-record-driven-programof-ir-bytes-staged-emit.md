# 051 — nanopass phase 2: record-driven programOf + staged IR emit

## Status

implemented — `spec_term.py` (`program_rt`, `program_query_rt`,
nibble-trie routine lookup, `fixed` generation axes, derived
λ-params nb-1/-nb, sentinel-leak refusal), `emit_chain.py`
(`emit_image` gains `rt`/`fixed`/`ir_ctx` threading; `_batch_bounded`
module-level seam), `gates_nanopass.py` (9 gates, all green).

End-to-end proof: `emit_image(Rb, rt=X86_64_WIN64_IR,
decompose_asm, decompose_pack)` → **6656B image, byte-identical to
`emit_native("native.x86_64.pe.ir")`** (sha bacc6505f91d01f2).
The production redirect+bytes kernel is now emitted entirely through
the staged record-driven chain — the self-emission gate.

## Model

Phase 1 split `programOf` into per-routine queries.  Phase 2 makes
the routine *set* itself term data:

- `program_rt(names_term)` — folds a serialized routine-name list
  through a static nibble trie (`_routine_trie`); each name resolves
  to its `routine_of` constant in-term.  A trie miss produces the
  malformed frag — decode refuses it (`bad item tag`), never skips.
- `fixed` — the generation-pinned axes.  Every Realization field
  outside the λ-spine (`order/alloc/abi/audit/io/ir_arena_bytes/
  payload/persist_bytes/reclaim`) is read by builders at Python
  generation time; pinning them into the term via `fixed` is what
  makes `ir_depack`'s reclaim/arena branches emit the IR variant
  instead of silently defaulting.  `_prog_axes` in emit_image is the
  explicit boundary.
- `ir_ctx` — record-level context flag (`any(n.startswith("ir_"))`,
  the same rule `_emit` uses); `mkapp_p` emits the IR node layout
  only when set.  Threaded as a generation input, not baked.
- derived λ-params — `ir_depack` computes `node_bytes - 1` and
  `-node_bytes`; a builder doing sentinel arithmetic would bake the
  literal.  These enter as two more spine parameters bound at the
  query boundary, and `_val_expr` now refuses unmapped sentinel
  values so future leaks fail loudly.

## Arena seam — bounded batches

`assemble_staged` pass 2 re-encodes every rel-sensitive insn with
the full resolver (`sym_t` + `loc_t` + end4) — each query re-carries
~135 symtab entries.  Measured on the production kernel: 32 roots
OK (6.2M nodes), 64 OOM (rc=4).  `_batch_bounded` halves on rc=4
until chunks fit — pure scheduling, queries are independent and
order is preserved.  Non-OOM failures propagate unsplit.  Same
helper wraps pass 1 (whole-list batches of 478 pass-1 encodes were
already near the edge).

## Numbers (record-driven IR emit, workdir=p2_ir)

| stage | host | cost |
|---|---|---|
| program.* × 26 | graph.lo | ~1–30s each, per-frag ckpts |
| link | `_rs.exe` (term_run) | 677K steps, 202s |
| pass1 478 encodes | `_rb.exe` ×4 | 27.9s |
| pass2 884 encodes | `_rb.exe` ×4 | 53.7s |
| pack* 6656B | `_rb.exe` ×4 | 4.7s |
| **wall** | | **469s** |

vs the same emit before checkpointing existed: program fold alone
was ~392s on the exe / 63s graph.lo just for `program`, plus a
944s link.  Per-fragment ckpt keys mean an edited routine misses
exactly its own key + `program.items`/`text.bin`/`image.bin`
downstream — `link.sections` survives.

## Found and fixed — _TRIE_DEAD was not dead

The old `_TRIE_DEAD` node was `PAIR KK (λk. K)`: descending one
nibble past an absent path returned bare `K`, not another dead node,
so the remaining nibbles unraveled into selector garbage and TLOOK
surfaced a malformed spine — misses only "worked" because no query
ever descended a dead path (gate 7 caught it: refusal arrived as a
downstream `nibble probe returned ...` decode error, not the
designed `bad item tag`).  Now `_TRIE_DEAD = M M` with
`M = λx. PAIR KK (λk. x x)` — a self-similar dead node: every dead
descent returns a dead node, the probe always ends on mv=KK, and
`mv miss hit` selects the refusal branch.  Hits are provably
unaffected (present keys never touch dead children).

## Caveats

- `program_rt`'s record fold is a single sequential term — the
  whole-record query is the *specification* path (what a self-hosting
  seed ingests); the staged emit still schedules per-routine queries
  since that's what checkpoints/parallelism want.  Both decode to
  identical item lists (gate 5/6).
- `_batch_bounded` retries re-pack query terms Python-side — bounded
  and small (~180KB per 64 roots) but not free.  The real fix for
  arena ceiling is the intra-process thread pool (Phase 5) or a
  bigger ir_arena — this is the honest bounded seam, not the
  performance endpoint.
- `fixed` pins at emit_image entry; a Realization mutated between
  generation calls could produce divergent frags — the checkpoint
  keys include `fixed` so stale artifacts can't be served, but the
  discipline is "treat R as immutable per emit."
