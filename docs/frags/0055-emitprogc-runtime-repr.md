---
type: frag
id: 0055
provenance: devin-cli
ts: 2026-10-30
tags: [koru, host2, emitprog, runtime, repr, perf]
---

# 0055 — emitProgC runtime repr: rope str, frame envs, Res pool, cached Vals

The compiled lane's memory profile after `kwir` landed was the
known bad shape: ~4.4GB peak on the 906 wire, ~9.9GB on 905 —
nearly all of it runtime allocation, none of it semantics. Four
representation changes in `KoruProgEmit.prelude`, all invisible
to the program's observable output:

1. **`str` is a rope.** `S{n,p,l,r}` — `++` conses a node (O(1));
   `s_flat` materializes + memoizes on first compare/print. Kills
   the `out ++` copy quadratic asymptotically — but measured
   honestly: alone it moved peak RSS ~5% and *cost* time (node
   allocs). The quadratic was real but not the dominant term at
   this corpus size.
2. **Env is frames, not conses.** `E{cnt,ns,vs}` — `genNamedArgs`
   emits a static literal name table (`an_N`) + one `efr` alloc
   whose `vs` is memcpy'd into the same allocation. One alloc per
   call where `ecn` spent N allocs + N name `xsd`s. Scan order
   (most-recent-first) is preserved exactly, dup names included.
   `ecn` survives for single arm-binds; `elk` prefilters on
   `n[0]` before `strcmp`.
3. **`Res` is pooled.** `rn` pops a freelist (next ptr stashed in
   `->v`); consumers `rfree` after the next Res exists — subflow
   frees `h` once dispatch returns, `t` once `ja` is extracted or
   `k==3` consumed; invoke-conts frees `ir` after its `ds` call.
   `br`/`jl` store the literal pointer — no `xsd`. A Res is freed
   by exactly one consumer site; `ds` never returns its own `r`,
   so no double-free and no static (`KSKIP`) ever enters the pool.
4. **`v_int`/`v_bool` are cached.** Vals are immutable post-
   construction (verified: no field writes outside `vn`-
   constructors), so `v_bool` is two statics and `v_int` returns
   shared slots for `[-1024, 8192)`. Identity is never observed —
   `veq` is structural and nothing pointer-compares Vals.
   Literal cells/strs also stop `xsd`-duplicating their names
   (`v_sref`).

Measured on the compiled lowerer (`-O0`, gate flags):

| wire | before | after | peak before | after |
|------|--------|-------|-------------|-------|
| 906  | 7.2s   | 2.1s  | 4425MB      | 1054MB |
| 905  | 14.3s  | 4.4s  | 9869MB      | 2248MB |

Output still byte-identical on 900/905/906 (graph slice vs
`korufe --lower`). The dominant remaining cost is structural:
every `.var` is an `elk` frame walk and every subexpression is an
`ev_N` call returning a boxed `Val` — the evaluator shape itself.
That is the codegen lane's problem (compiled tors, unboxed ints,
positional args), not the prelude's — named here so nobody
mistakes repr fixes for the end state.

Gate: 866 pass / 0 fail / 34 skip (unchanged; skips remain the
documented stack/time axes + forged rows).
