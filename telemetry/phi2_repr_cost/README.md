# phi2 representation-cost telemetry (decision 065)

Executed-evidence dataset for the nibble-chain -> byte-domain map
rewrite. Rows in `rows.jsonl`; the "before" map is pinned byte-for-byte
as `nibble_map_9bb305a.plex` (sha256 `e5235bde...`, identical to
`git show 9bb305a:phi2/maps/assemble_x86_win64.plex`). The "after" map
is the committed `phi2/maps/assemble_x86_win64.plex`.

## Semantics of the columns

- `steps`, `alloc`, `gc` — reducer counters from stderr
  (`steps=... alloc=... gc=...`); deterministic, wall-clock independent.
- `wall_s` — wall clock; varies with machine load.
- `rc` — reducer exit code. `0` = take-1 stream reached NF within fuel,
  `2` = fuel-cap (2e9 steps, i32-immediate ceiling), `4` = arena OOM
  (2GiB live set), `None` + no steps = outer 1800 s timeout.
- `sols` — decoded solution count of the take-1 stream.
  `sols=null` = not decode-checked (fuel-cap/OOM rows produce no NF).

## Probes

All via `eval<menv>` on `take 1`, `gc=sweep`, `reclaim=redirect`,
arena 2 GiB. Ops are `'op('push_r64 'rbp)`/`'op('ret)` enc'd term-form;
pc zero = 8 nibbles (`nibble`) resp. 4 LE bytes (`byte`). Eval env =
call-cone closure of the probe root over **all** `phi2/std/*.plex`
bundles + the map bundle (see trap note below).

## Reading the pair

- Nibble map: `enc2` solves (gate-verified fasmg bytes); `enc2_len`,
  `pass1`, `assemble` all OOM the 2GiB arena — the frag-0025 wall,
  reproduced under the reordered evaluator. Mechanism: 8-nibble
  succ-chains build a live set GC cannot reclaim.
- Byte map: `byte_add`/`enc2`/`enc2_len`/`pass1[ret]` all decode real
  sols (first machine-verified `pass1`/`enc2_len` results ever).
  Multi-op `pass1`/`assemble2`/`assemble` fuel-cap at 2e9.
- Residual wall mechanism (measured, not hypothesized): `eval.phi`
  threads one assoc-list subst through every nested `'call`;
  `subst_lookup` scans it linearly. Host instrumentation of the same
  relations: +2,372 walks/op, +164 bindings/op ⇒ quadratic in op
  count. Discriminating native probe `pass1[ret]@pc=1` = 548,555,085
  vs @pc=0 = 548,551,658 (Δ=3,427): op-2's intrinsic work is
  identical — the op-2 marginal inside `pass1[ret,ret]` is
  accumulated subst depth. 769 ops ⇒ ~10^14 steps ⇒ unreachable.

## Third pass: trie subst (frag 0027) — quadratic cleared

`eval.phi`'s subst is now a declared-data binary trie keyed on
little-endian bit-list ids (`sget`/`sput`/`sput_new`/`binc`; `beq`
total on bit lists so var-var unify needs no `RUN` eval). New
rows tagged `trie` / `trie-persist-wall`:

- `pass1 [ret,ret]` 816,333,786 steps sols=1 (was rc=2 cap);
  `pass1 [push;ret]` 848,245,370 sols=1 (was rc=2 cap);
  `assemble [push;ret]` 2,701,513,499 sols=1, bytes `55 c3`
  fasmg-MATCH; `assemble [lab;call;ret]` 2,715,233,833 sols=1,
  bytes `e8 fb ff ff ff c3` fasmg-MATCH.
- Marginal ~constant ≈410M/op through 8 ops (ret8 =
  3,280,724,518): the quadratic is gone.
- New wall: `persist_bytes` (256 MiB default) — the input-tier
  reduct cache below `irstart`. Multi-op eval fills it → `exit4`
  at ~230 s invariant to `ir_arena_bytes` (2/8/16 GiB). Sizing
  axis: 1 GiB covers 2-op `assemble`; 2 GiB covers 8-op `pass1`.
- Trie overhead costs ~+20% steps on small substs
  (`enc2_len ret` 483M vs 397M assoc) — per-bit descent only
  wins beyond ~100 bindings.

## Fourth pass: full-src — the persist wall is structural (frag 0028)

The imm32 ceiling on `persist_bytes` was an encoding accident —
widened to imm64 (`4720a08`). Full-src (769 items, take-1,
`fuel=None`) then gave a clean discriminator series:

| persist | pass1 full-src | assemble full-src |
|---|---|---|
| 1 GiB | rc=4 @ 277.0 s | — |
| 2.147 GiB | rc=4 @ 1841.3 s | rc=4 @ 1923.1 s |
| 16 GiB | rc=4 @ 24890.9 s | — |

Instrumented (`stats_p` on exit2/exit4 + `pfree=`): the zone
saturates early and rides the `flhead_p` recycling boundary
(`pfree`=16 saturated at 500M steps on ret64@1GiB, still alive at
2G+); `alloc≈1.5×steps`, `free≈alloc` — the dynamic arena reclaims
nearly everything. The concede is the first collect that frees
~nothing (`ret16`@256MiB: `gc=977` before rc=4).

Mechanism: `gc_collect` marks **every input cell `[permend,pcur0)`
as a root** — input-descended reducts (FWD'd into persist) are
pinned forever, so live-persist = the cumulative derivation
closure, monotone and unbounded for a single long root. The
pay-once memoization is built for *streams of small roots*; a
774-item take-1 is the shape it cannot serve. The OOM wall-times
are where the pinned closure crossed each cap — no finite cap
suffices. MEGAPLAN §7 misses at the full-src scale; closing it is
a retention-model decision (mark roots = the live root's cells,
not all input), i.e. new substrate — outside the freeze.

## Measurement traps (recorded)

1. **Absent-rel envs fail silently as empty streams** (~1.2M steps).
   An earlier pass omitted `arith_nibble_carry` from the nibble env
   (`nadd_b`→`nibble_succ` unfound → ∅), which read as "fast
   semantic failure" before decode-verification and full-env reruns
   exposed it as a harness artifact. `rc=0` alone proves nothing;
   check `env_rels` against the map's call-cone.
2. `take 2` on a single-sol stream forces proof of no second sol —
   far pricier than `take 1`. All rows are take-1.
3. Fuel-cap rc=2 and OOM rc=4 are different failures: fuel is an
   i32 immediate (2e9 ceiling); OOM is arena live-set.

## Reproduction

Runner: `_scratch/_telemetry.py` (uncommitted tooling; the `.plex`
fixtures + this manifest pin everything data-side). Goal shape:
`'call('sym rel, pair(arg-list, 'var 0))` enc'd term, eval env =
call-cone closure of the probe root over `phi2/std/*.plex` + map.

## Fifth pass: the wall was an allocator-policy bug — fixed (frag 0029)

The "mark roots = the live root's cells" fix was implemented as
the experiment: scan `[irj, irnroots)` only, traverse through
input cells, clear input marks post-collect. **Refuted** — live
persist at concede was cap−16 (`plast=0`): the memo table is
genuinely reachable, not dead-pinned.

The effective fix: **final-root dynamic routing**. Persist exists
because input cells must not point above `irstart` (per-root
decommit); the last root's FWDs have no future reader, so
`r_mkapp_p` routes `irj == irnroots-1` reducts to `mkapp`. Result:
`ret16 @256MiB` went rc=4@656s → rc=2@33s with `pfree`=full,
`plive=0`, gc=9. Full-src `pass1` fuel-caps at 2G steps in ~34s
and survived >35G steps under a 4 GiB arena — the bound moved
from space to wall-clock. Rows tagged `fix` carry the new stats.

## Sixth pass: what remains — step-count substrate

Live set is bounded; the cost is now **~410M reductions per source
op** ×774 ≈ ~320G steps ≈ hours. That is the eval.phi-on-
machine_term metacircular expansion, identical step count in the
Python witness. Levers: clause compilation vs interpreted
dispatch; an inet-shaped host substrate instead of SKI-as-
substrate (SKI was the Lean-proof shorthand, not the model —
decision 067 direction note).
