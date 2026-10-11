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
  `2` = fuel-cap (2e9 steps, i32-immediate ceiling), `None`+no steps =
  outer 1800 s timeout.
- `sols` — decoded solution count of the take-1 stream.
  **`sols=0` is an empty-stream semantic failure**, not a fuel wall:
  the evaluator scanned all clauses and produced nothing.
  `sols=null` = not decode-checked (fuel-capped rows).

## Probes

All via `eval<menv>` on `take 1`, `gc=sweep`, `reclaim=redirect`,
arena 2 GiB. Ops are `'op('push_r64 'rbp)`/`'op('ret)` enc'd term-form;
pc zero = 8 nibbles (`nibble`) resp. 4 LE bytes (`byte`).

- `byte_add` — `byte_add<200,55>` (byte map only; declared computed rel)
- `enc2` — single-op emission
- `enc2_len` — single-op length
- `pass1` — label/pc sweep over 1 or 2 ops
- `assemble2`/`assemble` — full emission over `[push rbp; ret]`

## Reading the pair

Nibble map: `enc2` solves (gate-verified fasmg bytes); `enc2_len`,
`pass1`, `assemble` all return **empty streams** — a machine-eval
semantic divergence in the nibble-chain length machinery, not cost.

Byte map: `enc2`, `enc2_len`, `pass1[ret]` all produce real sols
(first machine-verified `pass1` result ever). Multi-op `pass1`/
`assemble2`/`assemble` fuel-cap at 2e9 — residual corpus-eval cost,
still open.

## Reproduction

Runner: `_scratch/_telemetry.py` (uncommitted tooling; the `.plex`
fixtures + this manifest pin everything data-side). Goal construction:
enc'd `'call('sym rel, pair(arg-list, 'var 0))`, eval env = call-cone
closure of the probe root over std+map corpus.
