---
type: frag
id: 0027
provenance: devin-cli
ts: 2026-10-12
tags: [phi2, eval, subst, trie, bit-list, quadratic, decision-065,
       pass1, assemble, gc-sweep, persist]
---

# 0027 — declared substitution-strategy change: assoc list -> LSB-first bit trie; quadratic cleared, `assemble` runs to NF with fasmg-verified bytes; new wall was persist zone, not subst

## What landed

`phi2/eval.phi`'s substitution is now a **binary trie keyed on
little-endian bit-list var ids** — a declared-strategy change inside
corpus data, no host/engine special-casing:

- node = `[L|[V|R]]`, `V` = `[]` or `[v]`; empty trie = `[]`.
- `sget`/`sput`/`sput_new` recurse on `['atom([1|b])|kb]` key
  spines — list descent, no arithmetic on keys.
- `binc` = little-endian carry increment; ids are bit lists, so
  sequential ids keep the LSB-first trie balanced by construction
  (Okasaki–Gill IntMap — no rotations in a relational encoding).
- `beq` = total structural equality on bit lists, yields exactly
  one of `'yes`/`'no` (deterministic, so `unify_w` calls it
  directly — no `RUN`-collected nested eval per var-var unify).
- Trie overwrite ≡ assoc first-match shadowing: same key ⇒ same
  slot.

Retired: `subst_lookup` (linear assoc scan) and `next_id`
(peano-atom counter). Var ids were `ATOM(8,i)`; they are now bit
lists, and `n` threads through `ren_fc` via `binc`. `walk`,
`unify_w` (3 bind sites), `ren_fc` rewired; `ren` stays assoc
(per-clause, small); `env_find` stays assoc (~50 rels, constant).

Machine mirror `phi2/seed.py` mirrors all of it:
`sget`/`sput`/`sput_new`/`binc` lts + `_bitval`/`_mkbit` helpers;
`unify_w` var-var via `eq_term` (the machine's `beq` mirror).
Two real bugs were found and fixed by H0 tests: `_bitval`
under-applied the inner cell (needed `snd∘payload` ×3), and the
node destructures applied `mkcell`s to single lambdas instead of
`_payload`-then-`_cellpl_body`.

`realize.phi`/`runtime.phi` callers updated (`n=1` → `[1]`).
Gate `np_gates_rel` and the telemetry runner decode tries
(`sol_subst` walks `[L|[V|R]]` nodes; `bits_dec` reads ids).

## Measured (native, machine_term + ir exe, gc=sweep)

All rows byte/structure-decode-verified; steps are reducer
counters, deterministic. `pass1 1op` numbers are env=33 rels.

| probe                  | assoc subst (before)        | trie subst (now)            |
|------------------------|-----------------------------|-----------------------------|
| enc2_len ret           | 397,420,827 sols=1          | 482,770,084 sols=1          |
| pass1 [ret]            | 548,551,658 sols=1          | 504,980,199 sols=1          |
| pass1 [push]           | —                           | 439,124,305 sols=1          |
| pass1 [ret,ret]        | rc=2 cap >1.45G             | **816,333,786 sols=1**      |
| pass1 [push;ret]       | rc=2 cap >1.45G             | **848,245,370 sols=1**      |
| pass1 ret3             | —                           | 1,225,426,884 sols=1        |
| pass1 ret8             | —                           | 3,280,724,518 sols=1        |
| assemble [push;ret]    | rc=2 cap (1516s)            | **2,701,513,499 sols=1**    |
| assemble [lab;call;ret]| —                           | 2,715,233,833 sols=1        |

Byte-verification (independent fasmg oracle):

- `assemble [push;ret]` → `55 c3` — MATCH.
- `assemble [lab;call;ret]` → `e8 fb ff ff ff c3` — MATCH
  (label→rel32 resolution through `relfix`/`symtab` included).

Marginal op cost: ret1 505M → ret2 +311M → ret3 +409M → ret8
~+411M/op. The quadratic is gone; marginal is ~constant ≈410M/op.
Trie overhead costs ~+20% on small substs (`enc2_len ret`
483M vs 397M assoc — per-bit descent beats only beyond ~100
bindings).

## The wall that replaced the quadratic — persist zone, not subst

Multi-op runs OOM'd (`exit4`) at ~230 s **independent of
`ir_arena_bytes` (2/8/16 GiB identical)** — the structural reason:
`Realization.persist_bytes` is a fixed 256 MiB zone below
`irstart` holding input-tier reducts (enc'd env + M + goal
normalization — "pay once" caching across a root stream). Corpus
eval normalizes enough input-tier structure over multi-op runs to
fill it; a sweep that frees nothing concedes `exit4`.

Fix: `persist_bytes` is a declared Realization axis — bumped to
1 GiB (i32-immediate ceiling ≈2 GiB) for the probe rows above.
This is a sizing axis, not new substrate: `gc=sweep` unchanged.

`pass1 ret8` end-state: free=4.86 GiB of 8 GiB arena; the subst
trie itself is ~1.3K bindings × ~10 cells — the bulk live set is
reduction machinery, not subst.

## What this does NOT claim

- Full-src `assemble` (769 items, 2811 B .text) is in flight at
  the time of writing: extrapolated ~315G steps for `pass1` at
  ~410M/op, ~3× for `assemble` → hours, not a wall. MEGAPLAN §7
  stays open until that row exists.
- interpreter² (`eval` on enc'd defs) still cannot instantiate
  enc'd `'nvar` — a pre-existing true-L2 limit (frag 0016
  family). The old selftest's `len(l2)==1` was counting
  template-exploration solutions (unbound query var); it now
  asserts a real corpus-eval `unify` with a decode-verified
  trie binding.
- `beq` is only total on bit-list inputs; if an unbound/non-list
  id ever reached it the clause yields ∅. Ids are ground bit
  lists by construction.

## Files

- `phi2/eval.phi` + regenerated `eval.plex` (31 rels).
- `phi2/seed.py` — machine mirror + honest L2/corpus footholds.
- `phi2/realize.phi`, `phi2/runtime.phi` (+`.plex`) — `n` callers.
- `host/gates/np_gates_rel.py` — trie sol decoder, bit-list ids.
- `_scratch/_telemetry.py`, `_probe_assemble.py`,
  `_fullsrc_native.py` — probe rows + fasmg checks.
- `telemetry/phi2_repr_cost/` — rows appended, README updated.
