---
type: frag
id: 0057
provenance: devin-cli
ts: 2026-10-30
tags: [koru, host2, kwir, koruc, dialect, race, disjointness, ordering]
---

# 0057 — koruc-native wir lands: same-wire race won, order measured

Frag 0056 left two open rungs, both now closed.

## The koruc-native rewrite (`_scratch/kdrv/`)

`transform.py` rewrites `_scratch/wir.k` (korufe surface) → `wirn.k`
(koruc surface), mechanically and structurally: 169 tors, zero
unhandled sites. The dialect mapping discovered by the koruc backend:

- `-> T` returns become `| sval T | bad` unions — `bad` is a phantom
  outcome propagated through every nested `|>` stage (`| bad => bad`),
  which is also what makes each stage's failure a produce instead of a
  dispatch miss.
- Ordered `| _ b when g` arms become `| sval scrut |> cond(scrut)` +
  ordered `| c b when g` arms — koruc's emitter does not lower `when`
  on union-tag arms (payload capture + continuation silently dropped;
  deep-check does not catch it).
- `=>` payloads are atoms only; `->` inside union arms evaluates and
  discards (also unchecked). Compound produces pipe through
  `wid-i`/`wid-s` identity tors.
- `|>`-pipeline `: bind` chains nest as `| sval b |> next` dispatch
  under the previous arm; union results cannot use `: bind` (KORU022).
- `if` is a native expression but not laziness-free in args (comptime
  zig lowering) — ifs in arg/produce positions become `|> if(c)` nested
  dispatch, duplicating the tail per branch (preserves short-circuit).
- `++`, `@intToString`, `/` have no koruc runtime forms (`++` is
  zig-comptime) — hoisted to `app/kit` (`kcat`/`itos` zig procs);
  `A / B` → `@divTrunc(A,B)`; `.len` → `@as(i64, @intCast(x.len))`;
  slice indices → `@as(usize, @intCast(i))`.

Driver: `drv.k` + `drv.kz` — stdin cell sexpr → six typed slices →
`app/wir:main` → raw stdout write (`wout` proc; `std/io:print.ln`
formats through a 64KB stack buffer — 122KB output silently truncated,
a real surface limit).

## Same-wire race — three lanes, byte-compared

| wire | emitProgC `kwir_wiw` | koruc native `a.out` |
|------|----------------------|----------------------|
| 906  | 2.0s / 1053MB        | **0.7s / 587MB**     |
| 905  | 4.2s / 2247MB        | **0.8s / 1769MB**    |

Both outputs **byte-identical** (122173B, 228554B) to the korufe
authority. The koruc-compiled variant is ~3–5× faster — compiled zig
handlers vs the emitProgC boxed-Val evaluator shape; the C lane's
remaining multiplier is repr-level, as frag 0055 named.

Honest edges: `a.out` needs a large stack reserve (koru emits
non-TCO handler recursion — `wth`-style self-calls nest ~6.6K frames
on 39K rows; patched to 512MB via `pe_stack.py`). ReleaseSafe for the
race because Debug's leak check trips on concat garbage — the C lane
leaks identically, it just has no auditor; proper `allocated!`
plumbing would need per-site ownership tracking the transform does
not spell. `-O` asymmetry (ReleaseSafe vs `-O0` clang) noted — the
gap is structural, not tuning.

## Disjointness: order is the only remaining dispatch signal — measured

`disjoint.py` models each `| _ bind when g` guard as conjoined
per-variable interval sets (ℤ + a string-literal band); two arms are
provably disjoint iff ANY variable's constraints don't intersect.
Unmodeled parts (env-var compares, `if`, `!`) overapproximate toward
overlap — conservative: may flag ordered, never falsely disjoint.

Result over 158 arm-sets (369 arms, 169 tors):

| class      | count | meaning                                    |
|------------|-------|--------------------------------------------|
| trivial    | 62    | single arm, no choice                      |
| catchall   | 76    | disjoint guards + fallback-last            |
| ordered    | 20    | 2 proven overlaps + 18 undecidable         |
| unordered  | 0     | —                                          |

- Every nontrivial dispatch spells a fallback (korufe miss = empty
  produce), so **pure-unordered sets don't exist** — but in all 76
  catchall sets order only constrains the *fallback's position*;
  the guarded arms are interchangeable.
- The 2 proven overlaps (`wfel`, `wsti3`): `(r==1)&&(ifd==0)` before
  `r==1` — narrower-before-wider priority dispatch where order IS
  the semantics.
- The 18 undecidable are env-var guards (`i >= nr*6` loop bounds) that
  must precede payload dispatch — realistically all ordered too.

So the earlier conjecture holds with a number on it: order is
load-bearing at ~13% of dispatch sites (the two overlap-priority sets
plus the env-boundary checks); everywhere else dispatch is value-
disjoint modulo fallback position — the shape an unordered/inet
dispatch model would actually need.

Artifacts: `_scratch/kdrv/{transform.py,disjoint.py,drv.k,drv.kz,
kit.kz,wirn.k,pe_stack.py,disjoint_report.txt}`.
