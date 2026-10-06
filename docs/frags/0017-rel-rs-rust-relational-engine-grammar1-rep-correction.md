---
type: frag
id: 0017
provenance: devin-cli
ts: 2026-02-19
tags: [rel.rs, plexus, realization, corpus, grammar-1, rep-correction, eval-menv, congruence]
---

# 0017 — rel.rs: Rust relational engine realization; grammar-1 rep correction; corpus yields bytes

## What landed

`crates/plex-core/src/rel.rs` (plexus) — a pull-stream port of the
phi.rel/1 corpus stepper (`phi2/seed.py` `run_value`), plus
`src/bin/plex_rel.rs` (probe driver).  The .plex corpus stays the
spec: `host/`-side `load_corpus` output is dumped to JSON
(`_rel_export.py` → `_rel_probes.json`), `plex_rel` re-interns the
same terms and must reproduce `run_value`'s solutions term-for-term.

- Arena: interned hash-consed nodes (`a/p/v/s/lz/c/d/rd/pat/bc/gt`)
  + per-node ground bit — same as `_ND`/`_GR`.
- Subst: persistent assoc list (cons-cell bind, O(1) clone,
  shadowing identical to `{**s,k:v}`).
- `ren`: Rc<RefCell<map>> shared per clause — Python threads one
  dict across a clause's goals; per-goal clones would rename wrongly.
- Streams: generators become `next(&mut Eng)` pull objects —
  `Conj/One/RelBody/RelCall/RunGoal/Interleave/Branch/Builtin`.
- Tabling ported faithfully: ground-args call with open out-var →
  table entry; active producer → bypass (same-goal recursion
  diverges under fuel, as before); sealed → replay cached outs.
  In the reference the "resume suspended producer" branch is dead
  code — non-active always means sealed; the port drops it.

## Congruence (8/8 term-for-term vs run_value)

| probe | python witness | rel.rs | native combinator path |
| --- | --- | --- | --- |
| append [5;6] [] | 1 sol | 1 sol, 1.4ms | — |
| eval<menv> unify(a8,a8) | 1 sol | 1 sol, 2.7ms | 33M steps / 103s, 1 sol |
| eval<menv> env_find miss | 0 sol | 0 sol, 1.6ms | 16M steps / 17s, [] |
| eval<menv> call cons a8 b8 | 1 sol | 1 sol, 5ms | — |
| apply<map,src> assemble | 1 sol, 3.15s | 1 sol, 3.22s | 1.07B steps / 43min, [] |
| eval<menv> 'call assemble src | 1 sol, 3.52s | 1 sol, 3.19s | — |
| realize spec-maps[] | 1 sol | 1 sol, 0.9ms | — |
| rfold maps=[asm] | 1 sol, 4.31s | 1 sol, 3.45s | 1.2B steps / 52min, [] |

## Rep correction (important)

Earlier frags recorded "corpus `rfold maps=[asm]` → 0 sols" as
agreement with the native empty stream.  That witness was built on
grammar-2 args (`eP`/`_esym`-wrapped enc nodes — the machine-term
encoding).  Corpus `eval`/`apply`/`rfold` destructure **grammar-1**:
raw `pair`/`atom(0,0)` spines, `'tag`-node = `pair(sym_leaf,args)`,
`s0 = atom(0,0)`, `mapT = pair('sym'map, pair(menv, entry))` with
`entry` a raw sym leaf — exactly `enc_env`/`enc_goal` output.

With grammar-1 args, corpus `rfold maps=[asm]` and `apply<map,src>`
yield **1 sol — the byte derivation**.  The native `[]` results were
therefore encoding-mismatch or mfuel-bottoming, not honest empty
streams.  The corpus has always said the assemble path produces
bytes.

## Bugs the port flushed out

- `RCInit` discarded its inner stream after the first pull → second
  `next()` re-initialized on an empty name (`unbound rel ""`).
  Fix: init wrapper keeps the built stream and delegates.
- Immediate goals (unify/cmp/emit) returned their result without
  marking exhaustion → re-poll re-yielded the same subst
  (append gave 2 identical sols).  Fix: wrap result in `Once`.

## Round 2 — persistent subst + full std-corpus battery

Counters (`PLEX_REL_STATS=1`) showed the real wall was subst bind:
98,734 binds × avg subst size **7,420 entries** = 732M entry-copies —
Python's `{**s,k:v}` dict-copy has the identical O(n) bind cost,
which is exactly why the port sat at parity.  Subst is now
`im::HashMap` (persistent; O(log n) bind / O(1) clone, same
shadowing).  Results:

| probe | before | after | python |
| --- | --- | --- | --- |
| apply<map,src> | 3.22s | **297ms** | 3.15s |
| eval<menv> 'call assemble | 3.19s | **272ms** | 3.52s |
| rfold maps=[asm] | 3.45s | **324ms** | 4.31s |
| cogen spec-full | — | **~300ms** | 4.88s |

~11-13x over the witness on the search-bound probes.

### Full battery — 41/41 term-for-term or error-class identical

`_rel_export.py` now exports the whole std corpus (62 rels merged)
plus one probe per std rel: nibble carry ops, peano succ/pred/add,
fib (pairwise tabling), map/fold/member/assoc (self-shape
recursion), meta rels (norm/find/stream/any through `run`/`choice`
goalterms, `call` through env_lookup+MATCH+APPLY), unify_terms_core
constructors, and refusal-parity rows (`contract`/`compose`/
`fresh_var` — `{"op":..}` outs are unliftable in *both* engines;
`call 'norel` — env_lookup unbound; `assoc_id` — `cmp !=` requires
ground atoms).  All green.

The **real cogen workload** is now on the wire:
`cogen spec-full` = `cogen<spec(src1, [assemble_x86], qmaps,
regime, ctx)>` → spec destructure → `realize` → `rfold` →
`eval<menv> 'call assemble` — 1 sol, ~300ms (native combinator:
~45min+ via interpreter²; honest byte-tree derivation).

### Host artifact noted

Python witness crashes (native stack exhaustion) pulling a *second*
`sol` from `fold` — the `_conj`/`_rel_body` generator tower grows
unboundedly on the residual search.  Rust streams are heap objects
and don't share the limit.  Battery uses n=1 there; the divergence
is environmental, not semantic.

### Emit seam wired (decode -> pack -> containers)

`plex_rel` gains `PLEX_REL_DUMP=<file>` (thaw'd sols JSON);
`_cogen_emit.py` consumes it: byte-tree decode -> `.text` ->
`target_pe64.pack` / `target_elf64.pack` / `pack_obj` (the
fasmg-mined container family).

- `.text` `55 c3` == `isa_x86_64.encode(push rbp; ret)` — second
  witness byte-identical (corpus emits a `00` pad tail).
- `cogen_mini.exe` (2048B) / `.elf` (4096B) / `.o` (664B) written —
  all headers valid, `.text` payload intact.
- The PE **loads and executes**: rc=0xC0000005 is the toy program's
  own `ret`-at-entry fault (no return address — entry isn't
  called), not a loader rejection.
- Constraint surfaced: pe64's declared layout needs ≥1 data slot
  (empty .data puts .text on the same RVA → 193).
- Next seam for a *clean-exit* exe: an ExitProcess tail needs
  `call [rip+iat]` forms — a corpus encode-map coverage question.

## Trade-offs / honest edges

- Remaining per-activation cost is `lift` over corpus dicts +
  `One`'s goal-dict clone — the next lever is compiling clauses to
  template terms once at load (activation = fresh-var remap, ground
  subtrees shared O(1)).  Not done; current speed is adequate.
- Engine-per-probe (`load_corpus` per run) — fine for the probe
  harness; a persistent engine is trivial later.
- No occurs check, same as the reference — inherited faithfully.
- `debug` counters (`PLEX_REL_STATS`, `BINDS`) remain env-gated.

## Where this sits

Same `.plex` corpus, same terms, same sols — a fast host realization
of declared semantics, not a second semantics.  The dev loop is now
seconds; the native graph/combinator exe keeps exactly one job:
the bootstrap witness (seed → H0 on-substrate, once).
