# 059 — rel.rs fast realization in plexus; grammar-1 rep correction

Status: implemented (plexus `crates/plex-core/src/rel.rs` + `bin/plex_rel.rs`; isar-proofs `_rel_export.py` → `_rel_probes.json`; frag 0017)

## Decision

Port the phi.rel/1 corpus stepper (`phi2/seed.py` `run_value`) to
Rust as `rel.rs` inside plexus plex-core — a host *realization* of
the declared .plex semantics, not a new semantics.  The corpus
remains the spec; the JSON dump of `load_corpus`'s parsed graph is
the wire.  Congruence = term-for-term identical solutions vs
`run_value`, verified on the probe suite (8/8).

The native graph/combinator exe is not the dev runtime — it is the
bootstrap witness (seed → H0 on-substrate).  Dev iteration, corpus
eval, and map/encoding work run on rel.rs (and the Python witness).

## Rep correction

Grammar-1 (corpus eval's domain): raw `pair`/`atom(0,0)` spines,
`'tag`-node = `pair(sym_leaf, args)`, `s0 = atom(0,0)`, mapT =
`pair('sym'map, pair(menv, raw-sym-entry))` — what
`enc_env`/`enc_goal` emit.

Grammar-2 (`_cogen_bis2` L1/`eP` wrapping) is the *machine-term*
encoding.  Probing corpus rels with grammar-2 args silently
mismatches: assoc/env_find/unify guards see tagged nodes where raw
pairs are expected → empty streams that look like honest "no sol".

Consequence: the earlier "corpus rfold → 0 sols" verdict was a rep
bug.  Corpus `rfold maps=[asm]` / `apply<map,src>` yield **1 sol**
(the byte derivation) in ~4s.  The native `[]` after 1.2B steps was
encoding-mismatch or fuel-bottoming — never an honest empty.

## Measured (rel.rs vs run_value vs native)

- `eval<menv> unify(a8,a8)`: 2.7ms vs 10ms vs 33M steps/103s
- `apply<map,src>`: 3.2s vs 3.15s vs 1.07B steps/43min → []

## Round 2 (2026-02-19): persistent subst + full battery

- **Perf finding**: subst bind was the wall — 98,734 binds × avg
  subst 7,420 entries = 732M entry-copies per `apply` probe.
  `im::HashMap` (persistent) → O(log n) bind: 3.22s → **297ms**
  (~11x, ~13x over Python). Python pays the same O(n) dict-copy —
  that was the parity cause.
- **Full std battery**: 41/41 probes term-for-term (30 std rels +
  meta + refusals + cogen path). `cogen spec-full` — the actual
  eval<menv>-on-cogen workload — 1 sol in ~300ms.
- Python n=2 `fold` overflows the generator stack (host artifact,
  not semantic divergence).
- Architecture: rel.rs is a *realization host* (interpreter of the
  parsed .plex graph), not a seed — the chain stays open:
  `.plex` → {Python witness | rel.rs | native graph} interpreted,
  or → compiled through emit chain (seed→H0→H1→H2). Native exe =
  bootstrap witness only.

## Port notes (for future maintainers)

- Streams are pull-based `next(&mut Eng)` objects mirroring the
  Python generators; `ren` is `Rc<RefCell<map>>` shared per clause.
- Tabling: active→bypass, sealed→replay.  The reference's
  resume-suspended-producer branch is dead code; dropped.
- Port bugs found: init-wrapper dropped its inner stream; immediate
  goals didn't mark exhaustion (double-yield).

## Rejected alternatives

- `plex-core/src/quotient.rs` as the runtime — it's a boxed-AST
  tree-substitution evaluator of the I/K/W/B/C basis; not the
  relational .plex engine, and slower than graph.lo for this work.
- Continuing to optimize `graph.lo` as the dev loop — wrong
  realization axis for relational search (interpreter^2 constant:
  ~33M port-rewrites per trivial meta-circular call).
