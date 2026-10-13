---
type: frag
id: 0028
provenance: devin-cli
ts: 2026-10-13
tags: [phi2, eval, pass1, assemble, full-src, persist, redirect,
       gc-sweep, oom, megaplan-7, freeze, decision-066]
---

# 0028 — full-src verdict: pass1 OOMs on the persist zone at 16 GiB; the wall is superlinear frontier growth, not sizing; MEGAPLAN §7 misses

## What was measured

After frag 0027 cleared the substitution quadratic (~410M/op
marginal, linear through 8 ops, fasmg-verified), the full-src
criterion was attempted on the 769-item program (2811 B oracle
`.text`, 81 labels, env=33 rels for `pass1`, 54 for `assemble`) —
`machine_term(8192)` + ir exe, `reclaim="redirect"`, `gc="sweep"`,
`fuel=None`, take-1.

| run | persist | arena | result |
|---|---|---|---|
| `assemble` full-src | 2.147 GiB (imm32 max) | 32 GiB | rc=4 @ 1923.1 s |
| `pass1` full-src | 2.147 GiB | 32 GiB | rc=4 @ 1841.3 s |
| `pass1` full-src | 1 GiB | 32 GiB | rc=4 @ 277.0 s |
| `pass1` full-src | 16 GiB | 64 GiB | rc=4 @ 24890.9 s |

All four `exit4` with empty stderr; the dynamic arena stayed
near-empty (working set flat at persist size — the zone commits
eagerly at depack). The OOM is the persist allocator's
collect-then-concede path, not `ir_arena_bytes`.

## The mechanism

Two of the numbers are a discriminator pair: halving the persist
cap does not halve the survival time — it cuts it by ~6.6×, and
raising it 7.5× buys ~13.5× more time. OOM-time grows *faster* than
the cap, i.e. **the live input-tier frontier grows superlinearly in
steps**. The persist zone holds reducts of input-reachable cells so
input cells may point at them; over a single long root the
reachable-from-input frontier accumulates choicepoint/stream
structure roughly quadratically in op count. It is the *live* bound
for a redirect+IR eval, not the arena.

Extrapolation: `pass1` completion needs persist ≫16 GiB (the fill
curve has no inflection in evidence — each sizing step buys
~√progress). `assemble` is ~3.2× `pass1`'s steps at probe scale —
strictly harder, not run at full-src.

## What changed on the way

The 2.147 GiB cap was itself an accident: `pend = pcur +
persist_bytes` used `add_r64_imm` (signed imm32). Widened to
`mov_r64_imm` + `add_r64_r64` (commit `4720a08`, goldens refreshed
byte-coherently, nanopass 35/35). That fix mattered — it proved the
wall is the *growth rate*, not the ceiling: at 16 GiB the run
survived 13.5× longer and still conceded.

## The §7 verdict

**MEGAPLAN §7 misses.** Native `assemble` for the full-src program
under `gc=sweep` does not complete: the declared-realization space
(reclaim=redirect is the only gc=sweep leg; persist_bytes and
ir_arena_bytes are the only memory axes) has no point that carries
769 sequential ops in one take-1 stream. The next move is a
retention-model change — input-tier routing, stream/root splitting,
or a reclaim leg that does not pin input-reachable reducts — and
each of those is new substrate, which the freeze protocol forbids.

Frozen honestly:

- fixtures: `telemetry/phi2_repr_cost/rows.jsonl` rows tagged
  `trie-persist-wall` (this table, machine-readable)
- the trie strategy itself is proven at probe scale (frag 0027):
  the quadratic is cleared, emission is byte-verified — the wall is
  downstream of the substitution decision
- still open, unrelated: frag 0016 interpreter² `'nvar` limit

## What this does NOT claim

- No claim that pass1's search is exponential — step counts are
  consistent with ~linear ops × growing frontier; the OOM is
  *space*, and the space curve is what kills it.
- No claim the criterion is unreachable in principle — only under
  the current realization set. A reclaim leg without the
  persist-pin, or multi-root scheduling, is a design decision above
  this frag.
