---
type: decision
id: 0011
provenance: megaplan (~/.devin/plans/plan-83fea387acdafe69.md);
  audit-plex-assets.md; patent/phi-lang/phi_boot.py + phi-boot-self.py;
  src/ISAR/ISARMatrices.lean; plex/core/isar.py; host/plex_bundle.py,
  host/rel_eval.py (oracle)
ts: 2026-10-13
tags: [phi2, seed, kernel-head, slices, sole-python, corpus-std,
  congruence-gate, re-derivation]
---
# phi2/seed.py — the sole Python; kernel in the .plex head; corpus as
# std/*.plex; congruent with the oracle on day one

The re-derivation began: `phi2/` is the flat bend2-shaped tree where
seed.py is the *only* Python file and everything else is `.plex`
data.  host/ is donor/oracle from here on — imported for the gate,
headed for attic/ once the emitted chain stands.

## What's in the seed (and what isn't)

seed.py = codec + kernel decode + stepper + ports.  Nothing else.

- **`.plex` v3 codec** re-derived (index arithmetic only; same wire
  contract as plex_bundle.py — bundles are readable by both
  machines).
- **KERNEL section (kind 12)** — the 64-byte head the old V2 format
  left zeroed is now the point: 4 rows x 16 u8 cells carry the I,R,A,S
  matrices (Lean `isar.v1` set — plex/core's lineage; v2 differs only
  in R and is derivable through gauge P, which Lean proves conjugates
  them).  OPS section (kind 13) carries the declared 8-slice ordering
  ATOM,PAIR,FRESH,UNIFY,MATCH,APPLY,CHOICE,RUN — nibble tags are
  *indices into that table*, matching the patent K table.  Reading
  kernel.plex re-derives the ontological value-tags from the matrices
  (I diag -> 5 = TAG_SYM, A diag -> 0 = TAG_INT, S row0 -> 3 =
  TAG_DAT — plex/core's derivation, recomputed not copied) and checks
  K = I*R*A*S is nilpotent at load — the Lean rfl theorems executed
  as gate checks.
- **The stepper** is the full rel_eval contract: union-find subst,
  lazy goal streams with interleave, clause extensions, fresh
  renaming per instantiation, the RUN quotient (n=1 committed read /
  n=0 stream), MATCH/APPLY/env_lookup/call meta-level, atom_lazy
  forcing, the shape/lowering contract and forged-cycle refusal, fuel
  as observable empty stream.
- **Not in it**: no assembler, no packer, no parser, no schema — those
  arrive as maps/ and std/ data or stay donor until their .plex
  realization lands.

## The corpus is canonical .plex from day one

`host/corpus/stdlib.phi` was captured once through the donor
phi_rel.graph_bundle into six `std/` bundles under `what_who_how`
names: unify_terms_core (7 rels), arith_nibble_carry (5),
arith_peano_succ (4), lists_append_mapfold (3), meta_call_run (5),
rewrite_contract_compose (3) — all 27 rels, `merge_graphs` refuses
name collisions rather than silently overriding.

## The gate is congruence, not self-report

`python phi2/seed.py gate` runs the same 12 checks through seed's
stepper AND host/rel_eval.py (the oracle): forward calls (add, fib,
append, head, call, map, fold, nibble_half_add, nibble_add, norm —
identical answers), the backward append stream (3 splits, identical
order — observational equivalence), and identical refusal on compose
(the op-term out-pattern stays declared-not-realized in both
machines).  Post-attic the gate degrades to the corpus selftest.

## Stated trade-offs

- The stepper is a faithful re-derivation of rel_eval semantics, not
  a new machine — congruence is the gate's whole job, and it will be
  retired by eval.plex, not amended.
- Term graphs still travel as JSON inside BYTES sections (the
  graph_bundle contract).  The basis-term encoding is a later map;
  pretending sections are already terms would be a lie.
- kernel.plex is written by seed itself (`seed.py kernel out.plex`) —
  the artifact is data, its writer is stage-0 residue.
- The CLI is thin (`run`, `kernel`, `gate`, bare = selftest); dialect
  projection stays with host/dialect.py until its .plex realization.

## Evidence

- `python phi2/seed.py` — selftest: kernel slices (I=5 A=0 S.row0=3,
  K^2=0), rel-bundle round-trip, append fwd+bwd, head, refusals,
  corpus rels=27: pass
- `python phi2/seed.py gate` — 12 congruence checks vs oracle:
  identical streams, identical refusals: pass
- `python phi2/seed.py run phi2/std/*.plex "add<2,3>"` -> ATOM(8,5)
