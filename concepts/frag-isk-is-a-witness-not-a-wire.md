---
type: belief
id: frag-isk-is-a-witness-not-a-wire
provenance: isar-proofs — KernelCategory carrier analysis + Lars/CC trust-chain discussion, 2025-11
ts: 2025-11-18
tags: [isk, kernel, carrier, observation-regime, dialect, architecture]
---

**ISK is a proof-of-completeness witness, not a wire format.**
The ISK terms were never a privileged interchange choice — they
are a witness for proof mechanics, a minimal basis that makes
completeness theorems short to state. Baking `ISKSubtype` into
the `Kernel` interface — every view implementing
`view_of : ISKSubtype → Carrier` and `decode : Carrier →
ISKSubtype` — let the proof shorthand leak into the wire role,
turning it into the mandatory interchange for the whole stack.
The leak costs three ways: bracket abstraction destroys local
structure and inflates terms (worst case for a projectional
editor, where a small view edit becomes a large non-local
rewrite); `ISKSubtype` is a tree where the runtime wants a
shared composition graph, so `decode` drops sharing and layout
unless the view side-carries them (the `DegenerateKernel` `Bool`
tag gap is that leak made visible); and native domains
(registers, numbers, tensors) get double-encoded into combinator
trees just to cross the quotient and reconstructed on exit.

Universality and representation are different jobs and the
interface should not conflate them. `no_preferred_syntax` is
only *actually* symmetric once the anchor is gone — the README
scope note admits it: views are equidistant modulo the fixed
ISK anchor, not free of it.

Stage (a) landed: `Kernel` is parameterized by `(P, R :
ObservationRegime P)` with all coherence fields over `R.sim`;
`substrateKernel R` is the per-regime terminal object and
`ISAR_Kernel` is the ISK specialization — a peer kernel, no
longer the terminal object. `QuotientMap` generalizes to
arbitrary source/target regimes (`QuotientMapO` is the ISK
abbrev). `no_indiscrete_Kernel` generalizes to any
non-degenerate regime (`operEqRegime_nondegenerate` carries the
norm/konst witness). ISK remains for bootstrapping,
minimal-basis proofs, and canonical Gödel indexing — one
dialect among equals.

Decidability settled mechanically (probe: two regimes over a
shared-graph presentation — class-id `Obs` with decidable
`ObsEq`, and the presentation itself with a Prop relation —
both instantiate `substrateKernel`/`canonical_hom`/
`QuotientMap` with zero `Decidable` anywhere): the interface
never decides; decidability is a property of the chosen `Obs`
representation. `operEqRegime` already exploits this —
`InvariantLayer` IS the class-id. A third option beyond
Prop-vs-decidable: two regimes over one presentation
(semantic `ObsEq` + computational class-id `Obs`), related by
`QuotientMap`.

Open: the substrate pin `Dialect.encode : Object → ISKSubtype`
still routes composition through ISK — migrated through the
generalized `QuotientMap` layer when a dialect gets its own
regime; and whether the regime-parameterized `Kernel` is one
structure or two (a `UniversalKernel` witnessing completeness
vs a `CarrierKernel` doing representation work).

`observe` settled mechanically (probe `_scratch/inet_observe_probe.lean`
— hash vs equational-closure vs joinability discriminated on
annihilation, non-confluence, divergence): `sim` is joinability
(common reduct). Hash misses rewrite equivalence
(`F(G x)` vs `x`); equational theory over-identifies
(`B ~ C` provable across a non-confluent fork, no common
reduct); joinability matches execution truth and coincides
with equational theory exactly on the confluent fragment —
which is why Lafont's interaction rules, confluent by
construction, are the optimal-sharing substrate. Plain
nf-observe collapses all divergent terms to one ⊥ class
(probe: `nfs D = nfs (W D) = []`), so a total `observe`
needs a normalizability side-condition on the presentation —
the `Guard`/dead-live split pattern from `bendtt.lean`
(vendored `W:\src\bend`; bend2 has no HVM) is the model for
carrying it first-class rather than as a caveat.

Stage (b) landed (`src/ISAR/InteractionNet.lean`): `Net` — agents
plus wires as unordered end-pairs, sharing as datum not tree shape —
is the first non-ISK kernel carrier, instantiated against
`Kernel P R` with zero changes to the generic machinery.
`RuleTable` declares Lafont's annihilate/commute/erase as data;
`netStep` refuses on contract violation (mismatched arity, aux-wire
joining the dying pair) rather than fabricate. `Obv` makes the
⊥/refusal split structural. The textbook γδ grid, annihilation
splice, erasure, refusal, and fuel-0 divergence all evaluate
in-file; `inetKernel`/`inetCanonical`/`inetSelfMap` exercise
substrate kernel, canonical hom, and quotient map with no ISK
anywhere. Optimal graph sharing is the performance unlock this
parameterization was staged for.
