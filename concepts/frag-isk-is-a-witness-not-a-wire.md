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
vs a `CarrierKernel` doing representation work). Next carrier
candidate: typed composition graph / interaction-net shape —
optimal graph sharing is the performance unlock this
parameterization was staged for. Source is Lafont's
interaction nets; `bendtt.lean` (vendored `W:\src\bend`) is
the model for a formalized affine kernel in Lean — bend2 uses
no HVM.
