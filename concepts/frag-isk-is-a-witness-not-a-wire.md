---
type: belief
id: frag-isk-is-a-witness-not-a-wire
provenance: isar-proofs — KernelCategory carrier analysis + Lars/CC trust-chain discussion, 2025-11
ts: 2025-11-18
tags: [isk, kernel, carrier, observation-regime, dialect, architecture]
---

**ISK is a proof-of-completeness witness, not a wire format.**
Baking `ISKSubtype` into the `Kernel` interface — every view
implementing `view_of : ISKSubtype → Carrier` and
`decode : Carrier → ISKSubtype` — turns a minimal combinatory
basis into the mandatory interchange for the whole stack. The
privilege costs three ways: bracket abstraction destroys local
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

The direction held: parameterize `Kernel` by an
`ObservationRegime` (∼O) over an arbitrary carrier (typed
composition graph / e-graph), compose dialects through
`QuotientMap`s preserving ∼O directly, and keep domain-native
ops opaque until a specific lowering expands them. ISK remains
for bootstrapping, minimal-basis proofs, and canonical Gödel
indexing — one dialect among equals.

Open: whether the regime-parameterized `Kernel` is one structure
or two (a `UniversalKernel` witnessing completeness vs a
`CarrierKernel` doing representation work); and how much of the
existing view corpus survives the move intact vs needs its
`decode` rewritten to land in the new carrier.
