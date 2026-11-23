# 068 — ISK privilege is the overhead axis; carrier generalizes to ObservationRegime

## Context

`KernelCategory.lean` bakes `ISKSubtype` into the `Kernel`
interface itself: every view must implement
`view_of : ISKSubtype → Carrier` and `decode : Carrier → ISKSubtype`.
That silently makes a minimal combinatory basis the mandatory
interchange format for the whole stack — ISK is privileged as
*the* shorthand, not merely a witness that a tiny basis can
simulate every closed dialect.

The tax lands three ways (analyzed against the current tree):

- **Combinator blowup.** Bracket abstraction
  (`LambdaFragment.abstract0`) destroys local structure and
  inflates terms even when `B`, `C`, `W` are present. A small
  high-level edit becomes a large non-local rewrite once
  flattened to `ISKSubtype` — worst case for a projectional
  editor.
- **Tree vs. graph mismatch.** `ISKSubtype` is an inductive
  tree; `host/graph_runtime.py` runs shared composition graphs
  (node identity + edges). `decode` landing in a tree discards
  sharing and layout unless the view side-carries metadata —
  the gap `DegenerateKernel` exposes when `view_eq` ignores
  the `Bool` tag (`KernelCategory.lean:166-186`).
- **Double-encoding native domains.** `QuantityKernel`,
  `FASMView`, `BytecodeView` encode registers/numbers/tensors
  into combinator trees (or Gödel numbers) just to cross the
  quotient, then reconstruct on the way out
  (`mine_adopt.try_adopt`).

The README scope note already admits this:
`no_preferred_syntax` (ViewIndependence.lean) holds *inside*
the `Kernel` interface "whose `decode` still lands in
`ISKSubtype` — views are equidistant modulo that fixed anchor,
not free of it." The theorem is only truly symmetric once ISK
is demoted to a peer dialect.

## Decision (landed stage a)

Separate **universality** from **representation**:

- ISK stays as proof-of-completeness witness — bootstrapping,
  minimal-basis proofs, canonical Gödel indexing.
- The `Kernel` interface parameterizes by an
  `ObservationRegime` (∼O) over an arbitrary carrier (typed
  composition graph / e-graph), instead of hardcoding
  `ISKSubtype` (`ObservationRegime.lean` already supplies the
  structure).
- Dialects compose through `QuotientMap`s preserving ∼O
  directly — no detour through combinator trees.
- Domain-native ops (SIMD `join`/`norm`, FASM instrs, tensor
  ops) stay opaque atoms until a specific lowering expands
  them.

### Stage (a) landed — interface generalization

`Kernel` is now `Kernel (P : Type) (R : ObservationRegime P)`;
every `OperEq` field hypothesis/conclusion became `R.sim`.
`substrateKernel R` is the per-regime terminal object;
`ISAR_Kernel := Kernel ISKSubtype operEqRegime` is the ISAR
specialization and `substrateKernel operEqRegime` is its
terminal target — `ISAR_Kernel` itself is no longer the
terminal object, exactly the demotion semantics.
`QuotientMapO` became `QuotientMap P R Q S` over arbitrary
source/target regimes, with `QuotientMapO` kept as the ISK
abbrev. `no_indiscrete_Kernel` takes a non-degeneracy witness
`∃ t u, ¬ R.sim t u`; `operEqRegime_nondegenerate` supplies
the ISAR instance from the norm/konst atoms. `DialectKernel`'s
vestigial `KernelCategory` import removed (cycle:
`KernelCategory → ObservationRegime → … → DialectKernel →
KernelCategory`). All generic proofs ported with only
equivalence-law reasoning — nothing needed ISK-specific
structure, confirming the demotion was mechanical. Still
ISK-pinned, deliberately: `Dialect.encode : Object →
ISKSubtype` is the substrate pin, migrated later through the
generalized `QuotientMap` layer, and each concrete dialect's
`decode` still lands in ISK until its own regime exists.

## Where this sits historically

The trust-chain ordering settled in the host2 discussion
(commit `1e450af`, frag 0065): zig koru as behavioral authority
→ executable Lean spec matched line-by-line → flip so the spec
is authoritative and zig is production → spec/propositions/
proofs split (`Koru/Spec`, `Koru/Prop`, `Koru/Proof`) → C99
1-1 reference cross-compiled by gcc + ccomp → trickle to
generated artifacts.

- **D. T. Ross** — spec-as-executable-model, not spec-as-paper;
  a program is a machine whose correctness is its invariants.
- **Futamura** — `kEmitProg` interpreted by `krun` producing
  `emitProgC`'s bytes *is* the first projection, checked not
  assumed (`kp.emit`/`kp.*.h1`). Koru-written compiler through
  itself is second-Futamura.
- **Turchin** — the step-price work (frags 0064/0065) is what
  makes supercompilation of a koru-written compiler viable:
  spelled char loops are the worst input shape; named builtins
  bound the primitive set.
- **CompCert** — the real lesson isn't gcc/ccomp double-check;
  it's *the specification is the artifact, implementations are
  witnesses*. Same sentence for ISK: witness ≠ wire format.

## Still missing (named walls)

- **name→index dict** — positional flag repr needs it; `set`
  alone is insufficient (frag 0065 corrects the earlier
  over-claim). Next rung after the `push`/`set` pair-return
  refactor.
- **koruc AST→KProg bridge** — `koru-libs`/`koru-examples` are
  real koru, not the wire dialect; they can't feed `kemitp`
  until the bridge exists.
