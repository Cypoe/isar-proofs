# GArrowFlow Handoff: Formalizing Koru & ISAR Staging via Generalized Arrows

**Branch:** `host-invariant-realization-pipeline`  
**Commit landed:** `4185c49467afdd9296f25a6c385c15e640e5aa28` (`src/ISAR/GArrowFlow.lean`)  
**Toolchain:** `leanprover/lean4:v4.31.0`

---

## 1. Architectural Decision: Closing the August Square via Generalized Arrows

### 1.1 Why Generalized Arrows (Megacz) over Free Monad + S4 + Distributive Laws

We evaluated two candidate formalizations for Koru and ISAR's host-independent realization pipeline:

- **Rejected — Free Monad + S4 Modal Logic + Beck Distributive Laws (`F G -> G F`):**
  - Davies & Pfenning's S4 modal type theory assumes *homogeneous* staging where guest code lives inside the host's value/type universe. Koru compiles to *heterogeneous* hosts (C99, Zig, C#, FASM) with distinct value universes and runtimes.
  - Beck distributive laws between monads frequently fail to exist (no-go theorems) and require heavy coherence axioms.
  - Koru's `tor` is a named, multi-exit continuation edge statically visible at both ends, not a value-returning Kleisli arrow `a -> F b`.

- **Adopted — Generalized Arrows (Adam Megacz) + Coproduct Choice + Elgot Iteration (`GArrowFlow`):**
  - Megacz proved an isomorphism between *heterogeneous* multi-level languages and Generalized Arrows by **dropping `arr : (a -> b) -> g a b`**. Stage `n` (the host) orchestrates and flattens expressions into a `GArrow`-polymorphic morphism targeting stage `n+1` (the guest) without embedding arbitrary host functions into the guest.
  - Enforces the same strict **adjacency boundary** as Brian Cantwell Smith's **3-Lisp reflective tower** (each level `n` can only observe, manipulate, or prove invariants about the adjacent level `n+1`, never collapsing into itself), except *heterogeneous* across levels and grounded at concrete target instances (`C99`, `FASM`, `ISK`, `InteractionNet`, etc.).
  - Extends Megacz's monoidal GArrows with:
    - **Coproduct choice (`sum`, `inl`, `inr`, `fanin`)** for Koru's multi-exit `KArm` / `tor` dispatch (`dispatchTag` / `dispatchBare`).
    - **Elgot feedback (`iter : Hom a (sum b a) -> Hom a b`)** for `KFlow.preLabel` + `KArmNode.jump` loops (`runK ... (.loop ...)`).

### 1.2 I, S, A in the Base — R Strictly Above the Quotient

This aligns directly with the ISA-Physics / Plex foundation (`ISAR_AXIOMS.md`, `ontology_vs_semantics.md`):

- **I (Identity):** `Obj` + `id : Hom a a` (lives at level `n`).
- **S (State):** Port carriers / environments (`KEnv`, `KResult`, wire state; lives at level `n`).
- **A (Adjacency):** Composable wiring `Hom a b`, `comp`, `fanin`, `iter` without `arr` (lives at level `n` — this *is* the GArrow structure).
- **R (Rule / Rewrite / Observation):** Degenerate at level `n`; sits **above the quotient** as `HomEq` or a realization functor `GArrowFlowHom : G_n -> G_{n+1}` between adjacent levels.

Forcing a concrete `R` (specifically SKI `IRed` / `ITerm`) into the base layer is what forced every hosted dialect to project through SKI.

### 1.3 Closing the August Square & Naming Correction

In the philosophy (`ISAR_AXIOMS.md` Axioms 5–6, `ontology_vs_semantics.md`), **`InvariantLayer` is representation-free** — defined by its universal property:
- **Wiring / syntax side (I, S, A before choosing `R`):** the **initial / free `GArrowFlow`** (pure adjacency/composition with no `arr` and no baked-in rewrite rules).
- **Observation / quotient side (after choosing `O`):** the **terminal object** in the category of admissible views over `O` (`substrateKernel_terminal` in `KernelCategory.lean`).

In the current Lean code, the right side of the August square (`ObservationRegime -> QuotientMap -> CoGen/Realize`) is already built, while the corner anchor (`src/ISAR/InvariantLayer.lean`) still defines `InvariantLayer := Quotient operEqSetoid` over `ISKSubtype`.

**Naming & demotion target:**
1. **Do NOT delete `ObservationRegime.lean`, `QuotientMap`, or `CoGen.lean`** — `ObservationRegime P` is the closed-program (0-morphism) slice of `O`, and `GArrowFlow` is its compositional (I, S, A) lift.
2. **Demote `ISKSubtype / OperEq` to an `R`-chart (`ISKQuotient` / `ISKRealization`)** — one coordinate chart among peers, not the definition of `InvariantLayer`.
3. **Reserve `InvariantLayer` for the representation-free universal property** (the free `GArrowFlow` / terminal quotient over `O`), inhabited by genuinely distinct operational models (`ISK/OperEq`, `DegenerateNet/NetJoin`, `KFlow/FuelHom`, `C99`).

---

## 2. File-by-File Map on `host-invariant-realization-pipeline`

| File | Current Role | Target Role / Relationship to `GArrowFlow` |
| :--- | :--- | :--- |
| `src/ISAR/InvariantLayer.lean` | Defines `ISKSubtype`, `OperEq`, `InvariantLayer := Quotient operEqSetoid`, `app` congruence, `cd_loop_fuel`. | **Demote `ISK` to an `R`-chart (`ISKQuotient` / `ISKRealization`)**. Keep all existing confluence and `LinearIKTerm` proofs intact as proofs about the SKI coordinate chart, not as the universal ground. |
| `src/ISAR/DialectKernel.lean` | Legacy `Dialect` structure still hard-wired to `encode : Object -> ISKSubtype` and `decode : InvariantLayer -> Obs`. | Legacy SKI-transit layer; do not route new Koru/target realizations through `ISKSubtype` unless explicitly building an SKI backend. |
| `src/ISAR/ObservationRegime.lean` | Decision 068: parameterized `ObservationRegime P` and `QuotientMap P R Q S` away from `ISKSubtype`, operating on closed terms `P : Type`. | Keep intact as the closed-program slice of `O`. `GArrowFlow` is its compositional (I, S, A) categorical lift (`Hom a b` modulo `HomEq`); `GArrowFlowHom` is the compositional lift of `QuotientMap`. |
| `src/ISAR/KernelCategory.lean` | `Kernel P R` and per-regime `substrateKernel_terminal` theorem. | Terminality stays per-regime; `GArrowFlowHom` handles cross-regime realization without requiring a global `decode : Carrier -> P` for irreversible emissions (`KBackend.emit`). |
| `src/ISAR/InteractionNet.lean` | Interaction net operational model (`DegenerateNet` / `NetJoin`). | Second genuinely non-SKI coordinate chart inhabiting `O` alongside `ISK/OperEq` and `KFlow/FuelHom`. |
| `src/ISAR/FlowView.lean` | Tagged-tree codec `encProg`/`decProg : KProg <-> TTerm` with round-trip proof. Explicitly defers ISK-level semantic congruence. | Remains the wire/codec layer (`KEncoding KProg`). `GArrowFlow` sidesteps the need to write a `runK` interpreter inside SKI in order to prove backend soundness. |
| `src/ISAR/FlowDialect.lean` | Reference `runK` evaluator (`KVal`, `KExpr`, `KArm`, `KFlow`, `KCallable`, `KProg`, `KOutcome`, `KResult`, `KOracle`) + `runK_mono` + fixtures (`kArith`, `kCount`). | Directly lifted into `koruSemanticArrow : GArrowFlow` via `FuelHom`, reusing `runK_mono` for `denoteInvoke`, `denoteFlow`, `denoteFlowStep`, and `denoteFlowLoop`. |
| `src/ISAR/KoruDialect.lean` | `KoruLayers` (`KEncoding`, `KGrammar`/`wfProg`, `KSurface`, `KBackend`/`emitC99`) and `SelfHosting` / `SelfHostingC99` Futamura fixpoint propositions. | `emitC99` currently handles only `[("main", .bare e)]`. Extending `emitC99` to full `KFlow`s can be factored as a `GArrowFlowHom` into a `c99Arrow : GArrowFlow` (sequential statements, `switch`/`if-else`, `while`/`goto`), proving soundness per combinator (`comp`, `fanin`, `iter`). |
| `src/ISAR/GArrowFlow.lean` | **NEW (commit `4185c49`)** — defines `GArrowFlow`, `GArrowFlowHom`, `FuelHom`, `koruSemanticArrow`, `denoteInvoke`, `denoteFlow`, `denoteFlowStep`, `denoteFlowLoop`, and `denoteInvoke_kArith`. | **Not yet compiled with `lake build` and not yet imported in `src/ISAR.lean`.** |
| `src/ISAR.lean` | Root import list for the Lean library. | Needs `import ISAR.GArrowFlow` once `lake build ISAR.GArrowFlow` passes cleanly. |

---

## 3. Concrete Tasks for Local Agent

### Task 1: Compile & fix `src/ISAR/GArrowFlow.lean`
- Checkout `host-invariant-realization-pipeline` and run `lake build ISAR.GArrowFlow` under `leanprover/lean4:v4.31.0`.
- Fix any Lean 4.31 tactic/`simp`/elaboration issues in:
  - `koruSemanticArrow` (`comp_id_left`, `comp_id_right`, `comp_assoc`, `comp_congr`, `fanin_inl`, `fanin_inr`)
  - `fuelIterGo_mono`
  - `denoteFlowStep`
  - `denoteInvoke_kArith`
- Verify **zero `sorry`s** and **zero new axioms**.

### Task 2: Wire into `src/ISAR.lean`
- Add `import ISAR.GArrowFlow` to `src/ISAR.lean` (alongside `ISAR.FlowDialect` / `ISAR.KoruDialect`).
- Run a full `lake build` and confirm no regressions across existing modules.

### Task 3: Discharge Loop Adequacy (`denoteFlowLoop` <-> `runK ... .loop`)
- Prove that `denoteFlowLoop g o fl env` (defined as `koruSemanticArrow.iter (denoteFlowStep g o fl env)`) is `FuelHom.equiv` to:
  ```lean
  fun fuel hargs => asKResult (runK g o fuel (.loop fl env hargs))
  ```
- Note on fuel accounting: `denoteFlowStep` evaluates both `.invoke fl.head.1` and `.dispatchTag`/`.dispatchBare` at the same `fuel` parameter, while `runK` spends 1 fuel per `.loop` step; use `FuelHom.mono_le` / `runK_mono` in both directions of `FuelHom.equiv` (`∃ k, ...`).
- Add a `kCount` fixture check exercising `#label` / `@jump` iteration through `denoteFlowLoop`.

### Task 4: Close the August Square (Naming & Multi-Chart Realizations)
- **Demote ISK naming (staged refactor — avoid breaking downstream imports in one shot):**
  - Introduce `ISKQuotient` as the explicit name for `Quotient operEqSetoid` (keeping `abbrev InvariantLayer := ISKQuotient` only as a temporary compatibility alias if needed, or migrating callers cleanly once the universal `InvariantLayer` interface lands).
  - Reserve the representation-free `InvariantLayer` name for the universal property (free `GArrowFlow` / terminal quotient over `O`), with zero dependency on `ITerm` / `ISKSubtype`.
- **Extend `GArrowFlowHom`:**
  - Add choice and iteration preservation laws (`map_sum`, `map_fanin`, `map_iter`) once the object-mapping convention is settled.
- **Exhibit multiple coordinate charts inhabiting the same interface:**
  1. `koruSemanticArrow` (`KFlow / FuelHom`) — already in `GArrowFlow.lean`.
  2. `c99Arrow` (starting with `KoruDialect.renderCExpr`, then `fanin` -> `if`/`switch` and `iter` -> `while`/`goto`) with `emitC99` as a `GArrowFlowHom`.
  3. `ISKSubtype / operEqRegime` as a degenerate single-object `GArrow` chart (`Obj = Unit`, `Hom () () = ISKSubtype`).
  4. `DegenerateNet / NetJoin` (`InteractionNet.lean`) as a non-SKI operational witness alongside `ISK` and `KFlow`.
