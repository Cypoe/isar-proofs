# GArrowFlow Handoff: Formalizing Koru & ISAR Staging via Generalized Arrows

**Branch:** `host-invariant-realization-pipeline`  
**Commit landed:** `4185c49467afdd9296f25a6c385c15e640e5aa28` (`src/ISAR/GArrowFlow.lean`)  
**Toolchain:** `leanprover/lean4:v4.31.0`

---

## 1. Architectural Decision: Why Generalized Arrows (Megacz) over Free Monad + S4 + Distributive Laws

We evaluated two candidate formalizations for Koru and ISAR's host-independent realization pipeline:

### Rejected: Free Monad + S4 Modal Logic + Beck Distributive Laws (`F G -> G F`)
- **Homogeneous staging assumption:** Davies & Pfenning's S4 modal type theory assumes a single language across stages (guest code lives inside the host's value/type universe). Koru compiles to *heterogeneous* hosts (C99, Zig, C#, FASM) with distinct value universes and runtimes.
- **Fragile effect composition:** Composing two monads via a Beck distributive law `lambda : F G => G F` requires four coherence axioms and hits well-known no-go theorems where no distributive law exists.
- **Wrong control-flow shape:** Koru's `tor` is a named, multi-exit continuation edge statically visible at both ends, not a value-returning Kleisli arrow `a -> F b`.

### Adopted: Generalized Arrows (Adam Megacz) + Coproduct Choice + Elgot Iteration (`GArrowFlow`)
- **Heterogeneous multi-level staging without host leakage:** Megacz proved an isomorphism between multi-level languages and Generalized Arrows by **dropping `arr : (a -> b) -> g a b`**. Stage `n` (the host) orchestrates and flattens expressions into a `GArrow`-polymorphic morphism targeting stage `n+1` (the guest) without embedding arbitrary host functions into the guest.
- **Strict level-adjacency boundary (the 3-Lisp connection):** Like Brian Cantwell Smith's **3-Lisp reflective tower**, each level `n` can only observe, manipulate, or prove invariants about the adjacent level `n+1` — never collapsing into itself. Unlike 3-Lisp (homogeneous, infinite tower), Megacz's GArrow tower is **heterogeneous** across levels and grounded at concrete target instances (`C99`, `FASM`, `ITerm`, etc.).
- **Koru-specific extensions on top of monoidal GArrows:**
  - **Coproduct choice (`sum`, `inl`, `inr`, `fanin`)** for Koru's multi-exit `KArm` / `tor` dispatch (`dispatchTag` / `dispatchBare`).
  - **Elgot feedback (`iter : Hom a (sum b a) -> Hom a b`)** for `KFlow.preLabel` + `KArmNode.jump` loops (`runK ... (.loop ...)`).

---

## 2. File-by-File Map on `host-invariant-realization-pipeline`

| File | Current Role | Relationship to `GArrowFlow` |
| :--- | :--- | :--- |
| `src/ISAR/InvariantLayer.lean` | Defines `ISKSubtype`, `OperEq`, `InvariantLayer := Quotient operEqSetoid`, `app` congruence, `cd_loop_fuel`. | Demoted from *universal substrate* to one degenerate single-object `GArrow` instance (`Obj = Unit`, `Hom () () = ISKSubtype`). Keep intact — existing confluence and `LinearIKTerm` proofs remain valid for that backend. |
| `src/ISAR/DialectKernel.lean` | Legacy `Dialect` structure still hard-wired to `encode : Object -> ISKSubtype` and `decode : InvariantLayer -> Obs`. | Legacy transit layer; do not route new Koru/target realizations through `ISKSubtype` unless explicitly building an SKI backend. |
| `src/ISAR/ObservationRegime.lean` | Decision 068: parameterized `ObservationRegime P` and `QuotientMap P R Q S` away from `ISKSubtype`, but still operates on flat closed terms `P : Type`. | `GArrowFlow` is the categorical lift of `ObservationRegime P` from setoids of closed programs (`P`) to setoid-enriched categories of composable morphisms (`Hom a b` modulo `HomEq`). `GArrowFlowHom` is the compositional lift of `QuotientMap`. |
| `src/ISAR/KernelCategory.lean` | `Kernel P R` and per-regime `substrateKernel_terminal` theorem. | Terminality stays per-regime; `GArrowFlowHom` handles cross-regime realization without requiring a global `decode : Carrier -> P` for irreversible emissions (`KBackend.emit`). |
| `src/ISAR/FlowView.lean` | Tagged-tree codec `encProg`/`decProg : KProg <-> TTerm` with round-trip proof. Explicitly defers ISK-level semantic congruence. | Remains the wire/codec layer (`KEncoding KProg`). `GArrowFlow` sidesteps the need to write a `runK` interpreter inside SKI in order to prove backend soundness. |
| `src/ISAR/FlowDialect.lean` | Reference `runK` evaluator (`KVal`, `KExpr`, `KArm`, `KFlow`, `KCallable`, `KProg`, `KOutcome`, `KResult`, `KOracle`) + `runK_mono` + fixtures (`kArith`, `kCount`). | Directly lifted into `koruSemanticArrow : GArrowFlow` via `FuelHom`, reusing `runK_mono` for `denoteInvoke`, `denoteFlow`, `denoteFlowStep`, and `denoteFlowLoop`. |
| `src/ISAR/KoruDialect.lean` | `KoruLayers` (`KEncoding`, `KGrammar`/`wfProg`, `KSurface`, `KBackend`/`emitC99`) and `SelfHosting` / `SelfHostingC99` Futamura fixpoint propositions. | `emitC99` currently handles only `[("main", .bare e)]`. Extending `emitC99` (or future backends) to full `KFlow`s can be factored as a `GArrowFlowHom` into a `c99Arrow : GArrowFlow` (sequential statements, `switch`/`if-else`, `while`/`goto`), proving soundness per combinator (`comp`, `fanin`, `iter`). |
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

### Task 4: Extend `GArrowFlowHom` & Connect to `KoruDialect` / `InvariantLayer`
- Add choice and iteration preservation laws (`map_sum`, `map_fanin`, `map_iter`) to `GArrowFlowHom` once the exact object-mapping convention is settled.
- Sketch a `c99Arrow : GArrowFlow` target (starting with the `renderCExpr` subset in `KoruDialect.lean`, then adding `fanin` -> `if`/`switch` and `iter` -> `while`/`goto`) so `emitC99` can be refactored into a compositional `GArrowFlowHom`.
- Optionally exhibit `ISKSubtype` / `operEqRegime` as a degenerate single-object `GArrow` instance to formally close the loop with `InvariantLayer.lean`.
