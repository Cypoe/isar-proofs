# ADR 0003: Package Reorganization, Namespace Conflict Resolution & Dependency Setup

## Status
Accepted

## Context
As the repository grows into a professional proof-specification library under Lean 4, we need a clean, standard workspace organization. Keeping library files, standalone test files, and miscellaneous documentation in the root directory causes visual clutter, build configuration difficulties, and potential namespace collisions. Specifically:
- Defining the library root directly on files in `src/` can lead to naming collisions when multiple modules define identifiers (e.g. `compile`, `decode_raw`, and `subst`) directly in the global `ISAR` namespace.
- Standalone test files do not belong to the main library target.
- Python research scripts and CSV output files clutter the root and are not part of the Lean package.

## Decision
We make the following structural decisions:
1. **Source Organization (Option A)**:
   - All library source files are moved to `src/ISAR/`.
   - The entry point [src/ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/src/ISAR.lean) contains only imports/exports of the library submodules.
   - The core syntax file `ISAR.lean` is renamed to [Kernel.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/src/ISAR/Kernel.lean).
2. **Namespace Conflict Resolution**:
   - **`compile`**: Renamed `compile` in `BytecodeView.lean` to `compile_bytecode` and updated references in `ViewUnification.lean` to prevent conflicts with `LambdaFragment.lean`.
   - **`decode_raw` / `decode_raw_val`**: Renamed `decode_raw` in `IotaView.lean` to `iota_decode_raw` and `decode_raw_val` to `iota_decode_raw_val` to prevent conflicts with `TRSView.lean`.
   - **`subst`**: Renamed environment substitution `subst` in `Futamura.lean` to `subst_env` to prevent conflicts with lambda calculus term substitution in `LambdaFragment.lean`.
3. **Workspace Segregation**:
   - **Tests**: Moved all standalone `test_*.lean` files to [test/](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/test/) at the root directory, completely separate from the library target.
   - **ADRs**: Moved Architectural Decision Records (ADRs) to [docs/adr/](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/docs/adr/).
   - **RFCs & Stories**: Moved other markdown files to `docs/rfc/` and `docs/story/`.
   - **Scratch Scripts**: Moved all Python/CSV files to [scratch/](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/scratch/).
4. **Lake Configuration**:
   - Switched from `lakefile.toml` to [lakefile.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/lakefile.lean) to allow conditional dependencies.
   - Added `mathlib`, `checkdecls`, and development dependency `doc-gen4`.

## Consequences
- The workspace root is clean and follows standard Lean 4 repository layouts.
- Rebuilding the entire library is simplified to a single `lake build` command, compiling all 23 jobs in parallel with zero namespace collisions.
- Standalone test files compile independently without polluting the main library target.
