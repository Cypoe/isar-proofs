import Lake
open Lake DSL

package «isar» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`linter.docBlame, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["ISAR"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib «ISAR» where
  srcDir := "src"
  roots := #[`ISAR]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.31.0"
