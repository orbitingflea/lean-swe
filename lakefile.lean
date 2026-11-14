import Lake
open Lake DSL

package «lean-swe» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

lean_lib Core where

@[default_target]
lean_lib LeanSwe where
