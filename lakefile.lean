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

require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "v4.27.0" / "regex"

lean_lib Core where

lean_lib Packages where

@[default_target]
lean_lib LeanSwe where

@[default_target]
lean_exe «lean-swe-test» where
  root := `Tests.Main
