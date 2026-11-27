import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe proofs require Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

private def aeneasGenMods : Array Lean.Name := #[
  `LeanSweProofs.PostFork.Aeneas.TypesExternal,
  `LeanSweProofs.PostFork.Aeneas.Types,
  `LeanSweProofs.PostFork.Aeneas.FunsExternal,
  `LeanSweProofs.PostFork.Aeneas.Funs
]

package «lean-swe-proofs» where
  packagesDir := "../.lake/packages"
  moreLinkArgs := #["-Wl,-z,now", "-lcrypto", "-Wl,--exclude-libs,libcrypto.a", "-lpthread"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.missingDocs, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

require «lean-swe» from ".."

require «aeneas» from git
  "https://github.com/AeneasVerif/aeneas.git" @ "0d21a9ec7bbbb110110cacc14464a47fd71c8705" / "backends/lean"

@[default_target]
lean_lib LeanSweProofs where
  globs := #[.one `LeanSweProofs]

@[default_target]
lean_lib «LeanSweProofs.PostFork.AeneasGen» where
  roots := aeneasGenMods
  globs := aeneasGenMods.map Glob.one
  leanOptions := #[⟨`weak.linter.missingDocs, false⟩]
