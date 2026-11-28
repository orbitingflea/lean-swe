import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe proofs require Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

package «lean-swe-proofs» where
  packagesDir := "../.lake/packages"
  moreLinkArgs := #["-Wl,-z,now", "-lcrypto", "-Wl,--exclude-libs,libcrypto.a", "-lpthread"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.unusedVariables, true⟩
  ]

require «lean-swe» from ".."

@[default_target]
lean_lib LeanSweProofs where
  globs := #[.one `LeanSweProofs]
