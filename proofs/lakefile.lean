import Lake
open Lake DSL

#eval (if System.Platform.isWindows || System.Platform.isOSX then
    Lean.throwError "LeanSwe proofs require Linux (x86_64 or aarch64)"
  else pure () : Lean.Elab.Command.CommandElabM Unit)

private def aeneasGenMods : Array Lean.Name := #[
  `LeanSwe.PostFork.Aeneas.TypesExternal,
  `LeanSwe.PostFork.Aeneas.Types,
  `LeanSwe.PostFork.Aeneas.FunsExternal,
  `LeanSwe.PostFork.Aeneas.Funs
]

private partial def collectLeanMods (dir : System.FilePath) (pfx : Lean.Name) : IO (Array Lean.Name) := do
  if !(← dir.isDir) then
    return #[]
  let entries ← dir.readDir
  let sorted := entries.qsort fun a b => a.fileName < b.fileName
  let mut out : Array Lean.Name := #[]
  for entry in sorted do
    if ← entry.path.isDir then
      out := out ++ (← collectLeanMods entry.path (pfx.str entry.fileName))
    else if entry.path.extension == some "lean" then
      let stem := (entry.path.withExtension "").fileName.getD ""
      if !stem.isEmpty then
        let mod := pfx.str stem
        if !aeneasGenMods.contains mod then
          out := out.push mod
  return out

private unsafe def proofLibModsUnsafe (_ : Unit) : Array Lean.Name :=
  match unsafeIO (do
    let subMods ← collectLeanMods (__dir__ / "LeanSwe") `LeanSwe
    return #[`LeanSweProofs] ++ subMods) with
  | .ok mods => mods
  | .error _ => #[`LeanSweProofs]

@[implemented_by proofLibModsUnsafe]
private def getProofLibMods (_ : Unit) : Array Lean.Name :=
  #[`LeanSweProofs]

private def proofLibMods : Array Lean.Name :=
  getProofLibMods ()

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
  roots := proofLibMods
  globs := proofLibMods.map Glob.one

@[default_target]
lean_lib «LeanSwe.PostFork.AeneasGen» where
  roots := aeneasGenMods
  globs := aeneasGenMods.map Glob.one
  leanOptions := #[⟨`weak.linter.missingDocs, false⟩]
