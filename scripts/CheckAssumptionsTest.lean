import Lean

/-!
Focused positive and negative mutant self-test suite (`scripts/CheckAssumptionsTest.lean`)
for:
1. `Core.Refines` model-refinement verification and `RuntimeTests` retirement checks in
   `scripts/CheckAssumptions.lean`.
2. `harness/` toolchain and manifest parity checks in `scripts/CheckForeignThinness.lean`.
3. One-way transitive `.olean` import-DAG ratchet, `namespace <Pkg>.Model` inside `Proofs/`,
   and no-proof-content signature checks in `scripts/CheckPromises.lean`.

Compiles `scripts/CheckAssumptions.lean` and `scripts/CheckForeignThinness.lean` directly to
isolated `/tmp` binaries, compiles a spliced driver over `scripts/CheckPromises.lean` that calls
its real `auditImportDagEnv`, `mergeDagReports`, `encodeDagReportWireLines`,
`decodeDagReportWireLines`, and `evaluateDagRatchetWith` helpers directly, verifies clean
miniature baselines (`errors=0`), and injects focused negative mutants covering the targeted
`Core.Refines`/retirement rules and every harness-parity and import-DAG/no-proof-content
diagnostic code, confirming each fails closed with non-zero exit status and the expected
diagnostic code. All `/tmp` artifacts are removed unconditionally on exit.
-/

private def writeFileCreatingParents (p : System.FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile p content

private def runCmd (cmd : String) (args : Array String) (cwd? : Option System.FilePath := none)
    (extraEnv : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := cwd?, env := extraEnv }

private def compileLeanMod (repoRoot : System.FilePath) (leanPath : String) (src : System.FilePath) (olean : System.FilePath) : IO Unit := do
  if let some parent := olean.parent then
    IO.FS.createDirAll parent
  let out ← runCmd "lean"
    #["-R", repoRoot.toString, "-o", olean.toString, src.toString]
    none
    #[("LEAN_SRC_PATH", some repoRoot.toString), ("LEAN_PATH", some leanPath)]
  if out.exitCode != 0 then
    throw (IO.userError s!"lean compile failed for {src}:\n{out.stdout}\n{out.stderr}")

private def buildCheckAssumptionsBin (tmpRoot : System.FilePath) : IO System.FilePath := do
  let cFile := tmpRoot / "CheckAssumptions.c"
  let binFile := tmpRoot / "check-assumptions"
  let r1 ← runCmd "lean" #["-c", cFile.toString, "scripts/CheckAssumptions.lean"]
  if r1.exitCode != 0 then
    throw (IO.userError s!"failed to compile CheckAssumptions.lean to C:\n{r1.stdout}\n{r1.stderr}")
  let r2 ← runCmd "leanc" #["-O2", cFile.toString, "-o", binFile.toString, "-lleanshared"]
  if r2.exitCode != 0 then
    throw (IO.userError s!"failed to link check-assumptions binary:\n{r2.stdout}\n{r2.stderr}")
  return binFile

private def symlinkCoreLib (realLibDir targetLibDir : System.FilePath) : IO Unit := do
  let r1 ← runCmd "ln" #["-sfn", (realLibDir / "Core").toString, (targetLibDir / "Core").toString]
  if r1.exitCode != 0 then throw (IO.userError s!"ln Core failed: {r1.stderr}")
  if ← (realLibDir / "Core.olean").pathExists then
    let r2 ← runCmd "ln" #["-sfn", (realLibDir / "Core.olean").toString, (targetLibDir / "Core.olean").toString]
    if r2.exitCode != 0 then throw (IO.userError s!"ln Core.olean failed: {r2.stderr}")

private structure MiniRepo where
  root : System.FilePath
  libDir : System.FilePath
  leanPath : String

private def defaultSuitesJson : String :=
  "{\n" ++
  "  \"version\": 1,\n" ++
  "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
  "  \"suites\": {\n" ++
  "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
  "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] }\n" ++
  "  }\n" ++
  "}\n"

private def setupBaselineMiniRepo (baseDir realRepo realLibAbs : System.FilePath) : IO MiniRepo := do
  let root := baseDir / "repo"
  let libDir := baseDir / "lib"
  IO.FS.createDirAll root
  IO.FS.createDirAll libDir
  symlinkCoreLib realLibAbs libDir
  let leanPath := s!"{libDir}:{realLibAbs}"

  writeFileCreatingParents (root / "harness/Fuzz/suites.json") defaultSuitesJson
  writeFileCreatingParents (root / "Core/Assumptions.lean") (← IO.FS.readFile (realRepo / "Core/Assumptions.lean"))
  writeFileCreatingParents (root / "Core/NondetTest.lean") (← IO.FS.readFile (realRepo / "Core/NondetTest.lean"))
  writeFileCreatingParents (root / "Core/Refines.lean") (← IO.FS.readFile (realRepo / "Core/Refines.lean"))

  writeFileCreatingParents (root / "LeanSwe/MiniPure/Types.lean")
    "namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\nend LeanSwe.MiniPure\n"
  writeFileCreatingParents (root / "LeanSwe/MiniPure/Model.lean")
    "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\nend LeanSwe.MiniPure.Model\n"
  writeFileCreatingParents (root / "LeanSwe/MiniPure/Impl.lean")
    "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\nend LeanSwe.MiniPure.Internal\n"
  writeFileCreatingParents (root / "LeanSwe/MiniPure/Interface.lean")
    "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\nend LeanSwe.MiniPure\n"
  writeFileCreatingParents (root / "LeanSwe/MiniPure/SpecTests.lean")
    "import Core.NondetTest\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure\nopen Core Core.NondetTest\ndef test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (fn x = Model.evalModel x)\nend LeanSwe.MiniPure\n"
  writeFileCreatingParents (root / "LeanSwe/MiniPure/Proofs.lean")
    "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"

  writeFileCreatingParents (root / "LeanSwe/MiniFloat/Types.lean")
    "namespace LeanSwe.MiniFloat\nstructure FloatRes where\n  bits : UInt64\nend LeanSwe.MiniFloat\n"
  writeFileCreatingParents (root / "LeanSwe/MiniFloat/Model.lean")
    "import Init.Data.Float.Model\nimport LeanSwe.MiniFloat.Types\nnamespace LeanSwe.MiniFloat.Model\ndef isZeroMask (u : UInt64) : Bool := u == 0\ndef modelBits (u : UInt64) : UInt64 := if u == 0 then 0 else let b := (Float.Model.ofBits u).toBits; if b == 0 then 1 else b\ndef allowedGetBits (u out : UInt64) : Prop := if u == 0 then out = 0 else out ≠ 0\nend LeanSwe.MiniFloat.Model\n"
  writeFileCreatingParents (root / "LeanSwe/MiniFloat/Impl.lean")
    "import LeanSwe.MiniFloat.Types\nnamespace LeanSwe.MiniFloat.Internal\ndef implBits (u : UInt64) : UInt64 := if u == 0 then 0 else let b := (Float.ofBits u).toBits; if b == 0 then 1 else b\nend LeanSwe.MiniFloat.Internal\n"
  writeFileCreatingParents (root / "LeanSwe/MiniFloat/Interface.lean")
    "import LeanSwe.MiniFloat.Impl\nnamespace LeanSwe.MiniFloat\ndef getBits (u : UInt64) : UInt64 := Internal.implBits u\nend LeanSwe.MiniFloat\n"
  writeFileCreatingParents (root / "LeanSwe/MiniFloat/SpecTests.lean")
    "import Core.NondetTest\nimport LeanSwe.MiniFloat.Model\nimport LeanSwe.MiniFloat.Interface\nnamespace LeanSwe.MiniFloat\nopen Core Core.NondetTest\ndef test_minifloat_zero {r} [NondetTest r] (fn : UInt64 → UInt64) : r Unit := do\n  let _ ← nondet UInt64\n  NondetTest.assert ((fn 0 == 0) = Model.isZeroMask 0)\nend LeanSwe.MiniFloat\n"
  writeFileCreatingParents (root / "LeanSwe/MiniFloat/Proofs.lean")
    "import Core.Refines\nimport LeanSwe.MiniFloat.SpecTests\nnamespace LeanSwe.MiniFloat.Proofs\ntheorem proof_minifloat : Core.AllPass (LeanSwe.MiniFloat.test_minifloat_zero LeanSwe.MiniFloat.getBits) := fun _ => ⟨rfl, trivial⟩\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniFloat.getBits LeanSwe.MiniFloat.Model.allowedGetBits := fun u => by unfold LeanSwe.MiniFloat.getBits LeanSwe.MiniFloat.Internal.implBits LeanSwe.MiniFloat.Model.allowedGetBits; cases hu : (u == 0) <;> simp_all; cases hf : ((Float.ofBits u).toBits == 0) <;> simp_all\nend LeanSwe.MiniFloat.Proofs\n"

  writeFileCreatingParents (root / "LeanSwe.lean")
    "import Core.NondetTest\nimport Core.Assumptions\nimport Core.Refines\nimport LeanSwe.MiniPure.Types\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Impl\nimport LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniPure.SpecTests\nimport LeanSwe.MiniPure.Proofs\nimport LeanSwe.MiniFloat.Types\nimport LeanSwe.MiniFloat.Model\nimport LeanSwe.MiniFloat.Impl\nimport LeanSwe.MiniFloat.Interface\nimport LeanSwe.MiniFloat.SpecTests\nimport LeanSwe.MiniFloat.Proofs\n"

  writeFileCreatingParents (root / "harness/Tests/Main.lean")
    "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  Core.closeAssumpLog\n  return 0\n"

  let buildOrder := #[
    "LeanSwe/MiniPure/Types",
    "LeanSwe/MiniPure/Model",
    "LeanSwe/MiniPure/Impl",
    "LeanSwe/MiniPure/Interface",
    "LeanSwe/MiniPure/SpecTests",
    "LeanSwe/MiniPure/Proofs",
    "LeanSwe/MiniFloat/Types",
    "LeanSwe/MiniFloat/Model",
    "LeanSwe/MiniFloat/Impl",
    "LeanSwe/MiniFloat/Interface",
    "LeanSwe/MiniFloat/SpecTests",
    "LeanSwe/MiniFloat/Proofs",
    "LeanSwe"
  ]
  for m in buildOrder do
    compileLeanMod root leanPath (root / s!"{m}.lean") (libDir / s!"{m}.olean")
  compileLeanMod (root / "harness") leanPath (root / "harness/Tests/Main.lean")
    (root / "harness/.lake/build/lib/lean/Tests/Main.olean")

  return { root, libDir, leanPath }

private def copyDirTree (src dst : System.FilePath) : IO Unit := do
  let r ← runCmd "cp" #["-a", src.toString, dst.toString]
  if r.exitCode != 0 then
    throw (IO.userError s!"cp -a {src} {dst} failed: {r.stderr}")

private def expectFailureCode
    (bin : System.FilePath)
    (caseName expectedCode : String)
    (libDir repoDir : System.FilePath)
    (extraArgs : Array String := #["--allow-legacy"]) : IO Unit := do
  let out ← runCmd bin.toString (#[libDir.toString, repoDir.toString] ++ extraArgs)
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 then
    throw (IO.userError s!"FAIL [{caseName}]: expected exit != 0 with {expectedCode}, but exited 0:\n{combined}")
  if (combined.splitOn expectedCode).length <= 1 then
    throw (IO.userError s!"FAIL [{caseName}]: expected error code '{expectedCode}', got:\n{combined}")
  IO.println s!"PASS [{caseName}] -> {expectedCode}"

private def runMutantCase
    (base : MiniRepo)
    (tmpRoot bin : System.FilePath)
    (caseName expectedCode : String)
    (mutate : MiniRepo → IO (Array String)) : IO Unit := do
  let caseDir := tmpRoot / s!"case_{caseName}"
  let repoCopy := caseDir / "repo"
  let libCopy := caseDir / "lib"
  IO.FS.createDirAll caseDir
  copyDirTree base.root repoCopy
  copyDirTree base.libDir libCopy
  let mr : MiniRepo := {
    root := repoCopy
    libDir := libCopy
    leanPath := s!"{libCopy}:{base.leanPath}"
  }
  let recompileMods ← mutate mr
  for m in recompileMods do
    if m == "Tests/Main" then
      compileLeanMod (mr.root / "harness") mr.leanPath (mr.root / "harness/Tests/Main.lean")
        (mr.root / "harness/.lake/build/lib/lean/Tests/Main.olean")
    else
      compileLeanMod mr.root mr.leanPath (mr.root / s!"{m}.lean") (mr.libDir / s!"{m}.olean")
  expectFailureCode bin caseName expectedCode mr.libDir mr.root
  IO.FS.removeDirAll caseDir

private def runPositiveCase
    (base : MiniRepo)
    (tmpRoot bin : System.FilePath)
    (caseName : String)
    (mutate : MiniRepo → IO (Array String)) : IO Unit := do
  let caseDir := tmpRoot / s!"pos_{caseName}"
  let repoCopy := caseDir / "repo"
  let libCopy := caseDir / "lib"
  IO.FS.createDirAll caseDir
  copyDirTree base.root repoCopy
  copyDirTree base.libDir libCopy
  let mr : MiniRepo := {
    root := repoCopy
    libDir := libCopy
    leanPath := s!"{libCopy}:{base.leanPath}"
  }
  let recompileMods ← mutate mr
  for m in recompileMods do
    if m == "Tests/Main" then
      compileLeanMod (mr.root / "harness") mr.leanPath (mr.root / "harness/Tests/Main.lean")
        (mr.root / "harness/.lake/build/lib/lean/Tests/Main.olean")
    else
      compileLeanMod mr.root mr.leanPath (mr.root / s!"{m}.lean") (mr.libDir / s!"{m}.olean")
  let out ← runCmd bin.toString #[mr.libDir.toString, mr.root.toString, "--allow-legacy"]
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode != 0 || (combined.splitOn "errors=0").length <= 1 then
    throw (IO.userError s!"FAIL [{caseName}]: expected exit=0 errors=0, got exit={out.exitCode}:\n{combined}")
  IO.println s!"PASS [{caseName}] -> accepted (errors=0)"
  IO.FS.removeDirAll caseDir

private def buildForeignThinnessBin (tmpRoot : System.FilePath) : IO System.FilePath := do
  let cFile := tmpRoot / "CheckForeignThinness.c"
  let binFile := tmpRoot / "check-foreign-thinness"
  let r1 ← runCmd "lean" #["-DwarningAsError=true", "-c", cFile.toString, "scripts/CheckForeignThinness.lean"]
  if r1.exitCode != 0 then
    throw (IO.userError s!"failed to compile CheckForeignThinness.lean to C:\n{r1.stdout}\n{r1.stderr}")
  let r2 ← runCmd "leanc" #["-O2", cFile.toString, "-o", binFile.toString, "-lleanshared"]
  if r2.exitCode != 0 then
    throw (IO.userError s!"failed to link check-foreign-thinness binary:\n{r2.stdout}\n{r2.stderr}")
  return binFile

private def setJsonObjField (obj : Lean.Json) (field : String) (val : Lean.Json) : IO Lean.Json := do
  match obj with
  | .obj m => return .obj (m.insert field val)
  | _ => throw (IO.userError s!"expected JSON object while setting field '{field}'")

private def mapFirstManifestPkg
    (manifest : Lean.Json)
    (ctx : String)
    (pred : Lean.Json → Bool)
    (mutate : Lean.Json → IO Lean.Json) : IO String := do
  let pkgs ← match manifest.getObjVal? "packages" with
    | .ok (.arr a) => pure a
    | _ => throw (IO.userError s!"manifest missing 'packages' array ({ctx})")
  let mut out : Array Lean.Json := #[]
  let mut matched := false
  for entry in pkgs do
    if !matched && pred entry then
      out := out.push (← mutate entry)
      matched := true
    else
      out := out.push entry
  unless matched do
    throw (IO.userError s!"no matching package entry found in harness/lake-manifest.json for mutation '{ctx}'")
  let updated ← setJsonObjField manifest "packages" (.arr out)
  return updated.pretty

private def dropFirstManifestPkg
    (manifest : Lean.Json)
    (ctx : String)
    (pred : Lean.Json → Bool) : IO String := do
  let pkgs ← match manifest.getObjVal? "packages" with
    | .ok (.arr a) => pure a
    | _ => throw (IO.userError s!"manifest missing 'packages' array ({ctx})")
  let mut out : Array Lean.Json := #[]
  let mut matched := false
  for entry in pkgs do
    if !matched && pred entry then
      matched := true
    else
      out := out.push entry
  unless matched do
    throw (IO.userError s!"no matching package entry found in manifest for mutation '{ctx}'")
  let updated ← setJsonObjField manifest "packages" (.arr out)
  return updated.pretty

private def appendManifestPkg
    (manifest : Lean.Json)
    (ctx : String)
    (pred : Lean.Json → Bool)
    (makeExtra : Lean.Json → IO Lean.Json) : IO String := do
  let pkgs ← match manifest.getObjVal? "packages" with
    | .ok (.arr a) => pure a
    | _ => throw (IO.userError s!"manifest missing 'packages' array ({ctx})")
  let mut extra? : Option Lean.Json := none
  for entry in pkgs do
    if extra?.isNone && pred entry then
      extra? := some (← makeExtra entry)
  let some extra := extra?
    | throw (IO.userError s!"no matching package entry found in manifest for mutation '{ctx}'")
  let updated ← setJsonObjField manifest "packages" (.arr (pkgs.push extra))
  return updated.pretty

private def isInheritedPkg (entry : Lean.Json) : Bool :=
  (entry.getObjValAs? Bool "inherited").toOption == some true

private def isInheritedGitPkg (entry : Lean.Json) : Bool :=
  isInheritedPkg entry && (entry.getObjValAs? String "type").toOption == some "git"

private def toggleHexStr (s : String) : String :=
  if s.startsWith "0" then "1" ++ (s.drop 1).toString
  else "0" ++ (s.drop 1).toString

private def expectOutputContains
    (caseName expectedCode : String)
    (out : IO.Process.Output)
    (forbiddenCodes : Array String := #[]) : IO Unit := do
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 then
    throw (IO.userError s!"FAIL [{caseName}]: expected exit != 0 with {expectedCode}, got exit 0:\n{combined}")
  if (combined.splitOn expectedCode).length <= 1 then
    throw (IO.userError s!"FAIL [{caseName}]: expected code '{expectedCode}', got:\n{combined}")
  for bad in forbiddenCodes do
    if (combined.splitOn bad).length > 1 then
      throw (IO.userError s!"FAIL [{caseName}]: unexpected code '{bad}' also emitted:\n{combined}")
  IO.println s!"PASS [{caseName}] -> {expectedCode}"

private def runHarnessParitySelfTests (tmpRoot realRepo : System.FilePath) : IO Unit := do
  let bin ← buildForeignThinnessBin tmpRoot
  let baseDir := tmpRoot / "harness_parity_base"
  IO.FS.createDirAll baseDir
  let tcBytes ← IO.FS.readBinFile (realRepo / "lean-toolchain")
  let rootManRaw ← IO.FS.readFile (realRepo / "lake-manifest.json")
  let harnessManRaw ← IO.FS.readFile (realRepo / "harness" / "lake-manifest.json")
  let rootManJson ← match Lean.Json.parse rootManRaw with
    | .ok j => pure j
    | .error err => throw (IO.userError s!"failed to parse root lake-manifest.json: {err}")
  let harnessManJson ← match Lean.Json.parse harnessManRaw with
    | .ok j => pure j
    | .error err => throw (IO.userError s!"failed to parse harness/lake-manifest.json: {err}")
  let expectedInheritedCount ← match rootManJson.getObjVal? "packages" with
    | .ok (.arr a) => pure a.size
    | _ => throw (IO.userError "root lake-manifest.json missing 'packages' array")
  let minBudget : String :=
    "{\n" ++
    "  \"version\": 1,\n" ++
    "  \"files\": {},\n" ++
    "  \"vendored_files\": {},\n" ++
    "  \"function_overrides\": {},\n" ++
    "  \"named_thread_helpers\": []\n" ++
    "}\n"
  let initParityRepo (dir : System.FilePath) : IO Unit := do
    IO.FS.createDirAll (dir / "harness")
    IO.FS.writeFile (dir / ".foreign-budget.json") minBudget
    IO.FS.writeBinFile (dir / "lean-toolchain") tcBytes
    IO.FS.writeBinFile (dir / "harness" / "lean-toolchain") tcBytes
    IO.FS.writeFile (dir / "lake-manifest.json") rootManRaw
    IO.FS.writeFile (dir / "harness" / "lake-manifest.json") harnessManRaw
    let gi ← runCmd "git" #["init", "-q"] (some dir)
    if gi.exitCode != 0 then
      throw (IO.userError s!"git init failed: {gi.stderr}")
    let ga ← runCmd "git" #["add", ".foreign-budget.json", "lean-toolchain", "lake-manifest.json",
      "harness/lean-toolchain", "harness/lake-manifest.json"] (some dir)
    if ga.exitCode != 0 then
      throw (IO.userError s!"git add failed: {ga.stderr}")
  initParityRepo baseDir
  let okOut ← runCmd bin.toString #[baseDir.toString]
  let okCombined := okOut.stdout ++ "\n" ++ okOut.stderr
  let expectedBanner := s!"HARNESS_PARITY_CHECK: inherited_packages={expectedInheritedCount} errors=0"
  if okOut.exitCode != 0 || (okCombined.splitOn expectedBanner).length <= 1 then
    throw (IO.userError s!"FAIL [harness_parity_clean]: expected exit 0 with '{expectedBanner}':\n{okCombined}")
  IO.println s!"PASS [harness_parity_clean] -> {expectedBanner}"

  let runParityMut (name code : String)
      (mutate : System.FilePath → IO Unit)
      (forbiddenCodes : Array String := #[]) : IO Unit := do
    let d := tmpRoot / s!"parity_{name}"
    copyDirTree baseDir d
    mutate d
    let out ← runCmd bin.toString #[d.toString]
    expectOutputContains name code out forbiddenCodes
    IO.FS.removeDirAll d

  runParityMut "harness_toolchain_version_drift" "HARNESS_TOOLCHAIN_MISMATCH" fun d => do
    let curStr := (String.fromUTF8? tcBytes).getD ""
    let drifted := if curStr == "leanprover/lean4:v0.0.0" then "leanprover/lean4:v0.0.1" else "leanprover/lean4:v0.0.0"
    IO.FS.writeFile (d / "harness" / "lean-toolchain") drifted
  runParityMut "harness_toolchain_trailing_byte" "HARNESS_TOOLCHAIN_MISMATCH" fun d => do
    let mut extra := tcBytes
    extra := extra.push 10
    IO.FS.writeBinFile (d / "harness" / "lean-toolchain") extra
  runParityMut "harness_toolchain_empty" "HARNESS_TOOLCHAIN_INVALID"
      (forbiddenCodes := #["HARNESS_TOOLCHAIN_MISMATCH", "HARNESS_TOOLCHAIN_MISSING"]) fun d => do
    IO.FS.writeBinFile (d / "lean-toolchain") ByteArray.empty
    IO.FS.writeBinFile (d / "harness" / "lean-toolchain") ByteArray.empty
  runParityMut "harness_toolchain_missing" "HARNESS_TOOLCHAIN_MISSING" fun d => do
    IO.FS.removeFile (d / "harness" / "lean-toolchain")
  runParityMut "harness_manifest_invalid_json" "HARNESS_MANIFEST_ERROR" fun d => do
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") "{invalid-json"
  runParityMut "harness_manifest_packages_dir_drift" "HARNESS_MANIFEST_PACKAGES_DIR_MISMATCH" fun d => do
    let updated ← setJsonObjField harnessManJson "packagesDir" (.str ".lake/packages")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") updated.pretty
  runParityMut "harness_manifest_version_drift" "HARNESS_MANIFEST_FIELD_MISMATCH: manifest 'version' differs" fun d => do
    let updated ← setJsonObjField harnessManJson "version" (.str "0.0.0-drift")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") updated.pretty
  runParityMut "harness_manifest_fixed_toolchain_drift" "HARNESS_MANIFEST_FIELD_MISMATCH: manifest 'fixedToolchain' differs" fun d => do
    let cur := (harnessManJson.getObjValAs? Bool "fixedToolchain").toOption.getD false
    let updated ← setJsonObjField harnessManJson "fixedToolchain" (.bool (!cur))
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") updated.pretty
  runParityMut "harness_manifest_rev_drift" "HARNESS_MANIFEST_FIELD_MISMATCH" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "rev_drift" isInheritedGitPkg fun e => do
      let curRev := (e.getObjValAs? String "rev").toOption.getD "deadbeef"
      setJsonObjField e "rev" (.str (toggleHexStr curRev))
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_input_rev_drift" "HARNESS_MANIFEST_FIELD_MISMATCH" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "input_rev_drift" isInheritedGitPkg fun e => do
      let cur := (e.getObjValAs? String "inputRev").toOption.getD "main"
      setJsonObjField e "inputRev" (.str s!"{cur}-drift")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_subdir_drift" "HARNESS_MANIFEST_FIELD_MISMATCH" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "subdir_drift" isInheritedGitPkg fun e => do
      let nextVal : Lean.Json := match (e.getObjVal? "subDir").toOption with
        | some (.str s) => .str s!"{s}/drift"
        | _ => .str "drift-subdir"
      setJsonObjField e "subDir" nextVal
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_scope_drift" "HARNESS_MANIFEST_FIELD_MISMATCH" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "scope_drift" isInheritedGitPkg fun e => do
      let curScope := (e.getObjValAs? String "scope").toOption.getD ""
      setJsonObjField e "scope" (.str s!"{curScope}-drift")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_missing_pkg" "HARNESS_MANIFEST_MISSING_PACKAGE"
      (forbiddenCodes := #["HARNESS_MANIFEST_EXTRA_PACKAGE", "HARNESS_MANIFEST_MISSING_ROOT_DEP"]) fun d => do
    let mutated ← dropFirstManifestPkg harnessManJson "delete_inherited_pkg" isInheritedPkg
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_extra_pkg" "HARNESS_MANIFEST_EXTRA_PACKAGE"
      (forbiddenCodes := #["HARNESS_MANIFEST_MISSING_PACKAGE", "HARNESS_MANIFEST_DUPLICATE_PACKAGE"]) fun d => do
    let mutated ← appendManifestPkg harnessManJson "append_extra_pkg" isInheritedPkg fun e => do
      let curName := (e.getObjValAs? String "name").toOption.getD "pkg"
      setJsonObjField e "name" (.str s!"{curName}-extra-drift")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_duplicate_pkg" "HARNESS_MANIFEST_DUPLICATE_PACKAGE"
      (forbiddenCodes := #["HARNESS_MANIFEST_MISSING_PACKAGE", "HARNESS_MANIFEST_EXTRA_PACKAGE"]) fun d => do
    let mutated ← appendManifestPkg harnessManJson "dup_harness_pkg" isInheritedPkg pure
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "root_manifest_duplicate_pkg" "HARNESS_MANIFEST_DUPLICATE_PACKAGE"
      (forbiddenCodes := #["HARNESS_MANIFEST_MISSING_PACKAGE", "HARNESS_MANIFEST_EXTRA_PACKAGE"]) fun d => do
    let mutated ← appendManifestPkg rootManJson "dup_root_pkg" (fun _ => true) pure
    IO.FS.writeFile (d / "lake-manifest.json") mutated
  runParityMut "harness_manifest_unexpected_direct_dep" "HARNESS_MANIFEST_UNEXPECTED_PACKAGE" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "unexpected_direct_dep" isInheritedPkg fun e =>
      setJsonObjField e "inherited" (.bool false)
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_root_dep_drift" "HARNESS_MANIFEST_ROOT_DEP_MISMATCH" fun d => do
    let mutated ← mapFirstManifestPkg harnessManJson "root_dep_drift" (fun e => !isInheritedPkg e) fun e =>
      setJsonObjField e "dir" (.str "../drift")
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_missing_root_dep" "HARNESS_MANIFEST_MISSING_ROOT_DEP"
      (forbiddenCodes := #["HARNESS_MANIFEST_MISSING_PACKAGE", "HARNESS_MANIFEST_EXTRA_PACKAGE"]) fun d => do
    let mutated ← dropFirstManifestPkg harnessManJson "drop_root_dep" (fun e => !isInheritedPkg e)
    IO.FS.writeFile (d / "harness" / "lake-manifest.json") mutated
  runParityMut "harness_manifest_missing" "HARNESS_MANIFEST_MISSING" fun d => do
    IO.FS.removeFile (d / "harness" / "lake-manifest.json")
  IO.FS.removeDirAll baseDir

private def buildDagRatchetDriver (tmpRoot realRepo : System.FilePath) : IO System.FilePath := do
  let src ← IO.FS.readFile (realRepo / "scripts" / "CheckPromises.lean")
  let marker := "unsafe def main (args : List String) : IO UInt32 := do"
  let parts := src.splitOn marker
  if parts.length != 2 then
    throw (IO.userError "failed to locate CheckPromises.lean main marker for DAG self-test driver")
  let driverSrc := parts.head! ++
    "unsafe def main (args : List String) : IO UInt32 := do\n" ++
    "  if args.head? == some \"--ipc-roundtrip\" then\n" ++
    "    let vKey := \"WITHIN|LeanSwe.MiniPf.SpecTests|LeanSwe.MiniPf.Impl\"\n" ++
    "    let vMsg := \"DAG_WITHIN_VIOLATION: LeanSwe.MiniPf.SpecTests (SpecTests) transitively imports same-package LeanSwe.MiniPf.Impl (Impl)\"\n" ++
    "    let sKey := \"LeanSwe.MiniPf.Proofs|LeanSwe.MiniPf.Proofs|LeanSwe.MiniPf.Proofs.mock\"\n" ++
    "    let workerRep1 : DagAuditReport := {\n" ++
    "      violations := recordDagViolation {} vKey vMsg\n" ++
    "      sigProofCounts := recordSigProofHit (recordSigProofHit {} sKey \"thm1\") sKey \"thm2\"\n" ++
    "      checkedModules := 4\n" ++
    "    }\n" ++
    "    let workerRep2 : DagAuditReport := {\n" ++
    "      violations := recordDagViolation {} vKey \"DUPLICATE_MSG_IGNORED\"\n" ++
    "      sigProofCounts := recordSigProofHit (recordSigProofHit (recordSigProofHit {} sKey \"thm2\") sKey \"thm3\") sKey \"thm4\"\n" ++
    "      checkedModules := 2\n" ++
    "    }\n" ++
    "    let wireLines := #[\"PFW_MOD:LeanSwe.PostFork.Verified\"] ++\n" ++
    "      encodeDagReportWireLines workerRep1 ++\n" ++
    "      encodeDagReportWireLines workerRep2 ++\n" ++
    "      #[\"PFW_STATS:1:2:1\"]\n" ++
    "    let decoded := decodeDagReportWireLines wireLines\n" ++
    "    let decodedOk :=\n" ++
    "      decoded.checkedModules == 6 &&\n" ++
    "      decoded.violations.get? vKey == some vMsg &&\n" ++
    "      decoded.sigProofCounts.get? sKey == some (5, #[\"thm1\", \"thm2\", \"thm3\"])\n" ++
    "    let mainRep : DagAuditReport := {\n" ++
    "      violations := {}\n" ++
    "      sigProofCounts := recordSigProofHit {} sKey \"thm0\"\n" ++
    "      checkedModules := 9\n" ++
    "    }\n" ++
    "    let merged := mergeDagReports mainRep decoded\n" ++
    "    let mergedSamplesOk := merged.sigProofCounts.get? sKey == some (6, #[\"thm0\", \"thm1\", \"thm2\"])\n" ++
    "    let okErrs := evaluateDagRatchetWith #[vKey] #[(sKey, 6)] merged\n" ++
    "    let missErrs := evaluateDagRatchetWith #[] #[(sKey, 6)] merged\n" ++
    "    let grewErrs := evaluateDagRatchetWith #[vKey] #[(sKey, 5)] merged\n" ++
    "    let staleErrs := evaluateDagRatchetWith #[vKey] #[(sKey, 7)] merged\n" ++
    "    if !decodedOk || !mergedSamplesOk || merged.checkedModules != 15 || !okErrs.isEmpty || missErrs.size != 1 || grewErrs.size != 1 || staleErrs.size != 1 then\n" ++
    "      IO.eprintln s!\"IPC_ROUNDTRIP_FAIL: decodedOk={decodedOk} mergedSamplesOk={mergedSamplesOk} mods={merged.checkedModules} ok={okErrs.size} miss={missErrs.size} grew={grewErrs.size} stale={staleErrs.size}\"\n" ++
    "      return 1\n" ++
    "    IO.println \"PASS_IPC_ROUNDTRIP\"\n" ++
    "    return 0\n" ++
    "  if args.head? == some \"--ctoridx-check\" then\n" ++
    "    let libDir : System.FilePath := args[1]!\n" ++
    "    initSearchPath (← findSysroot) [libDir]\n" ++
    "    enableInitializersExecution\n" ++
    "    let env ← importModules #[{ module := `LeanSwe.MiniA.Types }] {} (loadExts := true)\n" ++
    "    let pubName := `LeanSwe.MiniA.Tag.ctorIdx\n" ++
    "    let pubImpl := pubName.str \"_impl\"\n" ++
    "    let some pubInfo := env.find? pubName | do IO.eprintln \"CTORIDX_MISSING_PUB\"; return 1\n" ++
    "    let some (.defnInfo pubDef) := env.find? pubName | do IO.eprintln \"CTORIDX_BAD_PUB\"; return 1\n" ++
    "    let privName := env.constants.fold (init := Name.anonymous) fun acc n _ =>\n" ++
    "      if n.isStr && n.getString! == \"ctorIdx\" && isPrivateName n && (n.toString.splitOn \"PrivTag\").length > 1 then n else acc\n" ++
    "    let some privInfo := env.find? privName | do IO.eprintln \"CTORIDX_MISSING_PRIV\"; return 1\n" ++
    "    let okPub ← isCompilerGeneratedCtorIdx env pubName pubImpl pubInfo\n" ++
    "    let okPriv ← isCompilerGeneratedCtorIdx env privName (privName.str \"_impl\") privInfo\n" ++
    "    let badNum ← isCompilerGeneratedCtorIdx env (Name.num `LeanSwe.MiniA.Tag 0) pubImpl pubInfo\n" ++
    "    let badAnon ← isCompilerGeneratedCtorIdx env Name.anonymous pubImpl pubInfo\n" ++
    "    let badRoot ← isCompilerGeneratedCtorIdx env (Name.mkStr1 \"ctorIdx\") ((Name.mkStr1 \"ctorIdx\").str \"_impl\") pubInfo\n" ++
    "    let badImpl ← isCompilerGeneratedCtorIdx env pubName (pubName.str \"_fake\") pubInfo\n" ++
    "    let badMismatch ← isCompilerGeneratedCtorIdx env pubName pubImpl privInfo\n" ++
    "    let badUnsafeNum ← isAllowedCompilerUnsafeDef env (Name.num `LeanSwe.MiniA.Tag 0) pubDef\n" ++
    "    let badUnsafeAnon ← isAllowedCompilerUnsafeDef env Name.anonymous pubDef\n" ++
    "    if !okPub || !okPriv || badNum || badAnon || badRoot || badImpl || badMismatch || badUnsafeNum || badUnsafeAnon then\n" ++
    "      IO.eprintln s!\"CTORIDX_CHECK_FAIL: okPub={okPub} okPriv={okPriv} badNum={badNum} badAnon={badAnon} badRoot={badRoot} badImpl={badImpl} badMismatch={badMismatch} badUnsafeNum={badUnsafeNum} badUnsafeAnon={badUnsafeAnon}\"\n" ++
    "      return 1\n" ++
    "    IO.println \"PASS_CTORIDX_CHECK\"\n" ++
    "    return 0\n" ++
    "  let libDir : System.FilePath := args[0]!\n" ++
    "  let rootMods := (args[1]!.splitOn \",\").filter (!·.isEmpty) |>.toArray.map (·.toName)\n" ++
    "  let edgeCsv := args[2]!\n" ++
    "  let sigCsv := args[3]!\n" ++
    "  let allowEdges := if edgeCsv.isEmpty then #[] else (edgeCsv.splitOn \";\").filter (!·.isEmpty) |>.toArray\n" ++
    "  let mut allowSigs : Array (String × Nat) := #[]\n" ++
    "  if !sigCsv.isEmpty then\n" ++
    "    for item in (sigCsv.splitOn \";\").filter (!·.isEmpty) do\n" ++
    "      match item.splitOn \"=\" with\n" ++
    "      | [k, n] => allowSigs := allowSigs.push (k, n.toNat!)\n" ++
    "      | _ => pure ()\n" ++
    "  initSearchPath (← findSysroot) [libDir]\n" ++
    "  enableInitializersExecution\n" ++
    "  let env ← importModules (rootMods.map fun m => { module := m }) {} (loadExts := true)\n" ++
    "  let rep := auditImportDagEnv env (fun _ => true) {} {} true\n" ++
    "  let errs := evaluateDagRatchetWith allowEdges allowSigs rep\n" ++
    "  IO.println s!\"DAG_TEST_SUMMARY: mods={rep.checkedModules} obs_edges={rep.violations.size} obs_sigs={rep.sigProofCounts.size} errors={errs.size}\"\n" ++
    "  for e in errs do\n" ++
    "    IO.eprintln e\n" ++
    "  return if errs.isEmpty then 0 else 1\n"
  let leanFile := tmpRoot / "DagRatchetDriver.lean"
  let cFile := tmpRoot / "DagRatchetDriver.c"
  let binFile := tmpRoot / "dag-ratchet-driver"
  IO.FS.writeFile leanFile driverSrc
  let r1 ← runCmd "lean" #["-R", tmpRoot.toString, "-c", cFile.toString, leanFile.toString] (some tmpRoot)
  if r1.exitCode != 0 then
    throw (IO.userError s!"failed to compile DagRatchetDriver.lean:\n{r1.stdout}\n{r1.stderr}")
  let r2 ← runCmd "leanc" #["-O2", cFile.toString, "-o", binFile.toString, "-lleanshared"]
  if r2.exitCode != 0 then
    throw (IO.userError s!"failed to link dag-ratchet-driver:\n{r2.stdout}\n{r2.stderr}")
  return binFile

private def runImportDagSelfTests (tmpRoot realRepo realLibAbs : System.FilePath) : IO Unit := do
  let bin ← buildDagRatchetDriver tmpRoot realRepo
  let baseDir := tmpRoot / "dag_base"
  let root := baseDir / "repo"
  let libDir := baseDir / "lib"
  IO.FS.createDirAll root
  IO.FS.createDirAll libDir
  symlinkCoreLib realLibAbs libDir
  let leanPath := s!"{libDir}:{realLibAbs}"

  writeFileCreatingParents (root / "LeanSwe/MiniA/Types.lean")
    "namespace LeanSwe.MiniA\ninductive Tag where | a | b deriving BEq\nprivate inductive PrivTag where | p | q\nend LeanSwe.MiniA\n"
  writeFileCreatingParents (root / "LeanSwe/MiniA/Model.lean")
    "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Model\ndef step (t : Tag) : Nat := match t with | .a => 1 | .b => 2\nend LeanSwe.MiniA.Model\n"
  writeFileCreatingParents (root / "LeanSwe/MiniA/Impl.lean")
    "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ndef stepImpl (t : Tag) : Nat := match t with | .a => 1 | .b => 2\nend LeanSwe.MiniA.Internal\n"
  writeFileCreatingParents (root / "LeanSwe/MiniA/Interface.lean")
    "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef step (t : Tag) : Nat := Internal.stepImpl t\nend LeanSwe.MiniA\n"
  writeFileCreatingParents (root / "LeanSwe/MiniA/SpecTests.lean")
    "import Core.NondetTest\nimport LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA\nopen Core Core.NondetTest\ndef test_a {r} [NondetTest r] (f : Tag → Nat) : r Unit := do\n  let x ← nondet Tag\n  NondetTest.assert (f x = Model.step x)\nend LeanSwe.MiniA\n"
  writeFileCreatingParents (root / "LeanSwe/MiniA/Proofs.lean")
    "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem step_cases (t : Tag) : Model.step t = Internal.stepImpl t := by cases t <;> simp [Model.step, Internal.stepImpl]\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a LeanSwe.MiniA.step) := fun t => ⟨by cases t <;> rfl, trivial⟩\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniA.step LeanSwe.MiniA.Model.step := fun t => by cases t <;> rfl\nend LeanSwe.MiniA.Proofs\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/Types.lean")
    "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniB\nabbrev BTag := LeanSwe.MiniA.Tag\nend LeanSwe.MiniB\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/Model.lean")
    "import LeanSwe.MiniA.Model\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.Model\ndef evalB (t : BTag) : Nat := LeanSwe.MiniA.Model.step t\nend LeanSwe.MiniB.Model\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/SysBridge.lean")
    "import LeanSwe.MiniA.Interface\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.SysBridge\ndef runB (t : BTag) : Nat := LeanSwe.MiniA.step t\nend LeanSwe.MiniB.SysBridge\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/Impl.lean")
    "import LeanSwe.MiniB.SysBridge\nnamespace LeanSwe.MiniB.Internal\ndef implB (t : BTag) : Nat := SysBridge.runB t\nend LeanSwe.MiniB.Internal\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/Interface.lean")
    "import LeanSwe.MiniB.Impl\nnamespace LeanSwe.MiniB\ndef callB (t : BTag) : Nat := Internal.implB t\nend LeanSwe.MiniB\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/RuntimeTests.lean")
    "import LeanSwe.MiniB.Interface\nnamespace LeanSwe.MiniB.RuntimeTests\ndef runOk : Nat := LeanSwe.MiniB.callB .a\nend LeanSwe.MiniB.RuntimeTests\n"
  writeFileCreatingParents (root / "LeanSwe/MiniB/Proofs.lean")
    "import Core.Refines\nimport LeanSwe.MiniB.Model\nimport LeanSwe.MiniB.Interface\nnamespace LeanSwe.MiniB.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniB.callB LeanSwe.MiniB.Model.evalB := fun t => by cases t <;> rfl\nend LeanSwe.MiniB.Proofs\n"
  writeFileCreatingParents (root / "LeanSwe.lean")
    "import LeanSwe.MiniA.Proofs\nimport LeanSwe.MiniB.RuntimeTests\nimport LeanSwe.MiniB.Proofs\n"

  let order := #[
    "LeanSwe/MiniA/Types", "LeanSwe/MiniA/Model", "LeanSwe/MiniA/Impl",
    "LeanSwe/MiniA/Interface", "LeanSwe/MiniA/SpecTests", "LeanSwe/MiniA/Proofs",
    "LeanSwe/MiniB/Types", "LeanSwe/MiniB/Model", "LeanSwe/MiniB/SysBridge",
    "LeanSwe/MiniB/Impl", "LeanSwe/MiniB/Interface", "LeanSwe/MiniB/RuntimeTests",
    "LeanSwe/MiniB/Proofs", "LeanSwe"
  ]
  for m in order do
    compileLeanMod root leanPath (root / s!"{m}.lean") (libDir / s!"{m}.olean")

  let okOut ← runCmd bin.toString #[libDir.toString, "LeanSwe", "", ""]
  let okComb := okOut.stdout ++ "\n" ++ okOut.stderr
  if okOut.exitCode != 0 || (okComb.splitOn "errors=0").length <= 1 then
    throw (IO.userError s!"FAIL [dag_baseline_clean]: expected exit 0 errors=0:\n{okComb}")
  IO.println s!"PASS [dag_baseline_clean] -> {okOut.stdout.trimAscii.toString}"

  let ipcOut ← runCmd bin.toString #["--ipc-roundtrip"]
  if ipcOut.exitCode != 0 || (ipcOut.stdout.splitOn "PASS_IPC_ROUNDTRIP").length <= 1 then
    throw (IO.userError s!"FAIL [dag_worker_ipc_roundtrip]:\n{ipcOut.stdout}\n{ipcOut.stderr}")
  IO.println "PASS [dag_worker_ipc_roundtrip] -> encodeDagReportWireLines + decodeDagReportWireLines + mergeDagReports verified"

  let ctorOut ← runCmd bin.toString #["--ctoridx-check", libDir.toString]
  if ctorOut.exitCode != 0 || (ctorOut.stdout.splitOn "PASS_CTORIDX_CHECK").length <= 1 || !ctorOut.stderr.isEmpty then
    throw (IO.userError s!"FAIL [ctoridx_edge_cases]:\n{ctorOut.stdout}\n{ctorOut.stderr}")
  IO.println "PASS [ctoridx_edge_cases] -> isCompilerGeneratedCtorIdx + isAllowedCompilerUnsafeDef verified"

  let staleOut ← runCmd bin.toString #[libDir.toString, "LeanSwe", "WITHIN|LeanSwe.MiniA.Model|LeanSwe.MiniA.Impl", ""]
  expectOutputContains "dag_stale_edge_allowlist" "STALE_IMPORT_DAG_ALLOWLIST" staleOut

  let staleSigZero ← runCmd bin.toString #[libDir.toString, "LeanSwe", "", "LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs.ghost=1"]
  expectOutputContains "dag_stale_sig_allowlist_missing" "STALE_SIG_PROOF_ALLOWLIST" staleSigZero

  let runDagMut (name expectedCode : String)
      (mutate : System.FilePath → IO (Array String))
      (edgeAllow sigAllow : String := "")
      (roots : String := "LeanSwe")
      (forbiddenCodes : Array String := #[]) : IO Unit := do
    let d := tmpRoot / s!"dag_{name}"
    let rc := d / "repo"
    let lc := d / "lib"
    IO.FS.createDirAll d
    copyDirTree root rc
    copyDirTree libDir lc
    let lp := s!"{lc}:{realLibAbs}"
    let mods ← mutate rc
    for m in mods do
      compileLeanMod rc lp (rc / s!"{m}.lean") (lc / s!"{m}.olean")
    let out ← runCmd bin.toString #[lc.toString, roots, edgeAllow, sigAllow]
    expectOutputContains name expectedCode out forbiddenCodes
    IO.FS.removeDirAll d

  runDagMut "within_model_imports_impl" "WITHIN|LeanSwe.MiniA.Model|LeanSwe.MiniA.Impl" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Model.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA.Model\ndef step (t : Tag) : Nat := Internal.stepImpl t\nend LeanSwe.MiniA.Model\n"
    return #["LeanSwe/MiniA/Model", "LeanSwe/MiniA/SpecTests", "LeanSwe/MiniA/Proofs", "LeanSwe/MiniB/Model", "LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "within_model_imports_other_helper"
      "DAG_WITHIN_VIOLATION: LeanSwe.MiniA.Model (Model) transitively imports same-package LeanSwe.MiniA.Helper (Other)"
      (roots := "LeanSwe.MiniA.Model") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "namespace LeanSwe.MiniA.Helper\ndef offset : Nat := 1\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Model.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Model\ndef step (t : Tag) : Nat := match t with | .a => Helper.offset | .b => 2\nend LeanSwe.MiniA.Model\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Model"]

  runDagMut "within_spectests_transitive_impl" "WITHIN|LeanSwe.MiniA.SpecTests|LeanSwe.MiniA.Impl" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Model.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA.Model\ndef step (t : Tag) : Nat := Internal.stepImpl t\nend LeanSwe.MiniA.Model\n"
    return #["LeanSwe/MiniA/Model", "LeanSwe/MiniA/SpecTests", "LeanSwe/MiniA/Proofs", "LeanSwe/MiniB/Model", "LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "within_impl_imports_spec" "WITHIN|LeanSwe.MiniA.Impl|LeanSwe.MiniA.SpecTests" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Impl.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Internal\ndef stepImpl (t : Tag) : Nat := match t with | .a => 1 | .b => 2\nend LeanSwe.MiniA.Internal\n"
    return #["LeanSwe/MiniA/Impl", "LeanSwe/MiniA/Interface", "LeanSwe/MiniA/Proofs", "LeanSwe/MiniB/SysBridge", "LeanSwe/MiniB/Impl", "LeanSwe/MiniB/Interface", "LeanSwe/MiniB/RuntimeTests", "LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "within_sysbridge_imports_runtimetests" "WITHIN|LeanSwe.MiniB.SysBridge|LeanSwe.MiniB.RuntimeTests"
      (roots := "LeanSwe.MiniB.SysBridge") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniB/RuntimeTests.lean")
      "namespace LeanSwe.MiniB.RuntimeTests\ndef tagVal : Nat := 1\nend LeanSwe.MiniB.RuntimeTests\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniB/SysBridge.lean")
      "import LeanSwe.MiniA.Interface\nimport LeanSwe.MiniB.Types\nimport LeanSwe.MiniB.RuntimeTests\nnamespace LeanSwe.MiniB.SysBridge\ndef runB (t : BTag) : Nat := LeanSwe.MiniA.step t + RuntimeTests.tagVal\nend LeanSwe.MiniB.SysBridge\n"
    return #["LeanSwe/MiniB/RuntimeTests", "LeanSwe/MiniB/SysBridge"]

  runDagMut "cross_direct_impl_import" "CROSS|LeanSwe.MiniB.Impl|LeanSwe.MiniA.Impl" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniB/Impl.lean")
      "import LeanSwe.MiniB.SysBridge\nimport LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniB.Internal\ndef implB (t : BTag) : Nat := SysBridge.runB t\nend LeanSwe.MiniB.Internal\n"
    return #["LeanSwe/MiniB/Impl", "LeanSwe/MiniB/Interface", "LeanSwe/MiniB/RuntimeTests", "LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "cross_direct_proofs_import" "CROSS|LeanSwe.MiniB.Proofs|LeanSwe.MiniA.Proofs" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniB/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Proofs\nimport LeanSwe.MiniB.Model\nimport LeanSwe.MiniB.Interface\nnamespace LeanSwe.MiniB.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniB.callB LeanSwe.MiniB.Model.evalB := fun t => by cases t <;> rfl\nend LeanSwe.MiniB.Proofs\n"
    return #["LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "cross_indirect_reachin_through_interface" "CROSS_REF|LeanSwe.MiniB.SysBridge|LeanSwe.MiniA.Impl" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniB/SysBridge.lean")
      "import LeanSwe.MiniA.Interface\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.SysBridge\ndef runB (t : BTag) : Nat := LeanSwe.MiniA.Internal.stepImpl t\nend LeanSwe.MiniB.SysBridge\n"
    return #["LeanSwe/MiniB/SysBridge", "LeanSwe/MiniB/Impl", "LeanSwe/MiniB/Interface", "LeanSwe/MiniB/RuntimeTests", "LeanSwe/MiniB/Proofs", "LeanSwe"]

  runDagMut "cross_internal_reachin_in_interface" "DAG_CROSS_INTERNAL_REACHIN"
      (roots := "LeanSwe.MiniB.SysBridge")
      (forbiddenCodes := #["DAG_CROSS_IMPORT_VIOLATION", "DAG_CROSS_REACHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Interface.lean")
      "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef step (t : Tag) : Nat := Internal.stepImpl t\nnamespace Internal\ndef leakedHelper (t : Tag) : Nat := stepImpl t\nend Internal\nend LeanSwe.MiniA\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniB/SysBridge.lean")
      "import LeanSwe.MiniA.Interface\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.SysBridge\ndef runB (t : BTag) : Nat := LeanSwe.MiniA.Internal.leakedHelper t\nend LeanSwe.MiniB.SysBridge\n"
    return #["LeanSwe/MiniA/Interface", "LeanSwe/MiniB/SysBridge"]

  runDagMut "duplicate_dag_allowlist_entry" "DUPLICATE_DAG_ALLOWLIST_ENTRY"
      (edgeAllow := "WITHIN|LeanSwe.MiniA.Model|LeanSwe.MiniA.Impl;WITHIN|LeanSwe.MiniA.Model|LeanSwe.MiniA.Impl")
      (roots := "LeanSwe.MiniA.Model")
      (forbiddenCodes := #["STALE_IMPORT_DAG_ALLOWLIST", "DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Model.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA.Model\ndef step (t : Tag) : Nat := Internal.stepImpl t\nend LeanSwe.MiniA.Model\n"
    return #["LeanSwe/MiniA/Model"]

  runDagMut "proofs_namespace_model_public" "PROOF_MODEL_NS_FORBIDDEN" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Model\ndef disguisedModel (n : Nat) : Nat := n\nend LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a LeanSwe.MiniA.step) := fun t => ⟨by cases t <;> rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "proofs_namespace_model_private" "PROOF_MODEL_NS_FORBIDDEN" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Model\nprivate def hiddenModel (n : Nat) : Nat := n\nend LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a LeanSwe.MiniA.step) := fun t => ⟨by cases t <;> rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "properties_uses_proofs_const" "PROOF_CONST_IN_SPEC" (roots := "LeanSwe.MiniA.Properties") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Properties.lean")
      "import LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniA\ndef prop_bad : Prop := LeanSwe.MiniA.Proofs.step_cases .a = LeanSwe.MiniA.Proofs.step_cases .a\nend LeanSwe.MiniA\n"
    return #["LeanSwe/MiniA/Properties"]

  runDagMut "spectests_body_uses_proofs_const" "PROOF_CONST_IN_SPEC" (roots := "LeanSwe.MiniA.SpecTests") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Proofs\ndef proofHelperVal : Nat := 7\nend LeanSwe.MiniA.Proofs\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/SpecTests.lean")
      "import Core.NondetTest\nimport LeanSwe.MiniA.Model\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniA\nopen Core Core.NondetTest\ndef test_bad_body {r} [NondetTest r] : r Unit := do\n  NondetTest.assert (Proofs.proofHelperVal = 7)\nend LeanSwe.MiniA\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe/MiniA/SpecTests"]

  runDagMut "within_impl_imports_proofs" "WITHIN|LeanSwe.MiniA.Impl|LeanSwe.MiniA.Proofs" (roots := "LeanSwe.MiniA.Impl") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Proofs\ndef pfConst : Nat := 1\nend LeanSwe.MiniA.Proofs\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Impl.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniA.Internal\ndef stepImpl (_ : Tag) : Nat := Proofs.pfConst\nend LeanSwe.MiniA.Internal\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe/MiniA/Impl"]

  runDagMut "cross_trans_model_imports_proofs" "DAG_TRANS_LEAK" (roots := "LeanSwe.MiniB.Model") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniB/Model.lean")
      "import LeanSwe.MiniA.Model\nimport LeanSwe.MiniA.Proofs\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.Model\ndef evalB (t : BTag) : Nat := LeanSwe.MiniA.Model.step t\nend LeanSwe.MiniB.Model\n"
    return #["LeanSwe/MiniB/Model"]

  runDagMut "refines_model_uses_proofs_const" "PROOF_CONST_IN_SIGNATURE" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef proofHelper (t : Tag) : Nat := Model.step t\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniA.step proofHelper := fun t => by cases t <;> rfl\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "obeys_model_uses_proofs_const" "PROOF_CONST_IN_SIGNATURE" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef proofPred (t : Tag) : Prop := Model.step t > 0\ntheorem obeys_model (t : Tag) : proofPred t := by cases t <;> simp [proofPred, Model.step]\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "allpass_sig_uses_proofs_const" "PROOF_CONST_IN_SIGNATURE" fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef fakeStep (t : Tag) : Nat := Model.step t\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "allpass_sig_count_grew" "PROOF_CONST_IN_SIGNATURE_GREW"
      (sigAllow := "LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs.fakeStep=1") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef fakeStep (t : Tag) : Nat := Model.step t\ntheorem proof_a1 : Core.AllPass (LeanSwe.MiniA.test_a fakeStep) := fun _ => ⟨rfl, trivial⟩\ntheorem proof_a2 : Core.AllPass (LeanSwe.MiniA.test_a fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "allpass_sig_count_stale" "STALE_SIG_PROOF_ALLOWLIST"
      (sigAllow := "LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs.fakeStep=2") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef fakeStep (t : Tag) : Nat := Model.step t\ntheorem proof_a1 : Core.AllPass (LeanSwe.MiniA.test_a fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "duplicate_sig_proof_allowlist_entry" "DUPLICATE_SIG_PROOF_ALLOWLIST_ENTRY"
      (sigAllow := "LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs.fakeStep=1;LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Proofs.fakeStep=1")
      (forbiddenCodes := #["STALE_SIG_PROOF_ALLOWLIST", "PROOF_CONST_IN_SIGNATURE"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef fakeStep (t : Tag) : Nat := Model.step t\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Proofs", "LeanSwe"]

  IO.FS.removeDirAll baseDir

/-- Execute self-tests for `Core.Refines`, boundary retirement, harness parity, and import-DAG gates. -/
def main (_ : List String) : IO UInt32 := do
  let realRepo ← IO.FS.realPath "."
  let realLib := realRepo / ".lake" / "build" / "lib" / "lean"
  unless ← (realLib / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_BUILD: run lake build first ({realLib / "LeanSwe.olean"})"
    return 1

  let mkOut ← runCmd "mktemp" #["-d", "/tmp/leanswe-assump-selftest.XXXXXX"]
  if mkOut.exitCode != 0 then
    IO.eprintln s!"mktemp failed: {mkOut.stderr}"
    return 1
  let tmpRoot : System.FilePath := mkOut.stdout.trimAscii.toString

  try
    let bin ← buildCheckAssumptionsBin tmpRoot
    let baseDir := tmpRoot / "baseline"
    IO.FS.createDirAll baseDir
    let base ← setupBaselineMiniRepo baseDir realRepo realLib

    let baseOut ← runCmd bin.toString #[base.libDir.toString, base.root.toString, "--allow-legacy"]
    if baseOut.exitCode != 0 then
      throw (IO.userError s!"Miniature baseline failed unexpectedly:\n{baseOut.stdout}\n{baseOut.stderr}")
    IO.println s!"PASS [baseline_clean] -> {baseOut.stdout.trimAscii.toString}"

    runPositiveCase base tmpRoot bin "polymorphic_and_step_from_refines_ok" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "class MiniTag (α : Type) where\n" ++
         "  tag : α → Nat\n" ++
         "instance : MiniTag String where\n" ++
         "  tag s := s.length\n" ++
         "structure RawBoxOpsM (m : Type → Type) where\n" ++
         "  readBox : m Nat\n" ++
         "structure BoxApiM (m : Type → Type) where\n" ++
         "  getPlusOne : m Nat\n" ++
         "  pureTwice : Nat → Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def tagModel {α : Type} [MiniTag α] (x : α) : Nat := MiniTag.tag x\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : RawBoxOpsM (StateM W)) (_ : Unit) : StateM W Nat := raw.readBox\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : BoxApiM (StateM W)) (_ : Unit) : StateM W Nat := api.getPlusOne\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s + 1 ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def tagImpl {α : Type} [MiniTag α] (x : α) : Nat := MiniTag.tag x\n" ++
         "def mkApiM {m : Type → Type} [Monad m] (raw : RawBoxOpsM m) : BoxApiM m := {\n" ++
         "  getPlusOne := do let v ← raw.readBox; return v + 1\n" ++
         "  pureTwice := fun n => n + n\n" ++
         "}\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def defaultOps : RawBoxOpsM IO := { readBox := pure 7 }\n" ++
         "def defaultApi : BoxApiM IO := Internal.mkApiM defaultOps\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def tagOf {α : Type} [MiniTag α] (x : α) : Nat := Internal.tagImpl x\n" ++
         "def getPlusOne : IO Nat := defaultApi.getPlusOne\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "private theorem step_ok : Core.RefinesStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  intro W proj raw hRaw w _ _\n" ++
         "  have h := hRaw w () rfl\n" ++
         "  dsimp only [Model.execRaw, Model.rawAllowed, Model.execPkg, Model.pkgAllowed, Internal.mkApiM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp, id] at h ⊢\n" ++
         "  cases hr : raw.readBox w with\n" ++
         "  | mk v w1 =>\n" ++
         "    simp only [hr] at h ⊢\n" ++
         "    exact ⟨congrArg (· + 1) h.1, h.2⟩\n" ++
         "theorem refines_model :\n" ++
         "    Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    (∀ {α : Type} [MiniTag α], Core.RefinesPureEq (@LeanSwe.MiniPure.tagOf α _) (@Model.tagModel α _)) ∧\n" ++
         "    Core.RefinesStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, fun _ => rfl, step_ok⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "missing_refines_model" "MISSING_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "private_refines_model" "MISSING_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\nprivate theorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "lambda_impl_in_refines" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq (fun x => LeanSwe.MiniPure.eval x) LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "diagonal_lambda_in_refines" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef addModel (a b : Nat) : Nat := a + b\ndef diagModel (p : Nat × Nat) : Nat := p.1 + p.1\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef addImpl (a b : Nat) : Nat := if a == b then a + b else 0\nend LeanSwe.MiniPure.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (a b : Nat) : Nat := Internal.addImpl a b\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        "import Core.NondetTest\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure\nopen Core Core.NondetTest\ndef test_minipure_diag {r} [NondetTest r] : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (eval x x = Model.addModel x x)\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq (fun p : Nat × Nat => LeanSwe.MiniPure.eval p.1 p.1) LeanSwe.MiniPure.Model.diagModel := fun p => by simp [LeanSwe.MiniPure.eval, LeanSwe.MiniPure.Internal.addImpl, LeanSwe.MiniPure.Model.diagModel]\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "lambda_allowed_in_refines" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval (fun x y => y = LeanSwe.MiniPure.Model.evalModel x) := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "partial_app_in_refines" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef addZeroModel (n : Nat) : Nat := n\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\ndef addK (k n : Nat) : Nat := if k == 0 then n else 999999\nend LeanSwe.MiniPure.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef addK (k n : Nat) : Nat := Internal.addK k n\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ Core.RefinesPureEq (LeanSwe.MiniPure.addK 0) LeanSwe.MiniPure.Model.addZeroModel := ⟨fun _ => rfl, fun _ => rfl⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "concrete_specialization_in_refines" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef idModel {α : Type} (x : α) : α := x\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef idPoly {α : Type} (x : α) : α := x\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ Core.RefinesPureEq (@LeanSwe.MiniPure.idPoly Nat) (@LeanSwe.MiniPure.Model.idModel Nat) := ⟨fun _ => rfl, fun _ => rfl⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "non_interface_impl_in_refines" "NON_INTERFACE_IMPL_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.Internal.evalImpl LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "omitted_pure_interface_op_in_refines" "INCOMPLETE_INTERFACE_REFINEMENT" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef unverifiedOp (n : Nat) : Nat := n + 42\nend LeanSwe.MiniPure\n"
      return #["LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "omitted_effectful_interface_op_in_refines" "INCOMPLETE_INTERFACE_REFINEMENT" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        "namespace LeanSwe.MiniPure\nstructure RawBoxOpsM (m : Type → Type) where\n  readBox : m Nat\nstructure BoxApiM (m : Type → Type) where\n  opCovered : m Nat\n  opSkipped : m Nat\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef rawWf (_ : Nat) : Bool := true\ndef execRaw {W : Type} (raw : RawBoxOpsM (StateM W)) (_ : Unit) : StateM W Nat := raw.readBox\ndef rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\ndef execPkg {W : Type} (api : BoxApiM (StateM W)) (_ : Unit) : StateM W Nat := api.opCovered\ndef pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\ndef mkApiM {m : Type → Type} [Monad m] (raw : RawBoxOpsM m) : BoxApiM m := { opCovered := raw.readBox, opSkipped := pure 999 }\nend LeanSwe.MiniPure.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef defaultOps : RawBoxOpsM IO := { readBox := pure 0 }\ndef defaultApi : BoxApiM IO := Internal.mkApiM defaultOps\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef opCovered : IO Nat := defaultApi.opCovered\ndef opSkipped : IO Nat := defaultApi.opSkipped\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ Core.RefinesStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := ⟨fun _ => rfl, fun _ _ h w req hwf => h w req hwf⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "proofs_local_spec_in_refines" "NON_MODEL_SPEC_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ndef localEvalSpec (n : Nat) : Nat := n + 1\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval localEvalSpec := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "model_references_impl_in_refines" "MODEL_REFERENCES_IMPL_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := LeanSwe.MiniPure.Internal.evalImpl n\nend LeanSwe.MiniPure.Model\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "output_insensitive_allowed_in_refines" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef allowedIgnoreOut (n _ : Nat) : Prop := n = n\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.allowedIgnoreOut := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "tautological_refl_allowed_in_refines" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef allowedSelfEq (_ y : Nat) : Prop := y = y\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.allowedSelfEq := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "single_point_refl_else_allowed_in_refines" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniFloat/Model.lean")
        "import Init.Data.Float.Model\nimport LeanSwe.MiniFloat.Types\nnamespace LeanSwe.MiniFloat.Model\ndef isZeroMask (u : UInt64) : Bool := u == 0\ndef modelBits (u : UInt64) : UInt64 := if u == 0 then 0 else let b := (Float.Model.ofBits u).toBits; if b == 0 then 1 else b\ndef allowedGetBits (u out : UInt64) : Prop := (u = 0 → out = 0) ∧ (u ≠ 0 → out = out)\nend LeanSwe.MiniFloat.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniFloat/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniFloat.SpecTests\nnamespace LeanSwe.MiniFloat.Proofs\ntheorem proof_minifloat : Core.AllPass (LeanSwe.MiniFloat.test_minifloat_zero LeanSwe.MiniFloat.getBits) := fun _ => ⟨rfl, trivial⟩\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniFloat.getBits LeanSwe.MiniFloat.Model.allowedGetBits := fun u => ⟨fun h => by subst h; rfl, fun _ => rfl⟩\nend LeanSwe.MiniFloat.Proofs\n"
      return #["LeanSwe/MiniFloat/Model", "LeanSwe/MiniFloat/SpecTests", "LeanSwe/MiniFloat/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "single_point_implication_allowed_in_refines" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef allowedZeroOnly (n y : Nat) : Prop := n = 0 → y = 1\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.allowedZeroOnly := fun n h => by subst h; rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "two_point_incomplete_guards_allowed_in_refines" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef allowedTwoPoints (n y : Nat) : Prop := (n = 0 → y = 1) ∧ (n = 1 → y = 2)\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.allowedTwoPoints := fun n => ⟨fun h => by subst h; rfl, fun h => by subst h; rfl⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "unit_codomain_refines_pure_eq" "TRIVIAL_CODOMAIN_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef unitModel (_ : Nat) : Unit := ()\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef unitOp (_ : Nat) : Unit := ()\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ Core.RefinesPureEq LeanSwe.MiniPure.unitOp LeanSwe.MiniPure.Model.unitModel := ⟨fun _ => rfl, fun _ => rfl⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "vacuous_wf_in_refines_step" "VACUOUS_WF_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef badWf (_ : Nat) : Bool := false\ndef stepAllowed (s _ out s' : Nat) : Prop := out = s + 999 ∧ s' = s\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef stepOp (req : Nat) : StateM Nat Nat := fun s => (req, s)\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ Core.RefinesStepId LeanSwe.MiniPure.Model.badWf LeanSwe.MiniPure.stepOp LeanSwe.MiniPure.Model.stepAllowed := ⟨fun _ => rfl, fun _ _ h => nomatch h⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "conditional_prop_hyp_in_refines_model" "CONDITIONAL_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 99\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model (h : 0 = 1) : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := nomatch h\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "uninhabited_binder_in_refines_model" "UNINHABITED_BINDER_IN_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 99\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model (f : Nat → Empty) : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := Empty.elim (f 0)\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "impossible_typeclass_in_refines_model" "NON_INHABITED_TYPECLASS_IN_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        "namespace LeanSwe.MiniPure\nclass ImpossibleTag (α : Type) where\n  contra : α → Empty\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef polyModel {α : Type} [ImpossibleTag α] (_ : α) : Nat := 999\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef polyOp {α : Type} [ImpossibleTag α] (_ : α) : Nat := 0\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ (∀ {α : Type} [inst : ImpossibleTag α], Core.RefinesPureEq (@LeanSwe.MiniPure.polyOp α inst) (@LeanSwe.MiniPure.Model.polyModel α inst)) := ⟨fun _ => rfl, fun {α} [inst : ImpossibleTag α] x => Empty.elim (inst.contra x)⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "uninhabited_domain_in_refines" "UNINHABITED_DOMAIN_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef emptyModel (_ : Empty) : Nat := 99\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef emptyOp (_ : Empty) : Nat := 0\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧ Core.RefinesPureEq LeanSwe.MiniPure.emptyOp LeanSwe.MiniPure.Model.emptyModel := ⟨fun _ => rfl, fun e => Empty.elim e⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "empty_or_stub_model" "EMPTY_OR_STUB_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalRel (n out : Nat) : Prop := out = n + 1\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        "import Core.NondetTest\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure\nopen Core Core.NondetTest\ndef test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (fn x = x + 1)\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\ntheorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalRel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runPositiveCase base tmpRoot bin "retired_pure_pkg_without_model_ok" fun mr => do
      IO.FS.removeFile (mr.root / "LeanSwe/MiniPure/Model.lean")
      IO.FS.removeFile (mr.libDir / "LeanSwe/MiniPure/Model.olean")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls.replace "import LeanSwe.MiniPure.Model\n" "")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        "import Core.NondetTest\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure\nopen Core Core.NondetTest\ndef test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (fn x = x + 1)\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "pure_pkg_with_model_in_fuzz_suites_still_requires_refines" "MISSING_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"minipure\": { \"paths\": [\"harness/Fuzz/MiniPure/\", \"LeanSwe/MiniPure/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniPure.Proofs\n"
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runPositiveCase base tmpRoot bin "external_cli_boundary_with_model_ok" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"minicli\": { \"paths\": [\"harness/Fuzz/MiniCli/\", \"LeanSwe/MiniCli/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/Process/SysBridge.lean")
        "namespace LeanSwe.Process.SysBridge\ndef runTool (cmd : String) : IO UInt32 := do let _ := cmd; return 0\nend LeanSwe.Process.SysBridge\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/Types.lean")
        "namespace LeanSwe.MiniCli\ninductive CliErr\n  | toolFailed\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniCli\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/Model.lean")
        "import LeanSwe.MiniCli.Types\nnamespace LeanSwe.MiniCli.Model\ndef exitOk (code : UInt32) : Bool := code == 0\nend LeanSwe.MiniCli.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/Impl.lean")
        "import LeanSwe.Process.SysBridge\nimport LeanSwe.MiniCli.Types\nnamespace LeanSwe.MiniCli.Internal\ndef invokeImpl (arg : String) : IO (Except CliErr UInt32) := do\n  let rc ← LeanSwe.Process.SysBridge.runTool arg\n  if rc == 0 then return .ok 0 else return .error .toolFailed\nend LeanSwe.MiniCli.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/Interface.lean")
        "import LeanSwe.MiniCli.Impl\nnamespace LeanSwe.MiniCli\ndef invoke (arg : String) : IO (Except CliErr UInt32) := Internal.invokeImpl arg\nend LeanSwe.MiniCli\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.MiniCli.Model\n" ++
         "import LeanSwe.MiniCli.Interface\n" ++
         "namespace LeanSwe.MiniCli\n" ++
         "open Core Core.NondetTest\n" ++
         "def test_minicli_model {r} [NondetTest r] : r Unit := do\n" ++
         "  let c ← nondet UInt32\n" ++
         "  NondetTest.assert (Model.exitOk c = (c == 0))\n" ++
         "def errorCoverage : List (ErrorObligation CliErr) := [\n" ++
         "  { request := \"LeanSwe.MiniCli.invoke\", errorKind := .toolFailed, justification := .tested \"LeanSwe.MiniCli.RuntimeTests.err_fail\" .real }\n" ++
         "]\n" ++
         "end LeanSwe.MiniCli\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniCli/Proofs.lean")
        "import LeanSwe.MiniCli.SpecTests\nnamespace LeanSwe.MiniCli.Proofs\ntheorem proof_minicli : Core.AllPass LeanSwe.MiniCli.test_minicli_model := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniCli.Proofs\n"
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++
         "import LeanSwe.Process.SysBridge\n" ++
         "import LeanSwe.MiniCli.Types\n" ++
         "import LeanSwe.MiniCli.Model\n" ++
         "import LeanSwe.MiniCli.Impl\n" ++
         "import LeanSwe.MiniCli.Interface\n" ++
         "import LeanSwe.MiniCli.SpecTests\n" ++
         "import LeanSwe.MiniCli.Proofs\n")
      return #[
        "LeanSwe/Process/SysBridge",
        "LeanSwe/MiniCli/Types",
        "LeanSwe/MiniCli/Model",
        "LeanSwe/MiniCli/Impl",
        "LeanSwe/MiniCli/Interface",
        "LeanSwe/MiniCli/SpecTests",
        "LeanSwe/MiniCli/Proofs",
        "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "retired_impure_float_without_model_forbidden" "MISSING_MODEL_MODULE" fun mr => do
      IO.FS.removeFile (mr.root / "LeanSwe/MiniFloat/Model.lean")
      IO.FS.removeFile (mr.libDir / "LeanSwe/MiniFloat/Model.olean")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls.replace "import LeanSwe.MiniFloat.Model\n" "")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniFloat/SpecTests.lean")
        "import Core.NondetTest\nimport LeanSwe.MiniFloat.Interface\nnamespace LeanSwe.MiniFloat\nopen Core Core.NondetTest\ndef test_minifloat_zero {r} [NondetTest r] (fn : UInt64 → UInt64) : r Unit := do\n  let _ ← nondet UInt64\n  NondetTest.assert ((fn 0 == 0) = true)\nend LeanSwe.MiniFloat\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniFloat/Proofs.lean")
        "import LeanSwe.MiniFloat.SpecTests\nnamespace LeanSwe.MiniFloat.Proofs\ntheorem proof_minifloat : Core.AllPass (LeanSwe.MiniFloat.test_minifloat_zero LeanSwe.MiniFloat.getBits) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniFloat.Proofs\n"
      return #["LeanSwe/MiniFloat/SpecTests", "LeanSwe/MiniFloat/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "retired_impure_extern_without_model_forbidden" "MISSING_MODEL_MODULE" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"minisub\": { \"paths\": [\"harness/Fuzz/MiniSub/\", \"LeanSwe/LinuxSyscall/MiniSub/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Types.lean")
        "namespace LeanSwe.LinuxSyscall.MiniSub\ninductive MiniSubErr\n  | sysFail\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Impl.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Types\nnamespace LeanSwe.LinuxSyscall.MiniSub.Internal\n@[extern \"lean_minisub_ping\"]\nopaque rawPing : UInt32 → IO (Except MiniSubErr UInt32)\nend LeanSwe.LinuxSyscall.MiniSub.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Interface.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Impl\nnamespace LeanSwe.LinuxSyscall.MiniSub\ndef ping (x : UInt32) : IO (Except MiniSubErr UInt32) := Internal.rawPing x\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Interface\n" ++
         "namespace LeanSwe.LinuxSyscall.MiniSub\n" ++
         "open Core Core.NondetTest\n" ++
         "def test_minisub_tag {r} [NondetTest r] (fn : UInt32 → UInt32) : r Unit := do\n" ++
         "  let x ← nondet UInt32\n" ++
         "  NondetTest.assert (fn x = x + 1)\n" ++
         "def errorCoverage : List (ErrorObligation MiniSubErr) := [\n" ++
         "  { request := \"LeanSwe.LinuxSyscall.MiniSub.ping\", errorKind := .sysFail, justification := .tested \"LeanSwe.LinuxSyscall.MiniSub.RuntimeTests.err_sys\" .real }\n" ++
         "]\n" ++
         "end LeanSwe.LinuxSyscall.MiniSub\n")
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Proofs.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\nnamespace LeanSwe.LinuxSyscall.MiniSub.Proofs\ntheorem proof_minisub : Core.AllPass (LeanSwe.LinuxSyscall.MiniSub.test_minisub_tag (· + 1)) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.LinuxSyscall.MiniSub.Proofs\n"
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++
         "import LeanSwe.LinuxSyscall.MiniSub.Types\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Impl\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Interface\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Proofs\n")
      return #[
        "LeanSwe/LinuxSyscall/MiniSub/Types",
        "LeanSwe/LinuxSyscall/MiniSub/Impl",
        "LeanSwe/LinuxSyscall/MiniSub/Interface",
        "LeanSwe/LinuxSyscall/MiniSub/SpecTests",
        "LeanSwe/LinuxSyscall/MiniSub/Proofs",
        "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "retired_boundary_without_fuzz_suite" "MISSING_FUZZ_SUITE" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        "{\n  \"version\": 1,\n  \"common_paths\": [\"Core/\"],\n  \"suites\": {\n    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] }\n  }\n}\n"
      return #[]

    runMutantCase base tmpRoot bin "trigger_only_path_in_other_fuzz_suite" "MISSING_FUZZ_SUITE" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"cmdline\": { \"paths\": [\"harness/Fuzz/CmdLine/\", \"LeanSwe/CmdLine/\", \"LeanSwe/MiniFloat/\"] }\n" ++
         "  }\n" ++
         "}\n")
      return #[]

    runMutantCase base tmpRoot bin "model_step_in_refines_step_forbidden" "NON_INTERFACE_IMPL_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def wf (_ : Nat) : Bool := true\n" ++
         "def stepModel (req : Nat) : StateM Nat Nat := fun s => (req + s, s)\n" ++
         "def stepAllowed (s req out s' : Nat) : Prop := out = req + s ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def stepOp (_ : Nat) : StateM Nat Nat := fun s => (0, s)\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ Core.RefinesStepId Model.wf Model.stepModel Model.stepAllowed := ⟨fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runPositiveCase base tmpRoot bin "retired_subpkg_fuzz_suite_ok" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"minisub\": { \"paths\": [\"harness/Fuzz/MiniSub/\", \"LeanSwe/LinuxSyscall/MiniSub/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Types.lean")
        "namespace LeanSwe.LinuxSyscall.MiniSub\ninductive MiniSubErr\n  | sysFail\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Model.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Types\nnamespace LeanSwe.LinuxSyscall.MiniSub.Model\ndef pingModel (x : UInt32) : UInt32 := x + 1\nend LeanSwe.LinuxSyscall.MiniSub.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Impl.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Types\nnamespace LeanSwe.LinuxSyscall.MiniSub.Internal\n@[extern \"lean_minisub_ping\"]\nopaque rawPing : UInt32 → IO (Except MiniSubErr UInt32)\nend LeanSwe.LinuxSyscall.MiniSub.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Interface.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Impl\nnamespace LeanSwe.LinuxSyscall.MiniSub\ndef ping (x : UInt32) : IO (Except MiniSubErr UInt32) := Internal.rawPing x\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Model\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Interface\n" ++
         "namespace LeanSwe.LinuxSyscall.MiniSub\n" ++
         "open Core Core.NondetTest\n" ++
         "def test_minisub_model {r} [NondetTest r] : r Unit := do\n" ++
         "  let x ← nondet UInt32\n" ++
         "  NondetTest.assert (Model.pingModel x = x + 1)\n" ++
         "def errorCoverage : List (ErrorObligation MiniSubErr) := [\n" ++
         "  { request := \"LeanSwe.LinuxSyscall.MiniSub.ping\", errorKind := .sysFail, justification := .tested \"LeanSwe.LinuxSyscall.MiniSub.RuntimeTests.err_sys\" .real }\n" ++
         "]\n" ++
         "end LeanSwe.LinuxSyscall.MiniSub\n")
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Proofs.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\nnamespace LeanSwe.LinuxSyscall.MiniSub.Proofs\ntheorem proof_minisub : Core.AllPass LeanSwe.LinuxSyscall.MiniSub.test_minisub_model := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.LinuxSyscall.MiniSub.Proofs\n"
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++
         "import LeanSwe.LinuxSyscall.MiniSub.Types\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Model\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Impl\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Interface\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Proofs\n")
      return #[
        "LeanSwe/LinuxSyscall/MiniSub/Types",
        "LeanSwe/LinuxSyscall/MiniSub/Model",
        "LeanSwe/LinuxSyscall/MiniSub/Impl",
        "LeanSwe/LinuxSyscall/MiniSub/Interface",
        "LeanSwe/LinuxSyscall/MiniSub/SpecTests",
        "LeanSwe/LinuxSyscall/MiniSub/Proofs",
        "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "retired_boundary_missing_error_coverage" "MISSING_ERROR_COVERAGE" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"minisub\": { \"paths\": [\"harness/Fuzz/MiniSub/\", \"LeanSwe/LinuxSyscall/MiniSub/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Types.lean")
        "namespace LeanSwe.LinuxSyscall.MiniSub\nstructure PingTag where\n  raw : UInt32\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Model.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Types\nnamespace LeanSwe.LinuxSyscall.MiniSub.Model\ndef pingModel (x : UInt32) : UInt32 := x + 1\nend LeanSwe.LinuxSyscall.MiniSub.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Impl.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Types\nnamespace LeanSwe.LinuxSyscall.MiniSub.Internal\n@[extern \"lean_minisub_ping_u32\"]\nopaque rawPing : UInt32 → IO UInt32\nend LeanSwe.LinuxSyscall.MiniSub.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Interface.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.Impl\nnamespace LeanSwe.LinuxSyscall.MiniSub\ndef ping (x : UInt32) : IO UInt32 := Internal.rawPing x\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/SpecTests.lean")
        "import Core.NondetTest\nimport LeanSwe.LinuxSyscall.MiniSub.Model\nimport LeanSwe.LinuxSyscall.MiniSub.Interface\nnamespace LeanSwe.LinuxSyscall.MiniSub\nopen Core Core.NondetTest\ndef test_minisub_model {r} [NondetTest r] : r Unit := do\n  let x ← nondet UInt32\n  NondetTest.assert (Model.pingModel x = x + 1)\nend LeanSwe.LinuxSyscall.MiniSub\n"
      writeFileCreatingParents (mr.root / "LeanSwe/LinuxSyscall/MiniSub/Proofs.lean")
        "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\nnamespace LeanSwe.LinuxSyscall.MiniSub.Proofs\ntheorem proof_minisub : Core.AllPass LeanSwe.LinuxSyscall.MiniSub.test_minisub_model := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.LinuxSyscall.MiniSub.Proofs\n"
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++
         "import LeanSwe.LinuxSyscall.MiniSub.Types\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Model\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Impl\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Interface\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.SpecTests\n" ++
         "import LeanSwe.LinuxSyscall.MiniSub.Proofs\n")
      return #[
        "LeanSwe/LinuxSyscall/MiniSub/Types",
        "LeanSwe/LinuxSyscall/MiniSub/Model",
        "LeanSwe/LinuxSyscall/MiniSub/Impl",
        "LeanSwe/LinuxSyscall/MiniSub/Interface",
        "LeanSwe/LinuxSyscall/MiniSub/SpecTests",
        "LeanSwe/LinuxSyscall/MiniSub/Proofs",
        "LeanSwe"
      ]

    let setupFallibleRuntimeMiniPure (mr : MiniRepo) (rtBody : String) : IO (Array String) := do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        "namespace LeanSwe.MiniPure\ninductive PureErr\n  | zeroInput\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef checkPosModel (n : Nat) : Except PureErr Nat := if n == 0 then .error .zeroInput else .ok n\nend LeanSwe.MiniPure.Model\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\ndef checkPosImpl (n : Nat) : Except PureErr Nat := if n == 0 then .error .zeroInput else .ok n\nend LeanSwe.MiniPure.Internal\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\ndef checkPos (n : Nat) : Except PureErr Nat := Internal.checkPosImpl n\nend LeanSwe.MiniPure\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Model\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "open Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n" ++
         "  let x ← nondet Nat\n" ++
         "  NondetTest.assert (fn x = Model.evalModel x)\n" ++
         "def errorCoverage : List (ErrorObligation PureErr) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.checkPos\", errorKind := .zeroInput, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\" .real }\n" ++
         "]\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import Core.Refines\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ Core.RefinesPureEq LeanSwe.MiniPure.checkPos Model.checkPosModel := ⟨fun _ => rfl, fun _ => rfl⟩\nend LeanSwe.MiniPure.Proofs\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/RuntimeTests.lean") rtBody
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls ++ "import LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "harness/Tests/Main.lean")
        "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  LeanSwe.MiniPure.RuntimeTests.runAll\n  Core.closeAssumpLog\n  return 0\n"
      return #[
        "LeanSwe/MiniPure/Types",
        "LeanSwe/MiniPure/Model",
        "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface",
        "LeanSwe/MiniPure/SpecTests",
        "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/RuntimeTests",
        "LeanSwe",
        "Tests/Main"
      ]

    runPositiveCase base tmpRoot bin "runtime_test_used_let_ok" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let res := LeanSwe.MiniPure.checkPos 0\n" ++
         "  match res with\n" ++
         "  | .error .zeroInput => pure ()\n" ++
         "  | .ok _ => throw (IO.userError \"expected zeroInput\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "unretired_pure_with_model_missing_refines" "MISSING_REFINES_MODEL" fun mr => do
      let mods ← setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let res := LeanSwe.MiniPure.checkPos 0\n" ++
         "  match res with\n" ++
         "  | .error .zeroInput => pure ()\n" ++
         "  | .ok _ => throw (IO.userError \"expected zeroInput\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\ntheorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniPure.Proofs\n"
      return mods

    runMutantCase base tmpRoot bin "unused_let_pkg_ref_in_runtime_test" "MISSING_PACKAGE_REF_IN_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let t ← IO.monoNanosNow\n" ++
         "  let _ := LeanSwe.MiniPure.checkPos (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + 1)))))))))))))))))\n" ++
         "  if t == 0 then throw (IO.userError \"unexpected zero clock\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "unused_let_inside_lambda_pkg_ref_in_runtime_test" "MISSING_PACKAGE_REF_IN_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "private def withCtx (k : Nat → IO Unit) : IO Unit := do\n" ++
         "  let t ← IO.monoNanosNow\n" ++
         "  k t\n" ++
         "def test_err_zero : IO Unit := withCtx fun t => do\n" ++
         "  let _ := LeanSwe.MiniPure.checkPos (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + (t + 1)))))))))))))))))\n" ++
         "  if t == 0 then throw (IO.userError \"unexpected zero clock\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "dead_branch_in_runtime_test" "DEAD_CONDITIONAL_IN_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  if (1 : Nat) == 2 then throw (IO.userError \"dead\")\n" ++
         "  let res := LeanSwe.MiniPure.checkPos 0\n" ++
         "  match res with\n" ++
         "  | .error .zeroInput => pure ()\n" ++
         "  | .ok _ => throw (IO.userError \"expected zeroInput\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runPositiveCase base tmpRoot bin "step_from_finally_refines_ok" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure RawBoxOpsM (m : Type → Type) where\n" ++
         "  readBox : m Nat\n" ++
         "structure BoxApiM (m : Type → Type) where\n" ++
         "  withBox : {α : Type} → (Nat → m α) → m α\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : RawBoxOpsM (StateM W)) (_ : Unit) : StateM W Nat := raw.readBox\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : BoxApiM (StateM W)) (_ : Unit) : StateM W Nat := api.withBox (fun n => pure (n + 1))\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s + 1 ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (raw : RawBoxOpsM m) : BoxApiM m := {\n" ++
         "  withBox := fun k => do\n" ++
         "    let (a, _) ← tryFinally' (do let v ← raw.readBox; k v) (fun _ => pure ())\n" ++
         "    pure a\n" ++
         "}\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def defaultOps : RawBoxOpsM IO := { readBox := pure 7 }\n" ++
         "def defaultApi : BoxApiM IO := Internal.mkApiM defaultOps\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def withBox {α : Type} (k : Nat → IO α) : IO α := defaultApi.withBox k\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "private theorem step_ok : Core.RefinesStepFromFinally id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  intro W proj raw hRaw w _ _\n" ++
         "  have h := hRaw w () rfl\n" ++
         "  dsimp only [Model.execRaw, Model.rawAllowed, Model.execPkg, Model.pkgAllowed, Internal.mkApiM, tryFinally', MonadFinally.tryFinally', Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp, id] at h ⊢\n" ++
         "  cases hr : raw.readBox w with\n" ++
         "  | mk v w1 =>\n" ++
         "    simp only [hr] at h ⊢\n" ++
         "    exact ⟨congrArg (· + 1) h.1, h.2⟩\n" ++
         "theorem refines_model :\n" ++
         "    Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.RefinesStepFromFinally id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, step_ok⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "step_from_finally_trivial_allowed" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure RawBoxOpsM (m : Type → Type) where\n" ++
         "  readBox : m Nat\n" ++
         "structure BoxApiM (m : Type → Type) where\n" ++
         "  withBox : {α : Type} → (Nat → m α) → m α\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : RawBoxOpsM (StateM W)) (_ : Unit) : StateM W Nat := raw.readBox\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : BoxApiM (StateM W)) (_ : Unit) : StateM W Nat := api.withBox (fun n => pure (n + 1))\n" ++
         "def pkgAllowed (_ : Nat) (_ : Unit) (_ _ : Nat) : Prop := True\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (raw : RawBoxOpsM m) : BoxApiM m := {\n" ++
         "  withBox := fun k => do\n" ++
         "    let (a, _) ← tryFinally' (do let v ← raw.readBox; k v) (fun _ => pure ())\n" ++
         "    pure a\n" ++
         "}\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def defaultOps : RawBoxOpsM IO := { readBox := pure 7 }\n" ++
         "def defaultApi : BoxApiM IO := Internal.mkApiM defaultOps\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def withBox {α : Type} (k : Nat → IO α) : IO α := defaultApi.withBox k\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem refines_model :\n" ++
         "    Core.RefinesPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.RefinesStepFromFinally id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ _ _ _ _ => trivial⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "dead_branch_deep_closed_let_in_runtime_test" "DEAD_CONDITIONAL_IN_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let c : Nat := (((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)\n" ++
         "  if c == 999 then throw (IO.userError \"dead\")\n" ++
         "  let res := LeanSwe.MiniPure.checkPos 0\n" ++
         "  match res with\n" ++
         "  | .error .zeroInput => pure ()\n" ++
         "  | .ok _ => throw (IO.userError \"expected zeroInput\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "deep_closed_let_dead_throw_in_runtime_test" "TRIVIAL_ERROR_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let c : Nat := (((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)\n" ++
         "  let fakeThrow : IO Unit := throw (IO.userError \"dead\")\n" ++
         "  if c == 999 then fakeThrow else pure ()\n" ++
         "  let res := LeanSwe.MiniPure.checkPos 0\n" ++
         "  match res with\n" ++
         "  | .error .zeroInput => pure ()\n" ++
         "  | .ok _ => pure ()\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "deep_closed_let_pure_bind_pkg_ref_stripped" "MISSING_PACKAGE_REF_IN_TEST" fun mr =>
      setupFallibleRuntimeMiniPure mr
        ("import Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n" ++
         "  let inert : IO Nat := pure (((((((((((((((((((LeanSwe.MiniPure.eval 0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)\n" ++
         "  let _ ← inert\n" ++
         "  let t ← IO.monoNanosNow\n" ++
         "  if t == 0 then throw (IO.userError \"unexpected zero clock\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")

    runMutantCase base tmpRoot bin "deep_tautology_kernel_defeq_refines_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "def sneakyAllowed (n y : Nat) : Prop := deepAdd 1500 (n + y) = n + y\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "private theorem deepAdd_eq : ∀ k x : Nat, Model.deepAdd k x = x\n" ++
         "  | 0, _ => rfl\n" ++
         "  | k + 1, x => by simp [Model.deepAdd, deepAdd_eq k x]\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.sneakyAllowed :=\n" ++
         "  fun n => deepAdd_eq 1500 (n + LeanSwe.MiniPure.eval n)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "bounded_meta_exhaustion_refines_fails_closed" "INCONCLUSIVE_REFINES_CHECK" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def deepTaut : Nat → Nat → Prop\n" ++
         "  | 0, x => x = x\n" ++
         "  | k + 1, x => deepTaut k x\n" ++
         "def sneakyAllowed (n y : Nat) : Prop := deepTaut 2500 (n + y)\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "private theorem deepTaut_true : ∀ k x : Nat, Model.deepTaut k x\n" ++
         "  | 0, _ => rfl\n" ++
         "  | k + 1, x => deepTaut_true k x\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "set_option maxRecDepth 16384 in\n" ++
         "theorem refines_model : Core.RefinesPure LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.sneakyAllowed :=\n" ++
         "  fun n => deepTaut_true 2500 (n + LeanSwe.MiniPure.eval n)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "bounded_meta_exhaustion_assumption_fails_closed" "INCONCLUSIVE_ASSUMPTION_CHECK" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Types.lean")
        "namespace LeanSwe.MiniExt\ninductive ExtErr | fail deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniExt\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Model.lean")
        ("import LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt.Model\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "end LeanSwe.MiniExt.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Impl.lean")
        ("import LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt.Internal\n" ++
         "def pingImpl : IO Nat := IO.monoNanosNow\n" ++
         "end LeanSwe.MiniExt.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Interface.lean")
        ("import LeanSwe.MiniExt.Impl\n" ++
         "namespace LeanSwe.MiniExt\n" ++
         "def ping : IO Nat := Internal.pingImpl\n" ++
         "end LeanSwe.MiniExt\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.MiniExt.Model\n" ++
         "import LeanSwe.MiniExt.Interface\n" ++
         "namespace LeanSwe.MiniExt\n" ++
         "open Core Core.NondetTest\n" ++
         "def assume_ping_taut {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n" ++
         "  NondetTest.assert (Model.deepAdd 1500 (fn 0) = fn 0)\n" ++
         "def externalAssumptions : List AssumptionObligation := [\n" ++
         "  { name := \"LeanSwe.MiniExt.assume_ping_taut\", subject := \"LeanSwe.MiniExt.ping\", formalPred? := some \"LeanSwe.MiniExt.assume_ping_taut\" }\n" ++
         "]\n" ++
         "end LeanSwe.MiniExt\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Proofs.lean")
        ("import LeanSwe.MiniExt.SpecTests\n" ++
         "namespace LeanSwe.MiniExt.Proofs\n" ++
         "private theorem deepAdd_eq : ∀ k x : Nat, Model.deepAdd k x = x\n" ++
         "  | 0, _ => rfl\n" ++
         "  | k + 1, x => by simp [Model.deepAdd, deepAdd_eq k x]\n" ++
         "set_option maxRecDepth 16384 in\n" ++
         "theorem assume_ping_taut_can_reach : Core.CanReach (LeanSwe.MiniExt.assume_ping_taut id) :=\n" ++
         "  ⟨deepAdd_eq 1500 0, trivial⟩\n" ++
         "set_option maxRecDepth 16384 in\n" ++
         "theorem consumer (fn : Nat → Nat) (h : Core.AllPass (LeanSwe.MiniExt.assume_ping_taut fn)) : Model.deepAdd 1500 (fn 0) = fn 0 := h.1\n" ++
         "end LeanSwe.MiniExt.Proofs\n")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++
         "import LeanSwe.MiniExt.Types\n" ++
         "import LeanSwe.MiniExt.Model\n" ++
         "import LeanSwe.MiniExt.Impl\n" ++
         "import LeanSwe.MiniExt.Interface\n" ++
         "import LeanSwe.MiniExt.SpecTests\n" ++
         "import LeanSwe.MiniExt.Proofs\n")
      return #[
        "LeanSwe/MiniExt/Types",
        "LeanSwe/MiniExt/Model",
        "LeanSwe/MiniExt/Impl",
        "LeanSwe/MiniExt/Interface",
        "LeanSwe/MiniExt/SpecTests",
        "LeanSwe/MiniExt/Proofs",
        "LeanSwe"
      ]

    expectFailureCode bin "inconclusive_dead_branch_fails_closed" "INCONCLUSIVE_DEAD_BRANCH_CHECK"
      base.libDir base.root #["--allow-legacy", "--dead-branch-fuel", "0"]

    runHarnessParitySelfTests tmpRoot realRepo
    runImportDagSelfTests tmpRoot realRepo realLib

    IO.FS.removeDirAll tmpRoot
    IO.println "CHECK_ASSUMPTIONS_SELFTEST_OK: all Core.Refines, retirement, harness parity, and import-DAG cases verified"
    return 0
  catch err =>
    let _ ← try IO.FS.removeDirAll tmpRoot catch _ => pure ()
    IO.eprintln s!"CHECK_ASSUMPTIONS_SELFTEST_FAILED: {err}"
    return 1
