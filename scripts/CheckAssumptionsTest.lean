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
  writeFileCreatingParents (root / "Core/Obeys.lean") (← IO.FS.readFile (realRepo / "Core/Obeys.lean"))
  writeFileCreatingParents (root / "Core/ConcOps.lean") (← IO.FS.readFile (realRepo / "Core/ConcOps.lean"))
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
    "import Core.NondetTest\nimport Core.Assumptions\nimport Core.Obeys\nimport Core.Refines\nimport LeanSwe.MiniPure.Types\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Impl\nimport LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniPure.SpecTests\nimport LeanSwe.MiniPure.Proofs\nimport LeanSwe.MiniFloat.Types\nimport LeanSwe.MiniFloat.Model\nimport LeanSwe.MiniFloat.Impl\nimport LeanSwe.MiniFloat.Interface\nimport LeanSwe.MiniFloat.SpecTests\nimport LeanSwe.MiniFloat.Proofs\n"

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

  runDagMut "other_helper_in_refines_model" "PROOF_CONST_IN_SIGNATURE"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Helper\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Proofs\ntheorem refines_model : Core.RefinesPureEq LeanSwe.MiniA.step Helper.fakeStep := fun t => by cases t <;> rfl\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "other_helper_in_obeys_model" "PROOF_CONST_IN_SIGNATURE"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Helper\ndef helperPred (t : Tag) : Prop := Model.step t > 0\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Proofs\ntheorem obeys_model (t : Tag) : Helper.helperPred t := by cases t <;> simp [Helper.helperPred, Model.step]\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "other_helper_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Helper|LeanSwe.MiniA.Helper.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Helper\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a Helper.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "other_helper_in_canreach_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Helper|LeanSwe.MiniA.Helper.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Helper\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_reach : Core.CanReach (LeanSwe.MiniA.test_a Helper.fakeStep) := ⟨.a, rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "other_helper_sig_count_stale" "STALE_SIG_PROOF_ALLOWLIST"
      (sigAllow := "LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Helper|LeanSwe.MiniA.Helper.fakeStep=2") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Helper\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a Helper.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "testsupport_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.TestSupport.Mock|LeanSwe.MiniA.TestSupport.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/TestSupport/Mock.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.TestSupport\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.TestSupport\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.TestSupport.Mock\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a TestSupport.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/TestSupport/Mock", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "legacy_alias_spoof_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.HealthySys|LeanSwe.MiniA.HealthySys.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/HealthySys.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.HealthySys\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.HealthySys\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.HealthySys\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a HealthySys.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/HealthySys", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "spectests_body_uses_other_helper" "PROOF_CONST_IN_SPEC"
      (edgeAllow := "WITHIN|LeanSwe.MiniA.SpecTests|LeanSwe.MiniA.Helper")
      (roots := "LeanSwe.MiniA.SpecTests")
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION", "STALE_IMPORT_DAG_ALLOWLIST"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "namespace LeanSwe.MiniA.Helper\ndef helperVal : Nat := 7\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/SpecTests.lean")
      "import Core.NondetTest\nimport LeanSwe.MiniA.Model\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA\nopen Core Core.NondetTest\ndef test_bad_other {r} [NondetTest r] : r Unit := do\n  NondetTest.assert (Helper.helperVal = 7)\nend LeanSwe.MiniA\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/SpecTests"]

  runDagMut "other_helper_namespace_model" "PROOF_MODEL_NS_FORBIDDEN"
      (roots := "LeanSwe.MiniA.Helper") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "namespace LeanSwe.MiniA.Model\ndef disguisedModel (n : Nat) : Nat := n\nend LeanSwe.MiniA.Model\n"
    return #["LeanSwe/MiniA/Helper"]

  runDagMut "within_impl_imports_other_helper" "WITHIN|LeanSwe.MiniA.Impl|LeanSwe.MiniA.Helper"
      (roots := "LeanSwe.MiniA.Impl") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Helper.lean")
      "namespace LeanSwe.MiniA.Helper\ndef val : Nat := 1\nend LeanSwe.MiniA.Helper\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Impl.lean")
      "import LeanSwe.MiniA.Types\nimport LeanSwe.MiniA.Helper\nnamespace LeanSwe.MiniA.Internal\ndef stepImpl (_ : Tag) : Nat := Helper.val\nend LeanSwe.MiniA.Internal\n"
    return #["LeanSwe/MiniA/Helper", "LeanSwe/MiniA/Impl"]

  runDagMut "properties_helper_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.Properties|LeanSwe.MiniA.Properties.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Properties.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Properties\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.Properties\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Properties\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a Properties.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/Properties", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "specmutants_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.SpecMutants|LeanSwe.MiniA.SpecMutants.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/SpecMutants.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.SpecMutants\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.SpecMutants\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.SpecMutants\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a SpecMutants.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/SpecMutants", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "runtimetests_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA.RuntimeTests|LeanSwe.MiniA.RuntimeTests.fakeStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA/RuntimeTests.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.RuntimeTests\ndef fakeStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA.RuntimeTests\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.RuntimeTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a RuntimeTests.fakeStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA/RuntimeTests", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  runDagMut "umbrella_in_allpass_sig"
      "PROOF_CONST_IN_SIGNATURE: LeanSwe.MiniA.Proofs|LeanSwe.MiniA|LeanSwe.MiniA.umbrellaStep count=1"
      (forbiddenCodes := #["DAG_WITHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/MiniA.lean")
      "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA\ndef umbrellaStep (t : Tag) : Nat := Model.step t\nend LeanSwe.MiniA\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniA/Proofs.lean")
      "import Core.Refines\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA\nnamespace LeanSwe.MiniA.Proofs\ntheorem proof_a : Core.AllPass (LeanSwe.MiniA.test_a LeanSwe.MiniA.umbrellaStep) := fun _ => ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"
    return #["LeanSwe/MiniA", "LeanSwe/MiniA/Proofs", "LeanSwe"]

  do
    let d := tmpRoot / "dag_aeneas_model_submodule_ok"
    let rc := d / "repo"
    let lc := d / "lib"
    IO.FS.createDirAll d
    copyDirTree root rc
    copyDirTree libDir lc
    let lp := s!"{lc}:{realLibAbs}"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Types.lean")
      "namespace LeanSwe.PostFork\ninductive PfTag where | ok\nend LeanSwe.PostFork\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Aeneas/Model/World.lean")
      "import LeanSwe.PostFork.Types\nnamespace LeanSwe.PostFork.Aeneas.Internal.World\ndef worldVal : Nat := 1\nend LeanSwe.PostFork.Aeneas.Internal.World\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Aeneas/Model.lean")
      "import LeanSwe.PostFork.Aeneas.Model.World\nnamespace LeanSwe.PostFork.Aeneas.Model\ndef modelVal : Nat := LeanSwe.PostFork.Aeneas.Internal.World.worldVal\nend LeanSwe.PostFork.Aeneas.Model\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/SpecTests.lean")
      "import Core.NondetTest\nimport LeanSwe.PostFork.Aeneas.Model\nnamespace LeanSwe.PostFork\nopen Core Core.NondetTest\ndef test_pf {r} [NondetTest r] : r Unit := do\n  NondetTest.assert (LeanSwe.PostFork.Aeneas.Model.modelVal = 1)\nend LeanSwe.PostFork\n"
    for m in #["LeanSwe/PostFork/Types", "LeanSwe/PostFork/Aeneas/Model/World", "LeanSwe/PostFork/Aeneas/Model", "LeanSwe/PostFork/SpecTests"] do
      compileLeanMod rc lp (rc / s!"{m}.lean") (lc / s!"{m}.olean")
    let out ← runCmd bin.toString #[lc.toString, "LeanSwe.PostFork.SpecTests", "", ""]
    let comb := out.stdout ++ "\n" ++ out.stderr
    if out.exitCode != 0 || (comb.splitOn "errors=0").length <= 1 then
      throw (IO.userError s!"FAIL [aeneas_model_submodule_ok]: expected exit 0 errors=0:\n{comb}")
    IO.println s!"PASS [aeneas_model_submodule_ok] -> {out.stdout.trimAscii.toString}"
    IO.FS.removeDirAll d

  runDagMut "aeneas_model_submodule_imports_impl"
      "DAG_WITHIN_VIOLATION: LeanSwe.PostFork.Aeneas.Model.World (Model) transitively imports same-package LeanSwe.PostFork.Aeneas.FunsExternal (Impl)"
      (roots := "LeanSwe.PostFork.Aeneas.Model.World") fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Types.lean")
      "namespace LeanSwe.PostFork\ninductive PfTag where | ok\nend LeanSwe.PostFork\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Aeneas/FunsExternal.lean")
      "namespace LeanSwe.PostFork.Aeneas.FunsExternal\ndef extVal : Nat := 1\nend LeanSwe.PostFork.Aeneas.FunsExternal\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Aeneas/Model/World.lean")
      "import LeanSwe.PostFork.Types\nimport LeanSwe.PostFork.Aeneas.FunsExternal\nnamespace LeanSwe.PostFork.Aeneas.Internal.World\ndef worldVal : Nat := LeanSwe.PostFork.Aeneas.FunsExternal.extVal\nend LeanSwe.PostFork.Aeneas.Internal.World\n"
    return #["LeanSwe/PostFork/Types", "LeanSwe/PostFork/Aeneas/FunsExternal", "LeanSwe/PostFork/Aeneas/Model/World"]

  runDagMut "aeneas_model_submodule_cross_internal"
      "DAG_CROSS_INTERNAL_REACHIN"
      (roots := "LeanSwe.MiniB.Model")
      (forbiddenCodes := #["DAG_CROSS_IMPORT_VIOLATION", "DAG_CROSS_REACHIN_VIOLATION"]) fun rc => do
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Types.lean")
      "namespace LeanSwe.PostFork\ninductive PfTag where | ok\nend LeanSwe.PostFork\n"
    writeFileCreatingParents (rc / "LeanSwe/PostFork/Aeneas/Model/World.lean")
      "import LeanSwe.PostFork.Types\nnamespace LeanSwe.PostFork.Aeneas.Internal.World\ndef worldVal : Nat := 1\nend LeanSwe.PostFork.Aeneas.Internal.World\n"
    writeFileCreatingParents (rc / "LeanSwe/MiniB/Model.lean")
      "import LeanSwe.PostFork.Aeneas.Model.World\nimport LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.Model\ndef evalB (_ : BTag) : Nat := LeanSwe.PostFork.Aeneas.Internal.World.worldVal\nend LeanSwe.MiniB.Model\n"
    return #["LeanSwe/PostFork/Types", "LeanSwe/PostFork/Aeneas/Model/World", "LeanSwe/MiniB/Model"]

  IO.FS.removeDirAll baseDir

private def runCentralCoverageSelfTests (base : MiniRepo) (tmpRoot bin : System.FilePath) : IO Unit := do
  let cDir := tmpRoot / "central_cov_base"
  let repo := cDir / "repo"
  let lib := cDir / "lib"
  IO.FS.createDirAll cDir
  copyDirTree base.root repo
  copyDirTree base.libDir lib
  let lp := s!"{lib}:{base.leanPath}"

  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Types.lean")
    ("namespace LeanSwe.MiniPure\n" ++
     "structure PureCfg where\n  delta : Nat\n" ++
     "inductive MiniErrKind\n  | badInput\n  | impossible\n  deriving Repr, BEq, DecidableEq\n" ++
     "structure MiniErr where\n  kind : MiniErrKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
     "end LeanSwe.MiniPure\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Model.lean")
    ("import LeanSwe.MiniPure.Types\n" ++
     "namespace LeanSwe.MiniPure.Model\n" ++
     "def evalModel (n : Nat) : Nat := n + 1\n" ++
     "def parseModel (s : String) : Except MiniErr Nat :=\n" ++
     "  if s.isEmpty then .error { kind := .badInput, msg := \"empty\" } else .ok s.length\n" ++
     "end LeanSwe.MiniPure.Model\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Impl.lean")
    ("import LeanSwe.MiniPure.Types\n" ++
     "namespace LeanSwe.MiniPure.Internal\n" ++
     "def evalImpl (n : Nat) : Nat := n + 1\n" ++
     "def parseImpl (s : String) : Except MiniErr Nat :=\n" ++
     "  if s.isEmpty then .error { kind := .badInput, msg := \"empty\" } else .ok s.length\n" ++
     "end LeanSwe.MiniPure.Internal\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Interface.lean")
    ("import LeanSwe.MiniPure.Impl\n" ++
     "namespace LeanSwe.MiniPure\n" ++
     "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
     "def parse (s : String) : Except MiniErr Nat := Internal.parseImpl s\n" ++
     "end LeanSwe.MiniPure\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Proofs.lean")
    ("import Core.Assumptions\nimport Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
     "namespace LeanSwe.MiniPure.Proofs\n" ++
     "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
     "theorem parse_never_impossible (s : String) : Core.NeverErrorKindPure MiniErr.kind .impossible (LeanSwe.MiniPure.parse s) := by\n" ++
     "  unfold Core.NeverErrorKindPure LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl\n" ++
     "  by_cases h : s.isEmpty <;> simp [h]\n" ++
     "theorem obeys_model :\n" ++
     "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
     "    Core.ObeysPureEq LeanSwe.MiniPure.parse Model.parseModel := ⟨fun _ => rfl, fun _ => rfl⟩\n" ++
     "end LeanSwe.MiniPure.Proofs\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/Types.lean")
    ("namespace LeanSwe.MiniExt\n" ++
     "inductive ExtErrKind\n  | hostFail\n  deriving Repr, BEq, DecidableEq\n" ++
     "structure ExtErr where\n  kind : ExtErrKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
     "end LeanSwe.MiniExt\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/Model.lean")
    ("import LeanSwe.MiniExt.Types\n" ++
     "namespace LeanSwe.MiniExt.Model\n" ++
     "def probeModel (k : String) : Nat := k.length\n" ++
     "end LeanSwe.MiniExt.Model\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/Impl.lean")
    ("import LeanSwe.MiniExt.Types\n" ++
     "namespace LeanSwe.MiniExt.Internal\n" ++
     "@[extern \"leanswe_miniext_probe\"]\n" ++
     "private opaque rawProbe (k : @& String) : IO (Option String)\n" ++
     "def probeImpl (k : String) : IO (Except ExtErr Nat) := do\n" ++
     "  match ← rawProbe k with\n" ++
     "  | some v => return .ok v.length\n" ++
     "  | none => return .error { kind := .hostFail, msg := \"missing\" }\n" ++
     "end LeanSwe.MiniExt.Internal\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/Interface.lean")
    ("import LeanSwe.MiniExt.Impl\n" ++
     "namespace LeanSwe.MiniExt\n" ++
     "def probe (k : String) : IO (Except ExtErr Nat) := Internal.probeImpl k\n" ++
     "end LeanSwe.MiniExt\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/SpecTests.lean")
    ("import Core.NondetTest\nimport Core.Assumptions\nimport LeanSwe.MiniExt.Interface\n" ++
     "namespace LeanSwe.MiniExt\nopen Core Core.NondetTest\n" ++
     "def assume_miniext_probe_nonzero {r} [NondetTest r] (f : String → Nat) : r Unit := do\n" ++
     "  let k ← nondet String\n" ++
     "  NondetTest.assert (f k ≥ 1)\n" ++
     "def externalAssumptions : List AssumptionObligation :=\n" ++
     "  [ { name := \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\", subject := \"LeanSwe.MiniExt.probe\", formalPred? := some \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\" } ]\n" ++
     "end LeanSwe.MiniExt\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniExt/Proofs.lean")
    ("import Core.NondetTest\nimport LeanSwe.MiniExt.SpecTests\n" ++
     "namespace LeanSwe.MiniExt.Proofs\n" ++
     "theorem assume_miniext_canreach : Core.CanReach (LeanSwe.MiniExt.assume_miniext_probe_nonzero (fun _ => 1)) :=\n" ++
     "  ⟨\"a\", by decide, trivial⟩\n" ++
     "end LeanSwe.MiniExt.Proofs\n")
  writeFileCreatingParents (repo / "LeanSwe/MiniPure/Proofs/Consumer.lean")
    ("import LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniExt.SpecTests\n" ++
     "namespace LeanSwe.MiniPure.Proofs\n" ++
     "theorem uses_miniext_assump (f : String → Nat) (h : Core.AllPass (LeanSwe.MiniExt.assume_miniext_probe_nonzero f)) :\n" ++
     "    LeanSwe.MiniPure.eval (f \"x\") ≥ 2 := by\n" ++
     "  have hx := (h \"x\").1\n" ++
     "  unfold LeanSwe.MiniPure.eval LeanSwe.MiniPure.Internal.evalImpl\n" ++
     "  omega\n" ++
     "end LeanSwe.MiniPure.Proofs\n")
  writeFileCreatingParents (repo / "harness/Fuzz/suites.json")
    ("{\n  \"version\": 1,\n  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n  \"suites\": {\n" ++
     "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
     "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
     "    \"miniext\": { \"paths\": [\"harness/Fuzz/MiniExt/\", \"LeanSwe/MiniExt/\"] }\n" ++
     "  }\n}\n")
  writeFileCreatingParents (repo / "scripts/package_manifest.json")
    ("{\n  \"version\": 1,\n  \"packages\": {\n" ++
     "    \"LeanSwe.MiniPure\": { \"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false },\n" ++
     "    \"LeanSwe.MiniFloat\": { \"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false },\n" ++
     "    \"LeanSwe.MiniExt\": { \"kind\": \"model\", \"purity\": \"nondet_io\", \"deps\": [], \"external_boundary\": true }\n" ++
     "  }\n}\n")
  writeFileCreatingParents (repo / "scripts/coverage_overrides.json")
    ("{\n  \"version\": 1,\n  \"overrides\": [\n" ++
     "    {\n" ++
     "      \"op\": \"LeanSwe.MiniExt.probe\",\n" ++
     "      \"kind\": \"LeanSwe.MiniExt.ExtErrKind.hostFail\",\n" ++
     "      \"mode\": \"untriggerable\",\n" ++
     "      \"test_symbol\": \"\",\n" ++
     "      \"reason\": \"Synthetic untriggerable OS fault for central coverage self-test\"\n" ++
     "    }\n" ++
     "  ]\n}\n")
  writeFileCreatingParents (repo / "scripts/external_assumptions.json")
    ("{\n  \"version\": 1,\n  \"assumptions\": [\n" ++
     "    {\n" ++
     "      \"id\": \"miniext.probe_nonzero\",\n" ++
     "      \"package\": \"LeanSwe.MiniExt\",\n" ++
     "      \"why_unfuzzable\": \"Global environment invariant\",\n" ++
     "      \"formal_pred\": \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\"\n" ++
     "    }\n" ++
     "  ]\n}\n")
  writeFileCreatingParents (repo / "LeanSwe.lean")
    ("import Core.NondetTest\nimport Core.Assumptions\nimport Core.Obeys\nimport Core.Refines\n" ++
     "import LeanSwe.MiniPure.Types\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Impl\n" ++
     "import LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniPure.SpecTests\nimport LeanSwe.MiniPure.Proofs\n" ++
     "import LeanSwe.MiniFloat.Types\nimport LeanSwe.MiniFloat.Model\nimport LeanSwe.MiniFloat.Impl\n" ++
     "import LeanSwe.MiniFloat.Interface\nimport LeanSwe.MiniFloat.SpecTests\nimport LeanSwe.MiniFloat.Proofs\n" ++
     "import LeanSwe.MiniExt.Types\nimport LeanSwe.MiniExt.Model\nimport LeanSwe.MiniExt.Impl\n" ++
     "import LeanSwe.MiniExt.Interface\nimport LeanSwe.MiniExt.SpecTests\nimport LeanSwe.MiniExt.Proofs\n" ++
     "import LeanSwe.MiniPure.Proofs.Consumer\n")

  for m in #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
      "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
      "LeanSwe/MiniExt/Types", "LeanSwe/MiniExt/Model", "LeanSwe/MiniExt/Impl",
      "LeanSwe/MiniExt/Interface", "LeanSwe/MiniExt/SpecTests", "LeanSwe/MiniExt/Proofs",
      "LeanSwe/MiniPure/Proofs/Consumer", "LeanSwe"] do
    compileLeanMod repo lp (repo / s!"{m}.lean") (lib / s!"{m}.olean")

  let goodNonce := "0123456789abcdef0123456789abcdef"
  let goodCovLog := cDir / "good.cov.log"
  IO.FS.writeFile goodCovLog
    (s!"{goodNonce}|LOG_INIT\n" ++
     s!"{goodNonce}|ERR_HIT|LeanSwe.MiniPure.parse|LeanSwe.MiniPure.MiniErrKind.badInput|real\n" ++
     s!"{goodNonce}|FUZZ_EQUIV|LeanSwe.MiniExt|miniext|500|4/4|ok=true\n" ++
     s!"{goodNonce}|LOG_CLOSE\n")

  let okOut ← runCmd bin.toString
    #[lib.toString, repo.toString, "--allow-legacy", "--coverage-log", goodCovLog.toString, "--nonce", goodNonce]
  let okComb := okOut.stdout ++ "\n" ++ okOut.stderr
  if okOut.exitCode != 0 || (okComb.splitOn "errors=0").length <= 1 ||
      (okComb.splitOn "olean_never_error=1").length <= 1 ||
      (okComb.splitOn "fuzz_equiv=1").length <= 1 then
    throw (IO.userError s!"FAIL [central_cov_positive]: expected exit=0 errors=0 olean_never_error=1 fuzz_equiv=1:\n{okComb}")
  IO.println "PASS [central_cov_positive] -> NeverErrorKind* .olean auto-discovery + ERR_HIT + FUZZ_EQUIV + overrides + external_assumptions verified"

  let wrongNonceLog := cDir / "wrong_nonce.cov.log"
  IO.FS.writeFile wrongNonceLog
    (s!"{goodNonce}|LOG_INIT\n" ++
     s!"deadbeefdeadbeefdeadbeefdeadbeef|ERR_HIT|LeanSwe.MiniPure.parse|LeanSwe.MiniPure.MiniErrKind.badInput|real\n" ++
     s!"{goodNonce}|LOG_CLOSE\n")
  expectFailureCode bin "central_cov_wrong_nonce_rejected" "INVALID_OR_UNAUTHENTICATED_COVERAGE_LOG_LINES"
    lib repo #["--allow-legacy", "--coverage-log", wrongNonceLog.toString, "--nonce", goodNonce]

  let unclosedLog := cDir / "unclosed.cov.log"
  IO.FS.writeFile unclosedLog
    (s!"{goodNonce}|LOG_INIT\n" ++
     s!"{goodNonce}|ERR_HIT|LeanSwe.MiniPure.parse|LeanSwe.MiniPure.MiniErrKind.badInput|real\n")
  let unclosedOut ← runCmd bin.toString
    #[lib.toString, repo.toString, "--allow-legacy", "--coverage-log", unclosedLog.toString, "--nonce", goodNonce]
  expectOutputContains "central_cov_missing_close_rejected" "INCOMPLETE_OR_UNINITIALIZED_COVERAGE_LOG" unclosedOut
  expectOutputContains "central_cov_bad_log_still_requires_coverage" "MISSING_ERROR_COVERAGE" unclosedOut

  do
    let surfDir := tmpRoot / "central_cov_surface_zero"
    let sRepo := surfDir / "repo"
    let sLib := surfDir / "lib"
    IO.FS.createDirAll surfDir
    copyDirTree repo sRepo
    copyDirTree lib sLib
    let slp := s!"{sLib}:{base.leanPath}"
    writeFileCreatingParents (sRepo / "LeanSwe/MiniPure/Types.lean")
      ("namespace LeanSwe.MiniPure\n" ++
       "structure PureCfg where\n  delta : Nat\n" ++
       "inductive MiniErrKind\n  | badInput\n  deriving Repr, BEq, DecidableEq\n" ++
       "structure MiniErr where\n  kind : MiniErrKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
       "structure MiniApi where\n  parseFn : String → Except MiniErr Nat\n" ++
       "end LeanSwe.MiniPure\n")
    writeFileCreatingParents (sRepo / "LeanSwe/MiniPure/Model.lean")
      ("import LeanSwe.MiniPure.Types\n" ++
       "namespace LeanSwe.MiniPure.Model\n" ++
       "def evalModel (n : Nat) : Nat := n + 1\n" ++
       "end LeanSwe.MiniPure.Model\n")
    writeFileCreatingParents (sRepo / "LeanSwe/MiniPure/Impl.lean")
      ("import LeanSwe.MiniPure.Types\n" ++
       "namespace LeanSwe.MiniPure.Internal\n" ++
       "def evalImpl (n : Nat) : Nat := n + 1\n" ++
       "def parseImpl (s : String) : Except MiniErr Nat :=\n" ++
       "  if s.isEmpty then .error { kind := .badInput, msg := \"empty\" } else .ok s.length\n" ++
       "end LeanSwe.MiniPure.Internal\n")
    writeFileCreatingParents (sRepo / "LeanSwe/MiniPure/Interface.lean")
      ("import LeanSwe.MiniPure.Impl\n" ++
       "namespace LeanSwe.MiniPure\n" ++
       "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
       "def defaultApi : MiniApi := { parseFn := Internal.parseImpl }\n" ++
       "end LeanSwe.MiniPure\n")
    writeFileCreatingParents (sRepo / "LeanSwe/MiniPure/Proofs.lean")
      ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
       "namespace LeanSwe.MiniPure.Proofs\n" ++
       "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
       "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel := fun _ => rfl\n" ++
       "end LeanSwe.MiniPure.Proofs\n")
    for m in #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/Proofs/Consumer", "LeanSwe"] do
      compileLeanMod sRepo slp (sRepo / s!"{m}.lean") (sLib / s!"{m}.olean")
    let validEmptyLog := surfDir / "valid_empty.cov.log"
    IO.FS.writeFile validEmptyLog s!"{goodNonce}|LOG_INIT\n{goodNonce}|LOG_CLOSE\n"
    expectFailureCode bin "central_cov_fallible_surface_zero_cells_rejected" "MISSING_ERROR_COVERAGE"
      sLib sRepo #["--allow-legacy", "--coverage-log", validEmptyLog.toString, "--nonce", goodNonce]
    IO.FS.removeDirAll surfDir

  let badFuzzLog := cDir / "bad_fuzz.cov.log"
  IO.FS.writeFile badFuzzLog
    (s!"{goodNonce}|LOG_INIT\n" ++
     s!"{goodNonce}|ERR_HIT|LeanSwe.MiniPure.parse|LeanSwe.MiniPure.MiniErrKind.badInput|real\n" ++
     s!"{goodNonce}|FUZZ_EQUIV|LeanSwe.MiniExt|miniext|500|3/4|ok=false\n" ++
     s!"{goodNonce}|LOG_CLOSE\n")
  expectFailureCode bin "central_cov_fuzz_equiv_false_rejected" "FUZZ_EQUIV_FAILED"
    lib repo #["--allow-legacy", "--coverage-log", badFuzzLog.toString, "--nonce", goodNonce]

  let missingCellLog := cDir / "missing_cell.cov.log"
  IO.FS.writeFile missingCellLog s!"{goodNonce}|LOG_INIT\n{goodNonce}|LOG_CLOSE\n"
  expectFailureCode bin "central_cov_uncovered_cell_rejected" "UNCOVERED_CENTRAL_ERROR_CELL"
    lib repo #["--allow-legacy", "--coverage-log", missingCellLog.toString, "--nonce", goodNonce]

  let mockedPureLog := cDir / "mocked_pure.cov.log"
  IO.FS.writeFile mockedPureLog
    (s!"{goodNonce}|LOG_INIT\n" ++
     s!"{goodNonce}|ERR_HIT|LeanSwe.MiniPure.parse|LeanSwe.MiniPure.MiniErrKind.badInput|mocked\n" ++
     s!"{goodNonce}|LOG_CLOSE\n")
  expectFailureCode bin "central_cov_mocked_err_hit_on_pure_rejected" "PURE_PACKAGE_MOCKED_ERR_HIT"
    lib repo #["--allow-legacy", "--coverage-log", mockedPureLog.toString, "--nonce", goodNonce]

  let runJsonMut (name code : String) (mutate : System.FilePath → IO Unit) : IO Unit := do
    let d := tmpRoot / s!"cc_{name}"
    let rc := d / "repo"
    IO.FS.createDirAll d
    copyDirTree repo rc
    mutate rc
    expectFailureCode bin name code lib rc #["--allow-legacy", "--coverage-log", goodCovLog.toString, "--nonce", goodNonce]
    IO.FS.removeDirAll d

  runJsonMut "central_cov_mocked_override_on_pure_rejected" "PURE_PACKAGE_MOCKED_OVERRIDE" fun rc => do
    writeFileCreatingParents (rc / "scripts/coverage_overrides.json")
      ("{\n  \"version\": 1,\n  \"overrides\": [\n" ++
       "    {\n" ++
       "      \"op\": \"LeanSwe.MiniPure.parse\",\n" ++
       "      \"kind\": \"LeanSwe.MiniPure.MiniErrKind.badInput\",\n" ++
       "      \"mode\": \"mocked\",\n" ++
       "      \"test_symbol\": \"LeanSwe.MiniPure.RuntimeTests.fake\",\n" ++
       "      \"reason\": \"Forbidden mocked override on pure package\"\n" ++
       "    }\n" ++
       "  ]\n}\n")

  runJsonMut "central_ext_assump_missing_formal_pred_rejected" "MISSING_EXTERNAL_ASSUMPTION_FORMAL_PRED" fun rc => do
    writeFileCreatingParents (rc / "scripts/external_assumptions.json")
      ("{\n  \"version\": 1,\n  \"assumptions\": [\n" ++
       "    {\n" ++
       "      \"id\": \"miniext.missing_pred\",\n" ++
       "      \"package\": \"LeanSwe.MiniExt\",\n" ++
       "      \"why_unfuzzable\": \"Missing formal predicate\",\n" ++
       "      \"formal_pred\": \"LeanSwe.MiniExt.assume_does_not_exist\"\n" ++
       "    }\n" ++
       "  ]\n}\n")

  runJsonMut "central_ext_assump_pure_pkg_rejected" "PURE_PACKAGE_EXTERNAL_ASSUMPTION" fun rc => do
    writeFileCreatingParents (rc / "scripts/external_assumptions.json")
      ("{\n  \"version\": 1,\n  \"assumptions\": [\n" ++
       "    {\n" ++
       "      \"id\": \"minipure.forbidden\",\n" ++
       "      \"package\": \"LeanSwe.MiniPure\",\n" ++
       "      \"why_unfuzzable\": \"Pure packages must not declare external assumptions\",\n" ++
       "      \"formal_pred\": null\n" ++
       "    }\n" ++
       "  ]\n}\n")

  do
    let maDir := tmpRoot / "cc_model_assumptions"
    let maRepo := maDir / "repo"
    let maLib := maDir / "lib"
    IO.FS.createDirAll maDir
    copyDirTree repo maRepo
    copyDirTree lib maLib
    let malp := s!"{maLib}:{base.leanPath}"
    writeFileCreatingParents (maRepo / "LeanSwe/MiniExt/Model/Assumptions.lean")
      ("import Core.NondetTest\nimport LeanSwe.MiniExt.Types\n" ++
       "namespace LeanSwe.MiniExt\nopen Core Core.NondetTest\n" ++
       "def assume_miniext_probe_nonzero {r} [NondetTest r] (f : String → Nat) : r Unit := do\n" ++
       "  let k ← nondet String\n" ++
       "  NondetTest.assert (f k ≥ 1)\n" ++
       "end LeanSwe.MiniExt\n")
    writeFileCreatingParents (maRepo / "LeanSwe/MiniExt/SpecTests.lean")
      ("import Core.Assumptions\nimport LeanSwe.MiniExt.Interface\nimport LeanSwe.MiniExt.Model.Assumptions\n" ++
       "namespace LeanSwe.MiniExt\nopen Core\n" ++
       "def externalAssumptions : List AssumptionObligation :=\n" ++
       "  [ { name := \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\", subject := \"LeanSwe.MiniExt.probe\", formalPred? := some \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\" } ]\n" ++
       "end LeanSwe.MiniExt\n")
    writeFileCreatingParents (maRepo / "LeanSwe/MiniPure/Proofs/Consumer.lean")
      ("import LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniExt.Model.Assumptions\n" ++
       "namespace LeanSwe.MiniPure.Proofs\n" ++
       "theorem uses_miniext_assump (f : String → Nat) (h : Core.AllPass (LeanSwe.MiniExt.assume_miniext_probe_nonzero f)) :\n" ++
       "    LeanSwe.MiniPure.eval (f \"x\") ≥ 2 := by\n" ++
       "  have hx := (h \"x\").1\n" ++
       "  unfold LeanSwe.MiniPure.eval LeanSwe.MiniPure.Internal.evalImpl\n" ++
       "  omega\n" ++
       "end LeanSwe.MiniPure.Proofs\n")
    for m in #["LeanSwe/MiniExt/Model/Assumptions", "LeanSwe/MiniExt/SpecTests",
        "LeanSwe/MiniExt/Proofs", "LeanSwe/MiniPure/Proofs/Consumer", "LeanSwe"] do
      compileLeanMod maRepo malp (maRepo / s!"{m}.lean") (maLib / s!"{m}.olean")
    let maOkOut ← runCmd bin.toString
      #[maLib.toString, maRepo.toString, "--allow-legacy", "--coverage-log", goodCovLog.toString, "--nonce", goodNonce]
    let maOkComb := maOkOut.stdout ++ "\n" ++ maOkOut.stderr
    if maOkOut.exitCode != 0 || (maOkComb.splitOn "errors=0").length <= 1 ||
        (maOkComb.splitOn "formal_assumptions=1").length <= 1 then
      throw (IO.userError s!"FAIL [central_model_assumptions_relocated_positive]: expected exit=0 errors=0 formal_assumptions=1:\n{maOkComb}")
    IO.println "PASS [central_model_assumptions_relocated_positive] -> Model.Assumptions formal_assumptions=1 verified"

    let runMaMut (name code : String)
        (mutate : System.FilePath → IO (Array String))
        (forbiddenCodes : Array String := #[]) : IO Unit := do
      let d := tmpRoot / s!"ma_{name}"
      let rc := d / "repo"
      let lc := d / "lib"
      IO.FS.createDirAll d
      copyDirTree maRepo rc
      copyDirTree maLib lc
      let dlp := s!"{lc}:{base.leanPath}"
      let mods ← mutate rc
      for m in mods do
        compileLeanMod rc dlp (rc / s!"{m}.lean") (lc / s!"{m}.olean")
      let out ← runCmd bin.toString
        #[lc.toString, rc.toString, "--allow-legacy", "--coverage-log", goodCovLog.toString, "--nonce", goodNonce]
      expectOutputContains name code out forbiddenCodes
      IO.FS.removeDirAll d

    runMaMut "central_model_assumptions_unlisted_rejected" "UNLISTED_FORMAL_ASSUMPTION" fun rc => do
      writeFileCreatingParents (rc / "LeanSwe/MiniExt/Model/Assumptions.lean")
        ("import Core.NondetTest\nimport LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt\nopen Core Core.NondetTest\n" ++
         "def assume_miniext_probe_nonzero {r} [NondetTest r] (f : String → Nat) : r Unit := do\n" ++
         "  let k ← nondet String\n" ++
         "  NondetTest.assert (f k ≥ 1)\n" ++
         "def assume_miniext_unlisted {r} [NondetTest r] (f : String → Nat) : r Unit := do\n" ++
         "  let k ← nondet String\n" ++
         "  NondetTest.assert (f k ≥ 2)\n" ++
         "end LeanSwe.MiniExt\n")
      return #["LeanSwe/MiniExt/Model/Assumptions", "LeanSwe/MiniExt/SpecTests",
        "LeanSwe/MiniExt/Proofs", "LeanSwe/MiniPure/Proofs/Consumer", "LeanSwe"]

    runMaMut "central_model_assumptions_trivial_rejected" "TRIVIAL_ASSUMPTION_ASSERT"
        (forbiddenCodes := #["UNLISTED_FORMAL_ASSUMPTION", "UNUSED_FORMAL_ASSUMPTION"]) fun rc => do
      writeFileCreatingParents (rc / "LeanSwe/MiniExt/Model/Assumptions.lean")
        ("import Core.NondetTest\nimport LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt\nopen Core Core.NondetTest\n" ++
         "def assume_miniext_probe_nonzero {r} [NondetTest r] (_ : String → Nat) : r Unit := do\n" ++
         "  let k ← nondet String\n" ++
         "  NondetTest.assert (k = k ∧ 0 = 0)\n" ++
         "end LeanSwe.MiniExt\n")
      writeFileCreatingParents (rc / "LeanSwe/MiniExt/Proofs.lean")
        ("import Core.NondetTest\nimport LeanSwe.MiniExt.SpecTests\n" ++
         "namespace LeanSwe.MiniExt.Proofs\n" ++
         "theorem assume_miniext_canreach : Core.CanReach (LeanSwe.MiniExt.assume_miniext_probe_nonzero (fun _ => 1)) :=\n" ++
         "  ⟨\"a\", ⟨rfl, rfl⟩, trivial⟩\n" ++
         "end LeanSwe.MiniExt.Proofs\n")
      writeFileCreatingParents (rc / "LeanSwe/MiniPure/Proofs/Consumer.lean")
        ("import LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniExt.Model.Assumptions\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem uses_miniext_assump (f : String → Nat) (h : Core.AllPass (LeanSwe.MiniExt.assume_miniext_probe_nonzero f)) :\n" ++
         "    0 = 0 ∧ LeanSwe.MiniPure.eval 0 = 1 := ⟨(h \"\").1.2, rfl⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniExt/Model/Assumptions", "LeanSwe/MiniExt/SpecTests",
        "LeanSwe/MiniExt/Proofs", "LeanSwe/MiniPure/Proofs/Consumer", "LeanSwe"]

    runMaMut "central_model_assumptions_unlinked_pred_rejected"
        "UNLINKED_FORMAL_ASSUMPTION_PRED: LeanSwe.MiniExt.assume_miniext_probe_nonzero exists in LeanSwe.MiniExt.Model.Assumptions with formalPred? = none" fun rc => do
      writeFileCreatingParents (rc / "LeanSwe/MiniExt/SpecTests.lean")
        ("import Core.Assumptions\nimport LeanSwe.MiniExt.Interface\nimport LeanSwe.MiniExt.Model.Assumptions\n" ++
         "namespace LeanSwe.MiniExt\nopen Core\n" ++
         "def externalAssumptions : List AssumptionObligation :=\n" ++
         "  [ { name := \"LeanSwe.MiniExt.assume_miniext_probe_nonzero\", subject := \"LeanSwe.MiniExt.probe\", formalPred? := none } ]\n" ++
         "end LeanSwe.MiniExt\n")
      return #["LeanSwe/MiniExt/SpecTests", "LeanSwe/MiniExt/Proofs", "LeanSwe"]

    IO.FS.removeDirAll maDir

  IO.FS.removeDirAll cDir

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

    runPositiveCase base tmpRoot bin "step_from_implicit_ground_fd_and_defaultOpsBase_ok" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure RawFdOpsM (m : Type → Type) (fd : Type) where\n  openFd : UInt32 → m fd\n" ++
         "structure FdOpsM (m : Type → Type) (fd : Type) where\n  openFd : UInt32 → m fd\n" ++
         "abbrev HandleId := Nat\n" ++
         "abbrev HandleRawFdOpsM (m : Type → Type) : Type := RawFdOpsM m HandleId\n" ++
         "abbrev HandleFdOpsM (m : Type → Type) : Type := FdOpsM m HandleId\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : HandleRawFdOpsM (StateM W)) (k : UInt32) : StateM W HandleId := raw.openFd k\n" ++
         "def rawAllowed (s : Nat) (k : UInt32) (out s' : Nat) : Prop := out = s + k.toNat ∧ s' = s + 1\n" ++
         "def execPkg {W : Type} (ops : HandleFdOpsM (StateM W)) (k : UInt32) : StateM W HandleId := ops.openFd k\n" ++
         "def pkgAllowed (s : Nat) (k : UInt32) (out s' : Nat) : Prop := out = s + k.toNat ∧ s' = s + 1\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkFdOpsM {m : Type → Type} {fd : Type} [Monad m] (raw : RawFdOpsM m fd) : FdOpsM m fd := { openFd := raw.openFd }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def defaultOpsBase : FdOpsM BaseIO UInt64 := Internal.mkFdOpsM { openFd := fun k => pure k.toUInt64 }\n" ++
         "def defaultOps : FdOpsM IO UInt64 := { openFd := fun k => liftM (defaultOpsBase.openFd k) }\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def openFd (k : UInt32) : IO UInt64 := defaultOps.openFd k\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ " ++
         "Core.ObeysStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkFdOpsM Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ h => h⟩\nend LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "step_from_uninhabited_fd_type_rejected" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure RawFdOpsM (m : Type → Type) (fd : Type) where\n  ping : Nat → m Nat\n" ++
         "structure FdOpsM (m : Type → Type) (fd : Type) where\n  ping : Nat → m Nat\n" ++
         "abbrev EmptyRawFdOpsM (m : Type → Type) : Type := RawFdOpsM m Empty\n" ++
         "abbrev EmptyFdOpsM (m : Type → Type) : Type := FdOpsM m Empty\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : EmptyRawFdOpsM (StateM W)) (k : Nat) : StateM W Nat := raw.ping k\n" ++
         "def rawAllowed (s k out s' : Nat) : Prop := out = s + k ∧ s' = s\n" ++
         "def execPkg {W : Type} (ops : EmptyFdOpsM (StateM W)) (k : Nat) : StateM W Nat := ops.ping k\n" ++
         "def pkgAllowed (s k out s' : Nat) : Prop := out = s + k ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkFdOpsM {m : Type → Type} {fd : Type} [Monad m] (raw : RawFdOpsM m fd) : FdOpsM m fd := { ping := raw.ping }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def defaultOps : FdOpsM IO Nat := Internal.mkFdOpsM { ping := pure }\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def ping (n : Nat) : IO Nat := defaultOps.ping n\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ " ++
         "Core.ObeysStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkFdOpsM Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ h => h⟩\nend LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "step_from_term_partial_app_on_mk_rejected" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure RawBoxOpsM (m : Type → Type) where\n  readBox : Nat → m Nat\n" ++
         "structure BoxApiM (m : Type → Type) where\n  readBox : Nat → m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (raw : RawBoxOpsM (StateM W)) (k : Nat) : StateM W Nat := raw.readBox k\n" ++
         "def rawAllowed (s k out s' : Nat) : Prop := out = s + k ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : BoxApiM (StateM W)) (k : Nat) : StateM W Nat := api.readBox k\n" ++
         "def pkgAllowed (s k out s' : Nat) : Prop := out = s + k ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiFlag {m : Type → Type} [Monad m] (flag : Bool) (raw : RawBoxOpsM m) : BoxApiM m := " ++
         "{ readBox := fun k => if flag then raw.readBox k else pure 0 }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def defaultApi : BoxApiM IO := Internal.mkApiFlag true { readBox := pure }\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def readBox (k : Nat) : IO Nat := defaultApi.readBox k\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧ " ++
         "Core.ObeysStepFrom id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf (fun {m} [Monad m] => Internal.mkApiFlag true (m := m)) Model.execPkg Model.pkgAllowed :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ h => h⟩\nend LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl", "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

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

    runMutantCase base tmpRoot bin "irreducible_tautology_defeq_refines_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "@[irreducible] def hideAdd (k x : Nat) : Nat := deepAdd k x\n" ++
         "def sneakyAllowed (n y : Nat) : Prop := hideAdd 15 (n + y) = n + y\n" ++
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
         "  fun n => by unfold LeanSwe.MiniPure.Model.sneakyAllowed LeanSwe.MiniPure.Model.hideAdd; exact deepAdd_eq 15 (n + LeanSwe.MiniPure.eval n)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "very_deep_defeq_refines_inconclusive_no_hang" "INCONCLUSIVE_REFINES_CHECK" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "def sneakyAllowed (n y : Nat) : Prop := deepAdd 1000000000 (n + y) = n + y\n" ++
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
         "  fun n => deepAdd_eq 1000000000 (n + LeanSwe.MiniPure.eval n)\n" ++
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

    runPositiveCase base tmpRoot bin "non_refines_gates_preserve_project_irreducible" fun mr => do
      writeFileCreatingParents (mr.root / "harness/Fuzz/suites.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"common_paths\": [\"Core/\", \"harness/Fuzz/Main.lean\"],\n" ++
         "  \"suites\": {\n" ++
         "    \"selftest\": { \"paths\": [\"harness/Fuzz/SelfTest.lean\"] },\n" ++
         "    \"minifloat\": { \"paths\": [\"harness/Fuzz/MiniFloat/\", \"LeanSwe/MiniFloat/\"] },\n" ++
         "    \"miniext\": { \"paths\": [\"harness/Fuzz/MiniExt/\", \"LeanSwe/MiniExt/\"] }\n" ++
         "  }\n" ++
         "}\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Types.lean")
        "namespace LeanSwe.MiniExt\ninductive MiniExtErr\n  | sysFail\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniExt\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Model.lean")
        ("import LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt.Model\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "@[irreducible] def opaqueZero : Nat := deepAdd 1000000000 0\n" ++
         "def pingModel (x : UInt32) : UInt32 := x + 1\n" ++
         "end LeanSwe.MiniExt.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Impl.lean")
        ("import LeanSwe.MiniExt.Types\n" ++
         "namespace LeanSwe.MiniExt.Internal\n" ++
         "@[extern \"lean_miniext_ping_u32\"]\n" ++
         "opaque rawPing : UInt32 → IO (Except MiniExtErr UInt32)\n" ++
         "end LeanSwe.MiniExt.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Interface.lean")
        ("import LeanSwe.MiniExt.Impl\n" ++
         "namespace LeanSwe.MiniExt\n" ++
         "def ping (x : UInt32) : IO (Except MiniExtErr UInt32) := Internal.rawPing x\n" ++
         "end LeanSwe.MiniExt\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/SpecTests.lean")
        ("import Core.NondetTest\n" ++
         "import Core.Assumptions\n" ++
         "import LeanSwe.MiniExt.Model\n" ++
         "import LeanSwe.MiniExt.Interface\n" ++
         "namespace LeanSwe.MiniExt\n" ++
         "open Core Core.NondetTest\n" ++
         "def assume_ping_opaque {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n" ++
         "  NondetTest.assert (fn Model.opaqueZero = fn 1)\n" ++
         "def externalAssumptions : List AssumptionObligation := [\n" ++
         "  { name := \"LeanSwe.MiniExt.assume_ping_opaque\", subject := \"LeanSwe.MiniExt.ping\", formalPred? := some \"LeanSwe.MiniExt.assume_ping_opaque\" }\n" ++
         "]\n" ++
         "def errorCoverage : List (ErrorObligation MiniExtErr) := [\n" ++
         "  { request := \"LeanSwe.MiniExt.ping\", errorKind := .sysFail, justification := .tested \"LeanSwe.MiniExt.RuntimeTests.err_sys\" .real }\n" ++
         "]\n" ++
         "end LeanSwe.MiniExt\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniExt/Proofs.lean")
        ("import LeanSwe.MiniExt.SpecTests\n" ++
         "namespace LeanSwe.MiniExt.Proofs\n" ++
         "theorem assume_ping_opaque_can_reach : Core.CanReach (LeanSwe.MiniExt.assume_ping_opaque (fun _ => 0)) :=\n" ++
         "  ⟨rfl, trivial⟩\n" ++
         "end LeanSwe.MiniExt.Proofs\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def deepAdd : Nat → Nat → Nat\n" ++
         "  | 0, x => x\n" ++
         "  | k + 1, x => (deepAdd k x) + 0\n" ++
         "@[irreducible] def slowZero : Nat := deepAdd 1000000000 0\n" ++
         "def allowedIsSlowZero (n : Nat) (b : Bool) : Prop := if b then n = slowZero else n ≠ slowZero\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def isSlowZeroImpl (n : Nat) : Bool := n == 0\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def isSlowZero (n : Nat) : Bool := Internal.isSlowZeroImpl n\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Refines\n" ++
         "import LeanSwe.MiniExt.SpecTests\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "private theorem deepAdd_eq : ∀ k x : Nat, Model.deepAdd k x = x\n" ++
         "  | 0, _ => rfl\n" ++
         "  | k + 1, x => by simp [Model.deepAdd, deepAdd_eq k x]\n" ++
         "private theorem slowZero_eq : Model.slowZero = 0 := by\n" ++
         "  unfold Model.slowZero\n" ++
         "  exact deepAdd_eq 1000000000 0\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem consume_miniext_opaque (fn : Nat → Nat) (h : Core.AllPass (LeanSwe.MiniExt.assume_ping_opaque fn)) :\n" ++
         "    fn LeanSwe.MiniExt.Model.opaqueZero = fn 1 ∧ LeanSwe.MiniPure.eval 0 = 1 :=\n" ++
         "  ⟨h.1, rfl⟩\n" ++
         "theorem refines_model :\n" ++
         "    Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧\n" ++
         "    Core.RefinesPure LeanSwe.MiniPure.isSlowZero LeanSwe.MiniPure.Model.allowedIsSlowZero := by\n" ++
         "  refine ⟨fun _ => rfl, fun n => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.isSlowZero LeanSwe.MiniPure.Internal.isSlowZeroImpl LeanSwe.MiniPure.Model.allowedIsSlowZero\n" ++
         "  rw [slowZero_eq]\n" ++
         "  cases n <;> simp\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
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
        "LeanSwe/MiniPure/Model",
        "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface",
        "LeanSwe/MiniPure/SpecTests",
        "LeanSwe/MiniPure/Proofs",
        "LeanSwe"
      ]

    runPositiveCase base tmpRoot bin "obeys_model_pure_eq_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\n" ++
         "import LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runPositiveCase base tmpRoot bin "obeys_model_upto_errmsg_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive ParseKind\n  | empty\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"empty input\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\nimport Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\nopen Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n" ++
         "  let x ← nondet Nat\n  NondetTest.assert (fn x = Model.evalModel x)\n" ++
         "def errorCoverage : List (ErrorObligation ParseKind) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.parse\", errorKind := .empty, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_empty\" .real },\n" ++
         "  { request := \"LeanSwe.MiniPure.parse\", errorKind := .bad, justification := .provedImpossible \"LeanSwe.MiniPure.Proofs.never_bad\" }\n" ++
         "]\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem never_bad : ∀ s : String, Core.NeverErrorKindPure ParseErr.kind ParseKind.bad (LeanSwe.MiniPure.parse s) := by\n" ++
         "  intro s; unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl; by_cases h : s.isEmpty <;> simp [h, Core.NeverErrorKindPure]\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg ParseErr.kind ParseErr.msg LeanSwe.MiniPure.parse LeanSwe.MiniPure.Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl LeanSwe.MiniPure.Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/RuntimeTests.lean")
        ("import Core.Assumptions\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_empty : IO Unit := do\n" ++
         "  match LeanSwe.MiniPure.parse \"\" with\n" ++
         "  | .error e => if e.kind != .empty then throw (IO.userError \"wrong kind\")\n" ++
         "  | .ok _ => throw (IO.userError \"expected error\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_empty\", mode := .real, run := test_err_empty }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls ++ "import LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "harness/Tests/Main.lean")
        "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  LeanSwe.MiniPure.RuntimeTests.runAll\n  Core.closeAssumpLog\n  return 0\n"
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/RuntimeTests", "LeanSwe", "Tests/Main"
      ]

    runPositiveCase base tmpRoot bin "obeys_model_step_from_finally_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : RawOpsM (StateM W)) (_ : Unit) : StateM W Nat := ops.getVal\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : PkgApiM (StateM W)) (_ : Unit) : StateM W Nat := api.readVal\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawOpsM m) : PkgApiM m :=\n" ++
         "  { readVal := do let v ← ops.getVal; pure v }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : PkgApiM IO := Internal.mkApiM { getVal := pure 0 }\n" ++
         "def readVal : IO Nat := defaultApi.readVal\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFromFinally id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  refine ⟨fun _ => rfl, ?_⟩\n" ++
         "  intro W proj raw hRaw w req hw\n" ++
         "  simpa [Model.execPkg, Internal.mkApiM, Model.execRaw, Model.rawAllowed, Model.pkgAllowed] using hRaw w req hw\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runPositiveCase base tmpRoot bin "obeys_model_conc_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : RawOpsM (StateM W)) (_ : Unit) : StateM W Nat := ops.getVal\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : PkgApiM (StateM W)) (_ : Unit) : StateM W Nat := api.readVal\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import Core.ConcOps\nimport LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkConcApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawOpsM m) (_ : Core.ConcOpsM m) : PkgApiM m :=\n" ++
         "  { readVal := ops.getVal }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import Core.ConcOps\nimport LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : PkgApiM IO := Internal.mkConcApiM { getVal := pure 0 } Core.ioConcOps\n" ++
         "def readVal : IO Nat := defaultApi.readVal\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport Core.ConcOps\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFromConc id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkConcApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  refine ⟨fun _ => rfl, ?_⟩\n" ++
         "  intro W proj raw conc hRaw _ w req hw\n" ++
         "  simpa [Model.execPkg, Internal.mkConcApiM, Model.execRaw, Model.rawAllowed, Model.pkgAllowed] using hRaw w req hw\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_model_conc_type_app_rejected" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : RawOpsM (StateM W)) (_ : Unit) : StateM W Nat := ops.getVal\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : PkgApiM (StateM W)) (_ : Unit) : StateM W Nat := api.readVal\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out s' : Nat) : Prop := out = s ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import Core.ConcOps\nimport LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkConcApiM {fd : Type} {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawOpsM m) (_ : Core.ConcOpsM m) : PkgApiM m :=\n" ++
         "  { readVal := do let _ := (fun (_ : fd) => ()); ops.getVal }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import Core.ConcOps\nimport LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : PkgApiM IO := @Internal.mkConcApiM UInt32 IO _ _ { getVal := pure 0 } Core.ioConcOps\n" ++
         "def readVal : IO Nat := defaultApi.readVal\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport Core.ConcOps\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFromConc id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf (@Internal.mkConcApiM Nat) Model.execPkg Model.pkgAllowed := by\n" ++
         "  refine ⟨fun _ => rfl, ?_⟩\n" ++
         "  intro W proj raw conc hRaw _ w req hw\n" ++
         "  simpa [Model.execPkg, Internal.mkConcApiM, Model.execRaw, Model.rawAllowed, Model.pkgAllowed] using hRaw w req hw\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runPositiveCase base tmpRoot bin "obeys_model_inverse_render_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def renderBool (b : Bool) (_ : Unit) : Option String := some (if b then \"true\" else \"false\")\n" ++
         "def wfBool (_ : Bool) : Prop := True\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (s : String) : Except InvErr Bool :=\n" ++
         "  if s == \"true\" then .ok true else if s == \"false\" then .ok false else .error { kind := .bad, msg := \"bad bool\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\nimport Core.Assumptions\n" ++
         "import LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\nopen Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n" ++
         "  let x ← nondet Nat\n  NondetTest.assert (fn x = Model.evalModel x)\n" ++
         "def errorCoverage : List (ErrorObligation InvKind) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.parseBool\", errorKind := .bad, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\" .real }\n" ++
         "]\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "private theorem renderBool_inj : Core.RenderInjectiveModulo Model.renderBool Eq := by\n" ++
         "  intro a b _ _ raw ha hb; cases a <;> cases b <;> simp [Model.renderBool] at ha hb <;> first | rfl | exact absurd (ha.trans hb.symm) (by decide)\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRender LeanSwe.MiniPure.parseBool Model.renderBool Model.wfBool Eq InvErr.msg := by\n" ++
         "  refine ⟨fun _ => rfl, Core.ObeysInverseRender.of_injective renderBool_inj ?_ ?_⟩\n" ++
         "  · intro raw out hp\n" ++
         "    unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
         "      · simp [h1, h2] at hp\n" ++
         "  · intro raw e hp\n" ++
         "    unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp\n" ++
         "      · simp [h1, h2] at hp; subst hp; refine ⟨by decide, ?_⟩; intro a _ hr; cases a <;> simp [Model.renderBool] at hr <;> exact absurd hr.symm (by assumption)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/RuntimeTests.lean")
        ("import Core.Assumptions\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_bad : IO Unit := do\n" ++
         "  match LeanSwe.MiniPure.parseBool \"nope\" with\n" ++
         "  | .error e => if e.kind != .bad then throw (IO.userError \"wrong kind\")\n" ++
         "  | .ok _ => throw (IO.userError \"expected error\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\", mode := .real, run := test_err_bad }\n" ++
         "]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\n" ++
         "end LeanSwe.MiniPure.RuntimeTests\n")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls ++ "import LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "harness/Tests/Main.lean")
        "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  LeanSwe.MiniPure.RuntimeTests.runAll\n  Core.closeAssumpLog\n  return 0\n"
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/RuntimeTests", "LeanSwe", "Tests/Main"
      ]

    runMutantCase base tmpRoot bin "duplicate_obeys_and_refines_rejected" "DUPLICATE_OBEYS_AND_REFINES_MODEL" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport Core.Refines\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\n" ++
         "theorem refines_model : Core.RefinesPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #["LeanSwe/MiniPure/Proofs", "LeanSwe"]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_const_kind_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure ParseErr where\n  code : Nat\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "def constKind (_ : ParseErr) : Nat := 0\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { code := 1, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { code := 99, msg := \"oops\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg constKind ParseErr.msg LeanSwe.MiniPure.parse LeanSwe.MiniPure.Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl LeanSwe.MiniPure.Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, constKind]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_pattern_match_enum_const_kind_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive EnumErr\n  | errA\n  | errB\n  deriving Repr, BEq, DecidableEq\n" ++
         "def matchConstKind : EnumErr → Nat\n  | .errA => 0\n  | .errB => 0\n" ++
         "def enumMsg : EnumErr → String\n  | .errA => \"a\"\n  | .errB => \"b\"\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except EnumErr Nat :=\n" ++
         "  if s.isEmpty then .error .errA else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except EnumErr Nat :=\n" ++
         "  if s.isEmpty then .error .errB else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except EnumErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg matchConstKind enumMsg LeanSwe.MiniPure.parse LeanSwe.MiniPure.Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl LeanSwe.MiniPure.Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, matchConstKind, enumMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_pattern_match_struct_const_kind_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive ParseKind\n  | empty\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "def sneakStructKind (e : ParseErr) : Nat :=\n  match e.kind with\n  | .empty => 0\n  | .bad => 0\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .bad, msg := \"oops\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg sneakStructKind ParseErr.msg LeanSwe.MiniPure.parse LeanSwe.MiniPure.Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl LeanSwe.MiniPure.Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, sneakStructKind]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_inverse_render_const_none_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def badRender : Bool → Unit → Option String\n  | true, _ => none\n  | false, _ => none\n" ++
         "def wfBool (_ : Bool) : Prop := True\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (_ : String) : Except InvErr Bool := .error { kind := .bad, msg := \"no\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRender LeanSwe.MiniPure.parseBool Model.badRender Model.wfBool Eq InvErr.msg := by\n" ++
         "  refine ⟨fun _ => rfl, fun _ => ?_⟩\n" ++
         "  refine ⟨by decide, fun a _ h => ?_⟩; cases a <;> simp [Model.badRender] at h\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_char_const_kind_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive CharErr\n  | io (c : Char)\n  | parse (c : Char)\n  deriving Repr, BEq, DecidableEq\n" ++
         "def constCharKind : CharErr → Nat\n  | .io _ => 0\n  | .parse _ => 0\n" ++
         "def charErrMsg : CharErr → String\n  | .io c => toString c\n  | .parse c => \"p\" ++ toString c\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except CharErr Nat :=\n" ++
         "  if s.isEmpty then .error (.io 'x') else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except CharErr Nat :=\n" ++
         "  if s.isEmpty then .error (.parse 'y') else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except CharErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg constCharKind charErrMsg LeanSwe.MiniPure.parse Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, constCharKind, charErrMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_unsampleable_field_fails_closed" "INCONCLUSIVE_REFINES_CHECK" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive FnErr\n  | io (f : Nat → Nat)\n  | parse (f : Nat → Nat)\n" ++
         "def constFnKind : FnErr → Nat\n  | .io _ => 0\n  | .parse _ => 0\n" ++
         "def fnErrMsg : FnErr → String\n  | .io _ => \"io\"\n  | .parse _ => \"parse\"\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except FnErr Nat :=\n" ++
         "  if s.isEmpty then .error (.io id) else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except FnErr Nat :=\n" ++
         "  if s.isEmpty then .error (.parse id) else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except FnErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg constFnKind fnErrMsg LeanSwe.MiniPure.parse Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, constFnKind, fnErrMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_inverse_render_tape_match_const_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "inductive MyTape\n  | t1\n  | t2\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def tapeConstRender (_ : Bool) (t : MyTape) : Option String :=\n  match t with\n  | .t1 => none\n  | .t2 => none\n" ++
         "def wfBool (_ : Bool) : Prop := True\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (_ : String) : Except InvErr Bool := .error { kind := .bad, msg := \"no\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRender LeanSwe.MiniPure.parseBool Model.tapeConstRender Model.wfBool Eq InvErr.msg := by\n" ++
         "  refine ⟨fun _ => rfl, fun _ => ?_⟩\n" ++
         "  refine ⟨by decide, fun _ t h => ?_⟩; cases t <;> simp [Model.tapeConstRender] at h\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_const_msg_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive ParseKind\n  | empty\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "def constMsg (_ : ParseErr) : String := \"x\"\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg ParseErr.kind constMsg LeanSwe.MiniPure.parse Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, constMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_proof_msg_rejected" "NON_MODEL_SPEC_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive ParseKind\n  | empty\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"nonempty\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "def proofMsg (e : ParseErr) : String := e.msg\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg ParseErr.kind proofMsg LeanSwe.MiniPure.parse Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, proofMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_upto_errmsg_private_proof_msg_rejected" "LAMBDA_OR_PARTIAL_APP_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive ParseKind\n  | empty\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat :=\n" ++
         "  if s.isEmpty then .error { kind := .empty, msg := \"nonempty\" } else .ok s.length\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "private def proofMsg (e : ParseErr) : String := e.msg\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysPureEqUpToErrMsg ParseErr.kind proofMsg LeanSwe.MiniPure.parse Model.parseModel := by\n" ++
         "  refine ⟨fun _ => rfl, fun s => ?_⟩\n" ++
         "  unfold LeanSwe.MiniPure.parse LeanSwe.MiniPure.Internal.parseImpl Model.parseModel\n" ++
         "  by_cases h : s.isEmpty <;> simp [h, Core.EqUpToErrMsg, proofMsg]\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_inverse_render_const_msg_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind\n  | bad\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "def constInvMsg (_ : InvErr) : String := \"x\"\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def renderBool (b : Bool) (_ : Unit) : Option String := some (if b then \"true\" else \"false\")\n" ++
         "def wfBool (_ : Bool) : Prop := True\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (s : String) : Except InvErr Bool :=\n" ++
         "  if s == \"true\" then .ok true else if s == \"false\" then .ok false else .error { kind := .bad, msg := \"\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "private theorem renderBool_inj : Core.RenderInjectiveModulo Model.renderBool Eq := by\n" ++
         "  intro a b _ _ raw ha hb; cases a <;> cases b <;> simp [Model.renderBool] at ha hb <;> first | rfl | exact absurd (ha.trans hb.symm) (by decide)\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRender LeanSwe.MiniPure.parseBool Model.renderBool Model.wfBool Eq constInvMsg := by\n" ++
         "  refine ⟨fun _ => rfl, Core.ObeysInverseRender.of_injective renderBool_inj ?_ ?_⟩\n" ++
         "  · intro raw out hp\n" ++
         "    unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
         "      · simp [h1, h2] at hp\n" ++
         "  · intro raw e hp\n" ++
         "    unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp\n" ++
         "      · simp [h1, h2] at hp; subst hp; refine ⟨by decide, ?_⟩; intro a _ hr; cases a <;> simp [Model.renderBool] at hr <;> exact absurd hr.symm (by assumption)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    let psOk ← runCmd bin.toString #[base.libDir.toString, base.root.toString, "--print-sig", "LeanSwe.MiniPure"]
    if psOk.exitCode != 0 ||
        (psOk.stdout.splitOn "Template for LeanSwe.MiniPure.Proofs.obeys_model").length <= 1 ||
        (psOk.stdout.splitOn "theorem obeys_model :").length <= 1 ||
        (psOk.stdout.splitOn "Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel").length <= 1 then
      throw (IO.userError s!"FAIL [print_sig_minipure_ok]: exit={psOk.exitCode}\nstdout={psOk.stdout}\nstderr={psOk.stderr}")
    IO.println "PASS [print_sig_minipure_ok] -> printed expected obeys_model template"

    do
      let psDir := tmpRoot / "print_sig_shapes"
      let repoCopy := psDir / "repo"
      let libCopy := psDir / "lib"
      IO.FS.createDirAll psDir
      copyDirTree base.root repoCopy
      copyDirTree base.libDir libCopy
      let lp := s!"{libCopy}:{base.leanPath}"
      writeFileCreatingParents (repoCopy / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "inductive ParseKind\n  | empty\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure ParseErr where\n  kind : ParseKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (repoCopy / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def parseModel (s : String) : Except ParseErr Nat := .ok s.length\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (repoCopy / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\n" ++
         "namespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseImpl (s : String) : Except ParseErr Nat := .ok s.length\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawOpsM m) : PkgApiM m := { readVal := ops.getVal }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (repoCopy / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parse (s : String) : Except ParseErr Nat := Internal.parseImpl s\n" ++
         "def zeroArg : Nat := 42\n" ++
         "def polyShow {α : Type} [ToString α] (x : α) : String := toString x\n" ++
         "def defaultApi : PkgApiM IO := Internal.mkApiM { getVal := pure 0 }\n" ++
         "def readVal : IO Nat := defaultApi.readVal\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (repoCopy / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      for m in #["LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
          "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"] do
        compileLeanMod repoCopy lp (repoCopy / s!"{m}.lean") (libCopy / s!"{m}.olean")
      let psShapes ← runCmd bin.toString #[libCopy.toString, repoCopy.toString, "--print-sig", "LeanSwe.MiniPure"]
      let st := psShapes.stdout
      let okShapes :=
        psShapes.exitCode == 0 &&
        (st.splitOn "Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel").length > 1 &&
        (st.splitOn "Core.ObeysPureEqUpToErrMsg LeanSwe.MiniPure.ParseErr.kind LeanSwe.MiniPure.ParseErr.msg LeanSwe.MiniPure.parse Model.parseModel").length > 1 &&
        (st.splitOn "<MANUAL_TEMPLATE_ARITY_0: LeanSwe.MiniPure.zeroArg").length > 1 &&
        (st.splitOn "<MANUAL_TEMPLATE_POLY: LeanSwe.MiniPure.polyShow").length > 1 &&
        (st.splitOn "Core.ObeysStepFromFinally <MAP_S> <RAW_WF> <EXEC_RAW> <RAW_ALLOWED> <PKG_WF> LeanSwe.MiniPure.Internal.mkApiM <EXEC_PKG> <PKG_ALLOWED>").length > 1 &&
        (st.splitOn "Model.rawStepWf").length == 1
      if !okShapes then
        throw (IO.userError s!"FAIL [print_sig_shapes_ok]: exit={psShapes.exitCode}\nstdout={st}\nstderr={psShapes.stderr}")
      IO.println "PASS [print_sig_shapes_ok] -> Except, 0-arg, poly, and effectful placeholders verified"
      IO.FS.removeDirAll psDir

    expectFailureCode bin "print_sig_unknown_pkg_rejected" "UNKNOWN_PACKAGE_FOR_PRINT_SIG"
      base.libDir base.root #["--print-sig", "LeanSwe.DoesNotExist"]

    runPositiveCase base tmpRoot bin "obeys_iface_combinator_ok" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure LeafOpsM (m : Type → Type) where\n  ping : Nat → m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def leafWf (_ : Nat) : Bool := true\n" ++
         "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
         "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "abbrev PingPairFn (m : Type → Type) : Type := Option Nat × Nat → m (Nat × Nat)\n" ++
         "def execPingPair {W : Type} (fn : PingPairFn (StateM W)) (req : Option Nat × Nat) : StateM W (Nat × Nat) := fn req\n" ++
         "def allowedPingPair (s : Nat) (req : Option Nat × Nat) (out : Nat × Nat) (s' : Nat) : Prop := out = (req.2, req.2 + 1) ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkOpsM {m : Type → Type} [Monad m] (raw : LeafOpsM m) : LeafOpsM m := { ping := raw.ping }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : LeafOpsM IO := Internal.mkOpsM { ping := pure }\n" ++
         "def pingPair {m : Type → Type} [Monad m] {fd : Type} (ops : LeafOpsM m) (req : Option fd × Nat) : m (Nat × Nat) := do\n" ++
         "  let a ← ops.ping req.2\n  return (a, a + 1)\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf Internal.mkOpsM Model.execLeaf Model.allowedLeaf ∧\n" ++
         "    Core.ObeysStepFrom (PkgApi := Model.PingPairFn) id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf LeanSwe.MiniPure.pingPair Model.execPingPair Model.allowedPingPair :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ h => h, fun _ ops h w req hw => by\n" ++
         "    have hs := h w req.2 hw\n" ++
         "    dsimp only [Function.comp, id, Model.execLeaf, Model.allowedLeaf, Model.execPingPair, LeanSwe.MiniPure.pingPair, Model.allowedPingPair, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hs ⊢\n" ++
         "    rcases hc : ops.ping req.2 w with ⟨v, w'⟩\n" ++
         "    rw [hc] at hs\n" ++
         "    dsimp only at hs ⊢\n" ++
         "    exact ⟨by rw [hs.1], hs.2⟩⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_iface_combinator_fake_exec_rejected" "INCOMPLETE_INTERFACE_REFINEMENT" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\n" ++
         "structure PureCfg where\n  delta : Nat\n" ++
         "structure LeafOpsM (m : Type → Type) where\n  ping : Nat → m Nat\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def leafWf (_ : Nat) : Bool := true\n" ++
         "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
         "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "abbrev PingPairFn (m : Type → Type) : Type := Nat → m (Nat × Nat)\n" ++
         "def execPingPairFake {W : Type} (_ : PingPairFn (StateM W)) (n : Nat) : StateM W (Nat × Nat) := pure (n, n + 1)\n" ++
         "def allowedPingPair (s req : Nat) (out : Nat × Nat) (s' : Nat) : Prop := out = (req, req + 1) ∧ s' = s\n" ++
         "end LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkOpsM {m : Type → Type} [Monad m] (raw : LeafOpsM m) : LeafOpsM m := { ping := raw.ping }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : LeafOpsM IO := Internal.mkOpsM { ping := pure }\n" ++
         "def pingPair {m : Type → Type} [Monad m] (ops : LeafOpsM m) (n : Nat) : m (Nat × Nat) := do\n" ++
         "  let a ← ops.ping n\n  return (a, a + 99)\n" ++
         "end LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.Interface\nimport LeanSwe.MiniPure.SpecTests\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf Internal.mkOpsM Model.execLeaf Model.allowedLeaf ∧\n" ++
         "    Core.ObeysStepFrom (PkgApi := Model.PingPairFn) id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf LeanSwe.MiniPure.pingPair Model.execPingPairFake Model.allowedPingPair :=\n" ++
         "  ⟨fun _ => rfl, fun _ _ h => h, fun _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runPositiveCase base tmpRoot bin "obeys_inverse_render_within_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind | bad deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def renderBool (b : Bool) (pad : Bool) : Option String :=\n" ++
         "  some ((if pad then \" \" else \"\") ++ (if b then \"true\" else \"false\"))\n" ++
         "def withinBool (pad : Bool) : Prop := pad = false\n" ++
         "def wfBool (_ : Bool) : Prop := True\nend LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (s : String) : Except InvErr Bool :=\n" ++
         "  if s == \"true\" then .ok true else if s == \"false\" then .ok false else .error { kind := .bad, msg := \"bad\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\nimport Core.Assumptions\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\nopen Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (fn x = Model.evalModel x)\n" ++
         "def errorCoverage : List (ErrorObligation InvKind) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.parseBool\", errorKind := .bad, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\" .real }\n]\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "private theorem renderBool_inj : Core.RenderInjectiveModulo Model.renderBool Eq := by\n" ++
         "  intro a b p1 p2 raw ha hb; cases a <;> cases b <;> cases p1 <;> cases p2 <;> simp [Model.renderBool] at ha hb <;> first | rfl | exact absurd (ha.trans hb.symm) (by decide)\n" ++
         "theorem obeys_model :\n    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRenderWithin LeanSwe.MiniPure.parseBool Model.renderBool Model.withinBool Model.wfBool Eq InvErr.msg := by\n" ++
         "  refine ⟨fun _ => rfl, Core.ObeysInverseRenderWithin.of_injective renderBool_inj ?_ ?_⟩\n" ++
         "  · intro raw out hp; unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp; subst hp; exact ⟨trivial, ⟨false, rfl⟩⟩\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp; subst hp; exact ⟨trivial, ⟨false, rfl⟩⟩\n" ++
         "      · simp [h1, h2] at hp\n" ++
         "  · intro raw e hp; unfold LeanSwe.MiniPure.parseBool LeanSwe.MiniPure.Internal.parseBoolImpl at hp\n" ++
         "    by_cases h1 : raw = \"true\"\n" ++
         "    · subst h1; simp at hp\n" ++
         "    · by_cases h2 : raw = \"false\"\n" ++
         "      · subst h2; simp at hp\n" ++
         "      · simp [h1, h2] at hp; subst hp; refine ⟨by decide, fun a p hr hlim => ?_⟩; rw [Model.withinBool] at hlim; subst hlim; cases a <;> simp [Model.renderBool] at hr <;> exact absurd hr.symm (by assumption)\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/RuntimeTests.lean")
        ("import Core.Assumptions\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_bad : IO Unit := do\n  match LeanSwe.MiniPure.parseBool \"nope\" with\n  | .error e => if e.kind != .bad then throw (IO.userError \"wrong\")\n  | .ok _ => throw (IO.userError \"expected err\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[{ testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\", mode := .real, run := test_err_bad }]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\nend LeanSwe.MiniPure.RuntimeTests\n")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean") (ls ++ "import LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "harness/Tests/Main.lean")
        "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  LeanSwe.MiniPure.RuntimeTests.runAll\n  Core.closeAssumpLog\n  return 0\n"
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/RuntimeTests", "LeanSwe", "Tests/Main"
      ]

    runMutantCase base tmpRoot bin "obeys_inverse_render_within_vacuous_limits_rejected" "VACUOUS_WITHIN_LIMITS_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind | bad deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def evalModel (n : Nat) : Nat := n + 1\n" ++
         "def renderBool (b : Bool) (_ : Unit) : Option String := some (if b then \"true\" else \"false\")\n" ++
         "def vacWithin (_ : Unit) : Prop := False\n" ++
         "def wfBool (_ : Bool) : Prop := True\nend LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def parseBoolImpl (_ : String) : Except InvErr Bool := .error { kind := .bad, msg := \"bad\" }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := Internal.parseBoolImpl s\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\nimport Core.Assumptions\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\nopen Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let x ← nondet Nat\n  NondetTest.assert (fn x = Model.evalModel x)\n" ++
         "def errorCoverage : List (ErrorObligation InvKind) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.parseBool\", errorKind := .bad, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\" .real }\n]\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysInverseRenderWithin LeanSwe.MiniPure.parseBool Model.renderBool Model.vacWithin Model.wfBool Eq InvErr.msg :=\n" ++
         "  ⟨fun _ => rfl, fun _ => ⟨by decide, fun _ _ _ h => h⟩⟩\nend LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runPositiveCase base tmpRoot bin "obeys_model_step_from_except_accepted" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : RawOpsM (ExceptT IO.Error (StateM W))) (_ : Unit) : ExceptT IO.Error (StateM W) Nat := ops.getVal\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out : Except IO.Error Nat) (s' : Nat) : Prop := out = .ok s ∧ s' = s\n" ++
         "inductive PkgOut where | res (v : Nat)\n" ++
         "def execPkg {W : Type} (api : PkgApiM (ExceptT IO.Error (StateM W))) (_ : Unit) : ExceptT IO.Error (StateM W) PkgOut := .res <$> api.readVal\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out : Except IO.Error PkgOut) (s' : Nat) : Prop :=\n" ++
         "  match out with | .ok (.res r) => r = s ∧ s' = s | .error _ => False\nend LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] [MonadExceptOf IO.Error m] (ops : RawOpsM m) : PkgApiM m :=\n" ++
         "  { readVal := tryCatch ops.getVal (fun _ => pure 0) }\nend LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : PkgApiM IO := Internal.mkApiM { getVal := pure 0 }\ndef readVal : IO Nat := defaultApi.readVal\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFromExcept id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  refine ⟨fun _ => rfl, ?_⟩\n  intro W proj raw hRaw w req hw\n  have hr := hRaw w () hw\n" ++
         "  dsimp only [Function.comp, id, Model.execRaw, Model.rawAllowed, Model.execPkg, Model.pkgAllowed, Internal.mkApiM] at hr ⊢\n" ++
         "  change match (ExceptT.map Model.PkgOut.res (ExceptT.tryCatch raw.getVal (fun _ => pure 0)) w).1 with | Except.ok (Model.PkgOut.res r) => r = proj w ∧ proj (ExceptT.map Model.PkgOut.res (ExceptT.tryCatch raw.getVal (fun _ => pure 0)) w).2 = proj w | Except.error _ => False\n" ++
         "  unfold ExceptT.map ExceptT.tryCatch; dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk] at hr ⊢\n" ++
         "  cases hg : raw.getVal w with | mk rv w1 => rw [hg] at hr; rcases hr with ⟨rfl, hw1⟩; exact ⟨rfl, hw1⟩\nend LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    runMutantCase base tmpRoot bin "obeys_model_step_from_except_inner_vacuous_rejected" "TRIVIAL_ALLOWED_IN_REFINES" fun mr => do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\n" ++
         "structure RawOpsM (m : Type → Type) where\n  getVal : m Nat\n" ++
         "structure PkgApiM (m : Type → Type) where\n  readVal : m Nat\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef rawWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : RawOpsM (ExceptT IO.Error (StateM W))) (_ : Unit) : ExceptT IO.Error (StateM W) Nat := ops.getVal\n" ++
         "def rawAllowed (s : Nat) (_ : Unit) (out : Except IO.Error Nat) (s' : Nat) : Prop := out = .ok s ∧ s' = s\n" ++
         "inductive PkgOut where | res (v : Nat)\n" ++
         "def execPkg {W : Type} (api : PkgApiM (ExceptT IO.Error (StateM W))) (_ : Unit) : ExceptT IO.Error (StateM W) PkgOut := .res <$> api.readVal\n" ++
         "def pkgAllowed (s : Nat) (_ : Unit) (out : Except IO.Error PkgOut) (s' : Nat) : Prop :=\n" ++
         "  match out with | .ok (.res _) => s' = s | .error _ => False\nend LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\n" ++
         "def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] [MonadExceptOf IO.Error m] (ops : RawOpsM m) : PkgApiM m :=\n" ++
         "  { readVal := tryCatch ops.getVal (fun _ => pure 0) }\nend LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "def defaultApi : PkgApiM IO := Internal.mkApiM { getVal := pure 0 }\ndef readVal : IO Nat := defaultApi.readVal\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem proof_minipure : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches LeanSwe.MiniPure.eval) := fun _ => ⟨rfl, trivial⟩\n" ++
         "theorem obeys_model :\n    Core.ObeysPureEq LeanSwe.MiniPure.eval Model.evalModel ∧\n" ++
         "    Core.ObeysStepFromExcept id Model.rawWf Model.execRaw Model.rawAllowed Model.rawWf Internal.mkApiM Model.execPkg Model.pkgAllowed := by\n" ++
         "  refine ⟨fun _ => rfl, ?_⟩\n  intro W proj raw hRaw w req hw\n  have hr := hRaw w () hw\n" ++
         "  dsimp only [Function.comp, id, Model.execRaw, Model.rawAllowed, Model.execPkg, Model.pkgAllowed, Internal.mkApiM] at hr ⊢\n" ++
         "  change match (ExceptT.map Model.PkgOut.res (ExceptT.tryCatch raw.getVal (fun _ => pure 0)) w).1 with | Except.ok (Model.PkgOut.res _) => proj (ExceptT.map Model.PkgOut.res (ExceptT.tryCatch raw.getVal (fun _ => pure 0)) w).2 = proj w | Except.error _ => False\n" ++
         "  unfold ExceptT.map ExceptT.tryCatch; dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk] at hr ⊢\n" ++
         "  cases hg : raw.getVal w with | mk rv w1 => rw [hg] at hr; rcases hr with ⟨rfl, hw1⟩; exact hw1\nend LeanSwe.MiniPure.Proofs\n")
      return #[
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs", "LeanSwe"
      ]

    let writePureFromSetup (mr : MiniRepo) (numModelExtra : String) (docProofsBody : String) : IO (Array String) := do
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/Types.lean")
        "namespace LeanSwe.MiniDep\nstructure NumApi where\n  fmt : Nat → Nat\nend LeanSwe.MiniDep\n"
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/Model.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniDep.Types\nnamespace LeanSwe.MiniDep.Model\n" ++
         "def fmtModel (n : Nat) : Nat := n + 1\n" ++
         numModelExtra ++ "\nend LeanSwe.MiniDep.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/Impl.lean")
        ("import LeanSwe.MiniDep.Types\nnamespace LeanSwe.MiniDep.Internal\n" ++
         "def fmtImpl (n : Nat) : Nat := n + 1\ndef defaultApi : NumApi := { fmt := fmtImpl }\nend LeanSwe.MiniDep.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/Interface.lean")
        ("import LeanSwe.MiniDep.Impl\nnamespace LeanSwe.MiniDep\n" ++
         "def defaultApi : NumApi := Internal.defaultApi\ndef fmt (n : Nat) : Nat := defaultApi.fmt n\nend LeanSwe.MiniDep\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/SpecTests.lean")
        ("import Core.NondetTest\nimport LeanSwe.MiniDep.Model\nimport LeanSwe.MiniDep.Interface\nnamespace LeanSwe.MiniDep\n" ++
         "open Core Core.NondetTest\ndef test_minidep {r} [NondetTest r] (fn : Nat → Nat) : r Unit := do\n  let n ← nondet Nat\n  NondetTest.assert (Model.allowedFmt n (fn n))\nend LeanSwe.MiniDep\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniDep/Proofs.lean")
        ("import Core.Obeys\nimport LeanSwe.MiniDep.SpecTests\nnamespace LeanSwe.MiniDep.Proofs\n" ++
         "theorem proof_minidep : Core.AllPass (LeanSwe.MiniDep.test_minidep LeanSwe.MiniDep.fmt) := fun n => ⟨by simp [Model.allowedFmt, LeanSwe.MiniDep.fmt, LeanSwe.MiniDep.defaultApi, Internal.defaultApi, Internal.fmtImpl], trivial⟩\n" ++
         "theorem obeys_model : Core.ObeysPure LeanSwe.MiniDep.fmt Model.allowedFmt := fun n => by simp [Model.allowedFmt, LeanSwe.MiniDep.fmt, LeanSwe.MiniDep.defaultApi, Internal.defaultApi, Internal.fmtImpl]\nend LeanSwe.MiniDep.Proofs\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Types.lean")
        ("namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\n" ++
         "inductive InvKind | zero | bad deriving Repr, BEq, DecidableEq\n" ++
         "structure InvErr where\n  kind : InvKind\n  msg : String\n  deriving Repr, BEq, DecidableEq\n" ++
         "structure PureApi where\n  eval : Nat → Nat\n  parseBool : String → Except InvErr Bool\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Model.lean")
        ("import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\n" ++
         "def allowedEval (n out : Nat) : Prop := out = n + 1\n" ++
         "def renderBool (b : Bool) (_ : Unit) : Option String := some (if b then \"1\" else \"0\")\n" ++
         "def wfBool (_ : Bool) : Prop := True\nend LeanSwe.MiniPure.Model\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Impl.lean")
        ("import LeanSwe.MiniDep.Types\nimport LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\n" ++
         "def mkApi (num : LeanSwe.MiniDep.NumApi) : PureApi :=\n" ++
         "  { eval := num.fmt\n" ++
         "  , parseBool := fun s => if s == \"1\" && num.fmt 0 == 1 then .ok true else if s == \"0\" && num.fmt 0 == 1 then .ok false else if s.isEmpty then .error { kind := .zero, msg := \"empty\" } else .error { kind := .bad, msg := \"bad\" } }\n" ++
         "end LeanSwe.MiniPure.Internal\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniDep.Interface\nimport LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n" ++
         "def defaultApi : PureApi := Internal.mkApi LeanSwe.MiniDep.defaultApi\n" ++
         "def eval (n : Nat) : Nat := defaultApi.eval n\n" ++
         "def parseBool (s : String) : Except InvErr Bool := defaultApi.parseBool s\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/SpecTests.lean")
        ("import Core.NondetTest\nimport Core.Assumptions\nimport LeanSwe.MiniDep.Model\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure\nopen Core Core.NondetTest\n" ++
         "def test_minipure_matches {r} [NondetTest r] (mk : LeanSwe.MiniDep.NumApi → PureApi) (num : LeanSwe.MiniDep.NumApi) : r Unit := do\n  assume (LeanSwe.MiniDep.Model.ObeysApi num)\n  let x ← nondet Nat\n  NondetTest.assert ((mk num).eval x = x + 1)\n" ++
         "def errorCoverage : List (ErrorObligation InvKind) := [\n" ++
         "  { request := \"LeanSwe.MiniPure.parseBool\", errorKind := .zero, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\" .real },\n" ++
         "  { request := \"LeanSwe.MiniPure.parseBool\", errorKind := .bad, justification := .tested \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\" .real }\n]\nend LeanSwe.MiniPure\n")
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/Proofs.lean") docProofsBody
      writeFileCreatingParents (mr.root / "LeanSwe/MiniPure/RuntimeTests.lean")
        ("import Core.Assumptions\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.RuntimeTests\n" ++
         "def test_err_zero : IO Unit := do\n  match LeanSwe.MiniPure.parseBool \"\" with\n  | .error e => if e.kind != .zero then throw (IO.userError \"wrong\")\n  | .ok _ => throw (IO.userError \"expected err\")\n" ++
         "def test_err_bad : IO Unit := do\n  match LeanSwe.MiniPure.parseBool \"nope\" with\n  | .error e => if e.kind != .bad then throw (IO.userError \"wrong\")\n  | .ok _ => throw (IO.userError \"expected err\")\n" ++
         "def registeredErrorTests : Array Core.RegisteredErrorTest := #[\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_zero\", mode := .real, run := test_err_zero },\n" ++
         "  { testName := \"LeanSwe.MiniPure.RuntimeTests.test_err_bad\", mode := .real, run := test_err_bad }]\n" ++
         "def runAll : IO Unit := Core.runRegisteredErrorTests registeredErrorTests\nend LeanSwe.MiniPure.RuntimeTests\n")
      let ls ← IO.FS.readFile (mr.root / "LeanSwe.lean")
      writeFileCreatingParents (mr.root / "LeanSwe.lean")
        (ls ++ "import LeanSwe.MiniDep.SpecTests\nimport LeanSwe.MiniDep.Proofs\nimport LeanSwe.MiniPure.RuntimeTests\n")
      writeFileCreatingParents (mr.root / "harness/Tests/Main.lean")
        "import Core.Assumptions\nimport LeanSwe\ndef main (_ : List String) : IO UInt32 := do\n  Core.initAssumpLog \"a\" \"b\"\n  LeanSwe.MiniPure.RuntimeTests.runAll\n  Core.closeAssumpLog\n  return 0\n"
      return #[
        "LeanSwe/MiniDep/Types", "LeanSwe/MiniDep/Model", "LeanSwe/MiniDep/Impl",
        "LeanSwe/MiniDep/Interface", "LeanSwe/MiniDep/SpecTests", "LeanSwe/MiniDep/Proofs",
        "LeanSwe/MiniPure/Types", "LeanSwe/MiniPure/Model", "LeanSwe/MiniPure/Impl",
        "LeanSwe/MiniPure/Interface", "LeanSwe/MiniPure/SpecTests", "LeanSwe/MiniPure/Proofs",
        "LeanSwe/MiniPure/RuntimeTests", "LeanSwe", "Tests/Main"
      ]

    let compliantDocProofs :=
      "import Core.Obeys\nimport LeanSwe.MiniPure.SpecTests\nnamespace LeanSwe.MiniPure.Proofs\n" ++
      "theorem proof_minipure (num : LeanSwe.MiniDep.NumApi) : Core.AllPass (LeanSwe.MiniPure.test_minipure_matches Internal.mkApi num) := fun h n => ⟨h n, trivial⟩\n" ++
      "theorem reach_minipure : Core.CanReach (LeanSwe.MiniPure.test_minipure_matches Internal.mkApi { fmt := fun n => n + 1 }) := ⟨fun _ => rfl, 0, rfl, trivial⟩\n" ++
      "private theorem renderBool_inj : Core.RenderInjectiveModulo Model.renderBool Eq := by\n" ++
      "  intro a b _ _ raw ha hb; cases a <;> cases b <;> simp [Model.renderBool] at ha hb <;> first | rfl | exact absurd (ha.trans hb.symm) (by decide)\n" ++
      "theorem obeys_model :\n" ++
      "    Core.ObeysPureFrom LeanSwe.MiniDep.Model.ObeysApi Internal.mkApi PureApi.eval Model.allowedEval ∧\n" ++
      "    Core.ObeysInverseRenderFrom LeanSwe.MiniDep.Model.ObeysApi Internal.mkApi PureApi.parseBool Model.renderBool Model.wfBool Eq InvErr.msg := by\n" ++
      "  refine ⟨fun _ h n => h n, fun num hnum => Core.ObeysInverseRender.of_injective renderBool_inj ?_ ?_⟩\n" ++
      "  · intro raw out hp; have h0 : num.fmt 0 = 1 := hnum 0; simp [Internal.mkApi, h0] at hp\n" ++
      "    by_cases h1 : raw = \"1\"\n" ++
      "    · subst h1; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
      "    · by_cases h2 : raw = \"0\"\n" ++
      "      · subst h2; simp at hp; subst hp; exact ⟨trivial, ⟨(), rfl⟩⟩\n" ++
      "      · by_cases he : raw = \"\" <;> simp [h1, h2, he] at hp\n" ++
      "  · intro raw e hp; have h0 : num.fmt 0 = 1 := hnum 0; simp [Internal.mkApi, h0] at hp\n" ++
      "    by_cases h1 : raw = \"1\"\n" ++
      "    · subst h1; simp at hp\n" ++
      "    · by_cases h2 : raw = \"0\"\n" ++
      "      · subst h2; simp at hp\n" ++
      "      · by_cases he : raw = \"\" <;> simp [h1, h2, he] at hp <;> subst hp <;> refine ⟨by decide, fun a _ hr => ?_⟩ <;> cases a <;> simp [Model.renderBool] at hr <;> exact absurd hr.symm (by assumption)\n" ++
      "end LeanSwe.MiniPure.Proofs\n"

    runPositiveCase base tmpRoot bin "obeys_pure_from_and_inv_from_accepted" fun mr =>
      writePureFromSetup mr
        ("def allowedFmt (n out : Nat) : Prop := out = n + 1\n" ++
         "def ObeysApi (api : NumApi) : Prop := Core.ObeysPure api.fmt allowedFmt\n" ++
         "def modelApi : NumApi := { fmt := fun n => n + 1 }\n" ++
         "theorem obeysApi_satisfiable : ∃ api : NumApi, ObeysApi api := ⟨modelApi, fun _ => rfl⟩")
        compliantDocProofs

    runMutantCase base tmpRoot bin "obeys_pure_from_obeys_mismatch_rejected" "PURE_FROM_OBEYS_MISMATCH" fun mr =>
      writePureFromSetup mr
        ("def allowedFmt (n out : Nat) : Prop := out ≥ n\n" ++
         "def ObeysApi (api : NumApi) : Prop := ∀ n, api.fmt n = n + 1\n" ++
         "def modelApi : NumApi := { fmt := fun n => n + 1 }\n" ++
         "theorem obeysApi_satisfiable : ∃ api : NumApi, ObeysApi api := ⟨modelApi, fun _ => rfl⟩")
        compliantDocProofs

    runMutantCase base tmpRoot bin "obeys_pure_from_missing_witness_rejected" "MISSING_PURE_FROM_WITNESS" fun mr =>
      writePureFromSetup mr
        ("def allowedFmt (n out : Nat) : Prop := out = n + 1\n" ++
         "def ObeysApi (api : NumApi) : Prop := Core.ObeysPure api.fmt allowedFmt")
        compliantDocProofs

    expectFailureCode bin "inconclusive_dead_branch_fails_closed" "INCONCLUSIVE_DEAD_BRANCH_CHECK"
      base.libDir base.root #["--allow-legacy", "--dead-branch-fuel", "0"]

    runCentralCoverageSelfTests base tmpRoot bin
    runHarnessParitySelfTests tmpRoot realRepo
    runImportDagSelfTests tmpRoot realRepo realLib

    IO.FS.removeDirAll tmpRoot
    IO.println "CHECK_ASSUMPTIONS_SELFTEST_OK: all Core.Refines, retirement, harness parity, and import-DAG cases verified"
    return 0
  catch err =>
    let _ ← try IO.FS.removeDirAll tmpRoot catch _ => pure ()
    IO.eprintln s!"CHECK_ASSUMPTIONS_SELFTEST_FAILED: {err}"
    return 1
