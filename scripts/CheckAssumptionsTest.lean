import Lean

/-!
Focused positive and negative mutant self-test suite (`scripts/CheckAssumptionsTest.lean`)
for `Core.Refines` model-refinement verification and `RuntimeTests` retirement checks in
`scripts/CheckAssumptions.lean`.

Compiles `scripts/CheckAssumptions.lean` once into an isolated `/tmp` workspace, verifies a clean
miniature baseline (`errors=0`) over pure and boundary packages (constraining all inputs), verifies
positive polymorphic and `RefinesStepFrom` fixtures, and injects mutants verifying that every
`Core.Refines` and retirement violation fails with non-zero exit status and the expected diagnostic.
All `/tmp` artifacts are removed unconditionally on exit.
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

/-- Execute self-tests for `Core.Refines` and boundary retirement checks in `scripts/CheckAssumptions.lean`. -/
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

    expectFailureCode bin "inconclusive_dead_branch_fails_closed" "INCONCLUSIVE_DEAD_BRANCH_CHECK"
      base.libDir base.root #["--allow-legacy", "--dead-branch-fuel", "0"]

    IO.FS.removeDirAll tmpRoot
    IO.println "CHECK_ASSUMPTIONS_SELFTEST_OK: all Core.Refines and boundary retirement mutant cases verified"
    return 0
  catch err =>
    let _ ← try IO.FS.removeDirAll tmpRoot catch _ => pure ()
    IO.eprintln s!"CHECK_ASSUMPTIONS_SELFTEST_FAILED: {err}"
    return 1
