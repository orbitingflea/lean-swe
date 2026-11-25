import Lean

/-!
Positive and negative synthetic `.olean` self-test suite (`scripts/CheckPromisesTest.lean`) for
the manifest-driven `obeys_model` presence/non-vacuity gate, generalized `.olean` wiring /
middle-hook ban, mechanical `.olean` `Expr` synthesis + reducible `isDefEq` verification, and
`--print-obeys-sig` CLI rendering in `scripts/CheckPromises.lean`.
-/

private def writeFileCreatingParents (p : System.FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then IO.FS.createDirAll parent
  IO.FS.writeFile p content

private def runCmd (cmd : String) (args : Array String) (cwd? : Option System.FilePath := none)
    (extraEnv : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := cwd?, env := extraEnv }

private def compileLeanMod (repoRoot : System.FilePath) (leanPath : String)
    (src olean : System.FilePath) : IO Unit := do
  if let some parent := olean.parent then IO.FS.createDirAll parent
  let out ← runCmd "lean" #["-R", repoRoot.toString, "-o", olean.toString, src.toString]
    none #[("LEAN_SRC_PATH", some repoRoot.toString), ("LEAN_PATH", some leanPath)]
  if out.exitCode != 0 then
    throw (IO.userError s!"lean compile failed for {src}:\n{out.stdout}\n{out.stderr}")

private def buildCheckPromisesBin (tmpRoot : System.FilePath) : IO System.FilePath := do
  let cFile := tmpRoot / "CheckPromises.c"
  let binFile := tmpRoot / "check-promises"
  let r1 ← runCmd "lean" #["-c", cFile.toString, "scripts/CheckPromises.lean"]
  if r1.exitCode != 0 then
    throw (IO.userError s!"failed to compile CheckPromises.lean to C:\n{r1.stdout}\n{r1.stderr}")
  let r2 ← runCmd "leanc" #["-O2", cFile.toString, "-o", binFile.toString, "-lleanshared"]
  if r2.exitCode != 0 then
    throw (IO.userError s!"failed to link check-promises binary:\n{r2.stdout}\n{r2.stderr}")
  return binFile

private def symlinkCoreLib (realLibDir targetLibDir : System.FilePath) : IO Unit := do
  let r1 ← runCmd "ln" #["-sfn", (realLibDir / "Core").toString, (targetLibDir / "Core").toString]
  if r1.exitCode != 0 then throw (IO.userError s!"ln Core failed: {r1.stderr}")
  if ← (realLibDir / "Core.olean").pathExists then
    let r2 ← runCmd "ln" #["-sfn", (realLibDir / "Core.olean").toString, (targetLibDir / "Core.olean").toString]
    if r2.exitCode != 0 then throw (IO.userError s!"ln Core.olean failed: {r2.stderr}")

private def baselineManifestJson : String :=
  "{\n  \"version\": 1,\n  \"packages\": {\n" ++
  "    \"LeanSwe.MiniPure\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false, \"spec_style\": \"pure_eq\"},\n" ++
  "    \"LeanSwe.MiniErrMsg\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false, \"err_msg_opaque\": true, \"spec_style\": \"pure_eq\"},\n" ++
  "    \"LeanSwe.MiniInv\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false, \"err_msg_opaque\": true, \"spec_style\": \"inverse_render\"},\n" ++
  "    \"LeanSwe.MiniProp\": {\"kind\": \"property\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false},\n" ++
  "    \"LeanSwe.MiniLeaf\": {\"kind\": \"model\", \"purity\": \"nondet_io\", \"deps\": [], \"external_boundary\": true, \"fuzz_suite\": \"minileaf\", \"spec_style\": \"state_step\"},\n" ++
  "    \"LeanSwe.MiniComp\": {\"kind\": \"model\", \"purity\": \"mixed\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": false, \"spec_style\": \"state_step\"}\n" ++
  "  }\n}\n"

private def baselineFiles : Array (String × String) := #[
  ("LeanSwe/MiniPure/Types.lean",
    "namespace LeanSwe.MiniPure\nstructure PureCfg where\n  delta : Nat\nend LeanSwe.MiniPure\n"),
  ("LeanSwe/MiniPure/Model.lean",
    "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\nend LeanSwe.MiniPure.Model\n"),
  ("LeanSwe/MiniPure/Impl.lean",
    "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Internal\ndef evalImpl (n : Nat) : Nat := n + 1\nend LeanSwe.MiniPure.Internal\n"),
  ("LeanSwe/MiniPure/Interface.lean",
    "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\ndef eval (n : Nat) : Nat := Internal.evalImpl n\nend LeanSwe.MiniPure\n"),
  ("LeanSwe/MiniPure/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\n" ++
    "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n"),
  ("LeanSwe/MiniErrMsg/Types.lean",
    "namespace LeanSwe.MiniErrMsg\ninductive ErrKind where | zero deriving DecidableEq\nstructure MiniErr where\n  kind : ErrKind\n  message : String\nend LeanSwe.MiniErrMsg\n"),
  ("LeanSwe/MiniErrMsg/Model.lean",
    "import LeanSwe.MiniErrMsg.Types\nnamespace LeanSwe.MiniErrMsg.Model\n" ++
    "def check (n : Nat) : Except MiniErr Nat := if n == 0 then .error { kind := .zero, message := \"model\" } else .ok n\nend LeanSwe.MiniErrMsg.Model\n"),
  ("LeanSwe/MiniErrMsg/Impl.lean",
    "import LeanSwe.MiniErrMsg.Types\nnamespace LeanSwe.MiniErrMsg.Internal\n" ++
    "def checkImpl (n : Nat) : Except MiniErr Nat := if n == 0 then .error { kind := .zero, message := \"impl\" } else .ok n\nend LeanSwe.MiniErrMsg.Internal\n"),
  ("LeanSwe/MiniErrMsg/Interface.lean",
    "import LeanSwe.MiniErrMsg.Impl\nnamespace LeanSwe.MiniErrMsg\ndef check (n : Nat) : Except MiniErr Nat := Internal.checkImpl n\nend LeanSwe.MiniErrMsg\n"),
  ("LeanSwe/MiniErrMsg/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniErrMsg.Model\nimport LeanSwe.MiniErrMsg.Interface\nnamespace LeanSwe.MiniErrMsg.Proofs\n" ++
    "theorem obeys_model : Core.ObeysPureEqUpToErrMsg MiniErr.kind MiniErr.message LeanSwe.MiniErrMsg.check LeanSwe.MiniErrMsg.Model.check := by\n" ++
    "  intro n; cases n with | zero => exact ⟨rfl, by decide⟩ | succ _ => rfl\nend LeanSwe.MiniErrMsg.Proofs\n"),
  ("LeanSwe/MiniInv/Types.lean",
    "namespace LeanSwe.MiniInv\nstructure InvErr where\n  message : String\nend LeanSwe.MiniInv\n"),
  ("LeanSwe/MiniInv/Model.lean",
    "import LeanSwe.MiniInv.Types\nnamespace LeanSwe.MiniInv.Model\n" ++
    "def render (n : Nat) (_ : Unit) : Option Nat := some n\ndef wf (_ : Nat) : Prop := True\ndef equiv (a b : Nat) : Prop := a = b\nend LeanSwe.MiniInv.Model\n"),
  ("LeanSwe/MiniInv/Impl.lean",
    "import LeanSwe.MiniInv.Types\nnamespace LeanSwe.MiniInv.Internal\ndef parseImpl (n : Nat) : Except InvErr Nat := .ok n\nend LeanSwe.MiniInv.Internal\n"),
  ("LeanSwe/MiniInv/Interface.lean",
    "import LeanSwe.MiniInv.Impl\nnamespace LeanSwe.MiniInv\ndef parse (n : Nat) : Except InvErr Nat := Internal.parseImpl n\nend LeanSwe.MiniInv\n"),
  ("LeanSwe/MiniInv/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniInv.Model\nimport LeanSwe.MiniInv.Interface\nnamespace LeanSwe.MiniInv.Proofs\n" ++
    "theorem obeys_model : Core.ObeysInverseRender LeanSwe.MiniInv.parse LeanSwe.MiniInv.Model.render LeanSwe.MiniInv.Model.wf LeanSwe.MiniInv.Model.equiv InvErr.message :=\n" ++
    "  fun _ => ⟨trivial, ⟨(), rfl⟩, fun _ _ h => Option.some.inj h⟩\nend LeanSwe.MiniInv.Proofs\n"),
  ("LeanSwe/MiniProp/Types.lean",
    "namespace LeanSwe.MiniProp\ndef inc (n : Nat) : Nat := n + 1\nend LeanSwe.MiniProp\n"),
  ("LeanSwe/MiniProp/Properties.lean",
    "import Core.NondetTest\nimport LeanSwe.MiniProp.Types\nnamespace LeanSwe.MiniProp.Properties\n" ++
    "def prop_inc {r : Type → Type} [Core.NondetTest r] : r Unit := do\n  let n ← Core.NondetTest.nondet Nat\n  Core.NondetTest.assume (n > 0)\n  Core.NondetTest.assert (inc n > 1)\nend LeanSwe.MiniProp.Properties\n"),
  ("LeanSwe/MiniProp/Proofs.lean",
    "import Core.NondetTest\nimport LeanSwe.MiniProp.Properties\nnamespace LeanSwe.MiniProp.Proofs\n" ++
    "theorem obeys_model : Core.AllPass (Properties.prop_inc (r := Core.AllPassRun)) ∧ Core.CanReach (Properties.prop_inc (r := Core.CanReachRun)) :=\n" ++
    "  ⟨fun _ h => ⟨Nat.succ_lt_succ h, trivial⟩, ⟨1, ⟨Nat.zero_lt_one, ⟨Nat.succ_lt_succ Nat.zero_lt_one, trivial⟩⟩⟩⟩\nend LeanSwe.MiniProp.Proofs\n"),
  ("LeanSwe/MiniLeaf/Types.lean",
    "namespace LeanSwe.MiniLeaf\nstructure LeafOpsM (m : Type → Type) where\n  ping : Nat → m Nat\nabbrev LeafOps := LeafOpsM IO\nend LeanSwe.MiniLeaf\n"),
  ("LeanSwe/MiniLeaf/Model.lean",
    "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Model\ndef leafWf (_ : Nat) : Bool := true\n" ++
    "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
    "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniLeaf.Model\n"),
  ("LeanSwe/MiniLeaf/Impl.lean",
    "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Internal\ndef mkOps {m : Type → Type} [Monad m] (raw : Nat → m Nat) : LeafOpsM m := { ping := raw }\nend LeanSwe.MiniLeaf.Internal\n"),
  ("LeanSwe/MiniLeaf/Interface.lean",
    "import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"mini_leaf_raw_ping\"]\nprivate opaque rawPing : Nat → BaseIO Nat\n" ++
    "def defaultOps : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\nend LeanSwe.MiniLeaf\n"),
  ("LeanSwe/MiniLeaf/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniLeaf.Interface\nnamespace LeanSwe.MiniLeaf.Proofs\n" ++
    "theorem obeys_model : Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf (fun {m} [Monad m] (ops : LeafOpsM m) => Internal.mkOps ops.ping) Model.execLeaf Model.allowedLeaf :=\n" ++
    "  fun _ _ h => h\nend LeanSwe.MiniLeaf.Proofs\n"),
  ("LeanSwe/MiniComp/Types.lean",
    "namespace LeanSwe.MiniComp\nstructure CompApiM (m : Type → Type) where\n  callPing : Nat → m Nat\nabbrev CompApi := CompApiM IO\nend LeanSwe.MiniComp\n"),
  ("LeanSwe/MiniComp/Model.lean",
    "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Model\ndef compWf (_ : Nat) : Bool := true\n" ++
    "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
    "def allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
    "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
    "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"),
  ("LeanSwe/MiniComp/Impl.lean",
    "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n" ++
    "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m := { callPing := fun n => leaf.ping n }\nend LeanSwe.MiniComp.Internal\n"),
  ("LeanSwe/MiniComp/Interface.lean",
    "import LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\n" ++
    "def defaultApi : CompApi := Internal.mkApiM LeanSwe.MiniLeaf.defaultOps\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"),
  ("LeanSwe/MiniComp/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniComp.Model\nimport LeanSwe.MiniComp.Interface\nnamespace LeanSwe.MiniComp.Proofs\n" ++
    "theorem obeys_model : Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkApiM Model.execPkg Model.allowedPkg :=\n" ++
    "  fun _ _ h => h\nend LeanSwe.MiniComp.Proofs\n")
]

private def baselineBuildOrder : Array String := #[
  "LeanSwe/MiniPure/Types.lean", "LeanSwe/MiniPure/Model.lean", "LeanSwe/MiniPure/Impl.lean", "LeanSwe/MiniPure/Interface.lean", "LeanSwe/MiniPure/Proofs.lean",
  "LeanSwe/MiniErrMsg/Types.lean", "LeanSwe/MiniErrMsg/Model.lean", "LeanSwe/MiniErrMsg/Impl.lean", "LeanSwe/MiniErrMsg/Interface.lean", "LeanSwe/MiniErrMsg/Proofs.lean",
  "LeanSwe/MiniInv/Types.lean", "LeanSwe/MiniInv/Model.lean", "LeanSwe/MiniInv/Impl.lean", "LeanSwe/MiniInv/Interface.lean", "LeanSwe/MiniInv/Proofs.lean",
  "LeanSwe/MiniProp/Types.lean", "LeanSwe/MiniProp/Properties.lean", "LeanSwe/MiniProp/Proofs.lean",
  "LeanSwe/MiniLeaf/Types.lean", "LeanSwe/MiniLeaf/Model.lean", "LeanSwe/MiniLeaf/Impl.lean", "LeanSwe/MiniLeaf/Interface.lean", "LeanSwe/MiniLeaf/Proofs.lean",
  "LeanSwe/MiniComp/Types.lean", "LeanSwe/MiniComp/Model.lean", "LeanSwe/MiniComp/Impl.lean", "LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"
]

private def baselineRootsCsv : String :=
  "LeanSwe.MiniPure.Proofs,LeanSwe.MiniErrMsg.Proofs,LeanSwe.MiniInv.Proofs,LeanSwe.MiniProp.Proofs,LeanSwe.MiniLeaf.Proofs,LeanSwe.MiniComp.Proofs"

private def copyFileOrDir (src dst : System.FilePath) : IO Unit := do
  let out ← runCmd "cp" #["-a", src.toString, dst.toString]
  if out.exitCode != 0 then throw (IO.userError s!"cp -a {src} {dst} failed: {out.stderr}")

private def buildSyntheticRepo (baseDir realLibAbs : System.FilePath) : IO (System.FilePath × System.FilePath) := do
  let root := baseDir / "repo"
  let libDir := baseDir / "lib"
  IO.FS.createDirAll root
  IO.FS.createDirAll libDir
  symlinkCoreLib realLibAbs libDir
  writeFileCreatingParents (root / "scripts/package_manifest.json") baselineManifestJson
  for (rel, content) in baselineFiles do writeFileCreatingParents (root / rel) content
  let leanPath := s!"{libDir}:{realLibAbs}"
  for rel in baselineBuildOrder do
    compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")
  return (root, libDir)

private def runAuditCase (bin libDir manifestPath : System.FilePath)
    (rootsCsv modelAllow hookAllow : String) (synthAllow : String := "") : IO IO.Process.Output :=
  runCmd bin.toString #["--internal-manifest-audit", libDir.toString, manifestPath.toString, rootsCsv, modelAllow, hookAllow, synthAllow]

private def runPrintSigCase (bin libDir manifestPath : System.FilePath) (rootsCsv pkgStr : String) : IO IO.Process.Output :=
  runCmd bin.toString #["--internal-print-obeys-sig", libDir.toString, manifestPath.toString, rootsCsv, pkgStr]

private def assertPass (label : String) (out : IO.Process.Output) : IO Unit := do
  if out.exitCode != 0 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected pass (exit 0), got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def assertPassWith (label expectedSub : String) (out : IO.Process.Output) : IO Unit := do
  assertPass label out
  if (out.stdout.splitOn expectedSub).length <= 1 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected stdout containing '{expectedSub}', got:\n{out.stdout}")

private def assertFailWith (label expectedDiag : String) (out : IO.Process.Output) : IO Unit := do
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 || (combined.splitOn expectedDiag).length <= 1 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected failure containing '{expectedDiag}', got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def runMutantCase
    (bin tmpRoot baseDir realLibAbs : System.FilePath) (caseName : String)
    (mutate : System.FilePath → System.FilePath → String → IO (String × String × String × String))
    (expectedDiag? : Option String) : IO Unit := do
  let caseDir := tmpRoot / s!"case_{caseName}"
  copyFileOrDir baseDir caseDir
  let root := caseDir / "repo"
  let libDir := caseDir / "lib"
  let leanPath := s!"{libDir}:{realLibAbs}"
  let (rootsCsv, modelAllow, hookAllow, synthAllow) ← mutate root libDir leanPath
  let out ← runAuditCase bin libDir (root / "scripts/package_manifest.json") rootsCsv modelAllow hookAllow synthAllow
  match expectedDiag? with
  | none => assertPass caseName out
  | some diag => assertFailWith caseName diag out
  IO.FS.removeDirAll caseDir

private def recompile (root libDir : System.FilePath) (leanPath : String) (rels : Array String) : IO Unit := do
  for rel in rels do
    compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")

private def writeAndRecompile (root libDir : System.FilePath) (leanPath : String)
    (files : Array (String × String)) (extraRels : Array String := #[]) : IO Unit := do
  for (rel, content) in files do writeFileCreatingParents (root / rel) content
  recompile root libDir leanPath (files.map Prod.fst ++ extraRels)

/-- Run all synthetic positive and negative self-tests for `CheckPromises.lean` manifest, wiring, and synthesis checks. -/
def main (_ : List String) : IO UInt32 := do
  let realRepo ← IO.FS.realPath "."
  let realLibAbs ← IO.FS.realPath (realRepo / ".lake" / "build" / "lib" / "lean")
  let mkOut ← runCmd "mktemp" #["-d", "/tmp/check-promises-test.XXXXXX"]
  if mkOut.exitCode != 0 then
    IO.eprintln s!"MKTEMP_FAILED: {mkOut.stderr}"
    return 1
  let tmpRoot : System.FilePath := mkOut.stdout.trimAscii.toString
  try
    let bin ← buildCheckPromisesBin tmpRoot
    let baseDir := tmpRoot / "baseline"
    let (baseRoot, baseLib) ← buildSyntheticRepo baseDir realLibAbs
    let baseMan := baseRoot / "scripts/package_manifest.json"

    assertPass "baseline_compliant" (← runAuditCase bin baseLib baseMan baselineRootsCsv "" "")
    assertFailWith "stale_model_presence_allowlist" "STALE_MODEL_PRESENCE_ALLOWLIST"
      (← runAuditCase bin baseLib baseMan baselineRootsCsv "MISSING_OBEYS_MODEL|LeanSwe.MiniPure" "")
    assertFailWith "stale_middle_hook_allowlist" "STALE_MIDDLE_HOOK_ALLOWLIST"
      (← runAuditCase bin baseLib baseMan baselineRootsCsv "" "MIDDLE_HOOK|LeanSwe.MiniComp")
    assertFailWith "stale_obeys_synth_allowlist" "STALE_OBEYS_SYNTH_ALLOWLIST"
      (← runAuditCase bin baseLib baseMan baselineRootsCsv "" "" "OBEYS_SYNTH|LeanSwe.MiniPure")

    assertPassWith "print_sig_pure" "Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel"
      (← runPrintSigCase bin baseLib baseMan baselineRootsCsv "LeanSwe.MiniPure")
    assertPassWith "print_sig_err_msg" "Core.ObeysPureEqUpToErrMsg"
      (← runPrintSigCase bin baseLib baseMan baselineRootsCsv "LeanSwe.MiniErrMsg")
    assertPassWith "print_sig_inv_render" "Core.ObeysInverseRender LeanSwe.MiniInv.parse LeanSwe.MiniInv.Model.render"
      (← runPrintSigCase bin baseLib baseMan baselineRootsCsv "LeanSwe.MiniInv")
    assertPassWith "print_sig_step" "Core.ObeysStepFrom id"
      (← runPrintSigCase bin baseLib baseMan baselineRootsCsv "LeanSwe.MiniComp")
    let propSigOut ← runPrintSigCase bin baseLib baseMan baselineRootsCsv "LeanSwe.MiniProp"
    assertPassWith "print_sig_prop_allpass" "Core.AllPass" propSigOut
    assertPassWith "print_sig_prop_canreach" "Core.CanReach" propSigOut

    runMutantCase bin tmpRoot baseDir realLibAbs "middle_hook_scoped_ops" (fun root libDir leanPath => do
      writeAndRecompile root libDir leanPath #[
        ("LeanSwe/MiniComp/Types.lean",
         "namespace LeanSwe.MiniComp\nstructure CompApiM (m : Type → Type) where\n  callPing : Nat → m Nat\nstructure ScopedCompOpsM (m : Type → Type) where\n  runScoped : Nat → m Nat\nabbrev CompApi := CompApiM IO\nend LeanSwe.MiniComp\n"),
        ("LeanSwe/MiniComp/Model.lean",
         "import LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Model\ndef compWf (_ : Nat) : Bool := true\ndef execRaw {W : Type} (ops : ScopedCompOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.runScoped req\ndef allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\ndef execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\ndef allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"),
        ("LeanSwe/MiniComp/Impl.lean",
         "import LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\ndef defaultScopedIoOps : ScopedCompOpsM IO := { runScoped := LeanSwe.MiniLeaf.defaultOps.ping }\ndef mkScopedApiM {m : Type → Type} [Monad m] (ops : ScopedCompOpsM m) : CompApiM m := { callPing := ops.runScoped }\nend LeanSwe.MiniComp.Internal\n"),
        ("LeanSwe/MiniComp/Interface.lean",
         "import LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\ndef defaultApi : CompApi := Internal.mkScopedApiM Internal.defaultScopedIoOps\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"),
        ("LeanSwe/MiniComp/Proofs.lean",
         "import Core.Obeys\nimport LeanSwe.MiniComp.Model\nimport LeanSwe.MiniComp.Interface\nnamespace LeanSwe.MiniComp.Proofs\ntheorem obeys_model : Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkScopedApiM Model.execPkg Model.allowedPkg := fun _ _ h => h\nend LeanSwe.MiniComp.Proofs\n")]
      assertPass "middle_hook_allowlisted" (← runAuditCase bin libDir (root / "scripts/package_manifest.json") baselineRootsCsv "" "MIDDLE_HOOK|LeanSwe.MiniComp")
      return (baselineRootsCsv, "", "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    let runStd (name : String) (expected? : Option String) (mutate : System.FilePath → System.FilePath → String → IO Unit) : IO Unit :=
      runMutantCase bin tmpRoot baseDir realLibAbs name (fun root libDir leanPath => do
        mutate root libDir leanPath; return (baselineRootsCsv, "", "", "")) expected?
    let runFiles (name : String) (expected? : Option String) (files : Array (String × String)) (extraRels : Array String := #[]) : IO Unit :=
      runStd name expected? fun root libDir leanPath => writeAndRecompile root libDir leanPath files extraRels

    runFiles "missing_obeys_model" (some "MANIFEST_MISSING_OBEYS_MODEL") #[
      ("LeanSwe/MiniPure/Proofs.lean",
       "import LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\nend LeanSwe.MiniPure.Proofs\n")]

    runMutantCase bin tmpRoot baseDir realLibAbs "missing_model" (fun root libDir leanPath => do
      writeAndRecompile root libDir leanPath #[("LeanSwe/MiniPure/Proofs.lean",
        "import LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\nend LeanSwe.MiniPure.Proofs\n")]
      return (baselineRootsCsv, "MISSING_OBEYS_MODEL|LeanSwe.MiniPure", "", "")
    ) (some "MANIFEST_MISSING_MODEL")

    runFiles "vacuous_obeys_model" (some "VACUOUS_OR_INVALID_OBEYS_MODEL") #[
      ("LeanSwe/MiniPure/Proofs.lean",
       "import Core.Obeys\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\n" ++
       "theorem obeys_model : Core.ObeysPure LeanSwe.MiniPure.eval (fun _ _ => True) := fun _ => trivial\nend LeanSwe.MiniPure.Proofs\n")]

    runFiles "forbidden_extern_non_boundary" (some "FORBIDDEN_EXTERN_IN_NON_BOUNDARY") #[
      ("LeanSwe/MiniPure/Interface.lean",
       "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n@[extern \"bad_pure_extern\"]\nprivate opaque badExtern : BaseIO Nat\n" ++
       "def eval (n : Nat) : Nat := Internal.evalImpl n\nend LeanSwe.MiniPure\n")] #["LeanSwe/MiniPure/Proofs.lean"]

    runFiles "public_extern_in_boundary" (some "INVALID_EXTERN_PLACEMENT") #[
      ("LeanSwe/MiniLeaf/Interface.lean",
       "import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"mini_leaf_raw_ping\"]\nopaque rawPing : Nat → BaseIO Nat\n" ++
       "def defaultOps : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\nend LeanSwe.MiniLeaf\n")]
      #["LeanSwe/MiniLeaf/Proofs.lean", "LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]

    runStd "unregistered_ghost_pkg" (some "MANIFEST_UNREGISTERED_PACKAGE") fun root _ _ => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        (baselineManifestJson.replace "    \"LeanSwe.MiniPure\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false, \"spec_style\": \"pure_eq\"},\n" "")

    runFiles "builder_mismatch" (some "MIDDLE_HOOK_VIOLATION") #[
      ("LeanSwe/MiniComp/Impl.lean",
       "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n" ++
       "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m := { callPing := fun n => leaf.ping n }\n" ++
       "def mkAltApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m := { callPing := fun n => leaf.ping (n + 1) }\nend LeanSwe.MiniComp.Internal\n"),
      ("LeanSwe/MiniComp/Interface.lean",
       "import LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\n" ++
       "def defaultApi : CompApi := Internal.mkAltApiM LeanSwe.MiniLeaf.defaultOps\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n")]
      #["LeanSwe/MiniComp/Proofs.lean"]

    runStd "external_cli_compliant" none fun root _ _ => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        (baselineManifestJson.replace "\"LeanSwe.MiniComp\": {\"kind\": \"model\", \"purity\": \"mixed\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": false,"
          "\"LeanSwe.MiniComp\": {\"kind\": \"model\", \"purity\": \"nondet_io\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": true,")

    runFiles "leaf_defaultOpsBase_and_thin_mk_wrapper_ok" none #[
      ("LeanSwe/MiniLeaf/Types.lean",
       "namespace LeanSwe.MiniLeaf\nstructure LeafOpsM (m : Type → Type) (fd : Type) where\n  ping : Nat → m fd\n" ++
       "abbrev HandleLeafOpsM (m : Type → Type) : Type := LeafOpsM m Nat\nabbrev LeafOps := HandleLeafOpsM IO\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Model.lean",
       "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Model\ndef leafWf (_ : Nat) : Bool := true\n" ++
       "def execLeaf {W : Type} (ops : HandleLeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
       "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniLeaf.Model\n"),
      ("LeanSwe/MiniLeaf/Impl.lean",
       "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Internal\n" ++
       "def mkOpsM {m : Type → Type} {fd : Type} [Monad m] (raw : LeafOpsM m fd) : LeafOpsM m fd := { ping := raw.ping }\n" ++
       "def mkOpsBase (raw : HandleLeafOpsM BaseIO) : HandleLeafOpsM BaseIO := mkOpsM raw\nend LeanSwe.MiniLeaf.Internal\n"),
      ("LeanSwe/MiniLeaf/Interface.lean",
       "import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"mini_leaf_raw_ping\"]\nprivate opaque rawPing : Nat → BaseIO Nat\n" ++
       "def defaultOpsBase : HandleLeafOpsM BaseIO := Internal.mkOpsBase { ping := rawPing }\n" ++
       "def defaultOps : LeafOps := { ping := fun n => liftM (defaultOpsBase.ping n) }\ndef ping (n : Nat) : IO Nat := defaultOps.ping n\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean",
       "import Core.Obeys\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniLeaf.Interface\nnamespace LeanSwe.MiniLeaf.Proofs\n" ++
       "theorem obeys_model : Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf Internal.mkOpsM Model.execLeaf Model.allowedLeaf :=\n  fun _ _ h => h\nend LeanSwe.MiniLeaf.Proofs\n"),
      ("LeanSwe/MiniComp/Model.lean",
       "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Model\ndef compWf (_ : Nat) : Bool := true\n" ++
       "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.HandleLeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
       "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
       "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"),
      ("LeanSwe/MiniComp/Impl.lean",
       "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n" ++
       "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.HandleLeafOpsM m) : CompApiM m := { callPing := fun n => leaf.ping n }\nend LeanSwe.MiniComp.Internal\n")]
      #["LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]

    let compModelHdr := "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Model\ndef compWf (_ : Nat) : Bool := true\n"
    let compIfaceHdr := "import LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\n"
    let compProofsHdr := "import Core.Obeys\nimport LeanSwe.MiniComp.Model\nimport LeanSwe.MiniComp.Interface\nnamespace LeanSwe.MiniComp.Proofs\n"
    let pureIfaceHdr := "import LeanSwe.MiniPure.Impl\nnamespace LeanSwe.MiniPure\n"
    let pureProofsHdr := "import Core.Obeys\nimport LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\n"

    runStd "external_cli_middle_hook" (some "MIDDLE_HOOK_VIOLATION") fun root libDir leanPath => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        (baselineManifestJson.replace "\"LeanSwe.MiniComp\": {\"kind\": \"model\", \"purity\": \"mixed\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": false,"
          "\"LeanSwe.MiniComp\": {\"kind\": \"model\", \"purity\": \"nondet_io\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": true,")
      writeAndRecompile root libDir leanPath #[("LeanSwe/MiniComp/Interface.lean",
        compIfaceHdr ++ "def defaultRawOps : LeanSwe.MiniLeaf.LeafOps := { ping := LeanSwe.MiniLeaf.defaultOps.ping }\n" ++
        "def defaultApi : CompApi := Internal.mkApiM defaultRawOps\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n")]
        #["LeanSwe/MiniComp/Proofs.lean"]

    runFiles "vacuous_raw_allowed_false" (some "VACUOUS_OR_INVALID_OBEYS_MODEL") #[
      ("LeanSwe/MiniComp/Model.lean",
       compModelHdr ++ "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedRaw (_ _ _ _ : Nat) : Prop := False\n" ++
       "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
       "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"),
      ("LeanSwe/MiniComp/Proofs.lean",
       compProofsHdr ++
       "theorem obeys_model : Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkApiM Model.execPkg Model.allowedPkg :=\n" ++
       "  fun _ _ h w req hw => False.elim (h w req hw)\nend LeanSwe.MiniComp.Proofs\n")]

    runFiles "renamed_default_client_bypass" (some "MIDDLE_HOOK_VIOLATION") #[
      ("LeanSwe/MiniComp/Interface.lean",
       compIfaceHdr ++ "def defaultClient : CompApi := Internal.mkApiM { ping := LeanSwe.MiniLeaf.defaultOps.ping }\ndef callPing (n : Nat) : IO Nat := defaultClient.callPing n\nend LeanSwe.MiniComp\n")]
      #["LeanSwe/MiniComp/Proofs.lean"]

    runFiles "decoy_defaultApi_with_hooked_defaultClient" (some "MIDDLE_HOOK_VIOLATION") #[
      ("LeanSwe/MiniComp/Interface.lean",
       compIfaceHdr ++ "def defaultApi : CompApi := Internal.mkApiM LeanSwe.MiniLeaf.defaultOps\n" ++
       "def defaultClient : CompApi := Internal.mkApiM { ping := LeanSwe.MiniLeaf.defaultOps.ping }\ndef callPing (n : Nat) : IO Nat := defaultClient.callPing n\nend LeanSwe.MiniComp\n")]
      #["LeanSwe/MiniComp/Proofs.lean"]

    runFiles "synth_missing_pure_op" (some "OBEYS_SYNTH_PURE_MISMATCH") #[
      ("LeanSwe/MiniPure/Model.lean",
       "import LeanSwe.MiniPure.Types\nnamespace LeanSwe.MiniPure.Model\ndef evalModel (n : Nat) : Nat := n + 1\ndef eval2 (n : Nat) : Nat := n + 2\nend LeanSwe.MiniPure.Model\n"),
      ("LeanSwe/MiniPure/Interface.lean",
       pureIfaceHdr ++ "def eval (n : Nat) : Nat := Internal.evalImpl n\ndef eval2 (n : Nat) : Nat := n + 2\nend LeanSwe.MiniPure\n")]
      #["LeanSwe/MiniPure/Proofs.lean"]

    runFiles "synth_extra_domain_guard" (some "OBEYS_SYNTH_PURE_MISMATCH") #[
      ("LeanSwe/MiniPure/Proofs.lean",
       pureProofsHdr ++ "theorem obeys_model : ∀ (x : Nat), x ≠ 0 → Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ _ _ => rfl\nend LeanSwe.MiniPure.Proofs\n")]

    runFiles "synth_substituted_impl_fn" (some "OBEYS_SYNTH_PURE_MISMATCH") #[
      ("LeanSwe/MiniPure/Proofs.lean",
       pureProofsHdr ++ "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.Internal.evalImpl LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\nend LeanSwe.MiniPure.Proofs\n")]

    runFiles "synth_missing_canreach_property" (some "OBEYS_SYNTH_MISSING_CANREACH") #[
      ("LeanSwe/MiniProp/Proofs.lean",
       "import Core.NondetTest\nimport LeanSwe.MiniProp.Properties\nnamespace LeanSwe.MiniProp.Proofs\n" ++
       "theorem obeys_model : Core.AllPass (Properties.prop_inc (r := Core.AllPassRun)) := fun _ h => ⟨Nat.succ_lt_succ h, trivial⟩\nend LeanSwe.MiniProp.Proofs\n")]

    runFiles "synth_uncovered_effectful_op" (some "OBEYS_SYNTH_UNCOVERED_EFF_OP") #[
      ("LeanSwe/MiniComp/Types.lean",
       "namespace LeanSwe.MiniComp\nstructure CompApiM (m : Type → Type) where\n  callPing : Nat → m Nat\n  callPong : Nat → m Nat\nabbrev CompApi := CompApiM IO\nend LeanSwe.MiniComp\n"),
      ("LeanSwe/MiniComp/Impl.lean",
       "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n" ++
       "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m := { callPing := fun n => leaf.ping n, callPong := fun n => leaf.ping n }\nend LeanSwe.MiniComp.Internal\n"),
      ("LeanSwe/MiniComp/Interface.lean",
       "import LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\n" ++
       "def defaultApi : CompApi := Internal.mkApiM LeanSwe.MiniLeaf.defaultOps\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\ndef callPong (n : Nat) : IO Nat := defaultApi.callPong n\nend LeanSwe.MiniComp\n")]
      #["LeanSwe/MiniComp/Model.lean", "LeanSwe/MiniComp/Proofs.lean"]

    let leafModHdr := "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Model\ndef leafWf (_ : Nat) : Bool := true\n"
    let leafImplHdr := "import LeanSwe.MiniLeaf.Types\nnamespace LeanSwe.MiniLeaf.Internal\n"
    let leafProofHdr := "import Core.Obeys\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniLeaf.Interface\nnamespace LeanSwe.MiniLeaf.Proofs\n"
    let compImplHdr := "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n"
    let concImplHdr := "import Core.ConcOps\n" ++ compImplHdr
    let pingPairModelSrc :=
      leafModHdr ++
      "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
      "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
      "abbrev PingTwiceFn (m : Type → Type) : Type := Nat → m (Nat × Nat)\n" ++
      "def execPingTwice {W : Type} (fn : PingTwiceFn (StateM W)) (n : Nat) : StateM W (Nat × Nat) := fn n\n" ++
      "def allowedPing2 (s req : Nat) (out : Nat × Nat) (s' : Nat) : Prop := out = (req, req + 1) ∧ s' = s\nend LeanSwe.MiniLeaf.Model\n"
    let rawPingIfaceHdr :=
      "import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"mini_leaf_raw_ping\"]\nprivate opaque rawPing : Nat → BaseIO Nat\n"
    let pingPairIfaceSrc (delta : Nat) (extra : String := "") : String :=
      rawPingIfaceHdr ++
      "def defaultOps : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\ndef ping (n : Nat) : IO Nat := defaultOps.ping n\n" ++
      s!"def pingPair \{m : Type → Type} [Monad m] (ops : LeafOpsM m) (n : Nat) : m (Nat × Nat) := do\n  let a ← ops.ping n\n  return (a, a + {delta})\n" ++
      extra ++ "end LeanSwe.MiniLeaf\n"
    let pingPairThmType :=
      leafProofHdr ++ "theorem obeys_model :\n" ++
      "    Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf (fun {m} [Monad m] (ops : LeafOpsM m) => Internal.mkOps ops.ping) Model.execLeaf Model.allowedLeaf ∧\n" ++
      "    Core.ObeysStepFrom (PkgApi := Model.PingTwiceFn) id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf LeanSwe.MiniLeaf.pingPair Model.execPingTwice Model.allowedPing2 :=\n"
    let pingPairProofsSrc :=
      pingPairThmType ++
      "  ⟨fun _ _ h => h, fun _ ops h w n hw => by\n    have hs := h w n hw\n" ++
      "    dsimp only [Function.comp, id, Model.execLeaf, Model.allowedLeaf, Model.execPingTwice, LeanSwe.MiniLeaf.pingPair, Model.allowedPing2, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hs ⊢\n" ++
      "    rcases hc : ops.ping n w with ⟨v, w'⟩\n    rw [hc] at hs; dsimp only at hs ⊢; exact ⟨by rw [hs.1], hs.2⟩⟩\nend LeanSwe.MiniLeaf.Proofs\n"
    let leafIdProofsSrc (mkExpr : String) : String :=
      leafProofHdr ++
      s!"theorem obeys_model : Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf {mkExpr} Model.execLeaf Model.allowedLeaf := fun _ _ h => h\nend LeanSwe.MiniLeaf.Proofs\n"

    runFiles "iface_combinator_stepfrom_ok" none #[
      ("LeanSwe/MiniLeaf/Model.lean", pingPairModelSrc), ("LeanSwe/MiniLeaf/Interface.lean", pingPairIfaceSrc 1),
      ("LeanSwe/MiniLeaf/Proofs.lean", pingPairProofsSrc)]

    runFiles "iface_combinator_fake_exec_rejected" (some "must directly invoke Interface op") #[
      ("LeanSwe/MiniLeaf/Model.lean",
       pingPairModelSrc.replace "(fn : PingTwiceFn (StateM W)) (n : Nat) : StateM W (Nat × Nat) := fn n"
         "(_ : PingTwiceFn (StateM W)) (n : Nat) : StateM W (Nat × Nat) := pure (n, n + 1)"),
      ("LeanSwe/MiniLeaf/Interface.lean", pingPairIfaceSrc 99),
      ("LeanSwe/MiniLeaf/Proofs.lean", pingPairThmType ++ "  ⟨fun _ _ h => h, fun _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩\nend LeanSwe.MiniLeaf.Proofs\n")]

    runFiles "iface_combinator_transitive_unproven_rejected" (some "OBEYS_SYNTH_UNCOVERED_EFF_OP") #[
      ("LeanSwe/MiniLeaf/Model.lean", pingPairModelSrc),
      ("LeanSwe/MiniLeaf/Interface.lean",
       pingPairIfaceSrc 1 "def pingTriple {m : Type → Type} [Monad m] (ops : LeafOpsM m) (n : Nat) : m Nat := do\n  let p ← pingPair ops n\n  return p.1 + p.2\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean", pingPairProofsSrc)]

    let fdLeafFiles (mkOpsCall defOpsCall : String) : Array (String × String) := #[
      ("LeanSwe/MiniLeaf/Types.lean",
       "namespace LeanSwe.MiniLeaf\nstructure RawOpsM (m : Type → Type) (fd : Type) where\n  ping : fd → m Nat\nstructure LeafOpsM (m : Type → Type) where\n  ping : Nat → m Nat\nabbrev LeafOps := LeafOpsM IO\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Model.lean",
       leafModHdr ++ "abbrev ModelRawM (m : Type → Type) := RawOpsM m Nat\ndef execRaw {W : Type} (ops : ModelRawM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
       "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniLeaf.Model\n"),
      ("LeanSwe/MiniLeaf/Impl.lean",
       leafImplHdr ++ "def mkOps {m : Type → Type} [Monad m] {fd : Type} (_ : RawOpsM m fd) (fuel : Nat := 18) : LeafOpsM m := { ping := fun n => if fuel == 0 then pure n else pure n }\n" ++
       s!"def mkOpsM \{m : Type → Type} [Monad m] (raw : RawOpsM m Nat) : LeafOpsM m := {mkOpsCall}\nend LeanSwe.MiniLeaf.Internal\n"),
      ("LeanSwe/MiniLeaf/Interface.lean",
       s!"import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"mini_leaf_raw_ping\"]\nprivate opaque rawPing : UInt32 → BaseIO Nat\nprivate def rawOps : RawOpsM IO UInt32 := \{ ping := fun fd => liftM (rawPing fd) }\ndef defaultOps : LeafOps := {defOpsCall}\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean",
       leafProofHdr ++ "theorem obeys_model : Core.ObeysStepFrom id Model.leafWf Model.execRaw Model.allowedLeaf Model.leafWf Internal.mkOpsM Model.execLeaf Model.allowedLeaf := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩\nend LeanSwe.MiniLeaf.Proofs\n")]
    let compExtraRels := #["LeanSwe/MiniComp/Model.lean", "LeanSwe/MiniComp/Impl.lean", "LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]

    runFiles "leaf_one_hop_builder_wrapper_ok" none (fdLeafFiles "mkOps raw" "Internal.mkOps rawOps") compExtraRels
    runFiles "leaf_one_hop_extra_arg_mismatch" (some "OBEYS_SYNTH_BUILDER_MISMATCH") (fdLeafFiles "mkOps raw 0" "Internal.mkOps rawOps 99") compExtraRels

    runFiles "leaf_struct_lift_defaultOps_ok" none #[
      ("LeanSwe/MiniLeaf/Interface.lean",
       rawPingIfaceHdr ++ "def defaultOps : LeafOps := { ping := fun n => liftM ((Internal.mkOps rawPing).ping n) }\nend LeanSwe.MiniLeaf\n")]
      #["LeanSwe/MiniLeaf/Proofs.lean", "LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]

    runFiles "leaf_struct_lift_bypass_field" (some "OBEYS_SYNTH_BUILDER_MISMATCH") #[
      ("LeanSwe/MiniLeaf/Types.lean",
       "namespace LeanSwe.MiniLeaf\nstructure LeafOpsM (m : Type → Type) where\n  ping : Nat → m Nat\n  pong : Nat → m Nat\nabbrev LeafOps := LeafOpsM IO\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Model.lean",
       leafModHdr ++ "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := if req == 0 then ops.ping req else ops.pong req\ndef allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniLeaf.Model\n"),
      ("LeanSwe/MiniLeaf/Impl.lean", leafImplHdr ++ "def mkOps {m : Type → Type} [Monad m] (ops : LeafOpsM m) : LeafOpsM m := ops\nend LeanSwe.MiniLeaf.Internal\n"),
      ("LeanSwe/MiniLeaf/Interface.lean",
       rawPingIfaceHdr ++ "private def rawOps : LeafOpsM BaseIO := { ping := rawPing, pong := rawPing }\ndef defaultOps : LeafOps := { ping := fun n => liftM ((Internal.mkOps rawOps).ping n), pong := fun n => liftM (rawPing n) }\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean", leafIdProofsSrc "Internal.mkOps")] compExtraRels

    runFiles "leaf_1hop_impl_delegation_fwd" none #[
      ("LeanSwe/MiniLeaf/Impl.lean",
       leafImplHdr ++ "def mkOpsM {m : Type → Type} [Monad m] (ops : LeafOpsM m) : LeafOpsM m := { ping := ops.ping }\ndef mkOps (raw : Nat → BaseIO Nat) : LeafOps := mkOpsM { ping := fun n => liftM (raw n) }\nend LeanSwe.MiniLeaf.Internal\n"),
      ("LeanSwe/MiniLeaf/Interface.lean", rawPingIfaceHdr ++ "def defaultOps : LeafOps := Internal.mkOps rawPing\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean", leafIdProofsSrc "Internal.mkOpsM")]

    runFiles "leaf_1hop_impl_delegation_rev" (some "OBEYS_SYNTH_BUILDER_MISMATCH") #[
      ("LeanSwe/MiniLeaf/Impl.lean",
       leafImplHdr ++ "def mkOps {m : Type → Type} [Monad m] (ops : LeafOpsM m) (wrap : m Nat → m Nat := id) : LeafOpsM m := { ping := fun n => wrap (ops.ping n) }\ndef mkOpsM {m : Type → Type} [Monad m] (ops : LeafOpsM m) : LeafOpsM m := mkOps ops\nend LeanSwe.MiniLeaf.Internal\n"),
      ("LeanSwe/MiniLeaf/Interface.lean", rawPingIfaceHdr ++ "def defaultOps : LeafOps := Internal.mkOps { ping := fun n => liftM (rawPing n) } id\nend LeanSwe.MiniLeaf\n"),
      ("LeanSwe/MiniLeaf/Proofs.lean", leafIdProofsSrc "Internal.mkOpsM")]

    runFiles "synth_derived_inhabited_aux_ignored" none #[
      ("LeanSwe/MiniPure/Interface.lean",
       pureIfaceHdr ++ "private structure PrivState where\n  x : Nat := 0\n  deriving Inhabited\ndef eval (n : Nat) : Nat := Internal.evalImpl n\nend LeanSwe.MiniPure\n")] #["LeanSwe/MiniPure/Proofs.lean"]

    runFiles "synth_smuggled_op_via_inst_body_rejected" (some "OBEYS_SYNTH_NO_MODEL_OP") #[
      ("LeanSwe/MiniPure/Interface.lean",
       pureIfaceHdr ++ "def instFoo.op (n : Nat) : Nat := n + 2\ninstance instFoo : Inhabited (Nat → Nat) := ⟨instFoo.op⟩\ndef eval (n : Nat) : Nat := Internal.evalImpl n\nend LeanSwe.MiniPure\n")]
      #["LeanSwe/MiniPure/Proofs.lean"]

    let invModHdr := "import LeanSwe.MiniInv.Types\nnamespace LeanSwe.MiniInv.Model\n"
    let invImplHdr := "import LeanSwe.MiniInv.Types\nnamespace LeanSwe.MiniInv.Internal\n"
    let invProofHdr := "import Core.Obeys\nimport LeanSwe.MiniInv.Model\nimport LeanSwe.MiniInv.Interface\nnamespace LeanSwe.MiniInv.Proofs\n"
    runStd "synth_inv_render_within_ok" none fun root libDir leanPath => do
      writeAndRecompile root libDir leanPath #[
        ("LeanSwe/MiniInv/Model.lean",
         invModHdr ++ "def render (n : Nat) (t : Nat) : Option Nat := if n == t then some n else none\ndef withinResourceLimits (t : Nat) : Prop := t ≤ 10\ndef WellFormedJson (_ : Nat) : Prop := True\ndef equiv (a b : Nat) : Prop := a = b\nend LeanSwe.MiniInv.Model\n"),
        ("LeanSwe/MiniInv/Impl.lean",
         invImplHdr ++ "def parseImpl (n : Nat) : Except InvErr Nat := if n ≤ 10 then .ok n else .error { message := \"cap\" }\nend LeanSwe.MiniInv.Internal\n"),
        ("LeanSwe/MiniInv/Proofs.lean",
         invProofHdr ++ "theorem obeys_model : Core.ObeysInverseRenderWithin LeanSwe.MiniInv.parse Model.render Model.withinResourceLimits Model.WellFormedJson Model.equiv InvErr.message := by\n" ++
         "  intro n; unfold LeanSwe.MiniInv.parse LeanSwe.MiniInv.Internal.parseImpl; by_cases h : n ≤ 10 <;> simp [h, Core.InverseRenderWithinSpec]\n" ++
         "  · exact ⟨trivial, ⟨n, by simp [Model.render]⟩, fun a t hr => by simp [Model.render] at hr; exact hr.2⟩\n" ++
         "  · intro a t hr hlim; simp [Model.render] at hr; simp [Model.withinResourceLimits] at hlim; omega\nend LeanSwe.MiniInv.Proofs\n")]
        #["LeanSwe/MiniInv/Interface.lean"]
      let sigOut ← runPrintSigCase bin libDir (root / "scripts/package_manifest.json") baselineRootsCsv "LeanSwe.MiniInv"
      assertPassWith "print_sig_inv_render_within_head" "Core.ObeysInverseRenderWithin LeanSwe.MiniInv.parse LeanSwe.MiniInv.Model.render" sigOut
      assertPassWith "print_sig_inv_render_within_args" "LeanSwe.MiniInv.Model.withinResourceLimits LeanSwe.MiniInv.Model.WellFormedJson" sigOut

    runFiles "vacuous_within_limits_false_rejected" (some "VACUOUS_OR_INVALID_OBEYS_MODEL") #[
      ("LeanSwe/MiniInv/Model.lean",
       invModHdr ++ "def render (n : Nat) (_ : Unit) : Option Nat := some n\ndef withinResourceLimits (_ : Unit) : Prop := False\ndef wf (_ : Nat) : Prop := True\ndef equiv (a b : Nat) : Prop := a = b\nend LeanSwe.MiniInv.Model\n"),
      ("LeanSwe/MiniInv/Impl.lean", invImplHdr ++ "def parseImpl (_ : Nat) : Except InvErr Nat := .error { message := \"bad\" }\nend LeanSwe.MiniInv.Internal\n"),
      ("LeanSwe/MiniInv/Proofs.lean",
       invProofHdr ++ "theorem obeys_model : Core.ObeysInverseRenderWithin LeanSwe.MiniInv.parse Model.render Model.withinResourceLimits Model.wf Model.equiv InvErr.message := fun _ => ⟨by decide, fun _ _ _ h => h⟩\nend LeanSwe.MiniInv.Proofs\n")]
      #["LeanSwe/MiniInv/Interface.lean"]

    let concIface (builderCall : String) : String :=
      "import Core.ConcOps\n" ++ compIfaceHdr ++
      s!"def defaultApi : CompApi := {builderCall}\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"
    let concProofHdr := "import Core.ConcOps\nimport LeanSwe.MiniComp.Model\nimport LeanSwe.MiniComp.Interface\nnamespace LeanSwe.MiniComp.Proofs\n"

    runStd "conc_stepfrom_compliant" none fun root libDir leanPath => do
      writeAndRecompile root libDir leanPath #[
        ("LeanSwe/MiniComp/Model.lean",
         compModelHdr ++ "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\ndef allowedPkg (_ req out s' : Nat) : Prop := out = req ∧ compWf s' = true\nend LeanSwe.MiniComp.Model\n"),
        ("LeanSwe/MiniComp/Impl.lean",
         concImplHdr ++ "def mkFullApiM {m : Type → Type} [Monad m] [MonadFinally m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) (conc : Core.ConcOpsM m) : CompApiM m :=\n" ++
         "  { callPing := fun n => do let _ := leaf; let r ← conc.mkRef true; let _ ← conc.readRef r; pure n }\nend LeanSwe.MiniComp.Internal\n"),
        ("LeanSwe/MiniComp/Interface.lean", concIface "Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOps Core.ioConcOps"),
        ("LeanSwe/MiniComp/Proofs.lean",
         concProofHdr ++ "theorem obeys_model : Core.ObeysStepFromConc id Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkFullApiM Model.execPkg Model.allowedPkg := by\n" ++
         "  intro W proj raw conc _ hconc w req hw; rcases hconc with ⟨_, hmk, hrd, _, _, _, _, _, _, _⟩; have h1 := hmk true w hw\n" ++
         "  cases hc1 : (conc.mkRef true).run w with | mk r w1 =>\n" ++
         "    rw [hc1] at h1; have h2 := hrd r w1 h1; cases hc2 : (conc.readRef r).run w1 with | mk _ w2 =>\n" ++
         "      rw [hc2] at h2; dsimp only [Model.execPkg, Model.allowedPkg, Internal.mkFullApiM, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at hc1 hc2 ⊢\n" ++
         "      rw [hc1]; dsimp only; rw [hc2]; exact ⟨rfl, h2⟩\nend LeanSwe.MiniComp.Proofs\n")]
      assertPassWith "print_sig_conc" "Core.ObeysStepFromConc id"
        (← runPrintSigCase bin libDir (root / "scripts/package_manifest.json") baselineRootsCsv "LeanSwe.MiniComp")

    runFiles "conc_vacuous_raw_allowed_false" (some "VACUOUS_OR_INVALID_OBEYS_MODEL") #[
      ("LeanSwe/MiniComp/Model.lean",
       compModelHdr ++ "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedRaw (_ _ _ _ : Nat) : Prop := False\n" ++
       "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\ndef allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"),
      ("LeanSwe/MiniComp/Impl.lean",
       concImplHdr ++ "def mkFullApiM {m : Type → Type} [Monad m] [MonadFinally m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) (_ : Core.ConcOpsM m) : CompApiM m := { callPing := fun n => leaf.ping n }\nend LeanSwe.MiniComp.Internal\n"),
      ("LeanSwe/MiniComp/Interface.lean", concIface "Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOps Core.ioConcOps"),
      ("LeanSwe/MiniComp/Proofs.lean",
       concProofHdr ++ "theorem obeys_model : Core.ObeysStepFromConc id Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkFullApiM Model.execPkg Model.allowedPkg :=\n" ++
       "  fun _ _ _ h _ w req hw => False.elim (h w req hw)\nend LeanSwe.MiniComp.Proofs\n")]

    runFiles "conc_builder_value_arg_rejected" (some "OBEYS_SYNTH_BUILDER_MISMATCH") #[
      ("LeanSwe/MiniComp/Impl.lean",
       concImplHdr ++ "def mkFullApiM (delta : Nat) {m : Type → Type} [Monad m] [MonadFinally m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) (_ : Core.ConcOpsM m) : CompApiM m := { callPing := fun n => leaf.ping (n + delta) }\nend LeanSwe.MiniComp.Internal\n"),
      ("LeanSwe/MiniComp/Interface.lean", concIface "Internal.mkFullApiM 1 LeanSwe.MiniLeaf.defaultOps Core.ioConcOps"),
      ("LeanSwe/MiniComp/Proofs.lean",
       concProofHdr ++ "theorem obeys_model : Core.ObeysStepFromConc id Model.compWf Model.execRaw Model.allowedRaw Model.compWf (Internal.mkFullApiM 0) Model.execPkg Model.allowedPkg :=\n" ++
       "  fun _ _ _ h _ w req hw => by simpa [Model.execPkg, Model.execRaw, Model.allowedPkg, Model.allowedRaw, Internal.mkFullApiM] using h w req hw\nend LeanSwe.MiniComp.Proofs\n")]

    runFiles "conc_builder_type_spec_rejected" (some "OBEYS_SYNTH_BUILDER_MISMATCH") #[
      ("LeanSwe/MiniComp/Impl.lean",
       concImplHdr ++ "def mkFullApiM {fd : Type} {m : Type → Type} [Monad m] [MonadFinally m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) (_ : Core.ConcOpsM m) : CompApiM m :=\n  { callPing := fun n => do let _ := (fun (_ : fd) => ()); leaf.ping n }\nend LeanSwe.MiniComp.Internal\n"),
      ("LeanSwe/MiniComp/Interface.lean", concIface "@Internal.mkFullApiM UInt32 IO _ _ LeanSwe.MiniLeaf.defaultOps Core.ioConcOps"),
      ("LeanSwe/MiniComp/Proofs.lean",
       concProofHdr ++ "theorem obeys_model : Core.ObeysStepFromConc id Model.compWf Model.execRaw Model.allowedRaw Model.compWf (@Internal.mkFullApiM Nat) Model.execPkg Model.allowedPkg :=\n" ++
       "  fun _ _ _ h _ w req hw => by simpa [Model.execPkg, Model.execRaw, Model.allowedPkg, Model.allowedRaw, Internal.mkFullApiM] using h w req hw\nend LeanSwe.MiniComp.Proofs\n")]

    IO.println "CHECK_PROMISES_SELF_TEST: passed=46 failed=0"
    return 0
  finally
    if ← tmpRoot.pathExists then IO.FS.removeDirAll tmpRoot
