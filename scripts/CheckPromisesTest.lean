import Lean

/-!
Positive and negative synthetic `.olean` self-test suite (`scripts/CheckPromisesTest.lean`) for
the manifest-driven `obeys_model` presence/non-vacuity gate and generalized `.olean` wiring /
middle-hook ban in `scripts/CheckPromises.lean`.

Compiles `scripts/CheckPromises.lean` once to an isolated `/tmp` binary and exercises
`--internal-manifest-audit` over compiled synthetic `.olean` packages covering:
1. Compliant pure, leaf `external_boundary`, and composite packages (`errors=0`).
2. Composite package wired through a same-package un-fuzzed middle hook (`ScopedCompOpsM`,
   simulating `ConnectProxy.ScopedProxyOpsM`) rejected with `MIDDLE_HOOK_VIOLATION`.
3. Exact shrinking allowlist enforcement (`STALE_MIDDLE_HOOK_ALLOWLIST` and
   `STALE_MODEL_PRESENCE_ALLOWLIST`).
4. Missing `obeys_model` (`MANIFEST_MISSING_OBEYS_MODEL`) and missing `Model`
   (`MANIFEST_MISSING_MODEL`) on manifest `kind == "model"` packages.
5. Vacuous `obeys_model` (`VACUOUS_OR_INVALID_OBEYS_MODEL`).
6. Direct `@[extern]` inside an `external_boundary == false` package
   (`FORBIDDEN_EXTERN_IN_NON_BOUNDARY`) and public `@[extern]` inside an `external_boundary == true`
   package (`INVALID_EXTERN_PLACEMENT`).
7. Unregistered ghost package missing from manifest (`MANIFEST_UNREGISTERED_PACKAGE`).
8. Disconnected builder mismatch between `defaultApi` and `obeys_model` (`MIDDLE_HOOK_VIOLATION`).
-/

private def writeFileCreatingParents (p : System.FilePath) (content : String) : IO Unit := do
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile p content

private def runCmd (cmd : String) (args : Array String) (cwd? : Option System.FilePath := none)
    (extraEnv : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := cwd?, env := extraEnv }

private def compileLeanMod (repoRoot : System.FilePath) (leanPath : String)
    (src olean : System.FilePath) : IO Unit := do
  if let some parent := olean.parent then
    IO.FS.createDirAll parent
  let out ← runCmd "lean"
    #["-R", repoRoot.toString, "-o", olean.toString, src.toString]
    none
    #[("LEAN_SRC_PATH", some repoRoot.toString), ("LEAN_PATH", some leanPath)]
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
  if r1.exitCode != 0 then
    throw (IO.userError s!"ln Core failed: {r1.stderr}")
  if ← (realLibDir / "Core.olean").pathExists then
    let r2 ← runCmd "ln" #["-sfn", (realLibDir / "Core.olean").toString, (targetLibDir / "Core.olean").toString]
    if r2.exitCode != 0 then
      throw (IO.userError s!"ln Core.olean failed: {r2.stderr}")

private def baselineManifestJson : String :=
  "{\n" ++
  "  \"version\": 1,\n" ++
  "  \"packages\": {\n" ++
  "    \"LeanSwe.MiniPure\": {\n" ++
  "      \"kind\": \"model\",\n" ++
  "      \"purity\": \"pure\",\n" ++
  "      \"deps\": [],\n" ++
  "      \"external_boundary\": false,\n" ++
  "      \"spec_style\": \"pure_eq\"\n" ++
  "    },\n" ++
  "    \"LeanSwe.MiniLeaf\": {\n" ++
  "      \"kind\": \"model\",\n" ++
  "      \"purity\": \"nondet_io\",\n" ++
  "      \"deps\": [],\n" ++
  "      \"external_boundary\": true,\n" ++
  "      \"fuzz_suite\": \"minileaf\",\n" ++
  "      \"spec_style\": \"state_step\"\n" ++
  "    },\n" ++
  "    \"LeanSwe.MiniComp\": {\n" ++
  "      \"kind\": \"model\",\n" ++
  "      \"purity\": \"mixed\",\n" ++
  "      \"deps\": [\"LeanSwe.MiniLeaf\"],\n" ++
  "      \"external_boundary\": false,\n" ++
  "      \"spec_style\": \"state_step\"\n" ++
  "    }\n" ++
  "  }\n" ++
  "}\n"

private def baselineFiles : Array (String × String) := #[
  ("LeanSwe/MiniPure/Types.lean",
    "namespace LeanSwe.MiniPure\n" ++
    "structure PureCfg where\n" ++
    "  delta : Nat\n" ++
    "end LeanSwe.MiniPure\n"),
  ("LeanSwe/MiniPure/Model.lean",
    "import LeanSwe.MiniPure.Types\n" ++
    "namespace LeanSwe.MiniPure.Model\n" ++
    "def evalModel (n : Nat) : Nat := n + 1\n" ++
    "end LeanSwe.MiniPure.Model\n"),
  ("LeanSwe/MiniPure/Impl.lean",
    "import LeanSwe.MiniPure.Types\n" ++
    "namespace LeanSwe.MiniPure.Internal\n" ++
    "def evalImpl (n : Nat) : Nat := n + 1\n" ++
    "end LeanSwe.MiniPure.Internal\n"),
  ("LeanSwe/MiniPure/Interface.lean",
    "import LeanSwe.MiniPure.Impl\n" ++
    "namespace LeanSwe.MiniPure\n" ++
    "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
    "end LeanSwe.MiniPure\n"),
  ("LeanSwe/MiniPure/Proofs.lean",
    "import Core.Obeys\n" ++
    "import LeanSwe.MiniPure.Model\n" ++
    "import LeanSwe.MiniPure.Interface\n" ++
    "namespace LeanSwe.MiniPure.Proofs\n" ++
    "theorem obeys_model : Core.ObeysPureEq LeanSwe.MiniPure.eval LeanSwe.MiniPure.Model.evalModel := fun _ => rfl\n" ++
    "end LeanSwe.MiniPure.Proofs\n"),
  ("LeanSwe/MiniLeaf/Types.lean",
    "namespace LeanSwe.MiniLeaf\n" ++
    "structure LeafOpsM (m : Type → Type) where\n" ++
    "  ping : Nat → m Nat\n" ++
    "abbrev LeafOps := LeafOpsM IO\n" ++
    "end LeanSwe.MiniLeaf\n"),
  ("LeanSwe/MiniLeaf/Model.lean",
    "import LeanSwe.MiniLeaf.Types\n" ++
    "namespace LeanSwe.MiniLeaf.Model\n" ++
    "def leafWf (_ : Nat) : Bool := true\n" ++
    "def execLeaf {W : Type} (ops : LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
    "def allowedLeaf (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
    "end LeanSwe.MiniLeaf.Model\n"),
  ("LeanSwe/MiniLeaf/Impl.lean",
    "import LeanSwe.MiniLeaf.Types\n" ++
    "namespace LeanSwe.MiniLeaf.Internal\n" ++
    "def mkOps {m : Type → Type} [Monad m] (raw : Nat → m Nat) : LeafOpsM m :=\n" ++
    "  { ping := raw }\n" ++
    "end LeanSwe.MiniLeaf.Internal\n"),
  ("LeanSwe/MiniLeaf/Interface.lean",
    "import LeanSwe.MiniLeaf.Impl\n" ++
    "namespace LeanSwe.MiniLeaf\n" ++
    "@[extern \"mini_leaf_raw_ping\"]\n" ++
    "private opaque rawPing : Nat → BaseIO Nat\n" ++
    "def defaultOps : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\n" ++
    "end LeanSwe.MiniLeaf\n"),
  ("LeanSwe/MiniLeaf/Proofs.lean",
    "import Core.Obeys\n" ++
    "import LeanSwe.MiniLeaf.Model\n" ++
    "import LeanSwe.MiniLeaf.Interface\n" ++
    "namespace LeanSwe.MiniLeaf.Proofs\n" ++
    "theorem obeys_model :\n" ++
    "    Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf\n" ++
    "      Model.leafWf (fun {m} [Monad m] (ops : LeafOpsM m) => Internal.mkOps ops.ping)\n" ++
    "      Model.execLeaf Model.allowedLeaf :=\n" ++
    "  fun _ _ h => h\n" ++
    "end LeanSwe.MiniLeaf.Proofs\n"),
  ("LeanSwe/MiniComp/Types.lean",
    "namespace LeanSwe.MiniComp\n" ++
    "structure CompApiM (m : Type → Type) where\n" ++
    "  callPing : Nat → m Nat\n" ++
    "abbrev CompApi := CompApiM IO\n" ++
    "end LeanSwe.MiniComp\n"),
  ("LeanSwe/MiniComp/Model.lean",
    "import LeanSwe.MiniLeaf.Types\n" ++
    "import LeanSwe.MiniLeaf.Model\n" ++
    "import LeanSwe.MiniComp.Types\n" ++
    "namespace LeanSwe.MiniComp.Model\n" ++
    "def compWf (_ : Nat) : Bool := true\n" ++
    "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
    "def allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
    "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
    "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
    "end LeanSwe.MiniComp.Model\n"),
  ("LeanSwe/MiniComp/Impl.lean",
    "import LeanSwe.MiniLeaf.Types\n" ++
    "import LeanSwe.MiniComp.Types\n" ++
    "namespace LeanSwe.MiniComp.Internal\n" ++
    "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m :=\n" ++
    "  { callPing := fun n => leaf.ping n }\n" ++
    "end LeanSwe.MiniComp.Internal\n"),
  ("LeanSwe/MiniComp/Interface.lean",
    "import LeanSwe.MiniLeaf.Interface\n" ++
    "import LeanSwe.MiniComp.Impl\n" ++
    "namespace LeanSwe.MiniComp\n" ++
    "def defaultApi : CompApi := Internal.mkApiM LeanSwe.MiniLeaf.defaultOps\n" ++
    "def callPing (n : Nat) : IO Nat := defaultApi.callPing n\n" ++
    "end LeanSwe.MiniComp\n"),
  ("LeanSwe/MiniComp/Proofs.lean",
    "import Core.Obeys\n" ++
    "import LeanSwe.MiniComp.Model\n" ++
    "import LeanSwe.MiniComp.Interface\n" ++
    "namespace LeanSwe.MiniComp.Proofs\n" ++
    "theorem obeys_model :\n" ++
    "    Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw\n" ++
    "      Model.compWf Internal.mkApiM Model.execPkg Model.allowedPkg :=\n" ++
    "  fun _ _ h => h\n" ++
    "end LeanSwe.MiniComp.Proofs\n")
]

private def baselineBuildOrder : Array String := #[
  "LeanSwe/MiniPure/Types.lean",
  "LeanSwe/MiniPure/Model.lean",
  "LeanSwe/MiniPure/Impl.lean",
  "LeanSwe/MiniPure/Interface.lean",
  "LeanSwe/MiniPure/Proofs.lean",
  "LeanSwe/MiniLeaf/Types.lean",
  "LeanSwe/MiniLeaf/Model.lean",
  "LeanSwe/MiniLeaf/Impl.lean",
  "LeanSwe/MiniLeaf/Interface.lean",
  "LeanSwe/MiniLeaf/Proofs.lean",
  "LeanSwe/MiniComp/Types.lean",
  "LeanSwe/MiniComp/Model.lean",
  "LeanSwe/MiniComp/Impl.lean",
  "LeanSwe/MiniComp/Interface.lean",
  "LeanSwe/MiniComp/Proofs.lean"
]

private def baselineRootsCsv : String :=
  "LeanSwe.MiniPure.Proofs,LeanSwe.MiniLeaf.Proofs,LeanSwe.MiniComp.Proofs"

private def copyFileOrDir (src dst : System.FilePath) : IO Unit := do
  let out ← runCmd "cp" #["-a", src.toString, dst.toString]
  if out.exitCode != 0 then
    throw (IO.userError s!"cp -a {src} {dst} failed: {out.stderr}")

private def buildSyntheticRepo (baseDir realLibAbs : System.FilePath) : IO (System.FilePath × System.FilePath) := do
  let root := baseDir / "repo"
  let libDir := baseDir / "lib"
  IO.FS.createDirAll root
  IO.FS.createDirAll libDir
  symlinkCoreLib realLibAbs libDir
  writeFileCreatingParents (root / "scripts/package_manifest.json") baselineManifestJson
  for (rel, content) in baselineFiles do
    writeFileCreatingParents (root / rel) content
  let leanPath := s!"{libDir}:{realLibAbs}"
  for rel in baselineBuildOrder do
    let olean := (libDir / rel).withExtension "olean"
    compileLeanMod root leanPath (root / rel) olean
  return (root, libDir)

private def runAuditCase (bin libDir manifestPath : System.FilePath)
    (rootsCsv modelAllow hookAllow : String) : IO IO.Process.Output :=
  runCmd bin.toString #["--internal-manifest-audit", libDir.toString, manifestPath.toString, rootsCsv, modelAllow, hookAllow]

private def assertPass (label : String) (out : IO.Process.Output) : IO Unit := do
  if out.exitCode != 0 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected pass (exit 0), got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def assertFailWith (label expectedDiag : String) (out : IO.Process.Output) : IO Unit := do
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 || (combined.splitOn expectedDiag).length <= 1 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected failure containing '{expectedDiag}', got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def runMutantCase
    (bin tmpRoot baseDir realLibAbs : System.FilePath)
    (caseName : String)
    (mutate : System.FilePath → System.FilePath → String → IO (String × String × String))
    (expectedDiag? : Option String) : IO Unit := do
  let caseDir := tmpRoot / s!"case_{caseName}"
  copyFileOrDir baseDir caseDir
  let root := caseDir / "repo"
  let libDir := caseDir / "lib"
  let leanPath := s!"{libDir}:{realLibAbs}"
  let (rootsCsv, modelAllow, hookAllow) ← mutate root libDir leanPath
  let out ← runAuditCase bin libDir (root / "scripts/package_manifest.json") rootsCsv modelAllow hookAllow
  match expectedDiag? with
  | none => assertPass caseName out
  | some diag => assertFailWith caseName diag out
  IO.FS.removeDirAll caseDir

private def recompile (root libDir : System.FilePath) (leanPath : String) (rels : Array String) : IO Unit := do
  for rel in rels do
    compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")

/-- Run all synthetic positive and negative self-tests for `CheckPromises.lean` manifest and wiring checks. -/
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

    let baseOut ← runAuditCase bin baseLib (baseRoot / "scripts/package_manifest.json") baselineRootsCsv "" ""
    assertPass "baseline_compliant" baseOut

    let staleModelOut ← runAuditCase bin baseLib (baseRoot / "scripts/package_manifest.json")
      baselineRootsCsv "MISSING_OBEYS_MODEL|LeanSwe.MiniPure" ""
    assertFailWith "stale_model_presence_allowlist" "STALE_MODEL_PRESENCE_ALLOWLIST" staleModelOut

    let staleHookOut ← runAuditCase bin baseLib (baseRoot / "scripts/package_manifest.json")
      baselineRootsCsv "" "MIDDLE_HOOK|LeanSwe.MiniComp"
    assertFailWith "stale_middle_hook_allowlist" "STALE_MIDDLE_HOOK_ALLOWLIST" staleHookOut

    runMutantCase bin tmpRoot baseDir realLibAbs "middle_hook_scoped_ops" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Types.lean")
        ("namespace LeanSwe.MiniComp\n" ++
         "structure CompApiM (m : Type → Type) where\n" ++
         "  callPing : Nat → m Nat\n" ++
         "structure ScopedCompOpsM (m : Type → Type) where\n" ++
         "  runScoped : Nat → m Nat\n" ++
         "abbrev CompApi := CompApiM IO\n" ++
         "end LeanSwe.MiniComp\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Model.lean")
        ("import LeanSwe.MiniComp.Types\n" ++
         "namespace LeanSwe.MiniComp.Model\n" ++
         "def compWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : ScopedCompOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.runScoped req\n" ++
         "def allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
         "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "end LeanSwe.MiniComp.Model\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Impl.lean")
        ("import LeanSwe.MiniLeaf.Interface\n" ++
         "import LeanSwe.MiniComp.Types\n" ++
         "namespace LeanSwe.MiniComp.Internal\n" ++
         "def defaultScopedIoOps : ScopedCompOpsM IO := { runScoped := LeanSwe.MiniLeaf.defaultOps.ping }\n" ++
         "def mkScopedApiM {m : Type → Type} [Monad m] (ops : ScopedCompOpsM m) : CompApiM m :=\n" ++
         "  { callPing := ops.runScoped }\n" ++
         "end LeanSwe.MiniComp.Internal\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Interface.lean")
        ("import LeanSwe.MiniComp.Impl\n" ++
         "namespace LeanSwe.MiniComp\n" ++
         "def defaultApi : CompApi := Internal.mkScopedApiM Internal.defaultScopedIoOps\n" ++
         "def callPing (n : Nat) : IO Nat := defaultApi.callPing n\n" ++
         "end LeanSwe.MiniComp\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Proofs.lean")
        ("import Core.Obeys\n" ++
         "import LeanSwe.MiniComp.Model\n" ++
         "import LeanSwe.MiniComp.Interface\n" ++
         "namespace LeanSwe.MiniComp.Proofs\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw\n" ++
         "      Model.compWf Internal.mkScopedApiM Model.execPkg Model.allowedPkg :=\n" ++
         "  fun _ _ h => h\n" ++
         "end LeanSwe.MiniComp.Proofs\n")
      recompile root libDir leanPath #[
        "LeanSwe/MiniComp/Types.lean",
        "LeanSwe/MiniComp/Model.lean",
        "LeanSwe/MiniComp/Impl.lean",
        "LeanSwe/MiniComp/Interface.lean",
        "LeanSwe/MiniComp/Proofs.lean"
      ]
      let allowPass ← runAuditCase bin libDir (root / "scripts/package_manifest.json")
        baselineRootsCsv "" "MIDDLE_HOOK|LeanSwe.MiniComp"
      assertPass "middle_hook_allowlisted" allowPass
      return (baselineRootsCsv, "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    runMutantCase bin tmpRoot baseDir realLibAbs "missing_obeys_model" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.Model\nimport LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\nend LeanSwe.MiniPure.Proofs\n"
      recompile root libDir leanPath #["LeanSwe/MiniPure/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "MANIFEST_MISSING_OBEYS_MODEL")

    runMutantCase bin tmpRoot baseDir realLibAbs "missing_model" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniPure/Proofs.lean")
        "import LeanSwe.MiniPure.Interface\nnamespace LeanSwe.MiniPure.Proofs\nend LeanSwe.MiniPure.Proofs\n"
      recompile root libDir leanPath #["LeanSwe/MiniPure/Proofs.lean"]
      return (baselineRootsCsv, "MISSING_OBEYS_MODEL|LeanSwe.MiniPure", "")
    ) (some "MANIFEST_MISSING_MODEL")

    runMutantCase bin tmpRoot baseDir realLibAbs "vacuous_obeys_model" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniPure/Proofs.lean")
        ("import Core.Obeys\n" ++
         "import LeanSwe.MiniPure.Model\n" ++
         "import LeanSwe.MiniPure.Interface\n" ++
         "namespace LeanSwe.MiniPure.Proofs\n" ++
         "theorem obeys_model : Core.ObeysPure LeanSwe.MiniPure.eval (fun _ _ => True) := fun _ => trivial\n" ++
         "end LeanSwe.MiniPure.Proofs\n")
      recompile root libDir leanPath #["LeanSwe/MiniPure/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "VACUOUS_OR_INVALID_OBEYS_MODEL")

    runMutantCase bin tmpRoot baseDir realLibAbs "forbidden_extern_non_boundary" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniPure/Interface.lean")
        ("import LeanSwe.MiniPure.Impl\n" ++
         "namespace LeanSwe.MiniPure\n" ++
         "@[extern \"bad_pure_extern\"]\n" ++
         "private opaque badExtern : BaseIO Nat\n" ++
         "def eval (n : Nat) : Nat := Internal.evalImpl n\n" ++
         "end LeanSwe.MiniPure\n")
      recompile root libDir leanPath #["LeanSwe/MiniPure/Interface.lean", "LeanSwe/MiniPure/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "FORBIDDEN_EXTERN_IN_NON_BOUNDARY")

    runMutantCase bin tmpRoot baseDir realLibAbs "public_extern_in_boundary" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniLeaf/Interface.lean")
        ("import LeanSwe.MiniLeaf.Impl\n" ++
         "namespace LeanSwe.MiniLeaf\n" ++
         "@[extern \"mini_leaf_raw_ping\"]\n" ++
         "opaque rawPing : Nat → BaseIO Nat\n" ++
         "def defaultOps : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\n" ++
         "end LeanSwe.MiniLeaf\n")
      recompile root libDir leanPath #[
        "LeanSwe/MiniLeaf/Interface.lean",
        "LeanSwe/MiniLeaf/Proofs.lean",
        "LeanSwe/MiniComp/Interface.lean",
        "LeanSwe/MiniComp/Proofs.lean"
      ]
      return (baselineRootsCsv, "", "")
    ) (some "INVALID_EXTERN_PLACEMENT")

    runMutantCase bin tmpRoot baseDir realLibAbs "unregistered_ghost_pkg" (fun root _ _ => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        ("{\n" ++
         "  \"version\": 1,\n" ++
         "  \"packages\": {\n" ++
         "    \"LeanSwe.MiniLeaf\": {\n" ++
         "      \"kind\": \"model\", \"purity\": \"nondet_io\", \"deps\": [], \"external_boundary\": true\n" ++
         "    },\n" ++
         "    \"LeanSwe.MiniComp\": {\n" ++
         "      \"kind\": \"model\", \"purity\": \"mixed\", \"deps\": [\"LeanSwe.MiniLeaf\"], \"external_boundary\": false\n" ++
         "    }\n" ++
         "  }\n" ++
         "}\n")
      return (baselineRootsCsv, "", "")
    ) (some "MANIFEST_UNREGISTERED_PACKAGE")

    runMutantCase bin tmpRoot baseDir realLibAbs "builder_mismatch" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Impl.lean")
        ("import LeanSwe.MiniLeaf.Types\n" ++
         "import LeanSwe.MiniComp.Types\n" ++
         "namespace LeanSwe.MiniComp.Internal\n" ++
         "def mkApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m :=\n" ++
         "  { callPing := fun n => leaf.ping n }\n" ++
         "def mkAltApiM {m : Type → Type} [Monad m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) : CompApiM m :=\n" ++
         "  { callPing := fun n => leaf.ping (n + 1) }\n" ++
         "end LeanSwe.MiniComp.Internal\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Interface.lean")
        ("import LeanSwe.MiniLeaf.Interface\n" ++
         "import LeanSwe.MiniComp.Impl\n" ++
         "namespace LeanSwe.MiniComp\n" ++
         "def defaultApi : CompApi := Internal.mkAltApiM LeanSwe.MiniLeaf.defaultOps\n" ++
         "def callPing (n : Nat) : IO Nat := defaultApi.callPing n\n" ++
         "end LeanSwe.MiniComp\n")
      recompile root libDir leanPath #[
        "LeanSwe/MiniComp/Impl.lean",
        "LeanSwe/MiniComp/Interface.lean",
        "LeanSwe/MiniComp/Proofs.lean"
      ]
      return (baselineRootsCsv, "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    runMutantCase bin tmpRoot baseDir realLibAbs "external_cli_compliant" (fun root _ _ => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        (baselineManifestJson.replace
          "\"LeanSwe.MiniComp\": {\n      \"kind\": \"model\",\n      \"purity\": \"mixed\",\n      \"deps\": [\"LeanSwe.MiniLeaf\"],\n      \"external_boundary\": false,"
          "\"LeanSwe.MiniComp\": {\n      \"kind\": \"model\",\n      \"purity\": \"nondet_io\",\n      \"deps\": [\"LeanSwe.MiniLeaf\"],\n      \"external_boundary\": true,")
      return (baselineRootsCsv, "", "")
    ) none

    runMutantCase bin tmpRoot baseDir realLibAbs "external_cli_middle_hook" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "scripts/package_manifest.json")
        (baselineManifestJson.replace
          "\"LeanSwe.MiniComp\": {\n      \"kind\": \"model\",\n      \"purity\": \"mixed\",\n      \"deps\": [\"LeanSwe.MiniLeaf\"],\n      \"external_boundary\": false,"
          "\"LeanSwe.MiniComp\": {\n      \"kind\": \"model\",\n      \"purity\": \"nondet_io\",\n      \"deps\": [\"LeanSwe.MiniLeaf\"],\n      \"external_boundary\": true,")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Interface.lean")
        ("import LeanSwe.MiniLeaf.Interface\n" ++
         "import LeanSwe.MiniComp.Impl\n" ++
         "namespace LeanSwe.MiniComp\n" ++
         "def defaultRawOps : LeanSwe.MiniLeaf.LeafOps := { ping := LeanSwe.MiniLeaf.defaultOps.ping }\n" ++
         "def defaultApi : CompApi := Internal.mkApiM defaultRawOps\n" ++
         "def callPing (n : Nat) : IO Nat := defaultApi.callPing n\n" ++
         "end LeanSwe.MiniComp\n")
      recompile root libDir leanPath #[
        "LeanSwe/MiniComp/Interface.lean",
        "LeanSwe/MiniComp/Proofs.lean"
      ]
      return (baselineRootsCsv, "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    runMutantCase bin tmpRoot baseDir realLibAbs "vacuous_raw_allowed_false" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Model.lean")
        ("import LeanSwe.MiniLeaf.Types\n" ++
         "import LeanSwe.MiniLeaf.Model\n" ++
         "import LeanSwe.MiniComp.Types\n" ++
         "namespace LeanSwe.MiniComp.Model\n" ++
         "def compWf (_ : Nat) : Bool := true\n" ++
         "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\n" ++
         "def allowedRaw (_ _ _ _ : Nat) : Prop := False\n" ++
         "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\n" ++
         "def allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
         "end LeanSwe.MiniComp.Model\n")
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Proofs.lean")
        ("import Core.Obeys\n" ++
         "import LeanSwe.MiniComp.Model\n" ++
         "import LeanSwe.MiniComp.Interface\n" ++
         "namespace LeanSwe.MiniComp.Proofs\n" ++
         "theorem obeys_model :\n" ++
         "    Core.ObeysStepFrom id Model.compWf Model.execRaw Model.allowedRaw\n" ++
         "      Model.compWf Internal.mkApiM Model.execPkg Model.allowedPkg :=\n" ++
         "  fun _ _ h w req hw => False.elim (h w req hw)\n" ++
         "end LeanSwe.MiniComp.Proofs\n")
      recompile root libDir leanPath #["LeanSwe/MiniComp/Model.lean", "LeanSwe/MiniComp/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "VACUOUS_OR_INVALID_OBEYS_MODEL")

    runMutantCase bin tmpRoot baseDir realLibAbs "renamed_default_client_bypass" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Interface.lean")
        ("import LeanSwe.MiniLeaf.Interface\n" ++
         "import LeanSwe.MiniComp.Impl\n" ++
         "namespace LeanSwe.MiniComp\n" ++
         "def defaultClient : CompApi := Internal.mkApiM { ping := LeanSwe.MiniLeaf.defaultOps.ping }\n" ++
         "def callPing (n : Nat) : IO Nat := defaultClient.callPing n\n" ++
         "end LeanSwe.MiniComp\n")
      recompile root libDir leanPath #["LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    runMutantCase bin tmpRoot baseDir realLibAbs "decoy_defaultApi_with_hooked_defaultClient" (fun root libDir leanPath => do
      writeFileCreatingParents (root / "LeanSwe/MiniComp/Interface.lean")
        ("import LeanSwe.MiniLeaf.Interface\n" ++
         "import LeanSwe.MiniComp.Impl\n" ++
         "namespace LeanSwe.MiniComp\n" ++
         "def defaultApi : CompApi := Internal.mkApiM LeanSwe.MiniLeaf.defaultOps\n" ++
         "def defaultClient : CompApi := Internal.mkApiM { ping := LeanSwe.MiniLeaf.defaultOps.ping }\n" ++
         "def callPing (n : Nat) : IO Nat := defaultClient.callPing n\n" ++
         "end LeanSwe.MiniComp\n")
      recompile root libDir leanPath #["LeanSwe/MiniComp/Interface.lean", "LeanSwe/MiniComp/Proofs.lean"]
      return (baselineRootsCsv, "", "")
    ) (some "MIDDLE_HOOK_VIOLATION")

    IO.println "CHECK_PROMISES_SELF_TEST: passed=16 failed=0"
    return 0
  finally
    if ← tmpRoot.pathExists then
      IO.FS.removeDirAll tmpRoot
