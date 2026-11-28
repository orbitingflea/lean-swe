import Lean

/-!
Synthetic `.olean` self-tests (`scripts/CheckPromisesConcCellTest.lean`) for
`Core.ObeysStepFromConcCell`, `defaultOpsBase`, and private `Interface` `Core.ioStateCell`
initializer auditing in `scripts/CheckPromises.lean`.
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

private def copyFileOrDir (src dst : System.FilePath) : IO Unit := do
  let out ← runCmd "cp" #["-a", src.toString, dst.toString]
  if out.exitCode != 0 then throw (IO.userError s!"cp -a {src} {dst} failed: {out.stderr}")

private def baselineRootsCsv : String :=
  "LeanSwe.MiniPure.Proofs,LeanSwe.MiniInv.Proofs,LeanSwe.MiniProp.Proofs,LeanSwe.MiniLeaf.Proofs,LeanSwe.MiniComp.Proofs"

private def runAuditCase (bin libDir manifestPath : System.FilePath)
    (rootsCsv : String) : IO IO.Process.Output :=
  runCmd bin.toString #["--internal-manifest-audit", libDir.toString, manifestPath.toString, rootsCsv]

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

private def writeAndRecompile (root libDir : System.FilePath) (leanPath : String)
    (files : Array (String × String)) : IO Unit := do
  for (rel, content) in files do writeFileCreatingParents (root / rel) content
  for (rel, _) in files do
    compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")

/-- Run `Core.ObeysStepFromConcCell` and `Core.ioStateCell` positive/negative self-tests. -/
def main (args : List String) : IO UInt32 := do
  let [binStr, tmpRootStr, baseDirStr, realLibStr] := args
    | IO.eprintln "Expected arguments: <bin> <tmpRoot> <baseDir> <realLibAbs>"; return 1
  let bin : System.FilePath := binStr
  let tmpRoot : System.FilePath := tmpRootStr
  let baseDir : System.FilePath := baseDirStr
  let realLibAbs : System.FilePath := realLibStr

  let runCase (caseName : String) (expectedDiag? : Option String)
      (mutate : System.FilePath → System.FilePath → String → IO Unit) : IO Unit := do
    let caseDir := tmpRoot / s!"case_{caseName}"
    copyFileOrDir baseDir caseDir
    let root := caseDir / "repo"
    let libDir := caseDir / "lib"
    let leanPath := s!"{libDir}:{realLibAbs}"
    mutate root libDir leanPath
    let out ← runAuditCase bin libDir (root / "scripts/package_manifest.json") baselineRootsCsv
    match expectedDiag? with
    | none => assertPass caseName out
    | some diag => assertFailWith caseName diag out
    IO.FS.removeDirAll caseDir

  let compModelHdr := "import LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Model\ndef compWf (_ : Nat) : Bool := true\n"
  let concImplHdr := "import Core.ConcOps\nimport LeanSwe.MiniLeaf.Types\nimport LeanSwe.MiniComp.Types\nnamespace LeanSwe.MiniComp.Internal\n"
  let compIfaceHdr := "import Core.ConcOps\nimport LeanSwe.MiniLeaf.Interface\nimport LeanSwe.MiniComp.Impl\nnamespace LeanSwe.MiniComp\n"
  let concProofHdr := "import Core.ConcOps\nimport LeanSwe.MiniComp.Model\nimport LeanSwe.MiniComp.Interface\nnamespace LeanSwe.MiniComp.Proofs\n"
  let rawPingIfaceHdr := "import LeanSwe.MiniLeaf.Impl\nnamespace LeanSwe.MiniLeaf\n@[extern \"leanswe_mini_leaf_raw_ping\"]\nprivate opaque rawPing : Nat → BaseIO Nat\n"
  let leafProofHdr := "import Core.Obeys\nimport LeanSwe.MiniLeaf.Model\nimport LeanSwe.MiniLeaf.Interface\nnamespace LeanSwe.MiniLeaf.Proofs\n"

  let cellModSrc := compModelHdr ++ "abbrev CellFam (_ _ : Type → Type) : Type := Nat\ndef mapS (r c : Nat) : Nat := r + c\ndef cellToModel {R T : Type → Type} (c : CellFam R T) : Nat := c\n" ++
    "def execRaw {W : Type} (ops : LeanSwe.MiniLeaf.LeafOpsM (StateM W)) (req : Nat) : StateM W Nat := ops.ping req\ndef allowedRaw (s req out s' : Nat) : Prop := out = req ∧ s' = s\n" ++
    "def execPkg {W : Type} (api : CompApiM (StateM W)) (req : Nat) : StateM W Nat := api.callPing req\ndef allowedPkg (s req out s' : Nat) : Prop := out = req ∧ s' = s\nend LeanSwe.MiniComp.Model\n"
  let cellImplSrc (extra : String := "") := "import LeanSwe.MiniComp.Model\n" ++ concImplHdr ++ extra ++
    "def mkFullApiM {m : Type → Type} [Monad m] [MonadFinally m] (leaf : LeanSwe.MiniLeaf.LeafOpsM m) (conc : Core.ConcOpsM m) (cell : Core.StateCellM m (Model.CellFam conc.Ref conc.TaskHandle)) : CompApiM m :=\n" ++
    "  { callPing := fun n => do let _ := conc; let _ ← cell.get; leaf.ping n }\nend LeanSwe.MiniComp.Internal\n"
  let cellProofSrc := concProofHdr ++ "theorem obeys_model : Core.ObeysStepFromConcCell (CellS := Model.CellFam) Model.mapS Model.cellToModel Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkFullApiM Model.execPkg Model.allowedPkg := by\n" ++
    "  intro W projRaw raw conc projCell cell hraw hfr _ hcell w req _; have hc := hcell.1 w; cases hg : cell.get.run w with | mk c0 w1 =>\n" ++
    "    rw [hg] at hc; dsimp only at hc; have hr := hraw w1 req rfl; have hcf := hfr w1 req rfl; dsimp only [Core.ObeysStep, Model.execRaw] at hr hcf; cases hp : (raw.ping req).run w1 with | mk out w2 =>\n" ++
    "      rw [hp] at hr hcf; dsimp only [Model.allowedRaw] at hr; dsimp only [Core.ObeysStep, Model.execPkg, Model.allowedPkg, Model.mapS, Model.cellToModel, Internal.mkFullApiM, bind, StateT.bind, StateT.run, Id.run] at hg hp ⊢\n" ++
    "      rw [hg]; dsimp only; rw [hp]; dsimp only; exact ⟨hr.1, by rw [hr.2, hcf, hc.2.1, hc.2.2]⟩\nend LeanSwe.MiniComp.Proofs\n"
  let cellLeafIface := rawPingIfaceHdr ++ "def defaultOpsBase : LeafOps := Internal.mkOps (fun n => liftM (rawPing n))\ndef defaultOps : LeafOps := defaultOpsBase\nend LeanSwe.MiniLeaf\n"
  let cellLeafProof := leafProofHdr ++ "theorem obeys_model : Core.ObeysStepFrom id Model.leafWf Model.execLeaf Model.allowedLeaf Model.leafWf (fun {m} [Monad m] (ops : LeafOpsM m) => Internal.mkOps ops.ping) Model.execLeaf Model.allowedLeaf := fun _ _ h => h\nend LeanSwe.MiniLeaf.Proofs\n"

  runCase "conc_cell_stepfrom_compliant" none fun root libDir leanPath => do
    writeAndRecompile root libDir leanPath #[
      ("LeanSwe/MiniLeaf/Interface.lean", cellLeafIface), ("LeanSwe/MiniLeaf/Proofs.lean", cellLeafProof),
      ("LeanSwe/MiniComp/Model.lean", cellModSrc), ("LeanSwe/MiniComp/Impl.lean", cellImplSrc),
      ("LeanSwe/MiniComp/Interface.lean", compIfaceHdr ++ "private initialize gCell : IO.Ref Nat ← IO.mkRef 0\ndef defaultApi : CompApi := Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOpsBase Core.ioConcOps (Core.ioStateCell gCell)\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"),
      ("LeanSwe/MiniComp/Proofs.lean", cellProofSrc)]
    assertPassWith "print_sig_conc_cell" "Core.ObeysStepFromConcCell"
      (← runPrintSigCase bin libDir (root / "scripts/package_manifest.json") baselineRootsCsv "LeanSwe.MiniComp")

  runCase "conc_cell_public_init_rejected" (some "MIDDLE_HOOK_VIOLATION") fun root libDir leanPath =>
    writeAndRecompile root libDir leanPath #[
      ("LeanSwe/MiniComp/Model.lean", cellModSrc), ("LeanSwe/MiniComp/Impl.lean", cellImplSrc),
      ("LeanSwe/MiniComp/Interface.lean", compIfaceHdr ++ "initialize gCell : IO.Ref Nat ← IO.mkRef 0\ndef defaultApi : CompApi := Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOps Core.ioConcOps (Core.ioStateCell gCell)\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"),
      ("LeanSwe/MiniComp/Proofs.lean", cellProofSrc)]

  runCase "conc_cell_impl_init_dep_rejected" (some "MIDDLE_HOOK_VIOLATION") fun root libDir leanPath =>
    writeAndRecompile root libDir leanPath #[
      ("LeanSwe/MiniComp/Model.lean", cellModSrc), ("LeanSwe/MiniComp/Impl.lean", cellImplSrc "def seedVal : Nat := 7\n"),
      ("LeanSwe/MiniComp/Interface.lean", compIfaceHdr ++ "private initialize gCell : IO.Ref Nat ← IO.mkRef Internal.seedVal\ndef defaultApi : CompApi := Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOps Core.ioConcOps (Core.ioStateCell gCell)\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"),
      ("LeanSwe/MiniComp/Proofs.lean", cellProofSrc)]

  let validCellIface := compIfaceHdr ++ "private initialize gCell : IO.Ref Nat ← IO.mkRef 0\ndef defaultApi : CompApi := Internal.mkFullApiM LeanSwe.MiniLeaf.defaultOpsBase Core.ioConcOps (Core.ioStateCell gCell)\ndef callPing (n : Nat) : IO Nat := defaultApi.callPing n\nend LeanSwe.MiniComp\n"

  runCase "conc_cell_lambda_id_mapS_rejected" (some "stepFromConcCell mapS") fun root libDir leanPath =>
    writeAndRecompile root libDir leanPath #[
      ("LeanSwe/MiniLeaf/Interface.lean", cellLeafIface), ("LeanSwe/MiniLeaf/Proofs.lean", cellLeafProof),
      ("LeanSwe/MiniComp/Model.lean", cellModSrc), ("LeanSwe/MiniComp/Impl.lean", cellImplSrc),
      ("LeanSwe/MiniComp/Interface.lean", validCellIface),
      ("LeanSwe/MiniComp/Proofs.lean", concProofHdr ++
        "theorem obeys_model : Core.ObeysStepFromConcCell (CellS := Model.CellFam) (fun _ => id) Model.cellToModel Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkFullApiM Model.execPkg Model.allowedPkg := by\n" ++
        "  intro W projRaw raw conc projCell cell hraw hfr _ hcell w req _; have hc := hcell.1 w; cases hg : cell.get.run w with | mk c0 w1 =>\n" ++
        "    rw [hg] at hc; dsimp only at hc; have hr := hraw w1 req rfl; have hcf := hfr w1 req rfl; dsimp only [Core.ObeysStep, Model.execRaw] at hr hcf; cases hp : (raw.ping req).run w1 with | mk out w2 =>\n" ++
        "      rw [hp] at hr hcf; dsimp only [Model.allowedRaw] at hr; dsimp only [Core.ObeysStep, Model.execPkg, Model.allowedPkg, Model.cellToModel, Internal.mkFullApiM, id, bind, StateT.bind, StateT.run, Id.run] at hg hp ⊢\n" ++
        "      rw [hg]; dsimp only; rw [hp]; dsimp only; exact ⟨hr.1, by rw [hcf, hc.2.1]⟩\nend LeanSwe.MiniComp.Proofs\n")]

  runCase "conc_cell_lambda_id_cellToModel_rejected" (some "stepFromConcCell cellToModel") fun root libDir leanPath =>
    writeAndRecompile root libDir leanPath #[
      ("LeanSwe/MiniLeaf/Interface.lean", cellLeafIface), ("LeanSwe/MiniLeaf/Proofs.lean", cellLeafProof),
      ("LeanSwe/MiniComp/Model.lean", cellModSrc), ("LeanSwe/MiniComp/Impl.lean", cellImplSrc),
      ("LeanSwe/MiniComp/Interface.lean", validCellIface),
      ("LeanSwe/MiniComp/Proofs.lean", concProofHdr ++
        "theorem obeys_model : Core.ObeysStepFromConcCell (CellS := Model.CellFam) Model.mapS (fun {_ _} => id) Model.compWf Model.execRaw Model.allowedRaw Model.compWf Internal.mkFullApiM Model.execPkg Model.allowedPkg := by\n" ++
        "  intro W projRaw raw conc projCell cell hraw hfr _ hcell w req _; have hc := hcell.1 w; cases hg : cell.get.run w with | mk c0 w1 =>\n" ++
        "    rw [hg] at hc; dsimp only at hc; have hr := hraw w1 req rfl; have hcf := hfr w1 req rfl; dsimp only [Core.ObeysStep, Model.execRaw] at hr hcf; cases hp : (raw.ping req).run w1 with | mk out w2 =>\n" ++
        "      rw [hp] at hr hcf; dsimp only [Model.allowedRaw] at hr; dsimp only [Core.ObeysStep, Model.execPkg, Model.allowedPkg, Model.mapS, Internal.mkFullApiM, id, bind, StateT.bind, StateT.run, Id.run] at hg hp ⊢\n" ++
        "      rw [hg]; dsimp only; rw [hp]; dsimp only; exact ⟨hr.1, by rw [hr.2, hcf, hc.2.1, hc.2.2]⟩\nend LeanSwe.MiniComp.Proofs\n")]

  return 0
