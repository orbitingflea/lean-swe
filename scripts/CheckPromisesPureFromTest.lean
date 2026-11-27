import Lean

/-!
Companion positive and negative synthetic `.olean` self-tests (`scripts/CheckPromisesPureFromTest.lean`)
for compositional pure contracts (`Core.ObeysPureFrom` and `Core.ObeysInverseRenderFrom`) in
`scripts/CheckPromises.lean`, invoked from `scripts/CheckPromisesTest.lean`.
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

private def symlinkCoreLib (realLibDir targetLibDir : System.FilePath) : IO Unit := do
  let r1 ← runCmd "ln" #["-sfn", (realLibDir / "Core").toString, (targetLibDir / "Core").toString]
  if r1.exitCode != 0 then throw (IO.userError s!"ln Core failed: {r1.stderr}")
  if ← (realLibDir / "Core.olean").pathExists then
    let r2 ← runCmd "ln" #["-sfn", (realLibDir / "Core.olean").toString, (targetLibDir / "Core.olean").toString]
    if r2.exitCode != 0 then throw (IO.userError s!"ln Core.olean failed: {r2.stderr}")

private def copyFileOrDir (src dst : System.FilePath) : IO Unit := do
  let out ← runCmd "cp" #["-a", src.toString, dst.toString]
  if out.exitCode != 0 then throw (IO.userError s!"cp -a {src} {dst} failed: {out.stderr}")

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

private def manifestJson (docDeps : String := "\"LeanSwe.MiniNum\"") : String :=
  "{\n  \"version\": 1,\n  \"packages\": {\n" ++
  "    \"LeanSwe.MiniNum\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false, \"spec_style\": \"pure_eq\"},\n" ++
  s!"    \"LeanSwe.MiniDoc\": \{\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [{docDeps}], \"external_boundary\": false, \"spec_style\": \"inverse_render\"}\n" ++
  "  }\n}\n"

private def rootsCsv : String := "LeanSwe.MiniNum.Proofs,LeanSwe.MiniDoc.Proofs"

private def baseFiles : Array (String × String) := #[
  ("LeanSwe/MiniNum/Types.lean",
    "namespace LeanSwe.MiniNum\nstructure NumApi where\n  fmt : Nat → Nat\nend LeanSwe.MiniNum\n"),
  ("LeanSwe/MiniNum/Model.lean",
    "import Core.Obeys\nimport LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Model\n" ++
    "def allowedFmt (n out : Nat) : Prop := out = n + 1\n" ++
    "def ObeysApi (api : NumApi) : Prop := Core.ObeysPure api.fmt allowedFmt\n" ++
    "def modelApi : NumApi := { fmt := fun n => n + 1 }\n" ++
    "theorem obeysApi_satisfiable : ∃ api : NumApi, ObeysApi api := ⟨modelApi, fun _ => rfl⟩\n" ++
    "end LeanSwe.MiniNum.Model\n"),
  ("LeanSwe/MiniNum/Impl.lean",
    "import LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Internal\n" ++
    "def fmtImpl (n : Nat) : Nat := n + 1\ndef defaultApi : NumApi := { fmt := fmtImpl }\nend LeanSwe.MiniNum.Internal\n"),
  ("LeanSwe/MiniNum/Interface.lean",
    "import LeanSwe.MiniNum.Impl\nnamespace LeanSwe.MiniNum\n" ++
    "def defaultApi : NumApi := Internal.defaultApi\ndef fmt (n : Nat) : Nat := defaultApi.fmt n\nend LeanSwe.MiniNum\n"),
  ("LeanSwe/MiniNum/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniNum.Model\nimport LeanSwe.MiniNum.Interface\nnamespace LeanSwe.MiniNum.Proofs\n" ++
    "theorem obeys_model : Core.ObeysPure LeanSwe.MiniNum.fmt Model.allowedFmt := fun _ => rfl\nend LeanSwe.MiniNum.Proofs\n"),
  ("LeanSwe/MiniDoc/Types.lean",
    "namespace LeanSwe.MiniDoc\nstructure DocErr where\n  message : String\n" ++
    "structure DocApi where\n  parse : Nat → Except DocErr Nat\n  format : Nat → Nat\n  idPoly : {α : Type} → α → Option α\nend LeanSwe.MiniDoc\n"),
  ("LeanSwe/MiniDoc/Model.lean",
    "import LeanSwe.MiniDoc.Types\nnamespace LeanSwe.MiniDoc.Model\n" ++
    "def render (n : Nat) (_ : Unit) : Option Nat := some (n + 1)\n" ++
    "def wf (_ : Nat) : Prop := True\ndef equiv (a b : Nat) : Prop := a = b\n" ++
    "def allowedFormat (n out : Nat) : Prop := out = n + 1\n" ++
    "def idPolyModel {α : Type} (x : α) : Option α := some x\nend LeanSwe.MiniDoc.Model\n"),
  ("LeanSwe/MiniDoc/Impl.lean",
    "import LeanSwe.MiniNum.Types\nimport LeanSwe.MiniDoc.Types\nnamespace LeanSwe.MiniDoc.Internal\n" ++
    "def mkApi (num : LeanSwe.MiniNum.NumApi) : DocApi :=\n" ++
    "  { parse := fun raw => if raw == 0 then .error { message := \"zero\" } else if num.fmt (raw - 1) == raw then .ok (raw - 1) else .error { message := \"bad\" }\n" ++
    "  , format := num.fmt\n  , idPoly := fun x => some x }\nend LeanSwe.MiniDoc.Internal\n"),
  ("LeanSwe/MiniDoc/Interface.lean",
    "import LeanSwe.MiniNum.Interface\nimport LeanSwe.MiniDoc.Impl\nnamespace LeanSwe.MiniDoc\n" ++
    "def defaultApi : DocApi := Internal.mkApi LeanSwe.MiniNum.defaultApi\n" ++
    "def parse (raw : Nat) : Except DocErr Nat := defaultApi.parse raw\n" ++
    "def format (n : Nat) : Nat := defaultApi.format n\n" ++
    "def idPoly {α : Type} (x : α) : Option α := defaultApi.idPoly x\nend LeanSwe.MiniDoc\n"),
  ("LeanSwe/MiniDoc/Proofs.lean",
    "import Core.Obeys\nimport LeanSwe.MiniNum.Model\nimport LeanSwe.MiniDoc.Model\nimport LeanSwe.MiniDoc.Interface\nnamespace LeanSwe.MiniDoc.Proofs\n" ++
    "theorem obeys_model :\n" ++
    "    Core.ObeysInverseRenderFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.parse Model.render Model.wf Model.equiv DocErr.message ∧\n" ++
    "    Core.ObeysPureFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.format Model.allowedFormat ∧\n" ++
    "    (∀ {α : Type}, Core.ObeysPureEq (@LeanSwe.MiniDoc.idPoly α) (@Model.idPolyModel α)) := by\n" ++
    "  refine ⟨?_, fun num hnum n => hnum n, fun _ => rfl⟩\n" ++
    "  intro num hnum raw\n" ++
    "  cases raw with\n" ++
    "  | zero => exact ⟨by decide, fun a _ hr => by simp [Model.render] at hr⟩\n" ++
    "  | succ m =>\n" ++
    "    have hm : num.fmt m = m + 1 := hnum m\n" ++
    "    simp [Internal.mkApi, Core.InverseRenderSpec, Model.render, Model.wf, Model.equiv, hm]\n" ++
    "end LeanSwe.MiniDoc.Proofs\n")
]

private def buildOrder : Array String := #[
  "LeanSwe/MiniNum/Types.lean", "LeanSwe/MiniNum/Model.lean", "LeanSwe/MiniNum/Impl.lean",
  "LeanSwe/MiniNum/Interface.lean", "LeanSwe/MiniNum/Proofs.lean",
  "LeanSwe/MiniDoc/Types.lean", "LeanSwe/MiniDoc/Model.lean", "LeanSwe/MiniDoc/Impl.lean",
  "LeanSwe/MiniDoc/Interface.lean", "LeanSwe/MiniDoc/Proofs.lean"
]

/-- Execute all `ObeysPureFrom` and `ObeysInverseRenderFrom` self-test cases. -/
def main (args : List String) : IO UInt32 := do
  let [binStr, tmpRootStr, realLibStr] := args
    | do IO.eprintln "USAGE: CheckPromisesPureFromTest <bin> <tmpRoot> <realLibAbs>"; return 1
  let bin : System.FilePath := binStr
  let suiteDir := System.FilePath.mk tmpRootStr / "pure_from_suite"
  let realLibAbs : System.FilePath := realLibStr
  let baseDir := suiteDir / "base"
  let baseRoot := baseDir / "repo"
  let baseLib := baseDir / "lib"
  IO.FS.createDirAll baseRoot
  IO.FS.createDirAll baseLib
  symlinkCoreLib realLibAbs baseLib
  writeFileCreatingParents (baseRoot / "scripts/package_manifest.json") (manifestJson)
  for (rel, src) in baseFiles do writeFileCreatingParents (baseRoot / rel) src
  let baseLeanPath := s!"{baseLib}:{realLibAbs}"
  for rel in buildOrder do
    compileLeanMod baseRoot baseLeanPath (baseRoot / rel) ((baseLib / rel).withExtension "olean")

  let runAudit (libDir manPath : System.FilePath) : IO IO.Process.Output :=
    runCmd bin.toString #["--internal-manifest-audit", libDir.toString, manPath.toString, rootsCsv]
  let runPrintSig (libDir manPath : System.FilePath) (pkg : String) : IO IO.Process.Output :=
    runCmd bin.toString #["--internal-print-obeys-sig", libDir.toString, manPath.toString, rootsCsv, pkg]

  assertPass "pure_from_compliant" (← runAudit baseLib (baseRoot / "scripts/package_manifest.json"))
  let sigOut ← runPrintSig baseLib (baseRoot / "scripts/package_manifest.json") "LeanSwe.MiniDoc"
  assertPassWith "print_sig_inv_render_from"
    "Core.ObeysInverseRenderFrom LeanSwe.MiniNum.Model.ObeysApi LeanSwe.MiniDoc.Internal.mkApi LeanSwe.MiniDoc.DocApi.parse" sigOut
  assertPassWith "print_sig_pure_from"
    "Core.ObeysPureFrom LeanSwe.MiniNum.Model.ObeysApi LeanSwe.MiniDoc.Internal.mkApi LeanSwe.MiniDoc.DocApi.format" sigOut

  let runMutant (name expectedDiag : String) (files : Array (String × String))
      (recomp : Array String) (manOverride? : Option String := none) : IO Unit := do
    let cDir := suiteDir / s!"case_{name}"
    copyFileOrDir baseDir cDir
    let root := cDir / "repo"
    let libDir := cDir / "lib"
    let leanPath := s!"{libDir}:{realLibAbs}"
    if let some mJson := manOverride? then
      writeFileCreatingParents (root / "scripts/package_manifest.json") mJson
    for (rel, src) in files do writeFileCreatingParents (root / rel) src
    for rel in recomp do
      compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")
    assertFailWith name expectedDiag (← runAudit libDir (root / "scripts/package_manifest.json"))
    IO.FS.removeDirAll cDir

  runMutant "pure_from_vacuous_dep_obeys_rejected" "VACUOUS_OR_INVALID_OBEYS_MODEL" #[
    ("LeanSwe/MiniNum/Model.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Model\n" ++
     "def allowedFmt (n out : Nat) : Prop := out = n + 1\ndef ObeysApi (_ : NumApi) : Prop := False\nend LeanSwe.MiniNum.Model\n"),
    ("LeanSwe/MiniDoc/Proofs.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Model\nimport LeanSwe.MiniDoc.Model\nimport LeanSwe.MiniDoc.Interface\nnamespace LeanSwe.MiniDoc.Proofs\n" ++
     "theorem obeys_model :\n" ++
     "    Core.ObeysInverseRenderFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.parse Model.render Model.wf Model.equiv DocErr.message ∧\n" ++
     "    Core.ObeysPureFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.format Model.allowedFormat ∧\n" ++
     "    (∀ {α : Type}, Core.ObeysPureEq (@LeanSwe.MiniDoc.idPoly α) (@Model.idPolyModel α)) :=\n" ++
     "  ⟨fun _ h => False.elim h, fun _ h => False.elim h, fun _ => rfl⟩\nend LeanSwe.MiniDoc.Proofs\n")]
    #["LeanSwe/MiniNum/Model.lean", "LeanSwe/MiniNum/Proofs.lean", "LeanSwe/MiniDoc/Proofs.lean"]

  runMutant "pure_from_obeys_mismatch_rejected" "PURE_FROM_OBEYS_MISMATCH" #[
    ("LeanSwe/MiniNum/Model.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Model\n" ++
     "def allowedFmt (n out : Nat) : Prop := out ≥ n\n" ++
     "def ObeysApi (api : NumApi) : Prop := ∀ n, api.fmt n = n + 1\n" ++
     "def modelApi : NumApi := { fmt := fun n => n + 1 }\n" ++
     "theorem obeysApi_satisfiable : ∃ api : NumApi, ObeysApi api := ⟨modelApi, fun _ => rfl⟩\nend LeanSwe.MiniNum.Model\n"),
    ("LeanSwe/MiniNum/Proofs.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Model\nimport LeanSwe.MiniNum.Interface\nnamespace LeanSwe.MiniNum.Proofs\n" ++
     "theorem obeys_model : Core.ObeysPure LeanSwe.MiniNum.fmt Model.allowedFmt := fun n => Nat.le_succ n\nend LeanSwe.MiniNum.Proofs\n")]
    #["LeanSwe/MiniNum/Model.lean", "LeanSwe/MiniNum/Proofs.lean", "LeanSwe/MiniDoc/Proofs.lean"]

  runMutant "pure_from_missing_witness_rejected" "MISSING_PURE_FROM_WITNESS" #[
    ("LeanSwe/MiniNum/Model.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Model\n" ++
     "def allowedFmt (n out : Nat) : Prop := out = n + 1\n" ++
     "def ObeysApi (api : NumApi) : Prop := Core.ObeysPure api.fmt allowedFmt\nend LeanSwe.MiniNum.Model\n")]
    #["LeanSwe/MiniNum/Model.lean", "LeanSwe/MiniNum/Proofs.lean", "LeanSwe/MiniDoc/Proofs.lean"]

  runMutant "pure_from_impl_tainted_witness_rejected" "MISSING_PURE_FROM_WITNESS" #[
    ("LeanSwe/MiniNum/Model.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Types\nnamespace LeanSwe.MiniNum.Model\n" ++
     "def allowedFmt (n out : Nat) : Prop := out = n + 1\n" ++
     "def ObeysApi (api : NumApi) : Prop := Core.ObeysPure api.fmt allowedFmt\nend LeanSwe.MiniNum.Model\n"),
    ("LeanSwe/MiniDoc/Proofs.lean",
     "import Core.Obeys\nimport LeanSwe.MiniNum.Model\nimport LeanSwe.MiniNum.Proofs\nimport LeanSwe.MiniDoc.Model\nimport LeanSwe.MiniDoc.Interface\nnamespace LeanSwe.MiniDoc.Proofs\n" ++
     "theorem tainted_wit : ∃ api : LeanSwe.MiniNum.NumApi, LeanSwe.MiniNum.Model.ObeysApi api := ⟨LeanSwe.MiniNum.defaultApi, LeanSwe.MiniNum.Proofs.obeys_model⟩\n" ++
     "theorem obeys_model :\n" ++
     "    Core.ObeysInverseRenderFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.parse Model.render Model.wf Model.equiv DocErr.message ∧\n" ++
     "    Core.ObeysPureFrom LeanSwe.MiniNum.Model.ObeysApi Internal.mkApi DocApi.format Model.allowedFormat ∧\n" ++
     "    (∀ {α : Type}, Core.ObeysPureEq (@LeanSwe.MiniDoc.idPoly α) (@Model.idPolyModel α)) := by\n" ++
     "  refine ⟨?_, fun num hnum n => hnum n, fun _ => rfl⟩\n  intro num hnum raw; cases raw with\n" ++
     "  | zero => exact ⟨by decide, fun a _ hr => by simp [Model.render] at hr⟩\n" ++
     "  | succ m => have hm : num.fmt m = m + 1 := hnum m; simp [Internal.mkApi, Core.InverseRenderSpec, Model.render, Model.wf, Model.equiv, hm]\nend LeanSwe.MiniDoc.Proofs\n")]
    #["LeanSwe/MiniNum/Model.lean", "LeanSwe/MiniNum/Proofs.lean", "LeanSwe/MiniDoc/Proofs.lean"]

  runMutant "pure_from_middle_hook_rejected" "MIDDLE_HOOK_VIOLATION" #[
    ("LeanSwe/MiniDoc/Impl.lean",
     "import LeanSwe.MiniNum.Types\nimport LeanSwe.MiniDoc.Types\nnamespace LeanSwe.MiniDoc.Internal\n" ++
     "def fakeNum : LeanSwe.MiniNum.NumApi := { fmt := fun _ => 0 }\n" ++
     "def mkApi (num : LeanSwe.MiniNum.NumApi) : DocApi :=\n" ++
     "  { parse := fun raw => if raw == 0 then .error { message := \"zero\" } else if num.fmt (raw - 1) == raw then .ok (raw - 1) else .error { message := \"bad\" }, format := num.fmt, idPoly := fun x => some x }\nend LeanSwe.MiniDoc.Internal\n"),
    ("LeanSwe/MiniDoc/Interface.lean",
     "import LeanSwe.MiniDoc.Impl\nnamespace LeanSwe.MiniDoc\n" ++
     "def defaultApi : DocApi := Internal.mkApi Internal.fakeNum\n" ++
     "def parse (raw : Nat) : Except DocErr Nat := defaultApi.parse raw\ndef format (n : Nat) : Nat := defaultApi.format n\ndef idPoly {α : Type} (x : α) : Option α := defaultApi.idPoly x\nend LeanSwe.MiniDoc\n")]
    #["LeanSwe/MiniDoc/Impl.lean", "LeanSwe/MiniDoc/Interface.lean", "LeanSwe/MiniDoc/Proofs.lean"]

  runMutant "pure_from_unmanifested_dep_rejected" "MIDDLE_HOOK_VIOLATION" #[] #[] (some (manifestJson ""))

  IO.FS.removeDirAll suiteDir
  return 0
