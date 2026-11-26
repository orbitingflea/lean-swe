import Lean

/-!
Companion positive and negative synthetic `.olean` self-tests (`scripts/CheckPromisesDagTest.lean`)
for the `SpecMutants` import-DAG rules in `scripts/CheckPromises.lean`, invoked from
`scripts/CheckPromisesTest.lean`.
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

private def assertPass (label : String) (out : IO.Process.Output) : IO Unit := do
  if out.exitCode != 0 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected pass (exit 0), got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def assertFailWith (label expectedDiag : String) (out : IO.Process.Output) : IO Unit := do
  let combined := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 || (combined.splitOn expectedDiag).length <= 1 then
    throw (IO.userError s!"CASE_FAILED ({label}): expected failure containing '{expectedDiag}', got exit={out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")

private def baseDagFiles : Array (String × String) := #[
  ("LeanSwe/MiniA/Types.lean", "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\nend LeanSwe.MiniA\n"),
  ("LeanSwe/MiniA/Model.lean", "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Model\ndef evalA (n : Nat) : Nat := n + aConst\nend LeanSwe.MiniA.Model\n"),
  ("LeanSwe/MiniA/SysBridge.lean", "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.SysBridge\ndef bridgeA (n : Nat) : Nat := n\nend LeanSwe.MiniA.SysBridge\n"),
  ("LeanSwe/MiniA/Impl.lean", "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n"),
  ("LeanSwe/MiniA/Interface.lean", "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef runA (n : Nat) : Nat := Internal.implA n\nend LeanSwe.MiniA\n"),
  ("LeanSwe/MiniA/SpecTests.lean",
    "import Core.NondetTest\nimport LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA\n" ++
    "def test_a {r : Type → Type} [Core.NondetTest r] (f : Nat → Nat) : r Unit := Core.NondetTest.assert (f 0 = 1)\nend LeanSwe.MiniA\n"),
  ("LeanSwe/MiniA/Proofs/Witness.lean",
    "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Proofs\ntheorem evalA_zero : Model.evalA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\n"),
  ("LeanSwe/MiniA/Proofs.lean",
    "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\n" ++
    "theorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
  ("LeanSwe/MiniB/Types.lean", "namespace LeanSwe.MiniB\ndef bConst : Nat := 2\nend LeanSwe.MiniB\n"),
  ("LeanSwe/MiniB/Proofs.lean", "import LeanSwe.MiniB.Types\nnamespace LeanSwe.MiniB.Proofs\ntheorem b_eq : bConst = 2 := rfl\nend LeanSwe.MiniB.Proofs\n")
]

private def runDagCase (bin : System.FilePath) (tmpRoot realLibAbs : System.FilePath)
    (caseName : String) (extraFiles : Array (String × String)) (rootsCsv : String) :
    IO IO.Process.Output := do
  let caseDir := tmpRoot / s!"dag_{caseName}"
  let root := caseDir / "repo"
  let libDir := caseDir / "lib"
  IO.FS.createDirAll root
  IO.FS.createDirAll libDir
  symlinkCoreLib realLibAbs libDir
  let leanPath := s!"{libDir}:{realLibAbs}"
  for (rel, content) in baseDagFiles ++ extraFiles do
    writeFileCreatingParents (root / rel) content
    compileLeanMod root leanPath (root / rel) ((libDir / rel).withExtension "olean")
  runCmd bin.toString #["--internal-dag-audit", libDir.toString, rootsCsv]

/-- Execute all `SpecMutants` import-DAG self-test cases. -/
def main (args : List String) : IO UInt32 := do
  let [binStr, tmpRootStr, realLibStr] := args
    | throw (IO.userError "usage: CheckPromisesDagTest <bin> <tmpRoot> <realLibAbs>")
  let bin : System.FilePath := binStr
  let tmpRoot : System.FilePath := tmpRootStr
  let realLibAbs : System.FilePath := realLibStr
  let stdRoots := "LeanSwe.MiniA.Proofs,LeanSwe.MiniA.SpecMutants,LeanSwe.MiniB.Proofs"

  assertPass "specmutants_pure_and_submodule_ok" (← runDagCase bin tmpRoot realLibAbs "ok" #[
    ("LeanSwe/MiniA/SpecMutants/Extra.lean",
      "import LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 2)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n"),
    ("LeanSwe/MiniA/SpecMutants.lean",
      "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.SpecMutants.Extra\nimport LeanSwe.MiniA.Proofs.Witness\nnamespace LeanSwe.MiniA\n" ++
      "example : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
  ] stdRoots)

  assertFailWith "specmutants_imports_impl_rejected" "DAG_WITHIN_VIOLATION: LeanSwe.MiniA.SpecMutants (SpecMutants) transitively imports same-package LeanSwe.MiniA.Impl (Impl)"
    (← runDagCase bin tmpRoot realLibAbs "bad_impl" #[
      ("LeanSwe/MiniA/SpecMutants.lean",
        "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
    ] stdRoots)

  assertFailWith "specmutants_imports_sysbridge_rejected" "DAG_WITHIN_VIOLATION: LeanSwe.MiniA.SpecMutants (SpecMutants) transitively imports same-package LeanSwe.MiniA.SysBridge (SysBridge)"
    (← runDagCase bin tmpRoot realLibAbs "bad_bridge" #[
      ("LeanSwe/MiniA/SpecMutants.lean",
        "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.SysBridge\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
    ] stdRoots)

  assertFailWith "specmutants_imports_iface_rejected" "DAG_WITHIN_VIOLATION: LeanSwe.MiniA.SpecMutants (SpecMutants) transitively imports same-package LeanSwe.MiniA.Interface (Interface)"
    (← runDagCase bin tmpRoot realLibAbs "bad_iface" #[
      ("LeanSwe/MiniA/SpecMutants.lean",
        "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
    ] stdRoots)

  assertFailWith "specmutants_trans_impl_via_proofs_rejected" "DAG_WITHIN_VIOLATION: LeanSwe.MiniA.SpecMutants (SpecMutants) transitively imports same-package LeanSwe.MiniA.Impl (Impl)"
    (← runDagCase bin tmpRoot realLibAbs "bad_trans_proofs" #[
      ("LeanSwe/MiniA/SpecMutants.lean",
        "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
    ] stdRoots)

  assertFailWith "specmutants_cross_proofs_rejected" "DAG_TRANS_LEAK: LeanSwe.MiniA.SpecMutants (SpecMutants) transitively imports cross-package LeanSwe.MiniB.Proofs (Proofs)"
    (← runDagCase bin tmpRoot realLibAbs "bad_cross_proofs" #[
      ("LeanSwe/MiniA/SpecMutants.lean",
        "import LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniB.Proofs\nnamespace LeanSwe.MiniA\nexample : ¬ Core.AllPass (test_a (fun _ => 0)) := by intro ⟨h, _⟩; cases h\nend LeanSwe.MiniA\n")
    ] stdRoots)

  IO.println "CHECK_PROMISES_DAG_SELF_TEST: passed=6 failed=0"
  return 0
