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

private def dagManifestJson : String :=
  "{\n  \"version\": 1,\n  \"packages\": {\n" ++
  "    \"LeanSwe.MiniA\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false},\n" ++
  "    \"LeanSwe.MiniB\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [\"LeanSwe.MiniA\"], \"external_boundary\": false},\n" ++
  "    \"LeanSwe.MiniC\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [], \"external_boundary\": false},\n" ++
  "    \"LeanSwe.MiniD\": {\"kind\": \"model\", \"purity\": \"pure\", \"deps\": [\"LeanSwe.MiniB\"], \"external_boundary\": false}\n" ++
  "  }\n}\n"

private def runDagCase (bin : System.FilePath) (tmpRoot realLibAbs : System.FilePath)
    (caseName : String) (extraFiles : Array (String × String)) (rootsCsv : String)
    (withManifest : Bool := false) (strictSplitRoot : Bool := false) :
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
  let baseArgs :=
    if strictSplitRoot then #["--internal-dag-audit", "--strict-split-root", libDir.toString, rootsCsv]
    else #["--internal-dag-audit", libDir.toString, rootsCsv]
  if withManifest then
    let mp := root / "scripts/package_manifest.json"
    writeFileCreatingParents mp dagManifestJson
    runCmd bin.toString (baseArgs.push mp.toString)
  else
    runCmd bin.toString baseArgs

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

  -- Level 2 Layer 1 proof-free negative & positive self-tests (t-127).
  assertFailWith "layer1_iface_public_theorem_rejected"
    "proofs/LeanSweProofs/MiniA/Proofs.lean or proofs/LeanSweProofs/MiniA/Properties.lean"
    (← runDagCase bin tmpRoot realLibAbs "l1_iface_pub_thm" #[
      ("LeanSwe/MiniA/Interface.lean",
        "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef runA (n : Nat) : Nat := Internal.implA n\ntheorem runA_zero : runA 0 = 1 := rfl\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Interface")

  assertFailWith "layer1_iface_private_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_iface_priv_thm" #[
      ("LeanSwe/MiniA/Interface.lean",
        "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\nprivate theorem helper_zero : 0 = 0 := rfl\ndef runA (n : Nat) : Nat := Internal.implA n\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Interface")

  assertFailWith "layer1_types_private_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_types_priv_thm" #[
      ("LeanSwe/MiniA/Types.lean",
        "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\nprivate theorem aConst_eq : aConst = 1 := rfl\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Types")

  assertFailWith "layer1_impl_public_theorem_rejected" "LAYER1_PUBLIC_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_pub_thm" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ntheorem pubHelper (n : Nat) : n + 1 > 0 := Nat.succ_pos n\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_unused_private_theorem_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_unused_priv_thm" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem unusedHelper : 1 = 1 := rfl\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_private_theorem_only_prop_def_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_prop_def_bypass" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem sneakyThm : 1 = 1 := rfl\nprivate def fakeProofDef : 1 = 1 := sneakyThm\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_private_theorem_let_prop_alias_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_let_prop_bypass" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem sneakyThm : 1 = 1 := rfl\nprivate def fakeLetProp : (let T := Prop; T) := let _ := sneakyThm; True\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_private_theorem_outparam_prop_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_outparam_prop_bypass" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem sneakyThm : 1 = 1 := rfl\nprivate def fakeOutParam : outParam (1 = 1) := sneakyThm\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_other_module_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_other_thm" #[
      ("LeanSwe/MiniA/Helpers.lean",
        "namespace LeanSwe.MiniA.Helpers\ntheorem sneakOther : 1 = 1 := rfl\nend LeanSwe.MiniA.Helpers\n")
    ] "LeanSwe.MiniA.Helpers")

  assertFailWith "layer1_pkg_umbrella_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_pkg_umbrella_thm" #[
      ("LeanSwe/MiniA.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA\ntheorem sneakPkgUmbrella : 1 = 1 := rfl\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA")

  assertFailWith "layer1_testsupport_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_testsupport_thm" #[
      ("LeanSwe/MiniA/TestSupport.lean",
        "namespace LeanSwe.MiniA.TestSupport\ntheorem sneakTestSupport : 1 = 1 := rfl\nend LeanSwe.MiniA.TestSupport\n")
    ] "LeanSwe.MiniA.TestSupport")

  assertFailWith "layer1_root_umbrella_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_root_umbrella_thm" #[
      ("LeanSwe.lean",
        "import LeanSwe.MiniA.Interface\ntheorem sneakRootUmbrella : 1 = 1 := rfl\n")
    ] "LeanSwe")

  assertFailWith "layer1_runtimetests_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_runtimetests_thm" #[
      ("LeanSwe/MiniA/RuntimeTests.lean",
        "namespace LeanSwe.MiniA.RuntimeTests\ntheorem sneakRuntimeTests : 1 = 1 := rfl\nend LeanSwe.MiniA.RuntimeTests\n")
    ] "LeanSwe.MiniA.RuntimeTests")

  assertFailWith "layer1_types_plain_nonempty_theorem_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_types_fake_nonempty_thm" #[
      ("LeanSwe/MiniA/Types.lean",
        "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\nprivate opaque FooPointed : NonemptyType\ndef Foo : Type := FooPointed.type\ntheorem fakeNonempty : Nonempty Foo := FooPointed.property\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Types")

  assertPass "layer1_types_real_nonempty_instance_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_types_real_nonempty_inst" #[
      ("LeanSwe/MiniA/Types.lean",
        "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\nprivate opaque FooPointed : NonemptyType\ndef Foo : Type := FooPointed.type\ninstance : Nonempty Foo := FooPointed.property\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Types")

  assertFailWith "layer1_impl_unused_prop_inductive_eliminator_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_prop_ind_bypass" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem sneakyThm : 1 = 1 := rfl\nprivate inductive DeadProp : (1 = 1) → Prop where | mk : DeadProp sneakyThm\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_unused_prop_structure_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_prop_struct_bypass" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem sneakyThm : 1 = 1 := rfl\nprivate structure DeadPropStruct : Prop where\n  h : (let _ := sneakyThm; True) := trivial\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_split_root_proofs_under_leanswe_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_split_root_proofs" #[
      ("LeanSwe/MiniA/Impl/FooProofs.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ntheorem sneakSplitProofs : 1 = 1 := rfl\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl.FooProofs" (strictSplitRoot := true))

  assertPass "layer1_impl_used_private_theorem_transitive_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_used_priv_ok" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem step_pos (n : Nat) : 0 < n + 1 := Nat.succ_pos n\nprivate theorem step_ne_zero (n : Nat) : n + 1 ≠ 0 := Nat.ne_of_gt (step_pos n)\ndef implA (n : Nat) : Nat := (⟨n + 1, step_ne_zero n⟩ : { k : Nat // k ≠ 0 }).val\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertPass "layer1_sysbridge_used_private_theorem_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_bridge_used_priv_ok" #[
      ("LeanSwe/MiniA/SysBridge.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.SysBridge\nprivate theorem nonneg_ok (n : Nat) : n < n + 1 := Nat.lt_succ_self n\ndef bridgeA (n : Nat) : Nat := (⟨n, nonneg_ok n⟩ : { k : Nat // k < k + 1 }).val\nend LeanSwe.MiniA.SysBridge\n")
    ] "LeanSwe.MiniA.SysBridge")

  assertFailWith "layer1_sysbridge_unused_private_theorem_rejected" "LAYER1_UNUSED_PRIVATE_THEOREM:"
    (← runDagCase bin tmpRoot realLibAbs "l1_bridge_unused_priv" #[
      ("LeanSwe/MiniA/SysBridge.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.SysBridge\nprivate theorem unusedBridge : 2 = 2 := rfl\ndef bridgeA (n : Nat) : Nat := n\nend LeanSwe.MiniA.SysBridge\n")
    ] "LeanSwe.MiniA.SysBridge")

  -- Cross-package Proofs -> direct-dep top-level Proofs/Properties public theorem reuse (t-127).
  assertPass "cross_proofs_direct_dep_public_thm_ok"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_ok" #[
      ("LeanSwe/MiniA/Properties.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Properties\ntheorem runA_pos (n : Nat) : 0 < runA n := Nat.succ_pos n\nend LeanSwe.MiniA.Properties\n"),
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef helperVal : Nat := 42\ntheorem runA_zero_eq : runA 0 = 1 := rfl\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nimport LeanSwe.MiniA.Properties\nnamespace LeanSwe.MiniB.Proofs\ntheorem reuse_both : LeanSwe.MiniA.runA 0 = 1 ∧ 0 < LeanSwe.MiniA.runA 1 := ⟨LeanSwe.MiniA.Proofs.runA_zero_eq, LeanSwe.MiniA.Properties.runA_pos 1⟩\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_def_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_def_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ndef helperVal : Nat := 42\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_def : LeanSwe.MiniA.Proofs.helperVal = 42 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_impl_reachin_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_impl_bad" #[
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_impl : LeanSwe.MiniA.Internal.implA 0 = 1 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_submodule_thm_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_sub_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Proofs.Witness\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_sub : LeanSwe.MiniA.Model.evalA 0 = 1 := LeanSwe.MiniA.Proofs.evalA_zero\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_internal_reachin_rejected" "DAG_CROSS_INTERNAL_REACHIN:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_internal_bad" #[
      ("LeanSwe/MiniA/Interface.lean",
        "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef Internal.ifaceLeak (n : Nat) : Nat := Internal.implA n\ndef runA (n : Nat) : Nat := Internal.ifaceLeak n\nend LeanSwe.MiniA\n"),
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_internal : LeanSwe.MiniA.Internal.ifaceLeak 0 = 1 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_non_dep_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_non_dep_bad" #[
      ("LeanSwe/MiniC/Types.lean", "namespace LeanSwe.MiniC\ndef cConst : Nat := 3\nend LeanSwe.MiniC\n"),
      ("LeanSwe/MiniC/Proofs.lean",
        "import LeanSwe.MiniC.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniC.Proofs\ntheorem c_ok : cConst = 3 := rfl\nend LeanSwe.MiniC.Proofs\n")
    ] "LeanSwe.MiniC.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_transitive_dep_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_trans_dep_bad" #[
      ("LeanSwe/MiniD/Types.lean", "namespace LeanSwe.MiniD\ndef dConst : Nat := 4\nend LeanSwe.MiniD\n"),
      ("LeanSwe/MiniD/Proofs.lean",
        "import LeanSwe.MiniD.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniD.Proofs\ntheorem d_ok : dConst = 4 := rfl\nend LeanSwe.MiniD.Proofs\n")
    ] "LeanSwe.MiniD.Proofs" (withManifest := true))

  assertFailWith "cross_properties_direct_dep_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_props_bad" #[
      ("LeanSwe/MiniA/Properties.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Properties\ntheorem runA_pos (n : Nat) : 0 < runA n := Nat.succ_pos n\nend LeanSwe.MiniA.Properties\n"),
      ("LeanSwe/MiniB/Properties.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Properties\nnamespace LeanSwe.MiniB.Properties\ntheorem b_ok : bConst = 2 := rfl\nend LeanSwe.MiniB.Properties\n")
    ] "LeanSwe.MiniB.Properties" (withManifest := true))

  assertPass "layer1_impl_struct_field_default_private_thm_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_struct_default_ok" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem pos_one : 0 < 1 := Nat.zero_lt_one\nstructure NonZeroCfg where\n  k : { n : Nat // 0 < n } := ⟨1, pos_one⟩\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "cross_proofs_direct_dep_suffix_def_elim_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_suffix_elim_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\ndef runA_zero_eq.elim : Nat := 7\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_elim : LeanSwe.MiniA.Proofs.runA_zero_eq.elim = 7 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_suffix_sub_thm_eq1_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_suffix_eq1_bad" #[
      ("LeanSwe/MiniA/Properties.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Properties\ntheorem runA_pos (n : Nat) : 0 < runA n := Nat.succ_pos n\nend LeanSwe.MiniA.Properties\n"),
      ("LeanSwe/MiniA/Proofs/Witness.lean",
        "import LeanSwe.MiniA.Model\nimport LeanSwe.MiniA.Properties\nnamespace LeanSwe.MiniA.Proofs\ntheorem evalA_zero : Model.evalA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\ntheorem LeanSwe.MiniA.Properties.runA_pos.eq_1 : 1 = 1 := rfl\n"),
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Proofs.Witness\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Properties\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_eq1 : 1 = 1 := LeanSwe.MiniA.Properties.runA_pos.eq_1\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_direct_dep_suffix_impl_splitter_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_direct_suffix_splitter_bad" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\ndef LeanSwe.MiniA.Proofs.runA_zero_eq.splitter : Nat := 9\n"),
      ("LeanSwe/MiniA/Interface.lean",
        "import LeanSwe.MiniA.Impl\nnamespace LeanSwe.MiniA\ndef runA (n : Nat) : Nat := Internal.implA n\nend LeanSwe.MiniA\n"),
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_splitter : LeanSwe.MiniA.Proofs.runA_zero_eq.splitter = 9 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertPass "cross_proofs_split_root_ok"
    (← runDagCase bin tmpRoot realLibAbs "cross_split_root_ok" #[
      ("LeanSweProofs/MiniA/Proofs.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSweProofs/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSweProofs.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem reuse_split : LeanSwe.MiniA.runA 0 = 1 := LeanSwe.MiniA.Proofs.runA_zero_eq\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSweProofs.MiniB.Proofs" (withManifest := true) (strictSplitRoot := true))

  assertFailWith "cross_proofs_split_root_target_leanswe_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_split_root_target_bad" #[
      ("LeanSweProofs/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem bad_target : bConst = 2 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSweProofs.MiniB.Proofs" (withManifest := true) (strictSplitRoot := true))

  assertFailWith "cross_proofs_split_root_source_leanswe_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_split_root_source_bad" #[
      ("LeanSweProofs/MiniA/Proofs.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Impl/FooProofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSweProofs.MiniA.Proofs\nnamespace LeanSwe.MiniB.Internal\ndef fooDef : Nat := bConst\nend LeanSwe.MiniB.Internal\n")
    ] "LeanSwe.MiniB.Impl.FooProofs" (withManifest := true) (strictSplitRoot := true))

  assertPass "layer1_impl_struct_extends_default_private_thm_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_struct_extends_default_ok" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem pos_one : 0 < 1 := Nat.zero_lt_one\nprivate structure BaseCfg where\n  k : { n : Nat // 0 < n }\nprivate structure ChildCfg extends BaseCfg where\n  k := ⟨1, pos_one⟩\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_impl_fake_nonempty_stdlib_let_rejected" "LAYER1_PUBLIC_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_fake_nonempty_stdlib" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\ninstance fake : Nonempty (let _ : ∀ n : Nat, n + 0 = n := Nat.add_zero; IO.RealWorld) := IO.RealWorld.nonemptyType.property\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "layer1_types_fake_nonempty_stdlib_let_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_types_fake_nonempty_stdlib" #[
      ("LeanSwe/MiniA/Types.lean",
        "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\ninstance fake : Nonempty (let _ : ∀ n : Nat, n + 0 = n := Nat.add_zero; IO.RealWorld) := IO.RealWorld.nonemptyType.property\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Types")

  assertFailWith "layer1_types_fake_nonempty_local_let_rejected" "LAYER1_THEOREM_FORBIDDEN:"
    (← runDagCase bin tmpRoot realLibAbs "l1_types_fake_nonempty_local" #[
      ("LeanSwe/MiniA/Types.lean",
        "namespace LeanSwe.MiniA\ndef aConst : Nat := 1\nprivate opaque FooPointed : NonemptyType\ndef Foo : Type := FooPointed.type\ninstance : Nonempty (let _ : 1 = 1 := rfl; Foo) := FooPointed.property\nend LeanSwe.MiniA\n")
    ] "LeanSwe.MiniA.Types")

  assertFailWith "cross_proofs_suffix_types_prefix_def_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_suffix_types_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\ndef LeanSwe.MiniA.aConst.elim : Nat := 7\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak : LeanSwe.MiniA.aConst.elim = 7 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_suffix_stdlib_prefix_def_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_suffix_stdlib_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\ndef Nat.add.elim : Nat := 7\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak : Nat.add.elim = 7 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_suffix_importer_prefix_def_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_suffix_importer_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\ndef LeanSwe.MiniB.bConst.elim : Nat := 7\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak : LeanSwe.MiniB.bConst.elim = 7 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_suffix_iface_prefix_sub_thm_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_suffix_iface_sub_bad" #[
      ("LeanSwe/MiniA/Proofs/Witness.lean",
        "import LeanSwe.MiniA.Model\nnamespace LeanSwe.MiniA.Proofs\ntheorem evalA_zero : Model.evalA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\ntheorem LeanSwe.MiniA.runA.else_eq : 1 = 1 := rfl\n"),
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nimport LeanSwe.MiniA.Proofs.Witness\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak : 1 = 1 := LeanSwe.MiniA.runA.else_eq\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertPass "cross_proofs_same_pkg_suffixed_on_dep_thm_ok"
    (← runDagCase bin tmpRoot realLibAbs "cross_same_pkg_suffix_ok" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\ndef LeanSwe.MiniA.Proofs.runA_zero_eq.elim : Nat := 7\nnamespace LeanSwe.MiniB.Proofs\ntheorem local_ok : LeanSwe.MiniA.Proofs.runA_zero_eq.elim = 7 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  assertFailWith "cross_proofs_specmutants_fooproofs_rejected" "DAG_CROSS_IMPORT_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_specmutants_fooproofs_bad" #[
      ("LeanSweProofs/MiniA/Proofs.lean",
        "import LeanSwe.MiniA.Interface\nnamespace LeanSwe.MiniA.Proofs\ntheorem runA_zero_eq : runA 0 = 1 := rfl\nend LeanSwe.MiniA.Proofs\n"),
      ("LeanSweProofs/MiniB/SpecMutants/FooProofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSweProofs.MiniA.Proofs\nnamespace LeanSwe.MiniB.SpecMutants\ntheorem bad_mut : bConst = 2 := rfl\nend LeanSwe.MiniB.SpecMutants\n")
    ] "LeanSweProofs.MiniB.SpecMutants.FooProofs" (withManifest := true) (strictSplitRoot := true))

  assertPass "layer1_impl_pub_struct_private_field_default_ok"
    (← runDagCase bin tmpRoot realLibAbs "l1_impl_pub_struct_priv_field_default_ok" #[
      ("LeanSwe/MiniA/Impl.lean",
        "import LeanSwe.MiniA.Types\nnamespace LeanSwe.MiniA.Internal\nprivate theorem pos_one : 0 < 1 := Nat.zero_lt_one\nstructure PubCfg where\n  private k : { n : Nat // 0 < n } := ⟨1, pos_one⟩\ndef implA (n : Nat) : Nat := n + 1\nend LeanSwe.MiniA.Internal\n")
    ] "LeanSwe.MiniA.Impl")

  assertFailWith "cross_proofs_suffix_aux_match_rejected" "DAG_CROSS_REACHIN_VIOLATION:"
    (← runDagCase bin tmpRoot realLibAbs "cross_suffix_aux_match_bad" #[
      ("LeanSwe/MiniA/Proofs.lean",
        "import Core.NondetTest\nimport LeanSwe.MiniA.Interface\nimport LeanSwe.MiniA.SpecTests\nnamespace LeanSwe.MiniA.Proofs\ntheorem test_a_ok : Core.AllPass (test_a runA) := ⟨rfl, trivial⟩\nend LeanSwe.MiniA.Proofs\ndef LeanSwe.MiniA.aConst.elim (n : Nat) : Nat := match n with | 0 => 1 | k + 1 => k\n"),
      ("LeanSwe/MiniB/Proofs.lean",
        "import LeanSwe.MiniB.Types\nimport LeanSwe.MiniA.Proofs\nnamespace LeanSwe.MiniB.Proofs\ntheorem sneak_match : LeanSwe.MiniA.aConst.elim.match_1 (fun _ => Nat) 0 (fun _ => 1) (fun k => k) = 1 := rfl\nend LeanSwe.MiniB.Proofs\n")
    ] "LeanSwe.MiniB.Proofs" (withManifest := true))

  IO.println "CHECK_PROMISES_DAG_SELF_TEST: passed=54 failed=0"
  return 0
