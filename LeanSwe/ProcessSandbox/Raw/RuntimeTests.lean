import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Model
import LeanSwe.Fs.Raw.Interface

namespace LeanSwe.ProcessSandbox.Raw.RuntimeTests

open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Model

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {ε α : Type} [Repr ε] (res : Except ε α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except SandboxError α) (expected : SandboxErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def isSystemRootPrefix (p : String) : Bool :=
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any (fun pre => p.startsWith pre)

/-- Execute OS-level runtime verification tests for `LeanSwe.ProcessSandbox.Raw`, returning `some reason` if skipped. -/
def runAllOutcome : IO (Option String) := do
  let baseCounts ← Raw.activeResourceCounts
  assertTrue (baseCounts == { openPlans := 0, activeBoxes := 0, activeForwarders := 0 })
    "initial Raw.activeResourceCounts == 0"

  let preRes ← Raw.preflight { needMemoryCgroup := true, needPidsCgroup := true }
  match preRes with
  | .error err =>
    assertTrue (err.kind == .unavailable && !err.message.isEmpty)
      "preflight fail-closed unavailable"
    let afterErrCounts ← Raw.activeResourceCounts
    assertTrue (afterErrCounts == baseCounts) "preflight failure leaves counts unchanged"
    return some s!"preflight unavailable: {err.message}"
  | .ok () =>
    assertTrue ((← Raw.activeResourceCounts) == baseCounts) "preflight ok leaves counts unchanged"

  let preset ← assertOk (← Raw.discoverHostPreset) "discoverHostPreset"
  assertTrue (!preset.systemEntries.isEmpty) "discoverHostPreset discovers system entries"
  assertTrue (!preset.etcPaths.contains "/etc/shadow") "discoverHostPreset excludes /etc/shadow"
  match ← IO.getEnv "HOME" with
  | some h =>
    if isSystemRootPrefix h then
      if ← System.FilePath.isDir h then
        assertTrue (preset.excludedHomePaths.contains h)
          "discoverHostPreset includes existing system-nested HOME"
  | none => pure ()

  assertErrKind (← Raw.closePlan { handleId := 0 }) .invalidInput "closePlan rejects 0"
  assertErrKind (← Raw.closePlan { handleId := UInt64.size }) .invalidInput "closePlan rejects >= 2^64"
  assertErrKind (← Raw.spawnBox { handleId := 0 }) .invalidInput "spawnBox rejects 0"
  let forgedBox : BoxHandle := { handleId := 0, pid := 1, pgid := 1, pidfd := 3 }
  let forgedFwd : PortForwarderHandle := { handleId := 0, boxHandleId := 0 }
  assertErrKind (← Raw.killProcessGroup forgedBox) .invalidInput "killProcessGroup rejects 0"
  assertErrKind (← Raw.pidfdKill forgedBox) .invalidInput "pidfdKill rejects 0"
  assertErrKind (← Raw.reapBox forgedBox) .invalidInput "reapBox rejects 0"
  assertErrKind (← Raw.stopPortForwarders forgedFwd) .invalidInput "stopPortForwarders rejects 0"

  let mockFailOps := Internal.mkRawOps
    { hostArch := pure 0xc000003e
      preflight := fun _ _ => pure (1, 13, "/sys/fs/cgroup", "mock preflight fail")
      discoverPreset := pure (1, 13, "unused", #[], #[], #[])
      sealPlan := fun _ => pure (1, 13, "", "unused", 0)
      closePlan := fun _ => pure (1, 13, "", "unused")
      spawnBox := fun _ => pure (1, 13, "", "unused", 0, 0, 0, 0)
      startForwarders := fun _ _ _ => pure (1, 13, "", "unused", 0)
      stopForwarders := fun _ => pure (1, 13, "", "unused")
      readOutput := fun _ _ _ _ _ => pure (1, 13, "", "unused", 0, 0, ByteArray.empty, ByteArray.empty)
      killPg := fun _ => pure (1, 13, "", "unused")
      pidfdKill := fun _ => pure (1, 13, "", "unused")
      reapBox := fun _ => pure (1, 13, "", "unused")
      activeCounts := pure (0, 0, 0) }
  match ← mockFailOps.preflight { needMemoryCgroup := true, needPidsCgroup := true } with
  | .ok () => throw (IO.userError "ASSERTION FAILED: mock failing preflight must return error")
  | .error e =>
    assertTrue (e.kind == .unavailable && e.errnoCode == some 13 && e.message == "mock preflight fail")
      s!"mock preflight 4-tuple mismatch: {repr e}"

  let tmpDir ← IO.FS.createTempDir
  let noAccessDir := tmpDir / "noaccess"
  try
    let validBase ← match validateSpecPure { program := "/bin/sh", args := #["-c", "cat; echo raw_err >&2"] } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let seccompBytes := encodeSeccompBpfModel #[bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]
    let plan := compilePlan validBase preset
    let ph ← assertOk (← Raw.sealPlan plan seccompBytes) "sealPlan"
    assertTrue (isValidSandboxHandleId ph.handleId) "sealPlan valid handleId"
    assertTrue ((← Raw.activeResourceCounts).openPlans == 1) "openPlans == 1"

    let bh ← assertOk (← Raw.spawnBox ph) "spawnBox"
    assertTrue (isValidSandboxHandleId bh.handleId && bh.pid > 0 && bh.pgid > 0 && bh.pidfd >= 0)
      "spawnBox valid BoxHandle"
    assertTrue ((← Raw.activeResourceCounts).activeBoxes == 1) "activeBoxes == 1"

    let out ← assertOk (← Raw.readBoxOutput bh "raw_in\n".toUTF8 10_000 (some 4096)) "readBoxOutput"
    assertTrue (out.outcome == .exited 0 &&
      String.fromUTF8! out.stdout == "raw_in\n" &&
      String.fromUTF8! out.stderr == "raw_err\n") "raw stdout/stderr/stdin"

    assertOk (← Raw.killProcessGroup bh) "killProcessGroup"
    assertOk (← Raw.pidfdKill bh) "pidfdKill"
    assertOk (← Raw.reapBox bh) "reapBox"
    assertErrKind (← Raw.reapBox bh) .invalidInput "double reapBox rejected"
    assertOk (← Raw.closePlan ph) "closePlan"
    assertErrKind (← Raw.closePlan ph) .invalidInput "double closePlan rejected"
    assertTrue ((← Raw.activeResourceCounts) == baseCounts) "counts conserved after raw run"

    let missingHost := (tmpDir / "does_not_exist").toString
    let validMissing ← match validateSpecPure
        { program := "/bin/true", mounts := #[.readOnly missingHost "/mnt"] } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let phMiss ← assertOk (← Raw.sealPlan (compilePlan validMissing preset) seccompBytes) "sealPlan missing host"
    try
      assertErrKind (← Raw.spawnBox phMiss) .notFound "spawnBox missing hostPath -> notFound"
    finally
      let _ ← Raw.closePlan phMiss

    IO.FS.createDirAll (noAccessDir / "sub")
    let _ ← assertOk (← LeanSwe.Fs.Raw.chmod noAccessDir.toString 0o000) "chmod 0000 parent"
    let validPerm ← match validateSpecPure
        { program := "/bin/true", mounts := #[.readOnly (noAccessDir / "sub").toString "/mnt"] } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let phPerm ← assertOk (← Raw.sealPlan (compilePlan validPerm preset) seccompBytes) "sealPlan EACCES host"
    try
      assertErrKind (← Raw.spawnBox phPerm) .permissionDenied
        "spawnBox unsearchable hostPath -> permissionDenied"
    finally
      let _ ← Raw.closePlan phPerm
      let _ ← LeanSwe.Fs.Raw.chmod noAccessDir.toString 0o700

    let roParent := tmpDir / "ro_parent"
    IO.FS.createDirAll roParent
    let validErofs ← match validateSpecPure
        { program := "/bin/true"
          mounts := #[.readOnly roParent.toString "/work", .scratch "/work/new_nested_subdir"] } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let phErofs ← assertOk (← Raw.sealPlan (compilePlan validErofs preset) seccompBytes) "sealPlan EROFS nested"
    try
      assertErrKind (← Raw.spawnBox phErofs) .unavailable
        "spawnBox nested mountpoint EROFS under RO parent fails closed .unavailable"
    finally
      let _ ← Raw.closePlan phErofs

    let validFwd ← match validateSpecPure
        { program := "/bin/true"
          portForwards := #[{ boxPort := 19111, hostPort := 19112 }] } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let phFwd ← assertOk (← Raw.sealPlan (compilePlan validFwd preset) seccompBytes) "sealPlan fwd"
    try
      let bhFwd ← assertOk (← Raw.spawnBox phFwd) "spawnBox fwd"
      try
        let fh ← assertOk (← Raw.startPortForwarders bhFwd #[{ boxPort := 19111, hostPort := 19112 }])
          "startPortForwarders"
        try
          assertTrue (isValidSandboxHandleId fh.handleId && fh.boxHandleId == bhFwd.handleId)
            "valid PortForwarderHandle"
          assertTrue ((← Raw.activeResourceCounts).activeForwarders == 1) "activeForwarders == 1"
        finally
          assertOk (← Raw.stopPortForwarders fh) "stopPortForwarders"
          assertErrKind (← Raw.stopPortForwarders fh) .invalidInput "double stopPortForwarders rejected"
      finally
        assertOk (← Raw.killProcessGroup bhFwd) "killProcessGroup fwd"
        assertOk (← Raw.pidfdKill bhFwd) "pidfdKill fwd"
        assertOk (← Raw.reapBox bhFwd) "reapBox fwd"
    finally
      assertOk (← Raw.closePlan phFwd) "closePlan fwd"

    let manyPorts := (Array.range 34).map fun idx =>
      { boxPort := UInt16.ofNat (20100 + idx), hostPort := UInt16.ofNat (21100 + idx) : PortForward }
    let validMany ← match validateSpecPure { program := "/bin/true", portForwards := manyPorts } with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
    let phMany ← assertOk (← Raw.sealPlan (compilePlan validMany preset) seccompBytes) "sealPlan 34 fwds"
    try
      let bhMany ← assertOk (← Raw.spawnBox phMany) "spawnBox 34 fwds (>32 SCM_RIGHTS batch)"
      try
        let fhMany ← assertOk (← Raw.startPortForwarders bhMany manyPorts) "startPortForwarders 34 fwds"
        try
          let outMany ← assertOk (← Raw.readBoxOutput bhMany ByteArray.empty 5_000 (some 1024)) "readBoxOutput 34 fwds"
          assertTrue (outMany.outcome == .exited 0) s!"34 fwds outcome: {repr outMany.outcome}"
        finally
          assertOk (← Raw.stopPortForwarders fhMany) "stopPortForwarders 34 fwds"
      finally
        assertOk (← Raw.killProcessGroup bhMany) "killProcessGroup 34 fwds"
        assertOk (← Raw.pidfdKill bhMany) "pidfdKill 34 fwds"
        assertOk (← Raw.reapBox bhMany) "reapBox 34 fwds"
    finally
      assertOk (← Raw.closePlan phMany) "closePlan 34 fwds"

    assertTrue ((← Raw.activeResourceCounts) == baseCounts) "final Raw.activeResourceCounts == 0"
  finally
    let _ ← LeanSwe.Fs.Raw.chmod noAccessDir.toString 0o700
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.ProcessSandbox.Raw runtime tests"
  return none

/-- Execute OS-level runtime verification tests for `LeanSwe.ProcessSandbox.Raw`. -/
def runAll : IO Unit := do
  let _ ← runAllOutcome

end LeanSwe.ProcessSandbox.Raw.RuntimeTests
