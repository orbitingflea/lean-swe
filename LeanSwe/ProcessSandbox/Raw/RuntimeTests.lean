import Core.Assumptions
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.RuntimeTests.ErrorHelpers
import LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
import LeanSwe.ProcessSandbox.Raw.SysBridge.HostCap
import LeanSwe.ProcessSandbox.Raw.SysBridge.Driver
import LeanSwe.ProcessSandbox.Model
import LeanSwe.Fs.Interface
import LeanSwe.LinuxSyscall.Files.Interface

namespace LeanSwe.ProcessSandbox.Raw.RuntimeTests

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.RuntimeTests.ErrorHelpers
open LeanSwe.ProcessSandbox.Model

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {ε α : Type} [Repr ε] (res : Except ε α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def isSystemRootPrefix (p : String) : Bool :=
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any (fun pre => p.startsWith pre)

private def assertCapErr {α : Type} (mkCap : IO (Model.RawHostCapM IO))
    (act : RawProcessSandboxOps → IO (Except SandboxError α))
    (expected : SandboxErrorKind) (label : String) : IO Unit := do
  assertErrKind (← act (SysBridge.mkOpsFromHostCapM (← mkCap))) expected label

/-- Real error test: `decodeHostAuditArch` rejects unsupported architecture constants with `.unavailable`. -/
def err_psandboxRaw_decodeHostAuditArch_unavailable : IO Unit :=
  assertErrKind (Raw.decodeHostAuditArch 0) .unavailable "decodeHostAuditArch 0 -> unavailable"

/-- Real error test: `encodePlan` rejects empty seccomp filter bytes with `.invalidInput`. -/
def err_psandboxRaw_encodePlan_invalidInput : IO Unit :=
  assertErrKind (Raw.encodePlan samplePlan ByteArray.empty) .invalidInput "encodePlan empty seccomp -> invalidInput"

/-- Mocked error test: `hostSeccompArch` fails closed with `.unavailable` on non-Linux targets. -/
def err_psandboxRaw_hostSeccompArch_unavailable : IO Unit :=
  assertCapErr capNonLinux (fun ops => ops.hostSeccompArch) .unavailable "hostSeccompArch non-Linux"

/-- Mocked error test: `preflight` fails closed with `.unavailable` on non-Linux hosts. -/
def err_psandboxRaw_preflight_unavailable : IO Unit :=
  assertCapErr capNonLinux (fun ops => ops.preflight {}) .unavailable "preflight non-Linux"

/-- Mocked error test: `discoverHostPreset` fails closed with `.unavailable` on non-Linux hosts. -/
def err_psandboxRaw_discoverHostPreset_unavailable : IO Unit :=
  assertCapErr capNonLinux (fun ops => ops.discoverHostPreset) .unavailable "discoverHostPreset non-Linux"

/-- Real error test: `sealPlan` rejects empty seccomp BPF bytes with `.invalidInput`. -/
def err_psandboxRaw_sealPlan_invalidInput : IO Unit := do
  assertErrKind (← Raw.sealPlan samplePlan ByteArray.empty) .invalidInput "sealPlan empty seccomp"

/-- Mocked error test: `sealPlan` fails closed with `.unavailable` on non-Linux hosts. -/
def err_psandboxRaw_sealPlan_unavailable : IO Unit :=
  assertCapErr capNonLinux (fun ops => ops.sealPlan samplePlan sampleSeccomp) .unavailable "sealPlan non-Linux"

/-- Mocked error test: `sealPlan` maps `memfdCreate` `ENOMEM` failure to `.ioError`. -/
def err_psandboxRaw_sealPlan_ioError : IO Unit :=
  assertCapErr capWithTable (fun ops => ops.sealPlan samplePlan sampleSeccomp) .ioError "sealPlan memfd ENOMEM"

/-- Real error test: `closePlan` rejects forged zero handle with `.invalidInput`. -/
def err_psandboxRaw_closePlan_invalidInput : IO Unit := do
  assertErrKind (← Raw.closePlan { handleId := 0 }) .invalidInput "closePlan handle 0"

/-- Real error test: `spawnBox` rejects forged zero `PlanHandle` with `.invalidInput`. -/
def err_psandboxRaw_spawnBox_invalidInput : IO Unit := do
  assertErrKind (← Raw.spawnBox { handleId := 0 }) .invalidInput "spawnBox handle 0"

/-- Mocked error test: `spawnBox` fails closed with `.unavailable` when `bwrap` cannot be resolved. -/
def err_psandboxRaw_spawnBox_unavailable : IO Unit :=
  assertCapErr (capWithTable seededPlanTable) (fun ops => ops.spawnBox activePlan) .unavailable "spawnBox missing bwrap"

/-- Mocked error test: `spawnBox` maps missing user mount `hostPath` (`ENOENT`) to `.notFound`. -/
def err_psandboxRaw_spawnBox_notFound : IO Unit :=
  assertCapErr (capSpawnMountErrno Errno.ENOENT) (fun ops => ops.spawnBox activePlan) .notFound "spawnBox mount ENOENT"

/-- Mocked error test: `spawnBox` maps unsearchable user mount `hostPath` (`EACCES`) to `.permissionDenied`. -/
def err_psandboxRaw_spawnBox_permissionDenied : IO Unit :=
  assertCapErr (capSpawnMountErrno Errno.EACCES) (fun ops => ops.spawnBox activePlan) .permissionDenied "spawnBox mount EACCES"

/-- Mocked error test: `spawnBox` maps `pipe2` `EMFILE` failure to `.ioError`. -/
def err_psandboxRaw_spawnBox_ioError : IO Unit :=
  assertCapErr capSpawnPipeIoError (fun ops => ops.spawnBox activePlan) .ioError "spawnBox pipe2 EMFILE"

/-- Real error test: `startPortForwarders` rejects forged zero `BoxHandle` with `.invalidInput`. -/
def err_psandboxRaw_startPortForwarders_invalidInput : IO Unit := do
  assertErrKind (← Raw.startPortForwarders forgedBox #[]) .invalidInput "startPortForwarders handle 0"

/-- Mocked error test: `startPortForwarders` maps `startFwdTask` `EMFILE` failure to `.ioError`. -/
def err_psandboxRaw_startPortForwarders_ioError : IO Unit :=
  assertCapErr (capWithTable (seededBoxTable none #[7])) (fun ops => ops.startPortForwarders activeBox #[{ boxPort := 8080, hostPort := 8081 }]) .ioError "startPortForwarders EMFILE"

/-- Real error test: `stopPortForwarders` rejects forged zero handle with `.invalidInput`. -/
def err_psandboxRaw_stopPortForwarders_invalidInput : IO Unit := do
  assertErrKind (← Raw.stopPortForwarders forgedFwd) .invalidInput "stopPortForwarders handle 0"

/-- Real error test: `readBoxOutput` rejects forged zero `BoxHandle` with `.invalidInput`. -/
def err_psandboxRaw_readBoxOutput_invalidInput : IO Unit := do
  assertErrKind (← Raw.readBoxOutput forgedBox ByteArray.empty 1000 none) .invalidInput "readBoxOutput handle 0"

/-- Mocked error test: `readBoxOutput` maps `PS_STATUS_INIT_ERR` status frame to `.unavailable`. -/
def err_psandboxRaw_readBoxOutput_unavailable : IO Unit :=
  assertCapErr (capReadStatusFrame { kind := PS_STATUS_INIT_ERR, flag := 0, value := 1 }) (fun ops => ops.readBoxOutput activeBox ByteArray.empty 5000 (some 1024)) .unavailable "readBoxOutput INIT_ERR"

/-- Mocked error test: `readBoxOutput` maps `PS_STATUS_EXEC_ERR` (`ENOENT`) status frame to `.notFound`. -/
def err_psandboxRaw_readBoxOutput_notFound : IO Unit :=
  assertCapErr (capReadStatusFrame { kind := PS_STATUS_EXEC_ERR, flag := 0, value := 2 }) (fun ops => ops.readBoxOutput activeBox ByteArray.empty 5000 (some 1024)) .notFound "readBoxOutput EXEC_ERR ENOENT"

/-- Mocked error test: `readBoxOutput` maps `PS_STATUS_EXEC_ERR` (`EACCES`) status frame to `.permissionDenied`. -/
def err_psandboxRaw_readBoxOutput_permissionDenied : IO Unit :=
  assertCapErr (capReadStatusFrame { kind := PS_STATUS_EXEC_ERR, flag := 0, value := 13 }) (fun ops => ops.readBoxOutput activeBox ByteArray.empty 5000 (some 1024)) .permissionDenied "readBoxOutput EXEC_ERR EACCES"

/-- Mocked error test: `readBoxOutput` maps `clock_gettime` `EINVAL` failure to `.ioError`. -/
def err_psandboxRaw_readBoxOutput_ioError : IO Unit :=
  assertCapErr capReadClockEinval (fun ops => ops.readBoxOutput activeBox ByteArray.empty 1000 none) .ioError "readBoxOutput clock_gettime EINVAL"

/-- Real error test: `killProcessGroup` rejects forged zero `BoxHandle` with `.invalidInput`. -/
def err_psandboxRaw_killProcessGroup_invalidInput : IO Unit := do
  assertErrKind (← Raw.killProcessGroup forgedBox) .invalidInput "killProcessGroup handle 0"

/-- Mocked error test: `killProcessGroup` maps `kill` `EPERM` failure to `.ioError`. -/
def err_psandboxRaw_killProcessGroup_ioError : IO Unit :=
  assertCapErr capKillPgEperm (fun ops => ops.killProcessGroup activeBox) .ioError "killProcessGroup kill EPERM"

/-- Real error test: `pidfdKill` rejects forged zero `BoxHandle` with `.invalidInput`. -/
def err_psandboxRaw_pidfdKill_invalidInput : IO Unit := do
  assertErrKind (← Raw.pidfdKill forgedBox) .invalidInput "pidfdKill handle 0"

/-- Mocked error test: `pidfdKill` maps `pidfd_send_signal` `EPERM` failure to `.ioError`. -/
def err_psandboxRaw_pidfdKill_ioError : IO Unit :=
  assertCapErr capPidfdKillEperm (fun ops => ops.pidfdKill activeBox) .ioError "pidfdKill EPERM"

/-- Real error test: `reapBox` rejects forged zero `BoxHandle` with `.invalidInput`. -/
def err_psandboxRaw_reapBox_invalidInput : IO Unit := do
  assertErrKind (← Raw.reapBox forgedBox) .invalidInput "reapBox handle 0"

/-- Mocked error test: `reapBox` maps cgroup `unlinkat` `EACCES` failure to `.ioError`. -/
def err_psandboxRaw_reapBox_ioError : IO Unit :=
  assertCapErr capReapUnlinkEacces (fun ops => ops.reapBox activeBox) .ioError "reapBox unlinkat EACCES"

/-- Registered runtime error-coverage probes matching `LeanSwe.ProcessSandbox.Raw.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_decodeHostAuditArch_unavailable", mode := .real, run := err_psandboxRaw_decodeHostAuditArch_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_encodePlan_invalidInput", mode := .real, run := err_psandboxRaw_encodePlan_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_hostSeccompArch_unavailable", mode := .mocked, run := err_psandboxRaw_hostSeccompArch_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_preflight_unavailable", mode := .mocked, run := err_psandboxRaw_preflight_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_discoverHostPreset_unavailable", mode := .mocked, run := err_psandboxRaw_discoverHostPreset_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_sealPlan_invalidInput", mode := .real, run := err_psandboxRaw_sealPlan_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_sealPlan_unavailable", mode := .mocked, run := err_psandboxRaw_sealPlan_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_sealPlan_ioError", mode := .mocked, run := err_psandboxRaw_sealPlan_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_closePlan_invalidInput", mode := .real, run := err_psandboxRaw_closePlan_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_spawnBox_invalidInput", mode := .real, run := err_psandboxRaw_spawnBox_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_spawnBox_unavailable", mode := .mocked, run := err_psandboxRaw_spawnBox_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_spawnBox_notFound", mode := .mocked, run := err_psandboxRaw_spawnBox_notFound },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_spawnBox_permissionDenied", mode := .mocked, run := err_psandboxRaw_spawnBox_permissionDenied },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_spawnBox_ioError", mode := .mocked, run := err_psandboxRaw_spawnBox_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_startPortForwarders_invalidInput", mode := .real, run := err_psandboxRaw_startPortForwarders_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_startPortForwarders_ioError", mode := .mocked, run := err_psandboxRaw_startPortForwarders_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_stopPortForwarders_invalidInput", mode := .real, run := err_psandboxRaw_stopPortForwarders_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_readBoxOutput_invalidInput", mode := .real, run := err_psandboxRaw_readBoxOutput_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_readBoxOutput_unavailable", mode := .mocked, run := err_psandboxRaw_readBoxOutput_unavailable },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_readBoxOutput_notFound", mode := .mocked, run := err_psandboxRaw_readBoxOutput_notFound },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_readBoxOutput_permissionDenied", mode := .mocked, run := err_psandboxRaw_readBoxOutput_permissionDenied },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_readBoxOutput_ioError", mode := .mocked, run := err_psandboxRaw_readBoxOutput_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_killProcessGroup_invalidInput", mode := .real, run := err_psandboxRaw_killProcessGroup_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_killProcessGroup_ioError", mode := .mocked, run := err_psandboxRaw_killProcessGroup_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_pidfdKill_invalidInput", mode := .real, run := err_psandboxRaw_pidfdKill_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_pidfdKill_ioError", mode := .mocked, run := err_psandboxRaw_pidfdKill_ioError },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_reapBox_invalidInput", mode := .real, run := err_psandboxRaw_reapBox_invalidInput },
  { testName := "LeanSwe.ProcessSandbox.Raw.RuntimeTests.err_psandboxRaw_reapBox_ioError", mode := .mocked, run := err_psandboxRaw_reapBox_ioError }
]

/-- Execute OS-level runtime verification tests for `LeanSwe.ProcessSandbox.Raw`, returning `some reason` if skipped. -/
def runAllOutcome : IO (Option String) := do
  Core.runRegisteredErrorTests registeredErrorTests
  let caughtErrno ← SysBridge.Driver.catchSysErrno Core.ioConcOps
    (throw (IO.userError "boom") : IO (Except Errno Unit))
  match caughtErrno with
  | .ok () => throw (IO.userError "ASSERTION FAILED: catchSysErrno must return .error on thrown IO.Error")
  | .error e => assertTrue (e == Errno.EIO) "catchSysErrno converts userError to Errno.EIO"
  let caughtOpt ← SysBridge.Driver.catchSysOpt Core.ioConcOps
    (throw (IO.userError "boom") : IO (Option Nat))
  assertTrue (caughtOpt == none) "catchSysOpt converts thrown IO.Error to none"
  let caughtPf ← SysBridge.Driver.catchSysPf Core.ioConcOps
    (throw (IO.userError "boom") : IO (Except PostFork.PostForkError Unit))
  match caughtPf with
  | .ok () => throw (IO.userError "ASSERTION FAILED: catchSysPf must return .error on thrown IO.Error")
  | .error e => assertTrue (e.kind == .sysError && e.errno == some Errno.EIO) "catchSysPf maps userError to sysError EIO"
  let cellNonLinux ← IO.mkRef ({} : HostCellState IO.Ref (fun α => Task (Except IO.Error α)))
  let fullNonLinux := SysBridge.Driver.mkFullOpsWithPlatformM false "x86_64-apple-darwin"
    { files := LeanSwe.LinuxSyscall.Files.defaultOps
      net := LeanSwe.LinuxSyscall.Net.defaultOps
      poll := LeanSwe.LinuxSyscall.Poll.defaultOps
      proc := LeanSwe.LinuxSyscall.Process.defaultOps
      sandbox := LeanSwe.LinuxSyscall.Sandbox.defaultOps
      timeRand := LeanSwe.LinuxSyscall.TimeRand.defaultOps
      passwd := LeanSwe.LinuxSyscall.Passwd.defaultOps
      postFork := LeanSwe.PostFork.defaultOps
      envVars := LeanSwe.EnvVars.Raw.defaultOps }
    Core.ioConcOps
    (Core.ioStateCell cellNonLinux)
  assertErrKind (← fullNonLinux.hostSeccompArch) .unavailable "mkFullOpsWithPlatformM non-Linux hostSeccompArch"
  assertErrKind (← fullNonLinux.preflight {}) .unavailable "mkFullOpsWithPlatformM non-Linux preflight"
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

  let arch ← assertOk (← Raw.hostSeccompArch) "hostSeccompArch"
  assertTrue (arch == .x86_64 || arch == .aarch64) "hostSeccompArch returns supported arch"
  let validTrue ← match validateSpecPure { program := "/bin/true" } with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"unexpected validateSpecPure error: {repr e}")
  let invalidSeccompPlan := compilePlan validTrue preset
  assertErrKind (← Raw.sealPlan invalidSeccompPlan ByteArray.empty) .invalidInput
    "sealPlan rejects empty seccomp BPF payload"
  assertErrKind (← Raw.sealPlan invalidSeccompPlan (ByteArray.mk #[1, 2, 3])) .invalidInput
    "sealPlan rejects non-8-byte-aligned seccomp BPF payload"
  assertErrKind (← Raw.sealPlan invalidSeccompPlan (ByteArray.mk (Array.replicate (161 * 8) 0))) .invalidInput
    "sealPlan rejects > 160-instruction seccomp BPF payload"
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
    let _ ← assertOk (← LeanSwe.Fs.chmod noAccessDir.toString 0o000) "chmod 0000 parent"
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
      let _ ← LeanSwe.Fs.chmod noAccessDir.toString 0o700

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

    assertTrue (SysBridge.Bwrap.absoluteBwrapPathDirs ":/usr/bin".toUTF8 == ["/usr/bin"])
      "absoluteBwrapPathDirs drops leading empty segment"
    assertTrue (SysBridge.Bwrap.absoluteBwrapPathDirs "/usr/bin:".toUTF8 == ["/usr/bin"])
      "absoluteBwrapPathDirs drops trailing empty segment"
    assertTrue (SysBridge.Bwrap.absoluteBwrapPathDirs "/bin::/usr/bin".toUTF8 == ["/bin", "/usr/bin"])
      "absoluteBwrapPathDirs drops middle empty segment"
    assertTrue (SysBridge.Bwrap.absoluteBwrapPathDirs ".:/usr/bin".toUTF8 == ["/usr/bin"])
      "absoluteBwrapPathDirs drops dot segment"
    assertTrue (SysBridge.Bwrap.absoluteBwrapPathDirs "rel/dir:/usr/bin".toUTF8 == ["/usr/bin"])
      "absoluteBwrapPathDirs drops relative segment"
    let probedRef ← IO.mkRef (#[] : Array String)
    let fakeRegStat : LeanSwe.LinuxSyscall.Files.StatInfo := {
      kind := .reg, size := 1, mode := 0o755, ino := 1, dev := 1, nlink := 1,
      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
    }
    let mockFiles : LeanSwe.LinuxSyscall.Files.FilesOpsM IO LeanSwe.LinuxSyscall.RawFd := {
      LeanSwe.LinuxSyscall.Files.defaultOps with
      fstatat := fun _ pathBs _ => do
        let p := (String.fromUTF8? pathBs).getD ""
        probedRef.modify (·.push p)
        if p == "./bwrap" || p == "rel/dir/bwrap" || p == "/usr/bin/bwrap" then
          return .ok fakeRegStat
        else
          return .error LeanSwe.LinuxSyscall.Errno.ENOENT
      faccessat := fun _ pathBs _ _ => do
        let p := (String.fromUTF8? pathBs).getD ""
        if p == "./bwrap" || p == "rel/dir/bwrap" || p == "/usr/bin/bwrap" then
          return .ok ()
        else
          return .error LeanSwe.LinuxSyscall.Errno.ENOENT
    }
    let mockResolved ← SysBridge.Bwrap.resolveBwrapPath mockFiles
      (pure (some ":/nonexistent:.:rel/dir:/usr/bin".toUTF8))
    let probedPaths ← probedRef.get
    assertTrue (mockResolved == some "/usr/bin/bwrap")
      s!"resolveBwrapPath ignored empty/relative segments (got {repr mockResolved})"
    assertTrue (probedPaths.all fun p => p.startsWith "/")
      s!"resolveBwrapPath only probed absolute paths (got {repr probedPaths})"
    let fakeBwrapDir := tmpDir / "fake_bwrap_dir"
    IO.FS.createDirAll fakeBwrapDir
    let fakeBwrap := fakeBwrapDir / "bwrap"
    IO.FS.writeFile fakeBwrap "#!/bin/sh\nexit 0\n"
    let _ ← assertOk (← LeanSwe.Fs.chmod fakeBwrap.toString 0o755) "chmod 0755 fake bwrap"
    let realResolved ← SysBridge.Bwrap.resolveBwrapPath LeanSwe.LinuxSyscall.Files.defaultOps
      (pure (some s!":/nonexistent:.:rel/dir:{fakeBwrapDir}:/usr/bin".toUTF8))
    assertTrue (realResolved == some fakeBwrap.toString)
      s!"resolveBwrapPath real FS skips empty/rel and resolves absolute dir (got {repr realResolved})"

    assertTrue ((← Raw.activeResourceCounts) == baseCounts) "final Raw.activeResourceCounts == 0"
  finally
    let _ ← LeanSwe.Fs.chmod noAccessDir.toString 0o700
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.ProcessSandbox.Raw runtime tests"
  return none

/-- Execute OS-level runtime verification tests for `LeanSwe.ProcessSandbox.Raw`. -/
def runAll : IO Unit := do
  let _ ← runAllOutcome

end LeanSwe.ProcessSandbox.Raw.RuntimeTests
