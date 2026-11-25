import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.LinuxSyscall.Sandbox.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Interface
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
import LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
import LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
import LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder
import LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo
import LeanSwe.ProcessSandbox.Raw.SysBridge.State
import LeanSwe.ProcessSandbox.Raw.SysBridge.Spawn
import LeanSwe.ProcessSandbox.Raw.SysBridge.IoHostCap

namespace LeanSwe.ProcessSandbox.Raw.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.hostSeccompArch`. -/
def hostSeccompArchPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) : m (Except SandboxError SeccompArch) :=
  pure (Internal.decodeHostAuditArch (detectHostAuditArch deps.isLinux deps.target))

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.preflight`. -/
def preflightPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (req : PreflightReq)
    (initBytesRes : Except String ByteArray := embeddedInitBytes) : m (Except SandboxError Unit) := do
  if !deps.isLinux then
    return .error (Internal.mapRawError (.unavailable none "ProcessSandbox requires Linux"))
  if detectHostAuditArch deps.isLinux deps.target == 0 then
    return .error (Internal.mapRawError (.unavailable (some Errno.ENOSYS) "unsupported host architecture for seccomp filter"))
  match ← resolveBwrapPath deps.files deps.getEnvPath eintrFuel with
  | none =>
    return .error (Internal.mapRawError (.unavailable (some Errno.ENOENT) "bwrap executable not found in PATH"))
  | some bwrapPath =>
    match ← deps.sandbox.landlockCreateRuleset none Sandbox.LANDLOCK_CREATE_RULESET_VERSION with
    | .error e =>
      return .error (Internal.mapRawError (.unavailable (some e) "Landlock ABI >= 4 is required"))
    | .ok (.version abi) =>
      if abi.toNat < 4 then
        return .error (Internal.mapRawError (.unavailable (some Errno.ENOSYS) "Landlock ABI >= 4 is required"))
      match ← deps.sandbox.seccomp (.getActionAvail Sandbox.SECCOMP_RET_ERRNO) {} ByteArray.empty with
      | .error e =>
        return .error (Internal.mapRawError (.unavailable (some e) "seccomp filter support is required"))
      | .ok _ =>
        match initBytesRes with
        | .error msg =>
          return .error (Internal.mapRawError (.unavailable (some Errno.ENOEXEC) msg))
        | .ok initBytes =>
          match ← probeBwrapNamespaces deps.files deps.sandbox deps.proc deps.postFork bwrapPath initBytes eintrFuel with
          | .error e =>
            return .error (Internal.mapRawError (.unavailable (some e) "bwrap unprivileged namespaces unavailable"))
          | .ok () =>
            match ← deps.proc.getpid with
            | .error e =>
              return .error (Internal.mapRawError (.unavailable (some e) "getpid failed"))
            | .ok pid =>
              let seq ← tbl.nextCgSeq
              match ← createSiblingCgroup deps.files pid seq eintrFuel with
              | .error e =>
                return .error (Internal.mapRawError (.unavailable (some e) "direct /sys/fs/cgroup sibling directory unavailable"))
              | .ok cgDir =>
                let fail? ← do
                  match ← retryEintr (deps.files.faccessat none (cgroupSubfile cgDir "cgroup.kill").toUTF8 { write := true } {}) eintrFuel with
                  | .error e => pure (some (e, "cgroup v2 cgroup.kill is unavailable"))
                  | .ok () =>
                    match ← retryEintr (deps.files.faccessat none (cgroupSubfile cgDir "cgroup.events").toUTF8 { read := true } {}) eintrFuel with
                    | .error e => pure (some (e, "cgroup v2 cgroup.events is unavailable"))
                    | .ok () =>
                      let memFail? ←
                        if req.needMemoryCgroup then
                          match ← configureCgroupMemory deps.files cgDir "max" eintrFuel with
                          | .ok () => pure none
                          | .error (fname, e) =>
                            let msg := if fname == "memory.max" then
                              "direct cgroup v2 memory controller unavailable"
                            else
                              s!"direct cgroup v2 {fname} unavailable"
                            pure (some (e, msg))
                        else
                          pure none
                      match memFail? with
                      | some f => pure (some f)
                      | none =>
                        if req.needPidsCgroup then
                          match ← configureCgroupPids deps.files cgDir "max" eintrFuel with
                          | .ok () => pure none
                          | .error e => pure (some (e, "direct cgroup v2 pids controller unavailable"))
                        else
                          pure none
                let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                match fail? with
                | some (e, msg) =>
                  return .error (Internal.mapRawError (.unavailable (some e) msg))
                | none =>
                  return .ok ()
    | .ok (.ruleset h) =>
      Files.closeOpt deps.files (some h)
      return .error (Internal.mapRawError (.unavailable (some Errno.ENOSYS) "Landlock ABI >= 4 is required"))

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.discoverHostPreset`. -/
def discoverHostPresetPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (eintrFuel : Nat) :
    m (Except SandboxError HostRuntimePreset) := do
  if !deps.isLinux then
    return .error (Internal.mapRawError (.unavailable none "ProcessSandbox requires Linux"))
  let preset ← discoverHostPresetM deps.files deps.proc deps.passwd deps.getEnvHome eintrFuel
  return .ok preset

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.sealPlan`. -/
def sealPlanPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (plan : CompiledSandboxPlan) (seccompBytes : ByteArray)
    (initBytesRes : Except String ByteArray := embeddedInitBytes) :
    m (Except SandboxError PlanHandle) := do
  match Internal.encodePlan plan seccompBytes with
  | .error e => return .error e
  | .ok wireBytes =>
    if !isPlanWithinInitLimits plan then
      return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid compiled sandbox plan"))
    if !deps.isLinux then
      return .error (Internal.mapRawError (.unavailable none "ProcessSandbox requires Linux"))
    match initBytesRes with
    | .error msg =>
      return .error (Internal.mapRawError (.unavailable (some Errno.ENOEXEC) msg))
    | .ok initBytes =>
      match ← createSealedMemfd deps.sandbox deps.files "leanswe-psandbox-plan" wireBytes eintrFuel with
      | .error e =>
        return .error (Internal.mapRawError (.ioError none e "failed to seal plan memfd"))
      | .ok planMemfd =>
        match ← createSealedMemfd deps.sandbox deps.files "leanswe-psandbox-init" initBytes eintrFuel with
        | .error e =>
          Files.closeOpt deps.files (some planMemfd)
          return .error (Internal.mapRawError (.ioError none e "failed to seal init memfd"))
        | .ok initMemfd =>
          match ← createSealedMemfd deps.sandbox deps.files "leanswe-psandbox-hosts" SYNTHETIC_HOSTS_BYTES eintrFuel with
          | .error e =>
            Files.closeOpt deps.files (some planMemfd)
            Files.closeOpt deps.files (some initMemfd)
            return .error (Internal.mapRawError (.ioError none e "failed to seal hosts memfd"))
          | .ok hostsMemfd =>
            let slot : PlanSlotM fd := {
              plan := plan
              planMemfd := planMemfd
              initMemfd := initMemfd
              hostsMemfd := hostsMemfd
            }
            match ← tbl.insertPlan slot with
            | none =>
              Files.closeOpt deps.files (some planMemfd)
              Files.closeOpt deps.files (some initMemfd)
              Files.closeOpt deps.files (some hostsMemfd)
              return .error (Internal.mapRawError (.ioError none Errno.ENOMEM "plan handle table exhausted"))
            | some hid =>
              return .ok { handleId := hid }

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.closePlan`. -/
def closePlanPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (ph : PlanHandle) : m (Except SandboxError Unit) := do
  if !isValidSandboxHandleId ph.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid plan handle"))
  match ← tbl.detachPlan ph.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid or closed plan handle"))
  | some slot =>
    Files.closeOpt deps.files (some slot.planMemfd)
    Files.closeOpt deps.files (some slot.initMemfd)
    Files.closeOpt deps.files (some slot.hostsMemfd)
    return .ok ()

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.startPortForwarders`. -/
def startPortForwardersPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (bh : BoxHandle) (fwds : Array PortForward) :
    m (Except SandboxError PortForwarderHandle) := do
  if !isValidSandboxHandleId bh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid box handle"))
  match ← tbl.takeBoxListeners bh.handleId fwds.size with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid box handle, forwarders already started, or port count mismatch"))
  | some listenerFds =>
    let hostPorts := fwds.map (·.hostPort)
    match ← deps.startFwdTask listenerFds hostPorts with
    | .error e =>
      closeFdArray deps.files listenerFds
      return .error (Internal.mapRawError (.ioError none e s!"failed to start port forwarder: {Errno.name e}"))
    | .ok taskHandle =>
      match ← tbl.insertFwd { boxHandleId := bh.handleId, taskHandle := taskHandle } with
      | none =>
        deps.stopFwdTask taskHandle
        return .error (Internal.mapRawError (.ioError none Errno.ENOMEM "forwarder handle table exhausted"))
      | some fhid =>
        return .ok { handleId := fhid, boxHandleId := bh.handleId }

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.stopPortForwarders`. -/
def stopPortForwardersPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (fh : PortForwarderHandle) : m (Except SandboxError Unit) := do
  if !isValidSandboxHandleId fh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid forwarder handle"))
  match ← tbl.detachFwd fh.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid or stopped forwarder handle"))
  | some fslot =>
    deps.stopFwdTask fslot.taskHandle
    return .ok ()

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.readBoxOutput`. -/
def readBoxOutputPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel ioFuel : Nat)
    (bh : BoxHandle) (stdin : ByteArray) (timeoutMs : Nat) (maxOut? : Option Nat) :
    m (Except SandboxError SandboxResult) := do
  if !isValidSandboxHandleId bh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid box handle"))
  match ← tbl.takeBoxIo bh.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid box handle"))
  | some (inFd?, outFd?, errFd?, statusFd?, goFd?, prog, cwd) =>
    readBoxOutputCore deps.files deps.poll deps.timeRand prog cwd
      inFd? outFd? errFd? statusFd? goFd? stdin timeoutMs maxOut? eintrFuel ioFuel

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.killProcessGroup`. -/
def killProcessGroupPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (bh : BoxHandle) : m (Except SandboxError Unit) := do
  if !isValidSandboxHandleId bh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid box handle"))
  match ← tbl.findBoxKillInfo bh.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid box handle"))
  | some (pgid, _) =>
    killBoxPg deps.proc pgid eintrFuel

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.pidfdKill`. -/
def pidfdKillPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (bh : BoxHandle) : m (Except SandboxError Unit) := do
  if !isValidSandboxHandleId bh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid box handle"))
  match ← tbl.findBoxKillInfo bh.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid box handle"))
  | some (_, pidfd) =>
    killBoxPidfd deps.proc pidfd eintrFuel

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.reapBox`. -/
def reapBoxPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (bh : BoxHandle) : m (Except SandboxError Unit) := do
  if !isValidSandboxHandleId bh.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid box handle"))
  match ← tbl.detachBox bh.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid or reaped box handle"))
  | some bslot =>
    Files.closeOpt deps.files bslot.stdinFd?
    Files.closeOpt deps.files bslot.stdoutFd?
    Files.closeOpt deps.files bslot.stderrFd?
    Files.closeOpt deps.files bslot.statusFd?
    Files.closeOpt deps.files bslot.goFd?
    closeFdArray deps.files bslot.listenerFds
    if !bslot.cgroupDir.isEmpty then
      let _ ← writeTextFile deps.files (cgroupSubfile bslot.cgroupDir "cgroup.kill") "1" eintrFuel
    if bslot.pid > 0 && bslot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
      let _ ← LinuxSyscall.Process.waitpidReapLoop deps.proc bslot.pid.toInt32 eintrFuel
      pure ()
    Files.closeOpt deps.files (some bslot.pidfd)
    match ← cleanupCgroupDir deps.files deps.timeRand bslot.cgroupDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel with
    | .ok () => return .ok ()
    | .error e =>
      return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))

/-- Construct a `RawProcessSandboxOpsM m` bundle purely over `HostSysDepsM` and `HostTableOpsM`. -/
def mkRawOpsM {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (ioFuel : Nat := DEFAULT_IO_FUEL) :
    RawProcessSandboxOpsM m :=
  { mapRawError := Internal.mapRawError
    decodeHostAuditArch := Internal.decodeHostAuditArch
    encodePlan := Internal.encodePlan
    hostSeccompArch := hostSeccompArchPure deps
    preflight := fun req => preflightPure deps tbl eintrFuel req
    discoverHostPreset := discoverHostPresetPure deps eintrFuel
    sealPlan := fun plan sec => sealPlanPure deps tbl eintrFuel plan sec
    closePlan := closePlanPure deps tbl
    spawnBox := spawnBoxPure deps tbl eintrFuel
    startPortForwarders := startPortForwardersPure deps tbl
    stopPortForwarders := stopPortForwardersPure deps tbl
    readBoxOutput := readBoxOutputPure deps tbl eintrFuel ioFuel
    killProcessGroup := killProcessGroupPure deps tbl eintrFuel
    pidfdKill := pidfdKillPure deps tbl eintrFuel
    reapBox := reapBoxPure deps tbl eintrFuel
    activeResourceCounts := tbl.counts }

private initialize gHostTable : IO.Ref IoHostState ← IO.mkRef {}

/-- Default `IO` host capability bundle backed by `LinuxSyscall.*`, `PostFork`, `EnvVars.Raw`, `Forwarder`, and atomic `gHostTable`. -/
def defaultOps : Model.RawHostCapM IO :=
  mkIoHostCap gHostTable

end LeanSwe.ProcessSandbox.Raw.SysBridge
