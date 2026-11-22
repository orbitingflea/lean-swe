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
import LeanSwe.ProcessSandbox.Host.Cgroup
import LeanSwe.ProcessSandbox.Host.Preset
import LeanSwe.ProcessSandbox.Host.Bwrap
import LeanSwe.ProcessSandbox.Host.Forwarder
import LeanSwe.ProcessSandbox.Host.StreamIo

namespace LeanSwe.ProcessSandbox.Host.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Host.Cgroup
open LeanSwe.ProcessSandbox.Host.Preset
open LeanSwe.ProcessSandbox.Host.Bwrap
open LeanSwe.ProcessSandbox.Host.Forwarder
open LeanSwe.ProcessSandbox.Host.StreamIo

/-- Sealed sandbox plan slot holding the structured `CompiledSandboxPlan` and three immutable `memfd` descriptors (zero duplicate wire parsing). -/
structure PlanSlotM (fd : Type) where
  /-- Validated structured sandbox plan retained directly for `bwrap` argv construction and cgroup setup. -/
  plan : CompiledSandboxPlan
  /-- Sealed `memfd` containing the `LSWP0002` wire payload read by `psandbox_init`. -/
  planMemfd : fd
  /-- Sealed `memfd` containing the compiled `leanswe-psandbox-init` helper ELF binary. -/
  initMemfd : fd
  /-- Sealed `memfd` containing synthetic `/etc/hosts` bytes. -/
  hostsMemfd : fd

/-- Active spawned sandbox box slot holding process identifiers, pipes, handed-off listeners, and per-box cgroup directory. -/
structure BoxSlotM (fd : Type) where
  /-- Host-visible `bwrap` PID (`1 ≤ pid ≤ 0x7fffffff`). -/
  pid : UInt32
  /-- Dedicated host process group ID (`pgid = pid`). -/
  pgid : UInt32
  /-- Race-free Linux `pidfd` descriptor tracking `pid`. -/
  pidfd : fd
  /-- Parent write end of guest `stdin` pipe (taken by `readBoxOutput`). -/
  stdinFd? : Option fd
  /-- Parent read end of guest `stdout` pipe (taken by `readBoxOutput`). -/
  stdoutFd? : Option fd
  /-- Parent read end of guest `stderr` pipe (taken by `readBoxOutput`). -/
  stderrFd? : Option fd
  /-- Parent read end of `psandbox_init` `status_pipe` (taken by `readBoxOutput`). -/
  statusFd? : Option fd
  /-- Parent write end of `psandbox_init` `go_pipe` (taken by `readBoxOutput`). -/
  goFd? : Option fd
  /-- Whether `readBoxOutput` has already claimed this box's I/O pipes. -/
  readStarted : Bool := false
  /-- Whether `startPortForwarders` has already claimed `listenerFds`. -/
  fwdsTaken : Bool := false
  /-- Handed-off in-box `127.0.0.1:boxPort` listener descriptors awaiting `startPortForwarders`. -/
  listenerFds : Array fd := #[]
  /-- Per-box direct `/sys/fs/cgroup/...` sibling directory path. -/
  cgroupDir : String
  /-- Guest executable path for `execvp` error reporting. -/
  program : String
  /-- Guest working directory for `chdir` error reporting. -/
  cwd : String

/-- Active host-side TCP port-forwarder slot linking handle ID to box handle ID and running task handle. -/
structure ForwarderSlotM (fwdTask : Type) where
  /-- Associated `BoxHandle.handleId`. -/
  boxHandleId : Nat
  /-- Backend forwarder task handle stopped by `stopPortForwarders`. -/
  taskHandle : fwdTask

/-- Pure in-memory host handle table tracking active plans, boxes, forwarders, and monotonic IDs. -/
structure HostTableState (fd : Type) (fwdTask : Type) where
  /-- Next monotonically increasing 64-bit handle ID (`≥ 1`). -/
  nextId : Nat := 1
  /-- Monotonic per-process cgroup directory sequence counter (`≥ 1`). -/
  cgSeq : Nat := 1
  /-- Active sealed plan slots keyed by `handleId`. -/
  plans : List (Nat × PlanSlotM fd) := []
  /-- Active unreaped box slots keyed by `handleId`. -/
  boxes : List (Nat × BoxSlotM fd) := []
  /-- Active running forwarder slots keyed by `handleId`. -/
  forwarders : List (Nat × ForwarderSlotM fwdTask) := []
  deriving Inhabited

/-- Lookup helper over association list `xs`. -/
def assocFind {α : Type} (hid : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k, v) :: rest => if k == hid then some v else assocFind hid rest

/-- Remove first entry matching `hid` from association list `xs`. -/
def assocRemove {α : Type} (hid : Nat) : List (Nat × α) → Option α × List (Nat × α)
  | [] => (none, [])
  | (k, v) :: rest =>
    if k == hid then
      (some v, rest)
    else
      let (found?, rest') := assocRemove hid rest
      (found?, (k, v) :: rest')

/-- Allocate a valid non-zero 64-bit handle ID if `st.nextId < UInt64.size`. -/
def allocHandleIdPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) :
    Option Nat × HostTableState fd fwdTask :=
  let hid := st.nextId
  if isValidSandboxHandleId hid then
    (some hid, { st with nextId := hid + 1 })
  else
    (none, st)

/-- Pure step inserting a sealed `PlanSlotM`. -/
def insertPlanPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (slot : PlanSlotM fd) :
    Option Nat × HostTableState fd fwdTask :=
  let (hid?, st1) := allocHandleIdPure st
  match hid? with
  | none => (none, st)
  | some hid => (some hid, { st1 with plans := (hid, slot) :: st1.plans })

/-- Pure step detaching a `PlanSlotM`. -/
def detachPlanPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (hid : Nat) :
    Option (PlanSlotM fd) × HostTableState fd fwdTask :=
  let (found?, plans') := assocRemove hid st.plans
  (found?, { st with plans := plans' })

/-- Pure step inserting a spawned `BoxSlotM`. -/
def insertBoxPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (slot : BoxSlotM fd) :
    Option Nat × HostTableState fd fwdTask :=
  let (hid?, st1) := allocHandleIdPure st
  match hid? with
  | none => (none, st)
  | some hid => (some hid, { st1 with boxes := (hid, slot) :: st1.boxes })

/-- Pure step detaching a `BoxSlotM` for `reapBox`. -/
def detachBoxPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (hid : Nat) :
    Option (BoxSlotM fd) × HostTableState fd fwdTask :=
  let (found?, boxes') := assocRemove hid st.boxes
  (found?, { st with boxes := boxes' })

/-- Pure step claiming handed-off listener descriptors from `hid` for `startPortForwarders`. -/
def takeBoxListenersPure {fd fwdTask : Type} (st : HostTableState fd fwdTask)
    (hid expectedCount : Nat) : Option (Array fd) × HostTableState fd fwdTask :=
  match assocFind hid st.boxes with
  | none => (none, st)
  | some slot =>
    if slot.fwdsTaken || slot.listenerFds.size != expectedCount then
      (none, st)
    else
      let boxes' := st.boxes.map fun (k, b) =>
        if k == hid then (k, { b with fwdsTaken := true, listenerFds := #[] }) else (k, b)
      (some slot.listenerFds, { st with boxes := boxes' })

/-- Pure step claiming streaming pipes from `hid` for `readBoxOutput` (rejected if already started). -/
def takeBoxIoPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (hid : Nat) :
    Option (Option fd × Option fd × Option fd × Option fd × Option fd × String × String) ×
      HostTableState fd fwdTask :=
  match assocFind hid st.boxes with
  | none => (none, st)
  | some slot =>
    if slot.readStarted then
      (none, st)
    else
      let boxes' := st.boxes.map fun (k, b) =>
        if k == hid then
          (k, { b with
            readStarted := true
            stdinFd? := none
            stdoutFd? := none
            stderrFd? := none
            statusFd? := none
            goFd? := none })
        else (k, b)
      (some (slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?, slot.statusFd?, slot.goFd?, slot.program, slot.cwd),
        { st with boxes := boxes' })

/-- Pure step inserting a running `ForwarderSlotM`. -/
def insertFwdPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (slot : ForwarderSlotM fwdTask) :
    Option Nat × HostTableState fd fwdTask :=
  let (hid?, st1) := allocHandleIdPure st
  match hid? with
  | none => (none, st)
  | some hid => (some hid, { st1 with forwarders := (hid, slot) :: st1.forwarders })

/-- Pure step detaching a `ForwarderSlotM`. -/
def detachFwdPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) (hid : Nat) :
    Option (ForwarderSlotM fwdTask) × HostTableState fd fwdTask :=
  let (found?, fwds') := assocRemove hid st.forwarders
  (found?, { st with forwarders := fwds' })

/-- Pure step allocating the next cgroup sequence number. -/
def nextCgSeqPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) :
    Nat × HostTableState fd fwdTask :=
  (st.cgSeq, { st with cgSeq := st.cgSeq + 1 })

/-- Pure resource-count snapshot matching `SandboxResourceCounts`. -/
def countsPure {fd fwdTask : Type} (st : HostTableState fd fwdTask) : SandboxResourceCounts :=
  { openPlans := st.plans.length
    activeBoxes := st.boxes.length
    activeForwarders := st.forwarders.length }

/-- Capability bundle over host handle-table operations parameterized by monad `m`, descriptor `fd`, and forwarder handle `fwdTask`. -/
structure HostTableOpsM (m : Type → Type) (fd : Type) (fwdTask : Type) where
  /-- Insert a sealed plan slot and return its allocated `handleId`. -/
  insertPlan : PlanSlotM fd → m (Option Nat)
  /-- Look up an active plan slot without removing it. -/
  findPlan : Nat → m (Option (PlanSlotM fd))
  /-- Atomically detach a plan slot for `closePlan`. -/
  detachPlan : Nat → m (Option (PlanSlotM fd))
  /-- Insert a spawned box slot and return its allocated `handleId`. -/
  insertBox : BoxSlotM fd → m (Option Nat)
  /-- Look up `(pgid, pidfd)` for an active box handle. -/
  findBoxKillInfo : Nat → m (Option (UInt32 × fd))
  /-- Atomically claim handed-off listener FDs from a box slot. -/
  takeBoxListeners : Nat → Nat → m (Option (Array fd))
  /-- Atomically claim streaming pipe FDs from a box slot. -/
  takeBoxIo : Nat → m (Option (Option fd × Option fd × Option fd × Option fd × Option fd × String × String))
  /-- Atomically detach a box slot for `reapBox`. -/
  detachBox : Nat → m (Option (BoxSlotM fd))
  /-- Insert a running forwarder slot and return its allocated `handleId`. -/
  insertFwd : ForwarderSlotM fwdTask → m (Option Nat)
  /-- Atomically detach a forwarder slot for `stopPortForwarders`. -/
  detachFwd : Nat → m (Option (ForwarderSlotM fwdTask))
  /-- Allocate the next monotonic per-box cgroup sequence number. -/
  nextCgSeq : m Nat
  /-- Snapshot active `(openPlans, activeBoxes, activeForwarders)` counts. -/
  counts : m SandboxResourceCounts

/-- Pure `StateM S` instantiation of `HostTableOpsM` via lens `(getTbl, setTbl)`. -/
def stateHostTableOps {S fd fwdTask : Type}
    (getTbl : S → HostTableState fd fwdTask)
    (setTbl : S → HostTableState fd fwdTask → S) : HostTableOpsM (StateM S) fd fwdTask where
  insertPlan slot := modifyGet fun s =>
    let (res, t') := insertPlanPure (getTbl s) slot
    (res, setTbl s t')
  findPlan hid := do
    let s ← get
    return assocFind hid (getTbl s).plans
  detachPlan hid := modifyGet fun s =>
    let (res, t') := detachPlanPure (getTbl s) hid
    (res, setTbl s t')
  insertBox slot := modifyGet fun s =>
    let (res, t') := insertBoxPure (getTbl s) slot
    (res, setTbl s t')
  findBoxKillInfo hid := do
    let s ← get
    return (assocFind hid (getTbl s).boxes).map fun b => (b.pgid, b.pidfd)
  takeBoxListeners hid expected := modifyGet fun s =>
    let (res, t') := takeBoxListenersPure (getTbl s) hid expected
    (res, setTbl s t')
  takeBoxIo hid := modifyGet fun s =>
    let (res, t') := takeBoxIoPure (getTbl s) hid
    (res, setTbl s t')
  detachBox hid := modifyGet fun s =>
    let (res, t') := detachBoxPure (getTbl s) hid
    (res, setTbl s t')
  insertFwd slot := modifyGet fun s =>
    let (res, t') := insertFwdPure (getTbl s) slot
    (res, setTbl s t')
  detachFwd hid := modifyGet fun s =>
    let (res, t') := detachFwdPure (getTbl s) hid
    (res, setTbl s t')
  nextCgSeq := modifyGet fun s =>
    let (seq, t') := nextCgSeqPure (getTbl s)
    (seq, setTbl s t')
  counts := do
    let s ← get
    return countsPure (getTbl s)

/-- Capability bundle supplying all Linux syscalls, `PostFork`, environment probes, and forwarder lifecycle hooks consumed by `ProcessSandbox.Host.SysBridge`. -/
structure HostSysDepsM (m : Type → Type) (fd : Type) (fwdTask : Type) where
  /-- Curated Linux file/descriptor syscalls (`openat`, `close`, `read`, `write`, `fstatat`, `faccessat`, `mkdirat`, `unlinkat`, `readlinkat`, `fcntl`, `reopenReadOnly`). -/
  files : Files.FilesOpsM m fd
  /-- Curated Linux socket syscalls (`socketpair`, `recvmsg`, `sendto`, etc.). -/
  net : Net.NetOpsM m fd
  /-- Curated Linux `ppoll` syscall. -/
  poll : Poll.PollOpsM m fd
  /-- Curated Linux process syscalls (`pipe2`, `waitpid`, `kill`, `pidfd_open`, `pidfd_send_signal`, `getpid`, `getuid`). -/
  proc : LinuxSyscall.Process.ProcessOpsM m fd
  /-- Curated Linux sandbox syscalls (`landlockCreateRuleset`, `seccomp`, `memfdCreate`). -/
  sandbox : Sandbox.SandboxOpsM m fd
  /-- Curated Linux monotonic clock and nanosleep syscalls. -/
  timeRand : TimeRand.TimeRandOpsM m
  /-- Curated Linux `getpwuid` syscall. -/
  passwd : Passwd.PasswdOpsM m
  /-- Verified post-`fork` child setup and sync-barrier bundle. -/
  postFork : PostFork.PostForkOpsM m fd
  /-- Whether the host OS is Linux (`System.Platform.isLinux`). -/
  isLinux : Bool
  /-- Compiler target triple (`System.Platform.target`, e.g. `x86_64-unknown-linux-gnu`). -/
  target : String
  /-- Read raw `PATH` environment bytes (`EnvVars.Raw`). -/
  getEnvPath : m (Option ByteArray)
  /-- Read `HOME` environment string (`EnvVars.Raw`). -/
  getEnvHome : m (Option String)
  /-- Start the host-side non-blocking TCP forwarder for handed-off listener FDs and host ports. -/
  startFwdTask : Array fd → Array UInt16 → m (Except Errno fwdTask)
  /-- Stop a running forwarder task and close its listener and wakeup descriptors. -/
  stopFwdTask : fwdTask → m Unit

/-- Check structural size bounds enforced by `psandbox_init.c` (`LSWP0002`) before sealing a `CompiledSandboxPlan`. -/
def isPlanWithinInitLimits (plan : CompiledSandboxPlan) : Bool :=
  plan.cwd.startsWith "/" &&
  plan.args.size ≤ 65536 &&
  plan.env.size ≤ 65536 &&
  plan.presetSystemEntries.size ≤ 1024 &&
  plan.presetEtcPaths.size ≤ 1024 &&
  plan.maskedPresetPaths.size ≤ 1024 &&
  plan.userMounts.size ≤ 4096 &&
  plan.portForwards.size ≤ 1024

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.hostSeccompArch`. -/
def hostSeccompArchPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) : m (Except SandboxError SeccompArch) :=
  pure (Internal.decodeHostAuditArch (detectHostAuditArch deps.isLinux deps.target))

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.preflight`. -/
def preflightPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (req : PreflightReq) : m (Except SandboxError Unit) := do
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
        match embeddedInitBytes with
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
    (eintrFuel : Nat) (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    m (Except SandboxError PlanHandle) := do
  match Internal.encodePlan plan seccompBytes with
  | .error e => return .error e
  | .ok wireBytes =>
    if !isPlanWithinInitLimits plan then
      return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid compiled sandbox plan"))
    if !deps.isLinux then
      return .error (Internal.mapRawError (.unavailable none "ProcessSandbox requires Linux"))
    match embeddedInitBytes with
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

/-- Precheck every user bind-mount `hostPath` via `stat` before creating cgroups or spawning `bwrap`. -/
def precheckHostMounts {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat) :
    List SandboxMount → m (Except SandboxError Unit)
  | [] => pure (.ok ())
  | mnt :: rest => do
    match mountHostPath? mnt with
    | none => precheckHostMounts files eintrFuel rest
    | some hp =>
      match ← retryEintr (files.fstatat none hp.toUTF8 {}) eintrFuel with
      | .error e => return .error (mapPathErrnoToSandboxError hp "host mount path error" e)
      | .ok _ => precheckHostMounts files eintrFuel rest

/-- Best-effort teardown of a partially spawned box after `releaseBarrier` succeeded. -/
def rollbackRunningChild {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (proc : LinuxSyscall.Process.ProcessOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (childPid : UInt32) (pidfd? : Option fd) (cgDir : String) (eintrFuel : Nat) : m Unit := do
  let _ ← killBoxPg proc childPid eintrFuel
  match pidfd? with
  | some pfd =>
    let _ ← killBoxPidfd proc pfd eintrFuel
    pure ()
  | none => pure ()
  if !cgDir.isEmpty then
    let _ ← writeTextFile files (cgroupSubfile cgDir "cgroup.kill") "1" eintrFuel
  if childPid > 0 && childPid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
    let _ ← LinuxSyscall.Process.waitpidReapLoop proc childPid.toInt32 eintrFuel
    pure ()
  Files.closeOpt files pidfd?
  let _ ← cleanupCgroupDir files timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
  pure ()

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.spawnBox`. -/
def spawnBoxPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (ph : PlanHandle) : m (Except SandboxError BoxHandle) := do
  if !isValidSandboxHandleId ph.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid plan handle"))
  match ← tbl.findPlan ph.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid or closed plan handle"))
  | some pslot =>
    let plan := pslot.plan
    match ← precheckHostMounts deps.files eintrFuel plan.userMounts.toList with
    | .error e => return .error e
    | .ok () =>
      match ← resolveBwrapPath deps.files deps.getEnvPath eintrFuel with
      | none =>
        return .error (Internal.mapRawError (.unavailable (some Errno.ENOENT) "bwrap executable not found in PATH"))
      | some bwrapPath =>
        match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
        | .error e => return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
        | .ok (inR, inW) =>
          match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
          | .error e =>
            Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
            return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
          | .ok (outR, outW) =>
            match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
            | .error e =>
              Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
              Files.closeOpt deps.files (some outR); Files.closeOpt deps.files (some outW)
              return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
            | .ok (errR, errW) =>
              let closeStdioPipes : m Unit := do
                Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
                Files.closeOpt deps.files (some outR); Files.closeOpt deps.files (some outW)
                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some errW)
              match ← retryEintr (deps.files.reopenReadOnly pslot.initMemfd) eintrFuel with
              | .error e =>
                closeStdioPipes
                return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed init memfd"))
              | .ok initFd =>
                match ← retryEintr (deps.files.reopenReadOnly pslot.hostsMemfd) eintrFuel with
                | .error e =>
                  Files.closeOpt deps.files (some initFd); closeStdioPipes
                  return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed hosts memfd"))
                | .ok hostsFd =>
                  match ← retryEintr (deps.files.reopenReadOnly pslot.planMemfd) eintrFuel with
                  | .error e =>
                    Files.closeOpt deps.files (some hostsFd); Files.closeOpt deps.files (some initFd); closeStdioPipes
                    return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed plan memfd"))
                  | .ok planFd =>
                    let closeBaseFds : m Unit := do
                      Files.closeOpt deps.files (some planFd)
                      Files.closeOpt deps.files (some hostsFd)
                      Files.closeOpt deps.files (some initFd)
                      closeStdioPipes
                    match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
                    | .error e =>
                      closeBaseFds
                      return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
                    | .ok (statusR, statusW) =>
                      match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
                      | .error e =>
                        Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW); closeBaseFds
                        return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
                      | .ok (goR, goW) =>
                        let nFwds := plan.portForwards.size
                        let ctrlRes ←
                          if nFwds > 0 then
                            match ← retryEintr (deps.net.socketpair .unix .seqpacket { cloexec := true }) eintrFuel with
                            | .ok pair => pure (Except.ok (some pair))
                            | .error e => pure (Except.error e)
                          else
                            pure (Except.ok none)
                        match ctrlRes with
                        | .error e =>
                          Files.closeOpt deps.files (some goR); Files.closeOpt deps.files (some goW)
                          Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW)
                          closeBaseFds
                          return .error (Internal.mapRawError (.ioError none e "socketpair failed"))
                        | .ok ctrlPair? =>
                          let ctrlR? := ctrlPair?.map Prod.fst
                          let ctrlW? := ctrlPair?.map Prod.snd
                          let closeAllPreFork : m Unit := do
                            Files.closeOpt deps.files ctrlR?; Files.closeOpt deps.files ctrlW?
                            Files.closeOpt deps.files (some goR); Files.closeOpt deps.files (some goW)
                            Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW)
                            closeBaseFds
                          match ← deps.proc.getpid with
                          | .error e =>
                            closeAllPreFork
                            return .error (Internal.mapRawError (.unavailable (some e) "getpid failed"))
                          | .ok hostPid =>
                            let seq ← tbl.nextCgSeq
                            match ← createSiblingCgroup deps.files hostPid seq eintrFuel with
                            | .error e =>
                              closeAllPreFork
                              return .error (Internal.mapRawError (.unavailable (some e) s!"failed to create direct cgroup v2 directory: {Errno.name e}"))
                            | .ok cgDir =>
                              let cgSetupErr? ← do
                                match ← retryEintr (deps.files.faccessat none (cgroupSubfile cgDir "cgroup.kill").toUTF8 { write := true } {}) eintrFuel with
                                | .error e => pure (some (e, "direct cgroup v2 cgroup.kill unavailable"))
                                | .ok () =>
                                  let memErr? ←
                                    match plan.limits.memoryMaxBytes with
                                    | none => pure none
                                    | some memMax =>
                                      match ← configureCgroupMemory deps.files cgDir (toString memMax) eintrFuel with
                                      | .ok () => pure none
                                      | .error (fname, e) => pure (some (e, s!"failed to set direct cgroup v2 {fname}: {Errno.name e}"))
                                  match memErr? with
                                  | some me => pure (some me)
                                  | none =>
                                    match plan.limits.pidsMax with
                                    | none => pure none
                                    | some pMax =>
                                      match ← configureCgroupPids deps.files cgDir (toString (cappedPidsMax pMax)) eintrFuel with
                                      | .ok () => pure none
                                      | .error e => pure (some (e, s!"failed to set direct cgroup v2 pids.max: {Errno.name e}"))
                              match cgSetupErr? with
                              | some (e, msg) =>
                                closeAllPreFork
                                let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                return .error (Internal.mapRawError (.unavailable (some e) msg))
                              | none =>
                                let baseKeep : Array (PostFork.FdRef fd) :=
                                  #[.handle statusW, .handle goR, .handle initFd, .handle hostsFd, .handle planFd]
                                let keepFds := match ctrlW? with
                                  | some cw => baseKeep.push (.handle cw)
                                  | none => baseKeep
                                let baseClose : Array (PostFork.FdRef fd) :=
                                  #[.handle inW, .handle outR, .handle errR, .handle statusR, .handle goW]
                                let closeFds := match ctrlR? with
                                  | some cr => baseClose.push (.handle cr)
                                  | none => baseClose
                                let childSpec : PostFork.ChildSpecM fd := {
                                  path := bwrapPath
                                  argv := buildSpawnBwrapArgv bwrapPath plan initFd hostsFd planFd statusW goR ctrlW?
                                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) false
                                  fdPolicy := .closeAllAbove2Except keepFds
                                  closeFds := closeFds
                                  processGroup := .newGroup
                                  sigpipe := .resetDefault
                                  forkMode := .immortalThread
                                }
                                match ← deps.postFork.spawnWithBarrier childSpec with
                                | .error pfErr =>
                                  closeAllPreFork
                                  let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                  return .error (Internal.mapRawError (.unavailable pfErr.errno s!"failed to fork bwrap: {pfErr.message}"))
                                | .ok pending =>
                                  let closeChildSides : m Unit := do
                                    Files.closeOpt deps.files (some initFd)
                                    Files.closeOpt deps.files (some hostsFd)
                                    Files.closeOpt deps.files (some planFd)
                                    Files.closeOpt deps.files (some inR)
                                    Files.closeOpt deps.files (some outW)
                                    Files.closeOpt deps.files (some errW)
                                    Files.closeOpt deps.files (some statusW)
                                    Files.closeOpt deps.files (some goR)
                                    Files.closeOpt deps.files ctrlW?
                                  let closeParentSides : m Unit := do
                                    Files.closeOpt deps.files (some inW)
                                    Files.closeOpt deps.files (some outR)
                                    Files.closeOpt deps.files (some errR)
                                    Files.closeOpt deps.files (some statusR)
                                    Files.closeOpt deps.files (some goW)
                                    Files.closeOpt deps.files ctrlR?
                                  match ← retryEintr (deps.proc.pidfd_open pending.pid {}) eintrFuel with
                                  | .error e =>
                                    let _ ← deps.postFork.abortBarrier pending
                                    closeChildSides; closeParentSides
                                    let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                    return .error (Internal.mapRawError (.unavailable (some e) s!"pidfd_open failed: {Errno.name e}"))
                                  | .ok pidfd =>
                                    match ← writeTextFile deps.files (cgroupSubfile cgDir "cgroup.procs") (toString pending.pid) eintrFuel with
                                    | .error e =>
                                      let _ ← deps.postFork.abortBarrier pending
                                      Files.closeOpt deps.files (some pidfd)
                                      closeChildSides; closeParentSides
                                      let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                      return .error (Internal.mapRawError (.unavailable (some e) s!"failed to attach child to cgroup.procs: {Errno.name e}"))
                                    | .ok () =>
                                      let relRes ← deps.postFork.releaseBarrier pending
                                      closeChildSides
                                      match relRes with
                                      | .error pfErr =>
                                        Files.closeOpt deps.files (some pidfd)
                                        closeParentSides
                                        let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                        return .error (Internal.mapRawError (.unavailable pfErr.errno s!"execvp bwrap failed: {pfErr.message}"))
                                      | .ok child =>
                                        let recvRes ←
                                          match ctrlR? with
                                          | some cr =>
                                            let r ← recvFdsScm deps.files deps.net deps.poll cr statusR nFwds
                                            Files.closeOpt deps.files (some cr)
                                            pure r
                                          | none => pure (.ok #[])
                                        match recvRes with
                                        | .error e =>
                                          let snip ← drainStderrSnippet deps.files errR
                                          Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                          Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                          Files.closeOpt deps.files (some goW)
                                          rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                          let msg := if snip.isEmpty then "failed to receive box port listener descriptors" else s!"sandbox setup failed: {snip}"
                                          return .error (Internal.mapRawError (.unavailable (some e) msg))
                                        | .ok listenerFds =>
                                          let (smsg?, readErr?) ← readInitStatusBlocking deps.files statusR ByteArray.empty 64
                                          match smsg? with
                                          | some msg =>
                                            if msg.kind == PS_STATUS_READY then
                                              let pgid := child.pgid.getD child.pid
                                              if child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID then
                                                closeFdArray deps.files listenerFds
                                                Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                                Files.closeOpt deps.files (some goW)
                                                rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                                return .error (Internal.mapRawError (.unavailable none "invalid child pid/pgid"))
                                              let bslot : BoxSlotM fd := {
                                                pid := child.pid
                                                pgid := pgid
                                                pidfd := pidfd
                                                stdinFd? := some inW
                                                stdoutFd? := some outR
                                                stderrFd? := some errR
                                                statusFd? := some statusR
                                                goFd? := some goW
                                                listenerFds := listenerFds
                                                cgroupDir := cgDir
                                                program := plan.program
                                                cwd := plan.cwd
                                              }
                                              match ← tbl.insertBox bslot with
                                              | none =>
                                                closeFdArray deps.files listenerFds
                                                Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                                Files.closeOpt deps.files (some goW)
                                                rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                                return .error (Internal.mapRawError (.ioError none Errno.ENOMEM "box handle table exhausted"))
                                              | some bhid =>
                                                return .ok {
                                                  handleId := bhid
                                                  pid := Int.ofNat child.pid.toNat
                                                  pgid := Int.ofNat pgid.toNat
                                                  pidfd := 0
                                                }
                                            else
                                              let snip ← drainStderrSnippet deps.files errR
                                              let eCode : Errno :=
                                                if msg.kind == PS_STATUS_INIT_ERR && msg.value != 0 then
                                                  msg.value.toUInt32
                                                else
                                                  readErr?.getD Errno.EPERM
                                              closeFdArray deps.files listenerFds
                                              Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                              Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                              Files.closeOpt deps.files (some goW)
                                              rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                              let msgTxt := if snip.isEmpty then s!"sandbox init failed before execvp: {Errno.name eCode}" else s!"sandbox init failed before execvp: {snip}"
                                              return .error (Internal.mapRawError (.unavailable (some eCode) msgTxt))
                                          | none =>
                                            let snip ← drainStderrSnippet deps.files errR
                                            let eCode : Errno := readErr?.getD Errno.EPERM
                                            closeFdArray deps.files listenerFds
                                            Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                            Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                            Files.closeOpt deps.files (some goW)
                                            rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                            let msgTxt := if snip.isEmpty then s!"sandbox init failed before execvp: {Errno.name eCode}" else s!"sandbox init failed before execvp: {snip}"
                                            return .error (Internal.mapRawError (.unavailable (some eCode) msgTxt))

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
    preflight := preflightPure deps tbl eintrFuel
    discoverHostPreset := discoverHostPresetPure deps eintrFuel
    sealPlan := sealPlanPure deps tbl eintrFuel
    closePlan := closePlanPure deps tbl
    spawnBox := spawnBoxPure deps tbl eintrFuel
    startPortForwarders := startPortForwardersPure deps tbl
    stopPortForwarders := stopPortForwardersPure deps tbl
    readBoxOutput := readBoxOutputPure deps tbl eintrFuel ioFuel
    killProcessGroup := killProcessGroupPure deps tbl eintrFuel
    pidfdKill := pidfdKillPure deps tbl eintrFuel
    reapBox := reapBoxPure deps tbl eintrFuel
    activeResourceCounts := tbl.counts }

private initialize gHostTable : IO.Ref (HostTableState RawFd IoForwarderHandle) ← IO.mkRef {}

/-- Default `IO` handle-table capability bundle backed by atomic `IO.Ref.modifyGet` transitions. -/
def ioHostTableOps : HostTableOpsM IO RawFd IoForwarderHandle where
  insertPlan slot := (gHostTable.modifyGet fun st => insertPlanPure st slot : BaseIO _)
  findPlan hid := do
    let st ← (gHostTable.get : BaseIO _)
    return assocFind hid st.plans
  detachPlan hid := (gHostTable.modifyGet fun st => detachPlanPure st hid : BaseIO _)
  insertBox slot := (gHostTable.modifyGet fun st => insertBoxPure st slot : BaseIO _)
  findBoxKillInfo hid := do
    let st ← (gHostTable.get : BaseIO _)
    return (assocFind hid st.boxes).map fun b => (b.pgid, b.pidfd)
  takeBoxListeners hid expected :=
    (gHostTable.modifyGet fun st => takeBoxListenersPure st hid expected : BaseIO _)
  takeBoxIo hid := (gHostTable.modifyGet fun st => takeBoxIoPure st hid : BaseIO _)
  detachBox hid := (gHostTable.modifyGet fun st => detachBoxPure st hid : BaseIO _)
  insertFwd slot := (gHostTable.modifyGet fun st => insertFwdPure st slot : BaseIO _)
  detachFwd hid := (gHostTable.modifyGet fun st => detachFwdPure st hid : BaseIO _)
  nextCgSeq := (gHostTable.modifyGet fun st => nextCgSeqPure st : BaseIO _)
  counts := do
    let st ← (gHostTable.get : BaseIO _)
    return countsPure st

/-- Default `IO` syscall dependency bundle backed purely by `LinuxSyscall.*`, `PostFork`, `EnvVars.Raw`, and `Forwarder`. -/
def ioHostSysDeps : HostSysDepsM IO RawFd IoForwarderHandle where
  files := Files.defaultOps
  net := Net.defaultOps
  poll := Poll.defaultOps
  proc := LinuxSyscall.Process.defaultOps
  sandbox := Sandbox.defaultOps
  timeRand := TimeRand.defaultOps
  passwd := Passwd.defaultOps
  postFork := PostFork.defaultOps
  isLinux := !System.Platform.isWindows && !System.Platform.isOSX
  target := System.Platform.target
  getEnvPath := do
    match ← EnvVars.Raw.getEnv "PATH" with
    | .ok (some s) => return some s.toUTF8
    | _ => return none
  getEnvHome := do
    match ← EnvVars.Raw.getEnv "HOME" with
    | .ok v? => return v?
    | .error _ => return none
  startFwdTask := startIoForwarder
  stopFwdTask := stopIoForwarder

/-- Default `IO` `RawProcessSandboxOps` bundle implemented in pure Lean over `LinuxSyscall.*`, `PostFork`, `EnvVars.Raw`, and `NetRelay`. -/
def defaultOps : RawProcessSandboxOps :=
  let core := mkRawOpsM ioHostSysDeps ioHostTableOps
  { mapRawError := Internal.mapRawError
    decodeHostAuditArch := Internal.decodeHostAuditArch
    encodePlan := Internal.encodePlan
    hostSeccompArch := Internal.catchSandbox core.hostSeccompArch
    preflight := fun req => Internal.catchSandbox (core.preflight req)
    discoverHostPreset := Internal.catchSandbox core.discoverHostPreset
    sealPlan := fun plan seccomp => Internal.catchSandbox (core.sealPlan plan seccomp)
    closePlan := fun ph => Internal.catchSandbox (core.closePlan ph)
    spawnBox := fun ph => Internal.catchSandbox (core.spawnBox ph)
    startPortForwarders := fun bh fwds => Internal.catchSandbox (core.startPortForwarders bh fwds)
    stopPortForwarders := fun fh => Internal.catchSandbox (core.stopPortForwarders fh)
    readBoxOutput := fun bh stdin toMs maxOut? =>
      Internal.catchSandbox (core.readBoxOutput bh stdin toMs maxOut?)
    killProcessGroup := fun bh => Internal.catchSandbox (core.killProcessGroup bh)
    pidfdKill := fun bh => Internal.catchSandbox (core.pidfdKill bh)
    reapBox := fun bh => Internal.catchSandbox (core.reapBox bh)
    activeResourceCounts := core.activeResourceCounts }

end LeanSwe.ProcessSandbox.Host.SysBridge
