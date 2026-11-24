import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.PostFork.Types
import LeanSwe.ProcessSandbox.Raw.Types

namespace LeanSwe.ProcessSandbox.Raw.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

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

/-- Capability bundle supplying all Linux syscalls, `PostFork`, environment probes, and forwarder lifecycle hooks consumed by `ProcessSandbox.Raw.SysBridge`. -/
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

/-- Check structural size bounds enforced by `psandbox-init` (`LSWP0002`) before sealing a `CompiledSandboxPlan`. -/
def isPlanWithinInitLimits (plan : CompiledSandboxPlan) : Bool :=
  plan.cwd.startsWith "/" &&
  plan.args.size ≤ 65536 &&
  plan.env.size ≤ 65536 &&
  plan.presetSystemEntries.size ≤ 1024 &&
  plan.presetEtcPaths.size ≤ 1024 &&
  plan.maskedPresetPaths.size ≤ 1024 &&
  plan.userMounts.size ≤ 4096 &&
  plan.portForwards.size ≤ 1024

end LeanSwe.ProcessSandbox.Raw.SysBridge
