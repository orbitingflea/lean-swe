import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.ProcessSandbox.Raw.Types

namespace LeanSwe.ProcessSandbox.Raw

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

/-- Polymorphic handle for a dedicated host-side TCP port-forwarder task and its wakeup `socketpair`. -/
structure ConcForwarderHandle (fd : Type) (Ref : Type → Type) (TaskHandle : Type → Type) where
  /-- Flag checked by the forwarder loop before and after `ppoll`. -/
  stopRequested : Ref Bool
  /-- Read end of the wakeup `socketpair` (closed after `waitTask`). -/
  wakeR : fd
  /-- Write end of the wakeup `socketpair` (signaled and closed on stop). -/
  wakeWRef : Ref (Option fd)
  /-- Handed-off box listener descriptors (closed after `waitTask`). -/
  listenerFds : Array fd
  /-- Dedicated asynchronous task executing `runForwarderLoop`. -/
  task : TaskHandle Unit

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

/-- Host resource-table state specialized to `RawFd` and `ConcForwarderHandle` for `Core.StateCellM`. -/
abbrev HostCellState (Ref : Type → Type) (TaskHandle : Type → Type) : Type :=
  HostTableState LeanSwe.LinuxSyscall.RawFd
    (ConcForwarderHandle LeanSwe.LinuxSyscall.RawFd Ref TaskHandle)

end LeanSwe.ProcessSandbox.Raw
