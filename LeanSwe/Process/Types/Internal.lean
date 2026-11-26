import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.PostFork.Types
import LeanSwe.EnvVars.Raw.Types
import LeanSwe.Process.Types

/-! Internal `SysBridge` and host-capability data shapes shared across `LeanSwe.Process`. -/

namespace LeanSwe.Process.Internal

open LeanSwe.Process

/-- Dependency bundle consumed by `SysBridge` parameterized over monad `m` and descriptor type `fd`. -/
structure SysDepsM (m : Type → Type) (fd : Type) where
  /-- Curated Linux process syscalls (`pipe2`, `waitpid`, `kill`, `pidfd_open`, `pidfd_send_signal`, `getpid`, `getuid`). -/
  proc : LeanSwe.LinuxSyscall.Process.ProcessOpsM m fd
  /-- Curated Linux file and descriptor syscalls (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`). -/
  files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd
  /-- Curated Linux descriptor-readiness syscall bundle (`ppoll`). -/
  poll : LeanSwe.LinuxSyscall.Poll.PollOpsM m fd
  /-- Curated Linux monotonic clock and nanosleep syscalls (`clock_gettime`, `clock_nanosleep`). -/
  timeRand : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m
  /-- Verified post-`fork` child setup and `execve` capability bundle. -/
  postFork : LeanSwe.PostFork.PostForkOpsM m fd
  /-- Snapshot raw NUL-free `environ(7)` byte entries when `inheritEnv = true`. -/
  listAmbientEnv : m (Except ProcessError (Array ByteArray))

/-- Direct imported OS capability bundle for `LeanSwe.Process` over `manifest.deps` specialized to `RawFd`. -/
structure ProcessSysCapsM (m : Type → Type) where
  /-- Curated Linux process syscalls (`pipe2`, `waitpid`, `kill`, etc.). -/
  proc : LeanSwe.LinuxSyscall.Process.ProcessOpsM m LeanSwe.LinuxSyscall.RawFd
  /-- Curated Linux file and descriptor syscalls (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`, etc.). -/
  files : LeanSwe.LinuxSyscall.Files.FilesOpsM m LeanSwe.LinuxSyscall.RawFd
  /-- Curated Linux descriptor-readiness syscall bundle (`ppoll`). -/
  poll : LeanSwe.LinuxSyscall.Poll.PollOpsM m LeanSwe.LinuxSyscall.RawFd
  /-- Curated Linux clock and sleep syscalls (`clock_gettime`, `clock_nanosleep`, `getrandom`). -/
  timeRand : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m
  /-- Verified post-`fork` child setup and `execve` capability bundle. -/
  postFork : LeanSwe.PostFork.PostForkOpsM m LeanSwe.LinuxSyscall.RawFd
  /-- Verified raw `environ(7)` capability bundle (`EnvVars.Raw.defaultOpsBase`). -/
  envRaw : LeanSwe.EnvVars.Raw.RawEnvVarsBundleM m

/-- Per-process slot tracked between `spawn`, `awaitOutput`, `killProcessGroup`, and `reap`. -/
structure ProcSlotM (fd : Type) where
  /-- Positive child OS PID (`1 ≤ pid ≤ 0x7fffffff`). -/
  pid : UInt32
  /-- Positive isolated child process group ID (`1 ≤ pgid ≤ 0x7fffffff`). -/
  pgid : UInt32
  /-- Parent write end of child `stdin` pipe, if still owned by the slot. -/
  stdinFd? : Option fd
  /-- Parent read end of child `stdout` pipe, if still owned by the slot. -/
  stdoutFd? : Option fd
  /-- Parent read end of child `stderr` pipe, if still owned by the slot. -/
  stderrFd? : Option fd
  /-- Whether `waitpid` has already reaped `pid`. -/
  waited : Bool := false
  deriving BEq, DecidableEq

/-- Pure in-memory table state tracking active unreaped `ProcSlotM` handles. -/
structure ProcTableState (fd : Type) where
  /-- Next monotonically increasing `handleId` (`≥ 1`). -/
  nextId : Nat := 1
  /-- Active handle slots keyed by `handleId`. -/
  slots : List (Nat × ProcSlotM fd) := []
  deriving BEq, DecidableEq, Inhabited

/-- Type family indexing `ProcTableState RawFd` for `Core.ObeysStepFromConcCell`. -/
abbrev ProcCellS (_ _ : Type → Type) : Type :=
  ProcTableState LeanSwe.LinuxSyscall.RawFd

/-- Capability interface over active process-slot table operations in monad `m`. -/
structure ProcTableOpsM (m : Type → Type) (fd : Type) where
  /-- Allocate a fresh `handleId` and insert `slot`. -/
  insertSlot : ProcSlotM fd → m Nat
  /-- Atomically take `(pid, stdinFd?, stdoutFd?, stderrFd?)` from `handleId`. -/
  takeSlotIo : Nat → m (Option (UInt32 × Option fd × Option fd × Option fd))
  /-- Record `waited` status on `handleId`, returning `false` if slot vanished. -/
  markWaited : Nat → Bool → m Bool
  /-- Look up `pgid` for `handleId` if active. -/
  lookupPgid : Nat → m (Option UInt32)
  /-- Atomically remove and return the slot for `handleId`. -/
  detachSlot : Nat → m (Option (ProcSlotM fd))
  /-- Return count of currently active unreaped handles. -/
  activeCount : m Nat

/-- Outcome of the pipe-streaming phase prior to `waitpid`. -/
inductive StreamPhaseOutcome where
  /-- Both `stdout` and `stderr` pipes reached EOF cleanly within limits. -/
  | eof (stdout stderr : ByteArray)
  /-- `timeoutMs` elapsed while streaming pipes. -/
  | timedOut (stdout stderr : ByteArray)
  /-- `maxOutputBytes` was exceeded while streaming pipes. -/
  | limitExceeded (stdout stderr : ByteArray)
  deriving BEq, DecidableEq

/-- Mutable loop state carried across `streamPipesLoop` iterations. -/
structure StreamLoopState (fd : Type) where
  /-- Open parent `stdin` write handle (`none` once closed). -/
  inFd? : Option fd
  /-- Open parent `stdout` read handle (`none` once closed). -/
  outFd? : Option fd
  /-- Open parent `stderr` read handle (`none` once closed). -/
  errFd? : Option fd
  /-- Current byte offset written into `stdin`. -/
  stdinPos : Nat := 0
  /-- Collected `stdout` chunks. -/
  outChunks : Array ByteArray := #[]
  /-- Total bytes in `outChunks`. -/
  outLen : Nat := 0
  /-- Collected `stderr` chunks. -/
  errChunks : Array ByteArray := #[]
  /-- Total bytes in `errChunks`. -/
  errLen : Nat := 0

/-- Public dependency bundle for `LeanSwe.Process` over imported OS capability interfaces. -/
structure ProcessHostCapsM (fd : Type) (m : Type → Type) where
  /-- Curated Linux process syscalls (`pipe2`, `waitpid`, `kill`, etc.). -/
  proc : LeanSwe.LinuxSyscall.Process.ProcessOpsM m fd
  /-- Curated Linux file and descriptor syscalls (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`, etc.). -/
  files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd
  /-- Curated Linux descriptor-readiness syscall bundle (`ppoll`). -/
  poll : LeanSwe.LinuxSyscall.Poll.PollOpsM m fd
  /-- Curated Linux clock and sleep syscalls (`clock_gettime`, `clock_nanosleep`, `getrandom`). -/
  timeRand : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m
  /-- Verified post-`fork` child setup and `execve` capability bundle. -/
  postFork : LeanSwe.PostFork.PostForkOpsM m fd
  /-- Snapshot raw NUL-free `environ(7)` byte entries when `inheritEnv = true`. -/
  listEnvironBytes : m (Array ByteArray)
  /-- Active child-process handle slot table operations. -/
  table : ProcTableOpsM m fd

/-- Concrete healthy-model `ProcessHostCapsM` specialized to `LinuxSyscall.Files.HandleId`. -/
abbrev HealthyHostCapsM (m : Type → Type) := ProcessHostCapsM LeanSwe.LinuxSyscall.Files.HandleId m

end LeanSwe.Process.Internal
