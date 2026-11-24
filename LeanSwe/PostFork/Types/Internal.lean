import LeanSwe.PostFork.Types

/-!
# PostFork Internal Host-Hook and Marshaling Data Shapes

Pure data shapes (`PosixHostOpsM`, `FlattenedForkArgsM`, `FlattenedForkArgs`) shared
between `LeanSwe.PostFork.Impl`, `LeanSwe.PostFork.Interface`, and
`LeanSwe.PostFork.SpecTests` without exposing `Impl` to `SpecTests` or leaking
internal constants across package boundaries.
-/

namespace LeanSwe.PostFork.Impl.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Low-level 1-syscall host operations consumed by `LeanSwe.PostFork.Impl.Internal.mkHostOps`. -/
structure PosixHostOpsM (m : Type → Type) (fd : Type) where
  /-- Probe whether raw OS descriptor `fd` is open (`F_GETFD`). -/
  probeFdOpen : Int32 → m (Except Errno Unit)
  /-- Probe whether managed handle `h` is open (`F_GETFD`). -/
  probeHandleOpen : fd → m (Except Errno Unit)
  /-- Allocate a `pipe2(..., O_CLOEXEC)` pair `(readEnd, writeEnd)`. -/
  mkPipeCloexec : m (Except Errno (fd × fd))
  /-- Close a managed handle `h`. -/
  closeFd : fd → m (Except Errno Unit)
  /-- Invoke `setpgid(pid, pgid)` once. -/
  setpgidOnce : Pid → Pid → m (Except Errno Unit)
  /-- Invoke `write(fd, data[off..off+len))` once. -/
  writeOnce : fd → ByteArray → UInt64 → UInt64 → m (Except Errno UInt64)
  /-- Invoke `read(fd, maxBytes)` once. -/
  readOnce : fd → UInt64 → m (Except Errno ByteArray)
  /-- Invoke `waitpid(pid, &st, 0)` once. -/
  waitOnce : Pid → m (Except Errno ChildWaitStatus)
  /-- Fork a child (directly or via immortal spawner thread) and invoke `leanswe_postfork_run_child`. -/
  forkRun :
    UInt32 → ForkMode → Option fd → fd →
    Array (FdRef fd) → Array (FdRef fd) → Array (FdRef fd) →
    Option String → String → Array (ArgToken fd) → Array ByteArray →
    m (Except Errno Pid)

/-- Flattened representation of `forkRun` descriptor handles and slots for C FFI marshaling, parameterized over handle type `fd`. -/
structure FlattenedForkArgsM (fd : Type) where
  /-- Managed handles pinned across `fork()`. -/
  handles : Array fd
  /-- Packed 5-slot `Int32` header `[sync_r, rep_w, stdin, stdout, stderr]`. -/
  metaSlots : ByteArray
  /-- Packed `Int32` slots for `closeFds`. -/
  closeSlots : ByteArray
  /-- Packed `Int32` slots for `keepFds`. -/
  keepSlots : ByteArray
  /-- Prefix strings for each `argv` token. -/
  argPrefixes : Array String
  /-- Suffix strings for each `argv` token. -/
  argSuffixes : Array String
  /-- Packed `Int32` descriptor slots (`-1` for `.lit`, `>= 0` for `.raw`, `-(idx+2)` for `.handle`). -/
  argSlots : ByteArray

/-- Real-world `RawFd` specialization of `FlattenedForkArgsM`. -/
abbrev FlattenedForkArgs := FlattenedForkArgsM RawFd

end LeanSwe.PostFork.Impl.Internal
