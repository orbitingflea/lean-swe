import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Impl

namespace LeanSwe.PostFork

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.Impl

@[extern "leanswe_postfork_host_probe_fd"]
private opaque rawProbeFdOpen : Int32 → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_probe_handle"]
private opaque rawProbeHandleOpen : @& RawFd → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_pipe_cloexec"]
private opaque rawMkPipeCloexec : BaseIO (Except Errno (RawFd × RawFd))

@[extern "leanswe_postfork_host_close_fd"]
private opaque rawCloseFd : @& RawFd → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_setpgid"]
private opaque rawSetpgid : Pid → Pid → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_write_once"]
private opaque rawWriteOnce : @& RawFd → @& ByteArray → UInt64 → UInt64 → BaseIO (Except Errno UInt64)

@[extern "leanswe_postfork_host_read_once"]
private opaque rawReadOnce : @& RawFd → UInt64 → BaseIO (Except Errno ByteArray)

@[extern "leanswe_postfork_host_wait_once"]
private opaque rawWaitOnce : Pid → BaseIO (Except Errno ChildWaitStatus)

@[extern "leanswe_postfork_host_fork_run"]
private opaque rawForkRun :
    UInt32 → UInt32 →
    @& Array RawFd → @& ByteArray → @& ByteArray → @& ByteArray →
    @& Array String → @& Array String → @& ByteArray →
    @& Option String → @& String → @& Array ByteArray →
    BaseIO (Except Errno Pid)

private def posixHostOps : LeanSwe.PostFork.Impl.Internal.PosixHostOpsM IO RawFd where
  probeFdOpen := fun fd => liftM (rawProbeFdOpen fd)
  probeHandleOpen := fun h => liftM (rawProbeHandleOpen h)
  mkPipeCloexec := liftM rawMkPipeCloexec
  closeFd := fun h => liftM (rawCloseFd h)
  setpgidOnce := fun pid pgid => liftM (rawSetpgid pid pgid)
  writeOnce := fun h buf off len => liftM (rawWriteOnce h buf off len)
  readOnce := fun h cap => liftM (rawReadOnce h cap)
  waitOnce := fun pid => liftM (rawWaitOnce pid)
  forkRun flags forkMode syncRead? errWrite stdioRefs closeRefs keepRefs cwd path argv envp :=
    let flat := LeanSwe.PostFork.Impl.Internal.flattenForkArgs syncRead? errWrite stdioRefs closeRefs keepRefs argv
    let imm := LeanSwe.PostFork.Impl.Internal.forkModeToUInt32 forkMode
    liftM (rawForkRun flags imm flat.handles flat.metaSlots flat.closeSlots flat.keepSlots
      flat.argPrefixes flat.argSuffixes flat.argSlots cwd path envp)

/-- Default `IO` capability bundle backed by `Internal.mkHostOps`, `postfork_shim.c`, and verified `#![no_std]` `libpostfork.a`. -/
def defaultOps : PostForkOps :=
  LeanSwe.PostFork.Impl.Internal.mkHostOps posixHostOps

/-- Validate `spec`, fork, run post-`fork` child setup, verify `execve` via EOF, and return the live `SpawnedChild`. -/
@[inline] def spawn (spec : ChildSpec) : IO (Except PostForkError SpawnedChild) :=
  defaultOps.spawn spec

/-- Validate `spec`, fork, pause child at the pre-`execve` sync barrier, and return `PendingChild`. -/
@[inline] def spawnWithBarrier (spec : ChildSpec) : IO (Except PostForkError PendingChild) :=
  defaultOps.spawnWithBarrier spec

/-- Release a `PendingChild` past its sync barrier and wait for `execve` completion (reaping automatically on failure). -/
@[inline] def releaseBarrier (p : PendingChild) : IO (Except PostForkError SpawnedChild) :=
  defaultOps.releaseBarrier p

/-- Abort a `PendingChild` at its sync barrier (`_exit(125)`), drain any pre-barrier failure report, and reap it. -/
@[inline] def abortBarrier (p : PendingChild) : IO (Except PostForkError AbortOutcome) :=
  defaultOps.abortBarrier p

end LeanSwe.PostFork
