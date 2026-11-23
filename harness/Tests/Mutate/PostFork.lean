import Tests.Common
import Tests.Mutate.PostForkMock
import LeanSwe.PostFork.Interface
import LeanSwe.PostFork.RuntimeTests
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Sandbox.Interface
import Fuzz.LinuxSyscall.ProcessEnv

namespace Tests.Mutate.PostFork

open LeanSwe
open Tests.Common

/-- Allocate a tracked `O_CLOEXEC` pipe pair `( >= 3 )` via `postfork_shim.c` (internal C-shim probe absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_pipe_cloexec"]
private opaque mutPfPipeCloexec :
    BaseIO (Except LinuxSyscall.Errno (LinuxSyscall.RawFd × LinuxSyscall.RawFd))

/-- Close and untrack a `postfork_shim.c` pipe `RawFd` handle (internal C-shim probe absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_close_fd"]
private opaque mutPfCloseFd :
    @& LinuxSyscall.RawFd → BaseIO (Except LinuxSyscall.Errno Unit)

/-- Exercise `leanswe_postfork_host_write_once` slice bounds and `SIGPIPE` masking directly (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_write_once"]
private opaque mutPfWriteOnce :
    @& LinuxSyscall.RawFd → @& ByteArray → UInt64 → UInt64 → BaseIO (Except LinuxSyscall.Errno UInt64)

/-- Exercise `leanswe_postfork_host_read_once` directly on a `postfork_shim.c` pipe handle (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_read_once"]
private opaque mutPfReadOnce :
    @& LinuxSyscall.RawFd → UInt64 → BaseIO (Except LinuxSyscall.Errno ByteArray)

/-- Probe raw integer descriptor openness while masking tracked internal `g_pf_pipes` handles (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_probe_fd"]
private opaque mutPfProbeFd :
    Int32 → BaseIO (Except LinuxSyscall.Errno Unit)

/-- Exercise `leanswe_postfork_host_setpgid` non-positive PID/PGID `EINVAL` guard directly (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_setpgid"]
private opaque mutPfSetpgid :
    LeanSwe.PostFork.Pid → LeanSwe.PostFork.Pid → BaseIO (Except LinuxSyscall.Errno Unit)

/-- Exercise `leanswe_postfork_host_wait_once` non-positive PID `EINVAL` guard directly (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_wait_once"]
private opaque mutPfWaitOnce :
    LeanSwe.PostFork.Pid → BaseIO (Except LinuxSyscall.Errno LeanSwe.PostFork.ChildWaitStatus)

/-- Exercise `leanswe_postfork_host_fork_run` malformed `meta_ba` and tracked-pipe `EBADF` ABI guards directly (absent from public `PostFork.Interface`). -/
@[extern "leanswe_postfork_host_fork_run"]
private opaque mutPfForkRun :
    UInt32 → UInt32 →
    @& Array LinuxSyscall.RawFd → @& ByteArray → @& ByteArray → @& ByteArray →
    @& Array String → @& Array String → @& ByteArray →
    @& Option String → @& String → @& Array ByteArray →
    BaseIO (Except LinuxSyscall.Errno LeanSwe.PostFork.Pid)

/-- Close a raw integer OS descriptor slot (`0..2` or `dup2` target) in the isolated `--postfork-probe` subprocess (`Files.close` accepts only boxed `RawFd`). -/
@[extern "close"]
private opaque mutPfRawCloseSlot : UInt32 → BaseIO UInt32

/-- Duplicate onto a specific raw integer OS descriptor slot (`dup2`) in the isolated `--postfork-probe` subprocess (`Files` exposes only `dupStdio`). -/
@[extern "dup2"]
private opaque mutPfRawDup2Slot : Int32 → Int32 → BaseIO Int32

@[noinline]
private def mutPfAllocPipeDropWrite : IO LinuxSyscall.RawFd := do
  match ← mutPfPipeCloexec with
  | .ok (r, _w) => pure r
  | .error e => throw (IO.userError s!"mutPfAllocPipeDropWrite failed: {e}")

private def mutPfReadProcThreads : IO Nat := do
  let txt ← IO.FS.readFile "/proc/self/status"
  for ln in txt.splitOn "\n" do
    if ln.startsWith "Threads:" then
      let numStr := (ln.drop 8).trimAscii.toString
      if let some n := numStr.toNat? then
        return n
  throw (IO.userError "Threads: missing in /proc/self/status")

private def reapSpawnedViaWaitpid (pid : LeanSwe.PostFork.Pid) :
    IO (Except LinuxSyscall.Errno LinuxSyscall.Process.WaitResult) := do
  for _ in List.range 64 do
    match ← LinuxSyscall.Process.waitpid pid.toInt32 with
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        return .error e
    | .ok st => return .ok st
  return .error LinuxSyscall.Errno.EINTR

private def runPostForkMutExtra : IO Unit := do
  let checkM (lbl : String) (ok : Bool) : IO Unit := do
    if !ok then
      throw (IO.userError s!"PostFork mut extra failed: {lbl}")
  let (rPipe, wPipe) ← match ← mutPfPipeCloexec with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"PostFork mut pipe2 failed errno={e}")
  try
    let rBounds ← mutPfWriteOnce wPipe (ByteArray.mk #[1]) 1 1
    checkM "write_once off==total len>0 EINVAL" (rBounds == .error LinuxSyscall.Errno.EINVAL)
    let _ ← mutPfCloseFd wPipe
    let rEbadf ← mutPfWriteOnce wPipe (ByteArray.mk #[1]) 0 1
    checkM "write_once closed RawFd EBADF" (rEbadf == .error LinuxSyscall.Errno.EBADF)
  finally
    let _ ← mutPfCloseFd rPipe
    let _ ← mutPfCloseFd wPipe

  Tests.Mutate.PostForkMock.runPostForkMockTests

  checkM "host setpgid(0, 1) EINVAL" ((← mutPfSetpgid 0 1) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host setpgid(1, 0) EINVAL" ((← mutPfSetpgid 1 0) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host waitOnce(0) EINVAL" ((← mutPfWaitOnce 0) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host forkRun bad meta_ba EINVAL"
    ((← mutPfForkRun 0 0 #[] ByteArray.empty ByteArray.empty ByteArray.empty #[] #[] ByteArray.empty none "/bin/true" #[]) ==
      .error LinuxSyscall.Errno.EINVAL)

  let finR ← mutPfAllocPipeDropWrite
  try
    checkM "host pipe finalizer closes dropped write end" ((← mutPfReadOnce finR 1) == .ok ByteArray.empty)
  finally
    let _ ← mutPfCloseFd finR

  let immSpec : LeanSwe.PostFork.ChildSpec :=
    { path := "/bin/true", argv := #[.lit "/bin/true"], forkMode := .immortalThread }
  match ← LeanSwe.PostFork.spawn immSpec with
  | .error e => throw (IO.userError s!"PostFork mut immortal warmup failed: {repr e}")
  | .ok c0 =>
    let _ ← reapSpawnedViaWaitpid c0.pid
  let thrBase ← mutPfReadProcThreads
  for _ in List.range 4 do
    match ← LeanSwe.PostFork.spawn immSpec with
    | .error e => throw (IO.userError s!"PostFork mut immortal loop failed: {repr e}")
    | .ok ci => let _ ← reapSpawnedViaWaitpid ci.pid
  let thrAfter ← mutPfReadProcThreads
  checkM s!"immortal spawner reuses single thread (base={thrBase} after={thrAfter})"
    (thrAfter ≤ thrBase + 1)

  match ← mutPfPipeCloexec with
  | .error e => throw (IO.userError s!"PostFork mut extra: host mkPipeCloexec failed: {repr e}")
  | .ok (pr, pw) =>
    try
      checkM "host writeOnce off=0 len=0" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 0 0) == .ok 0)
      checkM "host writeOnce off=size len=0" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 2 0) == .ok 0)
      checkM "host writeOnce oob off EINVAL" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 5 1) == .error LinuxSyscall.Errno.EINVAL)
      checkM "host writeOnce oob len EINVAL" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 1 5) == .error LinuxSyscall.Errno.EINVAL)
      checkM "host readOnce cap=0" ((← mutPfReadOnce pr 0) == .ok ByteArray.empty)
      checkM "host writeOnce 1B" ((← mutPfWriteOnce pw (ByteArray.mk #[99]) 0 1) == .ok 1)
      checkM "host readOnce 1B" ((← mutPfReadOnce pr 1) == .ok (ByteArray.mk #[99]))
      checkM "host probeFdOpen(-1) errors" (match ← mutPfProbeFd (-1) with | .error _ => true | .ok () => false)
    finally
      let _ ← mutPfCloseFd pr
      let _ ← mutPfCloseFd pw

  let selfBin := (← IO.appPath).toString
  match ← LeanSwe.PostFork.spawn {
    path := "/bin/sh"
    argv := #[.lit "/bin/sh", .lit "-c", .lit "ulimit -n 24 && exec \"$1\" --postfork-probe", .lit "sh", .lit selfBin]
  } with
  | .error e => throw (IO.userError s!"PostFork mut subproc probe spawn failed: {repr e}")
  | .ok prChild =>
    let prWst ← reapSpawnedViaWaitpid prChild.pid
    checkM s!"PostFork subproc EMFILE + SIGPIPE probe exited 0 (got {repr prWst})"
      (prWst == .ok (.exited prChild.pid 0))

/-- Subprocess entrypoint (`--postfork-probe`) testing `SIGPIPE` masking, tracked-pipe `EBADF`, untrack, and low-FD `EMFILE` relocation. -/
def runPostForkSubprocProbe : IO UInt32 := do
  if (← Fuzz.LinuxSyscall.ProcessEnv.setSigIgn 13 false) != .ok () then
    IO.eprintln "signal(SIGPIPE, SIG_DFL) failed"
    return 1
  match ← mutPfPipeCloexec with
  | .error _ =>
    return 1
  | .ok (sr, sw) =>
    let _ ← mutPfCloseFd sr
    let wrRes ← mutPfWriteOnce sw (ByteArray.mk #[1]) 0 1
    let _ ← mutPfCloseFd sw
    if wrRes != .error LinuxSyscall.Errno.EPIPE then
      return 1
  let mut openBefore : Array Int32 := #[]
  let mut closedHighBefore : Array Int32 := #[]
  for i in List.range 24 do
    let fd32 : Int32 := Int32.ofNat i
    match ← mutPfProbeFd fd32 with
    | .ok () => openBefore := openBefore.push fd32
    | .error _ =>
      if i ≥ 3 then
        closedHighBefore := closedHighBefore.push fd32
  if closedHighBefore.size < 2 then
    return 2
  match ← mutPfPipeCloexec with
  | .error _ => return 3
  | .ok (trR, trW) =>
    let trFd0 := closedHighBefore[0]!
    let trFd1 := closedHighBefore[1]!
    let pOpenOk ←
      if h : openBefore.size > 0 then
        pure ((← mutPfProbeFd openBefore[0]) == .ok ())
      else
        pure true
    let pTr0 ← mutPfProbeFd trFd0
    let pTr1 ← mutPfProbeFd trFd1
    let pushI32 := LeanSwe.PostFork.Impl.Internal.pushI32Le
    let metaBa := pushI32 (pushI32 (pushI32 (pushI32 (pushI32 ByteArray.empty (-1)) (-2)) trFd0) trFd0) trFd0
    let argSlots := pushI32 ByteArray.empty (-1)
    let fkRawTr ← mutPfForkRun 8 0 #[trW] metaBa ByteArray.empty ByteArray.empty
      #["/bin/true"] #[""] argSlots none "/bin/true" #[]
    let _ ← mutPfCloseFd trR
    let dupRc ← mutPfRawDup2Slot trFd1 trFd0
    let pAfterUntrack ← mutPfProbeFd trFd0
    if dupRc ≥ 0 then
      let _ ← mutPfRawCloseSlot trFd0.toUInt32
    let _ ← mutPfCloseFd trW
    if !pOpenOk || pTr0 != .error LinuxSyscall.Errno.EBADF || pTr1 != .error LinuxSyscall.Errno.EBADF ||
        fkRawTr != .error LinuxSyscall.Errno.EBADF || dupRc != trFd0 || pAfterUntrack != .ok () then
      return 4
  let mut allocated : Array (LinuxSyscall.RawFd × LinuxSyscall.RawFd) := #[]
  let mut sawEmfile := false
  try
    for _ in List.range 32 do
      if !sawEmfile then
        match ← mutPfPipeCloexec with
        | .ok p => allocated := allocated.push p
        | .error e =>
          if e == LinuxSyscall.Errno.EMFILE then
            sawEmfile := true
          else
            throw (IO.userError s!"unexpected pipe2 errno={e}")
  finally
    for (r, w) in allocated do
      let _ ← mutPfCloseFd r
      let _ ← mutPfCloseFd w
  if !sawEmfile then
    return 5
  let _ ← mutPfRawCloseSlot 0
  let _ ← mutPfRawCloseSlot 1
  let _ ← mutPfRawCloseSlot 2
  if (← LinuxSyscall.Sandbox.setrlimit .nofile 3 24) != .ok () then
    return 6
  match ← mutPfPipeCloexec with
  | .error e =>
    if e != LinuxSyscall.Errno.EMFILE then
      return 7
  | .ok (r, w) =>
    let _ ← mutPfCloseFd r
    let _ ← mutPfCloseFd w
    return 7
  if (← mutPfProbeFd 0) != .error LinuxSyscall.Errno.EBADF then
    return 8
  return 0

/-- Mutation test suite for `LeanSwe.PostFork`. -/
def postForkSuite : MutateSuite :=
  { «name» := "PostFork"
    runBase := do LeanSwe.PostFork.RuntimeTests.runAll; return none
    runExtra := runPostForkMutExtra }

end Tests.Mutate.PostFork
