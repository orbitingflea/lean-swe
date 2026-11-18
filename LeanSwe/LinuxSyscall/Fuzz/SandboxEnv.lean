import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Fuzz.SandboxEnv

open LeanSwe.LinuxSyscall

/-- Create an `O_CLOEXEC` POSIX pipe returning packed `(readFd, writeFd)` bits. -/
@[extern "leanswe_sbx_pipe"]
opaque pipePacked : IO (Except Errno UInt64)

/-- Flush stdio and fork a child process (`0` in child, child PID in parent). -/
@[extern "leanswe_sbx_fork"]
opaque forkRaw : IO (Except Errno UInt32)

/-- Wait once on `pid` returning raw Linux `waitpid(2)` status word. -/
@[extern "leanswe_sbx_waitpid"]
opaque waitpidRaw : UInt32 → IO (Except Errno UInt32)

/-- Terminate the current forked child immediately via `_exit(2)`. -/
@[extern "leanswe_sbx_exit"]
opaque exitChild : UInt32 → IO Unit

/-- Write bytes to a raw POSIX FD once. -/
@[extern "leanswe_sbx_write_bytes"]
opaque writeBytesRaw : UInt32 → @& ByteArray → IO (Except Errno UInt32)

/-- Read up to `maxBytes` from a raw POSIX FD once. -/
@[extern "leanswe_sbx_read_bytes"]
opaque readBytesRaw : UInt32 → UInt32 → IO (Except Errno ByteArray)

/-- Close a raw POSIX FD. -/
@[extern "leanswe_sbx_close_raw"]
opaque closeRaw : UInt32 → IO Unit

/-- Open a host path into a `RawFd` using selector `0..6` (`O_RDONLY|O_DIRECTORY`, `O_PATH|O_DIRECTORY`, `O_RDONLY`, `O_PATH`, `O_RDWR|O_CREAT`, `O_PATH|O_NOFOLLOW`, `O_RDONLY|O_NONBLOCK`). -/
@[extern "leanswe_sbx_open_host_fd"]
opaque openHostFd : @& ByteArray → UInt32 → IO (Except Errno RawFd)

/-- Open a pseudo-filesystem pipe `RawFd` (`asOPath != 0` opens `/proc/self/fd/<pipe>` with `O_PATH`). -/
@[extern "leanswe_sbx_open_pipe_fd"]
opaque openPipeFd : UInt32 → IO (Except Errno RawFd)

/-- Re-open an existing `RawFd` via `/proc/self/fd/<fd>` with `O_PATH | O_CLOEXEC`. -/
@[extern "leanswe_sbx_reopen_opath"]
opaque reopenOPath : @& RawFd → IO (Except Errno RawFd)

/-- Open a specialized kernel descriptor (`0`: `eventfd`, `1`: `AF_UNIX` socket, `2`: `nsfs`, `3`: unlinked file, `4`: unlinked dir, `5`: FIFO `O_PATH`, `6`: dangling symlink `O_PATH|O_NOFOLLOW`, `7`: bound `AF_UNIX` socket `O_PATH`). -/
@[extern "leanswe_sbx_open_special_fd"]
opaque openSpecialFd : UInt32 → @& ByteArray → IO (Except Errno RawFd)

/-- Close a boxed `RawFd` cleanly. -/
@[extern "leanswe_sbx_close_fd"]
opaque closeFd : @& RawFd → IO (Except Errno Unit)

/-- Enter a fresh user namespace via `unshare(CLONE_NEWUSER)` inside a single-threaded forked child. -/
@[extern "leanswe_sbx_enter_userns"]
opaque enterUserns : IO (Except Errno Unit)

/-- Enter extra Linux namespaces (`bit 0`: `CLONE_NEWPID`, `1`: `CLONE_NEWNET`, `2`: `CLONE_NEWUTS`, `3`: `CLONE_NEWIPC`). -/
@[extern "leanswe_sbx_unshare_extra"]
opaque unshareExtra : UInt32 → IO (Except Errno Unit)

/-- Install an arbitrary raw cBPF seccomp filter directly via `SYS_seccomp` (bypasses Lean wrapper guards for testing outer-filter boundaries). -/
@[extern "leanswe_sbx_install_raw_seccomp"]
opaque installRawSeccomp : @& ByteArray → IO (Except Errno Unit)

/-- Ensure directory/file permissions are `0700` so temporary directories created inside userns can be removed cleanly. -/
@[extern "leanswe_sbx_chmod_rw"]
opaque chmodRw : @& ByteArray → IO (Except Errno Unit)

/-- Enter a mapped user+mount namespace and prepare `overlayfs`, `devpts`, and bind-mount directories under `baseDir`. -/
@[extern "leanswe_sbx_setup_mnt_ns"]
opaque setupMntNs : @& ByteArray → IO (Except Errno Unit)

/-- Read current `(rlim_cur, rlim_max)` for resource selector `0..2`. -/
@[extern "leanswe_sbx_get_rlimit"]
opaque getRlimit : UInt32 → IO (Except Errno (UInt64 × UInt64))

/-- Read current Linux thread ID via `SYS_gettid`. -/
@[extern "leanswe_sbx_get_tid"]
opaque getTid : IO UInt32

/-- Read effective user ID via `geteuid(2)`. -/
@[extern "leanswe_sbx_geteuid"]
opaque getEuid : IO UInt32

/-- Spawn the helper pthread inside a forked child (`installFilter != 0` installs an independent `SECCOMP_RET_ALLOW` filter) and return its Linux TID. -/
@[extern "leanswe_sbx_spawn_sync_thread"]
opaque spawnSyncThreadRaw : UInt32 → IO (Except Errno UInt32)

/-- Spawn the helper pthread inside a forked child (`installFilter = true` diverges its seccomp filter from the main thread; `false` leaves it clean for `TSYNC`). -/
def spawnSyncThread (installFilter : Bool := true) : IO (Except Errno UInt32) :=
  spawnSyncThreadRaw (if installFilter then 1 else 0)

/-- Stop and join the helper pthread inside a forked child. -/
@[extern "leanswe_sbx_stop_sync_thread"]
opaque stopSyncThread : IO (Except Errno Unit)

/-- Unpack `(readFd, writeFd)` from `pipePacked`. -/
def createPipe : IO (Except Errno (UInt32 × UInt32)) := do
  match ← pipePacked with
  | .error e => return .error e
  | .ok packed =>
    let rfd := (packed &&& 0xFFFFFFFF).toUInt32
    let wfd := ((packed >>> 32) &&& 0xFFFFFFFF).toUInt32
    return .ok (rfd, wfd)

/-- Write the full contents of `bytes` to raw FD `fd`, retrying on `EINTR`. -/
partial def writeAllRaw (fd : UInt32) (bytes : ByteArray) : IO (Except Errno Unit) := do
  let rec go (off : Nat) : IO (Except Errno Unit) := do
    if off >= bytes.size then
      return .ok ()
    let slice := bytes.extract off bytes.size
    match ← writeBytesRaw fd slice with
    | .ok n =>
      if n.toNat == 0 then
        return .error Errno.EIO
      go (off + n.toNat)
    | .error e =>
      if e == Errno.EINTR then
        go off
      else
        return .error e
  go 0

/-- Read from raw FD `fd` until EOF, retrying on `EINTR`. -/
partial def readAllRaw (fd : UInt32) : IO (Except Errno ByteArray) := do
  let rec go (acc : ByteArray) : IO (Except Errno ByteArray) := do
    match ← readBytesRaw fd 65536 with
    | .ok chunk =>
      if chunk.isEmpty then
        return .ok acc
      go (acc ++ chunk)
    | .error e =>
      if e == Errno.EINTR then
        go acc
      else
        return .error e
  go ByteArray.empty

/-- Wait for `pid`, retrying on `EINTR`. -/
partial def waitpidRetry (pid : UInt32) : IO (Except Errno UInt32) := do
  match ← waitpidRaw pid with
  | .ok st => return .ok st
  | .error e =>
    if e == Errno.EINTR then
      waitpidRetry pid
    else
      return .error e

/-- Execute `childAction` inside a fresh forked child, returning `(waitStatus, stdoutPipeBytes)`. -/
def runForked (childAction : IO ByteArray) : IO (UInt32 × ByteArray) := do
  let (rfd, wfd) ← match ← createPipe with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"pipe failed: {e}")
  match ← forkRaw with
  | .error e =>
    closeRaw rfd
    closeRaw wfd
    throw (IO.userError s!"fork failed: {e}")
  | .ok pid =>
    if pid == 0 then
      closeRaw rfd
      let out ← try
          let payload ← childAction
          pure (ByteArray.mk #[0] ++ payload)
        catch err =>
          let msg := err.toString.toUTF8
          pure (ByteArray.mk #[1] ++ msg)
      let _ ← writeAllRaw wfd out
      closeRaw wfd
      exitChild 0
      return (0, ByteArray.empty)
    else
      closeRaw wfd
      let dataRes ← readAllRaw rfd
      closeRaw rfd
      let stRes ← waitpidRetry pid
      let st ← match stRes with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"waitpid failed: {e}")
      let data ← match dataRes with
        | .ok b => pure b
        | .error e => throw (IO.userError s!"pipe read failed: {e}")
      if !data.isEmpty && data.get! 0 == 1 then
        let errTxt := String.fromUTF8! (data.extract 1 data.size)
        throw (IO.userError s!"forked child error: {errTxt}")
      let payload := if data.isEmpty then ByteArray.empty else data.extract 1 data.size
      return (st, payload)

end LeanSwe.LinuxSyscall.Fuzz.SandboxEnv
