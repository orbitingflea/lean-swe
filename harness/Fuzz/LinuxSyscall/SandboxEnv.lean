import LeanSwe.LinuxSyscall.Common.Types

namespace Fuzz.LinuxSyscall.SandboxEnv

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

/-- Peek the raw POSIX FD integer inside a `RawFd` without pinning (`0xFFFFFFFF` if closed). -/
@[extern "leanswe_sbx_peek_raw_fd"]
opaque peekRawFd : @& RawFd → IO UInt32

/-- Enter a fresh user namespace via `unshare(CLONE_NEWUSER)` inside a single-threaded forked child. -/
@[extern "leanswe_sbx_enter_userns"]
opaque enterUserns : IO (Except Errno Unit)

/-- Enable `PR_SET_NO_NEW_PRIVS` (`prctl(38, 1, 0, 0, 0)`). -/
@[extern "leanswe_sbx_set_no_new_privs"]
opaque setNoNewPrivs : IO (Except Errno Unit)

/-- Query `PR_GET_NO_NEW_PRIVS` (`prctl(39, 0, 0, 0, 0)`). -/
@[extern "leanswe_sbx_get_no_new_privs"]
opaque getNoNewPrivs : IO (Except Errno UInt32)

/-- Install a raw cBPF seccomp filter via `SYS_seccomp(SECCOMP_SET_MODE_FILTER, flags, ...)`, returning `0` on success or conflicting TID on `TSYNC` mismatch. -/
@[extern "leanswe_sbx_install_raw_seccomp"]
opaque installSeccompFilter : UInt32 → @& ByteArray → IO (Except Errno UInt32)

/-- Install an arbitrary raw cBPF seccomp filter directly via `SYS_seccomp` (`flags = 0`). -/
def installRawSeccomp (filterBytes : ByteArray) : IO (Except Errno Unit) := do
  match ← installSeccompFilter 0 filterBytes with
  | .ok _ => return .ok ()
  | .error e => return .error e

/-- Enter a mapped user+mount namespace and prepare `overlayfs`, `devpts`, and bind-mount directories under `baseDir` (returns `0` on full success or mount errno after entering userns). -/
@[extern "leanswe_sbx_setup_mnt_ns"]
opaque setupMntNs : @& ByteArray → IO (Except Errno UInt32)

/-- Spawn the helper pthread inside a forked child (`installFilter != 0` installs an independent `SECCOMP_RET_ALLOW` filter) and return its Linux TID pipe FD. -/
@[extern "leanswe_sbx_spawn_sync_thread"]
opaque spawnSyncThreadRaw : UInt32 → IO (Except Errno UInt32)

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

private partial def readUpToRaw (fd : UInt32) (target : Nat) : IO (Except Errno ByteArray) := do
  let rec go (acc : ByteArray) : IO (Except Errno ByteArray) := do
    if acc.size >= target then
      return .ok acc
    match ← readBytesRaw fd (UInt32.ofNat (target - acc.size)) with
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

/-- Stop and join the helper pthread inside a forked child. -/
@[extern "leanswe_sbx_stop_sync_thread"]
opaque stopSyncThread : IO (Except Errno Unit)

/-- Spawn the helper pthread inside a forked child (`installFilter = true` diverges its seccomp filter from the main thread; `false` leaves it clean for `TSYNC`). -/
def spawnSyncThread (installFilter : Bool := true) : IO (Except Errno UInt32) := do
  match ← spawnSyncThreadRaw (if installFilter then 1 else 0) with
  | .error e => return .error e
  | .ok rfd =>
    let dataRes ← readUpToRaw rfd 4
    closeRaw rfd
    match dataRes with
    | .ok bytes =>
      if bytes.size == 4 then
        let b0 := (bytes.get! 0).toUInt32
        let b1 := (bytes.get! 1).toUInt32 <<< 8
        let b2 := (bytes.get! 2).toUInt32 <<< 16
        let b3 := (bytes.get! 3).toUInt32 <<< 24
        return .ok (b0 ||| b1 ||| b2 ||| b3)
      else
        let _ ← stopSyncThread
        return .error Errno.EIO
    | .error e =>
      let _ ← stopSyncThread
      return .error e

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
      let wr ← writeAllRaw wfd out
      closeRaw wfd
      match wr with
      | .ok () => exitChild 0
      | .error _ => exitChild 1
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
        let errTxt := (String.fromUTF8? (data.extract 1 data.size)).getD "invalid UTF-8 error message from forked child"
        throw (IO.userError s!"forked child error: {errTxt}")
      let payload := if data.isEmpty then ByteArray.empty else data.extract 1 data.size
      return (st, payload)

private def pushU16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  (b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8

private def pushU32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8).push
    ((v >>> 16) &&& 0xff).toUInt8).push ((v >>> 24) &&& 0xff).toUInt8

private def pushBpfInsn (b : ByteArray) (code : UInt16) (jt jf : UInt8) (k : UInt32) : ByteArray :=
  pushU32LE (((pushU16LE b code).push jt).push jf) k

/-- Encode a portable `x86_64`+`aarch64` cBPF filter returning `SECCOMP_RET_ERRNO | err` for the listed syscall numbers (`3 + x86Nrs.size + armNrs.size ≤ 255`). -/
def encodeSeccompErrnoBpf (x86Nrs armNrs : Array UInt32) (err : Errno) : ByteArray := Id.run do
  let nX := x86Nrs.size
  let nA := armNrs.size
  let mut b := ByteArray.empty
  b := pushBpfInsn b 0x0020 0 0 4
  b := pushBpfInsn b 0x0015 1 0 0xc000003e
  b := pushBpfInsn b 0x0015 (UInt8.ofNat (2 + nX)) (UInt8.ofNat (3 + nX + nA)) 0xc00000b7
  b := pushBpfInsn b 0x0020 0 0 0
  for i in [:nX] do
    b := pushBpfInsn b 0x0015 (UInt8.ofNat (2 + nX + nA - i)) 0 x86Nrs[i]!
  b := pushBpfInsn b 0x0006 0 0 0x7fff0000
  b := pushBpfInsn b 0x0020 0 0 0
  for j in [:nA] do
    b := pushBpfInsn b 0x0015 (UInt8.ofNat (nA - j)) 0 armNrs[j]!
  b := pushBpfInsn b 0x0006 0 0 0x7fff0000
  b := pushBpfInsn b 0x0006 0 0 (0x00050000 ||| (err &&& 0xffff))
  return b

/-- Encode a portable (`x86_64`/`aarch64`) `SECCOMP_RET_ERRNO` cBPF filter returning `eno` for the masked `TimeRand` syscalls (`syscallMask` bits: `bit 0 = clock_gettime`, `bit 1 = clock_nanosleep`, `bit 2 = getrandom`). -/
def encodeTimeRandSeccompErrnoBpf (eno : Errno) (syscallMask : UInt32 := 7) : ByteArray := Id.run do
  let mut x86Nrs : Array UInt32 := #[]
  let mut armNrs : Array UInt32 := #[]
  if (syscallMask &&& 1) != 0 then
    x86Nrs := x86Nrs.push 228
    armNrs := armNrs.push 113
  if (syscallMask &&& 2) != 0 then
    x86Nrs := x86Nrs.push 230
    armNrs := armNrs.push 115
  if (syscallMask &&& 4) != 0 then
    x86Nrs := x86Nrs.push 318
    armNrs := armNrs.push 278
  encodeSeccompErrnoBpf x86Nrs armNrs eno

/-- Install a portable (`x86_64`/`aarch64`) `TSYNC` `SECCOMP_RET_ERRNO` filter returning `eno` (`1..4095`, rejecting `EFAULT`) on the masked `TimeRand` syscalls (`syscallMask` in `1..7`: `bit 0 = clock_gettime`, `bit 1 = clock_nanosleep`, `bit 2 = getrandom`). Returns `0` on success, `EINVAL` on invalid inputs, `EAGAIN` if `TSYNC` returns a conflicting thread ID, or the kernel errno on syscall failure. -/
def installTimeRandSeccompErrno (eno : Errno) (syscallMask : UInt32 := 7) : IO UInt32 := do
  if eno == 0 || eno > 4095 || eno == Errno.EFAULT || syscallMask == 0 || syscallMask > 7 then
    return Errno.EINVAL
  match ← setNoNewPrivs with
  | .error e => return e
  | .ok () =>
    let bpf := encodeTimeRandSeccompErrnoBpf eno syscallMask
    match ← installSeccompFilter 1 bpf with
    | .ok rc => return if rc == 0 then 0 else Errno.EAGAIN
    | .error e => return e

/-- Parse serialized `HitStats` lines (`"bucket=count\n"`) emitted by a forked child worker. -/
def decodeHitCounts (bytes : ByteArray) : List (String × Nat) :=
  let txt := String.fromUTF8! bytes
  (txt.splitOn "\n").filterMap fun line =>
    if line.isEmpty then none
    else
      match line.splitOn "=" with
      | [k, vStr] => vStr.toNat?.map (fun n => (k, n))
      | _ => none

end Fuzz.LinuxSyscall.SandboxEnv
