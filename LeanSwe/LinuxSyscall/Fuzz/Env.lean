import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Fuzz.Env

/-- Create a named FIFO node on disk, returning `0` on success or host `errno`. -/
@[extern "leanswe_fuzz_mkfifo"]
opaque mkfifo (path : @& ByteArray) (mode : UInt32) : IO UInt32

/-- Create a bound closed `AF_UNIX` socket node on disk, returning `0` on success or host `errno`. -/
@[extern "leanswe_fuzz_mksock"]
opaque mksock (path : @& ByteArray) : IO UInt32

/-- Create a hard link on disk, returning `0` on success or host `errno`. -/
@[extern "leanswe_fuzz_link"]
opaque link (oldPath : @& ByteArray) (newPath : @& ByteArray) : IO UInt32

/-- Set process `umask`, returning the previous mask. -/
@[extern "leanswe_fuzz_umask"]
opaque umask (mask : UInt32) : IO UInt32

/-- Set file mode bits via `chmod`, returning `0` on success or host `errno`. -/
@[extern "leanswe_fuzz_chmod"]
opaque chmod (path : @& ByteArray) (mode : UInt32) : IO UInt32

/-- Query `st_dev` via `lstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_stat_dev"]
opaque statDev (path : @& ByteArray) : IO UInt64

/-- Query `st_ino` via `lstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_stat_ino"]
opaque statIno (path : @& ByteArray) : IO UInt64

/-- Query `st_mode & 0o7777` via `lstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_stat_mode"]
opaque statMode (path : @& ByteArray) : IO UInt32

/-- Ignore `SIGPIPE` so broken-FIFO writes return `EPIPE` rather than terminating. -/
@[extern "leanswe_fuzz_ignore_sigpipe"]
opaque ignoreSigpipe : IO Unit

/-- Query kernel file kind code for an already-open OS descriptor (`0..2`). -/
@[extern "leanswe_fuzz_fd_kind"]
opaque fdKind (fd : UInt32) : IO UInt32

/-- Pin any closed stdio descriptor (`0..2`) to `/dev/null` so later opens cannot claim `0..2`. -/
@[extern "leanswe_fuzz_pin_closed_stdio"]
opaque pinClosedStdio : IO Unit

/-- Return `true` iff `statfs` reports `TMPFS_MAGIC` (`F_GET_SEALS` supported). -/
@[extern "leanswe_fuzz_supports_seals"]
opaque supportsSeals (path : @& ByteArray) : IO Bool

/-- Query current `RLIMIT_FSIZE` soft limit. -/
@[extern "leanswe_fuzz_get_rlimit_fsize_cur"]
opaque getRlimitFsizeCur : IO UInt64

/-- Query current `RLIMIT_FSIZE` hard limit. -/
@[extern "leanswe_fuzz_get_rlimit_fsize_max"]
opaque getRlimitFsizeMax : IO UInt64

/-- Configure `RLIMIT_FSIZE` and `SIGXFSZ` (`SIG_IGN` when `ignoreSig` is `true`). -/
@[extern "leanswe_fuzz_set_rlimit_fsize"]
opaque setRlimitFsize (cur : UInt64) (maxLim : UInt64) (ignoreSig : Bool) : IO UInt32

/-- Query current `RLIMIT_NOFILE` soft limit. -/
@[extern "leanswe_fuzz_get_rlimit_nofile_cur"]
opaque getRlimitNofileCur : IO UInt64

/-- Query current `RLIMIT_NOFILE` hard limit. -/
@[extern "leanswe_fuzz_get_rlimit_nofile_max"]
opaque getRlimitNofileMax : IO UInt64

/-- Configure `RLIMIT_NOFILE` soft and hard limits (`maxLim == 0` preserves current hard limit), returning `0` on success or host `errno`. -/
@[extern "leanswe_fuzz_set_rlimit_nofile"]
opaque setRlimitNofile (cur : UInt64) (maxLim : UInt64) : IO UInt32

/-- Query current process PID via `getpid`. -/
@[extern "leanswe_fuzz_get_pid"]
opaque getPid : IO UInt32

/-- Query current effective UID via `geteuid`. -/
@[extern "leanswe_fuzz_get_uid"]
opaque getUid : IO UInt32

/-- Query packed `(st_uid, st_gid)` via `lstat`, returning `0xffffffffffffffff` on failure. -/
@[extern "leanswe_fuzz_stat_uid_gid"]
opaque statUidGid (path : @& ByteArray) : IO UInt64

/-- Query packed `(st_uid, st_gid)` via `stat` (following symlinks), returning `0xffffffffffffffff` on failure. -/
@[extern "leanswe_fuzz_stat_follow_uid_gid"]
opaque statFollowUidGid (path : @& ByteArray) : IO UInt64

/-- Query `st_uid` via `lstat`, returning `0xffffffff` on failure. -/
def statUid (path : @& ByteArray) : IO UInt32 := do
  return (← statUidGid path).toUInt32

/-- Query `st_gid` via `lstat`, returning `0xffffffff` on failure. -/
def statGid (path : @& ByteArray) : IO UInt32 := do
  return ((← statUidGid path) >>> 32).toUInt32

/-- Query `statfs.f_type` filesystem magic number, returning `0` on failure. -/
@[extern "leanswe_fuzz_statfs_type"]
opaque statfsFsType (path : @& ByteArray) : IO UInt64

/-- Return `true` iff `statfs.f_flags` reports `ST_RDONLY` (`0x1`). -/
@[extern "leanswe_fuzz_statfs_ro"]
opaque statfsIsReadOnly (path : @& ByteArray) : IO Bool

/-- Query `stx_mnt_id` via `statx(STATX_MNT_ID)`, returning `0` on failure. -/
@[extern "leanswe_fuzz_stat_mnt_id"]
opaque statMntId (path : @& ByteArray) : IO UInt64

/-- Query `st_mode` on an open file descriptor via `fstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_fd_mode"]
opaque fdMode (fd : UInt32) : IO UInt32

/-- Query packed `(st_uid, st_gid)` on an open file descriptor via `fstat`, returning `0xffffffffffffffff` on failure. -/
@[extern "leanswe_fuzz_fd_uid_gid"]
opaque fdUidGid (fd : UInt32) : IO UInt64

/-- Query `st_uid` on an open file descriptor via `fstat`, returning `0xffffffff` on failure. -/
def fdUid (fd : UInt32) : IO UInt32 := do
  return (← fdUidGid fd).toUInt32

/-- Query `st_gid` on an open file descriptor via `fstat`, returning `0xffffffff` on failure. -/
def fdGid (fd : UInt32) : IO UInt32 := do
  return ((← fdUidGid fd) >>> 32).toUInt32

/-- Query `st_dev` on an open file descriptor via `fstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_fd_dev"]
opaque fdDev (fd : UInt32) : IO UInt64

/-- Query `st_ino` on an open file descriptor via `fstat`, returning `0` on failure. -/
@[extern "leanswe_fuzz_fd_ino"]
opaque fdIno (fd : UInt32) : IO UInt64

/-- Call `chroot(path)`, returning `0` on success or `errno` on failure. -/
@[extern "leanswe_fuzz_chroot"]
opaque chroot (path : @& ByteArray) : IO UInt32

/-- Call `rmdir(path)`, returning `0` on success or `errno` on failure. -/
@[extern "leanswe_fuzz_rmdir"]
opaque rmdir (path : @& ByteArray) : IO UInt32

/-- Install a cBPF seccomp filter returning `SECCOMP_RET_ERRNO` for three syscall numbers. -/
@[extern "leanswe_files_fuzz_install_seccomp_errno"]
opaque installSeccompErrno (nr1 err1 nr2 err2 nr3 err3 : UInt32) : IO UInt32

/-- Create an anonymous sealable `memfd` (`MFD_CLOEXEC | MFD_ALLOW_SEALING`). -/
@[extern "leanswe_fuzz_open_memfd"]
opaque openMemfd : IO (Except LeanSwe.LinuxSyscall.Errno LeanSwe.LinuxSyscall.RawFd)

/-- Fork a child process, returning `0` to the child, child PID to the parent, or `0xffffffff` on error. -/
@[extern "leanswe_fuzz_fork_pid"]
opaque forkPid : IO UInt32

@[extern "leanswe_fuzz_wait_pid_once"]
private opaque waitPidOnce (pid : UInt32) : IO UInt32

/-- Wait on `pid` (retrying `EINTR`), returning `1000+sig` or `2000+exit`. -/
def waitPid (pid : UInt32) : IO UInt32 := do
  for _ in [:1000000] do
    let st ← waitPidOnce pid
    if st != 9996 then return st
  return 9998

/-- Fork a child process: child receives `0`; parent waits (retrying `EINTR`) and gets `1000+sig` or `2000+exit`. -/
def forkForStatus : IO UInt32 := do
  let pid ← forkPid
  if pid == 0 then return 0
  else if pid == 0xffffffff then return 9999
  else waitPid pid

/-- Terminate the current process immediately with `_exit(code)`. -/
@[extern "leanswe_fuzz_exit_immediate"]
opaque exitImmediate (code : UInt32) : IO Unit

/-- Return the host `__NR_getcwd` syscall number. -/
@[extern "leanswe_fuzz_nr_getcwd"]
opaque nrGetcwd : IO UInt32

/-- Return the host `__NR_fsync` syscall number. -/
@[extern "leanswe_fuzz_nr_fsync"]
opaque nrFsync : IO UInt32

/-- Return the host `SYS_faccessat2` syscall number (`439`). -/
@[extern "leanswe_fuzz_nr_faccessat2"]
opaque nrFaccessat2 : IO UInt32

/-- Return the host `__NR_close` syscall number. -/
@[extern "leanswe_fuzz_nr_close"]
opaque nrClose : IO UInt32

/-- Change current working directory to open directory descriptor `fd`, returning `0` or `errno`. -/
@[extern "leanswe_fuzz_fchdir"]
opaque fchdir (fd : @& LeanSwe.LinuxSyscall.RawFd) : IO UInt32

/-- Return the Linux syscall number for `Files` slot `0..19` (or `0xffffffff` if out of range). -/
@[extern "leanswe_fuzz_nr_for_slot"]
opaque nrForSlot (slot : UInt32) : IO UInt32

@[extern "leanswe_fuzz_write_fd_chunk"]
private opaque writeFdChunk (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO (Except UInt32 USize)

/-- Write all `bytes` directly to raw FD `fd` via `SYS_writev` (retrying partial writes and `EINTR`). -/
def writeFdSafe (fd : UInt32) (bytes : ByteArray) : IO UInt32 := do
  if bytes.isEmpty then return 0
  let mut off : Nat := 0
  for _ in [:bytes.size + 1024] do
    if off >= bytes.size then return 0
    match ← writeFdChunk fd bytes (USize.ofNat off) with
    | .ok n =>
      if n.toNat == 0 then return 5
      off := off + n.toNat
    | .error e =>
      if e != 4 then return e
  return (if off >= bytes.size then 0 else 5)

/-- Return the underlying OS FD number held in `rfd`, or `0xffffffff` if closed. -/
@[extern "leanswe_fuzz_raw_fd_num"]
opaque rawFdNum (rfd : @& LeanSwe.LinuxSyscall.RawFd) : IO UInt32

/-- Create an `O_CLOEXEC` pipe pair packed as `(readFd : UInt32) ||| ((writeFd : UInt32) <<< 32)`, or `0xffffffffffffffff`. -/
@[extern "leanswe_fuzz_pipe"]
opaque pipe : IO UInt64

/-- Close a raw OS descriptor by integer FD number, returning `0` or `errno`. -/
@[extern "leanswe_fuzz_close_raw_fd"]
opaque closeRawFd (fd : UInt32) : IO UInt32

/-- Read one chunk (up to 64 KiB) from a raw OS descriptor, returning `ok #[]` on EOF or `error errno`. -/
@[extern "leanswe_fuzz_read_fd_chunk"]
opaque readFdChunk (fd : UInt32) : IO (Except UInt32 ByteArray)

/-- Read all bytes from a raw OS descriptor until EOF. -/
def readFdAll (fd : UInt32) : IO ByteArray := do
  let mut out := ByteArray.empty
  for _ in [:4096] do
    match ← readFdChunk fd with
    | .ok chunk =>
      if chunk.isEmpty then break
      out := out ++ chunk
    | .error e =>
      if e == 4 then continue
      break
  return out

/-- Read effective capability bitmask (`CapEff`) from `/proc/self/status`, returning `0` on read failure. -/
def readCapEff : IO UInt64 := do
  try
    let txt ← IO.FS.readFile "/proc/self/status"
    for line in txt.splitOn "\n" do
      if line.startsWith "CapEff:" then
        let hex := (line.drop 7).trimAscii.toString
        let mut acc : UInt64 := 0
        for c in hex.toList do
          let d? : Option Nat :=
            if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
            else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
            else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
            else none
          if let some d := d? then
            acc := (acc <<< 4) ||| UInt64.ofNat d
        return acc
    return 0
  catch _ =>
    return 0

/-- Read an unsigned integer sysctl file under `/proc/sys/`, falling back to `dflt` on error. -/
def readSysctlU32 (path : System.FilePath) (dflt : UInt32) : IO UInt32 := do
  try
    let txt ← IO.FS.readFile path
    match txt.trimAscii.toString.toNat? with
    | some n => return UInt32.ofNat n
    | none => return dflt
  catch _ =>
    return dflt

/-- Parse `/proc/self/uid_map` or `/proc/self/gid_map` `(inside_start, len)` intervals. -/
def readIdMap (path : System.FilePath) : IO (List (UInt32 × UInt32)) := do
  try
    let txt ← IO.FS.readFile path
    let mut out : List (UInt32 × UInt32) := []
    for rawLine in txt.splitOn "\n" do
      let toks := (rawLine.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
      match toks with
      | a :: _ :: lenStr :: _ =>
        if let (some ins, some len) := (a.toNat?, lenStr.toNat?) then
          out := out ++ [(UInt32.ofNat ins, UInt32.ofNat len)]
      | _ => pure ()
    return out
  catch _ =>
    return [(0, UInt32.ofNat 0xffffffff)]

/-- Return `true` iff `id != 0xffffffff` falls inside any mapped `(inside_start, len)` range. -/
def isIdMapped (ranges : List (UInt32 × UInt32)) (id : UInt32) : Bool :=
  if id == (0xffffffff : UInt32) then false
  else ranges.any fun (ins, len) => id >= ins && (id.toNat - ins.toNat) < len.toNat

/-- Read `fsgid` and supplementary `Groups` from `/proc/self/status`. -/
def readSelfGids : IO (List UInt32) := do
  try
    let txt ← IO.FS.readFile "/proc/self/status"
    let mut out : List UInt32 := []
    for line in txt.splitOn "\n" do
      if line.startsWith "Gid:" then
        let clean := ((line.drop 4).toString.replace "\t" " ").trimAscii.toString
        let toks := (clean.splitOn " ").filter (!·.isEmpty)
        match toks with
        | _ :: eg :: _ :: fsg :: _ =>
          if let some g := fsg.toNat? then out := UInt32.ofNat g :: out
          else if let some g := eg.toNat? then out := UInt32.ofNat g :: out
        | _ :: eg :: _ =>
          if let some g := eg.toNat? then out := UInt32.ofNat g :: out
        | _ => pure ()
      else if line.startsWith "Groups:" then
        let clean := ((line.drop 7).toString.replace "\t" " ").trimAscii.toString
        let toks := (clean.splitOn " ").filter (!·.isEmpty)
        for tok in toks do
          if let some g := tok.toNat? then
            let g32 := UInt32.ofNat g
            if !out.contains g32 then out := g32 :: out
    return out
  catch _ =>
    return []

end LeanSwe.LinuxSyscall.Fuzz.Env
