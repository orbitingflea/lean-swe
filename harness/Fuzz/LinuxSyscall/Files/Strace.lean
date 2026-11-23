import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Files.Seed
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.SpecTests
import Fuzz.LinuxSyscall.Env
import Fuzz.LinuxSyscall.SandboxEnv
import LeanSwe.LinuxSyscall.Sandbox.Interface

namespace Fuzz.LinuxSyscall.Files.Strace

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

private def assertTrue (msg : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"assertion failed: {msg}")

private def assertEqErrno (msg : String) (actual expected : Errno) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{msg}: expected errno {expected}, got {actual}")

private def assertErr {α : Type} (msg : String) (r : Except Errno α) (expected : Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error {expected}, got ok")
  | .error e => assertEqErrno msg e expected

private def assertErrOneOf {α : Type} (msg : String) (r : Except Errno α) (allowed : List Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error in {allowed}, got ok")
  | .error e =>
    if !allowed.contains e then
      throw (IO.userError s!"{msg}: expected error in {allowed}, got {e}")

private def assertOk {α : Type} (msg : String) (r : Except Errno α) : IO α := do
  match r with
  | .ok v => return v
  | .error e => throw (IO.userError s!"{msg}: unexpected error {e}")

private def withTempSandbox (tag : String) (k : System.FilePath -> IO Unit) : IO Unit := do
  let nanos ← IO.monoNanosNow
  let dir : System.FilePath := s!"/dev/shm/leanswe-files-rt-{tag}-{nanos}"
  if ← dir.pathExists then
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", s!"chmod -R u+rwx '{dir}' 2>/dev/null || true"] }
    IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let savedCwd ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir dir
    k dir
  finally
    IO.Process.setCurrentDir savedCwd
    if ← dir.pathExists then
      try
        IO.FS.removeDirAll dir
      catch _ =>
        let _ ← IO.Process.run { cmd := "sh", args := #["-c", s!"chmod -R u+rwx '{dir}' 2>/dev/null || true"] }
        if ← dir.pathExists then
          IO.FS.removeDirAll dir

private def safeClose (ops : FilesOps) (fd : RawFd) : IO Unit := do
  let _ ← ops.close fd

private def rwCreatFlags : OpenFlags := { access := .rdwr, creat := true }
private def roFlags : OpenFlags := { access := .rdonly }
private def woFlags : OpenFlags := { access := .wronly }
private def dirFlags : OpenFlags := { access := .rdonly, directory := true }

/-- Verify `openat` flag encoding and embedded-NUL `EINVAL` guard. -/
private def assume_files_openat_flagsAndNulGuard : IO Unit := withTempSandbox "a-openat" fun _ => do
  let ops := defaultOps
  let rNul ← ops.openat none (ByteArray.mk #[97, 0, 98]) rwCreatFlags 0o644
  assertErr "openat NUL" rNul Errno.EINVAL
  let fd ← assertOk "openat creat" (← ops.openat none "f.txt".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
  safeClose ops fd
  let rExcl ← ops.openat none "f.txt".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644
  assertErr "openat O_EXCL" rExcl Errno.EEXIST

/-- Verify `openat2` resolve flags and ABI struct passing. -/
private def assume_files_openat2_resolveFlagsAndAbi : IO Unit := withTempSandbox "a-openat2" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "openat2 create" (← ops.openat2 none "g.txt".toUTF8 { flags := rwCreatFlags, mode := 0o644, resolve := { beneath := true } })
  safeClose ops fd
  let rEsc ← ops.openat2 none "../escape".toUTF8 { flags := roFlags, mode := 0, resolve := { beneath := true } }
  assertErr "openat2 beneath" rEsc Errno.EXDEV

/-- Verify `LeanFdBox` ABA-safe `EBADF` on double-close and `EBUSY` when pinned concurrently. -/
private def assume_files_close_abaSafeFdBox : IO Unit := withTempSandbox "a-close" fun _ => do
  let ops := defaultOps
  let fd1 ← assertOk "open fd1" (← ops.openat none "lockf".toUTF8 rwCreatFlags 0o644)
  let fd2 ← assertOk "open fd2" (← ops.openat none "lockf".toUTF8 rwCreatFlags 0o644)
  assertOk "close fd1 ok" (← ops.close fd1)
  assertErr "double close fd1" (← ops.close fd1) Errno.EBADF
  let fd1b ← assertOk "reopen fd1b" (← ops.openat none "lockf".toUTF8 rwCreatFlags 0o644)
  assertOk "flock fd1b ex" (← ops.flock fd1b (.exclusive false))
  let blocker ← IO.asTask (prio := .default) (ops.flock fd2 (.exclusive false))
  IO.sleep 20
  let closeBusy ← ops.close fd2
  assertErr "close while pinned" closeBusy Errno.EBUSY
  assertOk "unlock fd1b" (← ops.flock fd1b .unlock)
  match blocker.get with
  | .ok (.ok ()) => pure ()
  | .ok (.error e) => throw (IO.userError s!"blocked flock task failed: {e}")
  | .error e => throw (IO.userError s!"blocked flock IO error: {e}")
  assertOk "unlock fd2" (← ops.flock fd2 .unlock)
  safeClose ops fd2
  safeClose ops fd1b

/-- Verify `read` clamping to `16 MiB` and short-read behavior. -/
private def assume_files_read_clamped16MiBAndPartial : IO Unit := withTempSandbox "a-read" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "r.bin".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write" (← ops.write fd "abc".toUTF8)
  safeClose ops fd
  let rfd ← assertOk "reopen" (← ops.openat none "r.bin".toUTF8 roFlags 0)
  let got ← assertOk "read oversized" (← ops.read rfd 0x7fffffff)
  assertTrue "read bytes" (got == "abc".toUTF8)
  safeClose ops rfd

/-- Verify `write` partial count return and `O_APPEND` positioning. -/
private def assume_files_write_partialAndAppend : IO Unit := withTempSandbox "a-write" fun _ => do
  let ops := defaultOps
  let fd1 ← assertOk "open1" (← ops.openat none "w.bin".toUTF8 rwCreatFlags 0o644)
  let n1 ← assertOk "write1" (← ops.write fd1 "hi".toUTF8)
  assertTrue "n1=2" (n1 == 2)
  safeClose ops fd1
  let fd2 ← assertOk "open2" (← ops.openat none "w.bin".toUTF8 { access := .wronly, append := true } 0)
  let n2 ← assertOk "write2" (← ops.write fd2 "!".toUTF8)
  assertTrue "n2=1" (n2 == 1)
  safeClose ops fd2
  let fd3 ← assertOk "open3" (← ops.openat none "w.bin".toUTF8 roFlags 0)
  let all ← assertOk "read3" (← ops.read fd3 16)
  assertTrue "append content" (all == "hi!".toUTF8)
  safeClose ops fd3

/-- Verify `fstat` portable `StatInfo` decoding. -/
private def assume_files_fstat_portableStatDecode : IO Unit := withTempSandbox "a-fstat" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "st.bin".toUTF8 rwCreatFlags 0o640)
  let _ ← assertOk "write" (← ops.write fd "12345".toUTF8)
  let st ← assertOk "fstat" (← ops.fstat fd)
  assertTrue "reg kind" (st.kind == .reg)
  assertTrue "size=5" (st.size == 5)
  safeClose ops fd

/-- Verify `fstatat` `AT_SYMLINK_NOFOLLOW` and `AT_EMPTY_PATH`. -/
private def assume_files_fstatat_nofollowAndEmptyPath : IO Unit := withTempSandbox "a-fstatat" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "t.bin".toUTF8 rwCreatFlags 0o644)
  let stEmpty ← assertOk "fstatat empty" (← ops.fstatat (some fd) ByteArray.empty { emptyPath := true })
  assertTrue "emptyPath reg" (stEmpty.kind == .reg)
  safeClose ops fd
  assertOk "symlink" (← ops.symlinkat "t.bin".toUTF8 none "lnk".toUTF8)
  let stLnk ← assertOk "fstatat nofollow" (← ops.fstatat none "lnk".toUTF8 { symlinkNofollow := true })
  assertTrue "symlink kind" (stLnk.kind == .symlink)

/-- Verify `faccessat2` mode bits and `AT_EMPTY_PATH`. -/
private def assume_files_faccessat_modeBits : IO Unit := withTempSandbox "a-faccess" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "acc.bin".toUTF8 rwCreatFlags 0o444)
  assertOk "faccessat F_OK" (← ops.faccessat none "acc.bin".toUTF8 {} {})
  assertOk "faccessat AT_EMPTY_PATH" (← ops.faccessat (some fd) ByteArray.empty {} { emptyPath := true })
  assertErr "faccessat W_OK on 0444" (← ops.faccessat none "acc.bin".toUTF8 { write := true } {}) Errno.EACCES
  safeClose ops fd

/-- Verify `mkdirat` mode and NUL guard. -/
private def assume_files_mkdirat_modeAndNulGuard : IO Unit := withTempSandbox "a-mkdir" fun _ => do
  let ops := defaultOps
  assertErr "mkdirat NUL" (← ops.mkdirat none (ByteArray.mk #[100, 0]) 0o755) Errno.EINVAL
  assertOk "mkdirat" (← ops.mkdirat none "sub".toUTF8 0o755)
  let st ← assertOk "fstatat sub" (← ops.fstatat none "sub".toUTF8 {})
  assertTrue "sub is dir" (st.kind == .dir)

/-- Verify `unlinkat` `AT_REMOVEDIR` flag. -/
private def assume_files_unlinkat_removeDirFlag : IO Unit := withTempSandbox "a-unlink" fun _ => do
  let ops := defaultOps
  assertOk "mkdirat" (← ops.mkdirat none "d".toUTF8 0o755)
  assertErr "unlink dir without flag" (← ops.unlinkat none "d".toUTF8 false) Errno.EISDIR
  assertOk "unlink dir with flag" (← ops.unlinkat none "d".toUTF8 true)

/-- Verify `renameat2` `RENAME_NOREPLACE` and `RENAME_EXCHANGE` ABI. -/
private def assume_files_renameat2_flagsAbi : IO Unit := withTempSandbox "a-rename" fun _ => do
  let ops := defaultOps
  let f1 ← assertOk "open1" (← ops.openat none "r1".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "w1" (← ops.write f1 "one".toUTF8)
  safeClose ops f1
  let f2 ← assertOk "open2" (← ops.openat none "r2".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "w2" (← ops.write f2 "two!".toUTF8)
  safeClose ops f2
  assertErr "noreplace" (← ops.renameat2 none "r1".toUTF8 none "r2".toUTF8 { noreplace := true }) Errno.EEXIST
  assertOk "exchange" (← ops.renameat2 none "r1".toUTF8 none "r2".toUTF8 { exchange := true })
  let st1 ← assertOk "stat r1" (← ops.fstatat none "r1".toUTF8 {})
  assertTrue "exchanged size=4" (st1.size == 4)

/-- Verify `symlinkat` raw byte handling and NUL guard. -/
private def assume_files_symlinkat_rawBytesAndNulGuard : IO Unit := withTempSandbox "a-sym" fun _ => do
  let ops := defaultOps
  assertErr "symlink target NUL" (← ops.symlinkat (ByteArray.mk #[97, 0]) none "l".toUTF8) Errno.EINVAL
  assertOk "symlinkat" (← ops.symlinkat "dest-raw".toUTF8 none "l".toUTF8)

/-- Verify `readlinkat` clamped raw byte output. -/
private def assume_files_readlinkat_clampedRawBytes : IO Unit := withTempSandbox "a-readlink" fun _ => do
  let ops := defaultOps
  assertOk "symlinkat" (← ops.symlinkat "target-123".toUTF8 none "l".toUTF8)
  let got ← assertOk "readlinkat" (← ops.readlinkat none "l".toUTF8 64)
  assertTrue "target match" (got == "target-123".toUTF8)

/-- Verify `getdents64` returns raw dirent bytes on open directories. -/
private def assume_files_getdents64_rawDirentBuffer : IO Unit := withTempSandbox "a-getdents" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open dir" (← ops.openat none ".".toUTF8 dirFlags 0)
  let buf ← assertOk "getdents64" (← ops.getdents64 fd 4096)
  assertTrue "non-empty dirents" (buf.size > 0)
  safeClose ops fd

/-- Verify `fchmodat` mode update and NUL guard. -/
private def assume_files_fchmodat_modeAndNulGuard : IO Unit := withTempSandbox "a-fchmodat" fun _ => do
  let ops := defaultOps
  assertErr "fchmodat NUL" (← ops.fchmodat none (ByteArray.mk #[97, 0]) 0o600) Errno.EINVAL
  let fd ← assertOk "open" (← ops.openat none "m".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertOk "fchmodat" (← ops.fchmodat none "m".toUTF8 0o600)
  let st ← assertOk "stat" (← ops.fstatat none "m".toUTF8 {})
  assertTrue "mode=0600" ((st.mode &&& (0o777 : UInt32)) == (0o600 : UInt32))

/-- Verify `fchmod` updates mode on an open FD. -/
private def assume_files_fchmod_modeUpdate : IO Unit := withTempSandbox "a-fchmod" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "fm".toUTF8 rwCreatFlags 0o644)
  assertOk "fchmod" (← ops.fchmod fd 0o640)
  let st ← assertOk "fstat" (← ops.fstat fd)
  assertTrue "mode=0640" ((st.mode &&& (0o777 : UInt32)) == (0o640 : UInt32))
  safeClose ops fd

/-- Verify `flock` advisory lock flags and unlock. -/
private def assume_files_flock_advisoryLockFlags : IO Unit := withTempSandbox "a-flock" fun _ => do
  let ops := defaultOps
  let f1 ← assertOk "open1" (← ops.openat none "fl".toUTF8 rwCreatFlags 0o644)
  let f2 ← assertOk "open2" (← ops.openat none "fl".toUTF8 rwCreatFlags 0o644)
  assertOk "ex f1" (← ops.flock f1 (.exclusive false))
  assertErr "nb conflict" (← ops.flock f2 (.exclusive true)) Errno.EAGAIN
  assertOk "unlock f1" (← ops.flock f1 .unlock)
  assertOk "sh f2" (← ops.flock f2 (.shared true))
  safeClose ops f2
  safeClose ops f1

/-- Verify `fcntl` curated commands (`getFl`, `setFl`, `getFd`, `setFd`, `getSeals`). -/
private def assume_files_fcntl_curatedCommands : IO Unit := withTempSandbox "a-fcntl" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "fc".toUTF8 rwCreatFlags 0o644)
  let fl0 ← assertOk "getFl" (← ops.fcntl fd .getFl)
  assertTrue "rdwr bit 2" ((fl0 &&& 3) == 2)
  let _ ← assertOk "setFl" (← ops.fcntl fd (.setFl true true))
  let fl1 ← assertOk "getFl after" (← ops.fcntl fd .getFl)
  let mask : UInt32 := ((1 : UInt32) <<< 5) ||| ((1 : UInt32) <<< 8)
  assertTrue "append+nonblock bits" ((fl1 &&& mask) == mask)
  let _ ← assertOk "setFd" (← ops.fcntl fd (.setFd false))
  let fd0 ← assertOk "getFd" (← ops.fcntl fd .getFd)
  assertTrue "cloexec cleared" (fd0 == 0)
  match ← ops.fcntl fd .getSeals with
  | .ok seals => assertTrue "tmpfs seals >= 1" (seals >= 1)
  | .error e => assertEqErrno "non-tmpfs getSeals EINVAL" e Errno.EINVAL
  safeClose ops fd

/-- Verify `fsync` succeeds on a writable FD. -/
private def assume_files_fsync_fdSync : IO Unit := withTempSandbox "a-fsync" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "fs".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write" (← ops.write fd "sync".toUTF8)
  assertOk "fsync" (← ops.fsync fd)
  safeClose ops fd

/-- Verify `getcwd` returns current working directory and rejects tiny buffers. -/
private def assume_files_getcwd_clampedBuffer : IO Unit := withTempSandbox "a-getcwd" fun dir => do
  let ops := defaultOps
  assertErrOneOf "getcwd 1" (← ops.getcwd 1) [Errno.ERANGE, Errno.EINVAL]
  let cwd ← assertOk "getcwd 4096" (← ops.getcwd 4096)
  assertTrue "cwd matches dir" (cwd == dir.toString.toUTF8)

/-- Verify `lseek` (`SEEK_SET`/`SEEK_CUR`/`SEEK_END`, negative `EINVAL`, `0o400` dir rewind), `O_NOCTTY`, and `O_PATH`. -/
private def assume_files_lseek_offsetAndDirRewind : IO Unit := withTempSandbox "a-lseek" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open reg" (← ops.openat none "f.txt".toUTF8
    { access := .rdwr, creat := true, excl := true, noctty := true } 0o644)
  let _ ← assertOk "write" (← ops.write fd "hello".toUTF8)
  assertErr "lseek neg" (← ops.lseek fd (-1) .seekSet) Errno.EINVAL
  assertTrue "lseek set 2" ((← assertOk "set 2" (← ops.lseek fd 2 .seekSet)) == 2)
  assertTrue "read tail" ((← assertOk "read" (← ops.read fd 8)) == "llo".toUTF8)
  assertTrue "lseek end -2" ((← assertOk "end -2" (← ops.lseek fd (-2) .seekEnd)) == 3)
  assertTrue "lseek cur -1" ((← assertOk "cur -1" (← ops.lseek fd (-1) .seekCur)) == 2)
  safeClose ops fd
  let pfd ← assertOk "open O_PATH" (← ops.openat none "f.txt".toUTF8 { path := true } 0)
  assertErr "read O_PATH" (← ops.read pfd 4) Errno.EBADF
  assertErr "lseek O_PATH" (← ops.lseek pfd 0 .seekSet) Errno.EBADF
  assertErr "openat2 O_PATH|O_NOCTTY" (← ops.openat2 none "f.txt".toUTF8 { flags := { path := true, noctty := true } }) Errno.EINVAL
  safeClose ops pfd
  assertOk "mkdir d400" (← ops.mkdirat none "d400".toUTF8 0o755)
  let cfd ← assertOk "creat child" (← ops.openat none "d400/x".toUTF8 rwCreatFlags 0o644)
  safeClose ops cfd
  assertOk "chmod d400" (← ops.fchmodat none "d400".toUTF8 0o400)
  let dfd ← assertOk "open d400" (← ops.openat none "d400".toUTF8 dirFlags 0)
  let d1 ← assertOk "getdents1" (← ops.getdents64 dfd 4096)
  assertTrue "d1 non-empty" (d1.data.size ≥ 48)
  assertTrue "getdents eof" ((← assertOk "eof" (← ops.getdents64 dfd 4096)).data.size == 0)
  assertTrue "lseek dir 0" ((← assertOk "dir seek0" (← ops.lseek dfd 0 .seekSet)) == 0)
  let d2 ← assertOk "getdents2" (← ops.getdents64 dfd 4096)
  assertTrue "d2 matches d1 size" (d2.data.size == d1.data.size)
  safeClose ops dfd

/-- Verify `reopenReadOnly` reopens unlinked files/memfds read-only at offset `0` and rejects `O_PATH` symlinks with `ELOOP`. -/
private def assume_files_reopenReadOnly_procSelfFd : IO Unit := withTempSandbox "a-reopen" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open rw" (← ops.openat none "u.bin".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write" (← ops.write fd "secret".toUTF8)
  assertOk "unlink" (← ops.unlinkat none "u.bin".toUTF8 false)
  let ro ← assertOk "reopen unlinked" (← ops.reopenReadOnly fd)
  assertTrue "read from 0" ((← assertOk "read ro" (← ops.read ro 16)) == "secret".toUTF8)
  assertErr "write ro -> EBADF" (← ops.write ro "x".toUTF8) Errno.EBADF
  safeClose ops ro
  safeClose ops fd
  assertOk "sym" (← ops.symlinkat "missing".toUTF8 none "sym".toUTF8)
  let sfd ← assertOk "open sym O_PATH" (← ops.openat none "sym".toUTF8 { path := true, nofollow := true } 0)
  assertErr "reopen sym -> ELOOP" (← ops.reopenReadOnly sfd) Errno.ELOOP
  safeClose ops sfd

/-- Verify `dupStdio` duplicates valid stdio slots with `FD_CLOEXEC` (`>= 3`) without closing `0`/`1`/`2`. -/
private def assume_files_dupStdio_cloexecSlot : IO Unit := withTempSandbox "a-dupstdio" fun _ => do
  let ops := defaultOps
  for slot in [StdioFd.stdin, StdioFd.stdout, StdioFd.stderr] do
    match ← ops.dupStdio slot with
    | .ok dfd =>
      let fl ← assertOk "fcntl getFd" (← ops.fcntl dfd .getFd)
      assertTrue "FD_CLOEXEC set" (fl == 1)
      let rawFd ← Fuzz.LinuxSyscall.Env.rawFdNum dfd
      assertTrue "dupStdio rawFd >= 3" (rawFd >= 3 && rawFd != 0xffffffff)
      safeClose ops dfd
    | .error e =>
      assertEqErrno "dupStdio error if closed" e Errno.EBADF

private def closedFd (ops : FilesOps) : IO RawFd := do
  let fd ← assertOk "open temp" (← ops.openat none "tmpfd".toUTF8 rwCreatFlags 0o644)
  assertOk "close temp" (← ops.close fd)
  return fd

private def runMockTransient (opName : String) (act : FilesOps -> IO (Except Errno Unit)) : IO Unit :=
  withTempSandbox s!"m-{opName}" fun _ => do
    let realOps := defaultOps
    let ref ← IO.mkRef Errno.EIO
    let _ ← realOps.getcwd 64
    let mockOps : FilesOps := {
      openat := fun _ _ _ _ => do return .error (← ref.get)
      openat2 := fun _ _ _ => do return .error (← ref.get)
      close := fun _ => do return .error (← ref.get)
      read := fun _ _ => do return .error (← ref.get)
      write := fun _ _ => do return .error (← ref.get)
      fstat := fun _ => do return .error (← ref.get)
      fstatat := fun _ _ _ => do return .error (← ref.get)
      faccessat := fun _ _ _ _ => do return .error (← ref.get)
      mkdirat := fun _ _ _ => do return .error (← ref.get)
      unlinkat := fun _ _ _ => do return .error (← ref.get)
      renameat2 := fun _ _ _ _ _ => do return .error (← ref.get)
      symlinkat := fun _ _ _ => do return .error (← ref.get)
      readlinkat := fun _ _ _ => do return .error (← ref.get)
      getdents64 := fun _ _ => do return .error (← ref.get)
      fchmodat := fun _ _ _ => do return .error (← ref.get)
      fchmod := fun _ _ => do return .error (← ref.get)
      flock := fun _ _ => do return .error (← ref.get)
      fcntl := fun _ _ => do return .error (← ref.get)
      fsync := fun _ => do return .error (← ref.get)
      getcwd := fun _ => do return .error (← ref.get)
      lseek := fun _ _ _ => do return .error (← ref.get)
      reopenReadOnly := fun _ => do return .error (← ref.get)
      dupStdio := fun _ => do return .error (← ref.get)
    }
    let res ← act mockOps
    match res with
    | .ok () => throw (IO.userError s!"mock {opName} expected transient error")
    | .error e =>
      if e != Errno.EIO && e != Errno.EINTR && e != Errno.ENOMEM && e != Errno.ENFILE then
        throw (IO.userError s!"mock {opName} unexpected errno {e}")

/-- Real `openat` `.notFound` test (`ENOENT`). -/
private def err_openat_notFound : IO Unit := withTempSandbox "eo-nf" fun _ => do
  assertErr "openat ENOENT" (← defaultOps.openat none "missing".toUTF8 roFlags 0) Errno.ENOENT

/-- Real `openat` `.badFd` test (`EBADF`). -/
private def err_openat_badFd : IO Unit := withTempSandbox "eo-bfd" fun _ => do
  let ops := defaultOps
  let cfd ← closedFd ops
  assertErr "openat EBADF" (← ops.openat (some cfd) "x".toUTF8 roFlags 0) Errno.EBADF

/-- Real `openat` `.invalidArg` test (`EINVAL`). -/
private def err_openat_invalidArg : IO Unit := withTempSandbox "eo-inv" fun _ => do
  assertErr "openat EINVAL" (← defaultOps.openat none (ByteArray.mk #[97, 0]) roFlags 0) Errno.EINVAL

/-- Real `openat` `.stateConflict` test (`EEXIST`). -/
private def err_openat_stateConflict : IO Unit := withTempSandbox "eo-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "create" (← ops.openat none "ex".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertErr "openat EEXIST" (← ops.openat none "ex".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644) Errno.EEXIST

/-- Real `openat` `.permissionDenied` test (`EACCES`). -/
private def err_openat_permissionDenied : IO Unit := withTempSandbox "eo-pd" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "create" (← ops.openat none "ro".toUTF8 rwCreatFlags 0o444)
  safeClose ops fd
  assertErr "openat EACCES" (← ops.openat none "ro".toUTF8 woFlags 0) Errno.EACCES

/-- Mocked `openat` `.transientOrResource` test. -/
private def err_openat_transient : IO Unit :=
  runMockTransient "openat" fun ops => ops.openat none "x".toUTF8 roFlags 0 >>= fun r => pure (r.map fun _ => ())

/-- Real `openat2` `.notFound` test (`ENOENT`). -/
private def err_openat2_notFound : IO Unit := withTempSandbox "eo2-nf" fun _ => do
  assertErr "openat2 ENOENT" (← defaultOps.openat2 none "missing".toUTF8 { flags := roFlags }) Errno.ENOENT

/-- Real `openat2` `.badFd` test (`EBADF`). -/
private def err_openat2_badFd : IO Unit := withTempSandbox "eo2-bfd" fun _ => do
  let ops := defaultOps
  let cfd ← closedFd ops
  assertErr "openat2 EBADF" (← ops.openat2 (some cfd) "x".toUTF8 { flags := roFlags }) Errno.EBADF

/-- Real `openat2` `.invalidArg` test (`EINVAL`). -/
private def err_openat2_invalidArg : IO Unit := withTempSandbox "eo2-inv" fun _ => do
  assertErr "openat2 EINVAL" (← defaultOps.openat2 none "x".toUTF8 { flags := roFlags, resolve := { beneath := true, inRoot := true } }) Errno.EINVAL

/-- Real `openat2` `.stateConflict` test (`EXDEV`). -/
private def err_openat2_stateConflict : IO Unit := withTempSandbox "eo2-sc" fun _ => do
  assertErr "openat2 EXDEV" (← defaultOps.openat2 none "../x".toUTF8 { flags := roFlags, resolve := { beneath := true } }) Errno.EXDEV

/-- Real `openat2` `.permissionDenied` test (`EACCES`). -/
private def err_openat2_permissionDenied : IO Unit := withTempSandbox "eo2-pd" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "create" (← ops.openat none "ro2".toUTF8 rwCreatFlags 0o444)
  safeClose ops fd
  assertErr "openat2 EACCES" (← ops.openat2 none "ro2".toUTF8 { flags := woFlags }) Errno.EACCES

/-- Mocked `openat2` `.transientOrResource` test. -/
private def err_openat2_transient : IO Unit :=
  runMockTransient "openat2" fun ops => ops.openat2 none "x".toUTF8 { flags := roFlags } >>= fun r => pure (r.map fun _ => ())

/-- Mocked `close` error test. -/
private def err_close_mocked : IO Unit := withTempSandbox "ec-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "c".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "close" fun ops => ops.close fd

/-- Real `close` `.badFd` test (`EBADF`). -/
private def err_close_badFd : IO Unit := withTempSandbox "ec-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "close EBADF" (← defaultOps.close cfd) Errno.EBADF

/-- Mocked `read` error test. -/
private def err_read_mocked : IO Unit := withTempSandbox "er-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "r".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "read" fun ops => ops.read fd 16 >>= fun r => pure (r.map fun _ => ())

/-- Real `read` `.badFd` test (`EBADF`). -/
private def err_read_badFd : IO Unit := withTempSandbox "er-bfd" fun _ => do
  let ops := defaultOps
  let cfd ← closedFd ops
  assertErr "read EBADF" (← ops.read cfd 16) Errno.EBADF

/-- Real `read` `.stateConflict` test (`EISDIR`). -/
private def err_read_stateConflict : IO Unit := withTempSandbox "er-sc" fun _ => do
  let ops := defaultOps
  let dfd ← assertOk "opendir" (← ops.openat none ".".toUTF8 dirFlags 0)
  assertErr "read dir EISDIR" (← ops.read dfd 16) Errno.EISDIR
  safeClose ops dfd

/-- Mocked `write` error test. -/
private def err_write_mocked : IO Unit := withTempSandbox "ew-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "w".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "write" fun ops => ops.write fd "x".toUTF8 >>= fun r => pure (r.map fun _ => ())

/-- Real `write` `.badFd` test (`EBADF`). -/
private def err_write_badFd : IO Unit := withTempSandbox "ew-bfd" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open ro" (← ops.openat none "ro".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  let rfd ← assertOk "reopen ro" (← ops.openat none "ro".toUTF8 roFlags 0)
  assertErr "write EBADF" (← ops.write rfd "x".toUTF8) Errno.EBADF
  safeClose ops rfd

/-- Mocked `fstat` error test. -/
private def err_fstat_mocked : IO Unit := withTempSandbox "efs-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "fs".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "fstat" fun ops => ops.fstat fd >>= fun r => pure (r.map fun _ => ())

/-- Real `fstat` `.badFd` test (`EBADF`). -/
private def err_fstat_badFd : IO Unit := withTempSandbox "efs-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fstat EBADF" (← defaultOps.fstat cfd) Errno.EBADF

/-- Real `fstatat` `.notFound` test (`ENOENT`). -/
private def err_fstatat_notFound : IO Unit := withTempSandbox "efsa-nf" fun _ => do
  assertErr "fstatat ENOENT" (← defaultOps.fstatat none "missing".toUTF8 {}) Errno.ENOENT

/-- Real `fstatat` `.badFd` test (`EBADF`). -/
private def err_fstatat_badFd : IO Unit := withTempSandbox "efsa-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fstatat EBADF" (← defaultOps.fstatat (some cfd) "x".toUTF8 {}) Errno.EBADF

/-- Real `fstatat` `.invalidArg` test (`EINVAL`). -/
private def err_fstatat_invalidArg : IO Unit := withTempSandbox "efsa-inv" fun _ => do
  assertErr "fstatat EINVAL" (← defaultOps.fstatat none (ByteArray.mk #[97, 0]) {}) Errno.EINVAL

/-- Real `fstatat` `.stateConflict` test (`ENOTDIR`). -/
private def err_fstatat_stateConflict : IO Unit := withTempSandbox "efsa-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  assertErr "fstatat ENOTDIR" (← ops.fstatat (some fd) "c".toUTF8 {}) Errno.ENOTDIR
  safeClose ops fd

/-- Real `fstatat` `.permissionDenied` test (`EACCES`). -/
private def err_fstatat_permissionDenied : IO Unit := withTempSandbox "efsa-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o755)
  assertOk "chmod 000" (← ops.fchmodat none "d".toUTF8 0o000)
  assertErr "fstatat EACCES" (← ops.fstatat none "d/c".toUTF8 {}) Errno.EACCES

/-- Mocked `fstatat` `.transientOrResource` test. -/
private def err_fstatat_transient : IO Unit :=
  runMockTransient "fstatat" fun ops => ops.fstatat none "x".toUTF8 {} >>= fun r => pure (r.map fun _ => ())

/-- Real `faccessat` `.notFound` test (`ENOENT`). -/
private def err_faccessat_notFound : IO Unit := withTempSandbox "efa-nf" fun _ => do
  assertErr "faccessat ENOENT" (← defaultOps.faccessat none "missing".toUTF8 {} {}) Errno.ENOENT

/-- Real `faccessat` `.badFd` test (`EBADF`). -/
private def err_faccessat_badFd : IO Unit := withTempSandbox "efa-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "faccessat EBADF" (← defaultOps.faccessat (some cfd) "x".toUTF8 {} {}) Errno.EBADF

/-- Real `faccessat` `.invalidArg` test (`EINVAL`). -/
private def err_faccessat_invalidArg : IO Unit := withTempSandbox "efa-inv" fun _ => do
  assertErr "faccessat EINVAL" (← defaultOps.faccessat none (ByteArray.mk #[97, 0]) {} {}) Errno.EINVAL

/-- Real `faccessat` `.stateConflict` test (`ENOTDIR`). -/
private def err_faccessat_stateConflict : IO Unit := withTempSandbox "efa-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  assertErr "faccessat ENOTDIR" (← ops.faccessat (some fd) "c".toUTF8 {} {}) Errno.ENOTDIR
  safeClose ops fd

/-- Real `faccessat` `.permissionDenied` test (`EACCES`). -/
private def err_faccessat_permissionDenied : IO Unit := withTempSandbox "efa-pd" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "ro".toUTF8 rwCreatFlags 0o444)
  safeClose ops fd
  assertErr "faccessat EACCES" (← ops.faccessat none "ro".toUTF8 { write := true } {}) Errno.EACCES

/-- Mocked `faccessat` `.transientOrResource` test. -/
private def err_faccessat_transient : IO Unit :=
  runMockTransient "faccessat" fun ops => ops.faccessat none "x".toUTF8 {} {}

/-- Real `mkdirat` `.notFound` test (`ENOENT`). -/
private def err_mkdirat_notFound : IO Unit := withTempSandbox "emk-nf" fun _ => do
  assertErr "mkdirat ENOENT" (← defaultOps.mkdirat none "no/child".toUTF8 0o755) Errno.ENOENT

/-- Real `mkdirat` `.badFd` test (`EBADF`). -/
private def err_mkdirat_badFd : IO Unit := withTempSandbox "emk-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "mkdirat EBADF" (← defaultOps.mkdirat (some cfd) "d".toUTF8 0o755) Errno.EBADF

/-- Real `mkdirat` `.invalidArg` test (`EINVAL`). -/
private def err_mkdirat_invalidArg : IO Unit := withTempSandbox "emk-inv" fun _ => do
  assertErr "mkdirat EINVAL" (← defaultOps.mkdirat none (ByteArray.mk #[97, 0]) 0o755) Errno.EINVAL

/-- Real `mkdirat` `.stateConflict` test (`EEXIST`). -/
private def err_mkdirat_stateConflict : IO Unit := withTempSandbox "emk-sc" fun _ => do
  assertOk "mkdir1" (← defaultOps.mkdirat none "d".toUTF8 0o755)
  assertErr "mkdirat EEXIST" (← defaultOps.mkdirat none "d".toUTF8 0o755) Errno.EEXIST

/-- Real `mkdirat` `.permissionDenied` test (`EACCES`). -/
private def err_mkdirat_permissionDenied : IO Unit := withTempSandbox "emk-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o555)
  assertErr "mkdirat EACCES" (← ops.mkdirat none "d/c".toUTF8 0o755) Errno.EACCES

/-- Mocked `mkdirat` `.transientOrResource` test. -/
private def err_mkdirat_transient : IO Unit :=
  runMockTransient "mkdirat" fun ops => ops.mkdirat none "d".toUTF8 0o755

/-- Real `unlinkat` `.notFound` test (`ENOENT`). -/
private def err_unlinkat_notFound : IO Unit := withTempSandbox "eul-nf" fun _ => do
  assertErr "unlinkat ENOENT" (← defaultOps.unlinkat none "missing".toUTF8 false) Errno.ENOENT

/-- Real `unlinkat` `.badFd` test (`EBADF`). -/
private def err_unlinkat_badFd : IO Unit := withTempSandbox "eul-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "unlinkat EBADF" (← defaultOps.unlinkat (some cfd) "x".toUTF8 false) Errno.EBADF

/-- Real `unlinkat` `.invalidArg` test (`EINVAL`). -/
private def err_unlinkat_invalidArg : IO Unit := withTempSandbox "eul-inv" fun _ => do
  assertErr "unlinkat EINVAL" (← defaultOps.unlinkat none (ByteArray.mk #[97, 0]) false) Errno.EINVAL

/-- Real `unlinkat` `.stateConflict` test (`EISDIR`). -/
private def err_unlinkat_stateConflict : IO Unit := withTempSandbox "eul-sc" fun _ => do
  assertOk "mkdir" (← defaultOps.mkdirat none "d".toUTF8 0o755)
  assertErr "unlinkat EISDIR" (← defaultOps.unlinkat none "d".toUTF8 false) Errno.EISDIR

/-- Real `unlinkat` `.permissionDenied` test (`EACCES`). -/
private def err_unlinkat_permissionDenied : IO Unit := withTempSandbox "eul-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o755)
  let fd ← assertOk "open" (← ops.openat none "d/f".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertOk "chmod 555" (← ops.fchmodat none "d".toUTF8 0o555)
  assertErr "unlinkat EACCES" (← ops.unlinkat none "d/f".toUTF8 false) Errno.EACCES

/-- Mocked `unlinkat` `.transientOrResource` test. -/
private def err_unlinkat_transient : IO Unit :=
  runMockTransient "unlinkat" fun ops => ops.unlinkat none "x".toUTF8 false

/-- Real `renameat2` `.notFound` test (`ENOENT`). -/
private def err_renameat2_notFound : IO Unit := withTempSandbox "ern-nf" fun _ => do
  assertErr "renameat2 ENOENT" (← defaultOps.renameat2 none "m".toUTF8 none "dst".toUTF8 {}) Errno.ENOENT

/-- Real `renameat2` `.badFd` test (`EBADF`). -/
private def err_renameat2_badFd : IO Unit := withTempSandbox "ern-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "renameat2 EBADF" (← defaultOps.renameat2 (some cfd) "a".toUTF8 none "b".toUTF8 {}) Errno.EBADF

/-- Real `renameat2` `.invalidArg` test (`EINVAL`). -/
private def err_renameat2_invalidArg : IO Unit := withTempSandbox "ern-inv" fun _ => do
  assertErr "renameat2 EINVAL" (← defaultOps.renameat2 none "a".toUTF8 none "b".toUTF8 { noreplace := true, exchange := true }) Errno.EINVAL

/-- Real `renameat2` `.stateConflict` test (`EEXIST`). -/
private def err_renameat2_stateConflict : IO Unit := withTempSandbox "ern-sc" fun _ => do
  let ops := defaultOps
  let f1 ← assertOk "o1" (← ops.openat none "a".toUTF8 rwCreatFlags 0o644)
  safeClose ops f1
  let f2 ← assertOk "o2" (← ops.openat none "b".toUTF8 rwCreatFlags 0o644)
  safeClose ops f2
  assertErr "renameat2 EEXIST" (← ops.renameat2 none "a".toUTF8 none "b".toUTF8 { noreplace := true }) Errno.EEXIST

/-- Real `renameat2` `.permissionDenied` test (`EACCES`). -/
private def err_renameat2_permissionDenied : IO Unit := withTempSandbox "ern-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o755)
  let fd ← assertOk "open" (← ops.openat none "d/a".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertOk "chmod 555" (← ops.fchmodat none "d".toUTF8 0o555)
  assertErr "renameat2 EACCES" (← ops.renameat2 none "d/a".toUTF8 none "d/b".toUTF8 {}) Errno.EACCES

/-- Mocked `renameat2` `.transientOrResource` test. -/
private def err_renameat2_transient : IO Unit :=
  runMockTransient "renameat2" fun ops => ops.renameat2 none "a".toUTF8 none "b".toUTF8 {}

/-- Real `symlinkat` `.notFound` test (`ENOENT`). -/
private def err_symlinkat_notFound : IO Unit := withTempSandbox "esym-nf" fun _ => do
  assertErr "symlinkat ENOENT" (← defaultOps.symlinkat "tgt".toUTF8 none "no/lnk".toUTF8) Errno.ENOENT

/-- Real `symlinkat` `.badFd` test (`EBADF`). -/
private def err_symlinkat_badFd : IO Unit := withTempSandbox "esym-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "symlinkat EBADF" (← defaultOps.symlinkat "tgt".toUTF8 (some cfd) "lnk".toUTF8) Errno.EBADF

/-- Real `symlinkat` `.invalidArg` test (`EINVAL`). -/
private def err_symlinkat_invalidArg : IO Unit := withTempSandbox "esym-inv" fun _ => do
  assertErr "symlinkat EINVAL" (← defaultOps.symlinkat (ByteArray.mk #[97, 0]) none "lnk".toUTF8) Errno.EINVAL

/-- Real `symlinkat` `.stateConflict` test (`EEXIST`). -/
private def err_symlinkat_stateConflict : IO Unit := withTempSandbox "esym-sc" fun _ => do
  assertOk "sym1" (← defaultOps.symlinkat "t".toUTF8 none "l".toUTF8)
  assertErr "symlinkat EEXIST" (← defaultOps.symlinkat "t".toUTF8 none "l".toUTF8) Errno.EEXIST

/-- Real `symlinkat` `.permissionDenied` test (`EACCES`). -/
private def err_symlinkat_permissionDenied : IO Unit := withTempSandbox "esym-pd" fun _ => do
  assertOk "mkdir" (← defaultOps.mkdirat none "d".toUTF8 0o555)
  assertErr "symlinkat EACCES" (← defaultOps.symlinkat "t".toUTF8 none "d/l".toUTF8) Errno.EACCES

/-- Mocked `symlinkat` `.transientOrResource` test. -/
private def err_symlinkat_transient : IO Unit :=
  runMockTransient "symlinkat" fun ops => ops.symlinkat "t".toUTF8 none "l".toUTF8

/-- Real `readlinkat` `.notFound` test (`ENOENT`). -/
private def err_readlinkat_notFound : IO Unit := withTempSandbox "erl-nf" fun _ => do
  assertErr "readlinkat ENOENT" (← defaultOps.readlinkat none "missing".toUTF8 64) Errno.ENOENT

/-- Real `readlinkat` `.badFd` test (`EBADF`). -/
private def err_readlinkat_badFd : IO Unit := withTempSandbox "erl-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "readlinkat EBADF" (← defaultOps.readlinkat (some cfd) "l".toUTF8 64) Errno.EBADF

/-- Real `readlinkat` `.invalidArg` test (`EINVAL`). -/
private def err_readlinkat_invalidArg : IO Unit := withTempSandbox "erl-inv" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertErr "readlinkat EINVAL" (← ops.readlinkat none "reg".toUTF8 64) Errno.EINVAL

/-- Real `readlinkat` `.stateConflict` test (`ENOTDIR`). -/
private def err_readlinkat_stateConflict : IO Unit := withTempSandbox "erl-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  assertErr "readlinkat ENOTDIR" (← ops.readlinkat (some fd) "x".toUTF8 64) Errno.ENOTDIR
  safeClose ops fd

/-- Real `readlinkat` `.permissionDenied` test (`EACCES`). -/
private def err_readlinkat_permissionDenied : IO Unit := withTempSandbox "erl-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o755)
  assertOk "chmod 000" (← ops.fchmodat none "d".toUTF8 0o000)
  assertErr "readlinkat EACCES" (← ops.readlinkat none "d/l".toUTF8 64) Errno.EACCES

/-- Mocked `readlinkat` `.transientOrResource` test. -/
private def err_readlinkat_transient : IO Unit :=
  runMockTransient "readlinkat" fun ops => ops.readlinkat none "l".toUTF8 64 >>= fun r => pure (r.map fun _ => ())

/-- Real `getdents64` `.notFound` test on an unlinked open directory (`ENOENT`). -/
private def err_getdents64_notFound : IO Unit := withTempSandbox "egd-nf" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "dead".toUTF8 0o755)
  let dfd ← assertOk "opendir" (← ops.openat none "dead".toUTF8 dirFlags 0)
  assertOk "rmdir" (← ops.unlinkat none "dead".toUTF8 true)
  assertErr "getdents64 ENOENT" (← ops.getdents64 dfd 4096) Errno.ENOENT
  safeClose ops dfd

/-- Real `getdents64` `.badFd` test (`EBADF`). -/
private def err_getdents64_badFd : IO Unit := withTempSandbox "egd-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "getdents64 EBADF" (← defaultOps.getdents64 cfd 4096) Errno.EBADF

/-- Real `getdents64` `.invalidArg` test (`EINVAL`). -/
private def err_getdents64_invalidArg : IO Unit := withTempSandbox "egd-inv" fun _ => do
  let ops := defaultOps
  let dfd ← assertOk "opendir" (← ops.openat none ".".toUTF8 dirFlags 0)
  assertErr "getdents64 0 EINVAL" (← ops.getdents64 dfd 0) Errno.EINVAL
  safeClose ops dfd

/-- Real `getdents64` `.stateConflict` test (`ENOTDIR`). -/
private def err_getdents64_stateConflict : IO Unit := withTempSandbox "egd-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open reg" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  assertErr "getdents64 ENOTDIR" (← ops.getdents64 fd 4096) Errno.ENOTDIR
  safeClose ops fd

/-- Mocked `getdents64` error test. -/
private def err_getdents64_mocked : IO Unit := withTempSandbox "egd-m" fun _ => do
  let dfd ← assertOk "opendir" (← defaultOps.openat none ".".toUTF8 dirFlags 0)
  safeClose defaultOps dfd
  runMockTransient "getdents64" fun ops => ops.getdents64 dfd 4096 >>= fun r => pure (r.map fun _ => ())

/-- Real `fchmodat` `.notFound` test (`ENOENT`). -/
private def err_fchmodat_notFound : IO Unit := withTempSandbox "efca-nf" fun _ => do
  assertErr "fchmodat ENOENT" (← defaultOps.fchmodat none "missing".toUTF8 0o644) Errno.ENOENT

/-- Real `fchmodat` `.badFd` test (`EBADF`). -/
private def err_fchmodat_badFd : IO Unit := withTempSandbox "efca-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fchmodat EBADF" (← defaultOps.fchmodat (some cfd) "x".toUTF8 0o644) Errno.EBADF

/-- Real `fchmodat` `.invalidArg` test (`EINVAL`). -/
private def err_fchmodat_invalidArg : IO Unit := withTempSandbox "efca-inv" fun _ => do
  assertErr "fchmodat EINVAL" (← defaultOps.fchmodat none (ByteArray.mk #[97, 0]) 0o644) Errno.EINVAL

/-- Real `fchmodat` `.stateConflict` test (`ENOTDIR`). -/
private def err_fchmodat_stateConflict : IO Unit := withTempSandbox "efca-sc" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "reg".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertErr "fchmodat ENOTDIR" (← ops.fchmodat none "reg/c".toUTF8 0o644) Errno.ENOTDIR

/-- Real `fchmodat` `.permissionDenied` test (`EACCES`). -/
private def err_fchmodat_permissionDenied : IO Unit := withTempSandbox "efca-pd" fun _ => do
  let ops := defaultOps
  assertOk "mkdir" (← ops.mkdirat none "d".toUTF8 0o755)
  let fd ← assertOk "open" (← ops.openat none "d/f".toUTF8 rwCreatFlags 0o644)
  safeClose ops fd
  assertOk "chmod 000" (← ops.fchmodat none "d".toUTF8 0o000)
  assertErr "fchmodat EACCES" (← ops.fchmodat none "d/f".toUTF8 0o600) Errno.EACCES

/-- Mocked `fchmodat` `.transientOrResource` test. -/
private def err_fchmodat_transient : IO Unit :=
  runMockTransient "fchmodat" fun ops => ops.fchmodat none "x".toUTF8 0o644

/-- Mocked `fchmod` error test. -/
private def err_fchmod_mocked : IO Unit := withTempSandbox "efc-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "f".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "fchmod" fun ops => ops.fchmod fd 0o644

/-- Real `fchmod` `.badFd` test (`EBADF`). -/
private def err_fchmod_badFd : IO Unit := withTempSandbox "efc-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fchmod EBADF" (← defaultOps.fchmod cfd 0o644) Errno.EBADF

/-- Mocked `flock` error test. -/
private def err_flock_mocked : IO Unit := withTempSandbox "efl-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "f".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "flock" fun ops => ops.flock fd .unlock

/-- Real `flock` `.badFd` test (`EBADF`). -/
private def err_flock_badFd : IO Unit := withTempSandbox "efl-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "flock EBADF" (← defaultOps.flock cfd .unlock) Errno.EBADF

/-- Real `flock` `.stateConflict` test (`EAGAIN` / `EWOULDBLOCK`). -/
private def err_flock_stateConflict : IO Unit := withTempSandbox "efl-sc" fun _ => do
  let ops := defaultOps
  let f1 ← assertOk "o1" (← ops.openat none "lk".toUTF8 rwCreatFlags 0o644)
  let f2 ← assertOk "o2" (← ops.openat none "lk".toUTF8 rwCreatFlags 0o644)
  assertOk "ex f1" (← ops.flock f1 (.exclusive true))
  assertErr "flock EAGAIN" (← ops.flock f2 (.exclusive true)) Errno.EAGAIN
  safeClose ops f2
  safeClose ops f1

/-- Mocked `fcntl` error test. -/
private def err_fcntl_mocked : IO Unit := withTempSandbox "efc2-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "f".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "fcntl" fun ops => ops.fcntl fd .getFl >>= fun r => pure (r.map fun _ => ())

/-- Real `fcntl` `.badFd` test (`EBADF`). -/
private def err_fcntl_badFd : IO Unit := withTempSandbox "efc2-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fcntl EBADF" (← defaultOps.fcntl cfd .getFl) Errno.EBADF

/-- Real `fcntl` `.invalidArg` test (`EINVAL`). -/
private def err_fcntl_invalidArg : IO Unit := withTempSandbox "efc2-inv" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "fc".toUTF8 rwCreatFlags 0o644)
  assertErr "fcntl addSeals EINVAL" (← ops.fcntl fd (.addSeals 0x10000000)) Errno.EINVAL
  safeClose ops fd

/-- Real `fcntl` `.permissionDenied` test (`EPERM` on `O_RDONLY` `F_ADD_SEALS`). -/
private def err_fcntl_permissionDenied : IO Unit := withTempSandbox "efc2-pd" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "fcp".toUTF8 { access := .rdonly, creat := true } 0o644)
  assertErr "fcntl addSeals EPERM" (← ops.fcntl fd (.addSeals 1)) Errno.EPERM
  safeClose ops fd

/-- Mocked `fsync` error test. -/
private def err_fsync_mocked : IO Unit := withTempSandbox "efsy-m" fun _ => do
  let fd ← assertOk "open" (← defaultOps.openat none "f".toUTF8 rwCreatFlags 0o644)
  safeClose defaultOps fd
  runMockTransient "fsync" fun ops => ops.fsync fd

/-- Real `fsync` `.badFd` test (`EBADF`). -/
private def err_fsync_badFd : IO Unit := withTempSandbox "efsy-bfd" fun _ => do
  let cfd ← closedFd defaultOps
  assertErr "fsync EBADF" (← defaultOps.fsync cfd) Errno.EBADF

/-- Mocked `getcwd` error test. -/
private def err_getcwd_mocked : IO Unit :=
  runMockTransient "getcwd" fun ops => ops.getcwd 64 >>= fun r => pure (r.map fun _ => ())

/-- Real `getcwd` `.invalidArg` test (`ERANGE` / `EINVAL`). -/
private def err_getcwd_invalidArg : IO Unit := withTempSandbox "egc-inv" fun _ => do
  assertErrOneOf "getcwd ERANGE/EINVAL" (← defaultOps.getcwd 0) [Errno.ERANGE, Errno.EINVAL]

/-- Mocked `lseek` error test. -/
private def err_lseek_mocked : IO Unit :=
  runMockTransient "lseek" fun ops => do
    let fd ← assertOk "open" (← defaultOps.openat none "ls".toUTF8 rwCreatFlags 0o644)
    let r ← ops.lseek fd 0 .seekSet
    safeClose defaultOps fd
    return r.map fun _ => ()

/-- Real `lseek` `.badFd` test (`EBADF`). -/
private def err_lseek_badFd : IO Unit := withTempSandbox "els-bfd" fun _ => do
  let fd ← closedFd defaultOps
  assertErr "lseek EBADF" (← defaultOps.lseek fd 0 .seekSet) Errno.EBADF

/-- Real `lseek` `.invalidArg` test (`EINVAL` on negative offset). -/
private def err_lseek_invalidArg : IO Unit := withTempSandbox "els-inv" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "open" (← ops.openat none "f".toUTF8 rwCreatFlags 0o644)
  assertErr "lseek EINVAL" (← ops.lseek fd (-1) .seekSet) Errno.EINVAL
  safeClose ops fd

/-- Real `lseek` `.transientOrResource` test (`ESPIPE` on FIFO). -/
private def err_lseek_transient : IO Unit := withTempSandbox "els-spipe" fun _ => do
  let rc ← Fuzz.LinuxSyscall.Env.mkfifo "p.fifo".toUTF8 0o644
  assertTrue "mkfifo" (rc == 0)
  let ops := defaultOps
  let fd ← assertOk "open fifo" (← ops.openat none "p.fifo".toUTF8 { access := .rdonly, nonblock := true } 0)
  assertErr "lseek ESPIPE" (← ops.lseek fd 0 .seekSet) Errno.ESPIPE
  safeClose ops fd

/-- Mocked `reopenReadOnly` error test. -/
private def err_reopenReadOnly_mocked : IO Unit :=
  runMockTransient "reopenReadOnly" fun ops => do
    let fd ← assertOk "open" (← defaultOps.openat none "ro".toUTF8 rwCreatFlags 0o644)
    let r ← ops.reopenReadOnly fd
    safeClose defaultOps fd
    return r.map fun _ => ()

/-- Real `reopenReadOnly` `.badFd` test (`EBADF`). -/
private def err_reopenReadOnly_badFd : IO Unit := withTempSandbox "ero-bfd" fun _ => do
  let fd ← closedFd defaultOps
  assertErr "reopenReadOnly EBADF" (← defaultOps.reopenReadOnly fd) Errno.EBADF

/-- Real `reopenReadOnly` `.stateConflict` test (`ELOOP` on `O_PATH` symlink). -/
private def err_reopenReadOnly_stateConflict : IO Unit := withTempSandbox "ero-eloop" fun _ => do
  let ops := defaultOps
  assertOk "sym" (← ops.symlinkat "t".toUTF8 none "sym".toUTF8)
  let sfd ← assertOk "open O_PATH sym" (← ops.openat none "sym".toUTF8 { path := true, nofollow := true } 0)
  assertErr "reopenReadOnly ELOOP" (← ops.reopenReadOnly sfd) Errno.ELOOP
  safeClose ops sfd

/-- Real `reopenReadOnly` `.permissionDenied` test (`EACCES` on `0o000` `O_PATH`). -/
private def err_reopenReadOnly_permissionDenied : IO Unit := withTempSandbox "ero-eacces" fun _ => do
  let ops := defaultOps
  let fd ← assertOk "creat" (← ops.openat none "c0".toUTF8 rwCreatFlags 0o644)
  assertOk "chmod 0" (← ops.fchmod fd 0o000)
  safeClose ops fd
  let pfd ← assertOk "open O_PATH" (← ops.openat none "c0".toUTF8 { path := true } 0)
  assertErr "reopenReadOnly EACCES" (← ops.reopenReadOnly pfd) Errno.EACCES
  safeClose ops pfd

/-- Real `reopenReadOnly` `.transientOrResource` test (`ENXIO` on UNIX socket `O_PATH`). -/
private def err_reopenReadOnly_transient : IO Unit := withTempSandbox "ero-enxio" fun _ => do
  let rc ← Fuzz.LinuxSyscall.Env.mksock "s.sock".toUTF8
  assertTrue "mksock" (rc == 0)
  let ops := defaultOps
  let sfd ← assertOk "open O_PATH sock" (← ops.openat none "s.sock".toUTF8 { path := true } 0)
  assertErr "reopenReadOnly ENXIO" (← ops.reopenReadOnly sfd) Errno.ENXIO
  safeClose ops sfd

/-- Mocked `dupStdio` error test. -/
private def err_dupStdio_mocked : IO Unit :=
  runMockTransient "dupStdio" fun ops => ops.dupStdio .stdin >>= fun r => pure (r.map fun _ => ())

private def runEdgeCaseReproducers : IO Unit := withTempSandbox "repro" fun _ => do
  let ops := defaultOps
  let rCreatDir ← ops.openat none "cdir".toUTF8 { access := .rdonly, creat := true, directory := true } 0o755
  assertErrOneOf "O_CREAT|O_DIRECTORY" rCreatDir [Errno.EINVAL, Errno.EISDIR]
  let fd ← assertOk "creat rw" (← ops.openat none "tr.txt".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write" (← ops.write fd "hello".toUTF8)
  safeClose ops fd
  let fdRoTr ← assertOk "O_RDONLY|O_TRUNC on 0644" (← ops.openat none "tr.txt".toUTF8 { access := .rdonly, trunc := true } 0)
  let stTr ← assertOk "stat after trunc" (← ops.fstat fdRoTr)
  assertTrue "truncated to 0" (stTr.size == 0)
  safeClose ops fdRoTr
  let _ ← assertOk "chmod 444" (← ops.fchmodat none "tr.txt".toUTF8 0o444)
  assertErr "O_RDONLY|O_TRUNC on 0444" (← ops.openat none "tr.txt".toUTF8 { access := .rdonly, trunc := true } 0) Errno.EACCES
  let unlFd ← assertOk "open before unlink" (← ops.openat none "unlinked.txt".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write unlinked" (← ops.write unlFd "keep".toUTF8)
  assertOk "unlink open file" (← ops.unlinkat none "unlinked.txt".toUTF8 false)
  let stUnl ← assertOk "fstat unlinked" (← ops.fstat unlFd)
  assertTrue "unlinked nlink=0" (stUnl.nlink == 0)
  safeClose ops unlFd
  assertOk "mkdir dead2" (← ops.mkdirat none "dead2".toUTF8 0o755)
  let deadFd ← assertOk "opendir dead2" (← ops.openat none "dead2".toUTF8 dirFlags 0)
  assertOk "rmdir dead2" (← ops.unlinkat none "dead2".toUTF8 true)
  assertErr "create under dead dir" (← ops.openat (some deadFd) "child".toUTF8 rwCreatFlags 0o644) Errno.ENOENT
  safeClose ops deadFd
  let regFd ← assertOk "open reg d" (← ops.openat none "d".toUTF8 rwCreatFlags 0o644)
  let long256 := ByteArray.mk (Array.replicate 256 (97 : UInt8))
  assertErr "readlinkat regFd + NAME_MAX+1 -> ENOTDIR" (← ops.readlinkat (some regFd) long256 8) Errno.ENOTDIR
  safeClose ops regFd
  assertErr "readlinkat closedFd + NAME_MAX+1 -> EBADF" (← ops.readlinkat (some regFd) long256 8) Errno.EBADF
  assertErr "readlinkat closedFd + empty path -> EBADF" (← ops.readlinkat (some regFd) ByteArray.empty 8) Errno.EBADF
  assertErr "openat2 closedFd + beneath&inRoot -> EBADF"
    (← ops.openat2 (some regFd) "missing".toUTF8 { flags := woFlags, mode := 0o755, resolve := { beneath := true, inRoot := true } })
    Errno.EBADF
  let tgtFd ← assertOk "creat tgt_sym" (← ops.openat none "tgt_sym".toUTF8 rwCreatFlags 0o644)
  safeClose ops tgtFd
  assertOk "symlinkat sym_tr" (← ops.symlinkat "tgt_sym".toUTF8 none "sym_tr".toUTF8)
  assertErr "openat2 sym_tr/ with O_CREAT -> EISDIR"
    (← ops.openat2 none "sym_tr/".toUTF8 { flags := { access := .rdonly, creat := true }, mode := 0o555 })
    Errno.EISDIR
  assertOk "symlinkat dangling_tr" (← ops.symlinkat "dir2/b/".toUTF8 none "dangling_tr".toUTF8)
  assertErr "openat2 dangling_tr/ with O_CREAT|noSymlinks -> EISDIR"
    (← ops.openat2 none "dangling_tr/".toUTF8
      { flags := { access := .rdwr, creat := true, trunc := true, nofollow := true, nonblock := true, cloexec := true },
        mode := 0, resolve := { noSymlinks := true } })
    Errno.EISDIR
  assertErr "renameat2 closedFd empty whiteout -> EBADF"
    (← ops.renameat2 (some regFd) ByteArray.empty none ByteArray.empty { whiteout := true })
    Errno.EBADF
  assertErr "renameat2 none empty whiteout -> ENOENT"
    (← ops.renameat2 none ByteArray.empty none ByteArray.empty { whiteout := true })
    Errno.ENOENT
  assertErr "renameat2 missing old + NAME_MAX+1 new -> ENOENT"
    (← ops.renameat2 none "missing_old".toUTF8 none long256 { noreplace := true })
    Errno.ENOENT
  assertOk "mkdirat d_excl" (← ops.mkdirat none "d_excl".toUTF8 0o755)
  assertErr "openat2 dir with !O_CREAT && O_EXCL|O_TRUNC -> EISDIR"
    (← ops.openat2 none "d_excl".toUTF8 { flags := { access := .rdwr, creat := false, excl := true, trunc := true }, mode := 0 })
    Errno.EISDIR
  let dotFd ← assertOk "openat . rdonly|directory"
    (← ops.openat none ".".toUTF8 { access := .rdonly, directory := true, cloexec := true } 0)
  let dents1 ← assertOk "getdents64 . 4096" (← ops.getdents64 dotFd 4096)
  if dents1.data.size < 48 then
    throw <| IO.userError s!"expected at least 48 dirent bytes, got {dents1.data.size}"
  let dents0 ← assertOk "getdents64 . at EOF with buf=0" (← ops.getdents64 dotFd 0)
  if dents0.data.size != 0 then
    throw <| IO.userError s!"expected 0 bytes at dirent EOF with buf=0, got {dents0.data.size}"
  safeClose ops dotFd
  assertOk "mkdirat ro_dir" (← ops.mkdirat none "ro_dir".toUTF8 0o755)
  assertOk "mkdirat ro_dir/sub_d" (← ops.mkdirat none "ro_dir/sub_d".toUTF8 0o600)
  assertOk "fchmodat ro_dir 0o555" (← ops.fchmodat none "ro_dir".toUTF8 0o555)
  assertErr "unlinkat missing in 0o555 dir -> ENOENT" (← ops.unlinkat none "ro_dir/missing".toUTF8 true) Errno.ENOENT
  assertErr "unlinkat dir/ in 0o555 dir -> EISDIR" (← ops.unlinkat none "ro_dir/sub_d/".toUTF8 false) Errno.EISDIR
  assertErr "unlinkat dir in 0o555 dir -> EACCES" (← ops.unlinkat none "ro_dir/sub_d".toUTF8 false) Errno.EACCES
  assertOk "fchmodat ro_dir 0o755" (← ops.fchmodat none "ro_dir".toUTF8 0o755)
  assertOk "symlinkat sym_c -> d_miss" (← ops.symlinkat "d_miss".toUTF8 none "sym_c".toUTF8)
  assertErr "renameat2 sym_c/ missing {exchange} -> ENOENT"
    (← ops.renameat2 none "sym_c/".toUTF8 none "missing_dir2".toUTF8 { exchange := true })
    Errno.ENOENT
  let fstatFd ← assertOk "openat fstat_eaccess"
    (← ops.openat none "fstat_eaccess".toUTF8 rwCreatFlags 0o644)
  assertErr "fstatat (some fd) empty + emptyPath + eaccess -> EINVAL"
    (← ops.fstatat (some fstatFd) ByteArray.empty { emptyPath := true, eaccess := true })
    Errno.EINVAL
  assertErr "fstatat none empty + emptyPath + eaccess -> EINVAL"
    (← ops.fstatat none ByteArray.empty { emptyPath := true, eaccess := true })
    Errno.EINVAL
  assertErr "openat2 (some regFd) /d RESOLVE_BENEATH -> EXDEV"
    (← ops.openat2 (some fstatFd) "/d".toUTF8 { flags := { access := .wronly, creat := true }, mode := 0o444, resolve := { beneath := true } })
    Errno.EXDEV
  assertErr "openat2 (some regFd) /d RESOLVE_IN_ROOT -> ENOTDIR"
    (← ops.openat2 (some fstatFd) "/d".toUTF8 { flags := { access := .wronly, creat := true }, mode := 0o444, resolve := { inRoot := true } })
    Errno.ENOTDIR
  safeClose ops fstatFd
  assertErr "fstatat (some closedFd) empty + emptyPath + eaccess -> EINVAL"
    (← ops.fstatat (some fstatFd) ByteArray.empty { emptyPath := true, eaccess := true })
    Errno.EINVAL
  assertErr "fstatat (some closedFd) empty + emptyPath -> EBADF"
    (← ops.fstatat (some fstatFd) ByteArray.empty { emptyPath := true, eaccess := false })
    Errno.EBADF
  assertErr "faccessat (some closedFd) empty + emptyPath + eaccess -> EBADF"
    (← ops.faccessat (some fstatFd) ByteArray.empty { write := true, exec := true }
      { symlinkNofollow := true, emptyPath := true, eaccess := true })
    Errno.EBADF
  assertOk "mkdirat dead_namemax_dir" (← ops.mkdirat none "dead_namemax_dir".toUTF8 0o555)
  let deadNmFd ← assertOk "openat dead_namemax_dir"
    (← ops.openat none "dead_namemax_dir".toUTF8 { access := .rdonly, cloexec := true } 0)
  assertOk "unlinkat dead_namemax_dir" (← ops.unlinkat none "dead_namemax_dir".toUTF8 true)
  assertErr "faccessat dead dir + NAME_MAX+1 -> ENOENT"
    (← ops.faccessat (some deadNmFd) long256 { read := true } {})
    Errno.ENOENT
  assertErr "mkdirat dead dir + NAME_MAX+1 -> ENOENT"
    (← ops.mkdirat (some deadNmFd) long256 0o755)
    Errno.ENOENT
  safeClose ops deadNmFd
  assertOk "mkdirat gd_post_dir" (← ops.mkdirat none "gd_post_dir".toUTF8 0o755)
  assertOk "symlinkat ./ gd_post_dir/sym0" (← ops.symlinkat "./".toUTF8 none "gd_post_dir/sym0".toUTF8)
  let gdPostFd ← assertOk "openat gd_post_dir/sym0"
    (← ops.openat none "gd_post_dir/sym0".toUTF8 { access := .rdonly, cloexec := true } 0)
  let _ ← assertOk "getdents64 gd_post_dir 48" (← ops.getdents64 gdPostFd 48)
  assertOk "symlinkat sub gd_post_dir/sym1" (← ops.symlinkat "sub".toUTF8 none "gd_post_dir/sym1".toUTF8)
  let _ ← assertOk "getdents64 gd_post_dir 16777217" (← ops.getdents64 gdPostFd 16777217)
  let gdSmallEof ← assertOk "getdents64 gd_post_dir 16 at EOF -> 0" (← ops.getdents64 gdPostFd 16)
  if gdSmallEof.data.size != 0 then
    throw <| IO.userError s!"expected 0 bytes at post-open EOF with buf=16, got {gdSmallEof.data.size}"
  safeClose ops gdPostFd
  let fl0 ← assertOk "openat flock_drop 0" (← ops.openat none "flock_drop".toUTF8 rwCreatFlags 0o644)
  let fl1 ← assertOk "openat flock_drop 1" (← ops.openat none "flock_drop".toUTF8 { access := .rdonly, trunc := true } 0o600)
  assertOk "flock 0 SH|NB" (← ops.flock fl0 (.shared true))
  assertOk "flock 1 SH|NB" (← ops.flock fl1 (.shared true))
  assertErr "flock 1 EX|NB upgrade fails EAGAIN and drops SH" (← ops.flock fl1 (.exclusive true)) Errno.EAGAIN
  assertOk "flock 0 EX|NB succeeds after fl1 upgrade drop" (← ops.flock fl0 (.exclusive true))
  safeClose ops fl0
  safeClose ops fl1
  assertOk "mkdirat self_ro_parent" (← ops.mkdirat none "self_ro_parent".toUTF8 0o755)
  assertOk "mkdirat self_ro_parent/c" (← ops.mkdirat none "self_ro_parent/c".toUTF8 0o700)
  let selfFd ← assertOk "openat self_ro_parent" (← ops.openat none "self_ro_parent".toUTF8 { access := .rdonly, directory := true } 0)
  assertOk "fchmodat self_ro_parent 0o555" (← ops.fchmodat (some selfFd) ".".toUTF8 0o555)
  assertOk "renameat2 c -> c/ on 0o555 parent succeeds"
    (← ops.renameat2 (some selfFd) "c".toUTF8 (some selfFd) "c/".toUTF8 {})
  assertOk "fchmodat self_ro_parent 0o755" (← ops.fchmodat (some selfFd) ".".toUTF8 0o755)
  safeClose ops selfFd
  assertOk "mkdirat dir_move_parent" (← ops.mkdirat none "dir_move_parent".toUTF8 0o755)
  assertOk "mkdirat dir_move_000" (← ops.mkdirat none "dir_move_000".toUTF8 0o000)
  let mvParentFd ← assertOk "openat dir_move_parent"
    (← ops.openat none "dir_move_parent".toUTF8 { access := .rdonly, cloexec := true } 0o444)
  assertErr "renameat2 0o000 dir across parents -> EACCES"
    (← ops.renameat2 none "dir_move_000".toUTF8 (some mvParentFd) "sub".toUTF8 { whiteout := true })
    Errno.EACCES
  safeClose ops mvParentFd
  assertOk "fchmodat dir_move_000 0o755" (← ops.fchmodat none "dir_move_000".toUTF8 0o755)
  assertOk "mkdirat d_slash/" (← ops.mkdirat none "d_slash/".toUTF8 0o700)
  let regSlashFd ← assertOk "openat reg_slash" (← ops.openat none "reg_slash".toUTF8 rwCreatFlags 0o700)
  safeClose ops regSlashFd
  assertErr "renameat2 reg -> existing dir with trailing slash -> ENOTDIR"
    (← ops.renameat2 none "reg_slash".toUTF8 none "d_slash/".toUTF8 {})
    Errno.ENOTDIR
  assertOk "mkdirat anc_555 0o555" (← ops.mkdirat none "anc_555".toUTF8 0o555)
  assertErr "renameat2 0o555 dir into itself -> EINVAL before EACCES"
    (← ops.renameat2 none "anc_555".toUTF8 none "anc_555/lnk/".toUTF8 {})
    Errno.EINVAL
  assertOk "fchmodat anc_555 0o755" (← ops.fchmodat none "anc_555".toUTF8 0o755)
  assertOk "symlinkat sub wo_src" (← ops.symlinkat "sub".toUTF8 none "wo_src".toUTF8)
  assertOk "renameat2 wo_src -> wo_dst whiteout"
    (← ops.renameat2 none "wo_src".toUTF8 none "wo_dst".toUTF8 { whiteout := true })
  assertOk "fchmodat wo_src 0o644" (← ops.fchmodat none "wo_src".toUTF8 0o644)
  assertErr "openat2 chmodded whiteout charDev -> EACCES"
    (← ops.openat2 none "wo_src".toUTF8 {
      flags := { access := .rdwr, excl := true, nonblock := true, cloexec := true },
      mode := 0,
      resolve := { beneath := true } })
    Errno.EACCES
  assertOk "mkdirat anc_sub" (← ops.mkdirat none "anc_sub".toUTF8 0o700)
  assertOk "symlinkat missing anc_sub/a" (← ops.symlinkat "missing".toUTF8 none "anc_sub/a".toUTF8)
  assertErr "renameat2 anc_sub/a -> anc_sub -> ENOTEMPTY before EISDIR"
    (← ops.renameat2 none "anc_sub/a".toUTF8 none "anc_sub".toUTF8 {})
    Errno.ENOTEMPTY
  assertOk "symlinkat dir2/y nofollow_dir_lnk" (← ops.symlinkat "dir2/y".toUTF8 none "nofollow_dir_lnk".toUTF8)
  assertErr "openat2 symlink nofollow + directory + resolve.noSymlinks -> ENOTDIR"
    (← ops.openat2 none "nofollow_dir_lnk".toUTF8 {
      flags := { access := .rdwr, trunc := true, nofollow := true, directory := true, cloexec := true },
      mode := 0,
      resolve := { noXdev := true, noMagiclinks := true, noSymlinks := true } })
    Errno.ENOTDIR

private def runHardenedReproducers : IO Unit := withTempSandbox "repro-h" fun _ => do
  let ops := defaultOps
  assertOk "mkdirat ro_ren" (← ops.mkdirat none "ro_ren".toUTF8 0o755)
  assertOk "symlinkat ./ ro_ren/c" (← ops.symlinkat "./".toUTF8 none "ro_ren/c".toUTF8)
  assertOk "mkdirat ro_ren/d" (← ops.mkdirat none "ro_ren/d".toUTF8 0o600)
  assertOk "fchmodat ro_ren 0o555" (← ops.fchmodat none "ro_ren".toUTF8 0o555)
  assertErr "renameat2 0o555 dir -> symlink/ whiteout -> EACCES"
    (← ops.renameat2 none "ro_ren/d".toUTF8 none "ro_ren/c/".toUTF8 { whiteout := true })
    Errno.EACCES
  assertErr "renameat2 0o555 dir -> symlink/ exchange -> ENOTDIR"
    (← ops.renameat2 none "ro_ren/d".toUTF8 none "ro_ren/c/".toUTF8 { exchange := true })
    Errno.ENOTDIR
  assertOk "fchmodat ro_ren 0o755" (← ops.fchmodat none "ro_ren".toUTF8 0o755)
  let trPrep ← assertOk "openat tr.txt" (← ops.openat none "tr.txt".toUTF8 rwCreatFlags 0o644)
  safeClose ops trPrep
  assertOk "symlinkat dangling_tr" (← ops.symlinkat "dir2/b/".toUTF8 none "dangling_tr".toUTF8)
  assertErr "openat ./ O_CREAT|O_EXCL -> EEXIST"
    (← ops.openat none "./".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EEXIST
  assertErr "openat . O_CREAT|O_EXCL -> EEXIST"
    (← ops.openat none ".".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EEXIST
  assertOk "mkdirat sub_excl" (← ops.mkdirat none "sub_excl".toUTF8 0o755)
  assertErr "openat sub_excl/./ O_CREAT|O_EXCL -> EEXIST"
    (← ops.openat none "sub_excl/./".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EEXIST
  assertErr "openat sub_excl/../ O_CREAT|O_EXCL -> EEXIST"
    (← ops.openat none "sub_excl/../".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EEXIST
  assertErr "openat sub_excl/ O_CREAT|O_EXCL -> EISDIR"
    (← ops.openat none "sub_excl/".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EISDIR
  assertErr "openat missing_excl/ O_CREAT|O_EXCL -> EISDIR"
    (← ops.openat none "missing_excl/".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EISDIR
  assertErr "openat dangling_tr O_CREAT|O_EXCL -> EEXIST"
    (← ops.openat none "dangling_tr".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    Errno.EEXIST
  let mut dotPrefix := ""
  for _ in [:1000] do
    dotPrefix := dotPrefix ++ "./"
  let deepReg ← assertOk "openat 1000x ./ + tr.txt"
    (← ops.openat none (dotPrefix ++ "tr.txt").toUTF8 roFlags 0)
  let _ ← assertOk "fstatat 1000x ./ + tr.txt"
    (← ops.fstatat none (dotPrefix ++ "tr.txt").toUTF8 {})
  safeClose ops deepReg
  let appPrep ← assertOk "openat app0.txt" (← ops.openat none "app0.txt".toUTF8 rwCreatFlags 0o644)
  let nwPrep ← assertOk "write ab" (← ops.write appPrep "ab".toUTF8)
  assertTrue "write ab == 2" (nwPrep == 2)
  let nwZero ← assertOk "write empty == 0" (← ops.write appPrep ByteArray.empty)
  assertTrue "write empty == 0" (nwZero == 0)
  safeClose ops appPrep
  let appFd ← assertOk "openat app0.txt O_RDWR|O_APPEND"
    (← ops.openat none "app0.txt".toUTF8 { access := .rdwr, append := true } 0)
  let nwApp0 ← assertOk "0-byte O_APPEND write" (← ops.write appFd ByteArray.empty)
  assertTrue "0-byte O_APPEND write == 0" (nwApp0 == 0)
  let rdAfterApp0 ← assertOk "read after 0-byte O_APPEND write" (← ops.read appFd 2)
  assertTrue "0-byte O_APPEND write does not advance offset" (rdAfterApp0 == "ab".toUTF8)
  safeClose ops appFd
  assertOk "mkdirat gd_empty" (← ops.mkdirat none "gd_empty".toUTF8 0o755)
  let gdE ← assertOk "openat gd_empty" (← ops.openat none "gd_empty".toUTF8 dirFlags 0)
  assertErr "getdents64 before dots with buf=16 -> EINVAL" (← ops.getdents64 gdE 16) Errno.EINVAL
  safeClose ops gdE
  assertOk "mkdirat gd_mid" (← ops.mkdirat none "gd_mid".toUTF8 0o755)
  let gdMidA ← assertOk "openat gd_mid/a" (← ops.openat none "gd_mid/a".toUTF8 rwCreatFlags 0o644)
  safeClose ops gdMidA
  let gdMidFd ← assertOk "openat gd_mid" (← ops.openat none "gd_mid".toUTF8 dirFlags 0)
  let chunk1 ← assertOk "getdents64 gd_mid buf=24" (← ops.getdents64 gdMidFd 24)
  assertTrue "getdents64 gd_mid chunk1 >= 24" (chunk1.data.size >= 24)
  assertOk "unlinkat gd_mid/a mid-stream" (← ops.unlinkat none "gd_mid/a".toUTF8 false)
  let mut sawEof := false
  for _ in [:8] do
    let ch ← assertOk "getdents64 gd_mid drain" (← ops.getdents64 gdMidFd 4096)
    if ch.data.isEmpty then
      sawEof := true
      break
  assertTrue "getdents64 gd_mid reached EOF" sawEof
  let gdMidB ← assertOk "openat gd_mid/after_eof" (← ops.openat none "gd_mid/after_eof".toUTF8 rwCreatFlags 0o644)
  safeClose ops gdMidB
  let afterEof ← assertOk "getdents64 gd_mid after EOF" (← ops.getdents64 gdMidFd 4096)
  assertTrue "getdents64 stays at EOF after creat" afterEof.data.isEmpty
  safeClose ops gdMidFd
  assertOk "mkdirat gd_long" (← ops.mkdirat none "gd_long".toUTF8 0o755)
  let gdLongF ← assertOk "openat gd_long/very_long_entry_name_for_einval_probe"
    (← ops.openat none "gd_long/very_long_entry_name_for_einval_probe".toUTF8 rwCreatFlags 0o644)
  safeClose ops gdLongF
  let gdLongFd ← assertOk "openat gd_long" (← ops.openat none "gd_long".toUTF8 dirFlags 0)
  let mut gotSmallBufErr := false
  for _ in [:4] do
    match ← ops.getdents64 gdLongFd 24 with
    | .error e =>
      assertTrue "getdents64 small buf EINVAL" (e == Errno.EINVAL)
      gotSmallBufErr := true
      break
    | .ok bs =>
      if bs.data.isEmpty then break
  assertTrue "getdents64 long entry triggered EINVAL on buf=24" gotSmallBufErr
  safeClose ops gdLongFd
  assertErr "symlinkat missing/ -> ENOENT" (← ops.symlinkat "t".toUTF8 none "sym_missing/".toUTF8) Errno.ENOENT
  assertErr "symlinkat existing sub_excl/ -> EEXIST" (← ops.symlinkat "t".toUTF8 none "sub_excl/".toUTF8) Errno.EEXIST
  assertErr "symlinkat . -> EEXIST" (← ops.symlinkat "t".toUTF8 none ".".toUTF8) Errno.EEXIST
  assertErr "unlinkat . false -> EISDIR" (← ops.unlinkat none ".".toUTF8 false) Errno.EISDIR
  assertErr "unlinkat ./ true -> EINVAL" (← ops.unlinkat none "./".toUTF8 true) Errno.EINVAL
  assertErr "renameat2 . x -> EBUSY" (← ops.renameat2 none ".".toUTF8 none "rn_x".toUTF8 {}) Errno.EBUSY
  assertErr "renameat2 sub_excl . NOREPLACE -> EEXIST"
    (← ops.renameat2 none "sub_excl".toUTF8 none ".".toUTF8 { noreplace := true }) Errno.EEXIST

private def runMutantKillers : IO Unit := withTempSandbox "repro-m" fun _ => do
  let ops := defaultOps
  let stickyFd ← assertOk "openat sticky.txt" (← ops.openat none "sticky.txt".toUTF8 rwCreatFlags 0o644)
  assertOk "fchmod sticky 0o1755" (← ops.fchmod stickyFd 0o1755)
  let stSticky ← assertOk "fstat sticky" (← ops.fstat stickyFd)
  assertTrue "sticky 0o1755 preserved" ((stSticky.mode &&& 0o7777) == 0o1755)
  assertTrue "stat ino/dev nonzero" (stSticky.ino != 0 && stSticky.dev != 0)
  assertOk "fchmod sticky 0o7000" (← ops.fchmod stickyFd 0o7000)
  let stSpec ← assertOk "fstat 0o7000" (← ops.fstat stickyFd)
  assertTrue "0o7000 bits preserved" ((stSpec.mode &&& 0o7777) == 0o7000)
  assertErr "fcntl addSeals 0 on rdwr -> EPERM" (← ops.fcntl stickyFd (.addSeals 0)) Errno.EPERM
  assertErr "fcntl addSeals 1 on rdwr -> EPERM" (← ops.fcntl stickyFd (.addSeals 1)) Errno.EPERM
  assertErr "fcntl addSeals 0x10000000 on rdwr -> EINVAL" (← ops.fcntl stickyFd (.addSeals 0x10000000)) Errno.EINVAL
  let flFd1 ← assertOk "openat fl_check append=T nonblock=F clo=F"
    (← ops.openat none "fl_check.txt".toUTF8 { access := .rdwr, creat := true, append := true, nonblock := false, cloexec := false } 0o644)
  let fl1Val ← assertOk "getFl 1" (← ops.fcntl flFd1 .getFl)
  assertTrue "O_APPEND bit 5 set & O_NONBLOCK bit 8 clear"
    ((fl1Val &&& ((1 : UInt32) <<< 5)) != 0 && (fl1Val &&& ((1 : UInt32) <<< 8)) == 0 && (fl1Val &&& 3) == 2)
  let fd1Val ← assertOk "getFd 1" (← ops.fcntl flFd1 .getFd)
  assertTrue "cloexec=false -> getFd == 0" (fd1Val == 0)
  let _ ← assertOk "setFl nonblock=T append=F" (← ops.fcntl flFd1 (.setFl true false))
  let fl2Val ← assertOk "getFl 2" (← ops.fcntl flFd1 .getFl)
  assertTrue "nonblock set & append cleared"
    ((fl2Val &&& ((1 : UInt32) <<< 8)) != 0 && (fl2Val &&& ((1 : UInt32) <<< 5)) == 0)
  let _ ← assertOk "setFl nonblock=F append=T" (← ops.fcntl flFd1 (.setFl false true))
  let fl3Val ← assertOk "getFl 3" (← ops.fcntl flFd1 .getFl)
  assertTrue "nonblock cleared & append set"
    ((fl3Val &&& ((1 : UInt32) <<< 8)) == 0 && (fl3Val &&& ((1 : UInt32) <<< 5)) != 0)
  let _ ← assertOk "setFl nonblock=F append=F" (← ops.fcntl flFd1 (.setFl false false))
  let fl4Val ← assertOk "getFl 4" (← ops.fcntl flFd1 .getFl)
  assertTrue "both cleared" ((fl4Val &&& (((1 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 5))) == 0)
  let _ ← assertOk "setFd true" (← ops.fcntl flFd1 (.setFd true))
  let fd2Val ← assertOk "getFd 2" (← ops.fcntl flFd1 .getFd)
  assertTrue "setFd true -> getFd == 1" (fd2Val == 1)
  let _ ← assertOk "setFd false" (← ops.fcntl flFd1 (.setFd false))
  let fd3Val ← assertOk "getFd 3" (← ops.fcntl flFd1 .getFd)
  assertTrue "setFd false -> getFd == 0" (fd3Val == 0)
  safeClose ops flFd1
  safeClose ops stickyFd
  let flFd2 ← assertOk "openat fl_check nonblock=T clo=T"
    (← ops.openat none "fl_check.txt".toUTF8 { access := .rdonly, nonblock := true, cloexec := true } 0)
  let fl5Val ← assertOk "getFl 5" (← ops.fcntl flFd2 .getFl)
  assertTrue "rdonly+nonblock"
    ((fl5Val &&& 3) == 0 && (fl5Val &&& ((1 : UInt32) <<< 8)) != 0 && (fl5Val &&& ((1 : UInt32) <<< 5)) == 0)
  let fd5Val ← assertOk "getFd 5" (← ops.fcntl flFd2 .getFd)
  assertTrue "cloexec=true -> getFd == 1" (fd5Val == 1)
  safeClose ops flFd2
  let accF ← assertOk "openat acc_bits.txt" (← ops.openat none "acc_bits.txt".toUTF8 rwCreatFlags 0o644)
  safeClose ops accF
  assertOk "fchmodat acc_bits 0o400" (← ops.fchmodat none "acc_bits.txt".toUTF8 0o400)
  assertOk "faccessat R_OK on 0400" (← ops.faccessat none "acc_bits.txt".toUTF8 { read := true } {})
  assertErr "faccessat W_OK on 0400 -> EACCES" (← ops.faccessat none "acc_bits.txt".toUTF8 { write := true } {}) Errno.EACCES
  assertErr "faccessat X_OK on 0400 -> EACCES" (← ops.faccessat none "acc_bits.txt".toUTF8 { exec := true } {}) Errno.EACCES
  assertOk "fchmodat acc_bits 0o200" (← ops.fchmodat none "acc_bits.txt".toUTF8 0o200)
  assertErr "faccessat R_OK on 0200 -> EACCES" (← ops.faccessat none "acc_bits.txt".toUTF8 { read := true } {}) Errno.EACCES
  assertOk "faccessat W_OK|AT_EACCESS on 0200" (← ops.faccessat none "acc_bits.txt".toUTF8 { write := true } { eaccess := true })
  assertOk "fchmodat acc_bits 0o100" (← ops.fchmodat none "acc_bits.txt".toUTF8 0o100)
  assertOk "faccessat X_OK on 0100" (← ops.faccessat none "acc_bits.txt".toUTF8 { exec := true } {})
  assertOk "symlinkat acc_bits.txt -> acc_lnk" (← ops.symlinkat "acc_bits.txt".toUTF8 none "acc_lnk".toUTF8)
  let stFollow ← assertOk "fstatat acc_lnk follow" (← ops.fstatat none "acc_lnk".toUTF8 {})
  assertTrue "fstatat follows symlink to reg" (stFollow.kind == .reg && stFollow.ino != stSticky.ino)
  let stNoFollow ← assertOk "fstatat acc_lnk nofollow" (← ops.fstatat none "acc_lnk".toUTF8 { symlinkNofollow := true })
  assertTrue "fstatat nofollow sees symlink" (stNoFollow.kind == .symlink && stNoFollow.ino != stFollow.ino)
  assertOk "symlinkat dangling_m" (← ops.symlinkat "dir2/b/".toUTF8 none "dangling_m".toUTF8)
  assertOk "faccessat dangling_m AT_SYMLINK_NOFOLLOW" (← ops.faccessat none "dangling_m".toUTF8 {} { symlinkNofollow := true })
  let cwdFull ← assertOk "getcwd 4096" (← ops.getcwd 4096)
  let _ ← assertOk "getcwd exact len+1" (← ops.getcwd (cwdFull.data.size + 1).toUInt32)
  assertErr "getcwd exact len -> ERANGE" (← ops.getcwd cwdFull.data.size.toUInt32) Errno.ERANGE
  let _ ← assertOk "getcwd > 16MiB clamped" (← ops.getcwd (16 * 1024 * 1024 + 1234))
  let _ ← assertOk "readlinkat > 16MiB clamped" (← ops.readlinkat none "acc_lnk".toUTF8 (16 * 1024 * 1024 + 1234))
  let gdClampFd ← assertOk "openat . for clamp" (← ops.openat none ".".toUTF8 dirFlags 0)
  let _ ← assertOk "getdents64 > 16MiB clamped" (← ops.getdents64 gdClampFd (16 * 1024 * 1024 + 1234))
  safeClose ops gdClampFd
  let wrClampFd ← assertOk "openat app_m.txt for clamp" (← ops.openat none "app_m.txt".toUTF8 rwCreatFlags 0o644)
  let _ ← assertOk "write app_m" (← ops.write wrClampFd "ab".toUTF8)
  safeClose ops wrClampFd
  let rdClampFd ← assertOk "openat app_m.txt for clamp" (← ops.openat none "app_m.txt".toUTF8 roFlags 0)
  let rdClamp ← assertOk "read > 16MiB clamped" (← ops.read rdClampFd (16 * 1024 * 1024 + 1234))
  assertTrue "read clamped reads ab" (rdClamp == "ab".toUTF8)
  safeClose ops rdClampFd
  assertErr "fstatat (some closedFd) / returns EBADF"
    (← ops.fstatat (some rdClampFd) "/".toUTF8 {}) Errno.EBADF
  let stAbsRoot ← assertOk "fstatat none / succeeds" (← ops.fstatat none "/".toUTF8 {})
  assertTrue "root is dir" (stAbsRoot.kind == .dir)
  let heap4096 := ByteArray.mk (Array.replicate 4096 (97 : UInt8))
  assertErr "openat 4096-byte heap path -> ENAMETOOLONG" (← ops.openat none heap4096 roFlags 0) Errno.ENAMETOOLONG
  let heapNul := ByteArray.mk ((Array.replicate 4095 (97 : UInt8)).push 0)
  assertErr "openat 4096-byte heap path with NUL -> EINVAL" (← ops.openat none heapNul roFlags 0) Errno.EINVAL

private def decodeProbeFdKind (code : UInt32) : FileKind × Option SpecialDevKind :=
  match code with
  | 1 => (.reg, none)
  | 2 => (.dir, none)
  | 4 => (.fifo, none)
  | 5 => (.socket, none)
  | 31 => (.charDev, some .nullDev)
  | 32 => (.charDev, some .zeroDev)
  | 33 => (.charDev, some .fullDev)
  | 30 => (.charDev, none)
  | 6 => (.other, none)
  | _ => (.charDev, some .nullDev)

private def stepModelCheck (label : String) (st : FilesState) (req : FilesReq) (out : FilesOutcome) : IO FilesState := do
  match allowedStep st req out with
  | some s' => return s'
  | none => throw (IO.userError s!"Files model/kernel mismatch at {label}: req={repr req} out={repr out}")

private def errOrOkOut {α : Type} (r : Except Errno α) (toOut : α → FilesOutcome) : FilesOutcome :=
  match r with
  | .ok v => toOut v
  | .error e => .err e

/-- Deterministic environment reproducers covering special files, `/proc`/`/sys`, `umask`, hardlinks, cross-mount, and `ext4` `getdents64`. -/
private def markCwdUnlinked (st : FilesState) : FilesState :=
  match assocGet st.inodes st.cwdIno with
  | some cvn =>
    { st with
      cwdPath := .unbound st.cwdPath.bytes
      inodes := assocSet st.inodes st.cwdIno { cvn with nlink := 0 } }
  | none => { st with cwdPath := .unbound st.cwdPath.bytes }

private def markCwdUnowned (st : FilesState) : FilesState :=
  match assocGet st.inodes st.cwdIno with
  | some cvn =>
    { st with inodes := assocSet st.inodes st.cwdIno { cvn with owner := { cvn.owner with ownedByUid := false } } }
  | none => st

private def markChildUnowned (st : FilesState) (name : ByteArray) : FilesState :=
  match assocGet st.inodes st.cwdIno >>= (fun cvn => bytesAssocGet cvn.children name) with
  | some oino =>
    match assocGet st.inodes oino with
    | some ovn => { st with inodes := assocSet st.inodes oino { ovn with owner := { ovn.owner with ownedByUid := false } } }
    | none => st
  | none => st

private def runEnvProcAndDevChecks (ops : FilesOps) (st0 : FilesState) : IO FilesState := do
  let mut st := st0
  let stProcRes ← ops.openat none "/proc/self/status".toUTF8 roFlags 0
  let hidProc := st.nextHid
  st ← stepModelCheck "open /proc/self/status" st (.openat none "/proc/self/status".toUTF8 roFlags 0) (errOrOkOut stProcRes fun _ => .opened hidProc)
  match stProcRes with
  | .ok pfd =>
    let r1 ← ops.read pfd 4096
    st ← stepModelCheck "read /proc/self/status" st (.read hidProc 4096) (errOrOkOut r1 .bytes)
    let w1 ← ops.write pfd "x".toUTF8
    st ← stepModelCheck "write /proc/self/status" st (.write hidProc "x".toUTF8) (errOrOkOut w1 .u32)
    let fs1 ← ops.fsync pfd
    st ← stepModelCheck "fsync /proc/self/status" st (.fsync hidProc) (errOrOkOut fs1 fun _ => .unit)
    let c1 ← ops.close pfd
    st ← stepModelCheck "close /proc/self/status" st (.close hidProc) (errOrOkOut c1 fun _ => .unit)
  | .error e => throw (IO.userError s!"expected /proc/self/status open ok, got {e}")

  let rMagic ← ops.openat2 none "/proc/self/exe".toUTF8 { flags := roFlags, resolve := { noMagiclinks := true } }
  assertErr "openat2 noMagiclinks /proc/self/exe" rMagic Errno.ELOOP
  st ← stepModelCheck "noMagiclinks" st (.openat2 none "/proc/self/exe".toUTF8 { flags := roFlags, resolve := { noMagiclinks := true } }) (errOrOkOut rMagic fun _ => .opened st.nextHid)

  let rXdev ← ops.openat2 none "/proc/self/status".toUTF8 { flags := roFlags, resolve := { noXdev := true } }
  assertErr "openat2 noXdev /proc/self/status" rXdev Errno.EXDEV
  st ← stepModelCheck "noXdev" st (.openat2 none "/proc/self/status".toUTF8 { flags := roFlags, resolve := { noXdev := true } }) (errOrOkOut rXdev fun _ => .opened st.nextHid)

  let rExeWr ← ops.openat none "/proc/self/exe".toUTF8 woFlags 0
  st ← stepModelCheck "open /proc/self/exe wo" st (.openat none "/proc/self/exe".toUTF8 woFlags 0) (errOrOkOut rExeWr fun _ => .opened st.nextHid)
  if let .ok efd := rExeWr then
    safeClose ops efd

  let rMkProc ← ops.mkdirat none "/proc/self/nope".toUTF8 0o755
  st ← stepModelCheck "mkdir /proc/self/nope" st (.mkdirat none "/proc/self/nope".toUTF8 0o755) (errOrOkOut rMkProc fun _ => .unit)

  let rFull ← ops.openat none "/dev/full".toUTF8 { access := .rdwr } 0
  let hidFull := st.nextHid
  st ← stepModelCheck "open /dev/full" st (.openat none "/dev/full".toUTF8 { access := .rdwr } 0) (errOrOkOut rFull fun _ => .opened hidFull)
  match rFull with
  | .ok ffd =>
    let zBytes ← ops.read ffd 8
    st ← stepModelCheck "read /dev/full" st (.read hidFull 8) (errOrOkOut zBytes .bytes)
    let wZero ← ops.write ffd ByteArray.empty
    assertErr "write 0 /dev/full -> ENOSPC" wZero Errno.ENOSPC
    st ← stepModelCheck "write 0 /dev/full" st (.write hidFull ByteArray.empty) (errOrOkOut wZero .u32)
    let fsFull ← ops.fsync ffd
    st ← stepModelCheck "fsync /dev/full" st (.fsync hidFull) (errOrOkOut fsFull fun _ => .unit)
    let _ ← ops.close ffd
    st ← stepModelCheck "close /dev/full" st (.close hidFull) .unit
  | .error e => throw (IO.userError s!"expected /dev/full open ok, got {e}")
  return st

private def runEnvFifoAndUmaskChecks
    (ops : FilesOps) (st0 : FilesState) (savedMask : Mode) (rlMax : UInt64) : IO FilesState := do
  let mut st := st0
  let rSock ← ops.openat none "env.sock".toUTF8 { access := .rdonly, nonblock := true } 0
  assertErr "open socket -> ENXIO" rSock Errno.ENXIO
  st ← stepModelCheck "open socket" st (.openat none "env.sock".toUTF8 { access := .rdonly, nonblock := true } 0) (errOrOkOut rSock fun _ => .opened st.nextHid)

  let rFifoNoRd ← ops.openat none "env.fifo".toUTF8 { access := .wronly, nonblock := true } 0
  assertErr "open fifo wronly nonblock no reader -> ENXIO" rFifoNoRd Errno.ENXIO
  st ← stepModelCheck "fifo wronly ENXIO" st (.openat none "env.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (errOrOkOut rFifoNoRd fun _ => .opened st.nextHid)

  let rFifoRd ← ops.openat none "env.fifo".toUTF8 { access := .rdonly, nonblock := true } 0
  let hidFifoRd := st.nextHid
  st ← stepModelCheck "open fifo rd" st (.openat none "env.fifo".toUTF8 { access := .rdonly, nonblock := true } 0) (errOrOkOut rFifoRd fun _ => .opened hidFifoRd)
  let rFifoWr ← ops.openat none "env.fifo".toUTF8 { access := .wronly, nonblock := true } 0
  let hidFifoWr := st.nextHid
  st ← stepModelCheck "open fifo wr" st (.openat none "env.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (errOrOkOut rFifoWr fun _ => .opened hidFifoWr)
  match rFifoRd, rFifoWr with
  | .ok frd, .ok fwr =>
    let rEmpty ← ops.read frd 16
    assertErr "fifo empty nonblock read -> EAGAIN" rEmpty Errno.EAGAIN
    st ← stepModelCheck "fifo EAGAIN" st (.read hidFifoRd 16) (errOrOkOut rEmpty .bytes)
    let wFifo ← ops.write fwr "hi".toUTF8
    st ← stepModelCheck "fifo write" st (.write hidFifoWr "hi".toUTF8) (errOrOkOut wFifo .u32)
    let stFifo ← assertOk "fstat fifo after write" (← ops.fstat fwr)
    assertTrue "fifo keeps 06755 bits" ((stFifo.mode &&& 0o7777) == 0o6755)
    st ← stepModelCheck "fstat fifo" st (.fstat hidFifoWr) (.statted stFifo)
    let rData ← ops.read frd 16
    let gotHi ← assertOk "fifo read hi" rData
    assertTrue "fifo read hi bytes" (gotHi == "hi".toUTF8)
    st ← stepModelCheck "fifo read hi" st (.read hidFifoRd 16) (.bytes gotHi)
    let fsFifo ← ops.fsync fwr
    st ← stepModelCheck "fifo fsync" st (.fsync hidFifoWr) (errOrOkOut fsFifo fun _ => .unit)
    let _ ← ops.close frd
    st ← stepModelCheck "close fifo rd" st (.close hidFifoRd) .unit
    let wBroken ← ops.write fwr "x".toUTF8
    assertErr "fifo broken write -> EPIPE" wBroken Errno.EPIPE
    st ← stepModelCheck "fifo EPIPE" st (.write hidFifoWr "x".toUTF8) (errOrOkOut wBroken .u32)
    let _ ← ops.close fwr
    st ← stepModelCheck "close fifo wr" st (.close hidFifoWr) .unit
  | _, _ => throw (IO.userError "failed to open fifo rd/wr")

  let _ ← Fuzz.LinuxSyscall.Env.umask 0o200
  let rUm ← ops.openat none "um_file".toUTF8 rwCreatFlags 0o644
  let hidUm := st.nextHid
  st ← stepModelCheck "umask file open" st (.openat none "um_file".toUTF8 rwCreatFlags 0o644) (errOrOkOut rUm fun _ => .opened hidUm)
  match rUm with
  | .ok ufd =>
    let stUm ← assertOk "fstat um_file" (← ops.fstat ufd)
    assertTrue "umask 0200 clears owner write bit" ((stUm.mode &&& 0o777) == 0o444)
    st ← stepModelCheck "fstat um_file" st (.fstat hidUm) (.statted stUm)
    let _ ← ops.close ufd
    st ← stepModelCheck "close um_file" st (.close hidUm) .unit
  | .error e => throw (IO.userError s!"um_file failed: {e}")

  let rSgidSub ← ops.mkdirat none "sgid_dir/sub".toUTF8 0o755
  st ← stepModelCheck "mkdir sgid_dir/sub" st (.mkdirat none "sgid_dir/sub".toUTF8 0o755) (errOrOkOut rSgidSub fun _ => .unit)
  let stSgidSub ← assertOk "fstatat sgid_dir/sub" (← ops.fstatat none "sgid_dir/sub".toUTF8 {})
  assertTrue "sgid inherited on child dir" ((stSgidSub.mode &&& 0o2000) == 0o2000)
  st ← stepModelCheck "fstatat sgid_dir/sub" st (.fstatat none "sgid_dir/sub".toUTF8 {}) (.statted stSgidSub)

  let _ ← Fuzz.LinuxSyscall.Env.umask savedMask
  assertEqErrno "setrlimit fsize 16" (← Fuzz.LinuxSyscall.Env.setRlimitFsize 16 rlMax true) 0
  let rLimFd ← assertOk "open rlim_f" (← ops.openat none "rlim_f".toUTF8 rwCreatFlags 0o644)
  let wPart ← assertOk "write to RLIMIT_FSIZE" (← ops.write rLimFd (ByteArray.mk (Array.replicate 64 (65 : UInt8))))
  assertTrue "partial write bounded by RLIMIT_FSIZE" (wPart == 16)
  let rEfbig ← ops.write rLimFd (ByteArray.mk (Array.replicate 16 (66 : UInt8)))
  assertErr "write past RLIMIT_FSIZE -> EFBIG" rEfbig Errno.EFBIG
  safeClose ops rLimFd
  return st

private def runEnvCrossAndDeadCwdChecks
    (ops : FilesOps) (dir ext4Dir : System.FilePath) (canVarTmp : Bool)
    (rlCur rlMax : UInt64) (st0 : FilesState) : IO Unit := do
  let _ ← Fuzz.LinuxSyscall.Env.setRlimitFsize rlCur rlMax false
  let mut st := st0
  if canVarTmp then
    let crossDst := (ext4Dir / "moved").toString.toUTF8
    let rExdev ← ops.renameat2 none "hl_src".toUTF8 none crossDst {}
    assertErr "cross-mount renameat2 -> EXDEV" rExdev Errno.EXDEV
    st ← stepModelCheck "cross-mount renameat2" st (.renameat2 none "hl_src".toUTF8 none crossDst {}) (errOrOkOut rExdev fun _ => .unit)

    let longS := ByteArray.mk (Array.replicate 255 (115 : UInt8))
    let ext4DirBytes := ext4Dir.toString.toUTF8
    let ext4DirFd ← assertOk "open ext4Dir" (← ops.openat none ext4DirBytes dirFlags 0)
    let lf ← assertOk "open 255-s on ext4" (← ops.openat (some ext4DirFd) longS rwCreatFlags 0o644)
    safeClose ops lf
    safeClose ops ext4DirFd
    let ext4ScanFd ← assertOk "open ext4Dir scan" (← ops.openat none ext4DirBytes dirFlags 0)
    let gdExt4 ← ops.getdents64 ext4ScanFd 24
    let mut ext4St := FilesState.withSeededTree {
      cwdPath := ext4DirBytes
      cwdBound := true
      mountProfiles := [(0, { supportsSeals := false })]
      cwdEntries := [{ name := longS, kind := .reg, mode := 0o644, modeExact := true }]
    }
    let hidScan := ext4St.nextHid
    ext4St ← stepModelCheck "open ext4 scan" ext4St (.openat none ".".toUTF8 dirFlags 0) (.opened hidScan)
    let _ ← stepModelCheck "getdents64 255-s small buf on ext4" ext4St (.getdents64 hidScan 24) (errOrOkOut gdExt4 .bytes)
    safeClose ops ext4ScanFd

  let deadDir := dir / "dead_cwd"
  IO.FS.createDir deadDir
  IO.Process.setCurrentDir deadDir
  IO.FS.removeDir deadDir
  let rDeadCwd ← ops.getcwd 4096
  assertErr "getcwd unlinked cwd -> ENOENT" rDeadCwd Errno.ENOENT
  let deadSt := markCwdUnlinked (FilesState.withSeededTree {
    cwdPath := deadDir.toString.toUTF8
    cwdBound := false
  })
  let _ ← stepModelCheck "getcwd unlinked cwd" deadSt (.getcwd 4096) (errOrOkOut rDeadCwd .bytes)
  IO.Process.setCurrentDir dir

/-- Run environment generalization reproducers across `/proc/self`, `/dev/full`, FIFOs, sockets, `umask`, `RLIMIT_FSIZE`, cross-mount `renameat2`, and unlinked CWD. -/
def runEnvGeneralizationReproducers : IO Unit := withTempSandbox "env-gen" fun dir => do
  let ops := defaultOps
  Fuzz.LinuxSyscall.Env.ignoreSigpipe
  let dirStr := (← IO.FS.realPath dir).toString
  let dirBytes := dirStr.toUTF8
  let in0 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 0
  let out1 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 1
  let err2 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 2
  let sealsOk ← Fuzz.LinuxSyscall.Env.supportsSeals dirBytes
  let savedMask ← Fuzz.LinuxSyscall.Env.umask 0o022
  let rlCur ← Fuzz.LinuxSyscall.Env.getRlimitFsizeCur
  let rlMax ← Fuzz.LinuxSyscall.Env.getRlimitFsizeMax
  let varTmpBase : System.FilePath := "/var/tmp"
  let canVarTmp ← do
    if !(← varTmpBase.pathExists) then pure false
    else
      let dShm ← Fuzz.LinuxSyscall.Env.statDev dirBytes
      let dVt ← Fuzz.LinuxSyscall.Env.statDev varTmpBase.toString.toUTF8
      pure (dShm != 0 && dVt != 0 && dShm != dVt)
  let pid ← Fuzz.LinuxSyscall.Env.getPid
  let ext4Dir := varTmpBase / s!"leanswe-files-ext4-{pid}"
  if canVarTmp then
    if ← ext4Dir.pathExists then IO.FS.removeDirAll ext4Dir
    IO.FS.createDirAll ext4Dir
  try
    assertEqErrno "mkfifo env.fifo" (← Fuzz.LinuxSyscall.Env.mkfifo "env.fifo".toUTF8 0o644) 0
    assertEqErrno "chmod env.fifo 06755" (← Fuzz.LinuxSyscall.Env.chmod "env.fifo".toUTF8 0o6755) 0
    assertEqErrno "mksock env.sock" (← Fuzz.LinuxSyscall.Env.mksock "env.sock".toUTF8) 0
    let hlSrc ← assertOk "open hl_src" (← ops.openat none "hl_src".toUTF8 rwCreatFlags 0o644)
    let _ ← assertOk "write hl_src" (← ops.write hlSrc "hard".toUTF8)
    safeClose ops hlSrc
    assertEqErrno "hardlink hl_dst" (← Fuzz.LinuxSyscall.Env.link "hl_src".toUTF8 "hl_dst".toUTF8) 0
    let sgdFd ← assertOk "open sgd_dir" (← ops.openat none ".".toUTF8 dirFlags 0)
    safeClose ops sgdFd
    let sgdPath := dir / "sgid_dir"
    IO.FS.createDir sgdPath
    assertEqErrno "chmod sgid_dir 02755" (← Fuzz.LinuxSyscall.Env.chmod "sgid_dir".toUTF8 0o2755) 0
    let crossPathOpt := if canVarTmp then some ext4Dir.toString.toUTF8 else none
    let st0 := FilesState.withSeededTree {
      cwdPath := dirBytes
      cwdBound := true
      umask := 0o200
      cwdKernelIno? := some (← Fuzz.LinuxSyscall.Env.statIno dirBytes)
      cwdKernelDev? := some (← Fuzz.LinuxSyscall.Env.statDev dirBytes)
      crossMountPath? := crossPathOpt
      mountProfiles := [(0, { supportsSeals := sealsOk })]
      exeOwnedByUid := true
      stdinKind := in0.1
      stdinDevKind? := in0.2
      stdoutKind := out1.1
      stdoutDevKind? := out1.2
      stderrKind := err2.1
      stderrDevKind? := err2.2
      cwdEntries := [
        { name := "env.fifo".toUTF8, kind := .fifo, mode := 0o6755, modeExact := true },
        { name := "env.sock".toUTF8, kind := .socket, mode := 0o755, modeExact := true },
        { name := "hl_src".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "hard".toUTF8, hardlinkGroup? := some 1 },
        { name := "hl_dst".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "hard".toUTF8, hardlinkGroup? := some 1 },
        { name := "sgid_dir".toUTF8, kind := .dir, mode := 0o2755, modeExact := true }
      ]
    }
    let st1 ← runEnvProcAndDevChecks ops st0
    let st2 ← runEnvFifoAndUmaskChecks ops st1 savedMask rlMax
    runEnvCrossAndDeadCwdChecks ops dir ext4Dir canVarTmp rlCur rlMax st2
  finally
    let _ ← Fuzz.LinuxSyscall.Env.umask savedMask
    let _ ← Fuzz.LinuxSyscall.Env.setRlimitFsize rlCur rlMax false
    IO.Process.setCurrentDir dir
    if canVarTmp then
      if ← ext4Dir.pathExists then IO.FS.removeDirAll ext4Dir

private def runMultiFsOverlayAndRoWorker (ovlDirStr roDirStr : String) : IO UInt32 := do
  let ops := defaultOps
  let savedCwd ← IO.Process.getCurrentDir
  let savedMask ← Fuzz.LinuxSyscall.Env.umask 0o022
  try
    let ovlDir : System.FilePath := ovlDirStr
    IO.Process.setCurrentDir ovlDir
    let ovlReal ← IO.FS.realPath ovlDir
    let lowDev ← Fuzz.LinuxSyscall.Env.statDev (ovlReal / "low_f").toString.toUTF8
    let lowIno ← Fuzz.LinuxSyscall.Env.statIno (ovlReal / "low_f").toString.toUTF8
    let lowMode ← Fuzz.LinuxSyscall.Env.statMode (ovlReal / "low_f").toString.toUTF8
    let dMode ← Fuzz.LinuxSyscall.Env.statMode (ovlReal / "d").toString.toUTF8
    let dDev ← Fuzz.LinuxSyscall.Env.statDev (ovlReal / "d").toString.toUTF8
    let dIno ← Fuzz.LinuxSyscall.Env.statIno (ovlReal / "d").toString.toUTF8
    let hl1Mode ← Fuzz.LinuxSyscall.Env.statMode (ovlReal / "hl_lo1").toString.toUTF8
    let hl1Dev ← Fuzz.LinuxSyscall.Env.statDev (ovlReal / "hl_lo1").toString.toUTF8
    let hl1Ino ← Fuzz.LinuxSyscall.Env.statIno (ovlReal / "hl_lo1").toString.toUTF8
    let ovlMode ← Fuzz.LinuxSyscall.Env.statMode ovlReal.toString.toUTF8
    let mut ovlSt := FilesState.withSeededTree {
      cwdPath := ovlReal.toString.toUTF8
      cwdBound := true
      cwdMode := ovlMode
      cwdMountId := 4
      mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
      cwdOverlayMerged := false
      cwdEntries := [
        { name := "low_f".toUTF8, kind := .reg, mode := lowMode, modeExact := true,
          bytes := "low_data\n".toUTF8, kernelDev? := some lowDev, kernelIno? := some lowIno,
          mayCopyUp := true },
        { name := "d".toUTF8, kind := .dir, mode := dMode, modeExact := true,
          kernelDev? := some dDev, kernelIno? := some dIno, mayCopyUp := true },
        { name := "hl_lo1".toUTF8, kind := .reg, mode := hl1Mode, modeExact := true,
          bytes := "low_hl\n".toUTF8, hardlinkGroup? := some 2,
          kernelDev? := some hl1Dev, kernelIno? := some hl1Ino, mayCopyUp := true },
        { name := "hl_lo2".toUTF8, kind := .reg, mode := hl1Mode, modeExact := true,
          bytes := "low_hl\n".toUTF8, hardlinkGroup? := some 2, mayCopyUp := true }
      ]
    }
    let stDInit ← assertOk "overlayfs fstatat unmerged d" (← ops.fstatat none "d".toUTF8 {})
    assertTrue "overlayfs unmerged lower d nlink=2" (stDInit.nlink == 2)
    ovlSt ← stepModelCheck "overlayfs fstatat unmerged d" ovlSt (.fstatat none "d".toUTF8 {}) (.statted stDInit)
    assertOk "overlayfs mkdir pure_u" (← ops.mkdirat none "pure_u".toUTF8 0o755)
    ovlSt ← stepModelCheck "overlayfs mkdir pure_u" ovlSt (.mkdirat none "pure_u".toUTF8 0o755) .unit
    assertOk "overlayfs mkdir pure_u/sub" (← ops.mkdirat none "pure_u/sub".toUTF8 0o755)
    ovlSt ← stepModelCheck "overlayfs mkdir pure_u/sub" ovlSt (.mkdirat none "pure_u/sub".toUTF8 0o755) .unit
    let stPureU ← assertOk "overlayfs fstatat pure_u" (← ops.fstatat none "pure_u".toUTF8 {})
    assertTrue "overlayfs pure_u nlink=3" (stPureU.nlink == 3)
    ovlSt ← stepModelCheck "overlayfs fstatat pure_u" ovlSt (.fstatat none "pure_u".toUTF8 {}) (.statted stPureU)
    assertOk "overlayfs mkdir d/sub2" (← ops.mkdirat none "d/sub2".toUTF8 0o755)
    ovlSt ← stepModelCheck "overlayfs mkdir d/sub2" ovlSt (.mkdirat none "d/sub2".toUTF8 0o755) .unit
    let stDMerged ← assertOk "overlayfs fstatat merged d" (← ops.fstatat none "d".toUTF8 {})
    assertTrue "overlayfs merged d nlink=1" (stDMerged.nlink == 1)
    ovlSt ← stepModelCheck "overlayfs fstatat merged d" ovlSt (.fstatat none "d".toUTF8 {}) (.statted stDMerged)
    let hidHl1 := ovlSt.nextHid
    let fdHl1 ← assertOk "overlayfs open hl_lo1 O_RDWR" (← ops.openat none "hl_lo1".toUTF8 { access := .rdwr } 0)
    ovlSt ← stepModelCheck "overlayfs open hl_lo1 O_RDWR" ovlSt (.openat none "hl_lo1".toUTF8 { access := .rdwr } 0) (.opened hidHl1)
    let stHl1 ← assertOk "overlayfs fstat hl_lo1 copy-up" (← ops.fstat fdHl1)
    ovlSt ← stepModelCheck "overlayfs fstat hl_lo1 copy-up" ovlSt (.fstat hidHl1) (.statted stHl1)
    let stHl2 ← assertOk "overlayfs fstatat hl_lo2" (← ops.fstatat none "hl_lo2".toUTF8 {})
    ovlSt ← stepModelCheck "overlayfs fstatat hl_lo2" ovlSt (.fstatat none "hl_lo2".toUTF8 {}) (.statted stHl2)
    safeClose ops fdHl1
    ovlSt ← stepModelCheck "overlayfs close hl_lo1" ovlSt (.close hidHl1) .unit
    let hidLow := ovlSt.nextHid
    let rOpenLow ← ops.openat none "low_f".toUTF8 { access := .rdwr } 0
    let fdLow ← assertOk "overlayfs open O_RDWR lower file" rOpenLow
    ovlSt ← stepModelCheck "overlayfs copy-up open" ovlSt (.openat none "low_f".toUTF8 { access := .rdwr } 0) (.opened hidLow)
    let stAfter ← assertOk "overlayfs fstat after copy-up" (← ops.fstat fdLow)
    ovlSt ← stepModelCheck "overlayfs fstat after copy-up" ovlSt (.fstat hidLow) (.statted stAfter)
    let rW ← ops.write fdLow "!".toUTF8
    let wBytes ← assertOk "overlayfs write after copy-up" rW
    assertTrue "overlayfs wrote 1 byte" (wBytes == 1)
    ovlSt ← stepModelCheck "overlayfs write after copy-up" ovlSt (.write hidLow "!".toUTF8) (.u32 wBytes)
    safeClose ops fdLow
    ovlSt ← stepModelCheck "overlayfs close" ovlSt (.close hidLow) .unit
    let rRenDir ← ops.renameat2 none "d".toUTF8 none "d_moved".toUTF8 {}
    assertErr "overlayfs lowerdir rename -> EXDEV" rRenDir Errno.EXDEV
    let _ ← stepModelCheck "overlayfs lowerdir rename EXDEV" ovlSt
      (.renameat2 none "d".toUTF8 none "d_moved".toUTF8 {}) (errOrOkOut rRenDir fun _ => .unit)

    let roDir : System.FilePath := roDirStr
    IO.Process.setCurrentDir roDir
    let roReal ← IO.FS.realPath roDir
    let roMode ← Fuzz.LinuxSyscall.Env.statMode roReal.toString.toUTF8
    let exMode ← Fuzz.LinuxSyscall.Env.statMode (roReal / "existing").toString.toUTF8
    let ro444Mode ← Fuzz.LinuxSyscall.Env.statMode (roReal / "ro444").toString.toUTF8
    let roParent := roReal.parent.getD roReal
    let roParentMode ← Fuzz.LinuxSyscall.Env.statMode roParent.toString.toUTF8
    let roParentMnt ← Fuzz.LinuxSyscall.Env.statMntId roParent.toString.toUTF8
    let roMnt ← Fuzz.LinuxSyscall.Env.statMntId roReal.toString.toUTF8
    let roSt := FilesState.withSeededTree {
      cwdPath := roReal.toString.toUTF8
      cwdBound := true
      cwdMode := roMode
      cwdMountId := 4
      cwdParentMountId := if roParentMnt == roMnt then 4 else 5
      cwdParentMode := roParentMode
      cwdParentOwnedByUid := true
      mountProfiles := [(4, { readOnly := true, supportsSeals := false })]
      cwdEntries := [
        { name := "existing".toUTF8, kind := .reg, mode := exMode, modeExact := true, bytes := "ro\n".toUTF8 },
        { name := "ro444".toUTF8, kind := .reg, mode := ro444Mode, modeExact := true, bytes := "r4\n".toUTF8 }
      ]
    }
    let rRoCreat ← ops.openat none "new_ro".toUTF8 rwCreatFlags 0o644
    assertErr "ro open(O_CREAT) -> EROFS" rRoCreat Errno.EROFS
    let _ ← stepModelCheck "ro open(O_CREAT)" roSt (.openat none "new_ro".toUTF8 rwCreatFlags 0o644) (errOrOkOut rRoCreat fun _ => .opened roSt.nextHid)
    let rRoWr ← ops.openat none "existing".toUTF8 { access := .wronly } 0
    assertErr "ro open(O_WRONLY) -> EROFS" rRoWr Errno.EROFS
    let _ ← stepModelCheck "ro open(O_WRONLY)" roSt (.openat none "existing".toUTF8 { access := .wronly } 0) (errOrOkOut rRoWr fun _ => .opened roSt.nextHid)
    let rRo444Wr ← ops.openat none "ro444".toUTF8 { access := .wronly } 0
    assertErr "ro open(ro444, O_WRONLY) -> EACCES" rRo444Wr Errno.EACCES
    let _ ← stepModelCheck "ro open(ro444, O_WRONLY)" roSt (.openat none "ro444".toUTF8 { access := .wronly } 0) (errOrOkOut rRo444Wr fun _ => .opened roSt.nextHid)
    let rRo444Tr ← ops.openat none "ro444".toUTF8 { access := .wronly, trunc := true } 0
    assertErr "ro open(ro444, O_WRONLY|O_TRUNC) -> EROFS" rRo444Tr Errno.EROFS
    let _ ← stepModelCheck "ro open(ro444, O_WRONLY|O_TRUNC)" roSt (.openat none "ro444".toUTF8 { access := .wronly, trunc := true } 0) (errOrOkOut rRo444Tr fun _ => .opened roSt.nextHid)
    let rRoAcc444 ← ops.faccessat none "ro444".toUTF8 { write := true } {}
    assertErr "ro faccessat(ro444, W_OK) -> EACCES" rRoAcc444 Errno.EACCES
    let _ ← stepModelCheck "ro faccessat(ro444, W_OK)" roSt (.faccessat none "ro444".toUTF8 { write := true } {}) (errOrOkOut rRoAcc444 fun _ => .unit)
    let rRoAccEx ← ops.faccessat none "existing".toUTF8 { write := true } {}
    assertErr "ro faccessat(existing, W_OK) -> EROFS" rRoAccEx Errno.EROFS
    let _ ← stepModelCheck "ro faccessat(existing, W_OK)" roSt (.faccessat none "existing".toUTF8 { write := true } {}) (errOrOkOut rRoAccEx fun _ => .unit)
    let rRoAcc ← ops.faccessat none ".".toUTF8 { write := true } {}
    assertErr "ro faccessat(W_OK) -> EROFS" rRoAcc Errno.EROFS
    let _ ← stepModelCheck "ro faccessat(W_OK)" roSt (.faccessat none ".".toUTF8 { write := true } {}) (errOrOkOut rRoAcc fun _ => .unit)
    let rRoMk ← ops.mkdirat none "ro_sub".toUTF8 0o755
    assertErr "ro mkdirat -> EROFS" rRoMk Errno.EROFS
    let _ ← stepModelCheck "ro mkdirat" roSt (.mkdirat none "ro_sub".toUTF8 0o755) (errOrOkOut rRoMk fun _ => .unit)
    let rRoUnl ← ops.unlinkat none "existing".toUTF8 false
    assertErr "ro unlinkat -> EROFS" rRoUnl Errno.EROFS
    let _ ← stepModelCheck "ro unlinkat" roSt (.unlinkat none "existing".toUTF8 false) (errOrOkOut rRoUnl fun _ => .unit)
    let long256 := ByteArray.mk (Array.replicate 256 (UInt8.ofNat 97))
    let rRoUnlLong ← ops.unlinkat none long256 false
    assertErr "ro unlinkat(a*256) -> EROFS" rRoUnlLong Errno.EROFS
    let _ ← stepModelCheck "ro unlinkat(a*256)" roSt (.unlinkat none long256 false) (errOrOkOut rRoUnlLong fun _ => .unit)
    let rRoRenMiss ← ops.renameat2 none "missing".toUTF8 none "dst".toUTF8 {}
    assertErr "ro renameat2(missing -> dst) -> EROFS" rRoRenMiss Errno.EROFS
    let _ ← stepModelCheck "ro renameat2(missing -> dst)" roSt (.renameat2 none "missing".toUTF8 none "dst".toUTF8 {}) (errOrOkOut rRoRenMiss fun _ => .unit)
    let rRoRenDot ← ops.renameat2 none ".".toUTF8 none "dst".toUTF8 {}
    assertErr "ro renameat2(. -> dst) -> EBUSY" rRoRenDot Errno.EBUSY
    let _ ← stepModelCheck "ro renameat2(. -> dst)" roSt (.renameat2 none ".".toUTF8 none "dst".toUTF8 {}) (errOrOkOut rRoRenDot fun _ => .unit)
    let rRoRenXdev ← ops.renameat2 none "existing".toUTF8 none "../xdev_dst".toUTF8 {}
    assertErr "ro renameat2(existing -> ../xdev_dst) -> EXDEV" rRoRenXdev Errno.EXDEV
    let _ ← stepModelCheck "ro renameat2(existing -> ../xdev_dst)" roSt (.renameat2 none "existing".toUTF8 none "../xdev_dst".toUTF8 {}) (errOrOkOut rRoRenXdev fun _ => .unit)
    let rRoSym ← ops.symlinkat "x".toUTF8 none "ro_sym".toUTF8
    assertErr "ro symlinkat -> EROFS" rRoSym Errno.EROFS
    let _ ← stepModelCheck "ro symlinkat" roSt (.symlinkat "x".toUTF8 none "ro_sym".toUTF8) (errOrOkOut rRoSym fun _ => .unit)
    let rRoChm ← ops.fchmodat none "existing".toUTF8 0o600
    assertErr "ro fchmodat -> EROFS" rRoChm Errno.EROFS
    let _ ← stepModelCheck "ro fchmodat" roSt (.fchmodat none "existing".toUTF8 0o600) (errOrOkOut rRoChm fun _ => .unit)
    return 0
  finally
    let _ ← Fuzz.LinuxSyscall.Env.umask savedMask
    IO.Process.setCurrentDir savedCwd

private def runChrootOuterXdevWorker (outDir chrootRoot : String) : IO UInt32 := do
  let ops := defaultOps
  let epDir := System.FilePath.mk outDir / "ep"
  IO.FS.createDirAll epDir
  let epReal ← IO.FS.realPath epDir
  let depth := (epReal.toString.splitOn "/").filter (!·.isEmpty) |>.length
  if depth == 0 then
    IO.eprintln s!"expected non-root canonical epDir, got '{epReal}'"
    return 1
  let upPrefix := String.join (List.replicate depth "../")
  let outerSysFile := upPrefix ++ "sys/kernel/cpu_byteorder"
  let outerEtcDir := upPrefix ++ "etc"
  let outerEtcPasswd := upPrefix ++ "etc/passwd"
  IO.Process.setCurrentDir epReal
  let rc ← Fuzz.LinuxSyscall.Env.chroot chrootRoot.toUTF8
  if rc != 0 then
    IO.eprintln s!"chroot({chrootRoot}) failed with errno={rc}"
    return 1
  let longName := ByteArray.mk (Array.replicate 256 (97 : UInt8))
  let exFlags : RenameFlags := { exchange := true }
  let rSys ← ops.renameat2 none longName none outerSysFile.toUTF8 exFlags
  assertErr s!"chroot outer renameat2(a*256 -> {outerSysFile}, EXCHANGE) -> EXDEV" rSys Errno.EXDEV
  let rInner ← ops.renameat2 none longName none "/sys/kernel/cpu_byteorder".toUTF8 exFlags
  assertErr "chroot inner renameat2(a*256 -> /sys/kernel/cpu_byteorder, EXCHANGE) -> ENAMETOOLONG" rInner Errno.ENAMETOOLONG
  let rCrossSys ← ops.renameat2 none "/sys/kernel/cpu_byteorder".toUTF8 none outerSysFile.toUTF8 exFlags
  assertErr s!"chroot cross-/sys renameat2(/sys/kernel/cpu_byteorder -> {outerSysFile}, EXCHANGE) -> EXDEV" rCrossSys Errno.EXDEV
  let etcMnt ← Fuzz.LinuxSyscall.Env.statMntId outerEtcDir.toUTF8
  let cwdMnt ← Fuzz.LinuxSyscall.Env.statMntId ".".toUTF8
  let etcDev ← Fuzz.LinuxSyscall.Env.statDev outerEtcDir.toUTF8
  let cwdDev ← Fuzz.LinuxSyscall.Env.statDev ".".toUTF8
  let sameEtc := if etcMnt != 0 && cwdMnt != 0 then etcMnt == cwdMnt else etcDev != 0 && etcDev == cwdDev
  let rEtc ← ops.renameat2 none longName none outerEtcPasswd.toUTF8 exFlags
  if sameEtc then
    assertErr s!"chroot outer same-mount renameat2(a*256 -> {outerEtcPasswd}, EXCHANGE) -> ENAMETOOLONG" rEtc Errno.ENAMETOOLONG
  else
    assertErr s!"chroot outer cross-mount renameat2(a*256 -> {outerEtcPasswd}, EXCHANGE) -> EXDEV" rEtc Errno.EXDEV
  let rEtcSys ← ops.renameat2 none outerEtcPasswd.toUTF8 none outerSysFile.toUTF8 exFlags
  assertErr s!"chroot outer renameat2({outerEtcPasswd} -> {outerSysFile}, EXCHANGE) -> EXDEV" rEtcSys Errno.EXDEV
  let rNoXdev ← ops.openat2 none outerSysFile.toUTF8 {
    flags := { access := .rdonly, cloexec := true }, resolve := { noXdev := true }
  }
  assertErr s!"chroot outer openat2({outerSysFile}, RESOLVE_NO_XDEV) -> EXDEV" rNoXdev Errno.EXDEV
  return 0

/-- Multi-filesystem real-Linux probes (`cgroup2` `/sys/fs/cgroup`, plus `unshare -Urm` `overlayfs` copy-up/rename `EXDEV` and `-o remount,ro,bind` `EROFS`). -/
def runMultiFsReproducers : IO Unit := do
  let ops := defaultOps
  let cgPath : System.FilePath := "/sys/fs/cgroup"
  if ← cgPath.pathExists then
    let cgFs ← Fuzz.LinuxSyscall.Env.statfsFsType "/sys/fs/cgroup".toUTF8
    if cgFs == (0x63677270 : UInt64) then
      let cfd ← assertOk "open /sys/fs/cgroup" (← ops.openat none "/sys/fs/cgroup".toUTF8 dirFlags 0)
      let cst ← assertOk "fstat /sys/fs/cgroup" (← ops.fstat cfd)
      assertTrue "/sys/fs/cgroup is dir" (cst.kind == .dir)
      let gd ← assertOk "getdents64 /sys/fs/cgroup" (← ops.getdents64 cfd 4096)
      assertTrue "/sys/fs/cgroup dirents valid" ((countDirents64Strict gd).isSome)
      safeClose ops cfd
      let ctrl : System.FilePath := "/sys/fs/cgroup/cgroup.controllers"
      if ← ctrl.pathExists then
        let rfd ← assertOk "open cgroup.controllers" (← ops.openat none ctrl.toString.toUTF8 roFlags 0)
        let _ ← assertOk "read cgroup.controllers" (← ops.read rfd 128)
        safeClose ops rfd
  let probeUserns ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "command -v capsh >/dev/null 2>&1 && unshare -Urm true"]
  }
  if probeUserns.exitCode == 0 then
    let exe ← IO.appPath
    let script :=
      "set -e; " ++
      "T=$(mktemp -d /tmp/lsmfs.XXXXXX); " ++
      "trap 'umount \"$T/ro\" 2>/dev/null || true; umount \"$T/mnt\" 2>/dev/null || true; rm -rf \"$T\"' EXIT; " ++
      "mkdir -p \"$T/low/d\" \"$T/up\" \"$T/wk\" \"$T/mnt\" \"$T/ro_src\" \"$T/ro\"; " ++
      "printf 'low_data\\n' > \"$T/low/low_f\"; " ++
      "printf 'low_hl\\n' > \"$T/low/hl_lo1\"; ln \"$T/low/hl_lo1\" \"$T/low/hl_lo2\"; " ++
      "printf 'in_d\\n' > \"$T/low/d/in_d\"; " ++
      "printf 'ro\\n' > \"$T/ro_src/existing\"; chmod 0644 \"$T/ro_src/existing\"; " ++
      "printf 'r4\\n' > \"$T/ro_src/ro444\"; chmod 0444 \"$T/ro_src/ro444\"; " ++
      "mount -t overlay overlay -o \"lowerdir=$T/low,upperdir=$T/up,workdir=$T/wk\" \"$T/mnt\"; " ++
      "mount --bind \"$T/ro_src\" \"$T/ro\"; " ++
      "mount -o remount,ro,bind \"$T/ro\"; " ++
      "capsh --drop=cap_dac_override,cap_dac_read_search,cap_fowner -- -c '\"$1\" --files-strace-worker --multifs \"$2\" \"$3\"' _ \"$1\" \"$T/mnt\" \"$T/ro\""
    let out ← IO.Process.output {
      cmd := "unshare"
      args := #["-Urm", "sh", "-c", script, "_", exe.toString]
    }
    if out.exitCode != 0 then
      throw (IO.userError s!"multifs overlay/ro worker failed (exit={out.exitCode}): {out.stdout}\n{out.stderr}")
    if (← (System.FilePath.mk "/sys/kernel/cpu_byteorder").pathExists) &&
        (← (System.FilePath.mk "/var/tmp").pathExists) then
      let chrootScript :=
        "set -e; " ++
        "OUT=$(mktemp -d /var/tmp/lscx-out.XXXXXX); " ++
        "ROOT=$(mktemp -d /var/tmp/lscx-root.XXXXXX); " ++
        "trap 'rm -rf \"$OUT\" \"$ROOT\"' EXIT; " ++
        "mkdir -p \"$ROOT/sys/kernel\" \"$OUT/a/b/c/deep\"; " ++
        "ln -s \"$OUT/a/b/c/deep\" \"$OUT/lnk_out\"; " ++
        "printf 'little\\n' > \"$ROOT/sys/kernel/cpu_byteorder\"; chmod 0444 \"$ROOT/sys/kernel/cpu_byteorder\"; " ++
        "capsh --drop=cap_dac_override,cap_dac_read_search,cap_fowner,cap_fsetid -- -c '\"$1\" --files-strace-worker --chroot-xdev \"$2\" \"$3\" && \"$1\" --files-strace-worker --chroot-xdev \"$4\" \"$3\"' _ \"$1\" \"$OUT\" \"$ROOT\" \"$OUT/lnk_out\""
      let cout ← IO.Process.output {
        cmd := "unshare"
        args := #["-Urm", "sh", "-c", chrootScript, "_", exe.toString]
      }
      if cout.exitCode != 0 then
        throw (IO.userError s!"chroot outer xdev worker failed (exit={cout.exitCode}): {cout.stdout}\n{cout.stderr}")

/-- Deterministic magic-link and boundary reproducers covering magic-link `openat2`/`/proc/1`, `getcwd` boundaries, `unlinkat "/"`, `FUSE_SUPER_MAGIC`, `/proc`/`/dev` aliasing, pipe ring, and sticky-bit rules. -/
private def runMagicLinkProcChecks (ops : FilesOps) (st0 : FilesState) (proc1Owned : Bool) : IO FilesState := do
  let mut st := st0
  let fdRoot ← assertOk "open(/)" (← ops.openat none "/".toUTF8 dirFlags 0)
  let hRoot := st.nextHid
  st ← stepModelCheck "open(/)" st (.openat none "/".toUTF8 dirFlags 0) (.opened hRoot)
  for mp in ["/proc/self/fd/0", "/proc/self/cwd", "/proc/self/root"] do
    let rBen ← ops.openat2 none mp.toUTF8 { resolve := { beneath := true } }
    assertErr s!"openat2({mp}, RESOLVE_BENEATH) -> EXDEV" rBen Errno.EXDEV
    st ← stepModelCheck s!"openat2({mp}, beneath)" st (.openat2 none mp.toUTF8 { resolve := { beneath := true } }) (.err Errno.EXDEV)
    let rInRootCwd ← ops.openat2 none mp.toUTF8 { resolve := { inRoot := true } }
    assertErr s!"openat2(cwd, {mp}, RESOLVE_IN_ROOT) -> ENOENT" rInRootCwd Errno.ENOENT
    st ← stepModelCheck s!"openat2(cwd, {mp}, inRoot)" st (.openat2 none mp.toUTF8 { resolve := { inRoot := true } }) (.err Errno.ENOENT)
    let rInRoot ← ops.openat2 (some fdRoot) mp.toUTF8 { resolve := { inRoot := true } }
    assertErr s!"openat2(/, {mp}, RESOLVE_IN_ROOT) -> EXDEV" rInRoot Errno.EXDEV
    st ← stepModelCheck s!"openat2(/, {mp}, inRoot)" st (.openat2 (some hRoot) mp.toUTF8 { resolve := { inRoot := true } }) (.err Errno.EXDEV)
  safeClose ops fdRoot
  st ← stepModelCheck "close(/)" st (.close hRoot) .unit
  if !proc1Owned then
    let rP1Open ← ops.openat none "/proc/1/cwd".toUTF8 roFlags 0
    assertErr "openat(/proc/1/cwd) -> EACCES" rP1Open Errno.EACCES
    st ← stepModelCheck "openat(/proc/1/cwd)" st (.openat none "/proc/1/cwd".toUTF8 roFlags 0) (.err Errno.EACCES)
    let rP1Stat ← ops.fstatat none "/proc/1/cwd".toUTF8 {}
    assertErr "fstatat(/proc/1/cwd) -> EACCES" rP1Stat Errno.EACCES
    st ← stepModelCheck "fstatat(/proc/1/cwd)" st (.fstatat none "/proc/1/cwd".toUTF8 {}) (.err Errno.EACCES)
    let rP1Lstat ← ops.fstatat none "/proc/1/cwd".toUTF8 { symlinkNofollow := true }
    let stP1Lstat ← assertOk "lstat(/proc/1/cwd)" rP1Lstat
    assertTrue "lstat(/proc/1/cwd) is symlink" (stP1Lstat.kind == .symlink)
    st ← stepModelCheck "lstat(/proc/1/cwd)" st (.fstatat none "/proc/1/cwd".toUTF8 { symlinkNofollow := true }) (.statted stP1Lstat)
    let rP1Rl ← ops.readlinkat none "/proc/1/cwd".toUTF8 64
    assertErr "readlinkat(/proc/1/cwd) -> EACCES" rP1Rl Errno.EACCES
    st ← stepModelCheck "readlinkat(/proc/1/cwd)" st (.readlinkat none "/proc/1/cwd".toUTF8 64) (.err Errno.EACCES)
    let fdP1 ← assertOk "open(/proc/1)" (← ops.openat none "/proc/1".toUTF8 dirFlags 0)
    let hP1 := st.nextHid
    st ← stepModelCheck "open(/proc/1)" st (.openat none "/proc/1".toUTF8 dirFlags 0) (.opened hP1)
    let rP1Rel ← ops.openat2 (some fdP1) "cwd".toUTF8 { resolve := { beneath := true } }
    assertErr "openat2(/proc/1, cwd, beneath) -> EACCES" rP1Rel Errno.EACCES
    st ← stepModelCheck "openat2(/proc/1, cwd, beneath)" st (.openat2 (some hP1) "cwd".toUTF8 { resolve := { beneath := true } }) (.err Errno.EACCES)
    safeClose ops fdP1
    st ← stepModelCheck "close(/proc/1)" st (.close hP1) .unit
  let usernsRootP1St := FilesState.withSeededTree {
    hasCapDacOverride := true, hasCapDacReadSearch := true, hasCapFowner := true,
    proc1OwnedByUid := false, proc1UidMapped := false, proc1GidMapped := false
  }
  assertTrue "userns root /proc/1/cwd readlink -> EACCES"
    ((allowedStep usernsRootP1St (.readlinkat none "/proc/1/cwd".toUTF8 16) (.err Errno.EACCES)).isSome)
  return st

private def runRootAndCwdBoundaryChecks (ops : FilesOps) (dir : System.FilePath) (dirStr : String) (st0 : FilesState) : IO Unit := do
  let mut st := st0
  let rGc0 ← ops.getcwd 0
  assertErrOneOf "getcwd(0) -> ERANGE/EINVAL" rGc0 [Errno.ERANGE, Errno.EINVAL]
  let eGc0 := match rGc0 with | .error e => e | .ok _ => Errno.ERANGE
  st ← stepModelCheck "getcwd(0)" st (.getcwd 0) (.err eGc0)
  let rUnlRootDir ← ops.unlinkat none "/".toUTF8 true
  assertErr "unlinkat(/, true) -> EBUSY" rUnlRootDir Errno.EBUSY
  st ← stepModelCheck "unlinkat(/, true)" st (.unlinkat none "/".toUTF8 true) (.err Errno.EBUSY)
  let rUnlRootFile ← ops.unlinkat none "/".toUTF8 false
  assertErr "unlinkat(/, false) -> EISDIR" rUnlRootFile Errno.EISDIR
  st ← stepModelCheck "unlinkat(/, false)" st (.unlinkat none "/".toUTF8 false) (.err Errno.EISDIR)
  let oomAdjPath : System.FilePath := "/proc/self/oom_score_adj"
  if ← oomAdjPath.pathExists then
    if let .ok fdOom ← ops.openat none oomAdjPath.toString.toUTF8 { access := .rdwr } 0 then
      let hOom := st.nextHid
      st ← stepModelCheck "open oom_score_adj" st (.openat none oomAdjPath.toString.toUTF8 { access := .rdwr } 0) (.opened hOom)
      let rWo ← ops.write fdOom "0\n".toUTF8
      if let .ok nw := rWo then
        st ← stepModelCheck "write oom_score_adj" st (.write hOom "0\n".toUTF8) (.u32 nw)
      safeClose ops fdOom
      let _ ← stepModelCheck "close oom_score_adj" st (.close hOom) .unit

  let deadDir := dir / "dead_cwd"
  IO.FS.createDir deadDir
  IO.Process.setCurrentDir deadDir
  IO.FS.removeDir deadDir
  let rDeadGc ← ops.getcwd 256
  assertErr "getcwd(dead cwd) -> ENOENT" rDeadGc Errno.ENOENT
  IO.Process.setCurrentDir dir
  let deadModel := markCwdUnlinked (FilesState.withSeededTree { cwdPath := dirStr.toUTF8, cwdBound := true })
  let _ ← stepModelCheck "dead cwd getcwd -> ENOENT" deadModel (.getcwd 256) (.err Errno.ENOENT)
  let unreachModel := FilesState.withSeededTree { cwdPath := "/outside/ep".toUTF8, chrootUnreachable := true }
  assertTrue "chroot unreachable getcwd"
    ((allowedStep unreachModel (.getcwd 256) (.bytes "(unreachable)/outside/ep".toUTF8)).isSome)
  let longSeg := ByteArray.mk (Array.replicate 200 (UInt8.ofNat 98))
  let mut deepPath := "/tmp".toUTF8
  for _ in [:22] do
    deepPath := deepPath ++ "/".toUTF8 ++ longSeg
  let longCwdModel := FilesState.withSeededTree { cwdPath := deepPath, cwdBound := true }
  assertTrue "moved cwd > PATH_MAX -> ENAMETOOLONG"
    ((allowedStep longCwdModel (.getcwd 4096) (.err Errno.ENAMETOOLONG)).isSome)

  let fuseSt := FilesState.withSeededTree {
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [{ name := "low_f".toUTF8, kind := .reg, mode := 0o644, mayCopyUp := true }]
  }
  assertTrue "FUSE/overlayfs profile supportsSeals=false, isOverlay=true"
    (let p := mountProfileOf fuseSt 4; !p.supportsSeals && p.isOverlay)

private def runPipeAndStickyChecks : IO Unit := do
  let pipeSt0 := FilesState.withSeededTree {
    stdinKind := .fifo, stdinDevKind? := none, stdinMode := 0o600, stdinOwnedByUid := true
  }
  let pipeSt1 ← stepModelCheck "open /proc/self/fd/0 pipe" pipeSt0
    (.openat none "/proc/self/fd/0".toUTF8 { access := .rdwr, nonblock := true } 0) (.opened 0)
  let pipeSt2 ← stepModelCheck "pipe write 5B" pipeSt1 (.write 0 "hello".toUTF8) (.u32 5)
  let pipeSt3 ← stepModelCheck "pipe read 2B" pipeSt2 (.read 0 2) (.bytes "he".toUTF8)
  let pipeSt4 ← stepModelCheck "pipe close end" pipeSt3 (.close 0) .unit
  let _ ← stepModelCheck "pipe reopen after all closed" pipeSt4
    (.openat none "/proc/self/fd/0".toUTF8 { access := .rdonly, nonblock := true } 0) (.opened 1)
  let pipeFullSt ← stepModelCheck "pipe 65536B write" pipeSt1
    (.write 0 (ByteArray.mk (Array.replicate 65536 (UInt8.ofNat 65))) ) (.u32 65536)
  assertTrue "pipe nonblock EAGAIN at 16 pages"
    ((allowedStep pipeFullSt (.write 0 "x".toUTF8) (.err Errno.EAGAIN)).isSome)

  let stickySt := FilesState.withSeededTree {
    cwdPath := "/sticky".toUTF8
    cwdMode := 0o1777
    cwdEntries := [{ name := "other".toUTF8, kind := .reg, mode := 0o644, bytes := "x".toUTF8 }]
  }
  let stickySt2 := markChildUnowned (markCwdUnowned stickySt) "other".toUTF8
  assertTrue "sticky dir unlinkat unowned -> EPERM"
    ((allowedStep stickySt2 (.unlinkat none "other".toUTF8 false) (.err Errno.EPERM)).isSome)
  assertTrue "sticky dir renameat2 unowned -> EPERM"
    ((allowedStep stickySt2 (.renameat2 none "other".toUTF8 none "other2".toUTF8 {}) (.err Errno.EPERM)).isSome)
  assertTrue "sticky dir openat O_CREAT non-owned -> EACCES"
    ((allowedStep stickySt2 (.openat none "other".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.EACCES)).isSome)

/-- Run magic-link, root boundary, pipe, and sticky reproducers across `/proc/self/*`, `/proc/1`, root `unlinkat`/`getcwd`, `oom_score_adj`, unlinked/moved CWD, overlayfs profiles, pipes, and sticky directories. -/
def runMagicLinkAndStickyReproducers : IO Unit := withTempSandbox "magic-link" fun dir => do
  let ops := defaultOps
  let dirStr := (← IO.FS.realPath dir).toString
  let myUid ← Fuzz.LinuxSyscall.Env.getUid
  let myPid ← Fuzz.LinuxSyscall.Env.getPid
  let proc1Uid ← Fuzz.LinuxSyscall.Env.statUid "/proc/1".toUTF8
  let proc1Owned := (proc1Uid == myUid)
  let in0 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 0
  let out1 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 1
  let err2 ← decodeProbeFdKind <$> Fuzz.LinuxSyscall.Env.fdKind 2
  let devNullDev ← Fuzz.LinuxSyscall.Env.statDev "/dev/null".toUTF8
  let devNullIno ← Fuzz.LinuxSyscall.Env.statIno "/dev/null".toUTF8
  let devZeroDev ← Fuzz.LinuxSyscall.Env.statDev "/dev/zero".toUTF8
  let devZeroIno ← Fuzz.LinuxSyscall.Env.statIno "/dev/zero".toUTF8
  let devFullDev ← Fuzz.LinuxSyscall.Env.statDev "/dev/full".toUTF8
  let devFullIno ← Fuzz.LinuxSyscall.Env.statIno "/dev/full".toUTF8
  let in0Dev ← Fuzz.LinuxSyscall.Env.fdDev 0
  let in0Ino ← Fuzz.LinuxSyscall.Env.fdIno 0
  let out1Dev ← Fuzz.LinuxSyscall.Env.fdDev 1
  let out1Ino ← Fuzz.LinuxSyscall.Env.fdIno 1
  let err2Dev ← Fuzz.LinuxSyscall.Env.fdDev 2
  let err2Ino ← Fuzz.LinuxSyscall.Env.fdIno 2
  let lstatModeOr : ByteArray → Mode → IO Mode := fun p dflt => do
    match ← ops.fstatat none p { symlinkNofollow := true } with
    | .ok st => return st.mode
    | .error _ => return dflt
  let p0Link ← lstatModeOr "/proc/self/fd/0".toUTF8 0o777
  let p1Link ← lstatModeOr "/proc/self/fd/1".toUTF8 0o777
  let p2Link ← lstatModeOr "/proc/self/fd/2".toUTF8 0o777
  let st0 := FilesState.withSeededTree {
    cwdPath := dirStr.toUTF8
    cwdBound := true
    cwdMode := ← Fuzz.LinuxSyscall.Env.statMode dirStr.toUTF8
    proc1OwnedByUid := proc1Owned
    selfPidBytes := (toString myPid).toUTF8
    devNullKernelDev? := if devNullDev != 0 then some devNullDev else none
    devNullKernelIno? := if devNullIno != 0 then some devNullIno else none
    devZeroKernelDev? := if devZeroDev != 0 then some devZeroDev else none
    devZeroKernelIno? := if devZeroIno != 0 then some devZeroIno else none
    devFullKernelDev? := if devFullDev != 0 then some devFullDev else none
    devFullKernelIno? := if devFullIno != 0 then some devFullIno else none
    stdinKind := in0.1, stdinDevKind? := in0.2, stdinMode := ← Fuzz.LinuxSyscall.Env.fdMode 0,
    stdinOwnedByUid := ((← Fuzz.LinuxSyscall.Env.fdUid 0) == myUid),
    stdinKernelDev? := if in0Dev != 0 then some in0Dev else none,
    stdinKernelIno? := if in0Ino != 0 then some in0Ino else none,
    stdoutKind := out1.1, stdoutDevKind? := out1.2, stdoutMode := ← Fuzz.LinuxSyscall.Env.fdMode 1,
    stdoutOwnedByUid := ((← Fuzz.LinuxSyscall.Env.fdUid 1) == myUid),
    stdoutKernelDev? := if out1Dev != 0 then some out1Dev else none,
    stdoutKernelIno? := if out1Ino != 0 then some out1Ino else none,
    stderrKind := err2.1, stderrDevKind? := err2.2, stderrMode := ← Fuzz.LinuxSyscall.Env.fdMode 2,
    stderrOwnedByUid := ((← Fuzz.LinuxSyscall.Env.fdUid 2) == myUid),
    stderrKernelDev? := if err2Dev != 0 then some err2Dev else none,
    stderrKernelIno? := if err2Ino != 0 then some err2Ino else none,
    procFd0LinkMode := p0Link, procFd1LinkMode := p1Link, procFd2LinkMode := p2Link
  }
  let st1 ← runMagicLinkProcChecks ops st0 proc1Owned
  runRootAndCwdBoundaryChecks ops dir dirStr st1
  runPipeAndStickyChecks

private def runSeccompAndOverlayCopyUpReproducers : IO Unit := do
  let ops := defaultOps
  let scStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if scStatus == 0 then
    let nr ← Fuzz.LinuxSyscall.Env.nrGetcwd
    let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nr Errno.EFAULT nr Errno.EFAULT (0xffffffff : UInt32) 0
    if scErr != 0 then
      Fuzz.LinuxSyscall.Env.exitImmediate 77
    let _ ← ops.getcwd 64
    Fuzz.LinuxSyscall.Env.exitImmediate 78
  if scStatus == 2077 then
    IO.println "NOTE: skipping live seccomp EFAULT abort test (PR_SET_SECCOMP unsupported)"
  else
    assertTrue s!"seccomp EFAULT on getcwd must SIGABRT (1006), got {scStatus}" (scStatus == 1006)

  let sc0 := (FilesState.withSeededTree {
    cwdEntries := [{ name := "f".toUTF8, kind := .reg, mode := 0o644, bytes := "abc".toUTF8 }]
  }).withOuterSeccomp true
  let _ ← stepModelCheck "seccomp EPERM on getcwd" sc0 (.getcwd 64) (.err Errno.EPERM)
  let sc1 ← stepModelCheck "seccomp open f" sc0 (.openat none "f".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "seccomp ENOSYS on fsync" sc1 (.fsync 0) (.err Errno.ENOSYS)
  assertTrue "seccomp rejects EFAULT" ((allowedStep sc0 (.getcwd 64) (.err Errno.EFAULT)).isNone)
  assertTrue "seccomp rejects EPERM on embedded NUL"
    ((allowedStep sc0 (.fstatat none (ByteArray.mk #[97, 0]) {}) (.err Errno.EPERM)).isNone)
  let scStayOpen ← stepModelCheck "seccomp close EPERM keeps fd open" sc1 (.close 0) (.err Errno.EPERM)
  let _ ← stepModelCheck "seccomp post-EPERM-close read still works" scStayOpen (.read 0 8) (.bytes "abc".toUTF8)
  let scStayBusy ← stepModelCheck "seccomp close EBUSY keeps fd open" sc1 (.close 0) (.err Errno.EBUSY)
  let _ ← stepModelCheck "seccomp post-EBUSY-close read still works" scStayBusy (.read 0 8) (.bytes "abc".toUTF8)

  withTempSandbox "seccomp-ovl" fun tmpDir => do
    let dr ← IO.FS.realPath tmpDir
    let dMode ← Fuzz.LinuxSyscall.Env.statMode dr.toString.toUTF8
    let mut eSt := FilesState.withSeededTree {
      cwdPath := dr.toString.toUTF8
      cwdBound := true
      cwdMode := dMode
    }
    let dirFd ← assertOk "open ." (← ops.openat none ".".toUTF8 { access := .rdonly, directory := true } 0)
    let hidDir := eSt.nextHid
    eSt ← stepModelCheck "open ." eSt (.openat none ".".toUTF8 { access := .rdonly, directory := true } 0) (.opened hidDir)
    assertOk "close ." (← ops.close dirFd)
    eSt ← stepModelCheck "close ." eSt (.close hidDir) .unit
    let rClosedEmpty ← ops.fstatat (some dirFd) ByteArray.empty { emptyPath := true, eaccess := true }
    assertErr "closed fd AT_EMPTY_PATH | AT_EACCESS -> EINVAL" rClosedEmpty Errno.EINVAL
    eSt ← stepModelCheck "closed fd AT_EMPTY_PATH | AT_EACCESS" eSt
      (.fstatat (some hidDir) ByteArray.empty { emptyPath := true, eaccess := true }) (.err Errno.EINVAL)

    assertTrue "mkfifo p444.fifo" ((← Fuzz.LinuxSyscall.Env.mkfifo "p444.fifo".toUTF8 0o444) == 0)
    let _ ← Fuzz.LinuxSyscall.Env.chmod "p444.fifo".toUTF8 0o444
    let fMode ← Fuzz.LinuxSyscall.Env.statMode "p444.fifo".toUTF8
    let rFifoTrunc ← ops.openat none "p444.fifo".toUTF8 { access := .rdonly, nonblock := true, trunc := true } 0
    assertErr "open 0444 FIFO O_RDONLY|O_TRUNC -> EACCES" rFifoTrunc Errno.EACCES
    let fifoSt := FilesState.withSeededTree {
      cwdPath := dr.toString.toUTF8
      cwdEntries := [{ name := "p444.fifo".toUTF8, kind := .fifo, mode := fMode, modeExact := true }]
    }
    let _ ← stepModelCheck "model 0444 FIFO O_RDONLY|O_TRUNC -> EACCES" fifoSt
      (.openat none "p444.fifo".toUTF8 { access := .rdonly, nonblock := true, trunc := true } 0)
      (.err Errno.EACCES)

  let stickySame0 := FilesState.withSeededTree {
    cwdPath := "/sticky2".toUTF8
    cwdMode := 0o1777
    cwdEntries := [
      { name := "same_reg".toUTF8, kind := .reg, mode := 0o644, ownedByUid := false, ownerUid? := some 0 },
      { name := "diff_fifo".toUTF8, kind := .fifo, mode := 0o644, ownedByUid := false, ownerUid? := some 65534 }
    ]
  }
  let stickySame := match assocGet stickySame0.inodes stickySame0.cwdIno with
    | some cvn => { stickySame0 with inodes := assocSet stickySame0.inodes stickySame0.cwdIno { cvn with owner := { cvn.owner with ownedByUid := false, uid? := some 0 } } }
    | none => stickySame0
  let _ ← stepModelCheck "sticky same non-caller owner O_CREAT allowed" stickySame
    (.openat none "same_reg".toUTF8 { access := .rdonly, creat := true } 0o644) (.opened 0)
  let _ ← stepModelCheck "sticky diff non-caller owner fifo O_CREAT -> EACCES" stickySame
    (.openat none "diff_fifo".toUTF8 { access := .rdonly, nonblock := true, creat := true } 0o644) (.err Errno.EACCES)
  assertTrue "sticky diff owner fifo O_CREAT cannot succeed"
    ((allowedStep stickySame (.openat none "diff_fifo".toUTF8 { access := .rdonly, nonblock := true, creat := true } 0o644) (.opened 0)).isNone)

  let unreachOuter := FilesState.withSeededTree { cwdPath := "/outside/ep".toUTF8, chrootUnreachable := true }
  let _ ← stepModelCheck "chroot outside ../../../../etc/passwd faccessat" unreachOuter
    (.faccessat none "../../../../etc/passwd".toUTF8 { read := true } {}) .unit
  let longName256 := ByteArray.mk (Array.replicate 256 (97 : UInt8))
  let exFlags : RenameFlags := { exchange := true }
  let _ ← stepModelCheck "chroot default inner->outer cross-/sys renameat2 -> EXDEV" unreachOuter
    (.renameat2 none "/sys/kernel/cpu_byteorder".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  assertTrue "chroot default inner->outer cross-/sys renameat2 rejects EPERM"
    ((allowedStep unreachOuter
      (.renameat2 none "/sys/kernel/cpu_byteorder".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
      (.err Errno.EPERM)).isNone)
  let _ ← stepModelCheck "chroot default outer->inner cross-/sys renameat2 -> EXDEV" unreachOuter
    (.renameat2 none "../../../../sys/kernel/cpu_byteorder".toUTF8 none "/sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  let unreachOuterCustomSys := FilesState.withSeededTree {
    cwdPath := "/outside/ep".toUTF8
    sysMountId := 6
    chrootUnreachable := true
  }
  let _ ← stepModelCheck "chroot custom sysMountId=6 inner->outer cross-/sys renameat2 -> EXDEV" unreachOuterCustomSys
    (.renameat2 none "/sys/kernel/cpu_byteorder".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  let assertOuterSysDisjoint (label : String) (st : FilesState) (minExclusiveMid : Nat) : IO Unit := do
    let stOpened ← stepModelCheck s!"{label}: open outer /sys/kernel/cpu_byteorder" st
      (.openat none "../../../../sys/kernel/cpu_byteorder".toUTF8 { access := .rdonly, cloexec := true } 0) (.opened 0)
    let outerSysMid? := (assocGet stOpened.fds 0).bind fun desc =>
      (assocGet stOpened.inodes desc.ino).map (·.mountId)
    match outerSysMid? with
    | none => throw (IO.userError s!"{label}: missing opened outer /sys/kernel/cpu_byteorder inode")
    | some mid =>
      assertTrue s!"{label}: outerSysMountId ({mid}) > {minExclusiveMid}" (mid > minExclusiveMid)
      assertTrue s!"{label}: outer /sys mount {mid} does not inherit readOnly profile"
        (!isReadOnlyMount st mid)
      assertTrue s!"{label}: outer /sys mount {mid} does not inherit isOverlay profile"
        (!(mountProfileOf st mid).isOverlay)
  let unreachOuterHigherSeeded := FilesState.withSeededTree {
    cwdPath := "/outside/ep".toUTF8
    crossMountPath? := some "/cross".toUTF8
    chrootUnreachable := true
    cwdEntries := [
      { name := "ro_sub".toUTF8, kind := .dir, mode := 0o755, mountId? := some 6 },
      { relDir := ["ro_sub".toUTF8], name := "f".toUTF8, kind := .reg, mode := 0o644 }
    ]
    crossEntries := [
      { name := "ovl_sub".toUTF8, kind := .dir, mode := 0o755, mountId? := some 7 },
      { relDir := ["ovl_sub".toUTF8], name := "g".toUTF8, kind := .reg, mode := 0o644 }
    ]
    mountProfiles := [
      (6, { readOnly := true }),
      (7, { isOverlay := true }),
      (8, { readOnly := true, isOverlay := true })
    ]
  }
  assertOuterSysDisjoint "chroot outer /sys above cwdEntries/crossEntries/mountProfiles" unreachOuterHigherSeeded 8
  let _ ← stepModelCheck "chroot outer /sys fchmodat not EROFS (returns EPERM)" unreachOuterHigherSeeded
    (.fchmodat none "../../../../sys/kernel/cpu_byteorder".toUTF8 0o444) (.err Errno.EPERM)
  assertTrue "chroot outer /sys fchmodat rejects EROFS"
    ((allowedStep unreachOuterHigherSeeded
      (.fchmodat none "../../../../sys/kernel/cpu_byteorder".toUTF8 0o444) (.err Errno.EROFS)).isNone)
  let _ ← stepModelCheck "chroot cwdEntries mountId=6 -> outer /sys renameat2 -> EXDEV" unreachOuterHigherSeeded
    (.renameat2 none "ro_sub/f".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  assertTrue "chroot cwdEntries mountId=6 -> outer /sys renameat2 rejects EROFS"
    ((allowedStep unreachOuterHigherSeeded
      (.renameat2 none "ro_sub/f".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
      (.err Errno.EROFS)).isNone)
  let _ ← stepModelCheck "chroot crossEntries mountId=7 -> outer /sys renameat2 -> EXDEV" unreachOuterHigherSeeded
    (.renameat2 none "/cross/ovl_sub/g".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  let unreachOuterCwdEntryOnly := FilesState.withSeededTree {
    cwdPath := "/outside/ep".toUTF8
    chrootUnreachable := true
    cwdEntries := [
      { name := "sub6".toUTF8, kind := .dir, mode := 0o755, mountId? := some 6 },
      { relDir := ["sub6".toUTF8], name := "f".toUTF8, kind := .reg, mode := 0o644 }
    ]
  }
  assertOuterSysDisjoint "chroot outer /sys above cwdEntries mountId=6" unreachOuterCwdEntryOnly 6
  let _ ← stepModelCheck "chroot cwdEntries-only mountId=6 -> outer /sys renameat2 -> EXDEV" unreachOuterCwdEntryOnly
    (.renameat2 none "sub6/f".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  let unreachOuterCrossEntryOnly := FilesState.withSeededTree {
    cwdPath := "/outside/ep".toUTF8
    crossMountPath? := some "/cross".toUTF8
    chrootUnreachable := true
    crossEntries := [
      { name := "sub6".toUTF8, kind := .dir, mode := 0o755, mountId? := some 6 },
      { relDir := ["sub6".toUTF8], name := "g".toUTF8, kind := .reg, mode := 0o644 }
    ]
  }
  assertOuterSysDisjoint "chroot outer /sys above crossEntries mountId=6" unreachOuterCrossEntryOnly 6
  let _ ← stepModelCheck "chroot crossEntries-only mountId=6 -> outer /sys renameat2 -> EXDEV" unreachOuterCrossEntryOnly
    (.renameat2 none "/cross/sub6/g".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags)
    (.err Errno.EXDEV)
  let unreachOuterProfileOnly := FilesState.withSeededTree {
    cwdPath := "/outside/ep".toUTF8
    chrootUnreachable := true
    mountProfiles := [(6, { readOnly := true, isOverlay := true })]
  }
  assertOuterSysDisjoint "chroot outer /sys above mountProfiles key 6" unreachOuterProfileOnly 6
  let _ ← stepModelCheck "chroot mountProfiles-only key 6 outer /sys fchmodat -> EPERM" unreachOuterProfileOnly
    (.fchmodat none "../../../../sys/kernel/cpu_byteorder".toUTF8 0o444) (.err Errno.EPERM)
  assertTrue "chroot mountProfiles-only key 6 outer /sys fchmodat rejects EROFS"
    ((allowedStep unreachOuterProfileOnly
      (.fchmodat none "../../../../sys/kernel/cpu_byteorder".toUTF8 0o444) (.err Errno.EROFS)).isNone)
  let unreachSameMount := FilesState.withSeededTree {
    cwdPath := "/ep".toUTF8
    cwdMountId := 0
    cwdParentMountId := 0
    sysMountId := 0
    hostSyntheticOwnedByUid := true
    chrootUnreachable := true
    chrootOutsideAncestors := [
      (0o755, true, 0, none, none),
      (0o755, true, 0, none, none),
      (0o1777, false, 0, none, none),
      (0o755, false, 0, none, none)
    ]
  }
  let _ ← stepModelCheck "chroot outside renameat2(a*256 -> ../../../../sys/kernel/cpu_byteorder, EXCHANGE) -> EXDEV"
    unreachSameMount (.renameat2 none longName256 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags) (.err Errno.EXDEV)
  assertTrue "chroot outside renameat2(a*256 -> ../../../../sys/kernel/cpu_byteorder) rejects ENAMETOOLONG"
    ((allowedStep unreachSameMount (.renameat2 none longName256 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags) (.err Errno.ENAMETOOLONG)).isNone)
  let _ ← stepModelCheck "chroot outside same-mount renameat2(a*256 -> ../../../../etc/passwd, EXCHANGE) -> ENAMETOOLONG"
    unreachSameMount (.renameat2 none longName256 none "../../../../etc/passwd".toUTF8 exFlags) (.err Errno.ENAMETOOLONG)
  let _ ← stepModelCheck "chroot outside renameat2(etc/passwd -> sys/kernel/cpu_byteorder, EXCHANGE) -> EXDEV"
    unreachSameMount (.renameat2 none "../../../../etc/passwd".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags) (.err Errno.EXDEV)
  let _ ← stepModelCheck "chroot inner renameat2(a*256 -> /sys/kernel/cpu_byteorder, EXCHANGE) -> ENAMETOOLONG"
    unreachSameMount (.renameat2 none longName256 none "/sys/kernel/cpu_byteorder".toUTF8 exFlags) (.err Errno.ENAMETOOLONG)
  let _ ← stepModelCheck "chroot outside openat2(../../../../sys/kernel/cpu_byteorder, noXdev) -> EXDEV"
    unreachSameMount (.openat2 none "../../../../sys/kernel/cpu_byteorder".toUTF8 { resolve := { noXdev := true } }) (.err Errno.EXDEV)
  let _ ← stepModelCheck "chroot outside openat2(../../../../etc/passwd, noXdev) succeeds"
    unreachSameMount (.openat2 none "../../../../etc/passwd".toUTF8 { resolve := { noXdev := true } }) (.opened 0)
  let unreachSplitMount := FilesState.withSeededTree {
    cwdPath := "/ep".toUTF8
    cwdMountId := 0
    cwdParentMountId := 0
    sysMountId := 0
    hostSyntheticOwnedByUid := true
    chrootUnreachable := true
    chrootOutsideAncestors := [
      (0o755, true, 0, none, none),
      (0o755, true, 0, none, none),
      (0o1777, false, 0, none, none),
      (0o755, false, 5, none, none)
    ]
    chrootOuterEntries := [
      { name := "etc".toUTF8, kind := .dir, mode := 0o755, ownedByUid := false, mountId? := some 5, dynamicMeta := true },
      { relDir := ["etc".toUTF8], name := "passwd".toUTF8, kind := .reg, mode := 0o644, ownedByUid := false, mountId? := some 5, dynamicMeta := true },
      { name := "sys".toUTF8, kind := .dir, mode := 0o555, ownedByUid := false, mountId? := some 6, dynamicMeta := true },
      { relDir := ["sys".toUTF8], name := "kernel".toUTF8, kind := .dir, mode := 0o755, ownedByUid := false, mountId? := some 6, dynamicMeta := true },
      { relDir := ["sys".toUTF8, "kernel".toUTF8], name := "cpu_byteorder".toUTF8, kind := .reg, mode := 0o444, ownedByUid := false, mountId? := some 6, dynamicMeta := true }
    ]
  }
  let _ ← stepModelCheck "chroot split-mount renameat2(etc/passwd -> sys/kernel/cpu_byteorder, EXCHANGE) -> EXDEV"
    unreachSplitMount (.renameat2 none "../../../../etc/passwd".toUTF8 none "../../../../sys/kernel/cpu_byteorder".toUTF8 exFlags) (.err Errno.EXDEV)
  let _ ← stepModelCheck "chroot split-mount renameat2(a*256 -> ../../../../etc/passwd, EXCHANGE) -> EXDEV"
    unreachSplitMount (.renameat2 none longName256 none "../../../../etc/passwd".toUTF8 exFlags) (.err Errno.EXDEV)

  let ovlModel0 := FilesState.withSeededTree {
    cwdPath := "/ovl".toUTF8
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "lf".toUTF8, kind := .reg, mode := 0o644, bytes := "low".toUTF8, mayCopyUp := true },
      { name := "hl_lo1".toUTF8, kind := .reg, mode := 0o644, bytes := "hl".toUTF8, hardlinkGroup? := some 2, mayCopyUp := true },
      { name := "hl_lo2".toUTF8, kind := .reg, mode := 0o644, bytes := "hl".toUTF8, hardlinkGroup? := some 2, mayCopyUp := true },
      { name := "sym_hla".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "hl_lo1".toUTF8, mayCopyUp := true }
    ]
  }
  let om1 ← stepModelCheck "ovl open hl_lo1 O_RDONLY" ovlModel0 (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let om2 ← stepModelCheck "ovl open hl_lo2 O_RDONLY" om1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let om3 ← stepModelCheck "ovl flock hl_lo1 exclusive" om2 (.flock 0 (.exclusive true)) .unit
  let om4 ← stepModelCheck "ovl open sym_hla O_RDWR copy-up" om3 (.openat none "sym_hla".toUTF8 { access := .rdwr } 0) (.opened 2)
  let om5a ← stepModelCheck "ovl post-copyup sym_hla exclusive EAGAIN against pre-copyup hl_lo1" om4 (.flock 2 (.exclusive true)) (.err Errno.EAGAIN)
  let om5 ← stepModelCheck "ovl pre-copyup hl_lo2 exclusive succeeds independently of hl_lo1" om5a (.flock 1 (.exclusive true)) .unit
  let om6 ← stepModelCheck "ovl rename hl_lo1 copies up" om5 (.renameat2 none "hl_lo1".toUTF8 none "hl_moved".toUTF8 {}) .unit
  let _ ← stepModelCheck "ovl fchmodat hl_moved" om6 (.fchmodat none "hl_moved".toUTF8 0o600) .unit
  let olf1 ← stepModelCheck "ovl open lf O_RDONLY" ovlModel0 (.openat none "lf".toUTF8 roFlags 0) (.opened 0)
  let olf2 ← stepModelCheck "ovl unlink lf" olf1 (.unlinkat none "lf".toUTF8 false) .unit
  let _ ← stepModelCheck "ovl fchmod unlinked lower fd -> EEXIST" olf2 (.fchmod 0 0o600) (.err Errno.EEXIST)

private def runSeccompCloseAndOpathReproducers : IO Unit := do
  let ops := defaultOps
  withTempSandbox "seccomp-close" fun tmpDir => do
    let dr ← IO.FS.realPath tmpDir
    IO.Process.setCurrentDir dr
    assertTrue "mkfifo sc.fifo" ((← Fuzz.LinuxSyscall.Env.mkfifo "sc.fifo".toUTF8 0o644) == 0)
    let nrClose ← Fuzz.LinuxSyscall.Env.nrClose
    for injected in #[Errno.EPERM, Errno.EACCES, Errno.ENOSYS] do
      let scStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
      if scStatus == 0 then
        let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose injected nrClose injected (0xffffffff : UInt32) 0
        if scErr != 0 then
          Fuzz.LinuxSyscall.Env.exitImmediate 77
        let st0 := (FilesState.withSeededTree {
          cwdPath := dr.toString.toUTF8
          cwdBound := true
          cwdEntries := [{ name := "sc.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true }]
        }).withOuterSeccomp true
        match ← ops.openat none "sc.fifo".toUTF8 { access := .rdonly, nonblock := true } 0 with
        | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 11
        | .ok rfd =>
          let st1 ← match allowedStep st0 (.openat none "sc.fifo".toUTF8 { access := .rdonly, nonblock := true } 0) (.opened 0) with
            | some s => pure s
            | none => Fuzz.LinuxSyscall.Env.exitImmediate 12; pure st0
          match ← ops.close rfd with
          | .ok () => Fuzz.LinuxSyscall.Env.exitImmediate 13
          | .error ce =>
            if ce != injected then Fuzz.LinuxSyscall.Env.exitImmediate 14
          let st2 ← match allowedStep st1 (.close 0) (.err injected) with
            | some s => pure s
            | none => Fuzz.LinuxSyscall.Env.exitImmediate 15; pure st1
          match ← ops.fstat rfd with
          | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 16
          | .ok fst =>
            let _ ← match allowedStep st2 (.fstat 0) (.statted fst) with
              | some s => pure s
              | none => Fuzz.LinuxSyscall.Env.exitImmediate 17; pure st2
          match ← ops.openat none "sc.fifo".toUTF8 { access := .wronly, nonblock := true } 0 with
          | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 18
          | .ok wfd =>
            let st3 ← match allowedStep st2 (.openat none "sc.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.opened 1) with
              | some s => pure s
              | none => Fuzz.LinuxSyscall.Env.exitImmediate 19; pure st2
            let _ := (rfd, wfd, st3)
            Fuzz.LinuxSyscall.Env.exitImmediate 0
      if scStatus == 2077 then
        IO.println s!"NOTE: skipping live seccomp __NR_close={injected} FIFO test (PR_SET_SECCOMP unsupported)"
      else
        assertTrue s!"seccomp __NR_close={injected} + FIFO child failed with status={scStatus}" (scStatus == 2000)
    let scEbusyStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
    if scEbusyStatus == 0 then
      let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose Errno.EBUSY nrClose Errno.EBUSY (0xffffffff : UInt32) 0
      if scErr != 0 then Fuzz.LinuxSyscall.Env.exitImmediate 77
      match ← ops.openat none "sc.fifo".toUTF8 { access := .rdonly, nonblock := true } 0 with
      | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 11
      | .ok rfd =>
        match ← ops.close rfd with
        | .ok () => Fuzz.LinuxSyscall.Env.exitImmediate 13
        | .error ce => if ce != Errno.EBUSY then Fuzz.LinuxSyscall.Env.exitImmediate 14
        match ← ops.fstat rfd with
        | .ok _ => Fuzz.LinuxSyscall.Env.exitImmediate 0
        | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 16
    if scEbusyStatus == 2077 then
      IO.println "NOTE: skipping live seccomp __NR_close=EBUSY retained-box test (PR_SET_SECCOMP unsupported)"
    else
      assertTrue s!"seccomp __NR_close=EBUSY retained-box child failed with status={scEbusyStatus}" (scEbusyStatus == 2000)

    let scEioStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
    if scEioStatus == 0 then
      let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose Errno.EIO nrClose Errno.EIO (0xffffffff : UInt32) 0
      if scErr != 0 then Fuzz.LinuxSyscall.Env.exitImmediate 77
      match ← ops.openat none "sc.fifo".toUTF8 { access := .rdonly, nonblock := true } 0 with
      | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 11
      | .ok rfd =>
        match ← ops.close rfd with
        | .ok () => Fuzz.LinuxSyscall.Env.exitImmediate 13
        | .error ce => if ce != Errno.EIO then Fuzz.LinuxSyscall.Env.exitImmediate 14
        match ← ops.fstat rfd with
        | .error e => if e == Errno.EBADF then Fuzz.LinuxSyscall.Env.exitImmediate 0 else Fuzz.LinuxSyscall.Env.exitImmediate 16
        | .ok _ => Fuzz.LinuxSyscall.Env.exitImmediate 17
    if scEioStatus == 2077 then
      IO.println "NOTE: skipping live seccomp __NR_close=EIO closed-box test (PR_SET_SECCOMP unsupported)"
    else
      assertTrue s!"seccomp __NR_close=EIO closed-box child failed with status={scEioStatus}" (scEioStatus == 2000)

  let roSticky0 := FilesState.withSeededTree {
    cwdPath := "/ro_sticky".toUTF8
    cwdMode := 0o1777
    cwdMountId := 10
    mountProfiles := [(10, { readOnly := true })]
    cwdEntries := [{ name := "reg666".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, ownerUid? := some 65534 }]
  }
  let roSticky := match assocGet roSticky0.inodes roSticky0.cwdIno with
    | some cvn => { roSticky0 with inodes := assocSet roSticky0.inodes roSticky0.cwdIno { cvn with owner := { cvn.owner with ownedByUid := false, uid? := some 0 } } }
    | none => roSticky0
  let _ ← stepModelCheck "ro/s1777/reg666 O_RDWR|O_CREAT -> EACCES" roSticky
    (.openat none "reg666".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "ro/s1777/reg666 O_RDWR|O_CREAT -> EROFS" roSticky
    (.openat none "reg666".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.EROFS)
  let _ ← stepModelCheck "ro/s1777/reg666 O_RDONLY|O_CREAT|O_TRUNC -> EACCES" roSticky
    (.openat none "reg666".toUTF8 { access := .rdonly, creat := true, trunc := true } 0o644) (.err Errno.EACCES)

  let s1721Base := FilesState.withSeededTree {
    cwdPath := "/s1721".toUTF8
    cwdMode := 0o1721
    protectedRegular := 2
    protectedFifos := 1
    cwdEntries := [
      { name := "reg666".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, ownerUid? := some 65534 },
      { name := "fifo666".toUTF8, kind := .fifo, mode := 0o666, modeExact := true, ownedByUid := false, ownerUid? := some 65534 }
    ]
  }
  let s1721 := match assocGet s1721Base.inodes s1721Base.cwdIno with
    | some cvn => { s1721Base with inodes := assocSet s1721Base.inodes s1721Base.cwdIno { cvn with owner := { cvn.owner with ownedByUid := false, inGroup := false, uid? := some 0 } } }
    | none => s1721Base
  let _ ← stepModelCheck "rw/s1721/reg666 (protReg=2) -> EACCES" s1721
    (.openat none "reg666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  assertTrue "rw/s1721/reg666 cannot open"
    ((allowedStep s1721 (.openat none "reg666".toUTF8 { access := .rdonly, creat := true } 0o644) (.opened 0)).isNone)
  let _ ← stepModelCheck "rw/s1721/fifo666 (protFifo=1) -> ok" s1721
    (.openat none "fifo666".toUTF8 { access := .rdwr, nonblock := true, creat := true } 0o644) (.opened 0)
  assertTrue "rw/s1721/fifo666 (protFifo=1) rejects EACCES"
    ((allowedStep s1721 (.openat none "fifo666".toUTF8 { access := .rdwr, nonblock := true, creat := true } 0o644) (.err Errno.EACCES)).isNone)
  let s1721F2 := { s1721 with sysctls := { s1721.sysctls with protectedFifos := 2 } }
  let _ ← stepModelCheck "rw/s1721/fifo666 (protFifo=2) -> EACCES" s1721F2
    (.openat none "fifo666".toUTF8 { access := .rdwr, nonblock := true, creat := true } 0o644) (.err Errno.EACCES)

  let ovlDir0 := FilesState.withSeededTree {
    cwdPath := "/ovl_dir".toUTF8
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [{ name := "empty_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true }]
  }
  let od1 ← stepModelCheck "ovl open empty_ldir" ovlDir0 (.openat none "empty_ldir".toUTF8 dirFlags 0) (.opened 0)
  let od2 ← stepModelCheck "ovl rmdir empty_ldir" od1 (.unlinkat none "empty_ldir".toUTF8 true) .unit
  let _ ← stepModelCheck "ovl fchmod unlinked empty_ldir -> ENOTDIR" od2 (.fchmod 0 0o700) (.err Errno.ENOTDIR)

  let cdev0 := FilesState.withSeededTree {
    cwdPath := "/cdev".toUTF8
    cwdEntries := [{ name := "null444".toUTF8, kind := .charDev, devKind? := some .nullDev, mode := 0o444, modeExact := true }]
  }
  let _ ← stepModelCheck "0444 charDev O_RDONLY|O_TRUNC -> EACCES" cdev0
    (.openat none "null444".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.EACCES)
  assertTrue "0444 charDev O_RDONLY|O_TRUNC cannot open"
    ((allowedStep cdev0 (.openat none "null444".toUTF8 { access := .rdonly, trunc := true } 0) (.opened 0)).isNone)

  let capSt := FilesState.withSeededTree {
    hasCapDacOverride := true
    hasCapFowner := true
    cwdPath := "/cap".toUTF8
    cwdEntries := [
      { name := "r000".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false },
      { name := "r100".toUTF8, kind := .reg, mode := 0o100, modeExact := true, ownedByUid := false },
      { name := "d000".toUTF8, kind := .dir, mode := 0o000, modeExact := true, ownedByUid := false }
    ]
  }
  let _ ← stepModelCheck "CAP_DAC_OVERRIDE r000 R_OK" capSt (.faccessat none "r000".toUTF8 { read := true } {}) .unit
  let _ ← stepModelCheck "CAP_DAC_OVERRIDE r000 W_OK" capSt (.faccessat none "r000".toUTF8 { write := true } {}) .unit
  let _ ← stepModelCheck "CAP_DAC_OVERRIDE r000 X_OK -> EACCES" capSt (.faccessat none "r000".toUTF8 { exec := true } {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "CAP_DAC_OVERRIDE r100 X_OK" capSt (.faccessat none "r100".toUTF8 { exec := true } {}) .unit
  let _ ← stepModelCheck "CAP_DAC_OVERRIDE d000 X_OK" capSt (.faccessat none "d000".toUTF8 { exec := true } {}) .unit
  let _ ← stepModelCheck "CAP_FOWNER fchmodat unowned r000" capSt (.fchmodat none "r000".toUTF8 0o600) .unit
  let rsSt := FilesState.withSeededTree {
    hasCapDacReadSearch := true
    cwdPath := "/rs".toUTF8
    cwdEntries := [{ name := "d000".toUTF8, kind := .dir, mode := 0o000, modeExact := true, ownedByUid := false }]
  }
  let _ ← stepModelCheck "CAP_DAC_READ_SEARCH d000 R_OK" rsSt (.faccessat none "d000".toUTF8 { read := true } {}) .unit
  let _ ← stepModelCheck "CAP_DAC_READ_SEARCH d000 W_OK -> EACCES" rsSt (.faccessat none "d000".toUTF8 { write := true } {}) (.err Errno.EACCES)
  let sockSt := FilesState.withSeededTree {
    cwdPath := "/sock".toUTF8
    cwdEntries := [{ name := "p.sock".toUTF8, kind := .socket, mode := 0o555, modeExact := true }]
  }
  let _ ← stepModelCheck "0555 sock openat2 O_WRONLY -> EACCES" sockSt
    (.openat2 none "p.sock".toUTF8 { flags := { access := .wronly, creat := true, nofollow := true }, mode := 0o444, resolve := { inRoot := true } })
    (.err Errno.EACCES)
  let _ ← stepModelCheck "0555 sock openat O_RDONLY|O_TRUNC -> EACCES" sockSt
    (.openat none "p.sock".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "0555 sock openat O_RDONLY -> ENXIO" sockSt
    (.openat none "p.sock".toUTF8 { access := .rdonly } 0) (.err Errno.ENXIO)

/-- Deterministic userns, sticky, xdev, and overlay reproducers covering userns `capable_wrt_inode_uidgid`, `may_create_in_sticky`, `protected_symlinks`, `RESOLVE_NO_XDEV` `..` reset, overlayfs dead lower dir `rmdir` and `EFBIG` setgid stripping, and `fstatat(badfd, "", AT_EMPTY_PATH | AT_EACCESS)`. -/
def runUsernsStickyAndXdevReproducers : IO Unit := withTempSandbox "userns-xdev" fun _ => do
  let ops := defaultOps
  let nsCapSt := FilesState.withSeededTree {
    hasCapDacOverride := true
    hasCapDacReadSearch := true
    hasCapFowner := true
    proc1OwnedByUid := false
    proc1UidMapped := false
    proc1GidMapped := false
    cwdPath := "/rt_ns".toUTF8
    cwdEntries := [
      { name := "r_nogid".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false, uidMapped := true, gidMapped := false },
      { name := "r_nouid".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false, uidMapped := false, gidMapped := true },
      { name := "r_mapped".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false, uidMapped := true, gidMapped := true }
    ]
  }
  let _ ← stepModelCheck "unmapped gid CAP_DAC_OVERRIDE denied" nsCapSt (.openat none "r_nogid".toUTF8 roFlags 0) (.err Errno.EACCES)
  assertTrue "unmapped gid CAP_DAC_OVERRIDE cannot open" ((allowedStep nsCapSt (.openat none "r_nogid".toUTF8 roFlags 0) (.opened 0)).isNone)
  let _ ← stepModelCheck "unmapped gid CAP_FOWNER fchmodat allowed" nsCapSt (.fchmodat none "r_nogid".toUTF8 0o644) .unit
  assertTrue "unmapped gid CAP_FOWNER fchmodat rejects EPERM" ((allowedStep nsCapSt (.fchmodat none "r_nogid".toUTF8 0o644) (.err Errno.EPERM)).isNone)
  let _ ← stepModelCheck "unmapped uid CAP_DAC_OVERRIDE denied" nsCapSt (.openat none "r_nouid".toUTF8 roFlags 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "unmapped uid CAP_FOWNER fchmodat denied" nsCapSt (.fchmodat none "r_nouid".toUTF8 0o644) (.err Errno.EPERM)
  let _ ← stepModelCheck "mapped uid+gid CAP_DAC_OVERRIDE allowed" nsCapSt (.openat none "r_mapped".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "mapped uid+gid CAP_FOWNER fchmodat allowed" nsCapSt (.fchmodat none "r_mapped".toUTF8 0o644) .unit
  let _ ← stepModelCheck "userns /proc/1/fd/0 faccessat -> EACCES" nsCapSt (.faccessat none "/proc/1/fd/0".toUTF8 { read := true } { symlinkNofollow := true }) (.err Errno.EACCES)
  assertTrue "userns /proc/1/fd/0 faccessat cannot pass" ((allowedStep nsCapSt (.faccessat none "/proc/1/fd/0".toUTF8 { read := true } { symlinkNofollow := true }) .unit).isNone)

  let stickyOwnSt := FilesState.withSeededTree {
    hasCapFowner := true
    protectedRegular := 2
    protectedSymlinks := true
    cwdPath := "/rt_sticky".toUTF8
    cwdEntries := [
      { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { relDir := ["s1777".toUTF8], name := "u65534".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, ownerUid? := some 65534 },
      { relDir := ["s1777".toUTF8], name := "sym_other".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "tgt".toUTF8, ownedByUid := false, ownerUid? := some 65534 },
      { relDir := ["s1777".toUTF8], name := "sym_same".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "tgt".toUTF8, ownedByUid := false, ownerUid? := some 0 },
      { relDir := ["s1777".toUTF8], name := "tgt".toUTF8, kind := .reg, mode := 0o644, modeExact := true }
    ]
  }
  let _ ← stepModelCheck "sticky owned dir + unowned file O_CREAT -> EACCES" stickyOwnSt
    (.openat none "s1777/u65534".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.EACCES)
  assertTrue "sticky owned dir + unowned file O_CREAT cannot open"
    ((allowedStep stickyOwnSt (.openat none "s1777/u65534".toUTF8 { access := .rdwr, creat := true } 0o644) (.opened 0)).isNone)
  let _ ← stepModelCheck "protected_symlinks other owner -> EACCES" stickyOwnSt
    (.openat none "s1777/sym_other".toUTF8 roFlags 0) (.err Errno.EACCES)
  assertTrue "protected_symlinks other owner cannot open"
    ((allowedStep stickyOwnSt (.openat none "s1777/sym_other".toUTF8 roFlags 0) (.opened 0)).isNone)
  let _ ← stepModelCheck "protected_symlinks same dir owner -> ok" stickyOwnSt
    (.openat none "s1777/sym_same".toUTF8 roFlags 0) (.opened 0)

  let xdevSt := FilesState.withSeededTree {
    cwdPath := "/rt_xdev".toUTF8
    cwdMountId := 0
    cwdEntries := [
      { name := "sub".toUTF8, kind := .dir, mode := 0o755, modeExact := true },
      { name := "tgt".toUTF8, kind := .reg, mode := 0o644, modeExact := true },
      { name := "abs_sym".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "/rt_xdev/tgt".toUTF8 }
    ]
  }
  let _ ← stepModelCheck "RESOLVE_NO_XDEV abs_sym without dotdot -> EXDEV" xdevSt
    (.openat2 none "abs_sym".toUTF8 { resolve := { noXdev := true } }) (.err Errno.EXDEV)
  let _ ← stepModelCheck "RESOLVE_NO_XDEV sub/../abs_sym sets root -> ok" xdevSt
    (.openat2 none "sub/../abs_sym".toUTF8 { resolve := { noXdev := true } }) (.opened 0)

  let ovlDead0 := FilesState.withSeededTree {
    cwdPath := "/rt_ovl".toUTF8
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "ed".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { name := "sgid".toUTF8, kind := .reg, mode := 0o2750, modeExact := true }
    ]
  }
  let od1 ← stepModelCheck "ovl open ed" ovlDead0 (.openat none "ed".toUTF8 dirFlags 0) (.opened 0)
  let od2 ← stepModelCheck "ovl rmdir ed" od1 (.unlinkat none "ed".toUTF8 true) .unit
  let _ ← stepModelCheck "ovl dead ed openat . -> ok" od2 (.openat (some 0) ".".toUTF8 dirFlags 0) (.opened 1)
  let _ ← stepModelCheck "ovl dead ed openat foo -> ENOENT" od2 (.openat (some 0) "foo".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.ENOENT)
  let _ ← stepModelCheck "ovl dead ed getdents64 -> ENOENT" od2 (.getdents64 0 4096) (.err Errno.ENOENT)
  let _ ← stepModelCheck "ovl dead ed mkdirat -> ENOENT" od2 (.mkdirat (some 0) "sub".toUTF8 0o755) (.err Errno.ENOENT)
  let _ ← stepModelCheck "ovl dead ed symlinkat -> ENOENT" od2 (.symlinkat "x".toUTF8 (some 0) "sym".toUTF8) (.err Errno.ENOENT)
  let _ ← stepModelCheck "ovl dead ed fchmod -> ENOTDIR" od2 (.fchmod 0 0o700) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "ovl dead ed fchmodat . -> ENOTDIR" od2 (.fchmodat (some 0) ".".toUTF8 0o700) (.err Errno.ENOTDIR)

  let osg1 ← stepModelCheck "ovl open sgid" ovlDead0 (.openat none "sgid".toUTF8 { access := .wronly } 0) (.opened 0)
  let osg2 ← stepModelCheck "ovl write sgid EFBIG" osg1 (.write 0 "abcdef".toUTF8) (.err Errno.EFBIG)
  match assocGet osg2.fds 0 >>= fun d => assocGet osg2.inodes d.ino with
  | some svn => assertTrue "ovl write EFBIG strips S_ISGID" ((svn.mode &&& 0o7777) == 0o0750)
  | none => throw (IO.userError "missing sgid inode after EFBIG")

  let bfd ← assertOk "open for badfd fstatat" (← ops.openat none "bfd_tmp".toUTF8 rwCreatFlags 0o644)
  safeClose ops bfd
  let bfdStat ← ops.fstatat (some bfd) (ByteArray.mk #[]) { emptyPath := true, eaccess := true }
  assertErr "live fstatat(badfd, '', EMPTY|EACCESS) -> EINVAL" bfdStat Errno.EINVAL
  let (dmRes, _) := (modelOps.fstatat (some 99) (ByteArray.mk #[]) { emptyPath := true, eaccess := true }).run nsCapSt
  assertErr "modelOps fstatat(badfd, '', EMPTY|EACCESS) -> EINVAL" dmRes Errno.EINVAL
  let _ ← stepModelCheck "model badfd fstatat EMPTY|EACCESS -> EINVAL" nsCapSt
    (.fstatat (some 99) (ByteArray.mk #[]) { emptyPath := true, eaccess := true }) (.err Errno.EINVAL)
  assertTrue "model badfd fstatat EMPTY|EACCESS rejects EBADF"
    ((allowedStep nsCapSt (.fstatat (some 99) (ByteArray.mk #[]) { emptyPath := true, eaccess := true }) (.err Errno.EBADF)).isNone)

private def runCachedOpenat2AndMappedChmod : IO Unit := do
  let st := FilesState.withSeededTree {
    hasCapFowner := true
    cwdPath := "/rt_o2".toUTF8
    cwdEntries := [
      { name := "reg".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "x".toUTF8 },
      { name := "r_nogid".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false, uidMapped := true, gidMapped := false },
      { name := "r_nogid_ro".toUTF8, kind := .reg, mode := 0o444, modeExact := true, ownedByUid := false, uidMapped := true, gidMapped := false },
      { name := "r_nouid".toUTF8, kind := .reg, mode := 0o000, modeExact := true, ownedByUid := false, uidMapped := false, gidMapped := true }
    ]
  }
  let st1 ← stepModelCheck "open reg" st (.openat none "reg".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "openat2 O_CREAT|O_DIRECTORY|cached -> EINVAL" st1
    (.openat2 none "d".toUTF8 { flags := { creat := true, directory := true }, mode := 0o755, resolve := { cached := true } })
    (.err Errno.EINVAL)
  assertTrue "openat2 O_CREAT|O_DIRECTORY|cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 none "d".toUTF8 { flags := { creat := true, directory := true }, mode := 0o755, resolve := { cached := true } }) (.err Errno.EAGAIN)).isNone)
  let _ ← stepModelCheck "openat2 badfd|cached -> EBADF" st1
    (.openat2 (some 99) "reg".toUTF8 { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.EBADF)
  assertTrue "openat2 badfd|cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 (some 99) "reg".toUTF8 { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.EAGAIN)).isNone)
  let _ ← stepModelCheck "openat2 empty|cached -> ENOENT" st1
    (.openat2 none (ByteArray.mk #[]) { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.ENOENT)
  assertTrue "openat2 empty|cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 none (ByteArray.mk #[]) { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.EAGAIN)).isNone)
  let _ ← stepModelCheck "openat2 non-dir fd|cached -> ENOTDIR" st1
    (.openat2 (some 0) "x".toUTF8 { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.ENOTDIR)
  assertTrue "openat2 non-dir fd|cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 (some 0) "x".toUTF8 { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.EAGAIN)).isNone)
  let _ ← stepModelCheck "openat2 abs|beneath|cached -> EXDEV" st1
    (.openat2 none "/rt_o2/reg".toUTF8 { flags := roFlags, mode := 0, resolve := { beneath := true, cached := true } }) (.err Errno.EXDEV)
  assertTrue "openat2 beneath !cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 none "reg".toUTF8 { flags := roFlags, mode := 0, resolve := { beneath := true } }) (.err Errno.EAGAIN)).isNone)
  assertTrue "openat2 inRoot !cached rejects EAGAIN"
    ((allowedStep st1 (.openat2 none "reg".toUTF8 { flags := roFlags, mode := 0, resolve := { inRoot := true } }) (.err Errno.EAGAIN)).isNone)
  let p4096 := ByteArray.mk (Array.replicate 4096 (97 : UInt8))
  let _ ← stepModelCheck "openat2 len4096|creat|cached -> EAGAIN" st1
    (.openat2 none p4096 { flags := { creat := true }, mode := 0o644, resolve := { cached := true } }) (.err Errno.EAGAIN)
  let _ ← stepModelCheck "openat2 len4096|rdonly|cached -> ENAMETOOLONG" st1
    (.openat2 none p4096 { flags := roFlags, mode := 0, resolve := { cached := true } }) (.err Errno.ENAMETOOLONG)
  let (mRes, _) := (modelOps.openat2 (some 0) "x".toUTF8 { flags := roFlags, mode := 0, resolve := { cached := true } }).run st1
  assertErr "modelOps openat2 non-dir fd|cached -> ENOTDIR" mRes Errno.ENOTDIR
  let _ ← stepModelCheck "fchmodat uidMapped CAP_FOWNER -> ok" st (.fchmodat none "r_nogid".toUTF8 0o644) .unit
  let stNoGid ← stepModelCheck "open r_nogid_ro path" st (.openat none "r_nogid_ro".toUTF8 roFlags 0) (.opened 0)
  let (fcRes, _) := (modelOps.fchmod 0 0o644).run stNoGid
  assertOk "modelOps fchmod uidMapped CAP_FOWNER -> ok" fcRes
  let _ ← stepModelCheck "fchmodat r_nouid -> EPERM" st (.fchmodat none "r_nouid".toUTF8 0o644) (.err Errno.EPERM)

private def runSeccompDualFilterAndDetach : IO Unit := withTempSandbox "dual-seccomp" fun _ => do
  let ops := defaultOps
  let nrClose ← Fuzz.LinuxSyscall.Env.nrForSlot 2
  let nrFcntl ← Fuzz.LinuxSyscall.Env.nrForSlot 17
  let scStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if scStatus == 0 then
    match ← ops.openat none "sc_probe".toUTF8 rwCreatFlags 0o644 with
    | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 71
    | .ok fd =>
      if (← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose Errno.EPERM nrFcntl Errno.EBADF (0xffffffff : UInt32) 0) != 0 then
        Fuzz.LinuxSyscall.Env.exitImmediate 77
      match ← ops.close fd with
      | .error e =>
        if e != Errno.EPERM then Fuzz.LinuxSyscall.Env.exitImmediate 72
      | .ok () => Fuzz.LinuxSyscall.Env.exitImmediate 73
      match ← ops.fstat fd with
      | .ok _ => Fuzz.LinuxSyscall.Env.exitImmediate 0
      | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 74
  if scStatus != 2000 then
    throw (IO.userError s!"fd_box dual-filter close(EPERM)+fcntl(EBADF) probe failed: status={scStatus}")
  let scSt0 := FilesState.withSeededTree {
    ambientSeccomp := true
    cwdPath := "/rt_mc".toUTF8
    cwdEntries := [
      { name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "abc".toUTF8 },
      { name := "p.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true, pipeCapacity := .exact 16 }
    ]
  }
  let scSt1 ← stepModelCheck "open f 0" scSt0 (.openat none "f".toUTF8 roFlags 0) (.opened 0)
  let scSt2 ← stepModelCheck "open f 1" scSt1 (.openat none "f".toUTF8 roFlags 0) (.opened 1)
  let scSt3 ← stepModelCheck "flock 0" scSt2 (.flock 0 (.exclusive false)) .unit
  let scSt4 ← stepModelCheck "close 0 EIO detaches" scSt3 (.close 0) (.err Errno.EIO)
  assertTrue "EIO detaches hid 0" (!(scSt4.fds.any (·.1 == 0)))
  let _ ← stepModelCheck "fstat 0 after EIO -> EBADF" scSt4 (.fstat 0) (.err Errno.EBADF)
  let _ ← stepModelCheck "flock 1 succeeds after 0 EIO detach" scSt4 (.flock 1 (.exclusive true)) .unit
  let scStKeep ← stepModelCheck "close 0 EAGAIN keeps open" scSt3 (.close 0) (.err Errno.EAGAIN)
  assertTrue "EAGAIN keeps hid 0 open" (scStKeep.fds.any fun p => p.1 == 0 && p.2.closeState == .open)
  let _ ← stepModelCheck "flock 1 conflicts after 0 EAGAIN" scStKeep (.flock 1 (.exclusive true)) (.err Errno.EWOULDBLOCK)
  let _ ← stepModelCheck "fstat 0 ok after EAGAIN" scStKeep (.fstat 0) (.statted {
    kind := .reg, mode := 0o644, size := 3, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  })
  let pf1 ← stepModelCheck "open fifo rdwr" scSt0 (.openat none "p.fifo".toUTF8 { access := .rdwr, nonblock := true } 0) (.opened 0)
  let pf2 ← stepModelCheck "close fifo EIO detaches" pf1 (.close 0) (.err Errno.EIO)
  assertTrue "close fifo EIO detaches hid 0" (!(pf2.fds.any (·.1 == 0)))
  let _ ← stepModelCheck "open fifo wronly after EIO detach -> ENXIO" pf2 (.openat none "p.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.err Errno.ENXIO)
  let pfKeep ← stepModelCheck "close fifo EPERM keeps open" pf1 (.close 0) (.err Errno.EPERM)
  let _ ← stepModelCheck "open fifo wronly after EPERM -> ok" pfKeep (.openat none "p.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.opened 1)

private def runFifoSealsAndFsyncChecks : IO Unit := do
  let st := FilesState.withSeededTree {
    mountProfiles := [(0, { supportsSeals := true }), (4, { supportsSeals := true })]
    cwdPath := "/rt_fifo".toUTF8
    cwdEntries := [
      { name := "p64k.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true, pipeCapacity := .exact 16 },
      { name := "p4k.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true, pipeCapacity := .exact 1 },
      { name := "reg".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "abc".toUTF8 }
    ]
  }
  let s1 ← stepModelCheck "open p64k fifo" st (.openat none "p64k.fifo".toUTF8 { access := .rdwr, nonblock := true } 0) (.opened 0)
  assertTrue "fifo 64k write(8193) rejects EAGAIN"
    ((allowedStep s1 (.write 0 (ByteArray.mk (Array.replicate 8193 65))) (.err Errno.EAGAIN)).isNone)
  let s2 ← stepModelCheck "write 4096 to 64k fifo" s1 (.write 0 (ByteArray.mk (Array.replicate 4096 65))) (.u32 4096)
  let s3 ← stepModelCheck "read 1 from 64k fifo" s2 (.read 0 1) (.bytes (ByteArray.mk #[65]))
  assertTrue "64k fifo write(2) after 4096-1 rejects EAGAIN"
    ((allowedStep s3 (.write 0 (ByteArray.mk #[66, 67])) (.err Errno.EAGAIN)).isNone)
  let r5 ← stepModelCheck "p64k write(5)" s1 (.write 0 "hello".toUTF8) (.u32 5)
  let r61k ← stepModelCheck "p64k write(65537) -> 61441" r5 (.write 0 (ByteArray.mk (Array.replicate 65537 70))) (.u32 61441)
  let _ ← stepModelCheck "p64k write(8192) -> EAGAIN" r61k (.write 0 (ByteArray.mk (Array.replicate 8192 67))) (.err Errno.EAGAIN)
  let p4k1 ← stepModelCheck "open p4k fifo" st (.openat none "p4k.fifo".toUTF8 { access := .rdwr, nonblock := true } 0) (.opened 0)
  let p4k2 ← stepModelCheck "write 4096 to 4k fifo" p4k1 (.write 0 (ByteArray.mk (Array.replicate 4096 65))) (.u32 4096)
  let p4k3 ← stepModelCheck "read 1 from 4k fifo" p4k2 (.read 0 1) (.bytes (ByteArray.mk #[65]))
  let _ ← stepModelCheck "4k fifo write(2) -> EAGAIN" p4k3 (.write 0 (ByteArray.mk #[66, 67])) (.err Errno.EAGAIN)
  let sr ← stepModelCheck "open sealable reg" st (.openat none "reg".toUTF8 { access := .rdwr } 0) (.opened 0)
  let _ ← stepModelCheck "F_GET_SEALS sealable reg -> 1" sr (.fcntl 0 .getSeals) (.u32 1)
  assertTrue "F_GET_SEALS sealable reg rejects EINVAL"
    ((allowedStep sr (.fcntl 0 .getSeals) (.err Errno.EINVAL)).isNone)
  let extSt := FilesState.withSeededTree {
    mountProfiles := [(0, { supportsSeals := false }), (4, { supportsSeals := false })]
    cwdPath := "/rt_ext".toUTF8
    cwdEntries := [{ name := "reg".toUTF8, kind := .reg, mode := 0o644, modeExact := true }]
  }
  let er ← stepModelCheck "open ext4 reg" extSt (.openat none "reg".toUTF8 { access := .rdwr } 0) (.opened 0)
  let _ ← stepModelCheck "F_GET_SEALS ext4 reg -> EINVAL" er (.fcntl 0 .getSeals) (.err Errno.EINVAL)
  let (gRes, _) := (modelOps.fcntl 0 .getSeals).run er
  assertErr "modelOps F_GET_SEALS ext4 reg -> EINVAL" gRes Errno.EINVAL
  assertTrue "fsync fifo rejects ok" ((allowedStep s1 (.fsync 0) .unit).isNone)
  let _ ← stepModelCheck "fsync fifo -> EINVAL" s1 (.fsync 0) (.err Errno.EINVAL)
  let dn ← stepModelCheck "open /dev/null" st (.openat none "/dev/null".toUTF8 roFlags 0) (.opened 0)
  assertTrue "fsync /dev/null rejects ok" ((allowedStep dn (.fsync 0) .unit).isNone)
  let _ ← stepModelCheck "fsync /dev/null -> EINVAL" dn (.fsync 0) (.err Errno.EINVAL)

private def runErofsAndGetdentsChecks : IO Unit := do
  let deadOvl := FilesState.withSeededTree {
    cwdPath := "/rt_ovl2".toUTF8
    cwdOverlayMerged := true
    mountProfiles := [(4, { isOverlay := true })]
    cwdEntries := [{ name := "ed".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true }]
  }
  let ovlEd := match assocGet deadOvl.inodes deadOvl.cwdIno with
    | some cvn =>
      let data' := match cvn.data with
        | .dir dd => InodeData.dir { dd with lifecycle := .unlinked }
        | d => d
      { deadOvl with inodes := assocSet deadOvl.inodes deadOvl.cwdIno { cvn with data := data', nlink := 0 }, cwdPath := .unbound deadOvl.cwdPath.bytes }
    | none => deadOvl
  let _ ← stepModelCheck "dead ovl getcwd -> ENOENT" ovlEd (.getcwd 256) (.err Errno.ENOENT)
  assertTrue "dead ovl getcwd rejects bytes" ((allowedStep ovlEd (.getcwd 256) (.bytes "/rt_ovl2".toUTF8)).isNone)
  let (gcRes, _) := (modelOps.getcwd 256).run ovlEd
  assertErr "modelOps dead ovl getcwd -> ENOENT" gcRes Errno.ENOENT
  let roSt := FilesState.withSeededTree {
    cwdPath := "/rt_ro".toUTF8
    mountProfiles := [(4, { readOnly := true })]
    cwdEntries := [{ name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true }]
  }
  let roOpen ← stepModelCheck "ro open rdonly" roSt (.openat none "f".toUTF8 roFlags 0) (.opened 0)
  let (roWr, _) := (modelOps.openat none "new".toUTF8 rwCreatFlags 0o644).run roSt
  assertErr "modelOps EROFS openat" roWr Errno.EROFS
  let (roSym, _) := (modelOps.symlinkat "f".toUTF8 none "s".toUTF8).run roSt
  assertErr "modelOps EROFS symlinkat" roSym Errno.EROFS
  let (roFca, _) := (modelOps.fchmodat none "f".toUTF8 0o600).run roSt
  assertErr "modelOps EROFS fchmodat" roFca Errno.EROFS
  let (roFc, _) := (modelOps.fchmod 0 0o600).run roOpen
  assertErr "modelOps EROFS fchmod" roFc Errno.EROFS
  let longName := ByteArray.mk (Array.replicate 255 (120 : UInt8))
  let gd0 := FilesState.withSeededTree {
    cwdPath := "/rt_gd".toUTF8
    cwdEntries := [{ name := longName, kind := .reg, mode := 0o644, modeExact := true }]
  }
  let (gdRes0, gd1) := (modelOps.openat none ".".toUTF8 dirFlags 0).run gd0
  let dfd ← assertOk "open dir for getdents64" gdRes0
  let (d1, gd2) := (modelOps.getdents64 dfd 24).run gd1
  let b1 ← assertOk "modelOps getdents64 1 emits ." d1
  assertTrue "getdents64 1 non-empty" (b1.size == 24)
  let (d2, gd3) := (modelOps.getdents64 dfd 24).run gd2
  let b2 ← assertOk "modelOps getdents64 2 emits .." d2
  assertTrue "getdents64 2 non-empty" (b2.size == 24)
  let (d3, _) := (modelOps.getdents64 dfd 24).run gd3
  assertErr "modelOps getdents64 3 long child -> EINVAL" d3 Errno.EINVAL

/-- Deterministic cached-openat2, mapped-chmod, and seccomp reproducers covering `openat2` `RESOLVE_CACHED` validation order, `fchmod`/`fchmodat` `uidMapped`, `fd_box.h` dual-filter `close`, `maybeClosed`, FIFO `EAGAIN`, `F_GET_SEALS`, `fsync`, `overlayfs` dead `getcwd`, `EROFS`, and `modelOps.getdents64`. -/
def runCachedOpenat2AndSeccompReproducers : IO Unit := do
  runCachedOpenat2AndMappedChmod
  runSeccompDualFilterAndDetach
  runFifoSealsAndFsyncChecks
  runErofsAndGetdentsChecks

/-- Deterministic memfd-seal, special-trunc, and overlay copy-up reproducers covering `memfd` seals/`F_ADD_SEALS`, `O_RDONLY|O_TRUNC` on special files, uncalibrated FIFO bounds, `S_ISGID` stripping on `fchmod`/`fchmodat`, `renameat2` sticky-before-dest order, `overlayfs` lower-hardlink copy-up, 3-syscall `seccomp`, `openat2` `..` `EAGAIN`, and `getdents64` small buffers. -/
def runMemfdSealsAndSpecialTruncReproducers : IO Unit := do
  let memfdBase : FilesState := {
    inodes := [
      (0, { data := .dir { parentIno := 0, lifecycle := .live }, mode := 0o755, nlink := 2 }),
      (1, { data := .reg (RegData.ofBytes "hi".toUTF8 (.sealable 0)), mode := 0o644, nlink := 1 })
    ]
    fds := [
      (0, { ino := 1, access := .rdwr }),
      (1, { ino := 1, access := .rdonly })
    ]
    cwdPath := .bound "/tmp".toUTF8
    nextIno := 2
    nextHid := 2
  }
  let _ ← stepModelCheck "memfd rdonly addSeals badmask -> EPERM" memfdBase (.fcntl 1 (.addSeals 0x80000000)) (.err Errno.EPERM)
  assertTrue "memfd rdonly addSeals badmask rejects EINVAL"
    ((allowedStep memfdBase (.fcntl 1 (.addSeals 0x80000000)) (.err Errno.EINVAL)).isNone)
  let mf1 ← stepModelCheck "memfd addSeals FUTURE_WRITE|SHRINK" memfdBase (.fcntl 0 (.addSeals 0x12)) (.u32 0)
  let _ ← stepModelCheck "memfd write sealed -> EPERM" mf1 (.write 0 "x".toUTF8) (.err Errno.EPERM)
  assertTrue "memfd write sealed rejects u32" ((allowedStep mf1 (.write 0 "x".toUTF8) (.u32 1)).isNone)
  let mfGrow ← stepModelCheck "memfd addSeals GROW" memfdBase (.fcntl 0 (.addSeals 0x04)) (.u32 0)
  let _ ← stepModelCheck "memfd grow blocked -> EPERM" mfGrow (.write 0 "abc".toUTF8) (.err Errno.EPERM)
  let _ ← stepModelCheck "memfd overwrite in-bounds ok" mfGrow (.write 0 "x".toUTF8) (.u32 1)

  let specRoTrunc := FilesState.withSeededTree {
    cwdPath := "/rt_spec".toUTF8
    cwdEntries := [
      { name := "p444.fifo".toUTF8, kind := .fifo, mode := 0o444, modeExact := true },
      { name := "s444.sock".toUTF8, kind := .socket, mode := 0o444, modeExact := true },
      { name := "n444".toUTF8, kind := .charDev, devKind? := some .nullDev, mode := 0o444, modeExact := true }
    ]
  }
  let _ ← stepModelCheck "0444 fifo O_RDONLY|O_TRUNC -> EACCES" specRoTrunc
    (.openat none "p444.fifo".toUTF8 { access := .rdonly, nonblock := true, trunc := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "0444 sock O_RDONLY|O_TRUNC -> EACCES" specRoTrunc
    (.openat none "s444.sock".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "0444 null O_RDONLY|O_TRUNC -> EACCES" specRoTrunc
    (.openat none "n444".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.EACCES)
  let specCap := { specRoTrunc with cred := { capDacOverride := true } }
  let _ ← stepModelCheck "0444 null O_RDONLY|O_TRUNC w/ DAC_OVERRIDE -> ok" specCap
    (.openat none "n444".toUTF8 { access := .rdonly, trunc := true } 0) (.opened 0)

  let uncalSt := FilesState.withSeededTree {
    cwdPath := "/rt_pipe".toUTF8
    cwdEntries := [{ name := "up.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true, pipeCapacity := .uncalibrated 2 16 }]
  }
  let up1 ← stepModelCheck "open uncal fifo" uncalSt (.openat none "up.fifo".toUTF8 { access := .rdwr, nonblock := true } 0) (.opened 0)
  assertTrue "uncal(2,16) rejects EAGAIN on <=8KiB"
    ((allowedStep up1 (.write 0 (ByteArray.mk (Array.replicate 8192 65))) (.err Errno.EAGAIN)).isNone)
  let up2 ← stepModelCheck "uncal(2,16) write 4096" up1 (.write 0 (ByteArray.mk (Array.replicate 4096 65))) (.u32 4096)
  let up3 ← stepModelCheck "uncal(2,16) write second 4096" up2 (.write 0 (ByteArray.mk (Array.replicate 4096 65))) (.u32 4096)
  let _ ← stepModelCheck "uncal(2,16) allows EAGAIN at >8KiB after 2 slots" up3
    (.write 0 (ByteArray.mk (Array.replicate 4097 66))) (.err Errno.EAGAIN)

  let sgidNoGrp := FilesState.withSeededTree {
    cwdPath := "/rt_sgid".toUTF8
    cwdEntries := [{ name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, inGroup := false }]
  }
  let sg1 ← stepModelCheck "fchmodat S_ISGID stripped" sgidNoGrp (.fchmodat none "f".toUTF8 0o2755) .unit
  let _ ← stepModelCheck "fstat sees 0755" sg1 (.fstatat none "f".toUTF8 {}) (.statted {
    kind := .reg, mode := 0o755, size := 0, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  })
  let sgidGrp := FilesState.withSeededTree {
    cwdPath := "/rt_sgid2".toUTF8
    cwdEntries := [{ name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, inGroup := true }]
  }
  let sg2 ← stepModelCheck "fchmodat inGroup keeps S_ISGID" sgidGrp (.fchmodat none "f".toUTF8 0o2755) .unit
  let _ ← stepModelCheck "fstat sees 02755" sg2 (.fstatat none "f".toUTF8 {}) (.statted {
    kind := .reg, mode := 0o2755, size := 0, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  })

  let renSt := FilesState.withSeededTree {
    cwdPath := "/rt_ren".toUTF8
    cwdEntries := [
      { name := "sdir".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := false },
      { relDir := ["sdir".toUTF8], name := "unowned".toUTF8, kind := .reg, mode := 0o644, modeExact := true, ownedByUid := false },
      { name := "ro_dst".toUTF8, kind := .dir, mode := 0o555, modeExact := true }
    ]
  }
  let _ ← stepModelCheck "renameat2 sticky EPERM before dest EACCES" renSt
    (.renameat2 none "sdir/unowned".toUTF8 none "ro_dst/out".toUTF8 {}) (.err Errno.EPERM)
  assertTrue "renameat2 sticky rejects EACCES"
    ((allowedStep renSt (.renameat2 none "sdir/unowned".toUTF8 none "ro_dst/out".toUTF8 {}) (.err Errno.EACCES)).isNone)

  let ovlHl0 := FilesState.withSeededTree {
    cwdPath := "/rt_ovl3".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "hl1".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 7 },
      { name := "hl2".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 7 }
    ]
  }
  let oh1 ← stepModelCheck "ovl open hl1 rdwr" ovlHl0 (.openat none "hl1".toUTF8 { access := .rdwr } 0) (.opened 0)
  let oh2 ← stepModelCheck "ovl write hl1" oh1 (.write 0 "up!!".toUTF8) (.u32 4)
  let oh3 ← stepModelCheck "ovl open hl2 rdonly" oh2 (.openat none "hl2".toUTF8 roFlags 0) (.opened 1)
  let _ ← stepModelCheck "ovl read hl2 untouched" oh3 (.read 1 4) (.bytes "orig".toUTF8)

  let sc0 := FilesState.withSeededTree {
    ambientSeccomp := true
    cwdPath := "/rt_sc".toUTF8
    cwdEntries := [{ name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "abc".toUTF8 }]
  }
  let sc1 ← stepModelCheck "sc open 0" sc0 (.openat none "f".toUTF8 roFlags 0) (.opened 0)
  let sc2 ← stepModelCheck "sc open 1" sc1 (.openat none "f".toUTF8 roFlags 0) (.opened 1)
  let sc3 ← stepModelCheck "sc close 0 EINTR" sc2 (.close 0) (.err Errno.EINTR)
  let sc4 ← stepModelCheck "sc fcntl 0 EBADF drops" sc3 (.fcntl 0 .getFd) (.err Errno.EBADF)
  let _ ← stepModelCheck "sc close 0 again EBADF" sc4 (.close 0) (.err Errno.EBADF)
  let sc5 ← stepModelCheck "sc close 1 EINTR" sc4 (.close 1) (.err Errno.EINTR)
  let sc6 ← stepModelCheck "sc fstat 1 EBADF drops" sc5 (.fstat 1) (.err Errno.EBADF)
  let _ ← stepModelCheck "sc fcntl 1 again EBADF" sc6 (.fcntl 1 .getFd) (.err Errno.EBADF)

  let o2St := FilesState.withSeededTree {
    cwdPath := "/rt_o2b".toUTF8
    cwdEntries := [
      { name := "sub".toUTF8, kind := .dir, mode := 0o755, modeExact := true },
      { name := "esc".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "../out".toUTF8 }
    ]
  }
  let _ ← stepModelCheck "openat2 .. symlink RESOLVE_BENEATH allows EAGAIN" o2St
    (.openat2 none "esc".toUTF8 { resolve := { beneath := true } }) (.err Errno.EAGAIN)

  let gdName := ByteArray.mk (Array.replicate 255 120)
  let gdSt := FilesState.withSeededTree {
    cwdPath := "/rt_gd2".toUTF8
    cwdEntries := [{ name := gdName, kind := .reg, mode := 0o644, modeExact := true }]
  }
  let gd1 ← stepModelCheck "getdents open ." gdSt (.openat none ".".toUTF8 dirFlags 0) (.opened 0)
  let _ ← stepModelCheck "getdents 24B -> EINVAL" gd1 (.getdents64 0 24) (.err Errno.EINVAL)

private def runOverlayHardlinkAndDirReproducers : IO Unit := do
  let mkOvlHlTree := FilesState.withSeededTree {
    cwdPath := "/rt_ovl4".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "hl_lo1".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "hl_lo2".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "sym_hla".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "hl_lo1".toUTF8, mayCopyUp := true }
    ]
  }
  let hl1Ino ← match resolvePath mkOvlHlTree none "hl_lo1".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"hl_lo1 resolve failed: {e}")
  let hl2Ino ← match resolvePath mkOvlHlTree none "hl_lo2".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"hl_lo2 resolve failed: {e}")
  assertTrue "lower hardlinks share one InodeId" (hl1Ino == hl2Ino)
  let dummyStat : StatInfo := {
    kind := .reg, mode := 0o644, size := 4, dev := 1, ino := 1, nlink := 2,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let stA1 ← stepModelCheck "open hl_lo1 rdonly" mkOvlHlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stA2 ← stepModelCheck "open hl_lo2 rdonly" stA1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stA3 ← stepModelCheck "fchmod hl_lo1 fd -> 0600" stA2 (.fchmod 0 0o600) .unit
  let _ ← stepModelCheck "fstat hl_lo1 fd sees 0600" stA3 (.fstat 0) (.statted { dummyStat with mode := 0o600, nlink := 1 })
  let _ ← stepModelCheck "fstat hl_lo2 fd stays 0644" stA3 (.fstat 1) (.statted { dummyStat with mode := 0o644, nlink := 2 })
  let _ ← stepModelCheck "fstatat hl_lo2 stays 0644" stA3 (.fstatat none "hl_lo2".toUTF8 {}) (.statted { dummyStat with mode := 0o644, nlink := 2 })

  let stB1 ← stepModelCheck "open hl_lo1 rdonly" mkOvlHlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stB2 ← stepModelCheck "unlink hl_lo1" stB1 (.unlinkat none "hl_lo1".toUTF8 false) .unit
  let _ ← stepModelCheck "fchmod unlinked lower fd -> EEXIST" stB2 (.fchmod 0 0o600) (.err Errno.EEXIST)
  let _ ← stepModelCheck "fstatat hl_lo2 stays 0644" stB2 (.fstatat none "hl_lo2".toUTF8 {}) (.statted { dummyStat with mode := 0o644, nlink := 2 })

  let stC1 ← stepModelCheck "fchmodat sym_hla -> 0600" mkOvlHlTree (.fchmodat none "sym_hla".toUTF8 0o600) .unit
  let _ ← stepModelCheck "sym_hla remains symlink" stC1 (.readlinkat none "sym_hla".toUTF8 32) (.bytes "hl_lo1".toUTF8)
  let _ ← stepModelCheck "fstatat hl_lo1 sees 0600" stC1 (.fstatat none "hl_lo1".toUTF8 {}) (.statted { dummyStat with mode := 0o600, nlink := 1 })
  let _ ← stepModelCheck "fstatat hl_lo2 stays 0644" stC1 (.fstatat none "hl_lo2".toUTF8 {}) (.statted { dummyStat with mode := 0o644, nlink := 2 })

  let stD1 ← stepModelCheck "open hl_lo1 rdonly" mkOvlHlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stD1p := FilesState.attachProcFdLink stD1 "17".toUTF8 hl1Ino 0
  let stD2 ← stepModelCheck "open /proc/self/fd/17 rdwr" stD1p (.openat none "/proc/self/fd/17".toUTF8 { access := .rdwr } 0) (.opened 1)
  let stD3 ← stepModelCheck "write reopened fd" stD2 (.write 1 "ABCD".toUTF8) (.u32 4)
  let _ ← stepModelCheck "original rdonly fd sees ABCD" stD3 (.read 0 4) (.bytes "ABCD".toUTF8)
  let stD4 ← stepModelCheck "open hl_lo2 rdonly" stD3 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 2)
  let _ ← stepModelCheck "hl_lo2 stays orig" stD4 (.read 2 4) (.bytes "orig".toUTF8)
  let stD5 ← stepModelCheck "unlink hl_lo1" stD1p (.unlinkat none "hl_lo1".toUTF8 false) .unit
  let _ ← stepModelCheck "reopen unlinked lower procMagic rdwr -> EEXIST" stD5
    (.openat none "/proc/self/fd/17".toUTF8 { access := .rdwr } 0) (.err Errno.EEXIST)

  let mkOvlDirTree := FilesState.withSeededTree {
    cwdPath := "/rt_ovld".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "empty_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { name := "ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { relDir := ["ldir".toUTF8], name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, mayCopyUp := true }
    ]
  }
  let _ ← stepModelCheck "renameat2 empty_ldir -> non-empty ldir ENOTEMPTY" mkOvlDirTree
    (.renameat2 none "empty_ldir".toUTF8 none "ldir".toUTF8 {}) (.err Errno.ENOTEMPTY)
  let _ ← stepModelCheck "renameat2 empty_ldir -> non-empty ldir EXDEV" mkOvlDirTree
    (.renameat2 none "empty_ldir".toUTF8 none "ldir".toUTF8 {}) (.err Errno.EXDEV)
  let stF1 ← stepModelCheck "open empty_ldir" mkOvlDirTree (.openat none "empty_ldir".toUTF8 dirFlags 0) (.opened 0)
  let stF2 ← stepModelCheck "fchmod empty_ldir 0o4755" stF1 (.fchmod 0 0o4755) .unit
  let stF3 ← stepModelCheck "rmdir empty_ldir" stF2 (.unlinkat none "empty_ldir".toUTF8 true) .unit
  let _ ← stepModelCheck "fstat removed merged dir sees nlink=1" stF3 (.fstat 0)
    (.statted { dummyStat with kind := .dir, mode := 0o4755, nlink := 1 })
  let _ ← stepModelCheck "fchmod removed merged dir succeeds" stF3 (.fchmod 0 0o700) .unit
  let _ ← stepModelCheck "getdents64 removed merged dir -> ENOENT" stF3 (.getdents64 0 64) (.err Errno.ENOENT)

  let stGOpen0 ← stepModelCheck "open fd 0" mkOvlHlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stGOpen1 ← stepModelCheck "open fd 1" stGOpen0 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stG0 := FilesState.attachProcFdLink stGOpen1 "17".toUTF8 1 0
  let procSt1 : StatInfo := {
    kind := .symlink, mode := 0o700, size := 64, dev := 24, ino := 287203454, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let stG1 ← stepModelCheck "fstatat /proc/self/fd/17 binds dev/ino" stG0
    (.fstatat none "/proc/self/fd/17".toUTF8 { symlinkNofollow := true }) (.statted procSt1)
  let stG2 := FilesState.detachProcFdLink stG1 "17".toUTF8
  let stG3 := FilesState.attachProcFdLink stG2 "17".toUTF8 hl1Ino 1
  let _ ← stepModelCheck "reused /proc/self/fd/17 allows same dev/ino" stG3
    (.fstatat none "/proc/self/fd/17".toUTF8 { symlinkNofollow := true }) (.statted procSt1)

private def runStickyOverlayAndSealReproducers : IO Unit := do
  let stickyTree := FilesState.withSeededTree {
    cwdPath := "/rt_sticky2".toUTF8
    protectedRegular := 2
    cwdEntries := [
      { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { relDir := ["s1777".toUTF8], name := "reg666".toUTF8, kind := .reg, mode := 0o666, modeExact := true,
        bytes := "sticky\n".toUTF8, ownedByUid := false, inGroup := false, ownerUid? := some 1 },
      { name := "f640".toUTF8, kind := .reg, mode := 0o640, modeExact := true,
        bytes := "grp\n".toUTF8, ownedByUid := false, inGroup := true, ownerUid? := some 1 },
      { name := "f604".toUTF8, kind := .reg, mode := 0o604, modeExact := true,
        bytes := "oth\n".toUTF8, ownedByUid := false, inGroup := true, ownerUid? := some 1 }
    ]
  }
  let regIno ← match resolvePath stickyTree none "s1777/reg666".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"reg666 resolve failed: {e}")
  let stA1 ← stepModelCheck "open s1777/reg666 rdonly" stickyTree
    (.openat none "s1777/reg666".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "open s1777/reg666 O_CREAT blocked -> EACCES" stA1
    (.openat none "s1777/reg666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let stA2 := FilesState.attachProcFdLink stA1 "17".toUTF8 regIno 0
  let _ ← stepModelCheck "open /proc/self/fd/17 O_CREAT bypasses sticky check" stA2
    (.openat none "/proc/self/fd/17".toUTF8 { access := .rdwr, creat := true } 0o644) (.opened 1)

  let _ ← stepModelCheck "f640 inGroup O_RDONLY succeeds" stickyTree
    (.openat none "f640".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "f640 inGroup O_WRONLY -> EACCES" stickyTree
    (.openat none "f640".toUTF8 { access := .wronly } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "f604 inGroup O_RDONLY -> EACCES" stickyTree
    (.openat none "f604".toUTF8 roFlags 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "faccessat f640 R_OK ok" stickyTree
    (.faccessat none "f640".toUTF8 { read := true } {}) .unit
  let _ ← stepModelCheck "faccessat f604 R_OK -> EACCES" stickyTree
    (.faccessat none "f604".toUTF8 { read := true } {}) (.err Errno.EACCES)

  let ovlTree := FilesState.withSeededTree {
    cwdPath := "/rt_ovl5".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "hl_lo1".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "hl_lo2".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "empty_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { name := "ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { relDir := ["ldir".toUTF8], name := "f".toUTF8, kind := .reg, mode := 0o644, modeExact := true, mayCopyUp := true }
    ]
  }
  let hlIno ← match resolvePath ovlTree none "hl_lo1".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"hl_lo1 resolve failed: {e}")
  let dummyStat : StatInfo := {
    kind := .reg, mode := 0o644, size := 4, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let stC1 ← stepModelCheck "open hl_lo1" ovlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stC2 ← stepModelCheck "open hl_lo2" stC1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stC2p := FilesState.attachProcFdLink stC2 "18".toUTF8 hlIno 1
  let stC3 ← stepModelCheck "rename hl_lo1 -> hl_lo2 unlinks & copies up" stC2p
    (.renameat2 none "hl_lo1".toUTF8 none "hl_lo2".toUTF8 {}) .unit
  let _ ← stepModelCheck "hl_lo1 unlinked -> ENOENT" stC3 (.fstatat none "hl_lo1".toUTF8 {}) (.err Errno.ENOENT)
  let _ ← stepModelCheck "hl_lo2 nlink=1" stC3 (.fstatat none "hl_lo2".toUTF8 {}) (.statted dummyStat)
  let stC4 ← stepModelCheck "fchmod fd0 -> 0600" stC3 (.fchmod 0 0o600) .unit
  let _ ← stepModelCheck "fd0 sees 0600 nlink=1" stC4 (.fstat 0) (.statted { dummyStat with mode := 0o600, nlink := 1 })
  let _ ← stepModelCheck "fd1 stays 0644 nlink=2" stC4 (.fstat 1) (.statted { dummyStat with mode := 0o644, nlink := 2 })
  let _ ← stepModelCheck "reopen detached fd1 procMagic rdwr -> EEXIST" stC4
    (.openat none "/proc/self/fd/18".toUTF8 { access := .rdwr } 0) (.err Errno.EEXIST)

  let stD1 ← stepModelCheck "open hl_lo1" ovlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stD2 ← stepModelCheck "open hl_lo2" stD1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stD3 ← stepModelCheck "exchange hl_lo1 <-> hl_lo2 copies up both" stD2
    (.renameat2 none "hl_lo1".toUTF8 none "hl_lo2".toUTF8 { exchange := true }) .unit
  let _ ← stepModelCheck "hl_lo1 nlink=1" stD3 (.fstatat none "hl_lo1".toUTF8 {}) (.statted dummyStat)
  let _ ← stepModelCheck "hl_lo2 nlink=1" stD3 (.fstatat none "hl_lo2".toUTF8 {}) (.statted dummyStat)
  let stD4 ← stepModelCheck "fchmodat hl_lo1 -> 0600" stD3 (.fchmodat none "hl_lo1".toUTF8 0o600) .unit
  let _ ← stepModelCheck "fd1 (moved to hl_lo1) sees 0600" stD4 (.fstat 1) (.statted { dummyStat with mode := 0o600, nlink := 1 })
  let _ ← stepModelCheck "fd0 (moved to hl_lo2) stays 0644" stD4 (.fstat 0) (.statted { dummyStat with mode := 0o644, nlink := 1 })

  let _ ← stepModelCheck "rename hl_lo1 -> hl_lo2 RENAME_WHITEOUT allows EINVAL" ovlTree
    (.renameat2 none "hl_lo1".toUTF8 none "hl_lo2".toUTF8 { whiteout := true }) (.err Errno.EINVAL)
  let _ ← stepModelCheck "rename empty_ldir -> ldir RENAME_WHITEOUT allows EINVAL" ovlTree
    (.renameat2 none "empty_ldir".toUTF8 none "ldir".toUTF8 { whiteout := true }) (.err Errno.EINVAL)
  let _ ← stepModelCheck "self-rename hl_lo1 RENAME_WHITEOUT allows EINVAL" ovlTree
    (.renameat2 none "hl_lo1".toUTF8 none "hl_lo1".toUTF8 { whiteout := true }) (.err Errno.EINVAL)

  let stF1 ← stepModelCheck "open empty_ldir" ovlTree
    (.openat none "empty_ldir".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let stF2 ← stepModelCheck "unlink empty_ldir" stF1
    (.unlinkat none "empty_ldir".toUTF8 true) .unit
  let stF3 ← stepModelCheck "recreate empty_ldir" stF2
    (.mkdirat none "empty_ldir".toUTF8 0o755) .unit
  let _ ← stepModelCheck "fchmod old dead lower dir fd allows unit" stF3
    (.fchmod 0 0o700) .unit
  let _ ← stepModelCheck "fchmod old dead lower dir fd allows ENOTDIR" stF3
    (.fchmod 0 0o700) (.err Errno.ENOTDIR)

  let longName255 := ByteArray.mk (Array.replicate 255 (115 : UInt8))
  let gdCacheTree := FilesState.withSeededTree {
    cwdPath := "/rt_gd3".toUTF8
    cwdEntries := [
      { name := "d255".toUTF8, kind := .dir, mode := 0o755, modeExact := true },
      { relDir := ["d255".toUTF8], name := longName255, kind := .reg, mode := 0o644, modeExact := true }
    ]
  }
  let stG1 ← stepModelCheck "open d255" gdCacheTree
    (.openat none "d255".toUTF8 roFlags 0) (.opened 0)
  let stG2 ← stepModelCheck "getdents64 0 -> EINVAL" stG1
    (.getdents64 0 0) (.err Errno.EINVAL)
  let stG3 ← stepModelCheck "rename d255/s255 -> hl2" stG2
    (.renameat2 none ("d255/".toUTF8 ++ longName255) none "hl2".toUTF8 {}) .unit
  let _ ← stepModelCheck "cached getdents64 32 -> EINVAL" stG3
    (.getdents64 0 32) (.err Errno.EINVAL)

  let mem4k := FilesState.withSeededTree { cwdPath := "/rt_mem".toUTF8 }
  let mem4kInodes := assocSet mem4k.inodes 90
    { data := .reg (RegData.ofBytes (ByteArray.mk (Array.replicate 4096 (66 : UInt8))) (.sealable 0x04)),
      mode := 0o644, nlink := 1 }
  let mem4kFds := assocSet mem4k.fds 0
    { ino := 90, access := .wronly, pos := .byteOffset 151 }
  let mem4kSt := { mem4k with inodes := mem4kInodes, fds := mem4kFds }
  let _ ← stepModelCheck "F_SEAL_GROW partial page write 3945 ok" mem4kSt
    (.write 0 (ByteArray.mk (Array.replicate 8192 (67 : UInt8)))) (.u32 3945)

  let stickySymTree := FilesState.withSeededTree {
    cwdPath := "/rt_sym".toUTF8
    protectedRegular := 2
    protectedFifos := 1
    cwdEntries := [
      { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { relDir := ["s1777".toUTF8], name := "sym_other".toUTF8, kind := .symlink, symlinkTarget := "sub/a".toUTF8, ownedByUid := false, ownerUid? := some 1 },
      { relDir := ["s1777".toUTF8], name := "sym_same".toUTF8, kind := .symlink, symlinkTarget := "sub/a".toUTF8, ownedByUid := true, ownerUid? := some 0 }
    ]
  }
  let _ ← stepModelCheck "sticky sym_other O_CREAT|O_NOFOLLOW -> EACCES" stickySymTree
    (.openat none "s1777/sym_other".toUTF8 { access := .wronly, creat := true, nofollow := true } 0o644)
    (.err Errno.EACCES)
  let _ ← stepModelCheck "sticky sym_same O_CREAT|O_NOFOLLOW -> ELOOP" stickySymTree
    (.openat none "s1777/sym_same".toUTF8 { access := .wronly, creat := true, nofollow := true } 0o644)
    (.err Errno.ELOOP)
  let _ ← stepModelCheck "sticky sym_other O_NOFOLLOW (no creat) -> ELOOP" stickySymTree
    (.openat none "s1777/sym_other".toUTF8 { access := .wronly, nofollow := true } 0o644)
    (.err Errno.ELOOP)

private def runOverlayStickyAndMountReproducers : IO Unit := do
  let roFlags : OpenFlags := { access := .rdonly }
  let ovlTree := FilesState.withSeededTree {
    cwdPath := "/rt_ovl6".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "hl_lo1".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "hl_lo2".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "empty_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { name := "re_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true }
    ]
  }
  let stA1 ← stepModelCheck "open hl_lo1" ovlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stA2 ← stepModelCheck "open hl_lo2" stA1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stA3 ← stepModelCheck "flock hl_lo1 exclusive" stA2 (.flock 0 (.exclusive true)) .unit
  let stA4 ← stepModelCheck "flock hl_lo2 exclusive succeeds (distinct lower dentry)" stA3 (.flock 1 (.exclusive true)) .unit
  let stA5 ← stepModelCheck "open hl_lo1 again" stA4 (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 2)
  let _ ← stepModelCheck "flock hl_lo1 second fd conflicts -> EAGAIN" stA5 (.flock 2 (.exclusive true)) (.err Errno.EAGAIN)

  let dummyDirStat : StatInfo := {
    kind := .dir, mode := 0o755, size := 0, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let stB1 ← stepModelCheck "open empty_ldir" ovlTree
    (.openat none "empty_ldir".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let stB2 ← stepModelCheck "unlink empty_ldir" stB1 (.unlinkat none "empty_ldir".toUTF8 true) .unit
  let stB3 ← stepModelCheck "recreate empty_ldir" stB2 (.mkdirat none "empty_ldir".toUTF8 0o755) .unit
  let oldLdirIno ← match assocGet stB3.fds 0 with
    | some d => pure d.ino
    | none => throw (IO.userError "missing fd 0")
  let stB3p := FilesState.attachProcFdLink stB3 "19".toUTF8 oldLdirIno 0
  let stB4 ← stepModelCheck "fchmodat /proc/self/fd/19 on recreated empty ldir succeeds" stB3p
    (.fchmodat none "/proc/self/fd/19".toUTF8 0o700) .unit
  let _ ← stepModelCheck "fd 0 sees mode 0700 and nlink=1" stB4
    (.fstat 0) (.statted { dummyDirStat with mode := 0o700, nlink := 1 })
  let _ ← stepModelCheck "rmdir clobbered new empty_ldir -> ENOENT" stB4
    (.unlinkat none "empty_ldir".toUTF8 true) (.err Errno.ENOENT)

  let stC1 ← stepModelCheck "open re_ldir" ovlTree
    (.openat none "re_ldir".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let stC2 ← stepModelCheck "unlink re_ldir" stC1 (.unlinkat none "re_ldir".toUTF8 true) .unit
  let stC3 ← stepModelCheck "recreate re_ldir" stC2 (.mkdirat none "re_ldir".toUTF8 0o755) .unit
  let stC4 ← stepModelCheck "mkdir re_ldir/sub" stC3 (.mkdirat none "re_ldir/sub".toUTF8 0o755) .unit
  let _ ← stepModelCheck "fchmod old re_ldir with non-empty recreated upper -> ENOTEMPTY" stC4
    (.fchmod 0 0o700) (.err Errno.ENOTEMPTY)

  let stickyTree := FilesState.withSeededTree {
    cwdPath := "/rt_sticky3".toUTF8
    protectedRegular := 2
    protectedFifos := 1
    cwdEntries := [
      { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { name := "s1721".toUTF8, kind := .dir, mode := 0o1721, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { name := "gd".toUTF8, kind := .dir, mode := 0o2777, modeExact := true, ownedByUid := false, inGroup := false, gidMapped := true, ownerUid? := some 1 },
      { relDir := ["s1777".toUTF8], name := "sock666".toUTF8, kind := .socket, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 1 },
      { relDir := ["s1721".toUTF8], name := "sock666".toUTF8, kind := .socket, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 1 },
      { relDir := ["s1777".toUTF8], name := "dev666".toUTF8, kind := .charDev, devKind? := some .nullDev, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 1 }
    ]
  }
  let _ ← stepModelCheck "sticky s1777/sock666 O_CREAT -> EACCES" stickyTree
    (.openat none "s1777/sock666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "sticky s1777/sock666 no creat -> ENXIO" stickyTree
    (.openat none "s1777/sock666".toUTF8 roFlags 0) (.err Errno.ENXIO)
  let _ ← stepModelCheck "sticky s1721/sock666 O_CREAT -> ENXIO (no o+w)" stickyTree
    (.openat none "s1721/sock666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.ENXIO)
  let _ ← stepModelCheck "sticky s1777/dev666 O_CREAT -> EACCES" stickyTree
    (.openat none "s1777/dev666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "sticky s1777/dev666 no creat -> opened" stickyTree
    (.openat none "s1777/dev666".toUTF8 roFlags 0) (.opened 0)

  let dummyRegStat : StatInfo := {
    kind := .reg, mode := 0o755, size := 0, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let stD1 ← stepModelCheck "create gd/f_sgid 0o2755" stickyTree
    (.openat none "gd/f_sgid".toUTF8 { access := .rdwr, creat := true } 0o2755) (.opened 0)
  let _ ← stepModelCheck "gd/f_sgid strips S_ISGID when !inGroup & gid exec" stD1
    (.fstat 0) (.statted { dummyRegStat with mode := 0o755 })
  let stD2 ← stepModelCheck "create gd/f_nosgid 0o2644" stD1
    (.openat none "gd/f_nosgid".toUTF8 { access := .rdwr, creat := true } 0o2644) (.opened 1)
  let _ ← stepModelCheck "gd/f_nosgid keeps S_ISGID when 0o010 clear" stD2
    (.fstat 1) (.statted { dummyRegStat with mode := 0o2644 })
  let stD3 ← stepModelCheck "mkdir gd/sub 0o755 inherits S_ISGID" stD2
    (.mkdirat none "gd/sub".toUTF8 0o755) .unit
  let _ ← stepModelCheck "gd/sub has mode 0o2755" stD3
    (.fstatat none "gd/sub".toUTF8 {}) (.statted { dummyDirStat with mode := 0o2755, nlink := 2 })

  let mntTree := FilesState.withSeededTree {
    cwdPath := "/rt_mnt".toUTF8
    stdinMountId := 11
    stdoutMountId := 12
    stderrMountId := 13
    stdinKernelDev? := some 101
    stdoutKernelDev? := some 102
    stderrKernelDev? := some 103
    stdinOwnedByUid := true
    stdoutOwnedByUid := true
    stderrOwnedByUid := true
    mountProfiles := [(11, {}), (12, { readOnly := true }), (13, {})]
  }
  let checkStdMnt (p : String) (expected : Nat) : IO Unit := do
    match resolvePath mntTree none p.toUTF8 true with
    | .ok ino =>
      match assocGet mntTree.inodes ino with
      | some vn =>
        if vn.mountId != expected then
          throw (IO.userError s!"{p} expected mountId {expected}, got {vn.mountId}")
      | none => throw (IO.userError s!"missing inode {ino} for {p}")
    | .error e => throw (IO.userError s!"resolve {p} failed: {e}")
  checkStdMnt "/proc/self/fd/0" 11
  checkStdMnt "/proc/self/fd/1" 12
  checkStdMnt "/proc/self/fd/2" 13
  let _ ← stepModelCheck "fchmodat /proc/self/fd/0 succeeds (rw mount 11)" mntTree
    (.fchmodat none "/proc/self/fd/0".toUTF8 0o600) .unit
  let _ ← stepModelCheck "fchmodat /proc/self/fd/1 -> EROFS (ro mount 12)" mntTree
    (.fchmodat none "/proc/self/fd/1".toUTF8 0o600) (.err Errno.EROFS)
  let _ ← stepModelCheck "fchmodat /proc/self/fd/2 succeeds (rw mount 13)" mntTree
    (.fchmodat none "/proc/self/fd/2".toUTF8 0o600) .unit

private def runOverlayUnmappedAndProcFdReproducers : IO Unit := do
  let roFlags : OpenFlags := { access := .rdonly }
  let ovlTree := FilesState.withSeededTree {
    cwdPath := "/rt_ovl7".toUTF8
    cwdOverlayMerged := true
    cwdMountId := 4
    mountProfiles := [(4, { isOverlay := true, supportsSeals := false })]
    cwdEntries := [
      { name := "hl_lo1".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "hl_lo2".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "orig".toUTF8, mayCopyUp := true, hardlinkGroup? := some 9 },
      { name := "empty_ldir".toUTF8, kind := .dir, mode := 0o755, modeExact := true, mayCopyUp := true },
      { name := "src".toUTF8, kind := .dir, mode := 0o755, modeExact := true }
    ]
  }
  let hl1Ino ← match resolvePath ovlTree none "hl_lo1".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"hl_lo1 resolve failed: {e}")
  let hl2Ino ← match resolvePath ovlTree none "hl_lo2".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"hl_lo2 resolve failed: {e}")
  let stA1 ← stepModelCheck "open hl_lo1" ovlTree (.openat none "hl_lo1".toUTF8 roFlags 0) (.opened 0)
  let stA2 ← stepModelCheck "open hl_lo2" stA1 (.openat none "hl_lo2".toUTF8 roFlags 0) (.opened 1)
  let stA3 ← stepModelCheck "unlink hl_lo1" stA2 (.unlinkat none "hl_lo1".toUTF8 false) .unit
  let stA4 ← stepModelCheck "unlink hl_lo2" stA3 (.unlinkat none "hl_lo2".toUTF8 false) .unit
  let stA4p := FilesState.attachProcFdLink (FilesState.attachProcFdLink stA4 "20".toUTF8 hl1Ino 0) "21".toUTF8 hl2Ino 1
  let stA5 ← stepModelCheck "reopen /proc/self/fd/20" stA4p (.openat none "/proc/self/fd/20".toUTF8 roFlags 0) (.opened 2)
  let stA6 ← stepModelCheck "reopen /proc/self/fd/21" stA5 (.openat none "/proc/self/fd/21".toUTF8 roFlags 0) (.opened 3)
  let stA7 ← stepModelCheck "flock fd0 EX|NB" stA6 (.flock 0 (.exclusive true)) .unit
  let _ ← stepModelCheck "flock reopened fd2 conflicts -> EAGAIN" stA7 (.flock 2 (.exclusive true)) (.err Errno.EAGAIN)
  let _ ← stepModelCheck "flock distinct reopened fd3 succeeds" stA7 (.flock 3 (.exclusive true)) .unit

  let edIno ← match resolvePath ovlTree none "empty_ldir".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"empty_ldir resolve failed: {e}")
  let stB1 ← stepModelCheck "open empty_ldir" ovlTree
    (.openat none "empty_ldir".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let stB2 ← stepModelCheck "unlink empty_ldir" stB1 (.unlinkat none "empty_ldir".toUTF8 true) .unit
  let stB2p := FilesState.attachProcFdLink stB2 "22".toUTF8 edIno 0
  let stB3 ← stepModelCheck "reopen /proc/self/fd/22" stB2p
    (.openat none "/proc/self/fd/22".toUTF8 { access := .rdonly, directory := true } 0) (.opened 1)
  let stB4 ← stepModelCheck "recreate empty_ldir" stB3 (.mkdirat none "empty_ldir".toUTF8 0o755) .unit
  let stB5 ← stepModelCheck "fchmod reopened fd1 succeeds and clobbers" stB4 (.fchmod 1 0o700) .unit
  let _ ← stepModelCheck "rename clobbered empty_ldir -> moved -> ESTALE" stB5
    (.renameat2 none "empty_ldir".toUTF8 none "moved".toUTF8 {}) (.err Errno.ESTALE)
  let _ ← stepModelCheck "rename src -> clobbered empty_ldir -> ESTALE" stB5
    (.renameat2 none "src".toUTF8 none "empty_ldir".toUTF8 {}) (.err Errno.ESTALE)
  let _ ← stepModelCheck "rename exchange src <-> clobbered empty_ldir -> ESTALE" stB5
    (.renameat2 none "src".toUTF8 none "empty_ldir".toUTF8 { exchange := true }) (.err Errno.ESTALE)
  let _ ← stepModelCheck "rename noreplace src -> clobbered empty_ldir -> EEXIST" stB5
    (.renameat2 none "src".toUTF8 none "empty_ldir".toUTF8 { noreplace := true }) (.err Errno.EEXIST)

  let nonRegTree := FilesState.withSeededTree {
    cwdPath := "/rt_nonreg".toUTF8
    protectedRegular := 0
    protectedFifos := 0
    cwdEntries := [
      { name := "p444.fifo".toUTF8, kind := .fifo, mode := 0o444, modeExact := true },
      { name := "s444.sock".toUTF8, kind := .socket, mode := 0o444, modeExact := true },
      { name := "n444".toUTF8, kind := .charDev, devKind? := some .nullDev, mode := 0o444, modeExact := true },
      { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := true, ownerUid? := some 0 },
      { relDir := ["s1777".toUTF8], name := "sock666".toUTF8, kind := .socket, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 1 },
      { relDir := ["s1777".toUTF8], name := "dev666".toUTF8, kind := .charDev, devKind? := some .nullDev, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 1 },
      { name := "s_unmap".toUTF8, kind := .dir, mode := 0o1777, modeExact := true, ownedByUid := false, ownerUid? := some 65534, uidMapped := false, gidMapped := false, ownerUidTag? := some 2 },
      { relDir := ["s_unmap".toUTF8], name := "diff".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 65534, uidMapped := false, gidMapped := false, ownerUidTag? := some 3 },
      { relDir := ["s_unmap".toUTF8], name := "none_tag".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 65534, uidMapped := false, gidMapped := false },
      { relDir := ["s_unmap".toUTF8], name := "same".toUTF8, kind := .reg, mode := 0o666, modeExact := true, ownedByUid := false, inGroup := false, ownerUid? := some 65534, uidMapped := false, gidMapped := false, ownerUidTag? := some 2 }
    ]
  }
  let _ ← stepModelCheck "p444.fifo O_RDONLY|O_TRUNC|O_NONBLOCK no-caps -> EACCES" nonRegTree
    (.openat none "p444.fifo".toUTF8 { access := .rdonly, trunc := true, nonblock := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "s444.sock O_RDONLY|O_TRUNC no-caps -> EACCES" nonRegTree
    (.openat none "s444.sock".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.EACCES)
  let nonRegCap := { nonRegTree with cred := { capDacOverride := true } }
  let _ ← stepModelCheck "p444.fifo O_RDONLY|O_TRUNC|O_NONBLOCK capDacOverride -> opened" nonRegCap
    (.openat none "p444.fifo".toUTF8 { access := .rdonly, trunc := true, nonblock := true } 0) (.opened 0)
  let _ ← stepModelCheck "s444.sock O_RDONLY|O_TRUNC capDacOverride -> ENXIO" nonRegCap
    (.openat none "s444.sock".toUTF8 { access := .rdonly, trunc := true } 0) (.err Errno.ENXIO)
  let _ ← stepModelCheck "sticky s1777/sock666 O_CREAT with protected=0 -> EACCES" nonRegTree
    (.openat none "s1777/sock666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "sticky s1777/dev666 O_CREAT with protected=0 -> EACCES" nonRegTree
    (.openat none "s1777/dev666".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let unmapTree := { nonRegTree with sysctls := { protectedRegular := 2, protectedFifos := 1 } }
  let _ ← stepModelCheck "unmapped distinct uidTag O_CREAT -> EACCES" unmapTree
    (.openat none "s_unmap/diff".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "unmapped none uidTag O_CREAT -> EACCES" unmapTree
    (.openat none "s_unmap/none_tag".toUTF8 { access := .rdonly, creat := true } 0o644) (.err Errno.EACCES)
  let _ ← stepModelCheck "unmapped matching uidTag O_CREAT -> opened" unmapTree
    (.openat none "s_unmap/same".toUTF8 { access := .rdonly, creat := true } 0o644) (.opened 0)

  let secFifoTree := FilesState.withSeededTree {
    cwdPath := "/rt_sec".toUTF8
    ambientSeccomp := true
    cwdEntries := [{ name := "p.fifo".toUTF8, kind := .fifo, mode := 0o666, modeExact := true }]
  }
  let stF1 ← stepModelCheck "open fifo reader" secFifoTree
    (.openat none "p.fifo".toUTF8 { access := .rdonly, nonblock := true } 0) (.opened 0)
  let stF2 ← stepModelCheck "open fifo writer" stF1
    (.openat none "p.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.opened 1)
  let stF3 ← stepModelCheck "close(0) EIO under seccomp detaches reader 0" stF2
    (.close 0) (.err Errno.EIO)
  let _ ← stepModelCheck "fstat(0) after EIO -> EBADF" stF3 (.fstat 0) (.err Errno.EBADF)
  let _ ← stepModelCheck "write(1) after EIO detach -> EPIPE" stF3
    (.write 1 "abc".toUTF8) (.err Errno.EPIPE)
  let _ ← stepModelCheck "reopen writer O_WRONLY|O_NONBLOCK after EIO detach -> ENXIO" stF3
    (.openat none "p.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.err Errno.ENXIO)
  let stFKeep ← stepModelCheck "close(0) EAGAIN under seccomp keeps reader 0 open" stF2
    (.close 0) (.err Errno.EAGAIN)
  let dummyFifoStat : StatInfo := {
    kind := .fifo, mode := 0o666, size := 0, dev := 1, ino := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0
  }
  let _ ← stepModelCheck "reader 0 fstat still succeeds after EAGAIN" stFKeep
    (.fstat 0) (.statted dummyFifoStat)
  let _ ← stepModelCheck "reopen writer O_WRONLY|O_NONBLOCK succeeds after EAGAIN" stFKeep
    (.openat none "p.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.opened 2)

  let pid1Tree := FilesState.withSeededTree {
    cwdPath := "/rt_pid1".toUTF8
    selfPidBytes := "1".toUTF8
    procFd0LinkMode := 0o500
    stdinKind := .reg
    stdinMode := 0o640
    stdinOwnedByUid := false
    stdinInGroup := false
  }
  let _ ← stepModelCheck "selfIsOne /proc/self/fd/0 faccessat write nofollow -> EACCES" pid1Tree
    (.faccessat none "/proc/self/fd/0".toUTF8 { write := true } { symlinkNofollow := true }) (.err Errno.EACCES)
  let _ ← stepModelCheck "stdinInGroup=false 0640 open rdonly -> EACCES" pid1Tree
    (.openat none "/proc/self/fd/0".toUTF8 roFlags 0) (.err Errno.EACCES)

  let pid2Tree := FilesState.withSeededTree {
    cwdPath := "/rt_pid2".toUTF8
    selfPidBytes := "2".toUTF8
    proc1OwnedByUid := true
    proc1InGroup := true
    proc1CwdKernelDev? := some 88
    proc1CwdKernelIno? := some 8801
    proc1Fd0Kind := .reg
    proc1Fd0Mode := 0o444
    proc1Fd0LinkMode := 0o500
    proc1Fd0KernelDev? := some 88
    proc1Fd0KernelIno? := some 8802
    cwdKernelDev? := some 99
    cwdKernelIno? := some 9901
    stdinKind := .reg
    stdinMode := 0o600
    stdinKernelDev? := some 99
    stdinKernelIno? := some 9902
  }
  let p1FdIno ← match resolvePath pid2Tree none "/proc/1/fd/0".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"resolve /proc/1/fd/0 failed: {e}")
  let stIno ← match resolvePath pid2Tree none "/proc/self/fd/0".toUTF8 true with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"resolve /proc/self/fd/0 failed: {e}")
  if p1FdIno == stIno then
    throw (IO.userError "/proc/1/fd/0 aliased /proc/self/fd/0 despite distinct dev/ino")
  let gdTree := FilesState.withSeededTree {
    cwdPath := "/rt_gd4".toUTF8
    cwdEntries := [
      { name := "d".toUTF8, kind := .dir, mode := 0o755 },
      { name := "r".toUTF8, kind := .reg, mode := 0o644 },
      { name := "l".toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := "r".toUTF8 }
    ]
  }
  let gdRes :=
    ((do
      match ← modelOps.openat none ".".toUTF8 { access := .rdonly, directory := true } 0 with
      | .ok h => modelOps.getdents64 h 4096
      | .error e => return .error e).run gdTree).1
  let raw ← assertOk "getdents64" gdRes
  let parsed := parseDirents64Strict raw
  let wantParsed : List (ByteArray × UInt8) :=
    [(".".toUTF8, 4), ("..".toUTF8, 4), ("d".toUTF8, 4), ("r".toUTF8, 8), ("l".toUTF8, 10)]
  match parsed with
  | some xs =>
    let eqList := xs.length == wantParsed.length &&
      (xs.zip wantParsed).all fun ((a1, a2), (b1, b2)) => a1.data == b1.data && a2 == b2
    if !eqList then
      throw (IO.userError s!"modelOps.getdents64 decoded unexpected entries (len={xs.length})")
  | none =>
    throw (IO.userError "modelOps.getdents64 emitted malformed dirent64 buffer")
  let gdS0 ← stepModelCheck "open . for verify" gdTree
    (.openat none ".".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let zeroNmStub := ByteArray.mk <| Array.ofFn fun (idx : Fin 24) =>
    if idx.1 == 16 then 24 else if idx.1 == 18 then 8 else 0
  if (allowedStep gdS0 (.getdents64 0 4096) (.bytes zeroNmStub)).isSome then
    throw (IO.userError "allowedStep accepted all-zero d_name dirent64 record")
  let bogusNmStub := mkDirentEntry "bogus".toUTF8 8
  if (allowedStep gdS0 (.getdents64 0 4096) (.bytes bogusNmStub)).isSome then
    throw (IO.userError "allowedStep accepted nonexistent child name in dirent64")
  let badDtypeStub := mkDirentEntry "r".toUTF8 4
  if (allowedStep gdS0 (.getdents64 0 4096) (.bytes badDtypeStub)).isSome then
    throw (IO.userError "allowedStep accepted mismatched d_type for reg child")
  let dtUnknownStub := mkDirentEntry "r".toUTF8 0
  if (allowedStep gdS0 (.getdents64 0 4096) (.bytes dtUnknownStub)).isNone then
    throw (IO.userError "allowedStep rejected DT_UNKNOWN (0) for valid child")
  let mfd ← assertOk "memfd" (← Fuzz.LinuxSyscall.Env.openMemfd)
  let _ ← assertOk "write memfd" (← defaultOps.write mfd "sealed-data".toUTF8)
  assertOk "seal" (← (defaultOps.fcntl mfd (.addSeals 0x1f)) >>= fun r => pure (r.map fun _ => ()))
  let _ ← assertOk "seek end" (← defaultOps.lseek mfd 0 .seekEnd)
  let roMfd ← assertOk "reopenReadOnly sealed memfd" (← defaultOps.reopenReadOnly mfd)
  assertTrue "memfd read from 0" ((← assertOk "read" (← defaultOps.read roMfd 32)) == "sealed-data".toUTF8)
  safeClose defaultOps roMfd
  safeClose defaultOps mfd

private def runSgidStripAndSealReproducers : IO Unit := do
  let sBase := FilesState.withSeededTree {
    cwdPath := "/rt_sgid2".toUTF8
    umask := 0
    inInitUserNs := false
    cwdEntries := [
      { name := "gd".toUTF8, kind := .dir, mode := 0o2750, modeExact := true,
        ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, ownerUid? := some 0 },
      { name := "f_w".toUTF8, kind := .reg, mode := 0o2640, modeExact := true, bytes := "hello".toUTF8,
        ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, ownerUid? := some 0 },
      { name := "f_t".toUTF8, kind := .reg, mode := 0o2640, modeExact := true, bytes := "hello".toUTF8,
        ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, ownerUid? := some 0 },
      { name := "f_t0".toUTF8, kind := .reg, mode := 0o2640, modeExact := true, bytes := ByteArray.empty,
        ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, ownerUid? := some 0 },
      { name := "f_ix".toUTF8, kind := .reg, mode := 0o2650, modeExact := true, bytes := "hello".toUTF8,
        ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, ownerUid? := some 0 }
    ]
  }
  let mkSt (k : FileKind) (sz : Nat) (m : Mode) (ino : UInt64) (nl : Nat := 1) : StatInfo :=
    { kind := k, size := sz, mode := m, ino := ino, dev := 1, nlink := nl,
      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }
  let cFlags : OpenFlags := { access := .rdwr, creat := true }
  let stC1 ← stepModelCheck "create gd/c2640 keeps S_ISGID" sBase
    (.openat none "gd/c2640".toUTF8 cFlags 0o2640) (.opened 0)
  if (allowedStep stC1 (.fstat 0) (.statted (mkSt .reg 0 0o0640 70))).isSome then
    throw (IO.userError "allowedStep accepted 0o0640 on newly O_CREAT'd 0o2640 file")
  let stC2 ← stepModelCheck "fstat gd/c2640 exact 0o2640" stC1
    (.fstat 0) (.statted (mkSt .reg 0 0o2640 70))
  let stC3 ← stepModelCheck "write gd/c2640 strips !inGroup S_ISGID" stC2
    (.write 0 "X".toUTF8) (.u32 1)
  if (allowedStep stC3 (.fstat 0) (.statted (mkSt .reg 1 0o2640 70))).isSome then
    throw (IO.userError "allowedStep retained stale 0o2640 after !inGroup write")
  let _ ← stepModelCheck "fstat after write sees 0o0640" stC3
    (.fstat 0) (.statted (mkSt .reg 1 0o0640 70))

  let stMk ← stepModelCheck "mkdir d1700" sBase (.mkdirat none "d1700".toUTF8 0o1700) .unit
  if (allowedStep stMk (.fstatat none "d1700".toUTF8 {}) (.statted (mkSt .dir 0 0o0700 71 2))).isSome then
    throw (IO.userError "allowedStep accepted 0o0700 on newly mkdirat'd 0o1700 dir")
  let _ ← stepModelCheck "fstatat d1700 exact 0o1700" stMk
    (.fstatat none "d1700".toUTF8 {}) (.statted (mkSt .dir 0 0o1700 71 2))

  let wrFlags : OpenFlags := { access := .wronly }
  let trFlags : OpenFlags := { access := .wronly, trunc := true }
  let stW1 ← stepModelCheck "open f_w" sBase (.openat none "f_w".toUTF8 wrFlags 0) (.opened 0)
  let stW2 ← stepModelCheck "write f_w" stW1 (.write 0 "B".toUTF8) (.u32 1)
  let _ ← stepModelCheck "f_w strips to 0o0640" stW2 (.fstat 0) (.statted (mkSt .reg 5 0o0640 72))

  let stT1 ← stepModelCheck "open O_TRUNC f_t" sBase (.openat none "f_t".toUTF8 trFlags 0) (.opened 0)
  let _ ← stepModelCheck "f_t strips to 0o0640" stT1 (.fstat 0) (.statted (mkSt .reg 0 0o0640 73))

  let stT0 ← stepModelCheck "open O_TRUNC f_t0" sBase (.openat none "f_t0".toUTF8 trFlags 0) (.opened 0)
  let _ ← stepModelCheck "f_t0 strips to 0o0640" stT0 (.fstat 0) (.statted (mkSt .reg 0 0o0640 74))

  let mkSealed (mask : UInt32) (off : Nat) : FilesState :=
    let vn : VNode := {
      data := .reg (RegData.ofBytes "abc".toUTF8 (.sealable mask))
      mode := 0o2640
      modeExact := true
      owner := { ownedByUid := true, inGroup := false, uidMapped := true, gidMapped := true, uid? := some 0 }
      nlink := 1
    }
    { sBase with inodes := assocSet sBase.inodes 80 vn, fds := [(0, { ino := 80, access := .wronly, pos := .byteOffset off })], nextHid := 1 }
  let stSw ← stepModelCheck "F_SEAL_WRITE EPERM" (mkSealed 0x08 0) (.write 0 "X".toUTF8) (.err Errno.EPERM)
  let _ ← stepModelCheck "F_SEAL_WRITE strips to 0o0640" stSw (.fstat 0) (.statted (mkSt .reg 3 0o0640 80))
  let stSg ← stepModelCheck "F_SEAL_GROW EPERM" (mkSealed 0x04 3) (.write 0 "X".toUTF8) (.err Errno.EPERM)
  let _ ← stepModelCheck "F_SEAL_GROW strips to 0o0640" stSg (.fstat 0) (.statted (mkSt .reg 3 0o0640 80))

  let sUsernsCap := { sBase with cred := { capFsetid := true, initUserNs := false } }
  let stUc1 ← stepModelCheck "userns CAP_FSETID open f_w" sUsernsCap (.openat none "f_w".toUTF8 wrFlags 0) (.opened 0)
  let stUc2 ← stepModelCheck "userns CAP_FSETID write f_w" stUc1 (.write 0 "Z".toUTF8) (.u32 1)
  let _ ← stepModelCheck "userns CAP_FSETID preserves 0o2640" stUc2 (.fstat 0) (.statted (mkSt .reg 5 0o2640 72))
  let stUx1 ← stepModelCheck "userns CAP_FSETID open f_ix" sUsernsCap (.openat none "f_ix".toUTF8 wrFlags 0) (.opened 0)
  let stUx2 ← stepModelCheck "userns CAP_FSETID write f_ix" stUx1 (.write 0 "Z".toUTF8) (.u32 1)
  let _ ← stepModelCheck "userns CAP_FSETID strips S_IXGRP 0o2650 -> 0o0650" stUx2 (.fstat 0) (.statted (mkSt .reg 5 0o0650 75))

  let sSecSeal : FilesState :=
    let vnSec : VNode := {
      data := .reg (RegData.ofBytes "abc".toUTF8 (.sealable 0x08))
      mode := 0o4755
      modeExact := true
      nlink := 1
    }
    { sBase with
      ambientSeccomp := true
      inodes := assocSet sBase.inodes 81 vnSec
      fds := [(0, { ino := 81, access := .wronly, pos := .byteOffset 0 })]
      nextHid := 1 }
  let stSecEperm ← stepModelCheck "ambientSeccomp F_SEAL_WRITE EPERM" sSecSeal (.write 0 "X".toUTF8) (.err Errno.EPERM)
  let _ ← stepModelCheck "ambientSeccomp preserves 0o4755 if EPERM came from seccomp" stSecEperm (.fstat 0) (.statted (mkSt .reg 3 0o4755 81))
  let _ ← stepModelCheck "ambientSeccomp also allows 0o0755 if EPERM came from VFS" stSecEperm (.fstat 0) (.statted (mkSt .reg 3 0o0755 81))

private def runSharedOfdGetdentsChild (dirPath : String) : IO UInt32 := do
  IO.Process.setCurrentDir dirPath
  let _ ← Fuzz.LinuxSyscall.Env.closeRawFd 0
  let dfd ← match ← defaultOps.openat none ".".toUTF8 { access := .rdonly, directory := true, cloexec := false } 0 with
    | .ok f => pure f
    | .error _ => return 10
  if (← Fuzz.LinuxSyscall.Env.rawFdNum dfd) != 0 then
    safeClose defaultOps dfd
    return 11
  let dupFd ← match ← defaultOps.dupStdio .stdin with
    | .ok f => pure f
    | .error _ =>
      safeClose defaultOps dfd
      return 12
  let rGd ← defaultOps.getdents64 dfd 4096
  let fl0 ← defaultOps.fcntl dfd .getFd
  let fl1 ← defaultOps.fcntl dupFd .getFd
  safeClose defaultOps dupFd
  safeClose defaultOps dfd
  let gdBytes ← match rGd with
    | .ok b => pure b
    | .error _ => return 13
  let s0 : FilesState := {
    FilesState.initial dirPath.toUTF8 with
    freeStdioSlots := [.stdin]
  }
  let (_, s1) := evalModel s0 (.openat none ".".toUTF8 { access := .rdonly, directory := true, cloexec := false } 0)
  let (_, s2) := evalModel s1 (.dupStdio .stdin)
  let (_, s3Eval) := evalModel s2 (.getdents64 0 4096)
  let (fc0Eval, _) := evalModel s3Eval (.fcntl 0 .getFd)
  let (fc1Eval, _) := evalModel s3Eval (.fcntl 1 .getFd)
  let s3Allowed? := Files.allowedStep s2 (.getdents64 0 4096) (.bytes gdBytes)
  let allowedOk := match s3Allowed? with
    | none => false
    | some s3A =>
      (Files.allowedStep s3A (.fcntl 0 .getFd) (.u32 0)).isSome &&
      (Files.allowedStep s3A (.fcntl 1 .getFd) (.u32 1)).isSome
  match fl0, fl1 with
  | .ok 0, .ok 1 =>
    if outcomeEq fc0Eval (.u32 0) && outcomeEq fc1Eval (.u32 1) && allowedOk then return 0
    else return 14
  | _, _ => return 15

private def runUnmappedUsernsWorker (tmpDirStr : String) : IO UInt32 := do
  let tmpDir : System.FilePath := tmpDirStr
  let rOpen ← defaultOps.openat none (tmpDir / "f_unmap").toString.toUTF8 { access := .rdwr, creat := true } 0o644
  let rMkdir ← defaultOps.mkdirat none (tmpDir / "d_unmap").toString.toUTF8 0o755
  let rSym ← defaultOps.symlinkat "tgt".toUTF8 none (tmpDir / "s_unmap").toString.toUTF8
  if let .ok fd := rOpen then safeClose defaultOps fd
  let s0 : FilesState := {
    FilesState.initial tmpDirStr.toUTF8 with
    cred := { initUserNs := false }
  }
  let check75 {α : Type} (res : Except Errno α) (req : FilesReq) : Bool :=
    match res with
    | .error e => e == (75 : Errno) && (Files.allowedStep s0 req (.err e)).isSome
    | .ok _ => false
  if check75 rOpen (.openat none "f_unmap".toUTF8 { access := .rdwr, creat := true } 0o644) &&
      check75 rMkdir (.mkdirat none "d_unmap".toUTF8 0o755) &&
      check75 rSym (.symlinkat "tgt".toUTF8 none "s_unmap".toUTF8) then
    return 0
  else
    return 21

/-- Verify 64-bit `lseek` offsets, live `some dirFd` routing across `*at` syscalls, closed-stdio shared-OFD `getdents64` `FD_CLOEXEC` preservation, `F_SEAL_GROW` `S_ISUID` stripping, and unmapped user-namespace `EOVERFLOW` (`75`). -/
def runSharedOfdAndDirFdIntegrityChecks : IO Unit := withTempSandbox "dirfd_integrity" fun dir => do
  let dirReal ← IO.FS.realPath dir
  let cwdBox := dirReal / "cwd_box"
  let subBox := dirReal / "sub_box"
  IO.FS.createDirAll cwdBox
  IO.FS.createDirAll subBox
  let savedCwd ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir cwdBox
    IO.FS.writeFile (cwdBox / "victim") "keep_in_cwd"
    IO.FS.writeFile (subBox / "victim") "remove_in_sub"
    let subFd ← assertOk "open sub_box dirFd"
      (← defaultOps.openat none subBox.toString.toUTF8 { access := .rdonly, directory := true } 0)
    assertOk "mkdirat via some subFd" (← defaultOps.mkdirat (some subFd) "mk_sub".toUTF8 0o750)
    assertTrue "mk_sub created inside sub_box" (← (subBox / "mk_sub").isDir)
    assertTrue "mk_sub absent from cwd_box" (!(← (cwdBox / "mk_sub").pathExists))

    assertOk "symlinkat via some subFd" (← defaultOps.symlinkat "sym_payload".toUTF8 (some subFd) "lnk".toUTF8)
    let rlSub ← assertOk "readlinkat via some subFd" (← defaultOps.readlinkat (some subFd) "lnk".toUTF8 64)
    assertTrue "readlinkat via some subFd payload" (rlSub == "sym_payload".toUTF8)
    let rlCwd ← defaultOps.readlinkat none "lnk".toUTF8 64
    assertErr "lnk absent from cwd_box" rlCwd Errno.ENOENT

    assertOk "unlinkat via some subFd" (← defaultOps.unlinkat (some subFd) "victim".toUTF8 false)
    assertTrue "sub_box/victim removed" (!(← (subBox / "victim").pathExists))
    assertTrue "cwd_box/victim untouched" (← (cwdBox / "victim").pathExists)

    let fSub ← assertOk "openat creat via some subFd"
      (← defaultOps.openat (some subFd) "data64".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644)
    let wBytes ← assertOk "write data64" (← defaultOps.write fSub "hello64".toUTF8)
    assertTrue "wrote 7 bytes" (wBytes == 7)
    let hiOff : Int64 := 0x100000005
    let posHi ← assertOk "lseek 64-bit > 4GiB" (← defaultOps.lseek fSub hiOff .seekSet)
    assertTrue s!"lseek 64-bit offset preserved (got {posHi})" (posHi == 0x100000005)
    let posCur ← assertOk "lseek SEEK_CUR after 64-bit seek" (← defaultOps.lseek fSub (-3) .seekCur)
    assertTrue s!"lseek negative relative from >4GiB (got {posCur})" (posCur == 0x100000002)
    safeClose defaultOps fSub

    assertOk "fchmodat via some subFd" (← defaultOps.fchmodat (some subFd) "data64".toUTF8 0o600)
    let stSub ← assertOk "fstatat via some subFd" (← defaultOps.fstatat (some subFd) "data64".toUTF8 {})
    assertTrue "fchmodat applied to sub_box/data64" ((stSub.mode &&& 0o777) == 0o600)
    assertOk "faccessat via some subFd" (← defaultOps.faccessat (some subFd) "data64".toUTF8 { read := true } {})
    assertOk "renameat2 via some subFd" (← defaultOps.renameat2 (some subFd) "data64".toUTF8 (some subFd) "renamed64".toUTF8 {})
    assertTrue "renamed64 exists in sub_box" (← (subBox / "renamed64").pathExists)
    safeClose defaultOps subFd
  finally
    IO.Process.setCurrentDir savedCwd

  let emptyOfdBox := dirReal / "empty_ofd_box"
  IO.FS.createDirAll emptyOfdBox
  let csStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if csStatus == 0 then
    let rc ← try runSharedOfdGetdentsChild emptyOfdBox.toString catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  assertTrue s!"shared-OFD getdents64 cloexec child failed (status={csStatus})" (csStatus == 2000)

  if let .ok mfd ← Fuzz.LinuxSyscall.Env.openMemfd then
    let _ ← defaultOps.write mfd "abc".toUTF8
    assertOk "fchmod memfd 0o4755" (← defaultOps.fchmod mfd 0o4755)
    let _ ← defaultOps.fcntl mfd (.addSeals 0x04)
    let rW ← defaultOps.write mfd "x".toUTF8
    assertErr "write at EOF on F_SEAL_GROW -> EPERM" rW Errno.EPERM
    let stMfd ← assertOk "fstat memfd after F_SEAL_GROW EPERM" (← defaultOps.fstat mfd)
    assertTrue "F_SEAL_GROW EPERM strips S_ISUID to 0o0755" ((stMfd.mode &&& 0o7777) == 0o0755)
    safeClose defaultOps mfd

  let unmapDir := dirReal / "unmap_mnt"
  IO.FS.createDirAll unmapDir
  let exe ← IO.appPath
  let probeUnshare ← IO.Process.output {
    cmd := "unshare"
    args := #["--user", "--map-user=0", "--mount", "true"]
  }
  if probeUnshare.exitCode == 0 then
    let umOut ← IO.Process.output {
      cmd := "unshare"
      args := #["--user", "--map-user=0", "--mount", "sh", "-c",
        s!"mount -t tmpfs tmpfs '{unmapDir}' && exec '{exe}' --files-strace-worker --unmapped-userns '{unmapDir}'"]
    }
    assertTrue s!"unmapped userns EOVERFLOW worker failed (exit={umOut.exitCode}): {umOut.stderr}" (umOut.exitCode == 0)

  let pfsMnt := dirReal / "pfs_mnt"
  IO.FS.createDirAll pfsMnt
  let pfsTrusted := dirReal / "pfs_trusted"
  IO.FS.writeFile pfsTrusted "TRUSTED"
  let pfsStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if pfsStatus == 0 then
    let rc ← try
      match ← Fuzz.LinuxSyscall.SandboxEnv.setupMntNs pfsMnt.toString.toUTF8 with
      | .ok 0 =>
        match ← defaultOps.openat none pfsTrusted.toString.toUTF8 roFlags 0 with
        | .error _ => pure 2
        | .ok fd =>
          let rawNum ← Fuzz.LinuxSyscall.Env.rawFdNum fd
          if rawNum == 0xffffffff then
            safeClose defaultOps fd
            pure 2
          else
            match ← defaultOps.readlinkat none "/proc/thread-self".toUTF8 128 with
            | .error _ =>
              safeClose defaultOps fd
              pure 3
            | .ok tsBytes =>
              let tsStr := String.fromUTF8? tsBytes |>.getD ""
              let mOut ← IO.Process.output {
                cmd := "sh"
                args := #["-c", s!"mount -t tmpfs tmpfs '/proc/{tsStr}/fd' && printf 'SPOOFED' > '/proc/{tsStr}/fd/{rawNum}'"]
                stdin := .null
              }
              if mOut.exitCode != 0 then
                safeClose defaultOps fd
                pure 77
              else
                let res ← defaultOps.reopenReadOnly fd
                let _ ← IO.Process.output { cmd := "sh", args := #["-c", s!"umount '/proc/{tsStr}/fd' 2>/dev/null || true"], stdin := .null }
                safeClose defaultOps fd
                match res with
                | .error e => pure (if e == Errno.ENOENT then (0 : UInt32) else 4)
                | .ok rfd =>
                  safeClose defaultOps rfd
                  pure 5
      | _ => pure 77
    catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  if pfsStatus != 2077 then
    assertTrue s!"spoofed /proc/thread-self/fd reopen child failed (status={pfsStatus})" (pfsStatus == 2000)

  let sPart0 := FilesState.withSeededTree {
    cwdPath := "/um_part".toUTF8
    cwdBound := true
    hasCapDacOverride := true
    inInitUserNs := false
    hostUidMapped := true
    hostGidMapped := false
    procFd0LinkMode := 0o500
  }
  let sPart1 ← stepModelCheck "dupStdio stdin in partial userns" sPart0 (.dupStdio .stdin) (.opened 0)
  let sPart1p := sPart1.attachProcFdLink "3".toUTF8 ((assocGet sPart1.fds 0).map (·.ino) |>.getD 0) 0 0o500
  let _ ← stepModelCheck "attachProcFdLink inherits unmapped GID -> EACCES"
    sPart1p (.faccessat none "/proc/self/fd/3".toUTF8 { write := true } { symlinkNofollow := true }) (.err Errno.EACCES)
  let sPartCreat ← stepModelCheck "O_CREAT 0o444 in partial userns"
    sPart0 (.openat none "f444".toUTF8 { access := .rdonly, creat := true } 0o444) (.opened 0)
  let _ ← stepModelCheck "O_CREAT 0o444 unmapped GID blocks CAP_DAC_OVERRIDE -> EACCES"
    sPartCreat (.openat none "f444".toUTF8 { access := .wronly } 0) (.err Errno.EACCES)

private def mkPatternBytesLoop (n : Nat) (v : UInt8) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | k + 1, acc => mkPatternBytesLoop n v k (acc.push (v + UInt8.ofNat (k % 251)))

private def mkPatternBytes (n : Nat) (v : UInt8) : ByteArray :=
  mkPatternBytesLoop n v n (ByteArray.emptyWithCapacity n)

private def runClosedStdioChild (dirStr : String) : IO UInt32 := do
  let ops := defaultOps
  let _ ← Fuzz.LinuxSyscall.Env.closeRawFd 0
  match ← ops.dupStdio .stdin with
  | .error e =>
    if e != Errno.EBADF then return 2
  | .ok fd =>
    safeClose ops fd
    return 3
  let p1 := (dirStr ++ "/cs_openat").toUTF8
  let fd1 ← match ← ops.openat none p1 rwCreatFlags 0o644 with
    | .ok f => pure f
    | .error _ => return 4
  if (← Fuzz.LinuxSyscall.Env.rawFdNum fd1) != 0 then
    safeClose ops fd1
    return 12
  match ← ops.write fd1 "hello".toUTF8 with
  | .ok _ => pure ()
  | .error _ =>
    safeClose ops fd1
    return 13
  let dup1 ← match ← ops.dupStdio .stdin with
    | .ok f => pure f
    | .error _ =>
      safeClose ops fd1
      return 5
  match ← ops.lseek dup1 0 .seekSet with
  | .ok _ => pure ()
  | .error _ =>
    safeClose ops dup1
    safeClose ops fd1
    return 14
  let got1 ← match ← ops.read fd1 5 with
    | .ok bs => pure bs
    | .error _ =>
      safeClose ops dup1
      safeClose ops fd1
      return 15
  if got1 != "hello".toUTF8 then
    safeClose ops dup1
    safeClose ops fd1
    return 6
  let curOff ← match ← ops.lseek dup1 0 .seekCur with
    | .ok off => pure off
    | .error _ =>
      safeClose ops dup1
      safeClose ops fd1
      return 16
  if curOff != 5 then
    safeClose ops dup1
    safeClose ops fd1
    return 7
  safeClose ops fd1
  safeClose ops dup1
  let p2 := (dirStr ++ "/cs_openat2").toUTF8
  let fd2 ← match ← ops.openat2 none p2 { flags := rwCreatFlags, mode := 0o644 } with
    | .ok f => pure f
    | .error _ => return 8
  if (← Fuzz.LinuxSyscall.Env.rawFdNum fd2) != 0 then
    safeClose ops fd2
    return 17
  safeClose ops fd2
  let dFd0 ← match ← ops.openat none dirStr.toUTF8 dirFlags 0 with
    | .ok f => pure f
    | .error _ => return 9
  if (← Fuzz.LinuxSyscall.Env.rawFdNum dFd0) != 0 then
    safeClose ops dFd0
    return 18
  let dFdHi ← match ← ops.dupStdio .stdin with
    | .ok f => pure f
    | .error _ =>
      safeClose ops dFd0
      return 19
  safeClose ops dFd0
  let reFd0 ← match ← ops.reopenReadOnly dFdHi with
    | .ok f => pure f
    | .error _ =>
      safeClose ops dFdHi
      return 10
  if (← Fuzz.LinuxSyscall.Env.rawFdNum reFd0) != 0 then
    safeClose ops reFd0
    safeClose ops dFdHi
    return 20
  let reDup ← match ← ops.dupStdio .stdin with
    | .ok f => pure f
    | .error _ =>
      safeClose ops reFd0
      safeClose ops dFdHi
      return 11
  safeClose ops reDup
  safeClose ops reFd0
  safeClose ops dFdHi
  return 0

private def runDoubleCloseChild (sentinelPath : String) : IO UInt32 := do
  let fd ← match ← defaultOps.openat none sentinelPath.toUTF8 roFlags 0 with
    | .ok f => pure f
    | .error _ => return 2
  match ← defaultOps.close fd with
  | .ok () => pure ()
  | .error _ => return 3
  let nrClose ← Fuzz.LinuxSyscall.Env.nrClose
  let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose Errno.EPERM nrClose Errno.EPERM (0xffffffff : UInt32) 0
  if scErr != 0 then return 77
  match ← defaultOps.close fd with
  | .error e => return (if e == Errno.EBADF then 0 else 4)
  | .ok () => return 5

/-- Deterministic reproducers covering unboxed large `readSlice`/`bytesEq`, dynamic FIFO `O_WRONLY | O_NONBLOCK` `ENXIO`, closed-stdio slot `0` allocation/aliasing, and detached double-`close` syscall suppression. -/
def runDynamicFifoAndStdioReproducers : IO Unit := withTempSandbox "fifo-stdio" fun dir => do
  let dirReal ← IO.FS.realPath dir
  let chunk64k := mkPatternBytes 65536 29
  let rd64k : RegData := { size := 65536, extents := [(0, chunk64k)] }
  let sliced64k := rd64k.readSlice 0 65536
  assertTrue "unboxed readSlice + bytesEq 64 KiB" (bytesEq sliced64k chunk64k)
  let sBig0 := FilesState.withSeededTree {
    cwdPath := dirReal.toString.toUTF8
    cwdEntries := [{ name := "big".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := chunk64k }]
  }
  let sBig1 ← stepModelCheck "open big" sBig0 (.openat none "big".toUTF8 roFlags 0) (.opened 0)
  let _ ← stepModelCheck "read big 64k" sBig1 (.read 0 65536) (.bytes chunk64k)

  let fifoPath := dirReal / "dyn_fifo.fifo"
  let mkFifoRc ← Fuzz.LinuxSyscall.Env.mkfifo fifoPath.toString.toUTF8 0o644
  if mkFifoRc == 0 then
    let sFifo := FilesState.withSeededTree {
      cwdPath := dirReal.toString.toUTF8
      cwdEntries := [{ name := "dyn_fifo.fifo".toUTF8, kind := .fifo, mode := 0o644, modeExact := true, dynamicMeta := true }]
    }
    let rFifo ← defaultOps.openat none "dyn_fifo.fifo".toUTF8 { access := .wronly, nonblock := true } 0
    assertErr "0-reader FIFO O_WRONLY|O_NONBLOCK -> ENXIO" rFifo Errno.ENXIO
    let _ ← stepModelCheck "allowedStep accepts ENXIO on dynamic FIFO"
      sFifo (.openat none "dyn_fifo.fifo".toUTF8 { access := .wronly, nonblock := true } 0) (.err Errno.ENXIO)

  let csDir := dirReal / "cs"
  IO.FS.createDirAll csDir
  let csStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if csStatus == 0 then
    let rc ← try runClosedStdioChild csDir.toString catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  assertTrue s!"closed-stdio child failed (status={csStatus})" (csStatus == 2000)

  let sentinel := dirReal / "dc_sentinel"
  IO.FS.writeFile sentinel "x"
  let dcStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if dcStatus == 0 then
    let rc ← try runDoubleCloseChild sentinel.toString catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  if dcStatus != 2077 then
    assertTrue s!"detached double-close issued kernel close(-1) (status={dcStatus})" (dcStatus == 2000)

  let sGd0 := FilesState.withSeededTree {
    cwdPath := dirReal.toString.toUTF8
    umask := 0o077
    cwdEntries := [{
      name := "gd".toUTF8
      kind := .dir
      mode := 0o2755
      modeExact := true
      inGroup := false
      gidMapped := true
    }]
  }
  let sGd1 ← stepModelCheck "openat2 creat 0o2755 in sgid dir"
    sGd0 (.openat2 none "gd/f".toUTF8 { flags := { access := .rdonly, creat := true }, mode := 0o2755 }) (.opened 0)
  let mkGdStat (m : Mode) : StatInfo :=
    { kind := .reg, size := 0, mode := m, ino := 11, dev := 1, nlink := 1,
      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }
  let _ ← stepModelCheck "pre-umask S_ISGID+S_IXGRP stripped to 0o0700"
    sGd1 (.fstat 0) (.statted (mkGdStat 0o0700))
  assertTrue "rejects unstripped 0o2700"
    (Files.allowedStep sGd1 (.fstat 0) (.statted (mkGdStat 0o2700)) |>.isNone)
  let sGd2 ← stepModelCheck "openat2 creat 0o2740 in sgid dir"
    sGd0 (.openat2 none "gd/g".toUTF8 { flags := { access := .rdonly, creat := true }, mode := 0o2740 }) (.opened 0)
  let _ ← stepModelCheck "keeps S_ISGID without pre-umask S_IXGRP"
    sGd2 (.fstat 0) (.statted (mkGdStat 0o2700))

@[noinline] private def openAndDropHandle (p : ByteArray) : IO UInt32 := do
  let fd ← assertOk "openAndDropHandle" (← defaultOps.openat none p roFlags 0)
  Fuzz.LinuxSyscall.Env.rawFdNum fd

private def encodeBpfInsn (code : UInt16) (jt jf : UInt8) (k : UInt32) : Array UInt8 :=
  #[UInt8.ofNat (code.toNat % 256), UInt8.ofNat ((code.toNat / 256) % 256),
    jt, jf,
    UInt8.ofNat (k.toNat % 256), UInt8.ofNat ((k.toNat / 256) % 256),
    UInt8.ofNat ((k.toNat / 65536) % 256), UInt8.ofNat ((k.toNat / 16777216) % 256)]

private def runAtEaccessSeccompChild (sentinelPath : ByteArray) : IO UInt32 := do
  match ← LeanSwe.LinuxSyscall.Sandbox.prctl .setNoNewPrivs with
  | .ok _ => pure ()
  | .error _ => return 77
  let progBytes := ByteArray.mk (
    encodeBpfInsn 0x0020 0 0 0 ++
    encodeBpfInsn 0x0015 0 3 439 ++
    encodeBpfInsn 0x0020 0 0 40 ++
    encodeBpfInsn 0x0015 1 0 0x200 ++
    encodeBpfInsn 0x0006 0 0 0x00050001 ++
    encodeBpfInsn 0x0006 0 0 0x7FFF0000)
  match ← LeanSwe.LinuxSyscall.Sandbox.seccomp .setModeFilter {} progBytes with
  | .ok _ => pure ()
  | .error _ => return 77
  match ← defaultOps.faccessat none sentinelPath { read := true } { eaccess := false } with
  | .error e => if e != Errno.EPERM then return 2
  | .ok () => return 3
  match ← defaultOps.faccessat none sentinelPath { read := true } { eaccess := true } with
  | .ok () => return 0
  | .error _ => return 4

private def runCloseEintrDetachChild (sentinelPath : ByteArray) : IO UInt32 := do
  let fd ← match ← defaultOps.openat none sentinelPath roFlags 0 with
    | .ok f => pure f
    | .error _ => return 2
  let nrClose ← Fuzz.LinuxSyscall.Env.nrClose
  let scErr ← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose Errno.EINTR nrClose Errno.EINTR (0xffffffff : UInt32) 0
  if scErr != 0 then return 77
  match ← defaultOps.close fd with
  | .error e => if e != Errno.EINTR then return 3
  | .ok () => return 4
  match ← defaultOps.fstat fd with
  | .error e => return (if e == Errno.EBADF then 0 else 5)
  | .ok _ => return 6

private def runDupStdioFloorChild (sentinelPath : ByteArray) : IO UInt32 := do
  let f0 ← match ← defaultOps.openat none sentinelPath roFlags 0 with
    | .ok f => pure f
    | .error _ => return 2
  let f1 ← match ← defaultOps.openat none sentinelPath roFlags 0 with
    | .ok f => pure f
    | .error _ =>
      safeClose defaultOps f0
      return 3
  let f2 ← match ← defaultOps.openat none sentinelPath roFlags 0 with
    | .ok f => pure f
    | .error _ =>
      safeClose defaultOps f1
      safeClose defaultOps f0
      return 4
  let _ ← Fuzz.LinuxSyscall.Env.closeRawFd 0
  let dupOut ← match ← defaultOps.dupStdio .stdout with
    | .ok d => pure d
    | .error _ => return 5
  let rawNum ← Fuzz.LinuxSyscall.Env.rawFdNum dupOut
  safeClose defaultOps dupOut
  safeClose defaultOps f2
  safeClose defaultOps f1
  let _ ← defaultOps.close f0
  return (if rawNum >= 3 then 0 else 6)

private def runChrootSpoofChild (jailStr : String) : IO UInt32 := do
  match ← Fuzz.LinuxSyscall.SandboxEnv.enterUserns with
  | .ok () => pure ()
  | .error _ => return 77
  IO.FS.createDirAll jailStr
  let rc ← Fuzz.LinuxSyscall.Env.chroot jailStr.toUTF8
  if rc != 0 then return 77
  IO.Process.setCurrentDir "/"
  let fd ← match ← defaultOps.openat none "/trusted".toUTF8 rwCreatFlags 0o644 with
    | .ok f => pure f
    | .error _ => return 2
  let _ ← defaultOps.write fd "TRUSTED".toUTF8
  let rawNum ← Fuzz.LinuxSyscall.Env.rawFdNum fd
  let _ ← defaultOps.mkdirat none "/proc".toUTF8 0o755
  let _ ← defaultOps.mkdirat none "/proc/self".toUTF8 0o755
  let _ ← defaultOps.mkdirat none "/proc/self/fd".toUTF8 0o755
  let _ ← defaultOps.mkdirat none "/proc/thread-self".toUTF8 0o755
  let _ ← defaultOps.mkdirat none "/proc/thread-self/fd".toUTF8 0o755
  let spoofPath := s!"/proc/thread-self/fd/{rawNum}".toUTF8
  match ← defaultOps.openat none spoofPath rwCreatFlags 0o644 with
  | .ok sfd =>
    let _ ← defaultOps.write sfd "SPOOFED".toUTF8
    safeClose defaultOps sfd
  | .error _ =>
    safeClose defaultOps fd
    return 3
  let code1 ← match ← defaultOps.reopenReadOnly fd with
    | .error e => pure (if e == Errno.ENOENT then (0 : UInt32) else 4)
    | .ok rfd =>
      safeClose defaultOps rfd
      pure 5
  if code1 != 0 then
    safeClose defaultOps fd
    return code1
  let _ ← defaultOps.unlinkat none spoofPath false
  if (← Fuzz.LinuxSyscall.Env.link "/trusted".toUTF8 spoofPath) != 0 then
    safeClose defaultOps fd
    return 6
  let code2 ← match ← defaultOps.reopenReadOnly fd with
    | .error e => pure (if e == Errno.ENOENT then (0 : UInt32) else 7)
    | .ok rfd =>
      safeClose defaultOps rfd
      pure 8
  safeClose defaultOps fd
  return code2

private def runProcSpoofWorker (tmpDir : String) : IO UInt32 := do
  let ops := defaultOps
  let trustedPath := tmpDir ++ "/trusted"
  let spoofedPath := tmpDir ++ "/spoofed"
  IO.FS.writeFile trustedPath "TRUSTED"
  IO.FS.writeFile spoofedPath "SPOOFED"
  let fd ← match ← ops.openat none trustedPath.toUTF8 roFlags 0 with
    | .ok f => pure f
    | .error _ => return 2
  let rawNum ← Fuzz.LinuxSyscall.Env.rawFdNum fd
  let tsStr ← match ← ops.readlinkat none "/proc/thread-self".toUTF8 128 with
    | .ok b => pure (String.fromUTF8! b)
    | .error _ =>
      safeClose ops fd
      return 3
  let runMountCase (setupCmd cleanupCmd : String) : IO UInt32 := do
    let mOut ← IO.Process.output { cmd := "sh", args := #["-c", setupCmd], stdin := .null }
    if mOut.exitCode != 0 then return 77
    let r ← ops.reopenReadOnly fd
    let _ ← IO.Process.output { cmd := "sh", args := #["-c", cleanupCmd], stdin := .null }
    match r with
    | .error e => return (if e == Errno.ENOENT then 0 else 4)
    | .ok rfd =>
      safeClose ops rfd
      return 5
  let cpidFile := tmpDir ++ "/cpid"
  let c1 ← runMountCase
    (s!"set -e; ( exec {rawNum}<'{spoofedPath}'; exec sleep 10 >/dev/null 2>&1 ) </dev/null >/dev/null 2>&1 & CPID=$!; " ++
     s!"echo $CPID > '{cpidFile}'; mount --bind /proc/$CPID/fd /proc/{tsStr}/fd")
    (s!"umount /proc/{tsStr}/fd 2>/dev/null || true; kill $(cat '{cpidFile}' 2>/dev/null) 2>/dev/null || true")
  if c1 != 0 then safeClose ops fd; return c1
  let c2 ← runMountCase
    (s!"set -e; ( exec {rawNum}<'{trustedPath}'; exec sleep 10 >/dev/null 2>&1 ) </dev/null >/dev/null 2>&1 & CPID=$!; " ++
     s!"echo $CPID > '{cpidFile}'; mount --bind /proc/$CPID/fd /proc/{tsStr}/fd")
    (s!"umount /proc/{tsStr}/fd 2>/dev/null || true; kill $(cat '{cpidFile}' 2>/dev/null) 2>/dev/null || true")
  if c2 != 0 then safeClose ops fd; return c2
  let c3 ← runMountCase
    (s!"set -e; ( exec {rawNum}<'{spoofedPath}'; exec sleep 10 >/dev/null 2>&1 ) </dev/null >/dev/null 2>&1 & CPID=$!; " ++
     s!"echo $CPID > '{cpidFile}'; mount --bind /proc/$CPID /proc/{tsStr}")
    (s!"umount /proc/{tsStr} 2>/dev/null || true; kill $(cat '{cpidFile}' 2>/dev/null) 2>/dev/null || true")
  if c3 != 0 then safeClose ops fd; return c3
  let c4 ← runMountCase
    (s!"set -e; mount -t tmpfs tmpfs /proc/{tsStr}/fd; printf 'SPOOFED' > /proc/{tsStr}/fd/{rawNum}")
    (s!"umount /proc/{tsStr}/fd 2>/dev/null || true")
  safeClose ops fd
  return c4

private def runGetcwdUnboundLongChild (baseReal : System.FilePath) : IO UInt32 := do
  let gcwRoot := baseReal / "gcw_long"
  IO.FS.createDirAll gcwRoot
  IO.Process.setCurrentDir gcwRoot
  let ancFd ← match ← defaultOps.openat none ".".toUTF8 dirFlags 0 with
    | .ok f => pure f
    | .error _ => return 2
  let _ ← defaultOps.mkdirat none "s".toUTF8 0o755
  let seg200 := String.ofList (List.replicate 200 'a')
  let needSegs := (4040 - gcwRoot.toString.toUTF8.size) / 201
  let mut curRel := "s"
  for _ in [0 : max 1 needSegs] do
    curRel := curRel ++ "/" ++ seg200
    let _ ← defaultOps.mkdirat none curRel.toUTF8 0o755
  IO.Process.setCurrentDir (gcwRoot / curRel)
  let longName := (String.ofList (List.replicate 255 'x')).toUTF8
  match ← defaultOps.renameat2 (some ancFd) "s".toUTF8 (some ancFd) longName {} with
  | .ok () => pure ()
  | .error _ =>
    safeClose defaultOps ancFd
    return 3
  let res ← defaultOps.getcwd 0
  let _ ← defaultOps.renameat2 (some ancFd) longName (some ancFd) "s".toUTF8 {}
  safeClose defaultOps ancFd
  match res with
  | .error e => return (if e == Errno.ENAMETOOLONG then 0 else 4)
  | .ok _ => return 5

/-- Verify C-shim boundary, 64-bit stat/seek, `MAX_READ_BYTES` clamping, `AT_EACCESS` forwarding, `LeanFdBox` `EINTR`/finalizer lifecycle, `/proc` spoofing rejection, and `.unbound` `getcwd 0` `ENAMETOOLONG` parity. -/
def runCShimBoundaryProbes : IO Unit := withTempSandbox "cshim" fun dir => do
  let dirReal ← IO.FS.realPath dir
  let (_, sOpen0) := evalModel FilesState.initial (.openat none "/t".toUTF8 rwCreatFlags 0o644)
  let (_, sProc1) := evalModel sOpen0 (.mkdirat none "/proc".toUTF8 0o755)
  let (_, sProc2) := evalModel sProc1 (.mkdirat none "/proc/self".toUTF8 0o755)
  let (_, sProc3) := evalModel sProc2 (.mkdirat none "/proc/self/fd".toUTF8 0o755)
  assertTrue "fake /proc/self/fd rejects reopen opened"
    ((Files.allowedStep sProc3 (.reopenReadOnly 0) (.opened 1)).isNone)
  let _ ← stepModelCheck "fake /proc/self/fd reopen -> ENOENT"
    sProc3 (.reopenReadOnly 0) (.err Errno.ENOENT)
  let (_, sProcReg) := evalModel sProc1 (.openat none "/proc/self".toUTF8 rwCreatFlags 0o644)
  let _ ← stepModelCheck "non-pseudo /proc with reg /proc/self -> ENOENT"
    sProcReg (.reopenReadOnly 0) (.err Errno.ENOENT)
  let (_, sDanglingProc) := evalModel sOpen0 (.symlinkat "/missing".toUTF8 none "/proc".toUTF8)
  assertTrue "dangling /proc symlink rejects reopen opened"
    ((Files.allowedStep sDanglingProc (.reopenReadOnly 0) (.opened 1)).isNone)
  let _ ← stepModelCheck "dangling /proc symlink reopen -> ENOENT"
    sDanglingProc (.reopenReadOnly 0) (.err Errno.ENOENT)
  let _ ← stepModelCheck "unmodeled /proc allows ENOENT"
    sOpen0 (.reopenReadOnly 0) (.err Errno.ENOENT)

  let sCwd0 := FilesState.withSeededTree { cwdPath := "/d/sub".toUTF8, includeHostTree := false }
  let (_, sCwdRen) := evalModel sCwd0 (.renameat2 none "/d".toUTF8 none "/d_renamed".toUTF8 {})
  let _ ← stepModelCheck "unbound cwdPath getcwd 0 allows ENAMETOOLONG"
    sCwdRen (.getcwd 0) (.err Errno.ENAMETOOLONG)

  let sentinel := dirReal / "sentinel"
  IO.FS.writeFile sentinel "probe-bytes"
  let sentinelBytes := sentinel.toString.toUTF8

  let n1 ← openAndDropHandle sentinelBytes
  let n2 ← openAndDropHandle sentinelBytes
  assertTrue s!"finalizer leaked fd ({n1} != {n2})" (n1 == n2)

  let zfd ← assertOk "open /dev/zero" (← defaultOps.openat none "/dev/zero".toUTF8 roFlags 0)
  let z20 ← assertOk "read /dev/zero 20 MiB clamped" (← defaultOps.read zfd (20 * 1024 * 1024))
  assertTrue s!"expected 16 MiB clamp on 20 MiB read, got {z20.size}" (z20.size == 16777216)
  let zMax ← assertOk "read /dev/zero UINT32_MAX clamped" (← defaultOps.read zfd (0xffffffff : UInt32))
  assertTrue s!"expected 16 MiB clamp on UINT32_MAX read, got {zMax.size}" (zMax.size == 16777216)
  safeClose defaultOps zfd

  let nfd ← assertOk "open /dev/null wronly" (← defaultOps.openat none "/dev/null".toUTF8 { access := .wronly } 0)
  let w70k ← assertOk "write 70000 bytes to /dev/null"
    (← defaultOps.write nfd (ByteArray.mk (Array.replicate 70000 65)))
  assertTrue s!"expected 70000 write return, got {w70k}" (w70k == 70000)
  safeClose defaultOps nfd

  let spPath := (dirReal / "sparse64").toString.toUTF8
  let spFd ← assertOk "open sparse64" (← defaultOps.openat none spPath rwCreatFlags 0o644)
  let seekOff : Int64 := (0x100000005 : UInt64).toInt64
  let gotOff ← assertOk "lseek >4GiB" (← defaultOps.lseek spFd seekOff .seekSet)
  assertTrue s!"expected lseek 0x100000005, got {gotOff}" (gotOff == 0x100000005)
  let _ ← assertOk "write 1 byte at >4GiB" (← defaultOps.write spFd "Z".toUTF8)
  let stF ← assertOk "fstat >4GiB" (← defaultOps.fstat spFd)
  assertTrue s!"expected fstat size 0x100000006, got {stF.size}" (stF.size == 0x100000006)
  let stAt ← assertOk "fstatat >4GiB" (← defaultOps.fstatat none spPath {})
  assertTrue s!"expected fstatat size 0x100000006, got {stAt.size}" (stAt.size == 0x100000006)
  safeClose defaultOps spFd
  let _ ← defaultOps.unlinkat none spPath false

  let oldMask ← Fuzz.LinuxSyscall.Env.umask 0
  let pSticky := (dirReal / "sticky1644").toString.toUTF8
  let stFd ← assertOk "openat 0o1644"
    (← defaultOps.openat none pSticky { access := .rdwr, creat := true, excl := true } 0o1644)
  let pStickyDir := (dirReal / "sticky_dir1755").toString.toUTF8
  assertOk "mkdirat 0o1755" (← defaultOps.mkdirat none pStickyDir 0o1755)
  let _ ← Fuzz.LinuxSyscall.Env.umask oldMask
  let stSticky ← assertOk "fstat 0o1644" (← defaultOps.fstat stFd)
  assertTrue s!"expected mode 0o1644, got {stSticky.mode}" (stSticky.mode == 0o1644)
  safeClose defaultOps stFd
  let stStickyDir ← assertOk "fstatat mkdirat 0o1755" (← defaultOps.fstatat none pStickyDir {})
  assertTrue s!"expected mkdirat mode 0o1755, got {stStickyDir.mode}" (stStickyDir.mode == 0o1755)
  assertOk "fchmodat 0o1750" (← defaultOps.fchmodat none pSticky 0o1750)
  let stFchmodAt ← assertOk "fstatat fchmodat 0o1750" (← defaultOps.fstatat none pSticky {})
  assertTrue s!"expected fchmodat mode 0o1750, got {stFchmodAt.mode}" (stFchmodAt.mode == 0o1750)
  if (← Fuzz.LinuxSyscall.Env.getUid) != 0 then
    assertOk "fchmodat 0o200 wo" (← defaultOps.fchmodat none pSticky 0o200)
    assertErr "faccessat R_OK on 0o200 -> EACCES"
      (← defaultOps.faccessat none pSticky { read := true } {}) Errno.EACCES

  let pNoSymLnk := (dirReal / "nosym_lnk").toString.toUTF8
  assertOk "symlinkat nosym_lnk" (← defaultOps.symlinkat sentinelBytes none pNoSymLnk)
  assertErr "openat2 RESOLVE_NO_SYMLINKS -> ELOOP"
    (← defaultOps.openat2 none pNoSymLnk { flags := roFlags, resolve := { noSymlinks := true } }) Errno.ELOOP

  let pSock := (dirReal / "cshim.sock").toString.toUTF8
  assertEqErrno "mksock cshim.sock" (← Fuzz.LinuxSyscall.Env.mksock pSock) 0
  let stSockAt ← assertOk "fstatat socket" (← defaultOps.fstatat none pSock { symlinkNofollow := true })
  assertTrue s!"expected socket kind, got {repr stSockAt.kind}" (stSockAt.kind == .socket)
  let sockPathFd ← assertOk "openat O_PATH socket" (← defaultOps.openat none pSock { path := true } 0)
  let stSockFd ← assertOk "fstat O_PATH socket" (← defaultOps.fstat sockPathFd)
  assertTrue s!"expected fstat socket kind, got {repr stSockFd.kind}" (stSockFd.kind == .socket)
  safeClose defaultOps sockPathFd

  let devPath : System.FilePath := "/dev"
  if ← devPath.pathExists then
    let mut checkedBlk := false
    for entry in (← devPath.readDir) do
      if !checkedBlk then
        let epBytes := entry.path.toString.toUTF8
        if let .ok bfd ← defaultOps.openat none epBytes { path := true, nofollow := true } 0 then
          let rawB ← Fuzz.LinuxSyscall.Env.rawFdNum bfd
          let fm ← Fuzz.LinuxSyscall.Env.fdMode rawB
          if (fm &&& 0o170000) == 0o060000 then
            let stBlk ← assertOk "fstat blockDev" (← defaultOps.fstat bfd)
            assertTrue s!"expected blockDev kind, got {repr stBlk.kind}" (stBlk.kind == .blockDev)
            let stBlkAt ← assertOk "fstatat blockDev" (← defaultOps.fstatat none epBytes { symlinkNofollow := true })
            assertTrue s!"expected fstatat blockDev kind, got {repr stBlkAt.kind}" (stBlkAt.kind == .blockDev)
            checkedBlk := true
          safeClose defaultOps bfd

  let y2038File := dirReal / "y2038_ts.txt"
  IO.FS.writeFile y2038File "y2038\n"
  let pyY2038 ← IO.Process.output {
    cmd := "python3"
    args := #["-c", "import os, sys; os.utime(sys.argv[1], ns=(2200000001123456789, 2200000099987654321))", y2038File.toString]
    stdin := .null
  }
  assertTrue s!"y2038 utime failed: {pyY2038.stderr}" (pyY2038.exitCode == 0)
  let y2038Bytes := y2038File.toString.toUTF8
  let stYAt ← assertOk "fstatat y2038" (← defaultOps.fstatat none y2038Bytes {})
  assertTrue s!"fstatat y2038 mismatch: a=({stYAt.atimeSec},{stYAt.atimeNsec}) m=({stYAt.mtimeSec},{stYAt.mtimeNsec})"
    (stYAt.atimeSec == 2200000001 && stYAt.atimeNsec == 123456789 &&
     stYAt.mtimeSec == 2200000099 && stYAt.mtimeNsec == 987654321)
  let yFd ← assertOk "openat y2038" (← defaultOps.openat none y2038Bytes roFlags 0)
  let stYFd ← assertOk "fstat y2038" (← defaultOps.fstat yFd)
  safeClose defaultOps yFd
  assertTrue s!"fstat y2038 mismatch: a=({stYFd.atimeSec},{stYFd.atimeNsec}) m=({stYFd.mtimeSec},{stYFd.mtimeNsec})"
    (stYFd.atimeSec == 2200000001 && stYFd.atimeNsec == 123456789 &&
     stYFd.mtimeSec == 2200000099 && stYFd.mtimeNsec == 987654321)

  let appExeStdio ← IO.appPath
  let csOut ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "exec 0<&- 1>&- 2>&-; exec \"$1\" --files-strace-worker --closed-stdio-check", "_", appExeStdio.toString]
    stdin := .null
  }
  assertTrue s!"closed-stdio /dev/null pinning worker failed (exit={csOut.exitCode})" (csOut.exitCode == 0)
  for (label, cmd, args) in [
    ("close1", appExeStdio.toString, #["--files-strace-worker", "--sanitize-closed-stdio-check", "close1"]),
    ("close2", appExeStdio.toString, #["--files-strace-worker", "--sanitize-closed-stdio-check", "close2"]),
    ("closed-both", "sh", #["-c", "exec 0<&- 1>&- 2>&-; exec \"$1\" --files-strace-worker --sanitize-closed-stdio-check closed-both", "_", appExeStdio.toString]),
    ("devnull", "sh", #["-c", "exec >/dev/null 2>/dev/null; exec \"$1\" --files-strace-worker --sanitize-closed-stdio-check devnull", "_", appExeStdio.toString])
  ] do
    let scOut ← IO.Process.output { cmd, args, stdin := .null }
    assertTrue s!"sanitizeClosedStdio worker ({label}) failed (exit={scOut.exitCode}): {scOut.stderr}" (scOut.exitCode == 0)

  let probeUns ← IO.Process.output { cmd := "sh", args := #["-c", "unshare -Urm true"], stdin := .null }
  if probeUns.exitCode == 0 then
    let appExe ← IO.appPath
    let spDir := dirReal / "pspoof"
    IO.FS.createDirAll spDir
    let spOut ← IO.Process.output {
      cmd := "unshare"
      args := #["-Urm", appExe.toString, "--files-strace-worker", "--proc-spoof", spDir.toString]
      stdin := .null
    }
    if spOut.exitCode != 77 then
      assertTrue s!"procfs bind/tmpfs spoof worker failed (exit={spOut.exitCode}): {spOut.stderr}" (spOut.exitCode == 0)

  let probeStrace ← IO.Process.output { cmd := "sh", args := #["-c", "strace -qq -o /dev/null true"], stdin := .null }
  if probeStrace.exitCode == 0 then
    let stxOut ← IO.Process.output {
      cmd := "strace"
      args := #["-f", "-qq", "-o", "/dev/null", "-P", "/proc/", "-P", "/proc/thread-self/fd/",
        "-e", "inject=statx:retval=0", appExeStdio.toString, "--files-strace-worker",
        "--statx-nomntid", sentinel.toString]
      stdin := .null
    }
    assertTrue s!"reopenReadOnly missing STATX_MNT_ID probe failed (exit={stxOut.exitCode}): {stxOut.stderr}"
      (stxOut.exitCode == 0)

  let pBadMode := (dirReal / "bad_mode_openat2").toString.toUTF8
  assertErr "openat2 upper mode bits -> EINVAL"
    (← defaultOps.openat2 none pBadMode { flags := rwCreatFlags, mode := 0o100644 }) Errno.EINVAL
  let pUncached := (dirReal / "uncached_openat2").toString.toUTF8
  assertErrOneOf "openat2 O_CREAT | RESOLVE_CACHED -> EAGAIN/EINVAL"
    (← defaultOps.openat2 none pUncached { flags := rwCreatFlags, mode := 0o644, resolve := { cached := true } })
    [Errno.EAGAIN, Errno.EINVAL]
  assertErr "openat 4096-byte path -> ENAMETOOLONG"
    (← defaultOps.openat none (ByteArray.mk (Array.replicate 4096 97)) roFlags 0) Errno.ENAMETOOLONG

  let baseFd ← assertOk "open sentinel for reopen" (← defaultOps.openat none sentinelBytes { access := .rdwr } 0)
  assertErr "prime errno ENOENT before reopenReadOnly"
    (← defaultOps.openat none (dirReal / "no_such_prime_file").toString.toUTF8 roFlags 0) Errno.ENOENT
  let rfd ← assertOk "reopenReadOnly after ENOENT" (← defaultOps.reopenReadOnly baseFd)
  let fdFlags ← assertOk "reopenReadOnly getFd" (← defaultOps.fcntl rfd .getFd)
  assertTrue s!"expected FD_CLOEXEC=1 on reopenReadOnly, got {fdFlags}" (fdFlags == 1)
  let flFlags ← assertOk "reopenReadOnly getFl" (← defaultOps.fcntl rfd .getFl)
  assertTrue s!"expected O_NONBLOCK bit on reopenReadOnly, got {flFlags}" ((flFlags &&& ((1 : UInt32) <<< 8)) != 0)
  safeClose defaultOps rfd
  safeClose defaultOps baseFd

  let eaStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if eaStatus == 0 then
    let rc ← try runAtEaccessSeccompChild sentinelBytes catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  if eaStatus != 2077 then
    assertTrue s!"AT_EACCESS seccomp child failed (status={eaStatus})" (eaStatus == 2000)

  let eiStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if eiStatus == 0 then
    let rc ← try runCloseEintrDetachChild sentinelBytes catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  if eiStatus != 2077 then
    assertTrue s!"close EINTR detach child failed (status={eiStatus})" (eiStatus == 2000)

  let dsStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if dsStatus == 0 then
    let rc ← try runDupStdioFloorChild sentinelBytes catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  assertTrue s!"dupStdio >= 3 floor child failed (status={dsStatus})" (dsStatus == 2000)

  let crStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if crStatus == 0 then
    let rc ← try runChrootSpoofChild (dirReal / "jail").toString catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  if crStatus != 2077 then
    assertTrue s!"chroot spoofed /proc reopen child failed (status={crStatus})" (crStatus == 2000)

  let gwStatus ← Fuzz.LinuxSyscall.Env.forkForStatus
  if gwStatus == 0 then
    let rc ← try runGetcwdUnboundLongChild dirReal catch _ => pure 99
    Fuzz.LinuxSyscall.Env.exitImmediate rc
  assertTrue s!"getcwd(0) unbound ENAMETOOLONG child failed (status={gwStatus})" (gwStatus == 2000)

private def runStatNsecReopenAndDetachChecks : IO Unit := withTempSandbox "nsec-reopen-detach" fun dir => do
  let ops := defaultOps
  let dirReal ← IO.FS.realPath dir
  let tsFile := dirReal / "ts_check.txt"
  IO.FS.writeFile tsFile "ts_check\n"
  let pyOut ← IO.Process.output {
    cmd := "python3"
    args := #["-c", "import os, sys; os.utime(sys.argv[1], ns=(1700000001123456789, 1700000099987654321))", tsFile.toString]
    stdin := .null
  }
  assertTrue s!"utime nanosecond setup failed: {pyOut.stderr}" (pyOut.exitCode == 0)
  let stAt ← assertOk "fstatat ts_check.txt" (← ops.fstatat none "ts_check.txt".toUTF8 {})
  assertTrue s!"fstatat nanosecond mismatch: atime=({stAt.atimeSec},{stAt.atimeNsec}) mtime=({stAt.mtimeSec},{stAt.mtimeNsec})"
    (stAt.atimeSec == 1700000001 && stAt.atimeNsec == 123456789 &&
     stAt.mtimeSec == 1700000099 && stAt.mtimeNsec == 987654321)
  let tsFd ← assertOk "open ts_check.txt" (← ops.openat none "ts_check.txt".toUTF8 roFlags 0)
  let stFd ← try
    let s ← assertOk "fstat ts_check.txt" (← ops.fstat tsFd)
    let maxRead ← assertOk "read 0xffffffff clamp" (← ops.read tsFd 0xffffffff)
    assertTrue "read 0xffffffff payload" (maxRead == "ts_check\n".toUTF8)
    pure s
  finally
    safeClose ops tsFd
  assertTrue s!"fstat nanosecond mismatch: atime=({stFd.atimeSec},{stFd.atimeNsec}) mtime=({stFd.mtimeSec},{stFd.mtimeNsec})"
    (stFd.atimeSec == 1700000001 && stFd.atimeNsec == 123456789 &&
     stFd.mtimeSec == 1700000099 && stFd.mtimeNsec == 987654321)
  let sTs0 := FilesState.withSeededTree {
    cwdPath := dirReal.toString.toUTF8
    cwdBound := true
    cwdEntries := [{
      name := "ts_check.txt".toUTF8
      kind := .reg
      mode := stFd.mode
      modeExact := true
      bytes := "ts_check\n".toUTF8
      kernelDev? := some stFd.dev
      kernelIno? := some stFd.ino
    }]
  }
  let _ ← stepModelCheck "fstatat valid nsec" sTs0 (.fstatat none "ts_check.txt".toUTF8 {}) (.statted stAt)
  assertTrue "allowedStep rejects mtimeNsec >= 1e9"
    (Files.allowedStep sTs0 (.fstatat none "ts_check.txt".toUTF8 {}) (.statted { stAt with mtimeNsec := 1000000000 }) |>.isNone)
  assertTrue "allowedStep rejects atimeNsec >= 1e9"
    (Files.allowedStep sTs0 (.fstatat none "ts_check.txt".toUTF8 {}) (.statted { stAt with atimeNsec := 1000000000 }) |>.isNone)

  let rExWo ← ops.renameat2 none "ts_check.txt".toUTF8 none "wo_dst.txt".toUTF8 { exchange := true, whiteout := true }
  assertErr "renameat2 RENAME_EXCHANGE|RENAME_WHITEOUT -> EINVAL" rExWo Errno.EINVAL
  let _ ← stepModelCheck "model renameat2 RENAME_EXCHANGE|RENAME_WHITEOUT -> EINVAL" sTs0
    (.renameat2 none "ts_check.txt".toUTF8 none "wo_dst.txt".toUTF8 { exchange := true, whiteout := true }) (.err Errno.EINVAL)
  IO.FS.writeFile (dirReal / "wo_src.txt") "wo\n"
  let woMode ← Fuzz.LinuxSyscall.Env.statMode "wo_src.txt".toUTF8
  let sWo0 := FilesState.withSeededTree {
    cwdPath := dirReal.toString.toUTF8
    cwdBound := true
    cwdEntries := [{ name := "wo_src.txt".toUTF8, kind := .reg, mode := woMode, modeExact := true, bytes := "wo\n".toUTF8 }]
  }
  match ← ops.renameat2 none "wo_src.txt".toUTF8 none "wo_dst.txt".toUTF8 { whiteout := true } with
  | .ok () =>
    let sWo1 ← stepModelCheck "model renameat2 RENAME_WHITEOUT ok" sWo0
      (.renameat2 none "wo_src.txt".toUTF8 none "wo_dst.txt".toUTF8 { whiteout := true }) .unit
    let stWo ← assertOk "fstatat whiteout node" (← ops.fstatat none "wo_src.txt".toUTF8 {})
    assertTrue s!"whiteout node must be charDev mode 0, got {repr stWo.kind} {stWo.mode}"
      (stWo.kind == .charDev && stWo.mode == 0)
    let _ ← stepModelCheck "model fstatat whiteout node" sWo1
      (.fstatat none "wo_src.txt".toUTF8 {}) (.statted stWo)
  | .error eWo =>
    assertTrue s!"unexpected RENAME_WHITEOUT errno {eWo}" ([Errno.EPERM, Errno.EINVAL, Errno.EOPNOTSUPP].contains eWo)
    let _ ← stepModelCheck "model renameat2 RENAME_WHITEOUT err" sWo0
      (.renameat2 none "wo_src.txt".toUTF8 none "wo_dst.txt".toUTF8 { whiteout := true }) (.err eWo)

  let gcMax ← assertOk "getcwd 0xffffffff clamp" (← ops.getcwd 0xffffffff)
  assertTrue "getcwd 0xffffffff non-empty" (!gcMax.isEmpty)
  assertOk "symlinkat clamp_sym" (← ops.symlinkat "ts_check.txt".toUTF8 none "clamp_sym".toUTF8)
  let rlMax ← assertOk "readlinkat 0xffffffff clamp" (← ops.readlinkat none "clamp_sym".toUTF8 0xffffffff)
  assertTrue "readlinkat 0xffffffff target" (rlMax == "ts_check.txt".toUTF8)
  let dFd ← assertOk "open dir for getdents64 0xffffffff" (← ops.openat none ".".toUTF8 dirFlags 0)
  try
    let gdMax ← assertOk "getdents64 0xffffffff clamp" (← ops.getdents64 dFd 0xffffffff)
    assertTrue "getdents64 0xffffffff non-empty" (!gdMax.isEmpty)
  finally
    safeClose ops dFd

  let roSrcFd ← assertOk "open ro_chk.txt" (← ops.openat none "ro_chk.txt".toUTF8 rwCreatFlags 0o644)
  try
    let roNewFd ← assertOk "reopenReadOnly ro_chk.txt" (← ops.reopenReadOnly roSrcFd)
    try
      let fdBits ← assertOk "reopenReadOnly fcntl getFd" (← ops.fcntl roNewFd .getFd)
      assertTrue s!"reopenReadOnly must set FD_CLOEXEC (1), got {fdBits}" (fdBits == 1)
      let flBits ← assertOk "reopenReadOnly fcntl getFl" (← ops.fcntl roNewFd .getFl)
      assertTrue s!"reopenReadOnly must set O_NONBLOCK and O_RDONLY, got {flBits}"
        ((flBits &&& ((1 : UInt32) <<< 8)) != 0 && (flBits &&& 3) == 0)
    finally
      safeClose ops roNewFd
  finally
    safeClose ops roSrcFd

  let sExt1 ← stepModelCheck "model dupStdio stdout" sTs0 (.dupStdio .stdout) (.opened 0)
  let sExt2 ← stepModelCheck "model reopenReadOnly external stdio" sExt1 (.reopenReadOnly 0) (.opened 1)
  let _ ← stepModelCheck "model reopenReadOnly external stdio sets cloexec" sExt2 (.fcntl 1 .getFd) (.u32 1)
  assertTrue "model reopenReadOnly external stdio rejects getFd=0"
    (Files.allowedStep sExt2 (.fcntl 1 .getFd) (.u32 0) |>.isNone)
  assertTrue "evalModel reopenReadOnly external stdio getFd=1"
    (match (Files.evalModel sExt2 (.fcntl 1 .getFd)).1 with | .u32 v => v == 1 | _ => false)
  if (← Fuzz.LinuxSyscall.Env.fdKind 1) != 0 then
    let dupFd ← assertOk "live dupStdio stdout" (← ops.dupStdio .stdout)
    try
      match ← ops.reopenReadOnly dupFd with
      | .ok reExtFd =>
        try
          let extBits ← assertOk "live reopenReadOnly external getFd" (← ops.fcntl reExtFd .getFd)
          assertTrue s!"live reopenReadOnly external must set FD_CLOEXEC (1), got {extBits}" (extBits == 1)
        finally
          safeClose ops reExtFd
      | .error eRe =>
        let _ ← stepModelCheck "live reopenReadOnly external err" sExt1 (.reopenReadOnly 0) (.err eRe)
    finally
      safeClose ops dupFd

  let nrClose ← Fuzz.LinuxSyscall.Env.nrForSlot 2
  let nrFcntl ← Fuzz.LinuxSyscall.Env.nrForSlot 17
  let nrFstat ← Fuzz.LinuxSyscall.Env.nrForSlot 5
  let detachPath := (dirReal / "detach_chk.txt").toString.toUTF8
  for injected in #[Errno.EINTR, Errno.EIO, Errno.ENOSPC, (122 : Errno), Errno.ENOMEM, Errno.ESTALE, (104 : Errno)] do
    let scSt ← Fuzz.LinuxSyscall.Env.forkForStatus
    if scSt == 0 then
      match ← ops.openat none detachPath rwCreatFlags 0o644 with
      | .error _ => Fuzz.LinuxSyscall.Env.exitImmediate 78
      | .ok pfd =>
        if (← Fuzz.LinuxSyscall.Env.installSeccompErrno nrClose injected nrFcntl Errno.EPERM nrFstat Errno.EPERM) != 0 then
          Fuzz.LinuxSyscall.Env.exitImmediate 77
        match ← ops.close pfd with
        | .error ce =>
          if ce != injected then Fuzz.LinuxSyscall.Env.exitImmediate 79
        | .ok () => Fuzz.LinuxSyscall.Env.exitImmediate 80
        match ← ops.fstat pfd with
        | .error fe =>
          if fe == Errno.EBADF then Fuzz.LinuxSyscall.Env.exitImmediate 0 else Fuzz.LinuxSyscall.Env.exitImmediate 81
        | .ok _ => Fuzz.LinuxSyscall.Env.exitImmediate 82
    if scSt != 2077 then
      assertTrue s!"fd_box.h failed to detach box on close errno={injected} (status={scSt})" (scSt == 2000)

private def runUnboxedDirentAndGetcwdChecks : IO Unit := do
  assertTrue "mkDirentEntryChecked? empty rejected" (mkDirentEntryChecked? ByteArray.empty |>.isNone)
  assertTrue "mkDirentEntryChecked? embedded NUL rejected"
    (mkDirentEntryChecked? (ByteArray.mk #[97, 0, 98]) |>.isNone)
  assertTrue "mkDirentEntryChecked? slash rejected"
    (mkDirentEntryChecked? "a/b".toUTF8 |>.isNone)
  let over64k : ByteArray := Id.run do
    let mut b := ByteArray.emptyWithCapacity 65536
    let mut i := 0
    while i < 65536 do
      b := b.push 97
      i := i + 1
    return b
  assertTrue "mkDirentEntryChecked? >=64KiB rejected" (mkDirentEntryChecked? over64k |>.isNone)
  let sLongCwd : FilesState := { FilesState.initial with cwdPath := .bound over64k }
  assertTrue "evalModel getcwd >=PATH_MAX returns ENAMETOOLONG"
    (outcomeEq (evalModel sLongCwd (.getcwd 128)).1 (.err Errno.ENAMETOOLONG))
  match mkDirentEntryChecked? "entry_ok".toUTF8 8 42 with
  | none => throw (IO.userError "mkDirentEntryChecked? rejected valid name")
  | some ent =>
    assertTrue "parseDirents64Strict round-trips mkDirentEntryChecked?"
      (parseDirents64Strict ent == some [("entry_ok".toUTF8, 8)])
  let multiStub := mkTypedDirentStub [(dotBytes, 4, 1), (dotDotBytes, 4, 1), ("leaf".toUTF8, 10, 9)]
  assertTrue "parseDirents64Strict round-trips mkTypedDirentStub"
    (parseDirents64Strict multiStub == some [(dotBytes, 4), (dotDotBytes, 4), ("leaf".toUTF8, 10)])

private def runProtectedSymlinkWalkReproducers : IO Unit := do
  let mkState (protSym : Bool) (isRo : Bool := false) : FilesState :=
    FilesState.withSeededTree {
      cwdPath := "/rt_psym".toUTF8
      cwdMountId := 4
      mountProfiles := [(4, { readOnly := isRo, supportsSeals := false })]
      protectedRegular := 2
      protectedFifos := 1
      protectedSymlinks := protSym
      inInitUserNs := false
      cwdEntries := [
        { name := "sub".toUTF8, kind := .dir, mode := 0o755, modeExact := true },
        { relDir := ["sub".toUTF8], name := "a".toUTF8, kind := .reg, mode := 0o644, modeExact := true,
          bytes := "init-a".toUTF8 },
        { name := "s_unmap".toUTF8, kind := .dir, mode := 0o1777, modeExact := true,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s_unmap".toUTF8], name := "sym_other".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../sub/a".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s_unmap".toUTF8], name := "sym_dir".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../sub".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s_unmap".toUTF8], name := "sym_miss".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../missing".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s_unmap".toUTF8], name := "sym_abs".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "/rt_psym/sub/a".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s_unmap".toUTF8], name := "sym_owned".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "sym_other".toUTF8,
          ownedByUid := true, inGroup := true, ownerUid? := some 0,
          uidMapped := true, gidMapped := true },
        { name := "s1777".toUTF8, kind := .dir, mode := 0o1777, modeExact := true,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false },
        { relDir := ["s1777".toUTF8], name := "sym_other".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../sub/a".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 1,
          uidMapped := true, gidMapped := true },
        { name := "s_tag".toUTF8, kind := .dir, mode := 0o1777, modeExact := true,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false, ownerUidTag? := some 2 },
        { relDir := ["s_tag".toUTF8], name := "sym_same_tag".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../sub/a".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false, ownerUidTag? := some 2 },
        { relDir := ["s_tag".toUTF8], name := "sym_diff_tag".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "../sub/a".toUTF8,
          ownedByUid := false, inGroup := false, ownerUid? := some 65534,
          uidMapped := false, gidMapped := false, ownerUidTag? := some 3 }
      ]
    }
  let s0 := mkState true
  let s1 ← stepModelCheck "asym symlink a -> s_unmap/sym_other" s0
    (.symlinkat "s_unmap/sym_other".toUTF8 none "a".toUTF8) .unit
  let _ ← stepModelCheck "asym exact shrunk faccessat(a/l, F_OK) -> ENOTDIR" s1
    (.faccessat none "a/l".toUTF8 {} {}) (.err Errno.ENOTDIR)
  assertTrue "asym faccessat(a/l, F_OK) rejects EACCES"
    ((allowedStep s1 (.faccessat none "a/l".toUTF8 {} {}) (.err Errno.EACCES)).isNone)
  let _ ← stepModelCheck "asym faccessat(a/l, W_OK, AT_EACCESS) -> ENOTDIR" s1
    (.faccessat none "a/l".toUTF8 { write := true } { eaccess := true }) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "asym faccessat(a/l, R_OK) -> ENOTDIR" s1
    (.faccessat none "a/l".toUTF8 { read := true } {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "asym faccessat(a/l, X_OK) -> ENOTDIR" s1
    (.faccessat none "a/l".toUTF8 { exec := true } {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "asym faccessat(a/l, RWX, EACCESS|NOFOLLOW) -> ENOTDIR" s1
    (.faccessat none "a/l".toUTF8 { read := true, write := true, exec := true }
      { symlinkNofollow := true, eaccess := true }) (.err Errno.ENOTDIR)

  let s2 ← stepModelCheck "asym symlink b -> s1777/sym_other" s1
    (.symlinkat "s1777/sym_other".toUTF8 none "b".toUTF8) .unit
  let s3 ← stepModelCheck "asym symlink ad -> s_unmap/sym_dir" s2
    (.symlinkat "s_unmap/sym_dir".toUTF8 none "ad".toUTF8) .unit
  let s4 ← stepModelCheck "asym symlink at -> s_unmap/sym_other/" s3
    (.symlinkat "s_unmap/sym_other/".toUTF8 none "at".toUTF8) .unit
  let s5 ← stepModelCheck "asym symlink al -> s_unmap/sym_other/l" s4
    (.symlinkat "s_unmap/sym_other/l".toUTF8 none "al".toUTF8) .unit
  let s6 ← stepModelCheck "asym symlink am -> s_unmap/sym_miss" s5
    (.symlinkat "s_unmap/sym_miss".toUTF8 none "am".toUTF8) .unit

  let _ ← stepModelCheck "trailing a -> EACCES" s6
    (.faccessat none "a".toUTF8 {} {}) (.err Errno.EACCES)
  assertTrue "trailing a rejects unit"
    ((allowedStep s6 (.faccessat none "a".toUTF8 {} {}) .unit).isNone)
  let _ ← stepModelCheck "trailing a/ NOFOLLOW -> EACCES" s6
    (.faccessat none "a/".toUTF8 {} { symlinkNofollow := true }) (.err Errno.EACCES)
  let _ ← stepModelCheck "trailing at (-> sym_other/) -> EACCES" s6
    (.faccessat none "at".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "non-trailing via al (-> sym_other/l) -> ENOTDIR" s6
    (.faccessat none "al".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "mapped-in-unmapped b/l -> ENOTDIR" s6
    (.faccessat none "b/l".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "mapped-in-unmapped trailing b -> EACCES" s6
    (.faccessat none "b".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "direct s_unmap/sym_other trailing -> EACCES" s6
    (.faccessat none "s_unmap/sym_other".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "direct s_unmap/sym_other NOFOLLOW -> unit" s6
    (.faccessat none "s_unmap/sym_other".toUTF8 {} { symlinkNofollow := true }) .unit
  let _ ← stepModelCheck "direct s_unmap/sym_other/ NOFOLLOW -> EACCES" s6
    (.faccessat none "s_unmap/sym_other/".toUTF8 {} { symlinkNofollow := true }) (.err Errno.EACCES)
  let _ ← stepModelCheck "direct s_unmap/sym_other/l -> ENOTDIR" s6
    (.faccessat none "s_unmap/sym_other/l".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "direct s_unmap/sym_other/. -> ENOTDIR" s6
    (.faccessat none "s_unmap/sym_other/.".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "direct s_unmap/sym_other/.. -> ENOTDIR" s6
    (.faccessat none "s_unmap/sym_other/..".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "sticky owned sym_owned -> trailing sym_other EACCES" s6
    (.faccessat none "s_unmap/sym_owned".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "sticky owned sym_owned/l -> ENOTDIR" s6
    (.faccessat none "s_unmap/sym_owned/l".toUTF8 {} {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "dangling am trailing -> EACCES" s6
    (.faccessat none "am".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "dangling am/l -> ENOENT" s6
    (.faccessat none "am/l".toUTF8 {} {}) (.err Errno.ENOENT)
  let _ ← stepModelCheck "unmapped uidTag same allows trailing" s6
    (.faccessat none "s_tag/sym_same_tag".toUTF8 {} {}) .unit
  let _ ← stepModelCheck "unmapped uidTag diff blocks trailing -> EACCES" s6
    (.faccessat none "s_tag/sym_diff_tag".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "unmapped uidTag diff allows intermediate -> ENOTDIR" s6
    (.faccessat none "s_tag/sym_diff_tag/l".toUTF8 {} {}) (.err Errno.ENOTDIR)

  let _ ← stepModelCheck "dir symlink trailing -> EACCES" s6
    (.faccessat none "s_unmap/sym_dir".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "dir symlink intermediate sym_dir/a -> ok" s6
    (.faccessat none "s_unmap/sym_dir/a".toUTF8 { read := true, write := true } {}) .unit
  let _ ← stepModelCheck "dir symlink intermediate ad/a F_OK -> ok" s6
    (.faccessat none "ad/a".toUTF8 {} {}) .unit
  let _ ← stepModelCheck "dir symlink intermediate ad/a X_OK -> EACCES" s6
    (.faccessat none "ad/a".toUTF8 { exec := true } {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "dir symlink intermediate ad/. -> ok" s6
    (.faccessat none "ad/.".toUTF8 {} {}) .unit

  let _ ← stepModelCheck "openat a/l O_RDONLY -> ENOTDIR" s6
    (.openat none "a/l".toUTF8 { access := .rdonly } 0) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "openat a/l O_CREAT -> ENOTDIR" s6
    (.openat none "a/l".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "openat s_unmap/sym_dir/a O_RDONLY -> ok" s6
    (.openat none "s_unmap/sym_dir/a".toUTF8 { access := .rdonly } 0) (.opened 0)
  let _ ← stepModelCheck "openat s_unmap/sym_dir/new O_CREAT -> ok" s6
    (.openat none "s_unmap/sym_dir/new".toUTF8 { access := .rdwr, creat := true } 0o644) (.opened 0)
  let _ ← stepModelCheck "openat s_unmap/sym_other O_RDONLY -> EACCES" s6
    (.openat none "s_unmap/sym_other".toUTF8 { access := .rdonly } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "openat s_unmap/sym_other O_PATH -> EACCES" s6
    (.openat none "s_unmap/sym_other".toUTF8 { path := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "openat s_unmap/sym_other O_PATH|NOFOLLOW -> ok" s6
    (.openat none "s_unmap/sym_other".toUTF8 { path := true, nofollow := true } 0) (.opened 0)
  let _ ← stepModelCheck "openat s_unmap/sym_other/ O_PATH|NOFOLLOW -> EACCES" s6
    (.openat none "s_unmap/sym_other/".toUTF8 { path := true, nofollow := true } 0) (.err Errno.EACCES)
  let _ ← stepModelCheck "openat s_unmap/sym_other O_CREAT|O_EXCL -> EEXIST" s6
    (.openat none "s_unmap/sym_other".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644) (.err Errno.EEXIST)
  let _ ← stepModelCheck "openat s_unmap/sym_other/ O_CREAT -> EISDIR" s6
    (.openat none "s_unmap/sym_other/".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.EISDIR)
  let _ ← stepModelCheck "openat s_unmap/sym_other/l O_CREAT -> ENOTDIR" s6
    (.openat none "s_unmap/sym_other/l".toUTF8 { access := .rdwr, creat := true } 0o644) (.err Errno.ENOTDIR)

  let _ ← stepModelCheck "openat2 trailing protected_symlinks before RESOLVE_NO_SYMLINKS -> EACCES" s6
    (.openat2 none "s_unmap/sym_other".toUTF8 { resolve := { noSymlinks := true } }) (.err Errno.EACCES)
  assertTrue "openat2 trailing protected_symlinks rejects ELOOP"
    ((allowedStep s6 (.openat2 none "s_unmap/sym_other".toUTF8 { resolve := { noSymlinks := true } }) (.err Errno.ELOOP)).isNone)
  let _ ← stepModelCheck "openat2 intermediate sym_other/l RESOLVE_NO_SYMLINKS -> ELOOP" s6
    (.openat2 none "s_unmap/sym_other/l".toUTF8 { resolve := { noSymlinks := true } }) (.err Errno.ELOOP)
  let _ ← stepModelCheck "openat2 trailing sym_abs RESOLVE_BENEATH -> EACCES" s6
    (.openat2 none "s_unmap/sym_abs".toUTF8 { resolve := { beneath := true } }) (.err Errno.EACCES)
  let _ ← stepModelCheck "openat2 intermediate sym_abs/l RESOLVE_BENEATH -> EXDEV" s6
    (.openat2 none "s_unmap/sym_abs/l".toUTF8 { resolve := { beneath := true } }) (.err Errno.EXDEV)
  let sDir ← stepModelCheck "open s_unmap dirfd" s6
    (.openat none "s_unmap".toUTF8 { access := .rdonly, directory := true } 0) (.opened 0)
  let _ ← stepModelCheck "openat2(s_unmap, sym_other, BENEATH) -> EACCES" sDir
    (.openat2 (some 0) "sym_other".toUTF8 { resolve := { beneath := true } }) (.err Errno.EACCES)
  let _ ← stepModelCheck "openat2(s_unmap, sym_other/l, BENEATH) -> EXDEV" sDir
    (.openat2 (some 0) "sym_other/l".toUTF8 { resolve := { beneath := true } }) (.err Errno.EXDEV)

  let _ ← stepModelCheck "fstatat a/l -> ENOTDIR" s6
    (.fstatat none "a/l".toUTF8 {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "fstatat a/l NOFOLLOW -> ENOTDIR" s6
    (.fstatat none "a/l".toUTF8 { symlinkNofollow := true }) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "fstatat a trailing -> EACCES" s6
    (.fstatat none "a".toUTF8 {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "readlinkat a/l -> ENOTDIR" s6
    (.readlinkat none "a/l".toUTF8 64) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "readlinkat s_unmap/sym_other -> target" s6
    (.readlinkat none "s_unmap/sym_other".toUTF8 64) (.bytes "../sub/a".toUTF8)
  let _ ← stepModelCheck "readlinkat s_unmap/sym_other/ -> EACCES" s6
    (.readlinkat none "s_unmap/sym_other/".toUTF8 64) (.err Errno.EACCES)
  let _ ← stepModelCheck "fchmodat a/l -> ENOTDIR" s6
    (.fchmodat none "a/l".toUTF8 0o644) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "fchmodat s_unmap/sym_dir/a -> ok" s6
    (.fchmodat none "s_unmap/sym_dir/a".toUTF8 0o600) .unit

  let _ ← stepModelCheck "mkdirat a/l -> ENOTDIR" s6
    (.mkdirat none "a/l".toUTF8 0o755) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "mkdirat s_unmap/sym_other/l -> ENOTDIR" s6
    (.mkdirat none "s_unmap/sym_other/l".toUTF8 0o755) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "mkdirat ad/newd -> ok" s6
    (.mkdirat none "ad/newd".toUTF8 0o755) .unit
  let _ ← stepModelCheck "mkdirat s_unmap/sym_miss/l -> ENOENT" s6
    (.mkdirat none "s_unmap/sym_miss/l".toUTF8 0o755) (.err Errno.ENOENT)
  let _ ← stepModelCheck "unlinkat a/l -> ENOTDIR" s6
    (.unlinkat none "a/l".toUTF8 false) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "unlinkat s_unmap/sym_other/l -> ENOTDIR" s6
    (.unlinkat none "s_unmap/sym_other/l".toUTF8 false) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "symlinkat a/l -> ENOTDIR" s6
    (.symlinkat "t".toUTF8 none "a/l".toUTF8) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "symlinkat ad/newl -> ok" s6
    (.symlinkat "t".toUTF8 none "ad/newl".toUTF8) .unit
  let _ ← stepModelCheck "renameat2 a/l -> x ENOTDIR" s6
    (.renameat2 none "a/l".toUTF8 none "x".toUTF8 {}) (.err Errno.ENOTDIR)
  let _ ← stepModelCheck "renameat2 sub/a -> a/l ENOTDIR" s6
    (.renameat2 none "sub/a".toUTF8 none "a/l".toUTF8 {}) (.err Errno.ENOTDIR)

  let mut chainSt := s0
  chainSt ← stepModelCheck "chain l40" chainSt
    (.symlinkat "s_unmap/sym_other".toUTF8 none "l40".toUTF8) .unit
  for k in List.range 39 do
    let i := 39 - k
    chainSt ← stepModelCheck s!"chain l{i}" chainSt
      (.symlinkat s!"l{i + 1}".toUTF8 none s!"l{i}".toUTF8) .unit
  let _ ← stepModelCheck "39-hop chain into s_unmap/sym_other -> EACCES" chainSt
    (.faccessat none "l2".toUTF8 {} {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "40-hop chain into s_unmap/sym_other -> ELOOP" chainSt
    (.faccessat none "l1".toUTF8 {} {}) (.err Errno.ELOOP)

  let sOff := mkState false
  let _ ← stepModelCheck "protSym=false openat2 sym_other RESOLVE_NO_SYMLINKS -> ELOOP" sOff
    (.openat2 none "s_unmap/sym_other".toUTF8 { resolve := { noSymlinks := true } }) (.err Errno.ELOOP)
  let _ ← stepModelCheck "protSym=false readlinkat sym_other/ -> ENOTDIR" sOff
    (.readlinkat none "s_unmap/sym_other/".toUTF8 64) (.err Errno.ENOTDIR)
  let sRoProt := mkState true true
  let _ ← stepModelCheck "ro_bind protSym=true sym_other W_OK -> EACCES" sRoProt
    (.faccessat none "s_unmap/sym_other".toUTF8 { write := true } {}) (.err Errno.EACCES)
  let _ ← stepModelCheck "ro_bind protSym=true sym_other/l W_OK -> ENOTDIR" sRoProt
    (.faccessat none "s_unmap/sym_other/l".toUTF8 { write := true } {}) (.err Errno.ENOTDIR)
  let sRoOff := mkState false true
  let _ ← stepModelCheck "ro_bind protSym=false sym_other W_OK -> EROFS" sRoOff
    (.faccessat none "s_unmap/sym_other".toUTF8 { write := true } {}) (.err Errno.EROFS)

/-- Run all `Files` real and mocked regression and error-path checks (dispatched by `leanswe-fuzz --smoke` and `lean-swe-mut-test`). -/
def runChecks : IO Unit := do
  Fuzz.LinuxSyscall.Env.pinClosedStdio
  let savedMask ← Fuzz.LinuxSyscall.Env.umask 0o022
  try
    assume_files_openat_flagsAndNulGuard
    assume_files_openat2_resolveFlagsAndAbi
    assume_files_close_abaSafeFdBox
    assume_files_read_clamped16MiBAndPartial
    assume_files_write_partialAndAppend
    assume_files_fstat_portableStatDecode
    assume_files_fstatat_nofollowAndEmptyPath
    assume_files_faccessat_modeBits
    assume_files_mkdirat_modeAndNulGuard
    assume_files_unlinkat_removeDirFlag
    assume_files_renameat2_flagsAbi
    assume_files_symlinkat_rawBytesAndNulGuard
    assume_files_readlinkat_clampedRawBytes
    assume_files_getdents64_rawDirentBuffer
    assume_files_fchmodat_modeAndNulGuard
    assume_files_fchmod_modeUpdate
    assume_files_flock_advisoryLockFlags
    assume_files_fcntl_curatedCommands
    assume_files_fsync_fdSync
    assume_files_getcwd_clampedBuffer
    assume_files_lseek_offsetAndDirRewind
    assume_files_reopenReadOnly_procSelfFd
    assume_files_dupStdio_cloexecSlot
    err_openat_notFound
    err_openat_badFd
    err_openat_invalidArg
    err_openat_stateConflict
    err_openat_permissionDenied
    err_openat_transient
    err_openat2_notFound
    err_openat2_badFd
    err_openat2_invalidArg
    err_openat2_stateConflict
    err_openat2_permissionDenied
    err_openat2_transient
    err_close_mocked
    err_close_badFd
    err_read_mocked
    err_read_badFd
    err_read_stateConflict
    err_write_mocked
    err_write_badFd
    err_fstat_mocked
    err_fstat_badFd
    err_fstatat_notFound
    err_fstatat_badFd
    err_fstatat_invalidArg
    err_fstatat_stateConflict
    err_fstatat_permissionDenied
    err_fstatat_transient
    err_faccessat_notFound
    err_faccessat_badFd
    err_faccessat_invalidArg
    err_faccessat_stateConflict
    err_faccessat_permissionDenied
    err_faccessat_transient
    err_mkdirat_notFound
    err_mkdirat_badFd
    err_mkdirat_invalidArg
    err_mkdirat_stateConflict
    err_mkdirat_permissionDenied
    err_mkdirat_transient
    err_unlinkat_notFound
    err_unlinkat_badFd
    err_unlinkat_invalidArg
    err_unlinkat_stateConflict
    err_unlinkat_permissionDenied
    err_unlinkat_transient
    err_renameat2_notFound
    err_renameat2_badFd
    err_renameat2_invalidArg
    err_renameat2_stateConflict
    err_renameat2_permissionDenied
    err_renameat2_transient
    err_symlinkat_notFound
    err_symlinkat_badFd
    err_symlinkat_invalidArg
    err_symlinkat_stateConflict
    err_symlinkat_permissionDenied
    err_symlinkat_transient
    err_readlinkat_notFound
    err_readlinkat_badFd
    err_readlinkat_invalidArg
    err_readlinkat_stateConflict
    err_readlinkat_permissionDenied
    err_readlinkat_transient
    err_getdents64_notFound
    err_getdents64_badFd
    err_getdents64_invalidArg
    err_getdents64_stateConflict
    err_getdents64_mocked
    err_fchmodat_notFound
    err_fchmodat_badFd
    err_fchmodat_invalidArg
    err_fchmodat_stateConflict
    err_fchmodat_permissionDenied
    err_fchmodat_transient
    err_fchmod_mocked
    err_fchmod_badFd
    err_flock_mocked
    err_flock_badFd
    err_flock_stateConflict
    err_fcntl_mocked
    err_fcntl_badFd
    err_fcntl_invalidArg
    err_fcntl_permissionDenied
    err_fsync_mocked
    err_fsync_badFd
    err_getcwd_mocked
    err_getcwd_invalidArg
    err_lseek_mocked
    err_lseek_badFd
    err_lseek_invalidArg
    err_lseek_transient
    err_reopenReadOnly_mocked
    err_reopenReadOnly_badFd
    err_reopenReadOnly_stateConflict
    err_reopenReadOnly_permissionDenied
    err_reopenReadOnly_transient
    err_dupStdio_mocked
    runEdgeCaseReproducers
    runHardenedReproducers
    runMutantKillers
    runSharedOfdAndDirFdIntegrityChecks
    runEnvGeneralizationReproducers
    runMultiFsReproducers
    runMagicLinkAndStickyReproducers
    runSeccompAndOverlayCopyUpReproducers
    runSeccompCloseAndOpathReproducers
    runUsernsStickyAndXdevReproducers
    runCachedOpenat2AndSeccompReproducers
    runMemfdSealsAndSpecialTruncReproducers
    runOverlayHardlinkAndDirReproducers
    runStickyOverlayAndSealReproducers
    runOverlayStickyAndMountReproducers
    runOverlayUnmappedAndProcFdReproducers
    runSgidStripAndSealReproducers
    runDynamicFifoAndStdioReproducers
    runCShimBoundaryProbes
    runStatNsecReopenAndDetachChecks
    runUnboxedDirentAndGetcwdChecks
    runProtectedSymlinkWalkReproducers
  finally
    let _ ← Fuzz.LinuxSyscall.Env.umask savedMask

private def straceWorker (opName sentinelPath expectedErr : String) : IO UInt32 := do
  let expected : Errno := match expectedErr with
    | "EIO" => Errno.EIO
    | "EINTR" => Errno.EINTR
    | "ENOMEM" => Errno.ENOMEM
    | "ENFILE" => Errno.ENFILE
    | "EMFILE" => Errno.EMFILE
    | "ENOSPC" => Errno.ENOSPC
    | "EDQUOT" => (122 : Errno)
    | "ESTALE" => Errno.ESTALE
    | "ECONNRESET" => (104 : Errno)
    | _ => 0
  let checkRes {α : Type} (st : FilesState) (req : FilesReq) (res : Except Errno α) : IO UInt32 := do
    match res with
    | .error e =>
      if e != expected then
        IO.eprintln s!"strace-worker ({opName}): expected {expected} ({expectedErr}), got {e}"
        return 2
      if (Files.allowedStep st req (.err e)).isNone then
        IO.eprintln s!"strace-worker ({opName}): allowedStep rejected injected errno {e} ({expectedErr})"
        return 6
      return 0
    | .ok _ =>
      IO.eprintln s!"strace-worker ({opName}): expected error {expectedErr}, got ok"
      return 3
  let closeVerifyUnpin (fd : RawFd) : IO Bool := do
    match ← defaultOps.close fd with
    | .error e => return e != Errno.EBUSY
    | .ok () => return true
  let sp := System.FilePath.mk sentinelPath
  let dirStr := (sp.parent.map (·.toString)).getD "/"
  let baseStr := sp.fileName.getD sentinelPath
  let s0 := FilesState.withSeededTree {
    cwdPath := dirStr.toUTF8
    cwdEntries := [
      { name := baseStr.toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "ok".toUTF8 },
      { name := "unlink_target".toUTF8, kind := .reg, mode := 0o644, modeExact := true, bytes := "ok".toUTF8 },
      { name := "sub_dir".toUTF8, kind := .dir, mode := 0o755, modeExact := true },
      { name := "sym_existing".toUTF8, kind := .symlink, mode := 0o777, modeExact := true, symlinkTarget := baseStr.toUTF8 }
    ]
  }
  match opName with
  | "openat" =>
    let req : FilesReq := .openat none sentinelPath.toUTF8 roFlags 0
    let res ← defaultOps.openat none sentinelPath.toUTF8 roFlags 0
    if let .ok fd := res then
      if !(← closeVerifyUnpin fd) then return 5
    checkRes s0 req res
  | "openat2" =>
    let req : FilesReq := .openat2 none sentinelPath.toUTF8 { flags := roFlags }
    let res ← defaultOps.openat2 none sentinelPath.toUTF8 { flags := roFlags }
    if let .ok fd := res then
      if !(← closeVerifyUnpin fd) then return 5
    checkRes s0 req res
  | "read" =>
    let fd ← assertOk "strace open read" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.read fd 16
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.read 0 16) res
  | "write" =>
    let fd ← assertOk "strace open write" (← defaultOps.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let res ← defaultOps.write fd "hi".toUTF8
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.write 0 "hi".toUTF8) res
  | "fstat" =>
    let fd ← assertOk "strace open fstat" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.fstat fd
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.fstat 0) res
  | "fstatat" =>
    let res ← defaultOps.fstatat none sentinelPath.toUTF8 {}
    checkRes s0 (.fstatat none sentinelPath.toUTF8 {}) res
  | "faccessat" =>
    let res ← defaultOps.faccessat none sentinelPath.toUTF8 { read := true } {}
    checkRes s0 (.faccessat none sentinelPath.toUTF8 { read := true } {}) res
  | "mkdirat" =>
    let p := (dirStr ++ "/mkdir_target").toUTF8
    let res ← defaultOps.mkdirat none p 0o755
    checkRes s0 (.mkdirat none p 0o755) res
  | "unlinkat" =>
    let p := (dirStr ++ "/unlink_target").toUTF8
    let res ← defaultOps.unlinkat none p false
    checkRes s0 (.unlinkat none p false) res
  | "renameat2" =>
    let dst := (dirStr ++ "/rename_dst").toUTF8
    let res ← defaultOps.renameat2 none sentinelPath.toUTF8 none dst {}
    checkRes s0 (.renameat2 none sentinelPath.toUTF8 none dst {}) res
  | "symlinkat" =>
    let lp := (dirStr ++ "/symlink_new").toUTF8
    let res ← defaultOps.symlinkat baseStr.toUTF8 none lp
    checkRes s0 (.symlinkat baseStr.toUTF8 none lp) res
  | "readlinkat" =>
    let lp := (dirStr ++ "/sym_existing").toUTF8
    let res ← defaultOps.readlinkat none lp 128
    checkRes s0 (.readlinkat none lp 128) res
  | "getdents64" =>
    let dp := (dirStr ++ "/sub_dir").toUTF8
    let fd ← assertOk "strace open dir" (← defaultOps.openat none dp { access := .rdonly, directory := true } 0)
    let (_, s1) := evalModel s0 (.openat none dp { access := .rdonly, directory := true } 0)
    let res ← defaultOps.getdents64 fd 1024
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.getdents64 0 1024) res
  | "fchmodat" =>
    let res ← defaultOps.fchmodat none sentinelPath.toUTF8 0o644
    checkRes s0 (.fchmodat none sentinelPath.toUTF8 0o644) res
  | "fchmod" =>
    let fd ← assertOk "strace open fchmod" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.fchmod fd 0o644
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.fchmod 0 0o644) res
  | "flock" =>
    let fd ← assertOk "strace open flock" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.flock fd .unlock
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.flock 0 .unlock) res
  | "fcntl" =>
    let fd ← assertOk "strace open fcntl" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.fcntl fd .getFl
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.fcntl 0 .getFl) res
  | "fsync" =>
    let fd ← assertOk "strace open fsync" (← defaultOps.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let res ← defaultOps.fsync fd
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.fsync 0) res
  | "getcwd" =>
    let res ← defaultOps.getcwd 256
    checkRes s0 (.getcwd 256) res
  | "close" =>
    let fd ← assertOk "strace open close" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.close fd
    let rc ← checkRes s1 (.close 0) res
    if rc != 0 then return rc
    match ← defaultOps.fstat fd with
    | .error fe =>
      if fe != Errno.EBADF then
        IO.eprintln s!"strace-worker (close): expected detached EBADF on follow-up fstat, got {fe}"
        return 7
      return 0
    | .ok _ =>
      IO.eprintln "strace-worker (close): follow-up fstat succeeded on detached handle"
      return 7
  | "lseek" =>
    let fd ← assertOk "strace open lseek" (← defaultOps.openat none sentinelPath.toUTF8 roFlags 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 roFlags 0)
    let res ← defaultOps.lseek fd 0 .seekSet
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.lseek 0 0 .seekSet) res
  | "reopenReadOnly" =>
    let fd ← assertOk "strace open reopen" (← defaultOps.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let (_, s1) := evalModel s0 (.openat none sentinelPath.toUTF8 { access := .rdwr } 0)
    let res ← defaultOps.reopenReadOnly fd
    if let .ok rfd := res then
      if !(← closeVerifyUnpin rfd) then return 5
    if !(← closeVerifyUnpin fd) then return 5
    checkRes s1 (.reopenReadOnly 0) res
  | "dupStdio" =>
    let res ← defaultOps.dupStdio .stdin
    if let .ok dfd := res then
      if !(← closeVerifyUnpin dfd) then return 5
    checkRes s0 (.dupStdio .stdin) res
  | _ =>
    IO.eprintln s!"strace-worker: unknown op {opName}"
    return 4

/-- Run live `strace` fault-injection tests verifying `EIO`, `EINTR`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`, `EDQUOT` propagation and `Files.allowedStep` + `unpin` invariants across all 23 `Files` syscalls. -/
def runStraceFaultCheck : IO Unit := withTempSandbox "strace" fun dir => do
  let dirReal ← IO.FS.realPath dir
  let sentinel := dirReal / "fault_target"
  let unlinkTarget := dirReal / "unlink_target"
  let subDir := dirReal / "sub_dir"
  let mkdirTarget := dirReal / "mkdir_target"
  let symNew := dirReal / "symlink_new"
  let symExisting := dirReal / "sym_existing"
  IO.FS.writeFile sentinel "ok"
  IO.FS.writeFile unlinkTarget "ok"
  IO.FS.createDirAll subDir
  let _ ← defaultOps.symlinkat "fault_target".toUTF8 none symExisting.toString.toUTF8
  let exe ← IO.appPath
  let stdErrs := ["EIO", "EINTR", "ENOMEM", "ENFILE"]
  let cases : List (String × String × Array String) :=
    ([("openat", sentinel, "openat"), ("openat2", sentinel, "openat2"),
      ("read", sentinel, "read"), ("write", sentinel, "write"),
      ("fstat", sentinel, "fstat,newfstatat"), ("fstatat", sentinel, "newfstatat,statx"),
      ("faccessat", sentinel, "faccessat2"), ("mkdirat", mkdirTarget, "mkdirat"),
      ("unlinkat", unlinkTarget, "unlinkat"), ("renameat2", sentinel, "renameat2"),
      ("symlinkat", symNew, "symlinkat"), ("readlinkat", symExisting, "readlinkat"),
      ("getdents64", subDir, "getdents64"), ("fchmodat", sentinel, "fchmodat"),
      ("fchmod", sentinel, "fchmod"), ("flock", sentinel, "flock"),
      ("fcntl", sentinel, "fcntl"), ("fsync", sentinel, "fsync"),
      ("lseek", sentinel, "lseek")].flatMap fun (op, path, sys) =>
      stdErrs.map fun err =>
        (op, err, #["-P", path.toString, "-e", s!"inject={sys}:error={err}"])) ++
    (stdErrs.map fun err =>
      ("getcwd", err, #["-e", s!"inject=getcwd:error={err}"])) ++
    (["EIO", "EINTR", "ENOMEM", "EDQUOT", "ENOSPC", "ESTALE", "ECONNRESET"].map fun err =>
      ("close", err, #["-P", sentinel.toString, "-e", s!"inject=close:error={err}"])) ++
    (["EIO", "EINTR", "ENOMEM", "ENFILE", "EMFILE"].map fun err =>
      ("reopenReadOnly", err,
        ((List.range 12).map (fun i => #["-P", s!"/proc/thread-self/fd/{i + 3}"])).foldl (· ++ ·) #[] ++
        #["-e", s!"inject=openat:error={err}"])) ++
    ((stdErrs ++ ["EMFILE"]).map fun err =>
      ("dupStdio", err, #["-e", s!"inject=fcntl:error={err}"]))
  for (opName, errName, straceFlags) in cases do
    let out ← IO.Process.output {
      cmd := "strace"
      args := #["-f", "-qq", "-o", "/dev/null"] ++ straceFlags ++
        #[exe.toString, "--files-strace-worker", opName, sentinel.toString, errName]
    }
    if out.exitCode != 0 then
      throw (IO.userError s!"strace fault-injection failed for {opName}/{errName} (exit={out.exitCode}): {out.stderr}")
  let stxOut ← IO.Process.output {
    cmd := "strace"
    args := #["-f", "-qq", "-o", "/dev/null", "-P", "/proc/", "-P", "/proc/thread-self/fd/",
      "-e", "inject=statx:retval=0", exe.toString, "--files-strace-worker",
      "--statx-nomntid", sentinel.toString]
  }
  if stxOut.exitCode != 0 then
    throw (IO.userError s!"strace STATX_MNT_ID omission probe failed (exit={stxOut.exitCode}): {stxOut.stderr}")

private def runStatxNoMntIdWorker (sentinelPath : String) : IO UInt32 := do
  let fd ← match ← defaultOps.openat none sentinelPath.toUTF8 { access := .rdwr } 0 with
    | .ok f => pure f
    | .error _ => return 2
  let res ← defaultOps.reopenReadOnly fd
  if let .ok rfd := res then
    safeClose defaultOps rfd
  let cRes ← defaultOps.close fd
  let unpinOk := match cRes with
    | .ok () => true
    | .error e => e != Errno.EBUSY
  if !unpinOk then return 5
  match res with
  | .error e => return (if e == Errno.ENOENT then 0 else 4)
  | .ok _ => return 3

private def runSanitizeClosedStdioWorker (mode : String) : IO UInt32 := do
  match mode with
  | "close1" =>
    let _ ← Fuzz.LinuxSyscall.Env.closeRawFd 1
    if (← Fuzz.LinuxSyscall.Env.fdKind 1) != 0 then return 2
    let (outClosed, errClosed) ← Fuzz.LinuxSyscall.Env.sanitizeClosedStdio
    if !outClosed || errClosed then return 3
    IO.println "closed-stdout-noop"
    (← IO.getStdout).flush
    return 0
  | "close2" =>
    let _ ← Fuzz.LinuxSyscall.Env.closeRawFd 2
    if (← Fuzz.LinuxSyscall.Env.fdKind 2) != 0 then return 2
    let (outClosed, errClosed) ← Fuzz.LinuxSyscall.Env.sanitizeClosedStdio
    if outClosed || !errClosed then return 3
    IO.eprintln "closed-stderr-noop"
    (← IO.getStderr).flush
    return 0
  | "closed-both" =>
    let k1 ← Fuzz.LinuxSyscall.Env.fdKind 1
    let k2 ← Fuzz.LinuxSyscall.Env.fdKind 2
    if (k1 != 0 && k1 != 6) || (k2 != 0 && k2 != 6) then return 2
    let (outClosed, errClosed) ← Fuzz.LinuxSyscall.Env.sanitizeClosedStdio
    if !outClosed || !errClosed then return 3
    IO.println "closed-both-out"
    (← IO.getStdout).flush
    IO.eprintln "closed-both-err"
    (← IO.getStderr).flush
    return 0
  | "devnull" =>
    if (← Fuzz.LinuxSyscall.Env.fdKind 1) != 31 || (← Fuzz.LinuxSyscall.Env.fdKind 2) != 31 then return 2
    let (outClosed, errClosed) ← Fuzz.LinuxSyscall.Env.sanitizeClosedStdio
    if outClosed || errClosed then return 3
    IO.println "devnull-out"
    (← IO.getStdout).flush
    return 0
  | _ => return 9

/-- Handle `--files-strace-fault-check` and `--files-strace-worker` subcommands dispatched by `leanswe-fuzz` (`Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker`) and `lean-swe-mut-test`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["--worker", "--sanitize-closed-stdio-check", mode] =>
    return ← runSanitizeClosedStdioWorker mode
  | _ => pure ()
  Fuzz.LinuxSyscall.Env.pinClosedStdio
  match args with
  | [] =>
    runStraceFaultCheck
    IO.println "FILES_STRACE_FAULT_CHECK: ok (23 syscalls: openat, openat2, close, read, write, fstat, fstatat, faccessat, mkdirat, unlinkat, renameat2, symlinkat, readlinkat, getdents64, fchmodat, fchmod, flock, fcntl, fsync, getcwd, lseek, reopenReadOnly, dupStdio)"
    return 0
  | ["--worker", "--proc-spoof", tmpDir] =>
    runProcSpoofWorker tmpDir
  | ["--worker", "--statx-nomntid", sentinelPath] =>
    runStatxNoMntIdWorker sentinelPath
  | ["--worker", "--closed-stdio-check"] =>
    for slot in [StdioFd.stdin, StdioFd.stdout, StdioFd.stderr] do
      let slotIdx : UInt32 := match slot with | .stdin => 0 | .stdout => 1 | .stderr => 2
      let slotKind ← Fuzz.LinuxSyscall.Env.fdKind slotIdx
      let dfd ← match ← defaultOps.dupStdio slot with
        | .ok f => pure f
        | .error _ => return 2
      let st ← match ← defaultOps.fstat dfd with
        | .ok s => pure s
        | .error _ => safeClose defaultOps dfd; return 3
      let rd ← defaultOps.read dfd 16
      let wr ← defaultOps.write dfd "ok".toUTF8
      safeClose defaultOps dfd
      if slotKind == 6 then
        if st.kind != .fifo && st.kind != .socket && st.kind != .other then return 4
      else
        if st.kind != .charDev then return 4
        match rd, wr with
        | .ok bs, .ok nw => if !bs.isEmpty || nw != 2 then return 5
        | _, _ => return 6
    return 0
  | ["--worker", "--multifs", ovlDir, roDir] =>
    runMultiFsOverlayAndRoWorker ovlDir roDir
  | ["--worker", "--chroot-xdev", outDir, chrootRoot] =>
    runChrootOuterXdevWorker outDir chrootRoot
  | ["--worker", "--unmapped-userns", tmpDir] =>
    runUnmappedUsernsWorker tmpDir
  | ["--worker", opName, sentinel, errName] =>
    straceWorker opName sentinel errName
  | ["--worker", sentinel, errName] =>
    straceWorker "openat" sentinel errName
  | _ =>
    IO.eprintln s!"unknown files strace args: {args}"
    return 1

end Fuzz.LinuxSyscall.Files.Strace
