namespace LeanSwe.LinuxSyscall

/-- Raw Linux `errno` code (`include/uapi/asm-generic/errno*.h`, identical on `x86_64` and `aarch64`). -/
abbrev Errno := UInt32

/-- POSIX file permission mode bits (lower 12 bits, e.g. `0o644`, `0o755`). -/
abbrev Mode := UInt32

/-- Wrapper allocation cap (`16 MiB`) for read-like syscalls, legal under partial-read semantics. -/
def MAX_READ_BYTES : UInt32 := 16777216

/-- Maximum Linux path byte length (`PATH_MAX`). -/
def PATH_MAX : Nat := 4096

/-- Maximum Linux single path component byte length (`NAME_MAX`). -/
def NAME_MAX : Nat := 255

namespace Errno

/-- Operation not permitted (`EPERM`, 1). -/
def EPERM : Errno := 1
/-- No such file or directory (`ENOENT`, 2). -/
def ENOENT : Errno := 2
/-- No such process (`ESRCH`, 3). -/
def ESRCH : Errno := 3
/-- Interrupted system call (`EINTR`, 4). -/
def EINTR : Errno := 4
/-- Input/output error (`EIO`, 5). -/
def EIO : Errno := 5
/-- No such device or address (`ENXIO`, 6). -/
def ENXIO : Errno := 6
/-- Argument list too long (`E2BIG`, 7). -/
def E2BIG : Errno := 7
/-- Exec format error (`ENOEXEC`, 8). -/
def ENOEXEC : Errno := 8
/-- Bad file descriptor (`EBADF`, 9). -/
def EBADF : Errno := 9
/-- No child processes (`ECHILD`, 10). -/
def ECHILD : Errno := 10
/-- Resource temporarily unavailable (`EAGAIN` / `EWOULDBLOCK`, 11). -/
def EAGAIN : Errno := 11
/-- Operation would block (`EWOULDBLOCK`, alias of `EAGAIN`, 11). -/
def EWOULDBLOCK : Errno := 11
/-- Cannot allocate memory (`ENOMEM`, 12). -/
def ENOMEM : Errno := 12
/-- Permission denied (`EACCES`, 13). -/
def EACCES : Errno := 13
/-- Bad address (`EFAULT`, 14). Fail-loud C-wrapper invariant violation; wrappers `abort()` rather than masking it. -/
def EFAULT : Errno := 14
/-- Device or resource busy (`EBUSY`, 16). -/
def EBUSY : Errno := 16
/-- File exists (`EEXIST`, 17). -/
def EEXIST : Errno := 17
/-- Invalid cross-device link (`EXDEV`, 18). Also returned by `openat2` `RESOLVE_BENEATH` escape attempts. -/
def EXDEV : Errno := 18
/-- No such device (`ENODEV`, 19). -/
def ENODEV : Errno := 19
/-- Not a directory (`ENOTDIR`, 20). -/
def ENOTDIR : Errno := 20
/-- Is a directory (`EISDIR`, 21). -/
def EISDIR : Errno := 21
/-- Invalid argument (`EINVAL`, 22). -/
def EINVAL : Errno := 22
/-- Too many open files in system (`ENFILE`, 23). -/
def ENFILE : Errno := 23
/-- Too many open files (`EMFILE`, 24). -/
def EMFILE : Errno := 24
/-- Inappropriate ioctl for device (`ENOTTY`, 25). -/
def ENOTTY : Errno := 25
/-- File too large (`EFBIG`, 27). -/
def EFBIG : Errno := 27
/-- No space left on device (`ENOSPC`, 28). -/
def ENOSPC : Errno := 28
/-- Illegal seek (`ESPIPE`, 29). -/
def ESPIPE : Errno := 29
/-- Read-only file system (`EROFS`, 30). -/
def EROFS : Errno := 30
/-- Too many links (`EMLINK`, 31). -/
def EMLINK : Errno := 31
/-- Broken pipe (`EPIPE`, 32). -/
def EPIPE : Errno := 32
/-- Numerical result out of range (`ERANGE`, 34). Returned by `getcwd` when buffer is too small. -/
def ERANGE : Errno := 34
/-- File name too long (`ENAMETOOLONG`, 36). -/
def ENAMETOOLONG : Errno := 36
/-- Function not implemented (`ENOSYS`, 38). -/
def ENOSYS : Errno := 38
/-- Directory not empty (`ENOTEMPTY`, 39). -/
def ENOTEMPTY : Errno := 39
/-- Too many levels of symbolic links (`ELOOP`, 40). -/
def ELOOP : Errno := 40
/-- Operation not supported (`EOPNOTSUPP` / `ENOTSUP`, 95). -/
def EOPNOTSUPP : Errno := 95
/-- Operation canceled (`ECANCELED`, 125). -/
def ECANCELED : Errno := 125

/-- Returns `true` iff `e` is a transient or resource-exhaustion OS errno (`EINTR`, `EIO`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`). -/
def isTransientOsErrno (e : Errno) : Bool :=
  e == EINTR || e == EIO || e == ENOMEM ||
  e == ENFILE || e == EMFILE || e == ENOSPC

/-- Returns `true` iff `e` is a valid `SECCOMP_RET_ERRNO` data code (`1..4095`) excluding `EFAULT` (`14`, fail-loud pointer invariant). -/
def isSafeSeccompErrno (e : Errno) : Bool :=
  e != EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095

/-- Human-readable symbolic name of a Linux `Errno` code for diagnostics and fuzzing logs. -/
def name (e : Errno) : String :=
  match e.toNat with
  | 1 => "EPERM"
  | 2 => "ENOENT"
  | 3 => "ESRCH"
  | 4 => "EINTR"
  | 5 => "EIO"
  | 6 => "ENXIO"
  | 7 => "E2BIG"
  | 8 => "ENOEXEC"
  | 9 => "EBADF"
  | 10 => "ECHILD"
  | 11 => "EAGAIN"
  | 12 => "ENOMEM"
  | 13 => "EACCES"
  | 14 => "EFAULT"
  | 16 => "EBUSY"
  | 17 => "EEXIST"
  | 18 => "EXDEV"
  | 19 => "ENODEV"
  | 20 => "ENOTDIR"
  | 21 => "EISDIR"
  | 22 => "EINVAL"
  | 23 => "ENFILE"
  | 24 => "EMFILE"
  | 25 => "ENOTTY"
  | 27 => "EFBIG"
  | 28 => "ENOSPC"
  | 29 => "ESPIPE"
  | 30 => "EROFS"
  | 31 => "EMLINK"
  | 32 => "EPIPE"
  | 34 => "ERANGE"
  | 36 => "ENAMETOOLONG"
  | 38 => "ENOSYS"
  | 39 => "ENOTEMPTY"
  | 40 => "ELOOP"
  | 95 => "EOPNOTSUPP"
  | 125 => "ECANCELED"
  | n => s!"ERRNO({n})"

end Errno

private opaque RawFdPointed : NonemptyType

/-- Opaque ABA-safe Linux file descriptor handle backed by a mutex-guarded `LeanFdBox` external object. -/
def RawFd : Type := RawFdPointed.type

instance : Nonempty RawFd := RawFdPointed.property

/-- Returns `true` iff `b` contains an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNul (b : ByteArray) : Bool :=
  b.data.toList.any (· == (0 : UInt8))

/-- Kernel-reducible ASCII byte-array literal helper from `List Char` (avoids opaque `@[extern]` string UTF-8 decoding in proofs). -/
def asciiBytes (cs : List Char) : ByteArray :=
  ByteArray.mk (cs.map (fun c => UInt8.ofNat c.toNat)).toArray

/-- Returns `true` iff `e` is a curated catastrophic OS or hardware fault (`ENOMEM`, `EIO`, `ENFILE`) excluded from `healthyStep`. -/
def Errno.isCriticalOsErrno (e : Errno) : Bool :=
  e == Errno.ENOMEM || e == Errno.EIO || e == Errno.ENFILE

/-- Returns `true` iff `e` is an everyday visible OS resource-limit errno (`EMFILE`, `ENOSPC`) permitted inside `healthyStep`. -/
def Errno.isResourceLimitErrno (e : Errno) : Bool :=
  e == Errno.EMFILE || e == Errno.ENOSPC

end LeanSwe.LinuxSyscall
