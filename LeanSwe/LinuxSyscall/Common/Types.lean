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
/-- Text file busy (`ETXTBSY`, 26). -/
def ETXTBSY : Errno := 26
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
/-- No message of desired type (`ENOMSG`, 42). Returned by Landlock on empty access masks. -/
def ENOMSG : Errno := 42
/-- Package not installed (`ENOPKG`, 65). Returned by `pipe2(..., O_NOTIFICATION_PIPE)` when kernel `CONFIG_WATCH_QUEUE` is disabled. -/
def ENOPKG : Errno := 65
/-- Protocol error (`EPROTO`, 71). -/
def EPROTO : Errno := 71
/-- File descriptor in bad state (`EBADFD`, 77). Returned by Landlock on non-ruleset or pseudo-FS descriptors. -/
def EBADFD : Errno := 77
/-- Socket operation on non-socket (`ENOTSOCK`, 88). -/
def ENOTSOCK : Errno := 88
/-- Destination address required (`EDESTADDRREQ`, 89). -/
def EDESTADDRREQ : Errno := 89
/-- Message too long (`EMSGSIZE`, 90). -/
def EMSGSIZE : Errno := 90
/-- Protocol wrong type for socket (`EPROTOTYPE`, 91). -/
def EPROTOTYPE : Errno := 91
/-- Protocol not available (`ENOPROTOOPT`, 92). -/
def ENOPROTOOPT : Errno := 92
/-- Protocol not supported (`EPROTONOSUPPORT`, 93). -/
def EPROTONOSUPPORT : Errno := 93
/-- Socket type not supported (`ESOCKTNOSUPPORT`, 94). -/
def ESOCKTNOSUPPORT : Errno := 94
/-- Operation not supported (`EOPNOTSUPP` / `ENOTSUP`, 95). -/
def EOPNOTSUPP : Errno := 95
/-- Protocol family not supported (`EPFNOSUPPORT`, 96). -/
def EPFNOSUPPORT : Errno := 96
/-- Address family not supported by protocol (`EAFNOSUPPORT`, 97). -/
def EAFNOSUPPORT : Errno := 97
/-- Address already in use (`EADDRINUSE`, 98). -/
def EADDRINUSE : Errno := 98
/-- Cannot assign requested address (`EADDRNOTAVAIL`, 99). -/
def EADDRNOTAVAIL : Errno := 99
/-- Network is down (`ENETDOWN`, 100). -/
def ENETDOWN : Errno := 100
/-- Network is unreachable (`ENETUNREACH`, 101). -/
def ENETUNREACH : Errno := 101
/-- Software caused connection abort (`ECONNABORTED`, 103). -/
def ECONNABORTED : Errno := 103
/-- Connection reset by peer (`ECONNRESET`, 104). -/
def ECONNRESET : Errno := 104
/-- No buffer space available (`ENOBUFS`, 105). -/
def ENOBUFS : Errno := 105
/-- Transport endpoint is already connected (`EISCONN`, 106). -/
def EISCONN : Errno := 106
/-- Transport endpoint is not connected (`ENOTCONN`, 107). -/
def ENOTCONN : Errno := 107
/-- Cannot send after transport endpoint shutdown (`ESHUTDOWN`, 108). -/
def ESHUTDOWN : Errno := 108
/-- Too many references: cannot splice (`ETOOMANYREFS`, 109). -/
def ETOOMANYREFS : Errno := 109
/-- Connection timed out (`ETIMEDOUT`, 110). -/
def ETIMEDOUT : Errno := 110
/-- Connection refused (`ECONNREFUSED`, 111). -/
def ECONNREFUSED : Errno := 111
/-- No route to host (`EHOSTUNREACH`, 113). -/
def EHOSTUNREACH : Errno := 113
/-- Operation already in progress (`EALREADY`, 114). -/
def EALREADY : Errno := 114
/-- Operation now in progress (`EINPROGRESS`, 115). -/
def EINPROGRESS : Errno := 115
/-- Stale file handle (`ESTALE`, 116). -/
def ESTALE : Errno := 116
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
  | 26 => "ETXTBSY"
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
  | 42 => "ENOMSG"
  | 65 => "ENOPKG"
  | 71 => "EPROTO"
  | 77 => "EBADFD"
  | 88 => "ENOTSOCK"
  | 89 => "EDESTADDRREQ"
  | 90 => "EMSGSIZE"
  | 91 => "EPROTOTYPE"
  | 92 => "ENOPROTOOPT"
  | 93 => "EPROTONOSUPPORT"
  | 94 => "ESOCKTNOSUPPORT"
  | 95 => "EOPNOTSUPP"
  | 96 => "EPFNOSUPPORT"
  | 97 => "EAFNOSUPPORT"
  | 98 => "EADDRINUSE"
  | 99 => "EADDRNOTAVAIL"
  | 100 => "ENETDOWN"
  | 101 => "ENETUNREACH"
  | 103 => "ECONNABORTED"
  | 104 => "ECONNRESET"
  | 105 => "ENOBUFS"
  | 106 => "EISCONN"
  | 107 => "ENOTCONN"
  | 108 => "ESHUTDOWN"
  | 109 => "ETOOMANYREFS"
  | 110 => "ETIMEDOUT"
  | 111 => "ECONNREFUSED"
  | 113 => "EHOSTUNREACH"
  | 114 => "EALREADY"
  | 115 => "EINPROGRESS"
  | 116 => "ESTALE"
  | 125 => "ECANCELED"
  | n => s!"ERRNO({n})"

end Errno

private opaque RawFdPointed : NonemptyType

/-- Opaque ABA-safe Linux file descriptor handle backed by a mutex-guarded `LeanFdBox` external object. -/
def RawFd : Type := RawFdPointed.type

instance : Nonempty RawFd := RawFdPointed.property

/-- Tail-recursive `ByteArray` index loop checking for an embedded `0x00` byte across `rem` remaining bytes from `i`. -/
def hasEmbeddedNulLoop (b : ByteArray) (i : Nat) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    if h : i < b.size then
      if b[i] == (0 : UInt8) then true
      else hasEmbeddedNulLoop b (i + 1) rem
    else false

/-- Returns `true` iff `b` contains an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNul (b : ByteArray) : Bool :=
  hasEmbeddedNulLoop b 0 b.size

attribute [local simp] hasEmbeddedNulLoop hasEmbeddedNul hasEmbeddedNulLoop.eq_def hasEmbeddedNul.eq_def

/-- Kernel-reducible ASCII byte-array literal helper from `List Char` (avoids opaque `@[extern]` string UTF-8 decoding in proofs). -/
def asciiBytes (cs : List Char) : ByteArray :=
  ByteArray.mk (cs.map (fun c => UInt8.ofNat c.toNat)).toArray

/-- Returns `true` iff `e` is a curated catastrophic OS or hardware fault (`ENOMEM`, `EIO`, `ENFILE`) excluded from `healthyStep`. -/
def Errno.isCriticalOsErrno (e : Errno) : Bool :=
  e == Errno.ENOMEM || e == Errno.EIO || e == Errno.ENFILE

/-- Returns `true` iff `e` is an everyday visible OS resource-limit errno (`EMFILE`, `ENOSPC`) permitted inside `healthyStep`. -/
def Errno.isResourceLimitErrno (e : Errno) : Bool :=
  e == Errno.EMFILE || e == Errno.ENOSPC

/-- Default bounded retry budget for `EINTR` on single blocking syscalls. -/
def DEFAULT_EINTR_FUEL : Nat := 256

/-- Default fuel bound for non-blocking pipe streaming and timeout polling loops (`2^32`). -/
def DEFAULT_IO_FUEL : Nat := UInt32.size

/-- Retry an `Except Errno α` action across `Errno.EINTR` up to `fuel` additional attempts. -/
def retryEintr {m : Type → Type} [Monad m] {α : Type}
    (act : m (Except Errno α)) : Nat → m (Except Errno α)
  | 0 => act
  | fuel + 1 => do
    match ← act with
    | .error e =>
      if e == Errno.EINTR then retryEintr act fuel else return .error e
    | .ok v => return .ok v

/-- Flatten `chunks` into a single `ByteArray` in `O(totalBytes)`. -/
def concatChunks (chunks : Array ByteArray) (totalCap : Nat) : ByteArray :=
  chunks.toList.foldl (· ++ ·) (ByteArray.emptyWithCapacity totalCap)

/-- Tail-recursive byte-slice splitter accumulating segments delimited by `sep`. -/
def splitByteAcc (sep : UInt8) (curRev : List UInt8) (accRev : List ByteArray) :
    List UInt8 → List ByteArray
  | [] => (ByteArray.mk curRev.reverse.toArray :: accRev).reverse
  | b :: bs =>
    if b == sep then
      splitByteAcc sep [] (ByteArray.mk curRev.reverse.toArray :: accRev) bs
    else
      splitByteAcc sep (b :: curRev) accRev bs

/-- Split `b` on every occurrence of byte `sep`, preserving empty segments. -/
def splitByte (sep : UInt8) (b : ByteArray) : List ByteArray :=
  splitByteAcc sep [] [] b.toList

end LeanSwe.LinuxSyscall
