import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Impl

namespace LeanSwe.LinuxSyscall.Passwd

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_getpwuid_once"]
private opaque rawGetpwuidOnce :
    UInt32 → UInt32 → BaseIO (Except Errno (Option Internal.RawPasswdTuple))

@[extern "leanswe_sys_getpwnam_once"]
private opaque rawGetpwnamOnce :
    @& ByteArray → UInt32 → BaseIO (Except Errno (Option Internal.RawPasswdTuple))

private def posixPasswdOps : Internal.PosixPasswdOpsM BaseIO :=
  { getpwuidOnce := rawGetpwuidOnce
    getpwnamOnce := rawGetpwnamOnce }

/-- Default Linux `Passwd` capability bundle backed by `LeanSwe/LinuxSyscall/c/passwd_shim.c`. -/
def defaultOps : PasswdOps :=
  { getpwuid := fun uid => (Internal.mkPasswdOpsM posixPasswdOps).getpwuid uid
    getpwnam := fun name => (Internal.mkPasswdOpsM posixPasswdOps).getpwnam name }

/-- Look up the `PasswdEntry` for `uid` via reentrant `getpwuid_r(3)` with Lean `ERANGE` retry (`4096..65536`). -/
@[inline] def getpwuid (uid : UInt32) : IO (Except Errno (Option PasswdEntry)) :=
  defaultOps.getpwuid uid

/-- Look up the `PasswdEntry` for raw username `name` via reentrant `getpwnam_r(3)`, returning `Errno.EINVAL` on embedded `0x00` bytes, `Errno.ENAMETOOLONG` above `MAX_PASSWD_NAME_BYTES`, and retrying `ERANGE` (`4096..65536`) in Lean. -/
@[inline] def getpwnam (name : ByteArray) : IO (Except Errno (Option PasswdEntry)) :=
  defaultOps.getpwnam name

end LeanSwe.LinuxSyscall.Passwd
