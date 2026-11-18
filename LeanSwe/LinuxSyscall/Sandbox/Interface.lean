import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.LinuxSyscall.Sandbox.Impl

namespace LeanSwe.LinuxSyscall.Sandbox

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_landlock_query"]
private opaque rawLandlockQuery : UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_landlock_create"]
private opaque rawLandlockCreate : UInt64 → UInt64 → IO (Except Errno RawFd)

@[extern "leanswe_sys_landlock_add_path_beneath"]
private opaque rawLandlockAddPathBeneath :
    @& RawFd → @& RawFd → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_sys_landlock_add_net_port"]
private opaque rawLandlockAddNetPort :
    @& RawFd → UInt64 → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_sys_landlock_restrict_self"]
private opaque rawLandlockRestrictSelf : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_sys_seccomp_get_action_avail"]
private opaque rawSeccompGetActionAvail : UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_seccomp_set_filter"]
private opaque rawSeccompSetFilter : UInt32 → @& ByteArray → IO (Except Errno UInt32)

@[extern "leanswe_sys_prctl"]
private opaque rawPrctl : UInt32 → UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_setrlimit"]
private opaque rawSetrlimit : UInt32 → UInt64 → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_sys_memfd_create"]
private opaque rawMemfdCreate : @& ByteArray → UInt32 → IO (Except Errno RawFd)

private def posixSandboxOps : PosixSandboxOps :=
  { landlockQuery := rawLandlockQuery
    landlockCreate := rawLandlockCreate
    landlockAddPathBeneath := rawLandlockAddPathBeneath
    landlockAddNetPort := rawLandlockAddNetPort
    landlockRestrictSelf := rawLandlockRestrictSelf
    seccompGetActionAvail := rawSeccompGetActionAvail
    seccompSetFilter := rawSeccompSetFilter
    prctl := rawPrctl
    setrlimit := rawSetrlimit
    memfdCreate := rawMemfdCreate }

/-- Default Linux `Sandbox` syscall bundle backed by `LeanSwe/LinuxSyscall/c/sandbox_shim.c`. -/
def defaultOps : SandboxOps :=
  Internal.mkSandboxOps posixSandboxOps

/-- Query Landlock ABI version (`attr? = none, flags = 1`) or create a ruleset descriptor (`attr? = some attr, flags = 0`) via Linux `landlock_create_ruleset(2)`. -/
@[inline] def landlockCreateRuleset (attr? : Option LandlockRulesetAttr) (flags : UInt32) :
    IO (Except Errno (LandlockCreateResult RawFd)) :=
  defaultOps.landlockCreateRuleset attr? flags

/-- Add a `PATH_BENEATH` or `NET_PORT` rule to `ruleset` via Linux `landlock_add_rule(2)`. -/
@[inline] def landlockAddRule (ruleset : RawFd) (rule : LandlockRule RawFd) :
    IO (Except Errno Unit) :=
  defaultOps.landlockAddRule ruleset rule

/-- Restrict the calling thread with `ruleset` via Linux `landlock_restrict_self(2)`. -/
@[inline] def landlockRestrictSelf (ruleset : RawFd) : IO (Except Errno Unit) :=
  defaultOps.landlockRestrictSelf ruleset

/-- Probe action availability or install a classic BPF filter via Linux `seccomp(2)`. For `SECCOMP_SET_MODE_FILTER`, rejects invalid byte lengths (`0`, non-multiple of `8`, or `> 160` instructions) and unsafe filter instructions (`SECCOMP_RET_ERRNO | 0`, `SECCOMP_RET_ERRNO | EFAULT`, `KILL_PROCESS`, `KILL_THREAD`, `TRAP`, `TRACE`, `USER_NOTIF`, unknown action bits, `BPF_RET | BPF_A`, and `BPF_ALU | BPF_DIV | BPF_X` `0x003c`) with `EINVAL` in pure Lean before invoking the kernel. -/
@[inline] def seccomp (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray) :
    IO (Except Errno UInt32) :=
  defaultOps.seccomp op flags filterBytes

/-- Execute a curated `prctl(2)` command (`NO_NEW_PRIVS`, `CHILD_SUBREAPER`, `PDEATHSIG`). -/
@[inline] def prctl (op : PrctlOp) : IO (Except Errno UInt32) :=
  defaultOps.prctl op

/-- Set soft and hard limits for `resource` (`RLIMIT_CORE`, `RLIMIT_FSIZE`, `RLIMIT_NOFILE`) via Linux `setrlimit(2)`. -/
@[inline] def setrlimit (resource : RlimitResource) (cur : UInt64) (max : UInt64) :
    IO (Except Errno Unit) :=
  defaultOps.setrlimit resource cur max

/-- Create an anonymous in-memory file via Linux `memfd_create(2)`. -/
@[inline] def memfdCreate (name : ByteArray) (flags : MemfdFlags := {}) :
    IO (Except Errno RawFd) :=
  defaultOps.memfdCreate name flags

end LeanSwe.LinuxSyscall.Sandbox
