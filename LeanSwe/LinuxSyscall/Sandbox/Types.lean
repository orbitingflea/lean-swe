import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Sandbox

open LeanSwe.LinuxSyscall

/-- No message of desired type (`ENOMSG`, `42` on `x86_64` and `aarch64`); returned by Landlock on empty access masks. -/
def ENOMSG : Errno := 42

/-- File descriptor in bad state (`EBADFD`, `77` on `x86_64` and `aarch64`); returned by Landlock on non-ruleset or pseudo-FS descriptors. -/
def EBADFD : Errno := 77

/-- Maximum `memfd_create(2)` name byte length (`249` = `NAME_MAX - strlen("memfd:")`). -/
def MFD_NAME_MAX : Nat := 249

/-- Wrapper-bounded maximum classic BPF instruction count (`160`, matching fixed `struct sock_filter buf[160]`). -/
def SECCOMP_MAX_FILTER_INSNS : Nat := 160

/-- Maximum stacked Landlock domain layers per process (`LANDLOCK_MAX_NUM_LAYERS = 16`). -/
def LANDLOCK_MAX_STACKED_LAYERS : Nat := 16

/-- Highest valid Linux signal number accepted by `prctl(PR_SET_PDEATHSIG)` (`_NSIG = 64` on `x86_64` and `aarch64`). -/
def MAX_LINUX_SIGNAL : UInt32 := 64

/-- Portable 64-bit `RLIM_INFINITY` (`~0ULL`) on 64-bit `x86_64` and `aarch64` Linux. -/
def RLIM_INFINITY : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Kernel-wide hard ceiling on `RLIMIT_NOFILE` (`sysctl_nr_open_max = 0x7FFFFFC0` on 64-bit Linux). -/
def NOFILE_KERNEL_MAX : UInt64 := 0x7FFFFFC0

/-- `landlock_create_ruleset` flag querying the highest supported Landlock ABI version (`LANDLOCK_CREATE_RULESET_VERSION = 1`). -/
def LANDLOCK_CREATE_RULESET_VERSION : UInt32 := 1

/-- `landlock_create_ruleset` flag querying the fixed-errata bitmask (`LANDLOCK_CREATE_RULESET_ERRATA = 2`). -/
def LANDLOCK_CREATE_RULESET_ERRATA : UInt32 := 2

/-- `LANDLOCK_ACCESS_FS_EXECUTE` (`1 <<< 0`). -/
def LANDLOCK_ACCESS_FS_EXECUTE : UInt64 := (1 : UInt64) <<< 0
/-- `LANDLOCK_ACCESS_FS_WRITE_FILE` (`1 <<< 1`). -/
def LANDLOCK_ACCESS_FS_WRITE_FILE : UInt64 := (1 : UInt64) <<< 1
/-- `LANDLOCK_ACCESS_FS_READ_FILE` (`1 <<< 2`). -/
def LANDLOCK_ACCESS_FS_READ_FILE : UInt64 := (1 : UInt64) <<< 2
/-- `LANDLOCK_ACCESS_FS_READ_DIR` (`1 <<< 3`). -/
def LANDLOCK_ACCESS_FS_READ_DIR : UInt64 := (1 : UInt64) <<< 3
/-- `LANDLOCK_ACCESS_FS_REMOVE_DIR` (`1 <<< 4`). -/
def LANDLOCK_ACCESS_FS_REMOVE_DIR : UInt64 := (1 : UInt64) <<< 4
/-- `LANDLOCK_ACCESS_FS_REMOVE_FILE` (`1 <<< 5`). -/
def LANDLOCK_ACCESS_FS_REMOVE_FILE : UInt64 := (1 : UInt64) <<< 5
/-- `LANDLOCK_ACCESS_FS_MAKE_CHAR` (`1 <<< 6`). -/
def LANDLOCK_ACCESS_FS_MAKE_CHAR : UInt64 := (1 : UInt64) <<< 6
/-- `LANDLOCK_ACCESS_FS_MAKE_DIR` (`1 <<< 7`). -/
def LANDLOCK_ACCESS_FS_MAKE_DIR : UInt64 := (1 : UInt64) <<< 7
/-- `LANDLOCK_ACCESS_FS_MAKE_REG` (`1 <<< 8`). -/
def LANDLOCK_ACCESS_FS_MAKE_REG : UInt64 := (1 : UInt64) <<< 8
/-- `LANDLOCK_ACCESS_FS_MAKE_SOCK` (`1 <<< 9`). -/
def LANDLOCK_ACCESS_FS_MAKE_SOCK : UInt64 := (1 : UInt64) <<< 9
/-- `LANDLOCK_ACCESS_FS_MAKE_FIFO` (`1 <<< 10`). -/
def LANDLOCK_ACCESS_FS_MAKE_FIFO : UInt64 := (1 : UInt64) <<< 10
/-- `LANDLOCK_ACCESS_FS_MAKE_BLOCK` (`1 <<< 11`). -/
def LANDLOCK_ACCESS_FS_MAKE_BLOCK : UInt64 := (1 : UInt64) <<< 11
/-- `LANDLOCK_ACCESS_FS_MAKE_SYM` (`1 <<< 12`). -/
def LANDLOCK_ACCESS_FS_MAKE_SYM : UInt64 := (1 : UInt64) <<< 12
/-- `LANDLOCK_ACCESS_FS_REFER` (`1 <<< 13`, ABI v2+). -/
def LANDLOCK_ACCESS_FS_REFER : UInt64 := (1 : UInt64) <<< 13
/-- `LANDLOCK_ACCESS_FS_TRUNCATE` (`1 <<< 14`, ABI v3+). -/
def LANDLOCK_ACCESS_FS_TRUNCATE : UInt64 := (1 : UInt64) <<< 14
/-- `LANDLOCK_ACCESS_FS_IOCTL_DEV` (`1 <<< 15`, ABI v5+). -/
def LANDLOCK_ACCESS_FS_IOCTL_DEV : UInt64 := (1 : UInt64) <<< 15
/-- `LANDLOCK_ACCESS_FS_RESOLVE_UNIX` (`1 <<< 16`, ABI v9+). -/
def LANDLOCK_ACCESS_FS_RESOLVE_UNIX : UInt64 := (1 : UInt64) <<< 16

/-- All Landlock ABI v4 filesystem access bits (`bits 0..14`, `0x7FFF`). -/
def LANDLOCK_ACCESS_FS_V4_ALL : UInt64 := ((1 : UInt64) <<< 15) - 1

/-- Directory-only Landlock filesystem access bits (`bits 3..13`, `0x3FF8`), rejected with `EINVAL` on non-directory `parentFd`. -/
def LANDLOCK_DIR_ONLY_FS_MASK : UInt64 := 0x3FF8

/-- `LANDLOCK_ACCESS_NET_BIND_TCP` (`1 <<< 0`, ABI v4+). -/
def LANDLOCK_ACCESS_NET_BIND_TCP : UInt64 := (1 : UInt64) <<< 0
/-- `LANDLOCK_ACCESS_NET_CONNECT_TCP` (`1 <<< 1`, ABI v4+). -/
def LANDLOCK_ACCESS_NET_CONNECT_TCP : UInt64 := (1 : UInt64) <<< 1
/-- All Landlock ABI v4+ TCP network access bits (`0x3`). -/
def LANDLOCK_ACCESS_NET_ALL : UInt64 := 3

/-- `SECCOMP_RET_KILL_PROCESS` (`0x80000000`). -/
def SECCOMP_RET_KILL_PROCESS : UInt32 := 0x80000000
/-- `SECCOMP_RET_KILL_THREAD` (`0x00000000`). -/
def SECCOMP_RET_KILL_THREAD : UInt32 := 0x00000000
/-- `SECCOMP_RET_TRAP` (`0x00030000`). -/
def SECCOMP_RET_TRAP : UInt32 := 0x00030000
/-- `SECCOMP_RET_ERRNO` (`0x00050000`). -/
def SECCOMP_RET_ERRNO : UInt32 := 0x00050000
/-- `SECCOMP_RET_USER_NOTIF` (`0x7FC00000`). -/
def SECCOMP_RET_USER_NOTIF : UInt32 := 0x7FC00000
/-- `SECCOMP_RET_TRACE` (`0x7FF00000`). -/
def SECCOMP_RET_TRACE : UInt32 := 0x7FF00000
/-- `SECCOMP_RET_LOG` (`0x7FFC0000`). -/
def SECCOMP_RET_LOG : UInt32 := 0x7FFC0000
/-- `SECCOMP_RET_ALLOW` (`0x7FFF0000`). -/
def SECCOMP_RET_ALLOW : UInt32 := 0x7FFF0000
/-- Mask extracting the upper 16-bit action from a 32-bit `SECCOMP_RET_*` return value (`SECCOMP_RET_ACTION_FULL = 0xFFFF0000`). -/
def SECCOMP_RET_ACTION_FULL : UInt32 := 0xFFFF0000

/-- Returns `true` iff `byteLen` is a non-empty multiple of `8` within `SECCOMP_MAX_FILTER_INSNS` (`8 <= byteLen <= 1280`). -/
def isValidSeccompFilterByteLen (byteLen : Nat) : Bool :=
  byteLen > 0 && byteLen % 8 == 0 && byteLen ≤ SECCOMP_MAX_FILTER_INSNS * 8

/-- Portable Landlock ruleset attributes (`handled_access_fs` and `handled_access_net`, ABI v4+). -/
structure LandlockRulesetAttr where
  /-- Bitmask of handled `LANDLOCK_ACCESS_FS_*` rights. -/
  handledAccessFs : UInt64 := 0
  /-- Bitmask of handled `LANDLOCK_ACCESS_NET_*` rights. -/
  handledAccessNet : UInt64 := 0
  deriving Repr, DecidableEq, BEq

/-- Result of `landlock_create_ruleset(2)`: either a scalar query result (`attr = none`) or an `O_CLOEXEC` ruleset descriptor (`attr = some ...`). -/
inductive LandlockCreateResult (fd : Type := RawFd) where
  /-- Scalar ABI version or errata bitmask returned when `attr = none` (never wrapped as an OS file descriptor). -/
  | version (value : UInt32)
  /-- Newly allocated `O_CLOEXEC` Landlock ruleset descriptor returned when `attr = some ...` and `flags = 0`. -/
  | ruleset (handle : fd)
  deriving Repr, DecidableEq, BEq

/-- Portable rule specification for `landlock_add_rule(2)` (`__NR_landlock_add_rule = 445`). -/
inductive LandlockRule (fd : Type := RawFd) where
  /-- `LANDLOCK_RULE_PATH_BENEATH` (`rule_type = 1`): allow `allowedAccess` FS rights beneath `parentFd`. -/
  | pathBeneath (parentFd : fd) (allowedAccess : UInt64)
  /-- `LANDLOCK_RULE_NET_PORT` (`rule_type = 2`): allow `allowedAccess` TCP rights on `port` (`0..65535`). -/
  | netPort (port : UInt64) (allowedAccess : UInt64)
  deriving Repr, DecidableEq, BEq

/-- Curated operations for Linux `seccomp(2)` (`__NR_seccomp = 317` on `x86_64`, `277` on `aarch64`). -/
inductive SeccompOp where
  /-- `SECCOMP_GET_ACTION_AVAIL`: probe kernel support for `action` (requires `flags == 0`). -/
  | getActionAvail (action : UInt32)
  /-- `SECCOMP_SET_MODE_FILTER`: install the classic BPF `sock_filter` program in `filterBytes`. -/
  | setModeFilter
  deriving Repr, DecidableEq, BEq

/-- Portable filter installation flags for `seccomp(SECCOMP_SET_MODE_FILTER)` (`<linux/seccomp.h>`). -/
structure SeccompFlags where
  /-- Synchronize filter across all threads in the caller's thread group (`SECCOMP_FILTER_FLAG_TSYNC`). -/
  tsync : Bool := false
  /-- Log all non-`ALLOW` filter actions (`SECCOMP_FILTER_FLAG_LOG`). -/
  log : Bool := false
  /-- Disable Speculative Store Bypass mitigation (`SECCOMP_FILTER_FLAG_SPEC_ALLOW`). -/
  specAllow : Bool := false
  /-- Return `ESRCH` instead of positive thread ID if `TSYNC` cannot synchronize (`SECCOMP_FILTER_FLAG_TSYNC_ESRCH`). -/
  tsyncEsrch : Bool := false
  /-- Wait killably for `USER_NOTIF` responses (`SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV`; fails `EINVAL` without `NEW_LISTENER`). -/
  waitKillableRecv : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `SeccompFlags` into a portable bitmask decoded by `sandbox_shim.c`. -/
def SeccompFlags.toBits (f : SeccompFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.tsync 0 ||| bit f.log 1 ||| bit f.specAllow 2 ||| bit f.tsyncEsrch 4 |||
    bit f.waitKillableRecv 5

/-- Curated `prctl(2)` operations used for process sandboxing and supervision. -/
inductive PrctlOp where
  /-- `PR_SET_NO_NEW_PRIVS` (`prctl(38, 1, 0, 0, 0)`): irreversibly enable `no_new_privs`. -/
  | setNoNewPrivs
  /-- `PR_GET_NO_NEW_PRIVS` (`prctl(39, 0, 0, 0, 0)`): query `no_new_privs` (`1` if set, `0` otherwise). -/
  | getNoNewPrivs
  /-- `PR_SET_CHILD_SUBREAPER` (`prctl(36, enable ? 1 : 0, 0, 0, 0)`): set or clear child subreaper status. -/
  | setChildSubreaper (enable : Bool)
  /-- `PR_SET_PDEATHSIG` (`prctl(1, sig, 0, 0, 0)`): set parent-death signal (`0` clears, `1..64` valid, `> 64` -> `EINVAL`). -/
  | setPdeathsig (sig : UInt32)
  deriving Repr, DecidableEq, BEq

/-- Encode `PrctlOp` into a `(cmdTag, arg)` pair decoded by `sandbox_shim.c`. -/
def PrctlOp.toRaw : PrctlOp → UInt32 × UInt32
  | .setNoNewPrivs => (0, 1)
  | .getNoNewPrivs => (1, 0)
  | .setChildSubreaper enable => (2, if enable then 1 else 0)
  | .setPdeathsig sig => (3, sig)

/-- Curated resource limit selectors for `setrlimit(2)` (`<sys/resource.h>`). -/
inductive RlimitResource where
  /-- Maximum core dump file size in bytes (`RLIMIT_CORE`). -/
  | core
  /-- Maximum size in bytes of files the process may create (`RLIMIT_FSIZE`). -/
  | fsize
  /-- One past the maximum file descriptor number that can be opened (`RLIMIT_NOFILE`). -/
  | nofile
  deriving Repr, DecidableEq, BEq

/-- Encode `RlimitResource` into a portable selector tag (`0..2`) decoded by `sandbox_shim.c`. -/
def RlimitResource.toTag : RlimitResource → UInt32
  | .core => 0
  | .fsize => 1
  | .nofile => 2

/-- Portable symbolic flags for `memfd_create(2)` (`<linux/memfd.h>`). -/
structure MemfdFlags where
  /-- Set close-on-exec (`FD_CLOEXEC`) on the new file descriptor (`MFD_CLOEXEC`). -/
  cloexec : Bool := true
  /-- Enable file-sealing operations via `fcntl(F_ADD_SEALS)` (`MFD_ALLOW_SEALING`). -/
  allowSealing : Bool := false
  /-- Create non-executable (`0o666`) and seal with `F_SEAL_EXEC` (`MFD_NOEXEC_SEAL`). -/
  noexecSeal : Bool := false
  /-- Explicitly create executable (`0o777`, `MFD_EXEC`; mutually exclusive with `noexecSeal`). -/
  exec : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `MemfdFlags` into a portable bitmask decoded by `sandbox_shim.c`. -/
def MemfdFlags.toBits (f : MemfdFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.cloexec 0 ||| bit f.allowSealing 1 ||| bit f.noexecSeal 3 ||| bit f.exec 4

/-- Decoded 8-byte classic BPF `struct sock_filter` instruction (`<linux/filter.h>`). -/
structure SockFilterInsn where
  /-- 16-bit BPF instruction opcode (`code`). -/
  code : UInt16
  /-- Forward jump offset when comparison is true (`jt`). -/
  jt : UInt8
  /-- Forward jump offset when comparison is false (`jf`). -/
  jf : UInt8
  /-- 32-bit immediate, `seccomp_data` byte offset, scratch slot, or return action (`k`). -/
  k : UInt32
  deriving Repr, DecidableEq, BEq

/-- Decode a little-endian byte list into `SockFilterInsn` records (`none` if length is not a multiple of `8`). -/
def decodeSockFilterList : List UInt8 → Option (List SockFilterInsn)
  | [] => some []
  | b0 :: b1 :: jt :: jf :: k0 :: k1 :: k2 :: k3 :: rest =>
    match decodeSockFilterList rest with
    | none => none
    | some tail =>
      let code : UInt16 := UInt16.ofNat (b0.toNat + b1.toNat * 256)
      let k : UInt32 :=
        UInt32.ofNat (k0.toNat + k1.toNat * 256 + k2.toNat * 65536 + k3.toNat * 16777216)
      some ({ code, jt, jf, k } :: tail)
  | _ => none

/-- Tail-recursive byte decoder for `ByteArray` into `SockFilterInsn` records without materializing `ByteArray.data.toList`. -/
def decodeSockFilterBytesAux (b : ByteArray) (i : Nat) (acc : List SockFilterInsn) :
    Nat → List SockFilterInsn
  | 0 => acc.reverse
  | n + 1 =>
    let b0 := b.get! i
    let b1 := b.get! (i + 1)
    let jt := b.get! (i + 2)
    let jf := b.get! (i + 3)
    let k0 := b.get! (i + 4)
    let k1 := b.get! (i + 5)
    let k2 := b.get! (i + 6)
    let k3 := b.get! (i + 7)
    let code : UInt16 := UInt16.ofNat (b0.toNat + b1.toNat * 256)
    let k : UInt32 :=
      UInt32.ofNat (k0.toNat + k1.toNat * 256 + k2.toNat * 65536 + k3.toNat * 16777216)
    decodeSockFilterBytesAux b (i + 8) ({ code, jt, jf, k } :: acc) n

/-- Decode a `ByteArray` into `SockFilterInsn` instructions (`none` if byte length is not a multiple of `8`). -/
def decodeSockFilters (b : ByteArray) : Option (List SockFilterInsn) :=
  if b.size % 8 != 0 then
    none
  else
    some (decodeSockFilterBytesAux b 0 [] (b.size / 8))

/-- Returns `true` iff `insn` neither aborts early with `0 = SECCOMP_RET_KILL_THREAD` via `BPF_ALU | BPF_DIV | BPF_X` (`0x003c` when `X == 0`) nor uses an unsafe `BPF_RET` instruction (`BPF_RET | BPF_A`, `KILL_PROCESS`, `KILL_THREAD`, `TRAP`, `TRACE`, `USER_NOTIF`, unknown action bits, `SECCOMP_RET_ERRNO | 0`, or `SECCOMP_RET_ERRNO | EFAULT`). -/
def isSafeSeccompInsn (insn : SockFilterInsn) : Bool :=
  if insn.code == 0x003c then
    false
  else if (insn.code &&& 0x0007) == 0x0006 then
    if insn.code != 0x0006 then
      false
    else
      let act := insn.k &&& SECCOMP_RET_ACTION_FULL
      if act == SECCOMP_RET_ALLOW || act == SECCOMP_RET_LOG then
        true
      else if act == SECCOMP_RET_ERRNO then
        let data := insn.k &&& 0xFFFF
        data != 0 && data != Errno.EFAULT
      else
        false
  else
    true

/-- Returns `true` iff `filterBytes` decodes into classic BPF instructions every one of which satisfies `isSafeSeccompInsn`. -/
def hasSafeSeccompRetBytes (filterBytes : ByteArray) : Bool :=
  match decodeSockFilters filterBytes with
  | none => false
  | some prog => prog.all isSafeSeccompInsn

/-- Semantic error classification across the 7 curated `Sandbox` syscalls for `errorCoverage`. -/
inductive SandboxErrorKind where
  /-- Closed file descriptor (`EBADF`) or descriptor of incompatible kernel type (`EBADFD`). -/
  | badFd
  /-- Invalid flag, bitmask, signal, port, length, embedded NUL, BPF program, or empty access mask (`EINVAL`, `ENOMSG`). -/
  | invalidArg
  /-- Missing `no_new_privs` / capability or raising hard limit (`EPERM`, `EACCES`). -/
  | permissionDenied
  /-- Stacked Landlock domain limit, unsupported action/subsystem, or thread-sync failure (`E2BIG`, `EOPNOTSUPP`, `ENOSYS`, `ESRCH`, `EBUSY`). -/
  | limitOrUnsupported
  /-- Transient interrupt or kernel memory/FD exhaustion (`EINTR`, `EIO`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq

/-- Classify any Linux `Errno` into its `SandboxErrorKind` bucket. -/
def SandboxErrorKind.ofErrno (e : Errno) : SandboxErrorKind :=
  if e == Errno.EBADF || e == EBADFD then .badFd
  else if e == Errno.EINVAL || e == ENOMSG then .invalidArg
  else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
  else if e == Errno.E2BIG || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS ||
      e == Errno.ESRCH || e == Errno.EBUSY then .limitOrUnsupported
  else .transientOrResource

/-- Low-level thin C syscall hook bundle parameterized over monad `m` and descriptor type `fd`. -/
structure PosixSandboxOpsM (m : Type → Type) (fd : Type := RawFd) where
  /-- Raw `landlock_create_ruleset(NULL, 0, flags)` query hook (`flags != 0`). -/
  landlockQuery : UInt32 → m (Except Errno UInt32)
  /-- Raw `landlock_create_ruleset(&attr, sizeof(attr), 0)` ruleset-creation hook. -/
  landlockCreate : UInt64 → UInt64 → m (Except Errno fd)
  /-- Raw `landlock_add_rule(rs, LANDLOCK_RULE_PATH_BENEATH, &pb, 0)` hook. -/
  landlockAddPathBeneath : fd → fd → UInt64 → m (Except Errno Unit)
  /-- Raw `landlock_add_rule(rs, LANDLOCK_RULE_NET_PORT, &np, 0)` hook. -/
  landlockAddNetPort : fd → UInt64 → UInt64 → m (Except Errno Unit)
  /-- Raw `landlock_restrict_self(rs, 0)` hook. -/
  landlockRestrictSelf : fd → m (Except Errno Unit)
  /-- Raw `seccomp(SECCOMP_GET_ACTION_AVAIL, 0, &action)` hook. -/
  seccompGetActionAvail : UInt32 → m (Except Errno UInt32)
  /-- Raw `seccomp(SECCOMP_SET_MODE_FILTER, flagsBits, &prog)` hook (`8 <= filterBytes.size <= 1280`, multiple of 8). -/
  seccompSetFilter : UInt32 → ByteArray → m (Except Errno UInt32)
  /-- Raw `prctl` hook accepting `(cmdTag, arg)` from `PrctlOp.toRaw`. -/
  prctl : UInt32 → UInt32 → m (Except Errno UInt32)
  /-- Raw `setrlimit` hook accepting `(resTag, cur, max)`. -/
  setrlimit : UInt32 → UInt64 → UInt64 → m (Except Errno Unit)
  /-- Raw `memfd_create` hook accepting NUL-free `name` (`<= 249` bytes) and `MemfdFlags.toBits`. -/
  memfdCreate : ByteArray → UInt32 → m (Except Errno fd)

/-- Real-world `IO` specialization of `PosixSandboxOpsM` over `RawFd`. -/
abbrev PosixSandboxOps := PosixSandboxOpsM IO RawFd

/-- Monadic capability bundle for all 7 curated Linux `Sandbox` syscalls, parameterized over `m` and descriptor `fd`. -/
structure SandboxOpsM (m : Type → Type) (fd : Type := RawFd) where
  /-- Query Landlock ABI version (`attr = none, flags = 1`) or create a ruleset descriptor (`attr = some ..., flags = 0`). -/
  landlockCreateRuleset : Option LandlockRulesetAttr → UInt32 → m (Except Errno (LandlockCreateResult fd))
  /-- Add a `PATH_BENEATH` or `NET_PORT` rule to a Landlock ruleset via `landlock_add_rule(2)`. -/
  landlockAddRule : fd → LandlockRule fd → m (Except Errno Unit)
  /-- Enforce a Landlock ruleset on the calling thread via `landlock_restrict_self(2)`. -/
  landlockRestrictSelf : fd → m (Except Errno Unit)
  /-- Query action availability or install a classic BPF filter via `seccomp(2)`. -/
  seccomp : SeccompOp → SeccompFlags → ByteArray → m (Except Errno UInt32)
  /-- Execute a curated `prctl(2)` command (`NO_NEW_PRIVS`, `CHILD_SUBREAPER`, `PDEATHSIG`). -/
  prctl : PrctlOp → m (Except Errno UInt32)
  /-- Set soft and hard resource limits (`RLIMIT_CORE`, `RLIMIT_FSIZE`, `RLIMIT_NOFILE`) via `setrlimit(2)`. -/
  setrlimit : RlimitResource → UInt64 → UInt64 → m (Except Errno Unit)
  /-- Create an anonymous in-memory file via `memfd_create(2)`. -/
  memfdCreate : ByteArray → MemfdFlags → m (Except Errno fd)

/-- Real-world `IO` specialization of `SandboxOpsM` using ABA-safe `RawFd` handles. -/
abbrev SandboxOps := SandboxOpsM IO RawFd

/-- Logical handle identifier used by the relational `Sandbox` world model and fuzzer traces. -/
abbrev HandleId := Nat

/-- One syscall request in a `Sandbox` world-model trace (covers all 7 curated syscalls). -/
inductive SandboxReq where
  /-- `landlock_create_ruleset(attr?, flags)`. -/
  | landlockCreateRuleset (attr? : Option LandlockRulesetAttr) (flags : UInt32)
  /-- `landlock_add_rule(ruleset, rule)`. -/
  | landlockAddRule (ruleset : HandleId) (rule : LandlockRule HandleId)
  /-- `landlock_restrict_self(ruleset)`. -/
  | landlockRestrictSelf (ruleset : HandleId)
  /-- `seccomp(op, flags, filterBytes)`. -/
  | seccomp (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray)
  /-- `prctl(op)`. -/
  | prctl (op : PrctlOp)
  /-- `setrlimit(resource, cur, max)`. -/
  | setrlimit (resource : RlimitResource) (cur : UInt64) (max : UInt64)
  /-- `memfd_create(name, flags)`. -/
  | memfdCreate (name : ByteArray) (flags : MemfdFlags)

/-- Raw kernel outcome observed for one `SandboxReq`. -/
inductive SandboxOutcome where
  /-- `landlock_create_ruleset(none, flags)` succeeded with scalar ABI/errata `value`. -/
  | landlockVersion (value : UInt32)
  /-- `landlock_create_ruleset(some attr, 0)` or `memfd_create` succeeded and allocated `hid`. -/
  | opened (hid : HandleId)
  /-- Unit-returning syscall succeeded (`landlock_add_rule`, `landlock_restrict_self`, `setrlimit`). -/
  | unit
  /-- `UInt32`-returning syscall succeeded (`seccomp`, `prctl`). -/
  | u32 (val : UInt32)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, DecidableEq, BEq

end LeanSwe.LinuxSyscall.Sandbox
