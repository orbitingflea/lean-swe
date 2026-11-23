import LeanSwe.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Sandbox.Types

namespace LeanSwe.LinuxSyscall.Sandbox

open LeanSwe.LinuxSyscall

export LeanSwe.LinuxSyscall (assocGet assocSetAux assocSet)

/-- Construct a `ByteArray` consisting of `n` copies of `byte` (kernel-reducible). -/
def mkRepBytes (n : Nat) (byte : UInt8 := 97) : ByteArray :=
  ByteArray.mk (List.replicate n byte).toArray

/-- Serialize one `SockFilterInsn` into 8 little-endian bytes matching `struct sock_filter`. -/
def encodeSockFilterInsn (insn : SockFilterInsn) : List UInt8 :=
  let c := insn.code.toNat
  let k := insn.k.toNat
  [ UInt8.ofNat (c % 256)
  , UInt8.ofNat ((c / 256) % 256)
  , insn.jt
  , insn.jf
  , UInt8.ofNat (k % 256)
  , UInt8.ofNat ((k / 256) % 256)
  , UInt8.ofNat ((k / 65536) % 256)
  , UInt8.ofNat ((k / 16777216) % 256) ]

/-- Serialize a list of `SockFilterInsn` instructions into contiguous 8-byte little-endian `struct sock_filter` wire bytes. -/
def encodeSockFilters (prog : List SockFilterInsn) : ByteArray :=
  ByteArray.mk (prog.flatMap encodeSockFilterInsn).toArray

/-- Minimal 1-instruction `BPF_RET | BPF_K, SECCOMP_RET_ALLOW` classic BPF filter wire bytes. -/
def allowAllSeccompFilterBytes : ByteArray :=
  encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]

/-- Returns `true` iff `action` is one of the 8 action codes recognized by `seccomp(SECCOMP_GET_ACTION_AVAIL)` on Linux `>= 6.7`. -/
def isKnownSeccompAction (action : UInt32) : Bool :=
  action == SECCOMP_RET_KILL_PROCESS ||
  action == SECCOMP_RET_KILL_THREAD ||
  action == SECCOMP_RET_TRAP ||
  action == SECCOMP_RET_ERRNO ||
  action == SECCOMP_RET_USER_NOTIF ||
  action == SECCOMP_RET_TRACE ||
  action == SECCOMP_RET_LOG ||
  action == SECCOMP_RET_ALLOW

/-- Forward-DAG verifier matching Linux `seccomp_check_filter` + `bpf_check_classic` (`check_load_and_stores`). -/
def checkSeccompBpfLoop (pc : Nat) (totalLen : Nat) (memValid : UInt32)
    (masks : List (Nat × UInt32)) : List SockFilterInsn → Bool
  | [] => true
  | insn :: rest =>
    let curMem := memValid &&& (assocGet masks pc).getD 0xFFFF
    let c := insn.code.toNat
    if c == 0x0000 || c == 0x0001 || c == 0x0080 || c == 0x0081 ||
        c == 0x0007 || c == 0x0087 ||
        c == 0x0004 || c == 0x000c || c == 0x0014 || c == 0x001c ||
        c == 0x0024 || c == 0x002c || c == 0x003c ||
        c == 0x0044 || c == 0x004c || c == 0x0054 || c == 0x005c ||
        c == 0x006c || c == 0x007c || c == 0x0084 ||
        c == 0x00a4 || c == 0x00ac ||
        c == 0x0006 || c == 0x0016 then
      checkSeccompBpfLoop (pc + 1) totalLen curMem masks rest
    else if c == 0x0020 then
      insn.k.toNat < 64 && insn.k.toNat % 4 == 0 &&
        checkSeccompBpfLoop (pc + 1) totalLen curMem masks rest
    else if c == 0x0034 then
      insn.k != 0 && checkSeccompBpfLoop (pc + 1) totalLen curMem masks rest
    else if c == 0x0064 || c == 0x0074 then
      insn.k.toNat < 32 && checkSeccompBpfLoop (pc + 1) totalLen curMem masks rest
    else if c == 0x0002 || c == 0x0003 then
      if insn.k.toNat < 16 then
        let bit := (1 : UInt32) <<< UInt32.ofNat insn.k.toNat
        checkSeccompBpfLoop (pc + 1) totalLen (curMem ||| bit) masks rest
      else
        false
    else if c == 0x0060 || c == 0x0061 then
      if insn.k.toNat < 16 then
        let bit := (1 : UInt32) <<< UInt32.ofNat insn.k.toNat
        (curMem &&& bit) != 0 && checkSeccompBpfLoop (pc + 1) totalLen curMem masks rest
      else
        false
    else if c == 0x0005 then
      let tgt := pc + 1 + insn.k.toNat
      if tgt < totalLen then
        let prev := (assocGet masks tgt).getD 0xFFFF
        checkSeccompBpfLoop (pc + 1) totalLen 0xFFFF (assocSet masks tgt (prev &&& curMem)) rest
      else
        false
    else if c == 0x0015 || c == 0x001d || c == 0x0025 || c == 0x002d ||
        c == 0x0035 || c == 0x003d || c == 0x0045 || c == 0x004d then
      let t1 := pc + 1 + insn.jt.toNat
      let t2 := pc + 1 + insn.jf.toNat
      if t1 < totalLen && t2 < totalLen then
        let m1 := assocSet masks t1 (((assocGet masks t1).getD 0xFFFF) &&& curMem)
        let m2 := assocSet m1 t2 (((assocGet m1 t2).getD 0xFFFF) &&& curMem)
        checkSeccompBpfLoop (pc + 1) totalLen 0xFFFF m2 rest
      else
        false
    else
      false

/-- Returns `true` iff `prog` is a valid non-empty (`<= 160` insns) Linux `seccomp` classic BPF filter ending in `BPF_RET`. -/
def checkSeccompBpf (prog : List SockFilterInsn) : Bool :=
  let n := prog.length
  if n == 0 || n > SECCOMP_MAX_FILTER_INSNS then
    false
  else
    match prog.getLast? with
    | none => false
    | some last =>
      (last.code == 0x0006 || last.code == 0x0016) &&
        checkSeccompBpfLoop 0 n 0 [] prog

/-- Returns `true` iff every return path in `prog` yields `SECCOMP_RET_ALLOW` or `SECCOMP_RET_LOG` (masking upper 16 action bits via `SECCOMP_RET_ACTION_FULL`). -/
def isAllowOnlySeccompFilter : List SockFilterInsn → Bool
  | [] => true
  | insn :: rest =>
    let safeInsn :=
      if insn.code == 0x0016 || insn.code == 0x003c then false
      else if insn.code == 0x0006 then
        let act := insn.k &&& SECCOMP_RET_ACTION_FULL
        act == SECCOMP_RET_ALLOW || act == SECCOMP_RET_LOG
      else true
    safeInsn && isAllowOnlySeccompFilter rest

/-- Known `LANDLOCK_ACCESS_FS_*` mask for a concrete Landlock ABI version `abi` (`>= 4`). -/
def landlockKnownFsMask (abi : UInt32) : UInt64 :=
  if abi ≤ 4 then ((1 : UInt64) <<< 15) - 1
  else if abi ≤ 8 then ((1 : UInt64) <<< 16) - 1
  else ((1 : UInt64) <<< 17) - 1

/-- Kernel descriptor flavor tracked in `SandboxSysState`. -/
inductive SandboxFdKind where
  /-- Open Landlock ruleset descriptor created with `(handledFs, handledNet)`. -/
  | landlockRuleset (handledFs : UInt64) (handledNet : UInt64)
  /-- Open `memfd_create` anonymous file descriptor (`shm_mnt`, rejected by `landlock_add_rule` / `landlock_restrict_self` with `EBADFD`). -/
  | memfd (allowSealing : Bool) (noexecSeal : Bool)
  /-- Pre-opened or externally supplied filesystem path descriptor (`isDir = true` for directory, `false` for non-directory). -/
  | hostPath (isDir : Bool)
  /-- Non-path pseudo-FS descriptor (`pipe`, `socket`, `eventfd`, `pidfd`, `nsfs`), rejected by Landlock with `EBADFD`. -/
  | pseudoFs
  deriving Repr, DecidableEq, BEq

/-- Tracked descriptor metadata in `SandboxSysState`. -/
structure SandboxFdDesc where
  /-- Kernel object flavor of the descriptor. -/
  kind : SandboxFdKind
  /-- Close-on-exec flag (`FD_CLOEXEC`). -/
  cloexec : Bool := true
  /-- `true` when opened with `O_PATH` (`FMODE_PATH`), returning `EBADF` as `ruleset` (`CLASS(fd)`) while accepted by `CLASS(fd_raw)` as `parentFd`. -/
  oPath : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Tracked soft limit and monotonic hard-limit ceiling for one `RlimitResource`. -/
structure RlimitState where
  /-- Current soft limit (`rlim_cur`). -/
  cur : UInt64 := RLIM_INFINITY
  /-- Monotonic upper bound on the current hard limit (`rlim_max`). -/
  hardUpper : UInt64 := RLIM_INFINITY
  /-- `true` once an exact `rlim_cur` has been established by a prior succeeding `setrlimit` call. -/
  curExact : Bool := false
  /-- `true` once an exact `rlim_max` has been established by a prior succeeding `setrlimit` call. -/
  hardExact : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Environment-free executable relational state for the 7-syscall `LeanSwe.LinuxSyscall.Sandbox` bundle. -/
structure SandboxSysState where
  /-- Live logical descriptor table. -/
  fds : List (HandleId × SandboxFdDesc) := []
  /-- Next fresh `HandleId` allocated by deterministic `modelOps`. -/
  nextHid : HandleId := 0
  /-- Lazily observed thread `no_new_privs` attribute (`none` until observed via `prctl` or privilege-gated calls; monotonic `false -> true`). -/
  noNewPrivs? : Option Bool := none
  /-- Process `child_subreaper` attribute (`PR_SET_CHILD_SUBREAPER`). -/
  childSubreaper : Bool := false
  /-- Current parent-death signal (`PR_SET_PDEATHSIG`, `0..64`). -/
  pdeathsig : UInt32 := 0
  /-- Lazily observed `ns_capable_noaudit(current_user_ns(), CAP_SYS_ADMIN)` (`none` until observed; `some true` inside `CLONE_NEWUSER`). -/
  hasCapSysAdmin? : Option Bool := none
  /-- Lazily observed `capable(CAP_SYS_RESOURCE)` in `init_user_ns` (`none` until observed via `setrlimit`). -/
  hasCapSysResource? : Option Bool := none
  /-- `true` once any Landlock syscall (including `ERRATA`) has succeeded or returned a Landlock-initialized error on the host. -/
  landlockEnabled : Bool := false
  /-- Implied minimum Landlock ABI version inferred from prior successful v5+/v9+ ruleset creation (`0` before any v5+ evidence). -/
  landlockMinAbi : UInt32 := 0
  /-- Implied upper bound on Landlock ABI inferred from `EINVAL` on unknown `LANDLOCK_ACCESS_FS_*` bits (`4` if `IOCTL_DEV` rejected, `8` if `RESOLVE_UNIX` rejected). -/
  landlockMaxAbi? : Option UInt32 := none
  /-- Observed `LANDLOCK_CREATE_RULESET_ERRATA` state (`none`: unobserved, `some none`: `EINVAL` unsupported, `some (some mask)`: supported errata bitmask). -/
  landlockErrata? : Option (Option UInt32) := none
  /-- Observed Landlock ABI version once queried (`none` before first `CREATE_RULESET_VERSION` query). -/
  landlockAbi? : Option UInt32 := none
  /-- Default Landlock ABI version used by deterministic `modelOps` when `landlockAbi? = none` (`9` on Linux `7.1.6`). -/
  defaultLandlockAbi : UInt32 := 9
  /-- `true` once a `no_new_privs || CAP_SYS_ADMIN` gate has succeeded while both `noNewPrivs?` and `hasCapSysAdmin?` were unknown. -/
  passedNnpGate : Bool := false
  /-- Lower bound on enacted Landlock domains stacked on the calling thread (`0..16`). -/
  landlockLayers : Nat := 0
  /-- `true` once the exact stacked Landlock domain count is known (`false` when unknown outer Landlock domains may pre-exist). -/
  landlockLayersExact : Bool := false
  /-- `true` once any `seccomp(2)` syscall has succeeded in the current trace. -/
  seccompEnabled : Bool := false
  /-- Count of installed `seccomp` BPF filters on the calling thread. -/
  seccompFilters : Nat := 0
  /-- `true` once a potentially non-`ALLOW`/`LOG` `seccomp` filter has been installed in the current trace. -/
  seccompMayIntercept : Bool := false
  /-- `true` once any `memfd_create(2)` syscall has succeeded or observed `vm.memfd_noexec == 2` (`EACCES`). -/
  memfdEnabled : Bool := false
  /-- Tracked `RLIMIT_CORE` soft/hard state. -/
  rlimitCore : RlimitState := { cur := 0, hardUpper := RLIM_INFINITY, curExact := false, hardExact := false }
  /-- Tracked `RLIMIT_FSIZE` soft/hard state. -/
  rlimitFsize : RlimitState := { cur := RLIM_INFINITY, hardUpper := RLIM_INFINITY, curExact := false, hardExact := false }
  /-- Tracked `RLIMIT_NOFILE` soft/hard state. -/
  rlimitNofile : RlimitState := { cur := 1024, hardUpper := NOFILE_KERNEL_MAX, curExact := false, hardExact := false }
  /-- Kernel-wide `sysctl_nr_open` ceiling (`<= NOFILE_KERNEL_MAX`) enforced on `RLIMIT_NOFILE` even when `hasCapSysResource? = some true`. -/
  nofileNrOpenCeil : UInt64 := NOFILE_KERNEL_MAX
  /-- Host `vm.memfd_noexec == 2` observation for `MFD_EXEC` (`some true` if `exec = true` returned `EACCES`, `some false` if `exec = true` succeeded). -/
  memfdNoexecStrict? : Option Bool := none
  deriving Repr, DecidableEq, BEq

/-- Environment-free initial `SandboxSysState` with zero silent ambient privilege, `no_new_privs`, or Landlock-layer assumptions. -/
def SandboxSysState.initial : SandboxSysState := {}

/-- Initial `SandboxSysState` for a known fresh unprivileged process (`no_new_privs = false`, `CAP_SYS_ADMIN = false`, `CAP_SYS_RESOURCE = false`, `0` pre-stacked Landlock layers). -/
def SandboxSysState.unprivileged : SandboxSysState :=
  { noNewPrivs? := some false
    hasCapSysAdmin? := some false
    hasCapSysResource? := some false
    landlockLayersExact := true }

/-- Initial or derived `SandboxSysState` for a process started beneath an inherited **safe** outer `seccomp` filter satisfying the same verdict safety envelope as `hasSafeSeccompRetBytes` (`ALLOW`, `LOG`, or `SECCOMP_RET_ERRNO | e` with `1 <= e <= 4095` and `e != EFAULT`). Filters returning `SECCOMP_RET_ERRNO | 0` (fake-success `rax = 0` spoofing that aliases FD `0`, analogous to `ptrace`/`TRACE`/`USER_NOTIF`) are outside the safe-filter boundary, while `SECCOMP_RET_ERRNO | EFAULT` (`14`) hits the fail-loud C-ABI `abort()` invariant (`fd_box.h`, `sandbox_shim.c`). -/
def SandboxSysState.withOuterSeccomp (s : SandboxSysState := SandboxSysState.initial) : SandboxSysState :=
  { s with seccompMayIntercept := true }

/-- Well-formedness invariant on `SandboxSysState` preserved by `allowedStep` and `modelOps`. -/
def SandboxSysState.wf (s : SandboxSysState) : Bool :=
  s.fds.all (fun p => decide (p.1 < s.nextHid)) &&
    !(s.passedNnpGate && s.noNewPrivs? == some false && s.hasCapSysAdmin? == some false) &&
    (match s.landlockMaxAbi? with
     | none => true
     | some m => decide (4 ≤ m && s.landlockMinAbi ≤ m)) &&
    match s.landlockAbi? with
    | none => true
    | some v => decide (v ≥ 4 && v ≥ s.landlockMinAbi &&
        match s.landlockMaxAbi? with
        | none => true
        | some m => v ≤ m)

/-- Register a pre-existing host filesystem descriptor (`isDir = true` for directory, `false` for regular file, `oPath = true` when opened with `O_PATH`) at `hid` in `s`. -/
def SandboxSysState.withHostFd (s : SandboxSysState) (hid : HandleId) (isDir : Bool)
    (oPath : Bool := false) : SandboxSysState :=
  { s with
    fds := assocSet s.fds hid { kind := .hostPath isDir, cloexec := true, oPath := oPath }
    nextHid := Nat.max s.nextHid (hid + 1) }

/-- Register a pre-existing non-path pseudo-FS descriptor (`pipe`, `socket`, `eventfd`, `pidfd`, `nsfs`, `oPath = true` when re-opened with `O_PATH`) at `hid` in `s`. -/
def SandboxSysState.withPseudoFd (s : SandboxSysState) (hid : HandleId)
    (oPath : Bool := false) : SandboxSysState :=
  { s with
    fds := assocSet s.fds hid { kind := .pseudoFs, cloexec := true, oPath := oPath }
    nextHid := Nat.max s.nextHid (hid + 1) }

/-- Returns `true` iff `s` is consistent with failing the `no_new_privs || CAP_SYS_ADMIN` gate (`EPERM` / `EACCES`). -/
def canFailNnpGate (s : SandboxSysState) : Bool :=
  !s.passedNnpGate && s.noNewPrivs? != some true && s.hasCapSysAdmin? != some true

/-- Returns `true` iff `s` is consistent with passing the `no_new_privs || CAP_SYS_ADMIN` gate. -/
def canPassNnpGate (s : SandboxSysState) : Bool :=
  !(s.noNewPrivs? == some false && s.hasCapSysAdmin? == some false)

/-- Pin both `noNewPrivs? := some false` and `hasCapSysAdmin? := some false` when a `no_new_privs || CAP_SYS_ADMIN` gate fails. -/
def pinFailedNnpGate (s : SandboxSysState) : SandboxSysState :=
  { s with noNewPrivs? := some false, hasCapSysAdmin? := some false }

/-- Refine `(noNewPrivs?, hasCapSysAdmin?, passedNnpGate)` when a `no_new_privs || CAP_SYS_ADMIN` gate succeeds. -/
def pinPassedNnpGate (s : SandboxSysState) : SandboxSysState :=
  if s.noNewPrivs? == some true || s.hasCapSysAdmin? == some true then
    s
  else if s.noNewPrivs? == some false then
    { s with hasCapSysAdmin? := some true }
  else if s.hasCapSysAdmin? == some false then
    { s with noNewPrivs? := some true }
  else
    { s with passedNnpGate := true }

/-- Read the tracked `RlimitState` for `res` from `s`. -/
def SandboxSysState.getRlimit (s : SandboxSysState) : RlimitResource → RlimitState
  | .core => s.rlimitCore
  | .fsize => s.rlimitFsize
  | .nofile => s.rlimitNofile

/-- Update the tracked `RlimitState` for `res` in `s`. -/
def SandboxSysState.setRlimit (s : SandboxSysState) (res : RlimitResource) (st : RlimitState) : SandboxSysState :=
  match res with
  | .core => { s with rlimitCore := st }
  | .fsize => { s with rlimitFsize := st }
  | .nofile => { s with rlimitNofile := st }

/-- Returns `true` iff any prior step in `s` has already confirmed that Landlock is initialized and enabled in the kernel. -/
def hasLandlockEvidence (s : SandboxSysState) : Bool :=
  s.landlockEnabled || s.landlockAbi?.isSome || s.landlockErrata?.isSome ||
    s.landlockMaxAbi?.isSome || s.landlockLayers > 0 ||
    s.fds.any (fun (_, d) => match d.kind with | .landlockRuleset _ _ => true | _ => false)

/-- Returns `true` iff any prior step in `s` has already confirmed that `seccomp(2)` is enabled in the kernel. -/
def hasSeccompEvidence (s : SandboxSysState) : Bool :=
  s.seccompEnabled || s.seccompFilters > 0

/-- Returns `true` iff any prior step in `s` has already confirmed that `memfd_create(2)` is enabled in the kernel. -/
def hasMemfdEvidence (s : SandboxSysState) : Bool :=
  s.memfdEnabled || s.memfdNoexecStrict?.isSome ||
    s.fds.any (fun (_, d) => match d.kind with | .memfd _ _ => true | _ => false)

/-- Minimum Landlock ABI version required by `fsMask`. -/
def impliedLandlockAbi (fsMask : UInt64) : UInt32 :=
  if (fsMask &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) != 0 then 9
  else if (fsMask &&& LANDLOCK_ACCESS_FS_IOCTL_DEV) != 0 then 5
  else 4

/-- Maximum Landlock ABI upper bound implied when `landlock_create_ruleset` rejects `fsMask` with `EINVAL`. -/
def impliedMaxLandlockAbiOnEinval (fsMask : UInt64) : Option UInt32 :=
  if (fsMask &&& ~~~landlockKnownFsMask 8) == 0 then some 4
  else if (fsMask &&& ~~~landlockKnownFsMask 9) == 0 then some 8
  else none

/-- Maximum of two `UInt32` values (kernel-reducible). -/
def maxU32 (a b : UInt32) : UInt32 :=
  if a < b then b else a

/-- Minimum of two `UInt32` values (kernel-reducible). -/
def minU32 (a b : UInt32) : UInt32 :=
  if a < b then a else b

/-- Tighten an optional `UInt32` upper bound with `bound`. -/
def tightenMaxAbi (cur? : Option UInt32) (bound : UInt32) : Option UInt32 :=
  match cur? with
  | none => some bound
  | some m => some (minU32 m bound)

/-- Effective Landlock ABI version used by deterministic `modelOps` (`>= 4` whenever `hasLandlockEvidence s` holds, bounded by `landlockMinAbi` and `landlockMaxAbi?`). -/
def effectiveModelLandlockAbi (s : SandboxSysState) : UInt32 :=
  match s.landlockAbi? with
  | some abi => abi
  | none =>
    let base := if s.defaultLandlockAbi < 4 && hasLandlockEvidence s then 4 else s.defaultLandlockAbi
    let capped := match s.landlockMaxAbi? with
      | none => base
      | some m => minU32 base m
    maxU32 capped s.landlockMinAbi

/-- Invoke `ops.landlockRestrictSelf rs` `n` consecutive times in `StateM S`, stopping early on the first `.error`. -/
def repeatRestrictSelf {S fd : Type} (ops : SandboxOpsM (StateM S) fd) (rs : fd) :
    Nat → S → Except Errno Unit × S
  | 0, s => (.ok (), s)
  | k + 1, s =>
    let (r, s') := (ops.landlockRestrictSelf rs).run s
    match r with
    | .error e => (.error e, s')
    | .ok () => repeatRestrictSelf ops rs k s'

/-- Execute one `SandboxReq` against a `SandboxOpsM m HandleId` implementation and normalize its output to `SandboxOutcome`. -/
def execSandboxReq {m : Type → Type} [Monad m]
    (ops : SandboxOpsM m HandleId) (req : SandboxReq) : m SandboxOutcome :=
  match req with
  | .landlockCreateRuleset attr? flags => do
    match ← ops.landlockCreateRuleset attr? flags with
    | .ok (.version v) => return .landlockVersion v
    | .ok (.ruleset hid) => return .opened hid
    | .error e => return .err e
  | .landlockAddRule ruleset rule => do
    match ← ops.landlockAddRule ruleset rule with
    | .ok () => return .unit
    | .error e => return .err e
  | .landlockRestrictSelf ruleset => do
    match ← ops.landlockRestrictSelf ruleset with
    | .ok () => return .unit
    | .error e => return .err e
  | .seccomp op flags filterBytes => do
    match ← ops.seccomp op flags filterBytes with
    | .ok v => return .u32 v
    | .error e => return .err e
  | .prctl op => do
    match ← ops.prctl op with
    | .ok v => return .u32 v
    | .error e => return .err e
  | .setrlimit res cur max => do
    match ← ops.setrlimit res cur max with
    | .ok () => return .unit
    | .error e => return .err e
  | .memfdCreate name flags => do
    match ← ops.memfdCreate name flags with
    | .ok hid => return .opened hid
    | .error e => return .err e

/-- Returns `true` iff `req` fails a pure-Lean `mkSandboxOps` pre-check before reaching the OS syscall boundary. -/
def failsPureWrapperGuard : SandboxReq → Bool
  | .landlockCreateRuleset none flags => flags == 0
  | .landlockCreateRuleset (some _) flags => flags != 0
  | .seccomp (.getActionAvail _) flags _ => flags.toBits != 0
  | .seccomp .setModeFilter _ filterBytes =>
    !isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes
  | .memfdCreate name _ => hasEmbeddedNul name || name.data.size > MFD_NAME_MAX
  | _ => false

/-- Returns `true` iff `e` is `EINTR` or a curated catastrophic host fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isNonFdTransientErrno (e : Errno) : Bool :=
  e == Errno.EINTR || Errno.isCriticalOsErrno e

/-- Returns `true` iff `e` is `EINTR`, a curated catastrophic host fault (`ENOMEM`, `EIO`, `ENFILE`), or a visible resource limit (`EMFILE`, `ENOSPC`) on FD-allocating syscalls. -/
def isFdAllocTransientErrno (e : Errno) : Bool :=
  e == Errno.EINTR || Errno.isCriticalOsErrno e || Errno.isResourceLimitErrno e

/-- Core relational transition checker prior to optional `seccomp` filter interception. -/
def allowedStepCore (s : SandboxSysState) (req : SandboxReq) (out : SandboxOutcome) : Option SandboxSysState :=
  match out with
  | .err e =>
    if e == Errno.EFAULT then none
    else
      match req with
      | .landlockCreateRuleset none flags =>
        if flags == 0 then
          if e == Errno.EINVAL then some s else none
        else
          let canDisable := (e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s
          if flags == LANDLOCK_CREATE_RULESET_VERSION then
            if canDisable || isNonFdTransientErrno e then some s else none
          else if flags == LANDLOCK_CREATE_RULESET_ERRATA then
            let errataEinvalOk := match s.landlockErrata? with
              | some (some _) => false
              | _ => true
            if canDisable || isNonFdTransientErrno e then
              some s
            else if e == Errno.EINVAL && errataEinvalOk then
              some { s with landlockEnabled := true, landlockErrata? := some none }
            else
              none
          else
            if canDisable || isNonFdTransientErrno e then some s
            else if e == Errno.EINVAL then some { s with landlockEnabled := true }
            else none
      | .landlockCreateRuleset (some attr) flags =>
        if flags != 0 then
          if e == Errno.EINVAL then some s else none
        else
          let canDisable := (e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s
          if canDisable then
            some s
          else if attr.handledAccessFs == 0 && attr.handledAccessNet == 0 then
            if e == ENOMSG then some { s with landlockEnabled := true }
            else if isNonFdTransientErrno e then some s
            else none
          else if (attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0 then
            if e == Errno.EINVAL then some { s with landlockEnabled := true }
            else if isNonFdTransientErrno e then some s
            else none
          else
            match s.landlockAbi? with
            | some abi =>
              if (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0 then
                if e == Errno.EINVAL then some { s with landlockEnabled := true }
                else if isNonFdTransientErrno e then some s
                else none
              else
                if isFdAllocTransientErrno e then some s else none
            | none =>
              let knownMask := landlockKnownFsMask (maxU32 4 s.landlockMinAbi)
              if (attr.handledAccessFs &&& ~~~knownMask) != 0 then
                if e == Errno.EINVAL then
                  let nextMax := match impliedMaxLandlockAbiOnEinval attr.handledAccessFs with
                    | none => s.landlockMaxAbi?
                    | some b => tightenMaxAbi s.landlockMaxAbi? b
                  some { s with landlockEnabled := true, landlockMaxAbi? := nextMax }
                else if isFdAllocTransientErrno e then some s
                else none
              else
                if isFdAllocTransientErrno e then some s else none
      | .landlockAddRule ruleset rule =>
        let canDisable := (e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s
        if canDisable then
          some s
        else
          match assocGet s.fds ruleset with
          | none =>
            if e == Errno.EBADF then some { s with landlockEnabled := true }
            else if isNonFdTransientErrno e then some s
            else none
          | some rsDesc =>
            if rsDesc.oPath then
              if e == Errno.EBADF then some { s with landlockEnabled := true }
              else if isNonFdTransientErrno e then some s
              else none
            else
              match rsDesc.kind with
              | .memfd _ _ | .hostPath _ | .pseudoFs =>
                if e == EBADFD then some { s with landlockEnabled := true }
                else if isNonFdTransientErrno e then some s
                else none
              | .landlockRuleset handledFs handledNet =>
                match rule with
                | .pathBeneath parentHid allowedAccess =>
                  if allowedAccess == 0 then
                    if e == ENOMSG then some { s with landlockEnabled := true }
                    else if isNonFdTransientErrno e then some s
                    else none
                  else if (allowedAccess &&& ~~~handledFs) != 0 then
                    if e == Errno.EINVAL then some { s with landlockEnabled := true }
                    else if isNonFdTransientErrno e then some s
                    else none
                  else
                    match assocGet s.fds parentHid with
                    | none =>
                      if e == Errno.EBADF then some { s with landlockEnabled := true }
                      else if isNonFdTransientErrno e then some s
                      else none
                    | some pDesc =>
                      match pDesc.kind with
                      | .landlockRuleset _ _ | .memfd _ _ | .pseudoFs =>
                        if e == EBADFD then some { s with landlockEnabled := true }
                        else if isNonFdTransientErrno e then some s
                        else none
                      | .hostPath isDir =>
                        if !isDir && (allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0 then
                          if e == Errno.EINVAL then some { s with landlockEnabled := true }
                          else if isNonFdTransientErrno e then some s
                          else none
                        else
                          if isNonFdTransientErrno e then some s else none
                | .netPort port allowedAccess =>
                  if allowedAccess == 0 then
                    if e == ENOMSG then some { s with landlockEnabled := true }
                    else if isNonFdTransientErrno e then some s
                    else none
                  else if (allowedAccess &&& ~~~handledNet) != 0 || port > 65535 then
                    if e == Errno.EINVAL then some { s with landlockEnabled := true }
                    else if isNonFdTransientErrno e then some s
                    else none
                  else
                    if isNonFdTransientErrno e then some s else none
      | .landlockRestrictSelf ruleset =>
        let canDisable := (e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s
        if canDisable then
          some s
        else if e == Errno.EPERM && canFailNnpGate s then
          some { pinFailedNnpGate s with landlockEnabled := true }
        else if canPassNnpGate s then
          let sPass := { pinPassedNnpGate s with landlockEnabled := true }
          match assocGet s.fds ruleset with
          | none =>
            if e == Errno.EBADF then some sPass
            else if isNonFdTransientErrno e then some s
            else none
          | some desc =>
            if desc.oPath then
              if e == Errno.EBADF then some sPass
              else if isNonFdTransientErrno e then some s
              else none
            else
              match desc.kind with
              | .memfd _ _ | .hostPath _ | .pseudoFs =>
                if e == EBADFD then some sPass
                else if isNonFdTransientErrno e then some s
                else none
              | .landlockRuleset _ _ =>
                if e == Errno.E2BIG && (s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS || !s.landlockLayersExact) then
                  some { sPass with
                    landlockLayers := LANDLOCK_MAX_STACKED_LAYERS
                    landlockLayersExact := true }
                else if isNonFdTransientErrno e then
                  some s
                else
                  none
        else
          if isNonFdTransientErrno e then some s else none
      | .seccomp (.getActionAvail action) flags _ =>
        if flags.toBits != 0 then
          if e == Errno.EINVAL then some s else none
        else
          let canDisable := e == Errno.ENOSYS && !hasSeccompEvidence s
          if isKnownSeccompAction action then
            if canDisable || isNonFdTransientErrno e then some s else none
          else
            if e == Errno.EOPNOTSUPP then some { s with seccompEnabled := true }
            else if canDisable || isNonFdTransientErrno e then some s
            else none
      | .seccomp .setModeFilter flags filterBytes =>
        if !isValidSeccompFilterByteLen filterBytes.data.size ||
            !hasSafeSeccompRetBytes filterBytes then
          if e == Errno.EINVAL then some s else none
        else
          let canDisable := e == Errno.ENOSYS && !hasSeccompEvidence s
          if flags.waitKillableRecv then
            if e == Errno.EINVAL then some { s with seccompEnabled := true }
            else if canDisable || isNonFdTransientErrno e then some s
            else none
          else if canDisable then
            some s
          else if e == Errno.EACCES && canFailNnpGate s then
            some { pinFailedNnpGate s with seccompEnabled := true }
          else if canPassNnpGate s then
            let sPass := { pinPassedNnpGate s with seccompEnabled := true }
            match decodeSockFilters filterBytes with
            | none =>
              if e == Errno.EINVAL then some sPass
              else if isNonFdTransientErrno e then some s
              else none
            | some prog =>
              if !checkSeccompBpf prog then
                if e == Errno.EINVAL then some sPass
                else if isNonFdTransientErrno e then some s
                else none
              else
                let tsyncEsrchOk := flags.tsync && flags.tsyncEsrch && e == Errno.ESRCH
                if tsyncEsrchOk then some sPass
                else if isNonFdTransientErrno e then some s
                else none
          else
            if isNonFdTransientErrno e then some s else none
      | .prctl (.setPdeathsig sig) =>
        if sig > MAX_LINUX_SIGNAL then
          if e == Errno.EINVAL || isNonFdTransientErrno e then some s else none
        else
          if isNonFdTransientErrno e then some s else none
      | .prctl _ =>
        if isNonFdTransientErrno e then some s else none
      | .setrlimit res cur max =>
        if cur > max then
          if e == Errno.EINVAL || isNonFdTransientErrno e then some s else none
        else if res == .nofile && max > s.nofileNrOpenCeil then
          if e == Errno.EPERM || isNonFdTransientErrno e then some s else none
        else
          let st := s.getRlimit res
          if e == Errno.EPERM then
            if res != .nofile then
              if s.hasCapSysResource? != some true && (max > st.hardUpper || (!st.hardExact && max > 0)) then
                let s' := { s with hasCapSysResource? := some false }
                let tightened := if st.hardUpper ≤ max - 1 then st.hardUpper else max - 1
                some (s'.setRlimit res { st with hardUpper := tightened })
              else
                none
            else if s.hasCapSysResource? == some false then
              if max > st.hardUpper || (!st.hardExact && max > 0) then
                let tightened := if st.hardUpper ≤ max - 1 then st.hardUpper else max - 1
                some (s.setRlimit .nofile { st with hardUpper := tightened })
              else
                none
            else if max > st.hardUpper || (!st.hardExact && max > 0) then
              let nextCeil := if s.nofileNrOpenCeil ≤ max - 1 then s.nofileNrOpenCeil else max - 1
              some { s with nofileNrOpenCeil := nextCeil }
            else
              none
          else if isNonFdTransientErrno e then
            some s
          else
            none
      | .memfdCreate name flags =>
        if hasEmbeddedNul name || name.data.size > MFD_NAME_MAX then
          if e == Errno.EINVAL then some s else none
        else if flags.noexecSeal && flags.exec then
          if e == Errno.EINVAL then some { s with memfdEnabled := true }
          else if isNonFdTransientErrno e || (e == Errno.ENOSYS && !hasMemfdEvidence s) then some s
          else none
        else if flags.exec && e == Errno.EACCES && s.memfdNoexecStrict? != some false then
          some { s with memfdEnabled := true, memfdNoexecStrict? := some true }
        else if isFdAllocTransientErrno e || (e == Errno.ENOSYS && !hasMemfdEvidence s) then
          some s
        else
          none
  | .landlockVersion v =>
    match req with
    | .landlockCreateRuleset none flags =>
      if flags == LANDLOCK_CREATE_RULESET_VERSION then
        if v < 4 then none
        else
          match s.landlockAbi? with
          | none =>
            let maxOk := match s.landlockMaxAbi? with
              | none => true
              | some m => v ≤ m
            if v < s.landlockMinAbi || !maxOk then none
            else some { s with landlockEnabled := true, landlockAbi? := some v }
          | some prev =>
            if v == prev then some { s with landlockEnabled := true, landlockAbi? := some v }
            else none
      else if flags == LANDLOCK_CREATE_RULESET_ERRATA then
        match s.landlockErrata? with
        | none =>
          some { s with landlockEnabled := true, landlockErrata? := some (some v) }
        | some (some prev) =>
          if v == prev then some { s with landlockEnabled := true }
          else none
        | some none =>
          none
      else
        none
    | _ => none
  | .opened hid =>
    if (assocGet s.fds hid).isSome ||
        (s.rlimitNofile.curExact && s.rlimitNofile.cur == 0) then
      none
    else
      match req with
      | .landlockCreateRuleset (some attr) flags =>
        if flags != 0 then none
        else if attr.handledAccessFs == 0 && attr.handledAccessNet == 0 then none
        else if (attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0 then none
        else
          let fsOk := match s.landlockAbi? with
            | some abi => (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) == 0
            | none => (attr.handledAccessFs &&& ~~~landlockKnownFsMask 9) == 0
          let impMin := impliedLandlockAbi attr.handledAccessFs
          let abiCeilingOk := match s.landlockMaxAbi? with
            | none => true
            | some m => impMin ≤ m
          if !fsOk || !abiCeilingOk then none
          else
            some { s with
              fds := assocSet s.fds hid
                { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true }
              nextHid := Nat.max s.nextHid (hid + 1)
              landlockEnabled := true
              landlockMinAbi := maxU32 s.landlockMinAbi impMin }
      | .memfdCreate name flags =>
        if hasEmbeddedNul name || name.data.size > MFD_NAME_MAX then none
        else if flags.noexecSeal && flags.exec then none
        else if flags.exec && s.memfdNoexecStrict? == some true then none
        else
          let strict' := if flags.exec then some false else s.memfdNoexecStrict?
          some { s with
            fds := assocSet s.fds hid
              { kind := .memfd flags.allowSealing flags.noexecSeal, cloexec := flags.cloexec }
            nextHid := Nat.max s.nextHid (hid + 1)
            memfdEnabled := true
            memfdNoexecStrict? := strict' }
      | _ => none
  | .unit =>
    match req with
    | .landlockAddRule ruleset rule =>
      match assocGet s.fds ruleset with
      | none => none
      | some rsDesc =>
        if rsDesc.oPath then none
        else
          match rsDesc.kind with
          | .landlockRuleset handledFs handledNet =>
            match rule with
            | .pathBeneath parentHid allowedAccess =>
              if allowedAccess == 0 || (allowedAccess &&& ~~~handledFs) != 0 then none
              else
                match assocGet s.fds parentHid with
                | some { kind := .hostPath isDir, .. } =>
                  if !isDir && (allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0 then none
                  else some { s with landlockEnabled := true }
                | _ => none
            | .netPort port allowedAccess =>
              if allowedAccess == 0 || (allowedAccess &&& ~~~handledNet) != 0 || port > 65535 then none
              else some { s with landlockEnabled := true }
          | _ => none
    | .landlockRestrictSelf ruleset =>
      if !canPassNnpGate s then none
      else if s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS then none
      else
        let sPass := pinPassedNnpGate s
        match assocGet s.fds ruleset with
        | some { kind := .landlockRuleset _ _, oPath := false, .. } =>
          some { sPass with landlockEnabled := true, landlockLayers := s.landlockLayers + 1 }
        | _ => none
    | .setrlimit res cur max =>
      if cur > max then none
      else if res == .nofile && max > s.nofileNrOpenCeil then none
      else
        let st := s.getRlimit res
        if max > st.hardUpper && s.hasCapSysResource? == some false then none
        else
          let capR' := if max > st.hardUpper then some true else s.hasCapSysResource?
          let s' := { s with hasCapSysResource? := capR' }
          some (s'.setRlimit res { cur := cur, hardUpper := max, curExact := true, hardExact := true })
    | _ => none
  | .u32 val =>
    match req with
    | .seccomp (.getActionAvail action) flags _ =>
      if flags.toBits == 0 && isKnownSeccompAction action && val == 0 then
        some { s with seccompEnabled := true }
      else none
    | .seccomp .setModeFilter flags filterBytes =>
      if !isValidSeccompFilterByteLen filterBytes.data.size ||
          !hasSafeSeccompRetBytes filterBytes || flags.waitKillableRecv then
        none
      else if !canPassNnpGate s then none
      else
        let sPass := pinPassedNnpGate s
        match decodeSockFilters filterBytes with
        | none => none
        | some prog =>
          if !checkSeccompBpf prog then none
          else if val == 0 then
            let mayIntercept' := s.seccompMayIntercept || !isAllowOnlySeccompFilter prog
            some { sPass with
              seccompEnabled := true
              seccompFilters := s.seccompFilters + 1
              seccompMayIntercept := mayIntercept' }
          else if flags.tsync && !flags.tsyncEsrch then
            some { sPass with seccompEnabled := true }
          else
            none
    | .prctl .setNoNewPrivs =>
      if val == 0 then some { s with noNewPrivs? := some true } else none
    | .prctl .getNoNewPrivs =>
      if val == 0 && s.noNewPrivs? != some true && !(s.passedNnpGate && s.hasCapSysAdmin? == some false) then
        some { s with
          noNewPrivs? := some false
          hasCapSysAdmin? := if s.passedNnpGate then some true else s.hasCapSysAdmin? }
      else if val == 1 && s.noNewPrivs? != some false then
        some { s with noNewPrivs? := some true }
      else
        none
    | .prctl (.setChildSubreaper enable) =>
      if val == 0 then some { s with childSubreaper := enable } else none
    | .prctl (.setPdeathsig sig) =>
      if sig ≤ MAX_LINUX_SIGNAL && val == 0 then some { s with pdeathsig := sig } else none
    | _ => none

/-- Relational step verifier for `LeanSwe.LinuxSyscall.Sandbox` (`some s'` iff `out` is a legal Linux kernel transition from `s` on `req`). When `seccompMayIntercept = true` and `req` passes pure-Lean wrapper guards (`failsPureWrapperGuard req = false`), Linux evaluates installed `seccomp` BPF filters at syscall entry *before* kernel argument validation, so any intercepted errno `1 <= e <= 4095` (`e != EFAULT`, as `EFAULT` intentionally triggers fail-loud `abort()` in `sandbox_shim.c`) is permitted without pinning `s`. -/
def allowedStep (s : SandboxSysState) (req : SandboxReq) (out : SandboxOutcome) : Option SandboxSysState :=
  if !failsPureWrapperGuard req && s.seccompMayIntercept then
    match out with
    | .err e =>
      if e != Errno.EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095 then some s else none
    | _ => allowedStepCore s req out
  else
    allowedStepCore s req out

/-- Deterministic reference `SandboxOpsM (StateM SandboxSysState) HandleId` world model consistent with `allowedStep` on Linux `7.1.6`. -/
def modelOps : SandboxOpsM (StateM SandboxSysState) HandleId :=
  { landlockCreateRuleset := fun attr? flags => do
      let s ← get
      let abi := effectiveModelLandlockAbi s
      match attr? with
      | none =>
        if flags == 0 then
          return .error Errno.EINVAL
        if abi < 4 then
          return .error Errno.ENOSYS
        if flags == LANDLOCK_CREATE_RULESET_VERSION then
          set { s with landlockEnabled := true, landlockAbi? := some abi }
          return .ok (.version abi)
        if flags == LANDLOCK_CREATE_RULESET_ERRATA then
          match s.landlockErrata? with
          | some none =>
            if !s.seccompMayIntercept then
              set { s with landlockEnabled := true }
            return .error Errno.EINVAL
          | some (some mask) =>
            set { s with landlockEnabled := true }
            return .ok (.version mask)
          | none =>
            set { s with landlockEnabled := true, landlockErrata? := some (some 0) }
            return .ok (.version 0)
        if !s.seccompMayIntercept then
          set { s with landlockEnabled := true }
        return .error Errno.EINVAL
      | some attr =>
        if flags != 0 then
          return .error Errno.EINVAL
        if abi < 4 then
          return .error Errno.ENOSYS
        if attr.handledAccessFs == 0 && attr.handledAccessNet == 0 then
          if !s.seccompMayIntercept then
            set { s with landlockEnabled := true }
          return .error ENOMSG
        if (attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0 then
          if !s.seccompMayIntercept then
            set { s with landlockEnabled := true }
          return .error Errno.EINVAL
        if (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0 then
          if !s.seccompMayIntercept then
            let nextMax := match s.landlockAbi? with
              | some _ => s.landlockMaxAbi?
              | none =>
                match impliedMaxLandlockAbiOnEinval attr.handledAccessFs with
                | none => s.landlockMaxAbi?
                | some b => tightenMaxAbi s.landlockMaxAbi? b
            set { s with landlockEnabled := true, landlockMaxAbi? := nextMax }
          return .error Errno.EINVAL
        if s.rlimitNofile.curExact && s.fds.length ≥ s.rlimitNofile.cur.toNat then
          return .error Errno.EMFILE
        let hid := s.nextHid
        set { s with
          fds := assocSet s.fds hid
            { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true }
          nextHid := Nat.max s.nextHid (hid + 1)
          landlockEnabled := true
          landlockMinAbi := maxU32 s.landlockMinAbi (impliedLandlockAbi attr.handledAccessFs) }
        return .ok (.ruleset hid)
    landlockAddRule := fun ruleset rule => do
      let s ← get
      if effectiveModelLandlockAbi s < 4 then
        return .error Errno.ENOSYS
      match assocGet s.fds ruleset with
      | none =>
        if !s.seccompMayIntercept then set { s with landlockEnabled := true }
        return .error Errno.EBADF
      | some rsDesc =>
        if rsDesc.oPath then
          if !s.seccompMayIntercept then set { s with landlockEnabled := true }
          return .error Errno.EBADF
        match rsDesc.kind with
        | .memfd _ _ | .hostPath _ | .pseudoFs =>
          if !s.seccompMayIntercept then set { s with landlockEnabled := true }
          return .error EBADFD
        | .landlockRuleset handledFs handledNet =>
          match rule with
          | .pathBeneath parentHid allowedAccess =>
            if allowedAccess == 0 then
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error ENOMSG
            if (allowedAccess &&& ~~~handledFs) != 0 then
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error Errno.EINVAL
            match assocGet s.fds parentHid with
            | none =>
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error Errno.EBADF
            | some pDesc =>
              match pDesc.kind with
              | .landlockRuleset _ _ | .memfd _ _ | .pseudoFs =>
                if !s.seccompMayIntercept then set { s with landlockEnabled := true }
                return .error EBADFD
              | .hostPath isDir =>
                if !isDir && (allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0 then
                  if !s.seccompMayIntercept then set { s with landlockEnabled := true }
                  return .error Errno.EINVAL
                set { s with landlockEnabled := true }
                return .ok ()
          | .netPort port allowedAccess =>
            if allowedAccess == 0 then
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error ENOMSG
            if (allowedAccess &&& ~~~handledNet) != 0 then
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error Errno.EINVAL
            if port > 65535 then
              if !s.seccompMayIntercept then set { s with landlockEnabled := true }
              return .error Errno.EINVAL
            set { s with landlockEnabled := true }
            return .ok ()
    landlockRestrictSelf := fun ruleset => do
      let s ← get
      if effectiveModelLandlockAbi s < 4 then
        return .error Errno.ENOSYS
      let nnp := s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)
      let capA := s.hasCapSysAdmin?.getD (s.passedNnpGate && !nnp)
      if !nnp && !capA then
        if !s.seccompMayIntercept then set { pinFailedNnpGate s with landlockEnabled := true }
        return .error Errno.EPERM
      let sPass := { pinPassedNnpGate s with landlockEnabled := true }
      match assocGet s.fds ruleset with
      | none =>
        if !s.seccompMayIntercept then set sPass
        return .error Errno.EBADF
      | some desc =>
        if desc.oPath then
          if !s.seccompMayIntercept then set sPass
          return .error Errno.EBADF
        match desc.kind with
        | .memfd _ _ | .hostPath _ | .pseudoFs =>
          if !s.seccompMayIntercept then set sPass
          return .error EBADFD
        | .landlockRuleset _ _ =>
          if s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS then
            if !s.seccompMayIntercept then
              set { sPass with
                landlockLayers := LANDLOCK_MAX_STACKED_LAYERS
                landlockLayersExact := true }
            return .error Errno.E2BIG
          set { sPass with landlockLayers := s.landlockLayers + 1 }
          return .ok ()
    seccomp := fun op flags filterBytes => do
      let s ← get
      match op with
      | .getActionAvail action =>
        if flags.toBits != 0 then return .error Errno.EINVAL
        if isKnownSeccompAction action then
          set { s with seccompEnabled := true }
          return .ok 0
        else
          if !s.seccompMayIntercept then set { s with seccompEnabled := true }
          return .error Errno.EOPNOTSUPP
      | .setModeFilter =>
        if !isValidSeccompFilterByteLen filterBytes.data.size ||
            !hasSafeSeccompRetBytes filterBytes then
          return .error Errno.EINVAL
        if flags.waitKillableRecv then
          if !s.seccompMayIntercept then set { s with seccompEnabled := true }
          return .error Errno.EINVAL
        let nnp := s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)
        let capA := s.hasCapSysAdmin?.getD (s.passedNnpGate && !nnp)
        if !nnp && !capA then
          if !s.seccompMayIntercept then set { pinFailedNnpGate s with seccompEnabled := true }
          return .error Errno.EACCES
        let sPass := { pinPassedNnpGate s with seccompEnabled := true }
        match decodeSockFilters filterBytes with
        | none =>
          if !s.seccompMayIntercept then set sPass
          return .error Errno.EINVAL
        | some prog =>
          if !checkSeccompBpf prog then
            if !s.seccompMayIntercept then set sPass
            return .error Errno.EINVAL
          let mayIntercept' := s.seccompMayIntercept || !isAllowOnlySeccompFilter prog
          set { sPass with
            seccompFilters := s.seccompFilters + 1
            seccompMayIntercept := mayIntercept' }
          return .ok 0
    prctl := fun op => do
      let s ← get
      match op with
      | .setNoNewPrivs =>
        set { s with noNewPrivs? := some true }
        return .ok 0
      | .getNoNewPrivs =>
        let nnp := s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)
        let capA' := if !nnp && s.passedNnpGate then some true else s.hasCapSysAdmin?
        set { s with noNewPrivs? := some nnp, hasCapSysAdmin? := capA' }
        return .ok (if nnp then 1 else 0)
      | .setChildSubreaper enable =>
        set { s with childSubreaper := enable }
        return .ok 0
      | .setPdeathsig sig =>
        if sig > MAX_LINUX_SIGNAL then
          return .error Errno.EINVAL
        set { s with pdeathsig := sig }
        return .ok 0
    setrlimit := fun res cur max => do
      let s ← get
      if cur > max then
        return .error Errno.EINVAL
      if res == .nofile && max > s.nofileNrOpenCeil then
        return .error Errno.EPERM
      let st := s.getRlimit res
      let capR := s.hasCapSysResource?.getD false
      if !capR && max > st.hardUpper then
        if !s.seccompMayIntercept then
          if res == .nofile && s.hasCapSysResource?.isNone then
            let nextCeil := if s.nofileNrOpenCeil ≤ max - 1 then s.nofileNrOpenCeil else max - 1
            set { s with nofileNrOpenCeil := nextCeil }
          else
            set { s with hasCapSysResource? := some false }
        return .error Errno.EPERM
      let capR' := if max > st.hardUpper then some true else s.hasCapSysResource?
      let s' := { s with hasCapSysResource? := capR' }
      set (s'.setRlimit res { cur := cur, hardUpper := max, curExact := true, hardExact := true })
      return .ok ()
    memfdCreate := fun name flags => do
      let s ← get
      if hasEmbeddedNul name || name.data.size > MFD_NAME_MAX then
        return .error Errno.EINVAL
      if flags.noexecSeal && flags.exec then
        if !s.seccompMayIntercept then set { s with memfdEnabled := true }
        return .error Errno.EINVAL
      if flags.exec && s.memfdNoexecStrict? == some true then
        if !s.seccompMayIntercept then set { s with memfdEnabled := true }
        return .error Errno.EACCES
      if s.rlimitNofile.curExact && s.fds.length ≥ s.rlimitNofile.cur.toNat then
        return .error Errno.EMFILE
      let hid := s.nextHid
      let strict' := if flags.exec then some false else s.memfdNoexecStrict?
      set { s with
        fds := assocSet s.fds hid
          { kind := .memfd flags.allowSealing flags.noexecSeal, cloexec := flags.cloexec }
        nextHid := Nat.max s.nextHid (hid + 1)
        memfdEnabled := true
        memfdNoexecStrict? := strict' }
      return .ok hid }

instance : Inhabited SandboxSysState := ⟨SandboxSysState.initial⟩

/-- Returns `true` iff `out` is a curated catastrophic OS fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isCriticalFault : SandboxOutcome → Bool
  | .err e => Errno.isCriticalOsErrno e
  | _ => false

/-- Returns `true` iff `out` is a transient signal interruption (`EINTR`). -/
def isEintrOutcome : SandboxOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy execution environment wrapping `SandboxSysState` with a finite `EINTR` interruption budget (`seccompMayIntercept = false`). -/
structure HealthyEnv where
  /-- Underlying `Sandbox` relational world state. -/
  state : SandboxSysState := SandboxSysState.initial
  /-- Remaining bound on `EINTR` signal interruptions. -/
  eintrBudget : Nat := 0
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Initial healthy `Sandbox` environment (`SandboxSysState.initial`, `seccompMayIntercept = false`, `eintrBudget`). -/
def HealthyEnv.initial (eintrBudget : Nat := 0) : HealthyEnv :=
  { state := SandboxSysState.initial, eintrBudget := eintrBudget }

/-- Returns `true` iff `env` has no intercepting `seccomp` filter (`seccompMayIntercept = false`) and `env.state` satisfies `SandboxSysState.wf`. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.seccompMayIntercept && env.state.wf

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Sandbox`, capturing all legitimate Linux transitions, capability/Landlock/rlimit nondeterminism, everyday errors (`EMFILE`, `ENOSPC` on FD-allocating syscalls, `EINVAL`, `EPERM`, `EACCES`, `EBADF`, `EBADFD`, `E2BIG`, `EOPNOTSUPP`, `ENOSYS`, bounded `EINTR`), while banning curated critical OS faults (`ENOMEM`, `EIO`, `ENFILE`) and ambient `seccomp` preemption. -/
def healthyStep (env : HealthyEnv) (req : SandboxReq) (out : SandboxOutcome) : Option HealthyEnv :=
  if !env.wf || isCriticalFault out then
    none
  else
    match allowedStep env.state req out with
    | none => none
    | some s' =>
      if isEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Reference `SandboxOpsM (StateM HealthyEnv) HandleId` lifting `modelOps` while preserving `eintrBudget`. -/
def healthyModelOps : SandboxOpsM (StateM HealthyEnv) HandleId :=
  { landlockCreateRuleset := fun attr? flags => do
      let env ← get
      let (res, s') := (modelOps.landlockCreateRuleset attr? flags).run env.state
      set { env with state := s' }
      return res
    landlockAddRule := fun ruleset rule => do
      let env ← get
      let (res, s') := (modelOps.landlockAddRule ruleset rule).run env.state
      set { env with state := s' }
      return res
    landlockRestrictSelf := fun ruleset => do
      let env ← get
      let (res, s') := (modelOps.landlockRestrictSelf ruleset).run env.state
      set { env with state := s' }
      return res
    seccomp := fun op flags filterBytes => do
      let env ← get
      let (res, s') := (modelOps.seccomp op flags filterBytes).run env.state
      set { env with state := s' }
      return res
    prctl := fun op => do
      let env ← get
      let (res, s') := (modelOps.prctl op).run env.state
      set { env with state := s' }
      return res
    setrlimit := fun res cur max => do
      let env ← get
      let (outRes, s') := (modelOps.setrlimit res cur max).run env.state
      set { env with state := s' }
      return outRes
    memfdCreate := fun name flags => do
      let env ← get
      let (res, s') := (modelOps.memfdCreate name flags).run env.state
      set { env with state := s' }
      return res }

/-- Returns `true` iff `(req, out)` is a successful (`val == 0`) `seccomp(SECCOMP_SET_MODE_FILTER)` transition installing a non-allow-only BPF filter (`seccompMayIntercept = true`). -/
def installsInterceptingSeccomp (req : SandboxReq) (out : SandboxOutcome) : Bool :=
  match req, out with
  | .seccomp .setModeFilter _ filterBytes, .u32 val =>
    val == 0 &&
      match decodeSockFilters filterBytes with
      | some prog => !isAllowOnlySeccompFilter prog
      | none => false
  | _, _ => false

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthySandboxAt {W : Type} (proj : W → HealthyEnv)
    (ops : SandboxOpsM (StateM W) HandleId) : Prop :=
  ∀ (w : W) (req : SandboxReq),
    (proj w).wf = true →
    let (out, w') := (execSandboxReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Direct healthy-world refinement predicate over `StateM HealthyEnv`. -/
abbrev RefinesHealthySandbox (ops : SandboxOpsM (StateM HealthyEnv) HandleId) : Prop :=
  RefinesHealthySandboxAt id ops

end LeanSwe.LinuxSyscall.Sandbox
