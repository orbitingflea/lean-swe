import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.LinuxSyscall.Sandbox.Model

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest ErrorObligation ErrorJustification ErrorTestMode AssumptionObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Sandbox` ABI constants (`ENOMSG = 42`, `EBADFD = 77`, `MFD_NAME_MAX = 249`, `SECCOMP_MAX_FILTER_INSNS = 160`, `LANDLOCK_MAX_STACKED_LAYERS = 16`, `MAX_LINUX_SIGNAL = 64`), `Errno.isTransientOsErrno` (`EFAULT` excluded), and `SandboxErrorKind.ofErrno` map every `e : Errno` to its exact bucket. -/
def test_sandbox_errno_classificationAndConstants
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → SandboxErrorKind := SandboxErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (ENOMSG = 42 ∧ EBADFD = 77 ∧ MFD_NAME_MAX = 249 ∧
    SECCOMP_MAX_FILTER_INSNS = 160 ∧ LANDLOCK_MAX_STACKED_LAYERS = 16 ∧ MAX_LINUX_SIGNAL = 64)
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  let expectedKind : SandboxErrorKind :=
    if e == Errno.EBADF || e == EBADFD then .badFd
    else if e == Errno.EINVAL || e == ENOMSG then .invalidArg
    else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
    else if e == Errno.E2BIG || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS ||
        e == Errno.ESRCH || e == Errno.EBUSY then .limitOrUnsupported
    else .transientOrResource
  NondetTest.assert (classify e = expectedKind)
  NondetTest.assert (classify Errno.EBADF = .badFd ∧ classify EBADFD = .badFd)
  NondetTest.assert (classify Errno.EINVAL = .invalidArg ∧ classify ENOMSG = .invalidArg)
  NondetTest.assert (classify Errno.EPERM = .permissionDenied ∧ classify Errno.EACCES = .permissionDenied)
  NondetTest.assert (classify Errno.E2BIG = .limitOrUnsupported ∧
    classify Errno.EOPNOTSUPP = .limitOrUnsupported ∧
    classify Errno.ENOSYS = .limitOrUnsupported ∧
    classify Errno.ESRCH = .limitOrUnsupported ∧
    classify Errno.EBUSY = .limitOrUnsupported)
  NondetTest.assert (classify Errno.EINTR = .transientOrResource ∧
    classify Errno.EIO = .transientOrResource ∧
    classify Errno.ENOMEM = .transientOrResource ∧
    classify Errno.ENFILE = .transientOrResource ∧
    classify Errno.EMFILE = .transientOrResource ∧
    classify Errno.ENOSPC = .transientOrResource)

/-- Portable symbolic flag encoders (`SeccompFlags.toBits`, `PrctlOp.toRaw`, `RlimitResource.toTag`, `MemfdFlags.toBits`) are injective with exact ABI bit/tag assignments, and `encodeSockFilters` / `decodeSockFilters` implements the exact 8-byte little-endian `struct sock_filter` wire layout while rejecting non-multiples of `8` with `none`. -/
def test_sandbox_flags_andBpfCodecInjective
    {runner} [NondetTest runner]
    (encSeccomp : SeccompFlags → UInt32 := SeccompFlags.toBits)
    (encPrctl : PrctlOp → UInt32 × UInt32 := PrctlOp.toRaw)
    (encRlimit : RlimitResource → UInt32 := RlimitResource.toTag)
    (encMemfd : MemfdFlags → UInt32 := MemfdFlags.toBits)
    (encBpf : List SockFilterInsn → ByteArray := encodeSockFilters)
    (decBpf : ByteArray → Option (List SockFilterInsn) := decodeSockFilters) : runner Unit := do
  let sf1 ← nondet SeccompFlags
  let sf2 ← nondet SeccompFlags
  NondetTest.assert ((encSeccomp sf1 == encSeccomp sf2) = (sf1 == sf2))
  NondetTest.assert (encSeccomp {} = 0 ∧ encSeccomp { tsync := true } = 1 ∧
    encSeccomp { log := true } = 2 ∧ encSeccomp { specAllow := true } = 4 ∧
    encSeccomp { tsyncEsrch := true } = 16 ∧ encSeccomp { waitKillableRecv := true } = 32)
  NondetTest.assert (encSeccomp sf1 =
    ((if sf1.tsync then (1 : UInt32) else 0) |||
     (if sf1.log then (2 : UInt32) else 0) |||
     (if sf1.specAllow then (4 : UInt32) else 0) |||
     (if sf1.tsyncEsrch then (16 : UInt32) else 0) |||
     (if sf1.waitKillableRecv then (32 : UInt32) else 0)))
  let p1 ← nondet PrctlOp
  let p2 ← nondet PrctlOp
  let sig ← nondet UInt32
  NondetTest.assert ((encPrctl p1 == encPrctl p2) = (p1 == p2))
  NondetTest.assert (encPrctl .setNoNewPrivs = (0, 1) ∧
    encPrctl .getNoNewPrivs = (1, 0) ∧
    encPrctl (.setChildSubreaper false) = (2, 0) ∧
    encPrctl (.setChildSubreaper true) = (2, 1) ∧
    encPrctl (.setPdeathsig sig) = (3, sig))
  let r1 ← nondet RlimitResource
  let r2 ← nondet RlimitResource
  NondetTest.assert ((encRlimit r1 == encRlimit r2) = (r1 == r2))
  NondetTest.assert (encRlimit .core = 0 ∧ encRlimit .fsize = 1 ∧ encRlimit .nofile = 2)
  let m1 ← nondet MemfdFlags
  let m2 ← nondet MemfdFlags
  NondetTest.assert ((encMemfd m1 == encMemfd m2) = (m1 == m2))
  NondetTest.assert (encMemfd { cloexec := false } = 0 ∧
    encMemfd { cloexec := true } = 1 ∧
    encMemfd { cloexec := false, allowSealing := true } = 2 ∧
    encMemfd { cloexec := false, noexecSeal := true } = 8 ∧
    encMemfd { cloexec := false, exec := true } = 16)
  NondetTest.assert (encMemfd m1 =
    ((if m1.cloexec then (1 : UInt32) else 0) |||
     (if m1.allowSealing then (2 : UInt32) else 0) |||
     (if m1.noexecSeal then (8 : UInt32) else 0) |||
     (if m1.exec then (16 : UInt32) else 0)))
  let insn ← nondet SockFilterInsn
  let expectedWire := ByteArray.mk #[
    UInt8.ofNat (insn.code.toNat % 256),
    UInt8.ofNat ((insn.code.toNat / 256) % 256),
    insn.jt,
    insn.jf,
    UInt8.ofNat (insn.k.toNat % 256),
    UInt8.ofNat ((insn.k.toNat / 256) % 256),
    UInt8.ofNat ((insn.k.toNat / 65536) % 256),
    UInt8.ofNat ((insn.k.toNat / 16777216) % 256) ]
  NondetTest.assert (encBpf [insn] = expectedWire)
  let prog ← nondet (List SockFilterInsn)
  NondetTest.assert (decBpf (encBpf prog) = some prog)
  let oddBytes ← nondet ByteArray
  assume (oddBytes.data.size % 8 ≠ 0)
  NondetTest.assert (decBpf oddBytes = none)

/-- `Internal.mkSandboxOps` makes zero raw C hook calls (`callCount = 0`) whenever a pure-Lean guard fails (`memfd_create` embedded-NUL or `> 249` bytes, `landlock_create_ruleset` `(none, 0)` or `(some attr, flags != 0)`, `seccomp` `GET_ACTION_AVAIL` non-zero flags or `SET_MODE_FILTER` invalid byte length / unsafe instructions), and makes exactly `1` raw hook call propagating both `.ok` and `.error rawErr` faithfully across all 10 `PosixSandboxOpsM` hooks on valid inputs. -/
def test_sandbox_impl_wrapperGuards
    {runner} [NondetTest runner]
    (mkOps : PosixSandboxOpsM (StateM Nat) Nat → SandboxOpsM (StateM Nat) Nat) : runner Unit := do
  let attr ← nondet LandlockRulesetAttr
  let qFlags ← nondet UInt32
  assume (qFlags ≠ 0)
  let nzSecFlags ← nondet SeccompFlags
  assume (nzSecFlags.toBits ≠ 0)
  let scFlags ← nondet SeccompFlags
  let act ← nondet UInt32
  let prOp ← nondet PrctlOp
  let rlRes ← nondet RlimitResource
  let rlCur ← nondet UInt64
  let rlMax ← nondet UInt64
  let mfdFlags ← nondet MemfdFlags
  let rawErr ← nondet Errno
  let badNulName ← nondet ByteArray
  assume (hasEmbeddedNul badNulName = true)
  let overName ← nondet ByteArray
  assume (overName.data.size > MFD_NAME_MAX)
  let okName ← nondet ByteArray
  assume (hasEmbeddedNul okName = false ∧ okName.data.size ≤ MFD_NAME_MAX)
  let badFilter ← nondet ByteArray
  assume (badFilter.data.size = 0 ∨ badFilter.data.size % 8 ≠ 0 ∨
    badFilter.data.size > SECCOMP_MAX_FILTER_INSNS * 8 ∨
    hasSafeSeccompRetBytes badFilter = false)
  let okFilter ← nondet ByteArray
  assume (okFilter.data.size > 0 ∧ okFilter.data.size % 8 = 0 ∧
    okFilter.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
    hasSafeSeccompRetBytes okFilter = true)
  let bump : StateM Nat Unit := modify (· + 1)
  let okRaw : PosixSandboxOpsM (StateM Nat) Nat :=
    { landlockQuery := fun fl => do bump; return .ok (fl + 100)
      landlockCreate := fun fs net => do bump; return .ok (fs.toNat + net.toNat + 10)
      landlockAddPathBeneath := fun rs p acc => do
        bump
        return if rs == 3 && p == 4 && acc == 7 then .ok () else .error Errno.EBADF
      landlockAddNetPort := fun rs port acc => do
        bump
        return if rs == 3 && port == 443 && acc == 2 then .ok () else .error Errno.EINVAL
      landlockRestrictSelf := fun rs => do
        bump
        return if rs == 3 then .ok () else .error Errno.EBADF
      seccompGetActionAvail := fun a => do bump; return .ok (a ^^^ 1)
      seccompSetFilter := fun fl bs => do bump; return .ok (fl + UInt32.ofNat bs.data.size)
      prctl := fun tag arg => do bump; return .ok (tag * 1000 + arg)
      setrlimit := fun tag c m => do
        bump
        return if tag == rlRes.toTag && c == rlCur && m == rlMax then .ok () else .error Errno.EINVAL
      memfdCreate := fun nm fl => do bump; return .ok (nm.data.size + fl.toNat) }
  let errRaw : PosixSandboxOpsM (StateM Nat) Nat :=
    { landlockQuery := fun _ => do bump; return .error rawErr
      landlockCreate := fun _ _ => do bump; return .error rawErr
      landlockAddPathBeneath := fun _ _ _ => do bump; return .error rawErr
      landlockAddNetPort := fun _ _ _ => do bump; return .error rawErr
      landlockRestrictSelf := fun _ => do bump; return .error rawErr
      seccompGetActionAvail := fun _ => do bump; return .error rawErr
      seccompSetFilter := fun _ _ => do bump; return .error rawErr
      prctl := fun _ _ => do bump; return .error rawErr
      setrlimit := fun _ _ _ => do bump; return .error rawErr
      memfdCreate := fun _ _ => do bump; return .error rawErr }
  let ops := mkOps okRaw
  let errOps := mkOps errRaw
  NondetTest.assert ((ops.landlockCreateRuleset none 0).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.landlockCreateRuleset (some attr) qFlags).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp (.getActionAvail act) nzSecFlags badFilter).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags badFilter).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.memfdCreate badNulName mfdFlags).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.memfdCreate overName mfdFlags).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.landlockCreateRuleset none qFlags).run 0 = (.ok (.version (qFlags + 100)), 1))
  NondetTest.assert ((ops.landlockCreateRuleset (some attr) 0).run 0 =
    (.ok (.ruleset (attr.handledAccessFs.toNat + attr.handledAccessNet.toNat + 10)), 1))
  NondetTest.assert ((ops.landlockAddRule 3 (.pathBeneath 4 7)).run 0 = (.ok (), 1))
  NondetTest.assert ((ops.landlockAddRule 3 (.netPort 443 2)).run 0 = (.ok (), 1))
  NondetTest.assert ((ops.landlockRestrictSelf 3).run 0 = (.ok (), 1))
  NondetTest.assert ((ops.seccomp (.getActionAvail act) {} badFilter).run 0 = (.ok (act ^^^ 1), 1))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags okFilter).run 0 =
    (.ok (scFlags.toBits + UInt32.ofNat okFilter.data.size), 1))
  let (pTag, pArg) := prOp.toRaw
  NondetTest.assert ((ops.prctl prOp).run 0 = (.ok (pTag * 1000 + pArg), 1))
  NondetTest.assert ((ops.setrlimit rlRes rlCur rlMax).run 0 = (.ok (), 1))
  NondetTest.assert ((ops.memfdCreate okName mfdFlags).run 0 = (.ok (okName.data.size + mfdFlags.toBits.toNat), 1))
  NondetTest.assert ((errOps.landlockCreateRuleset none qFlags).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.landlockCreateRuleset (some attr) 0).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.landlockAddRule 3 (.pathBeneath 4 7)).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.landlockAddRule 3 (.netPort 443 2)).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.landlockRestrictSelf 3).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.seccomp (.getActionAvail act) {} badFilter).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.seccomp .setModeFilter scFlags okFilter).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.prctl prOp).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.setrlimit rlRes rlCur rlMax).run 0 = (.error rawErr, 1))
  NondetTest.assert ((errOps.memfdCreate okName mfdFlags).run 0 = (.error rawErr, 1))

/-- `Internal.mkSandboxOps` rejects unsafe `seccomp(SECCOMP_SET_MODE_FILTER)` return verdicts and runtime zero-abort opcodes (`SECCOMP_RET_ERRNO | 0`, `SECCOMP_RET_ERRNO | EFAULT`, `SECCOMP_RET_KILL_PROCESS`, `SECCOMP_RET_KILL_THREAD`, `SECCOMP_RET_TRAP`, `SECCOMP_RET_TRACE`, `SECCOMP_RET_USER_NOTIF`, unknown action bits, `BPF_RET | BPF_A` `0x0016`, reserved `BPF_RET` `0x000e`, and `BPF_ALU | BPF_DIV | BPF_X` `0x003c`) with `(.error Errno.EINVAL, 0)` in pure Lean, while forwarding `ALLOW`, `LOG`, and non-zero non-`EFAULT` `SECCOMP_RET_ERRNO` filters (`callCount = 1`). -/
def test_sandbox_impl_seccompSafetyGuards
    {runner} [NondetTest runner]
    (mkOps : PosixSandboxOpsM (StateM Nat) Nat → SandboxOpsM (StateM Nat) Nat) : runner Unit := do
  let scFlags ← nondet SeccompFlags
  let bump : StateM Nat Unit := modify (· + 1)
  let okRaw : PosixSandboxOpsM (StateM Nat) Nat :=
    { landlockQuery := fun _ => do bump; return .ok 0
      landlockCreate := fun _ _ => do bump; return .ok 0
      landlockAddPathBeneath := fun _ _ _ => do bump; return .ok ()
      landlockAddNetPort := fun _ _ _ => do bump; return .ok ()
      landlockRestrictSelf := fun _ => do bump; return .ok ()
      seccompGetActionAvail := fun _ => do bump; return .ok 0
      seccompSetFilter := fun fl bs => do bump; return .ok (fl + UInt32.ofNat bs.data.size)
      prctl := fun _ _ => do bump; return .ok 0
      setrlimit := fun _ _ _ => do bump; return .ok ()
      memfdCreate := fun _ _ => do bump; return .ok 0 }
  let ops := mkOps okRaw
  let fErrnoZero := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO }]
  let fErrnoEfault := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EFAULT }]
  let fKillProc := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_PROCESS }]
  let fKillThread := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_THREAD }]
  let fTrap := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRAP }]
  let fUnkAct := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := 0x12340000 }]
  let fRetA := encodeSockFilters [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let fRetX := encodeSockFilters [{ code := 0x000e, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let fDivX := encodeSockFilters
    [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let fTrace := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRACE ||| 7 }]
  let fNotif := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_USER_NOTIF }]
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fErrnoZero).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fErrnoEfault).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fKillProc).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fKillThread).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fTrap).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fUnkAct).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fRetA).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fRetX).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fDivX).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fTrace).run 0 = (.error Errno.EINVAL, 0))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fNotif).run 0 = (.error Errno.EINVAL, 0))
  let fAllow := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let fLog := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_LOG }]
  let fErrnoEperm := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM }]
  let fErrnoMax := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| 4095 }]
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fAllow).run 0 = (.ok (scFlags.toBits + 8), 1))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fLog).run 0 = (.ok (scFlags.toBits + 8), 1))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fErrnoEperm).run 0 = (.ok (scFlags.toBits + 8), 1))
  NondetTest.assert ((ops.seccomp .setModeFilter scFlags fErrnoMax).run 0 = (.ok (scFlags.toBits + 8), 1))

/-- `prctl` tracks `no_new_privs` monotonically (`0 -> 1`), rejects invalid `PR_SET_PDEATHSIG` signals (`> 64`) with `EINVAL`, accepts `0..64` and `PR_SET_CHILD_SUBREAPER`, and gates `landlock_restrict_self` (`EPERM`) and `seccomp(SET_MODE_FILTER)` (`EACCES`) when `no_new_privs` is unset. -/
def test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig
    {S fd : Type} {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rGet0, s₁) := (ops.prctl .getNoNewPrivs).run s₀
  NondetTest.assert (rGet0 = .ok 0 ∧ s₁ = s₀)
  let (rBadSig1, sB1) := (ops.prctl (.setPdeathsig 65)).run s₀
  NondetTest.assert (rBadSig1 = .error Errno.EINVAL ∧ sB1 = s₀)
  let (rBadSig2, sB2) := (ops.prctl (.setPdeathsig 100)).run s₀
  NondetTest.assert (rBadSig2 = .error Errno.EINVAL ∧ sB2 = s₀)
  let (rSigMax, s₂) := (ops.prctl (.setPdeathsig 64)).run s₀
  let (rSigKill, s₃) := (ops.prctl (.setPdeathsig 9)).run s₂
  let (rSigClr, s₄) := (ops.prctl (.setPdeathsig 0)).run s₃
  let (rSub1, s₅) := (ops.prctl (.setChildSubreaper true)).run s₄
  let (rSub0, s₆) := (ops.prctl (.setChildSubreaper false)).run s₅
  NondetTest.assert (rSigMax = .ok 0 ∧ rSigKill = .ok 0 ∧ rSigClr = .ok 0 ∧
    rSub1 = .ok 0 ∧ rSub0 = .ok 0)
  let (rRs, s₇) := (ops.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0).run s₆
  match rRs with
  | .ok (.ruleset rs) =>
    let (rRestrNoNnp, sRn) := (ops.landlockRestrictSelf rs).run s₇
    NondetTest.assert (rRestrNoNnp = .error Errno.EPERM ∧ sRn = s₇)
    let (rSecNoNnp, sSn) := (ops.seccomp .setModeFilter {} allowAllSeccompFilterBytes).run s₇
    NondetTest.assert (rSecNoNnp = .error Errno.EACCES ∧ sSn = s₇)
    let (rSetNnp, s₈) := (ops.prctl .setNoNewPrivs).run s₇
    let (rGet1, s₉) := (ops.prctl .getNoNewPrivs).run s₈
    let (rSetNnp2, s₁₀) := (ops.prctl .setNoNewPrivs).run s₉
    let (rGet2, _) := (ops.prctl .getNoNewPrivs).run s₁₀
    NondetTest.assert (rSetNnp = .ok 0 ∧ rGet1 = .ok 1 ∧ s₉ = s₈ ∧ rSetNnp2 = .ok 0 ∧ rGet2 = .ok 1)
  | _ => NondetTest.assert False

/-- Landlock (`landlock_create_ruleset`, `landlock_add_rule`, `landlock_restrict_self`) enforces `CREATE_RULESET_VERSION >= 4`, `ENOMSG` (`42`) on empty access masks, `EBADF` vs `EBADFD` (`77`) descriptor checks (including `memfd` and `pseudoFs`), directory-only FS access rejection on regular files, TCP port `<= 65535`, `EPERM` before `no_new_privs`, and `E2BIG` after `16` stacked layers. -/
def test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf
    {S : Type} {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM S) HandleId) (s₀ : S) (dirHid regHid pseudoHid : HandleId) : runner Unit := do
  let (rVer, s₁) := (ops.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_VERSION).run s₀
  match rVer with
  | .ok (.version abi) =>
    NondetTest.assert (abi ≥ 4)
    let (rNull0, sN0) := (ops.landlockCreateRuleset none 0).run s₁
    NondetTest.assert (rNull0 = .error Errno.EINVAL ∧ sN0 = s₁)
    let (rBadCombo, sBc) := (ops.landlockCreateRuleset (some {}) 1).run s₁
    NondetTest.assert (rBadCombo = .error Errno.EINVAL ∧ sBc = s₁)
    let (rEmpty, sEm) := (ops.landlockCreateRuleset (some { handledAccessFs := 0, handledAccessNet := 0 }) 0).run s₁
    NondetTest.assert (rEmpty = .error ENOMSG ∧ sEm = s₁)
    let (rUnkFs, sUf) := (ops.landlockCreateRuleset (some { handledAccessFs := (1 : UInt64) <<< 60 }) 0).run s₁
    NondetTest.assert (rUnkFs = .error Errno.EINVAL ∧ sUf = s₁)
    let (rUnkNet, sUn) := (ops.landlockCreateRuleset (some { handledAccessNet := (1 : UInt64) <<< 4 }) 0).run s₁
    NondetTest.assert (rUnkNet = .error Errno.EINVAL ∧ sUn = s₁)
    let (rCreate, s₂) := (ops.landlockCreateRuleset
      (some { handledAccessFs := LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR
              handledAccessNet := LANDLOCK_ACCESS_NET_CONNECT_TCP }) 0).run s₁
    match rCreate with
    | .ok (.ruleset rs) =>
      let (rMfd, s₃) := (ops.memfdCreate (asciiBytes ['m']) {}).run s₂
      match rMfd with
      | .error _ => NondetTest.assert False
      | .ok mfd =>
        let (rAddClosedRs, _) := (ops.landlockAddRule 999 (.pathBeneath dirHid LANDLOCK_ACCESS_FS_READ_DIR)).run s₃
        NondetTest.assert (rAddClosedRs = .error Errno.EBADF)
        let (rAddNonRs, _) := (ops.landlockAddRule mfd (.pathBeneath dirHid LANDLOCK_ACCESS_FS_READ_DIR)).run s₃
        let (rAddPseudoRs, _) := (ops.landlockAddRule pseudoHid (.pathBeneath dirHid LANDLOCK_ACCESS_FS_READ_DIR)).run s₃
        NondetTest.assert (rAddNonRs = .error EBADFD ∧ rAddPseudoRs = .error EBADFD)
        let (rAddZeroPb, _) := (ops.landlockAddRule rs (.pathBeneath 999 0)).run s₃
        NondetTest.assert (rAddZeroPb = .error ENOMSG)
        let (rAddUnhandPb, _) := (ops.landlockAddRule rs (.pathBeneath 999 LANDLOCK_ACCESS_FS_WRITE_FILE)).run s₃
        NondetTest.assert (rAddUnhandPb = .error Errno.EINVAL)
        let (rAddClosedParent, _) := (ops.landlockAddRule rs (.pathBeneath 999 LANDLOCK_ACCESS_FS_READ_FILE)).run s₃
        NondetTest.assert (rAddClosedParent = .error Errno.EBADF)
        let (rAddMfdParent, _) := (ops.landlockAddRule rs (.pathBeneath mfd LANDLOCK_ACCESS_FS_READ_FILE)).run s₃
        let (rAddPseudoParent, _) := (ops.landlockAddRule rs (.pathBeneath pseudoHid LANDLOCK_ACCESS_FS_READ_FILE)).run s₃
        let (rAddRsParent, _) := (ops.landlockAddRule rs (.pathBeneath rs LANDLOCK_ACCESS_FS_READ_FILE)).run s₃
        NondetTest.assert (rAddMfdParent = .error EBADFD ∧ rAddPseudoParent = .error EBADFD ∧ rAddRsParent = .error EBADFD)
        let (rAddDirBitOnReg, _) := (ops.landlockAddRule rs (.pathBeneath regHid LANDLOCK_ACCESS_FS_READ_DIR)).run s₃
        NondetTest.assert (rAddDirBitOnReg = .error Errno.EINVAL)
        let (rAddRegOk, s₄) := (ops.landlockAddRule rs (.pathBeneath regHid LANDLOCK_ACCESS_FS_READ_FILE)).run s₃
        let (rAddDirOk, s₅) := (ops.landlockAddRule rs (.pathBeneath dirHid LANDLOCK_ACCESS_FS_READ_DIR)).run s₄
        NondetTest.assert (rAddRegOk = .ok () ∧ rAddDirOk = .ok ())
        let (rAddZeroNp, _) := (ops.landlockAddRule rs (.netPort 70000 0)).run s₅
        NondetTest.assert (rAddZeroNp = .error ENOMSG)
        let (rAddUnhandNp, _) := (ops.landlockAddRule rs (.netPort 80 LANDLOCK_ACCESS_NET_BIND_TCP)).run s₅
        NondetTest.assert (rAddUnhandNp = .error Errno.EINVAL)
        let (rAddBigPort, _) := (ops.landlockAddRule rs (.netPort 65536 LANDLOCK_ACCESS_NET_CONNECT_TCP)).run s₅
        NondetTest.assert (rAddBigPort = .error Errno.EINVAL)
        let (rAddPort0, s₆) := (ops.landlockAddRule rs (.netPort 0 LANDLOCK_ACCESS_NET_CONNECT_TCP)).run s₅
        let (rAddPortMax, s₇) := (ops.landlockAddRule rs (.netPort 65535 LANDLOCK_ACCESS_NET_CONNECT_TCP)).run s₆
        NondetTest.assert (rAddPort0 = .ok () ∧ rAddPortMax = .ok ())
        let (rRestrBeforeNnp, _) := (ops.landlockRestrictSelf 999).run s₇
        NondetTest.assert (rRestrBeforeNnp = .error Errno.EPERM)
        let (_, s₈) := (ops.prctl .setNoNewPrivs).run s₇
        let (rRestrClosed, _) := (ops.landlockRestrictSelf 999).run s₈
        let (rRestrMfd, _) := (ops.landlockRestrictSelf mfd).run s₈
        let (rRestrPseudo, _) := (ops.landlockRestrictSelf pseudoHid).run s₈
        NondetTest.assert (rRestrClosed = .error Errno.EBADF ∧ rRestrMfd = .error EBADFD ∧ rRestrPseudo = .error EBADFD)
        let (r16, s₉) := repeatRestrictSelf ops rs 16 s₈
        NondetTest.assert (r16 = .ok ())
        let (r17, s₁₀) := (ops.landlockRestrictSelf rs).run s₉
        NondetTest.assert (r17 = .error Errno.E2BIG ∧ s₁₀ = s₉)
        let (rAfterCapClosed, _) := (ops.landlockRestrictSelf 999).run s₉
        let (rAfterCapMfd, _) := (ops.landlockRestrictSelf mfd).run s₉
        NondetTest.assert (rAfterCapClosed = .error Errno.EBADF ∧ rAfterCapMfd = .error EBADFD)
    | _ => NondetTest.assert False
  | _ => NondetTest.assert False

/-- `seccomp` supports `GET_ACTION_AVAIL` (`EOPNOTSUPP` on unknown actions or non-zero data bits, `EINVAL` on non-zero flags) and `SET_MODE_FILTER` (`EINVAL` on `0`, non-multiple-of-`8`, or `> 160` insns before `no_new_privs`, `EACCES` when `no_new_privs == false`, classic BPF verification, and `TSYNC`). -/
def test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation
    {S fd : Type} {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let overFilter ← nondet ByteArray
  assume (overFilter.data.size > SECCOMP_MAX_FILTER_INSNS * 8)
  let (rActErrno, _) := (ops.seccomp (.getActionAvail SECCOMP_RET_ERRNO) {} ByteArray.empty).run s₀
  let (rActAllow, _) := (ops.seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty).run s₀
  let (rActKillP, _) := (ops.seccomp (.getActionAvail SECCOMP_RET_KILL_PROCESS) {} ByteArray.empty).run s₀
  let (rActLog, _) := (ops.seccomp (.getActionAvail SECCOMP_RET_LOG) {} ByteArray.empty).run s₀
  NondetTest.assert (rActErrno = .ok 0 ∧ rActAllow = .ok 0 ∧ rActKillP = .ok 0 ∧ rActLog = .ok 0)
  let (rActDataBit, _) := (ops.seccomp (.getActionAvail (SECCOMP_RET_ERRNO ||| 1)) {} ByteArray.empty).run s₀
  let (rActUnk, _) := (ops.seccomp (.getActionAvail 0x12340000) {} ByteArray.empty).run s₀
  let (rActBadFl, _) := (ops.seccomp (.getActionAvail SECCOMP_RET_ALLOW) { tsync := true } ByteArray.empty).run s₀
  NondetTest.assert (rActDataBit = .error Errno.EOPNOTSUPP ∧ rActUnk = .error Errno.EOPNOTSUPP ∧
    rActBadFl = .error Errno.EINVAL)
  let (rEmptyF, _) := (ops.seccomp .setModeFilter {} ByteArray.empty).run s₀
  let (rOddF, _) := (ops.seccomp .setModeFilter {} (mkRepBytes 7)).run s₀
  let (rTooManyF, _) := (ops.seccomp .setModeFilter {} overFilter).run s₀
  let (rNoNnp, _) := (ops.seccomp .setModeFilter {} allowAllSeccompFilterBytes).run s₀
  NondetTest.assert (rEmptyF = .error Errno.EINVAL ∧ rOddF = .error Errno.EINVAL ∧
    rTooManyF = .error Errno.EINVAL ∧ rNoNnp = .error Errno.EACCES)
  let (_, s₁) := (ops.prctl .setNoNewPrivs).run s₀
  let badNoRet := encodeSockFilters [{ code := 0x0000, jt := 0, jf := 0, k := 0 }]
  let badUnaligned := encodeSockFilters
    [{ code := 0x0020, jt := 0, jf := 0, k := 2 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badOobAbs := encodeSockFilters
    [{ code := 0x0020, jt := 0, jf := 0, k := 64 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badDiv0 := encodeSockFilters
    [{ code := 0x0034, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badShift := encodeSockFilters
    [{ code := 0x0064, jt := 0, jf := 0, k := 32 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badModOp := encodeSockFilters
    [{ code := 0x0094, jt := 0, jf := 0, k := 3 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badUninitMem := encodeSockFilters
    [{ code := 0x0060, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let badOobJump := encodeSockFilters
    [{ code := 0x0015, jt := 1, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  NondetTest.assert (((ops.seccomp .setModeFilter {} badNoRet).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badUnaligned).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badOobAbs).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badDiv0).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badShift).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badModOp).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badUninitMem).run s₁).1 = .error Errno.EINVAL)
  NondetTest.assert (((ops.seccomp .setModeFilter {} badOobJump).run s₁).1 = .error Errno.EINVAL)
  let validRich := encodeSockFilters
    [ { code := 0x0020, jt := 0, jf := 0, k := 60 }
    , { code := 0x0002, jt := 0, jf := 0, k := 0 }
    , { code := 0x0060, jt := 0, jf := 0, k := 0 }
    , { code := 0x0015, jt := 0, jf := 0, k := 0 }
    , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW } ]
  let (rOk1, s₂) := (ops.seccomp .setModeFilter {} allowAllSeccompFilterBytes).run s₁
  let (rOk2, _) := (ops.seccomp .setModeFilter { tsync := true } validRich).run s₂
  NondetTest.assert (rOk1 = .ok 0 ∧ rOk2 = .ok 0)

/-- `setrlimit` rejects `cur > max` with `EINVAL` (taking precedence over `max > hard`), enforces monotonic `rlim_max` lowering (`EPERM` on attempts to raise `max`, while allowing `cur` to rise up to `max`), rejects `RLIMIT_NOFILE > NOFILE_KERNEL_MAX` with `EPERM`, and enforces `EMFILE` on FD-allocating syscalls when `RLIMIT_NOFILE` soft limit is `0`. -/
def test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile
    {S fd : Type} {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rCurGtMax, sCm) := (ops.setrlimit .core 100 50).run s₀
  NondetTest.assert (rCurGtMax = .error Errno.EINVAL ∧ sCm = s₀)
  let (rFs1, s₁) := (ops.setrlimit .fsize 512 1024).run s₀
  let (rFs2, s₂) := (ops.setrlimit .fsize 1024 1024).run s₁
  let (rFsRaiseMax, sRm) := (ops.setrlimit .fsize 1024 1025).run s₂
  let (rFsPrec, sPr) := (ops.setrlimit .fsize 2048 1500).run s₂
  NondetTest.assert (rFs1 = .ok () ∧ rFs2 = .ok () ∧
    rFsRaiseMax = .error Errno.EPERM ∧ sRm = s₂ ∧
    rFsPrec = .error Errno.EINVAL ∧ sPr = s₂)
  let (rCore0, s₃) := (ops.setrlimit .core 0 0).run s₂
  let (rCoreRaise, _) := (ops.setrlimit .core 0 1).run s₃
  NondetTest.assert (rCore0 = .ok () ∧ rCoreRaise = .error Errno.EPERM)
  let (rNfInf, sNf) := (ops.setrlimit .nofile RLIM_INFINITY RLIM_INFINITY).run s₃
  NondetTest.assert (rNfInf = .error Errno.EPERM ∧ sNf = s₃)
  let (rNf0, s₄) := (ops.setrlimit .nofile 0 64).run s₃
  NondetTest.assert (rNf0 = .ok ())
  let (rMfdEmfile, _) := (ops.memfdCreate (asciiBytes ['x']) {}).run s₄
  let (rLlEmfile, _) := (ops.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0).run s₄
  let (rLlVerOk, _) := (ops.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_VERSION).run s₄
  NondetTest.assert (rMfdEmfile = .error Errno.EMFILE ∧ rLlEmfile = .error Errno.EMFILE)
  match rLlVerOk with
  | .ok (.version v) => NondetTest.assert (v ≥ 4)
  | _ => NondetTest.assert False
  let (rNf64, s₅) := (ops.setrlimit .nofile 64 64).run s₄
  let (rMfdRestored, _) := (ops.memfdCreate (asciiBytes ['x']) {}).run s₅
  NondetTest.assert (rNf64 = .ok () ∧ ∃ h, rMfdRestored = .ok h)

/-- `memfd_create` rejects embedded NUL bytes (`EINVAL`), names longer than `249` bytes (`MFD_NAME_MAX`, `EINVAL`), and conflicting `MFD_NOEXEC_SEAL | MFD_EXEC` (`EINVAL`), while succeeding on empty (`0`-byte) and exact `249`-byte names across valid flag combinations with distinct handles. -/
def test_sandbox_ops_memfdCreate_nameBoundsAndFlags
    {S fd : Type} [DecidableEq fd] {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let badNul ← nondet ByteArray
  assume (hasEmbeddedNul badNul = true)
  let overMax ← nondet ByteArray
  assume (overMax.data.size > MFD_NAME_MAX)
  let (rNul, sN) := (ops.memfdCreate badNul {}).run s₀
  NondetTest.assert (rNul = .error Errno.EINVAL ∧ sN = s₀)
  let (rOver, sO) := (ops.memfdCreate overMax {}).run s₀
  NondetTest.assert (rOver = .error Errno.EINVAL ∧ sO = s₀)
  let (rConflict, sC) := (ops.memfdCreate (asciiBytes ['a']) { noexecSeal := true, exec := true }).run s₀
  NondetTest.assert (rConflict = .error Errno.EINVAL ∧ sC = s₀)
  let (rEmpty, s₁) := (ops.memfdCreate ByteArray.empty { cloexec := true, allowSealing := true }).run s₀
  let (rMax249, s₂) := (ops.memfdCreate (mkRepBytes 249) { cloexec := true, noexecSeal := true }).run s₁
  let (rExec, _) := (ops.memfdCreate (asciiBytes ['e']) { cloexec := false, exec := true }).run s₂
  match rEmpty, rMax249, rExec with
  | .ok h1, .ok h2, .ok h3 =>
    NondetTest.assert (h1 ≠ h2 ∧ h2 ≠ h3 ∧ h1 ≠ h3)
  | _, _, _ => NondetTest.assert False

/-- `Model.allowedStep` rejects `EFAULT` unconditionally, locks `landlockEnabled`/`landlockAbi?` (`ERRATA` rejecting `EINVAL` on ABI `>= 6`, `canDisable` accepted on all three Landlock syscalls before `hasLandlockEvidence`), gates `memfdNoexecStrict?` strictly on `flags.exec == true`, enforces `curExact` and `nofileNrOpenCeil`, masks `ALLOW`/`LOG` low-16-bit data, rejects unsafe `seccomp` filters with `EINVAL`, and preserves unpinned `SandboxSysState` across `seccompMayIntercept` error outcomes (`EPERM`, `EACCES`, `E2BIG`) so subsequent `ALLOW`ed syscalls succeed. -/
def test_sandbox_model_allowedStep_relationalInvariants
    {runner} [NondetTest runner]
    (step : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState := allowedStep) :
    runner Unit := do
  let s0 := SandboxSysState.initial
  NondetTest.assert ((step s0 (.prctl .getNoNewPrivs) (.err Errno.EFAULT)).isNone)
  NondetTest.assert ((step s0 (.prctl .getNoNewPrivs) (.err Errno.EINTR)).isSome)
  NondetTest.assert ((step s0 (.landlockCreateRuleset none 1) (.landlockVersion 3)).isNone)
  NondetTest.assert ((step s0 (.landlockCreateRuleset none 1) (.err Errno.ENOSYS)).isSome)
  NondetTest.assert ((step s0 (.landlockAddRule 99 (.netPort 80 1)) (.err Errno.EOPNOTSUPP)).isSome)
  let errnoZero := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO }]
  let errnoEfault := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EFAULT }]
  let killThread := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_THREAD }]
  let retA := encodeSockFilters [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  let divX := encodeSockFilters
    [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
  match step s0 (.prctl .setNoNewPrivs) (.u32 0) with
  | none => NondetTest.assert False
  | some sNnp =>
    NondetTest.assert ((step sNnp (.landlockRestrictSelf 99) (.err Errno.EOPNOTSUPP)).isSome)
    let allowWithData := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW ||| 0x63 }]
    match step sNnp (.seccomp .setModeFilter {} allowWithData) (.u32 0) with
    | none => NondetTest.assert False
    | some sAllowData =>
      NondetTest.assert (sAllowData.seccompMayIntercept = false)
      NondetTest.assert ((step sAllowData (.prctl (.setPdeathsig 99)) (.u32 0)).isNone)
    NondetTest.assert (step sNnp (.seccomp .setModeFilter {} errnoZero) (.err Errno.EINVAL) = some sNnp ∧
      (step sNnp (.seccomp .setModeFilter {} errnoZero) (.u32 0)).isNone)
    NondetTest.assert (step sNnp (.seccomp .setModeFilter {} errnoEfault) (.err Errno.EINVAL) = some sNnp ∧
      (step sNnp (.seccomp .setModeFilter {} errnoEfault) (.u32 0)).isNone)
    NondetTest.assert (step sNnp (.seccomp .setModeFilter {} killThread) (.err Errno.EINVAL) = some sNnp ∧
      (step sNnp (.seccomp .setModeFilter {} killThread) (.u32 0)).isNone)
    NondetTest.assert (step sNnp (.seccomp .setModeFilter {} retA) (.err Errno.EINVAL) = some sNnp ∧
      (step sNnp (.seccomp .setModeFilter {} retA) (.u32 0)).isNone)
    NondetTest.assert (step sNnp (.seccomp .setModeFilter {} divX) (.err Errno.EINVAL) = some sNnp ∧
      (step sNnp (.seccomp .setModeFilter {} divX) (.u32 0)).isNone)
  let errnoEperm := encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM }]
  match step s0 (.seccomp .setModeFilter {} errnoEperm) (.u32 0) with
  | none => NondetTest.assert False
  | some sIntercept =>
    NondetTest.assert (sIntercept.seccompMayIntercept = true)
    match step sIntercept (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0) (.opened 0) with
    | none => NondetTest.assert False
    | some sIntRs =>
      NondetTest.assert ((step sIntRs (.landlockCreateRuleset none 0) (.err Errno.EPERM)).isNone)
      NondetTest.assert ((step sIntRs (.seccomp .setModeFilter {} errnoZero) (.err Errno.EPERM)).isNone)
      NondetTest.assert ((step sIntRs (.prctl .getNoNewPrivs) (.err Errno.EFAULT)).isNone)
      match step sIntRs (.landlockRestrictSelf 99) (.err Errno.EPERM) with
      | none => NondetTest.assert False
      | some sAfterEperm =>
        NondetTest.assert (sAfterEperm = sIntRs ∧
          (step sAfterEperm (.landlockRestrictSelf 0) .unit).isSome)
      match step sIntRs (.landlockRestrictSelf 0) (.err Errno.E2BIG) with
      | none => NondetTest.assert False
      | some sAfterE2big =>
        NondetTest.assert (sAfterE2big = sIntRs ∧
          (step sAfterE2big (.landlockRestrictSelf 0) .unit).isSome)
      match step sIntRs (.setrlimit .fsize 512 2048) (.err Errno.EPERM) with
      | none => NondetTest.assert False
      | some sAfterRlim =>
        NondetTest.assert (sAfterRlim = sIntRs ∧
          (step sAfterRlim (.setrlimit .fsize 512 2048) .unit).isSome)
      match step sIntRs (.memfdCreate (asciiBytes ['a']) { exec := true, allowSealing := true }) (.err Errno.EACCES) with
      | none => NondetTest.assert False
      | some sAfterMfd =>
        NondetTest.assert (sAfterMfd = sIntRs ∧
          (step sAfterMfd (.memfdCreate (asciiBytes ['b']) { exec := true }) (.opened 1)).isSome)
  match step s0 (.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_ERRATA) (.landlockVersion 7) with
  | none => NondetTest.assert False
  | some sErrata =>
    NondetTest.assert ((step sErrata (.landlockAddRule 99 (.netPort 80 1)) (.err Errno.EOPNOTSUPP)).isNone)
  match step s0 (.landlockCreateRuleset none 1) (.landlockVersion 9) with
  | none => NondetTest.assert False
  | some sAbi =>
    NondetTest.assert ((step sAbi (.landlockCreateRuleset none 1) (.landlockVersion 8)).isNone)
    NondetTest.assert ((step sAbi (.landlockCreateRuleset none 1) (.landlockVersion 9)).isSome)
    NondetTest.assert ((step sAbi (.landlockCreateRuleset none 1) (.err Errno.ENOSYS)).isNone)
    NondetTest.assert ((step sAbi (.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_ERRATA) (.err Errno.EINVAL)).isNone)
  NondetTest.assert ((step s0 (.memfdCreate (asciiBytes ['a']) { noexecSeal := false, exec := false }) (.err Errno.EACCES)).isNone)
  match step s0 (.memfdCreate (asciiBytes ['a']) { noexecSeal := false, exec := false }) (.opened 0) with
  | none => NondetTest.assert False
  | some sDefMfd =>
    NondetTest.assert ((step sDefMfd (.memfdCreate (asciiBytes ['b']) { noexecSeal := false, exec := false }) (.opened 0)).isNone)
    NondetTest.assert ((step sDefMfd (.memfdCreate (asciiBytes ['b']) { noexecSeal := false, exec := true }) (.err Errno.EACCES)).isSome)
  match step s0 (.memfdCreate (asciiBytes ['a']) { noexecSeal := false, exec := true }) (.err Errno.EACCES) with
  | none => NondetTest.assert False
  | some sStrict =>
    NondetTest.assert ((step sStrict (.memfdCreate (asciiBytes ['b']) { noexecSeal := false, exec := true }) (.opened 0)).isNone)
    NondetTest.assert ((step sStrict (.memfdCreate (asciiBytes ['b']) { noexecSeal := false, exec := false }) (.opened 0)).isSome)
  let sUnsetCur0 := { s0 with rlimitNofile := { cur := 0, hardUpper := 64, curExact := false, hardExact := false } }
  NondetTest.assert ((step sUnsetCur0 (.memfdCreate (asciiBytes ['a']) {}) (.opened 0)).isSome)
  let sPriv := { s0 with hasCapSysResource? := some true }
  match step sPriv (.setrlimit .nofile 1024 2000000) (.err Errno.EPERM) with
  | none => NondetTest.assert False
  | some sPrivTight =>
    NondetTest.assert ((step sPrivTight (.setrlimit .nofile 1024 2000000) .unit).isNone)
    NondetTest.assert ((step sPrivTight (.setrlimit .nofile 1024 1999999) .unit).isSome)
  match step s0 (.setrlimit .fsize 512 2048) (.err Errno.EPERM) with
  | none => NondetTest.assert False
  | some sTight =>
    NondetTest.assert (sTight.hasCapSysResource? = some false)
    NondetTest.assert ((step sTight (.setrlimit .fsize 512 2048) .unit).isNone)
    NondetTest.assert ((step sTight (.setrlimit .fsize 512 2047) .unit).isSome)
  NondetTest.assert ((step s0 (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_RESOLVE_UNIX }) 0) (.err Errno.EOPNOTSUPP)).isSome)
  NondetTest.assert ((step s0 (.seccomp .setModeFilter { waitKillableRecv := true } allowAllSeccompFilterBytes) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.seccomp .setModeFilter { waitKillableRecv := true } allowAllSeccompFilterBytes) (.u32 0)).isNone)
  match step s0 (.seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty) (.u32 0) with
  | none => NondetTest.assert False
  | some sSec =>
    NondetTest.assert ((step sSec (.seccomp (.getActionAvail SECCOMP_RET_ALLOW) {} ByteArray.empty) (.err Errno.ENOSYS)).isNone)
    NondetTest.assert ((step sSec (.seccomp .setModeFilter {} allowAllSeccompFilterBytes) (.err Errno.ENOSYS)).isNone)
  match step s0 (.memfdCreate (asciiBytes ['z']) {}) (.opened 0) with
  | none => NondetTest.assert False
  | some sMfd =>
    NondetTest.assert ((step sMfd (.memfdCreate (asciiBytes ['w']) {}) (.err Errno.ENOSYS)).isNone)
  match step s0 (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_RESOLVE_UNIX }) 0) (.opened 0) with
  | none => NondetTest.assert False
  | some sV9 =>
    NondetTest.assert ((step sV9 (.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_ERRATA) (.err Errno.EINVAL)).isNone)
    NondetTest.assert ((step sV9 (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_IOCTL_DEV }) 0) (.err Errno.EINVAL)).isNone)
    NondetTest.assert ((step sV9 (.landlockCreateRuleset none 1) (.landlockVersion 8)).isNone)
    NondetTest.assert ((step sV9 (.landlockCreateRuleset none 1) (.landlockVersion 9)).isSome)

/-- `Model.allowedStep` carries zero silent ambient assumptions in `SandboxSysState.initial` (`getNoNewPrivs == 1`, `CLONE_NEWUSER` `nnp == 0` with `hasCapSysAdmin? = some true`, pre-stacked outer Landlock `E2BIG` layer locking, and privileged `rlim_max` raising with `hasCapSysResource? = some true`), and enforces `pseudoFs` (`EBADFD`) plus `O_PATH` `ruleset` (`EBADF`) vs `parentFd` (`0` / `EBADFD`) asymmetry. -/
def test_sandbox_model_allowedStep_environmentFreeAndOPath
    {runner} [NondetTest runner]
    (step : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState := allowedStep) :
    runner Unit := do
  let s0 := SandboxSysState.initial
  match step s0 (.prctl .getNoNewPrivs) (.u32 1) with
  | none => NondetTest.assert False
  | some sAmbNnp =>
    NondetTest.assert (sAmbNnp.noNewPrivs? = some true)
    NondetTest.assert ((step sAmbNnp (.prctl .getNoNewPrivs) (.u32 0)).isNone)
    NondetTest.assert ((step sAmbNnp (.seccomp .setModeFilter {} allowAllSeccompFilterBytes) (.u32 0)).isSome)
  match step s0 (.prctl .getNoNewPrivs) (.u32 0) with
  | none => NondetTest.assert False
  | some sUser0 =>
    match step sUser0 (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0) (.opened 0) with
    | none => NondetTest.assert False
    | some sUserRs =>
      match step sUserRs (.landlockRestrictSelf 0) .unit with
      | none => NondetTest.assert False
      | some sUserRestr =>
        NondetTest.assert (sUserRestr.noNewPrivs? = some false ∧ sUserRestr.hasCapSysAdmin? = some true)
        NondetTest.assert (step sUserRestr (.prctl .getNoNewPrivs) (.u32 0) = some sUserRestr)
        NondetTest.assert ((step sUserRestr (.landlockRestrictSelf 0) (.err Errno.EPERM)).isNone)
        NondetTest.assert ((step sUserRestr (.setrlimit .fsize 512 1024) (.err Errno.EPERM)).isSome)
        match step sUserRestr (.landlockRestrictSelf 0) (.err Errno.E2BIG) with
        | none => NondetTest.assert False
        | some sPreCap =>
          NondetTest.assert (sPreCap.landlockLayers = LANDLOCK_MAX_STACKED_LAYERS ∧ sPreCap.landlockLayersExact = true)
          NondetTest.assert ((step sPreCap (.landlockRestrictSelf 0) .unit).isNone)
          NondetTest.assert (step sPreCap (.landlockRestrictSelf 0) (.err Errno.E2BIG) = some sPreCap)
  match step s0 (.seccomp .setModeFilter {} allowAllSeccompFilterBytes) (.err Errno.EACCES) with
  | none => NondetTest.assert False
  | some sDenied =>
    NondetTest.assert (sDenied.noNewPrivs? = some false ∧ sDenied.hasCapSysAdmin? = some false)
    NondetTest.assert ((step sDenied (.prctl .getNoNewPrivs) (.u32 1)).isNone)
    NondetTest.assert ((step sDenied (.seccomp .setModeFilter {} allowAllSeccompFilterBytes) (.u32 0)).isNone)
  let sUnprivNnp := { SandboxSysState.unprivileged with noNewPrivs? := some true }
  match step sUnprivNnp (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0) (.opened 0) with
  | none => NondetTest.assert False
  | some sUnprivRs =>
    NondetTest.assert ((step sUnprivRs (.landlockRestrictSelf 0) (.err Errno.E2BIG)).isNone)
  match step s0 (.setrlimit .fsize 512 1024) .unit with
  | none => NondetTest.assert False
  | some sLim1 =>
    match step sLim1 (.setrlimit .fsize 1024 2048) .unit with
    | none => NondetTest.assert False
    | some sLimPriv =>
      NondetTest.assert (sLimPriv.hasCapSysResource? = some true)
      NondetTest.assert ((step sLimPriv (.setrlimit .fsize 1024 4096) (.err Errno.EPERM)).isNone)
  let sPseudo := (((s0.withPseudoFd 50).withHostFd 51 true).withHostFd 53 true true).withPseudoFd 54 true
  match step sPseudo (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR }) 0) (.opened 55) with
  | none => NondetTest.assert False
  | some sPseudoRs =>
    NondetTest.assert (step sPseudoRs (.landlockAddRule 50 (.pathBeneath 51 LANDLOCK_ACCESS_FS_READ_DIR)) (.err EBADFD) = some sPseudoRs)
    NondetTest.assert ((step sPseudoRs (.landlockAddRule 50 (.pathBeneath 51 LANDLOCK_ACCESS_FS_READ_DIR)) (.err Errno.EBADF)).isNone)
    NondetTest.assert (step sPseudoRs (.landlockAddRule 55 (.pathBeneath 50 LANDLOCK_ACCESS_FS_READ_FILE)) (.err EBADFD) = some sPseudoRs)
    NondetTest.assert ((step sPseudoRs (.landlockAddRule 55 (.pathBeneath 50 LANDLOCK_ACCESS_FS_READ_FILE)) .unit).isNone)
    NondetTest.assert (step sPseudoRs (.landlockAddRule 53 (.pathBeneath 51 LANDLOCK_ACCESS_FS_READ_DIR)) (.err Errno.EBADF) = some sPseudoRs)
    NondetTest.assert ((step sPseudoRs (.landlockAddRule 53 (.pathBeneath 51 LANDLOCK_ACCESS_FS_READ_DIR)) (.err EBADFD)).isNone)
    NondetTest.assert (step sPseudoRs (.landlockAddRule 55 (.pathBeneath 53 LANDLOCK_ACCESS_FS_READ_DIR)) .unit =
      some { sPseudoRs with landlockEnabled := true })
    NondetTest.assert (step sPseudoRs (.landlockAddRule 54 (.pathBeneath 51 LANDLOCK_ACCESS_FS_READ_DIR)) (.err Errno.EBADF) = some sPseudoRs)
    NondetTest.assert (step sPseudoRs (.landlockAddRule 55 (.pathBeneath 54 LANDLOCK_ACCESS_FS_READ_FILE)) (.err EBADFD) = some sPseudoRs)
    let sPseudoNnp := { sPseudoRs with noNewPrivs? := some true }
    NondetTest.assert (step sPseudoNnp (.landlockRestrictSelf 50) (.err EBADFD) = some sPseudoNnp)
    NondetTest.assert ((step sPseudoNnp (.landlockRestrictSelf 50) .unit).isNone)
    NondetTest.assert (step sPseudoNnp (.landlockRestrictSelf 53) (.err Errno.EBADF) = some sPseudoNnp)
    NondetTest.assert ((step sPseudoNnp (.landlockRestrictSelf 53) (.err EBADFD)).isNone)
  let sGapBase := (((s0.withHostFd 9 true).withHostFd 10 false).withHostFd 11 true).withHostFd 12 false
  match step sGapBase (.setrlimit .nofile 4 1024) .unit with
  | none => NondetTest.assert False
  | some sGap =>
    NondetTest.assert ((step sGap (.memfdCreate (asciiBytes ['g']) {}) (.opened 13)).isSome)
    NondetTest.assert ((step sGap (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0) (.opened 13)).isSome)
  match step sGapBase (.setrlimit .nofile 0 1024) .unit with
  | none => NondetTest.assert False
  | some sZeroNofile =>
    NondetTest.assert ((step sZeroNofile (.memfdCreate (asciiBytes ['g']) {}) (.opened 13)).isNone)
  let sOuter := s0.withOuterSeccomp
  NondetTest.assert ((step sOuter (.memfdCreate (asciiBytes ['o']) {}) (.err Errno.EPERM)).isSome)
  NondetTest.assert ((step sOuter (.memfdCreate (asciiBytes ['o']) {}) (.err Errno.EFAULT)).isNone)
  NondetTest.assert ((step sOuter (.memfdCreate (ByteArray.mk #[97, 0]) {}) (.err Errno.EPERM)).isNone)

/-- `SandboxSysState.initial` and `SandboxSysState.unprivileged` satisfy `wf`, and for every well-formed `s : SandboxSysState` and request `req : SandboxReq`, executing `modelOps` produces an outcome and next state accepted by `allowedStep` while preserving `wf`. -/
def test_sandbox_model_modelOpsRefinesAllowedStep
    {runner} [NondetTest runner]
    (ops : SandboxOpsM (StateM SandboxSysState) HandleId := modelOps)
    (step : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState := allowedStep) :
    runner Unit := do
  NondetTest.assert (SandboxSysState.initial.wf = true ∧ SandboxSysState.unprivileged.wf = true)
  let s ← nondet SandboxSysState
  assume (s.wf = true)
  let req ← nondet SandboxReq
  let (out, s') := (execSandboxReq ops req).run s
  NondetTest.assert (step s req out = some s' ∧ s'.wf = true)

/-- External trust-boundary assumptions for `LeanSwe.LinuxSyscall.Sandbox` C wrappers (`sandbox_shim.c` + `fd_box.h`) and Linux kernel ABI (`x86_64` + `aarch64`), verified 1-to-1 by `RuntimeTests.lean`, `leanswe-world-fuzz`, and `strace` fault injection. On `assume_sandbox_seccomp_actionAvailAndFilterAbi`, `Internal.mkSandboxOps` enforces `hasSafeSeccompRetBytes` in pure Lean (rejecting `SECCOMP_RET_ERRNO | 0`, `SECCOMP_RET_ERRNO | EFAULT`, `KILL_PROCESS`, `KILL_THREAD`, `TRAP`, `TRACE`, `USER_NOTIF`, unknown action bits, `BPF_RET | BPF_A` `0x0016`, and `BPF_ALU | BPF_DIV | BPF_X` `0x003c` with `EINVAL`), so `SandboxFuzz` can fuzz arbitrary `filterBytes` with zero avoided inputs; `SandboxSysState.withOuterSeccomp` likewise assumes inherited safe outer filters (`SECCOMP_RET_ERRNO | EFAULT` fails loud with `SIGABRT`, verified in `RuntimeTests.lean`). -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockCreateRuleset_versionAndRuleset"
      subject := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockAddRule_pathBeneathAndNetPort"
      subject := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_landlockRestrictSelf_nnpAndLayerCap"
      subject := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_seccomp_actionAvailAndFilterAbi"
      subject := "LeanSwe.LinuxSyscall.Sandbox.seccomp"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_prctl_nnpSubreaperAndPdeathsig"
      subject := "LeanSwe.LinuxSyscall.Sandbox.prctl"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_setrlimit_curMaxAndHardCap"
      subject := "LeanSwe.LinuxSyscall.Sandbox.setrlimit"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Sandbox.assume_sandbox_memfdCreate_nameBoundsAndSeals"
      subject := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate"
      formalPred? := none } ]

/-- Complete `(request × SandboxErrorKind)` error-coverage matrix for all 7 curated `Sandbox` syscalls (`35` obligations), linked to real Linux tests and mocked/fault-injection tests in `RuntimeTests.lean`. -/
def errorCoverage : List (ErrorObligation SandboxErrorKind) :=
  [ { request := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockCreateRuleset", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockCreateRuleset_transientOrResource" .real }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockAddRule", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockAddRule_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_limitOrUnsupported" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.landlockRestrictSelf", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_landlockRestrictSelf_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.seccomp", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.seccomp", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.seccomp", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.seccomp", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_limitOrUnsupported" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.seccomp", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_seccomp_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.prctl", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.prctl", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.prctl", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.prctl", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.prctl", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_prctl_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.setrlimit", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.setrlimit", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.setrlimit", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.setrlimit", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.setrlimit", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_setrlimit_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate", errorKind := .limitOrUnsupported, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Sandbox.memfdCreate", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests.err_memfdCreate_transientOrResource" .real } ]

end LeanSwe.LinuxSyscall.Sandbox
