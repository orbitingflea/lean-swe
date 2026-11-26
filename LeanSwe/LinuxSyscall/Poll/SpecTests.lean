import Core.NondetTest
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Model

namespace LeanSwe.LinuxSyscall.Poll

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Errno.isTransientOsErrno` excludes `EFAULT` and `PollErrorKind.ofErrno` classifies `EBADF`, `EINVAL`/`ENOSYS`, `EINTR`, and resource/transient errnos into their exact semantic buckets. -/
def test_poll_errno_classification
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → PollErrorKind := PollErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  NondetTest.assert (classify e =
    (if e == Errno.EBADF then .badFd
     else if e == Errno.EINVAL || e == Errno.ENOSYS then .invalidArg
     else if e == Errno.EINTR then .interrupted
     else .transientOrResource))
  NondetTest.assert (classify Errno.EBADF = .badFd)
  NondetTest.assert (classify Errno.EINVAL = .invalidArg)
  NondetTest.assert (classify Errno.ENOSYS = .invalidArg)
  NondetTest.assert (classify Errno.EINTR = .interrupted)
  NondetTest.assert (classify Errno.ENOMEM = .transientOrResource)
  NondetTest.assert (classify Errno.EMFILE = .transientOrResource)
  NondetTest.assert (classify Errno.ENFILE = .transientOrResource)
  NondetTest.assert (classify Errno.EIO = .transientOrResource)

/-- `PollEvents` and `EventFdFlags` bit encoders are injective and round-trip cleanly, default `EventFdFlags` enables `cloexec`, `Timespec.isValid` and `Timespec.isZero` enforce exact bounds, and `encodePollRequests`/`decodePollRevents` preserve exact per-entry readiness masks. -/
def test_poll_flags_and_codecs_roundtripAndInjective
    {runner} [NondetTest runner]
    (encEv : PollEvents → UInt32 := PollEvents.toBits)
    (decEv : UInt32 → PollEvents := PollEvents.ofBits)
    (encEfd : EventFdFlags → UInt32 := EventFdFlags.toBits)
    (validTs : Timespec → Bool := Timespec.isValid)
    (encReq : Array (Nat × PollEvents) → Array Nat × ByteArray := encodePollRequests)
    (decRev : ByteArray → Array PollEvents := decodePollRevents)
    (isZeroTs : Timespec → Bool := Timespec.isZero)
    (defEfd : EventFdFlags := {})
    (defTs : Timespec := {}) : runner Unit := do
  let ev1 ← nondet PollEvents
  let ev2 ← nondet PollEvents
  NondetTest.assert ((encEv ev1 == encEv ev2) = (ev1 == ev2))
  NondetTest.assert (encEv ev1 < 32)
  NondetTest.assert (decEv (encEv ev1) = ev1)
  let f1 ← nondet EventFdFlags
  let f2 ← nondet EventFdFlags
  NondetTest.assert ((encEfd f1 == encEfd f2) = (f1 == f2))
  NondetTest.assert (encEfd f1 < 8)
  NondetTest.assert (encEv { pollin := true } = 1 ∧ encEv { pollout := true } = 2 ∧
    encEv { pollerr := true } = 4 ∧ encEv { pollhup := true } = 8 ∧ encEv { pollnval := true } = 16)
  NondetTest.assert (encEfd { nonblock := true, cloexec := false } = 1 ∧
    encEfd { cloexec := true } = 2 ∧ encEfd { cloexec := false, semaphore := true } = 4)
  NondetTest.assert (validTs { sec := 0, nsec := 0 } = true)
  NondetTest.assert (validTs { sec := 5, nsec := 999999999 } = true)
  NondetTest.assert (validTs { sec := -1, nsec := 0 } = false)
  NondetTest.assert (validTs { sec := 0, nsec := 1000000000 } = false)
  let pair := encReq #[(10, ev1), (20, ev2)]
  NondetTest.assert (pair.1 = #[10, 20] ∧ pair.2.size = 2 ∧ decRev pair.2 = #[ev1, ev2])
  NondetTest.assert (defEfd = { nonblock := false, cloexec := true, semaphore := false } ∧
    defTs = { sec := 0, nsec := 0 })
  NondetTest.assert (isZeroTs { sec := 0, nsec := 0 } = true ∧
    isZeroTs { sec := 1, nsec := 0 } = false ∧ isZeroTs { sec := 0, nsec := 1 } = false)
  NondetTest.assert (EFD_MAX_COUNT = 0xfffffffffffffffe ∧ MAX_POLL_NFDS = 1048576 ∧ NANOS_PER_SEC = 1000000000)
  let ev3 ← nondet PollEvents
  let emptyEnc := encReq #[]
  let triEnc := encReq #[(10, ev1), (20, ev2), (30, ev3)]
  NondetTest.assert (emptyEnc.1 = #[] ∧ emptyEnc.2.size = 0 ∧ decRev emptyEnc.2 = #[] ∧
    triEnc.1 = #[10, 20, 30] ∧ triEnc.2.size = 3 ∧ decRev triEnc.2 = #[ev1, ev2, ev3])

/-- `ppoll` rejects any invalid `Timespec` (`sec < 0` or `nsec >= 1_000_000_000`) or `entries.size > MAX_POLL_NFDS` (both with `some` timeout and `none`) with `Errno.EINVAL` and leaves state unchanged. -/
def test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval
    {S fd : Type} {runner} [NondetTest runner]
    (ops : PollOpsM (StateM S) fd) : runner Unit := do
  let s₀ ← nondet S
  let entries ← nondet (Array (fd × PollEvents))
  let badTs ← nondet Timespec
  assume (Timespec.isValid badTs = false)
  let hugeEntries ← nondet (Array (fd × PollEvents))
  assume (hugeEntries.size > MAX_POLL_NFDS)
  NondetTest.assert ((ops.ppoll entries (some badTs)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.ppoll #[] (some badTs)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.ppoll hugeEntries (some { sec := 0, nsec := 0 })).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.ppoll hugeEntries none).run s₀ = (.error Errno.EINVAL, s₀))

/-- `eventfd2` and `ppoll` distinguish zero-initialized (`POLLOUT` only) vs positive-initialized (`POLLIN | POLLOUT`) `eventfd` descriptors, return empty `revents` on zero timeout when unready, reject infinite unready wait with `EINTR` rather than spurious empty `revents`, and evaluate duplicate FD entries independently. -/
def test_poll_ops_eventfdReadinessAndTimeouts
    {S fd : Type} {runner} [NondetTest runner]
    (ops : PollOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rEmpty, sE) := (ops.ppoll #[] (some { sec := 0, nsec := 0 })).run s₀
  NondetTest.assert (rEmpty = .ok #[] ∧ sE = s₀)
  let (r0, s₁) := (ops.eventfd2 0 { nonblock := true, cloexec := true }).run s₀
  match r0 with
  | .error _ => NondetTest.assert False
  | .ok e0 =>
    let (r5, s₂) := (ops.eventfd2 5 { nonblock := true, cloexec := true, semaphore := true }).run s₁
    match r5 with
    | .error _ => NondetTest.assert False
    | .ok e5 =>
      let bothEv : PollEvents := { pollin := true, pollout := true }
      let (rBoth, s₃) := (ops.ppoll #[(e0, bothEv), (e5, bothEv)] (some { sec := 0, nsec := 0 })).run s₂
      NondetTest.assert (rBoth = .ok #[{ pollout := true }, { pollin := true, pollout := true }] ∧ s₃ = s₂)
      let (rZeroTo, s₄) := (ops.ppoll #[(e0, { pollin := true })] (some { sec := 0, nsec := 0 })).run s₃
      NondetTest.assert (rZeroTo = .ok #[{}] ∧ s₄ = s₃)
      let (rSomeTo, s₅) := (ops.ppoll #[(e0, { pollin := true })] (some { sec := 0, nsec := 5000 })).run s₄
      NondetTest.assert (rSomeTo = .ok #[{}] ∧ s₅ = s₄)
      let (rInfUnready, _) := (ops.ppoll #[(e0, { pollin := true })] none).run s₅
      NondetTest.assert (rInfUnready = .error Errno.EINTR)
      let (rInfReady, s₆) := (ops.ppoll #[(e5, { pollin := true })] none).run s₅
      NondetTest.assert (rInfReady = .ok #[{ pollin := true }] ∧ s₆ = s₅)
      let (rDup, _) := (ops.ppoll #[(e5, { pollin := true }), (e5, { pollout := true }), (e5, {})]
        (some { sec := 0, nsec := 0 })).run s₆
      NondetTest.assert (rDup = .ok #[{ pollin := true }, { pollout := true }, {}])

/-- `PollState` checks `EBADF` before `UInt64.max` `EINVAL` in `eventfdAdd`, tracks `EFD_MAX_COUNT` saturation and `EFD_SEMAPHORE` step-by-1 vs reset-to-0 consumption, `LeanFdBox` close (`EBADF`), output-only `POLLERR`/`POLLHUP`, and kernel `POLLNVAL`. -/
def test_poll_state_counterSemaphoreCloseAndOutputFlags
    {runner} [NondetTest runner]
    (ops : PollOpsM (StateM PollState) HandleId := modelOps) : runner Unit := do
  let s₀ := PollState.initial
  NondetTest.assert (PollState.eventfdAdd s₀ 99 0xffffffffffffffff = .error Errno.EBADF)
  let (rNorm, s₁) := (ops.eventfd2 2 { nonblock := true, cloexec := true, semaphore := false }).run s₀
  let (rSem, s₂) := (ops.eventfd2 2 { nonblock := true, cloexec := true, semaphore := true }).run s₁
  match rNorm, rSem with
  | .ok hNorm, .ok hSem =>
    NondetTest.assert (PollState.eventfdAdd s₂ hNorm 0xffffffffffffffff = .error Errno.EINVAL)
    match PollState.eventfdAdd s₂ hNorm (EFD_MAX_COUNT - 2) with
    | .error _ => NondetTest.assert False
    | .ok sMax =>
      NondetTest.assert (PollState.eventfdAdd sMax hNorm 1 = .error Errno.EAGAIN)
      let (rSat, _) := (ops.ppoll #[(hNorm, { pollin := true, pollout := true })] (some {})).run sMax
      NondetTest.assert (rSat = .ok #[{ pollin := true, pollout := false }])
      match PollState.eventfdConsume sMax hNorm with
      | .error _ => NondetTest.assert False
      | .ok (vNorm, sDrained) =>
        NondetTest.assert (vNorm = EFD_MAX_COUNT)
        NondetTest.assert (PollState.eventfdConsume sDrained hNorm = .error Errno.EAGAIN)
        let (rAfterDrain, _) := (ops.ppoll #[(hNorm, { pollin := true, pollout := true })] (some {})).run sDrained
        NondetTest.assert (rAfterDrain = .ok #[{ pollin := false, pollout := true }])
        match PollState.eventfdConsume sDrained hSem with
        | .error _ => NondetTest.assert False
        | .ok (vSem1, sSem1) =>
          NondetTest.assert (vSem1 = 1)
          let (rSemStillIn, _) := (ops.ppoll #[(hSem, { pollin := true })] (some {})).run sSem1
          NondetTest.assert (rSemStillIn = .ok #[{ pollin := true }])
          match PollState.eventfdConsume sSem1 hSem with
          | .error _ => NondetTest.assert False
          | .ok (vSem2, sSem0) =>
            NondetTest.assert (vSem2 = 1)
            let (rSemEmpty, _) := (ops.ppoll #[(hSem, { pollin := true })] (some {})).run sSem0
            NondetTest.assert (rSemEmpty = .ok #[{ pollin := false }])
            let (hEp, sEp) := PollState.registerDesc sSem0 { kind := .endpoint false false true true }
            let (hInv, sInv) := PollState.registerDesc sEp { kind := .invalidOsFd }
            let (rOutOnly, _) := (ops.ppoll #[(hEp, {}), (hInv, {})] (some {})).run sInv
            NondetTest.assert (rOutOnly = .ok #[{ pollerr := true, pollhup := true }, { pollnval := true }])
            match PollState.closeHandle sInv hNorm with
            | .error _ => NondetTest.assert False
            | .ok sClosed =>
              let (rClosed, _) := (ops.ppoll #[(hNorm, { pollin := true })] (some {})).run sClosed
              NondetTest.assert (rClosed = .error Errno.EBADF)
  | _, _ => NondetTest.assert False

/-- `Model.allowedStep` rejects invalid-timeout success, `EINVAL` on empty valid `ppoll`, duplicate handle allocation, closed-FD success, mismatched `revents`, and spurious empty return on `timeout = none`, while permitting `RLIMIT_NOFILE` `EINVAL` when `entries.size > 0` and transient OS errnos. -/
def test_poll_model_allowedStep_invariants
    {runner} [NondetTest runner]
    (step : PollState → PollReq → PollOutcome → Option PollState := allowedStep) : runner Unit := do
  let s0 := PollState.initial
  NondetTest.assert ((step s0 (.ppoll #[] (some { sec := -1, nsec := 0 })) (.polled #[])).isNone)
  NondetTest.assert ((step s0 (.ppoll #[] (some { sec := -1, nsec := 0 })) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.ppoll #[] (some { sec := 0, nsec := 1000000000 })) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.ppoll #[] (some {})) (.err Errno.EINVAL)).isNone)
  NondetTest.assert ((step s0 (.ppoll #[(0, { pollin := true })] (some {})) (.polled #[{}])).isNone)
  NondetTest.assert ((step s0 (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EBADF)).isSome)
  NondetTest.assert ((step s0 (.eventfd2 0 {}) (.err Errno.EINVAL)).isNone)
  NondetTest.assert ((step s0 (.eventfd2 0 {}) (.err Errno.EMFILE)).isSome)
  match step s0 (.eventfd2 0 { nonblock := true, cloexec := true }) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.eventfd2 1 {}) (.opened 0)).isNone)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EINVAL)).isSome)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollin := true })] none) (.polled #[{}])).isNone)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollin := true })] none) (.err Errno.EINTR)).isSome)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollin := true })] (some {})) (.polled #[{}])).isSome)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollout := true })] none) (.polled #[{ pollout := true }])).isSome)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollout := true })] (some {})) (.polled #[{}])).isNone)
    NondetTest.assert ((step s1 (.ppoll #[(0, { pollout := true })] (some {})) (.polled #[])).isNone)

/-- `PollState.softNofile?` restricts `ppoll` `EINVAL` to `nfds > lim` (rejecting spurious `EINVAL` below `lim` and `.polled` above `lim`), and `ambientSeccomp` permits safe seccomp errnos (`1..4095 \ {EFAULT}`) iff `reachesKernelPollSyscall` holds. -/
def test_poll_model_softNofileAndAmbientSeccomp
    {runner} [NondetTest runner]
    (step : PollState → PollReq → PollOutcome → Option PollState := allowedStep) : runner Unit := do
  let s0 := PollState.initial
  match step s0 (.eventfd2 0 { nonblock := true, cloexec := true }) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    let sLim : PollState := { s1 with softNofile? := some 2 }
    NondetTest.assert ((step sLim (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EINVAL)).isNone)
    NondetTest.assert ((step sLim (.ppoll #[(0, {}), (0, {}), (0, {})] (some {})) (.err Errno.EINVAL)).isSome)
    NondetTest.assert ((step sLim (.ppoll #[(0, {}), (0, {}), (0, {})] (some {})) (.polled #[{}, {}, {}])).isNone)
    let sSec := s0.withOuterSeccomp
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err Errno.EPERM)).isSome)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err Errno.EACCES)).isSome)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err Errno.ENOSYS)).isSome)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err 4095)).isSome)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err Errno.EFAULT)).isNone)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err 0)).isNone)
    NondetTest.assert ((step sSec (.eventfd2 0 {}) (.err 4096)).isNone)
    NondetTest.assert ((step sSec (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EPERM)).isNone)
    NondetTest.assert ((step sSec (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EBADF)).isSome)
    NondetTest.assert ((step sSec (.ppoll #[] (some { sec := -1, nsec := 0 })) (.err Errno.EPERM)).isNone)
    let s1Sec := s1.withOuterSeccomp
    NondetTest.assert ((step s1Sec (.ppoll #[(0, { pollin := true })] (some {})) (.err Errno.EPERM)).isSome)

/-- Deterministic `stepPollCore s req none` output is universally accepted by `allowedStep` (`modelOps` soundness) for any fresh `nextHid` state. -/
def test_poll_model_stepCoreSound
    {runner} [NondetTest runner]
    (step : PollState → PollReq → PollOutcome → Option PollState := allowedStep) : runner Unit := do
  let s ← nondet PollState
  let req ← nondet PollReq
  let out ← nondet PollOutcome
  let s' ← nondet PollState
  assume (assocGet s.fds s.nextHid = none)
  assume (stepPollCore s req none = some (out, s'))
  NondetTest.assert (step s req out = some s')

/-- `Internal.mkPollOpsM` faithfully encodes `EventFdFlags.toBits`, `encodePollRequests`, `hasTimeout` (`0` vs `1`), `Timespec` fields, `EIO` length checks, and `decodePollRevents`, propagating every `Errno` unchanged. -/
def test_poll_mkPollOps_encodesAndDelegates
    {runner} [NondetTest runner]
    (mkOps : PosixPollOpsM Id Nat → PollOpsM Id Nat) : runner Unit := do
  let rawPpoll ← nondet (Array Nat → ByteArray → UInt8 → UInt64 → UInt32 → Except Errno ByteArray)
  let rawEfd ← nondet (UInt32 → UInt32 → Except Errno Nat)
  let entries ← nondet (Array (Nat × PollEvents))
  assume (entries.size ≤ MAX_POLL_NFDS)
  let ts ← nondet Timespec
  assume (ts.isValid = true)
  let initval ← nondet UInt32
  let flags ← nondet EventFdFlags
  let raw : PosixPollOpsM Id Nat := { ppoll := rawPpoll, eventfd2 := rawEfd }
  let ops := mkOps raw
  let (fds, reqBytes) := encodePollRequests entries
  let expectedNone : Except Errno (Array PollEvents) :=
    match rawPpoll fds reqBytes 0 0 0 with
    | .error e => .error e
    | .ok revBytes =>
      if revBytes.size != entries.size then .error Errno.EIO
      else .ok (decodePollRevents revBytes)
  let expectedSome : Except Errno (Array PollEvents) :=
    match rawPpoll fds reqBytes 1 ts.sec.toUInt64 ts.nsec with
    | .error e => .error e
    | .ok revBytes =>
      if revBytes.size != entries.size then .error Errno.EIO
      else .ok (decodePollRevents revBytes)
  NondetTest.assert (ops.eventfd2 initval flags = rawEfd initval flags.toBits)
  NondetTest.assert (ops.ppoll entries none = expectedNone)
  NondetTest.assert (ops.ppoll entries (some ts) = expectedSome)

/-- `Poll.defaultOps` is constructed via `Internal.mkPollOpsM`, and top-level `Poll.ppoll` and `Poll.eventfd2` delegate directly to `defaultOps` with exact default `timeout = none` and `cloexec = true` arguments. -/
def test_poll_interface_defaultOpsWiring
    {m : Type → Type} {fd : Type} {runner} [NondetTest runner]
    (mkOps : PosixPollOpsM m fd → PollOpsM m fd)
    (ops : PollOpsM m fd)
    (ppollFn : Array (fd × PollEvents) → Option Timespec → m (Except Errno (Array PollEvents)))
    (ppollDefault : Array (fd × PollEvents) → m (Except Errno (Array PollEvents)))
    (eventfd2Fn : UInt32 → EventFdFlags → m (Except Errno fd))
    (eventfd2Default : m (Except Errno fd)) : runner Unit := do
  let fds ← nondet (Array (fd × PollEvents))
  let timeout ← nondet (Option Timespec)
  let initval ← nondet UInt32
  let flags ← nondet EventFdFlags
  NondetTest.assert (∃ raw : PosixPollOpsM m fd, ops = mkOps raw)
  NondetTest.assert (ppollFn fds timeout = ops.ppoll fds timeout)
  NondetTest.assert (ppollDefault fds = ops.ppoll fds none)
  NondetTest.assert (eventfd2Fn initval flags = ops.eventfd2 initval flags)
  NondetTest.assert (eventfd2Default = ops.eventfd2 0 { nonblock := false, cloexec := true, semaphore := false })

end LeanSwe.LinuxSyscall.Poll
