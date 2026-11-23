import LeanSwe.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Poll.Types

namespace LeanSwe.LinuxSyscall.Poll

open LeanSwe.LinuxSyscall

export LeanSwe.LinuxSyscall (assocGet assocSetAux assocSet assocEraseAux assocErase)

/-- Logical descriptor kind tracked by `PollState` for `ppoll` readiness evaluation. -/
inductive PollDescKind where
  /-- Linux `eventfd` counter object (`counter > 0` -> `POLLIN`, `counter < EFD_MAX_COUNT` -> `POLLOUT`, `counter == UInt64.max` -> `POLLERR`). -/
  | eventfd (counter : UInt64) (flags : EventFdFlags)
  /-- Registered pipe, socket, or generic pollable endpoint with explicit readiness and output-only `POLLERR` / `POLLHUP` state. -/
  | endpoint (readable : Bool) (writable : Bool) (err : Bool := false) (hup : Bool := false)
  /-- Open `LeanFdBox` wrapper whose underlying OS descriptor was invalidated (`POLLNVAL` in `revents`). -/
  | invalidOsFd
  deriving Repr, DecidableEq, BEq

/-- Open descriptor entry in `PollState`. -/
structure PollDesc where
  /-- Descriptor kind and readiness state. -/
  kind : PollDescKind
  deriving Repr, DecidableEq, BEq

/-- Executable stateful world model for the 2 curated Linux `Poll` syscalls (`ppoll`, `eventfd2`). -/
structure PollState where
  /-- Open descriptor table mapping `HandleId` to `PollDesc`. -/
  fds : List (HandleId × PollDesc)
  /-- Next logical handle ID to allocate. -/
  nextHid : HandleId
  /-- Known soft `RLIMIT_NOFILE` limit when tracked by the harness (`none` = unknown). -/
  softNofile? : Option Nat := none
  /-- Whether an inherited safe outer `seccomp(SECCOMP_RET_ERRNO)` filter is active. -/
  ambientSeccomp : Bool := false
  deriving DecidableEq, BEq

private def formatPollFdsAux : List (HandleId × PollDesc) → Bool → String → String
  | [], _, acc => acc ++ "]"
  | (hid, desc) :: rest, isFirst, acc =>
    let sep := if isFirst then "" else ", "
    formatPollFdsAux rest false (acc ++ sep ++ "(" ++ toString hid ++ ", " ++ reprStr desc ++ ")")

instance : Repr PollState where
  reprPrec s _ :=
    Std.Format.text
      ("{ fds := " ++ formatPollFdsAux s.fds true "[" ++
       ", nextHid := " ++ toString s.nextHid ++
       ", softNofile? := " ++ reprStr s.softNofile? ++
       ", ambientSeccomp := " ++ toString s.ambientSeccomp ++ " }")

/-- Initial empty `PollState` with zero open handles. -/
def PollState.initial : PollState :=
  { fds := [], nextHid := 0, softNofile? := none, ambientSeccomp := false }

/-- Enable ambient outer `seccomp(SECCOMP_RET_ERRNO)` preemption on a `PollState`. -/
def PollState.withOuterSeccomp (s : PollState := PollState.initial) : PollState :=
  { s with ambientSeccomp := true }

instance : Inhabited PollState := ⟨PollState.initial⟩

/-- Compute exact Linux `revents` for a single open `PollDesc` given requested `reqEv` (`POLLERR`, `POLLHUP`, `POLLNVAL` are reported regardless of `reqEv`). -/
def computeDescRevents (desc : PollDesc) (reqEv : PollEvents) : PollEvents :=
  match desc.kind with
  | .eventfd counter _ =>
    { pollin := reqEv.pollin && counter > 0
      pollout := reqEv.pollout && counter < EFD_MAX_COUNT
      pollerr := counter == 0xffffffffffffffff
      pollhup := false
      pollnval := false }
  | .endpoint readable writable err hup =>
    { pollin := reqEv.pollin && readable
      pollout := reqEv.pollout && writable
      pollerr := err
      pollhup := hup
      pollnval := false }
  | .invalidOsFd =>
    { pollin := false
      pollout := false
      pollerr := false
      pollhup := false
      pollnval := true }

/-- Tail-recursive accumulator helper for `evalPollList`. -/
def evalPollListAux (s : PollState) :
    List (HandleId × PollEvents) → List PollEvents → Except Errno (List PollEvents)
  | [], acc => .ok acc.reverse
  | (hid, reqEv) :: rest, acc =>
    match assocGet s.fds hid with
    | none => .error Errno.EBADF
    | some desc => evalPollListAux s rest (computeDescRevents desc reqEv :: acc)

/-- Pin and evaluate `revents` for every `(hid, reqEv)` entry against `s.fds`, failing with `EBADF` if any `hid` is closed/absent (matching `LeanFdBox` pinning). -/
def evalPollList (s : PollState) (xs : List (HandleId × PollEvents)) : Except Errno (List PollEvents) :=
  evalPollListAux s xs []

/-- Close an open `HandleId` in `PollState` (returning `EBADF` if already closed/absent). -/
def PollState.closeHandle (s : PollState) (hid : HandleId) : Except Errno PollState :=
  match assocGet s.fds hid with
  | none => .error Errno.EBADF
  | some _ => .ok { s with fds := assocErase s.fds hid }

/-- Register an external pipe/socket/invalid descriptor in `PollState` at `s.nextHid`, returning `(hid, s')`. -/
def PollState.registerDesc (s : PollState) (desc : PollDesc) : HandleId × PollState :=
  let hid := s.nextHid
  (hid, { s with fds := assocSet s.fds hid desc, nextHid := hid + 1 })

/-- Simulate an 8-byte `eventfd` write (`delta > 0`, `delta != UInt64.max`) on `hid`, checking descriptor validity (`EBADF`, including `O_PATH`) before `UInt64.max` (`EINVAL`) and `EFD_MAX_COUNT` (`EAGAIN` when `nonblock`, `EINTR` otherwise). -/
def PollState.eventfdAdd (s : PollState) (hid : HandleId) (delta : UInt64) : Except Errno PollState :=
  match assocGet s.fds hid with
  | none => .error Errno.EBADF
  | some desc =>
    match desc.kind with
    | .invalidOsFd => .error Errno.EBADF
    | .eventfd counter flags =>
      if delta == 0xffffffffffffffff then .error Errno.EINVAL
      else if delta.toNat + counter.toNat > EFD_MAX_COUNT.toNat then
        if flags.nonblock then .error Errno.EAGAIN else .error Errno.EINTR
      else
        let next := UInt64.ofNat (counter.toNat + delta.toNat)
        .ok { s with fds := assocSet s.fds hid { kind := .eventfd next flags } }
    | .endpoint _ _ _ _ =>
      if delta == 0xffffffffffffffff then .error Errno.EINVAL else .error Errno.EINVAL

/-- Simulate an 8-byte `eventfd` read on `hid`, returning `EBADF` on `O_PATH` handles and honoring `EFD_NONBLOCK` and `EFD_SEMAPHORE`. -/
def PollState.eventfdConsume (s : PollState) (hid : HandleId) : Except Errno (UInt64 × PollState) :=
  match assocGet s.fds hid with
  | none => .error Errno.EBADF
  | some desc =>
    match desc.kind with
    | .invalidOsFd => .error Errno.EBADF
    | .eventfd counter flags =>
      if counter == 0 then
        if flags.nonblock then .error Errno.EAGAIN else .error Errno.EINTR
      else if flags.semaphore then
        let next := counter - 1
        .ok (1, { s with fds := assocSet s.fds hid { kind := .eventfd next flags } })
      else
        .ok (counter, { s with fds := assocSet s.fds hid { kind := .eventfd 0 flags } })
    | .endpoint _ _ _ _ => .error Errno.EINVAL

/-- Pure-Lean pre-syscall wrapper validation for `PollReq` matching `mkPollOpsM`. -/
def preCheckPoll : PollReq → Option Errno
  | .eventfd2 _ _ => none
  | .ppoll entries timeout =>
    let tsValid := match timeout with
      | none => true
      | some ts => ts.isValid
    if !tsValid || entries.size > MAX_POLL_NFDS then some Errno.EINVAL else none

/-- Returns `true` iff `req` passes both Lean wrapper validation and userspace `LeanFdBox` pinning, actually reaching a kernel syscall (`ppoll` or `eventfd2`). -/
def reachesKernelPollSyscall (s : PollState) : PollReq → Bool
  | .eventfd2 _ _ => true
  | .ppoll entries timeout =>
    (preCheckPoll (.ppoll entries timeout)).isNone &&
      (evalPollList s entries.toList).isOk

/-- Single-source-of-truth step core for `ppoll` and `eventfd2`: `obs? = none` produces the canonical `modelOps` outcome and next state; `obs? = some out` validates observed `out` for `allowedStep`. -/
def stepPollCore (s : PollState) (req : PollReq) (obs? : Option PollOutcome) :
    Option (PollOutcome × PollState) :=
  match req with
  | .eventfd2 initval flags =>
    let desc : PollDesc := { kind := .eventfd initval.toUInt64 flags }
    match obs? with
    | none =>
      let hid := s.nextHid
      some (.opened hid, { s with fds := assocSet s.fds hid desc, nextHid := hid + 1 })
    | some (.opened hid) =>
      if (assocGet s.fds hid).isSome then none
      else some (.opened hid, { s with fds := assocSet s.fds hid desc, nextHid := max s.nextHid (hid + 1) })
    | some (.err e) =>
      if Errno.isTransientOsErrno e || e == Errno.ENODEV then some (.err e, s) else none
    | some (.polled _) => none
  | .ppoll entries timeout =>
    match preCheckPoll (.ppoll entries timeout) with
    | some preErr =>
      match obs? with
      | none => some (.err preErr, s)
      | some (.err e) => if e == preErr then some (.err e, s) else none
      | some _ => none
    | none =>
      match evalPollList s entries.toList with
      | .error pinErr =>
        match obs? with
        | none => some (.err pinErr, s)
        | some (.err e) => if e == pinErr then some (.err e, s) else none
        | some _ => none
      | .ok revList =>
        let expected := revList.toArray
        let anyReady := revList.any (fun ev => !ev.isEmpty)
        let knownExceedsNofile : Bool := match s.softNofile? with
          | some lim => decide (entries.size > lim)
          | none => false
        let allowNofileEinval : Bool := match s.softNofile? with
          | some lim => decide (entries.size > lim)
          | none => decide (entries.size > 0)
        if knownExceedsNofile then
          match obs? with
          | none => some (.err Errno.EINVAL, s)
          | some (.err e) =>
            if e == Errno.EINVAL || Errno.isTransientOsErrno e then some (.err e, s) else none
          | some _ => none
        else
          match obs? with
          | none =>
            if !anyReady && timeout.isNone then some (.err Errno.EINTR, s)
            else some (.polled expected, s)
          | some (.polled got) =>
            if got.size != entries.size then none
            else if anyReady then
              if got == expected then some (.polled got, s) else none
            else
              match timeout with
              | none => none
              | some _ => if got == expected then some (.polled got, s) else none
          | some (.err e) =>
            if (allowNofileEinval && e == Errno.EINVAL) || Errno.isTransientOsErrno e then
              some (.err e, s)
            else none
          | some (.opened _) => none

/-- Relational step verifier for `ppoll` and `eventfd2`: returns `some s'` iff `out` is permitted from `s` on `req` on Linux `7.1+`. -/
def allowedStep (s : PollState) (req : PollReq) (out : PollOutcome) : Option PollState :=
  match (stepPollCore s req (some out)).map Prod.snd with
  | some s' => some s'
  | none =>
    if s.ambientSeccomp then
      match out with
      | .err e =>
        if Errno.isSafeSeccompErrno e && reachesKernelPollSyscall s req then some s else none
      | _ => none
    else none

/-- Deterministic executable `StateM PollState` reference implementation of `PollOpsM`, projected directly from `stepPollCore`. -/
def modelOps : PollOpsM (StateM PollState) HandleId :=
  { eventfd2 := fun initval flags => do
      let s ← get
      match stepPollCore s (.eventfd2 initval flags) none with
      | some (.opened hid, s') => set s'; return .ok hid
      | some (.err e, s') => set s'; return .error e
      | _ => return .error Errno.EINVAL
    ppoll := fun entries timeout => do
      let s ← get
      match stepPollCore s (.ppoll entries timeout) none with
      | some (.polled rev, s') => set s'; return .ok rev
      | some (.err e, s') => set s'; return .error e
      | _ => return .error Errno.EINVAL }

/-- Convert `Except Errno (Array PollEvents)` into `PollOutcome`. -/
def outcomeOfPolled : Except Errno (Array PollEvents) → PollOutcome
  | .ok rev => .polled rev
  | .error e => .err e

/-- Convert `Except Errno HandleId` into `PollOutcome`. -/
def outcomeOfOpened : Except Errno HandleId → PollOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Return `true` iff `out` is a curated catastrophic OS fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isCriticalFault : PollOutcome → Bool
  | .err e => Errno.isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `out` is an interrupted syscall outcome (`.err Errno.EINTR`). -/
def isEintrOutcome : PollOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy execution environment wrapping `PollState` with a finite `EINTR` interruption budget (`ambientSeccomp = false`). -/
structure HealthyEnv where
  /-- Underlying `Poll` world state. -/
  state : PollState := PollState.initial
  /-- Remaining bound on `EINTR` signal interruptions (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Initial healthy `Poll` environment with optional `eintrBudget`. -/
def HealthyEnv.initial (eintrBudget : Nat := 0) : HealthyEnv :=
  { state := PollState.initial, eintrBudget := eintrBudget }

/-- Return `true` iff `env` has no ambient `seccomp` `SECCOMP_RET_ERRNO` filter interception. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Poll`, excluding critical OS faults and ambient `seccomp` while bounding `EINTR` via `eintrBudget`. -/
def healthyStep (env : HealthyEnv) (req : PollReq) (out : PollOutcome) : Option HealthyEnv :=
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

/-- Execute one `PollReq` against a `PollOpsM m HandleId` capability bundle and decode its `PollOutcome`. -/
def execPollReq {m : Type → Type} [Monad m]
    (ops : PollOpsM m HandleId) : PollReq → m PollOutcome
  | .ppoll fds to? => outcomeOfPolled <$> ops.ppoll fds to?
  | .eventfd2 iv fl => outcomeOfOpened <$> ops.eventfd2 iv fl

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthyPollAt {W : Type} (proj : W → HealthyEnv)
    (ops : PollOpsM (StateM W) HandleId) : Prop :=
  ∀ (w : W) (req : PollReq),
    (proj w).wf = true →
    let (out, w') := (execPollReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Direct healthy-world refinement predicate specialized to `StateM HealthyEnv`. -/
abbrev RefinesHealthyPoll (ops : PollOpsM (StateM HealthyEnv) HandleId) : Prop :=
  RefinesHealthyPollAt id ops

end LeanSwe.LinuxSyscall.Poll
