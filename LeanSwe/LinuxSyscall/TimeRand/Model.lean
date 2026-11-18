import LeanSwe.LinuxSyscall.TimeRand.Types

namespace LeanSwe.LinuxSyscall.TimeRand

open LeanSwe.LinuxSyscall

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- One syscall request in a `TimeRand` world-model trace (covers all 3 curated syscalls). -/
inductive TimeRandReq where
  /-- `clock_gettime(clk)`. -/
  | clock_gettime (clk : ClockId)
  /-- `clock_nanosleep(clk, abstime, req)`. -/
  | clock_nanosleep (clk : ClockId) (abstime : Bool) (req : Timespec)
  /-- `getrandom(len, flags)`. -/
  | getrandom (len : UInt32) (flags : GrndFlags)
  deriving Repr, BEq

/-- Decoded syscall return value observed at the `TimeRand` world-model boundary. -/
inductive TimeRandOutcome where
  /-- Succeeded returning `Unit` (`clock_nanosleep`). -/
  | unit
  /-- Succeeded returning a `Timespec` (`clock_gettime`). -/
  | timespec (ts : Timespec)
  /-- Succeeded returning a `ByteArray` (`getrandom`). -/
  | bytes (data : ByteArray)
  /-- Failed with Linux `Errno` (`e ≠ EFAULT`). -/
  | err (errno : Errno)
  deriving Repr, BEq

/-- Executable stateful world model for the 3 curated Linux `TimeRand` syscalls (`clock_gettime`, `clock_nanosleep`, `getrandom`). -/
structure TimeRandState where
  /-- Monotonic clock lower bound in nanoseconds (`CLOCK_MONOTONIC`), non-decreasing across all observations and succeeding monotonic sleeps. -/
  monoLowerBoundNs : Nat := 0
  /-- Simulated `CLOCK_REALTIME` reading in signed nanoseconds since the Unix epoch (used by deterministic `modelOps`; unconstrained in `allowedStep`). -/
  realtimeNs : Int := 0
  /-- Whether the kernel CRNG has completed initial seeding (`false` permits `EAGAIN` on `GRND_NONBLOCK` without `GRND_INSECURE`; transitions permanently to `true` once a non-`insecure` `getrandom` succeeds). -/
  crngReady : Bool := false
  /-- Count of succeeding `getrandom` reads observed so far (seeds distinct deterministic byte blocks in `modelOps`). -/
  entropyDraws : Nat := 0
  /-- Whether an ambient outer `seccomp` filter (`SECCOMP_RET_ERRNO`) may preempt any `TimeRand` syscall before argument validation (`EFAULT` excluded). -/
  ambientSeccomp : Bool := false
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Initial `TimeRandState` before any monotonic observation (`monoLowerBoundNs = 0`, `crngReady = false` so early-boot `EAGAIN` is also permitted until first non-`insecure` `getrandom` success, `ambientSeccomp = false`). -/
def TimeRandState.initial (realtimeNs : Int := 0) (crngReady : Bool := false) : TimeRandState :=
  { monoLowerBoundNs := 0
    realtimeNs := realtimeNs
    crngReady := crngReady
    entropyDraws := 0
    ambientSeccomp := false }

/-- Enable ambient outer `seccomp` `SECCOMP_RET_ERRNO` preemption on a `TimeRandState` (safe filters have `1 ≤ data ≤ 4095 ∧ data ≠ EFAULT`: `SECCOMP_RET_ERRNO | 0` spoofs `rc = 0` fake success without executing the syscall, and `SECCOMP_RET_ERRNO | EFAULT` triggers the repo-wide fail-loud C-pointer `abort()` invariant in `Common/Types.lean:48`). -/
def TimeRandState.withOuterSeccomp (s : TimeRandState := TimeRandState.initial) : TimeRandState :=
  { s with ambientSeccomp := true }

/-- Deterministic byte-stream generator producing exact `len` bytes seeded by `(drawIdx, pos)` for `modelOps.getrandom`. -/
def deterministicEntropyList (drawIdx : Nat) : Nat → Nat → List UInt8
  | 0, _ => []
  | rem + 1, pos =>
    let mixed : Nat :=
      if pos < 4 then
        (drawIdx / (256 ^ pos)) % 256
      else
        (drawIdx * 131 + pos * 17 + 0x5A) % 256
    UInt8.ofNat mixed :: deterministicEntropyList drawIdx rem (pos + 1)

/-- Construct a deterministic `ByteArray` of exact length `len` for draw `drawIdx`. -/
def deterministicEntropyBytes (drawIdx len : Nat) : ByteArray :=
  ByteArray.mk (deterministicEntropyList drawIdx len 0).toArray

/-- Return `true` iff `gotLen` is a legal Linux `getrandom(2)` byte count for requested `len` (`0` when `len == 0`, exact `len` when `1 ≤ len ≤ 256`, and `1 ≤ gotLen ≤ min len MAX_READ_BYTES` when `len > 256`). -/
def validGetrandomResultLen (len : UInt32) (gotLen : Nat) : Bool :=
  let cap := min len.toNat MAX_READ_BYTES.toNat
  if cap == 0 then
    gotLen == 0
  else if cap ≤ GETRANDOM_EXACT_MAX then
    gotLen == cap
  else
    1 ≤ gotLen && gotLen ≤ cap

/-- Core Linux `7.1+` relational step checker without ambient `seccomp` `SECCOMP_RET_ERRNO` preemption. -/
def allowedStepCore (s : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome) : Option TimeRandState :=
  match req with
  | .clock_gettime clk =>
    match out with
    | .timespec ts =>
      match clk with
      | .realtime =>
        if ts.hasValidNsec then
          some s
        else
          none
      | .monotonic =>
        if ts.isValid && s.monoLowerBoundNs ≤ ts.toNanosNat then
          some { s with monoLowerBoundNs := ts.toNanosNat }
        else
          none
    | .err e =>
      match clk with
      | .realtime =>
        if (Timespec.ofEpochNanos? s.realtimeNs).isNone && e == Errno.EIO then some s else none
      | .monotonic =>
        if (Timespec.ofNanosNat? s.monoLowerBoundNs).isNone && e == Errno.EIO then some s else none
    | _ => none
  | .clock_nanosleep clk abstime reqTs =>
    if !reqTs.isValid then
      match out with
      | .err e => if e == Errno.EINVAL then some s else none
      | _ => none
    else
      match out with
      | .unit =>
        match clk with
        | .realtime => some s
        | .monotonic =>
          let reqNs := reqTs.toNanosNat
          let nextMono := if abstime then max s.monoLowerBoundNs reqNs else s.monoLowerBoundNs + reqNs
          some { s with monoLowerBoundNs := nextMono }
      | .err e =>
        if e == Errno.EINTR then some s else none
      | _ => none
  | .getrandom len flags =>
    if flags.isInvalid then
      match out with
      | .err e => if e == Errno.EINVAL then some s else none
      | _ => none
    else
      match out with
      | .bytes got =>
        if validGetrandomResultLen len got.data.size then
          some { s with
            crngReady := s.crngReady || !flags.insecure
            entropyDraws := s.entropyDraws + 1 }
        else
          none
      | .err e =>
        let allowEagain := !s.crngReady && flags.nonblock && !flags.insecure && e == Errno.EAGAIN
        let allowEintr := !s.crngReady && !flags.nonblock && !flags.insecure && e == Errno.EINTR
        if allowEagain || allowEintr then
          some s
        else
          none
      | _ => none

/-- Relational step checker for `LeanSwe.LinuxSyscall.TimeRand` (`some s'` iff `out` is a legal Linux `7.1+` outcome for `req` in state `s`). -/
def allowedStep (s : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome) : Option TimeRandState :=
  if s.ambientSeccomp then
    match out with
    | .err e =>
      if e != Errno.EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095 then
        some s
      else
        allowedStepCore s req out
    | _ => allowedStepCore s req out
  else
    allowedStepCore s req out

/-- Convert an `Except Errno Timespec` result into its `TimeRandOutcome`. -/
def outcomeOfTimespec : Except Errno Timespec → TimeRandOutcome
  | .ok ts => .timespec ts
  | .error e => .err e

/-- Convert an `Except Errno Unit` result into its `TimeRandOutcome`. -/
def outcomeOfUnit : Except Errno Unit → TimeRandOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert an `Except Errno ByteArray` result into its `TimeRandOutcome`. -/
def outcomeOfBytes : Except Errno ByteArray → TimeRandOutcome
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Deterministic pure `StateM TimeRandState` implementation of `TimeRandOpsM` whose transitions are universally sound with respect to `allowedStep`. -/
def modelOps : TimeRandOpsM (StateM TimeRandState) :=
  { clock_gettime := fun clk => do
      let s ← get
      match clk with
      | .realtime =>
        match Timespec.ofEpochNanos? s.realtimeNs with
        | some ts => return .ok ts
        | none => return .error Errno.EIO
      | .monotonic =>
        match Timespec.ofNanosNat? s.monoLowerBoundNs with
        | some ts =>
          set { s with monoLowerBoundNs := ts.toNanosNat }
          return .ok ts
        | none => return .error Errno.EIO
    clock_nanosleep := fun clk abstime reqTs => do
      let s ← get
      if !reqTs.isValid then
        return .error Errno.EINVAL
      match clk with
      | .realtime =>
        return .ok ()
      | .monotonic =>
        let reqNs := reqTs.toNanosNat
        let nextMono := if abstime then max s.monoLowerBoundNs reqNs else s.monoLowerBoundNs + reqNs
        set { s with monoLowerBoundNs := nextMono }
        return .ok ()
    getrandom := fun len flags => do
      let s ← get
      if flags.isInvalid then
        return .error Errno.EINVAL
      if !s.crngReady && flags.nonblock && !flags.insecure then
        return .error Errno.EAGAIN
      let cap := min len.toNat MAX_READ_BYTES.toNat
      let bs := deterministicEntropyBytes s.entropyDraws cap
      set { s with
        crngReady := s.crngReady || !flags.insecure
        entropyDraws := s.entropyDraws + 1 }
      return .ok bs }

end LeanSwe.LinuxSyscall.TimeRand
