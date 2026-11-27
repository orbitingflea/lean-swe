import LeanSwe.LinuxSyscall.TimeRand.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.TimeRand`

Defines the pure `timespecToMs` model, raw C-ABI wire decoders and single-step
relation (`RawTimeRandReq`, `RawTimeRandOut`, `execRawStep`, `allowedRawStep`,
`rawHealthyModelOps`), and package-level single-step entry points
(`execPkgStep`, `allowedPkgStep`) over `HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.TimeRand.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Pure behavior model of `LeanSwe.LinuxSyscall.TimeRand.timespecToMs`. -/
def timespecToMs (ts : Timespec) : Nat :=
  ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000

/-- Decode a portable raw `ClockId` wire tag (`0 = realtime`, `1 = monotonic`). -/
def decodeRawClockId? : UInt32 → Option ClockId
  | 0 => some .realtime
  | 1 => some .monotonic
  | _ => none

/-- Decode a portable raw `abstime` byte (`0 = false`, `1 = true`). -/
def decodeRawAbstime? : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- Decode a portable 3-bit `GrndFlags` mask (`0..7`). -/
def decodeRawGrndFlags? (bits : UInt32) : Option GrndFlags :=
  if bits < 8 then
    some { nonblock := (bits &&& 1) != 0
           random := (bits &&& 2) != 0
           insecure := (bits &&& 4) != 0 }
  else
    none

/-- Single-step request sum for `PosixTimeRandOpsM` C-ABI syscall hooks. -/
inductive RawTimeRandReq where
  /-- Raw `clock_gettime(clkRaw)`. -/
  | clock_gettime (clkRaw : UInt32)
  /-- Raw `clock_nanosleep(clkRaw, absRaw, sec, nsec)`. -/
  | clock_nanosleep (clkRaw : UInt32) (absRaw : UInt8) (sec : Int64) (nsec : UInt32)
  /-- Raw `getrandom(len, flagsBits)`. -/
  | getrandom (len : UInt32) (flagsBits : UInt32)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Single-step output sum for `PosixTimeRandOpsM` C-ABI syscall hooks. -/
inductive RawTimeRandOut where
  /-- Succeeded returning `Unit`. -/
  | unit
  /-- Succeeded returning raw `(sec, nsec)` pair. -/
  | rawTimespec (sec : Int64) (nsec : UInt32)
  /-- Succeeded returning `ByteArray`. -/
  | bytes (data : ByteArray)
  /-- Failed with Linux `Errno`. -/
  | err (errno : Errno)
  deriving Repr, BEq, Inhabited

/-- Decode an `Except Errno (Int64 × UInt32)` into `RawTimeRandOut`. -/
def outcomeOfRawGettime : Except Errno (Int64 × UInt32) → RawTimeRandOut
  | .ok (sec, nsec) => .rawTimespec sec nsec
  | .error e => .err e

/-- Decode an `Except Errno Unit` into `RawTimeRandOut`. -/
def outcomeOfRawUnit : Except Errno Unit → RawTimeRandOut
  | .ok () => .unit
  | .error e => .err e

/-- Decode an `Except Errno ByteArray` into `RawTimeRandOut`. -/
def outcomeOfRawBytes : Except Errno ByteArray → RawTimeRandOut
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Convert a `RawTimeRandOut` into its domain `TimeRandOutcome`. -/
def toModelOutcome : RawTimeRandOut → TimeRandOutcome
  | .unit => .unit
  | .rawTimespec sec nsec => .timespec { sec := sec, nsec := nsec }
  | .bytes bs => .bytes bs
  | .err e => .err e

/-- Execute one `RawTimeRandReq` against a `PosixTimeRandOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : PosixTimeRandOpsM (StateM W)) :
    RawTimeRandReq → StateM W RawTimeRandOut
  | .clock_gettime clkRaw => outcomeOfRawGettime <$> raw.clock_gettime clkRaw
  | .clock_nanosleep clkRaw absRaw sec nsec =>
    outcomeOfRawUnit <$> raw.clock_nanosleep clkRaw absRaw sec nsec
  | .getrandom len flagsBits => outcomeOfRawBytes <$> raw.getrandom len flagsBits

/-- Allowed single-step relation for `PosixTimeRandOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawTimeRandReq) (out : RawTimeRandOut)
    (env' : HealthyEnv) : Prop :=
  match req with
  | .clock_gettime clkRaw =>
    match decodeRawClockId? clkRaw with
    | some clk => healthyStep env (.clock_gettime clk) (toModelOutcome out) = some env'
    | none => out = .err Errno.EINVAL ∧ env' = env
  | .clock_nanosleep clkRaw absRaw sec nsec =>
    match decodeRawClockId? clkRaw, decodeRawAbstime? absRaw with
    | some clk, some abstime =>
      healthyStep env (.clock_nanosleep clk abstime { sec := sec, nsec := nsec })
        (toModelOutcome out) = some env'
    | _, _ => out = .err Errno.EINVAL ∧ env' = env
  | .getrandom len flagsBits =>
    match decodeRawGrndFlags? flagsBits with
    | some flags => healthyStep env (.getrandom len flags) (toModelOutcome out) = some env'
    | none => out = .err Errno.EINVAL ∧ env' = env

/-- Reference `PosixTimeRandOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : PosixTimeRandOpsM (StateM HealthyEnv) :=
  { clock_gettime := fun clkRaw =>
      match decodeRawClockId? clkRaw with
      | some clk => do
        match ← healthyModelOps.clock_gettime clk with
        | .ok ts => return .ok (ts.sec, ts.nsec)
        | .error e => return .error e
      | none => pure (.error Errno.EINVAL)
    clock_nanosleep := fun clkRaw absRaw sec nsec =>
      match decodeRawClockId? clkRaw, decodeRawAbstime? absRaw with
      | some clk, some abstime =>
        healthyModelOps.clock_nanosleep clk abstime { sec := sec, nsec := nsec }
      | _, _ => pure (.error Errno.EINVAL)
    getrandom := fun len flagsBits =>
      match decodeRawGrndFlags? flagsBits with
      | some flags => healthyModelOps.getrandom len flags
      | none => pure (.error Errno.EINVAL) }

/-- Execute one `TimeRandReq` against a `TimeRandOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : TimeRandOpsM (StateM W)) (req : TimeRandReq) :
    StateM W TimeRandOutcome :=
  execTimeRandReq ops req

/-- Allowed single-step relation for `TimeRandOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Capability-parametric return family `m (Except Errno Nat)` of `TimeRand.monoNowMs`. -/
abbrev MonoNowMsAct (m : Type → Type) : Type :=
  m (Except Errno Nat)

/-- Execute `TimeRand.monoNowMs` inside `StateM W`. -/
def execMonoNowMs {W : Type} (act : MonoNowMsAct (StateM W)) (_ : Unit) :
    StateM W (Except Errno Nat) :=
  act

/-- Relational single-step postcondition for `TimeRand.monoNowMs` over `HealthyEnv`. -/
def allowedMonoNowMs (env : HealthyEnv) (_ : Unit) (out : Except Errno Nat)
    (env' : HealthyEnv) : Prop :=
  ∃ ts : Timespec,
    out = .ok (timespecToMs ts) ∧
    healthyStep env (.clock_gettime .monotonic) (.timespec ts) = some env'

/-- Capability-parametric function family `Nat → Option Nat → m (Except Errno (Bool × Nat))` of `TimeRand.checkTimedOut`. -/
abbrev CheckTimedOutFn (m : Type → Type) : Type :=
  Nat → Option Nat → m (Except Errno (Bool × Nat))

/-- Pure deadline comparison `(expired, remainingMs)` from `(startMs, timeoutMs, nowMs)`. -/
def checkTimedOutFromNow (startMs timeoutMs nowMs : Nat) : Bool × Nat :=
  let elapsed := nowMs - startMs
  if elapsed ≥ timeoutMs then (true, 0) else (false, timeoutMs - elapsed)

/-- Execute `TimeRand.checkTimedOut` on `(startMs, timeoutMs?)` inside `StateM W`. -/
def execCheckTimedOut {W : Type} (fn : CheckTimedOutFn (StateM W)) (req : Nat × Option Nat) :
    StateM W (Except Errno (Bool × Nat)) :=
  fn req.1 req.2

/-- Relational single-step postcondition for `TimeRand.checkTimedOut` over `HealthyEnv`. -/
def allowedCheckTimedOut (env : HealthyEnv) (req : Nat × Option Nat)
    (out : Except Errno (Bool × Nat)) (env' : HealthyEnv) : Prop :=
  match req.2 with
  | none => env.wf = true ∧ out = .ok (false, 0) ∧ env' = env
  | some timeoutMs =>
    ∃ ts : Timespec,
      out = .ok (checkTimedOutFromNow req.1 timeoutMs (timespecToMs ts)) ∧
      healthyStep env (.clock_gettime .monotonic) (.timespec ts) = some env'

/-- Capability-parametric function family `Nat → m Unit` of `TimeRand.sleepMonoMs`. -/
abbrev SleepMonoMsFn (m : Type → Type) : Type :=
  Nat → m Unit

/-- Clamped relative `CLOCK_MONOTONIC` `Timespec` constructed by `TimeRand.sleepMonoMs`. -/
def sleepMonoTimespec (ms : Nat) : Timespec :=
  let clampedSec := Nat.min (ms / 1000) MAX_TIMESPEC_SEC
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

/-- Execute `TimeRand.sleepMonoMs` on `ms` inside `StateM W`. -/
def execSleepMonoMs {W : Type} (fn : SleepMonoMsFn (StateM W)) (ms : Nat) :
    StateM W Unit :=
  fn ms

/-- Relational single-step postcondition for `TimeRand.sleepMonoMs` over `HealthyEnv` (succeeds advancing `CLOCK_MONOTONIC` or returns early on `EINTR` decrementing `eintrBudget`). -/
def allowedSleepMonoMs (env : HealthyEnv) (ms : Nat) (_ : Unit)
    (env' : HealthyEnv) : Prop :=
  healthyStep env (.clock_nanosleep .monotonic false (sleepMonoTimespec ms)) .unit = some env' ∨
  healthyStep env (.clock_nanosleep .monotonic false (sleepMonoTimespec ms)) (.err Errno.EINTR) = some env'

end LeanSwe.LinuxSyscall.TimeRand.Model
