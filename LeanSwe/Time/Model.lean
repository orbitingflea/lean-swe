import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.Time.Types

/-!
# Pure Behavior Model for `LeanSwe.Time`

Defines the pure specification of monotonic duration/deadline helpers, UTC ISO
8601 and `YYYY-MM-DD` formatting/parsing, and the capability-parametric
single-step refinement contracts (`TimeOpsStepReq`/`TimeOpsStepOut` over
`TimeRandOpsM` and `PkgStepReq`/`PkgStepOut` over `TimeOpsM`) over
`LeanSwe.LinuxSyscall.TimeRand.HealthyEnv`.
-/

namespace LeanSwe.Time.Model

open LeanSwe.LinuxSyscall.TimeRand
  (TimeRandOpsM TimeRandReq TimeRandOutcome HealthyEnv
   MIN_TIMESPEC_SEC_INT MAX_TIMESPEC_NANOS
   execTimeRandReq healthyStep)

/-- Pure behavior model of `LeanSwe.Time.elapsedDuration`. -/
def elapsedDuration (startMono stopMono : Nat) : Std.Time.Duration :=
  if startMono ≤ stopMono then
    Std.Time.Duration.ofNanoseconds (Std.Time.Nanosecond.Offset.ofNat (stopMono - startMono))
  else
    0

/-- Pure behavior model of `LeanSwe.Time.deadlineNanos`. -/
def deadlineNanos (startMono : Nat) (limit : Std.Time.Duration) : Nat :=
  if limit.toNanoseconds.val ≥ 0 then startMono + limit.toNanoseconds.val.toNat else startMono

/-- Pure behavior model of `LeanSwe.Time.isMonoExpired`. -/
def isMonoExpired (nowMono deadlineMono : Nat) : Bool :=
  decide (deadlineMono ≤ nowMono)

/-- Convert a `Std.Time.Duration` to rounded-up sleep milliseconds. -/
def sleepDurationMs (d : Std.Time.Duration) : Nat :=
  if d.toNanoseconds.val ≤ 0 then 0
  else (d.toNanoseconds.val.toNat + 999999) / 1000000

/-- Convert `n % 10` into an ASCII decimal digit character `'0'..'9'`. -/
def digitChar (n : Nat) : Char :=
  Char.ofNat ('0'.toNat + (n % 10))

/-- Return `true` iff `c` is an ASCII decimal digit `'0'..'9'`. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Convert an ASCII decimal digit character `'0'..'9'` into `0..9`. -/
def digitVal (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Format `n % 100` as 2 zero-padded ASCII decimal characters. -/
def twoDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 10), digitChar n]

/-- Format `n % 10000` as 4 zero-padded ASCII decimal characters. -/
def fourDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 1000), digitChar (n / 100), digitChar (n / 10), digitChar n]

/-- Format `n % 1_000_000_000` as 9 zero-padded ASCII decimal characters. -/
def nineDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 100000000), digitChar (n / 10000000), digitChar (n / 1000000),
   digitChar (n / 100000), digitChar (n / 10000), digitChar (n / 1000),
   digitChar (n / 100), digitChar (n / 10), digitChar n]

/-- Format a proleptic Gregorian year as zero-padded characters. -/
def formatYearChars (y : Int) : List Char :=
  if 0 ≤ y ∧ y ≤ 9999 then
    fourDigitsChars y.toNat
  else if 0 ≤ y then
    (Nat.repr y.toNat).toList
  else
    let mag := (-y).toNat
    '-' :: (if mag ≤ 9999 then fourDigitsChars mag else (Nat.repr mag).toList)

/-- Decompose a UTC `Std.Time.Timestamp` into `(date, hour, minute, second, nanosecond)`. -/
def utcSplitTimestamp (ts : Std.Time.Timestamp) : Std.Time.PlainDate × Nat × Nat × Nat × Nat :=
  let ns := ts.toNanosecondsSinceUnixEpoch.val
  let sec := ns.ediv 1000000000
  let nano := (ns.emod 1000000000).toNat
  let day := sec.ediv 86400
  let sod := (sec.emod 86400).toNat
  (Std.Time.PlainDate.ofEpochDay (Std.Time.Day.Offset.ofInt day),
   sod / 3600, (sod % 3600) / 60, sod % 60, nano)

/-- Format a `Std.Time.PlainDate` as a `YYYY-MM-DD` character list. -/
def formatUtcDateChars (d : Std.Time.PlainDate) : List Char :=
  formatYearChars d.year.toInt ++ '-' :: twoDigitsChars d.month.val.toNat ++ '-' :: twoDigitsChars d.day.val.toNat

/-- Pure behavior model of `LeanSwe.Time.formatUtcIso8601`. -/
def formatUtcIso8601 (ts : Std.Time.Timestamp) : String :=
  let (d, hh, mm, ss, nano) := utcSplitTimestamp ts
  String.ofList (formatUtcDateChars d ++
    'T' :: twoDigitsChars hh ++ ':' :: twoDigitsChars mm ++ ':' :: twoDigitsChars ss ++
    '.' :: nineDigitsChars nano ++ ['Z'])

/-- Pure behavior model of `LeanSwe.Time.formatUtcCompact`. -/
def formatUtcCompact (ts : Std.Time.Timestamp) : String :=
  let (d, hh, mm, ss, _) := utcSplitTimestamp ts
  String.ofList (formatYearChars d.year.toInt ++
    twoDigitsChars d.month.val.toNat ++ twoDigitsChars d.day.val.toNat ++
    'T' :: twoDigitsChars hh ++ twoDigitsChars mm ++ twoDigitsChars ss ++ ['Z'])

/-- Pure behavior model of `LeanSwe.Time.formatUtcDate`. -/
def formatUtcDate (d : Std.Time.PlainDate) : String :=
  String.ofList (formatUtcDateChars d)

/-- Parse 2 ASCII digits into `0..99`. -/
def twoDigitsNat? (c1 c2 : Char) : Option Nat :=
  if isAsciiDigit c1 && isAsciiDigit c2 then
    some (digitVal c1 * 10 + digitVal c2)
  else
    none

/-- Parse 4 ASCII digits into `0..9999`. -/
def fourDigitsNat? (c1 c2 c3 c4 : Char) : Option Nat :=
  if isAsciiDigit c1 && isAsciiDigit c2 && isAsciiDigit c3 && isAsciiDigit c4 then
    some (((digitVal c1 * 10 + digitVal c2) * 10 + digitVal c3) * 10 + digitVal c4)
  else
    none

/-- Pop 1 character from the front of `cs`. -/
def pop1? : List Char → Option (Char × List Char)
  | c :: rest => some (c, rest)
  | [] => none

/-- Pop 2 characters from the front of `cs`. -/
def pop2? : List Char → Option (Char × Char × List Char)
  | c1 :: c2 :: rest => some (c1, c2, rest)
  | _ => none

/-- Pop 2 ASCII digits from the front of `cs` and decode into `0..99`. -/
def popTwoDigitsNat? (cs : List Char) : Option (Nat × List Char) :=
  match pop2? cs with
  | some (c1, c2, rest) =>
    match twoDigitsNat? c1 c2 with
    | some n => some (n, rest)
    | none => none
  | none => none

/-- Pop 4 ASCII digits from the front of `cs` and decode into `0..9999`. -/
def popFourDigitsNat? (cs : List Char) : Option (Nat × List Char) :=
  match pop2? cs with
  | some (c1, c2, r1) =>
    match pop2? r1 with
    | some (c3, c4, rest) =>
      match fourDigitsNat? c1 c2 c3 c4 with
      | some n => some (n, rest)
      | none => none
    | none => none
  | none => none

/-- Parse a validated `YYYY-MM-DD` (or `-YYYY-MM-DD`) calendar date prefix from `cs`. -/
def parseDatePrefix (neg : Bool) (cs : List Char) : Except TimeError (Std.Time.PlainDate × List Char) :=
  match popFourDigitsNat? cs with
  | none => .error { kind := .invalidFormat, message := "expected 4-digit year in YYYY-MM-DD date" }
  | some (yNat, r1) =>
    match pop1? r1 with
    | some (s1, r2) =>
      if s1 != '-' then
        .error { kind := .invalidFormat, message := "expected '-' after year in YYYY-MM-DD date" }
      else
        match popTwoDigitsNat? r2 with
        | none => .error { kind := .invalidFormat, message := "expected 2-digit month in YYYY-MM-DD date" }
        | some (mNat, r3) =>
          match pop1? r3 with
          | some (s2, r4) =>
            if s2 != '-' then
              .error { kind := .invalidFormat, message := "expected '-' after month in YYYY-MM-DD date" }
            else
              match popTwoDigitsNat? r4 with
              | none => .error { kind := .invalidFormat, message := "expected 2-digit day in YYYY-MM-DD date" }
              | some (dNat, rest) =>
                if neg && yNat == 0 then
                  .error { kind := .invalidFormat, message := "negative zero year -0000 is invalid" }
                else if hm : 1 ≤ mNat ∧ mNat ≤ 12 then
                  if hd : 1 ≤ dNat ∧ dNat ≤ 31 then
                    let yInt : Int := if neg then -(Int.ofNat yNat) else Int.ofNat yNat
                    match Std.Time.PlainDate.ofYearMonthDay?
                        (Std.Time.Year.Offset.ofInt yInt)
                        (Std.Time.Month.Ordinal.ofNat mNat hm)
                        (Std.Time.Day.Ordinal.ofNat dNat hd) with
                    | some date => .ok (date, rest)
                    | none => .error { kind := .invalidFormat, message := "invalid calendar day for month/year" }
                  else
                    .error { kind := .invalidFormat, message := "day out of range 01..31" }
                else
                  .error { kind := .invalidFormat, message := "month out of range 01..12" }
          | none => .error { kind := .invalidFormat, message := "expected '-DD' in YYYY-MM-DD date" }
    | none => .error { kind := .invalidFormat, message := "expected '-MM-DD' in YYYY-MM-DD date" }

/-- Parse a leading `YYYY-MM-DD` (or `-YYYY-MM-DD`) calendar date from `cs`. -/
def parseDateHead (cs : List Char) : Except TimeError (Std.Time.PlainDate × List Char) :=
  match cs with
  | c :: rest => if c == '-' then parseDatePrefix true rest else parseDatePrefix false cs
  | [] => parseDatePrefix false []

/-- Pure behavior model of `LeanSwe.Time.parseUtcDate`. -/
def parseUtcDate (raw : String) : Except TimeError Std.Time.PlainDate := do
  let (d, rest) ← parseDateHead raw.toList
  match rest with
  | [] => .ok d
  | _ :: _ => .error { kind := .invalidFormat, message := "unexpected trailing characters after YYYY-MM-DD date" }

/-- Split leading ASCII decimal digits from `cs`. -/
def splitLeadingDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isAsciiDigit c then
      let (ds, tl) := splitLeadingDigits rest
      (c :: ds, tl)
    else
      ([], c :: rest)

/-- Right-pad `1..9` fractional second digits with zeros to nanoseconds `0..999_999_999`. -/
def fracDigitsToNanos9 : Nat → Nat → List Char → Nat
  | 0, acc, _ => acc
  | k + 1, acc, c :: rest => fracDigitsToNanos9 k (acc * 10 + digitVal c) rest
  | k + 1, acc, [] => fracDigitsToNanos9 k (acc * 10) []

/-- Parse an ISO 8601 timezone designator (`Z`, `±HH:MM`, or `±HH:MM:SS`) into signed offset seconds. -/
def parseOffsetSeconds (cs : List Char) : Except TimeError Int :=
  match pop1? cs with
  | none => .error { kind := .invalidFormat, message := "expected ISO 8601 timezone suffix (Z or ±HH:MM)" }
  | some (c0, r0) =>
    if r0.isEmpty then
      if c0 == 'Z' || c0 == 'z' then .ok 0
      else .error { kind := .invalidFormat, message := "expected ISO 8601 timezone suffix (Z or ±HH:MM)" }
    else if c0 != '+' && c0 != '-' then
      .error { kind := .invalidFormat, message := "invalid sign in ISO 8601 UTC offset" }
    else
      match popTwoDigitsNat? r0 with
      | none => .error { kind := .invalidFormat, message := "invalid hour digits in ISO 8601 UTC offset" }
      | some (hh, r1) =>
        match pop1? r1 with
        | some (sep1, r2) =>
          if sep1 != ':' then
            .error { kind := .invalidFormat, message := "expected ':' in ISO 8601 UTC offset" }
          else
            match popTwoDigitsNat? r2 with
            | none => .error { kind := .invalidFormat, message := "invalid minute digits in ISO 8601 UTC offset" }
            | some (mm, r3) =>
              match r3 with
              | [] =>
                if hh ≤ 23 && mm ≤ 59 then
                  let mag : Int := Int.ofNat (hh * 3600 + mm * 60)
                  .ok (if c0 == '-' then -mag else mag)
                else
                  .error { kind := .invalidFormat, message := "ISO 8601 UTC offset hour/minute out of range" }
              | sep2 :: r4 =>
                if sep2 != ':' then
                  .error { kind := .invalidFormat, message := "unexpected trailing characters in ISO 8601 UTC offset" }
                else
                  match popTwoDigitsNat? r4 with
                  | some (ss, []) =>
                    if hh ≤ 23 && mm ≤ 59 && ss ≤ 59 then
                      let mag : Int := Int.ofNat (hh * 3600 + mm * 60 + ss)
                      .ok (if c0 == '-' then -mag else mag)
                    else
                      .error { kind := .invalidFormat, message := "ISO 8601 UTC offset hour/minute/second out of range" }
                  | _ =>
                    .error { kind := .invalidFormat, message := "invalid seconds in ISO 8601 UTC offset" }
        | none => .error { kind := .invalidFormat, message := "expected ':MM' in ISO 8601 UTC offset" }

/-- Pure behavior model of `LeanSwe.Time.parseUtcIso8601`. -/
def parseUtcIso8601 (raw : String) : Except TimeError Std.Time.Timestamp := do
  let (date, afterDate) ← parseDateHead raw.toList
  match pop1? afterDate with
  | none => .error { kind := .invalidFormat, message := "expected THH:MM:SS time and timezone in ISO 8601 timestamp" }
  | some (sep, r0) =>
    if sep != 'T' && sep != 't' then
      .error { kind := .invalidFormat, message := "expected 'T' separator in ISO 8601 timestamp" }
    else
      match popTwoDigitsNat? r0 with
      | none => .error { kind := .invalidFormat, message := "invalid hour digits in ISO 8601 timestamp" }
      | some (hh, r1) =>
        match pop1? r1 with
        | some (c1, r2) =>
          if c1 != ':' then
            .error { kind := .invalidFormat, message := "expected ':' after hour in ISO 8601 timestamp" }
          else
            match popTwoDigitsNat? r2 with
            | none => .error { kind := .invalidFormat, message := "invalid minute digits in ISO 8601 timestamp" }
            | some (mm, r3) =>
              match pop1? r3 with
              | some (c2, r4) =>
                if c2 != ':' then
                  .error { kind := .invalidFormat, message := "expected ':' after minute in ISO 8601 timestamp" }
                else
                  match popTwoDigitsNat? r4 with
                  | none => .error { kind := .invalidFormat, message := "invalid second digits in ISO 8601 timestamp" }
                  | some (ss, afterSec) =>
                    if !(hh ≤ 23 && mm ≤ 59 && ss ≤ 59) then
                      .error { kind := .invalidFormat, message := "ISO 8601 time field out of range" }
                    else do
                      let (nano, zoneCs) ←
                        match afterSec with
                        | dot :: fracStart =>
                          if dot == '.' then
                            let (ds, zc) := splitLeadingDigits fracStart
                            if ds.isEmpty || ds.length > 9 then
                              .error { kind := .invalidFormat, message := "ISO 8601 fractional seconds must have 1..9 digits" }
                            else
                              .ok (fracDigitsToNanos9 9 0 ds, zc)
                          else
                            .ok (0, dot :: fracStart)
                        | [] =>
                          .ok (0, [])
                      let offSec ← parseOffsetSeconds zoneCs
                      let wallSec : Int := date.toEpochDay.val * 86400 + Int.ofNat (hh * 3600 + mm * 60 + ss)
                      let utcSec : Int := wallSec - offSec
                      let totalNs : Int := utcSec * 1000000000 + Int.ofNat nano
                      .ok (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (Std.Time.Nanosecond.Offset.ofInt totalNs))
              | none => .error { kind := .invalidFormat, message := "expected ':SS' in ISO 8601 timestamp" }
        | none => .error { kind := .invalidFormat, message := "expected ':MM:SS' in ISO 8601 timestamp" }

/-- Pure behavior model of `LeanSwe.Time.utcDateOfTimestamp`. -/
def utcDateOfTimestamp (ts : Std.Time.Timestamp) : Std.Time.PlainDate :=
  (utcSplitTimestamp ts).1

/-- Pure behavior model of `LeanSwe.Time.timestampOfUtcDate`. -/
def timestampOfUtcDate (d : Std.Time.PlainDate) : Std.Time.Timestamp :=
  Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
    (Std.Time.Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))

/-- Well-formedness guard on `HealthyEnv` for `LeanSwe.Time` single-step refinement. -/
def healthyWf (env : HealthyEnv) : Bool :=
  HealthyEnv.wf env

/-- Execute a `TimeRandReq` against a `TimeRandOpsM (StateM W)` capability bundle. -/
def execRawStep {W : Type} (sys : TimeRandOpsM (StateM W)) (req : TimeRandReq) :
    StateM W TimeRandOutcome :=
  execTimeRandReq sys req

/-- Allowed `TimeRand` transition relation lifted from `LeanSwe.LinuxSyscall.TimeRand.healthyStep`. -/
def allowedRawStep (env : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Single-step request sum covering all `TimeOpsM` primitives. -/
inductive TimeOpsStepReq where
  /-- Read UTC wall-clock timestamp (`TimeOpsM.nowTimestamp`). -/
  | nowTimestamp
  /-- Read monotonic clock in nanoseconds (`TimeOpsM.monoNanosNow`). -/
  | monoNanosNow
  /-- Sleep `ms` milliseconds (`TimeOpsM.sleep`). -/
  | sleep (ms : UInt32)
  deriving Repr, DecidableEq, Inhabited

/-- Single-step output sum for `TimeOpsStepReq`. -/
inductive TimeOpsStepOut where
  /-- Timestamp returned by `TimeOpsM.nowTimestamp`. -/
  | nowTimestamp (ts : Std.Time.Timestamp)
  /-- Nanoseconds returned by `TimeOpsM.monoNanosNow`. -/
  | monoNanosNow (ns : Nat)
  /-- Unit outcome of `TimeOpsM.sleep`. -/
  | sleep
  deriving Repr, DecidableEq, Inhabited

/-- Execute one `TimeOpsStepReq` against an arbitrary `TimeOpsM (StateM W)`. -/
def execTimeOpsStep {W : Type} (ops : TimeOpsM (StateM W)) :
    TimeOpsStepReq → StateM W TimeOpsStepOut
  | .nowTimestamp => .nowTimestamp <$> ops.nowTimestamp
  | .monoNanosNow => .monoNanosNow <$> ops.monoNanosNow
  | .sleep ms => do ops.sleep ms; pure .sleep

/-- Shared monotonic sleep postcondition relating pre/post `HealthyEnv` for `sleepNs` nanoseconds. -/
def sleepEnvRel (env : HealthyEnv) (sleepNs : Nat) (env' : HealthyEnv) : Prop :=
  env'.wf = true ∧
  env.state.monoLowerBoundNs ≤ env'.state.monoLowerBoundNs ∧
  env'.state.realtimeNs = env.state.realtimeNs ∧
  env'.state.crngReady = env.state.crngReady ∧
  env'.state.entropyDraws = env.state.entropyDraws ∧
  env'.eintrBudget ≤ env.eintrBudget ∧
  (env'.eintrBudget = env.eintrBudget →
    min MAX_TIMESPEC_NANOS (env.state.monoLowerBoundNs + sleepNs) ≤ env'.state.monoLowerBoundNs)

/-- Allowed single-step relation for `TimeOpsM` over `HealthyEnv`. -/
def allowedTimeOpsStep (env : HealthyEnv) (req : TimeOpsStepReq) (out : TimeOpsStepOut)
    (env' : HealthyEnv) : Prop :=
  match req, out with
  | .nowTimestamp, .nowTimestamp ts =>
    MIN_TIMESPEC_SEC_INT * 1000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ Int.ofNat MAX_TIMESPEC_NANOS ∧
    env' = env
  | .monoNanosNow, .monoNanosNow ns =>
    min env.state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ns ∧
    ns ≤ MAX_TIMESPEC_NANOS ∧
    env'.wf = true ∧
    env'.state.monoLowerBoundNs = max env.state.monoLowerBoundNs ns ∧
    env'.state.realtimeNs = env.state.realtimeNs ∧
    env'.state.crngReady = env.state.crngReady ∧
    env'.state.entropyDraws = env.state.entropyDraws ∧
    env'.eintrBudget = env.eintrBudget
  | .sleep ms, .sleep =>
    sleepEnvRel env (ms.toNat * 1000000) env'
  | _, _ => False

/-- Finite pure action passed to `TimeApiM.measure` during single-step refinement. -/
inductive MeasureAction where
  /-- Return `val` immediately without sleeping. -/
  | pureNat (val : Nat)
  /-- Sleep `ms` milliseconds via `api.sleepMs`, then return `val`. -/
  | sleepMsNat (ms val : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return value of a `MeasureAction`. -/
def measureActionResult : MeasureAction → Nat
  | .pureNat val => val
  | .sleepMsNat _ val => val

/-- Execute a `MeasureAction` against a `TimeApiM (StateM W)`. -/
def execMeasureAction {W : Type} (api : TimeApiM (StateM W)) : MeasureAction → StateM W Nat
  | .pureNat val => pure val
  | .sleepMsNat ms val => do api.sleepMs ms; pure val

/-- Public effectful request sum covering all 5 effectful `TimeApiM` operations. -/
inductive PkgStepReq where
  /-- Read UTC wall-clock timestamp (`TimeApiM.nowTimestamp`). -/
  | nowTimestamp
  /-- Read monotonic clock in nanoseconds (`TimeApiM.monoNanosNow`). -/
  | monoNanosNow
  /-- Sleep `ms` milliseconds (`TimeApiM.sleepMs`). -/
  | sleepMs (ms : Nat)
  /-- Sleep for duration `d` (`TimeApiM.sleepDuration`). -/
  | sleepDuration (d : Std.Time.Duration)
  /-- Measure `act` elapsed monotonic duration (`TimeApiM.measure`). -/
  | measure (act : MeasureAction)
  deriving Repr, DecidableEq, Inhabited

/-- Public effectful output sum for `PkgStepReq`. -/
inductive PkgStepOut where
  /-- Result of `TimeApiM.nowTimestamp`. -/
  | nowTimestamp (ts : Std.Time.Timestamp)
  /-- Result of `TimeApiM.monoNanosNow`. -/
  | monoNanosNow (ns : Nat)
  /-- Result of `TimeApiM.sleepMs` or `TimeApiM.sleepDuration`. -/
  | unit
  /-- Result of `TimeApiM.measure`. -/
  | measured (res : Nat × Std.Time.Duration)
  deriving Repr, DecidableEq, Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `TimeApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : TimeApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .nowTimestamp => .nowTimestamp <$> api.nowTimestamp
  | .monoNanosNow => .monoNanosNow <$> api.monoNanosNow
  | .sleepMs ms => do api.sleepMs ms; pure .unit
  | .sleepDuration d => do api.sleepDuration d; pure .unit
  | .measure act => .measured <$> api.measure (execMeasureAction api act)

/-- Allowed single-step relation for `TimeApiM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : PkgStepReq) (out : PkgStepOut)
    (env' : HealthyEnv) : Prop :=
  match req, out with
  | .nowTimestamp, .nowTimestamp ts =>
    MIN_TIMESPEC_SEC_INT * 1000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ Int.ofNat MAX_TIMESPEC_NANOS ∧
    env' = env
  | .monoNanosNow, .monoNanosNow ns =>
    min env.state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ns ∧
    ns ≤ MAX_TIMESPEC_NANOS ∧
    env'.wf = true ∧
    env'.state.monoLowerBoundNs = max env.state.monoLowerBoundNs ns ∧
    env'.state.realtimeNs = env.state.realtimeNs ∧
    env'.state.crngReady = env.state.crngReady ∧
    env'.state.entropyDraws = env.state.entropyDraws ∧
    env'.eintrBudget = env.eintrBudget
  | .sleepMs ms, .unit =>
    sleepEnvRel env (ms * 1000000) env'
  | .sleepDuration d, .unit =>
    sleepEnvRel env (sleepDurationMs d * 1000000) env'
  | .measure act, .measured (val, elapsed) =>
    val = measureActionResult act ∧
    0 ≤ elapsed.toNanoseconds.val ∧
    env'.wf = true ∧
    env.state.monoLowerBoundNs ≤ env'.state.monoLowerBoundNs ∧
    env'.state.realtimeNs = env.state.realtimeNs ∧
    env'.state.crngReady = env.state.crngReady ∧
    env'.state.entropyDraws = env.state.entropyDraws ∧
    env'.eintrBudget ≤ env.eintrBudget
  | _, _ => False

end LeanSwe.Time.Model
