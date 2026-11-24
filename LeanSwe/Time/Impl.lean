import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Time.Types

namespace LeanSwe.Time.Internal

open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM Timespec)

/-- Alias of `LeanSwe.Time.MAX_EINTR_RETRIES` (`8`). -/
abbrev MAX_EINTR_RETRIES : Nat := LeanSwe.Time.MAX_EINTR_RETRIES

/-- Structurally bounded `TIMER_ABSTIME` `clock_nanosleep` loop on `CLOCK_MONOTONIC`, retrying only `Errno.EINTR` against the fixed absolute `target` deadline. -/
def sleepAbstimeRetry {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (target : Timespec) : Nat → m Unit
  | 0 => do
    let _ ← sys.clock_nanosleep .monotonic true target
    pure ()
  | fuel' + 1 => do
    match ← sys.clock_nanosleep .monotonic true target with
    | .ok () => pure ()
    | .error e =>
      if e == Errno.EINTR then
        sleepAbstimeRetry sys target fuel'
      else
        pure ()

/-- Convert a millisecond count `ms` into a valid relative `Timespec` (`sec = ms / 1000`, `nsec = (ms % 1000) * 10^6`). -/
def relativeTimespecOfMs (ms : UInt32) : Timespec :=
  { sec := Int64.ofInt (Int.ofNat (ms.toNat / 1000))
    nsec := UInt32.ofNat ((ms.toNat % 1000) * 1000000) }

/-- Construct `TimeOpsM m` purely over `TimeRandOpsM m` (`CLOCK_REALTIME`, `CLOCK_MONOTONIC`, and `TIMER_ABSTIME` `clock_nanosleep` with bounded `EINTR` retry). -/
def mkTimeOps {m : Type → Type} [Monad m] (sys : TimeRandOpsM m) : TimeOpsM m :=
  { nowTimestamp := do
      match ← sys.clock_gettime .realtime with
      | .ok ts =>
        pure (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
          (Std.Time.Nanosecond.Offset.ofInt ts.toEpochNanos))
      | .error _ =>
        pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
    monoNanosNow := do
      match ← sys.clock_gettime .monotonic with
      | .ok ts =>
        pure (if decide (0 ≤ ts.sec.toInt) then ts.toNanosNat else 0)
      | .error _ =>
        pure 0
    sleep := fun ms =>
      if ms == 0 then
        pure ()
      else do
        let deltaNs : Nat := ms.toNat * 1000000
        match ← sys.clock_gettime .monotonic with
        | .ok nowTs =>
          if decide (0 ≤ nowTs.sec.toInt) then
            match Timespec.ofNanosNat? (nowTs.toNanosNat + deltaNs) with
            | some targetTs =>
              sleepAbstimeRetry sys targetTs MAX_EINTR_RETRIES
            | none =>
              let _ ← sys.clock_nanosleep .monotonic false (relativeTimespecOfMs ms)
              pure ()
          else
            let _ ← sys.clock_nanosleep .monotonic false (relativeTimespecOfMs ms)
            pure ()
        | .error _ =>
          let _ ← sys.clock_nanosleep .monotonic false (relativeTimespecOfMs ms)
          pure () }

/-- Sleep `ms` milliseconds via `ops.sleep`, splitting durations larger than `UInt32.max` into sequential `UInt32` chunks. -/
def sleepMs {m : Type → Type} [Monad m] (ops : TimeOpsM m) (ms : Nat) : m Unit :=
  if ms = 0 then
    pure ()
  else
    let chunkNat := min ms (UInt32.size - 1)
    do
      ops.sleep (UInt32.ofNat chunkNat)
      sleepMs ops (ms - chunkNat)
termination_by ms
decreasing_by
  have hpos : 0 < ms := Nat.pos_of_ne_zero ‹_›
  have hc : 0 < min ms (UInt32.size - 1) := Nat.lt_min.mpr ⟨hpos, by decide⟩
  omega

/-- Convert a `Std.Time.Duration` to sleep milliseconds (non-positive clamps to 0; positive sub-millisecond durations round up to 1 ms). -/
def sleepDurationMs (d : Std.Time.Duration) : Nat :=
  if d.toNanoseconds.val ≤ 0 then 0
  else (d.toNanoseconds.val.toNat + 999999) / 1000000

/-- Sleep for `d` via `sleepMs`, clamping non-positive durations to zero and rounding positive sub-millisecond durations up to at least 1 ms. -/
def sleepDuration {m : Type → Type} [Monad m] (ops : TimeOpsM m) (d : Std.Time.Duration) : m Unit :=
  sleepMs ops (sleepDurationMs d)

/-- Compute non-negative elapsed `Std.Time.Duration` between monotonic nanosecond readings `(startMono, stopMono)`. -/
def elapsedDuration (startMono stopMono : Nat) : Std.Time.Duration :=
  if startMono ≤ stopMono then
    Std.Time.Duration.ofNanoseconds (Std.Time.Nanosecond.Offset.ofNat (stopMono - startMono))
  else
    0

/-- Execute `act` and return its result alongside elapsed monotonic `Std.Time.Duration`. -/
def measure {m : Type → Type} [Monad m] (ops : TimeOpsM m) {α : Type} (act : m α) :
    m (α × Std.Time.Duration) := do
  let startMono ← ops.monoNanosNow
  let out ← act
  let stopMono ← ops.monoNanosNow
  pure (out, elapsedDuration startMono stopMono)

/-- Compute monotonic nanosecond deadline `startMono + max 0 limit.toNanoseconds`. -/
def deadlineNanos (startMono : Nat) (limit : Std.Time.Duration) : Nat :=
  if limit.toNanoseconds.val ≥ 0 then startMono + limit.toNanoseconds.val.toNat else startMono

/-- Return `true` iff `deadlineMono ≤ nowMono` given `(nowMono, deadlineMono)`. -/
def isMonoExpired (nowMono deadlineMono : Nat) : Bool :=
  decide (deadlineMono ≤ nowMono)

/-- Convert `n % 10` into an ASCII decimal digit character `'0'..'9'`. -/
def digitChar (n : Nat) : Char :=
  Char.ofNat ('0'.toNat + (n % 10))

/-- Return `true` iff `c` is an ASCII decimal digit `'0'..'9'`. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Convert an ASCII decimal digit character `'0'..'9'` into its numeric value `0..9`. -/
def digitVal (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Format `n % 100` as exactly 2 zero-padded ASCII decimal characters. -/
def twoDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 10), digitChar n]

/-- Format `n % 10000` as exactly 4 zero-padded ASCII decimal characters. -/
def fourDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 1000), digitChar (n / 100), digitChar (n / 10), digitChar n]

/-- Format `n % 1_000_000_000` as exactly 9 zero-padded ASCII decimal characters. -/
def nineDigitsChars (n : Nat) : List Char :=
  [digitChar (n / 100000000), digitChar (n / 10000000), digitChar (n / 1000000),
   digitChar (n / 100000), digitChar (n / 10000), digitChar (n / 1000),
   digitChar (n / 100), digitChar (n / 10), digitChar n]

/-- Format an integer proleptic Gregorian year as zero-padded characters (`YYYY` for `0..9999`, signed extended otherwise). -/
def formatYearChars (y : Int) : List Char :=
  if 0 ≤ y ∧ y ≤ 9999 then
    fourDigitsChars y.toNat
  else if 0 ≤ y then
    (Nat.repr y.toNat).toList
  else
    let mag := (-y).toNat
    '-' :: (if mag ≤ 9999 then fourDigitsChars mag else (Nat.repr mag).toList)

/-- Decompose a UTC `Std.Time.Timestamp` into `(date, hour, minute, second, nanosecond)` via Euclidean division. -/
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

/-- Format a `Std.Time.Timestamp` in UTC ISO 8601 (`YYYY-MM-DDTHH:MM:SS.nnnnnnnnnZ`). -/
def formatUtcIso8601 (ts : Std.Time.Timestamp) : String :=
  let (d, hh, mm, ss, nano) := utcSplitTimestamp ts
  String.ofList (formatUtcDateChars d ++
    'T' :: twoDigitsChars hh ++ ':' :: twoDigitsChars mm ++ ':' :: twoDigitsChars ss ++
    '.' :: nineDigitsChars nano ++ ['Z'])

/-- Format a `Std.Time.Timestamp` as compact UTC stamp `YYYYMMDDTHHMMSSZ`. -/
def formatUtcCompact (ts : Std.Time.Timestamp) : String :=
  let (d, hh, mm, ss, _) := utcSplitTimestamp ts
  String.ofList (formatYearChars d.year.toInt ++
    twoDigitsChars d.month.val.toNat ++ twoDigitsChars d.day.val.toNat ++
    'T' :: twoDigitsChars hh ++ twoDigitsChars mm ++ twoDigitsChars ss ++ ['Z'])

/-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
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

/-- Parse a strict `YYYY-MM-DD` date string into `Std.Time.PlainDate`. -/
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

/-- Right-pad `1..9` fractional second digits with zeros to a 9-digit nanosecond value `0..999_999_999`. -/
def fracDigitsToNanos9 : Nat → Nat → List Char → Nat
  | 0, acc, _ => acc
  | k + 1, acc, c :: rest => fracDigitsToNanos9 k (acc * 10 + digitVal c) rest
  | k + 1, acc, [] => fracDigitsToNanos9 k (acc * 10) []

/-- Parse an ISO 8601 timezone designator (`Z`, `±HH:MM`, or `±HH:MM:SS`) into signed UTC offset seconds. -/
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

/-- Parse an ISO 8601 timestamp string (with `Z` or `±HH:MM` offset, with or without `1..9` fractional nanosecond digits) into a UTC `Std.Time.Timestamp`. -/
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

/-- Convert a `Std.Time.Timestamp` to its UTC calendar `Std.Time.PlainDate`. -/
def utcDateOfTimestamp (ts : Std.Time.Timestamp) : Std.Time.PlainDate :=
  (utcSplitTimestamp ts).1

/-- Convert a UTC `Std.Time.PlainDate` to the midnight `Std.Time.Timestamp` at start of that UTC day. -/
def timestampOfUtcDate (d : Std.Time.PlainDate) : Std.Time.Timestamp :=
  Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
    (Std.Time.Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))

/-- Assemble a `TimeApiM m` record over a `TimeOpsM m` effect implementation. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : TimeOpsM m) : TimeApiM m :=
  { nowTimestamp := ops.nowTimestamp
    monoNanosNow := ops.monoNanosNow
    sleepMs := sleepMs ops
    sleepDuration := sleepDuration ops
    measure := measure ops
    elapsedDuration := elapsedDuration
    deadlineNanos := deadlineNanos
    isMonoExpired := isMonoExpired
    formatUtcIso8601 := formatUtcIso8601
    parseUtcIso8601 := parseUtcIso8601
    formatUtcCompact := formatUtcCompact
    formatUtcDate := formatUtcDate
    parseUtcDate := parseUtcDate
    utcDateOfTimestamp := utcDateOfTimestamp
    timestampOfUtcDate := timestampOfUtcDate }

/-- Deterministic `TimeOpsM (StateM FakeClock)` advancing `wall`, `monoNanos`, and `sleepLog` on `sleep`. -/
def fakeOps : TimeOpsM (StateM FakeClock) :=
  { nowTimestamp := do
      let s ← get
      pure s.wall
    monoNanosNow := do
      let s ← get
      pure s.monoNanos
    sleep := fun ms =>
      modify fun s =>
        { wall := s.wall + Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat ms.toNat)
          monoNanos := s.monoNanos + ms.toNat * 1000000
          sleepLog := s.sleepLog.push ms } }

/-- Deterministic `TimeApiM (StateM FakeClock)` backed by `fakeOps`. -/
def fakeApi : TimeApiM (StateM FakeClock) :=
  mkApiM fakeOps

end LeanSwe.Time.Internal
