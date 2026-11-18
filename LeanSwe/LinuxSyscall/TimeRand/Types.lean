import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.TimeRand

open LeanSwe.LinuxSyscall

/-- Nanoseconds per whole second (`1_000_000_000`, `NSEC_PER_SEC`). -/
def NSEC_PER_SEC : Nat := 1000000000

/-- Maximum signed 64-bit seconds value (`Int64.max = 2^63 - 1`). -/
def MAX_TIMESPEC_SEC : Nat := 9223372036854775807

/-- Minimum signed 64-bit seconds value (`Int64.min = -2^63`). -/
def MIN_TIMESPEC_SEC_INT : Int := -9223372036854775808

/-- Maximum non-negative nanosecond total representable in a valid `Timespec`. -/
def MAX_TIMESPEC_NANOS : Nat := MAX_TIMESPEC_SEC * NSEC_PER_SEC + (NSEC_PER_SEC - 1)

/-- Maximum `getrandom(2)` length (`256` bytes) guaranteed by Linux to complete without signal-induced partial reads once CRNG is ready. -/
def GETRANDOM_EXACT_MAX : Nat := 256

/-- Portable Linux clock identifier translated via `<time.h>` (`CLOCK_REALTIME`, `CLOCK_MONOTONIC`). -/
inductive ClockId where
  /-- System-wide UTC wall-clock time (`CLOCK_REALTIME`). -/
  | realtime
  /-- Monotonic non-decreasing clock since an unspecified boot epoch (`CLOCK_MONOTONIC`). -/
  | monotonic
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Encode `ClockId` into a portable tag (`0 = CLOCK_REALTIME`, `1 = CLOCK_MONOTONIC`) for `timerand_shim.c`. -/
def ClockId.toRaw : ClockId → UInt32
  | .realtime => 0
  | .monotonic => 1

/-- Portable Linux `struct timespec` representation (`tv_sec` in seconds, `tv_nsec` in nanoseconds). -/
structure Timespec where
  /-- Whole seconds (`tv_sec`). Must satisfy `0 ≤ sec` for `clock_nanosleep` requests and `CLOCK_MONOTONIC` readings. -/
  sec : Int64 := 0
  /-- Nanosecond offset (`tv_nsec`). Must satisfy `nsec < 1_000_000_000` (`NSEC_PER_SEC`). -/
  nsec : UInt32 := 0
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Return `true` iff `ts` satisfies Linux `timespec64_valid` (`0 ≤ tv_sec` and `tv_nsec < 1_000_000_000`). -/
def Timespec.isValid (ts : Timespec) : Bool :=
  decide (0 ≤ ts.sec.toInt) && ts.nsec.toNat < NSEC_PER_SEC

/-- Return `true` iff `ts.nsec < 1_000_000_000` (valid `CLOCK_REALTIME` reading even if `sec < 0`). -/
def Timespec.hasValidNsec (ts : Timespec) : Bool :=
  ts.nsec.toNat < NSEC_PER_SEC

/-- Convert a non-negative `Timespec` (`0 ≤ sec`) to total nanoseconds as `Nat`. -/
def Timespec.toNanosNat (ts : Timespec) : Nat :=
  ts.sec.toInt.toNat * NSEC_PER_SEC + ts.nsec.toNat

/-- Convert any `Timespec` (including negative `sec` before the Unix epoch) to signed nanoseconds `sec * 10^9 + nsec`. -/
def Timespec.toEpochNanos (ts : Timespec) : Int :=
  ts.sec.toInt * Int.ofNat NSEC_PER_SEC + Int.ofNat ts.nsec.toNat

/-- Construct a valid non-negative `Timespec` from total nanoseconds `ns`, returning `none` iff `ns / 10^9 > Int64.max`. -/
def Timespec.ofNanosNat? (ns : Nat) : Option Timespec :=
  let sNat := ns / NSEC_PER_SEC
  let nsRem := ns % NSEC_PER_SEC
  if sNat ≤ MAX_TIMESPEC_SEC then
    some { sec := Int64.ofInt (Int.ofNat sNat), nsec := UInt32.ofNat nsRem }
  else
    none

/-- Construct a `Timespec` with `nsec < 10^9` from signed epoch nanoseconds `ns`, returning `none` iff `sec` overflows `Int64`. -/
def Timespec.ofEpochNanos? (ns : Int) : Option Timespec :=
  let sInt := ns.ediv (Int.ofNat NSEC_PER_SEC)
  let nsRem := (ns.emod (Int.ofNat NSEC_PER_SEC)).toNat
  if decide (MIN_TIMESPEC_SEC_INT ≤ sInt ∧ sInt ≤ Int.ofNat MAX_TIMESPEC_SEC) then
    some { sec := Int64.ofInt sInt, nsec := UInt32.ofNat nsRem }
  else
    none

/-- Portable symbolic flags for Linux `getrandom(2)` translated via `<sys/random.h>`. -/
structure GrndFlags where
  /-- Return `EAGAIN` instead of blocking if kernel CRNG is not yet initialized (`GRND_NONBLOCK`, `0x0001`). -/
  nonblock : Bool := false
  /-- Legacy `/dev/random` flag (`GRND_RANDOM`, `0x0002`; rejected with `EINVAL` by Linux when combined with `insecure`). -/
  random : Bool := false
  /-- Return best-effort bytes even before CRNG init (`GRND_INSECURE`, `0x0004`; clears `GRND_NONBLOCK` in kernel, mutually exclusive with `random`). -/
  insecure : Bool := false
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Encode `GrndFlags` into a portable 3-bit mask decoded by `timerand_shim.c` (`bit 0 = nonblock`, `bit 1 = random`, `bit 2 = insecure`). -/
def GrndFlags.toBits (f : GrndFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.nonblock 0 ||| bit f.random 1 ||| bit f.insecure 2

/-- Return `true` iff Linux `getrandom(2)` rejects `f` with `EINVAL` (`GRND_RANDOM | GRND_INSECURE`). -/
def GrndFlags.isInvalid (f : GrndFlags) : Bool :=
  f.random && f.insecure

/-- Semantic classification of Linux `TimeRand` syscall `Errno` outcomes for error-coverage auditing. -/
inductive TimeRandErrorKind where
  /-- Invalid `Timespec` (`sec < 0` or `nsec ≥ 10^9`), mutually exclusive `GrndFlags` (`random && insecure`), or unsupported clock/flags (`EINVAL`, `EOPNOTSUPP`, `ENOSYS`, `ERANGE`). -/
  | invalidArg
  /-- Non-blocking entropy request before kernel CRNG initialization (`EAGAIN` / `EWOULDBLOCK`). -/
  | wouldBlock
  /-- Permission rejection (`EPERM`, `EACCES`). -/
  | permissionDenied
  /-- Interrupted sleep/wait or transient/resource OS fault (`EINTR`, `EIO`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Classify any Linux `Errno` into a `TimeRandErrorKind`. -/
def TimeRandErrorKind.ofErrno (e : Errno) : TimeRandErrorKind :=
  if e == Errno.EINVAL || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS || e == Errno.ERANGE then .invalidArg
  else if e == Errno.EAGAIN then .wouldBlock
  else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
  else .transientOrResource

/-- Monadic capability bundle for all 3 curated Linux `TimeRand` syscalls, parameterized over effect monad `m`. -/
structure TimeRandOpsM (m : Type → Type) where
  /-- Read the current value of `clk` (`CLOCK_REALTIME` or `CLOCK_MONOTONIC`) via `clock_gettime(2)`. -/
  clock_gettime : ClockId → m (Except Errno Timespec)
  /-- Sleep on `clk` for relative duration `req` (`abstime = false`) or until deadline `req` (`abstime = true`, `TIMER_ABSTIME`) via `clock_nanosleep(2)`. -/
  clock_nanosleep : ClockId → Bool → Timespec → m (Except Errno Unit)
  /-- Read up to `min len MAX_READ_BYTES` random bytes via `getrandom(2)` (exact `len` when `len ≤ 256`). -/
  getrandom : UInt32 → GrndFlags → m (Except Errno ByteArray)

/-- Real-world `IO` specialization of `TimeRandOpsM`. -/
abbrev TimeRandOps := TimeRandOpsM IO

/-- Low-level C-ABI syscall hooks supplied by `Interface.lean` and backed by `timerand_shim.c`, parameterized over monad `m`. -/
structure PosixTimeRandOpsM (m : Type → Type) where
  /-- Raw `clock_gettime(2)` hook accepting portable `ClockId.toRaw` (`0` or `1`) and returning `(sec, nsec)`. -/
  clock_gettime : UInt32 → m (Except Errno (Int64 × UInt32))
  /-- Raw `clock_nanosleep(2)` (`SYS_clock_nanosleep`) hook accepting `(clockRaw, abstimeByte, sec, nsec)`. -/
  clock_nanosleep : UInt32 → UInt8 → Int64 → UInt32 → m (Except Errno Unit)
  /-- Raw `getrandom(2)` (`SYS_getrandom`) hook accepting `(len, flagsBits)` (clamped to `MAX_READ_BYTES` in C). -/
  getrandom : UInt32 → UInt32 → m (Except Errno ByteArray)

/-- Real-world `IO` specialization of `PosixTimeRandOpsM`. -/
abbrev PosixTimeRandOps := PosixTimeRandOpsM IO

end LeanSwe.LinuxSyscall.TimeRand
