import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Poll

open LeanSwe.LinuxSyscall

/-- Exclusive upper bound on valid `Timespec.nsec` values (`1_000_000_000` nanoseconds per second). -/
def NANOS_PER_SEC : UInt32 := 1000000000

/-- Maximum non-blocking counter value of a Linux `eventfd` (`0xfffffffffffffffe`, above which `POLLOUT` clears and `write` returns `EAGAIN`). -/
def EFD_MAX_COUNT : UInt64 := 0xfffffffffffffffe

/-- Maximum `nfds` accepted before failing with `EINVAL` in bounded world-model checks (`1_048_576`). -/
def MAX_POLL_NFDS : Nat := 1048576

/-- Relative timeout duration for Linux `ppoll(2)` (`struct timespec`). -/
structure Timespec where
  /-- Whole seconds (`tv_sec`; negative values are rejected with `EINVAL`). -/
  sec : Int64 := 0
  /-- Nanoseconds (`tv_nsec`; values `>= 1_000_000_000` are rejected with `EINVAL`). -/
  nsec : UInt32 := 0
  deriving Repr, DecidableEq, BEq

/-- Returns `true` iff `ts` satisfies Linux `timespec64_valid` for relative `ppoll` timeouts (`sec >= 0` and `nsec < 1_000_000_000`). -/
def Timespec.isValid (ts : Timespec) : Bool :=
  decide ((0 : Int64) ≤ ts.sec) && ts.nsec < NANOS_PER_SEC

/-- Returns `true` iff `ts` represents an immediate non-blocking poll (`sec == 0` and `nsec == 0`). -/
def Timespec.isZero (ts : Timespec) : Bool :=
  ts.sec == 0 && ts.nsec == 0

/-- Portable symbolic readiness bitmask for `ppoll(2)` (`events` request and `revents` result). -/
structure PollEvents where
  /-- Data may be read without blocking (`POLLIN`, `0x0001`). -/
  pollin : Bool := false
  /-- Writing now will not block (`POLLOUT`, `0x0004`). -/
  pollout : Bool := false
  /-- Error condition (`POLLERR`, `0x0008`; output-only in `revents`, ignored in `events`). -/
  pollerr : Bool := false
  /-- Peer closed or hang up (`POLLHUP`, `0x0010`; output-only in `revents`, ignored in `events`). -/
  pollhup : Bool := false
  /-- Underlying OS descriptor not open (`POLLNVAL`, `0x0020`; output-only in `revents`, ignored in `events`). -/
  pollnval : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Returns `true` iff no readiness, error, hangup, or invalid-FD flag is set in `ev`. -/
def PollEvents.isEmpty (ev : PollEvents) : Bool :=
  !ev.pollin && !ev.pollout && !ev.pollerr && !ev.pollhup && !ev.pollnval

/-- Encode `PollEvents` into a 5-bit portable bitmask (`0..31`) decoded by `poll_shim.c`. -/
def PollEvents.toBits (ev : PollEvents) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit ev.pollin 0 ||| bit ev.pollout 1 ||| bit ev.pollerr 2
    ||| bit ev.pollhup 3 ||| bit ev.pollnval 4

/-- Decode a 5-bit portable bitmask returned by `poll_shim.c` into `PollEvents`. -/
def PollEvents.ofBits (bits : UInt32) : PollEvents :=
  { pollin := (bits &&& ((1 : UInt32) <<< 0)) != 0
    pollout := (bits &&& ((1 : UInt32) <<< 1)) != 0
    pollerr := (bits &&& ((1 : UInt32) <<< 2)) != 0
    pollhup := (bits &&& ((1 : UInt32) <<< 3)) != 0
    pollnval := (bits &&& ((1 : UInt32) <<< 4)) != 0 }

/-- Portable symbolic flags for Linux `eventfd2(2)` translated via `<sys/eventfd.h>`. -/
structure EventFdFlags where
  /-- Set `O_NONBLOCK` (`EFD_NONBLOCK`) on the new open file description. -/
  nonblock : Bool := false
  /-- Set `FD_CLOEXEC` (`EFD_CLOEXEC`) on the new file descriptor. -/
  cloexec : Bool := true
  /-- Enable semaphore-like read semantics (`EFD_SEMAPHORE`, decrementing by `1` per read). -/
  semaphore : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `EventFdFlags` into a 3-bit portable bitmask (`0..7`) decoded by `poll_shim.c`. -/
def EventFdFlags.toBits (f : EventFdFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.nonblock 0 ||| bit f.cloexec 1 ||| bit f.semaphore 2

/-- Split an array of `(fd, PollEvents)` pairs into parallel `(Array fd × ByteArray)` buffers for C-ABI transport. -/
def encodePollRequests {fd : Type} (entries : Array (fd × PollEvents)) : Array fd × ByteArray :=
  (entries.map Prod.fst, ByteArray.mk (entries.map (fun (_, ev) => UInt8.ofNat ev.toBits.toNat)))

/-- Decode raw 5-bit per-entry `revents` bytes returned by `poll_shim.c` into `Array PollEvents`. -/
def decodePollRevents (raw : ByteArray) : Array PollEvents :=
  raw.foldl (fun acc b => acc.push (PollEvents.ofBits b.toUInt32)) #[]

/-- Semantic classification of Linux `Poll` syscall `Errno` outcomes for error-coverage auditing. -/
inductive PollErrorKind where
  /-- Closed or invalid `LeanFdBox` handle (`EBADF`). -/
  | badFd
  /-- Invalid `Timespec` (`tv_sec < 0` or `tv_nsec >= 10^9`) or excessive `nfds` (`EINVAL`, `ENOSYS`). -/
  | invalidArg
  /-- Blocked `ppoll` call interrupted by signal delivery (`EINTR`). -/
  | interrupted
  /-- Transient kernel or resource-exhaustion fault (`ENOMEM`, `ENFILE`, `EMFILE`, `EIO`, `ENOSPC`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq

/-- Classify any Linux `Errno` into a `PollErrorKind`. -/
def PollErrorKind.ofErrno (e : Errno) : PollErrorKind :=
  if e == Errno.EBADF then .badFd
  else if e == Errno.EINVAL || e == Errno.ENOSYS then .invalidArg
  else if e == Errno.EINTR then .interrupted
  else .transientOrResource

/-- Monad-parameterized capability bundle for the 2 curated Linux `Poll` syscalls (`ppoll`, `eventfd2`). -/
structure PollOpsM (m : Type → Type) (fd : Type) where
  /-- Poll `fds` for readiness events with optional relative `timeout` (`none` = block until ready or `EINTR`) via `ppoll(2)`. -/
  ppoll : Array (fd × PollEvents) → Option Timespec → m (Except Errno (Array PollEvents))
  /-- Create an `eventfd` object initialized to `initval` with `flags` via `eventfd2(2)`. -/
  eventfd2 : UInt32 → EventFdFlags → m (Except Errno fd)

/-- Real-world `IO` specialization of `PollOpsM` using ABA-safe `RawFd` handles. -/
abbrev PollOps := PollOpsM IO RawFd

/-- Monad-parameterized low-level C-ABI syscall hooks for `Poll` (`ppoll`, `eventfd2`). -/
structure PosixPollOpsM (m : Type → Type) (fd : Type) where
  /-- Raw `ppoll(2)` hook accepting `(fds, reqEventBytes, hasTimeout, secTwosCompBits, nsec)` and returning per-entry `revents` bytes. -/
  ppoll : Array fd → ByteArray → UInt8 → UInt64 → UInt32 → m (Except Errno ByteArray)
  /-- Raw `eventfd2(2)` hook accepting `(initval, portableFlagBits)`. -/
  eventfd2 : UInt32 → UInt32 → m (Except Errno fd)

/-- Concrete `IO` specialization of `PosixPollOpsM` supplied by `Interface.lean` and backed by `poll_shim.c`. -/
abbrev PosixPollOps := PosixPollOpsM IO RawFd

/-- Logical handle identifier used by the relational `Poll` world model and fuzzer traces. -/
abbrev HandleId := Nat

private def formatPollEntries (entries : Array (HandleId × PollEvents)) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < entries.size then
      let (hid, ev) := entries[i]'h
      let sep := if i == 0 then "" else ", "
      go (i + 1) (acc ++ sep ++ "(" ++ toString hid ++ ", " ++ reprStr ev ++ ")")
    else
      acc ++ "]"
  go 0 "#["

private def formatPollRevents (revents : Array PollEvents) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < revents.size then
      let ev := revents[i]'h
      let sep := if i == 0 then "" else ", "
      go (i + 1) (acc ++ sep ++ reprStr ev)
    else
      acc ++ "]"
  go 0 "#["

/-- One syscall request in a `Poll` world-model trace (covers `ppoll` and `eventfd2`). -/
inductive PollReq where
  /-- `ppoll(fds, timeout)`. -/
  | ppoll (fds : Array (HandleId × PollEvents)) (timeout : Option Timespec)
  /-- `eventfd2(initval, flags)`. -/
  | eventfd2 (initval : UInt32) (flags : EventFdFlags)
  deriving DecidableEq, BEq

instance : Repr PollReq where
  reprPrec r _ :=
    match r with
    | .ppoll fds timeout =>
      Std.Format.text ("PollReq.ppoll " ++ formatPollEntries fds ++ " (" ++ reprStr timeout ++ ")")
    | .eventfd2 initval flags =>
      Std.Format.text ("PollReq.eventfd2 " ++ toString initval ++ " (" ++ reprStr flags ++ ")")

/-- Raw kernel outcome observed for one `PollReq`. -/
inductive PollOutcome where
  /-- `ppoll` succeeded returning per-entry readiness masks of matching length. -/
  | polled (revents : Array PollEvents)
  /-- `eventfd2` succeeded and allocated logical handle `hid`. -/
  | opened (hid : HandleId)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving DecidableEq, BEq

instance : Repr PollOutcome where
  reprPrec o _ :=
    match o with
    | .polled revents => Std.Format.text ("PollOutcome.polled " ++ formatPollRevents revents)
    | .opened hid => Std.Format.text ("PollOutcome.opened " ++ toString hid)
    | .err code => Std.Format.text ("PollOutcome.err " ++ toString code)

end LeanSwe.LinuxSyscall.Poll
