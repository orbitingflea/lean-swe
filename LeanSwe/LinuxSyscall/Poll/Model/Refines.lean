import LeanSwe.LinuxSyscall.Poll.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.Poll`

Defines pure interface behavior specs (`msToPollTimespec`, `pollEvReady`),
raw C-ABI wire decoders and single-step contract (`RawPollOpsM`, `RawPollReq`,
`RawPollOut`, `execRawStep`, `allowedRawStep`, `rawHealthyModelOps`), and
package-level `HandleId` single-step entry points (`HandlePollOpsM`,
`healthyModelOps`, `execPkgStep`, `allowedPkgStep`) over `HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.Poll.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Poll

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Pure behavior model of `LeanSwe.LinuxSyscall.Poll.msToPollTimespec`. -/
def msToPollTimespec (ms : Nat) : Timespec :=
  let clampedSec := Nat.min (ms / 1000) 9223372036854775807
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

/-- Pure behavior model of `LeanSwe.LinuxSyscall.Poll.pollEvReady`. -/
def pollEvReady (wantOut : Bool) (ev : PollEvents) : Bool :=
  (if wantOut then ev.pollout else ev.pollin) || ev.pollhup || ev.pollerr || ev.pollnval

/-- Monad-parameterized raw C-ABI `Poll` capability family specialized to `HandleId`. -/
abbrev RawPollOpsM (m : Type → Type) : Type :=
  PosixPollOpsM m HandleId

/-- Monad-parameterized public `Poll` capability family specialized to `HandleId`. -/
abbrev HandlePollOpsM (m : Type → Type) : Type :=
  PollOpsM m HandleId

/-- Decode a portable 3-bit `EventFdFlags` bitmask (`0..7`). -/
def decodeRawEventFdFlags? (bits : UInt32) : Option EventFdFlags :=
  if bits < 8 then
    some { nonblock := (bits &&& 1) != 0
           cloexec := (bits &&& 2) != 0
           semaphore := (bits &&& 4) != 0 }
  else
    none

/-- Decode raw `(hasTimeout, secBits, nsec)` wire arguments into a validated `Option Timespec`. -/
def decodeRawPollTimeout? (hasTimeout : UInt8) (secBits : UInt64) (nsec : UInt32) :
    Option (Option Timespec) :=
  if hasTimeout == 0 then
    if secBits == 0 && nsec == 0 then some none else none
  else if hasTimeout == 1 then
    let ts : Timespec := { sec := secBits.toInt64, nsec := nsec }
    if ts.isValid then some (some ts) else none
  else
    none

/-- Decode one portable 5-bit `PollEvents` request byte (`0..31`). -/
def decodeRawPollEventByte? (b : UInt8) : Option PollEvents :=
  if b.toUInt32 < 32 then some (PollEvents.ofBits b.toUInt32) else none

/-- Zip and decode parallel `(HandleId, UInt8)` lists into `(HandleId × PollEvents)`. -/
def decodeRawPollEntriesList : List HandleId → List UInt8 → Option (List (HandleId × PollEvents))
  | [], [] => some []
  | hid :: hids, b :: bs =>
    match decodeRawPollEventByte? b, decodeRawPollEntriesList hids bs with
    | some ev, some rest => some ((hid, ev) :: rest)
    | _, _ => none
  | _, _ => none

/-- Decode parallel `(Array HandleId, ByteArray)` C-ABI buffers into `Array (HandleId × PollEvents)`. -/
def decodeRawPollEntries? (fds : Array HandleId) (reqBytes : ByteArray) :
    Option (Array (HandleId × PollEvents)) :=
  (decodeRawPollEntriesList fds.toList reqBytes.data.toList).map List.toArray

/-- Single-step request sum for `PosixPollOpsM` C-ABI syscall hooks. -/
inductive RawPollReq where
  /-- Raw `ppoll(fds, reqBytes, hasTimeout, secBits, nsec)`. -/
  | ppoll (fds : Array HandleId) (reqBytes : ByteArray) (hasTimeout : UInt8)
      (secBits : UInt64) (nsec : UInt32)
  /-- Raw `eventfd2(initval, flagsBits)`. -/
  | eventfd2 (initval : UInt32) (flagsBits : UInt32)
  deriving Repr, BEq, Inhabited

/-- Single-step output sum for `PosixPollOpsM` C-ABI syscall hooks. -/
inductive RawPollOut where
  /-- `ppoll` succeeded returning per-entry `revents` bytes. -/
  | polled (revBytes : ByteArray)
  /-- `eventfd2` succeeded returning logical handle `hid`. -/
  | opened (hid : HandleId)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, BEq, Inhabited

/-- Decode an `Except Errno ByteArray` into `RawPollOut`. -/
def outcomeOfRawPolled : Except Errno ByteArray → RawPollOut
  | .ok bs => .polled bs
  | .error e => .err e

/-- Decode an `Except Errno HandleId` into `RawPollOut`. -/
def outcomeOfRawOpened : Except Errno HandleId → RawPollOut
  | .ok hid => .opened hid
  | .error e => .err e

/-- Execute one `RawPollReq` against a `RawPollOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : RawPollOpsM (StateM W)) : RawPollReq → StateM W RawPollOut
  | .ppoll fds reqBytes hasTimeout secBits nsec =>
    outcomeOfRawPolled <$> raw.ppoll fds reqBytes hasTimeout secBits nsec
  | .eventfd2 initval flagsBits =>
    outcomeOfRawOpened <$> raw.eventfd2 initval flagsBits

/-- Allowed single-step relation for `PosixPollOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawPollReq) (out : RawPollOut)
    (env' : HealthyEnv) : Prop :=
  match req with
  | .eventfd2 initval flagsBits =>
    match decodeRawEventFdFlags? flagsBits with
    | some flags =>
      match out with
      | .opened hid => healthyStep env (.eventfd2 initval flags) (.opened hid) = some env'
      | .err e => healthyStep env (.eventfd2 initval flags) (.err e) = some env'
      | .polled _ => False
    | none => out = .err Errno.EINVAL ∧ env' = env
  | .ppoll fds reqBytes hasTimeout secBits nsec =>
    match decodeRawPollEntries? fds reqBytes, decodeRawPollTimeout? hasTimeout secBits nsec with
    | some entries, some timeout =>
      if entries.size ≤ MAX_POLL_NFDS then
        match out with
        | .polled revBytes =>
          revBytes.size = entries.size ∧
            healthyStep env (.ppoll entries timeout)
              (.polled (decodePollRevents revBytes)) = some env'
        | .err e =>
          healthyStep env (.ppoll entries timeout) (.err e) = some env'
        | .opened _ => False
      else
        out = .err Errno.EINVAL ∧ env' = env
    | _, _ => out = .err Errno.EINVAL ∧ env' = env

/-- Compute a handle ID strictly greater than every key in `fds` and at least `nextHid`. -/
def freshPollHid (fds : List (HandleId × PollDesc)) (nextHid : HandleId) : HandleId :=
  fds.foldl (fun acc p => max acc (p.1 + 1)) nextHid

/-- Reference `HandlePollOpsM (StateM HealthyEnv)` satisfying `healthyStep` from every well-formed `HealthyEnv`. -/
def healthyModelOps : HandlePollOpsM (StateM HealthyEnv) :=
  { eventfd2 := fun initval flags => do
      let env ← get
      let hid := freshPollHid env.state.fds env.state.nextHid
      let desc : PollDesc := { kind := .eventfd initval.toUInt64 flags }
      let s' : PollState :=
        { env.state with fds := assocSet env.state.fds hid desc, nextHid := hid + 1 }
      set { env with state := s' }
      return .ok hid
    ppoll := fun entries timeout => do
      let env ← get
      match preCheckPoll (.ppoll entries timeout) with
      | some preErr => return .error preErr
      | none =>
        match evalPollList env.state entries.toList with
        | .error pinErr => return .error pinErr
        | .ok revList =>
          let knownExceedsNofile : Bool := match env.state.softNofile? with
            | some lim => decide (entries.size > lim)
            | none => false
          if knownExceedsNofile then
            return .error Errno.EINVAL
          else
            let anyReady := revList.any (fun ev => !ev.isEmpty)
            if !anyReady && timeout.isNone then
              return .error Errno.EMFILE
            else
              return .ok revList.toArray }

/-- Reference `RawPollOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : RawPollOpsM (StateM HealthyEnv) :=
  { eventfd2 := fun initval flagsBits =>
      match decodeRawEventFdFlags? flagsBits with
      | some flags => healthyModelOps.eventfd2 initval flags
      | none => pure (.error Errno.EINVAL)
    ppoll := fun fds reqBytes hasTimeout secBits nsec =>
      match decodeRawPollEntries? fds reqBytes, decodeRawPollTimeout? hasTimeout secBits nsec with
      | some entries, some timeout =>
        if entries.size ≤ MAX_POLL_NFDS then do
          match ← healthyModelOps.ppoll entries timeout with
          | .ok revents =>
            return .ok (ByteArray.mk (revents.map (fun ev => UInt8.ofNat ev.toBits.toNat)))
          | .error e =>
            return .error e
        else
          pure (.error Errno.EINVAL)
      | _, _ => pure (.error Errno.EINVAL) }

/-- Execute one `PollReq` against a `HandlePollOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : HandlePollOpsM (StateM W)) (req : PollReq) :
    StateM W PollOutcome :=
  execPollReq ops req

/-- Allowed single-step relation for `PollOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : PollReq) (out : PollOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

end LeanSwe.LinuxSyscall.Poll.Model
