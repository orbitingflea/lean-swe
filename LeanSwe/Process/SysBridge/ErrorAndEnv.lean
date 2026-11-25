import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal

/-!
Pure error normalization, process-table state transitions, and raw `environ(7)` / `PATH`
byte helpers for `LeanSwe.Process.SysBridge`.
-/

namespace LeanSwe.Process.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.Process

export LeanSwe.Process.Internal
  (SysDepsM ProcessSysCapsM ProcSlotM ProcTableState ProcCellS ProcTableOpsM
   StreamPhaseOutcome StreamLoopState)

/-- Return `true` iff `s` contains a NUL character. -/
def hasNul (s : String) : Bool :=
  s.toList.contains '\x00'

/-- Return `true` iff an environment entry `(k, v?)` is invalid (empty key, `=`, or NUL byte). -/
def isInvalidEnvEntry (kv : String × Option String) : Bool :=
  kv.1.isEmpty || kv.1.toList.contains '=' || hasNul kv.1 ||
    match kv.2 with
    | some v => hasNul v
    | none => false

/-- Return `err` with a non-empty fallback message if `err.message` is empty. -/
def ensureNonEmptyMsg (fallback : String) (err : ProcessError) : ProcessError :=
  if err.message.isEmpty then { err with message := fallback } else err

/-- Per-read chunk size (`8192` bytes) when draining child `stdout` / `stderr` pipes. -/
def PIPE_READ_CHUNK : UInt32 := 8192

/-- Per-round per-stream byte cap (`65536` bytes) preventing one chatty pipe from starving the other. -/
def STREAM_FAIRNESS_BYTES : Nat := 65536

/-- Maximum slice size (`65536` bytes) passed per `write(2)` call on child `stdin`. -/
def STDIN_WRITE_CHUNK : Nat := 65536

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `ProcessRawError` into a normalized `ProcessError` with a non-empty message. -/
def mapRawError : ProcessRawError → ProcessError
  | .executableNotFound prog code detail =>
    { kind := .notFound
      program := some prog
      errnoCode := some code
      message := nonEmptyMsg s!"executable not found: {prog}" detail }
  | .permissionDenied prog? code detail =>
    { kind := .permissionDenied
      program := prog?
      errnoCode := some code
      message := nonEmptyMsg "permission denied" detail }
  | .invalidArgument prog? code detail =>
    { kind := .invalidInput
      program := prog?
      errnoCode := some code
      message := nonEmptyMsg "invalid process argument" detail }
  | .timedOut prog timeoutMs detail =>
    { kind := .timedOut
      program := some prog
      message := nonEmptyMsg s!"process '{prog}' timed out after {timeoutMs}ms" detail }
  | .outputLimitExceeded prog limitBytes detail =>
    { kind := .outputLimitExceeded
      program := some prog
      message := nonEmptyMsg s!"process '{prog}' exceeded output limit ({limitBytes} bytes)" detail }
  | .signaled prog sig detail =>
    { kind := .terminatedBySignal
      program := some prog
      signal := some sig
      message := nonEmptyMsg s!"process '{prog}' terminated by signal {sig}" detail }
  | .otherError code detail =>
    { kind := .ioError
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsg "process error" detail }

/-- Return `true` iff `e` represents an invalid input, path length, symlink loop, exec format, or argument-size error. -/
def isInvalidInputErrno (e : Errno) : Bool :=
  e == Errno.EINVAL || e == Errno.ENAMETOOLONG || e == Errno.ELOOP ||
  e == Errno.ENOEXEC || e == Errno.E2BIG

/-- Map a Linux `Errno` with optional target path/program and context detail into `ProcessError`. -/
def mapErrno (prog? : Option String) (ctx : String) (e : Errno) : ProcessError :=
  let detail := s!"{ctx}: {Errno.name e}"
  if e == Errno.ENOENT then
    let mapped := mapRawError (.executableNotFound (prog?.getD "") e detail)
    { mapped with program := prog? <|> mapped.program }
  else if e == Errno.EACCES || e == Errno.EPERM then
    mapRawError (.permissionDenied prog? e detail)
  else if isInvalidInputErrno e then
    mapRawError (.invalidArgument prog? e detail)
  else
    let mapped := mapRawError (.otherError e detail)
    { mapped with program := prog? }

/-- Pure step inserting `slot` into `ProcTableState`, returning `(handleId, nextState)`. -/
def insertSlotPure {fd : Type} (st : ProcTableState fd) (slot : ProcSlotM fd) :
    Nat × ProcTableState fd :=
  let hid := st.nextId
  (hid, { nextId := hid + 1, slots := (hid, slot) :: st.slots })

/-- Lookup helper over association list `slots`. -/
def findSlotPure {fd : Type} (hid : Nat) : List (Nat × ProcSlotM fd) → Option (ProcSlotM fd)
  | [] => none
  | (k, v) :: rest => if k == hid then some v else findSlotPure hid rest

/-- Pure step detaching pipe descriptors from `hid` for `awaitOutput`. -/
def takeSlotIoPure {fd : Type} (st : ProcTableState fd) (hid : Nat) :
    Option (UInt32 × Option fd × Option fd × Option fd) × ProcTableState fd :=
  match findSlotPure hid st.slots with
  | none => (none, st)
  | some slot =>
    let slots' := st.slots.map fun (k, s) =>
      if k == hid then (k, { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
      else (k, s)
    (some (slot.pid, slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?), { st with slots := slots' })

/-- Pure step updating `waited` on `hid` if still present (`false` if concurrently reaped). -/
def markWaitedPure {fd : Type} (st : ProcTableState fd) (hid : Nat) (waited : Bool) :
    Bool × ProcTableState fd :=
  match findSlotPure hid st.slots with
  | none => (false, st)
  | some _ =>
    let slots' := st.slots.map fun (k, s) =>
      if k == hid then (k, { s with waited := s.waited || waited }) else (k, s)
    (true, { st with slots := slots' })

/-- Remove first matching `hid` from association list `slots`. -/
def removeSlotList {fd : Type} (hid : Nat) :
    List (Nat × ProcSlotM fd) → Option (ProcSlotM fd) × List (Nat × ProcSlotM fd)
  | [] => (none, [])
  | (k, v) :: rest =>
    if k == hid then
      (some v, rest)
    else
      let (found?, rest') := removeSlotList hid rest
      (found?, (k, v) :: rest')

/-- Pure step detaching `hid` completely from `ProcTableState`. -/
def detachSlotPure {fd : Type} (st : ProcTableState fd) (hid : Nat) :
    Option (ProcSlotM fd) × ProcTableState fd :=
  let (found?, slots') := removeSlotList hid st.slots
  (found?, { st with slots := slots' })

/-- Pure `StateM S` instantiation of `ProcTableOpsM` via lens `(getTbl, setTbl)`. -/
def stateProcTableOps {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S) : ProcTableOpsM (StateM S) fd where
  insertSlot slot := modifyGet fun s =>
    let (hid, t') := insertSlotPure (getTbl s) slot
    (hid, setTbl s t')
  takeSlotIo hid := modifyGet fun s =>
    let (res, t') := takeSlotIoPure (getTbl s) hid
    (res, setTbl s t')
  markWaited hid waited := modifyGet fun s =>
    let (ok, t') := markWaitedPure (getTbl s) hid waited
    (ok, setTbl s t')
  lookupPgid hid := do
    let s ← get
    return (findSlotPure hid (getTbl s).slots).map (·.pgid)
  detachSlot hid := modifyGet fun s =>
    let (res, t') := detachSlotPure (getTbl s) hid
    (res, setTbl s t')
  activeCount := do
    let s ← get
    return (getTbl s).slots.length

/-- Capability-parameterized `ProcTableOpsM` backed directly by `Core.StateCellM`. -/
def cellProcTableOps {m : Type → Type} [Monad m] {fd : Type}
    (cell : Core.StateCellM m (ProcTableState fd)) : ProcTableOpsM m fd where
  insertSlot slot := cell.modifyGet (fun st => insertSlotPure st slot)
  takeSlotIo hid := cell.modifyGet (fun st => takeSlotIoPure st hid)
  markWaited hid waited := cell.modifyGet (fun st => markWaitedPure st hid waited)
  lookupPgid hid := do
    let st ← cell.get
    return (findSlotPure hid st.slots).map (·.pgid)
  detachSlot hid := cell.modifyGet (fun st => detachSlotPure st hid)
  activeCount := do
    let st ← cell.get
    return st.slots.length

/-- Return `true` iff raw byte slice `b` contains an embedded NUL (`0x00`) byte. -/
def hasByteNul (b : ByteArray) : Bool :=
  b.toList.any (· == (0 : UInt8))

/-- Return `true` iff raw `environ(7)` entry `entry` starts with `key ++ "="` (`0x3D`). -/
def bytesHasPrefixEq (key entry : ByteArray) : Bool :=
  if h : key.size < entry.size then
    entry.extract 0 key.size == key && entry[key.size] == (0x3D : UInt8)
  else
    false

/-- Merge explicit `overrides` (`some v` sets, `none` removes) onto raw `environ(7)` byte entries,
    preserving unmodified raw/non-UTF-8 entries verbatim and matching keys byte-for-byte before `'='`. -/
def mergeRawEnvOverrides (base : Array ByteArray)
    (overrides : Array (String × Option String)) : Array ByteArray :=
  let cleanBase := base.filter (fun b => !hasByteNul b)
  overrides.foldl
    (fun acc (k, v?) =>
      let kb := k.toUTF8
      let withoutKey := acc.filter (fun e => !bytesHasPrefixEq kb e)
      match v? with
      | none => withoutKey
      | some v => withoutKey.push (kb ++ ByteArray.mk #[0x3D] ++ v.toUTF8))
    cleanBase

/-- Look up the first `"PATH=..."` raw value bytes in `envBytes` (`none` if unset). -/
def findEnvPathRaw (envBytes : Array ByteArray) : Option ByteArray :=
  let pathKey := "PATH".toUTF8
  envBytes.findSome? fun e =>
    if bytesHasPrefixEq pathKey e then
      some (e.extract (pathKey.size + 1) e.size)
    else
      none

/-- Split a raw `PATH` value on `:` (`0x3A`), replacing every empty segment with `"."` per POSIX `execvp(3)`. -/
def splitPosixPathBytes (rawPath : ByteArray) : List ByteArray :=
  (splitByte (0x3A : UInt8) rawPath).map fun seg =>
    if seg.size == 0 then ".".toUTF8 else seg

/-- Compute host filesystem path bytes probed by `searchPathDirs` for `dir` and `program` under `cwd?`. -/
def probePathBytes (cwd? : Option String) (dir program : String) : ByteArray :=
  let execCand := dir ++ "/" ++ program
  let hostProbe :=
    match cwd? with
    | some cwdDir =>
      if dir.toList.head? == some '/' || cwdDir.isEmpty then execCand
      else cwdDir ++ "/" ++ execCand
    | none => execCand
  hostProbe.toUTF8

/-- Return `true` iff `e` records a permission-class candidate rejection while continuing `PATH` search. -/
def isPermPathSearchErrno (e : Errno) : Bool :=
  e == Errno.EACCES || e == Errno.EPERM || e == Errno.EISDIR || e == Errno.EROFS

/-- Return `true` iff `e` records a missing-entry rejection while continuing `PATH` search. -/
def isMissingPathSearchErrno (e : Errno) : Bool :=
  e == Errno.ENOENT || e == Errno.ENOTDIR

end LeanSwe.Process.SysBridge
