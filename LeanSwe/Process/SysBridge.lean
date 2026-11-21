import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Interface
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.Process.Types

namespace LeanSwe.Process.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.Process

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

/-- Default bounded retry budget for `EINTR` on single blocking syscalls. -/
def DEFAULT_EINTR_FUEL : Nat := 256

/-- Default fuel bound for non-blocking pipe streaming and timeout polling loops (`2^32`). -/
def DEFAULT_IO_FUEL : Nat := UInt32.size

/-- Maximum valid positive signed 32-bit Linux `pid_t` (`0x7fffffff`). -/
def MAX_LINUX_PID : UInt32 := 0x7fffffff

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

/-- Convert a Lean `IO.Error` into `ProcessRawError`. -/
def ioErrorToRaw (fallbackProg : Option String) : IO.Error → ProcessRawError
  | .noFileOrDirectory p code detail =>
    .executableNotFound (if p.isEmpty then fallbackProg.getD "" else p) code detail
  | .permissionDenied p? code detail =>
    .permissionDenied (p? <|> fallbackProg) code detail
  | .invalidArgument p? code detail =>
    .invalidArgument (p? <|> fallbackProg) code detail
  | .otherError code detail =>
    .otherError code detail
  | .userError detail =>
    .userError detail
  | .interrupted p code detail =>
    .otherError code s!"{p}: {detail}"
  | .timeExpired code detail =>
    .otherError code detail
  | .resourceExhausted p? code detail =>
    .otherError code s!"{p?.getD "process"}: {detail}"
  | .noSuchThing p? code detail =>
    .executableNotFound (p?.or fallbackProg |>.getD "") code detail
  | .alreadyExists _ code detail => .otherError code detail
  | .inappropriateType _ code detail => .otherError code detail
  | .unsupportedOperation code detail => .otherError code detail
  | .unsatisfiedConstraints code detail => .otherError code detail
  | .illegalOperation code detail => .otherError code detail
  | .resourceBusy code detail => .otherError code detail
  | .resourceVanished code detail => .otherError code detail
  | .hardwareFault code detail => .otherError code detail
  | .protocolError code detail => .otherError code detail
  | .unexpectedEof => .userError "unexpected end of file"

/-- Normalize an `IO.Error` into a `ProcessError`, preserving `fallbackProg` when absent. -/
def mapIoError (fallbackProg : Option String) (err : IO.Error) : ProcessError :=
  let mapped := mapRawError (ioErrorToRaw fallbackProg err)
  { mapped with program := mapped.program <|> fallbackProg }

/-- Execute an `IO` action returning `Except ProcessError α`, catching any runtime `IO.Error`. -/
def catchProc {α : Type} (prog? : Option String) (act : IO (Except ProcessError α)) :
    IO (Except ProcessError α) :=
  tryCatch act fun err => pure (.error (mapIoError prog? err))

/-- Dependency bundle consumed by `SysBridge` parameterized over monad `m` and descriptor type `fd`. -/
structure SysDepsM (m : Type → Type) (fd : Type) where
  /-- Curated Linux process syscalls (`pipe2`, `waitpid`, `kill`, `pidfd_open`, `pidfd_send_signal`, `getpid`, `getuid`). -/
  proc : LeanSwe.LinuxSyscall.Process.ProcessOpsM m fd
  /-- Curated Linux file and descriptor syscalls (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`). -/
  files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd
  /-- Curated Linux descriptor-readiness syscall bundle (`ppoll`). -/
  poll : LeanSwe.LinuxSyscall.Poll.PollOpsM m fd
  /-- Curated Linux monotonic clock and nanosleep syscalls (`clock_gettime`, `clock_nanosleep`). -/
  timeRand : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m
  /-- Verified post-`fork` child setup and `execve` capability bundle. -/
  postFork : LeanSwe.PostFork.PostForkOpsM m fd
  /-- Snapshot raw NUL-free `environ(7)` byte entries when `inheritEnv = true`. -/
  listAmbientEnv : m (Except ProcessError (Array ByteArray))

/-- Per-process slot tracked between `spawn`, `awaitOutput`, `killProcessGroup`, and `reap`. -/
structure ProcSlotM (fd : Type) where
  /-- Positive child OS PID (`1 ≤ pid ≤ 0x7fffffff`). -/
  pid : UInt32
  /-- Positive isolated child process group ID (`1 ≤ pgid ≤ 0x7fffffff`). -/
  pgid : UInt32
  /-- Parent write end of child `stdin` pipe, if still owned by the slot. -/
  stdinFd? : Option fd
  /-- Parent read end of child `stdout` pipe, if still owned by the slot. -/
  stdoutFd? : Option fd
  /-- Parent read end of child `stderr` pipe, if still owned by the slot. -/
  stderrFd? : Option fd
  /-- Whether `waitpid` has already reaped `pid`. -/
  waited : Bool := false

/-- Pure in-memory table state tracking active unreaped `ProcSlotM` handles. -/
structure ProcTableState (fd : Type) where
  /-- Next monotonically increasing `handleId` (`≥ 1`). -/
  nextId : Nat := 1
  /-- Active handle slots keyed by `handleId`. -/
  slots : List (Nat × ProcSlotM fd) := []
  deriving Inhabited

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

/-- Capability interface over active process-slot table operations in monad `m`. -/
structure ProcTableOpsM (m : Type → Type) (fd : Type) where
  /-- Allocate a fresh `handleId` and insert `slot`. -/
  insertSlot : ProcSlotM fd → m Nat
  /-- Atomically take `(pid, stdinFd?, stdoutFd?, stderrFd?)` from `handleId`. -/
  takeSlotIo : Nat → m (Option (UInt32 × Option fd × Option fd × Option fd))
  /-- Record `waited` status on `handleId`, returning `false` if slot vanished. -/
  markWaited : Nat → Bool → m Bool
  /-- Look up `pgid` for `handleId` if active. -/
  lookupPgid : Nat → m (Option UInt32)
  /-- Atomically remove and return the slot for `handleId`. -/
  detachSlot : Nat → m (Option (ProcSlotM fd))
  /-- Return count of currently active unreaped handles. -/
  activeCount : m Nat

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

/-- Retry an `Except Errno α` action across `Errno.EINTR` up to `fuel` attempts. -/
def retryEintr {m : Type → Type} [Monad m] {α : Type}
    (act : m (Except Errno α)) : Nat → m (Except Errno α)
  | 0 => act
  | fuel + 1 => do
    match ← act with
    | .error e =>
      if e == Errno.EINTR then retryEintr act fuel else return .error e
    | .ok v => return .ok v

/-- Best-effort close of an optional `fd` handle (`EINTR` is NOT retried per Linux `close(2)` semantics). -/
def closeOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) : Option fd → m Unit
  | none => pure ()
  | some h => do
    let _ ← files.close h
    pure ()

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

/-- Tail-recursive splitter for raw colon-separated (`0x3A`) `PATH` bytes mapping every empty
    segment (`""`, leading/trailing/adjacent `:`) to `"."` per POSIX `execvp(3)`. -/
def splitPosixPathBytesAcc (curRev : List UInt8) (accRev : List ByteArray) : List UInt8 → List ByteArray
  | [] =>
    let seg := if curRev.isEmpty then ".".toUTF8 else ByteArray.mk curRev.reverse.toArray
    (seg :: accRev).reverse
  | b :: bs =>
    if b == (0x3A : UInt8) then
      let seg := if curRev.isEmpty then ".".toUTF8 else ByteArray.mk curRev.reverse.toArray
      splitPosixPathBytesAcc [] (seg :: accRev) bs
    else
      splitPosixPathBytesAcc (b :: curRev) accRev bs

/-- Split a raw `PATH` value on `:` (`0x3A`), replacing every empty segment with `"."` per POSIX `execvp(3)`. -/
def splitPosixPathBytes (rawPath : ByteArray) : List ByteArray :=
  splitPosixPathBytesAcc [] [] rawPath.toList

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

/-- Search `dirs` for an executable regular file candidate matching POSIX `execvp`. -/
def searchPathDirs {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (eintrFuel : Nat) (sawPerm : Bool) : List String → m (Except ProcessError String)
  | [] =>
    if sawPerm then
      pure (.error (mapRawError (.permissionDenied (some program) Errno.EACCES "permission denied")))
    else
      pure (.error (mapRawError (.executableNotFound program Errno.ENOENT s!"executable not found: {program}")))
  | dir :: rest => do
    let execCand := dir ++ "/" ++ program
    let pathBytes := probePathBytes cwd? dir program
    match ← retryEintr (files.fstatat none pathBytes {}) eintrFuel with
    | .error e =>
      if isPermPathSearchErrno e then
        searchPathDirs files program cwd? eintrFuel true rest
      else if isMissingPathSearchErrno e then
        searchPathDirs files program cwd? eintrFuel sawPerm rest
      else
        pure (.error (mapErrno (some program) "execvp" e))
    | .ok st =>
      if st.kind != .reg then
        searchPathDirs files program cwd? eintrFuel true rest
      else
        match ← retryEintr (files.faccessat none pathBytes { exec := true } { eaccess := true }) eintrFuel with
        | .ok () => pure (.ok execCand)
        | .error e =>
          if isPermPathSearchErrno e then
            searchPathDirs files program cwd? eintrFuel true rest
          else if isMissingPathSearchErrno e then
            searchPathDirs files program cwd? eintrFuel sawPerm rest
          else
            pure (.error (mapErrno (some program) "execvp" e))

/-- Pre-validate optional working directory `cwd?` matching child `chdir(2)` semantics before `PATH` search. -/
def validateWorkingDir {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cwd? : Option String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except ProcessError Unit) :=
  match cwd? with
  | none => pure (.ok ())
  | some cwdDir => do
    if cwdDir.isEmpty then
      return .error (mapErrno (some cwdDir) "chdir" Errno.ENOENT)
    let cwdBytes := cwdDir.toUTF8
    match ← retryEintr (files.fstatat none cwdBytes {}) eintrFuel with
    | .error e => return .error (mapErrno (some cwdDir) "chdir" e)
    | .ok st =>
      if st.kind != .dir then
        return .error (mapErrno (some cwdDir) "chdir" Errno.ENOTDIR)
      match ← retryEintr (files.faccessat none cwdBytes { exec := true } { eaccess := true }) eintrFuel with
      | .error e => return .error (mapErrno (some cwdDir) "chdir" e)
      | .ok () => return .ok ()

/-- Resolve `program` against the effective child `PATH` bytes when `program` contains no `'/'`
    (expanding empty segments such as `""`, `:/usr/bin`, `/usr/bin:`, `a::b` to `"."` per POSIX
    `execvp(3)`). Because `PostFork.ChildSpecM.path` is a UTF-8 `String`, individual non-UTF-8
    `PATH` directory segments are skipped while valid UTF-8 segments continue to be searched. -/
def resolveExecutablePath {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (envBytes : Array ByteArray) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except ProcessError String) :=
  if program.toList.contains '/' then
    pure (.ok program)
  else
    let rawPath := (findEnvPathRaw envBytes).getD "/bin:/usr/bin".toUTF8
    let dirs := (splitPosixPathBytes rawPath).filterMap String.fromUTF8?
    searchPathDirs files program cwd? eintrFuel false dirs

/-- Check spawn-time request validity (non-empty `program`, no NUL bytes, valid `env` keys/values). -/
def isInvalidSpawnRequest (req : ExecRequest) : Bool :=
  req.program.isEmpty ||
  hasNul req.program ||
  PostFork.Model.hasEmbeddedNulStr req.program ||
  req.args.toList.any (fun a => hasNul a || PostFork.Model.hasEmbeddedNulStr a) ||
  (match req.cwd with
   | some d => hasNul d || PostFork.Model.hasEmbeddedNulStr d
   | none => false) ||
  req.env.toList.any (fun kv =>
    isInvalidEnvEntry kv ||
    PostFork.Model.hasEmbeddedNulStr kv.1 ||
    match kv.2 with | some v => PostFork.Model.hasEmbeddedNulStr v | none => false)

/-- Map a `PostForkError` from `PostFork.spawn` into `ProcessError` (attributing `.chdir` failures to `req.cwd`). -/
def mapPostForkError (req : ExecRequest) (pfErr : PostFork.PostForkError) : ProcessError :=
  match pfErr.childFailure with
  | some cf =>
    let target :=
      if cf.stage == .chdir && req.cwd.isSome then req.cwd.getD req.program else req.program
    mapErrno (some target) "spawn" cf.errno
  | none =>
    match pfErr.kind with
    | .invalidInput =>
      mapRawError (.invalidArgument (some req.program) (pfErr.errno.getD Errno.EINVAL) pfErr.message)
    | _ =>
      match pfErr.errno with
      | some e => mapErrno (some req.program) "spawn" e
      | none =>
        let mapped := mapRawError (.userError pfErr.message)
        { mapped with program := some req.program }

/-- Read raw ambient `environ(7)` bytes when `inheritEnv = true`, or return `#[]` when `inheritEnv = false`. -/
def readBaseEnv {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (inheritEnv : Bool) : m (Except ProcessError (Array ByteArray)) :=
  if inheritEnv then deps.listAmbientEnv else pure (.ok #[])

/-- Pure capability-parameterized implementation of `RawProcessOpsM.spawn`. -/
def spawnPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat) (req : ExecRequest) : m (Except ProcessError ProcessHandle) := do
  if isInvalidSpawnRequest req then
    return .error (mapRawError (.invalidArgument (some req.program) Errno.EINVAL "invalid process spawn argument"))
  match ← validateWorkingDir deps.files req.cwd eintrFuel with
  | .error cwdErr => return .error cwdErr
  | .ok _ =>
    match ← readBaseEnv deps req.inheritEnv with
    | .error envErr =>
      return .error (ensureNonEmptyMsg "failed to read environment" envErr)
    | .ok baseEnv =>
      let envBytes := mergeRawEnvOverrides baseEnv req.env
      match ← resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel with
      | .error resErr => return .error resErr
      | .ok resolvedPath =>
        if resolvedPath.isEmpty || PostFork.Model.hasEmbeddedNulStr resolvedPath then
          return .error (mapRawError (.invalidArgument (some req.program) Errno.EINVAL "invalid resolved executable path"))
        match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
        | .error e1 => return .error (mapErrno (some req.program) "pipe2" e1)
        | .ok (inR, inW) =>
          match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
          | .error e2 =>
            closeOpt deps.files (some inR)
            closeOpt deps.files (some inW)
            return .error (mapErrno (some req.program) "pipe2" e2)
          | .ok (outR, outW) =>
            match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
            | .error e3 =>
              closeOpt deps.files (some inR)
              closeOpt deps.files (some inW)
              closeOpt deps.files (some outR)
              closeOpt deps.files (some outW)
              return .error (mapErrno (some req.program) "pipe2" e3)
            | .ok (errR, errW) =>
              let childSpec : PostFork.ChildSpecM fd :=
                { path := resolvedPath
                  argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                  cwd := req.cwd
                  env := #[]
                  rawEnv := envBytes
                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                  fdPolicy := .inheritNonCloexec #[]
                  closeFds := #[.handle inW, .handle outR, .handle errR]
                  processGroup := .newGroup
                  sigpipe := .resetDefault
                  forkMode := .direct }
              let spawnRes ← deps.postFork.spawn childSpec
              closeOpt deps.files (some inR)
              closeOpt deps.files (some outW)
              closeOpt deps.files (some errW)
              match spawnRes with
              | .error pfErr =>
                closeOpt deps.files (some inW)
                closeOpt deps.files (some outR)
                closeOpt deps.files (some errR)
                return .error (mapPostForkError req pfErr)
              | .ok child =>
                let rawPgid := child.pgid.getD child.pid
                if child.pid == 0 || child.pid > MAX_LINUX_PID || rawPgid == 0 || rawPgid > MAX_LINUX_PID then
                  closeOpt deps.files (some inW)
                  closeOpt deps.files (some outR)
                  closeOpt deps.files (some errR)
                  return .error (mapRawError (.userError "spawned child returned out-of-range PID"))
                let hid ← tbl.insertSlot
                  { pid := child.pid
                    pgid := rawPgid
                    stdinFd? := some inW
                    stdoutFd? := some outR
                    stderrFd? := some errR
                    waited := false }
                return .ok
                  { handleId := hid
                    pid := Int.ofNat child.pid.toNat
                    pgid := Int.ofNat rawPgid.toNat }

/-- Flatten `chunks` into a single `ByteArray` in `O(totalBytes)`. -/
def concatChunks (chunks : Array ByteArray) (totalCap : Nat) : ByteArray :=
  chunks.toList.foldl (· ++ ·) (ByteArray.emptyWithCapacity totalCap)

/-- Read `CLOCK_MONOTONIC` in milliseconds. -/
def monoNowMs {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) : m (Except ProcessError Nat) := do
  match ← timeRand.clock_gettime .monotonic with
  | .ok ts =>
    let ms := ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000
    return .ok ms
  | .error e =>
    return .error (mapErrno none "clock_gettime" e)

/-- Check whether `timeoutMs?` has expired relative to `startMs`. -/
def checkTimedOut {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) (startMs : Nat) :
    Option Nat → m (Except ProcessError (Bool × Nat))
  | none => pure (.ok (false, 0))
  | some timeoutMs => do
    match ← monoNowMs timeRand with
    | .error e => return .error e
    | .ok nowMs =>
      let elapsed := nowMs - startMs
      if elapsed ≥ timeoutMs then
        return .ok (true, 0)
      else
        return .ok (false, timeoutMs - elapsed)

/-- Convert a remaining millisecond budget into a valid relative `Poll.Timespec`. -/
def msToPollTimespec (ms : Nat) : Poll.Timespec :=
  let clampedSec := Nat.min (ms / 1000) TimeRand.MAX_TIMESPEC_SEC
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

/-- Sleep on `CLOCK_MONOTONIC` for `ms` milliseconds, ignoring `EINTR`. -/
def sleepMonoMs {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) (ms : Nat) : m Unit := do
  let clampedSec := Nat.min (ms / 1000) TimeRand.MAX_TIMESPEC_SEC
  let remNs := (ms % 1000) * 1000000
  let _ ← timeRand.clock_nanosleep .monotonic false
    { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }
  pure ()

/-- Outcome of draining or writing one non-blocking pipe during a single streaming round. -/
inductive PipeStepResult (fd : Type) where
  /-- Normal round completion with updated descriptor (`none` if closed) and progress flag. -/
  | cont (fd? : Option fd) (chunks : Array ByteArray) (len : Nat) (madeProgress : Bool)
  /-- Timeout deadline reached during step. -/
  | timedOut
  /-- `maxOutputBytes` exceeded (captures prefix up to `maxOutputBytes`). -/
  | limitExceeded (chunks : Array ByteArray) (len : Nat)
  /-- Non-recoverable OS read error. -/
  | ioErr (err : ProcessError)

/-- Write as much of `stdin[pos..]` as non-blocking `inFd` accepts in this round. -/
def writeStdinStep {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd : fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat) :
    Nat → Bool → Nat → m (Except ProcessError (Option fd × Nat × Bool × Bool))
  | pos, prog, 0 =>
    if pos ≥ stdin.size then do
      closeOpt files (some inFd)
      return .ok (none, pos, prog, false)
    else
      return .ok (some inFd, pos, prog, false)
  | pos, prog, fuel + 1 => do
    if pos ≥ stdin.size then
      closeOpt files (some inFd)
      return .ok (none, pos, true, false)
    else
      match ← checkTimedOut timeRand startMs timeoutMs? with
      | .error e =>
        closeOpt files (some inFd)
        return .error e
      | .ok (true, _) =>
        closeOpt files (some inFd)
        return .ok (none, pos, prog, true)
      | .ok (false, _) =>
        let endIdx := Nat.min stdin.size (pos + STDIN_WRITE_CHUNK)
        let slice := stdin.extract pos endIdx
        match ← files.write inFd slice with
        | .ok n =>
          if n == 0 then
            closeOpt files (some inFd)
            return .ok (none, pos, prog, false)
          else
            let pos' := pos + n.toNat
            if pos' ≥ stdin.size then
              closeOpt files (some inFd)
              return .ok (none, pos', true, false)
            else
              writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos' true fuel
        | .error e =>
          if e == Errno.EINTR then
            writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos prog fuel
          else if e == Errno.EAGAIN then
            return .ok (some inFd, pos, prog, false)
          else
            closeOpt files (some inFd)
            return .ok (none, pos, true, false)

/-- Drain up to `STREAM_FAIRNESS_BYTES` from non-blocking `pipeFd` in one round, enforcing `timeoutMs?` and `maxOutputBytes?`. -/
def drainPipeStep {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pipeFd : fd) (otherLen : Nat) (startMs : Nat)
    (timeoutMs? : Option Nat) (maxOutputBytes? : Option Nat) :
    Array ByteArray → Nat → Nat → Bool → Nat → m (PipeStepResult fd)
  | chunks, curLen, _, prog, 0 =>
    pure (.cont (some pipeFd) chunks curLen prog)
  | chunks, curLen, iterBytes, prog, fuel + 1 => do
    if iterBytes ≥ STREAM_FAIRNESS_BYTES then
      return .cont (some pipeFd) chunks curLen prog
    match ← checkTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      closeOpt files (some pipeFd)
      return .ioErr e
    | .ok (true, _) =>
      closeOpt files (some pipeFd)
      return .timedOut
    | .ok (false, _) =>
      match ← files.read pipeFd PIPE_READ_CHUNK with
      | .ok chunk =>
        if chunk.size == 0 then
          closeOpt files (some pipeFd)
          return .cont none chunks curLen true
        else
          let total := curLen + otherLen
          match maxOutputBytes? with
          | some maxOut =>
            if total + chunk.size > maxOut then
              let keep := maxOut - total
              let (chunks', curLen') :=
                if keep > 0 then
                  let pre := chunk.extract 0 keep
                  (chunks.push pre, curLen + pre.size)
                else
                  (chunks, curLen)
              closeOpt files (some pipeFd)
              return .limitExceeded chunks' curLen'
            else
              drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
                (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel
          | none =>
            drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
              (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel
      | .error e =>
        if e == Errno.EINTR then
          drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
            chunks curLen iterBytes prog fuel
        else if e == Errno.EAGAIN then
          return .cont (some pipeFd) chunks curLen prog
        else
          closeOpt files (some pipeFd)
          return .ioErr (mapErrno none "read" e)

/-- Outcome of the pipe-streaming phase prior to `waitpid`. -/
inductive StreamPhaseOutcome where
  /-- Both `stdout` and `stderr` pipes reached EOF cleanly within limits. -/
  | eof (stdout stderr : ByteArray)
  /-- `timeoutMs` elapsed while streaming pipes. -/
  | timedOut (stdout stderr : ByteArray)
  /-- `maxOutputBytes` was exceeded while streaming pipes. -/
  | limitExceeded (stdout stderr : ByteArray)
  deriving BEq, DecidableEq

/-- Mutable loop state carried across `streamPipesLoop` iterations. -/
structure StreamLoopState (fd : Type) where
  /-- Open parent `stdin` write handle (`none` once closed). -/
  inFd? : Option fd
  /-- Open parent `stdout` read handle (`none` once closed). -/
  outFd? : Option fd
  /-- Open parent `stderr` read handle (`none` once closed). -/
  errFd? : Option fd
  /-- Current byte offset written into `stdin`. -/
  stdinPos : Nat := 0
  /-- Collected `stdout` chunks. -/
  outChunks : Array ByteArray := #[]
  /-- Total bytes in `outChunks`. -/
  outLen : Nat := 0
  /-- Collected `stderr` chunks. -/
  errChunks : Array ByteArray := #[]
  /-- Total bytes in `errChunks`. -/
  errLen : Nat := 0

/-- Close all still-open parent pipe handles in `st`. -/
def closeStreamState {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (st : StreamLoopState fd) : m Unit := do
  closeOpt files st.inFd?
  closeOpt files st.outFd?
  closeOpt files st.errFd?

/-- Build the `ppoll(2)` descriptor request array matching open pipe handles in `st`
    (`stdin` watches `POLLOUT`; `stdout` and `stderr` watch `POLLIN`). -/
def buildPollEntries {fd : Type} (st : StreamLoopState fd) : Array (fd × Poll.PollEvents) :=
  let a0 := match st.inFd? with
    | some h => #[(h, { pollout := true })]
    | none => #[]
  let a1 := match st.outFd? with
    | some h => a0.push (h, { pollin := true })
    | none => a0
  match st.errFd? with
  | some h => a1.push (h, { pollin := true })
  | none => a1

/-- Return `true` iff a `ppoll(2)` `revents` entry indicates readiness, hangup, error, or invalid descriptor. -/
def pollEvReady (wantOut : Bool) (ev : Poll.PollEvents) : Bool :=
  (if wantOut then ev.pollout else ev.pollin) || ev.pollhup || ev.pollerr || ev.pollnval

/-- Extract `(inReady, outReady, errReady)` from `ppoll(2)` `revents` aligned with `buildPollEntries st`. -/
def decodeReadyFlags {fd : Type} (st : StreamLoopState fd) (revents : Array Poll.PollEvents) :
    Bool × Bool × Bool :=
  let (inReady, i1) := match st.inFd? with
    | none => (false, 0)
    | some _ => (match revents[0]? with | some ev => pollEvReady true ev | none => true, 1)
  let (outReady, i2) := match st.outFd? with
    | none => (false, i1)
    | some _ => (match revents[i1]? with | some ev => pollEvReady false ev | none => true, i1 + 1)
  let errReady := match st.errFd? with
    | none => false
    | some _ => match revents[i2]? with | some ev => pollEvReady false ev | none => true
  (inReady, outReady, errReady)

/-- Execute one non-blocking `stdin` write round if `inFd?` is still open. -/
def stepStdinOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd? : Option fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (stdinPos stepFuel : Nat) :
    m (Option fd × Nat × Bool × Bool × Option ProcessError) :=
  match inFd? with
  | none => pure (none, stdinPos, false, false, none)
  | some inFd => do
    match ← writeStdinStep files timeRand inFd stdin startMs timeoutMs? stdinPos false stepFuel with
    | .error e => pure (none, stdinPos, false, false, some e)
    | .ok (nextFd?, p', pr, to) => pure (nextFd?, p', pr, to, none)

/-- Execute one non-blocking pipe drain round if `pipeFd?` is still open. -/
def stepDrainOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pipeFd? : Option fd) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen stepFuel : Nat) :
    m (PipeStepResult fd) :=
  match pipeFd? with
  | none => pure (.cont none chunks curLen false)
  | some pipeFd =>
    drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
      chunks curLen 0 false stepFuel

/-- Execute `stepStdinOpt` only when `ppoll` reported `stdin` ready, otherwise preserving `inFd?`. -/
def stepStdinIfReady {m : Type → Type} [Monad m] {fd : Type}
    (ready : Bool) (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd? : Option fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (stdinPos stepFuel : Nat) :
    m (Option fd × Nat × Bool × Bool × Option ProcessError) :=
  if ready then
    stepStdinOpt files timeRand inFd? stdin startMs timeoutMs? stdinPos stepFuel
  else
    pure (inFd?, stdinPos, false, false, none)

/-- Execute `stepDrainOpt` only when `ppoll` reported the pipe ready, otherwise preserving `pipeFd?`. -/
def stepDrainIfReady {m : Type → Type} [Monad m] {fd : Type}
    (ready : Bool) (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pipeFd? : Option fd) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen stepFuel : Nat) :
    m (PipeStepResult fd) :=
  if ready then
    stepDrainOpt files timeRand pipeFd? otherLen startMs timeoutMs? maxOutputBytes?
      chunks curLen stepFuel
  else
    pure (.cont pipeFd? chunks curLen false)

/-- Fuel-bounded `ppoll(2)`-driven pipe streaming loop (`stdin` write + `stdout`/`stderr` read). -/
def streamPipesLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (poll : Poll.PollOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (stdin : ByteArray) (startMs : Nat)
    (timeoutMs? : Option Nat) (maxOutputBytes? : Option Nat) (stepFuel : Nat) :
    StreamLoopState fd → Nat → m (Except ProcessError StreamPhaseOutcome)
  | st, 0 => do
    closeStreamState files st
    return .error (mapRawError (.userError "process I/O loop fuel exhausted"))
  | st, fuel + 1 => do
    if st.inFd?.isNone && st.outFd?.isNone && st.errFd?.isNone then
      return .ok (.eof (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
    match ← checkTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      closeStreamState files st
      return .error e
    | .ok (true, _) =>
      closeStreamState files st
      return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
    | .ok (false, remMs) =>
      let pollTimeout? : Option Poll.Timespec :=
        timeoutMs?.map fun _ => msToPollTimespec remMs
      match ← poll.ppoll (buildPollEntries st) pollTimeout? with
      | .error e =>
        if e == Errno.EINTR then
          streamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st fuel
        else
          closeStreamState files st
          return .error (mapErrno none "ppoll" e)
      | .ok revents =>
        let (inReady, outReady, errReady) := decodeReadyFlags st revents
        if !inReady && !outReady && !errReady then
          streamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st fuel
        else
          let (inFdNext?, stdinPos', _, inTimedOut, inErr?) ←
            stepStdinIfReady inReady files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel
          match inErr? with
          | some e =>
            closeOpt files st.outFd?
            closeOpt files st.errFd?
            return .error e
          | none =>
            if inTimedOut then
              closeOpt files inFdNext?
              closeOpt files st.outFd?
              closeOpt files st.errFd?
              return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
            let outStep ←
              stepDrainIfReady outReady files timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                st.outChunks st.outLen stepFuel
            match outStep with
            | .ioErr e =>
              closeOpt files inFdNext?
              closeOpt files st.errFd?
              return .error e
            | .timedOut =>
              closeOpt files inFdNext?
              closeOpt files st.errFd?
              return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
            | .limitExceeded outChunks' outLen' =>
              closeOpt files inFdNext?
              closeOpt files st.errFd?
              return .ok (.limitExceeded (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
            | .cont outFdNext? outChunks' outLen' _ =>
              let errStep ←
                stepDrainIfReady errReady files timeRand st.errFd? outLen' startMs timeoutMs? maxOutputBytes?
                  st.errChunks st.errLen stepFuel
              match errStep with
              | .ioErr e =>
                closeOpt files inFdNext?
                closeOpt files outFdNext?
                return .error e
              | .timedOut =>
                closeOpt files inFdNext?
                closeOpt files outFdNext?
                return .ok (.timedOut (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
              | .limitExceeded errChunks' errLen' =>
                closeOpt files inFdNext?
                closeOpt files outFdNext?
                return .ok (.limitExceeded (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
              | .cont errFdNext? errChunks' errLen' _ =>
                if inFdNext?.isNone && outFdNext?.isNone && errFdNext?.isNone then
                  return .ok (.eof (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
                streamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel
                  { inFd? := inFdNext?
                    outFd? := outFdNext?
                    errFd? := errFdNext?
                    stdinPos := stdinPos'
                    outChunks := outChunks'
                    outLen := outLen'
                    errChunks := errChunks'
                    errLen := errLen' }
                  fuel

/-- Decode a reaped `WaitResult` into `ExecOutcome`. -/
def decodeWaitOutcome (wr : LinuxSyscall.Process.WaitResult) (stdout stderr : ByteArray) : ExecOutcome :=
  match wr with
  | .exited _ code => .exited { exitCode := Int.ofNat code.toNat, stdout := stdout, stderr := stderr }
  | .signaled _ sig _ => .signaled (Int.ofNat sig.toNat) stdout stderr
  | _ => .exited { exitCode := 1, stdout := stdout, stderr := stderr }

/-- Blocking `waitpid` loop used when `timeoutMs? = none` (retries `EINTR`, treats `ECHILD` as exit `0`). -/
def waitBlockingLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32)
    (stdout stderr : ByteArray) : Nat → m (Except ProcessError ExecOutcome)
  | 0 => pure (.error (mapRawError (.userError "waitpid EINTR retry budget exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok wr => return .ok (decodeWaitOutcome wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then
        waitBlockingLoop proc pid stdout stderr fuel
      else if e == Errno.ECHILD then
        return .ok (.exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else
        return .error (mapErrno none "waitpid" e)

/-- Non-blocking `WNOHANG` `waitpid` + `clock_nanosleep` loop used when `timeoutMs? = some timeoutMs`. -/
def waitTimedLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) :
    Nat → m (Except ProcessError (Bool × ExecOutcome))
  | 0 => pure (.error (mapRawError (.userError "waitpid timeout loop fuel exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid { nohang := true } with
    | .ok .stillRunning =>
      match ← checkTimedOut timeRand startMs (some timeoutMs) with
      | .error e => return .error e
      | .ok (true, _) => return .ok (false, .timedOut stdout stderr)
      | .ok (false, remMs) =>
        sleepMonoMs timeRand (Nat.min remMs 5)
        waitTimedLoop proc timeRand pid startMs timeoutMs stdout stderr fuel
    | .ok wr =>
      return .ok (true, decodeWaitOutcome wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then
        waitTimedLoop proc timeRand pid startMs timeoutMs stdout stderr fuel
      else if e == Errno.ECHILD then
        return .ok (true, .exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else
        return .error (mapErrno none "waitpid" e)

/-- Set `O_NONBLOCK` on `fd?` if present. -/
def setNonblockingOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) : Option fd → m Unit
  | none => pure ()
  | some h => do
    let _ ← files.fcntl h (.setFl true false)
    pure ()

/-- Close `inFd0?` immediately when `stdin` is empty, or set `O_NONBLOCK` and retain it otherwise. -/
def setupStdinPipe {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (stdin : ByteArray) (inFd0? : Option fd) : m (Option fd) :=
  if stdin.size == 0 then do
    closeOpt files inFd0?
    pure none
  else
    match inFd0? with
    | none => pure none
    | some inFd => do
      let _ ← files.fcntl inFd (.setFl true false)
      pure (some inFd)

/-- Read monotonic start timestamp when `timeoutMs?` is `some _`, or return `0` when `none`. -/
def readStartMsOpt {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) : Option Nat → m (Except ProcessError Nat)
  | none => pure (.ok 0)
  | some _ => monoNowMs timeRand

/-- Pure capability-parameterized implementation of `RawProcessOpsM.awaitOutput`. -/
def awaitOutputPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel ioFuel : Nat) (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs? maxOutputBytes? : Option Nat) : m (Except ProcessError ExecOutcome) := do
  match ← tbl.takeSlotIo h.handleId with
  | none =>
    return .error (mapRawError (.userError "invalid process handle"))
  | some (pid, inFd0?, outFd0?, errFd0?) =>
    let inFd? ← setupStdinPipe deps.files stdin inFd0?
    setNonblockingOpt deps.files outFd0?
    setNonblockingOpt deps.files errFd0?
    match ← readStartMsOpt deps.timeRand timeoutMs? with
    | .error e =>
      closeOpt deps.files inFd?
      closeOpt deps.files outFd0?
      closeOpt deps.files errFd0?
      return .error e
    | .ok startMs =>
      let initSt : StreamLoopState fd :=
        { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
      match ← streamPipesLoop deps.files deps.poll deps.timeRand stdin startMs timeoutMs? maxOutputBytes? eintrFuel initSt ioFuel with
      | .error e => return .error e
      | .ok (.timedOut out err) =>
        let ok ← tbl.markWaited h.handleId false
        if !ok then
          return .error (mapRawError (.userError "process handle vanished"))
        return .ok (.timedOut out err)
      | .ok (.limitExceeded out err) =>
        let ok ← tbl.markWaited h.handleId false
        if !ok then
          return .error (mapRawError (.userError "process handle vanished"))
        return .ok (.outputLimitExceeded out err)
      | .ok (.eof out err) =>
        let pidI32 := pid.toInt32
        match timeoutMs? with
        | none =>
          match ← waitBlockingLoop deps.proc pidI32 out err eintrFuel with
          | .error e => return .error e
          | .ok outcome =>
            let ok ← tbl.markWaited h.handleId true
            if !ok then
              return .error (mapRawError (.userError "process handle vanished"))
            return .ok outcome
        | some timeoutMs =>
          match ← waitTimedLoop deps.proc deps.timeRand pidI32 startMs timeoutMs out err ioFuel with
          | .error e => return .error e
          | .ok (waited, outcome) =>
            let ok ← tbl.markWaited h.handleId waited
            if !ok then
              return .error (mapRawError (.userError "process handle vanished"))
            return .ok outcome

/-- Compute safe `kill(2)` target for isolated process group `pgid` (never returning `-1`). -/
def killTargetOfPgid (pgid : UInt32) : Int32 :=
  if pgid == 1 then 1 else -(pgid.toInt32)

/-- 5-step × 5ms grace probe loop between `SIGTERM` and `SIGKILL` (`true` if group already vanished). -/
def killGraceProbeLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (target : Int32) : Nat → m Bool
  | 0 => pure false
  | steps + 1 => do
    sleepMonoMs timeRand 5
    match ← proc.kill target .sigzero with
    | .error e =>
      if e == Errno.ESRCH then return true
      else killGraceProbeLoop proc timeRand target steps
    | .ok () =>
      killGraceProbeLoop proc timeRand target steps

/-- Pure capability-parameterized implementation of `RawProcessOpsM.killProcessGroup`. -/
def killProcessGroupPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.lookupPgid h.handleId with
  | none => return .ok ()
  | some pgid =>
    if pgid == 0 || pgid > MAX_LINUX_PID then
      return .ok ()
    let target := killTargetOfPgid pgid
    match ← retryEintr (deps.proc.kill target .sigterm) eintrFuel with
    | .error e =>
      if e == Errno.ESRCH then return .ok ()
      else return .error (mapErrno none "kill" e)
    | .ok () =>
      let vanished ← killGraceProbeLoop deps.proc deps.timeRand target 5
      if vanished then
        return .ok ()
      match ← retryEintr (deps.proc.kill target .sigkill) eintrFuel with
      | .error e =>
        if e == Errno.ESRCH then return .ok ()
        else return .error (mapErrno none "kill" e)
      | .ok () =>
        return .ok ()

/-- Reap blocking `waitpid` loop ignoring `ECHILD` and retrying `EINTR` up to `fuel`. -/
def reapWaitLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32) :
    Nat → m (Except ProcessError Unit)
  | 0 => pure (.error (mapRawError (.userError "reap waitpid EINTR retry budget exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok _ => return .ok ()
    | .error e =>
      if e == Errno.EINTR then reapWaitLoop proc pid fuel
      else if e == Errno.ECHILD then return .ok ()
      else return .error (mapErrno none "waitpid" e)

/-- Pure capability-parameterized implementation of `RawProcessOpsM.reap`. -/
def reapPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.detachSlot h.handleId with
  | none => return .ok ()
  | some slot =>
    closeOpt deps.files slot.stdinFd?
    closeOpt deps.files slot.stdoutFd?
    closeOpt deps.files slot.stderrFd?
    if !slot.waited && slot.pid > 0 && slot.pid ≤ MAX_LINUX_PID then
      reapWaitLoop deps.proc slot.pid.toInt32 eintrFuel
    else
      return .ok ()

/-- Construct a `RawProcessOpsM m` bundle purely over `SysDepsM m fd` and `ProcTableOpsM m fd`. -/
def mkRawOpsM {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL)
    (ioFuel : Nat := DEFAULT_IO_FUEL) : RawProcessOpsM m :=
  { mapRawError := mapRawError
    spawn := spawnPure deps tbl eintrFuel
    awaitOutput := awaitOutputPure deps tbl eintrFuel ioFuel
    killProcessGroup := killProcessGroupPure deps tbl eintrFuel
    reap := reapPure deps tbl eintrFuel
    activeProcessCount := tbl.activeCount }

private initialize gProcTable : IO.Ref (ProcTableState RawFd) ← IO.mkRef {}

/-- Default `IO` handle-table capability bundle backing `defaultOps`. -/
def ioProcTableOps : ProcTableOpsM IO RawFd where
  insertSlot slot :=
    (gProcTable.modifyGet fun st => insertSlotPure st slot : BaseIO _)
  takeSlotIo hid :=
    (gProcTable.modifyGet fun st => takeSlotIoPure st hid : BaseIO _)
  markWaited hid waited :=
    (gProcTable.modifyGet fun st => markWaitedPure st hid waited : BaseIO _)
  lookupPgid hid := do
    let st ← (gProcTable.get : BaseIO _)
    return (findSlotPure hid st.slots).map (·.pgid)
  detachSlot hid :=
    (gProcTable.modifyGet fun st => detachSlotPure st hid : BaseIO _)
  activeCount := do
    let st ← (gProcTable.get : BaseIO _)
    return st.slots.length

/-- Default `IO` syscall dependency bundle backing `defaultOps`. -/
def ioSysDeps : SysDepsM IO RawFd where
  proc := LeanSwe.LinuxSyscall.Process.defaultOps
  files := LeanSwe.LinuxSyscall.Files.defaultOps
  poll := LeanSwe.LinuxSyscall.Poll.defaultOps
  timeRand := LeanSwe.LinuxSyscall.TimeRand.defaultOps
  postFork := LeanSwe.PostFork.defaultOps
  listAmbientEnv := do
    let raw ← LeanSwe.EnvVars.Raw.listEnvironBytes
    return .ok raw

/-- Default `IO` `RawProcessOps` bundle backed purely by `LinuxSyscall.{Process,Files,Poll,TimeRand}`, `PostFork`, and `EnvVars.Raw`. -/
def defaultOps : RawProcessOps :=
  let core := mkRawOpsM ioSysDeps ioProcTableOps
  { mapRawError := mapRawError
    spawn := fun req => catchProc (some req.program) (core.spawn req)
    awaitOutput := fun h stdin timeoutMs? maxOutputBytes? =>
      catchProc none (core.awaitOutput h stdin timeoutMs? maxOutputBytes?)
    killProcessGroup := fun h => catchProc none (core.killProcessGroup h)
    reap := fun h => catchProc none (core.reap h)
    activeProcessCount := core.activeProcessCount }

/-- Spawn a child process directly in its own process group via `defaultOps`. -/
@[inline] def spawn (req : ExecRequest) : IO (Except ProcessError ProcessHandle) :=
  defaultOps.spawn req

/-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap via `defaultOps`. -/
@[inline] def awaitOutput
    (h : ProcessHandle)
    (stdin : ByteArray := ByteArray.empty)
    (timeoutMs : Option Nat := none)
    (maxOutputBytes : Option Nat := none) : IO (Except ProcessError ExecOutcome) :=
  defaultOps.awaitOutput h stdin timeoutMs maxOutputBytes

/-- Terminate the child process group (`SIGTERM` followed by `SIGKILL`) via `defaultOps`. -/
@[inline] def killProcessGroup (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultOps.killProcessGroup h

/-- Wait for and release a spawned child handle via `defaultOps`. -/
@[inline] def reap (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultOps.reap h

/-- Return the count of currently active unreaped process handles via `defaultOps`. -/
@[inline] def activeProcessCount : IO Nat :=
  defaultOps.activeProcessCount

end LeanSwe.Process.SysBridge
