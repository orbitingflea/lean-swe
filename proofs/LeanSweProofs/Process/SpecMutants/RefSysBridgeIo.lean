import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.PostFork.Types
import LeanSweProofs.PostFork.Model
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSweProofs.Process.Model

/-!
Pure spec-passing reference `PATH` resolution, `cwd` validation, and `ppoll`-driven pipe
streaming helpers over `.Types` and `.Model` for single-bug `LeanSwe.Process` mutants.
-/

namespace LeanSwe.Process.SpecMutants

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.Internal (StreamLoopState StreamPhaseOutcome)

/-- Best-effort close of an optional descriptor handle. -/
def refCloseOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) : Option fd → m Unit
  | none => pure ()
  | some h => do
    let _ ← files.close h
    pure ()

/-- Set `O_NONBLOCK` on an optional descriptor handle if present. -/
def refSetNonblockingOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) : Option fd → m Unit
  | none => pure ()
  | some h => do
    let _ ← files.fcntl h (.setFl true false)
    pure ()

/-- Return `true` iff a `ppoll(2)` `revents` entry signals readiness, hangup, error, or invalid FD. -/
def refPollEvReady (wantOut : Bool) (ev : Poll.PollEvents) : Bool :=
  (if wantOut then ev.pollout else ev.pollin) || ev.pollhup || ev.pollerr || ev.pollnval

/-- Convert a relative timeout in milliseconds to a valid `Poll.Timespec`. -/
def refMsToPollTimespec (ms : Nat) : Poll.Timespec :=
  let clampedSec := Nat.min (ms / 1000) 9223372036854775807
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

/-- Convert a non-negative `TimeRand.Timespec` reading to milliseconds. -/
def refTimespecToMs (ts : TimeRand.Timespec) : Nat :=
  ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000

/-- Read `CLOCK_MONOTONIC` in milliseconds via `timeRand.clock_gettime`. -/
def refMonoNowMs {m : Type → Type} [Monad m] (timeRand : TimeRand.TimeRandOpsM m) :
    m (Except Errno Nat) := do
  match ← timeRand.clock_gettime .monotonic with
  | .ok ts => return .ok (refTimespecToMs ts)
  | .error e => return .error e

/-- Check whether optional deadline `timeoutMs?` has expired relative to `startMs`. -/
def refCheckTimedOut {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) (startMs : Nat) :
    Option Nat → m (Except Errno (Bool × Nat))
  | none => pure (.ok (false, 0))
  | some timeoutMs => do
    match ← refMonoNowMs timeRand with
    | .error e => return .error e
    | .ok nowMs =>
      let elapsed := nowMs - startMs
      if elapsed ≥ timeoutMs then return .ok (true, 0)
      else return .ok (false, timeoutMs - elapsed)

/-- Sleep on `CLOCK_MONOTONIC` for `ms` milliseconds. -/
def refSleepMonoMs {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) (ms : Nat) : m Unit := do
  let clampedSec := Nat.min (ms / 1000) TimeRand.MAX_TIMESPEC_SEC
  let remNs := (ms % 1000) * 1000000
  let _ ← timeRand.clock_nanosleep .monotonic false
    { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }
  pure ()

/-- Return `err` with a non-empty fallback message if `err.message` is empty. -/
def refEnsureNonEmptyMsg (fallback : String) (err : ProcessError) : ProcessError :=
  if err.message.isEmpty then { err with message := fallback } else err

private def isInvalidInputErrnoRef (e : Errno) : Bool :=
  e == Errno.EINVAL || e == Errno.ENAMETOOLONG || e == Errno.ELOOP ||
  e == Errno.ENOEXEC || e == Errno.E2BIG

/-- Map a Linux `Errno` with optional target path/program and context detail into `ProcessError`. -/
def refMapErrno (prog? : Option String) (ctx : String) (e : Errno) : ProcessError :=
  let detail := s!"{ctx}: {Errno.name e}"
  if e == Errno.ENOENT then
    let mapped := Model.mapRawErrorModel (.executableNotFound (prog?.getD "") e detail)
    { mapped with program := prog? <|> mapped.program }
  else if e == Errno.EACCES || e == Errno.EPERM then
    Model.mapRawErrorModel (.permissionDenied prog? e detail)
  else if isInvalidInputErrnoRef e then
    Model.mapRawErrorModel (.invalidArgument prog? e detail)
  else
    let mapped := Model.mapRawErrorModel (.otherError e detail)
    { mapped with program := prog? }

private def hasByteNulRef (b : ByteArray) : Bool :=
  b.toList.any (· == (0 : UInt8))

private def bytesHasPrefixEqRef (key entry : ByteArray) : Bool :=
  if h : key.size < entry.size then
    entry.extract 0 key.size == key && entry[key.size] == (0x3D : UInt8)
  else false

/-- Merge explicit `overrides` onto raw `environ(7)` byte entries. -/
def refMergeRawEnvOverrides (base : Array ByteArray)
    (overrides : Array (String × Option String)) : Array ByteArray :=
  let cleanBase := base.filter (fun b => !hasByteNulRef b)
  overrides.foldl
    (fun acc (k, v?) =>
      let kb := k.toUTF8
      let withoutKey := acc.filter (fun e => !bytesHasPrefixEqRef kb e)
      match v? with
      | none => withoutKey
      | some v => withoutKey.push (kb ++ ByteArray.mk #[0x3D] ++ v.toUTF8))
    cleanBase

private def findEnvPathRawRef (envBytes : Array ByteArray) : Option ByteArray :=
  let pathKey := "PATH".toUTF8
  envBytes.findSome? fun e =>
    if bytesHasPrefixEqRef pathKey e then some (e.extract (pathKey.size + 1) e.size) else none

private def splitPosixPathBytesRef (rawPath : ByteArray) : List ByteArray :=
  (splitByte (0x3A : UInt8) rawPath).map fun seg =>
    if seg.size == 0 then ".".toUTF8 else seg

/-- Compute host filesystem path bytes probed for `dir` and `program` under `cwd?`. -/
def refProbePathBytes (cwd? : Option String) (dir program : String) : ByteArray :=
  let execCand := dir ++ "/" ++ program
  let hostProbe :=
    match cwd? with
    | some cwdDir =>
      if dir.toList.head? == some '/' || cwdDir.isEmpty then execCand
      else cwdDir ++ "/" ++ execCand
    | none => execCand
  hostProbe.toUTF8

private def isPermPathSearchErrnoRef (e : Errno) : Bool :=
  e == Errno.EACCES || e == Errno.EPERM || e == Errno.EISDIR || e == Errno.EROFS

private def isMissingPathSearchErrnoRef (e : Errno) : Bool :=
  e == Errno.ENOENT || e == Errno.ENOTDIR

private def searchPathDirsRef {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (eintrFuel : Nat) (sawPerm : Bool) : List String → m (Except ProcessError String)
  | [] =>
    if sawPerm then
      pure (.error (Model.mapRawErrorModel (.permissionDenied (some program) Errno.EACCES "permission denied")))
    else
      pure (.error (Model.mapRawErrorModel (.executableNotFound program Errno.ENOENT s!"executable not found: {program}")))
  | dir :: rest => do
    let execCand := dir ++ "/" ++ program
    let pathBytes := refProbePathBytes cwd? dir program
    match ← retryEintr (files.fstatat none pathBytes {}) eintrFuel with
    | .error e =>
      if isPermPathSearchErrnoRef e then searchPathDirsRef files program cwd? eintrFuel true rest
      else if isMissingPathSearchErrnoRef e then searchPathDirsRef files program cwd? eintrFuel sawPerm rest
      else pure (.error (refMapErrno (some program) "execvp" e))
    | .ok st =>
      if st.kind != .reg then
        searchPathDirsRef files program cwd? eintrFuel true rest
      else
        match ← retryEintr (files.faccessat none pathBytes { exec := true } { eaccess := true }) eintrFuel with
        | .ok () => pure (.ok execCand)
        | .error e =>
          if isPermPathSearchErrnoRef e then searchPathDirsRef files program cwd? eintrFuel true rest
          else if isMissingPathSearchErrnoRef e then searchPathDirsRef files program cwd? eintrFuel sawPerm rest
          else pure (.error (refMapErrno (some program) "execvp" e))

/-- Pre-validate optional working directory `cwd?` matching child `chdir(2)` semantics. -/
def refValidateWorkingDir {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cwd? : Option String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except ProcessError Unit) :=
  match cwd? with
  | none => pure (.ok ())
  | some cwdDir => do
    if cwdDir.isEmpty then return .error (refMapErrno (some cwdDir) "chdir" Errno.ENOENT)
    let cwdBytes := cwdDir.toUTF8
    match ← retryEintr (files.fstatat none cwdBytes {}) eintrFuel with
    | .error e => return .error (refMapErrno (some cwdDir) "chdir" e)
    | .ok st =>
      if st.kind != .dir then return .error (refMapErrno (some cwdDir) "chdir" Errno.ENOTDIR)
      match ← retryEintr (files.faccessat none cwdBytes { exec := true } { eaccess := true }) eintrFuel with
      | .error e => return .error (refMapErrno (some cwdDir) "chdir" e)
      | .ok () => return .ok ()

/-- Resolve `program` against effective child `PATH` bytes when `'/' ∉ program`. -/
def refResolveExecutablePath {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (envBytes : Array ByteArray) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except ProcessError String) :=
  if program.toList.contains '/' then pure (.ok program)
  else
    let rawPath := (findEnvPathRawRef envBytes).getD "/bin:/usr/bin".toUTF8
    let dirs := (splitPosixPathBytesRef rawPath).filterMap String.fromUTF8?
    searchPathDirsRef files program cwd? eintrFuel false dirs

private inductive RefPipeStepResult (fd : Type) where
  | cont (fd? : Option fd) (chunks : Array ByteArray) (len : Nat) (madeProgress : Bool)
  | timedOut (chunks : Array ByteArray) (len : Nat)
  | limitExceeded (chunks : Array ByteArray) (len : Nat)
  | ioErr (err : ProcessError)

private def writeStdinStepRef {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd : fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat) :
    Nat → Bool → Nat → m (Except ProcessError (Option fd × Nat × Bool × Bool))
  | pos, prog, 0 =>
    if pos ≥ stdin.size then do
      refCloseOpt files (some inFd)
      return .ok (none, pos, prog, false)
    else return .ok (some inFd, pos, prog, false)
  | pos, prog, fuel + 1 => do
    if pos ≥ stdin.size then
      refCloseOpt files (some inFd)
      return .ok (none, pos, true, false)
    else
      match ← refCheckTimedOut timeRand startMs timeoutMs? with
      | .error e =>
        refCloseOpt files (some inFd)
        return .error (refMapErrno none "clock_gettime" e)
      | .ok (true, _) =>
        refCloseOpt files (some inFd)
        return .ok (none, pos, prog, true)
      | .ok (false, _) =>
        let slice := stdin.extract pos (Nat.min stdin.size (pos + 65536))
        match ← files.write inFd slice with
        | .ok n =>
          if n == 0 then
            refCloseOpt files (some inFd)
            return .ok (none, pos, prog, false)
          else
            let pos' := pos + n.toNat
            if pos' ≥ stdin.size then
              refCloseOpt files (some inFd)
              return .ok (none, pos', true, false)
            else writeStdinStepRef files timeRand inFd stdin startMs timeoutMs? pos' true fuel
        | .error e =>
          if e == Errno.EINTR then writeStdinStepRef files timeRand inFd stdin startMs timeoutMs? pos prog fuel
          else if e == Errno.EAGAIN then return .ok (some inFd, pos, prog, false)
          else
            refCloseOpt files (some inFd)
            return .ok (none, pos, true, false)

/-- Execute one non-blocking `stdin` write round if `inFd?` is still open. -/
def refStepStdinOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd? : Option fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (stdinPos stepFuel : Nat) :
    m (Option fd × Nat × Bool × Bool × Option ProcessError) :=
  match inFd? with
  | none => pure (none, stdinPos, false, false, none)
  | some inFd => do
    match ← writeStdinStepRef files timeRand inFd stdin startMs timeoutMs? stdinPos false stepFuel with
    | .error e => pure (none, stdinPos, false, false, some e)
    | .ok (nextFd?, p', pr, to) => pure (nextFd?, p', pr, to, none)

private def drainPipeStepRef {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pipeFd : fd) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat) :
    Array ByteArray → Nat → Nat → Bool → Nat → m (RefPipeStepResult fd)
  | chunks, curLen, _, prog, 0 => pure (.cont (some pipeFd) chunks curLen prog)
  | chunks, curLen, iterBytes, prog, fuel + 1 => do
    if iterBytes ≥ 65536 then return .cont (some pipeFd) chunks curLen prog
    match ← refCheckTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      refCloseOpt files (some pipeFd)
      return .ioErr (refMapErrno none "clock_gettime" e)
    | .ok (true, _) =>
      refCloseOpt files (some pipeFd)
      return .timedOut chunks curLen
    | .ok (false, _) =>
      match ← files.read pipeFd 8192 with
      | .ok chunk =>
        if chunk.size == 0 then
          refCloseOpt files (some pipeFd)
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
                else (chunks, curLen)
              refCloseOpt files (some pipeFd)
              return .limitExceeded chunks' curLen'
            else
              drainPipeStepRef files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
                (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel
          | none =>
            drainPipeStepRef files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
              (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel
      | .error e =>
        if e == Errno.EINTR then
          drainPipeStepRef files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
            chunks curLen iterBytes prog fuel
        else if e == Errno.EAGAIN then return .cont (some pipeFd) chunks curLen prog
        else
          refCloseOpt files (some pipeFd)
          return .ioErr (refMapErrno none "read" e)

private def closeStreamStateRef {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (st : StreamLoopState fd) : m Unit := do
  refCloseOpt files st.inFd?
  refCloseOpt files st.outFd?
  refCloseOpt files st.errFd?

private def buildPollEntriesRef {fd : Type} (st : StreamLoopState fd) : Array (fd × Poll.PollEvents) :=
  let a0 := match st.inFd? with | some h => #[(h, { pollout := true })] | none => #[]
  let a1 := match st.outFd? with | some h => a0.push (h, { pollin := true }) | none => a0
  match st.errFd? with | some h => a1.push (h, { pollin := true }) | none => a1

private def decodeReadyFlagsRef {fd : Type} (st : StreamLoopState fd) (revents : Array Poll.PollEvents) :
    Bool × Bool × Bool :=
  let (inReady, i1) := match st.inFd? with
    | none => (false, 0)
    | some _ => (match revents[0]? with | some ev => refPollEvReady true ev | none => true, 1)
  let (outReady, i2) := match st.outFd? with
    | none => (false, i1)
    | some _ => (match revents[i1]? with | some ev => refPollEvReady false ev | none => true, i1 + 1)
  let errReady := match st.errFd? with
    | none => false
    | some _ => match revents[i2]? with | some ev => refPollEvReady false ev | none => true
  (inReady, outReady, errReady)

/-- Fuel-bounded `ppoll(2)`-driven pipe streaming loop. -/
def refStreamPipesLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (poll : Poll.PollOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (stdin : ByteArray) (startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat) (stepFuel : Nat) :
    StreamLoopState fd → Nat → m (Except ProcessError StreamPhaseOutcome)
  | st, 0 => do
    closeStreamStateRef files st
    return .error (Model.mapRawErrorModel (.userError "process I/O loop fuel exhausted"))
  | st, fuel + 1 => do
    if st.inFd?.isNone && st.outFd?.isNone && st.errFd?.isNone then
      return .ok (.eof (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
    match ← refCheckTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      closeStreamStateRef files st
      return .error (refMapErrno none "clock_gettime" e)
    | .ok (true, _) =>
      closeStreamStateRef files st
      return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
    | .ok (false, remMs) =>
      let pollTimeout? := timeoutMs?.map fun _ => refMsToPollTimespec remMs
      match ← poll.ppoll (buildPollEntriesRef st) pollTimeout? with
      | .error e =>
        if e == Errno.EINTR then
          refStreamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st fuel
        else
          closeStreamStateRef files st
          return .error (refMapErrno none "ppoll" e)
      | .ok revents =>
        let (inReady, outReady, errReady) := decodeReadyFlagsRef st revents
        if !inReady && !outReady && !errReady then
          refStreamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st fuel
        else
          let (inFdNext?, stdinPos', _, inTimedOut, inErr?) ←
            if inReady then refStepStdinOpt files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel
            else pure (st.inFd?, st.stdinPos, false, false, none)
          match inErr? with
          | some e =>
            refCloseOpt files st.outFd?
            refCloseOpt files st.errFd?
            return .error e
          | none =>
            if inTimedOut then
              refCloseOpt files inFdNext?
              refCloseOpt files st.outFd?
              refCloseOpt files st.errFd?
              return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
            let outStep ←
              if outReady then
                match st.outFd? with
                | none => pure (.cont none st.outChunks st.outLen false)
                | some pipeFd =>
                  drainPipeStepRef files timeRand pipeFd st.errLen startMs timeoutMs? maxOutputBytes?
                    st.outChunks st.outLen 0 false stepFuel
              else pure (.cont st.outFd? st.outChunks st.outLen false)
            match outStep with
            | .ioErr e =>
              refCloseOpt files inFdNext?
              refCloseOpt files st.errFd?
              return .error e
            | .timedOut outChunks' outLen' =>
              refCloseOpt files inFdNext?
              refCloseOpt files st.errFd?
              return .ok (.timedOut (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
            | .limitExceeded outChunks' outLen' =>
              refCloseOpt files inFdNext?
              refCloseOpt files st.errFd?
              return .ok (.limitExceeded (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
            | .cont outFdNext? outChunks' outLen' _ =>
              let errStep ←
                if errReady then
                  match st.errFd? with
                  | none => pure (.cont none st.errChunks st.errLen false)
                  | some pipeFd =>
                    drainPipeStepRef files timeRand pipeFd outLen' startMs timeoutMs? maxOutputBytes?
                      st.errChunks st.errLen 0 false stepFuel
                else pure (.cont st.errFd? st.errChunks st.errLen false)
              match errStep with
              | .ioErr e =>
                refCloseOpt files inFdNext?
                refCloseOpt files outFdNext?
                return .error e
              | .timedOut errChunks' errLen' =>
                refCloseOpt files inFdNext?
                refCloseOpt files outFdNext?
                return .ok (.timedOut (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
              | .limitExceeded errChunks' errLen' =>
                refCloseOpt files inFdNext?
                refCloseOpt files outFdNext?
                return .ok (.limitExceeded (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
              | .cont errFdNext? errChunks' errLen' _ =>
                if inFdNext?.isNone && outFdNext?.isNone && errFdNext?.isNone then
                  return .ok (.eof (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
                refStreamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel
                  { inFd? := inFdNext?, outFd? := outFdNext?, errFd? := errFdNext?,
                    stdinPos := stdinPos', outChunks := outChunks', outLen := outLen',
                    errChunks := errChunks', errLen := errLen' }
                  fuel

end LeanSwe.Process.SpecMutants
