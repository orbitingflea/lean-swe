import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.SysBridge.ErrorAndEnv

/-!
Fuel-bounded `ppoll(2)`-driven non-blocking `stdin` write and `stdout` / `stderr` pipe
drain loops for `LeanSwe.Process.SysBridge`.
-/

namespace LeanSwe.Process.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Outcome of draining or writing one non-blocking pipe during a single streaming round. -/
inductive PipeStepResult (fd : Type) where
  /-- Normal round completion with updated descriptor (`none` if closed) and progress flag. -/
  | cont (fd? : Option fd) (chunks : Array ByteArray) (len : Nat) (madeProgress : Bool)
  /-- Timeout deadline reached during step; `chunks` and `len` carry the full accumulated output (from prior rounds and this round) at timeout, so callers replace rather than re-append. -/
  | timedOut (chunks : Array ByteArray) (len : Nat)
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
      Files.closeOpt files (some inFd)
      return .ok (none, pos, prog, false)
    else
      return .ok (some inFd, pos, prog, false)
  | pos, prog, fuel + 1 => do
    if pos ≥ stdin.size then
      Files.closeOpt files (some inFd)
      return .ok (none, pos, true, false)
    else
      match ← TimeRand.checkTimedOut timeRand startMs timeoutMs? with
      | .error e =>
        Files.closeOpt files (some inFd)
        return .error (mapErrno none "clock_gettime" e)
      | .ok (true, _) =>
        Files.closeOpt files (some inFd)
        return .ok (none, pos, prog, true)
      | .ok (false, _) =>
        let endIdx := Nat.min stdin.size (pos + STDIN_WRITE_CHUNK)
        let slice := stdin.extract pos endIdx
        match ← files.write inFd slice with
        | .ok n =>
          if n == 0 then
            Files.closeOpt files (some inFd)
            return .ok (none, pos, prog, false)
          else
            let pos' := pos + n.toNat
            if pos' ≥ stdin.size then
              Files.closeOpt files (some inFd)
              return .ok (none, pos', true, false)
            else
              writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos' true fuel
        | .error e =>
          if e == Errno.EINTR then
            writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos prog fuel
          else if e == Errno.EAGAIN then
            return .ok (some inFd, pos, prog, false)
          else
            Files.closeOpt files (some inFd)
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
    match ← TimeRand.checkTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      Files.closeOpt files (some pipeFd)
      return .ioErr (mapErrno none "clock_gettime" e)
    | .ok (true, _) =>
      Files.closeOpt files (some pipeFd)
      return .timedOut chunks curLen
    | .ok (false, _) =>
      match ← files.read pipeFd PIPE_READ_CHUNK with
      | .ok chunk =>
        if chunk.size == 0 then
          Files.closeOpt files (some pipeFd)
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
              Files.closeOpt files (some pipeFd)
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
          Files.closeOpt files (some pipeFd)
          return .ioErr (mapErrno none "read" e)

/-- Close all still-open parent pipe handles in `st`. -/
def closeStreamState {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (st : StreamLoopState fd) : m Unit := do
  Files.closeOpt files st.inFd?
  Files.closeOpt files st.outFd?
  Files.closeOpt files st.errFd?

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

/-- Extract `(inReady, outReady, errReady)` from `ppoll(2)` `revents` aligned with `buildPollEntries st`. -/
def decodeReadyFlags {fd : Type} (st : StreamLoopState fd) (revents : Array Poll.PollEvents) :
    Bool × Bool × Bool :=
  let (inReady, i1) := match st.inFd? with
    | none => (false, 0)
    | some _ => (match revents[0]? with | some ev => Poll.pollEvReady true ev | none => true, 1)
  let (outReady, i2) := match st.outFd? with
    | none => (false, i1)
    | some _ => (match revents[i1]? with | some ev => Poll.pollEvReady false ev | none => true, i1 + 1)
  let errReady := match st.errFd? with
    | none => false
    | some _ => match revents[i2]? with | some ev => Poll.pollEvReady false ev | none => true
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
    match ← TimeRand.checkTimedOut timeRand startMs timeoutMs? with
    | .error e =>
      closeStreamState files st
      return .error (mapErrno none "clock_gettime" e)
    | .ok (true, _) =>
      closeStreamState files st
      return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
    | .ok (false, remMs) =>
      let pollTimeout? : Option Poll.Timespec :=
        timeoutMs?.map fun _ => Poll.msToPollTimespec remMs
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
            Files.closeOpt files st.outFd?
            Files.closeOpt files st.errFd?
            return .error e
          | none =>
            if inTimedOut then
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.outFd?
              Files.closeOpt files st.errFd?
              return .ok (.timedOut (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen))
            let outStep ←
              stepDrainIfReady outReady files timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                st.outChunks st.outLen stepFuel
            match outStep with
            | .ioErr e =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              return .error e
            | .timedOut outChunks' outLen' =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              return .ok (.timedOut (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
            | .limitExceeded outChunks' outLen' =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              return .ok (.limitExceeded (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen))
            | .cont outFdNext? outChunks' outLen' _ =>
              let errStep ←
                stepDrainIfReady errReady files timeRand st.errFd? outLen' startMs timeoutMs? maxOutputBytes?
                  st.errChunks st.errLen stepFuel
              match errStep with
              | .ioErr e =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
                return .error e
              | .timedOut errChunks' errLen' =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
                return .ok (.timedOut (concatChunks outChunks' outLen') (concatChunks errChunks' errLen'))
              | .limitExceeded errChunks' errLen' =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
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

end LeanSwe.Process.SysBridge
