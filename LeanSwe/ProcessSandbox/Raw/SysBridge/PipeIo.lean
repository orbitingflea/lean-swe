import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

/-- Per-read chunk size (`8192` bytes) when draining sandbox `stdout` / `stderr` pipes. -/
def PIPE_READ_CHUNK : UInt32 := 8192

/-- Per-round per-stream byte cap (`65536` bytes) preventing one chatty pipe from starving the other. -/
def STREAM_FAIRNESS_BYTES : Nat := 65536

/-- Maximum slice size (`65536` bytes) passed per `write(2)` call on sandbox `stdin`. -/
def STDIN_WRITE_CHUNK : Nat := 65536

/-- Outcome of draining one non-blocking sandbox pipe during a single streaming round. -/
inductive PipeStepResult (fd : Type) where
  /-- Normal round completion with updated descriptor (`none` if closed) and progress flag. -/
  | cont (fd? : Option fd) (chunks : Array ByteArray) (len : Nat) (madeProgress : Bool)
  /-- Timeout deadline reached during step; `chunks` and `len` hold all accumulated output. -/
  | timedOut (chunks : Array ByteArray) (len : Nat)
  /-- `maxOutputBytes` exceeded (captures prefix up to `maxOutputBytes`). -/
  | limitExceeded (chunks : Array ByteArray) (len : Nat)
  /-- Non-recoverable OS read error normalized to `SandboxError`. -/
  | ioErr (err : SandboxError)

/-- Close `inFd0?` immediately when `stdin` is empty, or set `O_NONBLOCK` and retain it otherwise. -/
def setupStdinPipe {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (stdin : ByteArray) (inFd0? : Option fd) : m (Option fd) :=
  if stdin.size == 0 then do
    Files.closeOpt files inFd0?
    pure none
  else
    match inFd0? with
    | none => pure none
    | some inFd => do
      let _ ← files.fcntl inFd (.setFl true false)
      pure (some inFd)

/-- Write as much of `stdin[pos..]` as non-blocking `inFd` accepts in this round. -/
def writeStdinStep {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (inFd : fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat) :
    Nat → Bool → Nat → m (Except SandboxError (Option fd × Nat × Bool × Bool))
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
        return .error (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
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
      return .ioErr (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
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
          return .ioErr (Internal.mapRawError (.ioError none e s!"read: {Errno.name e}"))

end LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo
