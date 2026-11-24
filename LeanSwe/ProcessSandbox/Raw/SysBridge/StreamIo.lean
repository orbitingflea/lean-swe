import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Model.InitStatus
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
import LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
import LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo

export LeanSwe.ProcessSandbox.Raw.Model
  (PS_STATUS_READY PS_STATUS_INIT_ERR PS_STATUS_EXEC_ERR PS_STATUS_EXITED PS_STATUS_SIGNALED
   InitStatusMsg encodeInitStatusMsg decodeInitStatusMsg)

/-- Blocking read of an 8-byte `InitStatusMsg` during `spawnBox` pre-`execvp` handshake (retrying `EINTR`, stopping on EOF/error). -/
def readInitStatusBlocking {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (statusFd : fd) :
    ByteArray → Nat → m (Option InitStatusMsg × Option Errno)
  | buf, 0 => pure (decodeInitStatusMsg buf, none)
  | buf, fuel + 1 => do
    if buf.size >= 8 then
      return (decodeInitStatusMsg buf, none)
    let want := 8 - buf.size
    match ← files.read statusFd (UInt32.ofNat want) with
    | .ok bs =>
      if bs.size == 0 then
        return (decodeInitStatusMsg buf, none)
      else
        let buf' := buf ++ bs
        if buf'.size >= 8 then
          return (decodeInitStatusMsg buf', none)
        else
          readInitStatusBlocking files statusFd buf' fuel
    | .error e =>
      if e == Errno.EINTR then
        readInitStatusBlocking files statusFd buf fuel
      else
        return (none, some e)

/-- Non-blocking step reading remaining bytes of the 8-byte `InitStatusMsg` from `statusFd`. -/
def readInitStatusStep {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (statusFd : fd) :
    ByteArray → Nat → m (Option fd × ByteArray × Option InitStatusMsg)
  | buf, 0 => pure (some statusFd, buf, decodeInitStatusMsg buf)
  | buf, fuel + 1 => do
    if buf.size >= 8 then
      Files.closeOpt files (some statusFd)
      return (none, buf, decodeInitStatusMsg buf)
    let want := 8 - buf.size
    match ← files.read statusFd (UInt32.ofNat want) with
    | .ok bs =>
      if bs.size == 0 then
        Files.closeOpt files (some statusFd)
        return (none, buf, none)
      else
        let buf' := buf ++ bs
        if buf'.size >= 8 then
          Files.closeOpt files (some statusFd)
          return (none, buf', decodeInitStatusMsg buf')
        else
          readInitStatusStep files statusFd buf' fuel
    | .error e =>
      if e == Errno.EINTR then
        readInitStatusStep files statusFd buf fuel
      else if e == Errno.EAGAIN then
        return (some statusFd, buf, none)
      else
        Files.closeOpt files (some statusFd)
        return (none, buf, none)

/-- Mutable 4-FD state carried across `readBoxStreamLoop` iterations. -/
structure BoxStreamState (fd : Type) where
  /-- Parent write end of guest `stdin` pipe (`none` once closed). -/
  inFd? : Option fd
  /-- Parent read end of guest `stdout` pipe (`none` once closed). -/
  outFd? : Option fd
  /-- Parent read end of guest `stderr` pipe (`none` once closed). -/
  errFd? : Option fd
  /-- Parent read end of `psandbox_init` `status_pipe` (`none` once closed). -/
  statusFd? : Option fd
  /-- Byte offset written into `stdin`. -/
  stdinPos : Nat := 0
  /-- Accumulated `stdout` byte chunks. -/
  outChunks : Array ByteArray := #[]
  /-- Total bytes in `outChunks`. -/
  outLen : Nat := 0
  /-- Accumulated `stderr` byte chunks. -/
  errChunks : Array ByteArray := #[]
  /-- Total bytes in `errChunks`. -/
  errLen : Nat := 0
  /-- Partial bytes accumulated from `statusFd?`. -/
  statusBuf : ByteArray := ByteArray.empty
  /-- Decoded terminal `InitStatusMsg`, if received. -/
  statusMsg? : Option InitStatusMsg := none

/-- Close all still-open descriptors in `BoxStreamState`. -/
def closeBoxStreamState {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (st : BoxStreamState fd) : m Unit := do
  Files.closeOpt files st.inFd?
  Files.closeOpt files st.outFd?
  Files.closeOpt files st.errFd?
  Files.closeOpt files st.statusFd?

/-- Build the 4-FD `ppoll(2)` descriptor array for `st` (`stdin` `POLLOUT`; `stdout`, `stderr`, `status` `POLLIN`). -/
def buildBoxPollEntries {fd : Type} (st : BoxStreamState fd) : Array (fd × Poll.PollEvents) :=
  let a0 := match st.inFd? with | some h => #[(h, { pollout := true })] | none => #[]
  let a1 := match st.outFd? with | some h => a0.push (h, { pollin := true }) | none => a0
  let a2 := match st.errFd? with | some h => a1.push (h, { pollin := true }) | none => a1
  match st.statusFd? with | some h => a2.push (h, { pollin := true }) | none => a2

/-- Decode `(inRev?, outReady, errReady, stReady)` aligned with `buildBoxPollEntries st`. -/
def decodeBoxReadyFlags {fd : Type} (st : BoxStreamState fd) (revents : Array Poll.PollEvents) :
    Option Poll.PollEvents × Bool × Bool × Bool :=
  let (inRev?, i1) := match st.inFd? with
    | none => (none, 0)
    | some _ => (some (revents[0]?.getD ({} : Poll.PollEvents)), 1)
  let (outReady, i2) := match st.outFd? with
    | none => (false, i1)
    | some _ => (match revents[i1]? with | some ev => Poll.pollEvReady false ev | none => true, i1 + 1)
  let (errReady, i3) := match st.errFd? with
    | none => (false, i2)
    | some _ => (match revents[i2]? with | some ev => Poll.pollEvReady false ev | none => true, i2 + 1)
  let stReady := match st.statusFd? with
    | none => false
    | some _ => match revents[i3]? with | some ev => Poll.pollEvReady false ev | none => true
  (inRev?, outReady, errReady, stReady)

/-- Classify the completed stream phase into `Except SandboxError SandboxResult` for `Raw.SysBridge` / `StreamIo`. -/
def classifyBoxStreamResult (program cwd : String)
    (timedOut limitExceeded : Bool) (statusMsg? : Option InitStatusMsg)
    (stdout stderr : ByteArray) : Except SandboxError SandboxResult :=
  match statusMsg? with
  | some msg =>
    if msg.kind == PS_STATUS_EXEC_ERR then
      let errCode : Errno := if msg.value == 0 then Errno.EIO else msg.value.toUInt32
      let targetPath := if msg.flag != 0 then cwd else program
      let ctx := if msg.flag != 0 then "chdir" else "execvp"
      .error (mapPathErrnoToSandboxError targetPath ctx errCode)
    else if !timedOut && !limitExceeded && msg.kind == PS_STATUS_INIT_ERR then
      let errCode : Errno := if msg.value == 0 then Errno.EPERM else msg.value.toUInt32
      .error (Internal.mapRawError (.unavailable (some errCode) s!"sandbox init failed before execvp: {Errno.name errCode}"))
    else if timedOut then
      .ok { outcome := .timedOut, stdout := stdout, stderr := stderr }
    else if limitExceeded then
      .ok { outcome := .outputLimitExceeded, stdout := stdout, stderr := stderr }
    else if msg.kind == PS_STATUS_EXITED then
      .ok { outcome := .exited (Int.ofNat msg.value.toUInt32.toNat), stdout := stdout, stderr := stderr }
    else if msg.kind == PS_STATUS_SIGNALED then
      .ok { outcome := .signaled (Int.ofNat msg.value.toUInt32.toNat), stdout := stdout, stderr := stderr }
    else
      .ok { outcome := .signaled 9, stdout := stdout, stderr := stderr }
  | none =>
    if timedOut then
      .ok { outcome := .timedOut, stdout := stdout, stderr := stderr }
    else if limitExceeded then
      .ok { outcome := .outputLimitExceeded, stdout := stdout, stderr := stderr }
    else
      .ok { outcome := .signaled 9, stdout := stdout, stderr := stderr }

/-- Fuel-bounded 4-FD `ppoll(2)` loop streaming `stdin`/`stdout`/`stderr` and decoding `InitStatusMsg` from `status_fd`, using `Raw.SysBridge.PipeIo` pipe helpers. -/
def readBoxStreamLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (poll : Poll.PollOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (program cwd : String) (stdin : ByteArray)
    (startMs timeoutMs : Nat) (maxOutputBytes? : Option Nat) (stepFuel : Nat) :
    BoxStreamState fd → Nat → m (Except SandboxError SandboxResult)
  | st, 0 => do
    closeBoxStreamState files st
    return .error (Internal.mapRawError (.ioError none Errno.EIO "sandbox I/O loop fuel exhausted"))
  | st, fuel + 1 => do
    if st.outFd?.isNone && st.errFd?.isNone && st.statusFd?.isNone then
      Files.closeOpt files st.inFd?
      return classifyBoxStreamResult program cwd false false st.statusMsg?
        (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen)
    match ← TimeRand.checkTimedOut timeRand startMs (some timeoutMs) with
    | .error e =>
      closeBoxStreamState files st
      return .error (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
    | .ok (true, _) =>
      closeBoxStreamState files st
      return classifyBoxStreamResult program cwd true false st.statusMsg?
        (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen)
    | .ok (false, remMs) =>
      match ← poll.ppoll (buildBoxPollEntries st) (some (Poll.msToPollTimespec remMs)) with
      | .error e =>
        if e == Errno.EINTR then
          readBoxStreamLoop files poll timeRand program cwd stdin startMs timeoutMs maxOutputBytes? stepFuel st fuel
        else
          closeBoxStreamState files st
          return .error (Internal.mapRawError (.ioError none e s!"ppoll: {Errno.name e}"))
      | .ok revents =>
        let (inRev?, outReady, errReady, stReady) := decodeBoxReadyFlags st revents
        let inAny := match inRev? with | some ev => Poll.pollEvReady true ev | none => false
        if !inAny && !outReady && !errReady && !stReady then
          match ← TimeRand.checkTimedOut timeRand startMs (some timeoutMs) with
          | .error e =>
            closeBoxStreamState files st
            return .error (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
          | .ok (true, _) =>
            closeBoxStreamState files st
            return classifyBoxStreamResult program cwd true false st.statusMsg?
              (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen)
          | .ok (false, _) =>
            readBoxStreamLoop files poll timeRand program cwd stdin startMs timeoutMs maxOutputBytes? stepFuel st fuel
        else
          let (inFdNext?, stdinPos', inTimedOut, inErr?) ←
            match st.inFd?, inRev? with
            | some inFd, some ev =>
              if ev.pollerr || ev.pollhup || ev.pollnval then
                Files.closeOpt files (some inFd)
                pure (none, st.stdinPos, false, none)
              else if ev.pollout then
                match ← writeStdinStep files timeRand inFd stdin startMs (some timeoutMs) st.stdinPos false stepFuel with
                | .error e => pure (none, st.stdinPos, false, some e)
                | .ok (nextFd?, p', _, to) => pure (nextFd?, p', to, none)
              else
                pure (some inFd, st.stdinPos, false, none)
            | inFd?, _ => pure (inFd?, st.stdinPos, false, none)
          match inErr? with
          | some e =>
            Files.closeOpt files st.outFd?
            Files.closeOpt files st.errFd?
            Files.closeOpt files st.statusFd?
            return .error e
          | none =>
            if inTimedOut then
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.outFd?
              Files.closeOpt files st.errFd?
              Files.closeOpt files st.statusFd?
              return classifyBoxStreamResult program cwd true false st.statusMsg?
                (concatChunks st.outChunks st.outLen) (concatChunks st.errChunks st.errLen)
            let outStep ←
              if outReady then
                match st.outFd? with
                | none => pure (.cont none st.outChunks st.outLen false)
                | some outFd =>
                  drainPipeStep files timeRand outFd st.errLen startMs (some timeoutMs) maxOutputBytes?
                    st.outChunks st.outLen 0 false stepFuel
              else
                pure (.cont st.outFd? st.outChunks st.outLen false)
            match outStep with
            | .ioErr e =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              Files.closeOpt files st.statusFd?
              return .error e
            | .timedOut outChunks' outLen' =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              Files.closeOpt files st.statusFd?
              return classifyBoxStreamResult program cwd true false st.statusMsg?
                (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen)
            | .limitExceeded outChunks' outLen' =>
              Files.closeOpt files inFdNext?
              Files.closeOpt files st.errFd?
              Files.closeOpt files st.statusFd?
              return classifyBoxStreamResult program cwd false true st.statusMsg?
                (concatChunks outChunks' outLen') (concatChunks st.errChunks st.errLen)
            | .cont outFdNext? outChunks' outLen' _ =>
              let errStep ←
                if errReady then
                  match st.errFd? with
                  | none => pure (.cont none st.errChunks st.errLen false)
                  | some errFd =>
                    drainPipeStep files timeRand errFd outLen' startMs (some timeoutMs) maxOutputBytes?
                      st.errChunks st.errLen 0 false stepFuel
                else
                  pure (.cont st.errFd? st.errChunks st.errLen false)
              match errStep with
              | .ioErr e =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
                Files.closeOpt files st.statusFd?
                return .error e
              | .timedOut errChunks' errLen' =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
                Files.closeOpt files st.statusFd?
                return classifyBoxStreamResult program cwd true false st.statusMsg?
                  (concatChunks outChunks' outLen') (concatChunks errChunks' errLen')
              | .limitExceeded errChunks' errLen' =>
                Files.closeOpt files inFdNext?
                Files.closeOpt files outFdNext?
                Files.closeOpt files st.statusFd?
                return classifyBoxStreamResult program cwd false true st.statusMsg?
                  (concatChunks outChunks' outLen') (concatChunks errChunks' errLen')
              | .cont errFdNext? errChunks' errLen' _ =>
                let (stFdNext?, stBuf', stMsgNext?) ←
                  if stReady then
                    match st.statusFd? with
                    | none => pure (none, st.statusBuf, st.statusMsg?)
                    | some sfd =>
                      let (sf', sb', sm?) ← readInitStatusStep files sfd st.statusBuf 16
                      pure (sf', sb', sm? <|> st.statusMsg?)
                  else
                    pure (st.statusFd?, st.statusBuf, st.statusMsg?)
                let stopEarly := match stMsgNext? with
                  | some msg => msg.kind == PS_STATUS_EXEC_ERR || msg.kind == PS_STATUS_INIT_ERR
                  | none => false
                if stopEarly then
                  Files.closeOpt files inFdNext?
                  Files.closeOpt files outFdNext?
                  Files.closeOpt files errFdNext?
                  Files.closeOpt files stFdNext?
                  return classifyBoxStreamResult program cwd false false stMsgNext?
                    (concatChunks outChunks' outLen') (concatChunks errChunks' errLen')
                else
                  readBoxStreamLoop files poll timeRand program cwd stdin startMs timeoutMs maxOutputBytes? stepFuel
                    { inFd? := inFdNext?
                      outFd? := outFdNext?
                      errFd? := errFdNext?
                      statusFd? := stFdNext?
                      stdinPos := stdinPos'
                      outChunks := outChunks'
                      outLen := outLen'
                      errChunks := errChunks'
                      errLen := errLen'
                      statusBuf := stBuf'
                      statusMsg? := stMsgNext? }
                    fuel

/-- Release the `go_fd` barrier, configure non-blocking pipe descriptors, and execute `readBoxStreamLoop`. -/
def readBoxOutputCore {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (poll : Poll.PollOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (program cwd : String)
    (inFd0? outFd0? errFd0? statusFd0? goFd0? : Option fd)
    (stdin : ByteArray) (timeoutMs : Nat) (maxOutputBytes? : Option Nat)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (ioFuel : Nat := DEFAULT_IO_FUEL) :
    m (Except SandboxError SandboxResult) := do
  match goFd0? with
  | some goFd =>
    let _ ← writeAllFd files goFd (ByteArray.mk #[0x47]) 0 eintrFuel
    Files.closeOpt files (some goFd)
  | none => pure ()
  let inFd? ← setupStdinPipe files stdin inFd0?
  Files.setNonblockingOpt files outFd0?
  Files.setNonblockingOpt files errFd0?
  Files.setNonblockingOpt files statusFd0?
  match ← TimeRand.monoNowMs timeRand with
  | .error e =>
    Files.closeOpt files inFd?
    Files.closeOpt files outFd0?
    Files.closeOpt files errFd0?
    Files.closeOpt files statusFd0?
    return .error (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
  | .ok startMs =>
    let effTimeout := Nat.max 1 timeoutMs
    let initSt : BoxStreamState fd := {
      inFd? := inFd?
      outFd? := outFd0?
      errFd? := errFd0?
      statusFd? := statusFd0?
    }
    readBoxStreamLoop files poll timeRand program cwd stdin startMs effTimeout maxOutputBytes? eintrFuel initSt ioFuel

/-- Send `SIGKILL` to the sandbox's isolated host process group (`-pgid`), ignoring `ESRCH`. -/
def killBoxPg {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pgid : UInt32)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except SandboxError Unit) := do
  if pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID then
    return .ok ()
  match ← retryEintr (proc.kill (LinuxSyscall.Process.killTargetOfPgid pgid) .sigkill) eintrFuel with
  | .ok () => return .ok ()
  | .error e =>
    if e == Errno.ESRCH then return .ok ()
    else return .error (Internal.mapRawError (.ioError none e s!"kill: {Errno.name e}"))

/-- Send `SIGKILL` via `pidfd_send_signal(2)` to the sandbox root without PID-reuse races, ignoring `ESRCH`. -/
def killBoxPidfd {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pidfd : fd)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except SandboxError Unit) := do
  match ← retryEintr (proc.pidfd_send_signal pidfd .sigkill {}) eintrFuel with
  | .ok () => return .ok ()
  | .error e =>
    if e == Errno.ESRCH then return .ok ()
    else return .error (Internal.mapRawError (.ioError none e s!"pidfd_send_signal: {Errno.name e}"))

end LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo
