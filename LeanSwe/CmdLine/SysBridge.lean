import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model
import LeanSwe.CmdLine.Model.Obeys
import LeanSwe.CmdLine.Impl
import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.CmdLine.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.CmdLine

/-- Bounded `EINTR` retry count (`Model.stdioEintrRetryLimit = 64`) for single `read(2)` / `write(2)` calls
    on stdio descriptors: up to `64` consecutive `EINTR` failures are absorbed, and a `65`th returns `EINTR`. -/
def stdioEintrFuel : Nat := Model.stdioEintrRetryLimit

/-- Map a Linux `Errno` returned by `LeanSwe.LinuxSyscall.Files` stdio primitives into the matching `IO.Error`. -/
def errnoToIoError (e : Errno) : IO.Error :=
  match e.toNat with
  | 4 => .interrupted "" 4 "interrupted system call"
  | 5 => .hardwareFault 5 "input/output error"
  | 9 => .invalidArgument none 9 "bad file descriptor"
  | 11 => .resourceExhausted none 11 "resource temporarily unavailable"
  | 21 => .inappropriateType none 21 "is a directory"
  | 24 => .resourceExhausted none 24 "too many open files"
  | 27 => .resourceExhausted none 27 "file too large"
  | 28 => .resourceExhausted none 28 "no space left on device"
  | 32 => .resourceVanished 32 "broken pipe"
  | _ => .otherError e (Errno.name e)

/-- Read 1 byte at a time from `d` up to `0x0A` (`'\n'`) or `0`-byte EOF without over-reading past newline,
    retrying transient `EINTR` via `LeanSwe.LinuxSyscall.retryEintr` while preserving `acc` and capping line
    length at `fuel` bytes (`EFBIG`). -/
def readStdioLineFdLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd) (d : fd) (acc : ByteArray) :
    Nat → m (Except Errno ByteArray)
  | 0 => pure (.error Errno.EFBIG)
  | fuel + 1 => do
    match ← retryEintr (files.read d 1) stdioEintrFuel with
    | .error e => pure (.error e)
    | .ok chunk =>
      if h : 0 < chunk.size then
        let b := chunk[0]
        let acc' := acc.push b
        if b == (0x0A : UInt8) then
          pure (.ok acc')
        else
          readStdioLineFdLoop files d acc' fuel
      else
        pure (.ok acc)

/-- Read one logical line (up to 64 MiB) from `.stdin` via `dupStdio` + `readStdioLineFdLoop`,
    always closing the duplicated descriptor via `tryFinally'`. -/
def readStdioLineM {m : Type → Type} [Monad m] [MonadFinally m] {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd) :
    m (Except Errno (Option String)) := do
  match ← files.dupStdio .stdin with
  | .error e => return .error e
  | .ok d =>
    let (r, _) ← tryFinally'
      (readStdioLineFdLoop files d ByteArray.empty 67108864)
      (fun _ => files.close d)
    match r with
    | .error e => return .error e
    | .ok lineBs =>
      if lineBs.isEmpty then
        return .ok none
      else
        let line := Model.decodeUtf8LossyLean lineBs
        return .ok (some (Internal.stripTrailingNewline line))

/-- Write all remaining bytes `bs[off..]` to `d` in `<= 1 MiB` slices, retrying transient `EINTR` via
    `LeanSwe.LinuxSyscall.retryEintr` and returning `EIO` if a non-empty `write` makes zero progress. -/
def writeStdioSlicesLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd) (d : fd) (bs : ByteArray) (off : Nat) :
    Nat → m (Except Errno Unit)
  | 0 =>
    if off >= bs.size then pure (.ok ()) else pure (.error Errno.EIO)
  | fuel + 1 => do
    if off >= bs.size then
      return .ok ()
    let endIdx := min bs.size (off + 1048576)
    let slice := if off == 0 && endIdx == bs.size then bs else bs.extract off endIdx
    match ← retryEintr (files.write d slice) stdioEintrFuel with
    | .error e => return .error e
    | .ok n =>
      if n == 0 then
        return .error Errno.EIO
      else
        writeStdioSlicesLoop files d bs (off + n.toNat) fuel

/-- Write `text` unbuffered to `slot` (`stdout` or `stderr`) via `dupStdio` + `write`,
    treating `""` as a total no-op and always closing the duplicated descriptor via `tryFinally'`. -/
def writeStdioSlotM {m : Type → Type} [Monad m] [MonadFinally m] {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd)
    (slot : LeanSwe.LinuxSyscall.Files.StdioFd) (text : String) :
    m (Except Errno Unit) := do
  if text.isEmpty then
    return .ok ()
  let bs := text.toUTF8
  match ← files.dupStdio slot with
  | .error e => return .error e
  | .ok d =>
    let (r, _) ← tryFinally'
      (writeStdioSlicesLoop files d bs 0 bs.size)
      (fun _ => files.close d)
    return r

/-- Build `CliOpsM m` over unbuffered `LeanSwe.LinuxSyscall.Files` (`dupStdio`/`read`/`write`/`close`)
    and an injected `getEnv` hook.

    Each call duplicates descriptor `0`/`1`/`2` with `dupStdio` and closes the duplicate on every exit path via
    `tryFinally'`. It intentionally does **not** flush C/Lean `IO.FS.Stream` buffers or honor `IO.withStdin`/
    `IO.withStdout`/`IO.withStderr`. Transient `EINTR` retries up to `stdioEintrFuel` (`64`) times per `read`/`write`. -/
def mkFilesCliOpsM {m : Type → Type} [Monad m] [MonadFinally m] [MonadExceptOf IO.Error m] {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM m fd)
    (getEnvFn : String → m (Except CmdLineError (Option String))) : CliOpsM m :=
  { readLine := do
      match ← readStdioLineM files with
      | .error e => throwThe IO.Error (errnoToIoError e)
      | .ok line? => return line?
    writeOut := fun text => do
      match ← writeStdioSlotM files .stdout text with
      | .error e => throwThe IO.Error (errnoToIoError e)
      | .ok () => return ()
    writeErr := fun text => do
      match ← writeStdioSlotM files .stderr text with
      | .error e => throwThe IO.Error (errnoToIoError e)
      | .ok () => return ()
    getEnv := getEnvFn }

/-- Build `CliOps` over unbuffered `LeanSwe.LinuxSyscall.Files` (`dupStdio`/`read`/`write`/`close`)
    and an injected `getEnv` hook.

    Operates directly on OS descriptors `0`/`1`/`2`; does **not** flush C/Lean `IO.FS.Stream` buffers or honor
    `IO.withStdin`/`IO.withStdout`/`IO.withStderr`. Callers mixing `IO.print`/`IO.println` with `CmdLine` on
    pipes/non-TTYs must flush Lean stdio beforehand, or inject a custom `CliOps` via `Internal.mkApiM`. -/
def mkFilesCliOps {fd : Type}
    (files : LeanSwe.LinuxSyscall.Files.FilesOpsM IO fd)
    (getEnvFn : String → IO (Except CmdLineError (Option String))) : CliOps :=
  mkFilesCliOpsM files getEnvFn

/-- Wrap an `IO` stdio step into `IO (Except CmdLineError α)`, mapping caught `IO.Error`s via `Model.mkStdioIoError`. -/
def catchStdioIo {α : Type} (act : IO α) : IO (Except CmdLineError α) :=
  BaseIO.toEIO (EIO.catchExceptions (act >>= fun a => pure (.ok a)) fun err =>
    pure (.error (Model.mkStdioIoError err.toString)))

/-- Lift a `CliOps` (`CliOpsM IO`) backend into `Model.CheckedCliOpsM IO`, catching stdio `IO.Error` throws into `.ioError`. -/
def mkCheckedCliOps (ops : CliOps) : Model.CheckedCliOpsM IO :=
  { readLineChecked := catchStdioIo ops.readLine
    writeOutChecked := fun text => catchStdioIo (ops.writeOut text)
    writeErrChecked := fun text => catchStdioIo (ops.writeErr text)
    cliOps := ops }

/-- Prompt for a line of input over a `Model.CheckedCliOpsM m` backend, propagating stdio `.ioError`s cleanly. -/
def promptLineChecked {m : Type → Type} [Monad m] (ops : Model.CheckedCliOpsM m)
    (prompt : String) (default : Option String := none) : m (Except CmdLineError String) := do
  match ← ops.writeOutChecked prompt with
  | .error e => return .error e
  | .ok () =>
    match ← ops.readLineChecked with
    | .error e => return .error e
    | .ok none => return .error { kind := .eof, message := "unexpected end of input" }
    | .ok (some line) =>
      let trimmed := Model.trimAscii line
      if trimmed.isEmpty then
        match default with
        | some d => return .ok d
        | none => return .ok ""
      else
        return .ok trimmed

/-- Prompt up to `maxAttempts` times over a `Model.CheckedCliOpsM m` backend for `y`/`yes`/`n`/`no` confirmation. -/
def confirmChecked {m : Type → Type} [Monad m] (ops : Model.CheckedCliOpsM m)
    (prompt : String) (default : Option Bool := none) (maxAttempts : Nat := 100) :
    m (Except CmdLineError Bool) :=
  match maxAttempts with
  | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
  | n + 1 => do
    match ← ops.writeOutChecked prompt with
    | .error e => return .error e
    | .ok () =>
      match ← ops.readLineChecked with
      | .error e => return .error e
      | .ok none => return .error { kind := .eof, message := "unexpected end of input" }
      | .ok (some line) =>
        let norm := Model.asciiLower (Model.trimAscii line)
        if norm.isEmpty then
          match default with
          | some b => return .ok b
          | none =>
            match n with
            | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
            | _ + 1 => do
              match ← ops.writeErrChecked "Please answer yes or no.\n" with
              | .error e => return .error e
              | .ok () => confirmChecked ops prompt default n
        else if norm == "y" || norm == "yes" then
          return .ok true
        else if norm == "n" || norm == "no" then
          return .ok false
        else
          match n with
          | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
          | _ + 1 => do
            match ← ops.writeErrChecked "Please answer yes or no.\n" with
            | .error e => return .error e
            | .ok () => confirmChecked ops prompt default n

end LeanSwe.CmdLine.SysBridge
