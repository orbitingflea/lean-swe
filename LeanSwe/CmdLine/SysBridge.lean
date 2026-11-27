import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Impl
import LeanSwe.EnvVars.Types
import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.CmdLine.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.CmdLine

/-- Bounded `EINTR` retry count (`64`) for single `read(2)` / `write(2)` calls
    on stdio descriptors: up to `64` consecutive `EINTR` failures are absorbed, and a `65`th returns `EINTR`. -/
def stdioEintrFuel : Nat := 64

/-- Normalize a raw host stdio exception message into a `.ioError` `CmdLineError` with non-empty message. -/
def mkStdioIoError (msg : String) : CmdLineError :=
  { kind := .ioError, message := if msg.isEmpty then "stdio I/O error" else msg }

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
  | _ => .otherError e (LeanSwe.LinuxSyscall.Errno.name e)

/-- Map an `EnvVarsError` into a `.ioError` `CmdLineError`, preserving `message` and `key`. -/
def mapEnvVarsError (err : LeanSwe.EnvVars.EnvVarsError) : CmdLineError :=
  { kind := .ioError, message := err.message, target := err.key }

/-- Check whether byte `b` is a UTF-8 continuation byte (`0x80..0xBF`). -/
def isUtf8ContinuationByte (b : UInt8) : Bool :=
  0x80 ≤ b && b ≤ 0xBF

/-- Return `some (cp, width)` iff a valid UTF-8 codepoint starts at byte offset `i` in `bs`. -/
def validateUtf8OneWidth (bs : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if _ : i < bs.size then
    let b0 := bs[i]
    if b0 < 0x80 then
      some (b0.toNat, 1)
    else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
      if _ : i + 1 < bs.size then
        let b1 := bs[i + 1]
        if isUtf8ContinuationByte b1 then
          some (((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F), 2)
        else none
      else none
    else if 0xE0 ≤ b0 && b0 ≤ 0xEF then
      if _ : i + 2 < bs.size then
        let b1 := bs[i + 1]
        let b2 := bs[i + 2]
        let b1Ok :=
          if b0 == 0xE0 then 0xA0 ≤ b1 && b1 ≤ 0xBF
          else if b0 == 0xED then 0x80 ≤ b1 && b1 ≤ 0x9F
          else isUtf8ContinuationByte b1
        if b1Ok && isUtf8ContinuationByte b2 then
          let cp := ((b0.toNat &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| (b2.toNat &&& 0x3F)
          some (cp, 3)
        else none
      else none
    else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then
      if _ : i + 3 < bs.size then
        let b1 := bs[i + 1]
        let b2 := bs[i + 2]
        let b3 := bs[i + 3]
        let b1Ok :=
          if b0 == 0xF0 then 0x90 ≤ b1 && b1 ≤ 0xBF
          else if b0 == 0xF4 then 0x80 ≤ b1 && b1 ≤ 0x8F
          else isUtf8ContinuationByte b1
        if b1Ok && isUtf8ContinuationByte b2 && isUtf8ContinuationByte b3 then
          let cp := ((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) |||
            ((b2.toNat &&& 0x3F) <<< 6) ||| (b3.toNat &&& 0x3F)
          some (cp, 4)
        else none
      else none
    else none
  else none

/-- Advance `i` past all contiguous UTF-8 continuation bytes (`0x80..0xBF`). -/
def skipUtf8ContinuationBytes (bs : ByteArray) (i : Nat) : Nat :=
  go bs i (bs.size - i)
where
  go (bs : ByteArray) (pos : Nat) : Nat → Nat
    | 0 => pos
    | fuel + 1 =>
      if _ : pos < bs.size then
        if isUtf8ContinuationByte bs[pos] then go bs (pos + 1) fuel else pos
      else pos

/-- Lossy UTF-8 decoder replacing each invalid byte sequence plus contiguous continuation bytes with `U+FFFD`. -/
def decodeUtf8LossyLean (bs : ByteArray) : String :=
  String.ofList (go 0 bs.size []).reverse
where
  go (pos : Nat) (fuel : Nat) (accRev : List Char) : List Char :=
    match fuel with
    | 0 => accRev
    | fuel' + 1 =>
      if pos >= bs.size then accRev
      else
        match validateUtf8OneWidth bs pos with
        | some (cp, w) => go (pos + w) fuel' (Char.ofNat cp :: accRev)
        | none =>
          let nextPos := skipUtf8ContinuationBytes bs (pos + 1)
          go nextPos fuel' (Char.ofNat 0xFFFD :: accRev)

/-- Map `LeanSwe.EnvVars.EnvVarsApiM.getEnv` into `CliOpsM.getEnv` via `mapEnvVarsError`. -/
def mapEnvVarsGet {m : Type → Type} [Monad m] (env : LeanSwe.EnvVars.EnvVarsApiM m)
    (key : String) : m (Except CmdLineError (Option String)) := do
  match ← env.getEnv key with
  | .ok v => return .ok v
  | .error err => return .error (mapEnvVarsError err)

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
        let line := decodeUtf8LossyLean lineBs
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

/-- Wrap a monadic stdio action into `m (Except CmdLineError α)`, catching `IO.Error` via `mkStdioIoError`. -/
def catchStdioM {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] {α : Type}
    (act : m α) : m (Except CmdLineError α) :=
  tryCatch (Except.ok <$> act) fun err =>
    pure (.error (mkStdioIoError err.toString))

/-- Prompt for a line of input over `CliOpsM m`, catching stdio `IO.Error` throws into `.ioError`. -/
def promptLineCheckedM {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : CliOpsM m)
    (prompt : String) (default : Option String := none) : m (Except CmdLineError String) := do
  match ← catchStdioM (ops.writeOut prompt) with
  | .error e => return .error e
  | .ok () =>
    match ← catchStdioM ops.readLine with
    | .error e => return .error e
    | .ok none => return .error { kind := .eof, message := "unexpected end of input" }
    | .ok (some line) =>
      let trimmed := Internal.trimAscii line
      if trimmed.isEmpty then
        match default with
        | some d => return .ok d
        | none => return .ok ""
      else
        return .ok trimmed

/-- Prompt up to `maxAttempts` times over `CliOpsM m` for `y`/`yes`/`n`/`no` confirmation, catching `IO.Error` into `.ioError`. -/
def confirmCheckedM {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : CliOpsM m)
    (prompt : String) (default : Option Bool := none) (maxAttempts : Nat := 100) :
    m (Except CmdLineError Bool) :=
  match maxAttempts with
  | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
  | n + 1 => do
    match ← catchStdioM (ops.writeOut prompt) with
    | .error e => return .error e
    | .ok () =>
      match ← catchStdioM ops.readLine with
      | .error e => return .error e
      | .ok none => return .error { kind := .eof, message := "unexpected end of input" }
      | .ok (some line) =>
        let norm := Internal.asciiLower (Internal.trimAscii line)
        if norm.isEmpty then
          match default with
          | some b => return .ok b
          | none =>
            match n with
            | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
            | _ + 1 => do
              match ← catchStdioM (ops.writeErr "Please answer yes or no.\n") with
              | .error e => return .error e
              | .ok () => confirmCheckedM ops prompt default n
        else if norm == "y" || norm == "yes" then
          return .ok true
        else if norm == "n" || norm == "no" then
          return .ok false
        else
          match n with
          | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
          | _ + 1 => do
            match ← catchStdioM (ops.writeErr "Please answer yes or no.\n") with
            | .error e => return .error e
            | .ok () => confirmCheckedM ops prompt default n

end LeanSwe.CmdLine.SysBridge
