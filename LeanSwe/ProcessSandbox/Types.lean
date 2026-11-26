namespace LeanSwe.ProcessSandbox

private def reprByteArray (bs : ByteArray) : Std.Format :=
  repr bs.toList

/-- Machine-checkable error categories returned by `LeanSwe.ProcessSandbox`. -/
inductive SandboxErrorKind where
  /-- Malformed `BoxSpec` such as an empty program, NUL byte, invalid path, reserved/duplicate mount, bad env key, or zero limit. -/
  | invalidInput
  /-- Host does not support sandboxed execution or pre-execution sandbox setup failed closed. -/
  | unavailable
  /-- Host mount source path, guest working directory, or guest executable does not exist. -/
  | notFound
  /-- Host mount source path, guest working directory, or guest executable lacks required permissions. -/
  | permissionDenied
  /-- Underlying I/O failure while piping standard streams or waiting for the guest. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.ProcessSandbox` operations. -/
structure SandboxError where
  /-- Machine-checkable error category. -/
  kind : SandboxErrorKind
  /-- Associated host or box path, when applicable. -/
  path : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a sandboxed guest is isolated from or connected to the host network. -/
inductive NetworkMode where
  /-- Guest has no access to host network state. -/
  | closed
  /-- Guest may observe and interact with host network state. -/
  | open
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Explicit filesystem mount mapped into the sandbox's empty root. -/
inductive SandboxMount where
  /-- Expose `hostPath` read-only at `boxPath` inside the sandbox. -/
  | readOnly (hostPath boxPath : String)
  /-- Expose `hostPath` read-write at `boxPath` inside the sandbox. -/
  | readWrite (hostPath boxPath : String)
  /-- Provide a fresh empty writable directory at `boxPath` inside the sandbox, discarded on exit. -/
  | scratch (boxPath : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Extract the target path inside the sandbox for a `SandboxMount`. -/
def mountBoxPath : SandboxMount → String
  | .readOnly _ bp => bp
  | .readWrite _ bp => bp
  | .scratch bp => bp

/-- Extract the source path on the host for a `SandboxMount`, or `none` for `.scratch`. -/
def mountHostPath? : SandboxMount → Option String
  | .readOnly hp _ => some hp
  | .readWrite hp _ => some hp
  | .scratch _ => none

/-- Unvalidated one-shot sandboxed command specification. -/
structure BoxSpec where
  /-- Executable name or path invoked inside the sandbox (never via a shell). -/
  program : String
  /-- Explicit argument array passed verbatim to the guest executable. -/
  args : Array String := #[]
  /-- Clean-slate environment variables (`("PATH", "/usr/bin:/bin")` is added if `"PATH"` is absent). -/
  env : Array (String × String) := #[]
  /-- Optional absolute working directory inside the sandbox (defaults to `"/tmp"` when `none`). -/
  cwd : Option String := none
  /-- Bytes delivered to the guest's standard input before closing it. -/
  stdin : ByteArray := ByteArray.empty
  /-- Explicit filesystem mounts added atop the empty root and read-only OS runtime preset. -/
  mounts : Array SandboxMount := #[]
  /-- Network isolation mode (defaults to `.closed`). -/
  network : NetworkMode := .closed
  /-- Optional positive wall-clock execution timeout in milliseconds (`some 0` is rejected). -/
  timeoutMs : Option Nat := none
  /-- Optional positive cap on combined `stdout.size + stderr.size` in bytes (`some 0` is rejected). -/
  maxOutputBytes : Option Nat := none
  deriving BEq, DecidableEq

instance : Inhabited BoxSpec where
  default := { program := "" }

instance : Repr BoxSpec where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "program := " ++ repr s.program,
        "args := " ++ repr s.args,
        "env := " ++ repr s.env,
        "cwd := " ++ repr s.cwd,
        "stdin := " ++ reprByteArray s.stdin,
        "mounts := " ++ repr s.mounts,
        "network := " ++ repr s.network,
        "timeoutMs := " ++ repr s.timeoutMs,
        "maxOutputBytes := " ++ repr s.maxOutputBytes
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Validated and normalized `BoxSpec` produced at the boundary by `validateSpec`. -/
structure ValidBoxSpec where
  /-- Non-empty, NUL-free executable name or path. -/
  program : String
  /-- NUL-free argument array. -/
  args : Array String
  /-- Validated, deduplicated clean-slate environment guaranteed to define `"PATH"`. -/
  env : Array (String × String)
  /-- Canonical absolute working directory inside the sandbox (`"/tmp"` when `spec.cwd = none`). -/
  cwd : String
  /-- Standard input bytes delivered to the guest. -/
  stdin : ByteArray
  /-- Canonicalized mounts with distinct non-reserved `boxPath`s, guaranteed to include `"/tmp"`. -/
  mounts : Array SandboxMount
  /-- Validated network isolation mode. -/
  network : NetworkMode
  /-- Validated optional timeout (`some n` implies `n > 0`). -/
  timeoutMs : Option Nat
  /-- Validated optional combined output cap (`some n` implies `n > 0`). -/
  maxOutputBytes : Option Nat
  deriving BEq, DecidableEq

instance : Inhabited ValidBoxSpec where
  default :=
    { program := "/bin/true"
      args := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      network := .closed
      timeoutMs := none
      maxOutputBytes := none }

instance : Repr ValidBoxSpec where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "program := " ++ repr s.program,
        "args := " ++ repr s.args,
        "env := " ++ repr s.env,
        "cwd := " ++ repr s.cwd,
        "stdin := " ++ reprByteArray s.stdin,
        "mounts := " ++ repr s.mounts,
        "network := " ++ repr s.network,
        "timeoutMs := " ++ repr s.timeoutMs,
        "maxOutputBytes := " ++ repr s.maxOutputBytes
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Project a `ValidBoxSpec` back into a normalized `BoxSpec`. -/
def validBoxSpecToBoxSpec (v : ValidBoxSpec) : BoxSpec :=
  { program := v.program
    args := v.args
    env := v.env
    cwd := some v.cwd
    stdin := v.stdin
    mounts := v.mounts
    network := v.network
    timeoutMs := v.timeoutMs
    maxOutputBytes := v.maxOutputBytes }

/-- Termination classification for a guest launched inside a sandbox. -/
inductive SandboxOutcome where
  /-- Guest exited with status `code` (signal-terminated guests report `128 + sig`). -/
  | exited (code : Int)
  /-- Guest exceeded `timeoutMs` and all guest processes were terminated and reaped. -/
  | timedOut
  /-- Combined `stdout` and `stderr` exceeded `maxOutputBytes` and all guest processes were terminated and reaped. -/
  | outputLimitExceeded
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Completed sandbox execution result carrying `outcome` and captured `stdout`/`stderr`. -/
structure SandboxResult where
  /-- Termination outcome of the sandboxed command. -/
  outcome : SandboxOutcome
  /-- Captured standard output bytes. -/
  stdout : ByteArray
  /-- Captured standard error bytes. -/
  stderr : ByteArray
  deriving BEq, DecidableEq

instance : Inhabited SandboxResult where
  default := { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }

instance : Repr SandboxResult where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "outcome := " ++ repr r.outcome,
        "stdout := " ++ reprByteArray r.stdout,
        "stderr := " ++ reprByteArray r.stderr
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Public isolated one-shot command execution API exported by `LeanSwe.ProcessSandbox`, parameterized over `m`. -/
structure ProcessSandboxApiM (m : Type → Type) where
  /-- Validate and normalize an untrusted `BoxSpec`, failing with `.invalidInput` on malformed inputs. -/
  validateSpec : BoxSpec → Except SandboxError ValidBoxSpec
  /-- Execute `BoxSpec` inside an isolated sandbox, reaping all guest descendants before returning. -/
  run : BoxSpec → m (Except SandboxError SandboxResult)
  /-- Probe whether the current host supports `ProcessSandbox.run`. -/
  isAvailable : m Bool

/-- Concrete `IO` sandbox API bundle exported by `LeanSwe.ProcessSandbox`. -/
abbrev ProcessSandboxApi := ProcessSandboxApiM IO

end LeanSwe.ProcessSandbox
