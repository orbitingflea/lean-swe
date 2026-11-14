import LeanSwe.Process.Raw.Types

/-!
# Process Package Types

Public data types, error enums, and generic `ProcessApiM` bundle for `LeanSwe.Process`.
Re-exports shared primitive types from `LeanSwe.Process.Raw.Types` and stays free of
OS and implementation internals so `SpecTests` depend only on this module.
-/

namespace LeanSwe.Process

export LeanSwe.Process.Raw
  (ProcessErrorKind ProcessError ProcessRawError ExecRequest ExecResult
   ProcessHandle ExecOutcome RawProcessOpsM RawProcessOps)

/-- Public command-execution operations exported by `LeanSwe.Process`, parameterized over effect monad `m`. -/
structure ProcessApiM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
  mapRawError : ProcessRawError → ProcessError
  /-- Validate and normalize an `ExecRequest` (rejecting empty program, NUL bytes, bad env keys, and zero timeout). -/
  validateRequest : ExecRequest → Except ProcessError ExecRequest
  /-- Construct a direct `execvp`-style `ExecRequest` with explicit argument array (no shell). -/
  mkCommandRequest : String → Array String → ExecRequest
  /-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
  withTextInput : ExecRequest → String → ExecRequest
  /-- Execute a command directly in its own process group, returning `ExecResult` even for non-zero exit codes. -/
  run : ExecRequest → m (Except ProcessError ExecResult)
  /-- Execute a command like `run`, mapping any non-zero exit code to `.error` with `kind := .nonZeroExit`. -/
  runChecked : ExecRequest → m (Except ProcessError ExecResult)
  /-- Convenience wrapper executing `program` with explicit `args` via `run`. -/
  runCommand : String → Array String → m (Except ProcessError ExecResult)
  /-- Convenience wrapper executing `program` with explicit `args` via `runChecked`. -/
  runCommandChecked : String → Array String → m (Except ProcessError ExecResult)
  /-- Return count of currently active (un-reaped) spawned child process handles. -/
  activeProcessCount : m Nat

/-- Concrete `IO` process execution API bundle for `LeanSwe.Process`. -/
abbrev ProcessApi := ProcessApiM IO

end LeanSwe.Process
