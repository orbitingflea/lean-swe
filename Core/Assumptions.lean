namespace Core

/-- Whether a runtime error-coverage test exercises the real external dependency or a mock/fault switch. -/
inductive ErrorTestMode where
  /-- Triggered against real C/OS/CLI behavior (`RLIMIT_NOFILE`, `chmod`, subprocess `execve`, missing path). -/
  | real
  /-- Triggered via a fake `...OpsM` implementation or thin-wrapper fault switch. -/
  | mocked
  deriving Repr, BEq, DecidableEq

/-- Alias for `ErrorTestMode`. -/
abbrev ErrorTriggerKind := ErrorTestMode

/-- The two permissible justifications for an error kind in the package model. -/
inductive ErrorJustification where
  /-- A theorem in `Proofs.lean` proves this request can never return this error kind. -/
  | provedImpossible (theoremName : String)
  /-- A registered runtime test (real or mocked) forces this error kind and verifies the response. -/
  | tested (testName : String) (mode : ErrorTestMode)
  deriving Repr, BEq, DecidableEq

/-- One `(request, errorKind)` obligation declared by a package's `SpecTests.lean`. -/
structure ErrorObligation (E : Type) where
  /-- Outside request / API entrypoint name. -/
  request : String
  /-- Error kind / constructor distinguishably produced or modeled for `request`. -/
  errorKind : E
  /-- Either proved impossible or exercised by a named runtime test. -/
  justification : ErrorJustification
  deriving Repr, BEq

/-- Canonical `.provedImpossible` proposition for `IO (Except E α)` APIs. -/
def NeverErrorKindIO {E K α : Type} (kindOf : E → K) (forbidden : K)
    (act : IO (Except E α)) (w : Void IO.RealWorld) : Prop :=
  match act w with
  | .ok (.error e) _ => kindOf e ≠ forbidden
  | .ok (.ok _) _ => True
  | .error _ _ => False

/-- Canonical `.provedImpossible` proposition for `BaseIO (Except E α)` APIs. -/
def NeverErrorKindBaseIO {E K α : Type} (kindOf : E → K) (forbidden : K)
    (act : BaseIO (Except E α)) (w : Void IO.RealWorld) : Prop :=
  match act w with
  | .mk (.error e) _ => kindOf e ≠ forbidden
  | .mk (.ok _) _ => True

/-- Canonical `.provedImpossible` proposition for pure `Except E α` APIs. -/
def NeverErrorKindPure {E K α : Type} (kindOf : E → K) (forbidden : K)
    (res : Except E α) : Prop :=
  match res with
  | .error e => kindOf e ≠ forbidden
  | .ok _ => True

/-- Typed external-world assumption declared in an external-boundary `SpecTests.lean`.
    Carries zero free-prose claim fields: meaning lives in the named `RuntimeTests` probe
    and optional `formalPred?` when an upper-layer `Proofs` theorem consumes a formal boundary hypothesis. -/
structure AssumptionObligation where
  /-- Qualified identifier (`<Pkg>.assume_<pkg>_<unit>_<cond>_<exp>`) matched 1-to-1 to `RuntimeTests.lean`. -/
  name : String
  /-- Qualified `<Pkg>.Interface` / `<Pkg>.Impl` boundary constant whose external behavior is pinned. -/
  subject : String
  /-- `some name` iff a formal `assume_*` predicate in `SpecTests` is consumed as a hypothesis by an upper-layer
      `Proofs` theorem; `none` otherwise. -/
  formalPred? : Option String := none
  deriving Repr, BEq, DecidableEq

/-- One named runtime assumption check registered by `RuntimeTests.lean`. -/
structure RegisteredAssumption where
  /-- Exact Lean constant name of the assumption in `SpecTests.lean`. -/
  specName : String
  /-- Executable `IO` test checking that the real external world satisfies the assumption. -/
  run : IO Unit

/-- One named runtime error-coverage test registered by `RuntimeTests.lean`. -/
structure RegisteredErrorTest where
  /-- Exact Lean constant name of the error-forcing test referenced by `ErrorJustification.tested`. -/
  testName : String
  /-- Mode (`real` or `mocked`). -/
  mode : ErrorTestMode
  /-- Executable `IO` test that forces the error and asserts clean handling. -/
  run : IO Unit

private structure AssumpLogSink where
  nonce : String
  logPath : String
  realLogPath : String
  handle : IO.FS.Handle

private initialize assumpLogSinkRef : IO.Ref (Option AssumpLogSink) ← IO.mkRef none
private initialize openedAssumpLogPathsRef : IO.Ref (Array String) ← IO.mkRef #[]

private def resolvePathBestEffort (p : String) : IO String := do
  try
    return (← IO.FS.realPath p).toString
  catch _ =>
    return p

/-- Open and initialize the single-handle assumption/error runtime verification log with a per-run `nonce`. -/
def initAssumpLog (logPath nonce : String) : IO Unit := do
  if logPath.isEmpty || nonce.isEmpty then
    throw (IO.userError "initAssumpLog requires non-empty path and nonce")
  let handle ← IO.FS.Handle.mk logPath .write
  handle.putStrLn s!"{nonce}|LOG_INIT"
  let realLogPath ← resolvePathBestEffort logPath
  assumpLogSinkRef.set (some { nonce, logPath, realLogPath, handle })
  openedAssumpLogPathsRef.modify fun paths => paths ++ #[logPath, realLogPath]

/-- Record a passing runtime assumption check to the open nonce-tagged verification log. -/
def logAssumpPass (specName : String) : IO Unit := do
  if let some sink ← assumpLogSinkRef.get then
    sink.handle.putStrLn s!"{sink.nonce}|ASSUMP_PASS|{specName}"

/-- Record a passing runtime error-coverage test to the open nonce-tagged verification log. -/
def logErrPass (testName : String) (mode : ErrorTestMode) : IO Unit := do
  if let some sink ← assumpLogSinkRef.get then
    sink.handle.putStrLn s!"{sink.nonce}|ERR_PASS|{testName}|{reprStr mode}"

/-- Flush and close the assumption/error verification log opened by `initAssumpLog`. -/
def closeAssumpLog : IO Unit := do
  if let some sink ← assumpLogSinkRef.get then
    sink.handle.putStrLn s!"{sink.nonce}|LOG_CLOSE"
    sink.handle.flush
    assumpLogSinkRef.set none

/-- Run registered assumption checks and record `PASS` lines to the open nonce-tagged log sink. -/
def runRegisteredAssumptions (items : Array RegisteredAssumption) : IO Unit := do
  for item in items do
    item.run
    logAssumpPass item.specName

/-- Run registered error-coverage tests and record `PASS` lines to the open nonce-tagged log sink. -/
def runRegisteredErrorTests (items : Array RegisteredErrorTest) : IO Unit := do
  for item in items do
    item.run
    logErrPass item.testName item.mode

/-- Append formatted markdown to `GITHUB_STEP_SUMMARY` when running in CI. -/
def appendStepSummary (markdown : String) : IO Unit := do
  let some summaryPath ← IO.getEnv "GITHUB_STEP_SUMMARY" | return ()
  if summaryPath.isEmpty then
    return ()
  let resolvedSummary ← resolvePathBestEffort summaryPath
  if let some sink ← assumpLogSinkRef.get then
    if summaryPath == sink.logPath || resolvedSummary == sink.logPath ||
        summaryPath == sink.realLogPath || resolvedSummary == sink.realLogPath then
      return ()
  let openedPaths ← openedAssumpLogPathsRef.get
  if openedPaths.any (fun p => p == summaryPath || p == resolvedSummary) then
    return ()
  let h ← IO.FS.Handle.mk summaryPath .append
  h.putStr markdown
  h.flush

end Core
