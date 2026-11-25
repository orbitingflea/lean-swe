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
  nonce : String := ""
  logPath : String := ""
  realLogPath : String := ""
  handle? : Option IO.FS.Handle := none
  coverageNonce : String := ""
  coverageLogPath : String := ""
  coverageRealLogPath : String := ""
  coverageHandle? : Option IO.FS.Handle := none
  errTestPassHook? : Option (String → ErrorTestMode → IO Unit) := none
  activeErrTest? : Option (String × ErrorTestMode) := none

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
  assumpLogSinkRef.modify fun st? =>
    some { st?.getD {} with nonce, logPath, realLogPath, handle? := some handle }
  openedAssumpLogPathsRef.modify fun paths => paths ++ #[logPath, realLogPath]

/-- Open and initialize the single-handle runtime `ERR_HIT` coverage log with a per-run `nonce`. -/
def initCoverageLog (logPath nonce : String) : IO Unit := do
  if logPath.isEmpty || nonce.isEmpty then
    throw (IO.userError "initCoverageLog requires non-empty path and nonce")
  let handle ← IO.FS.Handle.mk logPath .write
  handle.putStrLn s!"{nonce}|LOG_INIT"
  let realLogPath ← resolvePathBestEffort logPath
  assumpLogSinkRef.modify fun st? =>
    some { st?.getD {} with
      coverageNonce := nonce
      coverageLogPath := logPath
      coverageRealLogPath := realLogPath
      coverageHandle? := some handle }
  openedAssumpLogPathsRef.modify fun paths => paths ++ #[logPath, realLogPath]

/-- Record a live nonce-authenticated `ERR_HIT` line (`<nonce>|ERR_HIT|<qualOp>|<ErrorKindCtor>|<mode>`). -/
def logErrHit (qualOp errorKindCtor mode : String) : IO Unit := do
  if let some st ← assumpLogSinkRef.get then
    if let some h := st.coverageHandle? then
      h.putStrLn s!"{st.coverageNonce}|ERR_HIT|{qualOp}|{errorKindCtor}|{mode}"

/-- Flush and close the runtime `ERR_HIT` coverage log opened by `initCoverageLog`. -/
def closeCoverageLog : IO Unit := do
  if let some st ← assumpLogSinkRef.get then
    if let some h := st.coverageHandle? then
      h.putStrLn s!"{st.coverageNonce}|LOG_CLOSE"
      h.flush
      assumpLogSinkRef.modify fun cur? =>
        cur?.map fun cur =>
          { cur with
            coverageNonce := ""
            coverageLogPath := ""
            coverageRealLogPath := ""
            coverageHandle? := none }

/-- Register an optional runtime callback invoked immediately after each `RegisteredErrorTest` executes and passes. -/
def setErrTestPassHook (hook? : Option (String → ErrorTestMode → IO Unit)) : IO Unit :=
  assumpLogSinkRef.modify fun st? =>
    some { st?.getD {} with errTestPassHook? := hook? }

/-- Record a passing runtime assumption check to the open nonce-tagged verification log. -/
def logAssumpPass (specName : String) : IO Unit := do
  if let some st ← assumpLogSinkRef.get then
    if let some h := st.handle? then
      h.putStrLn s!"{st.nonce}|ASSUMP_PASS|{specName}"

/-- Record a passing runtime error-coverage test to the open nonce-tagged verification log. -/
def logErrPass (testName : String) (mode : ErrorTestMode) : IO Unit := do
  if let some st ← assumpLogSinkRef.get then
    if let some h := st.handle? then
      h.putStrLn s!"{st.nonce}|ERR_PASS|{testName}|{reprStr mode}"

/-- Flush and close the assumption/error verification log opened by `initAssumpLog`. -/
def closeAssumpLog : IO Unit := do
  if let some st ← assumpLogSinkRef.get then
    if let some h := st.handle? then
      h.putStrLn s!"{st.nonce}|LOG_CLOSE"
      h.flush
      assumpLogSinkRef.modify fun cur? =>
        cur?.map fun cur =>
          { cur with nonce := "", logPath := "", realLogPath := "", handle? := none }

/-- Run registered assumption checks and record `PASS` lines to the open nonce-tagged log sink. -/
def runRegisteredAssumptions (items : Array RegisteredAssumption) : IO Unit := do
  for item in items do
    item.run
    logAssumpPass item.specName

private def notifyActiveErrSubcase (kindTag : String) : IO Unit := do
  if kindTag.isEmpty then
    return ()
  if let some st ← assumpLogSinkRef.get then
    if let (some hook, some (activeName, activeMode)) := (st.errTestPassHook?, st.activeErrTest?) then
      if activeName.endsWith "_mocked" then
        let base := (activeName.dropEnd 7).toString
        hook s!"{base}_{kindTag}" activeMode

/-- Assert `res` returned `.error e` with `kindOf e == expected` (and `extraOk e`), then notify the active registered error-test hook with `kindTag`. -/
def assertErrorKindPass {E K α : Type} [BEq K] [Repr E] [Repr K]
    (kindTag : String) (kindOf : E → K) (expected : K)
    (res : Except E α) (msg : String) (extraOk : E → Bool := fun _ => true) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if kindOf e != expected || !extraOk e then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")
    notifyActiveErrSubcase kindTag

/-- Assert `res` returned `.ok expectedVal` after forcing an error condition, then notify the active registered error-test hook with `kindTag`. -/
def assertHandledErrorPass {E α : Type} [BEq α] [Repr E] [Repr α]
    (kindTag : String) (expectedVal : α)
    (res : Except E α) (msg : String) : IO Unit := do
  match res with
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")
  | .ok v =>
    if v != expectedVal then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expectedVal})")
    notifyActiveErrSubcase kindTag

/-- Run registered error-coverage tests and record `PASS` lines to the open nonce-tagged log sink. -/
def runRegisteredErrorTests (items : Array RegisteredErrorTest) : IO Unit := do
  for item in items do
    assumpLogSinkRef.modify fun st? =>
      some { st?.getD {} with activeErrTest? := some (item.testName, item.mode) }
    try
      item.run
    finally
      assumpLogSinkRef.modify fun cur? =>
        cur?.map fun cur => { cur with activeErrTest? := none }
    logErrPass item.testName item.mode
    if let some st ← assumpLogSinkRef.get then
      if let some hook := st.errTestPassHook? then
        hook item.testName item.mode

/-- Append formatted markdown to `GITHUB_STEP_SUMMARY` when running in CI. -/
def appendStepSummary (markdown : String) : IO Unit := do
  let some summaryPath ← IO.getEnv "GITHUB_STEP_SUMMARY" | return ()
  if summaryPath.isEmpty then
    return ()
  let resolvedSummary ← resolvePathBestEffort summaryPath
  if let some st ← assumpLogSinkRef.get then
    let activePaths := #[st.logPath, st.realLogPath, st.coverageLogPath, st.coverageRealLogPath]
    if activePaths.any (fun p => !p.isEmpty && (summaryPath == p || resolvedSummary == p)) then
      return ()
  let openedPaths ← openedAssumpLogPathsRef.get
  if openedPaths.any (fun p => p == summaryPath || p == resolvedSummary) then
    return ()
  let h ← IO.FS.Handle.mk summaryPath .append
  h.putStr markdown
  h.flush

end Core
