import Core.NondetTest
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.SpecTests.MockOps

namespace LeanSwe.ProcessSandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ProcessSandbox.Model

/-- `api.validateSpec` rejects empty `program`, NUL bytes in `program`, or NUL bytes in `args` with `.invalidInput`. -/
def test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let specEmpty ← nondet BoxSpec
  assume (specEmpty.program = "")
  match api.validateSpec specEmpty with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")
  let specNulProg ← nondet BoxSpec
  assume ('\x00' ∈ specNulProg.program.toList)
  match api.validateSpec specNulProg with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")
  let specNulArg ← nondet BoxSpec
  let idx ← nondet Nat
  assume (idx < specNulArg.args.size)
  assume ('\x00' ∈ specNulArg.args[idx]!.toList)
  match api.validateSpec specNulArg with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects `cwd` values that are empty, contain NUL bytes, are relative, or contain `".."` segments. -/
def test_psandbox_validateSpec_rejectsInvalidCwd
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let spec ← nondet BoxSpec
  let d ← nondet String
  assume (spec.cwd = some d)
  assume (normalizeCleanAbsPath d = none)
  match api.validateSpec spec with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects empty, NUL, relative, or `".."` mount `hostPath` or `boxPath` across `readOnly`, `readWrite`, and `scratch`. -/
def test_psandbox_validateSpec_rejectsInvalidMountPaths
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let badPath ← nondet String
  assume (normalizeCleanAbsPath badPath = none)
  let badMounts : List SandboxMount :=
    [ .readOnly badPath "/work"
    , .readOnly "/host/src" badPath
    , .readWrite badPath "/work"
    , .readWrite "/host/src" badPath
    , .scratch badPath
    ]
  NondetTest.assert (badMounts.all (fun m =>
    match api.validateSpec { program := "/bin/true", mounts := #[m] } with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false) = true)

/-- `api.validateSpec` rejects duplicate target `boxPath` entries (including lexically equivalent paths like `"/work"` and `"/work/"`). -/
def test_psandbox_validateSpec_rejectsDuplicateBoxPath
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let m₁ ← nondet SandboxMount
  let m₂ ← nondet SandboxMount
  let canonBp ← nondet String
  assume ((validateAndNormalizeMount m₁).map mountBoxPath = .ok canonBp)
  assume ((validateAndNormalizeMount m₂).map mountBoxPath = .ok canonBp)
  match api.validateSpec { program := "/bin/true", mounts := #[m₁, m₂] } with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` rejects any mount targeting `"/"` or shadowing/writing `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`, `/etc`, `/dev`, or `/proc`. -/
def test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let bp ← nondet String
  let bSegs ← nondet (List String)
  assume (parseCleanAbsSegs bp = some bSegs)
  assume (isReservedBoxSegs bSegs = true)
  let attempts : List SandboxMount :=
    [ .readOnly "/var/data" bp
    , .readWrite "/var/data" bp
    , .scratch bp
    ]
  NondetTest.assert (attempts.all (fun m =>
    match api.validateSpec { program := "/bin/true", mounts := #[m] } with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false) = true)

/-- `api.validateSpec` rejects port `0` (`boxPort = 0` or `hostPort = 0`) and duplicate `boxPort`s while allowing distinct `boxPort`s to target the same valid `hostPort`. -/
def test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let p ← nondet UInt16
  assume (p != 0)
  let zeroBox : BoxSpec := { program := "/bin/true", portForwards := #[{ boxPort := 0, hostPort := p }] }
  let zeroHost : BoxSpec := { program := "/bin/true", portForwards := #[{ boxPort := p, hostPort := 0 }] }
  let dupBox : BoxSpec :=
    { program := "/bin/true"
      portForwards := #[{ boxPort := p, hostPort := 8080 }, { boxPort := p, hostPort := 8081 }] }
  NondetTest.assert (match api.validateSpec zeroBox with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroHost with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec dupBox with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  let p₂ ← nondet UInt16
  assume (p₂ != 0 ∧ p₂ ≠ p)
  let sharedHost : BoxSpec :=
    { program := "/bin/true"
      portForwards := #[{ boxPort := p, hostPort := 9000 }, { boxPort := p₂, hostPort := 9000 }] }
  NondetTest.assert ((api.validateSpec sharedHost).isOk = true)

/-- `api.validateSpec` rejects `timeoutMs = 0`, `memoryMaxBytes = some 0`, and `pidsMax = some 0` while accepting `fileSizeMaxBytes = some 0` and `maxOutputBytes = some 0`. -/
def test_psandbox_validateSpec_limitsRules
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let zeroTimeout : BoxSpec := { program := "/bin/true", limits := { timeoutMs := 0 } }
  let zeroMem : BoxSpec := { program := "/bin/true", limits := { memoryMaxBytes := some 0 } }
  let zeroPids : BoxSpec := { program := "/bin/true", limits := { pidsMax := some 0 } }
  let zeroFileAndOut : BoxSpec :=
    { program := "/bin/true"
      limits := { timeoutMs := 100, fileSizeMaxBytes := some 0, maxOutputBytes := some 0 } }
  NondetTest.assert (match api.validateSpec zeroTimeout with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroMem with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match api.validateSpec zeroPids with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert ((api.validateSpec zeroFileAndOut).isOk = true)

/-- `api.validateSpec` rejects empty env keys, `'='` in env keys, or NUL bytes in env keys or values. -/
def test_psandbox_validateSpec_rejectsInvalidEnv
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let spec ← nondet BoxSpec
  let idx ← nondet Nat
  assume (idx < spec.env.size)
  assume (isValidEnvPair spec.env[idx]! = false)
  match api.validateSpec spec with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `api.validateSpec` defaults `cwd = none` to `"/tmp"`, injects `.scratch "/tmp"` iff no mount targets `"/tmp"`, injects `("PATH", "/usr/bin:/bin")` iff `"PATH"` is absent, deduplicates env keys (last-write-wins), and is idempotent. -/
def test_psandbox_validateSpec_defaultsOverridesAndIdempotence
    {runner} [NondetTest runner] (api : ProcessSandboxApi) : runner Unit := do
  let k ← nondet String
  let v₁ ← nondet String
  let v₂ ← nondet String
  assume (isValidEnvPair (k, v₁) = true ∧ isValidEnvPair (k, v₂) = true)
  assume (k ≠ "PATH")
  let specDefault : BoxSpec :=
    { program := "python3"
      args := #["-c", "pass"]
      cwd := none
      mounts := #[.readOnly "/work/src" "/workspace/"]
      env := #[(k, v₁), (k, v₂)] }
  match api.validateSpec specDefault with
  | .error _ => NondetTest.assert False
  | .ok valid =>
    NondetTest.assert (valid.cwd = "/tmp")
    NondetTest.assert (valid.mounts = #[.scratch "/tmp", .readOnly "/work/src" "/workspace"])
    NondetTest.assert (valid.env = #[("PATH", "/usr/bin:/bin"), (k, v₂)])
    NondetTest.assert (api.validateSpec (validBoxSpecToBoxSpec valid) = .ok valid)
  let customPath ← nondet String
  assume (!hasNulChar customPath.toList)
  let specCustomTmpAndPath : BoxSpec :=
    { program := "/usr/bin/env"
      cwd := some "/workspace/sub/"
      mounts := #[.readWrite "/host/tmp" "/tmp/"]
      env := #[("PATH", customPath)] }
  match api.validateSpec specCustomTmpAndPath with
  | .error _ => NondetTest.assert False
  | .ok validCustom =>
    NondetTest.assert (validCustom.cwd = "/workspace/sub")
    NondetTest.assert (validCustom.mounts = #[.readWrite "/host/tmp" "/tmp"])
    NondetTest.assert (validCustom.env = #[("PATH", customPath)])
    NondetTest.assert (api.validateSpec (validBoxSpecToBoxSpec validCustom) = .ok validCustom)

/-- Running an invalid `BoxSpec` fails immediately with `.invalidInput` and leaves `MockSandboxState` untouched. -/
def test_psandbox_run_invalidSpec_hasZeroSideEffects
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  match api.validateSpec spec with
  | .ok _ => assume False
  | .error _ =>
    let (res, s₁) := (api.run spec).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- `isAvailable` probes full host capability without leaking resources, and when either `preflight` or pre-`execvp` `spawnBox` setup fails `run` fails closed with `.unavailable`, zero guest execution, and conserved resources. -/
def test_psandbox_isAvailable_and_failClosedUnavailable
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let (avail, sAvail) := api.isAvailable.run s₀
  let expectedAvail :=
    s₀.hostBaseAvailable && s₀.memoryCgroupAvailable && s₀.pidsCgroupAvailable
  NondetTest.assert (avail = expectedAvail ∧
    sAvail.openPlans = s₀.openPlans ∧
    sAvail.activeBoxes = s₀.activeBoxes ∧
    sAvail.activeForwarders = s₀.activeForwarders ∧
    sAvail.spawnCalls = s₀.spawnCalls ∧
    sAvail.guestExecCalls = s₀.guestExecCalls)
  let sUnavail ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  assume ((api.validateSpec spec).isOk = true)
  assume (!sUnavail.hostBaseAvailable ∨
    (spec.limits.memoryMaxBytes.isSome && !sUnavail.memoryCgroupAvailable) ∨
    (spec.limits.pidsMax.isSome && !sUnavail.pidsCgroupAvailable))
  let (res, s₁) := (api.run spec).run sUnavail
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    s₁.spawnCalls = sUnavail.spawnCalls ∧
    s₁.guestExecCalls = sUnavail.guestExecCalls ∧
    s₁.openPlans = sUnavail.openPlans ∧
    s₁.activeBoxes = sUnavail.activeBoxes ∧
    s₁.activeForwarders = sUnavail.activeForwarders)
  let sSpawnUnavail ← nondet MockSandboxState
  let specSpawn ← nondet BoxSpec
  assume ((api.validateSpec specSpawn).isOk = true)
  assume (sSpawnUnavail.hostBaseAvailable = true ∧
    sSpawnUnavail.memoryCgroupAvailable = true ∧
    sSpawnUnavail.pidsCgroupAvailable = true)
  let sPreExecFail : MockSandboxState :=
    { sSpawnUnavail with
      failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
  let (resSpawn, s₂) := (api.run specSpawn).run sPreExecFail
  NondetTest.assert ((∃ e, resSpawn = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    s₂.guestExecCalls = sPreExecFail.guestExecCalls ∧
    s₂.openPlans = sPreExecFail.openPlans ∧
    s₂.activeBoxes = sPreExecFail.activeBoxes ∧
    s₂.activeForwarders = sPreExecFail.activeForwarders)

/-- `run` compiles an empty-root, clean-env, direct-`cgroup v2` plan that filters presets to allowlists, preserves top-level symlinks, masks nested host `$HOME` under `/usr` (including through symlinked preset roots), resolves synthetic `/etc/hosts` box-locally, preserves stable depth-sorted mounts, blocks `socket(AF_UNIX, ...)` while allowing anonymous `socketpair`, and sets `clone3` `ENOSYS` fallback. -/
def test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  let sWithPreset : MockSandboxState :=
    { s₀ with
      preset :=
        { systemEntries :=
            #[ .readOnlyDir "/usr"
             , .topSymlink "/bin" "usr/bin"
             , .topSymlink "/lib" "usr/lib"
             , .readOnlyDir "/home" ]
          etcPaths := #["/etc/passwd", "/etc/localtime", "/etc/shadow"]
          excludedHomePaths :=
            #[ "/usr/local/homes/user"
             , "/lib/custom_home/bob"
             , "/home/user" ] } }
  let spec : BoxSpec :=
    { program := "env"
      mounts := #[.readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"] }
  let (_, s₁) := (api.run spec).run sWithPreset
  match s₁.lastSealedPlan with
  | none => NondetTest.assert False
  | some plan =>
    NondetTest.assert (isValidCompiledPlan plan = true)
    NondetTest.assert (plan.emptyRoot = true ∧
      plan.directCgroupV2Fs = true ∧
      plan.blockUnixSocketAndSmc = true ∧
      plan.allowAnonUnixSocketpair = true ∧
      plan.clone3EnosysFallback = true ∧
      plan.cleanEnv = true)
    NondetTest.assert (plan.presetSystemEntries =
      #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin", .topSymlink "/lib" "usr/lib"])
    NondetTest.assert (plan.presetEtcPaths = #["/etc/passwd", "/etc/localtime"])
    NondetTest.assert (plan.maskedPresetPaths =
      #["/usr/local/homes/user", "/usr/lib/custom_home/bob"])
    NondetTest.assert (resolveBoxPath plan "/etc/hosts" = .virtualEtcHosts)
    NondetTest.assert (plan.cwd = "/tmp")
    NondetTest.assert (plan.env = #[("PATH", "/usr/bin:/bin")])
    NondetTest.assert (plan.userMounts.toList.map mountBoxPath = ["/tmp", "/work", "/work/sub"])

/-- `run` returns all exit codes (including `125`, `126`, `127`, `137`, `255`), signals, timeouts, and output-cap outcomes cleanly without magic exit numbers, and bounds `stdout.size + stderr.size ≤ limit`. -/
def test_psandbox_run_outcomesAndOutputCap
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let code ← nondet Int
  let sig ← nondet Int
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  let baseState : MockSandboxState := {}
  let (rExit, sExit) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rExit = .ok { outcome := .exited code, stdout := outBytes, stderr := errBytes } ∧
    sExit.openPlans = [] ∧ sExit.activeBoxes = [] ∧ sExit.activeForwarders = [])
  let (rSig, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rSig = .ok { outcome := .signaled sig, stdout := outBytes, stderr := errBytes })
  let (rTout, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes } }
  NondetTest.assert (rTout = .ok { outcome := .timedOut, stdout := outBytes, stderr := errBytes })
  let (rNoLim, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := none } }).run
      { baseState with scriptedOutput := .ok { outcome := .outputLimitExceeded, stdout := outBytes, stderr := errBytes } }
  match rNoLim with
  | .ok res => NondetTest.assert (res.outcome ≠ .outputLimitExceeded)
  | .error e => NondetTest.assert (e.message ≠ "")
  let cap ← nondet Nat
  let (rCap, _) :=
    (api.run { program := "/bin/sh", limits := { maxOutputBytes := some cap } }).run
      { baseState with scriptedOutput := .ok { outcome := .exited 0, stdout := outBytes, stderr := errBytes } }
  match rCap with
  | .error _ => NondetTest.assert False
  | .ok res =>
    NondetTest.assert (res.stdout.size + res.stderr.size ≤ cap)
    if outBytes.size + errBytes.size > cap then
      NondetTest.assert (res.outcome = .outputLimitExceeded)
    else
      NondetTest.assert (res.outcome = .exited 0 ∧ res.stdout = outBytes ∧ res.stderr = errBytes)

/-- `run` forwards `spec.stdin` and `spec.limits.timeoutMs` verbatim to `readBoxOutput` without dropping or zeroing either parameter. -/
def test_psandbox_run_forwardsStdinAndTimeoutMs
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let stdinBytes ← nondet ByteArray
  let timeoutMs ← nondet Nat
  assume (timeoutMs > 0)
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let spec : BoxSpec :=
    { program := "/bin/cat"
      stdin := stdinBytes
      limits := { timeoutMs := timeoutMs } }
  let (res, s₁) := (api.run spec).run s₀
  NondetTest.assert (res.isOk = true ∧
    s₁.lastReadStdin = some stdinBytes ∧
    s₁.lastReadTimeoutMs = some timeoutMs ∧
    s₁.openPlans = s₀.openPlans ∧
    s₁.activeBoxes = s₀.activeBoxes ∧
    s₁.activeForwarders = s₀.activeForwarders)

/-- `run` brackets `(boxPort, hostPort)` forwarders when `portForwards` is non-empty, skips starting forwarders when empty, and never runs the guest if forwarder startup fails. -/
def test_psandbox_run_portForwarderBracket
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
  assume (s₀.failSpawnWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let fwds : Array PortForward := #[{ boxPort := 8080, hostPort := 18080 }]
  let specFwd : BoxSpec := { program := "/bin/true", portForwards := fwds }
  let (rOk, sOk) := (api.run specFwd).run { s₀ with failForwarderStartWith := none }
  NondetTest.assert (rOk.isOk = true ∧
    sOk.lastStartedForwards = some fwds ∧
    sOk.activeForwarders = s₀.activeForwarders ∧
    sOk.activeBoxes = s₀.activeBoxes ∧
    sOk.openPlans = s₀.openPlans)
  let specNoFwd : BoxSpec := { program := "/bin/true", portForwards := #[] }
  let (rNoFwd, sNoFwd) := (api.run specNoFwd).run { s₀ with failForwarderStartWith := none }
  NondetTest.assert (rNoFwd.isOk = true ∧
    sNoFwd.lastStartedForwards = s₀.lastStartedForwards ∧
    sNoFwd.activeForwarders = s₀.activeForwarders)
  let fwdErr : SandboxError := { kind := .ioError, message := "bind failed" }
  let (rFail, sFail) := (api.run specFwd).run { s₀ with failForwarderStartWith := some fwdErr }
  NondetTest.assert ((∃ e, rFail = .error e ∧ e.kind = .ioError ∧ e.message ≠ "") ∧
    sFail.guestExecCalls = s₀.guestExecCalls ∧
    sFail.activeForwarders = s₀.activeForwarders ∧
    sFail.activeBoxes = s₀.activeBoxes ∧
    sFail.openPlans = s₀.openPlans)

/-- Across all normal outcomes and errors, `run` conserves `openPlans`, `activeBoxes`, and `activeForwarders` and executes `killProcessGroup`, `pidfdKill`, and `reapBox` whenever `spawnBox` succeeded. -/
def test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockSandboxState
  let spec ← nondet BoxSpec
  let (res, s₁) := (api.run spec).run s₀
  NondetTest.assert (s₁.openPlans = s₀.openPlans ∧
    s₁.activeBoxes = s₀.activeBoxes ∧
    s₁.activeForwarders = s₀.activeForwarders)
  match res with
  | .error err => NondetTest.assert (err.message ≠ "")
  | .ok _ => pure ()
  if s₁.activeBoxes == s₀.activeBoxes && s₁.spawnCalls == s₀.spawnCalls + 1 && s₀.failSpawnWith.isNone then
    NondetTest.assert (s₁.killPgCalls = s₀.killPgCalls + 1 ∧
      s₁.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
      s₁.reapCalls = s₀.reapCalls + 1)
  else
    pure ()

/-- Under `MonadFinally` (`ExceptT String (StateM MockSandboxState)`), uncaught cancellation exceptions during `startPortForwarders` or `readBoxOutput` still stop forwarders, kill/pidfdKill/reap the box, and close the sealed plan. -/
def test_psandbox_run_monadFinallyCleansUpOnCancellation
    {runner} [NondetTest runner]
    (mkApiEx : ProcessSandboxBuilder (ExceptT String (StateM MockSandboxState))) : runner Unit := do
  let apiEx := mkApiEx mockRawOpsEx
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
    s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  let spec : BoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }] }
  let (rReadCancel, sReadCancel) :=
    (apiEx.run spec).run { s₀ with throwOnReadOutput := true, throwOnStartForwarders := false }
  NondetTest.assert (rReadCancel = .error "cancelled-during-read" ∧
    sReadCancel.openPlans = s₀.openPlans ∧
    sReadCancel.activeBoxes = s₀.activeBoxes ∧
    sReadCancel.activeForwarders = s₀.activeForwarders ∧
    sReadCancel.killPgCalls = s₀.killPgCalls + 1 ∧
    sReadCancel.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
    sReadCancel.reapCalls = s₀.reapCalls + 1)
  let (rFwdCancel, sFwdCancel) :=
    (apiEx.run spec).run { s₀ with throwOnReadOutput := false, throwOnStartForwarders := true }
  NondetTest.assert (rFwdCancel = .error "cancelled-during-forwarder-start" ∧
    sFwdCancel.guestExecCalls = s₀.guestExecCalls ∧
    sFwdCancel.openPlans = s₀.openPlans ∧
    sFwdCancel.activeBoxes = s₀.activeBoxes ∧
    sFwdCancel.activeForwarders = s₀.activeForwarders ∧
    sFwdCancel.killPgCalls = s₀.killPgCalls + 1 ∧
    sFwdCancel.pidfdKillCalls = s₀.pidfdKillCalls + 1 ∧
    sFwdCancel.reapCalls = s₀.reapCalls + 1)

/-- Concrete 3-category shared-kernel checks covering blocked `socket(AF_UNIX, ...)` vs allowed `socketpair`, `clone3` `ENOSYS` fallback vs `CLONE_NEW*` block, `/tmp` scratch vs `readOnly` vs `readWrite`, and `allowBoxLocalhost` vs `portForwards`. -/
def test_psandbox_model_threeCategorySyscallSemantics
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall) : runner Unit := do
  let st₀ ← nondet SandboxWorldState
  assume (st₀.box.boxMemoryBytes = 0 ∧ st₀.box.boxProcs = [1])
  let preset : HostRuntimePreset :=
    { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/bin" "usr/bin"]
      etcPaths := #["/etc/passwd"]
      excludedHomePaths := #["/usr/local/homes/dev"] }
  let spec : BoxSpec :=
    { program := "/bin/sh"
      mounts :=
        #[ .readOnly "/host/ro" "/ro"
         , .readWrite "/host/rw" "/rw" ]
      allowBoxLocalhost := true
      portForwards := #[{ boxPort := 8080, hostPort := 18080 }]
      limits :=
        { timeoutMs := 5000
          memoryMaxBytes := some 4096
          pidsMax := some 4
          fileSizeMaxBytes := some 16 } }
  match validateSpecPure spec with
  | .error _ => NondetTest.assert False
  | .ok valid =>
    let plan := compilePlan valid preset
    let payload := "ok".toUTF8
    let bigPayload := String.ofList (List.replicate 32 'x') |>.toUTF8
    NondetTest.assert (stepFn plan st₀ (.adminOp (.unixSocketOrSmcOp "/var/run/docker.sock")) =
      .error .blockedBySeccompOrNamespace)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .stream) = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .seqpacket) = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.anonUnixSocketpair .disallowedOther) =
      .error .blockedBySeccompOrNamespace)
    NondetTest.assert (stepFn plan st₀ .clone3Attempt = .error .clone3FallbackEnosys)
    NondetTest.assert (stepFn plan st₀ (.cloneProc 2 true) = .error .blockedBySeccompOrNamespace)
    NondetTest.assert ((stepFn plan st₀ (.fsRead "/home/u/.ssh/id_rsa")).isOk = false)
    NondetTest.assert ((stepFn plan st₀ (.fsRead "/usr/local/homes/dev/.ssh/id_rsa")).isOk = false)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/ro/file.txt" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/rw/big.txt" bigPayload) = .error .fileSizeLimitExceeded)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/") = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/etc/hosts") = .ok st₀)
    NondetTest.assert (stepFn plan st₀ (.fsWrite "/etc/hosts" payload) = .error .readOnlyFilesystem)
    NondetTest.assert (stepFn plan st₀ (.fsRead "/usr/local/homes/dev") = .error .unmountedOrMaskedPath)
    match stepFn plan st₀ (.fsWrite "/tmp/scratch.txt" payload) with
    | .error _ => NondetTest.assert False
    | .ok stTmp =>
      NondetTest.assert (stTmp.host = st₀.host ∧
        lookupFsBytes stTmp.box.scratchFs "/tmp/scratch.txt" = some payload)
    match stepFn plan st₀ (.tcpSend true 9090 payload) with
    | .error _ => NondetTest.assert False
    | .ok stLo =>
      NondetTest.assert (stLo.host = st₀.host ∧
        stLo.box.boxLocalPorts = st₀.box.boxLocalPorts ++ [(9090, payload)])
    match stepFn plan st₀ (.tcpSend true 8080 payload) with
    | .error _ => NondetTest.assert False
    | .ok stFwd =>
      NondetTest.assert (stFwd.host.hostPorts = st₀.host.hostPorts ++ [(18080, payload)] ∧
        stFwd.host.hostFs = st₀.host.hostFs ∧
        stFwd.host.hostAdminState = st₀.host.hostAdminState)
    match stepFn plan st₀ (.fsWrite "/rw/out.txt" payload) with
    | .error _ => NondetTest.assert False
    | .ok stRw =>
      NondetTest.assert (lookupHostFile stRw.host "/host/rw/out.txt" = some payload ∧
        stRw.host.hostPorts = st₀.host.hostPorts ∧
        stRw.host.hostAdminState = st₀.host.hostAdminState)

/-- Frozen model specification: `HostState` never changes outside explicit `readWrite` mounts and `portForwards` across arbitrary `List GuestSyscall` traces (`SpecHostUnchangedOutsideGrants`). -/
def test_psandbox_model_hostUnchangedOutsideGrants
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall) : runner Unit :=
  NondetTest.assert (SpecHostUnchangedOutsideGrantsOn stepFn)

/-- Frozen model specification: whole-box `pids.max` and `memory.max` hold throughout execution and zero box processes survive teardown (`SpecZeroSurvivingBoxProcs`). -/
def test_psandbox_model_zeroSurvivingBoxProcs
    {runner} [NondetTest runner]
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState :=
      stepGuestSyscall)
    (teardownFn : SandboxWorldState → SandboxWorldState := reapAndTeardownBox) : runner Unit :=
  NondetTest.assert (SpecZeroSurvivingBoxProcsOn stepFn teardownFn)

/-- Frozen model specification: `validateSpecPure` and `compilePlan` produce sound empty-root, `$HOME`-masked, clean-env, direct-`cgroup v2` plans (`SpecCompilePlanSound`). -/
def test_psandbox_model_compilePlanSound
    {runner} [NondetTest runner]
    (validateFn : BoxSpec → Except SandboxError ValidBoxSpec := validateSpecPure)
    (compileFn : ValidBoxSpec → HostRuntimePreset → CompiledSandboxPlan := compilePlan) : runner Unit :=
  NondetTest.assert (SpecCompilePlanSoundOn validateFn compileFn)

/-- `run` queries `raw.hostSeccompArch`, seals `api.encodeSeccompBpf (api.compileSeccompBpf arch)` for both `.x86_64` and `.aarch64` (producing architecture-specific valid cBPF filters matching `auditArchOf arch`), and fails closed with `.unavailable`, zero `spawnCalls`, zero `guestExecCalls`, and conserved resources when `hostSeccompArch` fails. -/
def test_seccomp_run_queriesHostArchAndSealsEncodedFilter
    {runner} [NondetTest runner]
    (mkApi : ProcessSandboxBuilder (StateM MockSandboxState)) : runner Unit := do
  let api := mkApi mockRawOps
  let arch ← nondet SeccompArch
  let s₀ ← nondet MockSandboxState
  assume (s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
  assume (s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
  assume (s₀.scriptedOutput.isOk = true)
  let sArch : MockSandboxState := { s₀ with hostSeccompArch? := some arch }
  let (resOk, sOk) := (api.run { program := "/bin/true" }).run sArch
  let expectedProg := Seccomp.compileSeccompBpf arch
  let expectedBytes := Seccomp.encodeSeccompBpf expectedProg
  NondetTest.assert (resOk.isOk = true ∧
    isValidLinuxSeccompProg expectedProg = true ∧
    expectedBytes = encodeSeccompBpfModel expectedProg ∧
    evalBpf expectedProg { arch := auditArchOf arch, nr := 0 } = some 0x7fff0000 ∧
    evalBpf expectedProg { arch := 0, nr := 0 } = some 0x00050001 ∧
    sOk.lastSealedSeccompBytes = some expectedBytes ∧
    sOk.openPlans = sArch.openPlans ∧
    sOk.activeBoxes = sArch.activeBoxes ∧
    sOk.activeForwarders = sArch.activeForwarders)
  let sNoArch ← nondet MockSandboxState
  let specFail ← nondet BoxSpec
  assume ((api.validateSpec specFail).isOk = true)
  assume (sNoArch.hostBaseAvailable = true ∧
    sNoArch.memoryCgroupAvailable = true ∧
    sNoArch.pidsCgroupAvailable = true ∧
    sNoArch.hostSeccompArch? = none)
  let (resFail, sFail) := (api.run specFail).run sNoArch
  NondetTest.assert ((∃ e, resFail = .error e ∧ e.kind = .unavailable ∧ e.message ≠ "") ∧
    sFail.spawnCalls = sNoArch.spawnCalls ∧
    sFail.guestExecCalls = sNoArch.guestExecCalls ∧
    sFail.openPlans = sNoArch.openPlans ∧
    sFail.activeBoxes = sNoArch.activeBoxes ∧
    sFail.activeForwarders = sNoArch.activeForwarders)

end LeanSwe.ProcessSandbox
