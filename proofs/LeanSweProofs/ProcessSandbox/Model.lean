import LeanSwe.Fs.Types
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.ProcessSandbox.Types

namespace LeanSwe.ProcessSandbox.Model

open LeanSwe.ProcessSandbox

/-- Return `true` iff `cs` contains a NUL character (`Char.ofNat 0`). -/
def hasNulChar : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChar cs

/-- Split `cs` on `'/'` separators, preserving empty segments. -/
def splitSlashChars (cs : List Char) : List (List Char) :=
  let rec go (acc : List Char) : List Char → List (List Char)
    | [] => [acc.reverse]
    | c :: rest => if c == '/' then acc.reverse :: go [] rest else go (c :: acc) rest
  go [] cs

/-- Return `true` iff all elements in `xs` are pairwise distinct under `BEq`. -/
def allDistinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

/-- Deduplicate environment `(key, value)` pairs keeping the last occurrence of each key. -/
def dedupEnvPairs : List (String × String) → List (String × String)
  | [] => []
  | kv :: rest =>
    let tail := dedupEnvPairs rest
    if tail.any (fun p => p.1 == kv.1) then tail else kv :: tail

/-- Parse a clean absolute path into canonical segments, rejecting empty, NUL, relative, or `".."` paths. -/
def parseCleanAbsSegs (p : String) : Option (List String) :=
  let cs := p.toList
  if cs.isEmpty || hasNulChar cs || cs.head? != some '/' then none
  else
    let rawSegs := splitSlashChars cs.tail
    if rawSegs.any (fun s => s == ['.', '.']) then none
    else some <| rawSegs.filterMap fun s =>
      if s.isEmpty || s == ['.'] then none else some (String.ofList s)

/-- Format canonical path segments back into a canonical absolute path string. -/
def formatAbsSegs : List String → String
  | [] => "/"
  | segs => "/" ++ String.intercalate "/" segs

/-- Validate and canonicalize an absolute path string, returning `none` on empty, NUL, relative, or `".."`. -/
def normalizeCleanAbsPath (p : String) : Option String :=
  (parseCleanAbsSegs p).map formatAbsSegs

/-- Reserved top-level OS runtime directories that caller mounts may not target or shadow. -/
def reservedSystemTopDirs : List String :=
  ["usr", "bin", "sbin", "lib", "lib64", "etc", "dev", "proc"]

/-- Return `true` iff canonical box target segments `segs` equal `"/"` or lie under a reserved OS directory. -/
def isReservedBoxSegs : List String → Bool
  | [] => true
  | top :: _ => reservedSystemTopDirs.contains top

/-- Default `PATH` added to clean-slate `env` whenever `"PATH"` is absent from `BoxSpec.env`. -/
def defaultSandboxPath : String := "/usr/bin:/bin"

/-- Default working directory inside the sandbox whenever `BoxSpec.cwd` is `none`. -/
def defaultSandboxCwd : String := "/tmp"

/-- Return `true` iff `(k, v)` is a valid environment entry (non-empty `=`-free NUL-free key, NUL-free value). -/
def isValidEnvPair (kv : String × String) : Bool :=
  let kcs := kv.1.toList
  !kcs.isEmpty && !kcs.contains '=' && !hasNulChar kcs && !hasNulChar kv.2.toList

/-- Construct an `.invalidInput` `SandboxError` with optional associated `path`. -/
def invalidInput (message : String) (path : Option String := none) : SandboxError :=
  { kind := .invalidInput, path, message }

/-- Validate and normalize a `(hostPath, boxPath)` mount pair using constructor `ctor`. -/
def validateHostBoxPair (ctor : String → String → SandboxMount)
    (hostPath boxPath : String) : Except SandboxError SandboxMount :=
  match parseCleanAbsSegs hostPath, parseCleanAbsSegs boxPath with
  | none, _ => .error (invalidInput "invalid mount hostPath" (some hostPath))
  | _, none => .error (invalidInput "invalid mount boxPath" (some boxPath))
  | some hSegs, some bSegs =>
    if isReservedBoxSegs bSegs then
      .error (invalidInput "mount boxPath targets a reserved OS path" (some boxPath))
    else .ok (ctor (formatAbsSegs hSegs) (formatAbsSegs bSegs))

/-- Validate and normalize a single `SandboxMount`, rejecting malformed paths and reserved box targets. -/
def validateAndNormalizeMount : SandboxMount → Except SandboxError SandboxMount
  | .readOnly hp bp => validateHostBoxPair .readOnly hp bp
  | .readWrite hp bp => validateHostBoxPair .readWrite hp bp
  | .scratch bp =>
    match parseCleanAbsSegs bp with
    | none => .error (invalidInput "invalid scratch mount boxPath" (some bp))
    | some bSegs =>
      if isReservedBoxSegs bSegs then
        .error (invalidInput "scratch boxPath targets a reserved OS path" (some bp))
      else .ok (.scratch (formatAbsSegs bSegs))

/-- Validate and normalize a list of `SandboxMount` entries in order. -/
def validateMountsList : List SandboxMount → Except SandboxError (List SandboxMount)
  | [] => .ok []
  | m :: rest => do
    let normM ← validateAndNormalizeMount m
    let normRest ← validateMountsList rest
    .ok (normM :: normRest)

/-- Return `true` iff `m` is a `.readWrite` mount. -/
def isReadWriteMount : SandboxMount → Bool
  | .readWrite _ _ => true
  | .readOnly _ _ | .scratch _ => false

/-- Return `true` iff distinct mounts `m₁` and `m₂` introduce an unshadowed overlapping `.readWrite` `hostPath` alias. -/
def hasUnshadowedRwOverlapPair (m₁ m₂ : SandboxMount) : Bool :=
  if !(isReadWriteMount m₁ || isReadWriteMount m₂) then false
  else
    match mountHostPath? m₁, mountHostPath? m₂ with
    | some hp₁, some hp₂ =>
      match parseCleanAbsSegs hp₁, parseCleanAbsSegs (mountBoxPath m₁),
            parseCleanAbsSegs hp₂, parseCleanAbsSegs (mountBoxPath m₂) with
      | some h₁, some b₁, some h₂, some b₂ =>
        let p₁₂ := h₁.isPrefixOf h₂
        let p₂₁ := h₂.isPrefixOf h₁
        if !(p₁₂ || p₂₁) then false
        else
          let shadowed₁₂ := p₁₂ && b₂ == b₁ ++ h₂.drop h₁.length
          let shadowed₂₁ := p₂₁ && b₁ == b₂ ++ h₁.drop h₂.length
          !(shadowed₁₂ || shadowed₂₁)
      | _, _, _, _ => false
    | _, _ => false

/-- Return `true` iff any pair of distinct mounts in `ms` introduces an unshadowed overlapping `.readWrite` `hostPath` alias. -/
def hasUnshadowedRwOverlap : List SandboxMount → Bool
  | [] => false
  | m :: rest => rest.any (hasUnshadowedRwOverlapPair m) || hasUnshadowedRwOverlap rest

/-- Authoritative pure boundary validator turning `BoxSpec` into `ValidBoxSpec` or `.invalidInput`. -/
def validateSpecPure (spec : BoxSpec) : Except SandboxError ValidBoxSpec := do
  if spec.program.isEmpty then .error (invalidInput "program must not be empty")
  else if hasNulChar spec.program.toList then .error (invalidInput "program must not contain NUL bytes")
  else if spec.args.toList.any (fun a => hasNulChar a.toList) then
    .error (invalidInput "args must not contain NUL bytes")
  else if !spec.env.toList.all isValidEnvPair then
    .error (invalidInput "invalid environment variable entry")
  else if spec.timeoutMs == some 0 then
    .error (invalidInput "timeoutMs must be greater than zero when set")
  else if spec.maxOutputBytes == some 0 then
    .error (invalidInput "maxOutputBytes must be greater than zero when set")
  else
    let normCwd ← match spec.cwd with
      | none => .ok defaultSandboxCwd
      | some d => match normalizeCleanAbsPath d with
        | none => .error (invalidInput "cwd must be a clean absolute path" (some d))
        | some cleanD => .ok cleanD
    let normMounts ← validateMountsList spec.mounts.toList
    if !allDistinct (normMounts.map mountBoxPath) then
      .error (invalidInput "duplicate mount boxPath in BoxSpec")
    else if hasUnshadowedRwOverlap normMounts then
      .error (invalidInput "overlapping readWrite mount hostPath in BoxSpec")
    else
      let mountsWithTmp :=
        if normMounts.any (fun m => mountBoxPath m == "/tmp") then normMounts
        else .scratch "/tmp" :: normMounts
      let deduped := dedupEnvPairs spec.env.toList
      let cleanEnv :=
        if deduped.any (fun kv => kv.1 == "PATH") then deduped
        else ("PATH", defaultSandboxPath) :: deduped
      .ok { program := spec.program, args := spec.args, env := cleanEnv.toArray,
            cwd := normCwd, stdin := spec.stdin, mounts := mountsWithTmp.toArray,
            network := spec.network, timeoutMs := spec.timeoutMs,
            maxOutputBytes := spec.maxOutputBytes }

/-- Pure model of `LeanSwe.ProcessSandbox.validateSpec`, delegating directly to `validateSpecPure`. -/
def validateSpecModel (spec : BoxSpec) : Except SandboxError ValidBoxSpec :=
  validateSpecPure spec

/-- Abstract filesystem mapping canonical absolute paths to optional file contents. -/
abbrev FsState := String → Option ByteArray

/-- Abstract non-filesystem host or guest state tracked across a sandboxed run. -/
structure NonFsState where
  /-- Environment variables visible in this execution context. -/
  env : List (String × String)
  /-- Running processes visible in this execution context. -/
  processes : List String
  /-- Network state visible in this execution context. -/
  network : List String
  /-- Surviving un-reaped orphan guest process count after return. -/
  orphanCount : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Isolated command and state bundle delivered to a guest program launched under a `ValidBoxSpec`. -/
structure GuestInput where
  /-- Validated executable name or path invoked inside the sandbox. -/
  program : String
  /-- Validated explicit argument array passed verbatim to the guest. -/
  args : Array String
  /-- Canonical absolute working directory inside the sandbox. -/
  cwd : String
  /-- Standard input bytes delivered to the guest before closing stdin. -/
  stdin : ByteArray
  /-- Projected initial guest filesystem `S'`. -/
  fs : FsState
  /-- Projected initial isolated guest non-filesystem state. -/
  nonFs : NonFsState

instance : Inhabited GuestInput where
  default :=
    { program := "/bin/true"
      args := #[]
      cwd := defaultSandboxCwd
      stdin := ByteArray.empty
      fs := fun _ => none
      nonFs := default }

/-- Arbitrary guest program semantics mapping `GuestInput` to `(outcome, stdout, stderr, S'', guestNonFs')`. -/
abbrev GuestProgram :=
  GuestInput → SandboxOutcome × ByteArray × ByteArray × FsState × NonFsState

/-- Return `true` iff `k` is a non-validation host error category permitted on a `ValidBoxSpec`. -/
def isHostErrorKind : SandboxErrorKind → Bool
  | .invalidInput => false
  | .unavailable | .notFound | .permissionDenied | .ioError => true

/-- Abstract host state observed before and after each sandbox operation. -/
structure HostWorld where
  /-- Host filesystem state `S`. -/
  fs : FsState := fun _ => none
  /-- Read-only OS runtime preset exposed under reserved top-level directories inside the sandbox. -/
  presetFs : FsState := fun _ => none
  /-- Host non-filesystem state (environment, processes, network, surviving orphans). -/
  nonFs : NonFsState := default
  /-- Whether the host supports sandboxed execution (`isAvailable` result). -/
  available : Bool := true
  /-- Whether transient guest execution timeouts are permitted when `timeoutMs` is configured. -/
  allowTimeout : Bool := false
  /-- Optional pre-execution host failure for a validated spec (e.g. missing mount source or executable). -/
  hostError : ValidBoxSpec → Option SandboxErrorKind := fun _ => none
  /-- Arbitrary guest program semantics executed inside the sandbox. -/
  guest : GuestProgram := fun inp =>
    (.exited 0, ByteArray.empty, ByteArray.empty, inp.fs, inp.nonFs)

instance : Inhabited HostWorld where
  default := {}

/-- Select the mount with the longest canonical `boxPath` prefix covering `targetSegs`. -/
def bestMountForBoxPath (mounts : List SandboxMount) (targetSegs : List String) :
    Option SandboxMount :=
  mounts.foldl (init := (none : Option (Nat × SandboxMount))) (fun best m =>
    match parseCleanAbsSegs (mountBoxPath m) with
    | none => best
    | some bSegs =>
      if bSegs.isPrefixOf targetSegs then
        match best with
        | none => some (bSegs.length, m)
        | some (bestLen, _) => if bSegs.length ≥ bestLen then some (bSegs.length, m) else best
      else best)
  |>.map Prod.snd

/-- Project host filesystem `S` into guest filesystem `S'` through `mounts` and read-only `presetFs`. -/
def projectGuestFs (hostFs : FsState) (mounts : List SandboxMount) (presetFs : FsState) : FsState :=
  fun rawBoxPath =>
    match parseCleanAbsSegs rawBoxPath with
    | none => none
    | some pSegs =>
      match bestMountForBoxPath mounts pSegs with
      | some (.readOnly hp bp) | some (.readWrite hp bp) =>
        match parseCleanAbsSegs hp, parseCleanAbsSegs bp with
        | some hpSegs, some bpSegs => hostFs (formatAbsSegs (hpSegs ++ pSegs.drop bpSegs.length))
        | _, _ => none
      | some (.scratch _) => none
      | none =>
        match pSegs with
        | [] => none
        | top :: _ => if reservedSystemTopDirs.contains top then presetFs (formatAbsSegs pSegs) else none

/-- Construct the isolated initial `NonFsState` visible to a guest launched under `valid`. -/
def projectGuestNonFs (hostNonFs : NonFsState) (valid : ValidBoxSpec) : NonFsState :=
  { env := valid.env.toList
    processes := []
    network := match valid.network with | .closed => [] | .open => hostNonFs.network
    orphanCount := 0 }

/-- Project `HostWorld` and validated `ValidBoxSpec` into the isolated `GuestInput` seen by `s.guest`. -/
def projectGuestInput (s : HostWorld) (valid : ValidBoxSpec) : GuestInput where
  program := valid.program
  args := valid.args
  cwd := valid.cwd
  stdin := valid.stdin
  fs := projectGuestFs s.fs valid.mounts.toList s.presetFs
  nonFs := projectGuestNonFs s.nonFs valid

/-- Return `true` iff `m` is a `.readWrite` mount whose canonical `hostPath` is a prefix of `hSegs`. -/
def mountCoversHostSegs (hSegs : List String) : SandboxMount → Bool
  | .readWrite hp _ =>
    match parseCleanAbsSegs hp with
    | some hpSegs => hpSegs.isPrefixOf hSegs
    | none => false
  | .readOnly _ _ | .scratch _ => false

/-- Apply one mount's write-back rule at canonical host segments `hSegs`, keeping `acc` unless an unshadowed `.readWrite` mount owns it. -/
def applyMountWriteBack (allMounts : List SandboxMount) (guestFsAfter : FsState)
    (hSegs : List String) (acc : Option ByteArray) (m : SandboxMount) : Option ByteArray :=
  match m with
  | .readWrite hp bp =>
    match parseCleanAbsSegs hp, parseCleanAbsSegs bp with
    | some hpSegs, some bpSegs =>
      if hpSegs.isPrefixOf hSegs then
        let guestSegs := bpSegs ++ hSegs.drop hpSegs.length
        if bestMountForBoxPath allMounts guestSegs == some m then
          guestFsAfter (formatAbsSegs guestSegs)
        else acc
      else acc
    | _, _ => acc
  | .readOnly _ _ | .scratch _ => acc

/-- Update `hostFs` with bytes from `guestFsAfter` strictly under unshadowed `.readWrite` mounts (`S'' -> S_next`). -/
def applyWriteBack (hostFs guestFsAfter : FsState) (mounts : List SandboxMount) : FsState :=
  fun rawHostPath =>
    match parseCleanAbsSegs rawHostPath with
    | none => hostFs rawHostPath
    | some hSegs => mounts.foldl (applyMountWriteBack mounts guestFsAfter hSegs) (hostFs rawHostPath)

/-- Return `true` iff any `.readWrite` mount in `mounts` has a canonical `hostPath` prefix covering `rawHostPath`. -/
def isCoveredByReadWrite (mounts : List SandboxMount) (rawHostPath : String) : Bool :=
  match parseCleanAbsSegs rawHostPath with
  | none => false
  | some hSegs => mounts.any (mountCoversHostSegs hSegs)

/-- Merge post-run guest non-filesystem state back into the host, keeping `env`, `processes`, `orphanCount = 0`, and closed `network` isolated. -/
def applyNonFsWriteBack (hostNonFs guestNonFsAfter : NonFsState) (net : NetworkMode) : NonFsState :=
  { env := hostNonFs.env
    processes := hostNonFs.processes
    network := match net with | .closed => hostNonFs.network | .open => guestNonFsAfter.network
    orphanCount := 0 }

/-- Commit permitted filesystem and non-filesystem effects of a guest run back into `HostWorld`. -/
def commitGuestState (s : HostWorld) (valid : ValidBoxSpec)
    (guestFsAfter : FsState) (guestNonFsAfter : NonFsState) : HostWorld :=
  { s with
    fs := applyWriteBack s.fs guestFsAfter valid.mounts.toList
    nonFs := applyNonFsWriteBack s.nonFs guestNonFsAfter valid.network }

/-- Proposition holding iff combined `stdout` and `stderr` bytes satisfy `maxOutputBytes`. -/
def withinOutputCap (maxOutputBytes : Option Nat) (stdout stderr : ByteArray) : Prop :=
  match maxOutputBytes with
  | none => True
  | some cap => stdout.size + stderr.size ≤ cap

/-- Allowed outcomes for executing `s.guest` on a capable host with validated specification `valid`. -/
def allowedGuestRun (s : HostWorld) (valid : ValidBoxSpec)
    (out : Except SandboxError SandboxResult) (s' : HostWorld) : Prop :=
  let (rawOutcome, rawStdout, rawStderr, rawFsAfter, rawNonFsAfter) :=
    s.guest (projectGuestInput s valid)
  (withinOutputCap valid.maxOutputBytes rawStdout rawStderr ∧
    out = .ok { outcome := rawOutcome, stdout := rawStdout, stderr := rawStderr } ∧
    s' = commitGuestState s valid rawFsAfter rawNonFsAfter) ∨
  (∃ cap res midFs midNonFs,
    valid.maxOutputBytes = some cap ∧
    rawStdout.size + rawStderr.size > cap ∧
    out = .ok res ∧
    res.outcome = .outputLimitExceeded ∧
    res.stdout.size + res.stderr.size ≤ cap ∧
    s' = commitGuestState s valid midFs midNonFs) ∨
  (∃ res midFs midNonFs,
    s.allowTimeout = true ∧
    valid.timeoutMs.isSome ∧
    out = .ok res ∧
    res.outcome = .timedOut ∧
    withinOutputCap valid.maxOutputBytes res.stdout res.stderr ∧
    s' = commitGuestState s valid midFs midNonFs)

/-- Relational specification for `ProcessSandbox.run` on world `s` and input `spec`. -/
def allowedRun (s : HostWorld) (spec : BoxSpec)
    (out : Except SandboxError SandboxResult) (s' : HostWorld) : Prop :=
  match validateSpecPure spec with
  | .error _ => ∃ e, out = .error e ∧ e.kind = .invalidInput ∧ !e.message.isEmpty ∧ s' = s
  | .ok valid =>
    if !s.available then
      ∃ e, out = .error e ∧ e.kind = .unavailable ∧ !e.message.isEmpty ∧ s' = s
    else
      match s.hostError valid with
      | some k =>
        if isHostErrorKind k then
          ∃ e, out = .error e ∧ e.kind = k ∧ !e.message.isEmpty ∧ s' = s
        else allowedGuestRun s valid out s'
      | none => allowedGuestRun s valid out s'

/-- Single-step request union over `HostWorld` covering all public operations of `ProcessSandboxApiM`. -/
inductive SandboxStepReq where
  /-- Call `validateSpec` on `spec`. -/
  | validateSpec (spec : BoxSpec)
  /-- Call `run` on `spec` against `HostWorld.guest`. -/
  | run (spec : BoxSpec)
  /-- Call `isAvailable`. -/
  | isAvailable
  deriving Inhabited

/-- Single-step response union matching `SandboxStepReq`. -/
inductive SandboxStepOut where
  /-- Response of `validateSpec`. -/
  | validateSpec (res : Except SandboxError ValidBoxSpec)
  /-- Response of `run`. -/
  | run (res : Except SandboxError SandboxResult)
  /-- Response of `isAvailable`. -/
  | isAvailable (ok : Bool)
  deriving Inhabited

/-- Relational transition contract over `HostWorld` across `validateSpec`, `run`, and `isAvailable`. -/
def allowedSandboxStep (s : HostWorld) (req : SandboxStepReq) (out : SandboxStepOut) (s' : HostWorld) : Prop :=
  match req, out with
  | .validateSpec spec, .validateSpec res =>
    s' = s ∧
    match res, validateSpecPure spec with
    | .ok a, .ok b => a = b
    | .error e₁, .error e₂ => e₁.kind = e₂.kind ∧ !e₁.message.isEmpty
    | _, _ => False
  | .run spec, .run res => allowedRun s spec res s'
  | .isAvailable, .isAvailable ok => ok = s.available ∧ s' = s
  | _, _ => False

/-- Pure transition bundle representing any candidate `ProcessSandbox` implementation over `HostWorld`. -/
structure SandboxRunner where
  /-- Validate and normalize an untrusted `BoxSpec`. -/
  validateSpec : BoxSpec → Except SandboxError ValidBoxSpec
  /-- Execute `HostWorld.guest` under `spec` against `HostWorld`, returning `(result, nextWorld)`. -/
  run : HostWorld → BoxSpec → Except SandboxError SandboxResult × HostWorld
  /-- Probe whether `HostWorld` supports sandboxed execution. -/
  isAvailable : HostWorld → Bool

/-- Comprehensive contract requiring `runner` to satisfy `allowedSandboxStep` across every `HostWorld` and `BoxSpec`. -/
def obeys_sandbox_model (runner : SandboxRunner) : Prop :=
  (∀ (s : HostWorld) (spec : BoxSpec),
    allowedSandboxStep s (.validateSpec spec) (.validateSpec (runner.validateSpec spec)) s) ∧
  (∀ (s : HostWorld) (spec : BoxSpec),
    let r := runner.run s spec
    allowedSandboxStep s (.run spec) (.run r.1) r.2) ∧
  (∀ (s : HostWorld),
    allowedSandboxStep s .isAvailable (.isAvailable (runner.isAvailable s)) s)

/-- Single-step request sum covering all 3 public operations of `ProcessSandboxApiM` for `Core.ObeysStepFrom`. -/
inductive PkgStepReq where
  /-- Pure `api.validateSpec spec`. -/
  | validateSpec (spec : BoxSpec)
  /-- Effectful `api.run spec`. -/
  | run (spec : BoxSpec)
  /-- Effectful `api.isAvailable`. -/
  | isAvailable
  deriving Inhabited

/-- Single-step output sum for `PkgStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive PkgStepOut where
  /-- Validation outcome returned by `validateSpec`. -/
  | validateSpec (res : Except SandboxError ValidBoxSpec)
  /-- Execution outcome returned by `run`. -/
  | run (res : Except SandboxError SandboxResult)
  /-- Boolean probe result returned by `isAvailable`. -/
  | isAvailable (ok : Bool)
  deriving Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `ProcessSandboxApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : ProcessSandboxApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .validateSpec spec => pure (.validateSpec (api.validateSpec spec))
  | .run spec => .run <$> api.run spec
  | .isAvailable => .isAvailable <$> api.isAvailable

/-- Well-formedness guard on `LeanSwe.Process.Model.ProcessModelState` for `Core.ObeysStepFrom`. -/
def processStepWf (s : LeanSwe.Process.Model.ProcessModelState) : Bool :=
  LeanSwe.Process.Model.processStateWf s

/-- Execute one `LeanSwe.Process.Model.PkgStepReq` against `proc : LeanSwe.Process.ProcessApiM (StateM W)`. -/
def execProcessStep {W : Type} (proc : LeanSwe.Process.ProcessApiM (StateM W))
    (req : LeanSwe.Process.Model.PkgStepReq) : StateM W LeanSwe.Process.Model.PkgStepOut :=
  LeanSwe.Process.Model.execPkgStep proc req

/-- Direct `ProcessApiM` single-step contract delegated to `LeanSwe.Process.Model.allowedPkgStep`. -/
def allowedProcessStep (s : LeanSwe.Process.Model.ProcessModelState)
    (req : LeanSwe.Process.Model.PkgStepReq) (out : LeanSwe.Process.Model.PkgStepOut)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  LeanSwe.Process.Model.allowedPkgStep s req out s'

/-- Execute one host path `lstat` pre-check against `fs : LeanSwe.Fs.FsApiM (StateM W)`. -/
def execFsLstatStep {W : Type} (fs : LeanSwe.Fs.FsApiM (StateM W))
    (path : String) : StateM W (Except LeanSwe.Fs.FsError LeanSwe.Fs.FileStat) :=
  fs.lstat path

/-- Handle-preserving host path `lstat` pre-check contract over `ProcessModelState`. -/
def allowedFsLstatStep (s : LeanSwe.Process.Model.ProcessModelState)
    (path : String) (out : Except LeanSwe.Fs.FsError LeanSwe.Fs.FileStat)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  s' = s ∧ processStepWf s = true ∧
  match out with
  | .ok st => (!hasNulChar path.toList && !path.isEmpty) = true ∧ st.mode ≤ 0o7777
  | .error e => !e.message.isEmpty

/-- Handle-conserving `ProcessModelState` transition when `ProcessSandbox` executes up to two `ProcessApiM` calls. -/
def allowedProcessHandleStep (s s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  LeanSwe.Process.Model.processStateWf s = true ∧
  LeanSwe.Process.Model.processStateWf s' = true ∧
  s'.activeHandles = s.activeHandles ∧
  s.nextHandleId ≤ s'.nextHandleId ∧
  s'.nextHandleId ≤ s.nextHandleId + 2

/-- Relational single-step contract for all 3 `ProcessSandboxApiM` operations over `ProcessModelState`. -/
def allowedPkgStep (s : LeanSwe.Process.Model.ProcessModelState)
    (req : PkgStepReq) (out : PkgStepOut)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  match req, out with
  | .validateSpec spec, .validateSpec res =>
    res = validateSpecModel spec ∧ s' = s ∧ processStepWf s = true
  | .isAvailable, .isAvailable _ =>
    allowedProcessHandleStep s s'
  | .run spec, .run res =>
    match validateSpecPure spec with
    | .error eExpected =>
      res = .error eExpected ∧ s' = s ∧ processStepWf s = true
    | .ok valid =>
      allowedProcessHandleStep s s' ∧
      match res with
      | .ok r =>
        withinOutputCap valid.maxOutputBytes r.stdout r.stderr ∧
        (r.outcome = .timedOut → valid.timeoutMs.isSome = true) ∧
        (r.outcome = .outputLimitExceeded → valid.maxOutputBytes.isSome = true)
      | .error e =>
        isHostErrorKind e.kind = true ∧ !e.message.isEmpty
  | _, _ => False

private theorem foldl_applyMountWriteBack_eq (allMounts : List SandboxMount)
    (guestFsAfter : FsState) (hSegs : List String) :
    ∀ (ms : List SandboxMount) (acc : Option ByteArray),
      ms.any (mountCoversHostSegs hSegs) = false →
      ms.foldl (applyMountWriteBack allMounts guestFsAfter hSegs) acc = acc
  | [], _, _ => rfl
  | m :: rest, acc, hAny => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hAny
    have hStep : applyMountWriteBack allMounts guestFsAfter hSegs acc m = acc := by
      cases m with
      | readOnly _ _ | scratch _ => rfl
      | readWrite hp bp =>
        cases hHp : parseCleanAbsSegs hp with
        | none => simp [applyMountWriteBack, hHp]
        | some hpSegs =>
          have hNotPref : hpSegs.isPrefixOf hSegs = false := by
            simpa [mountCoversHostSegs, hHp] using hAny.1
          cases hBp : parseCleanAbsSegs bp <;> simp [applyMountWriteBack, hHp, hBp, hNotPref]
    simpa [List.foldl_cons, hStep] using
      foldl_applyMountWriteBack_eq allMounts guestFsAfter hSegs rest acc hAny.2

/-- Host paths outside every `.readWrite` mount are preserved verbatim by `applyWriteBack`, for every guest output filesystem `guestFsAfter`. -/
theorem applyWriteBack_eq_of_not_readWrite (hostFs guestFsAfter : FsState)
    (mounts : List SandboxMount) (rawHostPath : String)
    (hNotRw : isCoveredByReadWrite mounts rawHostPath = false) :
    applyWriteBack hostFs guestFsAfter mounts rawHostPath = hostFs rawHostPath := by
  unfold applyWriteBack
  unfold isCoveredByReadWrite at hNotRw
  cases hSegs : parseCleanAbsSegs rawHostPath with
  | none => rfl
  | some segs =>
    rw [hSegs] at hNotRw
    exact foldl_applyMountWriteBack_eq mounts guestFsAfter segs mounts (hostFs rawHostPath) hNotRw

end LeanSwe.ProcessSandbox.Model
