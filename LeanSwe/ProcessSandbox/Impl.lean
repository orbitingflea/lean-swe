import LeanSwe.Fs.Types
import LeanSwe.Process.Types
import LeanSwe.ProcessSandbox.Types

namespace LeanSwe.ProcessSandbox.Internal

open LeanSwe.Process (ExecRequest ExecResult ProcessApiM ProcessError)

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

/-- Validate and canonicalize an absolute path string. -/
def normalizeCleanAbsPath (p : String) : Option String :=
  (parseCleanAbsSegs p).map formatAbsSegs

/-- Reserved top-level OS runtime directories that caller mounts may not target or shadow. -/
def reservedSystemTopDirs : List String :=
  ["usr", "bin", "sbin", "lib", "lib64", "etc", "dev", "proc"]

/-- Return `true` iff canonical box target segments equal `"/"` or lie under a reserved OS directory. -/
def isReservedBoxSegs : List String → Bool
  | [] => true
  | top :: _ => reservedSystemTopDirs.contains top

/-- Default `PATH` added to clean-slate `env` whenever `"PATH"` is absent from `BoxSpec.env`. -/
def defaultSandboxPath : String := "/usr/bin:/bin"

/-- Default working directory inside the sandbox whenever `BoxSpec.cwd` is `none`. -/
def defaultSandboxCwd : String := "/tmp"

/-- Return `true` iff `(k, v)` has a non-empty `=`-free NUL-free key and NUL-free value. -/
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

/-- Validate and normalize a single `SandboxMount`. -/
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
  else match mountHostPath? m₁, mountHostPath? m₂ with
    | some hp₁, some hp₂ =>
      match parseCleanAbsSegs hp₁, parseCleanAbsSegs (mountBoxPath m₁),
            parseCleanAbsSegs hp₂, parseCleanAbsSegs (mountBoxPath m₂) with
      | some h₁, some b₁, some h₂, some b₂ =>
        let p₁₂ := h₁.isPrefixOf h₂
        let p₂₁ := h₂.isPrefixOf h₁
        if !(p₁₂ || p₂₁) then false
        else !((p₁₂ && b₂ == b₁ ++ h₂.drop h₁.length) || (p₂₁ && b₁ == b₂ ++ h₁.drop h₂.length))
      | _, _, _, _ => false
    | _, _ => false

/-- Return `true` iff any pair of distinct mounts in `ms` introduces an unshadowed overlapping `.readWrite` `hostPath` alias. -/
def hasUnshadowedRwOverlap : List SandboxMount → Bool
  | [] => false
  | m :: rest => rest.any (hasUnshadowedRwOverlapPair m) || hasUnshadowedRwOverlap rest

/-- Validate and normalize an untrusted `BoxSpec` directly against `Types.lean`. -/
def validateSpec (spec : BoxSpec) : Except SandboxError ValidBoxSpec := do
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

/-- Return the canonical path-segment depth of `m`'s `boxPath`. -/
def mountBoxDepth (m : SandboxMount) : Nat :=
  match parseCleanAbsSegs (mountBoxPath m) with
  | some segs => segs.length
  | none => 0

/-- Sort mounts by ascending `boxPath` segment depth so parent mounts precede shadowed child submounts. -/
def sortMountsByDepth (ms : List SandboxMount) : List SandboxMount :=
  ms.mergeSort (fun a b => mountBoxDepth a ≤ mountBoxDepth b)

/-- Return the mount with the longest canonical `boxPath` strictly prefixing `childSegs`. -/
def deepestProperAncestorMount (mounts : List SandboxMount) (childSegs : List String) :
    Option SandboxMount :=
  mounts.foldl (init := (none : Option (Nat × SandboxMount))) (fun best m =>
    match parseCleanAbsSegs (mountBoxPath m) with
    | none => best
    | some pSegs =>
      if pSegs.length < childSegs.length && pSegs.isPrefixOf childSegs then
        match best with
        | none => some (pSegs.length, m)
        | some (bestLen, _) => if pSegs.length ≥ bestLen then some (pSegs.length, m) else best
      else best)
  |>.map Prod.snd

/-- Emit the `bwrap` CLI flags for one normalized `SandboxMount`. -/
def mountFlags : SandboxMount → List String
  | .readOnly hp bp => ["--ro-bind", hp, bp]
  | .readWrite hp bp => ["--bind", hp, bp]
  | .scratch bp => ["--perms", "1777", "--tmpfs", bp]

/-- Emit `--setenv` `bwrap` CLI flags for clean-slate environment pairs. -/
def envFlags : List (String × String) → List String
  | [] => []
  | (k, v) :: rest => "--setenv" :: k :: v :: envFlags rest

/-- Minimal read-only OS runtime binds matching the reserved system top-level directories. -/
def osPresetFlags : List String :=
  ["--ro-bind", "/usr", "/usr", "--ro-bind-try", "/bin", "/bin", "--ro-bind-try", "/sbin", "/sbin",
   "--ro-bind-try", "/lib", "/lib", "--ro-bind-try", "/lib64", "/lib64", "--ro-bind-try", "/etc", "/etc",
   "--proc", "/proc", "--dev", "/dev"]

/-- Emit network-sharing flags for `net` (`["--share-net"]` iff `.open`). -/
def networkFlags : NetworkMode → List String
  | .closed => []
  | .open => ["--share-net"]

/-- Build the `bwrap` argument vector for a validated `ValidBoxSpec`. -/
def mkBwrapArgs (valid : ValidBoxSpec) : Array String :=
  let mountArgs := (sortMountsByDepth valid.mounts.toList).flatMap mountFlags
  (osPresetFlags ++ mountArgs ++ ["--remount-ro", "/", "--unshare-all"] ++
    networkFlags valid.network ++ ["--die-with-parent", "--new-session", "--clearenv"] ++
    envFlags valid.env.toList ++ ["--chdir", valid.cwd, "--", valid.program] ++
    valid.args.toList).toArray

/-- Construct the `LeanSwe.Process.ExecRequest` executing `valid` under `bwrap`. -/
def mkBwrapRequest (valid : ValidBoxSpec) : ExecRequest :=
  { program := "bwrap", args := mkBwrapArgs valid, cwd := none, env := #[], inheritEnv := true,
    stdin := valid.stdin, timeoutMs := valid.timeoutMs, maxOutputBytes := valid.maxOutputBytes }

/-- Construct the lightweight `ExecRequest` probing whether `bwrap` namespaces work on this host. -/
def mkProbeRequest : ExecRequest :=
  { program := "bwrap"
    args := (osPresetFlags ++ ["--perms", "1777", "--tmpfs", "/tmp", "--remount-ro", "/",
      "--unshare-all", "--die-with-parent", "--new-session", "--clearenv",
      "--setenv", "PATH", defaultSandboxPath, "--chdir", defaultSandboxCwd, "--", "/bin/true"]).toArray
    cwd := none, env := #[], inheritEnv := true, stdin := ByteArray.empty,
    timeoutMs := some 5000, maxOutputBytes := some 4096 }

/-- Truncate `(out, err)` so their combined byte length satisfies `cap?`. -/
def truncateToCap (cap? : Option Nat) (out err : ByteArray) : ByteArray × ByteArray :=
  match cap? with
  | none => (out, err)
  | some cap =>
    let out' := if out.size ≤ cap then out else out.extract 0 cap
    let rem := cap - out'.size
    (out', if err.size ≤ rem then err else err.extract 0 rem)

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Map a host `lstat` failure during mount pre-checking into a `SandboxError`. -/
def mapFsPrecheckError (target : String) (e : LeanSwe.Fs.FsError) : SandboxError :=
  let kind : SandboxErrorKind :=
    match e.kind with
    | .notFound | .notADirectory => .notFound
    | .permissionDenied => .permissionDenied
    | _ => .ioError
  { kind, path := some target, message := nonEmptyMsg "mount path unavailable" e.message }

/-- Verify every prefix of `relSegs` under `baseSegs` via `fs.lstat`, refusing symlinks and non-directory intermediates, and return whether the leaf is a directory. -/
def checkNoSymlinkPrefix {m : Type → Type} [Monad m] (fs : LeanSwe.Fs.FsApiM m)
    (baseSegs : List String) : List String → m (Except SandboxError Bool)
  | [] => do
    let p := formatAbsSegs baseSegs
    match ← fs.lstat p with
    | .error e => return .error (mapFsPrecheckError p e)
    | .ok st =>
      if st.kind == .symlink then
        return .error { kind := .permissionDenied, path := some p, message := "mount path refuses symlink" }
      else
        return .ok (st.kind == .dir)
  | [last] => do
    let p := formatAbsSegs (baseSegs ++ [last])
    match ← fs.lstat p with
    | .error e => return .error (mapFsPrecheckError p e)
    | .ok st =>
      if st.kind == .symlink then
        return .error { kind := .permissionDenied, path := some p, message := "mount path refuses symlink" }
      else
        return .ok (st.kind == .dir)
  | seg :: rest => do
    let nextBase := baseSegs ++ [seg]
    let p := formatAbsSegs nextBase
    match ← fs.lstat p with
    | .error e => return .error (mapFsPrecheckError p e)
    | .ok st =>
      if st.kind == .symlink then
        return .error { kind := .permissionDenied, path := some p, message := "mount path refuses symlink" }
      else if st.kind != .dir then
        return .error { kind := .notFound, path := some p, message := "mount path component is not a directory" }
      else
        checkNoSymlinkPrefix fs nextBase rest

/-- Verify one mount's host source path (if any) and nested target path/kind before invoking `bwrap`. -/
def checkOneMountPreconditions {m : Type → Type} [Monad m] (fs : LeanSwe.Fs.FsApiM m)
    (sorted : List SandboxMount) (mnt : SandboxMount) : m (Except SandboxError Unit) := do
  let srcRes ← match mountHostPath? mnt with
    | none => pure (.ok true)
    | some hp => match parseCleanAbsSegs hp with
      | none => pure (.error { kind := .notFound, path := some hp, message := "invalid mount hostPath" })
      | some hpSegs => checkNoSymlinkPrefix fs [] hpSegs
  match srcRes with
  | .error e => return .error e
  | .ok srcIsDir =>
    match parseCleanAbsSegs (mountBoxPath mnt) with
    | none => return .ok ()
    | some cSegs =>
      match deepestProperAncestorMount sorted cSegs with
      | some (.readOnly php pbp) | some (.readWrite php pbp) =>
        match parseCleanAbsSegs php, parseCleanAbsSegs pbp with
        | some phpSegs, some pbpSegs =>
          let rel := cSegs.drop pbpSegs.length
          match ← checkNoSymlinkPrefix fs phpSegs rel with
          | .error e => return .error e
          | .ok dstIsDir =>
            if dstIsDir != srcIsDir then
              return .error { kind := .notFound, path := some (formatAbsSegs (phpSegs ++ rel)), message := "nested mount target kind mismatch" }
            else return .ok ()
        | _, _ => return .ok ()
      | some (.scratch _) | none => return .ok ()

/-- Verify source paths and nested target mountpoints for every mount in `ms`. -/
def checkAllMountsPreconditions {m : Type → Type} [Monad m] (fs : LeanSwe.Fs.FsApiM m)
    (sorted : List SandboxMount) : List SandboxMount → m (Except SandboxError Unit)
  | [] => return .ok ()
  | mnt :: rest => do
    match ← checkOneMountPreconditions fs sorted mnt with
    | .error e => return .error e
    | .ok () => checkAllMountsPreconditions fs sorted rest

/-- Map a `ProcessError` from invoking `bwrap` into `Except SandboxError SandboxResult`. -/
def classifyProcessError (cap? : Option Nat) (pe : ProcessError) : Except SandboxError SandboxResult :=
  let rawOut := pe.stdout.getD ByteArray.empty
  let rawErr := pe.stderr.getD ByteArray.empty
  let (out, err) := truncateToCap cap? rawOut rawErr
  match pe.kind with
  | .timedOut => .ok { outcome := .timedOut, stdout := out, stderr := err }
  | .outputLimitExceeded => .ok { outcome := .outputLimitExceeded, stdout := out, stderr := err }
  | .terminatedBySignal =>
    let code : Int := 128 + pe.signal.getD 9
    let outcome := match cap? with
      | some cap => if rawOut.size + rawErr.size > cap then .outputLimitExceeded else .exited code
      | none => .exited code
    .ok { outcome, stdout := out, stderr := err }
  | .notFound | .permissionDenied =>
    .error { kind := .unavailable, message := nonEmptyMsg "bwrap unavailable on host" pe.message }
  | .invalidInput | .nonZeroExit | .ioError =>
    .error { kind := .ioError, message := nonEmptyMsg "sandbox process execution failed" pe.message }

/-- Map a completed `ExecResult` from `bwrap` into `Except SandboxError SandboxResult`. -/
def classifyExecResult (cap? : Option Nat) (res : ExecResult) : Except SandboxError SandboxResult :=
  match cap? with
  | some cap =>
    if res.stdout.size + res.stderr.size > cap then
      let (out, err) := truncateToCap (some cap) res.stdout res.stderr
      .ok { outcome := .outputLimitExceeded, stdout := out, stderr := err }
    else .ok { outcome := .exited res.exitCode, stdout := res.stdout, stderr := res.stderr }
  | none => .ok { outcome := .exited res.exitCode, stdout := res.stdout, stderr := res.stderr }

/-- Probe whether `bwrap` unprivileged namespaces work on this host via `proc`. -/
def isAvailable {m : Type → Type} [Monad m] (proc : ProcessApiM m) : m Bool := do
  match ← proc.run mkProbeRequest with
  | .ok res => return res.exitCode == 0
  | .error _ => return false

/-- Return `.error .unavailable` when `isAvailable proc` is `false`; otherwise preserve `fallback`. -/
def checkAvailOr {m : Type → Type} [Monad m] (proc : ProcessApiM m)
    (fallback : Except SandboxError SandboxResult) : m (Except SandboxError SandboxResult) := do
  if ← isAvailable proc then
    return fallback
  else
    return .error { kind := .unavailable, message := "sandbox unavailable on host" }

/-- Execute `spec` inside an isolated `bwrap` sandbox via `proc` after checking mount paths via `fs`. -/
def run {m : Type → Type} [Monad m] (proc : ProcessApiM m) (fs : LeanSwe.Fs.FsApiM m)
    (spec : BoxSpec) : m (Except SandboxError SandboxResult) := do
  match validateSpec spec with
  | .error e => return .error e
  | .ok valid =>
    let sorted := sortMountsByDepth valid.mounts.toList
    match ← checkAllMountsPreconditions fs sorted sorted with
    | .error e => return .error e
    | .ok () =>
      match ← proc.run (mkBwrapRequest valid) with
      | .error pe =>
        let res := classifyProcessError valid.maxOutputBytes pe
        if pe.kind == .outputLimitExceeded || pe.kind == .terminatedBySignal || pe.kind == .timedOut then
          checkAvailOr proc res
        else return res
      | .ok er =>
        let res := classifyExecResult valid.maxOutputBytes er
        if er.exitCode != 0 then checkAvailOr proc res else return res

/-- Construct a `ProcessSandboxApiM m` backed by `proc` and `fs`. -/
def mkApiM {m : Type → Type} [Monad m] (proc : ProcessApiM m) (fs : LeanSwe.Fs.FsApiM m) :
    ProcessSandboxApiM m :=
  { validateSpec := validateSpec, run := run proc fs, isAvailable := isAvailable proc }

end LeanSwe.ProcessSandbox.Internal
