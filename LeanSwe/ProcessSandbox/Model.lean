import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model.Seccomp

namespace LeanSwe.ProcessSandbox.Model

open LeanSwe.ProcessSandbox

/-- Return `true` iff `cs` contains a NUL character (`Char.ofNat 0`). -/
def hasNulChar : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChar cs

/-- Accumulator helper splitting a `List Char` on `'/'` separators. -/
def splitSlashAux (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: cs =>
    if c == '/' then acc.reverse :: splitSlashAux [] cs
    else splitSlashAux (c :: acc) cs

/-- Split `cs` on `'/'` separators, preserving empty segments. -/
def splitSlashChars (cs : List Char) : List (List Char) :=
  splitSlashAux [] cs

/-- Return `true` iff all elements in `xs` are pairwise distinct under `BEq`. -/
def allDistinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

/-- Deduplicate `xs` keeping the first occurrence of each key `f x`. -/
def dedupByFirst {α β : Type} [BEq β] (f : α → β) : List α → List α :=
  let rec go (seen : List β) : List α → List α
    | [] => []
    | x :: xs =>
      let k := f x
      if seen.contains k then go seen xs else x :: go (k :: seen) xs
  go []

/-- Deduplicate environment `(key, value)` pairs keeping the last occurrence of each key. -/
def dedupEnvPairs : List (String × String) → List (String × String)
  | [] => []
  | kv :: rest =>
    let tail := dedupEnvPairs rest
    if tail.any (fun p => p.1 == kv.1) then tail else kv :: tail

/-- Parse a clean absolute path into canonical segments, rejecting empty, NUL, relative, or `".."` paths. -/
def parseCleanAbsSegs (p : String) : Option (List String) :=
  let cs := p.toList
  if cs.isEmpty || hasNulChar cs || cs.head? != some '/' then
    none
  else
    let rawSegs := splitSlashChars cs.tail
    if rawSegs.any (fun s => s == ['.', '.']) then
      none
    else
      let clean := rawSegs.filterMap fun s =>
        if s.isEmpty || s == ['.'] then none else some (String.ofList s)
      some clean

/-- Format canonical path segments back into a canonical absolute POSIX path string. -/
def formatAbsSegs : List String → String
  | [] => "/"
  | segs => "/" ++ String.intercalate "/" segs

/-- Validate and canonicalize an absolute path string, returning `none` on empty, NUL, relative, or `".."`. -/
def normalizeCleanAbsPath (p : String) : Option String :=
  (parseCleanAbsSegs p).map formatAbsSegs

/-- Parse a clean relative or absolute symlink target into segments without NUL or `".."` components. -/
def parseSafePresetTargetSegs (target : String) : Option (List String) :=
  let cs := target.toList
  if cs.isEmpty || hasNulChar cs then
    none
  else
    let body := if cs.head? == some '/' then cs.tail else cs
    let rawSegs := splitSlashChars body
    if rawSegs.any (fun s => s == ['.', '.']) then
      none
    else
      let clean := rawSegs.filterMap fun s =>
        if s.isEmpty || s == ['.'] then none else some (String.ofList s)
      if clean.isEmpty then none else some clean

/-- Reserved top-level system directories inside every sandbox that user mounts may never shadow or write. -/
def reservedSystemTopDirs : List String :=
  ["usr", "bin", "sbin", "lib", "lib64", "etc", "dev", "proc"]

/-- Return `true` iff canonical box target segments `segs` equal `"/"` or lie at/under a reserved system path. -/
def isReservedBoxSegs : List String → Bool
  | [] => true
  | top :: _ => reservedSystemTopDirs.contains top

/-- Allowlisted top-level host system directories/symlinks permitted in `HostRuntimePreset`. -/
def allowlistedSystemRootPaths : List String :=
  ["/usr", "/bin", "/sbin", "/lib", "/lib64"]

/-- Allowlisted safe `/etc` paths permitted in `HostRuntimePreset`. -/
def allowlistedEtcPaths : List String :=
  [ "/etc/ld.so.cache"
  , "/etc/passwd"
  , "/etc/group"
  , "/etc/nsswitch.conf"
  , "/etc/localtime"
  , "/etc/os-release"
  , "/etc/alternatives"
  , "/etc/ssl/certs"
  , "/etc/ssl/openssl.cnf"
  ]

/-- Minimal safe virtual device nodes exposed under `/dev` inside the box. -/
def safeVirtualDevPaths : List String :=
  ["/dev", "/dev/null", "/dev/zero", "/dev/urandom", "/dev/tty", "/dev/ptmx", "/dev/pts"]

/-- Default `PATH` injected into clean-slate `env` whenever `"PATH"` is absent from `BoxSpec.env`. -/
def defaultSandboxPath : String :=
  "/usr/bin:/bin"

/-- Default working directory inside the box whenever `BoxSpec.cwd` is `none`. -/
def defaultSandboxCwd : String :=
  "/tmp"

/-- Return `true` iff `(k, v)` is a valid POSIX environment variable entry (non-empty `=`-free NUL-free key, NUL-free value). -/
def isValidEnvPair (kv : String × String) : Bool :=
  let kcs := kv.1.toList
  !kcs.isEmpty && !kcs.contains '=' && !hasNulChar kcs && !hasNulChar kv.2.toList

/-- Validate and normalize a single `SandboxMount`, rejecting invalid paths and reserved system box targets. -/
def validateAndNormalizeMount (m : SandboxMount) : Except SandboxError SandboxMount :=
  match m with
  | .readOnly hostPath boxPath =>
    match parseCleanAbsSegs hostPath, parseCleanAbsSegs boxPath with
    | none, _ =>
      .error { kind := .invalidInput, path := some hostPath, message := "invalid mount hostPath" }
    | _, none =>
      .error { kind := .invalidInput, path := some boxPath, message := "invalid mount boxPath" }
    | some hSegs, some bSegs =>
      if isReservedBoxSegs bSegs then
        .error { kind := .invalidInput, path := some boxPath, message := "mount boxPath cannot target or shadow system preset paths" }
      else
        .ok (.readOnly (formatAbsSegs hSegs) (formatAbsSegs bSegs))
  | .readWrite hostPath boxPath =>
    match parseCleanAbsSegs hostPath, parseCleanAbsSegs boxPath with
    | none, _ =>
      .error { kind := .invalidInput, path := some hostPath, message := "invalid mount hostPath" }
    | _, none =>
      .error { kind := .invalidInput, path := some boxPath, message := "invalid mount boxPath" }
    | some hSegs, some bSegs =>
      if isReservedBoxSegs bSegs then
        .error { kind := .invalidInput, path := some boxPath, message := "mount boxPath cannot target or shadow system preset paths" }
      else
        .ok (.readWrite (formatAbsSegs hSegs) (formatAbsSegs bSegs))
  | .scratch boxPath =>
    match parseCleanAbsSegs boxPath with
    | none =>
      .error { kind := .invalidInput, path := some boxPath, message := "invalid scratch mount boxPath" }
    | some bSegs =>
      if isReservedBoxSegs bSegs then
        .error { kind := .invalidInput, path := some boxPath, message := "scratch boxPath cannot target or shadow system preset paths" }
      else
        .ok (.scratch (formatAbsSegs bSegs))

/-- Validate and normalize a list of `SandboxMount` entries in order. -/
def validateMountsList : List SandboxMount → Except SandboxError (List SandboxMount)
  | [] => .ok []
  | m :: rest => do
    let normM ← validateAndNormalizeMount m
    let normRest ← validateMountsList rest
    .ok (normM :: normRest)

/-- Authoritative pure boundary validator turning `BoxSpec` into `ValidBoxSpec` or `.invalidInput`. -/
def validateSpecPure (spec : BoxSpec) : Except SandboxError ValidBoxSpec := do
  if spec.program.isEmpty then
    .error { kind := .invalidInput, message := "program must not be empty" }
  else if hasNulChar spec.program.toList then
    .error { kind := .invalidInput, message := "program must not contain NUL bytes" }
  else if spec.args.toList.any (fun a => hasNulChar a.toList) then
    .error { kind := .invalidInput, message := "args must not contain NUL bytes" }
  else
    let normCwd ←
      match spec.cwd with
      | none => .ok defaultSandboxCwd
      | some d =>
        match normalizeCleanAbsPath d with
        | none => .error { kind := .invalidInput, path := some d, message := "cwd must be a clean absolute box path" }
        | some cleanD => .ok cleanD
    let normMounts ← validateMountsList spec.mounts.toList
    if !allDistinct (normMounts.map mountBoxPath) then
      .error { kind := .invalidInput, message := "duplicate mount boxPath in BoxSpec" }
    else if spec.portForwards.toList.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) then
      .error { kind := .invalidInput, message := "portForwards ports must be in 1..65535" }
    else if !allDistinct (spec.portForwards.toList.map (·.boxPort)) then
      .error { kind := .invalidInput, message := "duplicate boxPort in portForwards" }
    else if !spec.env.toList.all isValidEnvPair then
      .error { kind := .invalidInput, message := "invalid environment variable entry" }
    else if spec.limits.timeoutMs == 0 then
      .error { kind := .invalidInput, message := "limits.timeoutMs must be greater than zero" }
    else if spec.limits.memoryMaxBytes == some 0 then
      .error { kind := .invalidInput, message := "limits.memoryMaxBytes must be greater than zero when set" }
    else if spec.limits.pidsMax == some 0 then
      .error { kind := .invalidInput, message := "limits.pidsMax must be greater than zero when set" }
    else
      let mountsWithDefaultTmp :=
        if normMounts.any (fun m => mountBoxPath m == "/tmp") then normMounts
        else .scratch "/tmp" :: normMounts
      let deduped := dedupEnvPairs spec.env.toList
      let cleanEnv :=
        if deduped.any (fun kv => kv.1 == "PATH") then deduped
        else ("PATH", defaultSandboxPath) :: deduped
      .ok
        { program := spec.program
          args := spec.args
          cwd := normCwd
          stdin := spec.stdin
          mounts := mountsWithDefaultTmp.toArray
          allowBoxLocalhost := spec.allowBoxLocalhost
          portForwards := spec.portForwards
          env := cleanEnv.toArray
          limits := spec.limits }

/-- Return the canonical segment depth of `mountBoxPath m`. -/
def mountBoxDepth (m : SandboxMount) : Nat :=
  match parseCleanAbsSegs (mountBoxPath m) with
  | some segs => segs.length
  | none => 0

/-- Sanitize a `PresetSystemEntry`, accepting only allowlisted `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64` entries. -/
def sanitizePresetSystemEntry (e : PresetSystemEntry) : Option PresetSystemEntry :=
  match e with
  | .readOnlyDir path =>
    match normalizeCleanAbsPath path with
    | some cleanP =>
      if allowlistedSystemRootPaths.contains cleanP then some (.readOnlyDir cleanP) else none
    | none => none
  | .topSymlink linkPath target =>
    match normalizeCleanAbsPath linkPath, parseSafePresetTargetSegs target with
    | some cleanLink, some targetSegs =>
      if allowlistedSystemRootPaths.contains cleanLink &&
          allowlistedSystemRootPaths.contains ("/" ++ targetSegs.headD "") then
        some (.topSymlink cleanLink target)
      else
        none
    | _, _ => none

/-- Expand a top-level preset symlink (e.g. `"/bin" -> "usr/bin"`) if `segs` starts at that symlink. -/
def expandPresetTopSymlink (entries : List PresetSystemEntry) (segs : List String) : List String :=
  match segs with
  | [] => []
  | top :: rest =>
    let topPath := "/" ++ top
    match entries.find? (fun e => presetEntryBoxPath e == topPath) with
    | some (.topSymlink _ target) =>
      match parseSafePresetTargetSegs target with
      | some targetSegs => targetSegs ++ rest
      | none => segs
    | _ => segs

/-- Return `true` iff canonical segments `hSegs` are strictly nested inside at least one mounted preset directory `dirSegs`. -/
def isStrictlyNestedInDirs (dirSegList : List (List String)) (hSegs : List String) : Bool :=
  dirSegList.any (fun dSegs => !dSegs.isEmpty && dSegs.isPrefixOf hSegs && decide (dSegs.length < hSegs.length))

/-- Insert `x` into a depth-ordered list keeping earlier elements ahead of equal-depth elements. -/
def insertByDepth {α : Type} (depth : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if depth x ≤ depth y then x :: y :: ys
    else y :: insertByDepth depth x ys

/-- Stable structural insertion sort ordering elements by ascending `depth` (reduces definitionally in the kernel). -/
def sortByDepth {α : Type} (depth : α → Nat) : List α → List α
  | [] => []
  | x :: xs => insertByDepth depth x (sortByDepth depth xs)

/-- Compile a `ValidBoxSpec` and discovered `HostRuntimePreset` into an immutable `CompiledSandboxPlan`. -/
def compilePlan (valid : ValidBoxSpec) (preset : HostRuntimePreset) : CompiledSandboxPlan :=
  let sysEntries :=
    dedupByFirst presetEntryBoxPath
      (preset.systemEntries.toList.filterMap sanitizePresetSystemEntry)
  let etcEntries :=
    dedupByFirst id
      (preset.etcPaths.toList.filterMap fun p =>
        match normalizeCleanAbsPath p with
        | some cleanP => if allowlistedEtcPaths.contains cleanP then some cleanP else none
        | none => none)
  let mountedSysDirSegs :=
    sysEntries.filterMap fun
      | .readOnlyDir p => parseCleanAbsSegs p
      | .topSymlink _ _ => none
  let rawMasks :=
    dedupByFirst id
      (preset.excludedHomePaths.toList.filterMap fun h =>
        match parseCleanAbsSegs h with
        | some rawHSegs =>
          let hSegs := expandPresetTopSymlink sysEntries rawHSegs
          if isStrictlyNestedInDirs mountedSysDirSegs hSegs then
            some (formatAbsSegs hSegs)
          else
            none
        | none => none)
  let orderedMasks :=
    sortByDepth (fun p => ((parseCleanAbsSegs p).getD []).length) rawMasks
  let mountsWithTmp :=
    if valid.mounts.toList.any (fun m => mountBoxPath m == "/tmp") then valid.mounts.toList
    else .scratch "/tmp" :: valid.mounts.toList
  let orderedMounts :=
    sortByDepth mountBoxDepth mountsWithTmp
  { emptyRoot := true
    unshareAllNamespaces := true
    mountFreshProc := true
    mountSafeDev := true
    presetSystemEntries := sysEntries.toArray
    presetEtcPaths := etcEntries.toArray
    maskedPresetPaths := orderedMasks.toArray
    userMounts := orderedMounts.toArray
    directCgroupV2Fs := true
    landlockMinAbi := 4
    allowBoxLocalhost := valid.allowBoxLocalhost
    portForwards := valid.portForwards
    blockUnixSocketAndSmc := true
    allowAnonUnixSocketpair := true
    clone3EnosysFallback := true
    seccompStrictDenylist := true
    noNewPrivs := true
    rlimitCoreZero := true
    subreaperAndPdeathsig := true
    cleanEnv := true
    env := valid.env
    program := valid.program
    args := valid.args
    cwd := valid.cwd
    limits := valid.limits }

/-- Computable invariant checking that a `CompiledSandboxPlan` enforces all mandatory sandbox invariants. -/
def isValidCompiledPlan (plan : CompiledSandboxPlan) : Bool :=
  plan.emptyRoot &&
  plan.unshareAllNamespaces &&
  plan.mountFreshProc &&
  plan.mountSafeDev &&
  plan.directCgroupV2Fs &&
  decide (plan.landlockMinAbi ≥ 4) &&
  plan.blockUnixSocketAndSmc &&
  plan.allowAnonUnixSocketpair &&
  plan.clone3EnosysFallback &&
  plan.seccompStrictDenylist &&
  plan.noNewPrivs &&
  plan.rlimitCoreZero &&
  plan.subreaperAndPdeathsig &&
  plan.cleanEnv &&
  plan.presetSystemEntries.toList.all (fun e => (sanitizePresetSystemEntry e).isSome) &&
  allDistinct (plan.presetSystemEntries.toList.map presetEntryBoxPath) &&
  plan.presetEtcPaths.toList.all (fun p => allowlistedEtcPaths.contains p) &&
  allDistinct plan.presetEtcPaths.toList &&
  plan.maskedPresetPaths.toList.all (fun m =>
    match parseCleanAbsSegs m with
    | some segs => !segs.isEmpty && formatAbsSegs segs == m
    | none => false) &&
  plan.userMounts.toList.all (fun m =>
    match validateAndNormalizeMount m with
    | .ok norm => norm == m
    | .error _ => false) &&
  allDistinct (plan.userMounts.toList.map mountBoxPath) &&
  plan.userMounts.toList.any (fun m => mountBoxPath m == "/tmp") &&
  plan.portForwards.toList.all (fun pf => pf.boxPort != 0 && pf.hostPort != 0) &&
  allDistinct (plan.portForwards.toList.map (·.boxPort)) &&
  plan.env.toList.all isValidEnvPair &&
  plan.env.toList.any (fun kv => kv.1 == "PATH") &&
  decide (plan.limits.timeoutMs > 0) &&
  plan.limits.memoryMaxBytes != some 0 &&
  plan.limits.pidsMax != some 0

/-- Propositional well-formedness invariant on `CompiledSandboxPlan`. -/
def ValidCompiledPlan (plan : CompiledSandboxPlan) : Prop :=
  isValidCompiledPlan plan = true

/-- Privileged and global host kernel state protected by namespaces, capabilities, and `seccomp`. -/
structure HostAdminState where
  /-- Host power/reboot/kexec state counter (`reboot`, `kexec_load`). -/
  powerGeneration : Nat := 0
  /-- Host system clock epoch offset in nanoseconds (`settimeofday`, `clock_settime`, `adjtimex`). -/
  clockOffsetNs : Int := 0
  /-- Loaded host kernel module names (`init_module`, `finit_module`, `delete_module`). -/
  loadedModules : List String := []
  /-- Host mount table and swap generation (`mount`, `umount2`, `pivot_root`, `swapon`, `swapoff`). -/
  hostMountGeneration : Nat := 0
  /-- Host IPC, keyring, BPF, `io_uring`, and Unix-domain socket tokens (`socket(AF_UNIX, ...)`, `AF_SMC`, `bpf`, `io_uring_*`, `keyctl`). -/
  hostIpcTokens : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Persistent host OS state outside the ephemeral sandbox instance. -/
structure HostState where
  /-- Canonical host filesystem mapping canonical absolute host paths (`"/..."`) to file bytes. -/
  hostFs : List (String × ByteArray) := []
  /-- Delivered raw TCP payloads on host `127.0.0.1:hostPort` listeners (`(hostPort, payload)`). -/
  hostPorts : List (UInt16 × ByteArray) := []
  /-- Live host process IDs outside the sandbox (`hostProcs`). -/
  hostProcs : List Nat := []
  /-- Privileged host administrative state (power, clock, modules, mounts, IPC/Unix sockets). -/
  hostAdminState : HostAdminState := {}
  deriving BEq, DecidableEq, Inhabited

instance : Repr HostState where
  reprPrec h _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "hostFs := " ++ repr (h.hostFs.map fun (p, bs) => (p, bs.toList)),
        "hostPorts := " ++ repr (h.hostPorts.map fun (pt, bs) => (pt, bs.toList)),
        "hostProcs := " ++ repr h.hostProcs,
        "hostAdminState := " ++ repr h.hostAdminState
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Ephemeral per-box state on the shared Linux kernel, discarded and reaped on box teardown. -/
structure BoxState where
  /-- In-memory `scratch` (`tmpfs`) files inside the box (`(canonicalBoxPath, bytes)`). -/
  scratchFs : List (String × ByteArray) := []
  /-- Traffic over the box's private isolated `127.0.0.1` loopback (`(boxPort, payload)`). -/
  boxLocalPorts : List (UInt16 × ByteArray) := []
  /-- Combined anonymous and `tmpfs` memory bytes charged to the box's `cgroup v2` (`memory.max`). -/
  boxMemoryBytes : Nat := 0
  /-- Live guest PIDs inside the box's isolated PID namespace and `cgroup v2` (`pids.max`). -/
  boxProcs : List Nat := [1]
  deriving BEq, DecidableEq, Inhabited

instance : Repr BoxState where
  reprPrec b _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "scratchFs := " ++ repr (b.scratchFs.map fun (p, bs) => (p, bs.toList)),
        "boxLocalPorts := " ++ repr (b.boxLocalPorts.map fun (pt, bs) => (pt, bs.toList)),
        "boxMemoryBytes := " ++ repr b.boxMemoryBytes,
        "boxProcs := " ++ repr b.boxProcs
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Combined `(host, box)` world state during execution of a sandboxed command. -/
structure SandboxWorldState where
  /-- Persistent host OS state. -/
  host : HostState := {}
  /-- Ephemeral sandbox instance state. -/
  box : BoxState := {}
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Look up file bytes at canonical path `p` in an association-list filesystem map. -/
def lookupFsBytes (fs : List (String × ByteArray)) (p : String) : Option ByteArray :=
  (fs.find? (fun kv => kv.1 == p)).map (·.2)

/-- Insert or overwrite canonical path `p` with `bytes` in an association-list filesystem map. -/
def putFsBytes (fs : List (String × ByteArray)) (p : String) (bytes : ByteArray) :
    List (String × ByteArray) :=
  if fs.any (fun kv => kv.1 == p) then
    fs.map (fun kv => if kv.1 == p then (p, bytes) else kv)
  else
    (p, bytes) :: fs

/-- Look up file bytes at canonical host path `hp` in `HostState`. -/
def lookupHostFile (h : HostState) (hp : String) : Option ByteArray :=
  lookupFsBytes h.hostFs hp

/-- Return `true` iff canonical host path `hp` lies at or beneath canonical host root `root`. -/
def isHostPathUnderOrEq (root hp : String) : Bool :=
  match parseCleanAbsSegs root, parseCleanAbsSegs hp with
  | some rSegs, some pSegs => rSegs.isPrefixOf pSegs
  | _, _ => false

/-- Return `true` iff canonical host path `hp` is covered by at least one `.readWrite` mount in `mounts`. -/
def isCoveredByReadWriteGrant (mounts : List SandboxMount) (hp : String) : Bool :=
  mounts.any fun
    | .readWrite hostRoot _ => isHostPathUnderOrEq hostRoot hp
    | _ => false

/-- Explicit 3-category shared-kernel classification of a `GuestSyscall` step. -/
inductive SyscallCategory where
  /-- Category 1: blocked by namespaces, empty root, `MS_RDONLY`, Landlock, `seccomp` (`EPERM`/`ENOSYS`), `rlimit`, or `cgroup v2`; fails with zero state change. -/
  | blocked
  /-- Category 2: box-local operation on the shared kernel modifying at most `BoxState` (`st'.host = st.host`). -/
  | boxLocal
  /-- Category 3: explicitly granted host mutation channel (`readWrite` mount within `fileSizeMaxBytes` or `portForwards` TCP relay). -/
  | grantedHostChannel
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Kernel rejection reason returned when a `GuestSyscall` is blocked. -/
inductive SyscallBlockReason where
  /-- Blocked by `seccomp` BPF or capability/namespace boundary (`EPERM` / `EACCES`). -/
  | blockedBySeccompOrNamespace
  /-- `clone3` rejected with `SECCOMP_RET_ERRNO | ENOSYS` so glibc falls back to `clone`. -/
  | clone3FallbackEnosys
  /-- Path is invalid, unmounted under the empty root, a disallowed `/dev` node, or masked `$HOME` (`ENOENT` / `EACCES`). -/
  | unmountedOrMaskedPath
  /-- Attempted write to read-only preset, `.readOnly` mount, `/proc`, or virtual root (`EROFS` / `EACCES`). -/
  | readOnlyFilesystem
  /-- Write exceeded per-process `RLIMIT_FSIZE` (`fileSizeMaxBytes`, `EFBIG`). -/
  | fileSizeLimitExceeded
  /-- Memory allocation or `scratch` `tmpfs` write exceeded whole-box `cgroup v2` `memory.max` (`ENOMEM` / OOM). -/
  | memoryLimitExceeded
  /-- Process `clone` exceeded whole-box `cgroup v2` `pids.max` or reused an active PID (`EAGAIN`). -/
  | pidsLimitExceeded
  /-- Network connect blocked by isolated `net` namespace or Landlock TCP rules (`ENETUNREACH` / `EACCES`). -/
  | networkBlocked
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Resolved mount target inside a `CompiledSandboxPlan` for a canonical box path. -/
inductive ResolvedBoxAccess where
  /-- Virtual empty-root directory `"/"` (read-only). -/
  | virtualRoot
  /-- Box-private `/proc` mount (read-only, box-local). -/
  | virtualProc
  /-- Safe virtual `/dev` node (`/dev/null`, `/dev/zero`, `/dev/urandom`, `/dev/tty`, `/dev/ptmx`, `/dev/pts`). -/
  | virtualSafeDev
  /-- Synthetic box-local read-only `/etc/hosts` (`127.0.0.1 localhost` / `::1 localhost`, never reading host `/etc/hosts`). -/
  | virtualEtcHosts
  /-- Masked preset subpath (e.g. host `$HOME` nested under `/usr`), inaccessible from `HostState.hostFs`. -/
  | maskedPreset
  /-- Immutable read-only OS preset path backed by `hostPath`. -/
  | presetReadOnly (hostPath : String)
  /-- User `.readOnly` mount backed by `hostPath`. -/
  | userReadOnly (hostPath : String)
  /-- User `.readWrite` mount rooted at canonical `hostRootSegs` mapping to canonical `hostPath`. -/
  | userReadWrite (hostRootSegs : List String) (hostPath : String)
  /-- User or default `/tmp` `.scratch` in-memory `tmpfs` mount at canonical `boxPath`. -/
  | userScratch (boxPath : String)
  /-- Unlisted path absent from the empty-root sandbox. -/
  | unmounted
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Select the deepest matching `SandboxMount` in `mounts` whose `boxPath` is a segment prefix of `segs`. -/
def findLongestUserMount (mounts : List SandboxMount) (segs : List String) :
    Option (SandboxMount × List String) :=
  mounts.foldl
    (fun best m =>
      match parseCleanAbsSegs (mountBoxPath m) with
      | some bSegs =>
        if bSegs.isPrefixOf segs then
          match best with
          | none => some (m, bSegs)
          | some (_, prevSegs) =>
            if prevSegs.length ≤ bSegs.length then some (m, bSegs) else best
        else
          best
      | none => best)
    none

/-- Resolve `boxPath` against `plan`'s empty root, virtual `/proc`/`/dev`/`/etc/hosts`, system presets, `$HOME` masks, and `userMounts`. -/
def resolveBoxPath (plan : CompiledSandboxPlan) (boxPath : String) : ResolvedBoxAccess :=
  match parseCleanAbsSegs boxPath with
  | none => .unmounted
  | some [] => .virtualRoot
  | some rawSegs =>
    let segs := expandPresetTopSymlink plan.presetSystemEntries.toList rawSegs
    let canonBox := formatAbsSegs segs
    if segs.head? == some "proc" then
      if plan.mountFreshProc then .virtualProc else .unmounted
    else if segs.head? == some "dev" then
      if plan.mountSafeDev && (safeVirtualDevPaths.contains canonBox || segs.take 2 == ["dev", "pts"]) then
        .virtualSafeDev
      else
        .unmounted
    else if segs == ["etc", "hosts"] then
      if plan.emptyRoot then .virtualEtcHosts else .unmounted
    else if plan.maskedPresetPaths.toList.any (fun mp =>
        match parseCleanAbsSegs mp with
        | some mSegs => !mSegs.isEmpty && mSegs.isPrefixOf segs
        | none => false) then
      .maskedPreset
    else if plan.presetEtcPaths.toList.any (fun ep =>
        match parseCleanAbsSegs ep with
        | some eSegs => !eSegs.isEmpty && eSegs.isPrefixOf segs
        | none => false) then
      .presetReadOnly canonBox
    else if plan.presetSystemEntries.toList.any (fun e =>
        match e with
        | .readOnlyDir dp =>
          match parseCleanAbsSegs dp with
          | some dSegs => !dSegs.isEmpty && dSegs.isPrefixOf segs
          | none => false
        | .topSymlink _ _ => false) then
      .presetReadOnly canonBox
    else
      match findLongestUserMount plan.userMounts.toList segs with
      | none => .unmounted
      | some (m, bSegs) =>
        let relSegs := segs.drop bSegs.length
        match m with
        | .scratch _ => .userScratch canonBox
        | .readOnly hostRoot _ =>
          let hRootSegs := (parseCleanAbsSegs hostRoot).getD []
          .userReadOnly (formatAbsSegs (hRootSegs ++ relSegs))
        | .readWrite hostRoot _ =>
          let hRootSegs := (parseCleanAbsSegs hostRoot).getD []
          .userReadWrite hRootSegs (formatAbsSegs (hRootSegs ++ relSegs))

/-- Classify a `GuestSyscall` in state `st` under `plan` into one of the 3 shared-kernel categories. -/
def classifySyscall (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    SyscallCategory :=
  match sc with
  | .adminOp _ => .blocked
  | .anonUnixSocketpair sockType =>
    match sockType with
    | .stream | .seqpacket => if plan.allowAnonUnixSocketpair then .boxLocal else .blocked
    | .disallowedOther => .blocked
  | .signalHostPid _ => .blocked
  | .clone3Attempt => .blocked
  | .fsRead boxPath =>
    match resolveBoxPath plan boxPath with
    | .virtualRoot | .virtualProc | .virtualSafeDev | .virtualEtcHosts => .boxLocal
    | .presetReadOnly hp | .userReadOnly hp | .userReadWrite _ hp =>
      if (lookupHostFile st.host hp).isSome then .boxLocal else .blocked
    | .userScratch bp =>
      if (lookupFsBytes st.box.scratchFs bp).isSome then .boxLocal else .blocked
    | .maskedPreset | .unmounted => .blocked
  | .fsWrite boxPath data =>
    match resolveBoxPath plan boxPath with
    | .virtualSafeDev =>
      if formatAbsSegs ((parseCleanAbsSegs boxPath).getD []) == "/dev" then .blocked else .boxLocal
    | .userScratch bp =>
      let prevBytes := (lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0
      let newMem := (st.box.boxMemoryBytes - prevBytes) + data.size
      if match plan.limits.fileSizeMaxBytes with | some maxF => decide (data.size > maxF) | none => false then
        .blocked
      else if match plan.limits.memoryMaxBytes with | some maxM => decide (newMem > maxM) | none => false then
        .blocked
      else
        .boxLocal
    | .userReadWrite _ _ =>
      if match plan.limits.fileSizeMaxBytes with | some maxF => decide (data.size > maxF) | none => false then
        .blocked
      else
        .grantedHostChannel
    | .virtualRoot | .virtualProc | .virtualEtcHosts | .presetReadOnly _ | .userReadOnly _ => .blocked
    | .maskedPreset | .unmounted => .blocked
  | .mmapAnon bytes =>
    if match plan.limits.memoryMaxBytes with
        | some maxM => decide (st.box.boxMemoryBytes + bytes > maxM)
        | none => false then
      .blocked
    else
      .boxLocal
  | .cloneProc newBoxPid hasCloneNewFlags =>
    if hasCloneNewFlags || newBoxPid == 0 || st.box.boxProcs.contains newBoxPid then
      .blocked
    else if match plan.limits.pidsMax with
        | some maxP => decide (st.box.boxProcs.length ≥ maxP)
        | none => false then
      .blocked
    else
      .boxLocal
  | .tcpSend destIsLoopback port _ =>
    if !destIsLoopback || port == 0 then
      .blocked
    else
      match plan.portForwards.toList.find? (fun pf => pf.boxPort == port) with
      | some _ => .grantedHostChannel
      | none => if plan.allowBoxLocalhost then .boxLocal else .blocked

/-- Execute one `GuestSyscall` transition against `SandboxWorldState` under `plan`. -/
def stepGuestSyscall (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .adminOp _ => .error .blockedBySeccompOrNamespace
  | .anonUnixSocketpair sockType =>
    match sockType with
    | .stream | .seqpacket =>
      if plan.allowAnonUnixSocketpair then .ok st else .error .blockedBySeccompOrNamespace
    | .disallowedOther => .error .blockedBySeccompOrNamespace
  | .signalHostPid _ => .error .blockedBySeccompOrNamespace
  | .clone3Attempt => .error .clone3FallbackEnosys
  | .fsRead boxPath =>
    match resolveBoxPath plan boxPath with
    | .virtualRoot | .virtualProc | .virtualSafeDev | .virtualEtcHosts => .ok st
    | .presetReadOnly hp | .userReadOnly hp | .userReadWrite _ hp =>
      if (lookupHostFile st.host hp).isSome then .ok st else .error .unmountedOrMaskedPath
    | .userScratch bp =>
      if (lookupFsBytes st.box.scratchFs bp).isSome then .ok st else .error .unmountedOrMaskedPath
    | .maskedPreset | .unmounted => .error .unmountedOrMaskedPath
  | .fsWrite boxPath data =>
    match resolveBoxPath plan boxPath with
    | .virtualSafeDev =>
      if formatAbsSegs ((parseCleanAbsSegs boxPath).getD []) == "/dev" then
        .error .readOnlyFilesystem
      else
        .ok st
    | .userScratch bp =>
      let prevBytes := (lookupFsBytes st.box.scratchFs bp).map ByteArray.size |>.getD 0
      let newMem := (st.box.boxMemoryBytes - prevBytes) + data.size
      if match plan.limits.fileSizeMaxBytes with | some maxF => decide (data.size > maxF) | none => false then
        .error .fileSizeLimitExceeded
      else if match plan.limits.memoryMaxBytes with | some maxM => decide (newMem > maxM) | none => false then
        .error .memoryLimitExceeded
      else
        .ok
          { st with
            box :=
              { st.box with
                scratchFs := putFsBytes st.box.scratchFs bp data
                boxMemoryBytes := newMem } }
    | .userReadWrite _ hp =>
      if match plan.limits.fileSizeMaxBytes with | some maxF => decide (data.size > maxF) | none => false then
        .error .fileSizeLimitExceeded
      else
        .ok
          { st with
            host := { st.host with hostFs := putFsBytes st.host.hostFs hp data } }
    | .virtualRoot | .virtualProc | .virtualEtcHosts | .presetReadOnly _ | .userReadOnly _ =>
      .error .readOnlyFilesystem
    | .maskedPreset | .unmounted =>
      .error .unmountedOrMaskedPath
  | .mmapAnon bytes =>
    if match plan.limits.memoryMaxBytes with
        | some maxM => decide (st.box.boxMemoryBytes + bytes > maxM)
        | none => false then
      .error .memoryLimitExceeded
    else
      .ok { st with box := { st.box with boxMemoryBytes := st.box.boxMemoryBytes + bytes } }
  | .cloneProc newBoxPid hasCloneNewFlags =>
    if hasCloneNewFlags then
      .error .blockedBySeccompOrNamespace
    else if newBoxPid == 0 || st.box.boxProcs.contains newBoxPid then
      .error .pidsLimitExceeded
    else if match plan.limits.pidsMax with
        | some maxP => decide (st.box.boxProcs.length ≥ maxP)
        | none => false then
      .error .pidsLimitExceeded
    else
      .ok { st with box := { st.box with boxProcs := newBoxPid :: st.box.boxProcs } }
  | .tcpSend destIsLoopback port payload =>
    if !destIsLoopback || port == 0 then
      .error .networkBlocked
    else
      match plan.portForwards.toList.find? (fun pf => pf.boxPort == port) with
      | some pf =>
        .ok
          { st with
            host := { st.host with hostPorts := st.host.hostPorts ++ [(pf.hostPort, payload)] } }
      | none =>
        if plan.allowBoxLocalhost then
          .ok
            { st with
              box := { st.box with boxLocalPorts := st.box.boxLocalPorts ++ [(port, payload)] } }
        else
          .error .networkBlocked

/-- Total world-state transition wrapper leaving `st` unchanged when `stepFn` returns `.error`. -/
def stepWorldWith
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState)
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) : SandboxWorldState :=
  match stepFn plan st sc with
  | .ok st' => st'
  | .error _ => st

/-- Fold a `List GuestSyscall` trace from `st₀` using `stepFn` (blocked steps fail without aborting subsequent guest syscalls). -/
def runGuestTraceWith
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState)
    (plan : CompiledSandboxPlan) (st₀ : SandboxWorldState) : List GuestSyscall → SandboxWorldState
  | [] => st₀
  | sc :: rest => runGuestTraceWith stepFn plan (stepWorldWith stepFn plan st₀ sc) rest

/-- Execute a `List GuestSyscall` trace under the canonical `stepGuestSyscall` relation. -/
def runGuestTrace (plan : CompiledSandboxPlan) (st₀ : SandboxWorldState) (trace : List GuestSyscall) :
    SandboxWorldState :=
  runGuestTraceWith stepGuestSyscall plan st₀ trace

/-- Reap all box processes (`subreaper` `kill(-1)` + `killProcessGroup` + `pidfdKill` + `cgroup.kill=1` + `rmdir` + `reapBox`) and discard ephemeral `BoxState`. -/
def reapAndTeardownBox (st : SandboxWorldState) : SandboxWorldState :=
  { host := st.host
    box :=
      { scratchFs := []
        boxLocalPorts := []
        boxMemoryBytes := 0
        boxProcs := [] } }

/-- Parameterized kernel-isolation specification over a candidate `stepFn`. -/
def SpecHostUnchangedOutsideGrantsOn
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState) :
    Prop :=
  (∀ (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall),
    ValidCompiledPlan plan →
    (classifySyscall plan st sc = .blocked →
      (stepFn plan st sc).isOk = false ∧ stepWorldWith stepFn plan st sc = st) ∧
    (classifySyscall plan st sc = .boxLocal →
      ∃ st', stepFn plan st sc = .ok st' ∧ st'.host = st.host)) ∧
  (∀ (plan : CompiledSandboxPlan) (st₀ : SandboxWorldState) (trace : List GuestSyscall),
    ValidCompiledPlan plan →
    let st₁ := runGuestTraceWith stepFn plan st₀ trace
    st₁.host.hostAdminState = st₀.host.hostAdminState ∧
    st₁.host.hostProcs = st₀.host.hostProcs ∧
    (∀ hp : String,
      isCoveredByReadWriteGrant plan.userMounts.toList hp = false →
      lookupHostFile st₁.host hp = lookupHostFile st₀.host hp) ∧
    (∀ maxF : Nat,
      plan.limits.fileSizeMaxBytes = some maxF →
      ∀ (hp : String) (bs : ByteArray),
        lookupHostFile st₀.host hp ≠ some bs →
        lookupHostFile st₁.host hp = some bs →
        bs.size ≤ maxF) ∧
    (∀ port : UInt16,
      (plan.portForwards.toList.map (·.hostPort)).contains port = false →
      st₁.host.hostPorts.filter (fun e => e.1 == port) =
        st₀.host.hostPorts.filter (fun e => e.1 == port)))

/-- Frozen theorem specification: across arbitrary `List GuestSyscall` traces, blocked syscalls leave `(host, box)` unchanged, box-local syscalls satisfy `st'.host = st.host`, and `HostState` never changes outside explicit `readWrite` mounts and `portForwards`. -/
def SpecHostUnchangedOutsideGrants : Prop :=
  SpecHostUnchangedOutsideGrantsOn stepGuestSyscall

/-- Parameterized whole-box `cgroup v2` cap and orphan-free teardown specification over `(stepFn, teardownFn)`. -/
def SpecZeroSurvivingBoxProcsOn
    (stepFn : CompiledSandboxPlan → SandboxWorldState → GuestSyscall → Except SyscallBlockReason SandboxWorldState)
    (teardownFn : SandboxWorldState → SandboxWorldState) : Prop :=
  ∀ (plan : CompiledSandboxPlan) (st₀ : SandboxWorldState) (trace : List GuestSyscall),
    ValidCompiledPlan plan →
    (∀ maxP, plan.limits.pidsMax = some maxP → st₀.box.boxProcs.length ≤ maxP) →
    (∀ maxM, plan.limits.memoryMaxBytes = some maxM → st₀.box.boxMemoryBytes ≤ maxM) →
    let stRun := runGuestTraceWith stepFn plan st₀ trace
    let stEnd := teardownFn stRun
    (∀ maxP, plan.limits.pidsMax = some maxP → stRun.box.boxProcs.length ≤ maxP) ∧
    (∀ maxM, plan.limits.memoryMaxBytes = some maxM → stRun.box.boxMemoryBytes ≤ maxM) ∧
    stEnd.box.boxProcs = [] ∧
    stEnd.box.scratchFs = [] ∧
    stEnd.box.boxLocalPorts = [] ∧
    stEnd.box.boxMemoryBytes = 0 ∧
    stEnd.host = stRun.host

/-- Frozen theorem specification: whole-box `pids.max` and `memory.max` hold throughout execution and zero box processes or scratch resources survive teardown. -/
def SpecZeroSurvivingBoxProcs : Prop :=
  SpecZeroSurvivingBoxProcsOn stepGuestSyscall reapAndTeardownBox

/-- Parameterized plan-compilation soundness specification over `(validateFn, compileFn)`. -/
def SpecCompilePlanSoundOn
    (validateFn : BoxSpec → Except SandboxError ValidBoxSpec)
    (compileFn : ValidBoxSpec → HostRuntimePreset → CompiledSandboxPlan) : Prop :=
  ∀ (spec : BoxSpec) (valid : ValidBoxSpec) (preset : HostRuntimePreset),
    validateFn spec = .ok valid →
    let plan := compileFn valid preset
    ValidCompiledPlan plan ∧
    plan.emptyRoot = true ∧
    plan.directCgroupV2Fs = true ∧
    plan.blockUnixSocketAndSmc = true ∧
    plan.allowAnonUnixSocketpair = true ∧
    plan.clone3EnosysFallback = true ∧
    plan.cleanEnv = true ∧
    (spec.cwd = none → plan.cwd = defaultSandboxCwd) ∧
    plan.userMounts.toList.any (fun m => mountBoxPath m == "/tmp") = true ∧
    (spec.env.toList.any (fun kv => kv.1 == "PATH") = false →
      plan.env.toList.contains ("PATH", defaultSandboxPath) = true) ∧
    (∀ kv ∈ plan.env.toList,
      kv = ("PATH", defaultSandboxPath) ∨ kv ∈ spec.env.toList) ∧
    resolveBoxPath plan "/etc/hosts" = .virtualEtcHosts ∧
    (∀ (h : String) (rawHSegs : List String),
      h ∈ preset.excludedHomePaths.toList →
      parseCleanAbsSegs h = some rawHSegs →
      let hSegs := expandPresetTopSymlink plan.presetSystemEntries.toList rawHSegs
      (∃ sysP ∈ plan.presetSystemEntries.toList,
        ∃ dSegs, sysP = .readOnlyDir (formatAbsSegs dSegs) ∧
          !dSegs.isEmpty ∧ dSegs.isPrefixOf hSegs ∧ dSegs.length < hSegs.length) →
      plan.maskedPresetPaths.toList.contains (formatAbsSegs hSegs) = true ∧
      ∀ (boxP : String) (rawPSegs : List String),
        parseCleanAbsSegs boxP = some rawPSegs →
        hSegs.isPrefixOf (expandPresetTopSymlink plan.presetSystemEntries.toList rawPSegs) = true →
        resolveBoxPath plan boxP = .maskedPreset)

/-- Frozen theorem specification: `validateSpecPure` + `compilePlan` always produce a `ValidCompiledPlan` enforcing empty root, direct `cgroup v2` cgroupfs, default `/tmp` + `cwd = "/tmp"`, allowlisted presets, nested `$HOME` masking, `AF_UNIX` `socket` block with anonymous `socketpair` allowed, `clone3` `ENOSYS` fallback, clean-slate `env` with default `PATH`, and safe mounts/ports. -/
def SpecCompilePlanSound : Prop :=
  SpecCompilePlanSoundOn validateSpecPure compilePlan

end LeanSwe.ProcessSandbox.Model
