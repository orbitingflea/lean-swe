import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.Preset

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup

/-- Top-level host system directories inspected for the immutable OS runtime preset. -/
def presetSystemRoots : Array String :=
  #["/usr", "/bin", "/sbin", "/lib", "/lib64"]

/-- Allowlisted safe `/etc` host entries mirrored read-only into the sandbox when present. -/
def presetEtcAllowlist : Array String :=
  #[
    "/etc/ld.so.cache",
    "/etc/passwd",
    "/etc/group",
    "/etc/nsswitch.conf",
    "/etc/localtime",
    "/etc/os-release",
    "/etc/alternatives",
    "/etc/ssl/certs",
    "/etc/ssl/openssl.cnf"
  ]

/-- Return `true` iff normalized absolute path `p` is strictly nested beneath one of `/usr/`, `/bin/`, `/sbin/`, `/lib/`, or `/lib64/`. -/
def isUnderSystemRootLexical (p : String) : Bool :=
  let cs := p.toList
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any fun pre =>
    let pcs := pre.toList
    pcs.isPrefixOf cs && cs.length > pcs.length

/-- Lexically normalize an absolute path by collapsing redundant `'/'` and `'.'` segments while rejecting relative paths and `'..'`. -/
def normalizeAbsLexical (p : String) : Option String :=
  let cs := p.toList
  if cs.head? != some '/' then
    none
  else
    let rec go (segs : List (List Char)) (accRev : List String) : Option String :=
      match segs with
      | [] =>
        if accRev.isEmpty then some "/"
        else some ("/" ++ String.intercalate "/" accRev.reverse)
      | seg :: rest =>
        if seg.isEmpty || seg == ['.'] then
          go rest accRev
        else if seg == ['.', '.'] then
          none
        else
          go rest (String.ofList seg :: accRev)
    go (splitChar '/' cs) []

/-- Deduplicate a list of strings while preserving first-seen order. -/
def dedupStrings (xs : List String) : Array String :=
  xs.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]

/-- Discover existing `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64` directories and top-level symlinks via `lstat` and `readlink`. -/
def discoverSystemEntries {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Array PresetSystemEntry) := do
  let mut entries : Array PresetSystemEntry := #[]
  for root in presetSystemRoots do
    match ← retryEintr (files.fstatat none root.toUTF8 { symlinkNofollow := true }) eintrFuel with
    | .error _ => pure ()
    | .ok st =>
      if st.kind == .symlink then
        match ← retryEintr (files.readlinkat none root.toUTF8 4096) eintrFuel with
        | .ok tgtBytes =>
          if tgtBytes.size > 0 then
            if let some tgt := String.fromUTF8? tgtBytes then
              entries := entries.push (.topSymlink root tgt)
        | .error _ => pure ()
      else if st.kind == .dir then
        entries := entries.push (.readOnlyDir root)
  return entries

/-- Discover existing allowlisted safe `/etc` entries via `stat`. -/
def discoverEtcPaths {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Array String) := do
  let mut paths : Array String := #[]
  for etcPath in presetEtcAllowlist do
    match ← retryEintr (files.fstatat none etcPath.toUTF8 {}) eintrFuel with
    | .ok _ => paths := paths.push etcPath
    | .error _ => pure ()
  return paths

/-- Filter candidate home paths to unique, normalized, existing host directories strictly nested beneath system preset roots (never touching `/home` autofs). -/
def filterExistingNestedHomes {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (candidates : List (Option String))
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Array String) := do
  let mut kept : List String := []
  for cand? in candidates do
    if let some raw := cand? then
      if let some norm := normalizeAbsLexical raw then
        if isUnderSystemRootLexical norm then
          match ← retryEintr (files.fstatat none norm.toUTF8 {}) eintrFuel with
          | .ok st =>
            if st.kind == .dir then
              kept := kept ++ [norm]
          | .error _ => pure ()
  return dedupStrings kept

/-- Discover nested host `$HOME` and `getpwuid(getuid()).pw_dir` directories requiring read-only empty `tmpfs` masks. -/
def discoverExcludedHomes {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd)
    (proc : LinuxSyscall.Process.ProcessOpsM m fd)
    (passwd : Passwd.PasswdOpsM m)
    (getHomeEnv : m (Option String))
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Array String) := do
  let homeEnv? ← getHomeEnv
  let pwDir? ← do
    match ← proc.getuid with
    | .error _ => pure none
    | .ok uid =>
      match ← passwd.getpwuid uid with
      | .ok (some entry) => pure entry.homeDirUtf8?
      | _ => pure none
  filterExistingNestedHomes files [homeEnv?, pwDir?] eintrFuel

/-- Discover the complete `HostRuntimePreset` for the current Linux host. -/
def discoverHostPresetM {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd)
    (proc : LinuxSyscall.Process.ProcessOpsM m fd)
    (passwd : Passwd.PasswdOpsM m)
    (getHomeEnv : m (Option String))
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m HostRuntimePreset := do
  let sysEntries ← discoverSystemEntries files eintrFuel
  let etcPaths ← discoverEtcPaths files eintrFuel
  let excludedHomes ← discoverExcludedHomes files proc passwd getHomeEnv eintrFuel
  return {
    systemEntries := sysEntries
    etcPaths := etcPaths
    excludedHomePaths := excludedHomes
  }

end LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
