import LeanSwe.Base64.Interface
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.PostFork.Types
import LeanSwe.ProcessSandbox.Raw.SysBridge.InitData
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
import LeanSwe.ProcessSandbox.Raw.SysBridge.Preset

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset

/-- Linux `F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE` (`0x0F`) immutability seal mask for `memfd` descriptors. -/
def F_SEAL_ALL : UInt32 := 0x0F

/-- Synthetic `/etc/hosts` content mounted read-only inside every sandbox. -/
def SYNTHETIC_HOSTS_BYTES : ByteArray :=
  "127.0.0.1 localhost\n::1 localhost\n".toUTF8

/-- Upper byte cap (`16 MiB`) enforced when decoding the embedded `leanswe-psandbox-init` helper ELF into a sealed `memfd`. -/
def MAX_INIT_ELF_BYTES : Nat := 16 * 1024 * 1024

/-- Detect native Linux `AUDIT_ARCH_*` constant from `(isLinux, targetTriple)` (`0` on unsupported platforms). -/
def detectHostAuditArch (isLinux : Bool) (target : String) : UInt32 :=
  let cs := target.toList
  if !isLinux then
    0
  else if "x86_64-".toList.isPrefixOf cs then
    0xc000003e
  else if "aarch64-".toList.isPrefixOf cs then
    0xc00000b7
  else
    0

/-- Decode a Base64-encoded `leanswe-psandbox-init` ELF payload, failing closed on invalid Base64, empty output, or payloads exceeding `MAX_INIT_ELF_BYTES`. -/
def decodeEmbeddedInitBytes (b64 : String) : Except String ByteArray :=
  match LeanSwe.Base64.decode b64 with
  | .error err => .error s!"invalid embedded init base64: {err.message}"
  | .ok bytes =>
    if bytes.size == 0 then
      .error "embedded init binary is empty"
    else if bytes.size > MAX_INIT_ELF_BYTES then
      .error "embedded init binary exceeds size cap"
    else
      .ok bytes

/-- Embedded `leanswe-psandbox-init` ELF bytes compiled from `psandbox-init` (decoded once and reused across `preflight` and every `sealPlan`). -/
def embeddedInitBytes : Except String ByteArray :=
  decodeEmbeddedInitBytes LeanSwe.ProcessSandbox.Raw.SysBridge.InitData.initBinaryBase64

/-- Map a path-related Linux `Errno` into `SandboxError` (`.notFound` for `ENOENT`/`ENOTDIR`, `.permissionDenied` for `EACCES`/`EPERM`, `.ioError` otherwise). -/
def mapPathErrnoToSandboxError (path ctx : String) (e : Errno) : SandboxError :=
  let detail := s!"{ctx}: {Errno.name e}"
  if e == Errno.ENOENT || e == Errno.ENOTDIR then
    Internal.mapRawError (.notFound path e detail)
  else if e == Errno.EACCES || e == Errno.EPERM then
    Internal.mapRawError (.permissionDenied (some path) e detail)
  else
    Internal.mapRawError (.ioError (some path) e detail)

/-- Build the `bwrap` argument vector used by `preflight` to probe unprivileged namespace creation. -/
def buildProbeBwrapArgv {fd : Type} (bwrapPath : String)
    (sysEntries : Array PresetSystemEntry) (hasLdCache : Bool) (initFd : fd) :
    Array (PostFork.ArgToken fd) :=
  let base : Array (PostFork.ArgToken fd) := #[
    .lit bwrapPath,
    .lit "--unshare-all",
    .lit "--as-pid-1",
    .lit "--die-with-parent",
    .lit "--clearenv"
  ]
  let withSys := sysEntries.foldl (fun acc e =>
    match e with
    | .topSymlink lp tgt => acc.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
    | .readOnlyDir p => acc.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p)) base
  let withLd :=
    if hasLdCache then
      withSys.push (.lit "--ro-bind") |>.push (.lit "/etc/ld.so.cache") |>.push (.lit "/etc/ld.so.cache")
    else
      withSys
  withLd ++ #[
    .lit "--perms", .lit "0555",
    .lit "--ro-bind-data", .fdDecimal (.handle initFd), .lit "/etc/.leanswe-psandbox-init",
    .lit "--remount-ro", .lit "/",
    .lit "--",
    .lit "/etc/.leanswe-psandbox-init",
    .lit "--probe"
  ]

/-- Build the full `bwrap` argument vector for `spawnBox` from `plan` and the reopened/control descriptor handles. -/
def buildSpawnBwrapArgv {fd : Type} (bwrapPath : String) (plan : CompiledSandboxPlan)
    (initFd hostsFd planFd statusW goR : fd) (ctrlW? : Option fd) :
    Array (PostFork.ArgToken fd) :=
  let base : Array (PostFork.ArgToken fd) := #[
    .lit bwrapPath,
    .lit "--unshare-all",
    .lit "--as-pid-1",
    .lit "--die-with-parent",
    .lit "--clearenv",
    .lit "--proc", .lit "/proc",
    .lit "--dev", .lit "/dev",
    .lit "--perms", .lit "0755",
    .lit "--dir", .lit "/etc"
  ]
  let withDirs := plan.presetSystemEntries.foldl (fun acc e =>
    match e with
    | .readOnlyDir p => acc.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p)
    | .topSymlink _ _ => acc) base
  let withSyms := plan.presetSystemEntries.foldl (fun acc e =>
    match e with
    | .topSymlink lp tgt => acc.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
    | .readOnlyDir _ => acc) withDirs
  let withEtc := plan.presetEtcPaths.foldl (fun acc p =>
    acc.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p)) withSyms
  let withCore := withEtc ++ #[
    .lit "--perms", .lit "0444",
    .lit "--ro-bind-data", .fdDecimal (.handle hostsFd), .lit "/etc/hosts",
    .lit "--perms", .lit "0555",
    .lit "--ro-bind-data", .fdDecimal (.handle initFd), .lit "/etc/.leanswe-psandbox-init"
  ]
  let withMasks := plan.maskedPresetPaths.foldl (fun acc m =>
    acc.push (.lit "--perms") |>.push (.lit "0000")
      |>.push (.lit "--tmpfs") |>.push (.lit m)
      |>.push (.lit "--remount-ro") |>.push (.lit m)) withCore
  let withMounts := plan.userMounts.foldl (fun acc m =>
    match m with
    | .readOnly hp bp => acc.push (.lit "--ro-bind") |>.push (.lit hp) |>.push (.lit bp)
    | .readWrite hp bp => acc.push (.lit "--bind") |>.push (.lit hp) |>.push (.lit bp)
    | .scratch bp => acc.push (.lit "--perms") |>.push (.lit "1777") |>.push (.lit "--tmpfs") |>.push (.lit bp)) withMasks
  let ctrlTok : PostFork.ArgToken fd :=
    match ctrlW? with
    | some h => .fdDecimal (.handle h)
    | none => .lit "-1"
  withMounts ++ #[
    .lit "--remount-ro", .lit "/",
    .lit "--",
    .lit "/etc/.leanswe-psandbox-init",
    .lit "--plan-fd", .fdDecimal (.handle planFd),
    .lit "--status-fd", .fdDecimal (.handle statusW),
    .lit "--go-fd", .fdDecimal (.handle goR),
    .lit "--ctrl-fd", ctrlTok
  ]

/-- Check whether `path` is an executable regular file via `stat` and `access(X_OK)`. -/
def isExecutableRegFile {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (path : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m Bool := do
  let bs := path.toUTF8
  match ← retryEintr (files.fstatat none bs {}) eintrFuel with
  | .error _ => return false
  | .ok st =>
    if st.kind != .reg then
      return false
    match ← retryEintr (files.faccessat none bs { exec := true } {}) eintrFuel with
    | .ok () => return true
    | .error _ => return false

/-- Return `true` iff `s` is a non-empty absolute path segment with no embedded NUL bytes. -/
def isSafeAbsPathDir (s : String) : Bool :=
  match s.toList with
  | '/' :: rest => !rest.contains '\x00'
  | _ => false

/-- Filter candidate `PATH` directory strings to retain only non-empty, NUL-free absolute paths (never `""`, `"."`, or relative directories). -/
def filterAbsoluteBwrapDirs (dirs : List String) : List String :=
  dirs.filter isSafeAbsPathDir

/-- Extract only absolute, non-empty, NUL-free directory entries from raw `PATH` bytes (discarding empty `""`/`"."` segments and all relative paths). -/
def absoluteBwrapPathDirs (rawPath : ByteArray) : List String :=
  filterAbsoluteBwrapDirs ((splitByte (0x3A : UInt8) rawPath).filterMap String.fromUTF8?)

/-- Join an absolute directory `dir` with `"bwrap"`, normalizing `"/"` to `"/bwrap"`. -/
def bwrapCandidatePath (dir : String) : String :=
  if dir == "/" then "/bwrap" else s!"{dir}/bwrap"

/-- Search absolute `dirs` for an executable `bwrap` binary, falling back to `"/usr/bin/bwrap"`. -/
def searchBwrapDirs {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat) : List String → m (Option String)
  | [] => do
    if ← isExecutableRegFile files "/usr/bin/bwrap" eintrFuel then
      return some "/usr/bin/bwrap"
    else
      return none
  | dir :: rest => do
    let cand := bwrapCandidatePath dir
    if ← isExecutableRegFile files cand eintrFuel then
      return some cand
    else
      searchBwrapDirs files eintrFuel rest

/-- Resolve the `bwrap` executable path from `PATH` (defaulting to `"/usr/bin:/bin"`), searching ONLY absolute, non-empty `PATH` segments (never `.` or CWD) with `/usr/bin/bwrap` fallback. -/
def resolveBwrapPath {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (getPathEnv : m (Option ByteArray))
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Option String) := do
  let rawPath := match ← getPathEnv with
    | some bs => if bs.size == 0 then "/usr/bin:/bin".toUTF8 else bs
    | none => "/usr/bin:/bin".toUTF8
  let dirs := absoluteBwrapPathDirs rawPath
  searchBwrapDirs files eintrFuel dirs

/-- Create an anonymous `memfd` (`MFD_CLOEXEC | MFD_ALLOW_SEALING`), write `data`, and apply `F_SEAL_ALL` (`0x0F`). -/
def createSealedMemfd {m : Type → Type} [Monad m] {fd : Type}
    (sandbox : Sandbox.SandboxOpsM m fd) (files : Files.FilesOpsM m fd)
    (name : String) (data : ByteArray)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno fd) := do
  match ← sandbox.memfdCreate name.toUTF8 { cloexec := true, allowSealing := true } with
  | .error e => return .error e
  | .ok h =>
    let wrRes ← if data.size > 0 then writeAllFd files h data 0 eintrFuel else pure (.ok ())
    match wrRes with
    | .error e =>
      Files.closeOpt files (some h)
      return .error e
    | .ok () =>
      match ← retryEintr (files.fcntl h (.addSeals F_SEAL_ALL)) eintrFuel with
      | .error e =>
        Files.closeOpt files (some h)
        return .error e
      | .ok _ => return .ok h

/-- Open 3 `/dev/null` descriptors first so stdio slots `0..2` are guaranteed occupied before allocating any kept `bwrap` descriptor. -/
def openThreeDevNull {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat) :
    m (Except Errno (fd × fd × fd)) := do
  let openOne := retryEintr (files.openat none "/dev/null".toUTF8 { access := .rdwr, cloexec := true } 0) eintrFuel
  match ← openOne with
  | .error e => return .error e
  | .ok d0 =>
    match ← openOne with
    | .error e =>
      Files.closeOpt files (some d0)
      return .error e
    | .ok d1 =>
      match ← openOne with
      | .error e =>
        Files.closeOpt files (some d0)
        Files.closeOpt files (some d1)
        return .error e
      | .ok d2 =>
        return .ok (d0, d1, d2)

/-- Wait for probe child `pid` to exit cleanly with status `0`, retrying `EINTR`. -/
def waitProbeExitZero {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32) :
    Nat → m (Except Errno Unit)
  | 0 => pure (.error Errno.EINTR)
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok (.exited _ 0) => return .ok ()
    | .ok _ => return .error Errno.EPERM
    | .error e =>
      if e == Errno.EINTR then waitProbeExitZero proc pid fuel
      else return .error e

/-- Probe whether unprivileged `bwrap --unshare-all --as-pid-1` can execute `/etc/.leanswe-psandbox-init --probe`. -/
def probeBwrapNamespaces {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd)
    (sandbox : Sandbox.SandboxOpsM m fd)
    (proc : LinuxSyscall.Process.ProcessOpsM m fd)
    (postFork : PostFork.PostForkOpsM m fd)
    (bwrapPath : String) (initBytes : ByteArray)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno Unit) := do
  match ← openThreeDevNull files eintrFuel with
  | .error e => return .error e
  | .ok (d0, d1, d2) =>
    match ← createSealedMemfd sandbox files "leanswe-psandbox-probe" initBytes eintrFuel with
    | .error e =>
      Files.closeOpt files (some d0)
      Files.closeOpt files (some d1)
      Files.closeOpt files (some d2)
      return .error e
    | .ok initMemfd =>
      let initFdRes ← retryEintr (files.reopenReadOnly initMemfd) eintrFuel
      Files.closeOpt files (some initMemfd)
      match initFdRes with
      | .error e =>
        Files.closeOpt files (some d0)
        Files.closeOpt files (some d1)
        Files.closeOpt files (some d2)
        return .error e
      | .ok initFd =>
        let sysEntries ← discoverSystemEntries files eintrFuel
        let hasLdCache ← match ← retryEintr (files.fstatat none "/etc/ld.so.cache".toUTF8 {}) eintrFuel with
          | .ok _ => pure true
          | .error _ => pure false
        let childSpec : PostFork.ChildSpecM fd := {
          path := bwrapPath
          argv := buildProbeBwrapArgv bwrapPath sysEntries hasLdCache initFd
          stdio := .redirect (.handle d0) (.handle d1) (.handle d2) false
          fdPolicy := .closeAllAbove2Except #[.handle initFd]
          processGroup := .newGroup
          sigpipe := .resetDefault
          forkMode := .immortalThread
        }
        let spawnRes ← postFork.spawn childSpec
        Files.closeOpt files (some d0)
        Files.closeOpt files (some d1)
        Files.closeOpt files (some d2)
        Files.closeOpt files (some initFd)
        match spawnRes with
        | .error pfErr =>
          return .error (pfErr.errno.getD Errno.EPERM)
        | .ok child =>
          waitProbeExitZero proc child.pid.toInt32 eintrFuel

/-- Best-effort close every descriptor in `fds`. -/
def closeFdArray {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (fds : Array fd) : m Unit := do
  for h in fds do
    Files.closeOpt files (some h)

/-- Receive exactly `expected` listener descriptors over `ctrlFd` in `<= 32`-FD `SCM_RIGHTS` batches while watching `statusFd` for early init failure. -/
def recvFdsScmLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd)
    (net : Net.NetOpsM m fd)
    (poll : Poll.PollOpsM m fd)
    (ctrlFd statusFd : fd) (expected : Nat) :
    Array fd → Nat → m (Except Errno (Array fd))
  | got, 0 => do
    if got.size == expected then
      return .ok got
    else
      closeFdArray files got
      return .error Errno.EPROTO
  | got, fuel + 1 => do
    if got.size >= expected then
      return .ok got
    match ← poll.ppoll #[(ctrlFd, { pollin := true }), (statusFd, { pollin := true })] none with
    | .error e =>
      if e == Errno.EINTR then
        recvFdsScmLoop files net poll ctrlFd statusFd expected got fuel
      else
        closeFdArray files got
        return .error e
    | .ok revents =>
      let r0 := revents[0]?.getD {}
      let r1 := revents[1]?.getD {}
      if r0.pollin then
        match ← net.recvmsg ctrlFd (UInt32.ofNat Net.MAX_SCM_FDS) with
        | .error e =>
          if e == Errno.EINTR then
            recvFdsScmLoop files net poll ctrlFd statusFd expected got fuel
          else
            closeFdArray files got
            return .error e
        | .ok batch =>
          if batch.isEmpty || got.size + batch.size > expected then
            closeFdArray files batch
            closeFdArray files got
            return .error Errno.EPROTO
          else
            recvFdsScmLoop files net poll ctrlFd statusFd expected (got ++ batch) fuel
      else if r0.pollerr || r0.pollhup || r0.pollnval ||
          r1.pollin || r1.pollhup || r1.pollerr || r1.pollnval then
        closeFdArray files got
        return .error Errno.EPROTO
      else
        recvFdsScmLoop files net poll ctrlFd statusFd expected got fuel

/-- Receive `expected` box listener descriptors via `SCM_RIGHTS` (`recvmsg` + `ppoll`). -/
def recvFdsScm {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd)
    (net : Net.NetOpsM m fd)
    (poll : Poll.PollOpsM m fd)
    (ctrlFd statusFd : fd) (expected : Nat)
    (fuel : Nat := 2048) : m (Except Errno (Array fd)) :=
  recvFdsScmLoop files net poll ctrlFd statusFd expected #[] fuel

/-- Trim trailing `'\n'` and `'\r'` characters from a diagnostic stderr snippet. -/
def trimTrailingNewlines (s : String) : String :=
  let rec go : Nat → String → String
    | 0, cur => cur
    | n + 1, cur =>
      if cur.endsWith "\n" || cur.endsWith "\r" then
        go n (cur.dropEnd 1).toString
      else
        cur
  go s.length s

/-- Non-blocking read of up to `maxBytes` diagnostic bytes from `stderrFd`. -/
def drainStderrSnippetLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (stderrFd : fd) (maxBytes : Nat) :
    Array ByteArray → Nat → Nat → m ByteArray
  | chunks, total, 0 => pure (concatChunks chunks total)
  | chunks, total, fuel + 1 => do
    if total ≥ maxBytes then
      return concatChunks chunks total
    else
      let want := maxBytes - total
      match ← files.read stderrFd (UInt32.ofNat want) with
      | .ok bs =>
        if bs.size == 0 then
          return concatChunks chunks total
        else
          drainStderrSnippetLoop files stderrFd maxBytes (chunks.push bs) (total + bs.size) fuel
      | .error _ =>
        return concatChunks chunks total

/-- Set `stderrFd` non-blocking and capture a short diagnostic snippet for pre-`execvp` error messages. -/
def drainStderrSnippet {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (stderrFd : fd)
    (maxBytes : Nat := 255) (fuel : Nat := 16) : m String := do
  Files.setNonblockingOpt files (some stderrFd)
  let raw ← drainStderrSnippetLoop files stderrFd maxBytes #[] 0 fuel
  return trimTrailingNewlines (String.fromUTF8? raw |>.getD "")

end LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
