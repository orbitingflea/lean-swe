import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.SysBridge.ErrorAndEnv

/-!
POSIX `execvp(3)` `PATH` resolution, working-directory pre-validation, and child `pipe2` +
`PostFork.spawn` launch logic for `LeanSwe.Process.SysBridge`.
-/

namespace LeanSwe.Process.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Search `dirs` for an executable regular file candidate matching POSIX `execvp`. -/
def searchPathDirs {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (eintrFuel : Nat) (sawPerm : Bool) : List String → m (Except ProcessError String)
  | [] =>
    if sawPerm then
      pure (.error (mapRawError (.permissionDenied (some program) Errno.EACCES "permission denied")))
    else
      pure (.error (mapRawError (.executableNotFound program Errno.ENOENT s!"executable not found: {program}")))
  | dir :: rest => do
    let execCand := dir ++ "/" ++ program
    let pathBytes := probePathBytes cwd? dir program
    match ← retryEintr (files.fstatat none pathBytes {}) eintrFuel with
    | .error e =>
      if isPermPathSearchErrno e then
        searchPathDirs files program cwd? eintrFuel true rest
      else if isMissingPathSearchErrno e then
        searchPathDirs files program cwd? eintrFuel sawPerm rest
      else
        pure (.error (mapErrno (some program) "execvp" e))
    | .ok st =>
      if st.kind != .reg then
        searchPathDirs files program cwd? eintrFuel true rest
      else
        match ← retryEintr (files.faccessat none pathBytes { exec := true } { eaccess := true }) eintrFuel with
        | .ok () => pure (.ok execCand)
        | .error e =>
          if isPermPathSearchErrno e then
            searchPathDirs files program cwd? eintrFuel true rest
          else if isMissingPathSearchErrno e then
            searchPathDirs files program cwd? eintrFuel sawPerm rest
          else
            pure (.error (mapErrno (some program) "execvp" e))

/-- Pre-validate optional working directory `cwd?` matching child `chdir(2)` semantics before `PATH` search. -/
def validateWorkingDir {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cwd? : Option String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except ProcessError Unit) :=
  match cwd? with
  | none => pure (.ok ())
  | some cwdDir => do
    if cwdDir.isEmpty then
      return .error (mapErrno (some cwdDir) "chdir" Errno.ENOENT)
    let cwdBytes := cwdDir.toUTF8
    match ← retryEintr (files.fstatat none cwdBytes {}) eintrFuel with
    | .error e => return .error (mapErrno (some cwdDir) "chdir" e)
    | .ok st =>
      if st.kind != .dir then
        return .error (mapErrno (some cwdDir) "chdir" Errno.ENOTDIR)
      match ← retryEintr (files.faccessat none cwdBytes { exec := true } { eaccess := true }) eintrFuel with
      | .error e => return .error (mapErrno (some cwdDir) "chdir" e)
      | .ok () => return .ok ()

/-- Resolve `program` against the effective child `PATH` bytes when `program` contains no `'/'`
    (expanding empty segments such as `""`, `:/usr/bin`, `/usr/bin:`, `a::b` to `"."` per POSIX
    `execvp(3)`). Because `PostFork.ChildSpecM.path` is a UTF-8 `String`, individual non-UTF-8
    `PATH` directory segments are skipped while valid UTF-8 segments continue to be searched. -/
def resolveExecutablePath {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (program : String) (cwd? : Option String)
    (envBytes : Array ByteArray) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except ProcessError String) :=
  if program.toList.contains '/' then
    pure (.ok program)
  else
    let rawPath := (findEnvPathRaw envBytes).getD "/bin:/usr/bin".toUTF8
    let dirs := (splitPosixPathBytes rawPath).filterMap String.fromUTF8?
    searchPathDirs files program cwd? eintrFuel false dirs

/-- Check spawn-time request validity (non-empty `program`, no NUL bytes, valid `env` keys/values). -/
def isInvalidSpawnRequest (req : ExecRequest) : Bool :=
  req.program.isEmpty ||
  hasNul req.program ||
  PostFork.Model.hasEmbeddedNulStr req.program ||
  req.args.toList.any (fun a => hasNul a || PostFork.Model.hasEmbeddedNulStr a) ||
  (match req.cwd with
   | some d => hasNul d || PostFork.Model.hasEmbeddedNulStr d
   | none => false) ||
  req.env.toList.any (fun kv =>
    isInvalidEnvEntry kv ||
    PostFork.Model.hasEmbeddedNulStr kv.1 ||
    match kv.2 with | some v => PostFork.Model.hasEmbeddedNulStr v | none => false)

/-- Map a `PostForkError` from `PostFork.spawn` into `ProcessError` (attributing `.chdir` failures to `req.cwd`). -/
def mapPostForkError (req : ExecRequest) (pfErr : PostFork.PostForkError) : ProcessError :=
  match pfErr.childFailure with
  | some cf =>
    let target :=
      if cf.stage == .chdir && req.cwd.isSome then req.cwd.getD req.program else req.program
    mapErrno (some target) "spawn" cf.errno
  | none =>
    match pfErr.kind with
    | .invalidInput =>
      mapRawError (.invalidArgument (some req.program) (pfErr.errno.getD Errno.EINVAL) pfErr.message)
    | _ =>
      match pfErr.errno with
      | some e => mapErrno (some req.program) "spawn" e
      | none =>
        let mapped := mapRawError (.userError pfErr.message)
        { mapped with program := some req.program }

/-- Read raw ambient `environ(7)` bytes when `inheritEnv = true`, or return `#[]` when `inheritEnv = false`. -/
def readBaseEnv {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (inheritEnv : Bool) : m (Except ProcessError (Array ByteArray)) :=
  if inheritEnv then deps.listAmbientEnv else pure (.ok #[])

/-- OS-only phase of `spawn` (validating `cwd`, resolving `PATH`, allocating pipes, launching via
    `PostFork.spawn`, and validating positive Linux PID/PGID bounds without touching the handle table). -/
def spawnOsPhase {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (eintrFuel : Nat) (req : ExecRequest) :
    m (Except ProcessError (ProcSlotM fd)) := do
  if isInvalidSpawnRequest req then
    return .error (mapRawError (.invalidArgument (some req.program) Errno.EINVAL "invalid process spawn argument"))
  match ← validateWorkingDir deps.files req.cwd eintrFuel with
  | .error cwdErr => return .error cwdErr
  | .ok _ =>
    match ← readBaseEnv deps req.inheritEnv with
    | .error envErr =>
      return .error (ensureNonEmptyMsg "failed to read environment" envErr)
    | .ok baseEnv =>
      let envBytes := mergeRawEnvOverrides baseEnv req.env
      match ← resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel with
      | .error resErr => return .error resErr
      | .ok resolvedPath =>
        if resolvedPath.isEmpty || PostFork.Model.hasEmbeddedNulStr resolvedPath then
          return .error (mapRawError (.invalidArgument (some req.program) Errno.EINVAL "invalid resolved executable path"))
        match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
        | .error e1 => return .error (mapErrno (some req.program) "pipe2" e1)
        | .ok (inR, inW) =>
          match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
          | .error e2 =>
            Files.closeOpt deps.files (some inR)
            Files.closeOpt deps.files (some inW)
            return .error (mapErrno (some req.program) "pipe2" e2)
          | .ok (outR, outW) =>
            match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
            | .error e3 =>
              Files.closeOpt deps.files (some inR)
              Files.closeOpt deps.files (some inW)
              Files.closeOpt deps.files (some outR)
              Files.closeOpt deps.files (some outW)
              return .error (mapErrno (some req.program) "pipe2" e3)
            | .ok (errR, errW) =>
              let childSpec : PostFork.ChildSpecM fd :=
                { path := resolvedPath
                  argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                  cwd := req.cwd
                  env := #[]
                  rawEnv := envBytes
                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                  fdPolicy := .inheritNonCloexec #[]
                  closeFds := #[.handle inW, .handle outR, .handle errR]
                  processGroup := .newGroup
                  sigpipe := .resetDefault
                  forkMode := .direct }
              let spawnRes ← deps.postFork.spawn childSpec
              Files.closeOpt deps.files (some inR)
              Files.closeOpt deps.files (some outW)
              Files.closeOpt deps.files (some errW)
              match spawnRes with
              | .error pfErr =>
                Files.closeOpt deps.files (some inW)
                Files.closeOpt deps.files (some outR)
                Files.closeOpt deps.files (some errR)
                return .error (mapPostForkError req pfErr)
              | .ok child =>
                let rawPgid := child.pgid.getD child.pid
                if child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID then
                  Files.closeOpt deps.files (some inW)
                  Files.closeOpt deps.files (some outR)
                  Files.closeOpt deps.files (some errR)
                  return .error (mapRawError (.userError "spawned child returned out-of-range PID"))
                return .ok
                  { pid := child.pid
                    pgid := rawPgid
                    stdinFd? := some inW
                    stdoutFd? := some outR
                    stderrFd? := some errR
                    waited := false }

/-- Pure capability-parameterized implementation of `RawProcessOpsM.spawn`, delegating OS work to `spawnOsPhase`. -/
def spawnPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat) (req : ExecRequest) : m (Except ProcessError ProcessHandle) := do
  match ← spawnOsPhase deps eintrFuel req with
  | .error err => return .error err
  | .ok slot =>
    let hid ← tbl.insertSlot slot
    return .ok
      { handleId := hid
        pid := Int.ofNat slot.pid.toNat
        pgid := Int.ofNat slot.pgid.toNat }

end LeanSwe.Process.SysBridge
