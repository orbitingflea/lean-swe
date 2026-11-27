import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Interface
import LeanSweProofs.PostFork.Model

/-!
Real-OS differential fuzzing suite `Fuzz.PostFork.suite` testing `LeanSwe.PostFork.spawn`
directly against real Linux executables (`/bin/true`, `/bin/false`, `/bin/sh`) and
`LeanSwe.PostFork.Model`, with zero mocks and zero Aeneas dependencies.
-/

namespace Fuzz.PostFork

open Fuzz.Common
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model

private def errKindCtor : PostForkErrorKind → String
  | .invalidInput => "LeanSwe.PostFork.PostForkErrorKind.invalidInput"
  | .sysError => "LeanSwe.PostFork.PostForkErrorKind.sysError"
  | .childFailed => "LeanSwe.PostFork.PostForkErrorKind.childFailed"

private def logSpawnErr {α : Type} (res : Except PostForkError α) : IO Unit := do
  if let .error e := res then
    Fuzz.Common.logErrHit "LeanSwe.PostFork.spawn" (errKindCtor e.kind) "real"

private def safePrintln (s : String) : IO Unit := do
  try IO.println s catch _ => pure ()

private def closeQuiet (fd : RawFd) : IO Unit := do
  let _ ← Files.close fd

private def pipeCloexec (label : String) : IO (RawFd × RawFd) := do
  for _ in List.range 16 do
    match ← Process.pipe2 { cloexec := true } with
    | .ok p => return p
    | .error e =>
      if e == Errno.EINTR then continue
      throw (IO.userError s!"{label}: pipe2 failed errno={e}")
  throw (IO.userError s!"{label}: pipe2 exceeded EINTR retries")

private def writeAll (fd : RawFd) (bs : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  for _ in List.range 256 do
    if off >= bs.size then return
    let slice := bs.extract off bs.size
    match ← Files.write fd slice with
    | .ok n =>
      if n.toNat == 0 then throw (IO.userError "writeAll: zero bytes written")
      off := off + n.toNat
    | .error e =>
      if e == Errno.EINTR then continue
      throw (IO.userError s!"writeAll failed errno={e}")
  if off < bs.size then throw (IO.userError "writeAll exceeded retries")

private def readAll (fd : RawFd) : IO ByteArray := do
  let mut acc := ByteArray.empty
  for _ in List.range 512 do
    match ← Files.read fd 4096 with
    | .ok chunk =>
      if chunk.size == 0 then return acc
      acc := acc ++ chunk
    | .error e =>
      if e == Errno.EINTR then continue
      throw (IO.userError s!"readAll failed errno={e}")
  throw (IO.userError "readAll exceeded retries")

private def reapExitCode (pid : Pid) (label : String) : IO UInt8 := do
  for _ in List.range 64 do
    match ← Process.waitpid pid.toInt32 {} with
    | .ok (.exited p code) =>
      if p != pid then throw (IO.userError s!"{label}: waitpid returned pid={p} expected={pid}")
      return code
    | .ok other =>
      throw (IO.userError s!"{label}: unexpected waitpid status {repr other}")
    | .error e =>
      if e == Errno.EINTR then continue
      throw (IO.userError s!"{label}: waitpid({pid}) failed errno={e}")
  throw (IO.userError s!"{label}: waitpid({pid}) exceeded EINTR retries")

private def assertNoZombies (label : String) : IO Unit := do
  match ← Process.waitpid (-1) { nohang := true } with
  | .error e =>
    if e != Errno.ECHILD && e != Errno.EINTR then
      throw (IO.userError s!"{label}: waitpid(-1, WNOHANG) failed errno={e}")
  | .ok .stillRunning => pure ()
  | .ok leaked =>
    throw (IO.userError s!"{label}: zombie child leaked after failed spawn: {repr leaked}")

private def assertValidSpawned (label : String) (pol : ProcessGroupPolicy) (ch : SpawnedChild) : IO Unit := do
  if ch.pid == 0 || ch.pid > 0x7fffffff then
    throw (IO.userError s!"{label}: out-of-range pid={ch.pid}")
  let expPgid : Option Pid := match pol with | .newGroup => some ch.pid | .inherit => none
  if ch.pgid != expPgid then
    throw (IO.userError s!"{label}: pgid mismatch got={repr ch.pgid} exp={repr expPgid}")

private structure Scratch where
  root : String
  validDir : String
  symDir : String
  validDirReal : String
  missingPath : String
  fileNotDir : String
  nonExecFile : String
  badExecFile : String
  isRoot : Bool

private def initScratch (seed : UInt64) : IO Scratch := do
  let myPid ← match ← Process.getpid with | .ok p => pure p | .error _ => pure 1
  let myUid ← match ← Process.getuid with | .ok u => pure u | .error _ => pure 1000
  let root := s!"/tmp/leanswe-pf-fuzz-{myPid}-{seed}"
  let validDir := s!"{root}/cwd_ok"
  let symDir := s!"{root}/cwd_sym"
  let missingPath := s!"{root}/no_such_entry"
  let fileNotDir := s!"{root}/not_a_dir"
  let nonExecFile := s!"{root}/nonexec"
  let badExecFile := s!"{root}/badexec"
  try IO.FS.removeDirAll root catch _ => pure ()
  IO.FS.createDirAll validDir
  IO.FS.writeBinFile fileNotDir ByteArray.empty
  IO.FS.writeBinFile nonExecFile "echo hi\n".toUTF8
  IO.FS.writeBinFile badExecFile (ByteArray.mk #[0x7f, 0x01, 0x02, 0x03, 0x04])
  let _ ← Files.symlinkat validDir.toUTF8 none symDir.toUTF8
  let _ ← Files.fchmodat none nonExecFile.toUTF8 0o644
  let _ ← Files.fchmodat none badExecFile.toUTF8 0o755
  let validDirReal := (← IO.FS.realPath validDir).toString
  return {
    root, validDir, symDir, validDirReal,
    missingPath, fileNotDir, nonExecFile, badExecFile,
    isRoot := myUid == 0
  }

private def cleanupScratch (sc : Scratch) : IO Unit := do
  try IO.FS.removeDirAll sc.root catch _ => pure ()

private def recHit (ref : IO.Ref CoverageTracker) (b : String) : IO Unit :=
  ref.modify (·.record "spawn" b)

private def runShCapture
    (label script : String) (stdinPayload : ByteArray)
    (cwd? : Option String := none)
    (env : Array (String × String) := #[])
    (rawEnv : Array ByteArray := #[])
    (pg : ProcessGroupPolicy := .newGroup)
    (sig : SigpipePolicy := .resetDefault)
    (extraArgs : Array String := #[])
    (aliasStderrToStdout : Bool := false) : IO (SpawnedChild × UInt8 × String × String) := do
  let (inR, inW) ← pipeCloexec s!"{label}.in"
  let (outR, outW) ← pipeCloexec s!"{label}.out"
  let (errR, errW) ← pipeCloexec s!"{label}.err"
  let spec : ChildSpec := {
    path := "/bin/sh"
    argv := #[.lit "sh", .lit "-c", .lit script, .lit "sh"] ++ extraArgs.map .lit
    cwd := cwd?
    env := env
    rawEnv := rawEnv
    stdio :=
      if aliasStderrToStdout then .redirect (.handle inR) (.handle outW) (.handle outW) true
      else .redirect (.handle inR) (.handle outW) (.handle errW) true
    fdPolicy := .closeAllAbove2Except #[]
    closeFds := #[.handle inW, .handle outR, .handle errR]
    processGroup := pg
    sigpipe := sig
  }
  if !Model.validateSpec spec then
    closeQuiet inR; closeQuiet inW; closeQuiet outR; closeQuiet outW; closeQuiet errR; closeQuiet errW
    throw (IO.userError s!"{label}: Model.validateSpec unexpectedly false")
  let res ← LeanSwe.PostFork.spawn spec
  closeQuiet inR; closeQuiet outW; closeQuiet errW
  match res with
  | .error e =>
    logSpawnErr res
    closeQuiet inW; closeQuiet outR; closeQuiet errR
    throw (IO.userError s!"{label}: spawn failed unexpectedly: {repr e}")
  | .ok ch =>
    assertValidSpawned label pg ch
    if !stdinPayload.isEmpty then writeAll inW stdinPayload
    closeQuiet inW
    let outBs ← readAll outR
    let errBs ← readAll errR
    closeQuiet outR; closeQuiet errR
    let code ← reapExitCode ch.pid label
    return (ch, code, String.fromUTF8! outBs, String.fromUTF8! errBs)

private def checkInvalidSpec (tRef : IO.Ref CoverageTracker) (label : String) (spec : ChildSpec) : IO Unit := do
  if Model.validateSpec spec then
    throw (IO.userError s!"{label}: expected Model.validateSpec=false")
  let res ← LeanSwe.PostFork.spawn spec
  logSpawnErr res
  match res with
  | .error e =>
    if e.kind != .invalidInput || e.errno.isSome || e.childFailure.isSome || e.message.isEmpty then
      throw (IO.userError s!"{label}: malformed invalidInput error: {repr e}")
    recHit tRef "err.invalidInput"
  | .ok ch =>
    let _ ← reapExitCode ch.pid label
    throw (IO.userError s!"{label}: expected invalidInput, got ok pid={ch.pid}")

private def checkChildFailure
    (tRef : IO.Ref CoverageTracker) (label bucketName : String)
    (expStage : FailureStage) (expErrnos : List Errno) (spec : ChildSpec) : IO Unit := do
  if !Model.validateSpec spec then
    throw (IO.userError s!"{label}: expected Model.validateSpec=true")
  let res ← LeanSwe.PostFork.spawn spec
  logSpawnErr res
  match res with
  | .error e =>
    match e.kind, e.childFailure with
    | .childFailed, some cf =>
      if cf.stage != expStage || !expErrnos.contains cf.errno || e.errno != some cf.errno ||
          cf.waitStatus != some (.exited 127) || e.message.isEmpty then
        throw (IO.userError s!"{label}: unexpected childFailure: {repr e}")
      assertNoZombies label
      recHit tRef bucketName
    | _, _ =>
      throw (IO.userError s!"{label}: expected childFailed, got {repr e}")
  | .ok ch =>
    let _ ← reapExitCode ch.pid label
    throw (IO.userError s!"{label}: expected childFailed({repr expStage}), got ok pid={ch.pid}")

private def checkClosedHandleSysErr (tRef : IO.Ref CoverageTracker) (which : Nat) : IO Unit := do
  let (r, w) ← pipeCloexec "closed_handle"
  let (okR, okW) ← pipeCloexec "open_handle"
  closeQuiet r; closeQuiet w
  let stdio := match which % 3 with
    | 0 => StdioPlan.redirect (.handle r) (.handle okW) (.handle okW) true
    | 1 => StdioPlan.redirect (.handle okR) (.handle w) (.handle okW) true
    | _ => StdioPlan.redirect (.handle okR) (.handle okW) (.handle w) true
  let res ← LeanSwe.PostFork.spawn { path := "/bin/true", argv := #[.lit "true"], stdio := stdio }
  closeQuiet okR; closeQuiet okW
  logSpawnErr res
  match res with
  | .error e =>
    if e.kind != .sysError || e.errno != some Errno.EBADF || e.childFailure.isSome || e.message.isEmpty then
      throw (IO.userError s!"closed_handle({which}): expected sysError EBADF, got {repr e}")
    recHit tRef "err.sysError.EBADF"
  | .ok ch =>
    let _ ← reapExitCode ch.pid "closed_handle"
    throw (IO.userError "closed_handle: expected sysError EBADF, got ok")

private def checkClosedRawFdSysErr (tRef : IO.Ref CoverageTracker) : IO Unit := do
  let res ← LeanSwe.PostFork.spawn {
    path := "/bin/true"
    argv := #[.lit "true"]
    stdio := .redirect (.raw 1020) (.raw 1020) (.raw 1020) true
  }
  logSpawnErr res
  match res with
  | .error e =>
    if e.kind != .sysError || e.errno != some Errno.EBADF then
      throw (IO.userError s!"closed_raw_fd: expected sysError EBADF, got {repr e}")
    recHit tRef "err.sysError.EBADF"
  | .ok ch =>
    let _ ← reapExitCode ch.pid "closed_raw_fd"
    throw (IO.userError "closed_raw_fd: expected sysError EBADF, got ok")

private def checkRawStdioPerm (tRef : IO.Ref CoverageTracker) (permIdx : Nat) : IO Unit := do
  let (s0, s1, s2) : Int32 × Int32 × Int32 := match permIdx % 6 with
    | 0 => (0, 2, 1)
    | 1 => (1, 0, 2)
    | 2 => (1, 2, 0)
    | 3 => (2, 0, 1)
    | 4 => (2, 1, 0)
    | _ => (0, 1, 2)
  let res ← LeanSwe.PostFork.spawn {
    path := "/bin/true"
    argv := #[.lit "true"]
    stdio := .redirect (.raw s0) (.raw s1) (.raw s2) false
  }
  match res with
  | .ok ch =>
    let code ← reapExitCode ch.pid "raw_stdio_perm"
    if code != 0 then throw (IO.userError s!"raw_stdio_perm: exit={code}")
    recHit tRef "ok.raw_stdio_swap"
  | .error e =>
    logSpawnErr res
    if e.kind == .sysError && e.errno == some Errno.EBADF then
      -- Closed parent stdio (e.g. `0<&-`) yields EBADF; also verify handle aliasing succeeds.
      let (inR, inW) ← pipeCloexec "raw_perm_fallback_in"
      let (outR, outW) ← pipeCloexec "raw_perm_fallback_out"
      let r2 ← LeanSwe.PostFork.spawn {
        path := "/bin/true"
        argv := #[.lit "true"]
        stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
      }
      closeQuiet inR; closeQuiet inW; closeQuiet outR; closeQuiet outW
      match r2 with
      | .ok ch2 =>
        let code ← reapExitCode ch2.pid "raw_stdio_perm_fallback"
        if code != 0 then throw (IO.userError s!"raw_stdio_perm_fallback: exit={code}")
        recHit tRef "ok.raw_stdio_swap"
      | .error e2 =>
        logSpawnErr r2
        throw (IO.userError s!"raw_stdio_perm_fallback failed: {repr e2}")
    else
      throw (IO.userError s!"raw_stdio_perm({permIdx}): unexpected error {repr e}")

private def checkRichShellEpisode (tRef : IO.Ref CoverageTracker) (sc : Scratch) (kind : Nat) (tag : Nat) : IO Unit := do
  match kind % 6 with
  | 0 =>
    let payload := s!"hello-{tag}\n"
    let (_, code, out, err) ← runShCapture "stdio_redirect"
      "cat; echo \"err-$1\" >&2" payload.toUTF8 (extraArgs := #[s!"{tag}"])
    if code != 0 || out != payload || err != s!"err-{tag}\n" then
      throw (IO.userError s!"stdio_redirect mismatch: code={code} out={repr out} err={repr err}")
    recHit tRef "ok.stdio_redirect"
  | 1 =>
    let (_, code, out, err) ← runShCapture "stdio_alias"
      "echo out1; echo err2 >&2" ByteArray.empty (aliasStderrToStdout := true)
    if code != 0 || out != "out1\nerr2\n" || !err.isEmpty then
      throw (IO.userError s!"stdio_alias mismatch: code={code} out={repr out} err={repr err}")
    recHit tRef "ok.stdio_alias"
  | 2 =>
    -- Open an extra NON-cloexec pipe and confirm the child sees NO inherited fd > 2.
    let (leakR, leakW) ← match ← Process.pipe2 { cloexec := false } with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"close_above2: pipe2 failed errno={e}")
    try
      let (_, code, out, _) ← runShCapture "close_above2"
        "for f in /proc/self/fd/*; do b=${f##*/}; [ \"$b\" -gt 2 ] && echo \"$b\"; done"
        ByteArray.empty
      -- `/bin/sh` itself opens one directory fd while globbing `/proc/self/fd/*`, never both leakR & leakW.
      let leaked := (out.splitOn "\n").filter (!·.isEmpty)
      if code != 0 || leaked.length > 1 then
        throw (IO.userError s!"close_above2: leaked fds > 2: code={code} fds={repr leaked}")
      recHit tRef "ok.close_above2"
    finally
      closeQuiet leakR; closeQuiet leakW
  | 3 =>
    let useNew := tag % 2 == 0
    let pol := if useNew then ProcessGroupPolicy.newGroup else ProcessGroupPolicy.inherit
    let (ch, code, out, _) ← runShCapture "pgrp"
      "read _ _ _ _ pg _ < /proc/self/stat; echo \"$pg\"" ByteArray.empty (pg := pol)
    let gotPg := out.trimAscii.toString
    if code != 0 then throw (IO.userError s!"pgrp: exit={code}")
    if useNew then
      if gotPg != s!"{ch.pid}" then
        throw (IO.userError s!"new_pgrp mismatch: got={gotPg} pid={ch.pid}")
      recHit tRef "ok.new_pgrp"
    else
      if gotPg == s!"{ch.pid}" then
        throw (IO.userError s!"inherit_pgrp unexpectedly changed pgid to child pid={ch.pid}")
      recHit tRef "ok.inherit_pgrp"
  | 4 =>
    let dir := if tag % 2 == 0 then sc.validDir else sc.symDir
    let (_, code, out, _) ← runShCapture "chdir_env"
      "pwd -P; echo \"K=$PF_KEY\"; echo \"R=$PF_RAW\"; echo \"A=$1:$2\""
      ByteArray.empty
      (cwd? := some dir)
      (env := #[("PF_KEY", s!"override-{tag}")])
      (rawEnv := #["PF_KEY=old".toUTF8, s!"PF_RAW=raw-{tag}".toUTF8, "PATH=/bin:/usr/bin".toUTF8])
      (extraArgs := #["alpha", s!"beta-{tag}"])
    let exp := s!"{sc.validDirReal}\nK=override-{tag}\nR=raw-{tag}\nA=alpha:beta-{tag}\n"
    if code != 0 || out != exp then
      throw (IO.userError s!"chdir_env mismatch: code={code} got={repr out} exp={repr exp}")
    recHit tRef "ok.chdir_valid"
    recHit tRef "ok.env_override"
  | _ =>
    -- Verify SIGPIPE (signal 13, bit 12 = 0x1000) is unblocked and not ignored in `/bin/sh` itself (avoiding `awk`, which installs SIG_IGN on SIGPIPE).
    let (_, code, out, _) ← runShCapture "sigpipe_default"
      "while IFS= read -r l; do case \"$l\" in SigBlk:*|SigIgn:*) set -- $l; echo \"$1 $2\";; esac; done < /proc/self/status"
      ByteArray.empty (sig := .resetDefault)
    if code != 0 || out.isEmpty then
      throw (IO.userError s!"sigpipe_default failed: code={code} out={repr out}")
    for ln in out.splitOn "\n" do
      let parts := (ln.splitOn " ").filter (!·.isEmpty)
      if parts.length == 2 then
        let hex := parts[1]!
        let last4 := String.ofList (hex.toList.drop (hex.length - min 4 hex.length))
        let mut val : Nat := 0
        for c in last4.toList do
          let d := if '0' <= c && c <= '9' then c.toNat - '0'.toNat
                   else if 'a' <= c && c <= 'f' then 10 + c.toNat - 'a'.toNat
                   else if 'A' <= c && c <= 'F' then 10 + c.toNat - 'A'.toNat
                   else 0
          val := val * 16 + d
        if (val &&& 0x1000) != 0 then
          throw (IO.userError s!"sigpipe_default: SIGPIPE bit set in {ln}")
    recHit tRef "ok.sigpipe_default"

private def requiredBuckets : Array CoverageBucket := #[
  bucket "spawn" "ok.true",
  bucket "spawn" "ok.false",
  bucket "spawn" "ok.stdio_redirect",
  bucket "spawn" "ok.stdio_alias",
  bucket "spawn" "ok.raw_stdio_swap",
  bucket "spawn" "ok.close_above2",
  bucket "spawn" "ok.new_pgrp",
  bucket "spawn" "ok.inherit_pgrp",
  bucket "spawn" "ok.chdir_valid",
  bucket "spawn" "ok.env_override",
  bucket "spawn" "ok.sigpipe_default",
  bucket "spawn" "err.invalidInput",
  bucket "spawn" "err.sysError.EBADF",
  bucket "spawn" "err.childFailed.chdir.ENOENT",
  bucket "spawn" "err.childFailed.chdir.ENOTDIR",
  bucket "spawn" "err.childFailed.execve.ENOENT",
  bucket "spawn" "err.childFailed.execve.EACCES",
  bucket "spawn" "err.childFailed.execve.ENOEXEC"
]

private def runFuzzStep (tRef : IO.Ref CoverageTracker) (sc : Scratch) (step : Nat) (rng : Rng) : IO Rng := do
  -- Deterministic warmup (steps 0..21) hits all 18 required buckets even on `--steps 22` / `--smoke`.
  if step < 12 then
    checkRichShellEpisode tRef sc step (step / 6)
    return rng
  let (tag, r1) :=
    match step with
    | 12 => (0, rng)
    | 13 => (26, rng)
    | 14 => (40, rng)
    | 15 => (52, rng)
    | 16 => (62, rng)
    | 17 => (72, rng)
    | 18 => (80, rng)
    | 19 => (88, rng)
    | 20 => (88, rng)
    | 21 => (94, rng)
    | _ => rng.nextNat 100
  if tag < 18 then
    -- Pure invalidInput corpus + Model.validateSpec agreement
    let (sub, r2) := r1.nextNat 8
    let badSpec : ChildSpec := match sub with
      | 0 => { path := "", argv := #[] }
      | 1 => { path := "/bin/true\x00x", argv := #[.lit "true"] }
      | 2 => { path := "/bin/true", argv := #[.lit "ok", .lit "bad\x00arg"] }
      | 3 => { path := "/bin/true", argv := #[.lit "true"], cwd := some "/tmp\x00bad" }
      | 4 => { path := "/bin/true", argv := #[.lit "true"], env := #[("", "v")] }
      | 5 => { path := "/bin/true", argv := #[.lit "true"], env := #[("A=B", "v")] }
      | 6 => { path := "/bin/true", argv := #[.lit "true"], rawEnv := #[ByteArray.mk #[65, 61, 0, 66]] }
      | _ => { path := "/bin/true", argv := #[.lit "true"], fdPolicy := .closeAllAbove2Except #[.raw 3] }
    checkInvalidSpec tRef s!"invalid_{sub}" badSpec
    return r2
  else if tag < 26 then
    let (sub, r2) := r1.nextNat 4
    let badFdSpec : ChildSpec := match sub with
      | 0 => { path := "/bin/true", argv := #[.lit "true"], stdio := .redirect (.raw (-1)) (.raw 1) (.raw 2) }
      | 1 => { path := "/bin/true", argv := #[.lit "true"], closeFds := #[.raw (-2)] }
      | 2 => { path := "/bin/true", argv := #[.lit "true"], closeFds := #[.raw 1] }
      | _ => { path := "/bin/true", argv := #[.lit "true"], stdio := .redirect (.raw 4) (.raw 1) (.raw 2), closeFds := #[.raw 4] }
    checkInvalidSpec tRef s!"invalid_fd_{sub}" badFdSpec
    return r2
  else if tag < 40 then
    let (sub, r2) := r1.nextNat 4
    if sub < 3 then checkClosedHandleSysErr tRef sub
    else checkClosedRawFdSysErr tRef
    return r2
  else if tag < 52 then
    checkChildFailure tRef "chdir_enoent" "err.childFailed.chdir.ENOENT" .chdir [Errno.ENOENT]
      { path := "/bin/true", argv := #[.lit "true"], cwd := some (if step % 2 == 0 then sc.missingPath else "") }
    return r1
  else if tag < 62 then
    checkChildFailure tRef "chdir_enotdir" "err.childFailed.chdir.ENOTDIR" .chdir [Errno.ENOTDIR]
      { path := "/bin/true", argv := #[.lit "true"], cwd := some sc.fileNotDir }
    return r1
  else if tag < 72 then
    checkChildFailure tRef "exec_enoent" "err.childFailed.execve.ENOENT" .execve [Errno.ENOENT]
      { path := sc.missingPath, argv := #[.lit "missing"] }
    return r1
  else if tag < 80 then
    let expected := if sc.isRoot then [Errno.EACCES, Errno.ENOEXEC] else [Errno.EACCES]
    checkChildFailure tRef "exec_eacces" "err.childFailed.execve.EACCES" .execve expected
      { path := sc.nonExecFile, argv := #[.lit "nonexec"] }
    return r1
  else if tag < 88 then
    checkChildFailure tRef "exec_enoexec" "err.childFailed.execve.ENOEXEC" .execve [Errno.ENOEXEC]
      { path := sc.badExecFile, argv := #[.lit "badexec"] }
    return r1
  else if tag < 94 then
    let isTrue := step % 2 == 0
    let pol := if step % 3 == 0 then ProcessGroupPolicy.newGroup else ProcessGroupPolicy.inherit
    let bin := if isTrue then "/bin/true" else "/bin/false"
    let res ← LeanSwe.PostFork.spawn { path := bin, argv := #[.lit bin], processGroup := pol }
    match res with
    | .ok ch =>
      assertValidSpawned "true_false" pol ch
      let code ← reapExitCode ch.pid "true_false"
      let expCode : UInt8 := if isTrue then 0 else 1
      if code != expCode then throw (IO.userError s!"{bin}: exit={code} expected={expCode}")
      recHit tRef (if isTrue then "ok.true" else "ok.false")
    | .error e =>
      logSpawnErr res
      throw (IO.userError s!"{bin}: unexpected spawn error {repr e}")
    return r1
  else if tag < 97 then
    checkRawStdioPerm tRef step
    return r1
  else
    let (k, r2) := r1.nextNat 6
    checkRichShellEpisode tRef sc k step
    return r2

private def runPostForkSelfTestShrink (seedVal : UInt64) : IO Unit := do
  let sc ← initScratch (seedVal ^^^ 0x9e3779b97f4a7c15)
  try
    let okSpec : ChildSpec := { path := "/bin/true", argv := #[.lit "/bin/true"] }
    let failSpec : ChildSpec := { path := sc.missingPath, argv := #[.lit "missing", .lit "decoy1", .lit "decoy2"] }
    let trace := (Array.replicate 32 okSpec).set! 19 failSpec
    let failsTrace (cand : Array ChildSpec) : IO Bool :=
      cand.anyM fun sp => do
        match ← LeanSwe.PostFork.spawn sp with
        | .ok ch =>
          let _ ← reapExitCode ch.pid "shrink_ok"
          return false
        | .error e =>
          return e.kind == .childFailed && (e.childFailure.map (·.stage) == some .execve)
    let shrunk ← match ← verifyShrinker failsTrace trace 1 with
      | .error msg => throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: {msg}")
      | .ok s => pure s
    safePrintln s!"POSTFORK_SHRINK_SELFTEST_OK: trace={trace.size}->{shrunk.size}"
  finally
    cleanupScratch sc

private def runPostForkSuite (steps : Nat) (seedVal : UInt64) : IO Unit := do
  let trackerRef ← IO.mkRef CoverageTracker.empty
  let sc ← initScratch seedVal
  try
    let mut rng := Rng.seed seedVal
    for step in List.range steps do
      rng ← runFuzzStep trackerRef sc step rng
    let tracker ← trackerRef.get
    assertCoverage "postfork" tracker requiredBuckets
    safePrintln (tracker.formatReport "postfork")
    safePrintln s!"FUZZ_SUMMARY suite=postfork steps={steps} seed={seedVal} errors=0"
  finally
    cleanupScratch sc

/-- Real-OS differential fuzzing suite for `LeanSwe.PostFork.spawn`. -/
def suite : FuzzSuite := {
  «name» := "postfork"
  description := "Real-OS fuzzer for LeanSwe.PostFork.spawn against Linux binaries and PostFork.Model"
  runSmoke := fun cfg => do
    let actual := max (min cfg.steps 200) 64
    Fuzz.Common.recordSuiteSteps actual
    runPostForkSuite actual cfg.seed
  runFuzz := fun cfg => do
    Fuzz.Common.recordSuiteSteps cfg.steps
    runPostForkSuite cfg.steps cfg.seed
  selfTestShrink := runPostForkSelfTestShrink
}

end Fuzz.PostFork
