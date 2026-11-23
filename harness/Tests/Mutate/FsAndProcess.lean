import Tests.Common
import LeanSwe.Fs.RuntimeTests
import LeanSwe.Process.RuntimeTests
import LeanSwe.Git.RuntimeTests
import LeanSwe.TempDir.RuntimeTests
import LeanSwe.ProcessSandbox.Seccomp.RuntimeTests
import LeanSwe.ProcessSandbox.Raw.RuntimeTests
import LeanSwe.ProcessSandbox.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Net.Interface
import Fuzz.LinuxSyscall.ProcessEnv

namespace Tests.Mutate.FsAndProcess

open LeanSwe
open Tests.Common

private structure GitMutProbeState where
  reqs : Array Git.GitRawRequest := #[]
  envs : Array (Array (String × Option String)) := #[]

private def runGitMutateExtra : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"GIT_MUTATE_EXTRA_FAIL: {label}")
  let mkReq (cwd : Option String) (args : Array String) (stdin : ByteArray := ByteArray.empty) : Git.GitRawRequest :=
    { cwd := cwd, args := args, stdin := stdin }
  let shaA := String.ofList (List.replicate 40 'a')
  let shaB := String.ofList (List.replicate 40 'b')
  let mockOps : Git.RawGitOpsM (StateM GitMutProbeState) :=
    { listEnv := pure (.ok #[("GIT_DIR", "/poison/.git"), ("LANG", "de_DE.UTF-8"), ("PATH", "/usr/bin")])
      execGit := fun env req => do
        modify fun s => { reqs := s.reqs.push req, envs := s.envs.push env }
        if req.args == #["merge-base", shaA, shaB] then
          return .ok { exitCode := 0, stdout := (shaA ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--verify" then
          return .ok { exitCode := 0, stdout := (shaA ++ "\n").toUTF8, stderr := ByteArray.empty }
        else
          return .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := Git.Impl.mkApiM mockOps
  let (cRes, stCommit) := (api.commit "/repo" { message := "# hdr\nbody  \n", allowEmpty := true }).run {}
  checkB "commit ok + sanitized inherited env + exact flags"
    (cRes == .ok { hex := shaA } &&
      stCommit.envs.all (fun e =>
        e.toList.contains ("GIT_DIR", none) &&
        e.toList.contains ("LANG", none) &&
        e.toList.contains ("LC_ALL", some "C") &&
        e.toList.contains ("GIT_LITERAL_PATHSPECS", some "1") &&
        e.toList.contains ("GIT_TERMINAL_PROMPT", some "0") &&
        !e.toList.any (fun (k, v) =>
          k == "GIT_CONFIG_GLOBAL" || k == "GIT_CONFIG_NOSYSTEM" ||
          v == some "protocol.allow" || v == some "user.name" ||
          v == some "user.email" || v == some "core.hooksPath")) &&
      stCommit.reqs[0]? == some
        (mkReq (some "/repo") #["commit", "--no-gpg-sign", "-m", "# hdr\nbody  \n", "--allow-empty"]))
  let (clRes, stClone) :=
    (api.clone "/src" "/dst" { bare := true, singleBranch := true, depth? := some 1, branch? := some "feat" }).run {}
  checkB "clone exact flags"
    (clRes == .ok () &&
      stClone.reqs.back? == some
        (mkReq none #["clone", "--bare", "--single-branch", "--depth", "1", "--branch", "feat", "--", "/src", "/dst"]))
  let (coB, stCoB) := (api.checkout "/repo" (.branch { raw := "feat" }) false).run {}
  let (coR, stCoR) := (api.checkout "/repo" (.ref "feat") false).run {}
  let (swE, stSwE) := (api.switch "/repo" { raw := "feat" } false none false).run {}
  checkB "checkout + switch default flags (no --no-guess)"
    (coB == .ok () && stCoB.reqs.back? == some (mkReq (some "/repo") #["checkout", "feat", "--"]) &&
      coR == .ok () && stCoR.reqs.back? == some (mkReq (some "/repo") #["checkout", "feat", "--"]) &&
      swE == .ok () && stSwE.reqs.back? == some (mkReq (some "/repo") #["switch", "feat"]))
  let (waDef, stWaDef) := (api.worktreeAdd "/repo" { path := "/wt_def" }).run {}
  checkB "worktreeAdd default basename mode"
    (waDef == .ok () && stWaDef.reqs.back? == some (mkReq (some "/repo") #["worktree", "add", "--", "/wt_def"]))
  let (stRes, stStat) := (api.status "/repo").run {}
  let (dfRes, stDiff) := (api.diffNameStatus "/repo" "HEAD" (some "feat") #["p.txt"]).run {}
  checkB "status + diffNameStatus default rename detection and untracked-files=normal"
    (stRes == .ok #[] &&
      stStat.reqs.back? == some
        (mkReq (some "/repo") #["status", "--porcelain=v1", "--untracked-files=normal", "-z"]) &&
      dfRes == .ok #[] &&
      stDiff.reqs.back? == some
        (mkReq (some "/repo") #["diff", "--name-status", "-z", "HEAD", "feat", "--", "p.txt"]))
  let (wtRes, stWt) :=
    (api.withWorktree "/repo" { path := "/wt", detach := true, force := true } (fun p => pure (.ok p))).run {}
  checkB "withWorktree forwards opts.force to worktreeRemove"
    (wtRes == .ok "/wt" &&
      stWt.reqs.back? == some (mkReq (some "/repo") #["worktree", "remove", "--force", "--", "/wt"]))
  let (mbRes, _) := (api.mergeBase? "/repo" { hex := shaA } { hex := shaB }).run {}
  checkB "mergeBase direct git merge-base delegation" (mbRes == .ok (some { hex := shaA }))
  let peTimeout := Git.mapProcessError "fetch" { kind := .timedOut, exitCode := some 124, stderr := some ("t".toUTF8), message := "" }
  let peInv := Git.mapProcessError "fetch" { kind := .invalidInput, message := "bad" }
  let evErr := Git.mapEnvVarsError { kind := .ioError, message := "" }
  checkB "Interface error mapping"
    (peTimeout.kind == .timeout && peTimeout.command == some "fetch" && peTimeout.exitCode == some 124 &&
      peTimeout.stderr == some "t" && !peTimeout.message.isEmpty &&
      peInv.kind == .invalidInput && evErr.kind == .commandFailed && !evErr.message.isEmpty)

/-- Mutation test suite for `LeanSwe.Fs`. -/
def fsSuite : MutateSuite :=
  { name := "Fs", runBase := do Fs.RuntimeTests.runAll; return none }

private def parseProcStatusHexMask (status field : String) : Option Nat := Id.run do
  for line in status.splitOn "\n" do
    if line.startsWith field then
      let hex := (line.drop field.length).trimAscii.toString
      if hex.isEmpty then return none
      let mut acc : Nat := 0
      for c in hex.toList do
        let d? :=
          if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
          else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
          else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
          else none
        match d? with
        | some d => acc := acc * 16 + d
        | none => return none
      return some acc
  return none

/-- Subprocess probe verifying `Process.run` and `LinuxSyscall.Files.write` under `SIGPIPE = SIG_DFL` and pre-pending `SIGPIPE`. -/
def runProcessSigpipeProbe : IO UInt32 := do
  let bit12 : Nat := 1 <<< 12
  if (← Fuzz.LinuxSyscall.ProcessEnv.setSigIgn 13 false) != .ok () then
    IO.eprintln "sigpipe-probe: setSigIgn(SIGPIPE, false) failed"
    return 1
  if (← Fuzz.LinuxSyscall.ProcessEnv.setSigBlock 13 false) != .ok () then
    IO.eprintln "sigpipe-probe: setSigBlock(SIGPIPE, false) failed"
    return 2
  let st0 ← IO.FS.readFile "/proc/thread-self/status"
  match parseProcStatusHexMask st0 "SigIgn:", parseProcStatusHexMask st0 "SigBlk:" with
  | some ign, some blk =>
    if (ign &&& bit12) != 0 || (blk &&& bit12) != 0 then
      IO.eprintln s!"sigpipe-probe: SIGPIPE not SIG_DFL+unblocked (ign={ign}, blk={blk})"
      return 3
  | _, _ =>
    IO.eprintln "sigpipe-probe: failed to parse /proc/thread-self/status"
    return 4
  let bigA := ByteArray.mk (Array.replicate 262144 (0x41 : UInt8))
  match ← Process.run {
    program := "sh"
    args := #["-c", "exec 0<&-; exit 0"]
    stdin := bigA
    timeoutMs := some 5000
  } with
  | .ok r =>
    if r.exitCode != 0 then
      IO.eprintln s!"sigpipe-probe: immediate-close child exitCode={r.exitCode}"
      return 5
  | .error e =>
    IO.eprintln s!"sigpipe-probe: immediate-close Process.run failed: {repr e}"
    return 6
  let bigB := ByteArray.mk (Array.replicate 524288 (0x42 : UInt8))
  match ← Process.run {
    program := "sh"
    args := #["-c", "dd bs=1 count=1 >/dev/null 2>&1; exec 0<&-; exit 0"]
    stdin := bigB
    timeoutMs := some 5000
  } with
  | .ok r =>
    if r.exitCode != 0 then
      IO.eprintln s!"sigpipe-probe: partial-read child exitCode={r.exitCode}"
      return 7
  | .error e =>
    IO.eprintln s!"sigpipe-probe: partial-read Process.run failed: {repr e}"
    return 8
  match ← LinuxSyscall.Process.pipe2 { cloexec := true } with
  | .error e =>
    IO.eprintln s!"sigpipe-probe: pipe2 failed: {e}"
    return 9
  | .ok (rd, wr) =>
    let _ ← LinuxSyscall.Files.close rd
    let w1 ← LinuxSyscall.Files.write wr (ByteArray.mk #[1, 2, 3])
    if w1 != .error LinuxSyscall.Errno.EPIPE then
      let _ ← LinuxSyscall.Files.close wr
      IO.eprintln s!"sigpipe-probe: expected EPIPE from Files.write, got {repr w1}"
      return 10
    let st1 ← IO.FS.readFile "/proc/thread-self/status"
    if (parseProcStatusHexMask st1 "SigPnd:").getD bit12 &&& bit12 != 0 then
      let _ ← LinuxSyscall.Files.close wr
      IO.eprintln "sigpipe-probe: SIGPIPE left pending after unblocked broken-pipe write"
      return 11
    if (← Fuzz.LinuxSyscall.ProcessEnv.setSigBlock 13 true) != .ok () then
      let _ ← LinuxSyscall.Files.close wr
      IO.eprintln "sigpipe-probe: setSigBlock(SIGPIPE, true) failed"
      return 12
    match ← LinuxSyscall.Net.socketpair .unix .stream { cloexec := true } with
    | .error e =>
      let _ ← LinuxSyscall.Files.close wr
      IO.eprintln s!"sigpipe-probe: socketpair failed: {e}"
      return 13
    | .ok (s0, s1) =>
      let _ ← LinuxSyscall.Files.close s1
      let _ ← LinuxSyscall.Net.sendto s0 (ByteArray.mk #[1]) { nosignal := false }
      let _ ← LinuxSyscall.Files.close s0
      let stPre ← IO.FS.readFile "/proc/thread-self/status"
      let prePend := (parseProcStatusHexMask stPre "SigPnd:").getD 0
      if (prePend &&& bit12) == 0 then
        let _ ← LinuxSyscall.Files.close wr
        IO.eprintln "sigpipe-probe: pre-existing thread-pending SIGPIPE not observed"
        return 14
      let w2 ← LinuxSyscall.Files.write wr (ByteArray.mk #[4])
      let stPost ← IO.FS.readFile "/proc/thread-self/status"
      let postPend := (parseProcStatusHexMask stPost "SigPnd:").getD 0
      let _ ← LinuxSyscall.Files.close wr
      let _ ← Fuzz.LinuxSyscall.ProcessEnv.setSigIgn 13 true
      let _ ← Fuzz.LinuxSyscall.ProcessEnv.setSigBlock 13 false
      if w2 != .error LinuxSyscall.Errno.EPIPE then
        IO.eprintln s!"sigpipe-probe: expected EPIPE with pre-pending SIGPIPE, got {repr w2}"
        return 15
      if (postPend &&& bit12) == 0 then
        IO.eprintln "sigpipe-probe: pre-existing thread-pending SIGPIPE was swallowed"
        return 16
  return 0

private def runProcessSigpipeCheck : IO Unit := do
  let selfBin := (← IO.appPath).toString
  match ← Process.run {
    program := selfBin
    args := #["--process-sigpipe-probe"]
    timeoutMs := some 10000
  } with
  | .ok r =>
    if r.exitCode != 0 then
      throw (IO.userError s!"Process SIGPIPE SIG_DFL probe failed (exit={r.exitCode}): {String.fromUTF8! r.stderr}")
  | .error e =>
    throw (IO.userError s!"Process SIGPIPE SIG_DFL probe errored (killed?): {repr e}")

/-- Mutation test suite for `LeanSwe.Process`. -/
def processSuite : MutateSuite :=
  { name := "Process"
    runBase := do Process.RuntimeTests.runAll; return none
    runExtra := runProcessSigpipeCheck }

/-- Mutation test suite for `LeanSwe.Git`. -/
def gitSuite : MutateSuite :=
  { name := "Git"
    runBase := do Git.RuntimeTests.runAll; return none
    runExtra := do Git.RuntimeTests.runMutateExtra; runGitMutateExtra }

/-- Mutation test suite for `LeanSwe.TempDir`. -/
def tempDirSuite : MutateSuite :=
  { name := "TempDir", runBase := do TempDir.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.ProcessSandbox.Seccomp`. -/
def processSandboxSeccompSuite : MutateSuite :=
  { name := "ProcessSandbox.Seccomp", runBase := do ProcessSandbox.Seccomp.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.ProcessSandbox.Raw`. -/
def processSandboxRawSuite : MutateSuite :=
  { name := "ProcessSandbox.Raw", runBase := ProcessSandbox.Raw.RuntimeTests.runAllOutcome }

/-- Mutation test suite for `LeanSwe.ProcessSandbox`. -/
def processSandboxSuite : MutateSuite :=
  { name := "ProcessSandbox", runBase := ProcessSandbox.RuntimeTests.runAllOutcome }

/-- Mutation test suite for `LeanSwe.SlotPool`. -/
def slotPoolSuite : MutateSuite :=
  { name := "SlotPool", runBase := do SlotPool.RuntimeTests.runAll; return none }

end Tests.Mutate.FsAndProcess
