import Tests.Common
import LeanSwe.Fs.Raw.RuntimeTests
import LeanSwe.Fs.RuntimeTests
import LeanSwe.Process.RuntimeTests
import LeanSwe.Git.RuntimeTests
import LeanSwe.TempDir.RuntimeTests
import LeanSwe.ProcessSandbox.Seccomp.RuntimeTests
import LeanSwe.ProcessSandbox.Raw.RuntimeTests
import LeanSwe.ProcessSandbox.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests

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

/-- Mutation test suite for `LeanSwe.Fs.Raw`. -/
def fsRawSuite : MutateSuite :=
  { name := "Fs.Raw", runBase := do Fs.Raw.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Fs`. -/
def fsSuite : MutateSuite :=
  { name := "Fs", runBase := do Fs.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Process`. -/
def processSuite : MutateSuite :=
  { name := "Process", runBase := do Process.RuntimeTests.runAll; return none }

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
