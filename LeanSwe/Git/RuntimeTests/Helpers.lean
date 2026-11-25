import Core.Assumptions
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.TempDir.Interface
import LeanSwe.Process.Interface

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Helper `assertTrue`. -/
def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

/-- Helper `assertOk`. -/
def assertOk {α : Type} (res : Except GitError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

/-- Helper `assertErrKind`. -/
def assertErrKind {α : Type} (res : Except GitError α) (expected : GitErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

/-- Helper `withTempDirIO`. -/
def withTempDirIO (f : String → IO Unit) : IO Unit := do
  let res ← LeanSwe.TempDir.withTempDir none "lean-swe-git-rt-" fun dir => do
    f dir
    pure (.ok ())
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"ASSERTION FAILED: withTempDir failed: {e.message}")

/-- Helper `testAuthorOpts`. -/
def testAuthorOpts (msg : String) (allowEmpty : Bool := false) : CommitOptions :=
  { message := msg
    allowEmpty := allowEmpty
    authorName := some "LeanSwe Test"
    authorEmail := some "test@leanswe.invalid" }

/-- Helper `runProcChecked`. -/
def runProcChecked (prog : String) (args : Array String) (cwd? : Option String := none) : IO Unit := do
  let res ← LeanSwe.Process.run { program := prog, args := args, cwd := cwd? }
  match res with
  | .error e => throw (IO.userError s!"ASSERTION FAILED: process {prog} failed: {e.message}")
  | .ok out =>
    if out.exitCode != 0 then
      let errStr := (String.fromUTF8? out.stderr).getD ""
      throw (IO.userError s!"ASSERTION FAILED: process {prog} exited {out.exitCode}: {errStr}")

/-- Helper `runProcRaw`. -/
def runProcRaw (prog : String) (args : Array String) (cwd? : Option String := none) :
    IO LeanSwe.Process.ExecResult := do
  match ← LeanSwe.Process.run { program := prog, args := args, cwd := cwd? } with
  | .error e => throw (IO.userError s!"ASSERTION FAILED: process {prog} failed: {e.message}")
  | .ok out => return out

/-- Helper `repeatCharStr`. -/
def repeatCharStr (c : Char) (n : Nat) : String :=
  String.ofList (List.replicate n c)

/-- Helper `repeatDoubleStr`. -/
def repeatDoubleStr (chunk : String) : Nat → String
  | 0 => chunk
  | k + 1 => repeatDoubleStr (chunk ++ chunk) k

/-- Helper `longInvalidPath`. -/
def longInvalidPath : String :=
  repeatCharStr 'a' 5000

/-- Helper `hugeInvalidPath`. -/
def hugeInvalidPath : String :=
  repeatDoubleStr (repeatCharStr 'a' 1024) 8

/-- Helper `dummyCid`. -/
def dummyCid : CommitId :=
  { hex := repeatCharStr 'a' 40 }

/-- Helper `zeroCid`. -/
def zeroCid : CommitId :=
  { hex := repeatCharStr '0' 40 }

/-- Helper `mainRef`. -/
def mainRef : RefName :=
  { raw := "main" }

/-- Helper `missingRef`. -/
def missingRef : RefName :=
  { raw := "no-such-branch" }

/-- Helper `badRef`. -/
def badRef : RefName :=
  { raw := "-bad-ref" }

/-- Helper `initCommittedRepo`. -/
def initCommittedRepo (dir : String) : IO CommitId := do
  assertOk (← Git.init dir false (some mainRef)) "initCommittedRepo init"
  IO.FS.writeFile (dir ++ "/f.txt") "base\n"
  assertOk (← Git.add dir #["f.txt"] false) "initCommittedRepo add"
  assertOk (← Git.commit dir (testAuthorOpts "base" false)) "initCommittedRepo commit"

/-- Helper `setupDivergedBranch`. -/
def setupDivergedBranch (repo : String) (branch : RefName) (content : String) : IO Unit := do
  assertOk (← Git.switch repo branch true none false) "setupDivergedBranch switch -c"
  IO.FS.writeFile (repo ++ "/f.txt") content
  assertOk (← Git.add repo #["f.txt"] false) "setupDivergedBranch add"
  let _ ← assertOk (← Git.commit repo (testAuthorOpts branch.raw false)) "setupDivergedBranch commit"
  assertOk (← Git.switch repo mainRef false none false) "setupDivergedBranch switch main"

/-- Helper `initConflictRepo`. -/
def initConflictRepo (repo : String) (dropMergeHead : Bool) : IO RefName := do
  let _ ← initCommittedRepo repo
  let sideRef : RefName := { raw := "side" }
  let otherRef : RefName := { raw := "other" }
  setupDivergedBranch repo sideRef "side\n"
  IO.FS.writeFile (repo ++ "/f.txt") "main\n"
  assertOk (← Git.add repo #["f.txt"] false) "initConflictRepo add main"
  let _ ← assertOk (← Git.commit repo (testAuthorOpts "main" false)) "initConflictRepo commit main"
  assertOk (← Git.createBranch repo otherRef (some "HEAD") false) "initConflictRepo create other"
  let mOut ← runProcRaw "git"
    #["-c", "user.name=t", "-c", "user.email=t@t", "merge", sideRef.raw] (some repo)
  assertTrue (mOut.exitCode != 0) "git merge side produced conflict"
  if dropMergeHead then
    IO.FS.removeFile (repo ++ "/.git/MERGE_HEAD")
  return otherRef

/-- Helper `writeBadUtf8File`. -/
def writeBadUtf8File (repo : String) : IO Unit :=
  runProcChecked "python3"
    #["-c", "import os, sys; open(os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'name'), 'wb').write(b'x' + bytes([10]))", repo]

/-- Helper `removeBadUtf8File`. -/
def removeBadUtf8File (repo : String) : IO Unit :=
  runProcChecked "python3"
    #["-c", "import os, sys; p = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'name'); os.path.exists(p) and os.unlink(p)", repo]

/-- Helper `withBadUtf8Repo`. -/
def withBadUtf8Repo (f : String → IO Unit) : IO Unit :=
  withTempDirIO fun root => do
    let link := root ++ "/utf8link"
    runProcChecked "python3"
      #["-c", "import os, subprocess, sys; d = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'dir'); os.makedirs(d); subprocess.run(['git', 'init', '-b', 'main'], cwd=d, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); os.symlink(d, sys.argv[2].encode('utf-8'))", root, link]
    try
      f link
    finally
      runProcChecked "python3"
        #["-c", "import os, shutil, sys; d = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'dir'); os.path.exists(d) and shutil.rmtree(d)", root]

/-- Helper `withBadUtf8UntrackedRepo`. -/
def withBadUtf8UntrackedRepo (f : String → IO Unit) : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    writeBadUtf8File repo
    try
      f repo
    finally
      removeBadUtf8File repo

/-- Helper `withBadUtf8CommittedRepo`. -/
def withBadUtf8CommittedRepo (f : String → CommitId → CommitId → IO Unit) : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    writeBadUtf8File repo
    try
      assertOk (← Git.add repo #[] true) "stage bad utf8 file"
      let c2 ← assertOk (← Git.commit repo (testAuthorOpts "bad utf8 filename" false)) "commit bad utf8 file"
      f repo c1 c2
    finally
      removeBadUtf8File repo

/-- Helper `runRealErr`. -/
def runRealErr {α : Type} (expected : GitErrorKind) (label : String)
    (act : IO (Except GitError α)) : IO Unit := do
  assertErrKind (← act) expected label

/-- Helper `runRealNonRepoErr`. -/
def runRealNonRepoErr {α : Type} (act : String → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← act root) .notARepo "non-repo path"

/-- Helper `runRealMissingDirErr`. -/
def runRealMissingDirErr {α : Type} (act : String → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← act (root ++ "/missing-repo")) .commandFailed "missing repo dir"

/-- Helper `runRealCommittedErr`. -/
def runRealCommittedErr {α : Type} (expected : GitErrorKind) (label : String)
    (act : String → CommitId → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let cid ← initCommittedRepo repo
    assertErrKind (← act repo cid) expected label

/-- Helper `runRealInitOnFileErr`. -/
def runRealInitOnFileErr : IO Unit :=
  withTempDirIO fun root => do
    let filePath := root ++ "/regular-file"
    IO.FS.writeFile filePath "x"
    assertErrKind (← Git.init filePath false none) .commandFailed "init on existing regular file"

/-- Helper `runRealCloneNonRepoErr`. -/
def runRealCloneNonRepoErr : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let _ ← initCommittedRepo src
    let filePath := root ++ "/not-a-dir"
    IO.FS.writeFile filePath "file\n"
    assertErrKind (← Git.clone src (filePath ++ "/sub") {}) .commandFailed "clone into file child"

/-- Helper `runRealCloneAlreadyExistsErr`. -/
def runRealCloneAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let dst := root ++ "/dst"
    let _ ← initCommittedRepo src
    IO.FS.createDirAll dst
    IO.FS.writeFile (dst ++ "/existing.txt") "occupied\n"
    assertErrKind (← Git.clone src dst {}) .alreadyExists "clone into non-empty target"

/-- Helper `runRealCloneNotFoundErr`. -/
def runRealCloneNotFoundErr : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← Git.clone (root ++ "/missing-src.git") (root ++ "/dst") {}) .notFound
      "clone missing source"

/-- Helper `runRealCommitConflictErr`. -/
def runRealCommitConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initConflictRepo repo false
    assertErrKind (← Git.commit repo (testAuthorOpts "merge commit" false)) .conflict "commit during conflict"

/-- Helper `runRealCheckoutDirtyErr`. -/
def runRealCheckoutDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    setupDivergedBranch repo sideRef "side-change\n"
    IO.FS.writeFile (repo ++ "/f.txt") "dirty-local\n"
    assertErrKind (← Git.checkout repo (.branch sideRef) false) .dirtyWorktree "checkout dirtyWorktree"

/-- Helper `runRealCheckoutBranchInUseErr`. -/
def runRealCheckoutBranchInUseErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    assertOk (← Git.createBranch repo sideRef none false) "create side"
    assertOk (← Git.worktreeAdd repo { path := root ++ "/wt", target? := some sideRef.raw }) "worktreeAdd side"
    assertErrKind (← Git.checkout repo (.branch sideRef) false) .branchInUse "checkout branchInUse"

/-- Helper `runRealCheckoutConflictErr`. -/
def runRealCheckoutConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let otherRef ← initConflictRepo repo false
    assertErrKind (← Git.checkout repo (.branch otherRef) false) .conflict "checkout conflict"

/-- Helper `runRealSwitchDirtyErr`. -/
def runRealSwitchDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    setupDivergedBranch repo sideRef "side-change\n"
    IO.FS.writeFile (repo ++ "/f.txt") "dirty-local\n"
    assertErrKind (← Git.switch repo sideRef false none false) .dirtyWorktree "switch dirtyWorktree"

/-- Helper `runRealSwitchBranchInUseErr`. -/
def runRealSwitchBranchInUseErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    assertOk (← Git.createBranch repo sideRef none false) "create side"
    assertOk (← Git.worktreeAdd repo { path := root ++ "/wt", target? := some sideRef.raw }) "worktreeAdd side"
    assertErrKind (← Git.switch repo sideRef false none false) .branchInUse "switch branchInUse"

/-- Helper `runRealSwitchConflictErr`. -/
def runRealSwitchConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let otherRef ← initConflictRepo repo true
    assertErrKind (← Git.switch repo otherRef false none false) .conflict "switch conflict"

/-- Helper `runRealWorktreeAddAlreadyExistsErr`. -/
def runRealWorktreeAddAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-exists"
    let _ ← initCommittedRepo repo
    IO.FS.createDirAll wt
    IO.FS.writeFile (wt ++ "/occupied.txt") "x\n"
    assertErrKind (← Git.worktreeAdd repo { path := wt, detach := true }) .alreadyExists
      "worktreeAdd alreadyExists"

/-- Helper `runRealWorktreeRemoveDirtyErr`. -/
def runRealWorktreeRemoveDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-dirty"
    let _ ← initCommittedRepo repo
    assertOk (← Git.worktreeAdd repo { path := wt, detach := true }) "worktreeAdd"
    IO.FS.writeFile (wt ++ "/dirty.txt") "dirty\n"
    assertErrKind (← Git.worktreeRemove repo wt false) .dirtyWorktree "worktreeRemove dirtyWorktree"

/-- Helper `runRealWithWorktreeDirtyErr`. -/
def runRealWithWorktreeDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-dirty"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := wt, detach := true } fun p => do
      IO.FS.writeFile (p ++ "/dirty.txt") "dirty\n"
      return .ok ()
    assertErrKind res .dirtyWorktree "withWorktree dirtyWorktree cleanup"

/-- Helper `runRealWithWorktreeNothingToCommitErr`. -/
def runRealWithWorktreeNothingToCommitErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p =>
      Git.commit p (testAuthorOpts "empty" false)
    assertErrKind res .nothingToCommit "withWorktree nothingToCommit"

/-- Helper `runRealWithWorktreeAlreadyExistsErr`. -/
def runRealWithWorktreeAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-exists"
    let _ ← initCommittedRepo repo
    IO.FS.createDirAll wt
    IO.FS.writeFile (wt ++ "/occupied.txt") "x\n"
    let res ← Git.withWorktree repo { path := wt, detach := true } fun _ => pure (.ok ())
    assertErrKind res .alreadyExists "withWorktree alreadyExists"

/-- Helper `runRealWithWorktreeNotFoundErr`. -/
def runRealWithWorktreeNotFoundErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p =>
      Git.add p #["missing.txt"] false
    assertErrKind res .notFound "withWorktree notFound"

/-- Helper `runRealWithWorktreeConflictErr`. -/
def runRealWithWorktreeConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p => do
      let sideRef : RefName := { raw := "wt-side" }
      let _ ← assertOk (← Git.createBranch p sideRef (some "HEAD") false) "create wt-side"
      IO.FS.writeFile (p ++ "/f.txt") "detached-change\n"
      assertOk (← Git.add p #["f.txt"] false) "add detached"
      let _ ← assertOk (← Git.commit p (testAuthorOpts "detached" false)) "commit detached"
      let detCid ← assertOk (← Git.revParseCommit p "HEAD") "revParse detached"
      assertOk (← Git.switch p sideRef false none false) "switch wt-side"
      IO.FS.writeFile (p ++ "/f.txt") "side-change\n"
      assertOk (← Git.add p #["f.txt"] false) "add side"
      let _ ← assertOk (← Git.commit p (testAuthorOpts "side" false)) "commit side"
      let mOut ← runProcRaw "git"
        #["-c", "user.name=t", "-c", "user.email=t@t", "merge", detCid.hex] (some p)
      assertTrue (mOut.exitCode != 0) "merge conflict inside worktree"
      Git.commit p (testAuthorOpts "fail merge" false)
    assertErrKind res .conflict "withWorktree conflict"

/-- Helper `runRealWithWorktreeParseError`. -/
def runRealWithWorktreeParseError : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p => do
      writeBadUtf8File p
      try
        Git.status p
      finally
        removeBadUtf8File p
    assertErrKind res .parseError "withWorktree parseError"

/-- Helper `mockFaultOutput`. -/
def mockFaultOutput : GitErrorKind → Except GitError GitRawOutput
  | .notARepo => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: not a git repository".toUTF8 }
  | .invalidRef => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: invalid reference: mock".toUTF8 }
  | .invalidPath => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: invalid path".toUTF8 }
  | .invalidInput => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: invalid input".toUTF8 }
  | .dirtyWorktree => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "error: local changes would be overwritten by checkout".toUTF8 }
  | .nothingToCommit => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "nothing to commit, working tree clean".toUTF8 }
  | .branchInUse => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: 'main' is already used by worktree at '/tmp/wt'".toUTF8 }
  | .alreadyExists => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: a branch named 'main' already exists".toUTF8 }
  | .notFound => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "error: branch 'missing' not found".toUTF8 }
  | .conflict => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: Exiting because of an unresolved conflict.".toUTF8 }
  | .timeout => .error { kind := .timeout, command := some "git", message := "mock git timed out" }
  | .commandFailed => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "fatal: mock command failed".toUTF8 }
  | .parseError => .ok { exitCode := 0, stdout := ByteArray.mk #[0xFF, 0xFE], stderr := ByteArray.empty }

/-- Helper `mockFaultOps`. -/
def mockFaultOps (kind : GitErrorKind) : RawGitOps :=
  { listEnv := pure (.ok #[])
    execGit := fun _ _ => pure (mockFaultOutput kind) }

/-- Helper `runMockErr`. -/
def runMockErr {α : Type} (expected : GitErrorKind)
    (act : GitApi → IO (Except GitError α)) : IO Unit := do
  let api := Impl.mkApiM (mockFaultOps expected)
  assertErrKind (← act api) expected s!"mocked {reprStr expected}"


end LeanSwe.Git.RuntimeTests
