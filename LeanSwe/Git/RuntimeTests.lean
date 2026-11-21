import Core.Assumptions
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.TempDir.Interface
import LeanSwe.Process.Interface

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except GitError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except GitError α) (expected : GitErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def withTempDirIO (f : String → IO Unit) : IO Unit := do
  let res ← LeanSwe.TempDir.withTempDir none "lean-swe-git-rt-" fun dir => do
    f dir
    pure (.ok ())
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"ASSERTION FAILED: withTempDir failed: {e.message}")

private def testAuthorOpts (msg : String) (allowEmpty : Bool := false) : CommitOptions :=
  { message := msg
    allowEmpty := allowEmpty
    authorName := some "LeanSwe Test"
    authorEmail := some "test@leanswe.invalid" }

private def runProcChecked (prog : String) (args : Array String) (cwd? : Option String := none) : IO Unit := do
  let res ← LeanSwe.Process.run { program := prog, args := args, cwd := cwd? }
  match res with
  | .error e => throw (IO.userError s!"ASSERTION FAILED: process {prog} failed: {e.message}")
  | .ok out =>
    if out.exitCode != 0 then
      let errStr := (String.fromUTF8? out.stderr).getD ""
      throw (IO.userError s!"ASSERTION FAILED: process {prog} exited {out.exitCode}: {errStr}")

private def runProcRaw (prog : String) (args : Array String) (cwd? : Option String := none) :
    IO LeanSwe.Process.ExecResult := do
  match ← LeanSwe.Process.run { program := prog, args := args, cwd := cwd? } with
  | .error e => throw (IO.userError s!"ASSERTION FAILED: process {prog} failed: {e.message}")
  | .ok out => return out

private def repeatCharStr (c : Char) (n : Nat) : String :=
  String.ofList (List.replicate n c)

private def repeatDoubleStr (chunk : String) : Nat → String
  | 0 => chunk
  | k + 1 => repeatDoubleStr (chunk ++ chunk) k

private def longInvalidPath : String :=
  repeatCharStr 'a' 5000

private def hugeInvalidPath : String :=
  repeatDoubleStr (repeatCharStr 'a' 1024) 8

private def dummyCid : CommitId :=
  { hex := repeatCharStr 'a' 40 }

private def zeroCid : CommitId :=
  { hex := repeatCharStr '0' 40 }

private def mainRef : RefName :=
  { raw := "main" }

private def missingRef : RefName :=
  { raw := "no-such-branch" }

private def badRef : RefName :=
  { raw := "-bad-ref" }

private def initCommittedRepo (dir : String) : IO CommitId := do
  assertOk (← Git.init dir false (some mainRef)) "initCommittedRepo init"
  IO.FS.writeFile (dir ++ "/f.txt") "base\n"
  assertOk (← Git.add dir #["f.txt"] false) "initCommittedRepo add"
  assertOk (← Git.commit dir (testAuthorOpts "base" false)) "initCommittedRepo commit"

private def setupDivergedBranch (repo : String) (branch : RefName) (content : String) : IO Unit := do
  assertOk (← Git.switch repo branch true none false) "setupDivergedBranch switch -c"
  IO.FS.writeFile (repo ++ "/f.txt") content
  assertOk (← Git.add repo #["f.txt"] false) "setupDivergedBranch add"
  let _ ← assertOk (← Git.commit repo (testAuthorOpts branch.raw false)) "setupDivergedBranch commit"
  assertOk (← Git.switch repo mainRef false none false) "setupDivergedBranch switch main"

private def initConflictRepo (repo : String) (dropMergeHead : Bool) : IO RefName := do
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

private def writeBadUtf8File (repo : String) : IO Unit :=
  runProcChecked "python3"
    #["-c", "import os, sys; open(os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'name'), 'wb').write(b'x' + bytes([10]))", repo]

private def removeBadUtf8File (repo : String) : IO Unit :=
  runProcChecked "python3"
    #["-c", "import os, sys; p = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'name'); os.path.exists(p) and os.unlink(p)", repo]

private def withBadUtf8Repo (f : String → IO Unit) : IO Unit :=
  withTempDirIO fun root => do
    let link := root ++ "/utf8link"
    runProcChecked "python3"
      #["-c", "import os, subprocess, sys; d = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'dir'); os.makedirs(d); subprocess.run(['git', 'init', '-b', 'main'], cwd=d, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); os.symlink(d, sys.argv[2].encode('utf-8'))", root, link]
    try
      f link
    finally
      runProcChecked "python3"
        #["-c", "import os, shutil, sys; d = os.path.join(sys.argv[1].encode('utf-8'), b'bad' + bytes([255]) + b'dir'); os.path.exists(d) and shutil.rmtree(d)", root]

private def withBadUtf8UntrackedRepo (f : String → IO Unit) : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    writeBadUtf8File repo
    try
      f repo
    finally
      removeBadUtf8File repo

private def withBadUtf8CommittedRepo (f : String → CommitId → CommitId → IO Unit) : IO Unit :=
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

private def runRealErr {α : Type} (expected : GitErrorKind) (label : String)
    (act : IO (Except GitError α)) : IO Unit := do
  assertErrKind (← act) expected label

private def runRealNonRepoErr {α : Type} (act : String → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← act root) .notARepo "non-repo path"

private def runRealMissingDirErr {α : Type} (act : String → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← act (root ++ "/missing-repo")) .commandFailed "missing repo dir"

private def runRealCommittedErr {α : Type} (expected : GitErrorKind) (label : String)
    (act : String → CommitId → IO (Except GitError α)) : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let cid ← initCommittedRepo repo
    assertErrKind (← act repo cid) expected label

private def runRealInitOnFileErr : IO Unit :=
  withTempDirIO fun root => do
    let filePath := root ++ "/regular-file"
    IO.FS.writeFile filePath "x"
    assertErrKind (← Git.init filePath false none) .commandFailed "init on existing regular file"

private def runRealCloneNonRepoErr : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let _ ← initCommittedRepo src
    let filePath := root ++ "/not-a-dir"
    IO.FS.writeFile filePath "file\n"
    assertErrKind (← Git.clone src (filePath ++ "/sub") {}) .commandFailed "clone into file child"

private def runRealCloneAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let dst := root ++ "/dst"
    let _ ← initCommittedRepo src
    IO.FS.createDirAll dst
    IO.FS.writeFile (dst ++ "/existing.txt") "occupied\n"
    assertErrKind (← Git.clone src dst {}) .alreadyExists "clone into non-empty target"

private def runRealCloneNotFoundErr : IO Unit :=
  withTempDirIO fun root => do
    assertErrKind (← Git.clone (root ++ "/missing-src.git") (root ++ "/dst") {}) .notFound
      "clone missing source"

private def runRealCommitConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initConflictRepo repo false
    assertErrKind (← Git.commit repo (testAuthorOpts "merge commit" false)) .conflict "commit during conflict"

private def runRealCheckoutDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    setupDivergedBranch repo sideRef "side-change\n"
    IO.FS.writeFile (repo ++ "/f.txt") "dirty-local\n"
    assertErrKind (← Git.checkout repo (.branch sideRef) false) .dirtyWorktree "checkout dirtyWorktree"

private def runRealCheckoutBranchInUseErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    assertOk (← Git.createBranch repo sideRef none false) "create side"
    assertOk (← Git.worktreeAdd repo { path := root ++ "/wt", target? := some sideRef.raw }) "worktreeAdd side"
    assertErrKind (← Git.checkout repo (.branch sideRef) false) .branchInUse "checkout branchInUse"

private def runRealCheckoutConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let otherRef ← initConflictRepo repo false
    assertErrKind (← Git.checkout repo (.branch otherRef) false) .conflict "checkout conflict"

private def runRealSwitchDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    setupDivergedBranch repo sideRef "side-change\n"
    IO.FS.writeFile (repo ++ "/f.txt") "dirty-local\n"
    assertErrKind (← Git.switch repo sideRef false none false) .dirtyWorktree "switch dirtyWorktree"

private def runRealSwitchBranchInUseErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let sideRef : RefName := { raw := "side" }
    assertOk (← Git.createBranch repo sideRef none false) "create side"
    assertOk (← Git.worktreeAdd repo { path := root ++ "/wt", target? := some sideRef.raw }) "worktreeAdd side"
    assertErrKind (← Git.switch repo sideRef false none false) .branchInUse "switch branchInUse"

private def runRealSwitchConflictErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let otherRef ← initConflictRepo repo true
    assertErrKind (← Git.switch repo otherRef false none false) .conflict "switch conflict"

private def runRealWorktreeAddAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-exists"
    let _ ← initCommittedRepo repo
    IO.FS.createDirAll wt
    IO.FS.writeFile (wt ++ "/occupied.txt") "x\n"
    assertErrKind (← Git.worktreeAdd repo { path := wt, detach := true }) .alreadyExists
      "worktreeAdd alreadyExists"

private def runRealWorktreeRemoveDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-dirty"
    let _ ← initCommittedRepo repo
    assertOk (← Git.worktreeAdd repo { path := wt, detach := true }) "worktreeAdd"
    IO.FS.writeFile (wt ++ "/dirty.txt") "dirty\n"
    assertErrKind (← Git.worktreeRemove repo wt false) .dirtyWorktree "worktreeRemove dirtyWorktree"

private def runRealWithWorktreeDirtyErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-dirty"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := wt, detach := true } fun p => do
      IO.FS.writeFile (p ++ "/dirty.txt") "dirty\n"
      return .ok ()
    assertErrKind res .dirtyWorktree "withWorktree dirtyWorktree cleanup"

private def runRealWithWorktreeNothingToCommitErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p =>
      Git.commit p (testAuthorOpts "empty" false)
    assertErrKind res .nothingToCommit "withWorktree nothingToCommit"

private def runRealWithWorktreeAlreadyExistsErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let wt := root ++ "/wt-exists"
    let _ ← initCommittedRepo repo
    IO.FS.createDirAll wt
    IO.FS.writeFile (wt ++ "/occupied.txt") "x\n"
    let res ← Git.withWorktree repo { path := wt, detach := true } fun _ => pure (.ok ())
    assertErrKind res .alreadyExists "withWorktree alreadyExists"

private def runRealWithWorktreeNotFoundErr : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let _ ← initCommittedRepo repo
    let res ← Git.withWorktree repo { path := root ++ "/wt", detach := true } fun p =>
      Git.add p #["missing.txt"] false
    assertErrKind res .notFound "withWorktree notFound"

private def runRealWithWorktreeConflictErr : IO Unit :=
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

private def runRealWithWorktreeParseError : IO Unit :=
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

private def mockFaultOutput : GitErrorKind → Except GitError GitRawOutput
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

private def mockFaultOps (kind : GitErrorKind) : RawGitOps :=
  { listEnv := pure (.ok #[])
    execGit := fun _ _ => pure (mockFaultOutput kind) }

private def runMockErr {α : Type} (expected : GitErrorKind)
    (act : GitApi → IO (Except GitError α)) : IO Unit := do
  let api := Impl.mkApiM (mockFaultOps expected)
  assertErrKind (← act api) expected s!"mocked {reprStr expected}"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig`. -/
def assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let poisonedOps : RawGitOps :=
      { listEnv := do
          match ← defaultRawOps.listEnv with
          | .error e => return .error e
          | .ok env => return .ok (env ++ #[
              ("GIT_DIR", "/nonexistent/evil/.git"),
              ("GIT_WORK_TREE", "/nonexistent/evil"),
              ("GIT_INDEX_FILE", "/nonexistent/evil/index"),
              ("GIT_AUTHOR_NAME", "Evil Author")
            ])
        execGit := defaultRawOps.execGit }
    let poisonedApi := Impl.mkApiM poisonedOps
    assertTrue ((← assertOk (← poisonedApi.headCommit? repo) "poisoned headCommit?") == some c1)
      "poisoned GIT_* env stripped before execGit"
    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare repo"
    assertTrue (← assertOk (← Git.isRepo bareDir) "bare isRepo") "bare repo recognized"
    assertErrKind (← Git.repoRoot bareDir) .notARepo "bare repoRoot returns notARepo"
    let bareReal ← IO.FS.realPath bareDir
    assertTrue ((← assertOk (← Git.commonDir bareDir) "bare commonDir") == bareReal.toString)
      "bare commonDir matches realPath"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename`. -/
def assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init status repo"
    IO.FS.writeFile (repo ++ "/a b.txt") "hello\n"
    IO.FS.writeFile (repo ++ "/old name.txt") "rename me\n"
    assertOk (← Git.add repo #["a b.txt", "old name.txt"] false) "add initial"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "init" false)) "commit initial"
    IO.FS.writeFile (repo ++ "/new name.txt") "rename me\n"
    IO.FS.removeFile (repo ++ "/old name.txt")
    assertOk (← Git.add repo #[] true) "stage rename"
    IO.FS.writeFile (repo ++ "/a b.txt") "modified\n"
    IO.FS.writeFile (repo ++ "/un track.txt") "untracked\n"
    let entries ← assertOk (← Git.status repo) "status"
    assertTrue (entries.toList.contains
      { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" })
      "status -z destination-first rename"
    assertTrue (entries.toList.contains
      { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" })
      "status -z unquoted space path modified"
    assertTrue (entries.toList.contains
      { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "un track.txt" })
      "status -z unquoted space path untracked"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename`. -/
def assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init diff repo"
    IO.FS.writeFile (repo ++ "/src name.txt") "same payload for rename detection\n"
    assertOk (← Git.add repo #["src name.txt"] false) "add src"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "c1" false)) "c1"
    IO.FS.writeFile (repo ++ "/dst name.txt") "same payload for rename detection\n"
    IO.FS.removeFile (repo ++ "/src name.txt")
    IO.FS.writeFile (repo ++ "/added file.txt") "new\n"
    assertOk (← Git.add repo #[] true) "stage rename + add"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "c2"
    let diffs ← assertOk (← Git.diffNameStatus repo c1.hex (some c2.hex) #[]) "diffNameStatus"
    assertTrue (diffs.any fun d =>
      d.path == "dst name.txt" && d.origPath == some "src name.txt" &&
      match d.kind with | .renamed _ => true | _ => false)
      "diff -z source-first rename mapped to origPath/path"
    assertTrue (diffs.any fun d => d.path == "added file.txt" && d.kind == .added)
      "diff -z added entry"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas`. -/
def assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas : IO Unit :=
  withTempDirIO fun root => do
    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare"
    let bareWts ← assertOk (← Git.listWorktrees bareDir) "listWorktrees bare"
    assertTrue (bareWts.size == 1 && bareWts[0]!.isBare && bareWts[0]!.head? == none && bareWts[0]!.branch? == none)
      "bare stanza parsed"

    let unborn := root ++ "/unborn"
    assertOk (← Git.init unborn false (some mainRef)) "init unborn"
    let unbornWts ← assertOk (← Git.listWorktrees unborn) "listWorktrees unborn"
    assertTrue (unbornWts.size == 1 && !unbornWts[0]!.isBare && unbornWts[0]!.head? == none && unbornWts[0]!.branch? == some mainRef)
      "unborn stanza parsed"

    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let wtDetached := root ++ "/wt-det"
    assertOk (← Git.worktreeAdd repo { path := wtDetached, detach := true }) "worktreeAdd detached"
    let wtDetReal := (← IO.FS.realPath wtDetached).toString
    let wts ← assertOk (← Git.listWorktrees repo) "listWorktrees linked"
    assertTrue (wts.size == 2) "two worktrees listed"
    assertTrue (wts.any fun w => w.path == wtDetReal && w.isDetached && w.head? == some c1 && w.branch? == none)
      "linked detached worktree stanza parsed"
    assertOk (← Git.worktreeRemove repo wtDetached false) "worktreeRemove detached"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_mergeBase_andIsAncestor_matchDagSemantics`. -/
def assume_git_mergeBase_andIsAncestor_matchDagSemantics : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    IO.FS.writeFile (repo ++ "/f.txt") "c2\n"
    assertOk (← Git.add repo #["f.txt"] false) "add c2"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "c2"
    let featRef : RefName := { raw := "feat" }
    assertOk (← Git.switch repo featRef true none false) "switch -c feat"
    IO.FS.writeFile (repo ++ "/feat.txt") "feat\n"
    assertOk (← Git.add repo #["feat.txt"] false) "add cFeat"
    let cFeat ← assertOk (← Git.commit repo (testAuthorOpts "cFeat" false)) "cFeat"
    assertOk (← Git.switch repo mainRef false none false) "switch main"
    IO.FS.writeFile (repo ++ "/main.txt") "c3\n"
    assertOk (← Git.add repo #["main.txt"] false) "add c3"
    let c3 ← assertOk (← Git.commit repo (testAuthorOpts "c3" false)) "c3"
    assertTrue (← assertOk (← Git.isAncestor repo c1 c1) "reflexive") "c1 <= c1"
    assertTrue (← assertOk (← Git.isAncestor repo c1 c3) "transitive") "c1 <= c3"
    assertTrue (!(← assertOk (← Git.isAncestor repo c3 c1) "antisym")) "not (c3 <= c1)"
    assertTrue (!(← assertOk (← Git.isAncestor repo c3 cFeat) "incomparable")) "not (c3 <= cFeat)"
    assertTrue ((← assertOk (← Git.mergeBase? repo c3 cFeat) "mergeBase") == some c2) "mergeBase == c2"
    runProcChecked "git" #["checkout", "--orphan", "orphan"] (some repo)
    IO.FS.writeFile (repo ++ "/orphan.txt") "orphan\n"
    assertOk (← Git.add repo #["orphan.txt"] false) "add orphan"
    let cOrphan ← assertOk (← Git.commit repo (testAuthorOpts "orphan" false)) "commit orphan"
    assertTrue ((← assertOk (← Git.mergeBase? repo c3 cOrphan) "disjoint mergeBase") == none)
      "disjoint histories have no mergeBase"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob`. -/
def assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init"
    assertTrue ((← assertOk (← Git.headState repo) "unborn headState") == .attached mainRef none)
      "unborn attached none"
    IO.FS.createDirAll (repo ++ "/sub")
    IO.FS.writeFile (repo ++ "/sub/item.txt") "payload\n"
    assertOk (← Git.add repo #["sub/item.txt"] false) "add sub/item.txt"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "c1" false)) "c1"
    assertTrue ((← assertOk (← Git.headState repo) "attached c1") == .attached mainRef (some c1))
      "attached c1"
    assertOk (← Git.checkout repo (.commit c1) false) "checkout detached"
    assertTrue ((← assertOk (← Git.headState repo) "detached c1") == .detached c1) "detached c1"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "sub/item.txt") "showFile blob") == some "payload\n".toUTF8)
      "showFile blob"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "sub") "showFile tree") == none)
      "showFile tree returns none"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "missing.txt") "showFile missing") == none)
      "showFile missing returns none"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_clone_andFetch_roundTripLocalRefsAndPrune`. -/
def assume_git_clone_andFetch_roundTripLocalRefsAndPrune : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let _ ← initCommittedRepo src
    let topicRef : RefName := { raw := "topic" }
    assertOk (← Git.createBranch src topicRef none false) "create topic in src"
    let origin := root ++ "/origin.git"
    assertOk (← Git.clone src origin { bare := true }) "clone --bare"
    let copyDir := root ++ "/copy"
    assertOk (← Git.clone origin copyDir {}) "clone local"
    assertOk (← Git.fetch copyDir origin (some "+refs/heads/*:refs/remotes/origin/*") false) "fetch all"
    let _ ← assertOk (← Git.revParseCommit copyDir "refs/remotes/origin/topic") "topic fetched"
    assertOk (← Git.deleteBranch origin topicRef true) "delete topic in origin"
    assertOk (← Git.fetch copyDir origin (some "+refs/heads/*:refs/remotes/origin/*") true) "fetch --prune"
    assertErrKind (← Git.revParseCommit copyDir "refs/remotes/origin/topic") .invalidRef "pruned remote ref absent"

/-- Registered external-world assumption probes for `LeanSwe.Git`. -/
def registeredAssumptions : Array Core.RegisteredAssumption :=
  #[ { specName := "LeanSwe.Git.assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig", run := assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig }
   , { specName := "LeanSwe.Git.assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename", run := assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename }
   , { specName := "LeanSwe.Git.assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename", run := assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename }
   , { specName := "LeanSwe.Git.assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas", run := assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas }
   , { specName := "LeanSwe.Git.assume_git_mergeBase_andIsAncestor_matchDagSemantics", run := assume_git_mergeBase_andIsAncestor_matchDagSemantics }
   , { specName := "LeanSwe.Git.assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob", run := assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob }
   , { specName := "LeanSwe.Git.assume_git_clone_andFetch_roundTripLocalRefsAndPrune", run := assume_git_clone_andFetch_roundTripLocalRefsAndPrune } ]

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidRef`. -/
def err_git_isRepo_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.isRepo "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidPath`. -/
def err_git_isRepo_invalidPath : IO Unit :=
  runRealErr .invalidPath "isRepo invalidPath" (Git.isRepo "")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidInput`. -/
def err_git_isRepo_invalidInput : IO Unit :=
  runRealErr .invalidInput "isRepo invalidInput" (Git.isRepo longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.dirtyWorktree`. -/
def err_git_isRepo_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.nothingToCommit`. -/
def err_git_isRepo_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.branchInUse`. -/
def err_git_isRepo_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.alreadyExists`. -/
def err_git_isRepo_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.notFound`. -/
def err_git_isRepo_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.conflict`. -/
def err_git_isRepo_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.timeout`. -/
def err_git_isRepo_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.isRepo "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.commandFailed`. -/
def err_git_isRepo_commandFailed : IO Unit :=
  runRealMissingDirErr Git.isRepo

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.notARepo`. -/
def err_git_repoRoot_notARepo : IO Unit :=
  runRealNonRepoErr Git.repoRoot

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidRef`. -/
def err_git_repoRoot_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.repoRoot "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidPath`. -/
def err_git_repoRoot_invalidPath : IO Unit :=
  runRealErr .invalidPath "repoRoot invalidPath" (Git.repoRoot "")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidInput`. -/
def err_git_repoRoot_invalidInput : IO Unit :=
  runRealErr .invalidInput "repoRoot invalidInput" (Git.repoRoot longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.dirtyWorktree`. -/
def err_git_repoRoot_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.nothingToCommit`. -/
def err_git_repoRoot_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.branchInUse`. -/
def err_git_repoRoot_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.alreadyExists`. -/
def err_git_repoRoot_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.notFound`. -/
def err_git_repoRoot_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.conflict`. -/
def err_git_repoRoot_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.timeout`. -/
def err_git_repoRoot_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.repoRoot "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.commandFailed`. -/
def err_git_repoRoot_commandFailed : IO Unit :=
  runRealMissingDirErr Git.repoRoot

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.parseError`. -/
def err_git_repoRoot_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.repoRoot link) .parseError "repoRoot parseError"

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.notARepo`. -/
def err_git_commonDir_notARepo : IO Unit :=
  runRealNonRepoErr Git.commonDir

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidRef`. -/
def err_git_commonDir_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.commonDir "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidPath`. -/
def err_git_commonDir_invalidPath : IO Unit :=
  runRealErr .invalidPath "commonDir invalidPath" (Git.commonDir "")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidInput`. -/
def err_git_commonDir_invalidInput : IO Unit :=
  runRealErr .invalidInput "commonDir invalidInput" (Git.commonDir longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.dirtyWorktree`. -/
def err_git_commonDir_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.nothingToCommit`. -/
def err_git_commonDir_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.branchInUse`. -/
def err_git_commonDir_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.alreadyExists`. -/
def err_git_commonDir_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.notFound`. -/
def err_git_commonDir_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.conflict`. -/
def err_git_commonDir_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.timeout`. -/
def err_git_commonDir_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.commonDir "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.commandFailed`. -/
def err_git_commonDir_commandFailed : IO Unit :=
  runRealMissingDirErr Git.commonDir

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.parseError`. -/
def err_git_commonDir_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.commonDir link) .parseError "commonDir parseError"

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.notARepo`. -/
def err_git_headCommit_notARepo : IO Unit :=
  runRealNonRepoErr Git.headCommit?

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidRef`. -/
def err_git_headCommit_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidPath`. -/
def err_git_headCommit_invalidPath : IO Unit :=
  runRealErr .invalidPath "headCommit? invalidPath" (Git.headCommit? "")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidInput`. -/
def err_git_headCommit_invalidInput : IO Unit :=
  runRealErr .invalidInput "headCommit? invalidInput" (Git.headCommit? longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.dirtyWorktree`. -/
def err_git_headCommit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.nothingToCommit`. -/
def err_git_headCommit_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.branchInUse`. -/
def err_git_headCommit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.alreadyExists`. -/
def err_git_headCommit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.notFound`. -/
def err_git_headCommit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.conflict`. -/
def err_git_headCommit_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.timeout`. -/
def err_git_headCommit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.commandFailed`. -/
def err_git_headCommit_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headCommit?

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.parseError`. -/
def err_git_headCommit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.notARepo`. -/
def err_git_headBranch_notARepo : IO Unit :=
  runRealNonRepoErr Git.headBranch?

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidRef`. -/
def err_git_headBranch_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidPath`. -/
def err_git_headBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "headBranch? invalidPath" (Git.headBranch? "")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidInput`. -/
def err_git_headBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "headBranch? invalidInput" (Git.headBranch? longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.dirtyWorktree`. -/
def err_git_headBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.nothingToCommit`. -/
def err_git_headBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.branchInUse`. -/
def err_git_headBranch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.alreadyExists`. -/
def err_git_headBranch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.notFound`. -/
def err_git_headBranch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.conflict`. -/
def err_git_headBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.timeout`. -/
def err_git_headBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.commandFailed`. -/
def err_git_headBranch_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headBranch?

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.parseError`. -/
def err_git_headBranch_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.notARepo`. -/
def err_git_headState_notARepo : IO Unit :=
  runRealNonRepoErr Git.headState

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.invalidRef`. -/
def err_git_headState_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.invalidPath`. -/
def err_git_headState_invalidPath : IO Unit :=
  runRealErr .invalidPath "headState invalidPath" (Git.headState "")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.invalidInput`. -/
def err_git_headState_invalidInput : IO Unit :=
  runRealErr .invalidInput "headState invalidInput" (Git.headState longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.dirtyWorktree`. -/
def err_git_headState_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.nothingToCommit`. -/
def err_git_headState_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.branchInUse`. -/
def err_git_headState_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.alreadyExists`. -/
def err_git_headState_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.notFound`. -/
def err_git_headState_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.conflict`. -/
def err_git_headState_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.timeout`. -/
def err_git_headState_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.commandFailed`. -/
def err_git_headState_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headState

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.parseError`. -/
def err_git_headState_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.notARepo`. -/
def err_git_revParseCommit_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.revParseCommit p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidRef`. -/
def err_git_revParseCommit_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "revParseCommit invalidRef" (fun repo _ => Git.revParseCommit repo "no-such-ref")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidPath`. -/
def err_git_revParseCommit_invalidPath : IO Unit :=
  runRealErr .invalidPath "revParseCommit invalidPath" (Git.revParseCommit "" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidInput`. -/
def err_git_revParseCommit_invalidInput : IO Unit :=
  runRealErr .invalidInput "revParseCommit invalidInput" (Git.revParseCommit "/tmp" "-bad")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.dirtyWorktree`. -/
def err_git_revParseCommit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.nothingToCommit`. -/
def err_git_revParseCommit_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.branchInUse`. -/
def err_git_revParseCommit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.alreadyExists`. -/
def err_git_revParseCommit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.notFound`. -/
def err_git_revParseCommit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.conflict`. -/
def err_git_revParseCommit_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.timeout`. -/
def err_git_revParseCommit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.commandFailed`. -/
def err_git_revParseCommit_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.revParseCommit p "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.parseError`. -/
def err_git_revParseCommit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.notARepo`. -/
def err_git_isAncestor_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.isAncestor p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidRef`. -/
def err_git_isAncestor_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "isAncestor invalidRef" (fun repo cid => Git.isAncestor repo zeroCid cid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidPath`. -/
def err_git_isAncestor_invalidPath : IO Unit :=
  runRealErr .invalidPath "isAncestor invalidPath" (Git.isAncestor "" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidInput`. -/
def err_git_isAncestor_invalidInput : IO Unit :=
  runRealErr .invalidInput "isAncestor invalidInput" (Git.isAncestor longInvalidPath dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.dirtyWorktree`. -/
def err_git_isAncestor_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.nothingToCommit`. -/
def err_git_isAncestor_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.branchInUse`. -/
def err_git_isAncestor_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.alreadyExists`. -/
def err_git_isAncestor_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.notFound`. -/
def err_git_isAncestor_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.conflict`. -/
def err_git_isAncestor_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.timeout`. -/
def err_git_isAncestor_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.commandFailed`. -/
def err_git_isAncestor_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.isAncestor p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.notARepo`. -/
def err_git_mergeBase_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.mergeBase? p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidRef`. -/
def err_git_mergeBase_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "mergeBase? invalidRef" (fun repo cid => Git.mergeBase? repo zeroCid cid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidPath`. -/
def err_git_mergeBase_invalidPath : IO Unit :=
  runRealErr .invalidPath "mergeBase? invalidPath" (Git.mergeBase? "" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidInput`. -/
def err_git_mergeBase_invalidInput : IO Unit :=
  runRealErr .invalidInput "mergeBase? invalidInput" (Git.mergeBase? longInvalidPath dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.dirtyWorktree`. -/
def err_git_mergeBase_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.nothingToCommit`. -/
def err_git_mergeBase_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.branchInUse`. -/
def err_git_mergeBase_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.alreadyExists`. -/
def err_git_mergeBase_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.notFound`. -/
def err_git_mergeBase_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.conflict`. -/
def err_git_mergeBase_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.timeout`. -/
def err_git_mergeBase_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.commandFailed`. -/
def err_git_mergeBase_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.mergeBase? p dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.parseError`. -/
def err_git_mergeBase_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.notARepo`. -/
def err_git_status_notARepo : IO Unit :=
  runRealNonRepoErr Git.status

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.invalidRef`. -/
def err_git_status_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.status "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.invalidPath`. -/
def err_git_status_invalidPath : IO Unit :=
  runRealErr .invalidPath "status invalidPath" (Git.status "")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.invalidInput`. -/
def err_git_status_invalidInput : IO Unit :=
  runRealErr .invalidInput "status invalidInput" (Git.status longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.dirtyWorktree`. -/
def err_git_status_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.nothingToCommit`. -/
def err_git_status_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.branchInUse`. -/
def err_git_status_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.alreadyExists`. -/
def err_git_status_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.notFound`. -/
def err_git_status_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.conflict`. -/
def err_git_status_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.timeout`. -/
def err_git_status_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.status "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.commandFailed`. -/
def err_git_status_commandFailed : IO Unit :=
  runRealMissingDirErr Git.status

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.parseError`. -/
def err_git_status_parseError : IO Unit :=
  withBadUtf8UntrackedRepo fun repo => do assertErrKind (← Git.status repo) .parseError "status parseError"

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.notARepo`. -/
def err_git_diffNameStatus_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.diffNameStatus p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidRef`. -/
def err_git_diffNameStatus_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "diffNameStatus invalidRef" (fun repo _ => Git.diffNameStatus repo "no-such-ref")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidPath`. -/
def err_git_diffNameStatus_invalidPath : IO Unit :=
  runRealErr .invalidPath "diffNameStatus invalidPath" (Git.diffNameStatus "" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidInput`. -/
def err_git_diffNameStatus_invalidInput : IO Unit :=
  runRealErr .invalidInput "diffNameStatus invalidInput" (Git.diffNameStatus "/tmp" "HEAD:bad")

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.dirtyWorktree`. -/
def err_git_diffNameStatus_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.nothingToCommit`. -/
def err_git_diffNameStatus_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.branchInUse`. -/
def err_git_diffNameStatus_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.alreadyExists`. -/
def err_git_diffNameStatus_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.notFound`. -/
def err_git_diffNameStatus_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.conflict`. -/
def err_git_diffNameStatus_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.timeout`. -/
def err_git_diffNameStatus_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.commandFailed`. -/
def err_git_diffNameStatus_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.diffNameStatus p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.parseError`. -/
def err_git_diffNameStatus_parseError : IO Unit :=
  withBadUtf8CommittedRepo fun repo c1 c2 => do assertErrKind (← Git.diffNameStatus repo c1.hex (some c2.hex)) .parseError "diffNameStatus parseError"

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.notARepo`. -/
def err_git_listWorktrees_notARepo : IO Unit :=
  runRealNonRepoErr Git.listWorktrees

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidRef`. -/
def err_git_listWorktrees_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.listWorktrees "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidPath`. -/
def err_git_listWorktrees_invalidPath : IO Unit :=
  runRealErr .invalidPath "listWorktrees invalidPath" (Git.listWorktrees "")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidInput`. -/
def err_git_listWorktrees_invalidInput : IO Unit :=
  runRealErr .invalidInput "listWorktrees invalidInput" (Git.listWorktrees longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.dirtyWorktree`. -/
def err_git_listWorktrees_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.nothingToCommit`. -/
def err_git_listWorktrees_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.branchInUse`. -/
def err_git_listWorktrees_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.alreadyExists`. -/
def err_git_listWorktrees_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.notFound`. -/
def err_git_listWorktrees_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.conflict`. -/
def err_git_listWorktrees_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.timeout`. -/
def err_git_listWorktrees_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.listWorktrees "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.commandFailed`. -/
def err_git_listWorktrees_commandFailed : IO Unit :=
  runRealMissingDirErr Git.listWorktrees

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.parseError`. -/
def err_git_listWorktrees_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.listWorktrees link) .parseError "listWorktrees parseError"

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.notARepo`. -/
def err_git_showFile_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.showFile? p "HEAD" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidRef`. -/
def err_git_showFile_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "showFile? invalidRef" (fun repo _ => Git.showFile? repo "no-such-ref" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidPath`. -/
def err_git_showFile_invalidPath : IO Unit :=
  runRealErr .invalidPath "showFile? invalidPath" (Git.showFile? "" "HEAD" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidInput`. -/
def err_git_showFile_invalidInput : IO Unit :=
  runRealErr .invalidInput "showFile? invalidInput" (Git.showFile? "/tmp" "HEAD:bad" "f.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.dirtyWorktree`. -/
def err_git_showFile_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.nothingToCommit`. -/
def err_git_showFile_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.branchInUse`. -/
def err_git_showFile_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.alreadyExists`. -/
def err_git_showFile_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.notFound`. -/
def err_git_showFile_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.conflict`. -/
def err_git_showFile_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.timeout`. -/
def err_git_showFile_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.commandFailed`. -/
def err_git_showFile_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.showFile? p "HEAD" "f.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.parseError`. -/
def err_git_showFile_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.notARepo`. -/
def err_git_init_notARepo : IO Unit :=
  runMockErr .notARepo (fun api => api.init "/mock/repo" false none)

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidRef`. -/
def err_git_init_invalidRef : IO Unit :=
  withTempDirIO fun root => do assertErrKind (← Git.init (root ++ "/repo") false (some badRef)) .invalidRef "init invalidRef"

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidPath`. -/
def err_git_init_invalidPath : IO Unit :=
  runRealErr .invalidPath "init invalidPath" (Git.init "")

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidInput`. -/
def err_git_init_invalidInput : IO Unit :=
  runRealErr .invalidInput "init invalidInput" (Git.init hugeInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.dirtyWorktree`. -/
def err_git_init_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.nothingToCommit`. -/
def err_git_init_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.branchInUse`. -/
def err_git_init_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.alreadyExists`. -/
def err_git_init_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.notFound`. -/
def err_git_init_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.conflict`. -/
def err_git_init_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.timeout`. -/
def err_git_init_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.init "/mock/repo" false none)

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.commandFailed`. -/
def err_git_init_commandFailed : IO Unit :=
  runRealInitOnFileErr

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.notARepo`. -/
def err_git_clone_notARepo : IO Unit :=
  runMockErr .notARepo (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.invalidRef`. -/
def err_git_clone_invalidRef : IO Unit :=
  withTempDirIO fun root => do let src := root ++ "/src"; let _ ← initCommittedRepo src; assertErrKind (← Git.clone src (root ++ "/dst") { branch? := some badRef.raw }) .invalidRef "clone invalidRef"

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.invalidInput`. -/
def err_git_clone_invalidInput : IO Unit :=
  runRealErr .invalidInput "clone invalidInput" (Git.clone "-evil" "/tmp/dst")

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.dirtyWorktree`. -/
def err_git_clone_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.nothingToCommit`. -/
def err_git_clone_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.branchInUse`. -/
def err_git_clone_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.alreadyExists`. -/
def err_git_clone_alreadyExists : IO Unit :=
  runRealCloneAlreadyExistsErr

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.notFound`. -/
def err_git_clone_notFound : IO Unit :=
  runRealCloneNotFoundErr

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.conflict`. -/
def err_git_clone_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.timeout`. -/
def err_git_clone_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.commandFailed`. -/
def err_git_clone_commandFailed : IO Unit :=
  runRealCloneNonRepoErr

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.notARepo`. -/
def err_git_add_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.add p #["f.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.invalidRef`. -/
def err_git_add_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.invalidPath`. -/
def err_git_add_invalidPath : IO Unit :=
  runRealErr .invalidPath "add invalidPath" (Git.add "" #["f.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.invalidInput`. -/
def err_git_add_invalidInput : IO Unit :=
  runRealErr .invalidInput "add invalidInput" (Git.add "/tmp" #[] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.dirtyWorktree`. -/
def err_git_add_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.nothingToCommit`. -/
def err_git_add_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.branchInUse`. -/
def err_git_add_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.alreadyExists`. -/
def err_git_add_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.notFound`. -/
def err_git_add_notFound : IO Unit :=
  runRealCommittedErr .notFound "add notFound" (fun repo _ => Git.add repo #["missing.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.conflict`. -/
def err_git_add_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.timeout`. -/
def err_git_add_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.commandFailed`. -/
def err_git_add_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.add p #["f.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.notARepo`. -/
def err_git_commit_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.commit p (testAuthorOpts "m"))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.invalidRef`. -/
def err_git_commit_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.invalidPath`. -/
def err_git_commit_invalidPath : IO Unit :=
  runRealErr .invalidPath "commit invalidPath" (Git.commit "" { message := "m" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.invalidInput`. -/
def err_git_commit_invalidInput : IO Unit :=
  runRealErr .invalidInput "commit invalidInput" (Git.commit "/tmp" { message := "" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.dirtyWorktree`. -/
def err_git_commit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.nothingToCommit`. -/
def err_git_commit_nothingToCommit : IO Unit :=
  runRealCommittedErr .nothingToCommit "commit nothingToCommit" (fun repo _ => Git.commit repo (testAuthorOpts "empty" false))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.branchInUse`. -/
def err_git_commit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.alreadyExists`. -/
def err_git_commit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.notFound`. -/
def err_git_commit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.conflict`. -/
def err_git_commit_conflict : IO Unit :=
  runRealCommitConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.timeout`. -/
def err_git_commit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.commandFailed`. -/
def err_git_commit_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.commit p (testAuthorOpts "m"))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.parseError`. -/
def err_git_commit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.notARepo`. -/
def err_git_createBranch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.createBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidRef`. -/
def err_git_createBranch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "createBranch invalidRef" (fun repo _ => Git.createBranch repo badRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidPath`. -/
def err_git_createBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "createBranch invalidPath" (Git.createBranch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidInput`. -/
def err_git_createBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "createBranch invalidInput" (Git.createBranch "/tmp" mainRef (some "HEAD:bad"))

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.dirtyWorktree`. -/
def err_git_createBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.nothingToCommit`. -/
def err_git_createBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.branchInUse`. -/
def err_git_createBranch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.alreadyExists`. -/
def err_git_createBranch_alreadyExists : IO Unit :=
  runRealCommittedErr .alreadyExists "createBranch alreadyExists" (fun repo _ => Git.createBranch repo mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.notFound`. -/
def err_git_createBranch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.conflict`. -/
def err_git_createBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.timeout`. -/
def err_git_createBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.commandFailed`. -/
def err_git_createBranch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.createBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.notARepo`. -/
def err_git_deleteBranch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.deleteBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidRef`. -/
def err_git_deleteBranch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "deleteBranch invalidRef" (fun repo _ => Git.deleteBranch repo badRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidPath`. -/
def err_git_deleteBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "deleteBranch invalidPath" (Git.deleteBranch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidInput`. -/
def err_git_deleteBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "deleteBranch invalidInput" (Git.deleteBranch longInvalidPath mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.dirtyWorktree`. -/
def err_git_deleteBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.nothingToCommit`. -/
def err_git_deleteBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.branchInUse`. -/
def err_git_deleteBranch_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "deleteBranch branchInUse" (fun repo _ => Git.deleteBranch repo mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.alreadyExists`. -/
def err_git_deleteBranch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.notFound`. -/
def err_git_deleteBranch_notFound : IO Unit :=
  runRealCommittedErr .notFound "deleteBranch notFound" (fun repo _ => Git.deleteBranch repo missingRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.conflict`. -/
def err_git_deleteBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.timeout`. -/
def err_git_deleteBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.commandFailed`. -/
def err_git_deleteBranch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.deleteBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.notARepo`. -/
def err_git_checkout_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.checkout p (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidRef`. -/
def err_git_checkout_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "checkout invalidRef" (fun repo _ => Git.checkout repo (.branch missingRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidPath`. -/
def err_git_checkout_invalidPath : IO Unit :=
  runRealErr .invalidPath "checkout invalidPath" (Git.checkout "" (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidInput`. -/
def err_git_checkout_invalidInput : IO Unit :=
  runRealErr .invalidInput "checkout invalidInput" (Git.checkout "/tmp" (.ref "HEAD:bad"))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.dirtyWorktree`. -/
def err_git_checkout_dirtyWorktree : IO Unit :=
  runRealCheckoutDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.nothingToCommit`. -/
def err_git_checkout_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.branchInUse`. -/
def err_git_checkout_branchInUse : IO Unit :=
  runRealCheckoutBranchInUseErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.alreadyExists`. -/
def err_git_checkout_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.notFound`. -/
def err_git_checkout_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.conflict`. -/
def err_git_checkout_conflict : IO Unit :=
  runRealCheckoutConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.timeout`. -/
def err_git_checkout_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.commandFailed`. -/
def err_git_checkout_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.checkout p (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.notARepo`. -/
def err_git_switch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.switch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidRef`. -/
def err_git_switch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "switch invalidRef" (fun repo _ => Git.switch repo missingRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidPath`. -/
def err_git_switch_invalidPath : IO Unit :=
  runRealErr .invalidPath "switch invalidPath" (Git.switch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidInput`. -/
def err_git_switch_invalidInput : IO Unit :=
  runRealErr .invalidInput "switch invalidInput" (Git.switch "/tmp" mainRef false (some "HEAD"))

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.dirtyWorktree`. -/
def err_git_switch_dirtyWorktree : IO Unit :=
  runRealSwitchDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.nothingToCommit`. -/
def err_git_switch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.branchInUse`. -/
def err_git_switch_branchInUse : IO Unit :=
  runRealSwitchBranchInUseErr

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.alreadyExists`. -/
def err_git_switch_alreadyExists : IO Unit :=
  runRealCommittedErr .alreadyExists "switch alreadyExists" (fun repo _ => Git.switch repo mainRef true)

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.notFound`. -/
def err_git_switch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.conflict`. -/
def err_git_switch_conflict : IO Unit :=
  runRealSwitchConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.timeout`. -/
def err_git_switch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.commandFailed`. -/
def err_git_switch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.switch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.notARepo`. -/
def err_git_reset_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.reset p .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidRef`. -/
def err_git_reset_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "reset invalidRef" (fun repo _ => Git.reset repo .hard zeroCid.hex)

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidPath`. -/
def err_git_reset_invalidPath : IO Unit :=
  runRealErr .invalidPath "reset invalidPath" (Git.reset "" .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidInput`. -/
def err_git_reset_invalidInput : IO Unit :=
  runRealErr .invalidInput "reset invalidInput" (Git.reset "/tmp" .hard "HEAD:bad")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.dirtyWorktree`. -/
def err_git_reset_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.nothingToCommit`. -/
def err_git_reset_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.branchInUse`. -/
def err_git_reset_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.alreadyExists`. -/
def err_git_reset_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.notFound`. -/
def err_git_reset_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.conflict`. -/
def err_git_reset_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.timeout`. -/
def err_git_reset_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.commandFailed`. -/
def err_git_reset_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.reset p .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.notARepo`. -/
def err_git_fetch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.fetch p "origin")

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.invalidRef`. -/
def err_git_fetch_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.invalidPath`. -/
def err_git_fetch_invalidPath : IO Unit :=
  runRealErr .invalidPath "fetch invalidPath" (Git.fetch "" "origin")

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.invalidInput`. -/
def err_git_fetch_invalidInput : IO Unit :=
  runRealErr .invalidInput "fetch invalidInput" (Git.fetch "/tmp" "--upload-pack=evil")

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.dirtyWorktree`. -/
def err_git_fetch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.nothingToCommit`. -/
def err_git_fetch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.branchInUse`. -/
def err_git_fetch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.alreadyExists`. -/
def err_git_fetch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.notFound`. -/
def err_git_fetch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.conflict`. -/
def err_git_fetch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.timeout`. -/
def err_git_fetch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.commandFailed`. -/
def err_git_fetch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.fetch p "origin")

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.notARepo`. -/
def err_git_worktreeAdd_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.worktreeAdd p { path := p ++ "/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidRef`. -/
def err_git_worktreeAdd_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "worktreeAdd invalidRef" (fun repo _ => Git.worktreeAdd repo { path := repo ++ "-wt", target? := some "no-such-ref" })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidPath`. -/
def err_git_worktreeAdd_invalidPath : IO Unit :=
  runRealErr .invalidPath "worktreeAdd invalidPath" (Git.worktreeAdd "" { path := "/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidInput`. -/
def err_git_worktreeAdd_invalidInput : IO Unit :=
  runRealErr .invalidInput "worktreeAdd invalidInput" (Git.worktreeAdd "/tmp" { path := "/tmp/wt", detach := true, newBranch? := some mainRef })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.dirtyWorktree`. -/
def err_git_worktreeAdd_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.nothingToCommit`. -/
def err_git_worktreeAdd_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.branchInUse`. -/
def err_git_worktreeAdd_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "worktreeAdd branchInUse" (fun repo _ => Git.worktreeAdd repo { path := repo ++ "-wt", target? := some mainRef.raw })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.alreadyExists`. -/
def err_git_worktreeAdd_alreadyExists : IO Unit :=
  runRealWorktreeAddAlreadyExistsErr

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.notFound`. -/
def err_git_worktreeAdd_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.conflict`. -/
def err_git_worktreeAdd_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.timeout`. -/
def err_git_worktreeAdd_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.commandFailed`. -/
def err_git_worktreeAdd_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.worktreeAdd p { path := p ++ "-wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.notARepo`. -/
def err_git_worktreeRemove_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.worktreeRemove p (p ++ "/wt"))

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidRef`. -/
def err_git_worktreeRemove_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidPath`. -/
def err_git_worktreeRemove_invalidPath : IO Unit :=
  runRealErr .invalidPath "worktreeRemove invalidPath" (Git.worktreeRemove "" "/wt")

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidInput`. -/
def err_git_worktreeRemove_invalidInput : IO Unit :=
  runRealErr .invalidInput "worktreeRemove invalidInput" (Git.worktreeRemove longInvalidPath "/tmp/wt")

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.dirtyWorktree`. -/
def err_git_worktreeRemove_dirtyWorktree : IO Unit :=
  runRealWorktreeRemoveDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.nothingToCommit`. -/
def err_git_worktreeRemove_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.branchInUse`. -/
def err_git_worktreeRemove_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.alreadyExists`. -/
def err_git_worktreeRemove_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.notFound`. -/
def err_git_worktreeRemove_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.conflict`. -/
def err_git_worktreeRemove_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.timeout`. -/
def err_git_worktreeRemove_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.commandFailed`. -/
def err_git_worktreeRemove_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.worktreeRemove p (p ++ "-wt"))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.notARepo`. -/
def err_git_withWorktree_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.withWorktree p { path := p ++ "/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidRef`. -/
def err_git_withWorktree_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "withWorktree invalidRef" (fun repo _ => Git.withWorktree repo { path := repo ++ "-wt", target? := some "no-such-ref" } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidPath`. -/
def err_git_withWorktree_invalidPath : IO Unit :=
  runRealErr .invalidPath "withWorktree invalidPath" (Git.withWorktree "" { path := "/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidInput`. -/
def err_git_withWorktree_invalidInput : IO Unit :=
  runRealErr .invalidInput "withWorktree invalidInput" (Git.withWorktree "/tmp" { path := "/tmp/wt", detach := true, newBranch? := some mainRef } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.dirtyWorktree`. -/
def err_git_withWorktree_dirtyWorktree : IO Unit :=
  runRealWithWorktreeDirtyErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.nothingToCommit`. -/
def err_git_withWorktree_nothingToCommit : IO Unit :=
  runRealWithWorktreeNothingToCommitErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.branchInUse`. -/
def err_git_withWorktree_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "withWorktree branchInUse" (fun repo _ => Git.withWorktree repo { path := repo ++ "-wt", target? := some mainRef.raw } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.alreadyExists`. -/
def err_git_withWorktree_alreadyExists : IO Unit :=
  runRealWithWorktreeAlreadyExistsErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.notFound`. -/
def err_git_withWorktree_notFound : IO Unit :=
  runRealWithWorktreeNotFoundErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.conflict`. -/
def err_git_withWorktree_conflict : IO Unit :=
  runRealWithWorktreeConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.withWorktree` returning `.timeout`. -/
def err_git_withWorktree_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.withWorktree "/mock/repo" { path := "/mock/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.commandFailed`. -/
def err_git_withWorktree_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.withWorktree p { path := p ++ "-wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.parseError`. -/
def err_git_withWorktree_parseError : IO Unit :=
  runRealWithWorktreeParseError

set_option maxRecDepth 2048 in
/-- Registered error-coverage tests for `LeanSwe.Git`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  List.toArray (
    { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidRef", mode := .mocked, run := err_git_isRepo_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidPath", mode := .real, run := err_git_isRepo_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidInput", mode := .real, run := err_git_isRepo_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_dirtyWorktree", mode := .mocked, run := err_git_isRepo_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_nothingToCommit", mode := .mocked, run := err_git_isRepo_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_branchInUse", mode := .mocked, run := err_git_isRepo_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_alreadyExists", mode := .mocked, run := err_git_isRepo_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_notFound", mode := .mocked, run := err_git_isRepo_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_conflict", mode := .mocked, run := err_git_isRepo_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_timeout", mode := .mocked, run := err_git_isRepo_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_commandFailed", mode := .real, run := err_git_isRepo_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notARepo", mode := .real, run := err_git_repoRoot_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidRef", mode := .mocked, run := err_git_repoRoot_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidPath", mode := .real, run := err_git_repoRoot_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidInput", mode := .real, run := err_git_repoRoot_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_dirtyWorktree", mode := .mocked, run := err_git_repoRoot_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_nothingToCommit", mode := .mocked, run := err_git_repoRoot_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_branchInUse", mode := .mocked, run := err_git_repoRoot_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_alreadyExists", mode := .mocked, run := err_git_repoRoot_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notFound", mode := .mocked, run := err_git_repoRoot_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_conflict", mode := .mocked, run := err_git_repoRoot_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_timeout", mode := .mocked, run := err_git_repoRoot_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_commandFailed", mode := .real, run := err_git_repoRoot_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_parseError", mode := .real, run := err_git_repoRoot_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_notARepo", mode := .real, run := err_git_commonDir_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidRef", mode := .mocked, run := err_git_commonDir_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidPath", mode := .real, run := err_git_commonDir_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidInput", mode := .real, run := err_git_commonDir_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_dirtyWorktree", mode := .mocked, run := err_git_commonDir_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_nothingToCommit", mode := .mocked, run := err_git_commonDir_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_branchInUse", mode := .mocked, run := err_git_commonDir_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_alreadyExists", mode := .mocked, run := err_git_commonDir_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_notFound", mode := .mocked, run := err_git_commonDir_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_conflict", mode := .mocked, run := err_git_commonDir_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_timeout", mode := .mocked, run := err_git_commonDir_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_commandFailed", mode := .real, run := err_git_commonDir_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_parseError", mode := .real, run := err_git_commonDir_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_notARepo", mode := .real, run := err_git_headCommit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidRef", mode := .mocked, run := err_git_headCommit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidPath", mode := .real, run := err_git_headCommit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidInput", mode := .real, run := err_git_headCommit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_dirtyWorktree", mode := .mocked, run := err_git_headCommit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_nothingToCommit", mode := .mocked, run := err_git_headCommit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_branchInUse", mode := .mocked, run := err_git_headCommit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_alreadyExists", mode := .mocked, run := err_git_headCommit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_notFound", mode := .mocked, run := err_git_headCommit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_conflict", mode := .mocked, run := err_git_headCommit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_timeout", mode := .mocked, run := err_git_headCommit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_commandFailed", mode := .real, run := err_git_headCommit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_parseError", mode := .mocked, run := err_git_headCommit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_notARepo", mode := .real, run := err_git_headBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidRef", mode := .mocked, run := err_git_headBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidPath", mode := .real, run := err_git_headBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidInput", mode := .real, run := err_git_headBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_dirtyWorktree", mode := .mocked, run := err_git_headBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_nothingToCommit", mode := .mocked, run := err_git_headBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_branchInUse", mode := .mocked, run := err_git_headBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_alreadyExists", mode := .mocked, run := err_git_headBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_notFound", mode := .mocked, run := err_git_headBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_conflict", mode := .mocked, run := err_git_headBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_timeout", mode := .mocked, run := err_git_headBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_commandFailed", mode := .real, run := err_git_headBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_parseError", mode := .mocked, run := err_git_headBranch_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_notARepo", mode := .real, run := err_git_headState_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidRef", mode := .mocked, run := err_git_headState_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidPath", mode := .real, run := err_git_headState_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidInput", mode := .real, run := err_git_headState_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_dirtyWorktree", mode := .mocked, run := err_git_headState_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_nothingToCommit", mode := .mocked, run := err_git_headState_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_branchInUse", mode := .mocked, run := err_git_headState_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_alreadyExists", mode := .mocked, run := err_git_headState_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_notFound", mode := .mocked, run := err_git_headState_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_conflict", mode := .mocked, run := err_git_headState_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_timeout", mode := .mocked, run := err_git_headState_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_commandFailed", mode := .real, run := err_git_headState_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_parseError", mode := .mocked, run := err_git_headState_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notARepo", mode := .real, run := err_git_revParseCommit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidRef", mode := .real, run := err_git_revParseCommit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidPath", mode := .real, run := err_git_revParseCommit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidInput", mode := .real, run := err_git_revParseCommit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_dirtyWorktree", mode := .mocked, run := err_git_revParseCommit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_nothingToCommit", mode := .mocked, run := err_git_revParseCommit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_branchInUse", mode := .mocked, run := err_git_revParseCommit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_alreadyExists", mode := .mocked, run := err_git_revParseCommit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notFound", mode := .mocked, run := err_git_revParseCommit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_conflict", mode := .mocked, run := err_git_revParseCommit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_timeout", mode := .mocked, run := err_git_revParseCommit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_commandFailed", mode := .real, run := err_git_revParseCommit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_parseError", mode := .mocked, run := err_git_revParseCommit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notARepo", mode := .real, run := err_git_isAncestor_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidRef", mode := .real, run := err_git_isAncestor_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidPath", mode := .real, run := err_git_isAncestor_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidInput", mode := .real, run := err_git_isAncestor_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_dirtyWorktree", mode := .mocked, run := err_git_isAncestor_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_nothingToCommit", mode := .mocked, run := err_git_isAncestor_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_branchInUse", mode := .mocked, run := err_git_isAncestor_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_alreadyExists", mode := .mocked, run := err_git_isAncestor_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notFound", mode := .mocked, run := err_git_isAncestor_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_conflict", mode := .mocked, run := err_git_isAncestor_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_timeout", mode := .mocked, run := err_git_isAncestor_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_commandFailed", mode := .real, run := err_git_isAncestor_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notARepo", mode := .real, run := err_git_mergeBase_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidRef", mode := .real, run := err_git_mergeBase_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidPath", mode := .real, run := err_git_mergeBase_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidInput", mode := .real, run := err_git_mergeBase_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_dirtyWorktree", mode := .mocked, run := err_git_mergeBase_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_nothingToCommit", mode := .mocked, run := err_git_mergeBase_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_branchInUse", mode := .mocked, run := err_git_mergeBase_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_alreadyExists", mode := .mocked, run := err_git_mergeBase_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notFound", mode := .mocked, run := err_git_mergeBase_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_conflict", mode := .mocked, run := err_git_mergeBase_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_timeout", mode := .mocked, run := err_git_mergeBase_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_commandFailed", mode := .real, run := err_git_mergeBase_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_parseError", mode := .mocked, run := err_git_mergeBase_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_notARepo", mode := .real, run := err_git_status_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidRef", mode := .mocked, run := err_git_status_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidPath", mode := .real, run := err_git_status_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidInput", mode := .real, run := err_git_status_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_dirtyWorktree", mode := .mocked, run := err_git_status_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_nothingToCommit", mode := .mocked, run := err_git_status_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_branchInUse", mode := .mocked, run := err_git_status_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_alreadyExists", mode := .mocked, run := err_git_status_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_notFound", mode := .mocked, run := err_git_status_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_conflict", mode := .mocked, run := err_git_status_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_timeout", mode := .mocked, run := err_git_status_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_commandFailed", mode := .real, run := err_git_status_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_parseError", mode := .real, run := err_git_status_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notARepo", mode := .real, run := err_git_diffNameStatus_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidRef", mode := .real, run := err_git_diffNameStatus_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidPath", mode := .real, run := err_git_diffNameStatus_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidInput", mode := .real, run := err_git_diffNameStatus_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_dirtyWorktree", mode := .mocked, run := err_git_diffNameStatus_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_nothingToCommit", mode := .mocked, run := err_git_diffNameStatus_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_branchInUse", mode := .mocked, run := err_git_diffNameStatus_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_alreadyExists", mode := .mocked, run := err_git_diffNameStatus_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notFound", mode := .mocked, run := err_git_diffNameStatus_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_conflict", mode := .mocked, run := err_git_diffNameStatus_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_timeout", mode := .mocked, run := err_git_diffNameStatus_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_commandFailed", mode := .real, run := err_git_diffNameStatus_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_parseError", mode := .real, run := err_git_diffNameStatus_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notARepo", mode := .real, run := err_git_listWorktrees_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidRef", mode := .mocked, run := err_git_listWorktrees_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidPath", mode := .real, run := err_git_listWorktrees_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidInput", mode := .real, run := err_git_listWorktrees_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_dirtyWorktree", mode := .mocked, run := err_git_listWorktrees_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_nothingToCommit", mode := .mocked, run := err_git_listWorktrees_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_branchInUse", mode := .mocked, run := err_git_listWorktrees_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_alreadyExists", mode := .mocked, run := err_git_listWorktrees_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notFound", mode := .mocked, run := err_git_listWorktrees_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_conflict", mode := .mocked, run := err_git_listWorktrees_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_timeout", mode := .mocked, run := err_git_listWorktrees_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_commandFailed", mode := .real, run := err_git_listWorktrees_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_parseError", mode := .real, run := err_git_listWorktrees_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_notARepo", mode := .real, run := err_git_showFile_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidRef", mode := .real, run := err_git_showFile_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidPath", mode := .real, run := err_git_showFile_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidInput", mode := .real, run := err_git_showFile_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_dirtyWorktree", mode := .mocked, run := err_git_showFile_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_nothingToCommit", mode := .mocked, run := err_git_showFile_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_branchInUse", mode := .mocked, run := err_git_showFile_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_alreadyExists", mode := .mocked, run := err_git_showFile_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_notFound", mode := .mocked, run := err_git_showFile_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_conflict", mode := .mocked, run := err_git_showFile_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_timeout", mode := .mocked, run := err_git_showFile_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_commandFailed", mode := .real, run := err_git_showFile_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_parseError", mode := .mocked, run := err_git_showFile_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_notARepo", mode := .mocked, run := err_git_init_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidRef", mode := .real, run := err_git_init_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidPath", mode := .real, run := err_git_init_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidInput", mode := .real, run := err_git_init_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_dirtyWorktree", mode := .mocked, run := err_git_init_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_nothingToCommit", mode := .mocked, run := err_git_init_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_branchInUse", mode := .mocked, run := err_git_init_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_alreadyExists", mode := .mocked, run := err_git_init_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_notFound", mode := .mocked, run := err_git_init_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_conflict", mode := .mocked, run := err_git_init_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_timeout", mode := .mocked, run := err_git_init_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_commandFailed", mode := .real, run := err_git_init_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_notARepo", mode := .mocked, run := err_git_clone_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_invalidRef", mode := .real, run := err_git_clone_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_invalidInput", mode := .real, run := err_git_clone_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_dirtyWorktree", mode := .mocked, run := err_git_clone_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_nothingToCommit", mode := .mocked, run := err_git_clone_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_branchInUse", mode := .mocked, run := err_git_clone_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_alreadyExists", mode := .real, run := err_git_clone_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_notFound", mode := .real, run := err_git_clone_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_conflict", mode := .mocked, run := err_git_clone_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_timeout", mode := .mocked, run := err_git_clone_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_commandFailed", mode := .real, run := err_git_clone_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_notARepo", mode := .real, run := err_git_add_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidRef", mode := .mocked, run := err_git_add_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidPath", mode := .real, run := err_git_add_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidInput", mode := .real, run := err_git_add_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_dirtyWorktree", mode := .mocked, run := err_git_add_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_nothingToCommit", mode := .mocked, run := err_git_add_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_branchInUse", mode := .mocked, run := err_git_add_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_alreadyExists", mode := .mocked, run := err_git_add_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_notFound", mode := .real, run := err_git_add_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_conflict", mode := .mocked, run := err_git_add_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_timeout", mode := .mocked, run := err_git_add_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_commandFailed", mode := .real, run := err_git_add_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_notARepo", mode := .real, run := err_git_commit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidRef", mode := .mocked, run := err_git_commit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidPath", mode := .real, run := err_git_commit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidInput", mode := .real, run := err_git_commit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_dirtyWorktree", mode := .mocked, run := err_git_commit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_nothingToCommit", mode := .real, run := err_git_commit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_branchInUse", mode := .mocked, run := err_git_commit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_alreadyExists", mode := .mocked, run := err_git_commit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_notFound", mode := .mocked, run := err_git_commit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_conflict", mode := .real, run := err_git_commit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_timeout", mode := .mocked, run := err_git_commit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_commandFailed", mode := .real, run := err_git_commit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_parseError", mode := .mocked, run := err_git_commit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_notARepo", mode := .real, run := err_git_createBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidRef", mode := .real, run := err_git_createBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidPath", mode := .real, run := err_git_createBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidInput", mode := .real, run := err_git_createBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_dirtyWorktree", mode := .mocked, run := err_git_createBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_nothingToCommit", mode := .mocked, run := err_git_createBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_branchInUse", mode := .mocked, run := err_git_createBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_alreadyExists", mode := .real, run := err_git_createBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_notFound", mode := .mocked, run := err_git_createBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_conflict", mode := .mocked, run := err_git_createBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_timeout", mode := .mocked, run := err_git_createBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_commandFailed", mode := .real, run := err_git_createBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notARepo", mode := .real, run := err_git_deleteBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidRef", mode := .real, run := err_git_deleteBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidPath", mode := .real, run := err_git_deleteBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidInput", mode := .real, run := err_git_deleteBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_dirtyWorktree", mode := .mocked, run := err_git_deleteBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_nothingToCommit", mode := .mocked, run := err_git_deleteBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_branchInUse", mode := .real, run := err_git_deleteBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_alreadyExists", mode := .mocked, run := err_git_deleteBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notFound", mode := .real, run := err_git_deleteBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_conflict", mode := .mocked, run := err_git_deleteBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_timeout", mode := .mocked, run := err_git_deleteBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_commandFailed", mode := .real, run := err_git_deleteBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_notARepo", mode := .real, run := err_git_checkout_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidRef", mode := .real, run := err_git_checkout_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidPath", mode := .real, run := err_git_checkout_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidInput", mode := .real, run := err_git_checkout_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_dirtyWorktree", mode := .real, run := err_git_checkout_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_nothingToCommit", mode := .mocked, run := err_git_checkout_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_branchInUse", mode := .real, run := err_git_checkout_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_alreadyExists", mode := .mocked, run := err_git_checkout_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_notFound", mode := .mocked, run := err_git_checkout_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_conflict", mode := .real, run := err_git_checkout_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_timeout", mode := .mocked, run := err_git_checkout_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_commandFailed", mode := .real, run := err_git_checkout_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_notARepo", mode := .real, run := err_git_switch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidRef", mode := .real, run := err_git_switch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidPath", mode := .real, run := err_git_switch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidInput", mode := .real, run := err_git_switch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_dirtyWorktree", mode := .real, run := err_git_switch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_nothingToCommit", mode := .mocked, run := err_git_switch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_branchInUse", mode := .real, run := err_git_switch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_alreadyExists", mode := .real, run := err_git_switch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_notFound", mode := .mocked, run := err_git_switch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_conflict", mode := .real, run := err_git_switch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_timeout", mode := .mocked, run := err_git_switch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_commandFailed", mode := .real, run := err_git_switch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_notARepo", mode := .real, run := err_git_reset_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidRef", mode := .real, run := err_git_reset_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidPath", mode := .real, run := err_git_reset_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidInput", mode := .real, run := err_git_reset_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_dirtyWorktree", mode := .mocked, run := err_git_reset_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_nothingToCommit", mode := .mocked, run := err_git_reset_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_branchInUse", mode := .mocked, run := err_git_reset_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_alreadyExists", mode := .mocked, run := err_git_reset_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_notFound", mode := .mocked, run := err_git_reset_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_conflict", mode := .mocked, run := err_git_reset_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_timeout", mode := .mocked, run := err_git_reset_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_commandFailed", mode := .real, run := err_git_reset_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_notARepo", mode := .real, run := err_git_fetch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidRef", mode := .mocked, run := err_git_fetch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidPath", mode := .real, run := err_git_fetch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidInput", mode := .real, run := err_git_fetch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_dirtyWorktree", mode := .mocked, run := err_git_fetch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_nothingToCommit", mode := .mocked, run := err_git_fetch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_branchInUse", mode := .mocked, run := err_git_fetch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_alreadyExists", mode := .mocked, run := err_git_fetch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_notFound", mode := .mocked, run := err_git_fetch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_conflict", mode := .mocked, run := err_git_fetch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_timeout", mode := .mocked, run := err_git_fetch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_commandFailed", mode := .real, run := err_git_fetch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notARepo", mode := .real, run := err_git_worktreeAdd_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidRef", mode := .real, run := err_git_worktreeAdd_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidPath", mode := .real, run := err_git_worktreeAdd_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidInput", mode := .real, run := err_git_worktreeAdd_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_dirtyWorktree", mode := .mocked, run := err_git_worktreeAdd_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_nothingToCommit", mode := .mocked, run := err_git_worktreeAdd_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_branchInUse", mode := .real, run := err_git_worktreeAdd_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_alreadyExists", mode := .real, run := err_git_worktreeAdd_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notFound", mode := .mocked, run := err_git_worktreeAdd_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_conflict", mode := .mocked, run := err_git_worktreeAdd_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_timeout", mode := .mocked, run := err_git_worktreeAdd_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_commandFailed", mode := .real, run := err_git_worktreeAdd_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notARepo", mode := .real, run := err_git_worktreeRemove_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidRef", mode := .mocked, run := err_git_worktreeRemove_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidPath", mode := .real, run := err_git_worktreeRemove_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidInput", mode := .real, run := err_git_worktreeRemove_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_dirtyWorktree", mode := .real, run := err_git_worktreeRemove_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_nothingToCommit", mode := .mocked, run := err_git_worktreeRemove_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_branchInUse", mode := .mocked, run := err_git_worktreeRemove_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_alreadyExists", mode := .mocked, run := err_git_worktreeRemove_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notFound", mode := .mocked, run := err_git_worktreeRemove_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_conflict", mode := .mocked, run := err_git_worktreeRemove_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_timeout", mode := .mocked, run := err_git_worktreeRemove_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_commandFailed", mode := .real, run := err_git_worktreeRemove_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notARepo", mode := .real, run := err_git_withWorktree_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidRef", mode := .real, run := err_git_withWorktree_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidPath", mode := .real, run := err_git_withWorktree_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidInput", mode := .real, run := err_git_withWorktree_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_dirtyWorktree", mode := .real, run := err_git_withWorktree_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_nothingToCommit", mode := .real, run := err_git_withWorktree_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_branchInUse", mode := .real, run := err_git_withWorktree_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_alreadyExists", mode := .real, run := err_git_withWorktree_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notFound", mode := .real, run := err_git_withWorktree_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_conflict", mode := .real, run := err_git_withWorktree_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_timeout", mode := .mocked, run := err_git_withWorktree_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_commandFailed", mode := .real, run := err_git_withWorktree_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_parseError", mode := .real, run := err_git_withWorktree_parseError }
    :: [])

private def runIntegrationSmoke : IO Unit := do
  withTempDirIO fun root => do
    let nonRepo := root ++ "/nonrepo"
    IO.FS.createDirAll nonRepo
    assertTrue (!(← assertOk (← Git.isRepo nonRepo) "isRepo nonRepo")) "nonRepo reports false"
    assertErrKind (← Git.repoRoot nonRepo) .notARepo "repoRoot nonRepo fails with notARepo"

    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare repo"
    assertTrue (← assertOk (← Git.isRepo bareDir) "isRepo bare") "bare isRepo true"
    assertErrKind (← Git.repoRoot bareDir) .notARepo "repoRoot on bare repo returns notARepo"
    let bareCommon ← assertOk (← Git.commonDir bareDir) "commonDir bare"
    let bareReal ← IO.FS.realPath bareDir
    assertTrue (bareCommon == bareReal.toString) "bare commonDir matches bare path"
    let bareWts ← assertOk (← Git.listWorktrees bareDir) "listWorktrees bare"
    assertTrue (bareWts.size == 1 && bareWts[0]!.isBare && bareWts[0]!.head? == none)
      "bare worktree list parsed without HEAD"

    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init repo"
    let repoReal := (← IO.FS.realPath repo).toString
    assertTrue (← assertOk (← Git.isRepo repo) "isRepo repo") "init repo isRepo true"
    assertTrue ((← assertOk (← Git.repoRoot repo) "repoRoot") == repoReal) "repoRoot matches realPath"
    assertTrue ((← assertOk (← Git.commonDir repo) "commonDir") == repoReal ++ "/.git")
      "commonDir matches .git"

    assertTrue ((← assertOk (← Git.headCommit? repo) "unborn headCommit?") == none) "unborn headCommit? is none"
    assertTrue ((← assertOk (← Git.headBranch? repo) "unborn headBranch?") == some mainRef)
      "unborn headBranch? is main"
    assertTrue ((← assertOk (← Git.headState repo) "unborn headState") == .attached mainRef none)
      "unborn headState is attached none"
    assertErrKind (← Git.revParseCommit repo "HEAD") .invalidRef "unborn revParseCommit HEAD fails"

    assertErrKind (← Git.commit repo (testAuthorOpts "empty" false)) .nothingToCommit
      "empty commit without allowEmpty returns nothingToCommit"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "initial empty" true)) "allowEmpty commit"
    assertTrue ((← assertOk (← Git.headCommit? repo) "headCommit? c1") == some c1) "headCommit? returns c1"
    assertTrue ((← assertOk (← Git.revParseCommit repo "HEAD") "revParseCommit HEAD") == c1)
      "revParseCommit HEAD returns c1"

    IO.FS.createDirAll (repo ++ "/subdir")
    IO.FS.writeFile (repo ++ "/subdir/nested.txt") "nested\n"
    IO.FS.writeFile (repo ++ "/a b.txt") "hello world\n"
    assertOk (← Git.add repo #["a b.txt", "subdir/nested.txt"] false) "add explicit files"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "add files" false)) "commit c2"
    let blob? ← assertOk (← Git.showFile? repo "HEAD" "a b.txt") "showFile? blob"
    assertTrue (blob? == some "hello world\n".toUTF8) "showFile? reads exact blob bytes"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "subdir") "showFile? tree") == none)
      "showFile? on directory tree returns none"

    let featRef ← assertOk (mkRefName "feat") "mkRefName feat"
    assertOk (← Git.switch repo featRef true (some c2.hex) false) "switch -c feat at c2"
    assertOk (← Git.switch repo featRef true (some c1.hex) true) "switch -C resets existing branch"
    assertTrue ((← assertOk (← Git.headCommit? repo) "headCommit? after switch -C") == some c1)
      "switch --force -C moved existing feat branch to c1"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout main after switch -C"
    assertOk (← Git.reset repo .hard "HEAD") "reset --hard"

    let diffFiltered ← assertOk (← Git.diffNameStatus repo c1.hex (some c2.hex) #["subdir"])
      "diffNameStatus with path filter"
    assertTrue (diffFiltered.size == 1 && diffFiltered[0]!.path == "subdir/nested.txt")
      "diffNameStatus path filter restricts output to subdir/nested.txt"

    let customMsg := "subject line\n\ndetailed body"
    let cCustom ← assertOk (← Git.commit repo
      { message := customMsg
        allowEmpty := true
        authorName := some "Alice Verifier"
        authorEmail := some "alice@verifier.invalid" }) "commit custom author/message"
    let logOut ← runProcRaw "git"
      #["log", "-1", "--format=%an|%ae|%cn|%ce|%B", cCustom.hex] (some repo)
    let logStr := (String.fromUTF8? logOut.stdout).getD ""
    assertTrue (logStr.startsWith "Alice Verifier|alice@verifier.invalid|Alice Verifier|alice@verifier.invalid|subject line\n\ndetailed body")
      "commit records exact author, committer, and cleaned message"

    assertOk (← Git.reset repo .soft c1.hex) "reset --soft to c1"
    let stAfterSoft ← assertOk (← Git.status repo) "status after reset --soft"
    assertTrue (stAfterSoft.size == 2 && stAfterSoft.all (fun e => e.indexStatus == some .added && e.worktreeStatus == none))
      "reset --soft preserves index entries as staged additions"
    assertOk (← Git.reset repo .mixed c1.hex) "reset --mixed to c1"
    let stAfterMixed ← assertOk (← Git.status repo) "status after reset --mixed"
    assertTrue (stAfterMixed.any (fun e => e.indexStatus == some .untracked))
      "reset --mixed unstages entries while preserving working tree files"
    assertOk (← Git.reset repo .hard c2.hex) "reset --hard back to c2"

    let wtForcePath := root ++ "/wt-force"
    assertOk (← Git.worktreeAdd repo { path := wtForcePath, detach := true }) "worktreeAdd detach"
    IO.FS.writeFile (wtForcePath ++ "/dirty.txt") "untracked\n"
    assertErrKind (← Git.worktreeRemove repo wtForcePath false) .dirtyWorktree
      "worktreeRemove without force rejects dirty worktree"
    assertOk (← Git.worktreeRemove repo wtForcePath true) "worktreeRemove --force removes dirty worktree"

    let wtBracketPath := root ++ "/wt-bracket"
    let bracketOk ← assertOk
      (← Git.withWorktree repo { path := wtBracketPath, detach := true } fun path => do
        let hc ← Git.headCommit? path
        pure (hc.map fun _ => path))
      "withWorktree ok"
    assertTrue (bracketOk == wtBracketPath) "withWorktree passed path"
    assertTrue ((← assertOk (← Git.listWorktrees repo) "listWorktrees after withWorktree ok").size == 1)
      "withWorktree cleaned up on ok"

    let boomErr : GitError := { kind := .invalidInput, message := "boom" }
    let bracketErr : Except GitError Unit ←
      Git.withWorktree repo { path := wtBracketPath, detach := true } fun _ =>
        pure (.error boomErr)
    assertErrKind bracketErr .invalidInput "withWorktree preserves action error"
    assertTrue ((← assertOk (← Git.listWorktrees repo) "listWorktrees after withWorktree error").size == 1)
      "withWorktree cleaned up on error"

    let shortPrefix := String.ofList (c2.hex.toList.take 7)
    let rpShortOld ← assertOk (← Git.revParseCommit repo shortPrefix) "revParseCommit resolves short SHA"
    assertTrue (rpShortOld == c2) "revParseCommit short SHA matches c2"
    assertOk (← Git.reset repo .hard shortPrefix) "reset accepts short SHA"
    assertOk (← Git.checkout repo (.ref shortPrefix) false) "checkout .ref accepts short SHA"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout back to main"
    assertOk (← Git.switch repo { raw := "short-sw" } true (some shortPrefix) false)
      "switch startPoint accepts short SHA"
    assertOk (← Git.switch repo mainRef false none false) "switch back to main"
    assertOk (← Git.deleteBranch repo { raw := "short-sw" } true) "cleanup short-sw"
    assertOk (← Git.createBranch repo { raw := "short-br" } (some shortPrefix) false)
      "createBranch startPoint accepts short SHA"
    assertOk (← Git.deleteBranch repo { raw := "short-br" } true) "cleanup short-br"
    let _ ← assertOk (← Git.diffNameStatus repo shortPrefix none #[]) "diffNameStatus accepts short SHA"
    let _ ← assertOk (← Git.diffNameStatus repo "HEAD" (some shortPrefix) #[]) "diffNameStatus revB accepts short SHA"
    let _ ← assertOk (← Git.showFile? repo shortPrefix "a b.txt") "showFile? accepts short SHA"
    let wtShortPath := root ++ "/wt-short"
    assertOk (← Git.worktreeAdd repo { path := wtShortPath, newBranch? := some { raw := "wt-sh" }, target? := some shortPrefix })
      "worktreeAdd target accepts short SHA"
    assertOk (← Git.worktreeRemove repo wtShortPath true) "cleanup wt-short"
    assertOk (← Git.deleteBranch repo { raw := "wt-sh" } true) "cleanup wt-sh"

    let forceBr : RefName := { raw := "force-target" }
    assertOk (← Git.switch repo forceBr true (some c1.hex) false) "create force-target at c1"
    IO.FS.writeFile (repo ++ "/only-ft.txt") "ft\n"
    assertOk (← Git.add repo #["only-ft.txt"] false) "stage only-ft"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "ft commit" false)) "commit ft"
    assertOk (← Git.switch repo mainRef false none false) "switch back to main"
    IO.FS.writeFile (repo ++ "/only-ft.txt") "untracked-collision\n"
    assertErrKind (← Git.switch repo forceBr false none false) .dirtyWorktree
      "switch existing without force rejects collision"
    assertOk (← Git.switch repo forceBr false none true) "switch existing with force overwrites collision"
    assertErrKind (← Git.switch repo mainRef true none false) .alreadyExists
      "switch -c on existing branch fails with alreadyExists"
    IO.FS.writeFile (repo ++ "/a b.txt") "dirty-for-ref-co\n"
    assertErrKind (← Git.checkout repo (.ref mainRef.raw) false) .dirtyWorktree
      "checkout .ref without force rejects dirty file"
    assertOk (← Git.checkout repo (.ref mainRef.raw) true) "checkout .ref with force overwrites dirty file"
    assertErrKind (← Git.deleteBranch repo forceBr false) .dirtyWorktree
      "deleteBranch without force rejects unmerged branch"
    assertOk (← Git.deleteBranch repo forceBr true) "deleteBranch with force deletes unmerged branch"

private def runExtendedParityAndGuardSmoke : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let mainRef : RefName := { raw := "main" }

    let br40Raw := String.ofList (List.replicate 40 'f')
    let br40Ref : RefName := { raw := br40Raw }
    assertOk (← Git.createBranch repo br40Ref (some c1.hex) false) "create 40-hex local branch"
    let wt40Path := root ++ "/wt-hex40"
    let wt40DupPath := root ++ "/wt-hex40-dup"
    assertOk (← Git.worktreeAdd repo { path := wt40Path, target? := some br40Raw }) "worktreeAdd attaches 40-hex branch"
    let hb40 ← assertOk (← Git.headBranch? wt40Path) "headBranch? on 40-hex worktree"
    assertTrue (hb40 == some br40Ref) "40-hex worktree attached to branch"
    assertErrKind (← Git.worktreeAdd repo { path := wt40DupPath, target? := some br40Raw }) .branchInUse
      "worktreeAdd rejects in-use 40-hex branch without force"
    assertOk (← Git.worktreeAdd repo { path := wt40DupPath, target? := some br40Raw, force := true })
      "worktreeAdd allows in-use 40-hex branch with force"
    assertOk (← Git.worktreeRemove repo wt40DupPath false) "remove duplicate 40-hex worktree"
    assertOk (← Git.worktreeRemove repo wt40Path false) "remove primary 40-hex worktree"
    assertOk (← Git.deleteBranch repo br40Ref true) "delete 40-hex local branch"

    let fetchDstDir := root ++ "/fetch-dst-qualify"
    assertOk (← Git.init fetchDstDir false (some mainRef)) "init fetchDstDir"
    IO.FS.writeFile (fetchDstDir ++ "/seed.txt") "seed\n"
    assertOk (← Git.add fetchDstDir #[] true) "stage seed"
    let _ ← assertOk (← Git.commit fetchDstDir (testAuthorOpts "seed" false)) "commit seed"
    IO.FS.writeFile (repo ++ "/f2.txt") "second\n"
    assertOk (← Git.add repo #["f2.txt"] false) "stage f2"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "commit c2"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:heads/main") false) .commandFailed
      "fetch main:heads/main refuses checked-out main"
    assertOk (← Git.fetch fetchDstDir repo (some (c1.hex ++ ":tags/qual-tag")) false)
      "fetch into tags/qual-tag"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:tags/qual-tag") false) .commandFailed
      "fetch non-force refuses clobbering existing tags/qual-tag"
    assertOk (← Git.fetch fetchDstDir repo (some "main:remotes/origin/qual") false)
      "fetch into remotes/origin/qual"
    let _ ← assertOk (← Git.revParseCommit fetchDstDir "refs/remotes/origin/qual")
      "revParseCommit refs/remotes/origin/qual"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:heads/HEAD") false) .invalidInput
      "fetch rejects unqualified heads/HEAD"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:tags/HEAD") false) .invalidInput
      "fetch rejects unqualified tags/HEAD"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:remotes/HEAD") false) .invalidInput
      "fetch rejects unqualified remotes/HEAD"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:remotes/HEAD/HEAD") false) .invalidInput
      "fetch rejects unqualified remotes/HEAD/HEAD"

    let subHeadBr : RefName := { raw := "subns/HEAD" }
    let cleanSubBr : RefName := { raw := "cleanns/ok" }
    assertOk (← Git.createBranch repo subHeadBr (some c1.hex) false) "create subns/HEAD branch"
    assertOk (← Git.createBranch repo cleanSubBr (some c1.hex) false) "create cleanns/ok branch"
    let unbornFetchDir := root ++ "/fetch-unborn-glob"
    assertOk (← Git.init unbornFetchDir false (some mainRef)) "init unbornFetchDir"
    assertErrKind (← Git.fetch unbornFetchDir repo (some "+refs/heads/subns/*:refs/heads/*") false) .commandFailed
      "fetch glob rejects HEAD-shadowing destination"
    let hcUnborn ← assertOk (← Git.headCommit? unbornFetchDir) "headCommit? stays unborn after rejected glob fetch"
    assertTrue (hcUnborn == none) "unborn HEAD preserved"
    assertOk (← Git.fetch unbornFetchDir repo (some "+refs/heads/cleanns/*:refs/heads/*") false)
      "fetch benign glob into refs/heads/*"
    let rpCleanOk ← assertOk (← Git.revParseCommit unbornFetchDir "refs/heads/ok")
      "revParseCommit refs/heads/ok after benign glob"
    assertTrue (rpCleanOk == c1) "benign glob fetched commit matches"

    let nestedTop := root ++ "/nested-top"
    let nestedMid := nestedTop ++ "/sub1"
    let nestedLeaf := nestedMid ++ "/sub2"
    IO.FS.createDirAll nestedLeaf
    assertOk (← Git.init nestedLeaf false (some mainRef)) "init nestedLeaf"
    IO.FS.writeFile (nestedLeaf ++ "/leaf.txt") "leaf\n"
    assertOk (← Git.add nestedLeaf #[] true) "add nestedLeaf"
    let _ ← assertOk (← Git.commit nestedLeaf (testAuthorOpts "leaf commit" false)) "commit nestedLeaf"
    assertOk (← Git.init nestedMid false (some mainRef)) "init nestedMid"
    assertOk (← Git.add nestedMid #[] true) "add nestedMid"
    let _ ← assertOk (← Git.commit nestedMid (testAuthorOpts "mid commit" false)) "commit nestedMid"
    assertOk (← Git.init nestedTop false (some mainRef)) "init nestedTop"
    assertOk (← Git.add nestedTop #[] true) "add nestedTop"
    let _ ← assertOk (← Git.commit nestedTop (testAuthorOpts "top commit" false)) "commit nestedTop"
    IO.FS.writeFile (nestedLeaf ++ "/untracked.txt") "untracked\n"
    let topSt ← assertOk (← Git.status nestedTop) "status on 3-level nested gitlinks"
    assertTrue (topSt.size == 1 && topSt[0]?.map (·.path) == some "sub1")
      "status reports nested untracked dirt on sub1"
    let topDf ← assertOk (← Git.diffNameStatus nestedTop "HEAD" none #[])
      "diffNameStatus on 3-level nested gitlinks"
    assertTrue topDf.isEmpty "diffNameStatus ignores untracked files in nested submodules"

    let v2Root := root ++ "/v2-checks"
    let v2Repo := v2Root ++ "/repo"
    let v2WtDef := v2Root ++ "/wt-def"
    let v2Clone := v2Root ++ "/clone"
    IO.FS.createDirAll v2Repo
    assertOk (← Git.init v2Repo false (some mainRef)) "v2 init"
    IO.FS.writeFile (v2Repo ++ "/a.txt") "v2\n"
    assertOk (← Git.add v2Repo #["a.txt"] false) "v2 add"
    let cV2 ← assertOk (← Git.commit v2Repo (testAuthorOpts "  pad  \n  \n\n\nline2 \t \r\n\n  " false)) "v2 commit"
    let catOut ← assertOk (← Git.defaultRawOps.execGit (Model.cleanGitEnv #[] #[]) { cwd := some v2Repo, args := #["cat-file", "commit", cV2.hex] }) "v2 cat-file"
    let catStr := String.fromUTF8? catOut.stdout |>.getD ""
    assertTrue (catStr.endsWith "\n\n  pad\n\nline2\n") "v2 commit message cleanup matches git -m"
    assertErrKind (← Git.commit v2Repo (testAuthorOpts "   \n" true)) .commandFailed "v2 whitespace-only allowEmpty fails"
    let shortV2 := String.ofList (cV2.hex.toList.take 7)
    let rpReflog ← assertOk (← Git.revParseCommit v2Repo "HEAD@{0}") "v2 revParse reflog"
    let rpShort ← assertOk (← Git.revParseCommit v2Repo shortV2) "v2 revParse short sha"
    assertTrue (rpReflog == cV2 && rpShort == cV2) "v2 extended revParseCommit matches commit"
    let sfReflog ← assertOk (← Git.showFile? v2Repo "HEAD@{0}" "a.txt") "v2 showFile? reflog"
    assertTrue (sfReflog == some "v2\n".toUTF8) "v2 showFile? reflog content"
    let dfTree ← assertOk (← Git.diffNameStatus v2Repo "HEAD^{tree}" none #[]) "v2 diffNameStatus tree rev"
    assertTrue dfTree.isEmpty "v2 diffNameStatus tree rev empty"
    assertErrKind (← Git.revParseCommit v2Repo "HEAD^{tree}") .invalidRef "v2 revParseCommit rejects tree object"
    assertOk (← Git.worktreeAdd v2Repo { path := v2WtDef }) "v2 default basename worktreeAdd"
    let wtDefBr ← assertOk (← Git.headBranch? v2WtDef) "v2 default basename branch"
    assertTrue (wtDefBr == some { raw := "wt-def" }) "v2 default basename branch name"
    let dwimBr : RefName := { raw := "dwim-br" }
    assertOk (← Git.createBranch v2Repo dwimBr (some cV2.hex) false) "v2 create dwim-br"
    assertOk (← Git.clone v2Repo v2Clone {}) "v2 clone"
    assertOk (← Git.checkout v2Clone (.branch dwimBr) false) "v2 remote dwim checkout"
    assertTrue ((← assertOk (← Git.headBranch? v2Clone) "v2 dwim checkout head") == some dwimBr) "v2 dwim checkout branch"
    assertOk (← Git.switch v2Clone mainRef false none false) "v2 switch main"
    assertOk (← Git.deleteBranch v2Clone dwimBr true) "v2 delete local dwim-br"
    assertOk (← Git.switch v2Clone dwimBr false none false) "v2 remote dwim switch"
    assertTrue ((← assertOk (← Git.headBranch? v2Clone) "v2 dwim switch head") == some dwimBr) "v2 dwim switch branch"
    let br40 := String.ofList (List.replicate 40 'e')
    assertOk (← Git.createBranch v2Repo { raw := br40 } (some cV2.hex) false) "v2 create 40-hex branch"
    assertOk (← Git.worktreeAdd v2Repo { path := v2Root ++ "/wt40-hold", target? := some br40 }) "v2 attach 40-hex branch"
    assertErrKind (← Git.worktreeAdd v2Repo { path := v2Root ++ "/wt40-readonly", target? := some br40 }) .branchInUse "v2 40-hex branchInUse"
    assertTrue (!(← System.FilePath.pathExists (v2Root ++ "/wt40-readonly"))) "v2 40-hex branchInUse is read-only"
    let v2Sub := v2Repo ++ "/sub"
    IO.FS.createDirAll v2Sub
    IO.FS.writeFile (v2Repo ++ "/pdot.txt") "dot1\n"
    IO.FS.writeFile (v2Sub ++ "/s.txt") "sub1\n"
    assertOk (← Git.add v2Repo #["."] false) "v2 add dot"
    let cDot ← assertOk (← Git.commit v2Repo (testAuthorOpts "dot commit" false)) "v2 commit dot"
    IO.FS.writeFile (v2Repo ++ "/pdot.txt") "dot2\n"
    IO.FS.writeFile (v2Sub ++ "/s.txt") "sub2\n"
    let dfDot ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #["."]) "v2 diff dot"
    let dfDir ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #["sub/"]) "v2 diff dir/"
    let dfAbs ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #[v2Repo ++ "/pdot.txt"]) "v2 diff abs in-repo"
    assertTrue (dfDot.size == 2) "v2 diff dot finds both files"
    assertTrue (dfDir.size == 1 && dfDir[0]?.map (·.path) == some "sub/s.txt") "v2 diff dir/ filters sub"
    assertTrue (dfAbs.size == 1 && dfAbs[0]?.map (·.path) == some "pdot.txt") "v2 diff abs in-repo filters pdot.txt"
    assertOk (← Git.add v2Repo #["sub/"] false) "v2 add dir/"
    assertOk (← Git.add v2Repo #[v2Repo ++ "/pdot.txt"] false) "v2 add abs in-repo"
    let cAbs ← assertOk (← Git.commit v2Repo (testAuthorOpts "abs+dir" false)) "v2 commit abs+dir"
    assertTrue (cAbs != cDot) "v2 abs+dir advanced commit"

/-- Execute end-to-end real `git` repository runtime verification tests for `LeanSwe.Git`. -/
def runAll : IO Unit := do
  runIntegrationSmoke
  runExtendedParityAndGuardSmoke
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Git runtime tests"

/-- Execute in-process unit probes for `LeanSwe.Git.Impl` helpers, error classification, and guard paths (`--mode full` mutation coverage). -/
def runMutateExtra : IO Unit := do
  assertTrue (Impl.asciiLower "AbC!1" == "abc!1") "asciiLower"
  assertTrue (Impl.containsSubstrCI "NoT a GiT" "fatal: NOT A GIT repo") "containsSubstrCI true"
  assertTrue (!Impl.containsSubstrCI "xyz" "abc") "containsSubstrCI false"
  assertTrue (Impl.trimTrailingNewlines "hi\r\n\n\r" == "hi") "trimTrailingNewlines"
  assertTrue (Impl.stripSingleTrailingLf "hi\r\n" == "hi\r") "stripSingleTrailingLf crlf"
  assertTrue (Impl.stripSingleTrailingLf "hi\n" == "hi") "stripSingleTrailingLf lf"
  assertTrue (Impl.stripSingleTrailingLf "hi" == "hi") "stripSingleTrailingLf plain"
  assertTrue (Impl.trimAsciiWhitespace " \t\r\n x \n\t " == "x") "trimAsciiWhitespace"
  assertTrue (Impl.ensureNonEmptyMsg "fb" "  \n " == "fb") "ensureNonEmptyMsg fallback"
  assertTrue (Impl.ensureNonEmptyMsg "fb" " ok " == "ok") "ensureNonEmptyMsg ok"

  assertTrue (Impl.decodeUtf8Lossy "abc".toUTF8 == "abc") "utf8 valid ascii"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xC2, 0x80]) == "\u0080") "utf8 2-byte min"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xDF, 0xBF]) == "\u07FF") "utf8 2-byte max"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xE0, 0xA0, 0x80]) == "\u0800") "utf8 3-byte E0 min"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xED, 0x9F, 0xBF]) == "\uD7FF") "utf8 3-byte ED max"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF0, 0x90, 0x80, 0x80]) == String.singleton (Char.ofNat 0x10000)) "utf8 4-byte F0 min"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF4, 0x8F, 0xBF, 0xBF]) == String.singleton (Char.ofNat 0x10FFFF)) "utf8 4-byte F4 max"
  let badSeqs : Array (ByteArray × String) := #[
    (ByteArray.mk #[0x80], "\uFFFD"),
    (ByteArray.mk #[0xC1, 0x80], "\uFFFD\uFFFD"),
    (ByteArray.mk #[0xC2], "\uFFFD"),
    (ByteArray.mk #[0xC2, 0x41], "\uFFFDA"),
    (ByteArray.mk #[0xE0, 0x9F, 0x80], "\uFFFD\uFFFD\uFFFD"),
    (ByteArray.mk #[0xED, 0xA0, 0x80], "\uFFFD\uFFFD\uFFFD"),
    (ByteArray.mk #[0xE2, 0x82], "\uFFFD\uFFFD"),
    (ByteArray.mk #[0xE2, 0x41, 0x80], "\uFFFDA\uFFFD"),
    (ByteArray.mk #[0xE2, 0x82, 0x41], "\uFFFD\uFFFDA"),
    (ByteArray.mk #[0xF0, 0x8F, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD\uFFFD"),
    (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD\uFFFD"),
    (ByteArray.mk #[0xF0, 0x90, 0x80], "\uFFFD\uFFFD\uFFFD"),
    (ByteArray.mk #[0xF0, 0x41, 0x80, 0x80], "\uFFFDA\uFFFD\uFFFD"),
    (ByteArray.mk #[0xF0, 0x90, 0x41, 0x80], "\uFFFD\uFFFDA\uFFFD"),
    (ByteArray.mk #[0xF0, 0x90, 0x80, 0x41], "\uFFFD\uFFFD\uFFFDA"),
    (ByteArray.mk #[0xF5, 0x80, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD\uFFFD")
  ]
  for (bs, exp) in badSeqs do
    assertTrue (Impl.decodeUtf8Lossy bs == exp) s!"decodeUtf8Lossy {repr bs.data}"
    assertErrKind (Impl.decodeUtf8Checked bs) .parseError "decodeUtf8Checked invalid"
  assertTrue ((← assertOk (Impl.decodeUtf8Checked "ok".toUTF8) "decodeUtf8Checked ok") == "ok") "decodeUtf8Checked ok"

  assertTrue ((Impl.validateExtraEnv #[("FOO", some "bar")]).isOk) "validateExtraEnv ok"
  assertErrKind (Impl.validateExtraEnv #[("", some "x")]) .invalidInput "validateExtraEnv empty key"
  assertErrKind (Impl.validateExtraEnv #[("A", some "x\x00y")]) .invalidInput "validateExtraEnv nul val"
  assertTrue ((Impl.validateCwd? none).isOk) "validateCwd none"
  assertTrue ((Impl.validateCwd? (some "/tmp")).isOk) "validateCwd /tmp"
  assertErrKind (Impl.validateCwd? (some "")) .invalidPath "validateCwd empty"
  assertErrKind (Impl.validateCwd? (some "a\x00b")) .invalidPath "validateCwd nul"

  let classifyCases : Array (String × String × GitErrorKind) := #[
    ("fatal: not a git repository (or any parent)", "", .notARepo),
    ("fatal: this operation must be run in a work tree", "", .notARepo),
    ("fatal: not allowed in a bare repository", "", .notARepo),
    ("", "nothing to commit, working tree clean\n", .nothingToCommit),
    ("no changes added to commit", "", .nothingToCommit),
    ("nothing added to commit", "", .nothingToCommit),
    ("fatal: 'feat' is already used by worktree at '/wt'", "", .branchInUse),
    ("fatal: 'feat' is already checked out at '/wt'", "", .branchInUse),
    ("error: used by worktree", "", .branchInUse),
    ("error: Your local changes would be overwritten by checkout", "", .dirtyWorktree),
    ("error: untracked working tree files would be removed by checkout", "", .dirtyWorktree),
    ("error: contains modified or untracked files", "", .dirtyWorktree),
    ("error: the branch 'not a git repository' is not fully merged", "", .dirtyWorktree),
    ("fatal: unresolved conflict", "", .conflict),
    ("CONFLICT (content): Merge conflict in conflict.txt", "", .conflict),
    ("error: fix conflicts and then commit the result", "", .conflict),
    ("error: Committing is not possible because you have unmerged files.", "", .conflict),
    ("fatal: branch 'feat' already exists", "", .alreadyExists),
    ("fatal: '/wt' is already registered", "", .alreadyExists),
    ("fatal: ambiguous argument 'foo': unknown revision", "", .invalidRef),
    ("fatal: ambiguous object name: 'refs/heads/foo'", "", .invalidRef),
    ("fatal: a branch is expected, got tag 'v1'", "", .invalidRef),
    ("fatal: not a valid object name: 'x'", "", .invalidRef),
    ("fatal: does not have any commits yet", "", .invalidRef),
    ("error: pathspec 'missing' did not match any file(s)", "", .notFound),
    ("fatal: '/x' is not a working tree", "", .notFound),
    ("fatal: couldn't find remote ref refs/heads/missing", "", .notFound),
    ("error: branch 'missing' not found", "", .notFound),
    ("fatal: cannot mkdir not a git repository: Permission denied", "", .commandFailed),
    ("fatal: cannot remove a locked working tree, lock reason: not a git repository\nuse 'remove -f -f'", "", .commandFailed),
    ("error: failed", "U\tnot a git repository.txt\n", .commandFailed),
    ("fatal: not a git repository: 'x' is not fully merged", "", .notARepo),
    ("fatal: pathspec 'sym/'not a git repository'' is beyond a symbolic link", "", .commandFailed),
    ("error: unable to index file 'bad'not a git repository'file'", "", .commandFailed),
    ("error: open(\"bad\\\"not a git repository\n\"end\"): Permission denied", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nnot a git repository\nhint: Use -f", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nhint: stop\nfatal: not a git repository", "", .notARepo),
    ("invalid reference: not a git repository", "", .invalidRef),
    ("fatal: couldn't find remote ref 'not a git repository'", "", .notFound),
    ("fatal: not a valid object name not a git repository", "", .invalidRef),
    ("error: short read while indexing not a git repository", "", .commandFailed),
    ("unable to create file /not a git repository: permission denied", "", .commandFailed),
    ("error: '\"not a git repository\"'", "", .commandFailed),
    ("error: \"'not a git repository'\"", "", .commandFailed),
    ("error: \"escaped\\\"still not a git repository\" end", "", .commandFailed),
    ("fatal: pathspec 'sym/a\nfatal: not a git repository' did not match any files\n", "", .notFound),
    ("error: cannot delete branch 'main' used by worktree at '/tmp/repoA'\n", "", .branchInUse),
    ("error: \"foo\" not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nnot a git repository", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nerror: not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nwarning: not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\n\tnot a git repository\nhint: stop\nnot a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\n\tnot a git repository", "", .commandFailed),
    ("   hint: not a git repository\nerror: failed\n", "", .commandFailed),
    ("error: failed\n\tnot a git repository\n", "", .commandFailed),
    ("not a git repository\nraw tail: Permission denied\n", "", .commandFailed),
    ("  Cloning into 'dst'...\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Preparing worktree (detached HEAD)\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("From /src\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Switched to branch 'main'\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Already on 'main'\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("HEAD is now at 1234567\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Branch 'main' set up\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("error: cannot stat 'sub/a\nfatal: not a git repository': Permission denied\n", "", .commandFailed),
    ("error: cannot lstat 'sub/a\nfatal: not a git repository': Permission denied\n", "", .commandFailed),
    ("warning: unable to unlink 'sub/a\nfatal: not a git repository': Permission denied\nerror: failed\n", "", .commandFailed),
    ("warning: could not open directory 'sub/': Permission denied\nerror: The following untracked working tree files would be overwritten by checkout:\n\ta':b.txt\nAborting\n", "", .dirtyWorktree),
    ("warning: unable to access 'sub/.gitattributes': Permission denied\nfatal: not a git repository: '/bad': Permission denied\n", "", .notARepo),
    ("warning: could not open directory 'sub/': Permission denied\nfatal: pathspec 'missing':x' did not match any files\n", "", .notFound),
    ("error: cannot stat 'sub/a': permission denied\nfatal: not a git repository': Permission denied\n", "", .commandFailed),
    ("error: would lose untracked files in 'sub'", "", .dirtyWorktree),
    ("error: local changes to the following files", "", .dirtyWorktree),
    ("error: uncommitted changes", "", .dirtyWorktree),
    ("error: Merge conflict in file.txt", "", .conflict),
    ("error: unmerged path file.txt", "", .conflict),
    ("error: 'file.txt' is unmerged", "", .conflict),
    ("error: file.txt: needs merge", "", .conflict),
    ("error: you need to resolve your current index first", "", .conflict),
    ("fatal: unknown revision", "", .invalidRef),
    ("fatal: not a valid commit name abc", "", .invalidRef),
    ("fatal: Needed a single revision", "", .invalidRef),
    ("fatal: not a valid branch point: 'abc'", "", .invalidRef),
    ("fatal: could not parse object 'abc'", "", .invalidRef),
    ("fatal: bad revision 'abc'", "", .invalidRef),
    ("fatal: bad object abc", "", .invalidRef),
    ("fatal: failed to resolve 'HEAD'", "", .invalidRef),
    ("fatal: unable to read tree abc", "", .invalidRef),
    ("fatal: reference is not a tree: abc", "", .invalidRef),
    ("fatal: '/missing' does not exist", "", .notFound),
    ("fatal: '/wt' is not a valid worktree", "", .notFound),
    ("fatal: No such file or directory", "", .notFound),
    ("", "", .commandFailed)
  ]
  for (errS, outS, expKind) in classifyCases do
    let ge := Impl.classifyError "git-test" { exitCode := 1, stdout := outS.toUTF8, stderr := errS.toUTF8 }
    assertTrue (ge.kind == expKind && !ge.message.isEmpty)
      s!"classifyError ({repr errS}, {repr outS}) expected {repr expKind}, got {repr ge}"
  let geCommitWarn := Impl.classifyError "commit" {
    exitCode := 1
    stdout := "On branch main\nnothing to commit\n".toUTF8
    stderr := "warning: could not open directory 'sub/': Permission denied\n".toUTF8 }
  assertTrue (geCommitWarn.kind == .nothingToCommit) "classifyError commit warning + stdout nothingToCommit"
  let geCommitWarn2 := Impl.classifyError "commit" {
    exitCode := 1
    stdout := "no changes added to commit\n".toUTF8
    stderr := "warning: unable to unlink 'sub/a\nfatal: spoof': Permission denied\n".toUTF8 }
  assertTrue (geCommitWarn2.kind == .nothingToCommit) "classifyError commit warning + stdout no changes added"
  let geCommitWarn3 := Impl.classifyError "commit" {
    exitCode := 1
    stdout := "nothing added to commit\n".toUTF8
    stderr := "warning: could not open directory 'sub/': Permission denied\n".toUTF8 }
  assertTrue (geCommitWarn3.kind == .nothingToCommit) "classifyError commit warning + stdout nothing added"
  let geCommitErr := Impl.classifyError "commit" {
    exitCode := 1
    stdout := "On branch main\nnothing to commit\n".toUTF8
    stderr := "error: failed\n".toUTF8 }
  assertTrue (geCommitErr.kind == .commandFailed) "classifyError commit error ignores stdout"

  assertTrue (Impl.joinProbeCwd none "a" == some "a") "joinProbeCwd none"
  assertTrue (Impl.joinProbeCwd (some "/base/") "/abs" == some "/abs") "joinProbeCwd abs"
  assertTrue (Impl.joinProbeCwd (some "/base/") "." == some "/base/") "joinProbeCwd dot"
  assertTrue (Impl.joinProbeCwd (some "/") "sub" == some "/sub") "joinProbeCwd root"
  assertTrue (Impl.joinProbeCwd (some "/a/b/") "sub" == some "/a/b/sub") "joinProbeCwd rel"

  let mkIdOps (f : Array String → GitRawRequest → Except GitError GitRawOutput) : RawGitOpsM Id :=
    { listEnv := pure (.ok #[("GIT_DIR", "/bad"), ("FOO", "bar")])
      execGit := fun _ req => f req.args req }
  let nulOps := mkIdOps (fun _ _ => .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })
  assertErrKind (Id.run (Impl.runGitRaw nulOps { args := #["status", "bad\x00arg"] })) .invalidInput "runGitRaw nul arg"
  assertErrKind (Id.run (Impl.runGitRaw nulOps { cwd := some "", args := #["status"] })) .invalidPath "runGitRaw empty cwd"
  assertErrKind (Id.run (Impl.runGitRaw nulOps { extraEnv := #[("", some "1")], args := #["status"] })) .invalidInput "runGitRaw bad env"
  let listErrOps : RawGitOpsM Id :=
    { listEnv := pure (.error { kind := .commandFailed, message := "env fail" })
      execGit := fun _ _ => .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  assertErrKind (Id.run (Impl.runGitRaw listErrOps { args := #["status"] })) .commandFailed "runGitRaw listEnv err"

  let notRepoOps := mkIdOps (fun _ _ =>
    .ok { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: not a git repository".toUTF8 })
  assertTrue (!(← assertOk (Id.run (Impl.isRepoImpl notRepoOps "/nonrepo")) "isRepo notARepo")) "isRepo notARepo false"
  assertErrKind (Id.run (Impl.headCommitImpl notRepoOps "/nonrepo")) .notARepo "headCommit notARepo"
  assertErrKind (Id.run (Impl.headBranchImpl notRepoOps "/nonrepo")) .notARepo "headBranch notARepo"
  let detachedUnbornOps := mkIdOps (fun args _ =>
    if args.toList.contains "symbolic-ref" || args.toList.contains "--verify" then
      .ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }
    else .ok { exitCode := 0, stdout := ".git\n".toUTF8, stderr := ByteArray.empty })
  assertErrKind (Id.run (Impl.headStateImpl detachedUnbornOps "/repo")) .invalidRef "headState detached no commit"
  let cid1 : CommitId := { hex := String.ofList (List.replicate 40 'a') }
  let badCid : CommitId := { hex := "bad" }
  assertErrKind (Id.run (Impl.isAncestorImpl nulOps "/repo" badCid cid1)) .invalidRef "isAncestor badCid"
  assertErrKind (Id.run (Impl.mergeBaseImpl nulOps "/repo" badCid cid1)) .invalidRef "mergeBase badCid"
  assertErrKind (Id.run (Impl.mergeBaseImpl nulOps "/repo" cid1 cid1)) .parseError "mergeBase empty stdout"
  let exit1BlankOps := mkIdOps (fun _ _ => .ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })
  assertTrue (!(← assertOk (Id.run (Impl.isAncestorImpl exit1BlankOps "/repo" cid1 cid1)) "isAncestor exit1")) "isAncestor exit1 blank"
  assertTrue ((← assertOk (Id.run (Impl.mergeBaseImpl exit1BlankOps "/repo" cid1 cid1)) "mergeBase exit1")).isNone "mergeBase exit1 blank"
  assertErrKind (Id.run (Impl.revParseCommitImpl exit1BlankOps "/repo" "HEAD")) .invalidRef "revParseCommit exit1 blank"
  assertErrKind (Id.run (Impl.createBranchImpl nulOps "/repo" { raw := "-bad" } none false)) .invalidRef "createBranch bad ref"
  assertErrKind (Id.run (Impl.deleteBranchImpl nulOps "/repo" { raw := "-bad" } false)) .invalidRef "deleteBranch bad ref"
  assertErrKind (Id.run (Impl.switchImpl nulOps "/repo" { raw := "-bad" } false none false)) .invalidRef "switch bad ref"
  assertErrKind (Id.run (Impl.checkoutImpl nulOps "/repo" (.branch { raw := "-bad" }) false)) .invalidRef "checkout bad ref"
  assertErrKind (Id.run (Impl.checkoutImpl nulOps "/repo" (.commit badCid) false)) .invalidRef "checkout bad cid"
  assertErrKind (Id.run (Impl.resetImpl nulOps "/repo" .hard "bad..rev")) .invalidInput "reset bad rev"
  assertErrKind (Id.run (Impl.fetchImpl nulOps "/repo" "-u" none false)) .invalidInput "fetch bad remote"
  assertErrKind (Id.run (Impl.fetchImpl nulOps "/repo" "origin" (some "-bad") false)) .invalidInput "fetch bad refspec"
  assertErrKind (Id.run (Impl.worktreeAddImpl nulOps "/repo" { path := "" })) .invalidPath "worktreeAdd bad path"
  assertErrKind (Id.run (Impl.worktreeAddImpl nulOps "/repo" { path := "/wt", newBranch? := some { raw := "-bad" } })) .invalidRef "worktreeAdd bad branch"
  assertErrKind (Id.run (Impl.worktreeRemoveImpl nulOps "/repo" "" false)) .invalidPath "worktreeRemove bad path"
  assertErrKind (Id.run (Impl.initImpl nulOps "/repo" false (some { raw := "-bad" }))) .invalidRef "init bad branch"
  assertErrKind (Id.run (Impl.cloneImpl nulOps "" "/dst" {})) .invalidInput "clone bad src"
  assertErrKind (Id.run (Impl.cloneImpl nulOps "/src" "" {})) .invalidInput "clone bad dst"
  assertErrKind (Id.run (Impl.cloneImpl nulOps "/src" "/dst" { branch? := some "-bad" })) .invalidRef "clone bad branch"
  assertErrKind (Id.run (Impl.commitImpl nulOps "/repo" { message := "ok", authorName := some "a\x00b" })) .invalidInput "commit bad author"
  assertErrKind (Id.run (Impl.addImpl nulOps "/repo" #[] false)) .invalidInput "add empty paths"
  assertErrKind (Id.run (Impl.addImpl nulOps "/repo" #[""] false)) .invalidPath "add empty pathspec"

  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xC3, 0xA9, 0xFF]) == "é\uFFFD") "decodeUtf8 valid 2b + invalid"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xC3, 0x41]) == "\uFFFDA") "decodeUtf8 bad 2b cont"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xE2, 0x82, 0xAC, 0xFF]) == "€\uFFFD") "decodeUtf8 valid 3b + invalid"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xE2, 0xA0, 0x80, 0xFF]) == "\u2800\uFFFD") "decodeUtf8 valid 3b b1 > 0x9F + invalid"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF1, 0x90, 0x80, 0x80, 0xFF]) == String.singleton (Char.ofNat 0x50000) ++ "\uFFFD") "decodeUtf8 valid 4b b1 > 0x8F + invalid"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xE0, 0x80, 0x80, 0xFF]) == "\uFFFD\uFFFD\uFFFD\uFFFD") "decodeUtf8 overlong 3b"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xED, 0xA0, 0x80, 0xFF]) == "\uFFFD\uFFFD\uFFFD\uFFFD") "decodeUtf8 surrogate 3b"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF0, 0x9F, 0x98, 0x80, 0xFF]) == "😀\uFFFD") "decodeUtf8 valid 4b + invalid"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF0, 0x80, 0x80, 0x80, 0xFF]) == "\uFFFD\uFFFD\uFFFD\uFFFD\uFFFD") "decodeUtf8 overlong 4b"
  assertTrue (Impl.decodeUtf8Lossy (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80, 0xFF]) == "\uFFFD\uFFFD\uFFFD\uFFFD\uFFFD") "decodeUtf8 out of range 4b"

  let nonRepoTargetOps := mkIdOps (fun args _ =>
    if args.toList.contains "rev-parse" then
      .ok { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: not a git repository".toUTF8 }
    else .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })
  assertTrue ((Id.run (Impl.cloneImpl nonRepoTargetOps "/src" "/dst" { branch? := some "main" })).isOk) "clone valid branch"
  assertTrue ((Id.run (Impl.addImpl nonRepoTargetOps "/repo" #["."] false)).isOk) "add dot delegated"
  assertTrue ((Id.run (Impl.addImpl nonRepoTargetOps "/repo" #["src/"] false)).isOk) "add dir trailing slash delegated"
  assertTrue ((Id.run (Impl.addImpl nonRepoTargetOps "/repo" #["/repo/a.txt"] false)).isOk) "add abs in-repo delegated"
  let showNotRepoOps := mkIdOps (fun args _ =>
    if args.toList.contains "cat-file" then
      .ok { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: not a git repository".toUTF8 }
    else .ok { exitCode := 0, stdout := (cid1.hex ++ "\n").toUTF8, stderr := ByteArray.empty })
  assertErrKind (Id.run (Impl.showFileImpl showNotRepoOps "/nonrepo" "HEAD" "a.txt")) .notARepo "showFile cat-file notARepo"
  let showTreeOps := mkIdOps (fun args _ =>
    if args.toList.contains "-t" then
      .ok { exitCode := 0, stdout := "tree\n".toUTF8, stderr := ByteArray.empty }
    else .ok { exitCode := 0, stdout := (cid1.hex ++ "\n").toUTF8, stderr := ByteArray.empty })
  assertTrue ((← assertOk (Id.run (Impl.showFileImpl showTreeOps "/repo" "HEAD" "dir")) "showFile tree")).isNone "showFile tree none"
  let coMissingBranchOps := mkIdOps (fun _ _ =>
    .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "error: pathspec 'v1' did not match any file(s) known to git\n".toUTF8 })
  assertErrKind (Id.run (Impl.checkoutImpl coMissingBranchOps "/repo" (.branch { raw := "v1" }) false)) .invalidRef "checkout missing branch"
  assertTrue ((Id.run (Impl.worktreeAddImpl nonRepoTargetOps "/repo" { path := "/wt" })).isOk) "worktreeAdd default basename ok"
  assertTrue ((Id.run (Impl.worktreeAddImpl nonRepoTargetOps "/repo" { path := "/wt", newBranch? := some { raw := "feat" } })).isOk) "worktreeAdd newBranch ok"
  let stdoutNotRepoExit1Ops := mkIdOps (fun args _ =>
    if args == #["rev-parse", "--git-dir"] then
      .ok { exitCode := 0, stdout := ".git\n".toUTF8, stderr := ByteArray.empty }
    else
      .ok { exitCode := 1, stdout := "fatal: not a git repository\n".toUTF8, stderr := ByteArray.empty })
  assertErrKind (Id.run (Impl.headCommitImpl stdoutNotRepoExit1Ops "/nonrepo")) .notARepo "headCommit stdout notARepo exit1"
  assertErrKind (Id.run (Impl.headBranchImpl stdoutNotRepoExit1Ops "/nonrepo")) .notARepo "headBranch stdout notARepo exit1"
  assertErrKind (Id.run (Impl.revParseCommitImpl stdoutNotRepoExit1Ops "/nonrepo" "HEAD")) .notARepo "revParseCommit stdout notARepo exit1"
  assertErrKind (Id.run (Impl.checkoutImpl stdoutNotRepoExit1Ops "/nonrepo" (.branch { raw := "main" }) false)) .notARepo "checkout show-ref stdout notARepo exit1"

  assertTrue ((Impl.classifyError "checkout"
    { exitCode := 1, stdout := ByteArray.empty
      stderr := ("error: open(\"a.txt\"): Permission denied\nerror: The following untracked working tree files would be overwritten by checkout:\n\tz\"):w.txt\nAborting\n").toUTF8 }).kind == .dirtyWorktree)
    "classifyError open span stops at diagnostic line"
  assertTrue ((Impl.classifyError "checkout"
    { exitCode := 128, stdout := ByteArray.empty
      stderr := ("warning: unable to create file a/b: Permission denied\nfatal: not a git repository: '/bad': Permission denied\n").toUTF8 }).kind == .notARepo)
    "classifyError unable-to-create span stops at diagnostic line"
  assertTrue ((Impl.classifyError "add"
    { exitCode := 128, stdout := ByteArray.empty
      stderr := ("fatal: cannot mkdir /ro/sub: Permission denied\nfatal: pathspec 'x:y' did not match any files\n").toUTF8 }).kind == .notFound)
    "classifyError cannot-mkdir span stops at diagnostic line"
  assertTrue ((Impl.classifyError "checkout"
    { exitCode := 1, stdout := ByteArray.empty
      stderr := ("warning: Remote branch old not found in upstream origin\nerror: The following untracked working tree files would be overwritten by checkout:\n\tfoo not found\nAborting\n").toUTF8 }).kind == .dirtyWorktree)
    "classifyError remote-branch span stops at diagnostic line"
  assertTrue ((Impl.classifyError "add"
    { exitCode := 1, stdout := ByteArray.empty
      stderr := ("error: open(\"not a git repository\"): Permission denied\nThe following paths are ignored by one of your .gitignore files:\nz\"):w.ign\nfatal: no files added\n").toUTF8 }).kind == .commandFailed)
    "classifyError open span stops at ignored header"

end LeanSwe.Git.RuntimeTests
