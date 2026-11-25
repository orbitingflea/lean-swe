import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

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
    ("error: the branch 'not a git repository' is not fully merged", "", .commandFailed),
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
    ("error: failed", "U\tnot a git repository.txt\n", .commandFailed),
    ("fatal: not a git repository: 'x' is not fully merged", "", .notARepo),
    ("error: pathspec 'not a git repository' did not match any file(s)", "", .notFound),
    ("fatal: branch 'already exists' not found", "", .notFound),
    ("error: unable to index file 'not a git repository'", "", .commandFailed),
    ("error: open(\"not a git repository\"): Permission denied", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nnot a git repository\nhint: Use -f", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nhint: stop\nfatal: not a git repository", "", .notARepo),
    ("fatal: invalid reference: 'not a git repository'", "", .invalidRef),
    ("fatal: couldn't find remote ref 'not a git repository'", "", .notFound),
    ("fatal: not a valid object name: 'not a git repository'", "", .invalidRef),
    ("error: '\"not a git repository\"'", "", .commandFailed),
    ("error: \"'not a git repository'\"", "", .commandFailed),
    ("error: \"escaped\\\"still not a git repository\" end", "", .commandFailed),
    ("error: cannot delete branch 'main' used by worktree at '/tmp/repoA'\n", "", .branchInUse),
    ("error: \"foo\" not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nnot a git repository", "", .commandFailed),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nerror: not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\nwarning: not a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\n\tnot a git repository\nhint: stop\nnot a git repository", "", .notARepo),
    ("The following paths are ignored by one of your .gitignore files:\nfoo\n\tnot a git repository", "", .commandFailed),
    ("   hint: not a git repository\nerror: failed\n", "", .commandFailed),
    ("error: failed\n\tnot a git repository\n", "", .commandFailed),
    ("  Cloning into 'dst'...\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Preparing worktree (detached HEAD)\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("From /src\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Switched to branch 'main'\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Already on 'main'\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("HEAD is now at 1234567\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("Branch 'main' set up\nfatal: not a git repository\nraw: Permission denied\n", "", .notARepo),
    ("warning: could not open directory 'sub/': Permission denied\nerror: The following untracked working tree files would be overwritten by checkout:\n\ta':b.txt\nAborting\n", "", .dirtyWorktree),
    ("warning: unable to access 'sub/.gitattributes': Permission denied\nfatal: not a git repository: '/bad': Permission denied\n", "", .notARepo),
    ("warning: could not open directory 'sub/': Permission denied\nfatal: pathspec 'missing' did not match any files\n", "", .notFound),
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
    stderr := "warning: unable to unlink 'sub/a fatal: spoof': Permission denied\n".toUTF8 }
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
  assertErrKind (Id.run (Impl.mergeBaseImpl nulOps "/repo" cid1 cid1)) .invalidRef "mergeBase empty stdout"
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
  let masterState : Model.GitRepoState := { defaultInitBranch := { raw := "master" } }
  let (clSelfRes, clSelfSt) := Model.evalGitApi.clone "file:///mock/bare" "/mock/bare" {} masterState
  assertTrue (clSelfRes.isOk) "clone self-target honors defaultInitBranch"
  assertTrue
    (match (Model.evalGitApi.headState "/mock/bare" clSelfSt).1 with
    | .ok (.attached br none) => br.raw == "master"
    | _ => false)
    "clone self-target attaches defaultInitBranch master"
  let (_, stSrc1) := Model.evalGitApi.init "/src" false (some { raw := "main" }) masterState
  let (c1Res, stSrc2) := Model.evalGitApi.commit "/src" { message := "c1", allowEmpty := true } stSrc1
  let c1 ← assertOk c1Res "mock commit c1"
  let (_, stSrc3) := Model.evalGitApi.createBranch "/src" { raw := "aaa" } none false stSrc2
  let (_, stSrc4) := Model.evalGitApi.checkout "/src" (.commit c1) false stSrc3
  let (clDetRes, stDst1) := Model.evalGitApi.clone "file:///src" "/dst" {} stSrc4
  assertTrue clDetRes.isOk "clone detached aaa/main under master ok"
  assertTrue
    (match (Model.evalGitApi.headState "/dst" stDst1).1 with
    | .ok (.attached br _) => br.raw == "aaa"
    | _ => false)
    "clone detached aaa/main under master selects aaa"
  let dst1SymOk :=
    match stDst1.repos.find? (fun r => r.commonDir == "/dst/.git".toUTF8) with
    | some r => r.symRefs.contains ("refs/remotes/origin/HEAD", "refs/remotes/origin/aaa")
    | none => false
  assertTrue dst1SymOk "clone detached aaa/main sets origin/HEAD to aaa"
  let (_, stF1) := Model.evalGitApi.init "/src2" false (some { raw := "aaa" }) masterState
  let (clEmp2, stF2) := Model.evalGitApi.clone "file:///src2" "/dst2" {} stF1
  assertTrue clEmp2.isOk "clone empty src2 ok"
  let (c2Res, stF3) := Model.evalGitApi.commit "/src2" { message := "c2", allowEmpty := true } stF2
  let c2 ← assertOk c2Res "mock commit c2"
  let (_, stF4) := Model.evalGitApi.createBranch "/src2" { raw := "master" } none false stF3
  let (_, stF5) := Model.evalGitApi.checkout "/src2" (.commit c2) false stF4
  let (feAmbig, stF6) := Model.evalGitApi.fetch "/dst2" "origin" none false stF5
  assertTrue feAmbig.isOk "fetch detached aaa/master ok"
  let dst2NoSym :=
    match stF6.repos.find? (fun r => r.commonDir == "/dst2/.git".toUTF8) with
    | some r => !r.symRefs.any (fun p => p.1 == "refs/remotes/origin/HEAD")
    | none => false
  assertTrue dst2NoSym "fetch detached aaa/master omits origin/HEAD"
  let (_, stU1) := Model.evalGitApi.init "/src3" false (some { raw := "aaa" }) masterState
  let (clEmp3, stU2) := Model.evalGitApi.clone "file:///src3" "/dst3" {} stU1
  assertTrue clEmp3.isOk "clone empty src3 ok"
  let (c3Res, stU3) := Model.evalGitApi.commit "/src3" { message := "c3", allowEmpty := true } stU2
  let c3 ← assertOk c3Res "mock commit c3"
  let (_, stU4) := Model.evalGitApi.checkout "/src3" (.commit c3) false stU3
  let (feUniq, stU5) := Model.evalGitApi.fetch "/dst3" "origin" none false stU4
  assertTrue feUniq.isOk "fetch detached unique aaa ok"
  let dst3HasSym :=
    match stU5.repos.find? (fun r => r.commonDir == "/dst3/.git".toUTF8) with
    | some r => r.symRefs.contains ("refs/remotes/origin/HEAD", "refs/remotes/origin/aaa")
    | none => false
  assertTrue dst3HasSym "fetch detached unique aaa sets origin/HEAD"
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

  let (_, stLit0) := Model.evalGitApi.init "/lit" false (some { raw := "main" }) masterState
  let (_, stLit1) := Model.evalGitApi.commit "/lit" { message := "seed", allowEmpty := true } stLit0
  for p in #["a[12].txt", "b*.txt", "c?.txt", "d\\e.txt", ":colon.txt", ":(top)x.txt", "-dash.txt", ":(exclude)a.txt", "*.txt", "-f"] do
    assertTrue (!Model.isExtendedPathspec p) s!"isExtendedPathspec literal {p}"
    assertTrue (Model.canNormalizeAddPathspecs stLit1 "/lit" #[p] false) s!"canNormalizeAddPathspecs literal {p}"
    assertTrue (Model.canNormalizeAddPathspecs stLit1 "/lit" #["/lit/" ++ p] false) s!"canNormalizeAddPathspecs abs literal {p}"
    assertTrue (Model.allowsDiffNameStatus stLit1 "/lit" "HEAD" none #[p] (.ok #[]))
      s!"allowsDiffNameStatus exact empty on missing {p}"
    assertTrue (!Model.allowsDiffNameStatus stLit1 "/lit" "HEAD" none #[p]
      (.ok #[{ kind := .modified, path := "bogus.txt" }]))
      s!"allowsDiffNameStatus rejects bogus entry for literal {p}"
    assertTrue (!(Model.allowsAdd stLit1 "/lit" #[p] false none
      (.error { kind := .commandFailed, message := "wrong" })).1)
      s!"allowsAdd rejects commandFailed when literal {p} is missing"
    assertTrue ((Model.allowsAdd stLit1 "/lit" #[p] false none
      (.error { kind := .notFound, message := "missing" })).1)
      s!"allowsAdd accepts notFound when literal {p} is missing"
  for p in #["/outside/x", "../up", "a//b", ".git/HEAD", "", String.ofList (List.replicate 260 'x')] do
    assertTrue (Model.isExtendedPathspec p) s!"isExtendedPathspec non-normalizable {p}"
  assertTrue (Model.allowsCliErrorKind false .notFound .notFound) "allowsCliErrorKind strict equal"
  assertTrue (!Model.allowsCliErrorKind false .notFound .notARepo) "allowsCliErrorKind strict rejects mismatch"
  assertTrue (Model.allowsCliErrorKind true .notFound .notARepo) "allowsCliErrorKind spoofable permits CLI error"
  assertTrue (!Model.allowsCliErrorKind true .invalidInput .commandFailed) "allowsCliErrorKind never relaxes invalidInput"


end LeanSwe.Git.RuntimeTests
