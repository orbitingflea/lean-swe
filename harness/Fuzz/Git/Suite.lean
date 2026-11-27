import Fuzz.Common.Suite
import Fuzz.Common.Coverage
import Fuzz.Common.Shrink
import Fuzz.Common.Rng
import Fuzz.Git.Gen
import Fuzz.Git.Exec

namespace Fuzz.Git

open Fuzz.Common
open LeanSwe.Git

private def safePrintln (s : String) : IO Unit := do
  try
    IO.println s
  catch _ =>
    pure ()

private def requiredBuckets : Array CoverageBucket := #[
  bucket "isRepo" "ok",
  bucket "repoRoot" "ok",
  bucket "commonDir" "ok",
  bucket "headCommit?" "ok",
  bucket "headBranch?" "ok",
  bucket "headState" "ok",
  bucket "revParseCommit" "ok",
  bucket "isAncestor" "ok",
  bucket "mergeBase?" "ok",
  bucket "status" "ok",
  bucket "diffNameStatus" "ok",
  bucket "listWorktrees" "ok",
  bucket "showFile?" "ok",
  bucket "init" "ok",
  bucket "clone" "ok",
  bucket "add" "ok",
  bucket "commit" "ok",
  bucket "createBranch" "ok",
  bucket "deleteBranch" "ok",
  bucket "checkout" "ok",
  bucket "switch" "ok",
  bucket "reset" "ok",
  bucket "fetch" "ok",
  bucket "worktreeAdd" "ok",
  bucket "worktreeRemove" "ok",
  bucket "withWorktree" "ok",
  bucket "vfsRemoveFile" "ok",
  bucket "vfsRemoveDir" "ok",
  bucket "vfsChmodSubDir" "ok",
  bucket "vfsSetFileExecutable" "ok",
  bucket "repoRoot" "err.notARepo",
  bucket "revParseCommit" "err.invalidRef",
  bucket "isRepo" "err.invalidPath",
  bucket "clone" "err.alreadyExists",
  bucket "commit" "err.invalidInput",
  bucket "checkout" "err.dirtyWorktree",
  bucket "checkout" "err.conflict",
  bucket "checkout" "err.branchInUse",
  bucket "switch" "err.dirtyWorktree",
  bucket "switch" "err.conflict",
  bucket "switch" "err.branchInUse",
  bucket "worktreeAdd" "err.branchInUse",
  bucket "worktreeRemove" "err.dirtyWorktree",
  bucket "commit" "err.nothingToCommit",
  bucket "deleteBranch" "err.branchInUse",
  bucket "deleteBranch" "err.commandFailed",
  bucket "createBranch" "err.alreadyExists",
  bucket "add" "err.notFound",
  bucket "commit" "err.conflict",
  bucket "status" "err.commandFailed",
  bucket "status" "err.parseError",
  bucket "timeoutProbe" "err.timeout"
]

private def warmupCorpus : Array GitFuzzStep := #[
  .opIsRepo (.raw "") false,
  .opClone (.raw ".git/config") (.slot .cloneRepo) { singleBranch := true } true,
  .opInit (.slot .repoA) false (some { raw := "main" }) true,
  .opIsRepo (.slot .repoA) true,
  .opIsRepo (.subRel .repoA "..") false,
  .opRepoRoot (.subRel .repoA "..") false,
  .opInit (.slot .bareRepo) true none false,
  .opRepoRoot (.slot .bareRepo) false,
  .opRevParseCommit (.slot .repoA) (.raw "HEAD") false,
  .opCommit (.slot .repoA) { message := "" } false,
  .opCommit (.slot .repoA) { message := "empty" } false,
  .opAdd (.slot .repoA) #["missing.txt"] false false,
  .opAdd (.slot .repoA) #["conflict.txt"] false false,
  .opAdd (.slot .repoA) #["already exists.txt"] false false,
  .vfsWriteFile .repoA "a.txt".toUTF8 "hello\n".toUTF8 false,
  .vfsSetFileExecutable .repoA "a.txt".toUTF8 true,
  .vfsSetFileExecutable .repoA "a.txt".toUTF8 false,
  .opAdd (.slot .repoA) #["a.txt"] false true,
  .opCommit (.slot .repoA)
    { message := "init a\n", authorName := some "  .Alice.  ", authorEmail := some "alice@example.com" } true,
  .opHeadCommit (.slot .repoA) true,
  .opHeadBranch (.slot .repoA) true,
  .opHeadState (.slot .repoA) true,
  .opRepoRoot (.slot .repoA) true,
  .opCommonDir (.slot .repoA) true,
  .opRevParseCommit (.slot .repoA) (.raw "HEAD") true,
  .opStatus (.slot .repoA) true,
  .opShowFile (.slot .repoA) (.raw "HEAD") "a.txt" true,
  .opCreateBranch (.slot .repoA) { raw := "feat" } none false false,
  .opCreateBranch (.slot .repoA) { raw := "feat" } none false false,
  .opDeleteBranch (.slot .repoA) { raw := "conflict" } false false,
  .opCreateBranch (.slot .repoA) { raw := "conflict" } none false false,
  .opCreateBranch (.slot .repoA) { raw := "conflict" } none false false,
  .opDeleteBranch (.slot .repoA) { raw := "conflict" } true false,
  .opCheckout (.slot .repoA) (.branch { raw := "conflict" }) false false,
  .opDeleteBranch (.slot .repoA) { raw := "main" } false false,
  .opSwitch (.slot .repoA) { raw := "feat" } false none false false,
  .vfsWriteFile .repoA "b.txt".toUTF8 "two\n".toUTF8 false,
  .opAdd (.slot .repoA) #[] true false,
  .opCommit (.slot .repoA) { message := "second" } false,
  .opRevParseCommit (.slot .repoA) (.raw "HEAD^0") false,
  .opRevParseCommit (.slot .repoA) (.raw "feat^0") false,
  .opRevParseCommit (.slot .repoA) (.raw "HEAD@{0}") false,
  .opRevParseCommit (.slot .repoA) (.raw ":/init a") false,
  .opRevParseCommit (.slot .repoA) (.shortCommitIdx 0 7 "dead000") false,
  .opShowFile (.slot .repoA) (.raw "HEAD@{0}") "a.txt" false,
  .opShowFile (.slot .repoA) (.shortCommitIdx 0 7 "dead000") "a.txt" false,
  .opCommit (.slot .repoA) { message := "  pad  \n  \n\n\nline2 \t \r\n\n  ", allowEmpty := true } false,
  .opIsAncestor (.slot .repoA) 0 1 none none false,
  .opMergeBase (.slot .repoA) 0 1 none none false,
  .opDiffNameStatus (.slot .repoA) (.raw "HEAD~1") (some (.raw "HEAD")) #[] false,
  .opDiffNameStatus (.slot .repoA) (.raw "HEAD^{tree}") none #[] false,
  .opCheckout (.slot .repoA) (.branch { raw := "main" }) false false,
  .vfsWriteFile .repoA "b.txt".toUTF8 "collision\n".toUTF8 false,
  .opCheckout (.slot .repoA) (.branch { raw := "feat" }) false false,
  .vfsRemoveFile .repoA "b.txt".toUTF8,
  .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "feat")) none false false false,
  .opCheckout (.slot .repoA) (.branch { raw := "feat" }) false false,
  .opSwitch (.slot .repoA) { raw := "feat" } false none false false,
  .opWorktreeAdd (.slot .repoA) (.slot .wt2) (some (.raw "feat")) none false false false,
  .opListWorktrees (.slot .repoA) false,
  .opWorktreeRemove (.slot .repoA) (.slot .wt1) false false,
  .opWorktreeAdd (.slot .repoA) (.slot .wt1) none none false false false,
  .opWorktreeRemove (.slot .repoA) (.slot .wt1) false false,
  .opDeleteBranch (.slot .repoA) { raw := "wt1" } false false,
  .opWithWorktree (.slot .repoA) (.slot .wt2) (some (.raw "HEAD")) none true false
    [.opStatus (.slot .wt2) true] false false,
  .opClone (.slot .repoA) (.slot .cloneRepo) {} true,
  .opFetch (.slot .cloneRepo) "origin" (some "+refs/heads/*:refs/remotes/origin/*") true true,
  .opCheckout (.slot .cloneRepo) (.branch { raw := "feat" }) false false,
  .opSwitch (.slot .cloneRepo) { raw := "main" } false none false false,
  .opDeleteBranch (.slot .cloneRepo) { raw := "feat" } true false,
  .opSwitch (.slot .cloneRepo) { raw := "feat" } false none false false,
  .opDeleteBranch (.slot .repoA) { raw := "feat" } true false,
  .gitRawCreateMergeConflict .repoA { raw := "mc_a" } { raw := "mc_b" } "conflict.txt" false,
  .opCommit (.slot .repoA) { message := "blocked" } false,
  .opCheckout (.slot .repoA) (.branch { raw := "mc_b" }) false false,
  .opSwitch (.slot .repoA) { raw := "mc_b" } false none false false,
  .opReset (.slot .repoA) .hard (.raw "HEAD") false,
  .gitRawCreateMergeConflict .repoA { raw := "mc_c" } { raw := "mc_d" } "conflict.txt" true,
  .opSwitch (.slot .repoA) { raw := "mc_d" } false none false false,
  .opSwitch (.slot .repoA) { raw := "conf_sw" } true (some (.raw "mc_d")) false false,
  .opReset (.slot .repoA) .hard (.raw "HEAD") false,
  .opInit (.slot .repoB) false none false,
  .vfsChmodDir .repoB false,
  .opStatus (.slot .repoB) false,
  .vfsChmodDir .repoB true,
  .vfsWriteFile .repoA (ByteArray.mk #[0x62, 0x61, 0x64, 0xff, 0x2e, 0x74, 0x78, 0x74]) "x".toUTF8 false,
  .opStatus (.slot .repoA) false,
  .opTimeoutProbe (.slot .repoA) 0
]

private def worktreeAndIgnoreRegressionTraces : Array (Array GitFuzzStep) := #[
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opClone (.slot .repoA) (.slot .bareRepo) { bare := true } false,
    .opWorktreeAdd (.slot .bareRepo) (.slot .bareWt) (some (.raw "HEAD")) (some { raw := "wtbr" }) false false false,
    .opIsRepo (.slot .bareWt) false,
    .opStatus (.slot .bareWt) false,
    .opHeadBranch (.slot .bareWt) false,
    .opHeadState (.slot .bareWt) false,
    .opListWorktrees (.slot .bareRepo) false,
    .opClone (.slot .bareWt) (.slot .cloneRepo) {} false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) (some { raw := "wt1br" }) false false false,
    .opClone (.fileUrlLocalhost .wt1) (.slot .repoB) {} false
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .vfsWriteFile .repoA ".gitignore".toUTF8 "*.log\n!keep.log\nbuild/\n/rootonly.txt\n".toUTF8 false,
    .vfsWriteFile .repoA "debug.log".toUTF8 "ign\n".toUTF8 false,
    .vfsWriteFile .repoA "keep.log".toUTF8 "ok\n".toUTF8 false,
    .vfsWriteFile .repoA "build/out.o".toUTF8 "bin\n".toUTF8 false,
    .vfsWriteFile .repoA "rootonly.txt".toUTF8 "r\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/rootonly.txt".toUTF8 "sr\n".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opAdd (.slot .repoA) #["debug.log"] false false,
    .opAdd (.slot .repoA) #[] true false,
    .opStatus (.slot .repoA) false,
    .opCommit (.slot .repoA) { message := "gitignore" } false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .vfsWriteFile .repoA "dir/a.txt".toUTF8 "d1\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opSwitch (.slot .repoA) { raw := "feat" } true none false false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "2\n".toUTF8 false,
    .vfsRemoveFile .repoA "dir/a.txt".toUTF8,
    .vfsRemoveDir .repoA "dir".toUTF8,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c2" } false,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) false false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "2\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCheckout (.slot .repoA) (.branch { raw := "feat" }) false false,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) false false,
    .opCheckout (.slot .repoA) (.branch { raw := "feat" }) false false,
    .vfsWriteFile .repoA "dir".toUTF8 "blocker\n".toUTF8 false,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) true false,
    .opStatus (.slot .repoA) false,
    .vfsRemoveFile .repoA "a.txt".toUTF8,
    .opAdd (.slot .repoA) #[] true false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[] false,
    .opReset (.slot .repoA) .hard (.raw "HEAD") false,
    .vfsRemoveFile .repoA "a.txt".toUTF8,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "rm a" } false,
    .vfsMkdir .repoA "a.txt".toUTF8,
    .opCheckout (.slot .repoA) (.branch { raw := "feat" }) false false
  ],
  #[
    .opIsRepo (.slot .symLoopA) false,
    .opStatus (.slot .symLoopA) false,
    .opInit (.slot .symLoopA) false none false,
    .opInit (.slot .danglingSym) false none false,
    .opInit (.subRel .missingDir "missing_sub/..") false none false,
    .opCheckout (.slot .missingDir) (.branch { raw := "main" }) false false,
    .opInit (.slot .subDir) false none false,
    .opInit (.slot .repoA) false none false,
    .opAdd (.slot .repoA) #[] true false,
    .vfsWriteFile .subDir "in.txt".toUTF8 "nested\n".toUTF8 false,
    .opAdd (.slot .subDir) #[] true false,
    .opCommit (.slot .subDir) { message := "nested c1" } false,
    .opAdd (.slot .repoA) #[] true false,
    .opStatus (.slot .repoA) false,
    .opCommit (.slot .repoA) { message := "with gitlink" } false
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .vfsWriteFile .repoA "a".toUTF8 "file\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/x.txt".toUTF8 "orig\n".toUTF8 false,
    .vfsWriteFile .repoA "dir/c.txt".toUTF8 "dc\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "base" } false,
    .vfsRemoveFile .repoA "a".toUTF8,
    .vfsWriteFile .repoA "a/b.txt".toUTF8 "df\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a/b.txt"] false false,
    .opStatus (.slot .repoA) false,
    .vfsSymlink .repoA "symdir".toUTF8 "dir".toUTF8,
    .opAdd (.slot .repoA) #["symdir/c.txt"] false false,
    .vfsWriteFile .repoA "sub/x.txt".toUTF8 "mod\n".toUTF8 false,
    .vfsChmodSubDir .repoA "sub".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[] false,
    .opAdd (.slot .repoA) #[] true false,
    .opAdd (.slot .repoA) #["sub/untracked.txt"] false false,
    .vfsChmodSubDir .repoA "sub".toUTF8 true
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .gitRawCreateTag .repoA { raw := "main" } (.raw "HEAD"),
    .gitRawCreateTag .repoA { raw := "v1" } (.raw "HEAD"),
    .vfsWriteFile .repoA "a.txt".toUTF8 "2\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c2" } false,
    .opSwitch (.slot .repoA) { raw := "ahead" } true none false false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "3\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c3" } false,
    .opSwitch (.slot .repoA) { raw := "main" } false none false false,
    .opHeadBranch (.slot .repoA) false,
    .opCheckout (.slot .repoA) (.ref (.raw "main")) false false,
    .opCreateBranch (.slot .repoA) { raw := "amb_br" } (some (.raw "main")) false false,
    .opCreateBranch (.slot .repoA) { raw := "amb_nosp" } none false false,
    .opSwitch (.slot .repoA) { raw := "amb_sw" } true (some (.raw "main")) false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "main")) (some { raw := "amb_wt" }) false false false,
    .opCheckout (.slot .repoA) (.branch { raw := "v1" }) false false,
    .opClone (.fileUrl .repoA) (.slot .cloneRepo) { depth? := some 2, singleBranch := true } false,
    .opCheckout (.slot .cloneRepo) (.branch { raw := "origin/main" }) false false,
    .opSwitch (.slot .cloneRepo) { raw := "origin/main" } false none false false,
    .opSwitch (.slot .cloneRepo) { raw := "old" } true (some (.raw "HEAD~1")) false false,
    .opDeleteBranch (.slot .cloneRepo) { raw := "main" } false false,
    .opClone (.slot .repoA) (.slot .bareRepo) { bare := true, branch? := some "v1", singleBranch := true } false,
    .opHeadState (.slot .bareRepo) false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opWorktreeAdd (.slot .repoA) (.slot .plainFile) (some (.raw "missing-branch")) none false false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) (some { raw := "wtbr1" }) false false false,
    .vfsRemoveTree .wt1,
    .opListWorktrees (.slot .repoA) false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) (some { raw := "wtbr2" }) false false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) (some { raw := "wtbr2" }) false true false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) (some { raw := "wtbr3" }) false true false,
    .opWorktreeAdd (.slot .repoA) (.slot .danglingSym) (some (.raw "HEAD")) (some { raw := "wt_dang" }) false false false,
    .vfsRemoveTree .wt1,
    .opWorktreeRemove (.slot .repoA) (.subRel .wt1 "../wt1") false false,
    .opWorktreeRemove (.slot .repoA) (.subRel .repoA "../wt1") false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt2) (some (.raw "HEAD")) none true false false,
    .vfsChmodDir .wt2 false,
    .opListWorktrees (.slot .repoA) false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt2) false false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt2) true false,
    .vfsChmodDir .wt2 true,
    .gitRawLockWorktree .repoA .wt2 true (some "hold"),
    .vfsRemoveTree .wt2,
    .opListWorktrees (.slot .repoA) false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt2) (some (.raw "HEAD")) none true true false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt2) true false,
    .gitRawLockWorktree .repoA .wt2 false none,
    .opWorktreeRemove (.slot .repoA) (.slot .wt2) false false
  ],
  #[
    .opClone (.fileUrl .bareRepo) (.slot .bareRepo) {} false,
    .opHeadState (.slot .bareRepo) false,
    .opClone (.fileUrl .cloneRepo) (.slot .cloneRepo) { bare := true } false,
    .opHeadState (.slot .cloneRepo) false,
    .opClone (.fileUrl .repoB) (.slot .repoB) { branch? := some "feat" } false
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .opWithWorktree
      (PathTarget.slot SlotId.repoA)
      (PathTarget.slot SlotId.wt1)
      none
      (some { raw := "bugfix" })
      false
      false
      [.opSwitch (PathTarget.slot SlotId.wt1) { raw := "main" } true none false false]
      false
      false
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .gitRawCreateMergeConflict .repoA { raw := "mc_a" } { raw := "mc_b" } "conflict.txt" false,
    .vfsWriteFile .repoA "conflict.txt".toUTF8 "resolved\n".toUTF8 false,
    .opAdd (.slot .repoA) #["conflict.txt"] false false,
    .opCheckout (.slot .repoA) (.branch { raw := "mc_a" }) false false,
    .opSwitch (.slot .repoA) { raw := "mc_b" } false none false false
  ]
]

private def mkAttrAndSubmoduleRegressionTraces : Unit → Array (Array GitFuzzStep) := fun () => #[
  #[
    .opInit (.slot .repoA) false none true,
    .vfsWriteFile .repoA ".gitignore".toUTF8 "foo/**\n!foo/keep.txt\n[[:digit:]].txt\nsp\\ \nbuild/\n".toUTF8 false,
    .vfsWriteFile .repoA "foo/keep.txt".toUTF8 "keep\n".toUTF8 false,
    .vfsWriteFile .repoA "foo/drop.txt".toUTF8 "drop\n".toUTF8 false,
    .vfsWriteFile .repoA "1.txt".toUTF8 "one\n".toUTF8 false,
    .vfsWriteFile .repoA "sp ".toUTF8 "space\n".toUTF8 false,
    .vfsWriteFile .repoA "build/out.o".toUTF8 "bin\n".toUTF8 false,
    .opStatus (.slot .repoA) true,
    .opAdd (.slot .repoA) #["build"] false true,
    .opAdd (.slot .repoA) #["quote\"name.txt"] false true,
    .opAdd (.slot .repoA) #["foo/keep.txt"] false true,
    .opCommit (.slot .repoA) { message := "nested-ign" } true
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8
      "*.txt text\ncrlf_lf.txt eol=lf\ncrlf_crlf.txt eol=crlf\nraw.bin binary\nnotxt.txt -text\n".toUTF8 false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "x\r\ny\r\n".toUTF8 false,
    .vfsWriteFile .repoA "crlf_lf.txt".toUTF8 "l1\r\nl2\r\n".toUTF8 false,
    .vfsWriteFile .repoA "crlf_crlf.txt".toUTF8 "c1\r\nc2\r\n".toUTF8 false,
    .vfsWriteFile .repoA "notxt.txt".toUTF8 "n1\r\nn2\r\n".toUTF8 false,
    .vfsWriteFile .repoA "raw.bin".toUTF8 "b1\r\nb2\r\n".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opStatus (.slot .repoA) false,
    .opCommit (.slot .repoA) { message := "attrs" } false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[] false
  ],
  #[
    .opInit (.raw "repo_cr\r") false none false,
    .opInit (.raw "repo_cr\r/sub") false none false,
    .opInit (.raw "dir_nl\n") false none false,
    .opInit (.raw "dir_nl\n/sub") false none false,
    .opInit (.slot .repoA) false (some { raw := "master" }) false,
    .opInit (.raw "out/missing/../../repoA/nested") false none false,
    .opInit (.subRel .danglingSym "child") false none false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "hi\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opCreateBranch (.slot .repoA) { raw := "side" } none false false,
    .gitRawCreateTag .repoA { raw := "v1" } (.raw "side"),
    .opSwitch (.slot .repoA) { raw := "alpha" } true (some (.raw "HEAD")) false false,
    .opCheckout (.slot .repoA) (.commitIdx 0 none) false false,
    .opClone (.slot .repoA) (.slot .cloneRepo) { branch? := some "alpha" } false,
    .opFetch (.slot .repoA) "." (some "HEAD:alpha") false false,
    .opFetch (.slot .cloneRepo) "origin" (some "refs/heads/side:refs/heads/got") false false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "v1") false
  ],
  #[
    .opInit (.slot .subDir) false none false,
    .vfsWriteFile .subDir "nested.txt".toUTF8 "n1\n".toUTF8 false,
    .opAdd (.slot .subDir) #["nested.txt"] false false,
    .opCommit (.slot .subDir) { message := "sub1" } false,
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "top.txt".toUTF8 "t1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["top.txt", "sub"] false false,
    .opCommit (.slot .repoA) { message := "with-sub" } false,
    .opShowFile (.slot .repoA) (.raw "HEAD") "sub" false,
    .opStatus (.slot .repoA) false,
    .vfsWriteFile .subDir "untracked.txt".toUTF8 "dirty\n".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opCreateBranch (.slot .repoA) { raw := "b2" } none false false,
    .opSwitch (.slot .repoA) { raw := "b2" } false none false false,
    .vfsWriteFile .repoA "d/inner.txt".toUTF8 "v1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["d/inner.txt"] false false,
    .opCommit (.slot .repoA) { message := "d1" } false,
    .opSwitch (.slot .repoA) { raw := "main" } false none false false,
    .vfsWriteFile .repoA "d/inner.txt".toUTF8 "v2\n".toUTF8 false,
    .opAdd (.slot .repoA) #["d/inner.txt"] false false,
    .opCommit (.slot .repoA) { message := "d2" } false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "b2")) none false false false,
    .opStatus (.slot .wt1) false,
    .vfsChmodSubDir .repoA "d".toUTF8 false,
    .opCheckout (.slot .repoA) (.branch { raw := "b2" }) true false,
    .vfsChmodSubDir .repoA "d".toUTF8 true,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) true false,
    .vfsChmodSubDir .repoA "d".toUTF8 false,
    .opReset (.slot .repoA) .hard (.raw "b2") false,
    .vfsChmodSubDir .repoA "d".toUTF8 true,
    .vfsChmodSubDir .wt1 "d".toUTF8 false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt1) true false,
    .vfsChmodSubDir .wt1 "d".toUTF8 true
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .vfsWriteFile .repoA "huge.bin".toUTF8 (ByteArray.mk (Array.replicate 16777217 'x'.toUInt8)) false,
    .opAdd (.slot .repoA) #["huge.bin"] false false,
    .opCommit (.slot .repoA) { message := "huge" } false,
    .opShowFile (.slot .repoA) (.raw "HEAD") "huge.bin" false
  ],
  #[
    .opInit (.slot .repoA) false none false,
    .gitRawCreateMergeConflict .repoA { raw := "mc_c" } { raw := "mc_d" } "conflict.txt" false,
    .opDeleteBranch (.slot .repoA) { raw := "mc_d" } true false,
    .opClone (.slot .repoA) (.slot .cloneRepo) {} false,
    .opShowFile (.slot .cloneRepo) (.commitIdx 5 "HEAD~1") "back\\slash.txt" false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opClone (.slot .repoA) (.slot .plainFile) {} false,
    .opCreateBranch (.slot .repoA) { raw := "feat" } none false false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "2\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCommit (.slot .repoA) { message := "c2" } false,
    .opReset (.slot .repoA) .soft (.raw "HEAD~1") false,
    .opStatus (.slot .repoA) false,
    .opReset (.slot .repoA) .mixed (.raw "HEAD") false,
    .opStatus (.slot .repoA) false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCommit (.slot .repoA) { message := "c2b" } false,
    .opCommit (.slot .repoA) { message := "empty-ok", allowEmpty := true } false,
    .opCreateBranch (.slot .repoA) { raw := "feat" } (some (.raw "HEAD")) true false,
    .opSwitch (.slot .repoA) { raw := "unmerged_br" } true none false false,
    .vfsWriteFile .repoA "unm.txt".toUTF8 "u\n".toUTF8 false,
    .opAdd (.slot .repoA) #["unm.txt"] false false,
    .opCommit (.slot .repoA) { message := "unm" } false,
    .opSwitch (.slot .repoA) { raw := "main" } false none false false,
    .opDeleteBranch (.slot .repoA) { raw := "unmerged_br" } false false,
    .vfsWriteFile .repoA "unm.txt".toUTF8 "dirty_local\n".toUTF8 false,
    .opSwitch (.slot .repoA) { raw := "unmerged_br" } false none false false,
    .vfsRemoveFile .repoA "unm.txt".toUTF8,
    .opClone (.slot .repoA) (.slot .cloneRepo) {} false,
    .opDeleteBranch (.slot .repoA) { raw := "feat" } true false,
    .opFetch (.slot .cloneRepo) "origin" none true false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "origin/feat") false,
    .opSwitch (.slot .repoA) { raw := "unmerged_br" } false none false false,
    .opSwitch (.slot .repoA) { raw := "main" } true (some (.raw "HEAD")) true false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) none true false false,
    .vfsWriteFile .wt1 "dirty_wt.txt".toUTF8 "d\n".toUTF8 false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt1) false false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt1) true false,
    .opWithWorktree (.slot .repoA) (.slot .wt2) (some (.raw "HEAD")) none true false
      [.opStatus (.slot .wt2) false] true false,
    .opTimeoutProbe (.slot .repoA) 1,
    .opTimeoutProbe (.slot .repoA) 2,
    .opTimeoutProbe (.slot .repoA) 3
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a.txt"] false false,
    .opCommit (.slot .repoA) { message := "c0" } false,
    .opClone (.slot .repoA) (.slot .danglingSym) { bare := false } false,
    .opClone (.slot .repoA) (.slot .danglingSym) { bare := true } false,
    .opIsRepo (.slot .danglingSym) false,
    .opCommonDir (.slot .danglingSym) false,
    .opHeadState (.slot .danglingSym) false,
    .opListWorktrees (.slot .danglingSym) false,
    .gitRawCreateCrissCrossMerge .repoA,
    .opMergeBase (.slot .repoA) 4 5 none none false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8 "*.txt eol=crlf\n".toUTF8 false,
    .vfsWriteFile .repoA "!bang.txt".toUTF8 "v1\r\n".toUTF8 false,
    .vfsWriteFile .repoA "nul.txt".toUTF8 (ByteArray.mk #[0x61, 0x00, 0x62, 0x0d, 0x0a]) false,
    .vfsWriteFile .repoA "p0.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p1.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p2.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p3.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p4.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p5.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p6.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p7.bin".toUTF8 "x".toUTF8 false,
    .vfsWriteFile .repoA "p8.bin".toUTF8 "x".toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c1" } false,
    .opClone (.slot .repoA) (.slot .cloneRepo) {} false,
    .vfsWriteFile .cloneRepo ".gitattributes".toUTF8 "*.txt -text\n".toUTF8 false,
    .opStatus (.slot .cloneRepo) false,
    .opSwitch (.slot .repoA) { raw := "notext" } true none false false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8 "*.txt -text\n".toUTF8 false,
    .vfsWriteFile .repoA "!bang.txt".toUTF8 "v2\n".toUTF8 false,
    .vfsWriteFile .repoA "nul.txt".toUTF8 (ByteArray.mk #[0x61, 0x00, 0x62, 0x32, 0x0a]) false,
    .opAdd (.slot .repoA) #[] true false,
    .opCommit (.slot .repoA) { message := "c2" } false,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) false false,
    .opStatus (.slot .repoA) false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8 "*.txt -text\n".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opCheckout (.slot .repoA) (.branch { raw := "notext" }) true false,
    .opCheckout (.slot .repoA) (.branch { raw := "main" }) true false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8 "*.txt -text\n".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opReset (.slot .repoA) .hard (.raw "notext") false,
    .opReset (.slot .repoA) .hard (.raw "main") false,
    .vfsWriteFile .repoA ".gitattributes".toUTF8 "*.txt -text\n".toUTF8 false,
    .opStatus (.slot .repoA) false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/b.txt".toUTF8 "2\n".toUTF8 false,
    .opAdd (.slot .repoA) #["."] false false,
    .opCommit (.slot .repoA) { message := "dot-add" } false,
    .vfsWriteFile .repoA "a.txt".toUTF8 "1b\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/b.txt".toUTF8 "2b\n".toUTF8 false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["."] false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["sub/"] false,
    .opAdd (.slot .repoA) #["sub/"] false false,
    .opStatus (.slot .repoA) false,
    .opAdd (.slot .repoA) #["./a.txt"] false false,
    .opCommit (.slot .repoA) { message := "dir-slash" } false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD~1") (some (.raw "HEAD")) #["sub/"] false,
    .opAdd (.slot .repoA) #["../outside"] false false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["../outside"] false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "old_ren.txt".toUTF8
      ("alpha-01\nalpha-02\nalpha-03\nalpha-04\nalpha-05\nalpha-06\nalpha-07\nalpha-08\nalpha-09\nalpha-10\n").toUTF8 false,
    .opAdd (.slot .repoA) #["old_ren.txt"] false false,
    .opCommit (.slot .repoA) { message := "ren-base" } false,
    .vfsRemoveFile .repoA "old_ren.txt".toUTF8,
    .vfsWriteFile .repoA "new_ren.txt".toUTF8
      ("alpha-01-edit\nalpha-02\nalpha-03\nalpha-04\nalpha-05\nalpha-06\nalpha-07\nalpha-08\nalpha-09\nalpha-10\n").toUTF8 false,
    .opAdd (.slot .repoA) #[] true false,
    .opStatus (.slot .repoA) false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[] false,
    .vfsWriteFile .repoA "new_ren.txt".toUTF8
      ("alpha-01-edit\nalpha-02-wt\nalpha-03\nalpha-04\nalpha-05\nalpha-06\nalpha-07\nalpha-08\nalpha-09\nalpha-10\n").toUTF8 false,
    .vfsWriteFile .repoA "old_ren.txt".toUTF8 "fresh-untracked\n".toUTF8 false,
    .opStatus (.slot .repoA) false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[] false,
    .opCommit (.slot .repoA) { message := "ren-commit" } false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD~1") (some (.raw "HEAD")) #[] false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "f.txt".toUTF8 "v1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["f.txt"] false false,
    .opCommit (.slot .repoA) { message := "base" } false,
    .opClone (.fileUrl .repoA) (.slot .cloneRepo) {} false,
    .opCreateBranch (.slot .repoA) { raw := "feat" } none false false,
    .opCreateBranch (.slot .repoA) { raw := "feat-1" } none false false,
    .opCreateBranch (.slot .repoA) { raw := "pr/42/head" } none false false,
    .opFetch (.slot .cloneRepo) "origin" (some "refs/heads/feat*:refs/remotes/origin/feat*") false false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "refs/remotes/origin/feat-1") false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "refs/remotes/origin/feat") false,
    .opFetch (.slot .cloneRepo) "origin" (some "+refs/heads/pr/*/head:refs/remotes/origin/pull/*") false false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "refs/remotes/origin/pull/42") false,
    .opFetch (.slot .cloneRepo) "origin" (some "refs/heads/feat*:refs/heads/HEAD*") false false,
    .opDeleteBranch (.slot .repoA) { raw := "feat-1" } true false,
    .opFetch (.slot .cloneRepo) "origin" (some "refs/heads/feat*:refs/remotes/origin/feat*") true false,
    .opRevParseCommit (.slot .cloneRepo) (.raw "refs/remotes/origin/feat-1") false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "a1.txt".toUTF8 "sibling\n".toUTF8 false,
    .vfsWriteFile .repoA "a[12].txt".toUTF8 "bracket\n".toUTF8 false,
    .opAdd (.slot .repoA) #["a[12].txt"] false false,
    .opStatus (.slot .repoA) false,
    .opAdd (.slot .repoA) #["."] false false,
    .opStatus (.slot .repoA) false,
    .vfsWriteFile .repoA "b*.txt".toUTF8 "star1\n".toUTF8 false,
    .vfsWriteFile .repoA "c?.txt".toUTF8 "q1\n".toUTF8 false,
    .vfsWriteFile .repoA "d\\e.txt".toUTF8 "bs1\n".toUTF8 false,
    .vfsWriteFile .repoA ":colon.txt".toUTF8 "col1\n".toUTF8 false,
    .vfsWriteFile .repoA ":(top)x.txt".toUTF8 "top1\n".toUTF8 false,
    .vfsWriteFile .repoA "-dash.txt".toUTF8 "dash1\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/:(top)z".toUTF8 "sub1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["b*.txt", "c?.txt", "d\\e.txt", ":colon.txt", ":(top)x.txt", "-dash.txt"] false false,
    .opAdd (.subRel .repoA "sub") #[":(top)z"] false false,
    .opStatus (.slot .repoA) false,
    .opCommit (.slot .repoA) { message := "lit-base" } false,
    .vfsWriteFile .repoA "a[12].txt".toUTF8 "bracket2\n".toUTF8 false,
    .vfsWriteFile .repoA "b*.txt".toUTF8 "star2\n".toUTF8 false,
    .vfsWriteFile .repoA "c?.txt".toUTF8 "q2\n".toUTF8 false,
    .vfsWriteFile .repoA "d\\e.txt".toUTF8 "bs2\n".toUTF8 false,
    .vfsWriteFile .repoA ":colon.txt".toUTF8 "col2\n".toUTF8 false,
    .vfsWriteFile .repoA ":(top)x.txt".toUTF8 "top2\n".toUTF8 false,
    .vfsWriteFile .repoA "-dash.txt".toUTF8 "dash2\n".toUTF8 false,
    .vfsWriteFile .repoA "sub/:(top)z".toUTF8 "sub2\n".toUTF8 false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["a[12].txt", "b*.txt", "c?.txt", "d\\e.txt", ":colon.txt", ":(top)x.txt", "-dash.txt"] false,
    .opDiffNameStatus (.subRel .repoA "sub") (.raw "HEAD") none #[":(top)z"] false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["*.txt"] false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #[":(exclude)a1.txt"] false,
    .opAdd (.slot .repoA) #["*.txt"] false false,
    .opAdd (.slot .repoA) #[":(exclude)a1.txt"] false false,
    .opAdd (.slot .repoA) #["-f"] false false,
    .opAdd (.slot .repoA) #["a[12].txt/"] false false,
    .opDiffNameStatus (.slot .repoA) (.raw "HEAD") none #["a[12].txt/"] false,
    .opAdd (.slot .repoA) #["already exists.txt"] false false,
    .opAdd (.slot .repoA) #["not a git repository.txt"] false false
  ],
  #[
    .opInit (.slot .repoA) false (some { raw := "main" }) false,
    .vfsWriteFile .repoA "f.txt".toUTF8 "v1\n".toUTF8 false,
    .opAdd (.slot .repoA) #["f.txt"] false false,
    .opCommit (.slot .repoA) { message := "base40" } false,
    .opCreateBranch (.slot .repoA) { raw := "ffffffffffffffffffffffffffffffffffffffff" } none false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "ffffffffffffffffffffffffffffffffffffffff")) none false false false,
    .opWorktreeAdd (.slot .repoA) (.slot .wt1) (some (.raw "refs/heads/ffffffffffffffffffffffffffffffffffffffff")) none false false false,
    .opHeadState (.slot .wt1) false,
    .opWorktreeRemove (.slot .repoA) (.slot .wt1) false false
  ]
]

private def verifyAbsPathspecParity : IO Unit := do
  let errRef ← IO.mkRef (none : Option String)
  let res ← LeanSwe.TempDir.withTempDir none "leanswe-git-abs-" fun rawDir => do
    let realRoot ← IO.FS.realPath rawDir
    let repo := realRoot.toString ++ "/repo"
    IO.FS.createDirAll (repo ++ "/sub")
    let api := LeanSwe.Git.defaultApi
    if let .error e := ← api.init repo false (some { raw := "main" }) then
      errRef.set (some s!"abs parity init failed: {repr e}")
      return .ok ()
    IO.FS.writeFile (repo ++ "/a.txt") "a1\n"
    IO.FS.writeFile (repo ++ "/sub/b.txt") "b1\n"
    if let .error e := ← api.add repo #[repo ++ "/a.txt", repo ++ "/sub/"] false then
      errRef.set (some s!"abs parity add1 failed: {repr e}")
      return .ok ()
    if let .error e := ← api.commit repo { message := "c1", authorName := some "Fuzz", authorEmail := some "fuzz@example.com" } then
      errRef.set (some s!"abs parity commit failed: {repr e}")
      return .ok ()
    IO.FS.writeFile (repo ++ "/a.txt") "a2\n"
    IO.FS.writeFile (repo ++ "/sub/b.txt") "b2\n"
    let dfAbs ← api.diffNameStatus repo "HEAD" none #[repo ++ "/a.txt"]
    let dfDirAbs ← api.diffNameStatus repo "HEAD" none #[repo ++ "/sub/"]
    match dfAbs, dfDirAbs with
    | .ok a, .ok b =>
      if a != #[{ kind := .modified, path := "a.txt" }] ||
          b != #[{ kind := .modified, path := "sub/b.txt" }] then
        errRef.set (some s!"abs parity diff mismatch: {repr dfAbs} {repr dfDirAbs}")
        return .ok ()
    | _, _ =>
      errRef.set (some s!"abs parity diff error: {repr dfAbs} {repr dfDirAbs}")
      return .ok ()
    if let .error e := ← api.add repo #[repo] false then
      errRef.set (some s!"abs parity add repo root failed: {repr e}")
      return .ok ()
    return .ok ()
  match res with
  | .error e => throw (IO.userError s!"GIT_FUZZ_ABS_PATHSPEC_ERROR: {e.message}")
  | .ok () =>
    if let some msg ← errRef.get then
      throw (IO.userError s!"GIT_FUZZ_ABS_PATHSPEC_ERROR: {msg}")

private def mockGitFaultOutput : GitErrorKind → Except GitError GitRawOutput
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

private def isProvedImpossibleGitCell (opName : String) (kind : GitErrorKind) : Bool :=
  (opName == "isRepo" && kind == .notARepo) ||
  (opName == "clone" && kind == .invalidPath) ||
  (kind == .parseError &&
    #["isRepo", "isAncestor", "init", "clone", "add", "createBranch", "deleteBranch",
      "checkout", "switch", "reset", "fetch", "worktreeAdd", "worktreeRemove"].contains opName)

private def runMockedGitErrorProbes : IO Unit := do
  let dummyCid : CommitId := { hex := "0123456789abcdef0123456789abcdef01234567" }
  let mainRef : RefName := { raw := "main" }
  let longInvalidPath : String := String.ofList (List.replicate 5000 'a')
  let mut hugeInvalidPath : String := String.ofList (List.replicate 1024 'a')
  for _ in List.range 8 do
    hugeInvalidPath := hugeInvalidPath ++ hugeInvalidPath
  let allKinds : Array GitErrorKind := #[
    .notARepo, .invalidRef, .invalidPath, .invalidInput, .dirtyWorktree,
    .nothingToCommit, .branchInUse, .alreadyExists, .notFound, .conflict,
    .timeout, .commandFailed, .parseError
  ]
  let opsFor (repoPath initPath cloneSrc : String) : Array (String × (GitApi → IO (Except GitError Unit))) := #[
    ("isRepo", fun a => (·.map fun _ => ()) <$> a.isRepo repoPath),
    ("repoRoot", fun a => (·.map fun _ => ()) <$> a.repoRoot repoPath),
    ("commonDir", fun a => (·.map fun _ => ()) <$> a.commonDir repoPath),
    ("headCommit?", fun a => (·.map fun _ => ()) <$> a.headCommit? repoPath),
    ("headBranch?", fun a => (·.map fun _ => ()) <$> a.headBranch? repoPath),
    ("headState", fun a => (·.map fun _ => ()) <$> a.headState repoPath),
    ("revParseCommit", fun a => (·.map fun _ => ()) <$> a.revParseCommit repoPath "HEAD"),
    ("isAncestor", fun a => (·.map fun _ => ()) <$> a.isAncestor repoPath dummyCid dummyCid),
    ("mergeBase?", fun a => (·.map fun _ => ()) <$> a.mergeBase? repoPath dummyCid dummyCid),
    ("status", fun a => (·.map fun _ => ()) <$> a.status repoPath),
    ("diffNameStatus", fun a => (·.map fun _ => ()) <$> a.diffNameStatus repoPath "HEAD" none #[]),
    ("listWorktrees", fun a => (·.map fun _ => ()) <$> a.listWorktrees repoPath),
    ("showFile?", fun a => (·.map fun _ => ()) <$> a.showFile? repoPath "HEAD" "file.txt"),
    ("init", fun a => a.init initPath false none),
    ("clone", fun a => a.clone cloneSrc "/mock/dst" {}),
    ("add", fun a => a.add repoPath #["file.txt"] false),
    ("commit", fun a => (·.map fun _ => ()) <$> a.commit repoPath { message := "msg" }),
    ("createBranch", fun a => a.createBranch repoPath mainRef none false),
    ("deleteBranch", fun a => a.deleteBranch repoPath mainRef false),
    ("checkout", fun a => a.checkout repoPath (.branch mainRef) false),
    ("switch", fun a => a.switch repoPath mainRef false none false),
    ("reset", fun a => a.reset repoPath .hard "HEAD"),
    ("fetch", fun a => a.fetch repoPath "origin" none false),
    ("worktreeAdd", fun a => a.worktreeAdd repoPath { path := "/mock/wt", detach := true }),
    ("worktreeRemove", fun a => a.worktreeRemove repoPath "/mock/wt" false),
    ("withWorktree", fun a => a.withWorktree repoPath { path := "/mock/wt", detach := true } fun _ =>
      pure (.error { kind := .parseError, message := "mock withWorktree callback parseError" }))
  ]
  for kind in allKinds do
    let (repoPath, initPath, cloneSrc) :=
      match kind with
      | .invalidPath => ("", "", "/mock/src")
      | .invalidInput => (longInvalidPath, hugeInvalidPath, "-evil")
      | _ => ("/mock/repo", "/mock/repo", "/mock/src")
    let api := Impl.mkApiM { listEnv := pure (.ok #[]), execGit := fun _ _ => pure (mockGitFaultOutput kind) }
    for (opName, act) in opsFor repoPath initPath cloneSrc do
      if isProvedImpossibleGitCell opName kind then
        continue
      let res ← act api
      match res with
      | .error e =>
        if e.kind != kind || e.message.isEmpty then
          throw (IO.userError s!"GIT_MOCK_PROBE_MISMATCH: {opName} expected {repr kind}, got {repr e}")
        logGitErr true opName res "mocked"
      | .ok () =>
        throw (IO.userError s!"GIT_MOCK_PROBE_UNEXPECTED_OK: {opName} expected {repr kind}")

private def runSmokeFuzz (cfg : FuzzConfig) : IO Unit := do
  runMockedGitErrorProbes
  verifyAbsPathspecParity
  let reg2 := mkAttrAndSubmoduleRegressionTraces ()
  let mut tracker ← runTraceOrShrink cfg.seed CoverageTracker.empty warmupCorpus
  for trace in worktreeAndIgnoreRegressionTraces do
    tracker ← runTraceOrShrink cfg.seed tracker trace
  for trace in reg2 do
    tracker ← runTraceOrShrink cfg.seed tracker trace
  assertCoverage "git" tracker requiredBuckets
  safePrintln (tracker.formatReport "git")
  let reg1Steps := worktreeAndIgnoreRegressionTraces.foldl (fun acc t => acc + t.size) warmupCorpus.size
  let totalSteps := reg2.foldl (fun acc t => acc + t.size) reg1Steps
  Fuzz.Common.recordSuiteSteps totalSteps
  safePrintln s!"FUZZ_SUMMARY suite=git mode=smoke steps={totalSteps} seed={cfg.seed}"

private def runFullFuzz (cfg : FuzzConfig) : IO Unit := do
  runMockedGitErrorProbes
  verifyAbsPathspecParity
  let reg2 := mkAttrAndSubmoduleRegressionTraces ()
  let mut smokeTracker ← runTraceOrShrink cfg.seed CoverageTracker.empty warmupCorpus
  for trace in worktreeAndIgnoreRegressionTraces do
    smokeTracker ← runTraceOrShrink cfg.seed smokeTracker trace
  for trace in reg2 do
    smokeTracker ← runTraceOrShrink cfg.seed smokeTracker trace
  assertCoverage "git.smoke" smokeTracker requiredBuckets
  let mut randTracker := CoverageTracker.empty
  let mut rng := Rng.seed cfg.seed
  let mut done := 0
  while done < cfg.steps do
    let (epLenRaw, rEp) := rng.nextRange 24 48
    rng := rEp
    let epLen := min epLenRaw (cfg.steps - done)
    let mut trace : Array GitFuzzStep := Array.mkEmpty (epLen + 5)
    let (preInit, rPre) := rng.chance 85 100
    let (seedCommit, rSeed) := if preInit then rPre.chance 50 100 else (false, rPre)
    rng := rSeed
    let mut ctx : GenContext := {
      hasRepoA := preInit
      commitHint := if seedCommit then 1 else 0
      liveFiles := if seedCommit then #["a.txt"] else #[]
      liveDirs := if seedCommit then #["emptyDir"] else #[]
    }
    if preInit then
      trace := trace.push (.opInit (.slot .repoA) false none false)
      if seedCommit then
        trace := trace.push (.vfsWriteFile .repoA "a.txt".toUTF8 "seed\n".toUTF8 false)
        trace := trace.push (.vfsMkdir .repoA "emptyDir".toUTF8)
        trace := trace.push (.opAdd (.slot .repoA) #["a.txt"] false false)
        trace := trace.push (.opCommit (.slot .repoA) { message := "seed" } false)
    for _ in List.range epLen do
      let (step, ctx', rStep) := genGitFuzzStep rng ctx
      rng := rStep
      ctx := ctx'
      trace := trace.push step
    randTracker ← runTraceOrShrink cfg.seed randTracker trace
    done := done + epLen
  safePrintln (randTracker.formatReport "git.random")
  if cfg.steps >= 3000 then
    assertCoverage "git.random" randTracker requiredBuckets
  let merged := smokeTracker.merge randTracker
  assertCoverage "git" merged requiredBuckets
  safePrintln (merged.formatReport "git")
  safePrintln s!"FUZZ_SUMMARY suite=git mode=full steps={cfg.steps} seed={cfg.seed}"

/-- Verify delta shrinking reduces an injected fault trace using real `runTrace`, tag pinning, and `shrinkStep`. -/
def runGitSelfTestShrink (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut ctx : GenContext := {}
  let mut randomTrace : Array GitFuzzStep := Array.mkEmpty 20
  for _ in List.range 18 do
    let (st, ctx', r') := genGitFuzzStep rng ctx
    rng := r'
    ctx := ctx'
    randomTrace := randomTrace.push st
  let (insertPos, _) := rng.nextRange 2 16
  let markerName := "__shrink_marker__.txt"
  let injected : Array GitFuzzStep :=
    #[.opInit (.slot .repoA) false none true] ++
    randomTrace.extract 0 insertPos ++
    #[.vfsWriteFile .repoA markerName.toUTF8 "long marker content\n".toUTF8 true,
      .opAdd (.slot .repoA) #[markerName] false true,
      .opCommit (.slot .repoA) { message := "long commit msg", allowEmpty := false } true] ++
    randomTrace.extract insertPos randomTrace.size
  let evalTaggedFault (cand : Array GitFuzzStep) : IO (Option String) := do
    let mut initialized := false
    let mut hasMarker := false
    let mut added := false
    let mut committed := false
    let mut decoy := false
    for step in cand do
      match step with
      | .opInit (.slot .repoA) false _ _ => initialized := true
      | .vfsWriteFile .repoA rel _ _ =>
        if initialized && rel == markerName.toUTF8 then
          hasMarker := true
      | .opAdd (.slot .repoA) ps _ _ =>
        if initialized && hasMarker && ps.contains markerName then
          added := true
      | .opCommit (.slot .repoA) _ _ =>
        if added then
          committed := true
      | .opDiffNameStatus _ (.raw "missing") _ _ _ => decoy := true
      | _ => pure ()
    if !(initialized && hasMarker && added && committed) then
      if decoy then return some "decoy:otherTag"
      return none
    match ← runTrace CoverageTracker.empty cand 0 with
    | .ok _ => return some "selfTest:markerCommit"
    | .error _ => return none
  let origTag := "selfTest:markerCommit"
  let triggersPinnedBug (cand : Array GitFuzzStep) : IO Bool := do
    match ← evalTaggedFault cand with
    | some tag' => return tag' == origTag
    | none => return false
  let decoyFails ← triggersPinnedBug #[.opDiffNameStatus (.slot .repoA) (.raw "missing") none #[] false]
  if decoyFails then
    throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: decoy tag was not rejected")
  if !(shrinkStep (.opTimeoutProbe (.subRel .repoA ".") 7)).any (fun s =>
      match s with | .opTimeoutProbe (.slot .repoA) 7 => true | .opTimeoutProbe _ 3 => true | _ => false) then
    throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: opTimeoutProbe shrinkStep regression")
  if !(shrinkStep (.opDiffNameStatus (.subRel .repoA "x") (.raw "main") (some (.raw "HEAD")) #["a.txt"] true)).any (fun s =>
      match s with | .opDiffNameStatus (.slot .repoA) _ _ _ _ => true | .opDiffNameStatus _ (.raw "HEAD") _ _ _ => true | _ => false) then
    throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: opDiffNameStatus shrinkStep regression")
  let wwtSample : GitFuzzStep :=
    .opWithWorktree (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) none true true
      [.opShowFile (.slot .wt1) (.raw "HEAD") "x.txt" false] false false
  if !(shrinkStep wwtSample).contains (.opShowFile (.slot .repoA) (.raw "HEAD") "x.txt" false) then
    throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: opWithWorktree inner-lift shrinkStep regression")
  if !(shrinkStep (.opCheckout (.slot .repoA) (.commitIdx 6 none) false false)).contains
      (.opCheckout (.slot .repoA) (.commitIdx 1 none) false false) then
    throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: commitIdx modulo shrinkStep regression")
  match ← verifyShrinker triggersPinnedBug injected 4 with
  | .error msg => throw (IO.userError s!"GIT_SHRINK_SELFTEST_FAILED: {msg}")
  | .ok shrunk =>
    let shrunkElem ← shrinkElements shrinkStep triggersPinnedBug shrunk
    let finalShrunk ← shrinkTrace triggersPinnedBug shrunkElem
    if finalShrunk.size > 4 then
      throw (IO.userError s!"GIT_SHRINK_SELFTEST_SIZE_FAILED: got {finalShrunk.size}")
    for st in finalShrunk do
      if stepHasPoisonEnv st then
        throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: poisonEnv was not minimized")
      match st with
      | .vfsWriteFile _ _ body ex =>
        if ex || body.size > 1 then
          throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: vfsWriteFile payload was not minimized")
      | .opCommit _ o _ =>
        if o.message.length > 2 then
          throw (IO.userError "GIT_SHRINK_SELFTEST_FAILED: opCommit message was not minimized")
      | _ => pure ()
    let wwtInjected : Array GitFuzzStep :=
      #[.opInit (.slot .repoA) false none true,
        .vfsWriteFile .repoA "seed.txt".toUTF8 "seed\n".toUTF8 true,
        .opAdd (.slot .repoA) #["seed.txt"] false true,
        .opCommit (.slot .repoA) { message := "seed msg" } true,
        .opWithWorktree (.slot .repoA) (.slot .wt1) (some (.raw "HEAD")) none true true
          [.vfsWriteFile .wt1 markerName.toUTF8 "long inner content\n".toUTF8 true,
           .opAdd (.slot .wt1) #[markerName] false true,
           .opCommit (.slot .wt1) { message := "long inner commit" } true]
          false true]
    let evalWwtFault (cand : Array GitFuzzStep) : IO Bool := do
      let flatSteps : List GitFuzzStep :=
        cand.toList.flatMap fun s =>
          match s with
          | .opWithWorktree _ _ _ _ _ _ ins _ _ => ins
          | other => [other]
      let mut hasInit := false
      let mut hasWrite := false
      let mut hasAdd := false
      let mut hasCommit := false
      for s in flatSteps do
        match s with
        | .opInit (.slot .repoA) false _ _ => hasInit := true
        | .vfsWriteFile sl rel _ _ =>
          if hasInit && (sl == .repoA || sl == .wt1) && rel == markerName.toUTF8 then
            hasWrite := true
        | .opAdd (.slot sl) ps _ _ =>
          if hasWrite && (sl == .repoA || sl == .wt1) && ps.contains markerName then
            hasAdd := true
        | .opCommit (.slot sl) o _ =>
          if hasAdd && (sl == .repoA || sl == .wt1) && o.message != "seed msg" then
            hasCommit := true
        | _ => pure ()
      if !(hasInit && hasWrite && hasAdd && hasCommit) then
        return false
      match ← runTrace CoverageTracker.empty cand 0 with
      | .ok _ => return true
      | .error _ => return false
    let mut wwtCur ← shrinkTrace evalWwtFault wwtInjected
    for _ in List.range 6 do
      let mut spliced := wwtCur
      for cand in spliceWithWorktreeSteps wwtCur do
        if ← evalWwtFault cand then
          spliced ← shrinkTrace evalWwtFault cand
          break
      let elShrunk ← shrinkElements shrinkStep evalWwtFault spliced
      let nxt ← shrinkTrace evalWwtFault elShrunk
      if nxt == wwtCur then
        break
      wwtCur := nxt
    if wwtCur.size != 4 || wwtCur.any (fun s => match s with | .opWithWorktree .. => true | _ => false) then
      throw (IO.userError s!"GIT_SHRINK_SELFTEST_FAILED: withWorktree splice failed ({wwtCur.size} steps)")
    safePrintln s!"GIT_SHRINK_SELFTEST_OK: original={injected.size} shrunk={finalShrunk.size} wwtShrunk={wwtCur.size}"

/-- Registered `git` stateful differential fuzzing suite comparing `LeanSwe.Git` against `GitRepoState`. -/
def suite : FuzzSuite := {
  name := "git"
  description := "Stateful differential fuzzer comparing LeanSwe.Git against pure GitRepoState over real git"
  runSmoke := runSmokeFuzz
  runFuzz := runFullFuzz
  selfTestShrink := runGitSelfTestShrink
}

end Fuzz.Git
