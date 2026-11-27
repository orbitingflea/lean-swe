import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests
import LeanSweProofs.Git.Proofs.DagProofs

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

theorem proof_git_api_unbornHead_behavior :
    AllPass (test_git_api_unbornHead_behavior evalGitApi) := by
  intro s0 path branch hs0 hpath hbr _hInit
  subst hs0
  subst hpath
  have hValRepo : validateFsPathArg "/repo" = .ok () := by cbv
  have hResInit : resolveVfsFuel 41 VfsNode.emptyDir [] ["repo".toUTF8] true = .error .enoent := by cbv
  have hNotDots : (["repo".toUTF8].getLast? == some "..".toUTF8 || ["repo".toUTF8].getLast? == some ".".toUTF8) = false := by cbv
  have hMkdir : Model.mkdirPVfsFuel 41 VfsNode.emptyDir [] ["repo".toUTF8] =
      .ok (.dir true true [("repo".toUTF8, .dir true true [])], ["repo".toUTF8]) := by cbv
  have hMkdirGit : Model.mkdirPVfsFuel 41 (.dir true true [("repo".toUTF8, .dir true true [])])
      ["repo".toUTF8] [".git".toUTF8, "refs".toUTF8] =
      .ok (.dir true true [("repo".toUTF8, .dir true true [(".git".toUTF8, .dir true true [("refs".toUTF8, .dir true true [])])])],
        ["repo".toUTF8, ".git".toUTF8, "refs".toUTF8]) := by cbv
  have hsplit : splitByteSlash "/repo".toUTF8 = ["repo".toUTF8] := by cbv
  have hcwd : startsWithSlashByte "/repo".toUTF8 = true := by cbv
  have hcanon : joinAbsByteParts ["repo".toUTF8] = "/repo".toUTF8 := by cbv
  have hjoin : joinPathsBytes "/repo".toUTF8 ".git".toUTF8 = "/repo/.git".toUTF8 := by cbv
  have hLookupNone : lookupNodeAtParts VfsNode.emptyDir ["repo".toUTF8] = none := rfl
  simp only [hValRepo, hbr, ↓reduceIte, hcwd, hsplit, hResInit, hNotDots, hMkdir, hcanon,
    hLookupNone, Option.isSome_none, List.any_nil, Bool.false_eq_true, hMkdirGit, hjoin,
    List.nil_append]
  let sAfterInit : GitRepoState :=
    { ({} : GitRepoState) with
      vfs := .dir true true [("repo".toUTF8, .dir true true [(".git".toUTF8, .dir true true [("refs".toUTF8, .dir true true [])])])],
      repos := [{
        commonDir := "/repo/.git".toUTF8, isBare := false, commits := [], refs := [], symRefs := [], remotes := [],
        worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic branch }] }] }
  have hResVfs : resolveDirInVfs sAfterInit "/repo" = .ok ["repo".toUTF8] := by cbv
  have hJoinRepo : joinAbsByteParts ["repo".toUTF8] = "/repo".toUTF8 := by cbv
  have hCommonNe : ("/repo/.git".toUTF8 == "/repo".toUTF8) = false := by cbv
  have hLiveRepo : isLiveDirAtParts sAfterInit.vfs ["repo".toUTF8] = true := by cbv
  have hStripSelf : stripPathPrefixBytes "/repo".toUTF8 "/repo".toUTF8 = none := by cbv
  have hDisc : discoverRepoAtParts sAfterInit ["repo".toUTF8] =
      some ({
        commonDir := "/repo/.git".toUTF8, isBare := false, commits := [], refs := [], symRefs := [], remotes := [],
        worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic branch }] },
        some { rootPath := "/repo".toUTF8, head := .symbolic branch }, none) := by
    simp only [discoverRepoAtParts, discoverRepoAtParts.go, List.reverse_cons, List.reverse_nil,
      List.nil_append, sAfterInit, hJoinRepo, hCommonNe, Bool.false_eq_true, ↓reduceIte,
      beq_self_eq_true, hLiveRepo, List.head?, Bool.not_false, Bool.true_and, Bool.true_or,
      Bool.and_true, List.find?, List.findSome?, hStripSelf]
  have hHead : (evalGitApi.headCommit? "/repo").run sAfterInit = (.ok none, sAfterInit) := by
    simp only [evalGitApi, StateT.run, stepHeadCommit, resolveCwdAndDiscover, Bind.bind,
      Except.bind, pure, hValRepo, hResVfs, hDisc, activeHeadSlot, headCommitOfSymbolic,
      findBranchCommit?, lookupFullRef]
    rfl
  have hBranch : (evalGitApi.headBranch? "/repo").run sAfterInit = (.ok (some branch), sAfterInit) := by
    simp only [evalGitApi, StateT.run, stepHeadBranch, resolveCwdAndDiscover, Bind.bind,
      Except.bind, pure, hValRepo, hResVfs, hDisc, activeHeadSlot]
  have hRevHead : parseSupportedRevSpec "HEAD" = some { base := .head, steps := [] } := by cbv
  have hRevParse : (evalGitApi.revParseCommit "/repo" "HEAD").run sAfterInit =
      (.error { kind := .invalidRef, message := "unborn HEAD" }, sAfterInit) := by
    simp only [evalGitApi, StateT.run, stepRevParseCommit, hRevHead, resolveCwdAndDiscover,
      Bind.bind, Except.bind, pure, hValRepo, hResVfs, hDisc, activeHeadSlot,
      resolveParsedRevInRepo, headCommitOfSymbolic, findBranchCommit?, lookupFullRef,
      List.find?_nil]
  dsimp only [sAfterInit, StateT.run] at hHead hBranch hRevParse
  simp only [assert, Bind.bind]
  have hHead1 : (evalGitApi.headCommit? "/repo" sAfterInit).1 = .ok none := congrArg Prod.fst hHead
  have hBranch1 : (evalGitApi.headBranch? "/repo" sAfterInit).1 = .ok (some branch) := congrArg Prod.fst hBranch
  have hRevParse1 : (evalGitApi.revParseCommit "/repo" "HEAD" sAfterInit).1 =
      .error { kind := .invalidRef, message := "unborn HEAD" } := congrArg Prod.fst hRevParse
  exact ⟨hHead1, hBranch1, ⟨{ kind := .invalidRef, message := "unborn HEAD" }, hRevParse1, rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_unbornHead_behavior`. -/
theorem reach_git_api_unbornHead_behavior :
    CanReach (test_git_api_unbornHead_behavior evalGitApi) := by
  let branch : RefName := { raw := "main" }
  have hBr : isValidRefNameStr branch.raw = true := by decide
  have hInit : ((evalGitApi.init "/repo" false (some branch)).run {}).1 = .ok () := by cbv
  exact ⟨{}, "/repo", branch, rfl, rfl, hBr, hInit,
    proof_git_api_unbornHead_behavior {} "/repo" branch rfl rfl hBr hInit⟩

private theorem find?_setRefInList_self (refs : List (String × CommitId)) (name : String) (cid : CommitId) :
    (setRefInList refs name cid).find? (fun p => p.1 == name) = some (name, cid) := by
  unfold setRefInList
  split
  · next hany =>
    induction refs with
    | nil => simp at hany
    | cons p ps ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hany
      by_cases hp : (p.1 == name) = true
      · simp [List.map, hp]
      · have hpf : (p.1 == name) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, false_or] at hany
        simp only [List.map, hpf, Bool.false_eq_true, ↓reduceIte, List.find?]
        exact ih hany
  · next hnot =>
    induction refs with
    | nil => simp
    | cons p ps ih =>
      simp only [List.any_cons, Bool.or_eq_true, not_or] at hnot
      have hpf : (p.1 == name) = false := Bool.eq_false_iff.mpr hnot.1
      simp only [List.cons_append, List.find?, hpf, ih hnot.2]

private instance : ReflBEq GitBlobKind where
  rfl {a} := by cases a with | regular ex => cases ex <;> rfl | symlink => rfl | gitlink => rfl

private instance : ReflBEq GitTreeEntry where
  rfl {a} := by
    cases a with
    | mk k b =>
      change (k == k && b == b) = true
      simp

/-- Proof of `test_git_api_commit_emptyVsAllowEmpty` for `evalGitApi`. -/
theorem proof_git_api_commit_emptyVsAllowEmpty :
    AllPass (test_git_api_commit_emptyVsAllowEmpty evalGitApi) := by
  intro s0 repo wt c0 b _hValid ⟨hRepos, hBare, hCommon, hWts⟩ ⟨hRoot, hVfs⟩ ⟨hHead, hBr⟩ hIdx
  have hFresh := proof_git_freshSyntheticCommitId_not_hasCommit repo
  have hValRepo : validateFsPathArg "/repo" = .ok () := by cbv
  have hOptEmpty : validateCommitOptions { message := "empty", allowEmpty := false } = .ok () := by cbv
  have hOptAllow : validateCommitOptions { message := "allow", allowEmpty := true } = .ok () := by cbv
  have hCleanEmpty : cleanCommitMessageWhitespace "empty" = "empty\n" := by cbv
  have hCleanAllow : cleanCommitMessageWhitespace "allow" = "allow\n" := by cbv
  have hResDir : resolveDirInVfs s0 "/repo" = .ok ["repo".toUTF8] := by
    unfold resolveDirInVfs
    rw [hVfs]
    cbv
  have hNotBare : repo.isBare = false := by simpa using hBare
  have hJoinRepo : joinAbsByteParts ["repo".toUTF8] = "/repo".toUTF8 := by cbv
  have hJoinRoot : joinAbsByteParts ([] : List ByteArray) = "/".toUTF8 := by cbv
  have hCommonNe : (repo.commonDir == "/repo".toUTF8) = false := by rw [hCommon]; cbv
  have hCommonNeRoot : (repo.commonDir == "/".toUTF8) = false := by rw [hCommon]; cbv
  have hRootNeRoot : (wt.rootPath == "/".toUTF8) = false := by rw [hRoot]; cbv
  have hLiveRepo : isLiveDirAtParts s0.vfs ["repo".toUTF8] = true := by rw [hVfs]; cbv
  have hLiveRoot : isLiveDirAtParts s0.vfs [] = true := by rw [hVfs]; cbv
  have hStripSelf : stripPathPrefixBytes "/repo".toUTF8 "/repo".toUTF8 = none := by cbv
  have hDisc : discoverRepoAtParts s0 ["repo".toUTF8] = some (repo, some wt, none) := by
    simp only [discoverRepoAtParts, discoverRepoAtParts.go, List.reverse_cons, List.reverse_nil,
      List.nil_append, hRepos, hJoinRepo, hCommonNe, Bool.false_eq_true, ↓reduceIte, hNotBare,
      hWts, hRoot, beq_self_eq_true, hLiveRepo, List.head?, Bool.not_false, Bool.true_and,
      Bool.true_or, Bool.and_true, List.find?, List.findSome?, hStripSelf]
  have hEmpty : (evalGitApi.commit "/repo" { message := "empty", allowEmpty := false }).run s0 =
      (.error { kind := .nothingToCommit, message := "nothing to commit, working tree clean" }, s0) := by
    simp only [evalGitApi, StateT.run, stepCommitWithId, hValRepo, hOptEmpty, resolveCwdAndDiscover,
      Bind.bind, Except.bind, pure, hResDir, hDisc, Bool.false_eq_true, ↓reduceIte,
      hIdx, List.isEmpty_nil, Bool.not_true, headCommitOfSymbolic, hHead, hBr,
      beq_self_eq_true, Bool.not_false, Bool.and_true]
  let cid := freshSyntheticCommitId repo
  let repo1 : RepoInstance :=
    { repo with
      commits := repo.commits ++ [{ id := cid, parents := [c0], tree := sortByBytes (·.1) (treeOfCommit repo c0), message := "allow\n" }]
      refs := setRefInList repo.refs ("refs/heads/" ++ b.raw) cid }
  let repo2 : RepoInstance :=
    updateWorktreeInRepo repo1 wt.rootPath fun slot =>
      { slot with head := .symbolic b, index := { slot.index with hasMergeHead := false, mergeParents := [] } }
  let sOk : GitRepoState := { s0 with repos := updateRepoInList s0.repos repo.commonDir (fun _ => repo2) }
  have hAllowNonEmpty : ("allow\n" : String).isEmpty = false := by cbv
  have hCommitOk : (evalGitApi.commit "/repo" { message := "allow", allowEmpty := true }).run s0 =
      (.ok cid, sOk) := by
    simp only [evalGitApi, StateT.run, stepCommitWithId, hValRepo, hOptAllow, resolveCwdAndDiscover,
      Bind.bind, Except.bind, pure, hResDir, hDisc, Bool.false_eq_true, ↓reduceIte,
      hIdx, List.isEmpty_nil, Bool.not_true, headCommitOfSymbolic, hHead, hBr, beq_self_eq_true,
      Bool.and_false, Bool.false_and, Option.getD_none, hCleanAllow, hAllowNonEmpty, hFresh, cid, repo1, repo2, sOk]
  have hHeadOk : (evalGitApi.headCommit? "/repo").run sOk = (.ok (some cid), sOk) := by
    have hResDirOk : resolveDirInVfs sOk "/repo" = .ok ["repo".toUTF8] := by
      simpa [resolveDirInVfs, sOk] using hResDir
    have hFindRef : lookupFullRef repo2 ("refs/heads/" ++ b.raw) = some cid := by
      simp [lookupFullRef, repo2, updateWorktreeInRepo, repo1, find?_setRefInList_self]
    have hCommonRepo2Ne : ("/repo/.git".toUTF8 == "/repo".toUTF8) = false := by cbv
    have hDiscOk : discoverRepoAtParts sOk ["repo".toUTF8] =
        some (repo2, some { wt with head := .symbolic b, index := { wt.index with hasMergeHead := false, mergeParents := [] } }, none) := by
      simp only [discoverRepoAtParts, discoverRepoAtParts.go, List.reverse_cons, List.reverse_nil,
        List.nil_append, sOk, hRepos, updateRepoInList, hCommon, beq_self_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, hJoinRepo, repo2, updateWorktreeInRepo, repo1, hCommonRepo2Ne,
        Bool.false_eq_true, hNotBare, hWts, hRoot, hLiveRepo, List.head?, Bool.not_false,
        Bool.true_and, Bool.true_or, Bool.and_true, List.find?, List.findSome?, hStripSelf]
    simp only [evalGitApi, StateT.run, stepHeadCommit, resolveCwdAndDiscover, Bind.bind, Except.bind,
      pure, hValRepo, hResDirOk, hDiscOk, activeHeadSlot, headCommitOfSymbolic,
      findBranchCommit?, hFindRef]
  simp only [assert, hEmpty, hCommitOk, hHeadOk]
  exact ⟨⟨{ kind := .nothingToCommit, message := "nothing to commit, working tree clean" }, rfl, rfl, trivial⟩, trivial, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_commit_emptyVsAllowEmpty`. -/
theorem reach_git_api_commit_emptyVsAllowEmpty :
    CanReach (test_git_api_commit_emptyVsAllowEmpty evalGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { rootPath := "/repo".toUTF8, head := .symbolic b }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    refs := [("refs/heads/main", c0)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  exact ⟨s0, repo, wt, c0, b, hValid, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
    proof_git_api_commit_emptyVsAllowEmpty s0 repo wt c0 b hValid ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl⟩

private theorem takeWhile_eq_self_of_forall {α : Type} {p : α → Bool} (cs : List α)
    (h : ∀ x ∈ cs, p x = true) : cs.takeWhile p = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [List.takeWhile, h c List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem c hx))]

private theorem dropWhile_eq_nil_of_forall {α : Type} {p : α → Bool} (cs : List α)
    (h : ∀ x ∈ cs, p x = true) : cs.dropWhile p = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [List.dropWhile, h c List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem c hx))]

private theorem parseSupportedRevSpec_of_isValidRefNameStr {s : String} (h : isValidRefNameStr s = true) :
    ∃ pr, parseSupportedRevSpec s = some pr ∧
      (pr.base = .head ∨ pr.base = .commitId { hex := s } ∨ pr.base = .ref s) := by
  have hCopy := h
  unfold isValidRefNameStr at hCopy
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hCopy
  rcases hCopy with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hneEmpty, hle⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hbad⟩, _⟩, _⟩, _⟩, _⟩
  have hmem : ∀ c ∈ s.toList, (c != '~' && c != '^') = true := by
    intro c hc
    have hc1 : c ≠ '~' := by
      intro heq; subst heq
      have hinv : isInvalidRefChar '~' = true := by decide
      have : s.toList.any isInvalidRefChar = true := List.any_eq_true.mpr ⟨'~', hc, hinv⟩
      rw [this] at hbad; cases hbad
    have hc2 : c ≠ '^' := by
      intro heq; subst heq
      have hinv : isInvalidRefChar '^' = true := by decide
      have : s.toList.any isInvalidRefChar = true := List.any_eq_true.mpr ⟨'^', hc, hinv⟩
      rw [this] at hbad; cases hbad
    simp [bne_iff_ne, hc1, hc2]
  have htake : s.toList.takeWhile (fun c => c != '~' && c != '^') = s.toList :=
    takeWhile_eq_self_of_forall s.toList hmem
  have hdrop : s.toList.dropWhile (fun c => c != '~' && c != '^') = [] :=
    dropWhile_eq_nil_of_forall s.toList hmem
  have hnat : s.utf8ByteSize ≤ 1024 := decide_eq_true_eq.mp hle
  have hgt : decide (s.utf8ByteSize > 1024) = false := decide_eq_false (Nat.not_lt.mpr hnat)
  unfold parseSupportedRevSpec
  rw [hneEmpty, hgt]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, htake, hdrop, String.ofList_toList]
  have hp0 : parseRevStepsAux 1 [] = some [] := rfl
  simp only [List.length_nil, hp0]
  by_cases hh : (s == "HEAD" || s == "@") = true
  · exact ⟨{ base := .head, steps := [] }, by simp [hh], Or.inl rfl⟩
  · by_cases hc : isValidCommitIdStr s = true
    · exact ⟨{ base := .commitId { hex := s }, steps := [] }, by simp [hh, hc], Or.inr (Or.inl rfl)⟩
    · exact ⟨{ base := .ref s, steps := [] }, by simp [hh, hc, h], Or.inr (Or.inr rfl)⟩

/-- Proof of `test_git_api_worktreeAdd_branchInUseRejected` for `evalGitApi`. -/
theorem proof_git_api_worktreeAdd_branchInUseRejected :
    AllPass (test_git_api_worktreeAdd_branchInUseRejected evalGitApi) := by
  intro s0 repo wt b c _hValid ⟨hRepos, hBare, hCommon, hWts⟩ ⟨hRoot, hVfs⟩ ⟨hHead, hBr⟩ ⟨hRef, hNotHex⟩
  have hNotHexB : isValidCommitIdStr b.raw = false := by
    simpa [Bool.not_eq_true'] using hNotHex
  have hValRepo : validateFsPathArg "/repo" = .ok () := by cbv
  have hValWt2 : validateFsPathArg "/wt2" = .ok () := by cbv
  obtain ⟨pr, hpr, hprBase⟩ := parseSupportedRevSpec_of_isValidRefNameStr hRef
  have hResDir : resolveDirInVfs s0 "/repo" = .ok ["repo".toUTF8] := by
    unfold resolveDirInVfs; rw [hVfs]; cbv
  have hNotBare : repo.isBare = false := by simpa using hBare
  have hJoinRepo : joinAbsByteParts ["repo".toUTF8] = "/repo".toUTF8 := by cbv
  have hCommonNe : (repo.commonDir == "/repo".toUTF8) = false := by rw [hCommon]; cbv
  have hLiveRepo : isLiveDirAtParts s0.vfs ["repo".toUTF8] = true := by rw [hVfs]; cbv
  have hStripSelf : stripPathPrefixBytes "/repo".toUTF8 "/repo".toUTF8 = none := by cbv
  have hDisc : discoverRepoAtParts s0 ["repo".toUTF8] = some (repo, some wt, none) := by
    simp only [discoverRepoAtParts, discoverRepoAtParts.go, List.reverse_cons, List.reverse_nil,
      List.nil_append, hRepos, hJoinRepo, hCommonNe, Bool.false_eq_true, ↓reduceIte, hNotBare,
      hWts, hRoot, beq_self_eq_true, hLiveRepo, List.head?, Bool.not_false, Bool.true_and,
      Bool.true_or, Bool.and_true, List.find?, List.findSome?, hStripSelf]
  have hDest : resolveVfsFuel 41 s0.vfs [] (splitByteSlash "/wt2".toUTF8) true = .error .enoent := by
    rw [hVfs]; cbv
  have hDestNoFollow : resolveVfsFuel 41 s0.vfs [] (splitByteSlash "/wt2".toUTF8) false = .error .enoent := by
    rw [hVfs]; cbv
  have hMkdirWt2 : mkdirPVfsFuel 41 s0.vfs [] (splitByteSlash "/wt2".toUTF8) =
      .ok (.dir true true [("repo".toUTF8, .dir true true []), ("wt2".toUTF8, .dir true true [])], ["wt2".toUTF8]) := by
    rw [hVfs]; cbv
  have hNormWt2 : normalizeDotDotParts [] (splitByteSlash "/wt2".toUTF8) = ["wt2".toUTF8] := by cbv
  have hJoinWt2 : joinAbsByteParts ["wt2".toUTF8] = "/wt2".toUTF8 := by cbv
  have hRepoWt2Ne : ("/repo".toUTF8 == "/wt2".toUTF8) = false := by cbv
  have hAnyWt2 : (repo.worktrees.any fun w => w.rootPath == joinAbsByteParts ["wt2".toUTF8]) = false := by
    simp only [hWts, hRoot, hJoinWt2, List.any_cons, List.any_nil, hRepoWt2Ne, Bool.or_self]
  have hInUse : isBranchCheckedOutAnywhere repo b = true := by
    have hbb : (b == b) = true := by
      cases b with | mk bs => change (bs == bs) = true; simp
    simp [isBranchCheckedOutAnywhere, hNotBare, hWts, hHead, hbb]
  have hStartWt2 : startsWithSlashByte "/wt2".toUTF8 = true := by cbv
  have hLookupB : lookupFullRef repo ("refs/heads/" ++ b.raw) = some c := hBr
  have hTgtLen : ("/wt2" == "") = false := by cbv
  have hRes : (evalGitApi.worktreeAdd "/repo" { path := "/wt2", target? := some b.raw }).run s0 =
      (.error { kind := .branchInUse, message := s!"'{b.raw}' is already used by worktree" }, s0) := by
    simp only [evalGitApi, StateT.run, stepWorktreeAdd, hValRepo, hValWt2, Bool.not_false,
      Option.isSome_none, Option.isSome_some, Option.isNone_none, Option.isNone_some, Bool.and_false,
      Bool.and_true, Bool.false_and, Bool.false_eq_true, Bool.true_or, ↓reduceIte, hpr, resolveCwdAndDiscover, Bind.bind,
      Except.bind, pure, hResDir, hDisc,
      activeHeadSlot, hRef, hNotHexB, findBranchCommit?, hLookupB, Option.map_some, hStartWt2,
      hDest, hDestNoFollow, hNormWt2, hAnyWt2, hMkdirWt2, hInUse]
  simp only [assert, hRes]
  exact ⟨⟨{ kind := .branchInUse, message := s!"'{b.raw}' is already used by worktree" }, rfl, rfl, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_worktreeAdd_branchInUseRejected`. -/
theorem reach_git_api_worktreeAdd_branchInUseRejected :
    CanReach (test_git_api_worktreeAdd_branchInUseRejected evalGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { rootPath := "/repo".toUTF8, head := .symbolic b }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    refs := [("refs/heads/main", c0)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  exact ⟨s0, repo, wt, b, c0, hValid, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by decide,
    proof_git_api_worktreeAdd_branchInUseRejected s0 repo wt b c0 hValid ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)⟩

/-- Proof of `test_git_api_checkout_dirtyWorktreeRejected` for `evalGitApi`. -/
theorem proof_git_api_checkout_dirtyWorktreeRejected :
    AllPass (test_git_api_checkout_dirtyWorktreeRejected evalGitApi) := by
  intro s0 repo wt bMain bFeat c0 c1 _hValid ⟨hRepos, hBare, hCommon, hWts⟩ ⟨hRoot, hHead⟩
    ⟨hBrMain, hBrFeat⟩ ⟨_hNe, hRefFeat⟩ hTree0 hTree1 hIdx hVfs
  have hValRepo : validateFsPathArg "/repo" = .ok () := by cbv
  have hResDir : resolveDirInVfs s0 "/repo" = .ok ["repo".toUTF8] := by
    unfold resolveDirInVfs; rw [hVfs]; cbv
  have hNotBare : repo.isBare = false := by simpa using hBare
  have hJoinRepo : joinAbsByteParts ["repo".toUTF8] = "/repo".toUTF8 := by cbv
  have hCommonNe : (repo.commonDir == "/repo".toUTF8) = false := by rw [hCommon]; cbv
  have hLiveRepo : isLiveDirAtParts s0.vfs ["repo".toUTF8] = true := by rw [hVfs]; cbv
  have hStripSelf : stripPathPrefixBytes "/repo".toUTF8 "/repo".toUTF8 = none := by cbv
  have hDisc : discoverRepoAtParts s0 ["repo".toUTF8] = some (repo, some wt, none) := by
    simp only [discoverRepoAtParts, discoverRepoAtParts.go, List.reverse_cons, List.reverse_nil,
      List.nil_append, hRepos, hJoinRepo, hCommonNe, Bool.false_eq_true, ↓reduceIte, hNotBare,
      hWts, hRoot, beq_self_eq_true, hLiveRepo, List.head?, Bool.not_false, Bool.true_and,
      Bool.true_or, Bool.and_true, List.find?, List.findSome?, hStripSelf]
  have hNotElsewhere : isBranchInUseElsewhere repo wt.rootPath bFeat = false := by
    simp [isBranchInUseElsewhere, hNotBare, hWts]
  have hApply : Model.applyTwoTreeCheckoutWithPerm s0.vfs wt (treeOfCommit repo c0) (treeOfCommit repo c1) false s0.repos =
      .error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" } := by
    unfold Model.applyTwoTreeCheckoutWithPerm
    rw [hVfs, hRoot, hIdx, hTree0, hTree1]
    cbv
  have hLookupFeat : lookupFullRef repo ("refs/heads/" ++ bFeat.raw) = some c1 := hBrFeat
  have hLookupMain : lookupFullRef repo ("refs/heads/" ++ bMain.raw) = some c0 := hBrMain
  have hRes : (evalGitApi.checkout "/repo" (.branch bFeat) false).run s0 =
      (.error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }, s0) := by
    simp only [evalGitApi, StateT.run, stepCheckout, hValRepo, hRefFeat, ↓reduceIte,
      resolveCwdAndDiscover, Bind.bind, Except.bind, pure, hResDir, hDisc,
      Bool.false_eq_true, findBranchCommit?, hLookupFeat, hNotElsewhere, Bool.false_and, hIdx, List.isEmpty_nil,
      Bool.not_true, Bool.not_false, Bool.and_false, headCommitOfSymbolic, hHead, hLookupMain, hApply]
  simp only [assert, hRes]
  exact ⟨⟨{ kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }, rfl, rfl, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_checkout_dirtyWorktreeRejected`. -/
theorem reach_git_api_checkout_dirtyWorktreeRejected :
    CanReach (test_git_api_checkout_dirtyWorktreeRejected evalGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let c1 : CommitId := { hex := "0000000000000000000000000000000000000001" }
  let bMain : RefName := { raw := "main" }
  let bFeat : RefName := { raw := "feat" }
  let e0 : GitTreeEntry := { kind := .regular false, bytes := "v0".toUTF8 }
  let e1 : GitTreeEntry := { kind := .regular false, bytes := "v1".toUTF8 }
  let wt : WorktreeSlot := {
    rootPath := "/repo".toUTF8
    head := .symbolic bMain
    index := { entries := [("a.txt".toUTF8, e0)] }
  }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [
      { id := c0, parents := [], tree := [("a.txt".toUTF8, e0)] },
      { id := c1, parents := [c0], tree := [("a.txt".toUTF8, e1)] }
    ]
    refs := [("refs/heads/main", c0), ("refs/heads/feat", c1)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [("a.txt".toUTF8, .file false "dirty".toUTF8)])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  exact ⟨s0, repo, wt, bMain, bFeat, c0, c1, hValid, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨by decide, by decide⟩, rfl, rfl, rfl, rfl,
    proof_git_api_checkout_dirtyWorktreeRejected s0 repo wt bMain bFeat c0 c1 hValid
      ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ rfl rfl rfl rfl⟩


end LeanSwe.Git.Proofs
