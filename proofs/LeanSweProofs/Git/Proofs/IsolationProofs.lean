import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests
import LeanSweProofs.Git.Proofs.ParserProofs
set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private theorem hasNulChar_append (a b : List Char) :
    hasNulChar (a ++ b) = (hasNulChar a || hasNulChar b) := by
  induction a with
  | nil => simp [hasNulChar]
  | cons c cs ih =>
    simp [hasNulChar, ih, Bool.or_assoc]

private theorem hasNulChar_of_mem {cs : List Char} (h : ∀ c ∈ cs, c ≠ Char.ofNat 0) :
    hasNulChar cs = false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c List.mem_cons_self
    have hcs := ih (fun x hx => h x (List.mem_cons_of_mem c hx))
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [hasNulChar, hbeq, hcs]

private theorem mem_of_hasNulChar_false {cs : List Char} (h : hasNulChar cs = false) :
    ∀ c ∈ cs, c ≠ Char.ofNat 0 := by
  induction cs with
  | nil => intro _ hc; cases hc
  | cons x xs ih =>
    simp only [hasNulChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hxs
    · exact h.1
    · exact ih h.2 c hxs

private theorem hasNulChar_of_subset {a b : List Char} (hsub : ∀ c ∈ a, c ∈ b)
    (hb : hasNulChar b = false) : hasNulChar a = false :=
  hasNulChar_of_mem (fun c hc => mem_of_hasNulChar_false hb c (hsub c hc))

private theorem isValidPathArg_of_ne_nil_no_nul (s : String) (hne : s.toList ≠ [])
    (hnul : hasNulChar s.toList = false) : isValidPathArg s = true := by
  unfold isValidPathArg
  cases hl : s.toList with
  | nil => contradiction
  | cons _ _ => simp [hl] at hnul ⊢; exact hnul

private theorem isValidPathArg_of_subset_ne_nil {a b : String}
    (hne : a.toList ≠ []) (hsub : ∀ c ∈ a.toList, c ∈ b.toList ∨ c = '/')
    (hb : isValidPathArg b = true) : isValidPathArg a = true := by
  unfold isValidPathArg at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
  apply isValidPathArg_of_ne_nil_no_nul a hne
  apply hasNulChar_of_mem
  intro c hc
  rcases hsub c hc with hcb | rfl
  · exact mem_of_hasNulChar_false hb.2 c hcb
  · decide

private theorem dropWhile_eq_nil_head_eq {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.dropWhile p = []) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro _ hx; cases hx
  | cons y ys ih =>
    simp only [List.dropWhile] at h
    split at h
    · next hy =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hys
      · exact hy
      · exact ih h x hys
    · cases h

private theorem mem_of_mem_dropWhile_local {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : x ∈ xs.dropWhile p) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.dropWhile] at h
    split at h
    · exact List.mem_cons_of_mem a (ih h)
    · exact h

private theorem isValidPathArg_stripTrailingSlashes (s : String) (hs : isValidPathArg s = true) :
    isValidPathArg (stripTrailingSlashes s) = true ∧ (stripTrailingSlashes s).toList ≠ [] := by
  have hs' := hs
  unfold isValidPathArg at hs'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs'
  rcases hs' with ⟨hneList, _⟩
  unfold stripTrailingSlashes
  dsimp only
  cases hrev : s.toList.reverse.dropWhile (· == '/') with
  | nil =>
    have hall : ∀ c ∈ s.toList, c = '/' := fun c hc =>
      beq_iff_eq.mp (dropWhile_eq_nil_head_eq hrev c (List.mem_reverse.mpr hc))
    cases hsl : s.toList with
    | nil => rw [hsl] at hneList; simp at hneList
    | cons c0 cs0 =>
      have hc0 : c0 = '/' := hall c0 (by rw [hsl]; exact List.mem_cons_self)
      subst hc0
      simp only [List.head?_cons, beq_self_eq_true, ↓reduceIte]
      exact ⟨by decide, by decide⟩
  | cons d ds =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    have hneL : (String.ofList (d :: ds).reverse).toList ≠ [] := by
      rw [String.toList_ofList]; simp
    refine ⟨?_, hneL⟩
    apply isValidPathArg_of_subset_ne_nil (b := s)
    · exact hneL
    · intro c hc
      rw [String.toList_ofList] at hc
      left
      have hcr : c ∈ s.toList.reverse.dropWhile (· == '/') := by
        rw [hrev]; exact List.mem_reverse.mp hc
      exact List.mem_reverse.mp (mem_of_mem_dropWhile_local hcr)
    · exact hs

private theorem ancestorLoop_head_eq (revPref : List Char) (acc : List String) (cs : List Char)
    (hne : revPref ≠ [] ∨ cs ≠ [])
    (hacc : ∀ s ∈ acc, s.length < (revPref.reverse ++ cs).length) :
    ∃ rest, ancestorLoop revPref acc cs = String.ofList (revPref.reverse ++ cs) :: rest := by
  induction cs generalizing revPref acc with
  | nil =>
    have hrev : revPref ≠ [] := by
      rcases hne with h | h
      · exact h
      · exact absurd rfl h
    have hEmptyF : revPref.isEmpty = false := by
      cases revPref with
      | nil => exact absurd rfl hrev
      | cons _ _ => rfl
    unfold ancestorLoop
    dsimp only
    simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
    have hHeadF : (acc.head? == some (String.ofList revPref.reverse)) = false := by
      cases ha : acc with
      | nil => rfl
      | cons hd tl =>
        dsimp only [List.head?]
        by_cases heq : hd = String.ofList revPref.reverse
        · subst heq
          have hlt := hacc (String.ofList revPref.reverse) (by rw [ha]; exact List.mem_cons_self)
          simp only [List.append_nil, String.length_ofList, List.length_reverse] at hlt
          omega
        · exact beq_false_of_ne (by intro h; injection h; contradiction)
    simp only [hHeadF, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ⟨acc, rfl⟩
  | cons c rest ih =>
    by_cases hslash : c = '/'
    · subst hslash
      unfold ancestorLoop
      dsimp only
      have hlist : ('/' :: revPref).reverse ++ rest = revPref.reverse ++ ('/' :: rest) := by simp
      rw [← hlist]
      refine ih ('/' :: revPref) _ (Or.inl (by simp)) ?_
      intro s hs
      split at hs
      · rw [hlist]; exact hacc s hs
      · rcases List.mem_cons.mp hs with rfl | hs'
        · simp only [List.length_append, List.length_reverse, List.length_cons, String.length_ofList]
          omega
        · rw [hlist]; exact hacc s hs'
    · have hLoop : ancestorLoop revPref acc (c :: rest) = ancestorLoop (c :: revPref) acc rest := by
        conv => lhs; unfold ancestorLoop
        split
        · contradiction
        · simp_all
        · simp_all
      rw [hLoop]
      have hlist : (c :: revPref).reverse ++ rest = revPref.reverse ++ c :: rest := by simp
      rw [← hlist]
      exact ih (c :: revPref) acc (Or.inl (by simp)) (by rw [hlist]; exact hacc)

private theorem ancestorCandidates_head_valid (p : String) (hp : isValidPathArg p = true) :
    ∃ rest, ancestorCandidates p = stripTrailingSlashes p :: rest ∧
      isValidPathArg (stripTrailingSlashes p) = true := by
  obtain ⟨hVal, hNonEmpty⟩ := isValidPathArg_stripTrailingSlashes p hp
  unfold ancestorCandidates
  dsimp only
  cases hsl : (stripTrailingSlashes p).toList with
  | nil => exact absurd hsl hNonEmpty
  | cons hd tl =>
    have hStrip : String.ofList (hd :: tl) = stripTrailingSlashes p := by
      rw [← hsl, String.ofList_toList]
    by_cases hslash : hd = '/'
    · subst hslash
      cases tl with
      | nil =>
        have hEq : stripTrailingSlashes p = "/" := by rw [← hStrip]
        exact ⟨[], by rw [hEq]; rfl, hVal⟩
      | cons r rs =>
        obtain ⟨rest, hres⟩ := ancestorLoop_head_eq ['/'] ["/"] (r :: rs) (Or.inl (by simp)) (by
          intro s hs
          rcases List.mem_singleton.mp hs with rfl
          simp [String.length])
        exact ⟨rest, by simpa [List.reverse_cons, List.reverse_nil, hStrip] using hres, hVal⟩
    · split
      · contradiction
      · simp_all
      · cases tl with
        | nil =>
          by_cases hdot : hd = '.'
          · subst hdot
            have hEq : stripTrailingSlashes p = "." := by rw [← hStrip]
            have hstep1 : ancestorLoop [] ["."] ['.'] = ["."] := by decide
            exact ⟨[], by simpa [hEq] using hstep1, hVal⟩
          · have hstep1 : ancestorLoop [] ["."] [hd] = ancestorLoop [hd] ["."] [] := by
              conv => lhs; unfold ancestorLoop
              split
              · contradiction
              · simp_all
              · simp_all
            have hstep2 : ancestorLoop [hd] ["."] [] = [String.ofList [hd], "."] := by
              unfold ancestorLoop
              dsimp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
                List.reverse_cons, List.reverse_nil, List.nil_append]
              have hneDot : (some "." == some (String.ofList [hd])) = false := by
                apply beq_false_of_ne
                intro h
                injection h with hs
                have hc := congrArg String.toList hs
                simp at hc
                exact hdot hc.symm
              simp only [List.reverse_singleton, hneDot, Bool.false_eq_true, ↓reduceIte]
            exact ⟨["."], by rw [hstep1, hstep2, hStrip], hVal⟩
        | cons r rs =>
          obtain ⟨rest, hres⟩ := ancestorLoop_head_eq [] ["."] (hd :: r :: rs) (Or.inr (by simp)) (by
            intro s hs
            rcases List.mem_singleton.mp hs with rfl
            simp [String.length])
          exact ⟨rest, by simpa [hStrip] using hres, hVal⟩

private theorem isValidPathArg_of_validateFsPathArg {p : String} (h : validateFsPathArg p = .ok ()) :
    isValidPathArg p = true := by
  unfold validateFsPathArg at h
  cases hv : isValidPathArg p with
  | true => rfl
  | false => simp [hv] at h

/-- Proof of `test_git_api_withWorktree_cleanupAndErrorPrecedence` for `Impl.mkApiM`. -/
theorem proof_git_api_withWorktree_cleanupAndErrorPrecedence :
    AllPass (test_git_api_withWorktree_cleanupAndErrorPrecedence (fun ops => Impl.mkApiM ops)) := by
  intro repoPath wtPath actOk cleanOk ⟨hRepoFs, hWtFs⟩
  have hRepo : isValidPathArg repoPath = true := isValidPathArg_of_validateFsPathArg hRepoFs
  have hWt : isValidPathArg wtPath = true := isValidPathArg_of_validateFsPathArg hWtFs
  have hRepo' : Impl.validateRepoPath repoPath = .ok () := by
    unfold Impl.validateRepoPath; rw [validateFsPathArgImpl_eq]; exact hRepoFs
  have hWt' : Impl.validateRepoPath wtPath = .ok () := by
    unfold Impl.validateRepoPath; rw [validateFsPathArgImpl_eq]; exact hWtFs
  have hCwdRepo : Impl.validateCwd? (some repoPath) = .ok () := by
    simp [Impl.validateCwd?, isValidPathArgImpl_eq, hRepo]
  have hExtra : Impl.validateExtraEnv #[] = .ok () := by unfold Impl.validateExtraEnv; simp
  have hNulWt : hasNulChar wtPath.toList = false := by
    simp [isValidPathArg] at hWt
    exact hWt.2
  let addArgs : Array String := #["worktree", "add", "--detach", "--", wtPath]
  let remArgs : Array String := #["worktree", "remove", "--", wtPath]
  let addReq : GitRawRequest := { cwd := some repoPath, args := addArgs }
  let remReq : GitRawRequest := { cwd := some repoPath, args := remArgs }
  have hArgsAdd : (addArgs.all fun a => !hasNulChar a.toList) = true := by
    rw [Array.all_eq_true]
    intro i hi
    match i with
    | 0 => simp [addArgs]; decide
    | 1 => simp [addArgs]; decide
    | 2 => simp [addArgs]; decide
    | 3 => simp [addArgs]; decide
    | 4 => simpa [addArgs] using hNulWt
    | _ + 5 => exfalso; simp [addArgs] at hi; omega
  have hArgsRem : (remArgs.all fun a => !hasNulChar a.toList) = true := by
    rw [Array.all_eq_true]
    intro i hi
    match i with
    | 0 => simp [remArgs]; decide
    | 1 => simp [remArgs]; decide
    | 2 => simp [remArgs]; decide
    | 3 => simpa [remArgs] using hNulWt
    | _ + 4 => exfalso; simp [remArgs] at hi; omega
  have hAddRaw :
      Impl.runGitRaw mockRawOps { cwd := some repoPath, args := #["worktree", "add", "--detach", "--", wtPath] } =
      (do
        match ← mockRawOps.listEnv with
        | .error e => return .error e
        | .ok inherited =>
          mockRawOps.execGit (cleanGitEnv inherited #[])
            { cwd := some repoPath, args := #["worktree", "add", "--detach", "--", wtPath] }) := by
    change Impl.runGitRaw mockRawOps addReq = _
    unfold Impl.runGitRaw
    rw [hCwdRepo, hExtra]
    simp only [addReq, addArgs, hasNulCharImpl_eq, cleanGitEnvImpl_eq, hArgsAdd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hRemRaw :
      Impl.runGitRaw mockRawOps { cwd := some repoPath, args := #["worktree", "remove", "--", wtPath] } =
      (do
        match ← mockRawOps.listEnv with
        | .error e => return .error e
        | .ok inherited =>
          mockRawOps.execGit (cleanGitEnv inherited #[])
            { cwd := some repoPath, args := #["worktree", "remove", "--", wtPath] }) := by
    change Impl.runGitRaw mockRawOps remReq = _
    unfold Impl.runGitRaw
    rw [hCwdRepo, hExtra]
    simp only [remReq, remArgs, hasNulCharImpl_eq, cleanGitEnvImpl_eq, hArgsRem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  let handlerFn : GitRawRequest → Nat → Except GitError GitRawOutput := fun req _ =>
    if req.args[1]? == some "add" then
      .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
    else if cleanOk then
      .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
    else
      .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 }
  let st₀ : GitCliMockState := { handler := handlerFn }
  have hAddC2 : (addArgs[1]? == some "add") = true := rfl
  have hRemC2 : (remArgs[1]? == some "add") = false := rfl
  let st2 : GitCliMockState :=
    { st₀ with
      recordedEnvs := st₀.recordedEnvs ++ [cleanGitEnv st₀.inheritedEnv #[]]
      recordedRequests := st₀.recordedRequests ++ [addReq]
      callCount := 1 }
  have hAddExec : Impl.worktreeAddImpl mockRawOps repoPath { path := wtPath, detach := true } st₀ =
      (.ok (), st2) := by
    unfold Impl.worktreeAddImpl Impl.runGitChecked
    simp only [hRepo', hWt', Option.isSome_none, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, pure,
      Array.append_empty]
    rw [show (#["worktree", "add"] ++ #["--detach"] ++ #["--", wtPath]) = addArgs from by simp [addArgs]]
    rw [hAddRaw]
    simp only [mockRawOps, st₀, handlerFn, addReq, addArgs, st2]
    rfl
  have hRemExecTrue : (hClean : cleanOk = true) →
      Impl.worktreeRemoveImpl mockRawOps repoPath wtPath false st2 =
        (.ok (), { st2 with
          recordedEnvs := st2.recordedEnvs ++ [cleanGitEnv st2.inheritedEnv #[]]
          recordedRequests := st2.recordedRequests ++ [remReq]
          callCount := 2 }) := by
    intro hClean
    unfold Impl.worktreeRemoveImpl Impl.runGitChecked
    simp only [hRepo', hWt', Bool.false_eq_true, ↓reduceIte, Array.append_empty,
      bind, StateT.bind, pure]
    rw [show (#["worktree", "remove"] ++ #["--", wtPath]) = remArgs from by simp [remArgs]]
    rw [hRemRaw]
    simp only [mockRawOps, bind, StateT.bind, pure, StateT.pure, st2, st₀, handlerFn,
      hRemC2, hClean, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true, remReq, remArgs]
  have hRemKind :
      (Impl.classifyError "worktree"
        { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 }).kind =
        .commandFailed := by
    cbv
  have hRemExecFalse : (hClean : cleanOk = false) →
      Impl.worktreeRemoveImpl mockRawOps repoPath wtPath false st2 =
        (.error (Impl.classifyError "worktree"
            { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 }),
          { st2 with
            recordedEnvs := st2.recordedEnvs ++ [cleanGitEnv st2.inheritedEnv #[]]
            recordedRequests := st2.recordedRequests ++ [remReq]
            callCount := 2 }) := by
    intro hClean
    unfold Impl.worktreeRemoveImpl Impl.runGitChecked
    simp only [hRepo', hWt', Bool.false_eq_true, ↓reduceIte, Array.append_empty,
      bind, StateT.bind, pure]
    rw [show (#["worktree", "remove"] ++ #["--", wtPath]) = remArgs from by simp [remArgs]]
    rw [hRemRaw]
    simp only [mockRawOps, bind, StateT.bind, pure, StateT.pure, st2, st₀, handlerFn,
      hRemC2, hClean, ↓reduceIte, Bool.false_eq_true, show ((1 : Int) == 0) = false from rfl,
      remReq, remArgs]
  have hWithTrue : (hClean : cleanOk = true) →
      ((Impl.mkApiM mockRawOps).withWorktree repoPath { path := wtPath, detach := true }
        (fun _ => if actOk then pure (.ok 42) else pure (.error { kind := .invalidInput, message := "action failed" }))).run st₀ =
        (if actOk then .ok 42 else .error { kind := .invalidInput, message := "action failed" },
         { st2 with
           recordedEnvs := st2.recordedEnvs ++ [cleanGitEnv st2.inheritedEnv #[]]
           recordedRequests := st2.recordedRequests ++ [remReq]
           callCount := 2 }) := by
    intro hClean
    dsimp only [Impl.mkApiM, Impl.withWorktreeImpl, StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure, MonadFinally.tryFinally']
    rw [hAddExec]
    dsimp only
    cases actOk
    · simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      rw [hRemExecTrue hClean]
    · simp only [↓reduceIte, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      rw [hRemExecTrue hClean]
      rfl
  have hWithFalse : (hClean : cleanOk = false) →
      ((Impl.mkApiM mockRawOps).withWorktree repoPath { path := wtPath, detach := true }
        (fun _ => if actOk then pure (.ok 42) else pure (.error { kind := .invalidInput, message := "action failed" }))).run st₀ =
        (if actOk then .error (Impl.classifyError "worktree" { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 })
         else .error { kind := .invalidInput, message := "action failed" },
         { st2 with
           recordedEnvs := st2.recordedEnvs ++ [cleanGitEnv st2.inheritedEnv #[]]
           recordedRequests := st2.recordedRequests ++ [remReq]
           callCount := 2 }) := by
    intro hClean
    dsimp only [Impl.mkApiM, Impl.withWorktreeImpl, StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure, MonadFinally.tryFinally']
    rw [hAddExec]
    dsimp only
    cases actOk
    · simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      rw [hRemExecFalse hClean]
    · simp only [↓reduceIte, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      rw [hRemExecFalse hClean]
      rfl
  dsimp only at hWithTrue hWithFalse ⊢
  by_cases hClean : cleanOk = true
  · rw [hWithTrue hClean]
    cases actOk <;> simp [assert, Bind.bind, hClean]
  · have hCleanF : cleanOk = false := Bool.eq_false_iff.mpr hClean
    rw [hWithFalse hCleanF]
    cases actOk
    · simp [assert, Bind.bind, hCleanF]
    · simp only [assert, Bind.bind, hCleanF, Bool.true_and, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨trivial, ⟨_, rfl, hRemKind⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_withWorktree_cleanupAndErrorPrecedence`. -/
theorem reach_git_api_withWorktree_cleanupAndErrorPrecedence :
    CanReach (test_git_api_withWorktree_cleanupAndErrorPrecedence (fun ops => Impl.mkApiM ops)) :=
  ⟨"/repo", "/wt", true, true, ⟨by cbv, by cbv⟩,
    proof_git_api_withWorktree_cleanupAndErrorPrecedence "/repo" "/wt" true true ⟨by cbv, by cbv⟩⟩

/-- Proof of `test_git_raw_mkApi_isolationAndGuards` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_isolationAndGuards :
    AllPass (test_git_raw_mkApi_isolationAndGuards (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_isolationAndGuards, AllPass, assert]
  let st₀ : GitCliMockState :=
    { inheritedEnv := #[("GIT_DIR", "/evil/.git"), ("LC_ALL", "fr_FR.UTF-8"), ("GIT_TERMINAL_PROMPT", "1"), ("PATH", "/usr/bin")]
      handler := fun req _ =>
        if req.args.toList.contains "commit" then
          .ok { exitCode := 1, stdout := "nothing to commit, working tree clean\n".toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "rev-parse" then
          .ok { exitCode := 0, stdout := (String.ofList (List.replicate 40 'a') ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "cat-file" then
          .ok { exitCode := 0, stdout := "tree\n".toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  have hCwdOk : Impl.validateCwd? (some "/repo") = .ok () := by
    unfold Impl.validateCwd?
    simp [isValidPathArgImpl_eq, show isValidPathArg "/repo" = true from by decide]
  have hExtraOk : Impl.validateExtraEnv #[] = .ok () := by
    unfold Impl.validateExtraEnv; simp
  have hEnvCheck :
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_DIR", none) ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("LC_ALL", none) ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("LC_ALL", some "C") ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_LITERAL_PATHSPECS", some "1") ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_CONFIG_VALUE_0", some "all") := by
    decide
  let commitOut : GitRawOutput :=
    { exitCode := 1, stdout := "nothing to commit, working tree clean\n".toUTF8, stderr := ByteArray.empty }
  let commitArgs : Array String := #["commit", "--no-gpg-sign", "-m", "msg"]
  have hCommitRun :
      ((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀ =
        (.error (Impl.classifyError "commit" commitOut),
         { st₀ with
           recordedEnvs := [cleanGitEnv st₀.inheritedEnv #[]]
           recordedRequests := [{ cwd := some "/repo", args := commitArgs }]
           callCount := 1 }) := by
    change Impl.commitImpl mockRawOps "/repo" { message := "msg" } st₀ = _
    have hOpts : validateCommitOptions { message := "msg" } = .ok () := by cbv
    have hExtraApp : (#[] ++ (#[] : Array (String × Option String))) = #[] := rfl
    have hArgs : (commitArgs.all fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["commit", "--no-gpg-sign", "-m", "msg"] (by decide)
    have hCont : (commitArgs.toList.contains "commit") = true := by decide
    unfold Impl.commitImpl Impl.runGitChecked Impl.runGitRaw
    simp only [hRepoOk, validateCommitOptionsImpl_eq, hasNulCharImpl_eq, cleanGitEnvImpl_eq, hOpts, Bool.false_eq_true, ↓reduceIte, Array.append_empty, hExtraApp,
      hCwdOk, hExtraOk, bind, StateT.bind, pure, mockRawOps, st₀]
    rw [show (#["commit", "--no-gpg-sign", "-m", "msg"].all fun a => !hasNulChar a.toList) = true from hArgs]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hCommit :
      ∃ e, (((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀).1 = .error e ∧
        e.kind = .nothingToCommit := by
    rw [hCommitRun]
    have hKind : (Impl.classifyError "commit" commitOut).kind = .nothingToCommit := by
      unfold Impl.classifyError
      dsimp only [commitOut]
      rw [show Impl.decodeUtf8Lossy ByteArray.empty = "" from rfl, decodeUtf8Lossy_toUTF8]
      cbv
    exact ⟨_, rfl, hKind⟩
  have hCommitEnv :
      ((((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀).2.recordedEnvs.all fun env =>
        env.toList.contains ("GIT_DIR", none) ∧
        env.toList.contains ("LC_ALL", none) ∧
        env.toList.contains ("LC_ALL", some "C") ∧
        env.toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
        env.toList.contains ("GIT_LITERAL_PATHSPECS", some "1") ∧
        env.toList.contains ("GIT_CONFIG_VALUE_0", some "all")) := by
    rw [hCommitRun]
    dsimp only [List.all, Bool.and_true]
    exact decide_eq_true hEnvCheck
  have hShowRun :
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD" "subdir").run st₀).1 = .ok none ∧
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD" "subdir").run st₀).2.callCount = 2 := by
    change (Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀).1 = .ok none ∧
      (Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀).2.callCount = 2
    have hRevValid : isValidRevSpec "HEAD" = true := by cbv
    have hStrictValid : isValidStrictRevSpec "HEAD" = true := by cbv
    have hRel : validateRelRepoPath "subdir" = .ok () := by cbv
    have hRevStr : ("HEAD" ++ "^{commit}") = "HEAD^{commit}" := rfl
    have hArgs1 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].all fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["rev-parse", "-q", "--verify", "HEAD^{commit}"] (by decide)
    have hC1 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].toList.contains "commit") = false := by decide
    have hC2 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].toList.contains "rev-parse") = true := by decide
    have hCid : mkCommitId (Impl.trimTrailingNewlines (String.ofList (List.replicate 40 'a') ++ "\n")) =
        .ok { hex := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" } := by
      rw [show Impl.trimTrailingNewlines (String.ofList (List.replicate 40 'a') ++ "\n") =
          "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" from by decide]
      unfold mkCommitId
      rw [show isValidCommitIdStr "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = true from by decide]
      rfl
    have hCatStr : (toString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++ toString ":" ++ toString "subdir") =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir" := rfl
    have hArgs2 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].all
        fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"] (by decide)
    have hD1 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "commit") = false := by decide
    have hD2 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "rev-parse") = false := by decide
    have hD3 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "cat-file") = true := by decide
    have hTrim : (Impl.trimAsciiWhitespace "tree\n" != "blob") = true := by decide
    have hShowEq : Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀ =
        (.ok none,
         { st₀ with
           recordedEnvs := [cleanGitEnv st₀.inheritedEnv #[], cleanGitEnv st₀.inheritedEnv #[]]
           recordedRequests :=
             [{ cwd := some "/repo", args := #["rev-parse", "-q", "--verify", "HEAD^{commit}"] },
              { cwd := some "/repo", args := #["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"] }]
           callCount := 2 }) := by
      unfold Impl.showFileImpl Impl.revParseCommitImpl
        Impl.runGitChecked Impl.runGitRaw
      simp only [hRepoOk, isValidStrictRevSpecImpl_eq, isValidRevSpecImpl_eq, validateRelRepoPathImpl_eq,
        hasNulCharImpl_eq, cleanGitEnvImpl_eq, mkCommitIdImpl_eq, hStrictValid, hRevValid, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, hRel, hCwdOk, hExtraOk, bind, StateT.bind, pure, mockRawOps, st₀]
      rw [hRevStr, hArgs1]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      rw [hC1, hC2]
      simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      rw [decodeUtf8Checked_toUTF8]
      dsimp only
      rw [hCid]
      dsimp only [bind, StateT.bind, pure, StateT.pure, mockRawOps]
      rw [hCatStr, hArgs2]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      rw [hD1, hD2, hD3]
      simp only [Bool.false_eq_true, ↓reduceIte, show (0 != (0 : Int)) = false from rfl]
      rw [decodeUtf8Checked_toUTF8]
      dsimp only
      rw [hTrim]
      simp only [↓reduceIte]
      rfl
    rw [hShowEq]
    exact ⟨rfl, rfl⟩
  have hFetch : ∃ e, (((Impl.mkApiM mockRawOps).fetch "/repo" "--upload-pack=evil" none false).run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).fetch "/repo" "--upload-pack=evil" none false).run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.fetchImpl mockRawOps "/repo" "--upload-pack=evil" none false st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.fetchImpl mockRawOps "/repo" "--upload-pack=evil" none false st₀).2.callCount = 0
    unfold Impl.fetchImpl
    rw [hRepoOk, isValidRemoteOrRefspecImpl_eq, show isValidRemoteOrRefspec "--upload-pack=evil" = false from by decide]
    exact ⟨_, rfl, rfl, rfl⟩
  have hAdd : ∃ e, (((Impl.mkApiM mockRawOps).add "/repo" #[] false).run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).add "/repo" #[] false).run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.addImpl mockRawOps "/repo" #[] false st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.addImpl mockRawOps "/repo" #[] false st₀).2.callCount = 0
    unfold Impl.addImpl
    rw [hRepoOk]
    exact ⟨_, rfl, rfl, rfl⟩
  have hColon : ∃ e, (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD:etc/passwd" "a").run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD:etc/passwd" "a").run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.showFileImpl mockRawOps "/repo" "HEAD:etc/passwd" "a" st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.showFileImpl mockRawOps "/repo" "HEAD:etc/passwd" "a" st₀).2.callCount = 0
    unfold Impl.showFileImpl
    rw [hRepoOk, isValidStrictRevSpecImpl_eq, show isValidStrictRevSpec "HEAD:etc/passwd" = false from by cbv]
    exact ⟨_, rfl, rfl, rfl⟩
  exact ⟨hCommit, hCommitEnv, hShowRun, hFetch, hAdd, hColon, trivial⟩


/-- `Impl.ensureNonEmptyMsg` always returns a non-empty string when `fallback ≠ ""`. -/
theorem proof_git_ensureNonEmptyMsg_nonEmpty (fallback msg : String) (hf : fallback ≠ "") :
    Impl.ensureNonEmptyMsg fallback msg ≠ "" := by
  unfold Impl.ensureNonEmptyMsg
  dsimp only
  split
  · exact hf
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- `Impl.classifyError` always produces a non-empty diagnostic message. -/
theorem proof_git_classifyError_nonEmptyMessage (cmd : String) (out : GitRawOutput) :
    (Impl.classifyError cmd out).message ≠ "" := by
  dsimp only [Impl.classifyError]
  refine proof_git_ensureNonEmptyMsg_nonEmpty _ _ ?_
  intro h
  have hl := congrArg String.length h
  have h4 : (toString ("git " : String)).length = 4 := rfl
  have h0 : ("" : String).length = 0 := rfl
  simp only [String.length_append, h4, h0] at hl
  omega

/-- `mapEnvVarsError` always produces a non-empty diagnostic message. -/
theorem proof_git_mapEnvVarsError_nonEmptyMessage (e : LeanSwe.EnvVars.EnvVarsError) :
    (mapEnvVarsError e).message ≠ "" := by
  unfold mapEnvVarsError
  dsimp only
  split
  · decide
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- `mapProcessError` always produces a non-empty diagnostic message. -/
theorem proof_git_mapProcessError_nonEmptyMessage (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (mapProcessError cmd e).message ≠ "" := by
  unfold mapProcessError
  dsimp only
  split
  · intro h
    have hl := congrArg String.length h
    have h4 : (toString ("git " : String)).length = 4 := rfl
    have h0 : ("" : String).length = 0 := rfl
    simp only [String.length_append, h4, h0] at hl
    omega
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

end LeanSwe.Git.Proofs
