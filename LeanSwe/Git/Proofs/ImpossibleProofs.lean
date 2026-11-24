import Core.Assumptions
import LeanSwe.EnvVars.Proofs
import LeanSwe.Process.Proofs.EndToEnd
import LeanSwe.Process.Interface
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open LeanSwe.Git

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem envvars_listEnv_never_throws (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.listEnv w = EST.Out.ok res w' := by
  have h := LeanSwe.EnvVars.Proofs.envvars_listEnv_never_notFound w
  unfold Core.NeverErrorKindIO at h
  cases hr : LeanSwe.EnvVars.listEnv w with
  | ok res w' => exact ⟨res, w', rfl⟩
  | error e w' => rw [hr] at h; exact False.elim h

private theorem process_run_never_throws (req : LeanSwe.Process.ExecRequest)
    (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.run req w = EST.Out.ok res w' :=
  LeanSwe.Process.Proofs.process_run_never_throws req w

private theorem defaultRawOps_listEnv_res (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultRawOps.listEnv w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultRawOps]
  rcases envvars_listEnv_never_throws w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok env => exact ⟨.ok env, w', rfl, fun _ h => by cases h⟩
  | error e => exact ⟨.error (LeanSwe.Git.mapEnvVarsError e), w', rfl, fun _ h => by cases h; rfl⟩

private theorem mapProcessError_kinds (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (LeanSwe.Git.mapProcessError cmd e).kind = .timeout ∨
    (LeanSwe.Git.mapProcessError cmd e).kind = .invalidInput ∨
    (LeanSwe.Git.mapProcessError cmd e).kind = .commandFailed := by
  dsimp only [LeanSwe.Git.mapProcessError]
  cases e.kind <;> simp

private theorem defaultRawOps_execGit_res (envOverrides : Array (String × Option String))
    (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.defaultRawOps.execGit envOverrides req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        e.kind = .timeout ∨ e.kind = .invalidInput ∨ e.kind = .commandFailed := by
  dsimp only [LeanSwe.Git.defaultRawOps]
  rcases process_run_never_throws
      { program := "git", args := req.args, cwd := req.cwd, env := envOverrides,
        stdin := req.stdin, timeoutMs := req.timeoutMs, maxOutputBytes := req.maxOutputBytes } w with ⟨res, w', hw⟩
  rw [io_bind_ok _ _ _ hw]
  cases res with
  | ok out => exact ⟨_, w', rfl, fun _ h => by cases h⟩
  | error e =>
    refine ⟨_, w', rfl, fun _ h => ?_⟩
    cases h
    exact mapProcessError_kinds (req.args[0]?.getD "git") e

private theorem runGitRaw_res (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitRaw LeanSwe.Git.defaultRawOps req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (e.kind = .invalidPath ∧ ∃ p, req.cwd = some p ∧ LeanSwe.Git.Model.isValidPathArg p = false) ∨
        e.kind = .invalidInput ∨
        e.kind = .timeout ∨
        e.kind = .commandFailed := by
  unfold LeanSwe.Git.Impl.runGitRaw
  cases hcwd : LeanSwe.Git.Impl.validateCwd? req.cwd with
  | error e =>
    dsimp only
    refine ⟨_, w, rfl, fun _ he => ?_⟩
    cases he
    cases hreq : req.cwd with
    | none => simp [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
    | some p =>
      simp only [LeanSwe.Git.Impl.validateCwd?, hreq] at hcwd
      split at hcwd
      · cases hcwd
      · cases hcwd
        rename_i hinv
        have hinvF : LeanSwe.Git.Model.isValidPathArg p = false := Bool.eq_false_iff.mpr hinv
        exact Or.inl ⟨rfl, p, rfl, hinvF⟩
  | ok _ =>
    dsimp only
    cases henv : LeanSwe.Git.Impl.validateExtraEnv req.extraEnv with
    | error e =>
      dsimp only
      refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he
      unfold LeanSwe.Git.Impl.validateExtraEnv at henv
      split at henv
      · cases henv
      · cases henv; exact Or.inr (Or.inl rfl)
    | ok _ =>
      dsimp only
      split
      · refine ⟨_, w, rfl, fun _ he => ?_⟩
        cases he; exact Or.inr (Or.inl rfl)
      · rcases defaultRawOps_listEnv_res w with ⟨renv, w1, hw1, hkenv⟩
        rw [io_bind_ok _ _ _ hw1]
        cases renv with
        | error e =>
          refine ⟨_, w1, rfl, fun _ he => ?_⟩
          cases he
          exact Or.inr (Or.inr (Or.inr (hkenv e rfl)))
        | ok inherited =>
          rcases defaultRawOps_execGit_res (LeanSwe.Git.Model.cleanGitEnv inherited req.extraEnv) req w1 with
            ⟨re, w2, hw2, hke⟩
          exact ⟨re, w2, hw2, fun e he => by
            rcases hke e he with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))⟩

private theorem classifyError_kinds (cmd : String) (out : GitRawOutput) :
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .invalidPath ∧
    (LeanSwe.Git.Impl.classifyError cmd out).kind ≠ .parseError := by
  dsimp only [LeanSwe.Git.Impl.classifyError]
  by_cases hBlank : (LeanSwe.Git.Impl.trimAsciiWhitespace (LeanSwe.Git.Impl.decodeUtf8Lossy out.stderr)).isEmpty = true
  · simp only [hBlank, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩
  · simp only [hBlank, Bool.false_eq_true, ↓reduceIte]
    repeat' (split; try exact ⟨by decide, by decide⟩)
    exact ⟨by decide, by decide⟩

private theorem runGitChecked_res (cmd : String) (req : GitRawRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req w = EST.Out.ok res w' ∧
      ∀ e, res = .error e →
        (req.cwd.elim True (fun p => LeanSwe.Git.Model.isValidPathArg p = true) → e.kind ≠ .invalidPath) ∧
        e.kind ≠ .parseError := by
  unfold LeanSwe.Git.Impl.runGitChecked
  rcases runGitRaw_res req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    dsimp only
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    rcases hkr e rfl with ⟨h1, p, hp, hinv⟩ | h | h | h
    · refine ⟨fun hvalid => ?_, by rw [h1]; decide⟩
      simp [hp, hinv] at hvalid
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
    · exact ⟨fun _ => by rw [h]; decide, by rw [h]; decide⟩
  | ok out =>
    dsimp only
    split
    · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
    · refine ⟨_, w1, rfl, fun e he => ?_⟩
      rw [← Except.error.inj he]
      have hk := classifyError_kinds cmd out
      exact ⟨fun _ => hk.1, hk.2⟩

private theorem bind_runGitChecked_never_parseError (cmd : String) (req : GitRawRequest)
    (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e => exact ⟨_, w1, rfl, fun _ he => by cases he; exact (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

private theorem bind_runGitChecked_no_cwd (cmd : String) (req : GitRawRequest)
    (hcwd : req.cwd = none) (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps cmd req >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())) w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rcases runGitChecked_res cmd req w with ⟨r, w1, hw1, hkr⟩
  rw [io_bind_ok _ _ _ hw1]
  cases r with
  | error e =>
    refine ⟨_, w1, rfl, fun _ he => ?_⟩
    cases he
    exact ⟨(hkr e rfl).1 (by simp [hcwd]), (hkr e rfl).2⟩
  | ok _ => exact ⟨_, w1, rfl, fun _ h => by cases h⟩

private theorem neverErrorKindIO_of_ok {α : Type} (kind : GitErrorKind)
    (act : IO (Except GitError α)) (w : Void IO.RealWorld)
    (h : ∃ res w', act w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ kind) :
    Core.NeverErrorKindIO GitError.kind kind act w := by
  rcases h with ⟨res, w', hw, hk⟩
  unfold Core.NeverErrorKindIO
  rw [hw]
  cases res with
  | ok _ => trivial
  | error e => exact hk e rfl

private theorem validateFsPathArg_kinds (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateFsPathArg p = .error e) :
    e.kind = .invalidPath ∨ e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateFsPathArg at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr rfl
    · cases h

private theorem validateRepoPath_never (repoPath : String) (e : GitError)
    (h : LeanSwe.Git.Impl.validateRepoPath repoPath = .error e) :
    e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  rcases validateFsPathArg_kinds repoPath e h with hk | hk <;> rw [hk] <;> exact ⟨by decide, by decide⟩

private theorem validateCloneEndpoint_kind (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateCloneEndpoint p = .error e) :
    e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateCloneEndpoint at h
  split at h
  · cases h; rfl
  · cases h

private theorem validateCloneEndpoint_isValidPathArg (p : String)
    (h : LeanSwe.Git.Model.validateCloneEndpoint p = .ok ()) :
    LeanSwe.Git.Model.isValidPathArg p = true := by
  unfold LeanSwe.Git.Model.validateCloneEndpoint at h
  split at h
  · cases h
  · next hcond =>
    cases hv : LeanSwe.Git.Model.isValidPathArg p
    · exfalso; apply hcond; simp [hv]
    · rfl

private theorem validateRelRepoPath_kind (p : String) (e : GitError)
    (h : LeanSwe.Git.Model.validateRelRepoPath p = .error e) :
    e.kind = .invalidPath ∨ e.kind = .invalidInput := by
  unfold LeanSwe.Git.Model.validateRelRepoPath at h
  split at h
  · cases h; exact Or.inl rfl
  · dsimp only at h
    split at h
    · cases h; exact Or.inl rfl
    · split at h
      · cases h; exact Or.inr rfl
      · cases h

private theorem mem_of_mem_dropWhile {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : x ∈ xs.dropWhile p) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.dropWhile] at h
    split at h
    · exact List.mem_cons_of_mem a (ih h)
    · exact h

private theorem validateRelRepoPaths_forM_kind (paths : List String) (e : GitError)
    (h : paths.forM LeanSwe.Git.Model.validateRelRepoPath = Except.error e) :
    e.kind = .invalidPath ∨ e.kind = .invalidInput := by
  induction paths with
  | nil => cases h
  | cons p ps ih =>
    dsimp only [List.forM] at h
    cases hv : LeanSwe.Git.Model.validateRelRepoPath p with
    | error err =>
      simp only [hv, Bind.bind, Except.bind] at h
      cases h
      exact validateRelRepoPath_kind p e hv
    | ok _ =>
      simp only [hv, Bind.bind, Except.bind] at h
      exact ih h

private theorem validateRelRepoPaths_never_parseError (paths : Array String) (e : GitError)
    (h : LeanSwe.Git.Model.validateRelRepoPaths paths = .error e) :
    e.kind ≠ .parseError := by
  unfold LeanSwe.Git.Model.validateRelRepoPaths at h
  cases hloop : paths.toList.forM LeanSwe.Git.Model.validateRelRepoPath with
  | error err =>
    simp only [hloop, Bind.bind, Except.bind] at h
    cases h
    rcases validateRelRepoPaths_forM_kind paths.toList e hloop with hk | hk <;> rw [hk] <;> decide
  | ok _ =>
    simp only [hloop, Bind.bind, Except.bind] at h
    split at h
    · cases h; decide
    · cases h

private theorem hasNulChar_iff_mem (cs : List Char) :
    LeanSwe.Git.Model.hasNulChar cs = false ↔ ∀ c ∈ cs, c ≠ Char.ofNat 0 := by
  induction cs with
  | nil => simp [LeanSwe.Git.Model.hasNulChar]
  | cons c cs ih =>
    simp only [LeanSwe.Git.Model.hasNulChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      List.mem_cons, forall_eq_or_imp, ih]

private theorem isValidPathArg_of_list (cs : List Char) (hne : cs ≠ [])
    (hnul : ∀ c ∈ cs, c ≠ Char.ofNat 0) :
    LeanSwe.Git.Model.isValidPathArg (String.ofList cs) = true := by
  unfold LeanSwe.Git.Model.isValidPathArg
  rw [String.toList_ofList]
  have h1 : (!cs.isEmpty) = true := by cases cs with | nil => contradiction | cons _ _ => rfl
  have h2 : (!LeanSwe.Git.Model.hasNulChar cs) = true := by
    rw [Bool.not_eq_true']
    exact (hasNulChar_iff_mem cs).mpr hnul
  simp [h1, h2]

private theorem parentPrefixChars_preserves (cs p : List Char)
    (hnul : ∀ c ∈ cs, c ≠ Char.ofNat 0)
    (h : LeanSwe.Git.Model.parentPrefixChars? cs = some p) :
    p ≠ [] ∧ ∀ c ∈ p, c ≠ Char.ofNat 0 := by
  unfold LeanSwe.Git.Model.parentPrefixChars? at h
  cases hdrop : cs.reverse.dropWhile (· != '/') with
  | nil => simp [hdrop] at h
  | cons d rest =>
    by_cases hslash : d = '/'
    · subst hslash
      simp only [hdrop, beq_self_eq_true, ↓reduceIte] at h
      split at h
      · split at h
        · cases h
          refine ⟨by decide, fun c hc => ?_⟩
          have hc' : c = '/' := by simpa using hc
          rw [hc']
          decide
        · cases h
      · cases h
        rename_i hns
        refine ⟨fun hemp => hns (by rw [List.reverse_eq_nil_iff] at hemp; rw [hemp]; rfl), fun c hc => ?_⟩
        have hcrev : c ∈ rest.dropWhile (· == '/') := List.mem_reverse.mp hc
        have hc_rest : c ∈ rest := mem_of_mem_dropWhile hcrev
        have hc_drop : c ∈ cs.reverse.dropWhile (· != '/') := by
          rw [hdrop]; exact List.mem_cons_of_mem _ hc_rest
        have hc_rev : c ∈ cs.reverse := mem_of_mem_dropWhile hc_drop
        exact hnul c (List.mem_reverse.mp hc_rev)
    · have hbeq : (d == '/') = false := beq_false_of_ne hslash
      simp only [hdrop, hbeq, Bool.false_eq_true, ↓reduceIte] at h
      cases h

private theorem ancestorLoop_valid (revPref : List Char) (acc : List String) (cs : List Char)
    (hacc : ∀ x ∈ acc, LeanSwe.Git.Model.isValidPathArg x = true)
    (hnulRev : ∀ c ∈ revPref, c ≠ Char.ofNat 0)
    (hnulCs : ∀ c ∈ cs, c ≠ Char.ofNat 0) :
    ∀ x ∈ LeanSwe.Git.Model.ancestorLoop revPref acc cs,
      LeanSwe.Git.Model.isValidPathArg x = true := by
  induction cs generalizing revPref acc with
  | nil =>
    intro x hx
    unfold LeanSwe.Git.Model.ancestorLoop at hx
    dsimp only at hx
    by_cases hEmpty : revPref.isEmpty = true
    · simp [hEmpty] at hx
      exact hacc x hx
    · have hEmptyF : revPref.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
      simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte] at hx
      by_cases hHead : (acc.head? == some (String.ofList revPref.reverse)) = true
      · simp [hHead] at hx
        exact hacc x hx
      · have hHeadF : (acc.head? == some (String.ofList revPref.reverse)) = false := Bool.eq_false_iff.mpr hHead
        simp only [hHeadF, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hx
        rcases hx with rfl | hx'
        · apply isValidPathArg_of_list
          · cases revPref <;> simp_all
          · intro c hc
            exact hnulRev c (List.mem_reverse.mp hc)
        · exact hacc x hx'
  | cons c rest ih =>
    intro x hx
    by_cases hslash : c = '/'
    · subst hslash
      unfold LeanSwe.Git.Model.ancestorLoop at hx
      dsimp only at hx
      apply ih ('/' :: revPref) _ _ ?_ ?_ x hx
      · intro y hy
        by_cases hSkip : (revPref.isEmpty || revPref.head? == some '/') = true
        · simp [hSkip] at hy
          exact hacc y hy
        · have hSkipF : (revPref.isEmpty || revPref.head? == some '/') = false := Bool.eq_false_iff.mpr hSkip
          simp only [hSkipF, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hy
          rcases hy with rfl | hy'
          · apply isValidPathArg_of_list
            · cases revPref <;> simp_all
            · intro ch hch
              exact hnulRev ch (List.mem_reverse.mp hch)
          · exact hacc y hy'
      · intro ch hch
        rcases List.mem_cons.mp hch with rfl | hch'
        · decide
        · exact hnulRev ch hch'
      · intro ch hch
        exact hnulCs ch (List.mem_cons_of_mem _ hch)
    · have hc0 : c ≠ Char.ofNat 0 := hnulCs c List.mem_cons_self
      have hLoop : LeanSwe.Git.Model.ancestorLoop revPref acc (c :: rest) =
          LeanSwe.Git.Model.ancestorLoop (c :: revPref) acc rest := by
        conv => lhs; unfold LeanSwe.Git.Model.ancestorLoop
        split
        · contradiction
        · simp_all
        · simp_all
      rw [hLoop] at hx
      apply ih (c :: revPref) acc hacc _ (fun ch hch => hnulCs ch (List.mem_cons_of_mem _ hch)) x hx
      intro ch hch
      rcases List.mem_cons.mp hch with rfl | hch'
      · exact hc0
      · exact hnulRev ch hch'

private theorem ancestorCandidates_valid (p : String)
    (hp : LeanSwe.Git.Model.isValidPathArg p = true) :
    ∀ x ∈ LeanSwe.Git.Model.ancestorCandidates p, LeanSwe.Git.Model.isValidPathArg x = true := by
  intro x hx
  unfold LeanSwe.Git.Model.isValidPathArg at hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hpnul : ∀ c ∈ p.toList, c ≠ Char.ofNat 0 := (hasNulChar_iff_mem p.toList).mp hp.2
  have hnlnul : ∀ c ∈ (LeanSwe.Git.Model.stripTrailingSlashes p).toList, c ≠ Char.ofNat 0 := by
    intro c hc
    unfold LeanSwe.Git.Model.stripTrailingSlashes at hc
    dsimp only at hc
    split at hc
    · split at hc
      · have hc' : c = '/' := by simpa using hc
        rw [hc']; decide
      · simp at hc
    · rw [String.toList_ofList] at hc
      exact hpnul c (List.mem_reverse.mp (mem_of_mem_dropWhile (List.mem_reverse.mp hc)))
  unfold LeanSwe.Git.Model.ancestorCandidates at hx
  dsimp only at hx
  cases hstrip : (LeanSwe.Git.Model.stripTrailingSlashes p).toList with
  | nil =>
    rw [hstrip] at hx
    cases hx
  | cons hd tl =>
    rw [hstrip] at hx hnlnul
    by_cases hslash : hd = '/'
    · subst hslash
      apply ancestorLoop_valid ['/'] ["/"] tl _ _ _ x hx
      · intro y hy
        have hy' : y = "/" := by simpa using hy
        rw [hy']; decide
      · intro c hc
        have hc' : c = '/' := by simpa using hc
        rw [hc']; decide
      · intro c hc
        exact hnlnul c (List.mem_cons_of_mem _ hc)
    · split at hx
      · contradiction
      · simp_all
      · apply ancestorLoop_valid [] ["."] (hd :: tl) _ (fun _ hc => by cases hc) hnlnul x hx
        intro y hy
        have hy' : y = "." := by simpa using hy
        rw [hy']; decide

private theorem isRepo_res (repoPath : String) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Git.isRepo repoPath w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .notARepo ∧ e.kind ≠ .parseError := by
  rw [show LeanSwe.Git.isRepo repoPath = LeanSwe.Git.Impl.isRepoImpl LeanSwe.Git.defaultRawOps repoPath from rfl]
  unfold LeanSwe.Git.Impl.isRepoImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact validateRepoPath_never repoPath e hv⟩
  | ok _ =>
    dsimp only
    rcases runGitRaw_res { cwd := some repoPath, args := #["rev-parse", "--git-dir"] } w with
      ⟨r, w1, hw1, hkr⟩
    rw [io_bind_ok _ _ _ hw1]
    cases r with
    | error e =>
      dsimp only
      refine ⟨_, w1, rfl, fun _ he => ?_⟩
      cases he
      rcases hkr e rfl with ⟨h, _⟩ | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩
    | ok out =>
      dsimp only
      split
      · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
      · split
        · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
        · refine ⟨_, w1, rfl, fun e he => ?_⟩
          rw [← Except.error.inj he]
          rename_i hne
          have hk := classifyError_kinds "rev-parse" out
          refine ⟨?_, hk.2⟩
          intro heq
          apply hne
          simp [heq]
          decide

/-- `Git.isRepo` handles `notARepo` by returning `Ok false`, so it never fails with `.notARepo`. -/
theorem git_isRepo_never_notARepo (repoPath : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .notARepo (Git.isRepo repoPath) w :=
  neverErrorKindIO_of_ok .notARepo (Git.isRepo repoPath) w (by
    rcases isRepo_res repoPath w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).1⟩)

/-- `Git.isRepo` never fails with `.parseError`. -/
theorem git_isRepo_never_parseError (repoPath : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.isRepo repoPath) w :=
  neverErrorKindIO_of_ok .parseError (Git.isRepo repoPath) w (by
    rcases isRepo_res repoPath w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).2⟩)

/-- `Git.isAncestor` never fails with `.parseError`. -/
theorem git_isAncestor_never_parseError (repoPath : String) (ancestor descendant : CommitId)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.isAncestor repoPath ancestor descendant) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.isAncestor repoPath ancestor descendant =
      LeanSwe.Git.Impl.isAncestorImpl LeanSwe.Git.defaultRawOps repoPath ancestor descendant from rfl]
  unfold LeanSwe.Git.Impl.isAncestorImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · refine ⟨_, w, rfl, fun _ he => ?_⟩
      cases he; dsimp only; decide
    · rcases runGitRaw_res { cwd := some repoPath, args := #["merge-base", "--is-ancestor", ancestor.hex, descendant.hex] } w with
        ⟨r, w1, hw1, hkr⟩
      rw [io_bind_ok _ _ _ hw1]
      cases r with
      | error e =>
        dsimp only
        refine ⟨_, w1, rfl, fun _ he => ?_⟩
        cases he
        rcases hkr e rfl with ⟨h, _⟩ | h | h | h <;> rw [h] <;> decide
      | ok out =>
        dsimp only
        split
        · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
        · split
          · exact ⟨_, w1, rfl, fun _ h => by cases h⟩
          · refine ⟨_, w1, rfl, fun e he => ?_⟩
            rw [← Except.error.inj he]
            exact (classifyError_kinds "merge-base" out).2

/-- `Git.init` never fails with `.parseError`. -/
theorem git_init_never_parseError (path : String) (bare : Bool) (initialBranch? : Option RefName)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.init path bare initialBranch?) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.init path bare initialBranch? =
      LeanSwe.Git.Impl.initImpl LeanSwe.Git.defaultRawOps path bare initialBranch? from rfl]
  unfold LeanSwe.Git.Impl.initImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath path with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never path e hv).2⟩
  | ok _ =>
    dsimp only
    let runAfter : Array String → IO (Except GitError Unit) := fun bArgs =>
      LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps "init"
        { cwd := none, args := #["init"] ++ (if bare then #["--bare"] else #[]) ++ bArgs ++ #["--", path] } >>= fun r =>
        match r with
        | Except.error e => pure (Except.error e)
        | Except.ok _ => pure (Except.ok ())
    have hrun : ∀ bArgs, ∃ res w', runAfter bArgs w = EST.Out.ok res w' ∧ ∀ e, res = .error e → e.kind ≠ .parseError := by
      intro bArgs
      exact bind_runGitChecked_never_parseError "init" _ w
    cases initialBranch? with
    | none => exact hrun #[]
    | some b =>
      dsimp only
      split
      · exact hrun #["-b", b.raw]
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

private theorem clone_res (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    ∃ res w', Git.clone source target opts w = EST.Out.ok res w' ∧
      ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
  rw [show Git.clone source target opts =
      LeanSwe.Git.Impl.cloneImpl LeanSwe.Git.defaultRawOps source target opts from rfl]
  unfold LeanSwe.Git.Impl.cloneImpl
  cases hs : LeanSwe.Git.Model.validateCloneEndpoint source with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; rw [validateCloneEndpoint_kind source e hs]; exact ⟨by decide, by decide⟩⟩
  | ok _ =>
    cases ht : LeanSwe.Git.Model.validateCloneEndpoint target with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; rw [validateCloneEndpoint_kind target e ht]; exact ⟨by decide, by decide⟩⟩
    | ok _ =>
      dsimp only
      let afterBranch : Array String → Array String → IO (Except GitError Unit) := fun depthArgs bArgs =>
        LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps "clone"
          { cwd := none, args := #["clone"] ++ (if opts.bare then #["--bare"] else #[]) ++
              (if opts.singleBranch then #["--single-branch"] else #[]) ++
              depthArgs ++ bArgs ++ #["--", source, target] } >>= fun r =>
          match r with
          | Except.error e => pure (Except.error e)
          | Except.ok _ => pure (Except.ok ())
      have hafter : ∀ depthArgs bArgs, ∃ res w', afterBranch depthArgs bArgs w = EST.Out.ok res w' ∧
          ∀ e, res = .error e → e.kind ≠ .invalidPath ∧ e.kind ≠ .parseError := by
        intro depthArgs bArgs
        exact bind_runGitChecked_no_cwd "clone" _ rfl w
      have hbody : ∀ depthArgs, ∃ res w',
          (match
              match opts.branch? with
              | none => Except.ok #[]
              | some b =>
                if LeanSwe.Git.Model.isValidRefNameStr b then Except.ok #["--branch", b]
                else Except.error ({ kind := GitErrorKind.invalidRef, message := s!"invalid clone branch: '{b}'" } : GitError) with
            | Except.error e => pure (Except.error e)
            | Except.ok bArgs => afterBranch depthArgs bArgs) w = EST.Out.ok res w' ∧
          ∀ e : GitError, res = Except.error e → e.kind ≠ GitErrorKind.invalidPath ∧ e.kind ≠ GitErrorKind.parseError := by
        intro depthArgs
        cases opts.branch? with
        | none => exact hafter depthArgs #[]
        | some b =>
          dsimp only
          split
          · exact hafter depthArgs #["--branch", b]
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; exact ⟨by decide, by decide⟩⟩
      cases hd : opts.depth? with
      | none => exact hbody #[]
      | some d =>
        cases d with
        | zero => exact ⟨_, w, rfl, fun _ he => by cases he; exact ⟨by decide, by decide⟩⟩
        | succ n => exact hbody #["--depth", toString (n + 1)]

/-- `Git.clone` does not run with a `cwd` and maps path checks to `.invalidInput`, so it never fails with `.invalidPath`. -/
theorem git_clone_never_invalidPath (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .invalidPath (Git.clone source target opts) w :=
  neverErrorKindIO_of_ok .invalidPath (Git.clone source target opts) w (by
    rcases clone_res source target opts w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).1⟩)

/-- `Git.clone` never fails with `.parseError`. -/
theorem git_clone_never_parseError (source target : String) (opts : CloneOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.clone source target opts) w :=
  neverErrorKindIO_of_ok .parseError (Git.clone source target opts) w (by
    rcases clone_res source target opts w with ⟨res, w', hw, hk⟩
    exact ⟨res, w', hw, fun e he => (hk e he).2⟩)

/-- `Git.add` never fails with `.parseError`. -/
theorem git_add_never_parseError (repoPath : String) (paths : Array String) (all : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.add repoPath paths all) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.add repoPath paths all =
      LeanSwe.Git.Impl.addImpl LeanSwe.Git.defaultRawOps repoPath paths all from rfl]
  unfold LeanSwe.Git.Impl.addImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
    · split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · exact bind_runGitChecked_never_parseError "add" _ w

/-- `Git.createBranch` never fails with `.parseError`. -/
theorem git_createBranch_never_parseError (repoPath : String) (branch : RefName)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.createBranch repoPath branch startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.createBranch repoPath branch startPoint? force =
      LeanSwe.Git.Impl.createBranchImpl LeanSwe.Git.defaultRawOps repoPath branch startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.createBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · cases startPoint? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "branch" _ w
      | some sp =>
        dsimp only
        split
        · exact bind_runGitChecked_never_parseError "branch" _ w
        · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.deleteBranch` never fails with `.parseError`. -/
theorem git_deleteBranch_never_parseError (repoPath : String) (branch : RefName) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.deleteBranch repoPath branch force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.deleteBranch repoPath branch force =
      LeanSwe.Git.Impl.deleteBranchImpl LeanSwe.Git.defaultRawOps repoPath branch force from rfl]
  unfold LeanSwe.Git.Impl.deleteBranchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · exact bind_runGitChecked_never_parseError "branch" _ w

/-- `Git.checkout` never fails with `.parseError`. -/
theorem git_checkout_never_parseError (repoPath : String) (target : CheckoutTarget) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.checkout repoPath target force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.checkout repoPath target force =
      LeanSwe.Git.Impl.checkoutImpl LeanSwe.Git.defaultRawOps repoPath target force from rfl]
  unfold LeanSwe.Git.Impl.checkoutImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    cases target with
    | branch b =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    | commit cid =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    | ref spec =>
      dsimp only
      split
      · exact bind_runGitChecked_never_parseError "checkout" _ w
      · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.switch` never fails with `.parseError`. -/
theorem git_switch_never_parseError (repoPath : String) (branch : RefName) (create : Bool)
    (startPoint? : Option String) (force : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError
      (Git.switch repoPath branch create startPoint? force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.switch repoPath branch create startPoint? force =
      LeanSwe.Git.Impl.switchImpl LeanSwe.Git.defaultRawOps repoPath branch create startPoint? force from rfl]
  unfold LeanSwe.Git.Impl.switchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · cases startPoint? with
        | none =>
          dsimp only
          exact bind_runGitChecked_never_parseError "switch" _ w
        | some sp =>
          dsimp only
          split
          · exact bind_runGitChecked_never_parseError "switch" _ w
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.reset` never fails with `.parseError`. -/
theorem git_reset_never_parseError (repoPath : String) (mode : ResetMode) (rev : String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.reset repoPath mode rev) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.reset repoPath mode rev =
      LeanSwe.Git.Impl.resetImpl LeanSwe.Git.defaultRawOps repoPath mode rev from rfl]
  unfold LeanSwe.Git.Impl.resetImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · exact bind_runGitChecked_never_parseError "reset" _ w

/-- `Git.fetch` never fails with `.parseError`. -/
theorem git_fetch_never_parseError (repoPath remote : String) (refspec? : Option String)
    (prune : Bool) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.fetch repoPath remote refspec? prune) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.fetch repoPath remote refspec? prune =
      LeanSwe.Git.Impl.fetchImpl LeanSwe.Git.defaultRawOps repoPath remote refspec? prune from rfl]
  unfold LeanSwe.Git.Impl.fetchImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    dsimp only
    split
    · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
    · cases refspec? with
      | none =>
        dsimp only
        exact bind_runGitChecked_never_parseError "fetch" _ w
      | some r =>
        dsimp only
        split
        · exact bind_runGitChecked_never_parseError "fetch" _ w
        · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.worktreeAdd` never fails with `.parseError`. -/
theorem git_worktreeAdd_never_parseError (repoPath : String) (opts : WorktreeAddOptions)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeAdd repoPath opts) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeAdd repoPath opts =
      LeanSwe.Git.Impl.worktreeAddImpl LeanSwe.Git.defaultRawOps repoPath opts from rfl]
  unfold LeanSwe.Git.Impl.worktreeAddImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    cases hv2 : LeanSwe.Git.Impl.validateRepoPath opts.path with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never opts.path e hv2).2⟩
    | ok _ =>
      dsimp only
      split
      · exact ⟨_, w, rfl, fun _ he => by cases he; decide⟩
      · have hAfter : ∀ (bArgs : Array String), ∃ res w',
            (match
                match opts.target? with
                | none => Except.ok #[]
                | some t =>
                  if LeanSwe.Git.Model.isValidStrictRevSpec t then Except.ok #[t]
                  else Except.error ({ kind := GitErrorKind.invalidInput, message := s!"invalid worktree target: '{t}'" } : GitError) with
              | Except.error e => pure (Except.error e)
              | Except.ok tArgs => do
                let args :=
                  #["worktree", "add"] ++
                  (if opts.force then #["--force"] else #[]) ++
                  (if opts.detach then #["--detach"] else #[]) ++
                  bArgs ++ #["--", opts.path] ++ tArgs
                match ← LeanSwe.Git.Impl.runGitChecked LeanSwe.Git.defaultRawOps "worktree" { cwd := some repoPath, args := args } with
                | Except.error e => return Except.error e
                | Except.ok _ => return Except.ok ()) w = EST.Out.ok res w' ∧
            ∀ e : GitError, res = Except.error e → e.kind ≠ GitErrorKind.parseError := by
          intro bArgs
          cases opts.target? with
          | none => exact bind_runGitChecked_never_parseError "worktree" _ w
          | some t =>
            dsimp only
            split
            · exact bind_runGitChecked_never_parseError "worktree" _ w
            · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩
        cases opts.newBranch? with
        | none => exact hAfter #[]
        | some b =>
          dsimp only
          split
          · exact hAfter #["-b", b.raw]
          · exact ⟨_, w, rfl, fun _ he => by cases he; dsimp only; decide⟩

/-- `Git.worktreeRemove` never fails with `.parseError`. -/
theorem git_worktreeRemove_never_parseError (repoPath wtPath : String) (force : Bool)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO GitError.kind .parseError (Git.worktreeRemove repoPath wtPath force) w := by
  apply neverErrorKindIO_of_ok
  rw [show Git.worktreeRemove repoPath wtPath force =
      LeanSwe.Git.Impl.worktreeRemoveImpl LeanSwe.Git.defaultRawOps repoPath wtPath force from rfl]
  unfold LeanSwe.Git.Impl.worktreeRemoveImpl
  cases hv : LeanSwe.Git.Impl.validateRepoPath repoPath with
  | error e =>
    dsimp only
    exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never repoPath e hv).2⟩
  | ok _ =>
    cases hv2 : LeanSwe.Git.Impl.validateRepoPath wtPath with
    | error e =>
      dsimp only
      exact ⟨_, w, rfl, fun _ he => by cases he; exact (validateRepoPath_never wtPath e hv2).2⟩
    | ok _ =>
      dsimp only
      exact bind_runGitChecked_never_parseError "worktree" _ w

end LeanSwe.Git.Proofs
