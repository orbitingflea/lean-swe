import LeanSwe.Process.SysBridge
import LeanSwe.Process.Proofs.HealthyStep

/-!
Error-mapping, `openFds` pipe-prefix erasure, `EINTR` retry, `PATH` search, working-directory
validation, and chunk concatenation lemmas for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

theorem stateT_bind_eq {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    SysBridge.nonEmptyMsg fallback msg ≠ "" := by
  unfold SysBridge.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

theorem ensureNonEmptyMsg_ne_empty (fallback : String) (err : ProcessError) (hf : fallback ≠ "") :
    (SysBridge.ensureNonEmptyMsg fallback err).message ≠ "" := by
  unfold SysBridge.ensureNonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- `SysBridge.mapRawError` always produces a non-empty diagnostic message. -/
theorem mapRawError_message_ne_empty (raw : ProcessRawError) :
    (SysBridge.mapRawError raw).message ≠ "" := by
  cases raw with
  | executableNotFound prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "executable not found: " prog (by decide))
  | permissionDenied _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | timedOut prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | outputLimitExceeded prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | signaled prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- `SysBridge.mapErrno` always yields a non-empty message and never synthesizes `.timedOut`, `.outputLimitExceeded`, or `.terminatedBySignal`. -/
theorem mapErrno_kind_and_msg (prog? : Option String) (ctx : String) (e : Errno) :
    let err := SysBridge.mapErrno prog? ctx e
    err.message ≠ "" ∧
    err.kind ≠ .timedOut ∧
    err.kind ≠ .outputLimitExceeded ∧
    err.kind ≠ .terminatedBySignal := by
  unfold SysBridge.mapErrno
  dsimp only
  split
  · refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  · split
    · refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
    · split
      · refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
      · refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]

/-- `SysBridge.mapPostForkError` always yields a non-empty message and never synthesizes `.timedOut`, `.outputLimitExceeded`, or `.terminatedBySignal`. -/
theorem mapPostForkError_kind_and_msg (req : ExecRequest) (pfErr : PostFork.PostForkError) :
    let err := SysBridge.mapPostForkError req pfErr
    err.message ≠ "" ∧
    err.kind ≠ .timedOut ∧
    err.kind ≠ .outputLimitExceeded ∧
    err.kind ≠ .terminatedBySignal := by
  unfold SysBridge.mapPostForkError
  cases pfErr.childFailure with
  | some cf => exact mapErrno_kind_and_msg _ _ _
  | none =>
    cases pfErr.kind <;> dsimp only
    · refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
    all_goals
      cases pfErr.errno with
      | some e => exact mapErrno_kind_and_msg _ _ _
      | none => refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]

/-- `killTargetOfPgid` never returns `-1` (`kill(-1, sig)` process-wide broadcast is impossible for every `UInt32`). -/
theorem killTargetOfPgid_ne_neg_one (pgid : UInt32) :
    LinuxSyscall.Process.killTargetOfPgid pgid ≠ (-1 : Int32) := by
  unfold LinuxSyscall.Process.killTargetOfPgid
  by_cases h1 : pgid == 1
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    intro hEq
    have hNeg := congrArg (fun x : Int32 => (-x).toUInt32) hEq
    simp at hNeg
    exact h1 (beq_iff_eq.mpr hNeg)

/-- Return `some x` when `true` and `none` when `false`. -/
def optFdOf {fd : Type} (x : fd) : Bool → Option fd
  | true => some x
  | false => none

/-- Prepend optional active parent pipe ends (`errR`, `outR`, `inW`) onto `base`. -/
def pipePrefix {fd : Type} (errR outR inW : fd) (bErr bOut bIn : Bool) (base : List fd) : List fd :=
  (if bErr then [errR] else []) ++ (if bOut then [outR] else []) ++ (if bIn then [inW] else []) ++ base

theorem pipePrefix_erase_err {fd : Type} [DecidableEq fd]
    (errR outR inW : fd) (bOut bIn : Bool) (base : List fd) :
    (pipePrefix errR outR inW true bOut bIn base).erase errR =
      pipePrefix errR outR inW false bOut bIn base := by
  simp [pipePrefix]

theorem pipePrefix_erase_out {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} (hEO : errR ≠ outR) (bErr bIn : Bool) (base : List fd) :
    (pipePrefix errR outR inW bErr true bIn base).erase outR =
      pipePrefix errR outR inW bErr false bIn base := by
  cases bErr <;> simp [pipePrefix, beq_false_of_ne hEO]

theorem pipePrefix_erase_in {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} (hEI : errR ≠ inW) (hOI : outR ≠ inW) (bErr bOut : Bool) (base : List fd) :
    (pipePrefix errR outR inW bErr bOut true base).erase inW =
      pipePrefix errR outR inW bErr bOut false base := by
  cases bErr <;> cases bOut <;> simp [pipePrefix, beq_false_of_ne hEI, beq_false_of_ne hOI]

theorem optFdOf_isNone {fd : Type} (x : fd) (b : Bool)
    (h : (optFdOf x b).isNone = true) : b = false := by
  cases b
  · rfl
  · simp [optFdOf] at h

theorem closeOpt_optFdOf {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (x : fd) (fdAt : Bool → List fd)
    (hErase : ∀ st, openFds st = fdAt true → openFds ((files.close x).run st).2 = fdAt false)
    (b : Bool) (s : S) (hOpen : openFds s = fdAt b) :
    let r := (Files.closeOpt files (optFdOf x b)).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = fdAt false := by
  cases b
  · exact ⟨rfl, hOpen⟩
  · dsimp only [optFdOf]
    unfold Files.closeOpt
    rw [stateT_bind_eq]
    exact ⟨hCloseT s x, hErase s hOpen⟩

theorem closeStreamState_pipePrefix {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hCloseO : ∀ s h, openFds ((files.close h).run s).2 = (openFds s).erase h)
    {errR outR inW : fd} (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW)
    {bErr bOut bIn : Bool} {base : List fd}
    (st : StreamLoopState fd) (s : S)
    (hIn : st.inFd? = optFdOf inW bIn)
    (hOut : st.outFd? = optFdOf outR bOut)
    (hErr : st.errFd? = optFdOf errR bErr)
    (hOpen : openFds s = pipePrefix errR outR inW bErr bOut bIn base) :
    let r := (SysBridge.closeStreamState files st).run s
    getTbl r.2 = getTbl s ∧ openFds r.2 = base := by
  dsimp only
  unfold SysBridge.closeStreamState
  rw [hIn, hOut, hErr, stateT_bind_eq, stateT_bind_eq]
  obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
    (fun b => pipePrefix errR outR inW bErr bOut b base)
    (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_in hEI hOI]) bIn s hOpen
  let s1 := ((Files.closeOpt files (optFdOf inW bIn)).run s).2
  obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
    (fun b => pipePrefix errR outR inW bErr b false base)
    (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_out hEO]) bOut s1 hO1
  let s2 := ((Files.closeOpt files (optFdOf outR bOut)).run s1).2
  obtain ⟨hT3, hO3⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
    (fun b => pipePrefix errR outR inW b false false base)
    (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_err]) bErr s2 hO2
  exact ⟨hT3.trans (hT2.trans hT1), hO3⟩

theorem retryEintr_frame {S β α : Type}
    (proj : S → β)
    (act : StateM S (Except Errno α))
    (hFrame : ∀ s, proj (act.run s).2 = proj s)
    (fuel : Nat) (s : S) :
    proj ((LinuxSyscall.retryEintr act fuel).run s).2 = proj s := by
  induction fuel generalizing s with
  | zero => exact hFrame s
  | succ f ih =>
    unfold LinuxSyscall.retryEintr
    rw [stateT_bind_eq]
    cases hRes : (act.run s).1 with
    | ok v =>
      dsimp only [pure, StateT.pure, StateT.run]
      exact hFrame s
    | error e =>
      dsimp only
      split
      · rw [ih]
        exact hFrame s
      · dsimp only [pure, StateT.pure, StateT.run]
        exact hFrame s

theorem retryEintr_pipe2_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (act : StateM S (Except Errno (fd × fd)))
    (hPipe : ∀ s,
      let r := act.run s
      getTbl r.2 = getTbl s ∧
      (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
      (∀ rf wf, r.1 = .ok (rf, wf) →
        rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s))
    (fuel : Nat) (s : S) :
    let r := (LinuxSyscall.retryEintr act fuel).run s
    getTbl r.2 = getTbl s ∧
    (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
    (∀ rf wf, r.1 = .ok (rf, wf) →
      rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s) := by
  dsimp only
  induction fuel generalizing s with
  | zero => exact hPipe s
  | succ f ih =>
    unfold LinuxSyscall.retryEintr
    rw [stateT_bind_eq]
    obtain ⟨hT, hErr, hOk⟩ := hPipe s
    cases hR : (act.run s).1 with
    | ok pair =>
      rcases pair with ⟨rf, wf⟩
      dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨hT, (by intro _ h; cases h), ?_⟩
      intro rf' wf' hEq
      injection hEq with hSub
      injection hSub with h1 h2
      subst h1 h2
      exact hOk rf wf hR
    | error e =>
      have hO1 := hErr e hR
      dsimp only
      split
      · obtain ⟨hTi, hEi, hOki⟩ := ih (act.run s).2
        refine ⟨hTi.trans hT, fun e' he' => (hEi e' he').trans hO1, ?_⟩
        intro rf wf hOkRes
        obtain ⟨hne, hnr, hnw, hcons⟩ := hOki rf wf hOkRes
        rw [hO1] at hnr hnw hcons
        exact ⟨hne, hnr, hnw, hcons⟩
      · dsimp only [pure, StateT.pure, StateT.run]
        exact ⟨hT, fun _ _ => hO1, (by intro _ _ h; cases h)⟩

/-- `resolveExecutablePath` bypasses `PATH` search immediately in 0 syscalls when `'/' ∈ program.toList`. -/
theorem resolveExecutablePath_slash_bypasses_path {S fd : Type}
    (files : Files.FilesOpsM (StateM S) fd) (program : String)
    (cwd? : Option String) (envBytes : Array ByteArray)
    (eintrFuel : Nat) (s : S) (hSlash : '/' ∈ program.toList) :
    (SysBridge.resolveExecutablePath files program cwd? envBytes eintrFuel).run s = (.ok program, s) := by
  have hc : program.toList.contains '/' = true := List.contains_iff_mem.mpr hSlash
  unfold SysBridge.resolveExecutablePath
  rw [ite_eq_left hc]
  rfl

/-- `splitPosixPathBytes` replaces every empty `PATH` segment (`""`, leading/trailing/adjacent `:`) with `"."` per POSIX `execvp(3)`. -/
theorem splitPosixPathBytes_empty_segments :
    SysBridge.splitPosixPathBytes "".toUTF8 = [".".toUTF8] ∧
    SysBridge.splitPosixPathBytes ":/usr/bin".toUTF8 = [".".toUTF8, "/usr/bin".toUTF8] ∧
    SysBridge.splitPosixPathBytes "/usr/bin:".toUTF8 = ["/usr/bin".toUTF8, ".".toUTF8] ∧
    SysBridge.splitPosixPathBytes "a::b".toUTF8 = ["a".toUTF8, ".".toUTF8, "b".toUTF8] := by
  decide +kernel

/-- `searchPathDirs` preserves `.permissionDenied` across trailing `ENOENT` directories once `sawPerm = true`. -/
theorem searchPathDirs_empty_sawPerm {S fd : Type}
    (files : Files.FilesOpsM (StateM S) fd) (program : String)
    (cwd? : Option String) (eintrFuel : Nat) (s : S) :
    let r := (SysBridge.searchPathDirs files program cwd? eintrFuel true []).run s
    r.2 = s ∧ ∃ err, r.1 = .error err ∧ err.kind = .permissionDenied ∧ err.program = some program := by
  dsimp only [SysBridge.searchPathDirs, pure, StateT.pure, StateT.run]
  exact ⟨rfl, _, rfl, rfl, rfl⟩

private theorem searchPathDirs_spec {S β fd : Type}
    (proj : S → β)
    (files : Files.FilesOpsM (StateM S) fd)
    (hStat : ∀ s dir path flags, proj ((files.fstatat dir path flags).run s).2 = proj s)
    (hAcc : ∀ s dir path mask flags, proj ((files.faccessat dir path mask flags).run s).2 = proj s)
    (program : String) (cwd? : Option String) (eintrFuel : Nat) (sawPerm : Bool)
    (dirs : List String) (s : S) :
    let r := (SysBridge.searchPathDirs files program cwd? eintrFuel sawPerm dirs).run s
    proj r.2 = proj s ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  induction dirs generalizing sawPerm s with
  | nil =>
    unfold SysBridge.searchPathDirs
    cases sawPerm <;>
      (dsimp only [pure, StateT.pure, StateT.run]
       refine ⟨rfl, ?_⟩
       intro err hEq
       injection hEq with hE
       rw [← hE]
       refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError])
  | cons dir rest ih =>
    unfold SysBridge.searchPathDirs
    dsimp only
    let pathBytes := SysBridge.probePathBytes cwd? dir program
    rw [stateT_bind_eq]
    have hF1 := retryEintr_frame proj (files.fstatat none pathBytes {})
      (fun st => hStat st none pathBytes {}) eintrFuel s
    cases hR1 : (LinuxSyscall.retryEintr (files.fstatat none pathBytes {}) eintrFuel).run s with
    | mk r1 s1 =>
      rw [hR1] at hF1
      cases r1 with
      | error e =>
        dsimp only
        by_cases hPerm : SysBridge.isPermPathSearchErrno e = true
        · simp only [hPerm, ↓reduceIte]
          obtain ⟨hT, hErr⟩ := ih true s1
          exact ⟨hT.trans hF1, hErr⟩
        · simp only [hPerm, Bool.false_eq_true, ↓reduceIte]
          by_cases hMiss : SysBridge.isMissingPathSearchErrno e = true
          · simp only [hMiss, ↓reduceIte]
            obtain ⟨hT, hErr⟩ := ih sawPerm s1
            exact ⟨hT.trans hF1, hErr⟩
          · simp only [hMiss, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
            refine ⟨hF1, ?_⟩
            intro err hEq
            injection hEq with hE
            rw [← hE]
            exact mapErrno_kind_and_msg (some program) "execvp" e
      | ok st =>
        dsimp only
        split
        · obtain ⟨hT, hErr⟩ := ih true s1
          exact ⟨hT.trans hF1, hErr⟩
        · rw [stateT_bind_eq]
          have hF2 := retryEintr_frame proj
            (files.faccessat none pathBytes { exec := true } { eaccess := true })
            (fun st0 => hAcc st0 none pathBytes { exec := true } { eaccess := true }) eintrFuel s1
          cases hR2 : (LinuxSyscall.retryEintr (files.faccessat none pathBytes { exec := true } { eaccess := true }) eintrFuel).run s1 with
          | mk r2 s2 =>
            rw [hR2] at hF2
            cases r2 with
            | ok _ =>
              dsimp only [pure, StateT.pure, StateT.run]
              exact ⟨hF2.trans hF1, (by intro _ h; cases h)⟩
            | error e =>
              dsimp only
              by_cases hPerm : SysBridge.isPermPathSearchErrno e = true
              · simp only [hPerm, ↓reduceIte]
                obtain ⟨hT, hErr⟩ := ih true s2
                exact ⟨hT.trans (hF2.trans hF1), hErr⟩
              · simp only [hPerm, Bool.false_eq_true, ↓reduceIte]
                by_cases hMiss : SysBridge.isMissingPathSearchErrno e = true
                · simp only [hMiss, ↓reduceIte]
                  obtain ⟨hT, hErr⟩ := ih sawPerm s2
                  exact ⟨hT.trans (hF2.trans hF1), hErr⟩
                · simp only [hMiss, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
                  refine ⟨hF2.trans hF1, ?_⟩
                  intro err hEq
                  injection hEq with hE
                  rw [← hE]
                  exact mapErrno_kind_and_msg (some program) "execvp" e

theorem resolveExecutablePath_spec {S β fd : Type}
    (proj : S → β)
    (files : Files.FilesOpsM (StateM S) fd)
    (hStat : ∀ s dir path flags, proj ((files.fstatat dir path flags).run s).2 = proj s)
    (hAcc : ∀ s dir path mask flags, proj ((files.faccessat dir path mask flags).run s).2 = proj s)
    (program : String) (cwd? : Option String) (envBytes : Array ByteArray)
    (eintrFuel : Nat) (s : S) :
    let r := (SysBridge.resolveExecutablePath files program cwd? envBytes eintrFuel).run s
    proj r.2 = proj s ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  unfold SysBridge.resolveExecutablePath
  split
  · dsimp only [pure, StateT.pure, StateT.run]
    exact ⟨rfl, (by intro _ h; cases h)⟩
  · exact searchPathDirs_spec proj files hStat hAcc program cwd? eintrFuel false _ s

theorem validateWorkingDir_spec {S β fd : Type}
    (proj : S → β)
    (files : Files.FilesOpsM (StateM S) fd)
    (hStat : ∀ s dir path flags, proj ((files.fstatat dir path flags).run s).2 = proj s)
    (hAcc : ∀ s dir path mask flags, proj ((files.faccessat dir path mask flags).run s).2 = proj s)
    (cwd? : Option String) (eintrFuel : Nat) (s : S) :
    let r := (SysBridge.validateWorkingDir files cwd? eintrFuel).run s
    proj r.2 = proj s ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  cases cwd? with
  | none =>
    dsimp only [SysBridge.validateWorkingDir, pure, StateT.pure, StateT.run]
    exact ⟨rfl, (by intro _ h; cases h)⟩
  | some cwdDir =>
    unfold SysBridge.validateWorkingDir
    dsimp only
    split
    · dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨rfl, ?_⟩
      intro err hEq; injection hEq with hE; rw [← hE]
      exact mapErrno_kind_and_msg (some cwdDir) "chdir" Errno.ENOENT
    · let cwdBytes := cwdDir.toUTF8
      rw [stateT_bind_eq]
      have hF1 := retryEintr_frame proj (files.fstatat none cwdBytes {})
        (fun st => hStat st none cwdBytes {}) eintrFuel s
      cases hR1 : (LinuxSyscall.retryEintr (files.fstatat none cwdBytes {}) eintrFuel).run s with
      | mk r1 s1 =>
        rw [hR1] at hF1
        cases r1 with
        | error e =>
          dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hF1, ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg (some cwdDir) "chdir" e
        | ok st =>
          dsimp only
          split
          · dsimp only [pure, StateT.pure, StateT.run]
            refine ⟨hF1, ?_⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            exact mapErrno_kind_and_msg (some cwdDir) "chdir" Errno.ENOTDIR
          · rw [stateT_bind_eq]
            have hF2 := retryEintr_frame proj
              (files.faccessat none cwdBytes { exec := true } { eaccess := true })
              (fun st0 => hAcc st0 none cwdBytes { exec := true } { eaccess := true }) eintrFuel s1
            cases hR2 : (LinuxSyscall.retryEintr (files.faccessat none cwdBytes { exec := true } { eaccess := true }) eintrFuel).run s1 with
            | mk r2 s2 =>
              rw [hR2] at hF2
              cases r2 with
              | error e =>
                dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hF2.trans hF1, ?_⟩
                intro err hEq; injection hEq with hE; rw [← hE]
                exact mapErrno_kind_and_msg (some cwdDir) "chdir" e
              | ok _ =>
                dsimp only [pure, StateT.pure, StateT.run]
                exact ⟨hF2.trans hF1, (by intro _ h; cases h)⟩

private theorem emptyCap_size (n : Nat) : (ByteArray.emptyWithCapacity n).size = 0 := rfl

private theorem foldl_append_size (xs : List ByteArray) (acc : ByteArray) :
    (xs.foldl (· ++ ·) acc).size = acc.size + (xs.map ByteArray.size).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, ByteArray.size_append]
    omega

/-- `concatChunks chunks cap` has exact byte length equal to the sum of chunk sizes. -/
theorem concatChunks_size (chunks : Array ByteArray) (cap : Nat) :
    (LinuxSyscall.concatChunks chunks cap).size = (chunks.toList.map ByteArray.size).sum := by
  unfold LinuxSyscall.concatChunks
  rw [foldl_append_size, emptyCap_size, Nat.zero_add]

end LeanSwe.Process.Proofs
