import LeanSwe.Process.SysBridge
import LeanSwe.Process.Proofs.HealthyStep

/-!
# `SysBridge` Behavioral & Resource-Conservation Proofs

Universal `healthyStep`-parameterized behavioral, process-slot conservation, and OS
descriptor (`openFds`) conservation proofs for `LeanSwe.Process.SysBridge.mkRawOpsM`
over **any** `SysDepsM` satisfying `RefinesHealthySysDeps`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

private theorem stateT_bind_eq {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
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

private theorem ensureNonEmptyMsg_ne_empty (fallback : String) (err : ProcessError) (hf : fallback ≠ "") :
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

private def optFdOf {fd : Type} (x : fd) : Bool → Option fd
  | true => some x
  | false => none

private def pipePrefix {fd : Type} (errR outR inW : fd) (bErr bOut bIn : Bool) (base : List fd) : List fd :=
  (if bErr then [errR] else []) ++ (if bOut then [outR] else []) ++ (if bIn then [inW] else []) ++ base

private theorem pipePrefix_erase_err {fd : Type} [DecidableEq fd]
    (errR outR inW : fd) (bOut bIn : Bool) (base : List fd) :
    (pipePrefix errR outR inW true bOut bIn base).erase errR =
      pipePrefix errR outR inW false bOut bIn base := by
  simp [pipePrefix]

private theorem pipePrefix_erase_out {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} (hEO : errR ≠ outR) (bErr bIn : Bool) (base : List fd) :
    (pipePrefix errR outR inW bErr true bIn base).erase outR =
      pipePrefix errR outR inW bErr false bIn base := by
  cases bErr <;> simp [pipePrefix, beq_false_of_ne hEO]

private theorem pipePrefix_erase_in {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} (hEI : errR ≠ inW) (hOI : outR ≠ inW) (bErr bOut : Bool) (base : List fd) :
    (pipePrefix errR outR inW bErr bOut true base).erase inW =
      pipePrefix errR outR inW bErr bOut false base := by
  cases bErr <;> cases bOut <;> simp [pipePrefix, beq_false_of_ne hEI, beq_false_of_ne hOI]

private theorem optFdOf_isNone {fd : Type} (x : fd) (b : Bool)
    (h : (optFdOf x b).isNone = true) : b = false := by
  cases b
  · rfl
  · simp [optFdOf] at h

private theorem closeOpt_optFdOf {S fd : Type}
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

private theorem closeStreamState_pipePrefix {S fd : Type} [DecidableEq fd]
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

private theorem retryEintr_frame {S β α : Type}
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

private theorem retryEintr_pipe2_spec {S fd : Type}
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

private theorem resolveExecutablePath_spec {S β fd : Type}
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

private theorem validateWorkingDir_spec {S β fd : Type}
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

private theorem monoNowMs_spec {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (s : S) :
    proj ((TimeRand.monoNowMs timeRand).run s).2 = proj s := by
  unfold TimeRand.monoNowMs
  rw [stateT_bind_eq]
  cases ((timeRand.clock_gettime .monotonic).run s).1 with
  | ok _ => exact hCg s .monotonic
  | error _ => exact hCg s .monotonic

private theorem checkTimedOut_spec {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (startMs : Nat) (timeoutMs? : Option Nat) (s : S) :
    let r := (TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s
    proj r.2 = proj s ∧
    (timeoutMs? = none → r.1 = .ok (false, 0)) ∧
    (∀ rem, r.1 = .ok (true, rem) → timeoutMs?.isSome = true) := by
  dsimp only
  cases timeoutMs? with
  | none =>
    dsimp only [TimeRand.checkTimedOut, pure, StateT.pure, StateT.run]
    exact ⟨rfl, fun _ => rfl, (by intro _ h; cases h)⟩
  | some timeoutMs =>
    unfold TimeRand.checkTimedOut
    rw [stateT_bind_eq]
    have hF := monoNowMs_spec proj timeRand hCg s
    cases ((TimeRand.monoNowMs timeRand).run s).1 with
    | error _ =>
      dsimp only [pure, StateT.pure, StateT.run]
      exact ⟨hF, (by intro h; cases h), (by intro _ h; cases h)⟩
    | ok _ =>
      dsimp only
      split <;>
        (dsimp only [pure, StateT.pure, StateT.run]
         exact ⟨hF, (by intro h; cases h), fun _ _ => rfl⟩)

private theorem sleepMonoMs_frame {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (ms : Nat) (s : S) :
    proj ((TimeRand.sleepMonoMs timeRand ms).run s).2 = proj s := by
  unfold TimeRand.sleepMonoMs
  rw [stateT_bind_eq]
  exact hNs s _ _ _

private theorem writeStdinStep_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hWrite : ∀ s h d, getTbl ((files.write h d).run s).2 = getTbl s ∧
      openFds ((files.write h d).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    (inFd : fd) (fdAt : Bool → List fd)
    (hErase : ∀ st, openFds st = fdAt true → openFds ((files.close inFd).run st).2 = fdAt false)
    (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (pos : Nat) (prog : Bool) (fuel : Nat) (s : S)
    (hOpen : openFds s = fdAt true) :
    let r := (SysBridge.writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos prog fuel).run s
    getTbl r.2 = getTbl s ∧
    (∀ nextFd? p' pr, r.1 = .ok (nextFd?, p', pr, true) → timeoutMs?.isSome = true) ∧
    (∀ nextFd? p' pr to, r.1 = .ok (nextFd?, p', pr, to) →
      ∃ b', nextFd? = optFdOf inFd b' ∧ openFds r.2 = fdAt b') ∧
    (∀ err, r.1 = .error err →
      openFds r.2 = fdAt false ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hCgP : ∀ st clk, proj ((timeRand.clock_gettime clk).run st).2 = proj st :=
    fun st clk => Prod.ext (hCg st clk).1 (hCg st clk).2
  induction fuel generalizing pos prog s with
  | zero =>
    unfold SysBridge.writeStdinStep
    split
    · rw [stateT_bind_eq]
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s hOpen
      refine ⟨hT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨false, hN.symm, hO⟩
    · dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨rfl, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨true, hN.symm, hOpen⟩
  | succ f ih =>
    unfold SysBridge.writeStdinStep
    split
    · rw [stateT_bind_eq]
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s hOpen
      refine ⟨hT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨false, hN.symm, hO⟩
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = fdAt true :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s1 hFcO
        refine ⟨hT.trans hFcT, (by intro _ _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact ⟨hO, mapErrno_kind_and_msg none "clock_gettime" e⟩
      | ok pair =>
        rcases pair with ⟨isTo, rem⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          let slice := stdin.extract pos (Nat.min stdin.size (pos + STDIN_WRITE_CHUNK))
          have hFwT : getTbl ((files.write inFd slice).run s1).2 = getTbl s :=
            (hWrite s1 inFd slice).1.trans hFcT
          have hFwO : openFds ((files.write inFd slice).run s1).2 = fdAt true :=
            (hWrite s1 inFd slice).2.trans hFcO
          let s2 := ((files.write inFd slice).run s1).2
          cases hW : ((files.write inFd slice).run s1).1 with
          | ok n =>
            dsimp only
            split
            · rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
              refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
              intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
              exact ⟨false, hN.symm, hO⟩
            · split
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
                refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨false, hN.symm, hO⟩
              · obtain ⟨hFi, hTi, hOi, hEi⟩ := ih (pos + n.toNat) true s2 hFwO
                exact ⟨hFi.trans hFwT, hTi, hOi, hEi⟩
          | error e =>
            dsimp only
            split
            · obtain ⟨hFi, hTi, hOi, hEi⟩ := ih pos prog s2 hFwO
              exact ⟨hFi.trans hFwT, hTi, hOi, hEi⟩
            · split
              · dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨true, hN.symm, hFwO⟩
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
                refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨false, hN.symm, hO⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s1 hFcO
          refine ⟨hT.trans hFcT, fun _ _ _ _ => hTo rem hCt, ?_, (by intro _ h; cases h)⟩
          intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
          exact ⟨false, hN.symm, hO⟩

private theorem drainPipeStep_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hRead : ∀ s h c, getTbl ((files.read h c).run s).2 = getTbl s ∧
      openFds ((files.read h c).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    (pipeFd : fd) (fdAt : Bool → List fd)
    (hErase : ∀ st, openFds st = fdAt true → openFds ((files.close pipeFd).run st).2 = fdAt false)
    (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen iterBytes : Nat) (prog : Bool) (fuel : Nat) (s : S)
    (hOpen : openFds s = fdAt true)
    (hSum : (chunks.toList.map ByteArray.size).sum = curLen)
    (hCap : ∀ lim, maxOutputBytes? = some lim → curLen + otherLen ≤ lim) :
    let r := (SysBridge.drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
      chunks curLen iterBytes prog fuel).run s
    getTbl r.2 = getTbl s ∧
    (∀ ch' len', r.1 = .timedOut ch' len' →
      timeoutMs?.isSome = true ∧
      openFds r.2 = fdAt false ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ ch' len', r.1 = .limitExceeded ch' len' →
      openFds r.2 = fdAt false ∧
      maxOutputBytes?.isSome = true ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ fd? ch' len' pr, r.1 = .cont fd? ch' len' pr →
      (∃ b', fd? = optFdOf pipeFd b' ∧ openFds r.2 = fdAt b') ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ err, r.1 = .ioErr err →
      openFds r.2 = fdAt false ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hCgP : ∀ st clk, proj ((timeRand.clock_gettime clk).run st).2 = proj st :=
    fun st clk => Prod.ext (hCg st clk).1 (hCg st clk).2
  induction fuel generalizing chunks curLen iterBytes prog s with
  | zero =>
    unfold SysBridge.drainPipeStep
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
    intro fd? ch' len' _ hEq
    injection hEq with hFd hCh hLen _
    subst hCh hLen
    exact ⟨⟨true, hFd.symm, hOpen⟩, hSum, hCap⟩
  | succ f ih =>
    unfold SysBridge.drainPipeStep
    split
    · dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro fd? ch' len' _ hEq
      injection hEq with hFd hCh hLen _
      subst hCh hLen
      exact ⟨⟨true, hFd.symm, hOpen⟩, hSum, hCap⟩
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = fdAt true :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s1 hFcO
        refine ⟨hT.trans hFcT,
          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact ⟨hO, mapErrno_kind_and_msg none "clock_gettime" e⟩
      | ok pair =>
        rcases pair with ⟨isTo, rem⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          have hFrT : getTbl ((files.read pipeFd PIPE_READ_CHUNK).run s1).2 = getTbl s :=
            (hRead s1 pipeFd PIPE_READ_CHUNK).1.trans hFcT
          have hFrO : openFds ((files.read pipeFd PIPE_READ_CHUNK).run s1).2 = fdAt true :=
            (hRead s1 pipeFd PIPE_READ_CHUNK).2.trans hFcO
          let s2 := ((files.read pipeFd PIPE_READ_CHUNK).run s1).2
          cases hR : ((files.read pipeFd PIPE_READ_CHUNK).run s1).1 with
          | ok chunk =>
            dsimp only
            split
            · rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
              refine ⟨hT.trans hFrT,
                (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
              intro fd? ch' len' _ hEq
              injection hEq with hFd hCh hLen _
              subst hCh hLen
              exact ⟨⟨false, hFd.symm, hO⟩, hSum, hCap⟩
            · have hPushSum : ((chunks.push chunk).toList.map ByteArray.size).sum = curLen + chunk.size := by
                simp [Array.toList_push, hSum]
              cases maxOutputBytes? with
              | none =>
                dsimp only
                obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih (chunks.push chunk) (curLen + chunk.size)
                  (iterBytes + chunk.size) true s2 hFrO hPushSum (fun _ hm => by cases hm)
                exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
              | some maxOut =>
                dsimp only
                have hCurLe : curLen + otherLen ≤ maxOut := hCap maxOut rfl
                by_cases hGt : curLen + otherLen + chunk.size > maxOut
                · rw [ite_eq_left hGt]
                  by_cases hKeep : maxOut - (curLen + otherLen) > 0
                  · rw [ite_eq_left hKeep]
                    dsimp only
                    rw [stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                    have hPreSz : (chunk.extract 0 (maxOut - (curLen + otherLen))).size = maxOut - (curLen + otherLen) := by
                      rw [ByteArray.size_extract]
                      omega
                    have hPreSum :
                        ((chunks.push (chunk.extract 0 (maxOut - (curLen + otherLen)))).toList.map ByteArray.size).sum =
                          curLen + (chunk.extract 0 (maxOut - (curLen + otherLen))).size := by
                      simp [Array.toList_push, hSum]
                    refine ⟨hT.trans hFrT,
                      (by intro _ _ h; cases h), ?_, (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
                    intro ch' len' hEq
                    injection hEq with hCh hLen
                    subst hCh hLen
                    refine ⟨hO, rfl, hPreSum, ?_⟩
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    rw [hPreSz]
                    omega
                  · rw [ite_eq_right hKeep]
                    dsimp only
                    rw [stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                    refine ⟨hT.trans hFrT,
                      (by intro _ _ h; cases h), ?_, (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
                    intro ch' len' hEq
                    injection hEq with hCh hLen
                    subst hCh hLen
                    refine ⟨hO, rfl, hSum, ?_⟩
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    exact hCurLe
                · rw [ite_eq_right hGt]
                  have hNextCap : ∀ lim, some maxOut = some lim → (curLen + chunk.size) + otherLen ≤ lim := by
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    omega
                  obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih (chunks.push chunk) (curLen + chunk.size)
                    (iterBytes + chunk.size) true s2 hFrO hPushSum hNextCap
                  exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
          | error e =>
            dsimp only
            split
            · obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih chunks curLen iterBytes prog s2 hFrO hSum hCap
              exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
            · split
              · dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hFrT, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro fd? ch' len' _ hEq
                injection hEq with hFd hCh hLen _
                subst hCh hLen
                exact ⟨⟨true, hFd.symm, hFrO⟩, hSum, hCap⟩
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                refine ⟨hT.trans hFrT,
                  (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
                intro err hEq
                injection hEq with hE
                subst hE
                exact ⟨hO, mapErrno_kind_and_msg none "read" e⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s1 hFcO
          refine ⟨hT.trans hFcT, ?_, (by intro _ _ h; cases h),
            (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
          intro ch' len' hEq
          injection hEq with hCh hLen
          subst hCh hLen
          exact ⟨hTo rem hCt, hO, hSum, hCap⟩

private theorem streamPipesLoop_spec {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (poll : Poll.PollOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hCloseO : ∀ s h, openFds ((files.close h).run s).2 = (openFds s).erase h)
    (hRead : ∀ s h c, getTbl ((files.read h c).run s).2 = getTbl s ∧
      openFds ((files.read h c).run s).2 = openFds s)
    (hWrite : ∀ s h d, getTbl ((files.write h d).run s).2 = getTbl s ∧
      openFds ((files.write h d).run s).2 = openFds s)
    (hPoll : ∀ s entries to, getTbl ((poll.ppoll entries to).run s).2 = getTbl s ∧
      openFds ((poll.ppoll entries to).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    {errR outR inW : fd} (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW)
    (base : List fd)
    (stdin : ByteArray) (startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat) (stepFuel : Nat)
    (bErr bOut bIn : Bool)
    (st : StreamLoopState fd) (ioFuel : Nat) (s : S)
    (hIn : st.inFd? = optFdOf inW bIn)
    (hOut : st.outFd? = optFdOf outR bOut)
    (hErr : st.errFd? = optFdOf errR bErr)
    (hOpen : openFds s = pipePrefix errR outR inW bErr bOut bIn base)
    (hOutSum : (st.outChunks.toList.map ByteArray.size).sum = st.outLen)
    (hErrSum : (st.errChunks.toList.map ByteArray.size).sum = st.errLen)
    (hCap : ∀ lim, maxOutputBytes? = some lim → st.outLen + st.errLen ≤ lim) :
    let r := (SysBridge.streamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st ioFuel).run s
    getTbl r.2 = getTbl s ∧
    openFds r.2 = base ∧
    (∀ out errB, r.1 = .ok (.eof out errB) →
      ∀ lim, maxOutputBytes? = some lim → out.size + errB.size ≤ lim) ∧
    (∀ out errB, r.1 = .ok (.timedOut out errB) → timeoutMs?.isSome = true) ∧
    (∀ out errB, r.1 = .ok (.limitExceeded out errB) →
      maxOutputBytes?.isSome = true ∧
      (∀ lim, maxOutputBytes? = some lim → out.size + errB.size ≤ lim)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun s0 : S => (getTbl s0, openFds s0)
  have hCgP : ∀ s0 clk, proj ((timeRand.clock_gettime clk).run s0).2 = proj s0 :=
    fun s0 clk => Prod.ext (hCg s0 clk).1 (hCg s0 clk).2
  induction ioFuel generalizing bErr bOut bIn st s with
  | zero =>
    unfold SysBridge.streamPipesLoop
    rw [stateT_bind_eq]
    dsimp only [pure, StateT.pure, StateT.run]
    obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
      hEO hEI hOI st s hIn hOut hErr hOpen
    refine ⟨hT, hO, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
    intro err hEq
    injection hEq with hE
    rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ fuel ih =>
    unfold SysBridge.streamPipesLoop
    split
    · next hAllNone =>
      rw [Bool.and_eq_true, Bool.and_eq_true] at hAllNone
      have hbIn : bIn = false := optFdOf_isNone inW bIn (hIn ▸ hAllNone.1.1)
      have hbOut : bOut = false := optFdOf_isNone outR bOut (hOut ▸ hAllNone.1.2)
      have hbErr : bErr = false := optFdOf_isNone errR bErr (hErr ▸ hAllNone.2)
      subst hbIn hbOut hbErr
      dsimp only [pure, StateT.pure, StateT.run]
      have hO : openFds s = base := by simpa [pipePrefix] using hOpen
      refine ⟨rfl, hO, ?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
      intro out errB hEq lim hLim
      injection hEq with hSub
      injection hSub with hO1 hE1
      rw [← hO1, ← hE1, concatChunks_size, concatChunks_size, hOutSum, hErrSum]
      exact hCap lim hLim
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 =
          pipePrefix errR outR inW bErr bOut bIn base :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
          hEO hEI hOI st s1 hIn hOut hErr hFcO
        refine ⟨hT.trans hFcT, hO,
          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact mapErrno_kind_and_msg none "clock_gettime" e
      | ok pair =>
        rcases pair with ⟨isTo, remMs⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          let pollTimeout? : Option Poll.Timespec :=
            timeoutMs?.map fun _ => Poll.msToPollTimespec remMs
          let pollRun := (poll.ppoll (SysBridge.buildPollEntries st) pollTimeout?).run s1
          have hPollFrame := hPoll s1 (SysBridge.buildPollEntries st) pollTimeout?
          have hFpT : getTbl pollRun.2 = getTbl s := hPollFrame.1.trans hFcT
          have hFpO : openFds pollRun.2 = pipePrefix errR outR inW bErr bOut bIn base :=
            hPollFrame.2.trans hFcO
          cases hPr : pollRun.1 with
          | error pe =>
            dsimp only
            by_cases hEintr : pe == Errno.EINTR
            · simp only [hEintr, ↓reduceIte]
              obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr bOut bIn st pollRun.2
                hIn hOut hErr hFpO hOutSum hErrSum hCap
              exact ⟨hFi.trans hFpT, hOi, hEofI, hToI, hLiI, hErrI⟩
            · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
              rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
                hEO hEI hOI st pollRun.2 hIn hOut hErr hFpO
              refine ⟨hT.trans hFpT, hO,
                (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
              intro err hEq
              injection hEq with hE
              rw [← hE]
              exact mapErrno_kind_and_msg none "ppoll" pe
          | ok revents =>
            dsimp only
            generalize SysBridge.decodeReadyFlags st revents = rFlags
            rcases rFlags with ⟨inReady, outReady, errReady⟩
            dsimp only
            by_cases hIdle : (!inReady && !outReady && !errReady) = true
            · simp only [hIdle, ↓reduceIte]
              obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr bOut bIn st pollRun.2
                hIn hOut hErr hFpO hOutSum hErrSum hCap
              exact ⟨hFi.trans hFpT, hOi, hEofI, hToI, hLiI, hErrI⟩
            · simp only [hIdle, Bool.false_eq_true, ↓reduceIte]
              have hStdinStep :
                  ∃ bIn' inFdNext? stdinPos' inProg inTimedOut inErr? s2,
                    (SysBridge.stepStdinIfReady inReady files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel).run pollRun.2 =
                      ((inFdNext?, stdinPos', inProg, inTimedOut, inErr?), s2) ∧
                    getTbl s2 = getTbl s ∧
                    inFdNext? = optFdOf inW bIn' ∧
                    openFds s2 = pipePrefix errR outR inW bErr bOut bIn' base ∧
                    (inTimedOut = true → timeoutMs?.isSome = true) ∧
                    (∀ e, inErr? = some e →
                      bIn' = false ∧
                      e.message ≠ "" ∧ e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal) := by
                unfold SysBridge.stepStdinIfReady
                cases inReady
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact ⟨bIn, st.inFd?, st.stdinPos, false, false, none, pollRun.2, rfl,
                    hFpT, hIn, hFpO, (by intro h; cases h), (by intro _ h; cases h)⟩
                · simp only [↓reduceIte]
                  unfold SysBridge.stepStdinOpt
                  rw [hIn]
                  cases bIn with
                  | false =>
                    exact ⟨false, none, st.stdinPos, false, false, none, pollRun.2, rfl, hFpT, rfl, hFpO,
                      (by intro h; cases h), (by intro _ h; cases h)⟩
                  | true =>
                    dsimp only [optFdOf]
                    obtain ⟨hFw, hTw, hOw, hEw⟩ := writeStdinStep_spec getTbl openFds files timeRand
                      hCloseT hWrite hCg inW (fun b => pipePrefix errR outR inW bErr bOut b base)
                      (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_in hEI hOI])
                      stdin startMs timeoutMs? st.stdinPos false stepFuel pollRun.2 hFpO
                    let rwS := (SysBridge.writeStdinStep files timeRand inW stdin startMs timeoutMs? st.stdinPos false stepFuel).run pollRun.2
                    cases hRw : rwS.1 with
                    | error e =>
                      obtain ⟨hOErr, hMsgErr⟩ := hEw e hRw
                      refine ⟨false, none, st.stdinPos, false, false, some e, rwS.2, ?_, hFw.trans hFpT,
                        rfl, hOErr, (by intro h; cases h), ?_⟩
                      · rw [stateT_bind_eq]; dsimp only [rwS] at hRw; rw [hRw]; rfl
                      · intro err he; injection he with hEq; rw [← hEq]; exact ⟨rfl, hMsgErr⟩
                    | ok tup =>
                      rcases tup with ⟨nFd, p', pr, to⟩
                      obtain ⟨bIn', hnFd, hOOk⟩ := hOw nFd p' pr to hRw
                      refine ⟨bIn', nFd, p', pr, to, none, rwS.2, ?_, hFw.trans hFpT,
                        hnFd, hOOk,
                        fun hToTrue => hTw nFd p' pr (by rw [hToTrue] at hRw; exact hRw),
                        (by intro _ h; cases h)⟩
                      rw [stateT_bind_eq]; dsimp only [rwS] at hRw; rw [hRw]; rfl
              rcases hStdinStep with ⟨bIn', inFdNext?, stdinPos', inProg, inTimedOut, inErr?, s2,
                hRunIn, hFs2, hInNext, hOs2, hInTo, hInErr⟩
              rw [stateT_bind_eq, hRunIn]
              dsimp only
              cases inErr? with
              | some e =>
                dsimp only
                obtain ⟨hbInF, hMsgIn⟩ := hInErr e rfl
                subst hbInF
                rw [hOut, hErr, stateT_bind_eq, stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hTOut, hOOut⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                  (fun b => pipePrefix errR outR inW bErr b false base)
                  (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_out hEO]) bOut s2 hOs2
                let s2a := ((Files.closeOpt files (optFdOf outR bOut)).run s2).2
                obtain ⟨hTErr, hOErr⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                  (fun b => pipePrefix errR outR inW b false false base)
                  (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_err]) bErr s2a hOOut
                refine ⟨hTErr.trans (hTOut.trans hFs2), hOErr,
                  (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgIn
              | none =>
                dsimp only
                cases hInToB : inTimedOut
                · rw [ite_eq_right (by decide)]
                  have hOutStep :
                      ∃ outRes s3,
                        (SysBridge.stepDrainIfReady outReady files timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                          st.outChunks st.outLen stepFuel).run s2 = (outRes, s3) ∧
                        getTbl s3 = getTbl s ∧
                        (∀ ch' len', outRes = .timedOut ch' len' →
                          timeoutMs?.isSome = true ∧
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ ch' len', outRes = .limitExceeded ch' len' →
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          maxOutputBytes?.isSome = true ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ fd? ch' len' pr, outRes = .cont fd? ch' len' pr →
                          (∃ bOut', fd? = optFdOf outR bOut' ∧
                            openFds s3 = pipePrefix errR outR inW bErr bOut' bIn' base) ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ err, outRes = .ioErr err →
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          err.message ≠ "" ∧ err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
                    unfold SysBridge.stepDrainIfReady
                    cases outReady
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      refine ⟨.cont st.outFd? st.outChunks st.outLen false, s2, rfl, hFs2,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                      intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst hFd h1 h2
                      exact ⟨⟨bOut, hOut, hOs2⟩, hOutSum, hCap⟩
                    · simp only [↓reduceIte]
                      unfold SysBridge.stepDrainOpt
                      rw [hOut]
                      cases bOut with
                      | false =>
                        refine ⟨.cont none st.outChunks st.outLen false, s2, rfl, hFs2,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                        intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst h1 h2
                        exact ⟨⟨false, hFd.symm, hOs2⟩, hOutSum, hCap⟩
                      | true =>
                        dsimp only [optFdOf]
                        obtain ⟨hFo, hToO, hLiO, hCoO, hEoO⟩ := drainPipeStep_spec getTbl openFds files timeRand
                          hCloseT hRead hCg outR (fun b => pipePrefix errR outR inW bErr b bIn' base)
                          (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_out hEO])
                          st.errLen startMs timeoutMs? maxOutputBytes?
                          st.outChunks st.outLen 0 false stepFuel s2 hOs2 hOutSum hCap
                        exact ⟨_, _, rfl, hFo.trans hFs2, hToO, hLiO, hCoO, hEoO⟩
                  rcases hOutStep with ⟨outRes, s3, hRunOut, hFs3, hToO, hLiO, hCoO, hEoO⟩
                  rw [stateT_bind_eq, hRunOut]
                  dsimp only
                  have hCloseInAndErr : ∀ st0,
                      openFds st0 = pipePrefix errR outR inW bErr false bIn' base →
                      getTbl st0 = getTbl s →
                      let rEnd := ((Files.closeOpt files st.errFd?).run
                        ((Files.closeOpt files inFdNext?).run st0).2)
                      getTbl rEnd.2 = getTbl s ∧ openFds rEnd.2 = base := by
                    intro st0 hO0 hT0
                    rw [hInNext, hErr]
                    obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                      (fun b => pipePrefix errR outR inW bErr false b base)
                      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' st0 hO0
                    obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                      (fun b => pipePrefix errR outR inW b false false base)
                      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) bErr _ hO1
                    exact ⟨hT2.trans (hT1.trans hT0), hO2⟩
                  cases outRes with
                  | ioErr e =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hO3, hMsgO⟩ := hEoO e rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    refine ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                    intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgO
                  | timedOut outChunks' outLen' =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hSomeTo, hO3, _, _⟩ := hToO outChunks' outLen' rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    exact ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), fun _ _ _ => hSomeTo,
                      (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                  | limitExceeded outChunks' outLen' =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hO3, hSome, hOSum', hOCap'⟩ := hLiO outChunks' outLen' rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    refine ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                    intro out errB hEq
                    injection hEq with hSub
                    injection hSub with hO1 hE1
                    rw [← hO1, ← hE1]
                    refine ⟨hSome, ?_⟩
                    intro lim hLim
                    rw [concatChunks_size, concatChunks_size, hOSum', hErrSum]
                    exact hOCap' lim hLim
                  | cont outFdNext? outChunks' outLen' outProg =>
                    dsimp only
                    obtain ⟨⟨bOut', hOutNext, hOs3⟩, hOSum', hOCap'⟩ := hCoO outFdNext? outChunks' outLen' outProg rfl
                    have hErrCapIn : ∀ lim, maxOutputBytes? = some lim → st.errLen + outLen' ≤ lim := by
                      intro lim hLim; have := hOCap' lim hLim; omega
                    have hErrStep :
                        ∃ errRes s4,
                          (SysBridge.stepDrainIfReady errReady files timeRand st.errFd? outLen' startMs timeoutMs? maxOutputBytes?
                            st.errChunks st.errLen stepFuel).run s3 = (errRes, s4) ∧
                          getTbl s4 = getTbl s ∧
                          (∀ ch' len', errRes = .timedOut ch' len' →
                            timeoutMs?.isSome = true ∧
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ ch' len', errRes = .limitExceeded ch' len' →
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            maxOutputBytes?.isSome = true ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ fd? ch' len' pr, errRes = .cont fd? ch' len' pr →
                            (∃ bErr', fd? = optFdOf errR bErr' ∧
                              openFds s4 = pipePrefix errR outR inW bErr' bOut' bIn' base) ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ err, errRes = .ioErr err →
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            err.message ≠ "" ∧ err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
                      unfold SysBridge.stepDrainIfReady
                      cases errReady
                      · simp only [Bool.false_eq_true, ↓reduceIte]
                        refine ⟨.cont st.errFd? st.errChunks st.errLen false, s3, rfl, hFs3,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                        intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst hFd h1 h2
                        exact ⟨⟨bErr, hErr, hOs3⟩, hErrSum, hErrCapIn⟩
                      · simp only [↓reduceIte]
                        unfold SysBridge.stepDrainOpt
                        rw [hErr]
                        cases bErr with
                        | false =>
                          refine ⟨.cont none st.errChunks st.errLen false, s3, rfl, hFs3,
                            (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                          intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst h1 h2
                          exact ⟨⟨false, hFd.symm, hOs3⟩, hErrSum, hErrCapIn⟩
                        | true =>
                          dsimp only [optFdOf]
                          obtain ⟨hFe, hToE, hLiE, hCoE, hEoE⟩ := drainPipeStep_spec getTbl openFds files timeRand
                            hCloseT hRead hCg errR (fun b => pipePrefix errR outR inW b bOut' bIn' base)
                            (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_err])
                            outLen' startMs timeoutMs? maxOutputBytes?
                            st.errChunks st.errLen 0 false stepFuel s3 hOs3 hErrSum hErrCapIn
                          exact ⟨_, _, rfl, hFe.trans hFs3, hToE, hLiE, hCoE, hEoE⟩
                    rcases hErrStep with ⟨errRes, s4, hRunErr, hFs4, hToE, hLiE, hCoE, hEoE⟩
                    rw [stateT_bind_eq, hRunErr]
                    dsimp only
                    have hCloseInAndOut : ∀ st0,
                        openFds st0 = pipePrefix errR outR inW false bOut' bIn' base →
                        getTbl st0 = getTbl s →
                        let rEnd := ((Files.closeOpt files outFdNext?).run
                          ((Files.closeOpt files inFdNext?).run st0).2)
                        getTbl rEnd.2 = getTbl s ∧ openFds rEnd.2 = base := by
                      intro st0 hO0 hT0
                      rw [hInNext, hOutNext]
                      obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                        (fun b => pipePrefix errR outR inW false bOut' b base)
                        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' st0 hO0
                      obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                        (fun b => pipePrefix errR outR inW false b false base)
                        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) bOut' _ hO1
                      exact ⟨hT2.trans (hT1.trans hT0), hO2⟩
                    cases errRes with
                    | ioErr e =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hO4, hMsgE⟩ := hEoE e rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      refine ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                      intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgE
                    | timedOut errChunks' errLen' =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hSomeTo, hO4, _, _⟩ := hToE errChunks' errLen' rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      exact ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), fun _ _ _ => hSomeTo,
                        (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                    | limitExceeded errChunks' errLen' =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hO4, hSome, hESum', hECap'⟩ := hLiE errChunks' errLen' rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      refine ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                      intro out errB hEq
                      injection hEq with hSub
                      injection hSub with hO1 hE1
                      rw [← hO1, ← hE1]
                      refine ⟨hSome, ?_⟩
                      intro lim hLim
                      rw [concatChunks_size, concatChunks_size, hOSum', hESum']
                      have := hECap' lim hLim
                      omega
                    | cont errFdNext? errChunks' errLen' errProg =>
                      dsimp only
                      obtain ⟨⟨bErr', hErrNext, hOs4⟩, hESum', hECap'⟩ := hCoE errFdNext? errChunks' errLen' errProg rfl
                      have hNextCap : ∀ lim, maxOutputBytes? = some lim → outLen' + errLen' ≤ lim := by
                        intro lim hLim; have := hECap' lim hLim; omega
                      split
                      · next hNextAllNone =>
                        rw [Bool.and_eq_true, Bool.and_eq_true] at hNextAllNone
                        have hbIn' : bIn' = false := optFdOf_isNone inW bIn' (hInNext ▸ hNextAllNone.1.1)
                        have hbOut' : bOut' = false := optFdOf_isNone outR bOut' (hOutNext ▸ hNextAllNone.1.2)
                        have hbErr' : bErr' = false := optFdOf_isNone errR bErr' (hErrNext ▸ hNextAllNone.2)
                        subst hbIn' hbOut' hbErr'
                        dsimp only [pure, StateT.pure, StateT.run]
                        have hOEnd : openFds s4 = base := by simpa [pipePrefix] using hOs4
                        refine ⟨hFs4, hOEnd, ?_,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                        intro out errB hEq lim hLim
                        injection hEq with hSub
                        injection hSub with hO1 hE1
                        rw [← hO1, ← hE1, concatChunks_size, concatChunks_size, hOSum', hESum']
                        exact hNextCap lim hLim
                      · obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr' bOut' bIn'
                          { inFd? := inFdNext?
                            outFd? := outFdNext?
                            errFd? := errFdNext?
                            stdinPos := stdinPos'
                            outChunks := outChunks'
                            outLen := outLen'
                            errChunks := errChunks'
                            errLen := errLen' }
                          s4 hInNext hOutNext hErrNext hOs4 hOSum' hESum' hNextCap
                        exact ⟨hFi.trans hFs4, hOi, hEofI, hToI, hLiI, hErrI⟩
                · rw [ite_eq_left rfl]
                  rw [hInNext, hOut, hErr, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                  dsimp only [pure, StateT.pure, StateT.run]
                  obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                    (fun b => pipePrefix errR outR inW bErr bOut b base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' s2 hOs2
                  obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                    (fun b => pipePrefix errR outR inW bErr b false base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) bOut _ hO1
                  obtain ⟨hT3, hO3⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                    (fun b => pipePrefix errR outR inW b false false base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) bErr _ hO2
                  exact ⟨hT3.trans (hT2.trans (hT1.trans hFs2)), hO3,
                    (by intro _ _ h; cases h), fun _ _ _ => hInTo hInToB,
                    (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
            hEO hEI hOI st s1 hIn hOut hErr hFcO
          exact ⟨hT.trans hFcT, hO,
            (by intro _ _ h; cases h), fun _ _ _ => hTo remMs hCt,
            (by intro _ _ h; cases h), (by intro _ h; cases h)⟩

private theorem decodeWaitOutcome_spec (wr : LinuxSyscall.Process.WaitResult) (out errB : ByteArray) :
    (∀ res, SysBridge.decodeWaitOutcome wr out errB = .exited res → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ o e, SysBridge.decodeWaitOutcome wr out errB ≠ .timedOut o e) ∧
    (∀ o e, SysBridge.decodeWaitOutcome wr out errB ≠ .outputLimitExceeded o e) := by
  cases wr with
  | signaled _ _ _ =>
    dsimp only [SysBridge.decodeWaitOutcome]
    exact ⟨(by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
  | exited _ _ | stopped _ _ | continued _ | stillRunning =>
    dsimp only [SysBridge.decodeWaitOutcome]
    refine ⟨?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
    intro res hEq
    injection hEq with hR
    rw [← hR]
    exact ⟨rfl, rfl⟩

private theorem waitBlockingLoop_spec {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (pid : Int32) (out errB : ByteArray) (fuel : Nat) (s : S) :
    let r := (SysBridge.waitBlockingLoop proc pid out errB fuel).run s
    proj r.2 = proj s ∧
    (∀ res, r.1 = .ok (.exited res) → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ o e, r.1 ≠ .ok (.timedOut o e)) ∧
    (∀ o e, r.1 ≠ .ok (.outputLimitExceeded o e)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  induction fuel generalizing s with
  | zero =>
    unfold SysBridge.waitBlockingLoop
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ f ih =>
    unfold SysBridge.waitBlockingLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid {}
    let s1 := ((proc.waitpid pid {}).run s).2
    cases hW : ((proc.waitpid pid {}).run s).1 with
    | ok wr =>
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hEx, hNoTo, hNoLim⟩ := decodeWaitOutcome_spec wr out errB
      refine ⟨hFw, ?_, ?_, ?_, (by intro _ h; cases h)⟩
      · intro res hEq; injection hEq with hSub; exact hEx res hSub
      · intro o e hEq; injection hEq with hSub; exact hNoTo o e hSub
      · intro o e hEq; injection hEq with hSub; exact hNoLim o e hSub
    | error e =>
      dsimp only
      split
      · obtain ⟨hFi, hEx, hNoTo, hNoLim, hEi⟩ := ih s1
        exact ⟨hFi.trans hFw, hEx, hNoTo, hNoLim, hEi⟩
      · split
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, ?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
          intro res hEq; injection hEq with hSub; injection hSub with hR; rw [← hR]; exact ⟨rfl, rfl⟩
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, (by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "waitpid" e

private theorem waitTimedLoop_spec {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (pid : Int32) (startMs timeoutMs : Nat) (out errB : ByteArray) (fuel : Nat) (s : S) :
    let r := (SysBridge.waitTimedLoop proc timeRand pid startMs timeoutMs out errB fuel).run s
    proj r.2 = proj s ∧
    (∀ w res, r.1 = .ok (w, .exited res) → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ w o e, r.1 ≠ .ok (w, .outputLimitExceeded o e)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  induction fuel generalizing s with
  | zero =>
    unfold SysBridge.waitTimedLoop
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ f ih =>
    unfold SysBridge.waitTimedLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid { nohang := true }
    let s1 := ((proc.waitpid pid { nohang := true }).run s).2
    cases hW : ((proc.waitpid pid { nohang := true }).run s).1 with
    | ok wr =>
      cases wr with
      | stillRunning =>
        dsimp only
        rw [stateT_bind_eq]
        obtain ⟨hFc, _, _⟩ := checkTimedOut_spec proj timeRand hCg startMs (some timeoutMs) s1
        let s2 := ((TimeRand.checkTimedOut timeRand startMs (some timeoutMs)).run s1).2
        cases hCt : ((TimeRand.checkTimedOut timeRand startMs (some timeoutMs)).run s1).1 with
        | error e =>
          dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFc.trans hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "clock_gettime" e
        | ok pair =>
          rcases pair with ⟨isTo, remMs⟩
          cases isTo
          · dsimp only
            rw [stateT_bind_eq]
            have hFs := sleepMonoMs_frame proj timeRand hNs (Nat.min remMs 5) s2
            obtain ⟨hFi, hEx, hNoLim, hEi⟩ := ih ((TimeRand.sleepMonoMs timeRand (Nat.min remMs 5)).run s2).2
            exact ⟨hFi.trans (hFs.trans (hFc.trans hFw)), hEx, hNoLim, hEi⟩
          · dsimp only [pure, StateT.pure, StateT.run]
            exact ⟨hFc.trans hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
      | exited rPid code =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
      | signaled rPid sig core =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        exact ⟨hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
      | stopped rPid sig =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
      | continued rPid =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
    | error e =>
      dsimp only
      split
      · obtain ⟨hFi, hEx, hNoLim, hEi⟩ := ih s1
        exact ⟨hFi.trans hFw, hEx, hNoLim, hEi⟩
      · split
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
          intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
          exact ⟨rfl, rfl⟩
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "waitpid" e

private theorem killGraceProbeLoop_frame {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hKill : ∀ s t sg, proj ((proc.kill t sg).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (target : Int32) (steps : Nat) (s : S) :
    proj ((SysBridge.killGraceProbeLoop proc timeRand target steps).run s).2 = proj s := by
  induction steps generalizing s with
  | zero => rfl
  | succ st ih =>
    unfold SysBridge.killGraceProbeLoop
    rw [stateT_bind_eq, stateT_bind_eq]
    have hFs := sleepMonoMs_frame proj timeRand hNs 5 s
    let s1 := ((TimeRand.sleepMonoMs timeRand 5).run s).2
    have hFk := hKill s1 target .sigzero
    let s2 := ((proc.kill target .sigzero).run s1).2
    cases ((proc.kill target .sigzero).run s1).1 with
    | error e =>
      dsimp only
      split
      · exact hFk.trans hFs
      · exact (ih s2).trans (hFk.trans hFs)
    | ok _ =>
      dsimp only
      exact (ih s2).trans (hFk.trans hFs)

private theorem killProcessGroupPure_frame {S β fd : Type}
    (proj : S → β)
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (deps : SysDepsM (StateM S) fd)
    (hKill : ∀ s t sg, proj ((deps.proc.kill t sg).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((deps.timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (eintrFuel : Nat) (h : ProcessHandle) (s : S) :
    proj ((SysBridge.killProcessGroupPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run s).2 =
      proj s := by
  unfold SysBridge.killProcessGroupPure
  rw [stateT_bind_eq]
  have hLk : ((SysBridge.stateProcTableOps getTbl setTbl).lookupPgid h.handleId).run s =
      ((SysBridge.findSlotPure h.handleId (getTbl s).slots).map (·.pgid), s) := rfl
  rw [hLk]
  dsimp only
  cases (SysBridge.findSlotPure h.handleId (getTbl s).slots).map (·.pgid) with
  | none => rfl
  | some pgid =>
    dsimp only
    split
    · rfl
    · rw [stateT_bind_eq]
      let target := LinuxSyscall.Process.killTargetOfPgid pgid
      have hF1 := retryEintr_frame proj (deps.proc.kill target .sigterm)
        (fun st => hKill st target .sigterm) eintrFuel s
      let s1 := ((LinuxSyscall.retryEintr (deps.proc.kill target .sigterm) eintrFuel).run s).2
      cases ((LinuxSyscall.retryEintr (deps.proc.kill target .sigterm) eintrFuel).run s).1 with
      | error e =>
        dsimp only
        split <;> exact hF1
      | ok _ =>
        dsimp only
        rw [stateT_bind_eq]
        have hFg := killGraceProbeLoop_frame proj deps.proc deps.timeRand hKill hNs target 5 s1
        let s2 := ((SysBridge.killGraceProbeLoop deps.proc deps.timeRand target 5).run s1).2
        cases ((SysBridge.killGraceProbeLoop deps.proc deps.timeRand target 5).run s1).1 with
        | true => exact hFg.trans hF1
        | false =>
          rw [ite_eq_right (by decide)]
          rw [stateT_bind_eq]
          have hF2 := retryEintr_frame proj (deps.proc.kill target .sigkill)
            (fun st => hKill st target .sigkill) eintrFuel s2
          cases ((LinuxSyscall.retryEintr (deps.proc.kill target .sigkill) eintrFuel).run s2).1 with
          | error e =>
            dsimp only
            split <;> exact hF2.trans (hFg.trans hF1)
          | ok _ =>
            exact hF2.trans (hFg.trans hF1)

private theorem reapWaitLoop_frame {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (pid : Int32) (fuel : Nat) (s : S) :
    proj ((LinuxSyscall.Process.waitpidReapLoop proc pid fuel).run s).2 = proj s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih =>
    unfold LinuxSyscall.Process.waitpidReapLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid {}
    cases ((proc.waitpid pid {}).run s).1 with
    | ok _ => exact hFw
    | error _ =>
      dsimp only
      split
      · exact (ih _).trans hFw
      · split <;> exact hFw

private theorem reapPure_head_slot_none_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (hGetSet : ∀ s t, getTbl (setTbl s t) = t)
    (hOpenSet : ∀ s t, openFds (setTbl s t) = openFds s)
    (deps : SysDepsM (StateM S) fd)
    (hWait : ∀ s pid fl,
      getTbl ((deps.proc.waitpid pid fl).run s).2 = getTbl s ∧
      openFds ((deps.proc.waitpid pid fl).run s).2 = openFds s)
    (eintrFuel : Nat) (h : ProcessHandle) (slot : ProcSlotM fd)
    (rest : List (Nat × ProcSlotM fd)) (nextId : Nat) (s : S)
    (hTbl : getTbl s = { nextId := nextId, slots := (h.handleId, slot) :: rest })
    (hFdsNone : slot.stdinFd? = none ∧ slot.stdoutFd? = none ∧ slot.stderrFd? = none) :
    let r := (SysBridge.reapPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run s
    (getTbl r.2).slots.length = rest.length ∧
    openFds r.2 = openFds s ∧
    (∀ err, r.1 = .error err →
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hWaitP : ∀ st pid fl, proj ((deps.proc.waitpid pid fl).run st).2 = proj st :=
    fun st pid fl => Prod.ext (hWait st pid fl).1 (hWait st pid fl).2
  unfold SysBridge.reapPure
  rw [stateT_bind_eq]
  have hDet : ((SysBridge.stateProcTableOps getTbl setTbl).detachSlot h.handleId).run s =
      (some slot, setTbl s { nextId := nextId, slots := rest }) := by
    dsimp only [SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    rw [hTbl]
    simp only [SysBridge.detachSlotPure, SysBridge.removeSlotList, beq_self_eq_true, ↓reduceIte]
    rfl
  rw [hDet]
  dsimp only
  let s1 := setTbl s { nextId := nextId, slots := rest }
  have hGs1 : getTbl s1 = { nextId := nextId, slots := rest } := hGetSet s _
  have hOs1 : openFds s1 = openFds s := hOpenSet s _
  rw [hFdsNone.1, hFdsNone.2.1, hFdsNone.2.2]
  dsimp only [Files.closeOpt]
  rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
  dsimp only [pure, StateT.pure, StateT.run]
  split
  · have hFrP := reapWaitLoop_frame proj deps.proc hWaitP slot.pid.toInt32 eintrFuel s1
    dsimp only [StateT.run] at hFrP
    rcases hW : LinuxSyscall.Process.waitpidReapLoop deps.proc slot.pid.toInt32 eintrFuel s1 with ⟨wRes, sW⟩
    rw [hW] at hFrP
    have hFrT : getTbl sW = { nextId := nextId, slots := rest } := (congrArg Prod.fst hFrP).trans hGs1
    have hFrO : openFds sW = openFds s := (congrArg Prod.snd hFrP).trans hOs1
    dsimp only [bind, StateT.bind, StateT.run]
    change _ ∧ _ ∧ _
    have hW' : LinuxSyscall.Process.waitpidReapLoop deps.proc slot.pid.toInt32 eintrFuel
        (setTbl s { nextId := nextId, slots := rest }) = (wRes, sW) := hW
    rw [hW']
    cases wRes with
    | ok _ =>
      exact ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, (by intro _ h; cases h)⟩
    | error oe =>
      cases oe with
      | none =>
        refine ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, ?_⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        refine ⟨?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
      | some e =>
        refine ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, ?_⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        have hM := mapErrno_kind_and_msg none "waitpid" e
        exact ⟨hM.2.1, hM.2.2.1, hM.2.2.2⟩
  · dsimp only [pure, StateT.pure, StateT.run]
    exact ⟨congrArg (fun t => t.slots.length) hGs1, hOs1, (by intro _ h; cases h)⟩

private theorem erase_two_fresh {fd : Type} [DecidableEq fd]
    {r w : fd} {base : List fd} (hNe : r ≠ w) :
    ((w :: r :: base).erase r).erase w = base := by
  simp [beq_false_of_ne (Ne.symm hNe)]

private theorem erase_four_fresh {fd : Type} [DecidableEq fd]
    {r1 w1 r2 w2 : fd} {base : List fd}
    (h1 : r1 ≠ w1) (h2 : r2 ≠ w2)
    (hr2 : r2 ∉ w1 :: r1 :: base) (hw2 : w2 ∉ w1 :: r1 :: base) :
    ((((w2 :: r2 :: w1 :: r1 :: base).erase r1).erase w1).erase r2).erase w2 = base := by
  simp only [List.mem_cons, not_or] at hr2 hw2
  simp [beq_false_of_ne (Ne.symm h1),
    beq_false_of_ne (Ne.symm h2),
    beq_false_of_ne hr2.1,
    beq_false_of_ne hr2.2.1,
    beq_false_of_ne hw2.1,
    beq_false_of_ne hw2.2.1]

private theorem erase_child_ends_six {fd : Type} [DecidableEq fd]
    {inR inW outR outW errR errW : fd} {base : List fd}
    (h1 : inR ≠ inW) (_h2 : outR ≠ outW) (_h3 : errR ≠ errW)
    (hr2 : outR ∉ inW :: inR :: base) (hw2 : outW ∉ inW :: inR :: base)
    (hr3 : errR ∉ outW :: outR :: inW :: inR :: base)
    (hw3 : errW ∉ outW :: outR :: inW :: inR :: base) :
    (((errW :: errR :: outW :: outR :: inW :: inR :: base).erase inR).erase outW).erase errW =
      errR :: outR :: inW :: base ∧
    errR ≠ outR ∧ errR ≠ inW ∧ outR ≠ inW := by
  simp only [List.mem_cons, not_or] at hr2 hw2 hr3 hw3
  refine ⟨?_, hr3.2.1, hr3.2.2.1, hr2.1⟩
  simp [beq_false_of_ne (Ne.symm h1),
    beq_false_of_ne hr2.2.1,
    beq_false_of_ne hw2.2.1,
    beq_false_of_ne hr3.1,
    beq_false_of_ne hr3.2.2.2.1,
    beq_false_of_ne hw3.1,
    beq_false_of_ne hw3.2.2.2.1]

private theorem erase_parent_ends_three {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} {base : List fd}
    (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW) :
    (((errR :: outR :: inW :: base).erase inW).erase outR).erase errR = base := by
  simp [beq_false_of_ne hEO, beq_false_of_ne hEI, beq_false_of_ne hOI]

/-- Core bridge theorem: for **every** `deps` satisfying `RefinesHealthySysDeps`, `SysBridge.mkRawOpsM deps (stateProcTableOps getTbl setTbl) eintrFuel ioFuel` satisfies `RawProcessLaws openFds` (including full OS descriptor conservation and process-slot conservation) across arbitrary short pipe `read`/`write`, `EAGAIN`, `EPIPE`, bounded `EINTR`, and everyday OS errors (`EMFILE`, `ENOENT`, `EACCES`). -/
theorem mkRawOpsM_satisfies_RawProcessLaws {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel ioFuel : Nat) :
    RawProcessLaws openFds
      (SysBridge.mkRawOpsM deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel ioFuel) := by
  let tbl := SysBridge.stateProcTableOps getTbl setTbl
  let proj := fun s : S => (getTbl s, openFds s)
  have hCloseT : ∀ s h, getTbl ((deps.files.close h).run s).2 = getTbl s :=
    fun s h => (hDeps.close_frame s h).1
  have hCloseO : ∀ s h, openFds ((deps.files.close h).run s).2 = (openFds s).erase h :=
    fun s h => (hDeps.close_frame s h).2.1
  have hCloseSome : ∀ (x : fd) (st : S),
      let r := (Files.closeOpt deps.files (some x)).run st
      getTbl r.2 = getTbl st ∧ openFds r.2 = (openFds st).erase x := by
    intro x st
    unfold Files.closeOpt
    rw [stateT_bind_eq]
    exact ⟨hCloseT st x, hCloseO st x⟩
  have hReadTO : ∀ s h c, getTbl ((deps.files.read h c).run s).2 = getTbl s ∧
      openFds ((deps.files.read h c).run s).2 = openFds s :=
    fun s h c => ⟨(hDeps.read_frame s h c).1, (hDeps.read_frame s h c).2.1⟩
  have hWriteTO : ∀ s h d, getTbl ((deps.files.write h d).run s).2 = getTbl s ∧
      openFds ((deps.files.write h d).run s).2 = openFds s :=
    fun s h d => ⟨(hDeps.write_frame s h d).1, (hDeps.write_frame s h d).2.1⟩
  have hStatP : ∀ s dir p fl, proj ((deps.files.fstatat dir p fl).run s).2 = proj s :=
    fun s dir p fl => Prod.ext (hDeps.fstatat_frame s dir p fl).1 (hDeps.fstatat_frame s dir p fl).2.1
  have hAccP : ∀ s dir p m fl, proj ((deps.files.faccessat dir p m fl).run s).2 = proj s :=
    fun s dir p m fl => Prod.ext (hDeps.faccessat_frame s dir p m fl).1 (hDeps.faccessat_frame s dir p m fl).2.1
  have hFcntlTO : ∀ s h cmd, getTbl ((deps.files.fcntl h cmd).run s).2 = getTbl s ∧
      openFds ((deps.files.fcntl h cmd).run s).2 = openFds s :=
    fun s h cmd => ⟨(hDeps.fcntl_frame s h cmd).1, (hDeps.fcntl_frame s h cmd).2.1⟩
  have hWaitTO : ∀ s pid fl, getTbl ((deps.proc.waitpid pid fl).run s).2 = getTbl s ∧
      openFds ((deps.proc.waitpid pid fl).run s).2 = openFds s :=
    fun s pid fl => ⟨(hDeps.waitpid_frame s pid fl).1, (hDeps.waitpid_frame s pid fl).2.1⟩
  have hWaitP : ∀ s pid fl, proj ((deps.proc.waitpid pid fl).run s).2 = proj s :=
    fun s pid fl => Prod.ext (hWaitTO s pid fl).1 (hWaitTO s pid fl).2
  have hKillP : ∀ s t sg, proj ((deps.proc.kill t sg).run s).2 = proj s :=
    fun s t sg => Prod.ext (hDeps.kill_frame s t sg).1 (hDeps.kill_frame s t sg).2.1
  have hCgTO : ∀ s clk, getTbl ((deps.timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((deps.timeRand.clock_gettime clk).run s).2 = openFds s :=
    fun s clk => ⟨(hDeps.clock_gettime_frame s clk).1, (hDeps.clock_gettime_frame s clk).2.1⟩
  have hCgP : ∀ s clk, proj ((deps.timeRand.clock_gettime clk).run s).2 = proj s :=
    fun s clk => Prod.ext (hCgTO s clk).1 (hCgTO s clk).2
  have hNsTO : ∀ s clk abs r, getTbl ((deps.timeRand.clock_nanosleep clk abs r).run s).2 = getTbl s ∧
      openFds ((deps.timeRand.clock_nanosleep clk abs r).run s).2 = openFds s :=
    fun s clk abs r => hDeps.clock_nanosleep_frame s clk abs r
  have hNsP : ∀ s clk abs r, proj ((deps.timeRand.clock_nanosleep clk abs r).run s).2 = proj s :=
    fun s clk abs r => Prod.ext (hNsTO s clk abs r).1 (hNsTO s clk abs r).2
  have hPipeRetry : ∀ s,
      let r := (LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s
      getTbl r.2 = getTbl s ∧
      (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
      (∀ rf wf, r.1 = .ok (rf, wf) →
        rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s) := by
    intro s
    exact retryEintr_pipe2_spec getTbl openFds (deps.proc.pipe2 { cloexec := true })
      (fun st =>
        let hp := hDeps.pipe2_frame st { cloexec := true }
        ⟨hp.1, fun e he => (hp.2.1 e he).1, hp.2.2⟩)
      eintrFuel s
  have hSpawnSpec : ∀ s₀ req,
      let sp := (SysBridge.spawnPure deps tbl eintrFuel req).run s₀
      (∀ err, sp.1 = .error err →
        getTbl sp.2 = getTbl s₀ ∧
        openFds sp.2 = openFds s₀ ∧
        err.message ≠ "" ∧
        err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) ∧
      (∀ h, sp.1 = .ok h →
        h.pid > 0 ∧ h.pgid > 0 ∧
        ∃ errR outR inW slot,
          errR ≠ outR ∧ errR ≠ inW ∧ outR ≠ inW ∧
          slot.stdinFd? = optFdOf inW true ∧
          slot.stdoutFd? = optFdOf outR true ∧
          slot.stderrFd? = optFdOf errR true ∧
          openFds sp.2 = pipePrefix errR outR inW true true true (openFds s₀) ∧
          getTbl sp.2 = { nextId := h.handleId + 1, slots := (h.handleId, slot) :: (getTbl s₀).slots }) := by
    intro s₀ req
    dsimp only
    unfold SysBridge.spawnPure
    by_cases hInv : SysBridge.isInvalidSpawnRequest req = true
    · rw [ite_eq_left hInv]
      dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨?_, (by intro _ h; cases h)⟩
      intro err hEq; injection hEq with hE; rw [← hE]
      refine ⟨rfl, rfl, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
    · rw [ite_eq_right hInv]
      rw [stateT_bind_eq]
      obtain ⟨hFcwdP, hEcwd⟩ := validateWorkingDir_spec proj deps.files hStatP hAccP req.cwd eintrFuel s₀
      let s0c := ((SysBridge.validateWorkingDir deps.files req.cwd eintrFuel).run s₀).2
      have hFs0c : getTbl s0c = getTbl s₀ := congrArg Prod.fst hFcwdP
      have hOs0c : openFds s0c = openFds s₀ := congrArg Prod.snd hFcwdP
      cases hCwdRes : ((SysBridge.validateWorkingDir deps.files req.cwd eintrFuel).run s₀).1 with
      | error cwdErr =>
        dsimp only [pure, StateT.pure, StateT.run]
        refine ⟨?_, (by intro _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        exact ⟨hFs0c, hOs0c, hEcwd cwdErr hCwdRes⟩
      | ok _ =>
        dsimp only
        have hEnvStep :
            ∃ baseRes s1,
              (SysBridge.readBaseEnv deps req.inheritEnv).run s0c = (baseRes, s1) ∧
              getTbl s1 = getTbl s₀ ∧
              openFds s1 = openFds s₀ ∧
              (∀ e, baseRes = .error e →
                e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal) := by
          unfold SysBridge.readBaseEnv
          cases req.inheritEnv
          · exact ⟨.ok #[], s0c, rfl, hFs0c, hOs0c, (by intro _ h; cases h)⟩
          · obtain ⟨hFeT, hFeO, hKe⟩ := hDeps.listAmbientEnv_frame s0c
            exact ⟨_, _, rfl, hFeT.trans hFs0c, hFeO.trans hOs0c, hKe⟩
        rcases hEnvStep with ⟨baseRes, s1, hRunEnv, hFs1, hOs1, hErrEnv⟩
        rw [stateT_bind_eq, hRunEnv]
        cases baseRes with
        | error envErr =>
          dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨?_, (by intro _ h; cases h)⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          obtain ⟨hk1, hk2, hk3⟩ := hErrEnv envErr rfl
          have hkEq : (SysBridge.ensureNonEmptyMsg "failed to read environment" envErr).kind = envErr.kind := by
            unfold SysBridge.ensureNonEmptyMsg; split <;> rfl
          refine ⟨hFs1, hOs1, ensureNonEmptyMsg_ne_empty _ _ (by decide), ?_, ?_, ?_⟩ <;> rw [hkEq]
          · exact hk1
          · exact hk2
          · exact hk3
        | ok baseEnv =>
          dsimp only
          rw [stateT_bind_eq]
          let envBytes := SysBridge.mergeRawEnvOverrides baseEnv req.env
          obtain ⟨hFresP, hEres⟩ := resolveExecutablePath_spec proj deps.files hStatP hAccP
            req.program req.cwd envBytes eintrFuel s1
          let s2 := ((SysBridge.resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel).run s1).2
          have hFs2 : getTbl s2 = getTbl s₀ := (congrArg Prod.fst hFresP).trans hFs1
          have hOs2 : openFds s2 = openFds s₀ := (congrArg Prod.snd hFresP).trans hOs1
          cases hResP : ((SysBridge.resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel).run s1).1 with
          | error resErr =>
            dsimp only [pure, StateT.pure, StateT.run]
            refine ⟨?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; rw [← hE]
            exact ⟨hFs2, hOs2, hEres resErr hResP⟩
          | ok resolvedPath =>
            dsimp only
            split
            · dsimp only [pure, StateT.pure, StateT.run]
              refine ⟨?_, (by intro _ h; cases h)⟩
              intro err hEq; injection hEq with hE; subst hE
              refine ⟨hFs2, hOs2, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
            · rw [stateT_bind_eq]
              obtain ⟨hTp1, hEp1, hOkp1⟩ := hPipeRetry s2
              let s3 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s2).2
              have hFs3 : getTbl s3 = getTbl s₀ := hTp1.trans hFs2
              cases hP1 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s2).1 with
              | error e1 =>
                dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨?_, (by intro _ h; cases h)⟩
                intro err hEq; injection hEq with hE; subst hE
                exact ⟨hFs3, (hEp1 e1 hP1).trans hOs2, mapErrno_kind_and_msg (some req.program) "pipe2" e1⟩
              | ok p1 =>
                rcases p1 with ⟨inR, inW⟩
                obtain ⟨hNe1, _, _, hOp1⟩ := hOkp1 inR inW hP1
                rw [hOs2] at hOp1
                dsimp only
                rw [stateT_bind_eq]
                obtain ⟨hTp2, hEp2, hOkp2⟩ := hPipeRetry s3
                let s4 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s3).2
                have hFs4 : getTbl s4 = getTbl s₀ := hTp2.trans hFs3
                cases hP2 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s3).1 with
                | error e2 =>
                  dsimp only
                  rw [stateT_bind_eq, stateT_bind_eq]
                  dsimp only [pure, StateT.pure, StateT.run]
                  have hOs4 : openFds s4 = inW :: inR :: openFds s₀ := (hEp2 e2 hP2).trans hOp1
                  obtain ⟨hTc1, hOc1⟩ := hCloseSome inR s4
                  obtain ⟨hTc2, hOc2⟩ := hCloseSome inW _
                  have hOEnd : openFds ((Files.closeOpt deps.files (some inW)).run
                      ((Files.closeOpt deps.files (some inR)).run s4).2).2 = openFds s₀ := by
                    rw [hOc2, hOc1, hOs4, erase_two_fresh hNe1]
                  refine ⟨?_, (by intro _ h; cases h)⟩
                  intro err hEq; injection hEq with hE; subst hE
                  exact ⟨hTc2.trans (hTc1.trans hFs4), hOEnd, mapErrno_kind_and_msg (some req.program) "pipe2" e2⟩
                | ok p2 =>
                  rcases p2 with ⟨outR, outW⟩
                  obtain ⟨hNe2, hNr2, hNw2, hOp2⟩ := hOkp2 outR outW hP2
                  rw [hOp1] at hNr2 hNw2 hOp2
                  dsimp only
                  rw [stateT_bind_eq]
                  obtain ⟨hTp3, hEp3, hOkp3⟩ := hPipeRetry s4
                  let s5 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s4).2
                  have hFs5 : getTbl s5 = getTbl s₀ := hTp3.trans hFs4
                  cases hP3 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s4).1 with
                  | error e3 =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    have hOs5 : openFds s5 = outW :: outR :: inW :: inR :: openFds s₀ := (hEp3 e3 hP3).trans hOp2
                    obtain ⟨hTc1, hOc1⟩ := hCloseSome inR s5
                    obtain ⟨hTc2, hOc2⟩ := hCloseSome inW _
                    obtain ⟨hTc3, hOc3⟩ := hCloseSome outR _
                    obtain ⟨hTc4, hOc4⟩ := hCloseSome outW _
                    have hOEnd : openFds ((Files.closeOpt deps.files (some outW)).run
                        ((Files.closeOpt deps.files (some outR)).run
                          ((Files.closeOpt deps.files (some inW)).run
                            ((Files.closeOpt deps.files (some inR)).run s5).2).2).2).2 = openFds s₀ := by
                      rw [hOc4, hOc3, hOc2, hOc1, hOs5, erase_four_fresh hNe1 hNe2 hNr2 hNw2]
                    refine ⟨?_, (by intro _ h; cases h)⟩
                    intro err hEq; injection hEq with hE; subst hE
                    exact ⟨hTc4.trans (hTc3.trans (hTc2.trans (hTc1.trans hFs5))),
                      hOEnd, mapErrno_kind_and_msg (some req.program) "pipe2" e3⟩
                  | ok p3 =>
                    rcases p3 with ⟨errR, errW⟩
                    obtain ⟨hNe3, hNr3, hNw3, hOp3⟩ := hOkp3 errR errW hP3
                    rw [hOp2] at hNr3 hNw3 hOp3
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                    let childSpec : PostFork.ChildSpecM fd :=
                      { path := resolvedPath
                        argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                        cwd := req.cwd
                        env := #[]
                        rawEnv := envBytes
                        stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                        fdPolicy := .inheritNonCloexec #[]
                        closeFds := #[.handle inW, .handle outR, .handle errR]
                        processGroup := .newGroup
                        sigpipe := .resetDefault
                        forkMode := .direct }
                    obtain ⟨hFpfT, hFpfO⟩ := hDeps.postFork_frame s5 childSpec
                    let spf := (deps.postFork.spawn childSpec).run s5
                    obtain ⟨hTcC1, hOcC1⟩ := hCloseSome inR spf.2
                    obtain ⟨hTcC2, hOcC2⟩ := hCloseSome outW _
                    obtain ⟨hTcC3, hOcC3⟩ := hCloseSome errW _
                    let s6 := ((Files.closeOpt deps.files (some errW)).run
                      ((Files.closeOpt deps.files (some outW)).run
                        ((Files.closeOpt deps.files (some inR)).run spf.2).2).2).2
                    have hFcChild : getTbl s6 = getTbl s₀ :=
                      hTcC3.trans (hTcC2.trans (hTcC1.trans (hFpfT.trans hFs5)))
                    obtain ⟨hChildErase, hEO, hEI, hOI⟩ :=
                      erase_child_ends_six hNe1 hNe2 hNe3 hNr2 hNw2 hNr3 hNw3
                    have hOcChild : openFds s6 = errR :: outR :: inW :: openFds s₀ := by
                      dsimp only [s6]
                      rw [hOcC3, hOcC2, hOcC1, hFpfO, hOp3, hChildErase]
                    cases hPfRes : spf.1 with
                    | error pfErr =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hTcP1, hOcP1⟩ := hCloseSome inW s6
                      obtain ⟨hTcP2, hOcP2⟩ := hCloseSome outR _
                      obtain ⟨hTcP3, hOcP3⟩ := hCloseSome errR _
                      have hOPar : openFds ((Files.closeOpt deps.files (some errR)).run
                          ((Files.closeOpt deps.files (some outR)).run
                            ((Files.closeOpt deps.files (some inW)).run s6).2).2).2 = openFds s₀ := by
                        rw [hOcP3, hOcP2, hOcP1, hOcChild, erase_parent_ends_three hEO hEI hOI]
                      refine ⟨?_, (by intro _ h; cases h)⟩
                      intro err hEq; injection hEq with hE; subst hE
                      exact ⟨hTcP3.trans (hTcP2.trans (hTcP1.trans hFcChild)),
                        hOPar, mapPostForkError_kind_and_msg req pfErr⟩
                    | ok child =>
                      dsimp only
                      let rawPgid := child.pgid.getD child.pid
                      by_cases hBadPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = true
                      · rw [ite_eq_left hBadPid]
                        rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                        dsimp only [pure, StateT.pure, StateT.run]
                        obtain ⟨hTcP1, hOcP1⟩ := hCloseSome inW s6
                        obtain ⟨hTcP2, hOcP2⟩ := hCloseSome outR _
                        obtain ⟨hTcP3, hOcP3⟩ := hCloseSome errR _
                        have hOPar : openFds ((Files.closeOpt deps.files (some errR)).run
                            ((Files.closeOpt deps.files (some outR)).run
                              ((Files.closeOpt deps.files (some inW)).run s6).2).2).2 = openFds s₀ := by
                          rw [hOcP3, hOcP2, hOcP1, hOcChild, erase_parent_ends_three hEO hEI hOI]
                        refine ⟨?_, (by intro _ h; cases h)⟩
                        intro err hEq; injection hEq with hE; rw [← hE]
                        refine ⟨hTcP3.trans (hTcP2.trans (hTcP1.trans hFcChild)),
                          hOPar, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
                      · rw [ite_eq_right hBadPid]
                        rw [stateT_bind_eq]
                        let newSlot : ProcSlotM fd :=
                          { pid := child.pid
                            pgid := rawPgid
                            stdinFd? := some inW
                            stdoutFd? := some outR
                            stderrFd? := some errR
                            waited := false }
                        have hIns : (tbl.insertSlot newSlot).run s6 =
                            ((getTbl s₀).nextId, setTbl s6 (SysBridge.insertSlotPure (getTbl s₀) newSlot).2) := by
                          dsimp only [tbl, SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
                            StateT.modifyGet, StateT.run]
                          rw [hFcChild]
                          rfl
                        rw [hIns]
                        dsimp only [pure, StateT.pure, StateT.run]
                        refine ⟨(by intro _ h; cases h), ?_⟩
                        intro hOut hEq
                        injection hEq with hSub
                        rw [← hSub]
                        dsimp only
                        have hPidNe0 : child.pid ≠ 0 := fun hz => hBadPid (by simp [hz])
                        have hPgidNe0 : rawPgid ≠ 0 := fun hz => hBadPid (by simp [hz])
                        have hPidPos : 0 < child.pid.toNat :=
                          Nat.pos_of_ne_zero fun hz =>
                            hPidNe0 (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
                        have hPgidPos : 0 < rawPgid.toNat :=
                          Nat.pos_of_ne_zero fun hz =>
                            hPgidNe0 (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
                        refine ⟨Int.ofNat_lt.mpr hPidPos, Int.ofNat_lt.mpr hPgidPos,
                          errR, outR, inW, newSlot, hEO, hEI, hOI, rfl, rfl, rfl, ?_, ?_⟩
                        · rw [hDeps.openFds_set, hOcChild]; rfl
                        · rw [hDeps.get_set]; rfl
  refine
    { mapRawError_eq := rfl
      activeCount_pure := fun _ => rfl
      spawn_err := ?_
      spawn_lifecycle := ?_ }
  · intro s req err hEq
    have hSp := (hSpawnSpec s req).1 err (congrArg Prod.fst hEq)
    exact ⟨congrArg (fun t => t.slots.length) hSp.1, hSp.2.1, hSp.2.2⟩
  · intro s₀ req h s₁ hSpawnOk
    have hSpOk := (hSpawnSpec s₀ req).2 h (congrArg Prod.fst hSpawnOk)
    have hs₁Eq : ((SysBridge.spawnPure deps tbl eintrFuel req).run s₀).2 = s₁ := congrArg Prod.snd hSpawnOk
    rw [hs₁Eq] at hSpOk
    obtain ⟨hPidPos, hPgidPos, errR, outR, inW, slot, hEO, hEI, hOI,
      hSlotIn, hSlotOut, hSlotErr, hOpen₁, hTbl₁⟩ := hSpOk
    refine ⟨hPidPos, hPgidPos, ?_⟩
    have hKillAndReapNone : ∀ (stAw : S) (sl : ProcSlotM fd) (rest : List (Nat × ProcSlotM fd)) (nid : Nat),
        getTbl stAw = { nextId := nid, slots := (h.handleId, sl) :: rest } →
        openFds stAw = openFds s₀ →
        (sl.stdinFd? = none ∧ sl.stdoutFd? = none ∧ sl.stderrFd? = none) →
        rest.length = (getTbl s₀).slots.length →
        let kl := (SysBridge.killProcessGroupPure deps tbl eintrFuel h).run stAw
        let rp := (SysBridge.reapPure deps tbl eintrFuel h).run kl.2
        (getTbl rp.2).slots.length = (getTbl s₀).slots.length ∧
        openFds rp.2 = openFds s₀ ∧
        (∀ rerr, rp.1 = .error rerr →
          rerr.kind ≠ .timedOut ∧ rerr.kind ≠ .outputLimitExceeded ∧ rerr.kind ≠ .terminatedBySignal) := by
      intro stAw sl rest nid hTblAw hOpenAw hFdsNone hRestLen
      have hFkP := killProcessGroupPure_frame proj getTbl setTbl deps hKillP hNsP eintrFuel h stAw
      let kl := (SysBridge.killProcessGroupPure deps tbl eintrFuel h).run stAw
      have hTblKl : getTbl kl.2 = { nextId := nid, slots := (h.handleId, sl) :: rest } :=
        (congrArg Prod.fst hFkP).trans hTblAw
      have hOpenKl : openFds kl.2 = openFds s₀ :=
        (congrArg Prod.snd hFkP).trans hOpenAw
      obtain ⟨hLenRp, hOpenRp, hErrRp⟩ := reapPure_head_slot_none_spec getTbl setTbl openFds
        hDeps.get_set hDeps.openFds_set deps hWaitTO eintrFuel h sl rest nid kl.2 hTblKl hFdsNone
      exact ⟨hLenRp.trans hRestLen, hOpenRp.trans hOpenKl, hErrRp⟩
    let restTaken := (getTbl s₀).slots.map fun (k, s) =>
      if k == h.handleId then (k, { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none }) else (k, s)
    have hRestTakenLen : restTaken.length = (getTbl s₀).slots.length := List.length_map _
    let slotTaken : ProcSlotM fd := { slot with stdinFd? := none, stdoutFd? := none, stderrFd? := none }
    have hSlotTakenNone : slotTaken.stdinFd? = none ∧ slotTaken.stdoutFd? = none ∧ slotTaken.stderrFd? = none :=
      ⟨rfl, rfl, rfl⟩
    have hTake : (tbl.takeSlotIo h.handleId).run s₁ =
        (some (slot.pid, slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?),
         setTbl s₁ { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken }) := by
      dsimp only [tbl, SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
      rw [hTbl₁]
      simp only [SysBridge.takeSlotIoPure, SysBridge.findSlotPure, beq_self_eq_true, ↓reduceIte,
        List.map_cons, slotTaken, restTaken]
      rfl
    dsimp only [SysBridge.mkRawOpsM]
    unfold SysBridge.awaitOutputPure
    rw [stateT_bind_eq, hTake]
    dsimp only
    let s₂ := setTbl s₁ { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken }
    have hTbl₂ : getTbl s₂ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
      hDeps.get_set s₁ _
    have hOpen₂ : openFds s₂ = pipePrefix errR outR inW true true true (openFds s₀) :=
      (hDeps.openFds_set s₁ _).trans hOpen₁
    have hSetupIn :
        ∃ bIn₀ inFd? s₃,
          (SysBridge.setupStdinPipe deps.files req.stdin slot.stdinFd?).run s₂ = (inFd?, s₃) ∧
          getTbl s₃ = getTbl s₂ ∧
          inFd? = optFdOf inW bIn₀ ∧
          openFds s₃ = pipePrefix errR outR inW true true bIn₀ (openFds s₀) := by
      unfold SysBridge.setupStdinPipe
      rw [hSlotIn]
      split
      · obtain ⟨hTi, hOi⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT inW
          (fun b => pipePrefix errR outR inW true true b (openFds s₀))
          (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) true s₂ hOpen₂
        refine ⟨false, none, ((Files.closeOpt deps.files (optFdOf inW true)).run s₂).2,
          ?_, hTi, rfl, hOi⟩
        rw [stateT_bind_eq]; rfl
      · dsimp only [optFdOf]
        refine ⟨true, some inW, ((deps.files.fcntl inW (.setFl true false)).run s₂).2,
          ?_, (hFcntlTO s₂ inW _).1, rfl, (hFcntlTO s₂ inW _).2.trans hOpen₂⟩
        rw [stateT_bind_eq]; rfl
    rcases hSetupIn with ⟨bIn₀, inFd?, s₃, hRunInSet, hFs₃, hInOpt, hOpen₃⟩
    rw [stateT_bind_eq, hRunInSet]
    dsimp only
    have hSetupOut :
        ∃ s₄,
          (Files.setNonblockingOpt deps.files slot.stdoutFd?).run s₃ = ((), s₄) ∧
          getTbl s₄ = getTbl s₂ ∧
          openFds s₄ = pipePrefix errR outR inW true true bIn₀ (openFds s₀) := by
      unfold Files.setNonblockingOpt
      rw [hSlotOut]
      dsimp only [optFdOf]
      refine ⟨((deps.files.fcntl outR (.setFl true false)).run s₃).2,
        ?_, (hFcntlTO s₃ outR _).1.trans hFs₃, (hFcntlTO s₃ outR _).2.trans hOpen₃⟩
      rw [stateT_bind_eq]; rfl
    rcases hSetupOut with ⟨s₄, hRunOutSet, hFs₄, hOpen₄⟩
    rw [stateT_bind_eq, hRunOutSet]
    dsimp only
    have hSetupErr :
        ∃ s₅,
          (Files.setNonblockingOpt deps.files slot.stderrFd?).run s₄ = ((), s₅) ∧
          getTbl s₅ = getTbl s₂ ∧
          openFds s₅ = pipePrefix errR outR inW true true bIn₀ (openFds s₀) := by
      unfold Files.setNonblockingOpt
      rw [hSlotErr]
      dsimp only [optFdOf]
      refine ⟨((deps.files.fcntl errR (.setFl true false)).run s₄).2,
        ?_, (hFcntlTO s₄ errR _).1.trans hFs₄, (hFcntlTO s₄ errR _).2.trans hOpen₄⟩
      rw [stateT_bind_eq]; rfl
    rcases hSetupErr with ⟨s₅, hRunErrSet, hFs₅, hOpen₅⟩
    rw [stateT_bind_eq, hRunErrSet]
    dsimp only
    have hStartStep :
        ∃ startRes s₆,
          (SysBridge.readStartMsOpt deps.timeRand req.timeoutMs).run s₅ = (startRes, s₆) ∧
          getTbl s₆ = getTbl s₂ ∧
          openFds s₆ = pipePrefix errR outR inW true true bIn₀ (openFds s₀) ∧
          (∀ err, startRes = .error err →
            err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
      unfold SysBridge.readStartMsOpt
      cases req.timeoutMs with
      | none => exact ⟨.ok 0, s₅, rfl, hFs₅, hOpen₅, (by intro _ h; cases h)⟩
      | some _ =>
        have hFmP := monoNowMs_spec proj deps.timeRand hCgP s₅
        rcases hM : (TimeRand.monoNowMs deps.timeRand).run s₅ with ⟨mRes, sM⟩
        rw [hM] at hFmP
        cases mRes with
        | ok ms =>
          exact ⟨.ok ms, sM, by rw [stateT_bind_eq, hM]; rfl,
            (congrArg Prod.fst hFmP).trans hFs₅,
            (congrArg Prod.snd hFmP).trans hOpen₅, (by intro _ h; cases h)⟩
        | error e =>
          exact ⟨.error (SysBridge.mapErrno none "clock_gettime" e), sM,
            by rw [stateT_bind_eq, hM]; rfl,
            (congrArg Prod.fst hFmP).trans hFs₅,
            (congrArg Prod.snd hFmP).trans hOpen₅,
            fun err he => by
              injection he with hE; rw [← hE]
              exact (mapErrno_kind_and_msg none "clock_gettime" e).2⟩
    rcases hStartStep with ⟨startRes, s₆, hRunStart, hFs₆, hOpen₆, hErrStart⟩
    rw [stateT_bind_eq, hRunStart]
    dsimp only
    cases startRes with
    | error e =>
      dsimp only
      rw [hInOpt, hSlotOut, hSlotErr, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hTc1, hOc1⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT inW
        (fun b => pipePrefix errR outR inW true true b (openFds s₀))
        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn₀ s₆ hOpen₆
      obtain ⟨hTc2, hOc2⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT outR
        (fun b => pipePrefix errR outR inW true b false (openFds s₀))
        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) true _ hOc1
      obtain ⟨hTc3, hOc3⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT errR
        (fun b => pipePrefix errR outR inW b false false (openFds s₀))
        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) true _ hOc2
      let sEndErr := ((Files.closeOpt deps.files (optFdOf errR true)).run
        ((Files.closeOpt deps.files (optFdOf outR true)).run
          ((Files.closeOpt deps.files (optFdOf inW bIn₀)).run s₆).2).2).2
      have hTblEnd : getTbl sEndErr = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
        hTc3.trans (hTc2.trans (hTc1.trans (hFs₆.trans hTbl₂)))
      obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone sEndErr slotTaken restTaken (h.handleId + 1)
        hTblEnd hOc3 hSlotTakenNone hRestTakenLen
      refine ⟨?_, (by intro _ h; cases h), (by intro _ _ _ h; cases h),
        (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
      intro err hEq; injection hEq with hE; rw [← hE]
      obtain ⟨hk1, hk2, hk3⟩ := hErrStart e rfl
      exact ⟨hk1, hk2, hk3, hLenEnd, hOpenEnd⟩
    | ok startMs =>
      dsimp only
      rw [stateT_bind_eq]
      let initSt : StreamLoopState fd :=
        { inFd? := inFd?, outFd? := slot.stdoutFd?, errFd? := slot.stderrFd? }
      have hPollTO : ∀ s entries to, getTbl ((deps.poll.ppoll entries to).run s).2 = getTbl s ∧
          openFds ((deps.poll.ppoll entries to).run s).2 = openFds s :=
        fun s entries to => ⟨(hDeps.ppoll_frame s entries to).1, (hDeps.ppoll_frame s entries to).2.1⟩
      obtain ⟨hFst, hOst, hEofSt, hToSt, hLimSt, hErrSt⟩ := streamPipesLoop_spec getTbl openFds
        deps.files deps.poll deps.timeRand hCloseT hCloseO hReadTO hWriteTO hPollTO hCgTO
        hEO hEI hOI (openFds s₀) req.stdin startMs req.timeoutMs req.maxOutputBytes eintrFuel
        true true bIn₀ initSt ioFuel s₆ hInOpt hSlotOut hSlotErr hOpen₆ rfl rfl (fun _ _ => Nat.zero_le _)
      have hMarkHelper : ∀ (stM : S) (waitedFlag : Bool),
          getTbl stM = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } →
          ∃ slM restM,
            (tbl.markWaited h.handleId waitedFlag).run stM =
              (true, setTbl stM { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }) ∧
            (slM.stdinFd? = none ∧ slM.stdoutFd? = none ∧ slM.stderrFd? = none) ∧
            restM.length = (getTbl s₀).slots.length := by
        intro stM waitedFlag hTblM
        refine ⟨{ slotTaken with waited := slotTaken.waited || waitedFlag },
          restTaken.map (fun (k, s) => if k == h.handleId then (k, { s with waited := s.waited || waitedFlag }) else (k, s)),
          ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · dsimp only [tbl, SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
          rw [hTblM]
          simp only [SysBridge.markWaitedPure, SysBridge.findSlotPure, beq_self_eq_true,
            ↓reduceIte, List.map_cons]
          rfl
        · rw [List.length_map, hRestTakenLen]
      cases hLoop : (SysBridge.streamPipesLoop deps.files deps.poll deps.timeRand req.stdin startMs
          req.timeoutMs req.maxOutputBytes eintrFuel initSt ioFuel).run s₆ with
      | mk loopRes s₇ =>
        rw [hLoop] at hFst hOst hEofSt hToSt hLimSt hErrSt
        have hTbl₇ : getTbl s₇ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
          hFst.trans (hFs₆.trans hTbl₂)
        cases loopRes with
        | error e =>
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₇ slotTaken restTaken (h.handleId + 1)
            hTbl₇ hOst hSlotTakenNone hRestTakenLen
          refine ⟨?_, (by intro _ h; cases h), (by intro _ _ _ h; cases h),
            (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          obtain ⟨_, hk1, hk2, hk3⟩ := hErrSt e rfl
          exact ⟨hk1, hk2, hk3, hLenEnd, hOpenEnd⟩
        | ok phase =>
          cases phase with
          | timedOut out errB =>
            dsimp only
            obtain ⟨slM, restM, hMkRun, hSlMNone, hRestMLen⟩ := hMarkHelper s₇ false hTbl₇
            rw [stateT_bind_eq, hMkRun]
            dsimp only
            rw [ite_eq_right (by decide)]
            dsimp only [pure, StateT.pure, StateT.run]
            let s₈ := setTbl s₇ { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }
            obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₈ slM restM (h.handleId + 1)
              (hDeps.get_set s₇ _) ((hDeps.openFds_set s₇ _).trans hOst) hSlMNone hRestMLen
            refine ⟨(by intro _ h; cases h), (by intro _ h; cases h), (by intro _ _ _ h; cases h), ?_,
              (by intro _ _ h; cases h)⟩
            intro _ _ _
            exact ⟨hToSt out errB rfl, hLenEnd, hOpenEnd⟩
          | limitExceeded out errB =>
            dsimp only
            obtain ⟨slM, restM, hMkRun, hSlMNone, hRestMLen⟩ := hMarkHelper s₇ false hTbl₇
            rw [stateT_bind_eq, hMkRun]
            dsimp only
            rw [ite_eq_right (by decide)]
            dsimp only [pure, StateT.pure, StateT.run]
            let s₈ := setTbl s₇ { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }
            obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₈ slM restM (h.handleId + 1)
              (hDeps.get_set s₇ _) ((hDeps.openFds_set s₇ _).trans hOst) hSlMNone hRestMLen
            obtain ⟨hMaxSome, hMaxLe⟩ := hLimSt out errB rfl
            refine ⟨(by intro _ h; cases h), (by intro _ h; cases h), (by intro _ _ _ h; cases h),
              (by intro _ _ h; cases h), ?_⟩
            intro o e hEq; injection hEq with hSub; injection hSub with hO hE; rw [← hO, ← hE]
            exact ⟨hMaxSome, hMaxLe, hLenEnd, hOpenEnd⟩
          | eof out errB =>
            dsimp only
            have hCapEof := hEofSt out errB rfl
            cases hToOpt : req.timeoutMs with
            | none =>
              dsimp only
              rw [stateT_bind_eq]
              obtain ⟨hFwP, hExW, hNoToW, hNoLimW, hErrW⟩ := waitBlockingLoop_spec proj deps.proc
                hWaitP slot.pid.toInt32 out errB eintrFuel s₇
              cases hWRes : (SysBridge.waitBlockingLoop deps.proc slot.pid.toInt32 out errB eintrFuel).run s₇ with
              | mk wRes s₈ =>
                rw [hWRes] at hFwP hExW hNoToW hNoLimW hErrW
                have hTbl₈ : getTbl s₈ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
                  (congrArg Prod.fst hFwP).trans hTbl₇
                have hOpen₈ : openFds s₈ = openFds s₀ :=
                  (congrArg Prod.snd hFwP).trans hOst
                cases wRes with
                | error e =>
                  dsimp only [pure, StateT.pure, StateT.run]
                  obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₈ slotTaken restTaken (h.handleId + 1)
                    hTbl₈ hOpen₈ hSlotTakenNone hRestTakenLen
                  refine ⟨?_, (by intro _ h; cases h), (by intro _ _ _ h; cases h),
                    (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
                  intro err hEq; injection hEq with hE; rw [← hE]
                  obtain ⟨_, hk1, hk2, hk3⟩ := hErrW e rfl
                  exact ⟨hk1, hk2, hk3, hLenEnd, hOpenEnd⟩
                | ok outcome =>
                  dsimp only
                  obtain ⟨slM, restM, hMkRun, hSlMNone, hRestMLen⟩ := hMarkHelper s₈ true hTbl₈
                  rw [stateT_bind_eq, hMkRun]
                  dsimp only
                  rw [ite_eq_right (by decide)]
                  dsimp only [pure, StateT.pure, StateT.run]
                  let s₉ := setTbl s₈ { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }
                  have hTbl₉ : getTbl s₉ = { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM } :=
                    hDeps.get_set s₈ _
                  have hOpen₉ : openFds s₉ = openFds s₀ :=
                    (hDeps.openFds_set s₈ _).trans hOpen₈
                  obtain ⟨hLenKillReap, hOpenKillReap, _⟩ := hKillAndReapNone s₉ slM restM (h.handleId + 1)
                    hTbl₉ hOpen₉ hSlMNone hRestMLen
                  obtain ⟨hLenDirectReap, hOpenDirectReap, hErrDirectReap⟩ := reapPure_head_slot_none_spec
                    getTbl setTbl openFds hDeps.get_set hDeps.openFds_set deps hWaitTO
                    eintrFuel h slM restM (h.handleId + 1) s₉ hTbl₉ hSlMNone
                  refine ⟨(by intro _ h; cases h), ?_, ?_, ?_, ?_⟩
                  · intro res hEq
                    injection hEq with hOutEq
                    obtain ⟨hOutB, hErrB⟩ := hExW res (congrArg Except.ok hOutEq)
                    rw [hOutB, hErrB]
                    exact ⟨hCapEof, hLenDirectReap.trans hRestMLen, hOpenDirectReap.trans hOpen₉, hErrDirectReap⟩
                  · intro _ _ _ _
                    exact ⟨hLenKillReap, hOpenKillReap⟩
                  · intro o e hEq
                    injection hEq with hOutEq
                    exact absurd (congrArg Except.ok hOutEq) (hNoToW o e)
                  · intro o e hEq
                    injection hEq with hOutEq
                    exact absurd (congrArg Except.ok hOutEq) (hNoLimW o e)
            | some timeoutMs =>
              dsimp only
              rw [stateT_bind_eq]
              obtain ⟨hFwP, hExW, hNoLimW, hErrW⟩ := waitTimedLoop_spec proj deps.proc deps.timeRand
                hWaitP hCgP hNsP slot.pid.toInt32 startMs timeoutMs out errB ioFuel s₇
              cases hWRes : (SysBridge.waitTimedLoop deps.proc deps.timeRand slot.pid.toInt32
                  startMs timeoutMs out errB ioFuel).run s₇ with
              | mk wRes s₈ =>
                rw [hWRes] at hFwP hExW hNoLimW hErrW
                have hTbl₈ : getTbl s₈ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
                  (congrArg Prod.fst hFwP).trans hTbl₇
                have hOpen₈ : openFds s₈ = openFds s₀ :=
                  (congrArg Prod.snd hFwP).trans hOst
                cases wRes with
                | error e =>
                  dsimp only [pure, StateT.pure, StateT.run]
                  obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₈ slotTaken restTaken (h.handleId + 1)
                    hTbl₈ hOpen₈ hSlotTakenNone hRestTakenLen
                  refine ⟨?_, (by intro _ h; cases h), (by intro _ _ _ h; cases h),
                    (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
                  intro err hEq; injection hEq with hE; rw [← hE]
                  obtain ⟨_, hk1, hk2, hk3⟩ := hErrW e rfl
                  exact ⟨hk1, hk2, hk3, hLenEnd, hOpenEnd⟩
                | ok wpair =>
                  rcases wpair with ⟨waitedFlag, outcome⟩
                  dsimp only
                  obtain ⟨slM, restM, hMkRun, hSlMNone, hRestMLen⟩ := hMarkHelper s₈ waitedFlag hTbl₈
                  rw [stateT_bind_eq, hMkRun]
                  dsimp only
                  rw [ite_eq_right (by decide)]
                  dsimp only [pure, StateT.pure, StateT.run]
                  let s₉ := setTbl s₈ { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }
                  have hTbl₉ : getTbl s₉ = { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM } :=
                    hDeps.get_set s₈ _
                  have hOpen₉ : openFds s₉ = openFds s₀ :=
                    (hDeps.openFds_set s₈ _).trans hOpen₈
                  obtain ⟨hLenKillReap, hOpenKillReap, _⟩ := hKillAndReapNone s₉ slM restM (h.handleId + 1)
                    hTbl₉ hOpen₉ hSlMNone hRestMLen
                  obtain ⟨hLenDirectReap, hOpenDirectReap, hErrDirectReap⟩ := reapPure_head_slot_none_spec
                    getTbl setTbl openFds hDeps.get_set hDeps.openFds_set deps hWaitTO
                    eintrFuel h slM restM (h.handleId + 1) s₉ hTbl₉ hSlMNone
                  refine ⟨(by intro _ h; cases h), ?_, ?_, ?_, ?_⟩
                  · intro res hEq
                    injection hEq with hOutEq
                    obtain ⟨hOutB, hErrB⟩ := hExW waitedFlag res (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq)
                    rw [hOutB, hErrB]
                    exact ⟨hCapEof, hLenDirectReap.trans hRestMLen, hOpenDirectReap.trans hOpen₉, hErrDirectReap⟩
                  · intro _ _ _ _
                    exact ⟨hLenKillReap, hOpenKillReap⟩
                  · intro _ _ _
                    exact ⟨rfl, hLenKillReap, hOpenKillReap⟩
                  · intro o e hEq
                    injection hEq with hOutEq
                    exact absurd (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq) (hNoLimW waitedFlag o e)

end LeanSwe.Process.Proofs
