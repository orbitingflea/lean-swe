import Core.ConcOps
import LeanSwe.ProcessSandbox.Raw.Model.FullStep
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model

/-- Concrete cell state specialization `HostCellState Id Id` for the pure non-vacuity witness. -/
abbrev WitnessCell := HostCellState Id Id

/-- Pure witness world pairing `TimeRand` monotonic/entropy counters, `WitnessCell`, and a scheduler step counter. -/
structure WitnessWorld where
  /-- Monotonic clock lower bound in nanoseconds (`<= MAX_TIMESPEC_NANOS`). -/
  monoNs : Nat := 0
  /-- Number of completed `getrandom` draws. -/
  entropyDraws : Nat := 0
  /-- Host handle-table cell state. -/
  cell : WitnessCell := {}
  /-- Monotonic step counter driving `sched : Nat → Bool` in `witnessConc`. -/
  step : Nat := 0
  deriving Inhabited

/-- Healthy `TimeRand` environment corresponding to `(mono, draws)`. -/
def witnessTimeEnv (mono draws : Nat) : TimeRand.HealthyEnv :=
  { state :=
      { monoLowerBoundNs := min mono TimeRand.MAX_TIMESPEC_NANOS
        realtimeNs := 0
        crngReady := true
        entropyDraws := draws
        ambientSeccomp := false }
    eintrBudget := 0 }

/-- Project `WitnessWorld` onto `HealthyRawSysWorld`. -/
def witnessProjRaw (w : WitnessWorld) : HealthyRawSysWorld :=
  { HealthyRawSysWorld.initial with timeEnv := witnessTimeEnv w.monoNs w.entropyDraws }

/-- Project `WitnessWorld` onto `WitnessCell`. -/
def witnessProjCell (w : WitnessWorld) : WitnessCell :=
  w.cell

/-- Constant handle ID `100` mapped from any `RawFd` in the empty-table witness world. -/
def dummyHid : RawFd → Nat := fun _ => 100

/-- Every `WitnessWorld` state projects to a well-formed `HealthyRawSysWorld`. -/
theorem witnessProjRaw_wf (w : WitnessWorld) :
    fullWorldWf (witnessProjRaw w) = true := by
  have hInit : HealthyRawSysWorld.initial.wf = true := by decide
  unfold fullWorldWf HealthyRawSysWorld.wf witnessProjRaw witnessTimeEnv TimeRand.HealthyEnv.wf
  unfold HealthyRawSysWorld.wf at hInit
  simp only [Bool.and_eq_true] at hInit ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hInit.1.1.1.1.1.1.1.1, hInit.1.1.1.1.1.1.1.2⟩,
    hInit.1.1.1.1.1.1.2⟩, hInit.1.1.1.1.1.2⟩, hInit.1.1.1.1.2⟩, rfl⟩,
    hInit.1.1.2⟩, hInit.1.2⟩, hInit.2⟩

/-- Schedule-driven pure `Core.ConcOpsM (StateM WitnessWorld)` witness. -/
def witnessConc (sched : Nat → Bool) : Core.ConcOpsM (StateM WitnessWorld) where
  Ref := Id
  TaskHandle := Id
  mkRef x w := (x, { w with step := w.step + 1 })
  readRef r w := (r, { w with step := w.step + 1 })
  writeRef _ _ w := ((), { w with step := w.step + 1 })
  modifyGetRef r f w := ((f r).1, { w with step := w.step + 1 })
  spawnTask act w := act.run { w with step := w.step + 1 }
  hasFinished _ w := (sched w.step, { w with step := w.step + 1 })
  pollTask t w :=
    if sched w.step then (some (.ok t), { w with step := w.step + 1 })
    else (none, { w with step := w.step + 1 })
  waitTask t w := (.ok t, { w with step := w.step + 1 })
  tryCatchMsg act w :=
    let (a, w') := act.run w
    (.ok a, w')

/-- Pure `Core.StateCellM (StateM WitnessWorld) WitnessCell` lens witness. -/
def witnessCell : Core.StateCellM (StateM WitnessWorld) WitnessCell where
  get w := (w.cell, w)
  modifyGet f w :=
    let (a, c') := f w.cell
    (a, { w with cell := c' })

/-- `witnessConc sched` satisfies `Core.ObeysConcFrame` for every `sched : Nat → Bool`. -/
theorem witnessConc_obeys (sched : Nat → Bool) :
    Core.ObeysConcFrame (fun w => fullWorldWf (witnessProjRaw w) = true)
      (fun w₁ w₂ => witnessProjCell w₂ = witnessProjCell w₁)
      (witnessConc sched) := by
  refine ⟨fun {_α} t P => P t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ x w _; exact ⟨witnessProjRaw_wf _, rfl⟩
  · intro _ r w _; exact ⟨witnessProjRaw_wf _, rfl⟩
  · intro _ r v w _; exact ⟨witnessProjRaw_wf _, rfl⟩
  · intro _ _ r f w _; exact ⟨witnessProjRaw_wf _, rfl, r, rfl⟩
  · intro _ act P hAct w _
    have h1 := hAct { w with step := w.step + 1 } (witnessProjRaw_wf _)
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  · intro _ t w _; exact ⟨witnessProjRaw_wf _, rfl⟩
  · intro _ t w _
    dsimp only [witnessConc, StateT.run, Id.run]
    cases sched w.step <;> exact ⟨witnessProjRaw_wf _, rfl, trivial⟩
  · intro _ t w _; exact ⟨witnessProjRaw_wf _, rfl, trivial⟩
  · intro _ t P hP w _
    dsimp only [witnessConc, StateT.run, Id.run]
    cases sched w.step
    · exact ⟨witnessProjRaw_wf _, rfl, trivial⟩
    · exact ⟨witnessProjRaw_wf _, rfl, hP⟩
  · intro _ t P hP w _; exact ⟨witnessProjRaw_wf _, rfl, hP⟩
  · intro _ act QOk QErr _ hOk w hw
    have h1 := hOk w hw
    exact ⟨h1.1, h1.2.1⟩

/-- `witnessCell` satisfies `Core.ObeysStateCell witnessProjRaw witnessProjCell`. -/
theorem witnessCell_obeys :
    Core.ObeysStateCell witnessProjRaw witnessProjCell witnessCell :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

/-- Fallback `Errno` accepted by `Files.healthyStep` on `Files.HealthyEnv.initial`. -/
def sampleFilesErrno (req : Files.FilesReq) : Errno :=
  match Files.evalReq Files.FilesState.initial req with
  | .wrapperErr want =>
    if Errno.isCriticalOsErrno want || want == Errno.EINTR then Errno.EINVAL else want
  | .err primary _ _ =>
    if primary == Errno.ENOSPC then Errno.EMFILE else Errno.ENOSPC
  | .ok wantOut _ _ =>
    match wantOut with
    | .err p => if p == Errno.ENOSPC then Errno.EMFILE else Errno.ENOSPC
    | _ => Errno.ENOSPC
  | .nondet _ _ => Errno.ENOSPC

private theorem verifyNondet_spc (s : Files.FilesState) (act : Files.NondetAction) :
    match Files.verifyNondet s act (.err Errno.ENOSPC) with
    | none => True
    | some s' => s' = s := by
  have hFalse : (Errno.ENOSPC == Errno.ENXIO) = false ∧ (Errno.ENOSPC == Errno.EAGAIN) = false ∧
      (Errno.ENOSPC == Errno.EINVAL) = false ∧ (Errno.ENOSPC == Errno.ENODEV) = false ∧
      (Errno.ENOSPC == Errno.EROFS) = false ∧ (Errno.ENOSPC == Errno.EFBIG) = false ∧
      (Errno.ENOSPC == Errno.EPERM) = false ∧ (Errno.ENOSPC == Errno.EPIPE) = false ∧
      (Errno.ENOSPC == Errno.EINTR) = false ∧ (Errno.ENOSPC == Errno.ERANGE) = false ∧
      (Errno.ENOSPC == Errno.ENAMETOOLONG) = false ∧ (Errno.ENOSPC != Errno.EFAULT) = true := by decide
  rcases hFalse with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩
  cases act <;> dsimp only [Files.verifyNondet]
  all_goals
    try simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, ite_self]
  all_goals
    first
      | trivial
      | rfl
      | (rename_i _ extraErrs _; cases extraErrs.contains Errno.ENOSPC <;> first | trivial | rfl)

private def wrapperErrSafe : Files.StepResult → Bool
  | .wrapperErr e => e == Errno.EINVAL || e == Errno.EBADF
  | _ => true

private theorem wes_einval : wrapperErrSafe (.wrapperErr Errno.EINVAL) = true := by decide

private theorem wes_ebadf : wrapperErrSafe (.wrapperErr Errno.EBADF) = true := by decide

private theorem wes_ite {c : Prop} [Decidable c] {a b : Files.StepResult}
    (ha : wrapperErrSafe a = true) (hb : wrapperErrSafe b = true) :
    wrapperErrSafe (if c then a else b) = true := by
  by_cases c <;> simp_all

private theorem wes_openat2 {b : Bool} {res : Files.ResolveFlags} {td : Bool} {r : Files.StepResult}
    (hr : wrapperErrSafe r = true) :
    wrapperErrSafe (Files.withOpenat2Eagain b res td r) = true := by
  cases r <;> exact hr

private theorem evalOpen_safe (s : Files.FilesState) (dir : Option Files.HandleId)
    (path : ByteArray) (fl : Files.OpenFlags) (md : Mode) (res : Files.ResolveFlags) (so : Bool) :
    wrapperErrSafe (Files.evalOpen s dir path fl md res so) = true := by
  unfold Files.evalOpen
  by_cases hFp : (!so && fl.path) = true
  · simp only [hFp, ↓reduceIte]
    repeat (first | rfl | apply wes_ite)
    generalize Files.resolveOpenTargetWalk s dir path _ _ _ _ = wt
    rcases wt with ⟨walkRes, td⟩
    apply wes_openat2; dsimp only
    cases walkRes with
    | error _ => rfl
    | ok wl =>
      cases wl with
      | externalOpaque _ => rfl
      | existing targetIno _ _ _ _ _ _ =>
        dsimp only; repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes targetIno with
        | none => rfl
        | some vn =>
          dsimp only
          cases vn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
      | missingInParent _ _ _ =>
        repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
  · have hFpF : (!so && fl.path) = false := Bool.eq_false_iff.mpr hFp
    simp only [hFpF, Bool.false_eq_true, ↓reduceIte]
    repeat (first | rfl | apply wes_ite)
    generalize Files.resolveOpenTargetWalk s dir path _ _ _ _ = wt
    rcases wt with ⟨walkRes, td⟩
    apply wes_openat2; dsimp only
    cases walkRes with
    | error _ => rfl
    | ok wl =>
      cases wl with
      | externalOpaque _ => rfl
      | existing targetIno _ _ _ _ _ _ =>
        dsimp only; repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes targetIno with
        | none => rfl
        | some vn =>
          dsimp only
          cases vn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
      | missingInParent parentIno _ _ =>
        dsimp only; repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes parentIno with
        | none => rfl
        | some pvn =>
          dsimp only
          cases pvn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalAt_wrapperErr_safe (req : Files.FilesReq) (want : Errno)
    (hAt : match req with
      | .openat .. | .fstatat .. | .faccessat ..
      | .mkdirat .. | .unlinkat .. | .readlinkat .. => True
      | _ => False)
    (h : Files.evalReq Files.FilesState.initial req = .wrapperErr want) :
    Errno.isCriticalOsErrno want = false ∧ (want == Errno.EINTR) = false := by
  have hSafe : wrapperErrSafe (Files.evalReq Files.FilesState.initial req) = true := by
    unfold Files.evalReq
    apply wes_ite; · exact wes_einval
    cases req <;> try contradiction
    · apply wes_ite; · exact wes_ebadf
      apply wes_ite; · rfl
      exact evalOpen_safe _ _ _ _ _ _ _
    · apply wes_ite; · exact wes_einval
      apply wes_ite; · exact wes_ebadf
      apply wes_ite; · rfl
      unfold Files.evalStat
      repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | dsimp only | split)
    · repeat (first | rfl | exact wes_ebadf | apply wes_ite)
      unfold Files.evalAccess
      repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | dsimp only | split)
    · repeat (first | rfl | exact wes_ebadf | apply wes_ite)
      unfold Files.evalMkdir
      repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | dsimp only | split)
    · repeat (first | rfl | exact wes_ebadf | apply wes_ite)
      unfold Files.evalUnlink
      repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | dsimp only | split)
    · apply wes_ite; · exact wes_ebadf
      apply wes_ite; · rfl
      unfold Files.evalReadlink
      repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | dsimp only | split)
  rw [h] at hSafe
  simp only [wrapperErrSafe, Bool.or_eq_true, beq_iff_eq] at hSafe
  rcases hSafe with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- `sampleFilesErrno` preserves `Files.HealthyEnv.initial` across all 6 `*at` operations. -/
theorem sampleFilesErrno_at_healthy (req : Files.FilesReq)
    (hAt : match req with
      | .openat .. | .fstatat .. | .faccessat ..
      | .mkdirat .. | .unlinkat .. | .readlinkat .. => True
      | _ => False)
    (hDir : ∀ h ∈ Files.candidateDirFds req, h = 100) :
    Files.healthyStep Files.HealthyEnv.initial req (.err (sampleFilesErrno req)) =
      some Files.HealthyEnv.initial := by
  have hAllowed : Files.allowedStep Files.HealthyEnv.initial.state req (.err (sampleFilesErrno req)) =
      Files.verifyWithSeccomp Files.HealthyEnv.initial.state req (.err (sampleFilesErrno req)) := by
    cases req with
    | openat d _ _ _ | fstatat d _ _ | faccessat d _ _ _
    | mkdirat d _ _ | unlinkat d _ _ | readlinkat d _ _ =>
      cases d with
      | none => rfl
      | some hid =>
        have h100 : hid = 100 := hDir hid (by simp [Files.candidateDirFds])
        subst h100; rfl
    | _ => contradiction
  have hVer : Files.verifyStep Files.FilesState.initial
      (Files.evalReq Files.FilesState.initial req) (.err (sampleFilesErrno req)) =
      some Files.FilesState.initial ∧
      Errno.isCriticalOsErrno (sampleFilesErrno req) = false ∧
      (sampleFilesErrno req == Errno.EINTR) = false := by
    unfold sampleFilesErrno
    cases hEv : Files.evalReq Files.FilesState.initial req with
    | wrapperErr want =>
      have ⟨hC, hI⟩ := evalAt_wrapperErr_safe req want hAt hEv
      simp [Files.verifyStep, Files.isOutcomeErr, hC, hI]
    | err primary alts st? =>
      dsimp only [Files.verifyStep]
      by_cases hp : (primary == Errno.ENOSPC) = true
      · have hpEq : primary = Errno.ENOSPC := beq_iff_eq.mp hp
        subst hpEq
        have hNe : (Errno.EMFILE == Errno.ENOSPC) = false := by decide
        have hTr : Errno.isTransientOsErrno Errno.EMFILE = true := by decide
        simp only [beq_self_eq_true, ↓reduceIte, hNe, Bool.false_eq_true, hTr]
        cases alts.contains Errno.EMFILE <;> exact ⟨rfl, by decide, by decide⟩
      · have hpF : (primary == Errno.ENOSPC) = false := Bool.eq_false_iff.mpr hp
        have hSym : (Errno.ENOSPC == primary) = false :=
          Bool.eq_false_iff.mpr (fun hs => hp (beq_iff_eq.mpr (beq_iff_eq.mp hs).symm))
        have hTr : Errno.isTransientOsErrno Errno.ENOSPC = true := by decide
        simp only [hpF, Bool.false_eq_true, ↓reduceIte, hSym, hTr]
        cases alts.contains Errno.ENOSPC <;> exact ⟨rfl, by decide, by decide⟩
    | ok wantOut next extraErrs =>
      cases wantOut with
      | err p =>
        by_cases hp : (p == Errno.ENOSPC) = true
        · have hpEq := beq_iff_eq.mp hp; subst hpEq
          have hNe : (Errno.EMFILE == Errno.ENOSPC) = false := by decide
          have hTr : Errno.isTransientOsErrno Errno.EMFILE = true := by decide
          simp [Files.verifyStep, Files.outcomeEq, hNe, hTr, Bool.or_true]
          exact ⟨by decide, by decide⟩
        · have hpF := Bool.eq_false_iff.mpr hp
          have hSym : (Errno.ENOSPC == p) = false :=
            Bool.eq_false_iff.mpr (fun hs => hp (beq_iff_eq.mpr (beq_iff_eq.mp hs).symm))
          have hTr : Errno.isTransientOsErrno Errno.ENOSPC = true := by decide
          simp [Files.verifyStep, Files.outcomeEq, hpF, hSym, hTr, Bool.or_true]
          exact ⟨by decide, by decide⟩
      | _ =>
        have hTr : Errno.isTransientOsErrno Errno.ENOSPC = true := by decide
        simp [Files.verifyStep, Files.outcomeEq, hTr, Bool.or_true]
        exact ⟨by decide, by decide⟩
    | nondet act extraErrs =>
      dsimp only [Files.verifyStep]
      have hTr : Errno.isTransientOsErrno Errno.ENOSPC = true := by decide
      have hVN := verifyNondet_spc Files.FilesState.initial act
      cases hV : Files.verifyNondet Files.FilesState.initial act (.err Errno.ENOSPC) with
      | none => simp [hTr, Bool.or_true]; exact ⟨by decide, by decide⟩
      | some s' => rw [hV] at hVN; subst hVN; exact ⟨rfl, by decide, by decide⟩
  have hWf : (!Files.HealthyEnv.initial.wf) = false := by decide
  have hNotClose : Files.isCloseEbusy req (.err (sampleFilesErrno req)) = false := by
    cases req <;> first | contradiction | rfl
  unfold Files.healthyStep Files.isCriticalFault Files.isEintrOutcome
  simp only [hWf, hVer.2.1, hNotClose, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [hAllowed]; unfold Files.verifyWithSeccomp; dsimp only
  have hVer' : Files.verifyStep Files.HealthyEnv.initial.state
      (Files.evalReq Files.HealthyEnv.initial.state req) (.err (sampleFilesErrno req)) =
      some Files.HealthyEnv.initial.state := hVer.1
  rw [hVer']; dsimp only; simp only [hVer.2.2, Bool.false_eq_true, ↓reduceIte]

/-- Pure `Files.FilesOpsM (StateM WitnessWorld) RawFd` witness. -/
def witnessFiles : Files.FilesOpsM (StateM WitnessWorld) RawFd where
  openat d p fl m := pure (.error (sampleFilesErrno (.openat (d.map dummyHid) p fl m)))
  openat2 _ _ _ := pure (.error Errno.EBADF)
  close _ := pure (.error Errno.EBADF)
  read _ _ := pure (.error Errno.EBADF)
  write _ _ := pure (.error Errno.EBADF)
  fstat _ := pure (.error Errno.EBADF)
  fstatat d p fl := pure (.error (sampleFilesErrno (.fstatat (d.map dummyHid) p fl)))
  faccessat d p mk fl := pure (.error (sampleFilesErrno (.faccessat (d.map dummyHid) p mk fl)))
  mkdirat d p m := pure (.error (sampleFilesErrno (.mkdirat (d.map dummyHid) p m)))
  unlinkat d p rm := pure (.error (sampleFilesErrno (.unlinkat (d.map dummyHid) p rm)))
  renameat2 _ _ _ _ _ := pure (.error Errno.EBADF)
  symlinkat _ _ _ := pure (.error Errno.EBADF)
  readlinkat d p c := pure (.error (sampleFilesErrno (.readlinkat (d.map dummyHid) p c)))
  getdents64 _ _ := pure (.error Errno.EBADF)
  fchmodat _ _ _ := pure (.error Errno.EBADF)
  fchmod _ _ := pure (.error Errno.EBADF)
  flock _ _ := pure (.error Errno.EBADF)
  fcntl _ _ := pure (.error Errno.EBADF)
  fsync _ := pure (.error Errno.EBADF)
  getcwd _ := pure (.error Errno.EINVAL)
  lseek _ _ _ := pure (.error Errno.EBADF)
  reopenReadOnly _ := pure (.error Errno.EBADF)
  dupStdio _ := pure (.error Errno.EBADF)

/-- Fallback `Errno` accepted by `Net.healthyStep` on `Net.HealthyEnv.initial`. -/
def sampleNetErrno (req : Net.NetReq) : Errno :=
  match Net.preCheckNet req with
  | some err => err
  | none =>
    match req with
    | .socket .. | .socketpair .. => Errno.ENOSPC
    | _ => Errno.EBADF

private theorem preCheckNet_safe (req : Net.NetReq) (err : Errno)
    (h : Net.preCheckNet req = some err) :
    Errno.isCriticalOsErrno err = false ∧ (err == Errno.EINTR) = false := by
  unfold Net.preCheckNet Net.validateSocketArgs Net.validateSocketpairArgs at h
  cases req <;> simp only at h
  all_goals
    repeat (first
      | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
      | split at h
      | cases h)

private theorem sampleNetErrno_core (s : Net.NetState) (h100 : Net.lookupHandleFileId s 100 = none)
    (nreq : RawFdNetReq) (err0 : Errno) (hErr0 : sampleNetErrno (mapRawFdNetReq dummyHid nreq) = err0) :
    Errno.isCriticalOsErrno err0 = false ∧
    (err0 == Errno.EINTR) = false ∧
    Net.stepNetCore s (mapRawFdNetReq dummyHid nreq) (some (.err err0)) = some (.err err0, s) := by
  have hEmit : ∀ e : Errno,
      Net.emitErr (some (.err e)) s e [] (allowTransient := false) = some (.err e, s) := by
    intro e; unfold Net.emitErr; dsimp only; rw [beq_self_eq_true]; rfl
  have ⟨preOpt, hPre⟩ : ∃ o, Net.preCheckNet (mapRawFdNetReq dummyHid nreq) = o := ⟨_, rfl⟩
  cases preOpt with
  | some err =>
    have ⟨hC, hI⟩ := preCheckNet_safe _ err hPre
    have hEq : err0 = err := by rw [← hErr0]; unfold sampleNetErrno; rw [hPre]
    subst hEq
    refine ⟨hC, hI, ?_⟩
    delta Net.stepNetCore; rw [hPre]; exact hEmit _
  | none =>
    cases nreq <;>
      (dsimp only [mapRawFdNetReq, dummyHid] at hErr0 hPre ⊢;
       unfold sampleNetErrno at hErr0; rw [hPre] at hErr0; dsimp only at hErr0;
       subst hErr0;
       refine ⟨by decide, by decide, ?_⟩;
       delta Net.stepNetCore; rw [hPre]; dsimp only;
       try dsimp only [Net.stepAccept4, Net.stepConnect, Net.stepGetsockopt,
         Net.stepRecvfrom, Net.stepSendto, Net.stepShutdown, Net.stepRecvmsg, Net.withSock];
       try rw [h100];
       rfl)

/-- `sampleNetErrno` preserves `Net.HealthyEnv.initial` across all `RawFdNetReq` operations. -/
theorem sampleNetErrno_healthy (nreq : RawFdNetReq) :
    let req := mapRawFdNetReq dummyHid nreq
    Net.healthyStep Net.HealthyEnv.initial req (.err (sampleNetErrno req)) =
      some Net.HealthyEnv.initial := by
  dsimp only
  have hWf : (!Net.HealthyEnv.initial.wf) = false := by decide
  have ⟨hCrit, hEintr, hStep⟩ := sampleNetErrno_core Net.HealthyEnv.initial.state rfl nreq _ rfl
  unfold Net.healthyStep Net.allowedStep Net.isCriticalFault Net.isEintrOutcome
  simp only [hWf, hCrit, hStep, Option.map, hEintr, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- Pure `Net.NetOpsM (StateM WitnessWorld) RawFd` witness. -/
def witnessNet : Net.NetOpsM (StateM WitnessWorld) RawFd where
  socket dom st fl p := pure (.error (sampleNetErrno (.socket dom st fl p)))
  socketpair dom st fl := pure (.error (sampleNetErrno (.socketpair dom st fl)))
  bind _ _ := pure (.error Errno.EBADF)
  listen _ _ := pure (.error Errno.EBADF)
  accept4 _ fl := pure (.error (sampleNetErrno (.accept4 100 fl)))
  connect _ sa := pure (.error (sampleNetErrno (.connect 100 sa)))
  getsockopt _ opt := pure (.error (sampleNetErrno (.getsockopt 100 opt)))
  setsockopt _ _ _ := pure (.error Errno.EBADF)
  getsockname _ := pure (.error Errno.EBADF)
  recvfrom _ n fl := pure (.error (sampleNetErrno (.recvfrom 100 n fl)))
  sendto _ bs fl := pure (.error (sampleNetErrno (.sendto 100 bs fl)))
  shutdown _ how := pure (.error (sampleNetErrno (.shutdown 100 how)))
  sendmsg _ _ := pure (.error Errno.EBADF)
  recvmsg _ mf := pure (.error (sampleNetErrno (.recvmsg 100 mf)))
  ioctl _ _ _ := pure (.error Errno.EBADF)

/-- Fallback `Errno` accepted by `Poll.healthyStep` on `Poll.HealthyEnv.initial`. -/
def samplePollErrno (fds : Array (RawFd × Poll.PollEvents)) (to? : Option Poll.Timespec) : Errno :=
  match Poll.preCheckPoll (.ppoll (fds.map fun p => (100, p.2)) to?) with
  | some _ => Errno.EINVAL
  | none => if fds.toList.isEmpty then Errno.EMFILE else Errno.EBADF

/-- `samplePollErrno` preserves `Poll.HealthyEnv.initial` for every `ppoll` request. -/
theorem samplePollErrno_healthy (fds : Array (RawFd × Poll.PollEvents))
    (to? : Option Poll.Timespec) :
    Poll.healthyStep Poll.HealthyEnv.initial
      (.ppoll (fds.map fun p => (dummyHid p.1, p.2)) to?)
      (.err (samplePollErrno fds to?)) = some Poll.HealthyEnv.initial := by
  have hPreEq : ∀ preErr,
      Poll.preCheckPoll (.ppoll (fds.map fun p => (100, p.2)) to?) = some preErr →
      preErr = Errno.EINVAL := by
    intro preErr hP; unfold Poll.preCheckPoll at hP; dsimp only at hP
    repeat (first | (injection hP with hE; exact hE.symm) | split at hP | cases hP)
  have hWf : (!Poll.HealthyEnv.initial.wf) = false := by decide
  have ⟨preOpt, hPre⟩ : ∃ o, Poll.preCheckPoll (.ppoll (fds.map fun p => (100, p.2)) to?) = o := ⟨_, rfl⟩
  have hCore :
      let entries := fds.map fun p => (100, p.2)
      let err := samplePollErrno fds to?
      Errno.isCriticalOsErrno err = false ∧
      (err == Errno.EINTR) = false ∧
      Poll.stepPollCore Poll.HealthyEnv.initial.state (.ppoll entries to?) (some (.err err)) =
        some (.err err, Poll.HealthyEnv.initial.state) := by
    dsimp only
    cases preOpt with
    | some preErr =>
      have hEq := hPreEq preErr hPre; subst hEq
      simp only [samplePollErrno, hPre]
      refine ⟨by decide, by decide, ?_⟩
      simp only [Poll.stepPollCore, hPre, beq_self_eq_true, ↓reduceIte]
    | none =>
      simp only [samplePollErrno, hPre]
      rcases fds with ⟨_ | ⟨⟨fd0, ev⟩, tl⟩⟩
      · simp only [List.isEmpty, ↓reduceIte]
        have hToL : (Array.map (fun p => (100, p.2)) ({ toList := [] } : Array (RawFd × Poll.PollEvents))).toList = [] := by
          rw [Array.toList_map]; rfl
        have hSz : (Array.map (fun p => (100, p.2)) ({ toList := [] } : Array (RawFd × Poll.PollEvents))).size = 0 := by
          rw [Array.size_map]; rfl
        refine ⟨by decide, by decide, ?_⟩
        unfold Poll.stepPollCore; dsimp only; rw [hPre, hToL, hSz]; rfl
      · simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
        have hToL : (Array.map (fun p => (100, p.2)) ({ toList := (fd0, ev) :: tl } : Array (RawFd × Poll.PollEvents))).toList =
            (100, ev) :: tl.map (fun p => (100, p.2)) := by
          rw [Array.toList_map]; rfl
        refine ⟨by decide, by decide, ?_⟩
        unfold Poll.stepPollCore; dsimp only; rw [hPre, hToL]; rfl
  rcases hCore with ⟨hCrit, hEintr, hStep⟩
  unfold Poll.healthyStep Poll.allowedStep Poll.isCriticalFault Poll.isEintrOutcome dummyHid
  simp only [hWf, hCrit, hStep, Option.map, hEintr, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- Pure `Poll.PollOpsM (StateM WitnessWorld) RawFd` witness. -/
def witnessPoll : Poll.PollOpsM (StateM WitnessWorld) RawFd where
  ppoll fds to? := pure (.error (samplePollErrno fds to?))
  eventfd2 _ _ := pure (.error Errno.EMFILE)

/-- `evalKill` on `Process.HealthyEnv.initial.state` never returns `Errno.ENOSPC`. -/
theorem evalKillInit_err_ne_enospc
    (tgt : Int32) (sig : LinuxSyscall.Process.Signal) (e : Errno)
    (h : LinuxSyscall.Process.evalKill LinuxSyscall.Process.HealthyEnv.initial.state tgt sig = .error e) :
    (Errno.ENOSPC == e) = false := by
  unfold LinuxSyscall.Process.evalKill at h
  by_cases h1 : sig.isNptlReserved = true
  · simp only [h1, ↓reduceIte] at h; injection h with hE; subst hE; decide
  · have h1f := Bool.eq_false_iff.mpr h1; simp only [h1f, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : (tgt == Int32.minValue) = true
    · simp only [h2, ↓reduceIte] at h; injection h with hE; subst hE; decide
    · have h2f := Bool.eq_false_iff.mpr h2; simp only [h2f, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : tgt > 0
      · simp only [h3, ↓reduceIte] at h
        unfold LinuxSyscall.Process.deliverSignalToTarget at h
        simp only [h1f, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hSelf : (tgt.toUInt32 == LinuxSyscall.Process.effectiveSelfPid LinuxSyscall.Process.HealthyEnv.initial.state) = true
        · simp only [hSelf, ↓reduceIte] at h
          cases hV : sig.isValid <;> simp [hV] at h
          subst h; decide
        · have hSf := Bool.eq_false_iff.mpr hSelf; simp only [hSf, Bool.false_eq_true, ↓reduceIte] at h
          have hNo : assocGet LinuxSyscall.Process.HealthyEnv.initial.state.procs tgt.toUInt32 = none := rfl
          rw [hNo] at h; dsimp only at h; injection h with hE; subst hE; decide
      · simp only [h3, ↓reduceIte] at h
        have hGrp : ∀ pgid,
            LinuxSyscall.Process.evalKillProcessGroup LinuxSyscall.Process.HealthyEnv.initial.state pgid sig = .error e →
            (Errno.ENOSPC == e) = false := by
          intro pgid hg; unfold LinuxSyscall.Process.evalKillProcessGroup at hg
          repeat (first | (injection hg with hE; subst hE; decide) | split at hg | dsimp only at hg | cases hg)
        by_cases h4 : (tgt == 0) = true
        · simp only [h4, ↓reduceIte] at h; exact hGrp _ h
        · have h4f := Bool.eq_false_iff.mpr h4; simp only [h4f, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : (tgt == -1) = true
          · simp only [h5, ↓reduceIte] at h
            have hAny : LinuxSyscall.Process.anyActiveProc LinuxSyscall.Process.HealthyEnv.initial.state.procs
                (fun pid e => pid != LinuxSyscall.Process.effectiveSelfPid LinuxSyscall.Process.HealthyEnv.initial.state &&
                  pid > 1 && e.isLeader && e.lifecycle != .reaped && e.lifecycle != .exitDead) = false := rfl
            rw [hAny] at h; simp at h; subst h; decide
          · have h5f := Bool.eq_false_iff.mpr h5; simp only [h5f, Bool.false_eq_true, ↓reduceIte] at h
            exact hGrp _ h

/-- `checkPidfdOpenTarget` never returns `Errno.ENOSPC`. -/
theorem checkPidfdOpen_err_ne_enospc (s : LinuxSyscall.Process.ProcessSysState)
    (pid : UInt32) (fl : LinuxSyscall.Process.PidfdOpenFlags) (e : Errno)
    (h : LinuxSyscall.Process.checkPidfdOpenTarget s pid fl = .error e) :
    (Errno.ENOSPC == e) = false := by
  unfold LinuxSyscall.Process.checkPidfdOpenTarget at h
  dsimp only at h
  repeat (first | (injection h with hEq; subst hEq; decide) | split at h | dsimp only at h | cases h)

/-- Pure `LinuxSyscall.Process.ProcessOpsM (StateM WitnessWorld) RawFd` witness. -/
def witnessProc : LinuxSyscall.Process.ProcessOpsM (StateM WitnessWorld) RawFd where
  pipe2 _ := pure (.error Errno.ENOSPC)
  waitpid _ _ := pure (.error Errno.ENOSPC)
  kill _ sig := pure (.error (if sig.isNptlReserved then Errno.EINVAL else Errno.ENOSPC))
  pidfd_open _ _ := pure (.error Errno.ENOSPC)
  pidfd_send_signal _ sig _ :=
    pure (.error (if sig.isNptlReserved then Errno.EINVAL else Errno.EBADF))
  getpid := pure (.ok (LinuxSyscall.Process.effectiveSelfPid LinuxSyscall.Process.ProcessSysState.initial))
  getuid := pure (.ok LinuxSyscall.Process.ProcessSysState.initial.selfUid)

end LeanSwe.ProcessSandbox.Raw.Proofs
