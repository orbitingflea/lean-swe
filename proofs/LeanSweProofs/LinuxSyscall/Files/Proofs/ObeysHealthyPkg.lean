import LeanSweProofs.LinuxSyscall.Files.Proofs.ObeysRaw

/-!
# Package-Level Healthy Witness Proofs for `LeanSwe.LinuxSyscall.Files`

Proves `healthyModelOps_obeysStep` for `LeanSwe.LinuxSyscall.Files.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Files.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

private def wrapperErrSafe : StepResult → Bool
  | .wrapperErr e => e == Errno.EINVAL || e == Errno.EBADF
  | _ => true

private theorem wes_einval : wrapperErrSafe (.wrapperErr Errno.EINVAL) = true := by decide

private theorem wes_ebadf : wrapperErrSafe (.wrapperErr Errno.EBADF) = true := by decide

private theorem wes_ite {c : Prop} [Decidable c] {a b : StepResult}
    (ha : wrapperErrSafe a = true) (hb : wrapperErrSafe b = true) :
    wrapperErrSafe (if c then a else b) = true := by
  by_cases c <;> simp_all

private theorem wes_openat2 {b : Bool} {res : ResolveFlags} {td : Bool} {r : StepResult}
    (hr : wrapperErrSafe r = true) :
    wrapperErrSafe (withOpenat2Eagain b res td r) = true := by
  cases r <;> exact hr

private theorem evalOpen_safe (s : FilesState) (dir : Option HandleId)
    (path : ByteArray) (fl : OpenFlags) (md : Mode) (res : ResolveFlags) (so : Bool) :
    wrapperErrSafe (evalOpen s dir path fl md res so) = true := by
  unfold evalOpen
  by_cases hFp : (!so && fl.path) = true
  · simp only [hFp, ↓reduceIte]
    repeat (first | rfl | apply wes_ite)
    generalize resolveOpenTargetWalk s dir path _ _ _ _ = wt
    rcases wt with ⟨walkRes, td⟩
    apply wes_openat2
    dsimp only
    cases walkRes with
    | error _ => rfl
    | ok wl =>
      cases wl with
      | externalOpaque _ => rfl
      | existing targetIno trailing isSpec pIno? lf? viaPm pmHid? =>
        dsimp only
        repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes targetIno with
        | none => rfl
        | some vn =>
          dsimp only
          cases vn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
      | missingInParent parentIno leaf trailing =>
        repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
  · have hFpF : (!so && fl.path) = false := Bool.eq_false_iff.mpr hFp
    simp only [hFpF, Bool.false_eq_true, ↓reduceIte]
    repeat (first | rfl | apply wes_ite)
    generalize resolveOpenTargetWalk s dir path _ _ _ _ = wt
    rcases wt with ⟨walkRes, td⟩
    apply wes_openat2
    dsimp only
    cases walkRes with
    | error _ => rfl
    | ok wl =>
      cases wl with
      | externalOpaque _ => rfl
      | existing targetIno trailing isSpec pIno? lf? viaPm pmHid? =>
        dsimp only
        repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes targetIno with
        | none => rfl
        | some vn =>
          dsimp only
          cases vn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
      | missingInParent parentIno leaf trailing =>
        dsimp only
        repeat (first | rfl | apply wes_ite)
        cases assocGet s.inodes parentIno with
        | none => rfl
        | some pvn =>
          dsimp only
          cases pvn.data <;>
            repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalRead_safe (s : FilesState) (hid : HandleId) (mb : UInt32) :
    wrapperErrSafe (evalRead s hid mb) = true := by
  unfold evalRead
  cases assocGet s.fds hid with
  | none => exact wes_ebadf
  | some desc =>
    dsimp only
    repeat (first | rfl | apply wes_ite)
    cases assocGet s.inodes desc.ino with
    | none => rfl
    | some vn =>
      dsimp only
      cases vn.data <;>
        repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalWrite_safe (s : FilesState) (hid : HandleId) (bs : ByteArray) :
    wrapperErrSafe (evalWrite s hid bs) = true := by
  unfold evalWrite
  cases assocGet s.fds hid with
  | none => exact wes_ebadf
  | some desc =>
    dsimp only
    repeat (first | rfl | apply wes_ite)
    cases assocGet s.inodes desc.ino with
    | none => rfl
    | some vn =>
      dsimp only
      cases vn.data <;>
        repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalStat_safe (s : FilesState) (req : FilesReq) :
    wrapperErrSafe (evalStat s req) = true := by
  unfold evalStat
  cases req <;>
    repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalAccess_safe (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (mask : AccessModeMask) (flags : AtFlags) :
    wrapperErrSafe (evalAccess s dir path mask flags) = true := by
  unfold evalAccess
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalMkdir_safe (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (mode : Mode) :
    wrapperErrSafe (evalMkdir s dir path mode) = true := by
  unfold evalMkdir
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalUnlink_safe (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (rd : Bool) :
    wrapperErrSafe (evalUnlink s dir path rd) = true := by
  unfold evalUnlink
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalRename_safe (s : FilesState) (od : Option HandleId) (op : ByteArray)
    (nd : Option HandleId) (np : ByteArray) (fl : RenameFlags) :
    wrapperErrSafe (evalRename s od op nd np fl) = true := by
  unfold evalRename
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalSymlink_safe (s : FilesState) (t : ByteArray) (d : Option HandleId)
    (lp : ByteArray) :
    wrapperErrSafe (evalSymlink s t d lp) = true := by
  unfold evalSymlink
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalReadlink_safe (s : FilesState) (d : Option HandleId) (p : ByteArray)
    (c : UInt32) :
    wrapperErrSafe (evalReadlink s d p c) = true := by
  unfold evalReadlink
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalGetdents_safe (s : FilesState) (hid : HandleId) (c : UInt32) :
    wrapperErrSafe (evalGetdents s hid c) = true := by
  unfold evalGetdents
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalChmodNode_safe (s : FilesState) (ino : InodeId) (vn : VNode) (md : Mode)
    (pl? : Option (InodeId × ByteArray)) (ud? : Option (HandleId × OpenDesc)) :
    wrapperErrSafe (evalChmodNode s ino vn md pl? ud?) = true := by
  unfold evalChmodNode
  cases vn.data <;>
    repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalFlock_safe (s : FilesState) (hid : HandleId) (op : FlockOp) :
    wrapperErrSafe (evalFlock s hid op) = true := by
  unfold evalFlock
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalFcntl_safe (s : FilesState) (hid : HandleId) (cmd : FcntlCmd) :
    wrapperErrSafe (evalFcntl s hid cmd) = true := by
  unfold evalFcntl
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalFsync_safe (s : FilesState) (hid : HandleId) :
    wrapperErrSafe (evalFsync s hid) = true := by
  unfold evalFsync
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalGetcwd_safe (s : FilesState) (c : UInt32) :
    wrapperErrSafe (evalGetcwd s c) = true := by
  unfold evalGetcwd
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalLseek_safe (s : FilesState) (hid : HandleId) (off : Int64) (wh : SeekWhence) :
    wrapperErrSafe (evalLseek s hid off wh) = true := by
  unfold evalLseek
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalReopenReadOnly_safe (s : FilesState) (hid : HandleId) :
    wrapperErrSafe (evalReopenReadOnly s hid) = true := by
  unfold evalReopenReadOnly
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalDupStdio_safe (s : FilesState) (sl : StdioFd) :
    wrapperErrSafe (evalDupStdio s sl) = true := by
  unfold evalDupStdio
  repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)

private theorem evalReq_safe (s : FilesState) (req : FilesReq) :
    wrapperErrSafe (evalReq s req) = true := by
  unfold evalReq
  apply wes_ite; · exact wes_einval
  cases req with
  | openat _ _ _ _ =>
    apply wes_ite; · exact wes_ebadf
    apply wes_ite; · rfl
    exact evalOpen_safe _ _ _ _ _ _ _
  | openat2 _ _ _ =>
    apply wes_ite; · exact wes_ebadf
    dsimp only
    apply wes_ite; · rfl
    exact evalOpen_safe _ _ _ _ _ _ _
  | close _ =>
    repeat (first | rfl | exact wes_einval | exact wes_ebadf | apply wes_ite | apply wes_openat2 | dsimp only | split)
  | read _ _ => exact evalRead_safe _ _ _
  | write _ _ => exact evalWrite_safe _ _ _
  | fstat _ => exact evalStat_safe _ _
  | fstatat _ _ _ =>
    apply wes_ite; · exact wes_einval
    apply wes_ite; · exact wes_ebadf
    apply wes_ite; · rfl
    exact evalStat_safe _ _
  | faccessat _ _ _ _ =>
    repeat (first | rfl | exact wes_ebadf | apply wes_ite)
    exact evalAccess_safe _ _ _ _ _
  | mkdirat _ _ _ =>
    repeat (first | rfl | exact wes_ebadf | apply wes_ite)
    exact evalMkdir_safe _ _ _ _
  | unlinkat _ _ _ =>
    repeat (first | rfl | exact wes_ebadf | apply wes_ite)
    exact evalUnlink_safe _ _ _ _
  | renameat2 _ _ _ _ _ =>
    apply wes_ite; · exact wes_ebadf
    apply wes_ite; · rfl
    apply wes_ite; · rfl
    exact evalRename_safe _ _ _ _ _ _
  | symlinkat _ _ _ =>
    apply wes_ite; · exact wes_ebadf
    apply wes_ite; · rfl
    exact evalSymlink_safe _ _ _ _
  | readlinkat _ _ _ =>
    apply wes_ite; · exact wes_ebadf
    apply wes_ite; · rfl
    exact evalReadlink_safe _ _ _ _
  | getdents64 _ _ => exact evalGetdents_safe _ _ _
  | fchmodat _ _ _ =>
    repeat (first | rfl | exact wes_ebadf | apply wes_ite | dsimp only | split)
    all_goals exact evalChmodNode_safe _ _ _ _ _ _
  | fchmod _ _ =>
    repeat (first | rfl | exact wes_ebadf | apply wes_ite | dsimp only | split)
    all_goals exact evalChmodNode_safe _ _ _ _ _ _
  | flock _ _ => exact evalFlock_safe _ _ _
  | fcntl _ _ => exact evalFcntl_safe _ _ _
  | fsync _ => exact evalFsync_safe _ _
  | getcwd _ => exact evalGetcwd_safe _ _
  | lseek _ _ _ => exact evalLseek_safe _ _ _ _
  | reopenReadOnly _ => exact evalReopenReadOnly_safe _ _
  | dupStdio _ => exact evalDupStdio_safe _ _

private theorem evalReq_wrapperErr_safe {s : FilesState} {req : FilesReq} {e : Errno}
    (h : evalReq s req = .wrapperErr e) :
    e = Errno.EINVAL ∨ e = Errno.EBADF := by
  have hSafe := evalReq_safe s req
  rw [h] at hSafe
  simp only [wrapperErrSafe, Bool.or_eq_true, beq_iff_eq] at hSafe
  exact hSafe

private theorem verifyStep_emfile_isSome (s : FilesState) (res : StepResult)
    (hNotWrap : res.isWrapperErr = false) :
    (verifyStep s res (.err Errno.EMFILE)).isSome = true := by
  have hTr : Errno.EMFILE.isTransientOsErrno = true := by decide
  cases res with
  | wrapperErr _ => cases hNotWrap
  | err primary alts st? =>
    unfold verifyStep
    dsimp only
    by_cases h1 : (Errno.EMFILE == primary) = true
    · simp only [h1, ↓reduceIte]; rfl
    · by_cases h2 : alts.contains Errno.EMFILE = true
      · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]; rfl
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, hTr]; rfl
  | ok wantOut next extraErrs =>
    unfold verifyStep
    dsimp only
    by_cases h1 : outcomeEq (.err Errno.EMFILE) wantOut = true
    · simp only [h1, ↓reduceIte]; rfl
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, hTr, Bool.or_true]; rfl
  | nondet act extraErrs =>
    unfold verifyStep
    dsimp only
    cases verifyNondet s act (.err Errno.EMFILE) with
    | some _ => rfl
    | none => simp only [hTr, Bool.or_true, ↓reduceIte]; rfl

private theorem verifyStep_ok_implies_allowedStep_isSome (s s1 : FilesState) (req : FilesReq)
    (e : Errno)
    (hNoClose : ∀ h, req ≠ .close h)
    (hNotEnospc : (e == Errno.ENOSPC) = false)
    (hVs : verifyStep s (evalReq s req) (.err e) = some s1) :
    (allowedStep s req (.err e)).isSome = true := by
  have hVws : verifyWithSeccomp s req (.err e) = some s1 := by
    unfold verifyWithSeccomp; dsimp only; rw [hVs]
  cases req with
  | close h => exact absurd rfl (hNoClose h)
  | dupStdio _ =>
    simp [allowedStep, isOutcomeErr, hNotEnospc, hVws]
  | read hid _ | write hid _ | fstat hid | getdents64 hid _
  | fchmod hid _ | flock hid _ | fcntl hid _ | fsync hid
  | lseek hid _ _ | reopenReadOnly hid =>
    dsimp only [allowedStep, directHid?]
    cases assocGet s.fds hid with
    | none => simp [hVws]
    | some desc =>
      dsimp only
      split
      · split
        · rfl
        · simp [hVws]
      · simp [hVws]
  | openat _ _ _ _ | openat2 _ _ _ | fstatat _ _ _ | faccessat _ _ _ _
  | mkdirat _ _ _ | unlinkat _ _ _ | renameat2 _ _ _ _ _ | symlinkat _ _ _
  | readlinkat _ _ _ | fchmodat _ _ _ | getcwd _ =>
    dsimp only [allowedStep, directHid?]
    split
    · simp [hVws]
    · split
      · simp [hVs]
      · split
        · simp [hVs]
        · rw [hVs]; dsimp only; split <;> rfl

private theorem allowedStep_fallback_isSome (s : FilesState) (req : FilesReq)
    (hNoClose : ∀ h, req ≠ .close h) :
    (allowedStep s req (.err (Model.fallbackFilesErrno s req))).isSome = true := by
  unfold Model.fallbackFilesErrno
  cases hRes : evalReq s req with
  | wrapperErr want =>
    dsimp only
    rcases evalReq_wrapperErr_safe hRes with rfl | rfl
    · have hVs : verifyStep s (evalReq s req) (.err Errno.EINVAL) = some s := by
        rw [hRes]; rfl
      exact verifyStep_ok_implies_allowedStep_isSome s s req Errno.EINVAL hNoClose (by decide) hVs
    · have hVs : verifyStep s (evalReq s req) (.err Errno.EBADF) = some s := by
        rw [hRes]; rfl
      exact verifyStep_ok_implies_allowedStep_isSome s s req Errno.EBADF hNoClose (by decide) hVs
  | err primary alts st? | ok primary alts st? | nondet primary alts =>
    dsimp only
    have hNw : (evalReq s req).isWrapperErr = false := by rw [hRes]; rfl
    have hVsSome := verifyStep_emfile_isSome s (evalReq s req) hNw
    cases hVs : verifyStep s (evalReq s req) (.err Errno.EMFILE) with
    | none => rw [hVs] at hVsSome; cases hVsSome
    | some s1 =>
      exact verifyStep_ok_implies_allowedStep_isSome s s1 req Errno.EMFILE hNoClose (by decide) hVs

private theorem crit_einval : isCriticalFault (.err Errno.EINVAL) = false := by decide
private theorem eintr_einval : isEintrOutcome (.err Errno.EINVAL) = false := by decide
private theorem crit_ebadf : isCriticalFault (.err Errno.EBADF) = false := by decide
private theorem eintr_ebadf : isEintrOutcome (.err Errno.EBADF) = false := by decide
private theorem crit_emfile : isCriticalFault (.err Errno.EMFILE) = false := by decide
private theorem eintr_emfile : isEintrOutcome (.err Errno.EMFILE) = false := by decide

private theorem healthyStep_fallback_isSome {env : HealthyEnv} {req : FilesReq}
    (hWf : env.wf = true) (hNoClose : ∀ h, req ≠ .close h) :
    ∃ env', healthyStep env req (.err (Model.fallbackFilesErrno env.state req)) = some env' := by
  have hSafe :
      isCriticalFault (.err (Model.fallbackFilesErrno env.state req)) = false ∧
      isEintrOutcome (.err (Model.fallbackFilesErrno env.state req)) = false := by
    unfold Model.fallbackFilesErrno
    cases hRes : evalReq env.state req with
    | wrapperErr want =>
      dsimp only
      rcases evalReq_wrapperErr_safe hRes with rfl | rfl
      · exact ⟨crit_einval, eintr_einval⟩
      · exact ⟨crit_ebadf, eintr_ebadf⟩
    | _ => exact ⟨crit_emfile, eintr_emfile⟩
  have hNoBusy : isCloseEbusy req (.err (Model.fallbackFilesErrno env.state req)) = false := by
    cases req with
    | close h => exact absurd rfl (hNoClose h)
    | _ => rfl
  have hAlSome := allowedStep_fallback_isSome env.state req hNoClose
  cases hAl : allowedStep env.state req (.err (Model.fallbackFilesErrno env.state req)) with
  | none => rw [hAl] at hAlSome; cases hAlSome
  | some s' =>
    refine ⟨{ state := s', eintrBudget := env.eintrBudget }, ?_⟩
    unfold healthyStep
    simp [hWf, hSafe.1, hNoBusy, hAl, hSafe.2]

private theorem runHealthyFilesOp_obeys {α : Type}
    {req : FilesReq}
    {pack : Except Errno α → FilesOutcome}
    {unpack : FilesOutcome → Option (Except Errno α)}
    {extraOk : Except Errno α → Bool}
    {env : HealthyEnv}
    (hWf : env.wf = true)
    (hPackErr : ∀ e, pack (.error e) = .err e)
    (hNoClose : ∀ h, req ≠ .close h) :
    healthyStep env req (pack (Model.runHealthyFilesOp req pack unpack extraOk env).1) =
      some (Model.runHealthyFilesOp req pack unpack extraOk env).2 := by
  obtain ⟨envFb, hFb⟩ := healthyStep_fallback_isSome hWf hNoClose
  unfold Model.runHealthyFilesOp
  dsimp only
  let fbPair : Except Errno α × HealthyEnv :=
    match healthyStep env req (.err (Model.fallbackFilesErrno env.state req)) with
    | some ef => (.error (Model.fallbackFilesErrno env.state req), ef)
    | none => (.error (Model.fallbackFilesErrno env.state req), env)
  have hFbGoal : healthyStep env req (pack fbPair.1) = some fbPair.2 := by
    dsimp only [fbPair]
    rw [hFb]
    dsimp only
    rw [hPackErr]
    exact hFb
  rcases evalModel env.state req with ⟨candOut, _⟩
  dsimp only
  cases unpack candOut with
  | none => exact hFbGoal
  | some candRes =>
    dsimp only
    cases extraOk candRes with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hFbGoal
    | true =>
      simp only [↓reduceIte]
      cases hSt : healthyStep env req (pack candRes) with
      | none => exact hFbGoal
      | some env' =>
        dsimp only
        cases env'.wf with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hFbGoal
        | true => simp only [↓reduceIte]; exact hSt

private theorem healthyModelOps_close_obeys (env : HealthyEnv) (hid : HandleId)
    (hWf : env.wf = true) :
    let r := (Model.healthyModelOps.close hid).run env
    healthyStep env (.close hid) (outcomeOfUnit r.1) = some r.2 := by
  have hNotWf : (!env.wf) = false := by simp [hWf]
  unfold outcomeOfUnit healthyStep isCriticalFault Errno.isCriticalOsErrno
    isCloseEbusy allowedStep allowedCloseStep verifyStep
    isOutcomeErr isEintrOutcome
  dsimp only [Model.healthyModelOps, modelOps, runOp, evalModel, evalReq, precheckNul,
    StateT.run, bind, StateT.bind, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run]
  rw [hNotWf]
  cases assocGet env.state.fds hid <;> rfl

/-- `Model.healthyModelOps` satisfies `Model.allowedPkgStep` from every well-formed `HealthyEnv`. -/
theorem healthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep := by
  intro env req hWf
  dsimp only [id] at hWf
  rw [execPkgStep_eq]
  cases req with
  | close hid =>
    dsimp only [id, execFilesReq, Model.allowedPkgStep,
      Functor.map, StateT.run, stateT_map_eq]
    exact healthyModelOps_close_obeys env hid hWf
  | _ =>
    dsimp only [id, execFilesReq, Model.healthyModelOps,
      Model.allowedPkgStep, Functor.map, StateT.run, stateT_map_eq]
    apply runHealthyFilesOp_obeys hWf
    · intro _; rfl
    · intro _ hc; cases hc

end LeanSwe.LinuxSyscall.Files.Proofs
