import LeanSweProofs.Process.Proofs.HealthySimBase

/-!
# `Files` `healthyStep` Refinement for `HealthySimState`

Proves `RefinesHealthyFilesOpsAt projSimFiles id healthySimDeps.files` with isolated per-syscall
theorems so elaboration memory stays compact.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

@[simp] private theorem stateM_modifyGet_run {S α : Type} (f : S → α × S) (s : S) :
    (modifyGet f : StateM S α).run s = f s := rfl

private theorem evalReq_read_eq (fs : Files.FilesState) (hid : Files.HandleId) (maxBytes : UInt32) :
    Files.evalReq fs (.read hid maxBytes) = Files.evalRead fs hid maxBytes := rfl

private theorem evalReq_write_eq (fs : Files.FilesState) (hid : Files.HandleId) (data : ByteArray) :
    Files.evalReq fs (.write hid data) = Files.evalWrite fs hid data := rfl

private theorem evalReq_fcntl_eq (fs : Files.FilesState) (hid : Files.HandleId) (cmd : Files.FcntlCmd) :
    Files.evalReq fs (.fcntl hid cmd) = Files.evalFcntl fs hid cmd := rfl

private theorem eq_if_cases {α : Type} {r t f : α} {c : Bool}
    (h : r = if c = true then t else f) : r = t ∨ r = f := by
  cases c
  · exact Or.inr h
  · exact Or.inl h

private theorem assocGet_map_toSimOpenDesc (xs : List (Files.HandleId × HealthySimFd)) (k : Files.HandleId) :
    Files.assocGet (xs.map (fun (h, d) => (h, toSimOpenDesc d))) k =
      (Files.assocGet xs k).map toSimOpenDesc := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', d⟩
    simp only [List.map_cons, Files.assocGet]
    split
    · rfl
    · exact ih

private theorem healthySimInodes_stat_fixed (ino : Files.InodeId) (vn : Files.VNode)
    (hGet : Files.assocGet healthySimInodes ino = some vn) :
    let st := Files.mkStatFromVNode ino vn
    let vn' := { vn with kernelId := { dev? := some st.dev, ino? := some st.ino, allowAlias := vn.kernelId.allowAlias } }
    Files.assocSet healthySimInodes ino vn' = healthySimInodes := by
  dsimp only
  rcases ino with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
    first
      | (injection hGet with hEq; subst hEq; rfl)
      | cases hGet

private theorem healthySimInodes_checkStatMatch (simFds : List (Files.HandleId × HealthySimFd))
    (ino : Files.InodeId) (vn : Files.VNode)
    (hGet : Files.assocGet healthySimInodes ino = some vn) :
    Files.checkStatMatchInState (toSimFilesState simFds) ino vn (Files.mkStatFromVNode ino vn) = true := by
  have hCheck : Files.checkStatMatchInState (toSimFilesState []) ino vn (Files.mkStatFromVNode ino vn) = true := by
    rcases ino with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
      first
        | (injection hGet with hEq; subst hEq; decide)
        | cases hGet
  have hAlias : vn.kernelId.allowAlias = true := by
    rcases ino with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
      first
        | (injection hGet with hEq; subst hEq; rfl)
        | cases hGet
  unfold Files.checkStatMatchInState at hCheck ⊢
  have hMatchEq : Files.checkStatMatch (toSimFilesState simFds) vn (Files.mkStatFromVNode ino vn) =
      Files.checkStatMatch (toSimFilesState []) vn (Files.mkStatFromVNode ino vn) := rfl
  rw [hMatchEq, hAlias]
  rw [hAlias] at hCheck
  simpa [Bool.true_or, Bool.or_true, Bool.and_true] using hCheck

private theorem healthySimInodes_not_symlink (ino : Files.InodeId) (vn : Files.VNode)
    (hGet : Files.assocGet healthySimInodes ino = some vn) :
    ∀ symTgt, vn.data ≠ .symlink symTgt := by
  rcases ino with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
    first
      | (injection hGet with hEq; subst hEq; intro _ hC; cases hC)
      | cases hGet

private theorem walkPath_err_nonCritical (fs : Files.FilesState)
    (hNoSym : ∀ i vn, Files.assocGet fs.inodes i = some vn → ∀ symTgt, vn.data ≠ .symlink symTgt)
    (rootIno : Files.InodeId) (anchorMount : Nat) (resolve : Files.ResolveFlags)
    (mode : Files.WalkMode) (rootSet touchedDotDot : Bool)
    (curDentry? : Option (Files.InodeId × ByteArray))
    (stepFuel symFuel : Nat) (curIno : Files.InodeId) (depth : Nat)
    (segs : List ByteArray) (trailing : Bool) (e : Errno)
    (hw : (Files.walkPath fs rootIno anchorMount resolve mode rootSet touchedDotDot
      curDentry? stepFuel symFuel curIno depth segs trailing).1 = .error e) :
    Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR := by
  induction stepFuel generalizing symFuel curIno depth segs trailing rootSet touchedDotDot curDentry? with
  | zero =>
    unfold Files.walkPath at hw
    dsimp only at hw
    injection hw with hEq; subst hEq; decide
  | succ f ih =>
    unfold Files.walkPath at hw
    cases segs with
    | nil =>
      dsimp only at hw
      cases mode with
      | openTarget _ _ _ => dsimp only at hw; cases hw
      | lookup _ | parent =>
        dsimp only at hw
        cases hCur : Files.assocGet fs.inodes curIno with
        | none =>
          rw [hCur] at hw; dsimp only at hw
          injection hw with hEq; subst hEq; decide
        | some vn =>
          rw [hCur] at hw; dsimp only at hw
          by_cases h1 : (trailing && vn.kind != .dir) = true
          · rw [ite_eq_left h1] at hw
            by_cases h2 : (vn.isDynamic && vn.kind == .other) = true
            · rw [ite_eq_left h2] at hw; cases hw
            · rw [ite_eq_right h2] at hw; dsimp only at hw; injection hw with hEq; subst hEq; decide
          · rw [ite_eq_right h1] at hw; cases hw
    | cons seg rest =>
      dsimp only at hw
      cases hCur : Files.assocGet fs.inodes curIno with
      | none =>
        rw [hCur] at hw; dsimp only at hw
        injection hw with hEq; subst hEq; decide
      | some dirVn =>
        rw [hCur] at hw; dsimp only at hw
        cases hDirData : dirVn.data with
        | dir dd =>
          rw [hDirData] at hw; dsimp only at hw
          by_cases hPerm : (!Files.hasVNodePermIn fs dirVn false false true) = true
          · rw [ite_eq_left hPerm] at hw; dsimp only at hw; injection hw with hEq; subst hEq; decide
          · rw [ite_eq_right hPerm] at hw
            by_cases hDot : Files.bytesEq seg Files.dotBytes = true
            · rw [ite_eq_left hDot] at hw; exact ih _ _ _ _ _ _ _ _ hw
            · rw [ite_eq_right hDot] at hw
              by_cases hDotDot : Files.bytesEq seg Files.dotDotBytes = true
              · rw [ite_eq_left hDotDot] at hw
                by_cases hb1 : (resolve.beneath && depth == 0) = true
                · rw [ite_eq_left hb1] at hw; dsimp only at hw; injection hw with hEq; subst hEq; decide
                · rw [ite_eq_right hb1] at hw
                  by_cases hb2 : (resolve.inRoot && depth == 0) = true
                  · rw [ite_eq_left hb2] at hw; exact ih _ _ _ _ _ _ _ _ hw
                  · rw [ite_eq_right hb2] at hw
                    by_cases hb3 : (resolve.noXdev && Files.inodeMountId fs dd.parentIno != anchorMount) = true
                    · rw [ite_eq_left hb3] at hw; dsimp only at hw; injection hw with hEq; subst hEq; decide
                    · rw [ite_eq_right hb3] at hw; exact ih _ _ _ _ _ _ _ _ hw
              · rw [ite_eq_right hDotDot] at hw
                have hDropOkIf : ∀ {α : Type} (c : Bool) (okVal : α) (restVal : Except Errno α × Bool),
                    (if c then (Except.ok okVal, touchedDotDot) else restVal).1 = .error e →
                    restVal.1 = .error e := by
                  intro _ c _ _ hIf
                  cases c
                  · exact hIf
                  · cases hIf
                have hw' := hDropOkIf _ _ _ hw
                clear hw
                by_cases hDead : (dirVn.nlink == 0 || dd.lifecycle.isDead) = true
                · rw [ite_eq_left hDead] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                · rw [ite_eq_right hDead] at hw'
                  by_cases hLong : seg.size > NAME_MAX
                  · rw [ite_eq_left hLong] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                  · rw [ite_eq_right hLong] at hw'
                    cases hCh : Files.bytesAssocGet dd.children seg with
                    | none =>
                      rw [hCh] at hw'; dsimp only at hw'
                      cases mode with
                      | openTarget _ _ _ =>
                        dsimp only at hw'
                        by_cases hFin : rest.isEmpty = true
                        · rw [ite_eq_left hFin] at hw'; cases hw'
                        · rw [ite_eq_right hFin] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                      | lookup _ | parent =>
                        dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                    | some childIno =>
                      rw [hCh] at hw'; dsimp only at hw'
                      cases hChild : Files.assocGet fs.inodes childIno with
                      | none =>
                        rw [hChild] at hw'; dsimp only at hw'
                        injection hw' with hEq; subst hEq; decide
                      | some childVn =>
                        rw [hChild] at hw'; dsimp only at hw'
                        by_cases hXd : (resolve.noXdev && childVn.mountId != anchorMount) = true
                        · rw [ite_eq_left hXd] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                        · rw [ite_eq_right hXd] at hw'
                          cases hCData : childVn.data with
                          | symlink symTgt =>
                            exact False.elim (hNoSym childIno childVn hChild symTgt hCData)
                          | reg _ | dir _ | fifo _ | charDev _ | blockDev | socket | other =>
                            rw [hCData] at hw'; dsimp only at hw'
                            by_cases hFin : rest.isEmpty = true
                            · rw [ite_eq_left hFin] at hw'
                              cases mode with
                              | openTarget _ _ _ => dsimp only at hw'; cases hw'
                              | lookup _ | parent =>
                                dsimp only at hw'
                                by_cases hTr : (trailing && childVn.kind != .dir) = true
                                · rw [ite_eq_left hTr] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                                · rw [ite_eq_right hTr] at hw'; cases hw'
                            · rw [ite_eq_right hFin] at hw'
                              by_cases hNotD : (childVn.kind != .dir) = true
                              · rw [ite_eq_left hNotD] at hw'; dsimp only at hw'; injection hw' with hEq; subst hEq; decide
                              · rw [ite_eq_right hNotD] at hw'; exact ih _ _ _ _ _ _ _ _ hw'
        | reg _ | symlink _ | fifo _ | charDev _ | blockDev | socket | other =>
          rw [hDirData] at hw; dsimp only at hw
          by_cases hExt : (dirVn.isDynamic && dirVn.kind == .other) = true
          · rw [ite_eq_left hExt] at hw; cases hw
          · rw [ite_eq_right hExt] at hw; dsimp only at hw; injection hw with hEq; subst hEq; decide

private theorem resolvePath_err_nonCritical (simFds : List (Files.HandleId × HealthySimFd))
    (dir : Option Files.HandleId) (path : ByteArray) (follow : Bool) (e : Errno)
    (h : Files.resolveLookupOrExt (toSimFilesState simFds) dir path follow = .error e) :
    Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR := by
  let fs := toSimFilesState simFds
  change Files.resolveLookupOrExt fs dir path follow = .error e at h
  unfold Files.resolveLookupOrExt at h
  by_cases hNul : hasEmbeddedNul path = true
  · rw [ite_eq_left hNul] at h; injection h with hEq; subst hEq; decide
  · rw [ite_eq_right hNul] at h
    have hAfterDir :
        ∃ u : Unit,
          (Bind.bind (Files.validatePathBytes path) fun (isAbs, segs, trailing) =>
            if path.data.size == 0 then Except.error Errno.ENOENT
            else if isAbs && ({} : Files.ResolveFlags).beneath then .error Errno.EXDEV
            else do
              let startIno ←
                if isAbs && !({} : Files.ResolveFlags).beneath && !({} : Files.ResolveFlags).inRoot then .ok fs.rootIno
                else Files.resolveStartDir fs dir
              let baseIno := if isAbs then (if ({} : Files.ResolveFlags).inRoot then startIno else fs.rootIno) else startIno
              let anchorMount := Files.inodeMountId fs baseIno
              let initDentry? := if isAbs && !({} : Files.ResolveFlags).beneath && !({} : Files.ResolveFlags).inRoot then none
                else match dir with
                  | some hid => (Files.assocGet fs.fds hid).bind (·.dentry?)
                  | none => if fs.cwdIno == fs.rootIno then none else none
              let res ← (Files.walkPath fs startIno anchorMount {} (.lookup follow) (isAbs || ({} : Files.ResolveFlags).inRoot) false
                initDentry? (segs.length + (Files.MAX_SYMLINKS + 1) * PATH_MAX + 32) Files.MAX_SYMLINKS
                baseIno 0 segs trailing).1
              match res with
              | .existing ino _ _ pIno? lf? _ procHid? =>
                let dentry? := match pIno?, lf? with | some p, some l => some (p, l) | _, _ => none
                let procDesc? := procHid?.bind fun hid => (Files.assocGet fs.fds hid).map fun d => (hid, d)
                .ok (some (ino, dentry?, procDesc?))
              | .externalOpaque _ => .ok none
              | .missingInParent _ _ _ => .error Errno.ENOENT) = Except.error e ∨
          (e = Errno.EBADF ∧ u = ()) := by
      refine ⟨(), ?_⟩
      cases dir with
      | none =>
        exact Or.inl h
      | some hid =>
        change Bind.bind (match Files.assocGet fs.fds hid with
          | none => Except.error Errno.EBADF
          | some _ => Except.ok ()) _ = Except.error e at h
        cases hG : Files.assocGet fs.fds hid with
        | none =>
          rw [hG] at h
          dsimp only [Bind.bind, Except.bind] at h
          injection h with hEq
          exact Or.inr ⟨hEq.symm, rfl⟩
        | some _ =>
          rw [hG] at h
          exact Or.inl h
    rcases hAfterDir with ⟨_, hRest | ⟨rfl, _⟩⟩
    · cases hVP : Files.validatePathBytes path with
      | error ev =>
        rw [hVP] at hRest; dsimp only [Bind.bind, Except.bind] at hRest
        injection hRest with hEq; subst hEq
        unfold Files.validatePathBytes at hVP
        repeat (first | (injection hVP with hV; subst hV; decide) | split at hVP | cases hVP)
      | ok tup =>
        rcases tup with ⟨isAbs, segs, trailing⟩
        rw [hVP] at hRest; dsimp only [Bind.bind, Except.bind] at hRest
        by_cases hSz : (path.data.size == 0) = true
        · rw [ite_eq_left hSz] at hRest; injection hRest with hEq; subst hEq; decide
        · rw [ite_eq_right hSz] at hRest
          cases isAbs with
          | true =>
            simp at hRest
            split at hRest
            · next ew hW =>
              injection hRest with hEq; subst hEq
              exact walkPath_err_nonCritical fs healthySimInodes_not_symlink _ _ _ _ _ _ _ _ _ _ _ _ _ ew hW
            · next wt _ =>
              rcases wt with _ | _ | _ <;> dsimp only at hRest <;>
                first | (cases hRest; done) | (injection hRest with hEq; subst hEq; decide)
          | false =>
            simp at hRest
            cases hSt : Files.resolveStartDir fs dir with
            | error es =>
              rw [hSt] at hRest; dsimp only at hRest
              injection hRest with hEq; subst hEq
              unfold Files.resolveStartDir at hSt
              cases dir with
              | none => cases hSt
              | some hid =>
                dsimp only at hSt
                repeat (first | (injection hSt with hS; subst hS; decide) | split at hSt | cases hSt)
            | ok startIno =>
              rw [hSt] at hRest; dsimp only at hRest
              split at hRest
              · next ew hW =>
                injection hRest with hEq; subst hEq
                exact walkPath_err_nonCritical fs healthySimInodes_not_symlink _ _ _ _ _ _ _ _ _ _ _ _ _ ew hW
              · next wt _ =>
                rcases wt with _ | _ | _ <;> dsimp only at hRest <;>
                  first | (cases hRest; done) | (injection hRest with hEq; subst hEq; decide)
    · decide

private theorem no_closeUncertain_in_simFds (simFds : List (Files.HandleId × HealthySimFd)) :
    ∀ h d, Files.assocGet (toSimFilesState simFds).fds h = some d → d.closeState = .open := by
  intro h d hGet
  rw [toSimFilesState, assocGet_map_toSimOpenDesc] at hGet
  cases hG : Files.assocGet simFds h with
  | none => rw [hG] at hGet; cases hGet
  | some sd => rw [hG] at hGet; injection hGet with hEq; rw [← hEq]; rfl

private theorem simFiles_healthyStep_nonClose
    (simFds : List (Files.HandleId × HealthySimFd))
    (req : Files.FilesReq) (out : Files.FilesOutcome)
    (hNotClose : ∀ h, req ≠ .close h)
    (hNotDup : ∀ sl, req ≠ .dupStdio sl) :
    Files.healthyStep { state := toSimFilesState simFds, eintrBudget := 0 } req out =
      match Files.verifyStep (toSimFilesState simFds) (Files.evalReq (toSimFilesState simFds) req) out with
      | none => none
      | some s' =>
        match out with
        | .err code =>
          if !Errno.isCriticalOsErrno code && code != Errno.EINTR then
            some { state := s', eintrBudget := 0 }
          else none
        | _ => some { state := s', eintrBudget := 0 } := by
  have hSec : (toSimFilesState simFds).ambientSeccomp = false := rfl
  have hNoBusy : Files.isCloseEbusy req out = false := by
    cases req <;> try rfl
    next h => exact absurd rfl (hNotClose h)
  have hVerSec : Files.verifyWithSeccomp (toSimFilesState simFds) req out =
      Files.verifyStep (toSimFilesState simFds) (Files.evalReq (toSimFilesState simFds) req) out := by
    unfold Files.verifyWithSeccomp
    dsimp only
    rw [hSec]
    cases Files.verifyStep (toSimFilesState simFds) (Files.evalReq (toSimFilesState simFds) req) out <;> rfl
  have hAllow : Files.allowedStep (toSimFilesState simFds) req out =
      Files.verifyWithSeccomp (toSimFilesState simFds) req out := by
    unfold Files.allowedStep
    cases req with
    | close h => exact absurd rfl (hNotClose h)
    | dupStdio sl => exact absurd rfl (hNotDup sl)
    | read hid _ | write hid _ | fstat hid | getdents64 hid _
    | fchmod hid _ | flock hid _ | fcntl hid _ | fsync hid
    | lseek hid _ _ | reopenReadOnly hid =>
      dsimp only [Files.directHid?]
      cases hG : Files.assocGet (toSimFilesState simFds).fds hid with
      | none => rfl
      | some desc =>
        dsimp only
        rw [no_closeUncertain_in_simFds simFds hid desc hG]
        rfl
    | getcwd _ => rfl
    | openat dir _ _ _ | openat2 dir _ _ | fstatat dir _ _ | faccessat dir _ _ _
    | mkdirat dir _ _ | unlinkat dir _ _ | symlinkat _ dir _ | readlinkat dir _ _
    | fchmodat dir _ _ =>
      cases dir with
      | none => rfl
      | some h =>
        dsimp only [Files.directHid?, Files.candidateDirFds, List.filter]
        cases hG : Files.assocGet (toSimFilesState simFds).fds h with
        | none => rfl
        | some d =>
          simp only [no_closeUncertain_in_simFds simFds h d hG]
          rfl
    | renameat2 d1 _ d2 _ _ =>
      cases d1 with
      | none =>
        cases d2 with
        | none => rfl
        | some h2 =>
          dsimp only [Files.directHid?, Files.candidateDirFds]
          simp only [List.nil_append, List.filter]
          cases hG2 : Files.assocGet (toSimFilesState simFds).fds h2 with
          | none => rfl
          | some d2 =>
            simp only [no_closeUncertain_in_simFds simFds h2 d2 hG2]
            rfl
      | some h1 =>
        cases d2 with
        | none =>
          dsimp only [Files.directHid?, Files.candidateDirFds]
          simp only [List.append_nil, List.filter]
          cases hG1 : Files.assocGet (toSimFilesState simFds).fds h1 with
          | none => rfl
          | some d1 =>
            simp only [no_closeUncertain_in_simFds simFds h1 d1 hG1]
            rfl
        | some h2 =>
          dsimp only [Files.directHid?, Files.candidateDirFds]
          simp only [List.cons_append, List.nil_append, List.filter]
          cases hG1 : Files.assocGet (toSimFilesState simFds).fds h1 with
          | none =>
            cases hG2 : Files.assocGet (toSimFilesState simFds).fds h2 with
            | none => rfl
            | some d2 =>
              simp only [no_closeUncertain_in_simFds simFds h2 d2 hG2]
              rfl
          | some d1 =>
            cases hG2 : Files.assocGet (toSimFilesState simFds).fds h2 with
            | none =>
              simp only [no_closeUncertain_in_simFds simFds h1 d1 hG1]
              rfl
            | some d2 =>
              simp only [no_closeUncertain_in_simFds simFds h1 d1 hG1,
                no_closeUncertain_in_simFds simFds h2 d2 hG2]
              rfl
  unfold Files.healthyStep Files.HealthyEnv.wf Files.isCriticalFault Files.isEintrOutcome
  rw [hSec, hNoBusy, hAllow, hVerSec]
  dsimp only
  cases hVer : Files.verifyStep (toSimFilesState simFds) (Files.evalReq (toSimFilesState simFds) req) out with
  | none =>
    cases out with
    | err code =>
      by_cases hc : Errno.isCriticalOsErrno code = true
      · simp [hc]
      · simp [Bool.eq_false_iff.mpr hc]
    | opened _ | unit | bytes _ | u32 _ | u64 _ | statted _ => rfl
  | some s' =>
    dsimp only
    cases out with
    | err code =>
      by_cases hc : Errno.isCriticalOsErrno code = true
      · simp [hc]
      · have hcf := Bool.eq_false_iff.mpr hc
        by_cases he : (code == Errno.EINTR) = true
        · simp [bne, hcf, he]
        · have hef := Bool.eq_false_iff.mpr he
          simp [bne, hcf, hef]
    | opened _ | unit | bytes _ | u32 _ | u64 _ | statted _ => rfl


private theorem simFiles_close_healthy (s : HealthySimState) (hid : Files.HandleId)
    (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.close hid).run s
    Files.healthyStep (projSimFiles s) (.close (id hid)) (Files.outcomeOfUnit r.1) =
      some (projSimFiles r.2) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, id]
  cases hGet : Files.assocGet s.simFds hid with
  | none =>
    dsimp only [Files.outcomeOfUnit]
    have hNoneF : Files.assocGet (toSimFilesState s.simFds).fds hid = none := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    unfold Files.healthyStep Files.HealthyEnv.wf Files.isCriticalFault Files.isEintrOutcome
      Files.isCloseEbusy Files.allowedStep Files.allowedCloseStep Files.verifyStep
    dsimp only
    have hSec : (toSimFilesState s.simFds).ambientSeccomp = false := rfl
    rw [hSec, hNoneF]
    simp [Files.isOutcomeErr, Errno.isCriticalOsErrno, Errno.EBADF, Errno.EBUSY, Errno.EINTR,
      Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  | some d =>
    dsimp only [Files.outcomeOfUnit]
    have hSomeF : Files.assocGet (toSimFilesState s.simFds).fds hid = some (toSimOpenDesc d) := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    unfold Files.healthyStep Files.HealthyEnv.wf Files.isCriticalFault Files.isEintrOutcome
      Files.isCloseEbusy Files.allowedStep Files.allowedCloseStep
    dsimp only
    have hSec : (toSimFilesState s.simFds).ambientSeccomp = false := rfl
    rw [hSec, hSomeF]
    simp only [Bool.not_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, Files.HealthyEnv.mk.injEq]
    refine ⟨?_, trivial⟩
    have hEraseEq : Files.assocErase (toSimFilesState s.simFds).fds hid =
        (Files.assocErase s.simFds hid).map (fun (k, v) => (k, toSimOpenDesc v)) :=
      assocErase_map_val s.simFds toSimOpenDesc hid
    unfold Files.closeDescInState
    dsimp only
    rw [hEraseEq]
    generalize Files.assocErase s.simFds hid = ys
    let fds' := ys.map (fun (k, v) => (k, toSimOpenDesc v))
    have hIno789 : (toSimOpenDesc d).ino = 7 ∨ (toSimOpenDesc d).ino = 8 ∨ (toSimOpenDesc d).ino = 9 := by
      unfold toSimOpenDesc
      cases d.isReader <;> cases d.hangMode <;> simp
    have hOfd : (toSimOpenDesc d).ofdId? = none := rfl
    have hPath : (toSimOpenDesc d).isPathFd = false := rfl
    rw [hOfd, hPath]
    rcases hIno789 with hIno | hIno | hIno
    all_goals
      rw [hIno]
      dsimp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      change
        (let pruned : List (Files.InodeId × Files.VNode) :=
           if _ then healthySimInodes
           else if fds'.any (·.2.ino == _) then healthySimInodes
           else if fds'.any (fun (_, d0) =>
               match Files.assocGet healthySimInodes d0.ino with
               | some sv => match sv.data with | .symlink (.procMagic tgt _) => tgt == _ | _ => false
               | none => false) then healthySimInodes
           else healthySimInodes;
         { toSimFilesState s.simFds with
           inodes := pruned
           fds := fds'
           freeStdioSlots := []
           managedStdioMap := []
           procClosedAfter :=
             if pruned.any (fun (_, vn) =>
                 match vn.data with
                 | .symlink (.procMagic _ (some h)) => h == hid
                 | _ => false) then
               Files.assocSet [] hid 100
             else [] }) = toSimFilesState ys
      simp only [ite_self]
      rfl

private theorem simFiles_read_healthy (s : HealthySimState) (hid : Files.HandleId) (maxBytes : UInt32)
    (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.read hid maxBytes).run s
    Files.healthyStep (projSimFiles s) (.read (id hid) maxBytes) (Files.outcomeOfBytes r.1) =
      some (projSimFiles r.2) ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ maxBytes.toNat) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, id, Files.outcomeOfBytes]
  cases hGet : Files.assocGet s.simFds hid with
  | none =>
    dsimp only
    have hNoneF : Files.assocGet (toSimFilesState s.simFds).fds hid = none := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    refine ⟨?_, (by intro _ h; cases h)⟩
    rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
    rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep
    dsimp only
    rw [hNoneF]
    simp [Files.isOutcomeErr, Errno.isCriticalOsErrno, Errno.EBADF, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  | some d =>
    dsimp only
    have hSomeF : Files.assocGet (toSimFilesState s.simFds).fds hid = some (toSimOpenDesc d) := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    cases hRd : d.isReader with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      refine ⟨?_, (by intro _ h; cases h)⟩
      rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
      have hAcc : ((toSimOpenDesc d).access == .wronly) = true := by simp [toSimOpenDesc, hRd]; decide
      have hCrit9 : Errno.isCriticalOsErrno Errno.EBADF = false := by decide
      have hNeEi9 : (Errno.EBADF != Errno.EINTR) = true := by decide
      simp [hNotPath, hAcc, hCrit9, hNeEi9]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hAcc : ((toSimOpenDesc d).access == .wronly) = false := by simp [toSimOpenDesc, hRd]; decide
      cases hHang : d.hangMode with
      | true =>
        simp only [↓reduceIte]
        cases hNb : d.nonblock with
        | true =>
          simp only [↓reduceIte]
          refine ⟨?_, (by intro _ h; cases h)⟩
          rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
          rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep Files.verifyNondet
          dsimp only
          rw [hSomeF]
          have hIno9 : Files.assocGet (toSimFilesState s.simFds).inodes 9 = some (mkSimVNode 9 (.charDev .generic) 0o600 1) := rfl
          have hDyn9 : (mkSimVNode 9 (.charDev .generic) 0o600 1).isDynamic = true := rfl
          have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
          have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
          have hInoEq : (toSimOpenDesc d).ino = 9 := by simp [toSimOpenDesc, hRd, hHang]
          have hNbEq : (toSimOpenDesc d).nonblock = true := by simp [toSimOpenDesc, hNb]
          have hData9 : (mkSimVNode 9 (.charDev .generic) 0o600 1).data = .charDev .generic := rfl
          have hCrit11 : Errno.isCriticalOsErrno Errno.EAGAIN = false := by decide
          have hNeEi11 : (Errno.EAGAIN != Errno.EINTR) = true := by decide
          simp [hNotPath, hAcc, hNotExt, hInoEq, hIno9, hDyn9, hNbEq, hData9, hCrit11, hNeEi11]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨?_, ?_⟩
          · rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
            rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep Files.verifyNondet
            dsimp only
            rw [hSomeF]
            have hIno9 : Files.assocGet (toSimFilesState s.simFds).inodes 9 = some (mkSimVNode 9 (.charDev .generic) 0o600 1) := rfl
            have hDyn9 : (mkSimVNode 9 (.charDev .generic) 0o600 1).isDynamic = true := rfl
            have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
            have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
            have hInoEq : (toSimOpenDesc d).ino = 9 := by simp [toSimOpenDesc, hRd, hHang]
            have hData9 : (mkSimVNode 9 (.charDev .generic) 0o600 1).data = .charDev .generic := rfl
            simp [hNotPath, hAcc, hNotExt, hInoEq, hIno9, hDyn9, hData9]
          · intro bs hEq; injection hEq with hB; rw [← hB]; exact Nat.zero_le _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        let cap := Nat.min maxBytes.toNat MAX_READ_BYTES.toNat
        let takeN := Nat.min cap (d.payload.size - d.offset)
        have hTakeLeAvail : takeN ≤ d.payload.size - d.offset := Nat.min_le_right _ _
        have hTakeLeCap : takeN ≤ cap := Nat.min_le_left _ _
        have hCapLeMax : cap ≤ maxBytes.toNat := Nat.min_le_left _ _
        have hIno8 : Files.assocGet (toSimFilesState s.simFds).inodes 8 = some (mkSimVNode 8 (.reg {}) 0o600 1) := rfl
        have hDyn : (mkSimVNode 8 (.reg {}) 0o600 1).isDynamic = true := rfl
        have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
        have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
        have hInoEq : (toSimOpenDesc d).ino = 8 := by simp [toSimOpenDesc, hRd, hHang]
        have hData8 : (mkSimVNode 8 (.reg {}) 0o600 1).data = .reg {} := rfl
        by_cases hZero : takeN == 0
        · simp only [takeN, cap] at hZero
          simp only [hZero, ↓reduceIte]
          refine ⟨?_, ?_⟩
          · rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
            rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep Files.verifyNondet
            dsimp only
            rw [hSomeF]
            simp [hNotPath, hAcc, hNotExt, hInoEq, hIno8, hDyn, hData8]
          · intro bs hEq; injection hEq with hB; rw [← hB]; exact Nat.zero_le _
        · have hZeroF : (Nat.min (Nat.min maxBytes.toNat MAX_READ_BYTES.toNat) (d.payload.size - d.offset) == 0) = false :=
            Bool.eq_false_iff.mpr hZero
          have hTakePos : 0 < takeN := Nat.pos_of_ne_zero (fun hz => hZero (beq_iff_eq.mpr hz))
          let chunk := d.payload.extract d.offset (d.offset + takeN)
          have hChunkSz : chunk.size = takeN := by
            change (d.payload.extract d.offset (d.offset + takeN)).size = takeN
            rw [ByteArray.size_extract]
            omega
          have hChunkLeCap : chunk.size ≤ cap := by
            rw [hChunkSz]
            exact hTakeLeCap
          have hChunkNe0 : (chunk.size == 0) = false :=
            beq_false_of_ne (by omega)
          simp only [hZeroF, Bool.false_eq_true, ↓reduceIte]
          refine ⟨?_, ?_⟩
          · rw [simFiles_healthyStep_nonClose s.simFds (.read hid maxBytes) _ (fun _ h => by cases h) (fun _ h => by cases h)]
            rw [evalReq_read_eq]; unfold Files.evalRead Files.verifyStep Files.verifyNondet
            dsimp only
            rw [hSomeF]
            simp only [hNotPath, hAcc, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hNotExt,
              hInoEq, hIno8, hData8, hDyn]
            dsimp only [chunk, takeN, cap] at hChunkNe0 hChunkLeCap
            have hCapEq : min maxBytes.toNat MAX_READ_BYTES.toNat = maxBytes.toNat.min MAX_READ_BYTES.toNat := by
              simp [Nat.min_def]
            rw [← hCapEq] at hChunkLeCap
            simp only [hChunkNe0, Bool.false_eq_true, ↓reduceIte, hChunkLeCap, toSimOpenDesc,
              hRd, hHang, Files.FilePos.offset]
            refine congrArg (fun x : Files.FilesState => some ({ state := x, eintrBudget := 0 } : Files.HealthyEnv)) ?_
            let newOff : Nat := d.offset +
              (d.payload.extract d.offset
                (d.offset + (maxBytes.toNat.min MAX_READ_BYTES.toNat).min (d.payload.size - d.offset))).size
            change { toSimFilesState s.simFds with
              fds :=
                match Files.assocGet (toSimFilesState s.simFds).fds hid with
                | none => (toSimFilesState s.simFds).fds
                | some target =>
                  match target.ofdId? with
                  | none => Files.assocSet (toSimFilesState s.simFds).fds hid
                      { target with pos := Files.FilePos.byteOffset newOff }
                  | some oid => (toSimFilesState s.simFds).fds.map fun (h, (d0 : Files.OpenDesc)) =>
                      if d0.ofdId? == some oid then
                        (h, { d0 with pos := Files.FilePos.byteOffset newOff })
                      else (h, d0) } = _
            rw [hSomeF]
            let dUpd : HealthySimFd :=
              { isReader := true, nonblock := d.nonblock, append := d.append,
                cloexec := d.cloexec, hangMode := false, offset := newOff, payload := d.payload }
            have hSetEq : Files.assocSet (toSimFilesState s.simFds).fds hid (toSimOpenDesc dUpd) =
                (Files.assocSet s.simFds hid dUpd).map (fun (k, v) => (k, toSimOpenDesc v)) :=
              assocSet_map_val s.simFds toSimOpenDesc hid dUpd
            dsimp only [toSimOpenDesc]
            simp only [hRd, hHang, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            dsimp only [dUpd] at hSetEq
            simp only [toSimOpenDesc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSetEq
            rw [hSetEq]
            rfl
          · intro bs hEq
            injection hEq with hB
            rw [← hB]
            exact Nat.le_trans (by rw [hChunkSz]; exact hTakeLeCap) hCapLeMax

private theorem simFiles_write_healthy (s : HealthySimState) (hid : Files.HandleId) (data : ByteArray)
    (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.write hid data).run s
    Files.healthyStep (projSimFiles s) (.write (id hid) data) (Files.outcomeOfU32 r.1) =
      some (projSimFiles r.2) ∧
    (∀ n, r.1 = .ok n → n.toNat ≤ data.size) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, id, Files.outcomeOfU32]
  cases hGet : Files.assocGet s.simFds hid with
  | none =>
    dsimp only
    have hNoneF : Files.assocGet (toSimFilesState s.simFds).fds hid = none := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    refine ⟨?_, (by intro _ h; cases h)⟩
    rw [simFiles_healthyStep_nonClose s.simFds (.write hid data) _ (fun _ h => by cases h) (fun _ h => by cases h)]
    rw [evalReq_write_eq]; unfold Files.evalWrite Files.verifyStep
    dsimp only
    rw [hNoneF]
    simp [Files.isOutcomeErr, Errno.isCriticalOsErrno, Errno.EBADF, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  | some d =>
    dsimp only
    have hSomeF : Files.assocGet (toSimFilesState s.simFds).fds hid = some (toSimOpenDesc d) := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    cases hRd : d.isReader with
    | true =>
      simp only [↓reduceIte]
      refine ⟨?_, (by intro _ h; cases h)⟩
      rw [simFiles_healthyStep_nonClose s.simFds (.write hid data) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_write_eq]; unfold Files.evalWrite Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
      have hAcc : ((toSimOpenDesc d).access == .rdonly) = true := by simp [toSimOpenDesc, hRd]; decide
      have hCrit9 : Errno.isCriticalOsErrno Errno.EBADF = false := by decide
      have hNeEi9 : (Errno.EBADF != Errno.EINTR) = true := by decide
      simp [hNotPath, hAcc, hCrit9, hNeEi9]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      let n := Nat.min data.size MAX_READ_BYTES.toNat
      have hNLeMax : n ≤ MAX_READ_BYTES.toNat := Nat.min_le_right _ _
      have hNLeData : n ≤ data.size := Nat.min_le_left _ _
      have hnLt : n < UInt32.size :=
        Nat.lt_of_le_of_lt hNLeMax (by decide)
      have hu32 : (UInt32.ofNat n).toNat = n := by
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt hnLt
      have hIno7 : Files.assocGet (toSimFilesState s.simFds).inodes 7 = some (mkSimVNode 7 (.charDev .nullDev) 0o666 1) := rfl
      refine ⟨?_, ?_⟩
      · rw [simFiles_healthyStep_nonClose s.simFds (.write hid data) _ (fun _ h => by cases h) (fun _ h => by cases h)]
        rw [evalReq_write_eq]; unfold Files.evalWrite Files.verifyStep Files.verifyNondet
        dsimp only
        rw [hSomeF]
        have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
        have hAcc : ((toSimOpenDesc d).access == .rdonly) = false := by simp [toSimOpenDesc, hRd]; decide
        have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
        have hInoEq : (toSimOpenDesc d).ino = 7 := by simp [toSimOpenDesc, hRd]
        have hPseudo : (mkSimVNode 7 (.charDev .nullDev) 0o666 1).isPseudo = false := rfl
        have hData7 : (mkSimVNode 7 (.charDev .nullDev) 0o666 1).data = .charDev .nullDev := rfl
        simp only [hNotPath, hAcc, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hNotExt,
          hInoEq, hIno7, hData7, hPseudo]
        dsimp only [n] at hu32
        rw [hu32]
        by_cases hEmpty : (data.size == 0) = true
        · have hd0 : data.size = 0 := beq_iff_eq.mp hEmpty
          have hn0 : data.size.min MAX_READ_BYTES.toNat = 0 :=
            Nat.eq_zero_of_le_zero (hd0 ▸ hNLeData)
          rw [ite_eq_left hEmpty, hn0]
          rfl
        · have hdPos : 1 ≤ data.size :=
            Nat.pos_of_ne_zero (fun hz => hEmpty (beq_iff_eq.mpr hz))
          have hMaxPos : 1 ≤ MAX_READ_BYTES.toNat := by decide
          have hDec1 : decide (data.size.min MAX_READ_BYTES.toNat ≥ 1) = true :=
            decide_eq_true (Nat.le_min.mpr ⟨hdPos, hMaxPos⟩)
          have hDec2 : decide (data.size.min MAX_READ_BYTES.toNat ≤ data.size) = true :=
            decide_eq_true hNLeData
          rw [ite_eq_right hEmpty, hDec1, hDec2]
          rfl
      · intro nOut hEq
        injection hEq with hN
        rw [← hN, hu32]
        exact hNLeData

private theorem simFiles_fstatat_healthy (s : HealthySimState) (dir : Option Files.HandleId)
    (path : ByteArray) (flags : Files.AtFlags) (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.fstatat dir path flags).run s
    Files.healthyStep (projSimFiles s) (.fstatat (dir.map id) path flags) (Files.outcomeOfStatted r.1) =
      some (projSimFiles r.2) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, Files.outcomeOfStatted]
  have hDirId : dir.map id = dir := by cases dir <;> rfl
  rw [hDirId]
  rw [simFiles_healthyStep_nonClose s.simFds (.fstatat dir path flags) _ (fun _ h => by cases h) (fun _ h => by cases h)]
  let fs := toSimFilesState s.simFds
  let req : Files.FilesReq := .fstatat dir path flags
  change (match Files.verifyStep fs (Files.evalReq fs req)
      (match match (Files.evalModel fs req).1 with
       | .statted st => Except.ok st
       | .err e => Except.error e
       | _ => Except.error Errno.EINVAL with
       | .ok st => Files.FilesOutcome.statted st
       | .error e => Files.FilesOutcome.err e) with
    | none => none
    | some s' => _) = _
  have hStatStep :
      ∃ out,
        (Files.evalModel fs req).1 = out ∧
        ((∃ st, out = .statted st) ∨ ∃ e, out = .err e ∧ Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
        Files.verifyStep fs (Files.evalReq fs req) out = some fs := by
    have hStatNodeOk : ∀ ino vn (ex : List Errno),
        Files.assocGet healthySimInodes ino = some vn →
        ∃ out,
          (Files.runNondetDefault fs (.statNode ino vn)).1 = out ∧
          ((∃ st, out = .statted st) ∨ ∃ e, out = .err e ∧ Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
          Files.verifyStep fs (.nondet (.statNode ino vn) ex) out = some fs := by
      intro ino vn ex hIno
      have hFix := healthySimInodes_stat_fixed ino vn hIno
      have hChk := healthySimInodes_checkStatMatch s.simFds ino vn hIno
      let st := Files.mkStatFromVNode ino vn
      let vnUpd : Files.VNode :=
        { vn with kernelId := { dev? := some st.dev, ino? := some st.ino, allowAlias := vn.kernelId.allowAlias } }
      have hFsSet : { fs with inodes := Files.assocSet fs.inodes ino vnUpd } = fs := by
        dsimp only [fs, toSimFilesState, st, vnUpd]
        rw [hFix]
      refine ⟨.statted st, rfl, Or.inl ⟨st, rfl⟩, ?_⟩
      unfold Files.verifyStep Files.verifyNondet
      dsimp only [fs, st, vnUpd] at hChk hFsSet ⊢
      rw [hChk]
      simp only [↓reduceIte]
      exact congrArg some hFsSet
    have hCore : ∀ res, res = Files.evalReq fs req →
        ∃ out,
          (match res with
            | .wrapperErr e => (Files.FilesOutcome.err e, fs)
            | .err e _ st? => (Files.FilesOutcome.err e, st?.getD fs)
            | .ok o next _ => (o, next)
            | .nondet act _ => Files.runNondetDefault fs act).1 = out ∧
          ((∃ st, out = .statted st) ∨ ∃ e, out = .err e ∧ Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
          Files.verifyStep fs res out = some fs := by
      intro res hR
      dsimp only [req, Files.evalReq, Files.precheckNul] at hR
      rcases eq_if_cases hR with hR | hR
      · subst hR
        exact ⟨.err Errno.EINVAL, rfl, Or.inr ⟨Errno.EINVAL, rfl, by decide, by decide⟩,
          by simp [Files.verifyStep, Files.isOutcomeErr]⟩
      · rcases eq_if_cases hR with hR | hR
        · subst hR
          exact ⟨.err Errno.EINVAL, rfl, Or.inr ⟨Errno.EINVAL, rfl, by decide, by decide⟩,
            by simp [Files.verifyStep, Files.isOutcomeErr]⟩
        · rcases eq_if_cases hR with hR | hR
          · subst hR
            exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
              by simp [Files.verifyStep, Files.isOutcomeErr]⟩
          · rcases eq_if_cases hR with hR | hR
            · subst hR
              exact ⟨.err Errno.ENOTDIR, rfl, Or.inr ⟨Errno.ENOTDIR, rfl, by decide, by decide⟩,
                by simp [Files.verifyStep, Files.verifyNondet, Errno.ENOTDIR, Errno.EFAULT]⟩
            · unfold Files.evalStat at hR
              dsimp only at hR
              split at hR
              · subst hR
                exact ⟨.err Errno.EINVAL, rfl, Or.inr ⟨Errno.EINVAL, rfl, by decide, by decide⟩,
                  by simp [Files.verifyStep, Files.isOutcomeErr]⟩
              · split at hR
                · cases dir with
                  | none =>
                    dsimp only at hR
                    cases hIno : Files.assocGet fs.inodes fs.cwdIno with
                    | none =>
                      rw [hIno] at hR; subst hR
                      exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
                        by simp [Files.verifyStep]⟩
                    | some vn =>
                      rw [hIno] at hR; subst hR
                      exact hStatNodeOk fs.cwdIno vn [] hIno
                  | some hid =>
                    dsimp only at hR
                    cases hG : Files.assocGet fs.fds hid with
                    | none =>
                      rw [hG] at hR; dsimp only at hR; subst hR
                      exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
                        by simp [Files.verifyStep]⟩
                    | some d =>
                      rw [hG] at hR; dsimp only at hR
                      cases hIno : Files.assocGet fs.inodes d.ino with
                      | none =>
                        rw [hIno] at hR; subst hR
                        exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
                          by simp [Files.verifyStep]⟩
                      | some vn =>
                        rw [hIno] at hR; subst hR
                        exact hStatNodeOk d.ino vn [] hIno
                · cases hResL : Files.resolveLookupOrExt fs dir path (!flags.symlinkNofollow) with
                  | error re =>
                    rw [hResL] at hR; subst hR
                    exact ⟨.err re, rfl,
                      Or.inr ⟨re, rfl, resolvePath_err_nonCritical s.simFds dir path (!flags.symlinkNofollow) re hResL⟩,
                      by simp [Files.verifyStep]⟩
                  | ok opt =>
                    rw [hResL] at hR
                    cases opt with
                    | none =>
                      subst hR
                      exact ⟨.err Errno.ENOTDIR, rfl, Or.inr ⟨Errno.ENOTDIR, rfl, by decide, by decide⟩,
                        by simp [Files.verifyStep, Files.verifyNondet, Errno.ENOTDIR, Errno.EFAULT]⟩
                    | some tup =>
                      rcases tup with ⟨ino, _, _⟩
                      dsimp only at hR
                      cases hIno : Files.assocGet fs.inodes ino with
                      | none =>
                        rw [hIno] at hR; subst hR
                        exact ⟨.err Errno.ENOENT, rfl, Or.inr ⟨Errno.ENOENT, rfl, by decide, by decide⟩,
                          by simp [Files.verifyStep]⟩
                      | some vn =>
                        rw [hIno] at hR; subst hR
                        exact hStatNodeOk ino vn [] hIno
    obtain ⟨out, hOut, hKind, hVer⟩ := hCore (Files.evalReq fs req) rfl
    refine ⟨out, ?_, hKind, hVer⟩
    unfold Files.evalModel
    exact hOut
  rcases hStatStep with ⟨out, hOutEq, hKind, hVer⟩
  rw [hOutEq]
  rcases hKind with ⟨st, rfl⟩ | ⟨e, rfl, hCrit, hNeEi⟩
  · dsimp only
    rw [hVer]
  · dsimp only
    rw [hVer]
    simp only [bne, hCrit, beq_false_of_ne hNeEi, Bool.not_false, Bool.and_self, ↓reduceIte]
    rfl

private theorem simFiles_faccessat_healthy (s : HealthySimState) (dir : Option Files.HandleId)
    (path : ByteArray) (mask : Files.AccessModeMask) (flags : Files.AtFlags)
    (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.faccessat dir path mask flags).run s
    Files.healthyStep (projSimFiles s) (.faccessat (dir.map id) path mask flags) (Files.outcomeOfUnit r.1) =
      some (projSimFiles r.2) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, Files.outcomeOfUnit]
  have hDirId : dir.map id = dir := by cases dir <;> rfl
  rw [hDirId]
  rw [simFiles_healthyStep_nonClose s.simFds (.faccessat dir path mask flags) _ (fun _ h => by cases h) (fun _ h => by cases h)]
  let fs := toSimFilesState s.simFds
  let req : Files.FilesReq := .faccessat dir path mask flags
  change (match Files.verifyStep fs (Files.evalReq fs req)
      (match match (Files.evalModel fs req).1 with
       | .unit => Except.ok ()
       | .err e => Except.error e
       | _ => Except.error Errno.EINVAL with
       | .ok () => Files.FilesOutcome.unit
       | .error e => Files.FilesOutcome.err e) with
    | none => none
    | some s' => _) = _
  have hAccStep :
      ∃ out,
        (Files.evalModel fs req).1 = out ∧
        (out = .unit ∨ ∃ e, out = .err e ∧ Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
        Files.verifyStep fs (Files.evalReq fs req) out = some fs := by
    have hCore : ∀ res, res = Files.evalReq fs req →
        ∃ out,
          (match res with
            | .wrapperErr e => (Files.FilesOutcome.err e, fs)
            | .err e _ st? => (Files.FilesOutcome.err e, st?.getD fs)
            | .ok o next _ => (o, next)
            | .nondet act _ => Files.runNondetDefault fs act).1 = out ∧
          (out = .unit ∨ ∃ e, out = .err e ∧ Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
          Files.verifyStep fs res out = some fs := by
      intro res hR
      dsimp only [req, Files.evalReq, Files.precheckNul] at hR
      rcases eq_if_cases hR with hR | hR
      · subst hR
        exact ⟨.err Errno.EINVAL, rfl, Or.inr ⟨Errno.EINVAL, rfl, by decide, by decide⟩,
          by simp [Files.verifyStep, Files.isOutcomeErr]⟩
      · rcases eq_if_cases hR with hR | hR
        · subst hR
          exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
            by simp [Files.verifyStep, Files.isOutcomeErr]⟩
        · rcases eq_if_cases hR with hR | hR
          · subst hR
            exact ⟨.err Errno.ENOTDIR, rfl, Or.inr ⟨Errno.ENOTDIR, rfl, by decide, by decide⟩,
              by simp [Files.verifyStep, Files.verifyNondet, Errno.ENOTDIR, Errno.EFAULT]⟩
          · unfold Files.evalAccess at hR
            dsimp only at hR
            by_cases hEmp : (path.size == 0 && flags.emptyPath) = true
            · rw [ite_eq_left hEmp] at hR
              cases dir with
              | none =>
                dsimp only at hR
                cases hIno : Files.assocGet fs.inodes fs.cwdIno with
                | none =>
                  rw [hIno] at hR; subst hR
                  exact ⟨.err Errno.ENOENT, rfl, Or.inr ⟨Errno.ENOENT, rfl, by decide, by decide⟩,
                    by simp [Files.verifyStep]⟩
                | some vn =>
                  rw [hIno] at hR; dsimp only at hR
                  repeat (first
                    | (subst hR; exact ⟨.unit, rfl, Or.inl rfl, by simp [Files.verifyStep, Files.outcomeEq]⟩)
                    | (subst hR; exact ⟨.err _, rfl, Or.inr ⟨_, rfl, by decide, by decide⟩, by simp [Files.verifyStep]⟩)
                    | split at hR)
              | some hid =>
                dsimp only at hR
                cases hG : Files.assocGet fs.fds hid with
                | none =>
                  rw [hG] at hR; dsimp only at hR; subst hR
                  exact ⟨.err Errno.EBADF, rfl, Or.inr ⟨Errno.EBADF, rfl, by decide, by decide⟩,
                    by simp [Files.verifyStep]⟩
                | some d =>
                  rw [hG] at hR; dsimp only at hR
                  cases hIno : Files.assocGet fs.inodes d.ino with
                  | none =>
                    rw [hIno] at hR; subst hR
                    exact ⟨.err Errno.ENOENT, rfl, Or.inr ⟨Errno.ENOENT, rfl, by decide, by decide⟩,
                      by simp [Files.verifyStep]⟩
                  | some vn =>
                    rw [hIno] at hR; dsimp only at hR
                    repeat (first
                      | (subst hR; exact ⟨.unit, rfl, Or.inl rfl, by simp [Files.verifyStep, Files.outcomeEq]⟩)
                      | (subst hR; exact ⟨.err _, rfl, Or.inr ⟨_, rfl, by decide, by decide⟩, by simp [Files.verifyStep]⟩)
                      | split at hR)
            · rw [ite_eq_right hEmp] at hR
              cases hResL : Files.resolveLookupOrExt fs dir path (!flags.symlinkNofollow) with
              | error re =>
                rw [hResL] at hR
                dsimp only [Functor.map, Except.map] at hR
                subst hR
                exact ⟨.err re, rfl,
                  Or.inr ⟨re, rfl, resolvePath_err_nonCritical s.simFds dir path (!flags.symlinkNofollow) re hResL⟩,
                  by simp [Files.verifyStep]⟩
              | ok opt =>
                rw [hResL] at hR
                dsimp only [Functor.map, Except.map] at hR
                cases opt with
                | none =>
                  dsimp only [Option.map] at hR
                  subst hR
                  exact ⟨.err Errno.ENOTDIR, rfl, Or.inr ⟨Errno.ENOTDIR, rfl, by decide, by decide⟩,
                    by simp [Files.verifyStep, Files.verifyNondet, Errno.ENOTDIR, Errno.EFAULT]⟩
                | some tup =>
                  rcases tup with ⟨ino, _, _⟩
                  dsimp only [Option.map] at hR
                  cases hIno : Files.assocGet fs.inodes ino with
                  | none =>
                    rw [hIno] at hR; subst hR
                    exact ⟨.err Errno.ENOENT, rfl, Or.inr ⟨Errno.ENOENT, rfl, by decide, by decide⟩,
                      by simp [Files.verifyStep]⟩
                  | some vn =>
                    rw [hIno] at hR; dsimp only at hR
                    repeat (first
                      | (subst hR; exact ⟨.unit, rfl, Or.inl rfl, by simp [Files.verifyStep, Files.outcomeEq]⟩)
                      | (subst hR; exact ⟨.err _, rfl, Or.inr ⟨_, rfl, by decide, by decide⟩, by simp [Files.verifyStep]⟩)
                      | split at hR)
    obtain ⟨out, hOut, hKind, hVer⟩ := hCore (Files.evalReq fs req) rfl
    refine ⟨out, ?_, hKind, hVer⟩
    unfold Files.evalModel
    exact hOut
  rcases hAccStep with ⟨out, hOutEq, hKind, hVer⟩
  rw [hOutEq]
  rcases hKind with rfl | ⟨e, rfl, hCrit, hNeEi⟩
  · dsimp only; rw [hVer]
  · dsimp only; rw [hVer]; simp only [bne, hCrit, beq_false_of_ne hNeEi, Bool.not_false, Bool.and_self, ↓reduceIte]; rfl

private theorem simFiles_fcntl_healthy (s : HealthySimState) (hid : Files.HandleId) (cmd : Files.FcntlCmd)
    (_ : (projSimFiles s).wf = true) :
    let r := (healthySimDeps.files.fcntl hid cmd).run s
    Files.healthyStep (projSimFiles s) (.fcntl (id hid) cmd) (Files.outcomeOfU32 r.1) =
      some (projSimFiles r.2) := by
  dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, id, Files.outcomeOfU32]
  cases hGet : Files.assocGet s.simFds hid with
  | none =>
    dsimp only
    have hNoneF : Files.assocGet (toSimFilesState s.simFds).fds hid = none := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid cmd) _ (fun _ h => by cases h) (fun _ h => by cases h)]
    rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
    dsimp only
    rw [hNoneF]
    simp [Files.isOutcomeErr, Errno.isCriticalOsErrno, Errno.EBADF, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  | some d =>
    dsimp only
    have hSomeF : Files.assocGet (toSimFilesState s.simFds).fds hid = some (toSimOpenDesc d) := by
      simp [toSimFilesState, assocGet_map_toSimOpenDesc, hGet]
    cases cmd with
    | getFl =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid .getFl) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
      simp [hNotExt, Files.outcomeEq]
    | setFl nb ap =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid (.setFl nb ap)) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
      simp only [hNotPath, Bool.false_eq_true, ↓reduceIte, Files.outcomeEq]
      change some (Files.HealthyEnv.mk
        { toSimFilesState s.simFds with
           fds :=
             match Files.assocGet (toSimFilesState s.simFds).fds hid with
             | none => (toSimFilesState s.simFds).fds
             | some target =>
               match target.ofdId? with
               | none => Files.assocSet (toSimFilesState s.simFds).fds hid { target with nonblock := nb, append := ap }
               | some oid => (toSimFilesState s.simFds).fds.map fun (h, (d0 : Files.OpenDesc)) =>
                   if d0.ofdId? == some oid then (h, { d0 with nonblock := nb, append := ap }) else (h, d0) }
        0) = _
      rw [hSomeF]
      dsimp only [toSimOpenDesc]
      refine congrArg (fun x : Files.FilesState => some ({ state := x, eintrBudget := 0 } : Files.HealthyEnv)) ?_
      have hSetEq : Files.assocSet (toSimFilesState s.simFds).fds hid
          (toSimOpenDesc { d with nonblock := nb, append := ap }) =
          (Files.assocSet s.simFds hid { d with nonblock := nb, append := ap }).map
            (fun (k, v) => (k, toSimOpenDesc v)) :=
        assocSet_map_val s.simFds toSimOpenDesc hid { d with nonblock := nb, append := ap }
      change { toSimFilesState s.simFds with
        fds := Files.assocSet (toSimFilesState s.simFds).fds hid (toSimOpenDesc { d with nonblock := nb, append := ap }) } = _
      rw [hSetEq]
      rfl
    | getFd =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid .getFd) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      simp [toSimOpenDesc, Files.outcomeEq]
    | setFd clo =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid (.setFd clo)) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      simp only [Files.outcomeEq]
      refine congrArg (fun x : Files.FilesState => some ({ state := x, eintrBudget := 0 } : Files.HealthyEnv)) ?_
      have hSetEq : Files.assocSet (toSimFilesState s.simFds).fds hid
          (toSimOpenDesc { d with cloexec := clo }) =
          (Files.assocSet s.simFds hid { d with cloexec := clo }).map
            (fun (k, v) => (k, toSimOpenDesc v)) :=
        assocSet_map_val s.simFds toSimOpenDesc hid { d with cloexec := clo }
      change { toSimFilesState s.simFds with
        fds := Files.assocSet (toSimFilesState s.simFds).fds hid (toSimOpenDesc { d with cloexec := clo }) } = _
      rw [hSetEq]
      rfl
    | addSeals seals =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid (.addSeals seals)) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
      have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
      have hCrit1 : Errno.isCriticalOsErrno Errno.EPERM = false := by decide
      have hNeEi1 : (Errno.EPERM != Errno.EINTR) = true := by decide
      have hCrit22 : Errno.isCriticalOsErrno Errno.EINVAL = false := by decide
      have hNeEi22 : (Errno.EINVAL != Errno.EINTR) = true := by decide
      simp only [hNotPath, hNotExt, Bool.false_eq_true, ↓reduceIte]
      cases hRd : d.isReader
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hAcc : ((toSimOpenDesc d).access == .rdonly) = false := by simp [toSimOpenDesc, hRd]; decide
        have hInoEq : (toSimOpenDesc d).ino = 7 := by simp [toSimOpenDesc, hRd]
        have hIno7 : Files.assocGet (toSimFilesState s.simFds).inodes 7 = some (mkSimVNode 7 (.charDev .nullDev) 0o666 1) := rfl
        have hData7 : (mkSimVNode 7 (.charDev .nullDev) 0o666 1).data = .charDev .nullDev := rfl
        rw [hInoEq, hIno7]
        dsimp only
        rw [hAcc]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hBad : ((seals &&& ~~~(0x3f : UInt32)) != 0) = true
        · rw [hBad]
          simp [hCrit22, hNeEi22]
        · have hBadF : ((seals &&& ~~~(0x3f : UInt32)) != 0) = false := Bool.eq_false_iff.mpr hBad
          rw [hBadF]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hData7]
          simp [hCrit22, hNeEi22]
      · simp only [↓reduceIte]
        have hAcc : ((toSimOpenDesc d).access == .rdonly) = true := by simp [toSimOpenDesc, hRd]; decide
        cases hHang : d.hangMode
        · have hInoEq : (toSimOpenDesc d).ino = 8 := by simp [toSimOpenDesc, hRd, hHang]
          have hIno8 : Files.assocGet (toSimFilesState s.simFds).inodes 8 = some (mkSimVNode 8 (.reg {}) 0o600 1) := rfl
          simp [hAcc, hInoEq, hIno8, hCrit1, hNeEi1]
        · have hInoEq : (toSimOpenDesc d).ino = 9 := by simp [toSimOpenDesc, hRd, hHang]
          have hIno9 : Files.assocGet (toSimFilesState s.simFds).inodes 9 = some (mkSimVNode 9 (.charDev .generic) 0o600 1) := rfl
          simp [hAcc, hInoEq, hIno9, hCrit1, hNeEi1]
    | getSeals =>
      dsimp only
      rw [simFiles_healthyStep_nonClose s.simFds (.fcntl hid .getSeals) _ (fun _ h => by cases h) (fun _ h => by cases h)]
      rw [evalReq_fcntl_eq]; unfold Files.evalFcntl Files.verifyStep
      dsimp only
      rw [hSomeF]
      have hNotPath : (toSimOpenDesc d).isPathFd = false := rfl
      have hNotExt : (toSimOpenDesc d).isExternalStdio = false := rfl
      have hCrit22 : Errno.isCriticalOsErrno Errno.EINVAL = false := by decide
      have hNeEi22 : (Errno.EINVAL != Errno.EINTR) = true := by decide
      simp only [hNotPath, hNotExt, Bool.false_eq_true, ↓reduceIte]
      cases hRd : d.isReader
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have hInoEq : (toSimOpenDesc d).ino = 7 := by simp [toSimOpenDesc, hRd]
        have hIno7 : Files.assocGet (toSimFilesState s.simFds).inodes 7 = some (mkSimVNode 7 (.charDev .nullDev) 0o666 1) := rfl
        have hData7 : (mkSimVNode 7 (.charDev .nullDev) 0o666 1).data = .charDev .nullDev := rfl
        simp [hInoEq, hIno7, hData7, hCrit22, hNeEi22]
      · cases hHang : d.hangMode
        · simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
          have hInoEq : (toSimOpenDesc d).ino = 8 := by simp [toSimOpenDesc, hRd, hHang]
          have hIno8 : Files.assocGet (toSimFilesState s.simFds).inodes 8 = some (mkSimVNode 8 (.reg {}) 0o600 1) := rfl
          have hData8 : (mkSimVNode 8 (.reg {}) 0o600 1).data = .reg {} := rfl
          have hSup : (!(mkSimVNode 8 (.reg {}) 0o600 1).isPseudo &&
              (Files.mountProfileOf (toSimFilesState s.simFds) (mkSimVNode 8 (.reg {}) 0o600 1).mountId).supportsSeals) = true := rfl
          rw [hInoEq, hIno8]
          dsimp only
          rw [hData8, hSup]
          simp [Files.outcomeEq]
        · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          have hInoEq : (toSimOpenDesc d).ino = 9 := by simp [toSimOpenDesc, hRd, hHang]
          have hIno9 : Files.assocGet (toSimFilesState s.simFds).inodes 9 = some (mkSimVNode 9 (.charDev .generic) 0o600 1) := rfl
          have hData9 : (mkSimVNode 9 (.charDev .generic) 0o600 1).data = .charDev .generic := rfl
          simp [hInoEq, hIno9, hData9, hCrit22, hNeEi22]


/-- `healthySimDeps.files` refines canonical `Files.healthyStep` (excluding `.close`/`EBUSY`) via `projSimFiles`. -/
theorem healthySimDeps_files_refinesHealthy :
    RefinesHealthyFilesOpsAt projSimFiles id healthySimDeps.files where
  close_healthy := simFiles_close_healthy
  read_healthy := simFiles_read_healthy
  write_healthy := simFiles_write_healthy
  fstatat_healthy := simFiles_fstatat_healthy
  faccessat_healthy := simFiles_faccessat_healthy
  fcntl_healthy := simFiles_fcntl_healthy

end LeanSwe.Process.Proofs
