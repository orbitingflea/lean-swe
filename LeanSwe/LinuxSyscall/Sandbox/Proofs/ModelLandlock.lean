import LeanSwe.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

@[local simp] private theorem st_pure {α : Type} (a : α) (s : SandboxSysState) :
    StateT.pure (m := Id) a s = (a, s) := rfl

@[local simp] private theorem st_bind {α β : Type} (m : StateT SandboxSysState Id α)
    (f : α → StateT SandboxSysState Id β) (s : SandboxSysState) :
    StateT.bind m f s = let p := m s; f p.1 p.2 := rfl

@[local simp] private theorem st_set (s' s : SandboxSysState) :
    StateT.set (m := Id) s' s = ((), s') := rfl

@[local simp] private theorem st_get (s : SandboxSysState) :
    StateT.get (m := Id) s = (s, s) := rfl

private theorem assocGet_of_all_lt {α : Type} :
    ∀ (l : List (Nat × α)) (n : Nat),
      l.all (fun p => decide (p.1 < n)) = true → assocGet l n = none
  | [], _, _ => rfl
  | (k, _) :: rest, n, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold assocGet
    have hne : (k == n) = false := beq_false_of_ne (Nat.ne_of_lt h.1)
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact assocGet_of_all_lt rest n h.2

private theorem assocSet_all_lt {α : Type} :
    ∀ (l : List (Nat × α)) (k : Nat) (v : α) (m : Nat),
      l.all (fun p => decide (p.1 < m)) = true → k < m →
      (assocSet l k v).all (fun p => decide (p.1 < m)) = true
  | [], k, v, m, _, hk => by simp [assocSet, hk]
  | (a, b) :: rest, k, v, m, h, hk => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold assocSet
    by_cases heq : (a == k)
    · simp only [heq, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hk, h.2⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, assocSet_all_lt rest k v m h.2 hk⟩

private theorem all_lt_mono {α : Type} :
    ∀ (l : List (Nat × α)) {a b : Nat},
      l.all (fun p => decide (p.1 < a)) = true → a ≤ b →
      l.all (fun p => decide (p.1 < b)) = true
  | [], _, _, _, _ => rfl
  | (k, _) :: rest, a, b, h, hab => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 hab, all_lt_mono rest h.2 hab⟩

/-- Extract descriptor-key bound from `SandboxSysState.wf`. -/
theorem wf_fds_of_wf (s : SandboxSysState) (hwf : s.wf = true) :
    s.fds.all (fun p => decide (p.1 < s.nextHid)) = true := by
  unfold SandboxSysState.wf at hwf
  exact (Bool.and_eq_true _ _ |>.mp hwf).1

/-- Extract minimum Landlock ABI invariant from `SandboxSysState.wf`. -/
theorem wf_abi_of_wf (s : SandboxSysState) (hwf : s.wf = true) :
    (match s.landlockAbi? with | none => true | some v => decide (v ≥ 4)) = true := by
  unfold SandboxSysState.wf at hwf
  exact (Bool.and_eq_true _ _ |>.mp hwf).2

/-- `SandboxSysState.wf` transfers across states sharing `fds`, `nextHid`, and `landlockAbi?`. -/
theorem wf_congr {a b : SandboxSysState} (hf : a.fds = b.fds)
    (hn : a.nextHid = b.nextHid) (hl : a.landlockAbi? = b.landlockAbi?)
    (ha : a.wf = true) : b.wf = true := by
  unfold SandboxSysState.wf at ha ⊢; rw [← hf, ← hn, ← hl]; exact ha

/-- `SandboxSysState.wf` is invariant under setting `landlockEnabled := true`. -/
theorem wf_with_enabled (s : SandboxSysState) (hwf : s.wf = true) :
    ({ s with landlockEnabled := true }).wf = true :=
  wf_congr rfl rfl rfl hwf

private theorem wf_pinPassed (s : SandboxSysState) (hwf : s.wf = true) :
    (pinPassedNnpGate s).wf = true := by
  unfold SandboxSysState.wf at hwf ⊢
  unfold pinPassedNnpGate
  by_cases h1 : (s.noNewPrivs? == some false) <;> by_cases h2 : (s.hasCapSysAdmin? == some false) <;>
    simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;> exact hwf

private theorem wf_restrict_pin (s : SandboxSysState) (hwf : s.wf = true) (layers : Nat) :
    ({ pinPassedNnpGate s with landlockEnabled := true, landlockLayers := layers }).wf = true := by
  have hp := wf_pinPassed s hwf
  unfold SandboxSysState.wf at hp ⊢
  exact hp

private theorem wf_restrict_nopin (s : SandboxSysState) (hwf : s.wf = true) (layers : Nat) :
    ({ s with landlockEnabled := true, landlockLayers := layers }).wf = true := by
  unfold SandboxSysState.wf at hwf ⊢
  exact hwf

/-- `s.nextHid` is always fresh in a well-formed `SandboxSysState`. -/
theorem assocGet_nextHid_none (s : SandboxSysState) (hwf : s.wf = true) :
    assocGet s.fds s.nextHid = none :=
  assocGet_of_all_lt s.fds s.nextHid (wf_fds_of_wf s hwf)

/-- Inserting at `s.nextHid` and bumping `nextHid` preserves descriptor-key well-formedness. -/
theorem assocSet_nextHid_all_lt (s : SandboxSysState) (d : SandboxFdDesc)
    (hwf : s.wf = true) :
    (assocSet s.fds s.nextHid d).all
      (fun p => decide (p.1 < Nat.max s.nextHid (s.nextHid + 1))) = true := by
  have h1 := all_lt_mono s.fds (wf_fds_of_wf s hwf) (Nat.le_max_left s.nextHid (s.nextHid + 1))
  have h2 : s.nextHid < Nat.max s.nextHid (s.nextHid + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self s.nextHid) (Nat.le_max_right s.nextHid (s.nextHid + 1))
  exact assocSet_all_lt s.fds s.nextHid d _ h1 h2

private theorem ui64_and_assoc (a b c : UInt64) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, Nat.and_assoc]

private theorem mask_not_v4_of_not_known (fs : UInt64) (abi : UInt32)
    (h : (fs &&& ~~~landlockKnownFsMask abi) != 0) :
    (fs &&& ~~~LANDLOCK_ACCESS_FS_V4_ALL) != 0 := by
  simp only [bne_iff_ne, ne_eq] at h ⊢
  unfold landlockKnownFsMask at h
  split at h
  · exact h
  · split at h
    · have hSub : ~~~(((1 : UInt64) <<< 16) - 1) =
          ~~~LANDLOCK_ACCESS_FS_V4_ALL &&& ~~~(((1 : UInt64) <<< 16) - 1) := by decide
      intro hz
      apply h
      rw [hSub, ← ui64_and_assoc, hz]
      decide
    · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
          ~~~LANDLOCK_ACCESS_FS_V4_ALL &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
      intro hz
      apply h
      rw [hSub, ← ui64_and_assoc, hz]
      decide

private theorem mask_known_to_9 (fs : UInt64) (abi : UInt32)
    (h : (fs &&& ~~~landlockKnownFsMask abi) = 0) :
    (fs &&& ~~~landlockKnownFsMask 9) = 0 := by
  unfold landlockKnownFsMask at h ⊢
  simp only [show ¬((9 : UInt32) ≤ 4) by decide, show ¬((9 : UInt32) ≤ 8) by decide, ↓reduceIte]
  split at h
  · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
        ~~~(((1 : UInt64) <<< 15) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
    rw [hSub, ← ui64_and_assoc, h]; decide
  · split at h
    · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
          ~~~(((1 : UInt64) <<< 16) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
      rw [hSub, ← ui64_and_assoc, h]; decide
    · exact h

/-- Helper showing seccomp filter interception permits safe non-`EFAULT` errnos. -/
theorem allowedStep_seccomp_err (s : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hGuard : failsPureWrapperGuard req = false)
    (hSec : s.seccompMayIntercept = true)
    (hNe : e ≠ Errno.EFAULT) (hLo : 1 ≤ e.toNat) (hHi : e.toNat ≤ 4095) :
    allowedStep s req (.err e) = some s := by
  unfold allowedStep
  simp [hGuard, hSec, bne_iff_ne, hNe, hLo, hHi]

/-- Helper linking `modelOps` NNP failure condition to `allowedStepCore`. -/
theorem nnp_fail_iff {nnp? capA? : Option Bool}
    (h : (!(nnp?.getD false) && !(capA?.getD false)) = true) :
    (nnp? != some true && capA? != some true) = true := by
  cases nnp? <;> cases capA? <;> simp_all

/-- Helper linking `modelOps` NNP pass condition to `allowedStepCore`. -/
theorem nnp_pass_iff {nnp? capA? : Option Bool}
    (h : (!(nnp?.getD false) && !(capA?.getD false)) = false) :
    !(nnp? == some false && capA? == some false) = true := by
  cases nnp? with
  | none => simp_all
  | some a => cases a <;> cases capA? <;> simp_all

private theorem effectiveAbi_lt4_implies_none (s : SandboxSysState) (hwf : s.wf = true)
    (hLt : effectiveModelLandlockAbi s < 4) :
    s.landlockAbi? = none ∧ hasLandlockEvidence s = false := by
  unfold effectiveModelLandlockAbi at hLt
  have hAbi := wf_abi_of_wf s hwf
  cases hOpt : s.landlockAbi? with
  | some v =>
    rw [hOpt] at hLt hAbi
    simp only [decide_eq_true_eq] at hAbi
    have : ¬(v < 4) := UInt32.not_lt.mpr hAbi
    exact absurd hLt this
  | none =>
    rw [hOpt] at hLt
    refine ⟨rfl, ?_⟩
    cases hEv : hasLandlockEvidence s
    · rfl
    · simp only [hEv, Bool.and_true] at hLt
      by_cases hDef : s.defaultLandlockAbi < 4
      · have hDec : decide (s.defaultLandlockAbi < 4) = true := decide_eq_true hDef
        simp only [hDec, ↓reduceIte] at hLt
        exact absurd hLt (by decide)
      · have hDec : decide (s.defaultLandlockAbi < 4) = false := decide_eq_false hDef
        simp only [hDec, Bool.false_eq_true, ↓reduceIte] at hLt
        exact absurd hLt hDef

private theorem allowedStep_guard_err_eq (s : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hGuard : failsPureWrapperGuard req = true)
    (hCore : allowedStepCore s req (.err e) = some s) :
    allowedStep s req (.err e) = some s := by
  unfold allowedStep
  simp [hGuard, hCore]

private theorem allowedStep_err_eq (s : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hGuard : failsPureWrapperGuard req = false)
    (hEf : e ≠ Errno.EFAULT) (hRng : 1 ≤ e.toNat ∧ e.toNat ≤ 4095)
    (hCore : s.seccompMayIntercept = false → allowedStepCore s req (.err e) = some s) :
    allowedStep s req (.err e) = some s := by
  unfold allowedStep
  cases hSec : s.seccompMayIntercept
  · simp [hGuard, hCore hSec]
  · simp [hGuard, hEf, hRng]

private theorem enosys_ne_efault : Errno.ENOSYS ≠ Errno.EFAULT := by decide
private theorem emfile_ne_efault : Errno.EMFILE ≠ Errno.EFAULT := by decide

/-- `modelOps.landlockCreateRuleset` refines `allowedStep` and preserves `wf`. -/
theorem refine_landlockCreateRuleset (s : SandboxSysState) (hwf : s.wf = true)
    (attr? : Option LandlockRulesetAttr) (flags : UInt32) :
    let r := (execSandboxReq modelOps (.landlockCreateRuleset attr? flags)).run s
    allowedStep s (.landlockCreateRuleset attr? flags) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  cases attr? with
  | none =>
    by_cases hFl0 : flags == 0
    · simp only [hFl0, ↓reduceIte]
      exact ⟨allowedStep_guard_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl0])
        (by simp [allowedStepCore, hFl0, Errno.EINVAL, Errno.EFAULT]), hwf⟩
    · by_cases hLt4 : effectiveModelLandlockAbi s < 4
      · have ⟨_, hNoEv⟩ := effectiveAbi_lt4_implies_none s hwf hLt4
        simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4]
        refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl0]) (by decide) (by decide) ?_, hwf⟩
        intro _
        simp [allowedStepCore, hFl0, hNoEv, enosys_ne_efault]
      · have hGe4 : effectiveModelLandlockAbi s ≥ 4 := UInt32.not_lt.mp hLt4
        by_cases hVer : flags == LANDLOCK_CREATE_RULESET_VERSION
        · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer]
          cases hOpt : s.landlockAbi? with
          | none =>
            simp [allowedStep, allowedStepCore, hVer, hOpt, hGe4]
            unfold SandboxSysState.wf
            simp [wf_fds_of_wf s hwf, decide_eq_true hGe4]
          | some prev =>
            have hEq : effectiveModelLandlockAbi s = prev := by simp [effectiveModelLandlockAbi, hOpt]
            have hPrevGe4 : 4 ≤ prev := by rw [← hEq]; exact hGe4
            simp [allowedStep, allowedStepCore, hVer, hOpt, hEq, hPrevGe4]
            unfold SandboxSysState.wf
            simp [wf_fds_of_wf s hwf, decide_eq_true hPrevGe4]
        · by_cases hErr : flags == LANDLOCK_CREATE_RULESET_ERRATA
          · by_cases hLt6 : effectiveModelLandlockAbi s < 6
            · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer, hErr, hLt6]
              refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl0]) (by decide) (by decide) ?_, hwf⟩
              intro _
              cases hOpt : s.landlockAbi? with
              | none => simp [allowedStepCore, hVer, hErr, Errno.EINVAL, Errno.EFAULT, hOpt]
              | some a =>
                have ha : a < 6 := by simpa [effectiveModelLandlockAbi, hOpt] using hLt6
                simp [allowedStepCore, hVer, hErr, Errno.EINVAL, Errno.EFAULT, hOpt, ha]
            · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer, hErr, hLt6]
              refine ⟨?_, wf_with_enabled s hwf⟩
              cases hOpt : s.landlockAbi? with
              | none => simp [allowedStep, allowedStepCore, hVer, hErr, hOpt]
              | some a =>
                have ha : ¬(a < 6) := by simpa [effectiveModelLandlockAbi, hOpt] using hLt6
                simp [allowedStep, allowedStepCore, hVer, hErr, hOpt, ha]
          · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer, hErr]
            refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl0]) (by decide) (by decide) ?_, hwf⟩
            intro _
            simp [allowedStepCore, hVer, hErr, Errno.EINVAL, Errno.EFAULT]
  | some attr =>
    by_cases hFl : flags != 0
    · simp only [hFl, ↓reduceIte]
      exact ⟨allowedStep_guard_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl])
        (by simp [allowedStepCore, hFl, Errno.EINVAL, Errno.EFAULT]), hwf⟩
    · have hFl0 : flags == 0 := by simpa using hFl
      by_cases hLt4 : effectiveModelLandlockAbi s < 4
      · have ⟨hNone, hNoEv⟩ := effectiveAbi_lt4_implies_none s hwf hLt4
        simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4]
        refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
        intro _
        simp [allowedStepCore, hFl, hNoEv, hNone, enosys_ne_efault]
      · by_cases hEmpty : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
        · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty]
          refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
          intro _
          simp [allowedStepCore, hFl, hEmpty, ENOMSG, Errno.EFAULT]
        · by_cases hNet : (attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0
          · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet]
            refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
            intro _
            simp [allowedStepCore, hFl, hEmpty, hNet, Errno.EINVAL, Errno.EFAULT]
          · by_cases hFs : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) != 0
            · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs]
              refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
              intro _
              simp only [allowedStepCore, hFl, Bool.false_eq_true, ↓reduceIte, hEmpty, hNet]
              cases hOpt : s.landlockAbi? with
              | none =>
                have hv4 := mask_not_v4_of_not_known attr.handledAccessFs (effectiveModelLandlockAbi s) hFs
                simp [hv4, Errno.EINVAL, Errno.EFAULT]
              | some abi =>
                have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                rw [hEq] at hFs
                simp [hFs, Errno.EINVAL, Errno.EFAULT]
            · by_cases hEmf : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = true
              · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs, hEmf]
                refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
                intro _
                simp only [allowedStepCore, hFl, Bool.false_eq_true, ↓reduceIte, hEmpty, hNet]
                cases hOpt : s.landlockAbi? with
                | none => simp [Errno.isTransientOsErrno, emfile_ne_efault]
                | some abi => simp [Errno.isTransientOsErrno, emfile_ne_efault]
              · have hNoneHid := assocGet_nextHid_none s hwf
                have hEmfF : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = false := by
                  simpa using hEmf
                have hFds' := assocSet_nextHid_all_lt s
                  { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true } hwf
                have hAbi' := wf_abi_of_wf s hwf
                have hWf' : ({ s with
                    fds := assocSet s.fds s.nextHid
                      { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true },
                    nextHid := Nat.max s.nextHid (s.nextHid + 1),
                    landlockEnabled := true } : SandboxSysState).wf = true := by
                  unfold SandboxSysState.wf
                  exact Bool.and_eq_true _ _ |>.mpr ⟨hFds', hAbi'⟩
                simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs, hEmf]
                refine ⟨?_, hWf'⟩
                cases hOpt : s.landlockAbi? with
                | none =>
                  have hFs9 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask 9) = 0 := by
                    have hRaw : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) = 0 := by
                      cases h1 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) == 0
                      · simp_all
                      · simpa using h1
                    exact mask_known_to_9 attr.handledAccessFs (effectiveModelLandlockAbi s) hRaw
                  cases hSec : s.seccompMayIntercept <;>
                    simp [allowedStep, allowedStepCore, hFl, hEmpty, hNet, hNoneHid, hEmfF, hOpt, hFs9, hSec,
                      Nat.max_eq_right (Nat.le_succ s.nextHid)]
                | some abi =>
                  have hFsA : (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) = 0 := by
                    have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                    cases h1 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) == 0
                    · simp only [bne_iff_ne, ne_eq] at hFs
                      rw [← hEq] at h1
                      simp_all
                    · simpa using h1
                  cases hSec : s.seccompMayIntercept <;>
                    simp [allowedStep, allowedStepCore, hFl, hEmpty, hNet, hNoneHid, hEmfF, hOpt, hFsA, hSec,
                      Nat.max_eq_right (Nat.le_succ s.nextHid)]

/-- `modelOps.landlockAddRule` refines `allowedStep` and preserves `wf`. -/
theorem refine_landlockAddRule (s : SandboxSysState) (hwf : s.wf = true)
    (ruleset : HandleId) (rule : LandlockRule HandleId) :
    let r := (execSandboxReq modelOps (.landlockAddRule ruleset rule)).run s
    allowedStep s (.landlockAddRule ruleset rule) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  by_cases hLt4 : effectiveModelLandlockAbi s < 4
  · have ⟨_, hNoEv⟩ := effectiveAbi_lt4_implies_none s hwf hLt4
    simp only [hLt4, ↓reduceIte]
    refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
    intro _
    simp [allowedStepCore, hNoEv, enosys_ne_efault]
  · simp only [hLt4, ↓reduceIte]
    cases hRs : assocGet s.fds ruleset with
    | none =>
      refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
      intro _
      simp [allowedStepCore, hRs, Errno.EBADF, Errno.EFAULT]
    | some rsDesc =>
      by_cases hOp : rsDesc.oPath
      · simp only [hOp, ↓reduceIte]
        refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
        intro _
        simp [allowedStepCore, hRs, hOp, Errno.EBADF, Errno.EFAULT]
      · rcases rsDesc with ⟨rsKind, rsClo, rsOp⟩
        dsimp only at hOp
        simp only [Bool.not_eq_true] at hOp
        subst hOp
        cases hKind : rsKind with
        | memfd _ _ | hostPath _ | pseudoFs =>
          refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
          intro _
          simp [allowedStepCore, hRs, hKind, EBADFD, Errno.EFAULT]
        | landlockRuleset handledFs handledNet =>
          cases rule with
          | pathBeneath parentHid allowedAccess =>
            by_cases hZero : allowedAccess == 0
            · simp only [hZero]
              refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
              intro _
              simp [allowedStepCore, hRs, hKind, hZero, ENOMSG, Errno.EFAULT]
            · by_cases hUnh : (allowedAccess &&& ~~~handledFs) != 0
              · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh]
                refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                intro _
                simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EFAULT]
              · cases hPar : assocGet s.fds parentHid with
                | none =>
                  simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar]
                  refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                  intro _
                  simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, Errno.EBADF, Errno.EFAULT]
                | some pDesc =>
                  rcases pDesc with ⟨pKind, pClo, pOp⟩
                  cases hPK : pKind with
                  | landlockRuleset _ _ | memfd _ _ | pseudoFs =>
                    simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK]
                    refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                    intro _
                    simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, EBADFD, Errno.EFAULT]
                  | hostPath isDir =>
                    by_cases hDirErr : (!isDir && (allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0) = true
                    · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK, hDirErr]
                      refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                      intro _
                      simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, hDirErr, Errno.EINVAL, Errno.EFAULT]
                    · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK, hDirErr]
                      refine ⟨?_, hwf⟩
                      cases hSec : s.seccompMayIntercept <;>
                        simp [allowedStep, allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, hDirErr, hSec]
          | netPort port allowedAccess =>
            by_cases hZero : allowedAccess == 0
            · simp only [hZero]
              refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
              intro _
              simp [allowedStepCore, hRs, hKind, hZero, ENOMSG, Errno.EFAULT]
            · by_cases hUnh : ((allowedAccess &&& ~~~handledNet) != 0 || port > 65535) = true
              · have hBad : (allowedAccess &&& ~~~handledNet) != 0 ∨ port > 65535 := by
                  simpa [Bool.or_eq_true] using hUnh
                rcases hBad with hA | hP
                · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA]
                  refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                  intro _
                  simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EFAULT]
                · by_cases hA : (allowedAccess &&& ~~~handledNet) != 0
                  · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA]
                    refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                    intro _
                    simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EFAULT]
                  · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA, hP]
                    refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
                    intro _
                    simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EFAULT]
              · have hA : ((allowedAccess &&& ~~~handledNet) != 0) = false := by
                  cases h1 : (allowedAccess &&& ~~~handledNet) != 0 <;> simp_all
                have hP : ¬(port > 65535) := by
                  intro hp; simp [hp] at hUnh
                simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA, hP]
                refine ⟨?_, hwf⟩
                cases hSec : s.seccompMayIntercept <;>
                  simp [allowedStep, allowedStepCore, hRs, hKind, hZero, hUnh, hSec]

/-- `modelOps.landlockRestrictSelf` refines `allowedStep` and preserves `wf`. -/
theorem refine_landlockRestrictSelf (s : SandboxSysState) (hwf : s.wf = true)
    (ruleset : HandleId) :
    let r := (execSandboxReq modelOps (.landlockRestrictSelf ruleset)).run s
    allowedStep s (.landlockRestrictSelf ruleset) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  by_cases hLt4 : effectiveModelLandlockAbi s < 4
  · have ⟨_, hNoEv⟩ := effectiveAbi_lt4_implies_none s hwf hLt4
    simp only [hLt4, ↓reduceIte]
    refine ⟨allowedStep_err_eq s _ _ rfl (by decide) (by decide) ?_, hwf⟩
    intro _
    simp [allowedStepCore, hNoEv, enosys_ne_efault]
  · by_cases hGate : (!(s.noNewPrivs?.getD false) && !(s.hasCapSysAdmin?.getD false)) = true
    · have hFail := nnp_fail_iff hGate
      simp only [hLt4, ↓reduceIte, hGate]
      cases hSec : s.seccompMayIntercept
      · refine ⟨?_, by
          simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure, pinFailedNnpGate]
          unfold SandboxSysState.wf
          exact Bool.and_eq_true _ _ |>.mpr ⟨wf_fds_of_wf s hwf, wf_abi_of_wf s hwf⟩⟩
        simp [allowedStep, failsPureWrapperGuard, allowedStepCore, canFailNnpGate, hFail, hSec,
          Errno.EPERM, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
      · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
        simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.EPERM ≠ Errno.EFAULT by decide,
          show 1 ≤ Errno.EPERM.toNat ∧ Errno.EPERM.toNat ≤ 4095 by decide]
    · have hGateF : (!(s.noNewPrivs?.getD false) && !(s.hasCapSysAdmin?.getD false)) = false :=
        Bool.eq_false_iff.mpr hGate
      have hPassT : canPassNnpGate s = true := by
        unfold canPassNnpGate
        cases h1 : s.noNewPrivs? with
        | none => simp
        | some a => cases a <;> cases h2 : s.hasCapSysAdmin? <;> simp_all
      simp only [hLt4, ↓reduceIte, hGateF]
      cases hRs : assocGet s.fds ruleset with
      | none =>
        cases hSec : s.seccompMayIntercept
        · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_pinPassed s hwf⟩
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hSec,
            Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EPERM, Errno.EFAULT]
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.EBADF ≠ Errno.EFAULT by decide,
            show 1 ≤ Errno.EBADF.toNat ∧ Errno.EBADF.toNat ≤ 4095 by decide]
      | some desc =>
        by_cases hOp : desc.oPath
        · simp only [hOp, ↓reduceIte]
          cases hSec : s.seccompMayIntercept
          · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_pinPassed s hwf⟩
            simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hOp, hSec,
              Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EPERM, Errno.EFAULT]
          · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
            simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.EBADF ≠ Errno.EFAULT by decide,
              show 1 ≤ Errno.EBADF.toNat ∧ Errno.EBADF.toNat ≤ 4095 by decide]
        · rcases desc with ⟨dKind, dClo, dOp⟩
          dsimp only at hOp
          simp only [Bool.not_eq_true] at hOp
          subst hOp
          cases hKind : dKind with
          | memfd _ _ | hostPath _ | pseudoFs =>
            have hE1 : EBADFD ≠ Errno.EOPNOTSUPP := by decide
            have hE2 : EBADFD ≠ Errno.ENOSYS := by decide
            have hE3 : EBADFD ≠ Errno.EPERM := by decide
            have hE4 : EBADFD ≠ Errno.EFAULT := by decide
            cases hSec : s.seccompMayIntercept
            · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_pinPassed s hwf⟩
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hKind, hSec,
                hE1, hE2, hE3, hE4]
            · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
              simp [allowedStep, failsPureWrapperGuard, hSec, hE4,
                show 1 ≤ EBADFD.toNat ∧ EBADFD.toNat ≤ 4095 by decide]
          | landlockRuleset _ _ =>
            by_cases hCap : s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS
            · simp only [hCap, ↓reduceIte]
              cases hSec : s.seccompMayIntercept
              · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_pinPassed s hwf⟩
                simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hKind, hCap, hSec,
                  Errno.E2BIG, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EPERM, Errno.EFAULT]
              · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
                simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.E2BIG ≠ Errno.EFAULT by decide,
                  show 1 ≤ Errno.E2BIG.toNat ∧ Errno.E2BIG.toNat ≤ 4095 by decide]
            · simp only [hCap, ↓reduceIte]
              cases hSec : s.seccompMayIntercept
              · refine ⟨?_, wf_restrict_pin s hwf (s.landlockLayers + 1)⟩
                simp [allowedStep, allowedStepCore, hPassT, hCap, hRs, hKind, hSec]
              · refine ⟨?_, wf_restrict_pin s hwf (s.landlockLayers + 1)⟩
                simp [allowedStep, allowedStepCore, hPassT, hCap, hRs, hKind, hSec]

end LeanSwe.LinuxSyscall.Sandbox
