import LeanSwe.LinuxSyscall.Sandbox.Proofs.ModelLandlock

namespace LeanSwe.LinuxSyscall.Sandbox

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

private theorem wf_pinFailed_misc (s : SandboxSysState) (hwf : s.wf = true)
    (hNp : s.passedNnpGate = false) :
    (pinFailedNnpGate s).wf = true := by
  exact wf_mk (wf_fds_of_wf s hwf) (by simp [pinFailedNnpGate, hNp]) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)

private theorem wf_pinPassed_misc (s : SandboxSysState) (hwf : s.wf = true) :
    (pinPassedNnpGate s).wf = true := by
  unfold pinPassedNnpGate
  by_cases ht : (s.noNewPrivs? == some true || s.hasCapSysAdmin? == some true) = true
  · simp only [ht, ↓reduceIte]; exact hwf
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : (s.noNewPrivs? == some false) = true
    · simp only [h1, ↓reduceIte]
      exact wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (s.hasCapSysAdmin? == some false) = true
      · simp only [h3, ↓reduceIte]
        exact wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        exact wf_mk (wf_fds_of_wf s hwf) (by simp [h1, h3]) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)

private theorem rlimit_tighten_of_gt (st : RlimitState) (max : UInt64)
    (h : st.hardUpper < max) :
    { st with hardUpper := if st.hardUpper ≤ max - 1 then st.hardUpper else max - 1 } = st := by
  have h1 : st.hardUpper.toNat < max.toNat := h
  have hPos : (1 : UInt64) ≤ max := by
    change (1 : UInt64).toNat ≤ max.toNat
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have hLe : st.hardUpper ≤ max - 1 := by
    change st.hardUpper.toNat ≤ (max - 1).toNat
    rw [UInt64.toNat_sub_of_le _ _ hPos]
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  simp [hLe]

private theorem setRlimit_getRlimit_self (s : SandboxSysState) (res : RlimitResource) :
    s.setRlimit res (s.getRlimit res) = s := by
  cases res <;> rfl

/-- `modelOps.seccomp` refines `allowedStep` and preserves `wf`. -/
theorem refine_seccomp (s : SandboxSysState) (hwf : s.wf = true)
    (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray) :
    let r := (execSandboxReq modelOps (.seccomp op flags filterBytes)).run s
    allowedStep s (.seccomp op flags filterBytes) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  cases op with
  | getActionAvail action =>
    by_cases hFl : flags.toBits != 0
    · simp only [hFl, ↓reduceIte]
      refine ⟨?_, hwf⟩
      simp [hFl, allowedStep, failsPureWrapperGuard, allowedStepCore, show Errno.EINVAL ≠ Errno.EFAULT by decide]
    · have hFl0 : flags.toBits == 0 := by simpa using hFl
      by_cases hKnown : isKnownSeccompAction action
      · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hKnown]
        have hWfSec : ({ s with seccompEnabled := true }).wf = true := by
          unfold SandboxSysState.wf at hwf ⊢; exact hwf
        refine ⟨?_, hWfSec⟩
        cases hSec : s.seccompMayIntercept <;>
          simp [allowedStep, allowedStepCore, hFl0, hKnown, hSec]
      · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hKnown]
        have hWfSec : ({ s with seccompEnabled := true }).wf = true :=
          wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
        cases hSec : s.seccompMayIntercept
        · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfSec⟩
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFl, hKnown, hSec,
            show Errno.EOPNOTSUPP ≠ Errno.EFAULT by decide]
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          exact allowedStep_seccomp_err s _ Errno.EOPNOTSUPP (by simp [failsPureWrapperGuard, hFl])
            hSec (by decide) (by decide) (by decide)
  | setModeFilter =>
    have hSz : filterBytes.data.size = filterBytes.size := rfl
    by_cases hGuard : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = true
    · have hGuard' : (!isValidSeccompFilterByteLen filterBytes.size || !hasSafeSeccompRetBytes filterBytes) = true := hGuard
      simp only [hGuard, ↓reduceIte]
      refine ⟨?_, hwf⟩
      simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGuard', show Errno.EINVAL ≠ Errno.EFAULT by decide]
    · have hGuardF : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = false := by
        simpa using hGuard
      have hGuardOk : (isValidSeccompFilterByteLen filterBytes.size = true ∧ hasSafeSeccompRetBytes filterBytes = true) := by
        cases hV : isValidSeccompFilterByteLen filterBytes.size <;> cases hS : hasSafeSeccompRetBytes filterBytes <;>
          simp_all
      by_cases hWk : flags.waitKillableRecv = true
      · simp only [hGuardF, Bool.false_eq_true, ↓reduceIte, hWk]
        have hWfSec : ({ s with seccompEnabled := true }).wf = true :=
          wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
        cases hSec : s.seccompMayIntercept
        · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfSec⟩
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGuardOk, hWk, hSec,
            show Errno.EINVAL ≠ Errno.EFAULT by decide]
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hGuardOk])
            hSec (by decide) (by decide) (by decide)
      · have hWkF : flags.waitKillableRecv = false := Bool.eq_false_iff.mpr hWk
        by_cases hGate : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
              !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = true
        · have hFail := nnpGate_fail_iff hwf hGate
          have hNp : s.passedNnpGate = false := by unfold canFailNnpGate at hFail; simp_all
          simp only [hGuardF, Bool.false_eq_true, ↓reduceIte, hWkF, hGate]
          cases hSec : s.seccompMayIntercept
          · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_pinFailed_misc s hwf hNp⟩
            simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGuardOk, hWkF, hFail, hSec,
              show Errno.EACCES ≠ Errno.ENOSYS by decide,
              show Errno.EACCES ≠ Errno.EFAULT by decide]
          · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
            exact allowedStep_seccomp_err s _ Errno.EACCES (by simp [failsPureWrapperGuard, hGuardOk])
              hSec (by decide) (by decide) (by decide)
        · have hGateF : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
              !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = false :=
            Bool.eq_false_iff.mpr hGate
          have hPassC := nnpGate_pass_iff hwf hGateF
          have hWfPassSec : ({ pinPassedNnpGate s with seccompEnabled := true } : SandboxSysState).wf = true := by
            have hp := wf_pinPassed_misc s hwf
            exact wf_mk (wf_fds_of_wf _ hp) (wf_nnpGate_of_wf _ hp) (wf_maxAbi_of_wf _ hp) (wf_abi_of_wf _ hp)
          simp only [hGuardF, Bool.false_eq_true, ↓reduceIte, hWkF, hGateF]
          cases hDec : decodeSockFilters filterBytes with
          | none =>
            cases hSec : s.seccompMayIntercept
            · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfPassSec⟩
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGuardOk, hWkF, hPassC, hDec, hSec,
                show Errno.EINVAL ≠ Errno.ENOSYS by decide,
                show Errno.EINVAL ≠ Errno.EACCES by decide,
                show Errno.EINVAL ≠ Errno.EFAULT by decide]
            · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
              exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hGuardOk])
                hSec (by decide) (by decide) (by decide)
          | some prog =>
            by_cases hBpf : checkSeccompBpf prog
            · have hWfS : ({ pinPassedNnpGate s with
                  seccompEnabled := true
                  seccompFilters := s.seccompFilters + 1
                  seccompMayIntercept := s.seccompMayIntercept || !isAllowOnlySeccompFilter prog }).wf = true := by
                have hp := wf_pinPassed_misc s hwf
                exact wf_mk (wf_fds_of_wf _ hp) (wf_nnpGate_of_wf _ hp) (wf_maxAbi_of_wf _ hp) (wf_abi_of_wf _ hp)
              simp only [hBpf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              refine ⟨?_, hWfS⟩
              cases hSec : s.seccompMayIntercept <;>
                simp [allowedStep, allowedStepCore, hGuardOk, hWkF, hPassC, hDec, hBpf, hSec]
            · simp only [hBpf, Bool.not_false, ↓reduceIte]
              cases hSec : s.seccompMayIntercept
              · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfPassSec⟩
                simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGuardOk, hWkF, hPassC, hDec, hBpf, hSec,
                  show Errno.EINVAL ≠ Errno.ENOSYS by decide,
                  show Errno.EINVAL ≠ Errno.EACCES by decide,
                  show Errno.EINVAL ≠ Errno.EFAULT by decide]
              · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
                exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hGuardOk])
                  hSec (by decide) (by decide) (by decide)

/-- `modelOps.prctl` refines `allowedStep` and preserves `wf`. -/
theorem refine_prctl (s : SandboxSysState) (hwf : s.wf = true) (op : PrctlOp) :
    let r := (execSandboxReq modelOps (.prctl op)).run s
    allowedStep s (.prctl op) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  cases op with
  | setNoNewPrivs =>
    have hWf' : ({ s with noNewPrivs? := some true }).wf = true :=
      wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
    refine ⟨?_, hWf'⟩
    cases hSec : s.seccompMayIntercept <;> simp [allowedStep, allowedStepCore, hSec]
  | getNoNewPrivs =>
    have h2 := wf_nnpGate_of_wf s hwf
    cases hp : s.passedNnpGate <;> cases hNnp : s.noNewPrivs? with
    | none =>
      cases hCap : s.hasCapSysAdmin? with
      | none =>
        refine ⟨?_, wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)⟩
        cases hSec : s.seccompMayIntercept <;> simp [allowedStep, allowedStepCore, hp, hNnp, hCap, hSec]
      | some c =>
        cases c <;>
          (refine ⟨?_, wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)⟩;
           cases hSec : s.seccompMayIntercept <;> simp [allowedStep, allowedStepCore, hp, hNnp, hCap, hSec])
    | some b =>
      cases b <;> cases hCap : s.hasCapSysAdmin? <;>
        (try rename_i c; cases c) <;>
        (try simp_all) <;>
        (refine ⟨?_, wf_mk (wf_fds_of_wf s hwf) (by simp_all) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)⟩;
         cases hSec : s.seccompMayIntercept <;> simp_all [allowedStep, allowedStepCore])
  | setChildSubreaper enable =>
    have hWf' : ({ s with childSubreaper := enable }).wf = true := by
      unfold SandboxSysState.wf at hwf ⊢; exact hwf
    refine ⟨?_, hWf'⟩
    cases hSec : s.seccompMayIntercept <;> simp [allowedStep, allowedStepCore, hSec]
  | setPdeathsig sig =>
    by_cases hGt : sig > MAX_LINUX_SIGNAL
    · simp only [hGt, ↓reduceIte]
      refine ⟨?_, hwf⟩
      cases hSec : s.seccompMayIntercept
      · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hGt, hSec,
          show Errno.EINVAL ≠ Errno.EFAULT by decide]
      · exact allowedStep_seccomp_err s _ Errno.EINVAL (by rfl) hSec (by decide) (by decide) (by decide)
    · have hLe : sig ≤ MAX_LINUX_SIGNAL := UInt32.not_lt.mp hGt
      have hWf' : ({ s with pdeathsig := sig }).wf = true := by
        unfold SandboxSysState.wf at hwf ⊢; exact hwf
      simp only [hGt, ↓reduceIte]
      refine ⟨?_, hWf'⟩
      cases hSec : s.seccompMayIntercept <;> simp [allowedStep, allowedStepCore, hLe, hSec]

private theorem setrlimit_hardUpper_lt_self (s : SandboxSysState) (res : RlimitResource) (b : Bool) :
    (({ s with hasCapSysResource? := some b } : SandboxSysState).setRlimit res (s.getRlimit res)) =
      { s with hasCapSysResource? := some b } := by
  cases res <;> rfl

private theorem refine_setrlimit_core_or_fsize (s : SandboxSysState) (hwf : s.wf = true)
    (res : RlimitResource) (hNotNf : res ≠ .nofile) (cur max : UInt64) :
    let r := (execSandboxReq modelOps (.setrlimit res cur max)).run s
    allowedStep s (.setrlimit res cur max) r.1 = some r.2 ∧ r.2.wf = true := by
  have hBeqF : (res == .nofile) = false := by cases res <;> simp_all <;> decide
  have hBneT : (res != .nofile) = true := by cases res <;> simp_all <;> decide
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  by_cases hCur : cur > max
  · simp only [hCur, ↓reduceIte]
    refine ⟨?_, hwf⟩
    cases hSec : s.seccompMayIntercept
    · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hSec,
        show Errno.EINVAL ≠ Errno.EFAULT by decide]
    · exact allowedStep_seccomp_err s _ Errno.EINVAL (by rfl) hSec (by decide) (by decide) (by decide)
  · by_cases hPerm : (!(s.hasCapSysResource?.getD false) && decide (max > (s.getRlimit res).hardUpper)) = true
    · have hParts := Bool.and_eq_true _ _ |>.mp hPerm
      have hCapF : s.hasCapSysResource?.getD false = false := by simpa using hParts.1
      have hMaxH : max > (s.getRlimit res).hardUpper := by simpa using hParts.2
      simp only [hCur, hBeqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        hCapF, Bool.not_false, hMaxH, decide_true, Bool.true_and]
      cases hSec : s.seccompMayIntercept
      · have hWf' : ({ s with hasCapSysResource? := some false }).wf = true := by
          unfold SandboxSysState.wf at hwf ⊢; exact hwf
        simp only [Bool.not_false, ↓reduceIte]
        refine ⟨?_, hWf'⟩
        have hTight := rlimit_tighten_of_gt (s.getRlimit res) max hMaxH
        have hTight' : ∀ st : RlimitState, st = s.getRlimit res →
            { cur := st.cur, hardUpper := if (s.getRlimit res).hardUpper ≤ max - 1 then (s.getRlimit res).hardUpper else max - 1,
              curExact := st.curExact, hardExact := st.hardExact } = s.getRlimit res := by
          intro st hst; subst hst; exact hTight
        cases hC : s.hasCapSysResource? with
        | none =>
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hBeqF, hBneT, hC, hSec, hMaxH,
            show Errno.EPERM ≠ Errno.EFAULT by decide]
          rw [hTight' _ rfl]; cases res <;> rfl
        | some b =>
          cases b
          · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hBeqF, hBneT, hC, hSec, hMaxH,
              show Errno.EPERM ≠ Errno.EFAULT by decide]
            rw [hTight' _ rfl]; cases res <;> rfl
          · rw [hC] at hCapF; cases hCapF
      · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
        exact allowedStep_seccomp_err s _ Errno.EPERM (by rfl) hSec (by decide) (by decide) (by decide)
    · have hPermF : (!(s.hasCapSysResource?.getD false) && decide (max > (s.getRlimit res).hardUpper)) = false := by
        simpa using hPerm
      have hWf' : (({ s with hasCapSysResource? :=
          if max > (s.getRlimit res).hardUpper then some true else s.hasCapSysResource? }).setRlimit
          res { cur := cur, hardUpper := max, curExact := true, hardExact := true }).wf = true := by
        unfold SandboxSysState.wf
        cases res <;> exact hwf
      simp only [hCur, hBeqF, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hPermF]
      refine ⟨?_, hWf'⟩
      cases hC : s.hasCapSysResource? with
      | none =>
        have hN : ¬(max > (s.getRlimit res).hardUpper) := by simp_all
        cases hSec : s.seccompMayIntercept <;>
          simp [allowedStep, allowedStepCore, hCur, hBeqF, hC, hSec, hN]
      | some b =>
        cases b
        · have hN : ¬(max > (s.getRlimit res).hardUpper) := by simp_all
          cases hSec : s.seccompMayIntercept <;>
            simp [allowedStep, allowedStepCore, hCur, hBeqF, hC, hSec, hN]
        · cases hSec : s.seccompMayIntercept <;>
            simp [allowedStep, allowedStepCore, hCur, hBeqF, hC, hSec]

private theorem refine_setrlimit_nofile (s : SandboxSysState) (hwf : s.wf = true)
    (cur max : UInt64) :
    let r := (execSandboxReq modelOps (.setrlimit .nofile cur max)).run s
    allowedStep s (.setrlimit .nofile cur max) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  have hNfEq : (RlimitResource.nofile == RlimitResource.nofile) = true := by decide
  have hNfNe : (RlimitResource.nofile != RlimitResource.nofile) = false := by decide
  by_cases hCur : cur > max
  · simp only [hCur, ↓reduceIte]
    refine ⟨?_, hwf⟩
    cases hSec : s.seccompMayIntercept
    · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hSec,
        show Errno.EINVAL ≠ Errno.EFAULT by decide]
    · exact allowedStep_seccomp_err s _ Errno.EINVAL (by rfl) hSec (by decide) (by decide) (by decide)
  · by_cases hMaxC : max > s.nofileNrOpenCeil
    · simp only [hCur, hNfEq, hMaxC, decide_true, Bool.true_and, ↓reduceIte]
      refine ⟨?_, hwf⟩
      cases hSec : s.seccompMayIntercept
      · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hNfEq, hMaxC, hSec,
          show Errno.EPERM ≠ Errno.EFAULT by decide]
      · exact allowedStep_seccomp_err s _ Errno.EPERM (by rfl) hSec (by decide) (by decide) (by decide)
    · by_cases hPerm : (!(s.hasCapSysResource?.getD false) && decide (max > (s.getRlimit .nofile).hardUpper)) = true
      · have hParts := Bool.and_eq_true _ _ |>.mp hPerm
        have hCapF : s.hasCapSysResource?.getD false = false := by simpa using hParts.1
        have hMaxH : max > (s.getRlimit .nofile).hardUpper := by simpa using hParts.2
        simp only [hCur, hNfEq, hMaxC, decide_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          hCapF, Bool.not_false, hMaxH, decide_true]
        cases hSec : s.seccompMayIntercept
        · simp only [Bool.not_false, ↓reduceIte]
          cases hC : s.hasCapSysResource? with
          | none =>
            have hWf' : ({ s with nofileNrOpenCeil :=
                if s.nofileNrOpenCeil ≤ max - 1 then s.nofileNrOpenCeil else max - 1 }).wf = true := by
              unfold SandboxSysState.wf at hwf ⊢; exact hwf
            refine ⟨?_, hWf'⟩
            simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hNfEq, hNfNe, hMaxC, hMaxH, hC, hSec,
              show Errno.EPERM ≠ Errno.EFAULT by decide]
          | some b =>
            cases b
            · have hWf' : ({ s with hasCapSysResource? := some false }).wf = true := by
                unfold SandboxSysState.wf at hwf ⊢; exact hwf
              refine ⟨?_, hWf'⟩
              have hTight := rlimit_tighten_of_gt (s.getRlimit .nofile) max hMaxH
              have hTight' : ∀ st : RlimitState, st = s.getRlimit .nofile →
                  { cur := st.cur, hardUpper := if (s.getRlimit .nofile).hardUpper ≤ max - 1 then (s.getRlimit .nofile).hardUpper else max - 1,
                    curExact := st.curExact, hardExact := st.hardExact } = s.getRlimit .nofile := by
                intro st hst; subst hst; exact hTight
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hCur, hNfEq, hNfNe, hMaxC, hC, hSec, hMaxH,
                show Errno.EPERM ≠ Errno.EFAULT by decide]
              rw [hTight' _ rfl, setRlimit_getRlimit_self]
              cases s; simp_all
            · rw [hC] at hCapF; cases hCapF
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          exact allowedStep_seccomp_err s _ Errno.EPERM (by rfl) hSec (by decide) (by decide) (by decide)
      · have hPermF : (!(s.hasCapSysResource?.getD false) && decide (max > (s.getRlimit .nofile).hardUpper)) = false := by
          simpa using hPerm
        have hWf' : (({ s with hasCapSysResource? :=
            if max > (s.getRlimit .nofile).hardUpper then some true else s.hasCapSysResource? }).setRlimit
            .nofile { cur := cur, hardUpper := max, curExact := true, hardExact := true }).wf = true := by
          unfold SandboxSysState.wf; exact hwf
        simp only [hCur, hNfEq, hMaxC, decide_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hPermF]
        refine ⟨?_, hWf'⟩
        cases hC : s.hasCapSysResource? with
        | none =>
          have hN : ¬(max > (s.getRlimit .nofile).hardUpper) := by simp_all
          cases hSec : s.seccompMayIntercept <;>
            simp [allowedStep, allowedStepCore, hCur, hNfEq, hMaxC, hC, hSec, hN]
        | some b =>
          cases b
          · have hN : ¬(max > (s.getRlimit .nofile).hardUpper) := by simp_all
            cases hSec : s.seccompMayIntercept <;>
              simp [allowedStep, allowedStepCore, hCur, hNfEq, hMaxC, hC, hSec, hN]
          · cases hSec : s.seccompMayIntercept <;>
              simp [allowedStep, allowedStepCore, hCur, hNfEq, hMaxC, hC, hSec]

/-- `modelOps.setrlimit` refines `allowedStep` and preserves `wf`. -/
theorem refine_setrlimit (s : SandboxSysState) (hwf : s.wf = true)
    (res : RlimitResource) (cur max : UInt64) :
    let r := (execSandboxReq modelOps (.setrlimit res cur max)).run s
    allowedStep s (.setrlimit res cur max) r.1 = some r.2 ∧ r.2.wf = true := by
  cases res with
  | core => exact refine_setrlimit_core_or_fsize s hwf .core (by decide) cur max
  | fsize => exact refine_setrlimit_core_or_fsize s hwf .fsize (by decide) cur max
  | nofile => exact refine_setrlimit_nofile s hwf cur max

/-- `modelOps.memfdCreate` refines `allowedStep` and preserves `wf`. -/
theorem refine_memfdCreate (s : SandboxSysState) (hwf : s.wf = true)
    (name : ByteArray) (flags : MemfdFlags) :
    let r := (execSandboxReq modelOps (.memfdCreate name flags)).run s
    allowedStep s (.memfdCreate name flags) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [execSandboxReq, modelOps]
  dsimp only [StateT.run, Pure.pure, Bind.bind, get, getThe, MonadStateOf.get, set]
  dsimp only [StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Id.run]
  dsimp only [StateT.bind, StateT.pure, Pure.pure, Bind.bind, Id.run]
  have hSz : name.data.size = name.size := rfl
  by_cases hBadName : (hasEmbeddedNul name || decide (name.data.size > MFD_NAME_MAX)) = true
  · have hBadName' : (hasEmbeddedNul name || decide (name.size > MFD_NAME_MAX)) = true := hBadName
    simp only [hBadName, ↓reduceIte]
    refine ⟨?_, hwf⟩
    simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hBadName',
      show Errno.EINVAL ≠ Errno.EFAULT by decide]
  · have hBadNameF : (hasEmbeddedNul name || decide (name.data.size > MFD_NAME_MAX)) = false := by
      simpa using hBadName
    have hNameOk : hasEmbeddedNul name = false ∧ name.size ≤ MFD_NAME_MAX := by
      cases hN : hasEmbeddedNul name with
      | false =>
        simp only [hN, Bool.false_or, decide_eq_false_iff_not, Nat.not_lt] at hBadNameF
        exact ⟨rfl, hBadNameF⟩
      | true => simp [hN] at hBadNameF
    have hNotOver : ¬(MFD_NAME_MAX < name.size) := Nat.not_lt.mpr hNameOk.2
    by_cases hConf : (flags.noexecSeal && flags.exec) = true
    · simp only [hBadNameF, Bool.false_eq_true, ↓reduceIte, hConf]
      have hWfMem : ({ s with memfdEnabled := true }).wf = true :=
        wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
      cases hSec : s.seccompMayIntercept
      · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfMem⟩
        simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hNameOk, hNotOver, hConf, hSec,
          show Errno.EINVAL ≠ Errno.EFAULT by decide]
      · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
        exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hNameOk])
          hSec (by decide) (by decide) (by decide)
    · have hConfF : (flags.noexecSeal && flags.exec) = false := by simpa using hConf
      by_cases hStrict : (flags.exec && (s.memfdNoexecStrict? == some true)) = true
      · have hParts := Bool.and_eq_true _ _ |>.mp hStrict
        have hFlExec : flags.exec = true := hParts.1
        have hFlNoex : flags.noexecSeal = false := by
          rw [hFlExec] at hConfF; simpa using hConfF
        have hStrTrue : s.memfdNoexecStrict? = some true := by simpa using hParts.2
        simp only [hBadNameF, Bool.false_eq_true, ↓reduceIte, hConfF, hStrict]
        have hWfMem : ({ s with memfdEnabled := true }).wf = true :=
          wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
        cases hSec : s.seccompMayIntercept
        · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfMem⟩
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hNameOk, hNotOver,
            hFlNoex, hFlExec, hStrTrue, hSec,
            show Errno.EACCES ≠ Errno.EFAULT by decide]
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          exact allowedStep_seccomp_err s _ Errno.EACCES (by simp [failsPureWrapperGuard, hNameOk])
            hSec (by decide) (by decide) (by decide)
      · have hStrictF : (flags.exec && (s.memfdNoexecStrict? == some true)) = false := by
          simpa using hStrict
        by_cases hEmf : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = true
        · simp only [hBadNameF, Bool.false_eq_true, ↓reduceIte, hConfF, hStrictF, hEmf]
          refine ⟨?_, hwf⟩
          cases hSec : s.seccompMayIntercept
          · simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hNameOk, hConfF, hNotOver, hSec,
              Errno.isTransientOsErrno, show Errno.EMFILE ≠ Errno.EACCES by decide,
              show Errno.EMFILE ≠ Errno.EFAULT by decide]
          · exact allowedStep_seccomp_err s _ Errno.EMFILE (by simp [failsPureWrapperGuard, hNameOk])
              hSec (by decide) (by decide) (by decide)
        · have hNoneHid := assocGet_nextHid_none s hwf
          have hEmfF : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = false := by
            simpa using hEmf
          have hEmf0 : (s.rlimitNofile.curExact && (s.rlimitNofile.cur == 0)) = false := by
            cases hEx : s.rlimitNofile.curExact
            · simp
            · simp only [hEx, Bool.true_and, decide_eq_false_iff_not, Nat.not_le] at hEmfF
              have hNz : s.rlimitNofile.cur.toNat ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hEmfF)
              have hNe : s.rlimitNofile.cur ≠ 0 := fun h0 => hNz (by simp [h0])
              simp [hNe]
          have hWf' : ({ s with
              fds := assocSet s.fds s.nextHid
                { kind := .memfd flags.allowSealing flags.noexecSeal, cloexec := flags.cloexec }
              nextHid := Nat.max s.nextHid (s.nextHid + 1)
              memfdEnabled := true
              memfdNoexecStrict? := if flags.exec then some false else s.memfdNoexecStrict? }).wf = true :=
            wf_mk (assocSet_nextHid_all_lt s _ hwf) (wf_nnpGate_of_wf s hwf)
              (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
          simp only [hBadNameF, Bool.false_eq_true, ↓reduceIte, hConfF, hStrictF, hEmf]
          refine ⟨?_, hWf'⟩
          cases hSec : s.seccompMayIntercept <;>
            simp [allowedStep, allowedStepCore, hNoneHid, hEmf0, hNameOk, hConfF, hStrictF, hSec,
              Nat.max_eq_right (Nat.le_succ s.nextHid)]

end LeanSwe.LinuxSyscall.Sandbox
