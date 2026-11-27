import Core.Obeys
import LeanSwe.LinuxSyscall.Passwd.Model.Refines
import LeanSwe.LinuxSyscall.Passwd.Proofs.OpsContracts
import LeanSwe.LinuxSyscall.Passwd.Proofs.HealthyStep

/-!
`IO` refinement soundness theorems (`getpwuid`/`getpwnam`) and canonical `Core.ObeysStepFrom`
capability-refinement proofs (`obeysStepFrom_passwd`, `modelRawOps_obeys_allowedRawStep`) for
`LeanSwe.LinuxSyscall.Passwd`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

private theorem retryPasswdLookup_baseio_sound
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (req : PasswdReq) (pred : PasswdEntry → Bool)
    (once : UInt32 → BaseIO (Except Errno (Option Internal.RawPasswdTuple)))
    (sizes : List UInt32) (hNonEmpty : sizes ≠ [])
    (hInv : isUserspaceInvalidReq req = false) (hwf : (abs w₀).isWellFormed = true)
    (hOnce : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz ∈ sizes,
      match once sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) req (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) req .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (pred entry → allowedStep (abs w) req (.found entry) = some (abs w') ∧ (abs w').isWellFormed = true) ∧
        (!(pred entry) → abs w' = abs w)) :
    ∀ (w : Void IO.RealWorld), abs w = abs w₀ →
      match Internal.retryPasswdLookup once pred sizes w with
      | .mk res wOut =>
        allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs wOut) ∧
        (abs wOut).isWellFormed = true := by
  induction sizes with
  | nil => contradiction
  | cons sz rest ih =>
    intro w hw
    have hSz := hOnce w hw sz (by simp)
    cases rest with
    | nil =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        instMonadBaseIO, instMonadBaseIO._aux_13, instMonadBaseIO._aux_5, ST.bind, ST.pure]
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        rw [hw] at hSz
        cases r with
        | error e =>
          simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
          exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            dsimp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs w') ∧
              (abs w').isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hw' : abs w' = abs w₀ := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hw']
              exact ⟨allowedStep_eio (abs w₀) req hInv, hwf⟩
    | cons sz2 rest2 =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        instMonadBaseIO, instMonadBaseIO._aux_13, instMonadBaseIO._aux_5, ST.bind, ST.pure]
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        rw [hw] at hSz
        cases r with
        | error e =>
          by_cases hEr : e == Errno.ERANGE
          · simp only [hEr, ↓reduceIte]
            have hw' : abs w' = abs w₀ := hSz.1 hEr
            exact ih (by simp) (fun w1 hw1 z hz => hOnce w1 hw1 z (by simp [hz])) w' hw'
          · simp only [hEr, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
            exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            dsimp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs w') ∧
              (abs w').isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hw' : abs w' = abs w₀ := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hw']
              exact ⟨allowedStep_eio (abs w₀) req hInv, hwf⟩

/-- Universal `IO` refinement soundness for `(Internal.mkPasswdOpsM raw).getpwuid`: never throws `IO.Error` and steps according to `Model.allowedStep` while preserving `PasswdState.isWellFormed`. -/
theorem proof_passwd_mkPasswdOps_getpwuid_io_soundAgainstAllowedStep
    (raw : Internal.PosixPasswdOpsM BaseIO)
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (uid : UInt32)
    (hwf : (abs w₀).isWellFormed = true)
    (hRaw : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz : UInt32,
      4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
      match raw.getpwuidOnce uid sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) (.getpwuid uid) (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) (.getpwuid uid) .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (entry.hasNoEmbeddedNul && entry.uid == uid →
          allowedStep (abs w) (.getpwuid uid) (.found entry) = some (abs w') ∧
            (abs w').isWellFormed = true) ∧
        (!(entry.hasNoEmbeddedNul && entry.uid == uid) → abs w' = abs w)) :
    ∃ res wFinal,
      ((Internal.mkPasswdOpsM raw).getpwuid uid : IO _) w₀ = .ok res wFinal ∧
      allowedStep (abs w₀) (.getpwuid uid) (outcomeOfEntryOpt res) = some (abs wFinal) ∧
      (abs wFinal).isWellFormed = true := by
  have hBase := retryPasswdLookup_baseio_sound abs w₀ (.getpwuid uid)
    (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
    (raw.getpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
    (fun w hw sz hMem => hRaw w hw sz (passwdRetryBufSizes_range sz hMem)) w₀ rfl
  dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases hCall : Internal.retryPasswdLookup (raw.getpwuidOnce uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      Internal.passwdRetryBufSizes w₀ with
  | mk res wFinal =>
    rw [hCall] at hBase
    exact ⟨res, wFinal, rfl, hBase.1, hBase.2⟩

/-- Universal `IO` refinement soundness for `(Internal.mkPasswdOpsM raw).getpwnam`: never throws `IO.Error` and steps according to `Model.allowedStep` while preserving `PasswdState.isWellFormed`. -/
theorem proof_passwd_mkPasswdOps_getpwnam_io_soundAgainstAllowedStep
    (raw : Internal.PosixPasswdOpsM BaseIO)
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (name : ByteArray)
    (hwf : (abs w₀).isWellFormed = true)
    (hRaw : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz : UInt32,
      4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
      validPasswdName name = true →
      name.size ≤ MAX_PASSWD_NAME_BYTES →
      match raw.getpwnamOnce name sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) (.getpwnam name) (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) (.getpwnam name) .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (entry.hasNoEmbeddedNul && entry.name == name →
          allowedStep (abs w) (.getpwnam name) (.found entry) = some (abs w') ∧
            (abs w').isWellFormed = true) ∧
        (!(entry.hasNoEmbeddedNul && entry.name == name) → abs w' = abs w)) :
    ∃ res wFinal,
      ((Internal.mkPasswdOpsM raw).getpwnam name : IO _) w₀ = .ok res wFinal ∧
      allowedStep (abs w₀) (.getpwnam name) (outcomeOfEntryOpt res) = some (abs wFinal) ∧
      (abs wFinal).isWellFormed = true := by
  by_cases hv : validPasswdName name = true
  · by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
    · refine ⟨.error Errno.ENAMETOOLONG, w₀, ?_, ?_, hwf⟩
      · dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, pure,
          instMonadBaseIO._aux_5]
        rfl
      · simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, Errno.ENAMETOOLONG]
    · have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
      have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
        simp [isUserspaceInvalidReq, hv, hlen]
      have hBase := retryPasswdLookup_baseio_sound abs w₀ (.getpwnam name)
        (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
        (raw.getpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
        (fun w hw sz hMem => hRaw w hw sz (passwdRetryBufSizes_range sz hMem) hv hlenLe) w₀ rfl
      dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen]
      cases hCall : Internal.retryPasswdLookup (raw.getpwnamOnce name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          Internal.passwdRetryBufSizes w₀ with
      | mk res wFinal =>
        rw [hCall] at hBase
        exact ⟨res, wFinal, rfl, hBase.1, hBase.2⟩
  · have hvF : validPasswdName name = false := by
      cases hb : validPasswdName name <;> simp_all
    refine ⟨.error Errno.EINVAL, w₀, ?_, ?_, hwf⟩
    · dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
      simp only [hvF, Bool.not_false, ↓reduceIte, pure, instMonadBaseIO._aux_5]
      rfl
    · simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hvF, Errno.EINVAL]

private def entryKeyMatches : PasswdReq → PasswdEntry → Bool
  | .getpwuid uid, entry => entry.uid == uid
  | .getpwnam name, entry => entry.name == name

private theorem healthyStep_found_valid
    (env env' : HealthyEnv) (req : PasswdReq) (entry : PasswdEntry)
    (h : healthyStep env req (.found entry) = some env') :
    entry.hasNoEmbeddedNul = true ∧ entryKeyMatches req entry = true := by
  have hAl := (healthyStep_implies_allowedStep env env' req (.found entry) h).1
  unfold allowedStep at hAl
  cases hc : allowedStepCore env.state req (.found entry) with
  | some sc =>
    cases req with
    | getpwuid uid =>
      dsimp only [allowedStepCore] at hc
      cases hdb : lookupPasswdByUid env.state.byUid uid <;> rw [hdb] at hc
      · dsimp only at hc
        split at hc
        · rename_i hok
          exact Bool.and_eq_true_iff.mp hok
        · contradiction
      · rename_i opt
        cases opt with
        | none => contradiction
        | some expected =>
          dsimp only at hc
          split at hc
          · rename_i hok
            simp only [Bool.and_eq_true] at hok
            exact ⟨hok.1.2, hok.2⟩
          · contradiction
    | getpwnam name =>
      dsimp only [allowedStepCore] at hc
      by_cases hv : validPasswdName name = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
        · simp [hlen] at hc
        · simp only [hlen, ↓reduceIte] at hc
          cases hdb : lookupPasswdByName env.state.byName name <;> rw [hdb] at hc
          · dsimp only at hc
            split at hc
            · rename_i hok
              exact Bool.and_eq_true_iff.mp hok
            · contradiction
          · rename_i opt
            cases opt with
            | none => contradiction
            | some expected =>
              dsimp only at hc
              split at hc
              · rename_i hok
                simp only [Bool.and_eq_true] at hok
                exact ⟨hok.1.2, hok.2⟩
              · contradiction
      · have hvF : validPasswdName name = false := by
          cases hb : validPasswdName name <;> simp_all
        simp [hvF] at hc
  | none =>
    rw [hc] at hAl
    dsimp only at hAl
    split at hAl
    · split at hAl
      · rename_i hfb
        simp only [Bool.and_eq_true, isValidNssFallbackOutcome] at hfb
        cases req <;> exact hfb.2
      · contradiction
    · contradiction

private theorem healthyStep_erange_eq
    (env env' : HealthyEnv) (req : PasswdReq)
    (hInv : isUserspaceInvalidReq req = false)
    (h : healthyStep env req (.err Errno.ERANGE) = some env') :
    env' = env := by
  have hCore : allowedStepCore env.state req (.err Errno.ERANGE) = some env.state := by
    cases req with
    | getpwuid uid =>
      cases hdb : lookupPasswdByUid env.state.byUid uid with
      | none => simp [allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.ERANGE]
      | some opt =>
        cases opt <;> simp [allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.ERANGE]
    | getpwnam name =>
      simp only [isUserspaceInvalidReq, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hInv
      have hv : validPasswdName name = true := by
        cases hb : validPasswdName name <;> simp_all
      cases hdb : lookupPasswdByName env.state.byName name with
      | none => simp [allowedStepCore, hv, hInv.2, hdb, isAllowedPasswdOsErrno, Errno.ERANGE]
      | some opt =>
        cases opt <;> simp [allowedStepCore, hv, hInv.2, hdb, isAllowedPasswdOsErrno, Errno.ERANGE]
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault (.err Errno.ERANGE)) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte, allowedStep, hCore] at h
    have hEi : isEintrOutcome (.err Errno.ERANGE) = false := by decide
    simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    cases env
    exact h.symm

private theorem retryPasswdLookup_healthy_sound
    {W : Type} (proj : W → HealthyEnv) (req : PasswdReq) (pred : PasswdEntry → Bool)
    (once : UInt32 → StateM W Model.RawStepOut)
    (sizes : List UInt32) (hNonEmpty : sizes ≠ [])
    (hInv : isUserspaceInvalidReq req = false)
    (hPred : ∀ entry, entry.hasNoEmbeddedNul = true → entryKeyMatches req entry = true → pred entry = true)
    (hOnce : ∀ (w : W), (proj w).wf = true → ∀ sz ∈ sizes,
      let r := (once sz).run w
      healthyStep (proj w) req (Model.outcomeOfRawOut r.1) = some (proj r.2)) :
    ∀ (w : W), (proj w).wf = true →
      let r := (Internal.retryPasswdLookup once pred sizes).run w
      healthyStep (proj w) req (outcomeOfEntryOpt r.1) = some (proj r.2) := by
  induction sizes with
  | nil => contradiction
  | cons sz rest ih =>
    intro w hwf
    have hSz := hOnce w hwf sz (by simp)
    cases rest with
    | nil =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hSz ⊢
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        dsimp only at hSz
        cases r with
        | error e =>
          dsimp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt, Model.outcomeOfRawOut] at hSz ⊢
          exact hSz
        | ok opt =>
          cases opt with
          | none =>
            dsimp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt, Model.outcomeOfRawOut] at hSz ⊢
            exact hSz
          | some t =>
            dsimp only [Model.outcomeOfRawOut] at hSz
            rcases healthyStep_found_valid (proj w) (proj w') req (Model.entryOfRawTuple t) hSz with
              ⟨hNul, hKey⟩
            have hp : pred (Model.entryOfRawTuple t) = true := hPred _ hNul hKey
            dsimp only [Internal.validateRawPasswdResult]
            change healthyStep (proj w) req
              (outcomeOfEntryOpt
                (if pred (Model.entryOfRawTuple t) then .ok (some (Model.entryOfRawTuple t))
                 else .error Errno.EIO)) = some (proj w')
            rw [hp]
            exact hSz
    | cons sz2 rest2 =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hSz ⊢
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        dsimp only at hSz
        cases r with
        | error e =>
          by_cases hEr : (e == Errno.ERANGE) = true
          · simp only [hEr, ↓reduceIte]
            have heq : e = Errno.ERANGE := eq_of_beq hEr
            subst heq
            have hw' : proj w' = proj w :=
              healthyStep_erange_eq (proj w) (proj w') req hInv hSz
            have hwf' : (proj w').wf = true := by rw [hw']; exact hwf
            have hNext := ih (by simp) (fun w1 hw1 z hz => hOnce w1 hw1 z (by simp [hz])) w' hwf'
            simpa [StateT.run, hw'] using hNext
          · simp only [hEr, Bool.false_eq_true, ↓reduceIte, StateT.pure, outcomeOfEntryOpt]
            exact hSz
        | ok opt =>
          cases opt with
          | none =>
            dsimp only [Internal.validateRawPasswdResult, StateT.pure,
              outcomeOfEntryOpt, Model.outcomeOfRawOut] at hSz ⊢
            exact hSz
          | some t =>
            dsimp only [Model.outcomeOfRawOut] at hSz
            rcases healthyStep_found_valid (proj w) (proj w') req (Model.entryOfRawTuple t) hSz with
              ⟨hNul, hKey⟩
            have hp : pred (Model.entryOfRawTuple t) = true := hPred _ hNul hKey
            dsimp only [Internal.validateRawPasswdResult, StateT.pure]
            change healthyStep (proj w) req
              (outcomeOfEntryOpt
                (if pred (Model.entryOfRawTuple t) then .ok (some (Model.entryOfRawTuple t))
                 else .error Errno.EIO)) = some (proj w')
            rw [hp]
            exact hSz

/-- Canonical `Core.ObeysStepFrom` refinement lifting `Internal.PosixPasswdOpsM` to `PasswdOpsM`. -/
theorem obeysStepFrom_passwd :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkPasswdOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hwf
  dsimp only [Function.comp_apply, id, Model.rawStepWf] at hwf ⊢
  have hBufValid : ∀ sz ∈ Internal.passwdRetryBufSizes, Model.validRawBufBytes sz = true := by
    intro sz hMem
    have hr := passwdRetryBufSizes_range sz hMem
    unfold Model.validRawBufBytes
    exact decide_eq_true ⟨by omega, hr.2⟩
  cases req with
  | getpwuid uid =>
    have hOnce : ∀ (w₁ : W), (proj w₁).wf = true → ∀ sz ∈ Internal.passwdRetryBufSizes,
        let r := (raw.getpwuidOnce uid sz).run w₁
        healthyStep (proj w₁) (.getpwuid uid) (Model.outcomeOfRawOut r.1) = some (proj r.2) := by
      intro w₁ hwf₁ sz hMem
      have hStep := hRaw w₁ (.getpwuidOnce uid sz) hwf₁
      have hvSz := hBufValid sz hMem
      simpa [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.RawStepReq.toPasswdReq,
        Model.execRawStep, hvSz] using hStep
    have hRun := retryPasswdLookup_healthy_sound proj (.getpwuid uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      (raw.getpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl
      (fun entry hNul hKey => Bool.and_eq_true_iff.mpr ⟨hNul, hKey⟩)
      hOnce w hwf
    dsimp only [Model.allowedPkgStep, Model.execPkgStep, execPasswdReq, Internal.mkPasswdOpsM,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRun ⊢
    cases hRunCall : (Internal.retryPasswdLookup (raw.getpwuidOnce uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      Internal.passwdRetryBufSizes) w with
    | mk res wOut =>
      rw [hRunCall] at hRun
      exact hRun
  | getpwnam name =>
    by_cases hv : validPasswdName name = true
    · by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · dsimp only [Model.allowedPkgStep, Model.execPkgStep, execPasswdReq, Internal.mkPasswdOpsM]
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, Bind.bind, Pure.pure,
          StateT.run, StateT.bind, StateT.pure, outcomeOfEntryOpt]
        have hNoCrit : isCriticalFault (.err Errno.ENAMETOOLONG) = false := by decide
        have hNoEi : isEintrOutcome (.err Errno.ENAMETOOLONG) = false := by decide
        have hCore : allowedStep (proj w).state (.getpwnam name) (.err Errno.ENAMETOOLONG) =
            some (proj w).state := by
          simp [allowedStep, allowedStepCore, hv, hlen, Errno.ENAMETOOLONG]
        have hTight := allowedStep_healthy_tight (proj w) (.getpwnam name)
          (.err Errno.ENAMETOOLONG) (proj w).state hCore hwf (by simp [hNoEi]) hNoCrit
        simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
        cases hp : proj w
        rw [hp] at hTight
        exact hTight
      · have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
          simp [isUserspaceInvalidReq, hv, hlen]
        have hOnce : ∀ (w₁ : W), (proj w₁).wf = true → ∀ sz ∈ Internal.passwdRetryBufSizes,
            let r := (raw.getpwnamOnce name sz).run w₁
            healthyStep (proj w₁) (.getpwnam name) (Model.outcomeOfRawOut r.1) = some (proj r.2) := by
          intro w₁ hwf₁ sz hMem
          have hStep := hRaw w₁ (.getpwnamOnce name sz) hwf₁
          have hvSz := hBufValid sz hMem
          simpa [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.RawStepReq.toPasswdReq,
            Model.execRawStep, hvSz] using hStep
        have hRun := retryPasswdLookup_healthy_sound proj (.getpwnam name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          (raw.getpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv
          (fun entry hNul hKey => Bool.and_eq_true_iff.mpr ⟨hNul, hKey⟩)
          hOnce w hwf
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execPasswdReq, Internal.mkPasswdOpsM]
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, Bind.bind, Pure.pure,
          StateT.run, StateT.bind, StateT.pure] at hRun ⊢
        cases hRunCall : (Internal.retryPasswdLookup (raw.getpwnamOnce name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          Internal.passwdRetryBufSizes) w with
        | mk res wOut =>
          rw [hRunCall] at hRun
          exact hRun
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      dsimp only [Model.allowedPkgStep, Model.execPkgStep, execPasswdReq, Internal.mkPasswdOpsM]
      simp only [hvF, Bool.not_false, ↓reduceIte, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure, outcomeOfEntryOpt]
      have hNoCrit : isCriticalFault (.err Errno.EINVAL) = false := by decide
      have hNoEi : isEintrOutcome (.err Errno.EINVAL) = false := by decide
      have hCore : allowedStep (proj w).state (.getpwnam name) (.err Errno.EINVAL) =
          some (proj w).state := by
        simp [allowedStep, allowedStepCore, hvF, Errno.EINVAL]
      have hTight := allowedStep_healthy_tight (proj w) (.getpwnam name)
        (.err Errno.EINVAL) (proj w).state hCore hwf (by simp [hNoEi]) hNoCrit
      simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
      cases hp : proj w
      rw [hp] at hTight
      exact hTight

/-- Reference `Model.modelRawOps` satisfies `Core.ObeysStep` against `Model.allowedRawStep`. -/
theorem modelRawOps_obeys_allowedRawStep :
    Core.ObeysStep id Model.rawStepWf (Model.execRawStep Model.modelRawOps) Model.allowedRawStep := by
  intro env req hwf
  dsimp only [id, Model.rawStepWf] at hwf ⊢
  cases req with
  | getpwuidOnce uid sz =>
    by_cases hv : Model.validRawBufBytes sz = true
    · have hRef := healthyModelOps_refinesHealthyPasswd env (.getpwuid uid) hwf
      dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRef
      dsimp only [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.RawStepReq.toPasswdReq,
        Model.execRawStep, Model.modelRawOps]
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
        StateT.run, StateT.bind]
      cases hCall : healthyModelOps.getpwuid uid env with
      | mk res env' =>
        rw [hCall] at hRef
        dsimp only [outcomeOfEntryOpt] at hRef
        cases res with
        | error e =>
          dsimp only [StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
          exact hRef
        | ok opt =>
          cases opt with
          | none =>
            dsimp only [Option.map, StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
            exact hRef
          | some entry =>
            have hTuple : Model.entryOfRawTuple (Model.tupleOfEntry entry) = entry := by
              cases entry; rfl
            dsimp only [Option.map, StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
            rw [hTuple]
            exact hRef
    · have hvF : Model.validRawBufBytes sz = false := by
        cases hb : Model.validRawBufBytes sz <;> simp_all
      simp [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.execRawStep,
        Model.modelRawOps, hvF, hwf, pure, StateT.pure, StateT.run]
  | getpwnamOnce name sz =>
    by_cases hv : Model.validRawBufBytes sz = true
    · have hRef := healthyModelOps_refinesHealthyPasswd env (.getpwnam name) hwf
      dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRef
      dsimp only [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.RawStepReq.toPasswdReq,
        Model.execRawStep, Model.modelRawOps]
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
        StateT.run, StateT.bind]
      cases hCall : healthyModelOps.getpwnam name env with
      | mk res env' =>
        rw [hCall] at hRef
        dsimp only [outcomeOfEntryOpt] at hRef
        cases res with
        | error e =>
          dsimp only [StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
          exact hRef
        | ok opt =>
          cases opt with
          | none =>
            dsimp only [Option.map, StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
            exact hRef
          | some entry =>
            have hTuple : Model.entryOfRawTuple (Model.tupleOfEntry entry) = entry := by
              cases entry; rfl
            dsimp only [Option.map, StateT.pure, pure, Pure.pure, Model.outcomeOfRawOut]
            rw [hTuple]
            exact hRef
    · have hvF : Model.validRawBufBytes sz = false := by
        cases hb : Model.validRawBufBytes sz <;> simp_all
      simp [Model.allowedRawStep, Model.RawStepReq.bufBytes, Model.execRawStep,
        Model.modelRawOps, hvF, hwf, pure, StateT.pure, StateT.run]

end LeanSwe.LinuxSyscall.Passwd.Proofs
