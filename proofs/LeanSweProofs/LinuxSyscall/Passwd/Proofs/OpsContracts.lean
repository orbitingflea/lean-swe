import LeanSwe.LinuxSyscall.Passwd.Impl
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.ModelSoundness

/-!
`Internal.mkPasswdOpsM` retry-loop contracts, soundness against `allowedStep`, and `Interface`
wiring proofs for `LeanSwe.LinuxSyscall.Passwd`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

/-- Formal verification of `Internal.mkPasswdOpsM`: invalid (`EINVAL`) and oversized (`ENAMETOOLONG`) `getpwnam` names fail before FFI, and `getpwuid`/`getpwnam` double scratch capacity across `4096 → 8192 → 16384 → 32768 → 65536` on `ERANGE`, stop immediately on non-`ERANGE` errors, and validate returned entries via `Internal.validateRawPasswdResult` (rejecting mismatched keys or embedded NULs with `Errno.EIO`). -/
theorem internal_mkPasswdOpsM_contracts
    (raw : Internal.PosixPasswdOpsM Id) (uid : UInt32) (name : ByteArray) :
    let stepOr (pred : PasswdEntry → Bool)
        (once : UInt32 → Except Errno (Option Internal.RawPasswdTuple))
        (sz : UInt32) (next : Except Errno (Option PasswdEntry)) :
        Except Errno (Option PasswdEntry) :=
      match once sz with
      | .error e => if e == Errno.ERANGE then next else .error e
      | .ok opt => Internal.validateRawPasswdResult pred (.ok opt)
    let finish (pred : PasswdEntry → Bool)
        (once : UInt32 → Except Errno (Option Internal.RawPasswdTuple))
        (sz : UInt32) : Except Errno (Option PasswdEntry) :=
      Internal.validateRawPasswdResult pred (once sz)
    let uidPred : PasswdEntry → Bool := fun entry => entry.hasNoEmbeddedNul && entry.uid == uid
    let namPred : PasswdEntry → Bool := fun entry => entry.hasNoEmbeddedNul && entry.name == name
    (Internal.mkPasswdOpsM raw).getpwuid uid =
      stepOr uidPred (raw.getpwuidOnce uid) 4096
        (stepOr uidPred (raw.getpwuidOnce uid) 8192
          (stepOr uidPred (raw.getpwuidOnce uid) 16384
            (stepOr uidPred (raw.getpwuidOnce uid) 32768
              (finish uidPred (raw.getpwuidOnce uid) 65536)))) ∧
    (Internal.mkPasswdOpsM raw).getpwnam name =
      if !validPasswdName name then
        .error Errno.EINVAL
      else if name.size > MAX_PASSWD_NAME_BYTES then
        .error Errno.ENAMETOOLONG
      else
        stepOr namPred (raw.getpwnamOnce name) 4096
          (stepOr namPred (raw.getpwnamOnce name) 8192
            (stepOr namPred (raw.getpwnamOnce name) 16384
              (stepOr namPred (raw.getpwnamOnce name) 32768
                (finish namPred (raw.getpwnamOnce name) 65536)))) := by
  refine ⟨?_, ?_⟩
  · dsimp only [Internal.mkPasswdOpsM, Internal.passwdRetryBufSizes, Internal.retryPasswdLookup,
      Bind.bind, Pure.pure]
    cases raw.getpwuidOnce uid 4096 with
    | ok _ => rfl
    | error e1 =>
      by_cases h1 : e1 == Errno.ERANGE
      · simp only [h1, ↓reduceIte]
        cases raw.getpwuidOnce uid 8192 with
        | ok _ => rfl
        | error e2 =>
          by_cases h2 : e2 == Errno.ERANGE
          · simp only [h2, ↓reduceIte]
            cases raw.getpwuidOnce uid 16384 with
            | ok _ => rfl
            | error e3 =>
              by_cases h3 : e3 == Errno.ERANGE
              · simp only [h3, ↓reduceIte]
                cases raw.getpwuidOnce uid 32768 with
                | ok _ => rfl
                | error e4 =>
                  by_cases h4 : e4 == Errno.ERANGE
                  · simp only [h4, ↓reduceIte]
                  · simp [h4]
              · simp [h3]
          · simp [h2]
      · simp [h1]
  · dsimp only [Internal.mkPasswdOpsM, Internal.passwdRetryBufSizes, Internal.retryPasswdLookup,
      Bind.bind, Pure.pure]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen]
      · simp only [hlen, ↓reduceIte]
        cases raw.getpwnamOnce name 4096 with
        | ok _ => rfl
        | error e1 =>
          by_cases h1 : e1 == Errno.ERANGE
          · simp only [h1, ↓reduceIte]
            cases raw.getpwnamOnce name 8192 with
            | ok _ => rfl
            | error e2 =>
              by_cases h2 : e2 == Errno.ERANGE
              · simp only [h2, ↓reduceIte]
                cases raw.getpwnamOnce name 16384 with
                | ok _ => rfl
                | error e3 =>
                  by_cases h3 : e3 == Errno.ERANGE
                  · simp only [h3, ↓reduceIte]
                    cases raw.getpwnamOnce name 32768 with
                    | ok _ => rfl
                    | error e4 =>
                      by_cases h4 : e4 == Errno.ERANGE
                      · simp only [h4, ↓reduceIte]
                      · simp [h4]
                  · simp [h3]
              · simp [h2]
          · simp [h1]
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF]

/-- Any non-userspace-invalid `PasswdReq` accepts `Errno.EIO` without mutating `PasswdState`. -/
theorem allowedStep_eio (s : PasswdState) (req : PasswdReq)
    (hreq : isUserspaceInvalidReq req = false) :
    allowedStep s req (.err Errno.EIO) = some s := by
  cases req with
  | getpwuid uid =>
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none => simp [allowedStep, allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.EIO]
    | some opt =>
      cases opt <;> simp [allowedStep, allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.EIO]
  | getpwnam name =>
    have hv : validPasswdName name = true := by
      simp [isUserspaceInvalidReq] at hreq
      exact hreq.1
    have hlen : ¬ (name.size > MAX_PASSWD_NAME_BYTES) := by
      simp [isUserspaceInvalidReq] at hreq
      exact Nat.not_lt.mpr hreq.2
    cases hdb : lookupPasswdByName s.byName name with
    | none => simp [allowedStep, allowedStepCore, hv, hlen, hdb, isAllowedPasswdOsErrno, Errno.EIO]
    | some opt =>
      cases opt <;> simp [allowedStep, allowedStepCore, hv, hlen, hdb, isAllowedPasswdOsErrno, Errno.EIO]

private theorem retryPasswdLookup_sound
    (s : PasswdState) (req : PasswdReq) (pred : PasswdEntry → Bool)
    (once : UInt32 → StateM PasswdState (Except Errno (Option Internal.RawPasswdTuple)))
    (sizes : List UInt32) (hNonEmpty : sizes ≠ [])
    (hInv : isUserspaceInvalidReq req = false) (hwf : s.isWellFormed = true)
    (hOnce : ∀ sz ∈ sizes,
      let (r, s') := once sz s
      match r with
      | .error e =>
        (e == Errno.ERANGE → s' = s) ∧
        allowedStep s req (.err e) = some s' ∧ s'.isWellFormed = true
      | .ok none =>
        allowedStep s req .notFound = some s' ∧ s'.isWellFormed = true
      | .ok (some t) =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (pred entry → allowedStep s req (.found entry) = some s' ∧ s'.isWellFormed = true) ∧
        (!(pred entry) → s' = s)) :
    let (res, sOut) := Internal.retryPasswdLookup once pred sizes s
    allowedStep s req (outcomeOfEntryOpt res) = some sOut ∧ sOut.isWellFormed = true := by
  induction sizes with
  | nil => contradiction
  | cons sz rest ih =>
    have hSz := hOnce sz (by simp)
    cases rest with
    | nil =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      cases hCall : once sz s with
      | mk r s' =>
        rw [hCall] at hSz
        dsimp only at hSz
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
            simp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep s req (outcomeOfEntryOpt res) = some s' ∧ s'.isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hs' : s' = s := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hs']
              exact ⟨allowedStep_eio s req hInv, hwf⟩
    | cons sz2 rest2 =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      cases hCall : once sz s with
      | mk r s' =>
        rw [hCall] at hSz
        dsimp only at hSz
        cases r with
        | error e =>
          by_cases hEr : e == Errno.ERANGE
          · simp only [hEr, ↓reduceIte]
            have hs' : s' = s := hSz.1 hEr
            rw [hs']
            exact ih (by simp) (fun z hz => hOnce z (by simp [hz]))
          · simp only [hEr, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
            exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            simp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep s req (outcomeOfEntryOpt res) = some s' ∧ s'.isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hs' : s' = s := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hs']
              exact ⟨allowedStep_eio s req hInv, hwf⟩

/-- Every element of `Internal.passwdRetryBufSizes` lies in `[4096, 65536]`. -/
theorem passwdRetryBufSizes_range (sz : UInt32) (hMem : sz ∈ Internal.passwdRetryBufSizes) :
    4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 := by
  simp only [Internal.passwdRetryBufSizes, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Proof of `test_passwd_mkPasswdOps_soundAgainstAllowedStep` for `Internal.mkPasswdOpsM`. -/
theorem proof_passwd_mkPasswdOps_soundAgainstAllowedStep :
    AllPass (test_passwd_mkPasswdOps_soundAgainstAllowedStep
      (fun gUid gNam => Internal.mkPasswdOpsM { getpwuidOnce := gUid, getpwnamOnce := gNam })) := by
  intro s uid name badName overCapName rawGetpwuidOnce rawGetpwnamOnce hwf hBad hOverValid hOverSize hRawUid hRawNam
  dsimp only [test_passwd_mkPasswdOps_soundAgainstAllowedStep, NondetTest.assert, Bind.bind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [Internal.mkPasswdOpsM, hBad]; rfl
  · simp [Internal.mkPasswdOpsM, hOverValid, hOverSize]; rfl
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    exact (retryPasswdLookup_sound s (.getpwuid uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      (rawGetpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
      (fun sz hMem => hRawUid sz (passwdRetryBufSizes_range sz hMem))).1
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    exact (retryPasswdLookup_sound s (.getpwuid uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      (rawGetpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
      (fun sz hMem => hRawUid sz (passwdRetryBufSizes_range sz hMem))).2
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, pure, StateT.pure, outcomeOfEntryOpt, allowedStep, allowedStepCore, hv,
          Errno.ENAMETOOLONG]
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
          simp [isUserspaceInvalidReq, hv, hlen]
        exact (retryPasswdLookup_sound s (.getpwnam name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          (rawGetpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
          (fun sz hMem => hRawNam sz (passwdRetryBufSizes_range sz hMem) hv hlenLe)).1
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, pure, StateT.pure, outcomeOfEntryOpt, allowedStep, allowedStepCore, Errno.EINVAL]
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, pure, StateT.pure, hwf]
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
          simp [isUserspaceInvalidReq, hv, hlen]
        exact (retryPasswdLookup_sound s (.getpwnam name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          (rawGetpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
          (fun sz hMem => hRawNam sz (passwdRetryBufSizes_range sz hMem) hv hlenLe)).2
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, pure, StateT.pure, hwf]

/-- Non-vacuity `CanReach` witness for `test_passwd_mkPasswdOps_soundAgainstAllowedStep`. -/
theorem reach_passwd_mkPasswdOps_soundAgainstAllowedStep :
    CanReach (test_passwd_mkPasswdOps_soundAgainstAllowedStep
      (fun gUid gNam => Internal.mkPasswdOpsM { getpwuidOnce := gUid, getpwnamOnce := gNam })) := by
  let rawGetpwuidNone : UInt32 → UInt32 → StateM PasswdState (Except Errno (Option Internal.RawPasswdTuple)) :=
    fun _ _ => pure (.ok none)
  let rawGetpwnamNone : ByteArray → UInt32 → StateM PasswdState (Except Errno (Option Internal.RawPasswdTuple)) :=
    fun _ _ => pure (.ok none)
  let s0 : PasswdState :=
    { byUid := setPasswdByUid ∅ 0 none
      byName := setPasswdByName ∅ ByteArray.empty none }
  have hs0 : s0.isWellFormed = true := by
    simp only [s0, PasswdState.isWellFormed, Bool.and_eq_true]
    exact ⟨setPasswdByUid_wellFormed ∅ 0 none (by decide) (by decide),
      setPasswdByName_wellFormed ∅ ByteArray.empty none (by decide) (by decide)⟩
  refine ⟨s0, 0, ByteArray.empty, ByteArray.mk #[0], overCapWitness, rawGetpwuidNone, rawGetpwnamNone, hs0,
    by decide, validPasswdName_overCapWitness, overCapWitness_size_gt,
    (fun _ _ => by dsimp only [rawGetpwuidNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByUid_set_self, hs0]),
    (fun _ _ _ _ => by dsimp only [rawGetpwnamNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByName_set_self, hs0, show validPasswdName ByteArray.empty = true by decide]),
    ?_⟩
  exact proof_passwd_mkPasswdOps_soundAgainstAllowedStep s0 0 ByteArray.empty (ByteArray.mk #[0])
    overCapWitness rawGetpwuidNone rawGetpwnamNone hs0 (by decide) validPasswdName_overCapWitness overCapWitness_size_gt
    (fun _ _ => by dsimp only [rawGetpwuidNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByUid_set_self, hs0])
    (fun _ _ _ _ => by dsimp only [rawGetpwnamNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByName_set_self, hs0, show validPasswdName ByteArray.empty = true by decide])

/-- Proof of `test_passwd_mkPasswdOps_exactRetryAndDelegation` for `Internal.mkPasswdOpsM` and `Internal.mkPasswdOps`. -/
theorem proof_passwd_mkPasswdOps_exactRetryAndDelegation :
    AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
      (fun gUid gNam => Internal.mkPasswdOpsM { getpwuidOnce := gUid, getpwnamOnce := gNam })
      Internal.passwdRetryBufSizes
      (fun gUid gNam => Internal.mkPasswdOps { getpwuidOnce := gUid, getpwnamOnce := gNam })) := by
  intro rawGetpwuid rawGetpwnam uid name
  dsimp only [test_passwd_mkPasswdOps_exactRetryAndDelegation, NondetTest.assert, Bind.bind]
  have hContracts := internal_mkPasswdOpsM_contracts
    { getpwuidOnce := rawGetpwuid, getpwnamOnce := rawGetpwnam } uid name
  have hRetryEq : ∀ (pred : PasswdEntry → Bool)
      (once : UInt32 → Except Errno (Option Internal.RawPasswdTuple)),
      (let stepOr (sz : UInt32) (next : Except Errno (Option PasswdEntry)) :=
         match once sz with
         | .error e => if e == Errno.ERANGE then next else .error e
         | .ok opt => Internal.validateRawPasswdResult pred (.ok opt)
       stepOr 4096 (stepOr 8192 (stepOr 16384 (stepOr 32768
         (Internal.validateRawPasswdResult pred (once 65536)))))) =
      (let validateTuple : Except Errno (Option Internal.RawPasswdTuple) → Except Errno (Option PasswdEntry)
         | .error e => .error e
         | .ok none => .ok none
         | .ok (some t) =>
           let entry : PasswdEntry :=
             { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
               homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
           if pred entry then .ok (some entry) else .error Errno.EIO
       let stepOr (sz : UInt32) (next : Except Errno (Option PasswdEntry)) :=
         match once sz with
         | .error e => if e == Errno.ERANGE then next else .error e
         | .ok opt => validateTuple (.ok opt)
       stepOr 4096 (stepOr 8192 (stepOr 16384 (stepOr 32768 (validateTuple (once 65536)))))) := by
    intro pred once
    dsimp only
    cases once 4096 with
    | ok opt => cases opt <;> rfl
    | error e1 =>
      by_cases h1 : e1 == Errno.ERANGE
      · simp only [h1, ↓reduceIte]
        cases once 8192 with
        | ok opt => cases opt <;> rfl
        | error e2 =>
          by_cases h2 : e2 == Errno.ERANGE
          · simp only [h2, ↓reduceIte]
            cases once 16384 with
            | ok opt => cases opt <;> rfl
            | error e3 =>
              by_cases h3 : e3 == Errno.ERANGE
              · simp only [h3, ↓reduceIte]
                cases once 32768 with
                | ok opt => cases opt <;> rfl
                | error e4 =>
                  by_cases h4 : e4 == Errno.ERANGE
                  · simp only [h4, ↓reduceIte]
                    cases once 65536 with
                    | error _ => rfl
                    | ok opt => cases opt <;> rfl
                  · simp [h4]
              · simp [h3]
          · simp [h2]
      · simp [h1]
  refine ⟨rfl, rfl, rfl, ?_, ?_, trivial⟩
  · exact hContracts.1.trans (hRetryEq _ (rawGetpwuid uid))
  · rw [hContracts.2]
    split
    · rfl
    · split
      · rfl
      · exact hRetryEq _ (rawGetpwnam name)

/-- Soundness binding: `Passwd.getpwuid` dispatches through `Passwd.defaultOps.getpwuid`. -/
theorem proof_passwd_getpwuid_eq_defaultOps (uid : UInt32) :
    Passwd.getpwuid uid = Passwd.defaultOps.getpwuid uid := rfl

/-- Soundness binding: `Passwd.getpwnam` dispatches through `Passwd.defaultOps.getpwnam`. -/
theorem proof_passwd_getpwnam_eq_defaultOps (name : ByteArray) :
    Passwd.getpwnam name = Passwd.defaultOps.getpwnam name := rfl

/-- Pure user-space short-circuit: `Passwd.getpwnam` on any invalid name returns `pure (.error Errno.EINVAL)` without invoking the C FFI shim. -/
theorem proof_passwd_getpwnam_invalidName_eq_einval (name : ByteArray)
    (hInv : validPasswdName name = false) :
    Passwd.getpwnam name = pure (.error Errno.EINVAL) := by
  simp [Passwd.getpwnam, Passwd.defaultOps, Internal.mkPasswdOpsM, hInv]
  rfl

/-- Pure user-space short-circuit: `Passwd.getpwnam` on any NUL-free name longer than `MAX_PASSWD_NAME_BYTES` returns `pure (.error Errno.ENAMETOOLONG)` without invoking the C FFI shim. -/
theorem proof_passwd_getpwnam_overCap_eq_enametoolong (name : ByteArray)
    (hValid : validPasswdName name = true)
    (hLen : name.size > MAX_PASSWD_NAME_BYTES) :
    Passwd.getpwnam name = pure (.error Errno.ENAMETOOLONG) := by
  simp [Passwd.getpwnam, Passwd.defaultOps, Internal.mkPasswdOpsM, hValid, hLen]
  rfl

/-- Proof of `test_passwd_interface_wiringAndSoundness` for `Interface.lean` definitions. -/
theorem proof_passwd_interface_wiringAndSoundness :
    AllPass (test_passwd_interface_wiringAndSoundness defaultOps getpwuid getpwnam) := by
  intro uid name
  dsimp only [test_passwd_interface_wiringAndSoundness, NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, ?_, ?_, trivial⟩
  · intro hvF
    exact proof_passwd_getpwnam_invalidName_eq_einval name hvF
  · intro hv hlen
    exact proof_passwd_getpwnam_overCap_eq_enametoolong name hv hlen

end LeanSwe.LinuxSyscall.Passwd.Proofs
