import LeanSwe.LinuxSyscall.Passwd.Proofs.ModelCore

/-!
Outer-`seccomp` / transient NSS fallback step proofs and `modelOps` soundness against `allowedStep`
for `LeanSwe.LinuxSyscall.Passwd`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

/-- Proof of `test_passwd_allowedStep_withOuterSeccomp` for `allowedStep`. -/
theorem proof_passwd_allowedStep_withOuterSeccomp :
    AllPass test_passwd_allowedStep_withOuterSeccomp := by
  intro sRaw uid overCapName hOverValid hOverSize
  dsimp only [test_passwd_allowedStep_withOuterSeccomp, NondetTest.assert, Bind.bind]
  let sBase : PasswdState := { sRaw with byUid := ∅, byName := ∅ }
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  let badName := ByteArray.mk #[114, 0, 111]
  let entryOk : PasswdEntry :=
    { name := rootName, uid := uid, gid := 0, gecos := rootName,
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't'],
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let entryOther : PasswdEntry := { entryOk with homeDir := asciiBytes ['/', 't', 'm', 'p'] }
  let entryWrongUid : PasswdEntry := { entryOk with uid := uid + 1 }
  let entryWrongName : PasswdEntry := { entryOk with name := asciiBytes ['o', 't', 'h', 'e', 'r'] }
  let entryWithNul : PasswdEntry := { entryOk with homeDir := ByteArray.mk #[47, 0, 120] }
  have hRootValid : validPasswdName rootName = true := by decide
  have hRootSize : ¬ (rootName.size > MAX_PASSWD_NAME_BYTES) := by decide
  have hBadValid : validPasswdName badName = false := by decide
  have hEntryOkNul : entryOk.hasNoEmbeddedNul = true := by
    simp only [entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWithNulF : entryWithNul.hasNoEmbeddedNul = false := by
    simp only [entryWithNul, entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWrongUidF : (entryWrongUid.uid == uid) = false := by
    have hLt : uid.toNat < 2 ^ 32 := uid.toNat_lt
    have hNe : uid + 1 ≠ uid := by
      intro h
      have h2 := congrArg UInt32.toNat h
      rw [UInt32.toNat_add] at h2
      have hOne : (1 : UInt32).toNat = 1 := rfl
      rw [hOne] at h2
      omega
    simp [entryWrongUid, hNe]
  have hWrongNameF : (entryWrongName.name == rootName) = false := by
    simp [entryWrongName, rootName, asciiBytes]
  let sNoSec : PasswdState := { sBase with ambientSeccomp := false, transientNssUnavail := false }
  let sSec := sNoSec.withOuterSeccomp
  let sTrans := sNoSec.withTransientNssUnavail
  let sSecFound : PasswdState :=
    { sSec with
      byUid := setPasswdByUid sSec.byUid uid (some entryOther)
      byName := setPasswdByName sSec.byName rootName (some entryOther) }
  let sTransFound : PasswdState :=
    { sTrans with
      byUid := setPasswdByUid sTrans.byUid uid (some entryOther)
      byName := setPasswdByName sTrans.byName rootName (some entryOther) }
  have hU : lookupPasswdByUid sBase.byUid uid = none := rfl
  have hN : lookupPasswdByName sBase.byName rootName = none := rfl
  have hBase :
      PasswdState.initial.ambientSeccomp = false ∧
      PasswdState.initial.transientNssUnavail = false ∧
      sSec.ambientSeccomp = true ∧
      allowedStep sNoSec (.getpwuid uid) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwuid uid) (.err Errno.ENOSYS) = some sSec ∧
      allowedStep sSec (.getpwnam rootName) (.err Errno.EPERM) = some sSec ∧
      allowedStep sSec (.getpwnam badName) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwnam overCapName) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwuid uid) (.err Errno.EFAULT) = none ∧
      allowedStep sSec (.getpwnam rootName) (.err Errno.EFAULT) = none ∧
      allowedStep sSec (.getpwuid uid) (.err 0) = none ∧
      allowedStep sSec (.getpwuid uid) (.err 4096) = none := by
    simp [PasswdState.initial, PasswdState.withOuterSeccomp, sNoSec, sSec, rootName, badName,
      allowedStep, allowedStepCore, isUserspaceInvalidReq, hRootValid, hRootSize, hBadValid,
      hOverValid, hOverSize, hU, hN, isAllowedPasswdOsErrno, Errno.ENOSYS, Errno.EINVAL,
      Errno.EPERM, Errno.EFAULT, Errno.ERANGE, Errno.ENOENT, Errno.ENXIO, Errno.EINTR,
      Errno.EIO, Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.EACCES, Errno.EAGAIN,
      Errno.ENODEV, Errno.ENOTDIR, Errno.EISDIR, Errno.ESPIPE, Errno.ENAMETOOLONG, Errno.ELOOP]
  have hSecF :
      allowedStep sSecFound (.getpwuid uid) .notFound = some sSecFound ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryOk) = some sSecFound ∧
      allowedStep sSecFound (.getpwnam rootName) .notFound = some sSecFound ∧
      allowedStep sSecFound (.getpwnam rootName) (.found entryOk) = some sSecFound ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryWrongUid) = none ∧
      allowedStep sSecFound (.getpwnam rootName) (.found entryWrongName) = none ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryWithNul) = none ∧
      allowedStep sSecFound (.getpwnam badName) .notFound = none ∧
      allowedStep sSecFound (.getpwnam overCapName) .notFound = none := by
    have hNeOther : (entryOk == entryOther) = false := by
      simp [entryOk, entryOther, asciiBytes]
    have hNeWrongName : (entryWrongName == entryOther) = false := by
      simp [entryWrongName, entryOk, entryOther, rootName, asciiBytes]
    simp [sSecFound, sSec, sNoSec, PasswdState.withOuterSeccomp, allowedStep, allowedStepCore,
      isUserspaceInvalidReq, isValidNssFallbackOutcome, lookupPasswdByUid_set_self,
      lookupPasswdByName_set_self, hRootValid, hRootSize, hBadValid, hOverValid, hOverSize,
      hEntryOkNul, hWithNulF, hWrongUidF, hWrongNameF, hNeOther, hNeWrongName, entryOk]
  have hTransF :
      allowedStep sTransFound (.getpwuid uid) .notFound = some sTransFound ∧
      allowedStep sTransFound (.getpwuid uid) (.found entryOk) = some sTransFound ∧
      allowedStep sTransFound (.getpwnam rootName) .notFound = some sTransFound ∧
      allowedStep sTransFound (.getpwnam rootName) (.found entryOk) = some sTransFound ∧
      allowedStep sTransFound (.getpwuid uid) (.found entryWrongUid) = none ∧
      allowedStep sTransFound (.getpwnam rootName) (.found entryWrongName) = none ∧
      allowedStep sTransFound (.getpwuid uid) (.err Errno.EPIPE) = none ∧
      allowedStep sTransFound (.getpwnam badName) .notFound = none ∧
      allowedStep sTransFound (.getpwnam overCapName) .notFound = none := by
    have hNeOther : (entryOk == entryOther) = false := by
      simp [entryOk, entryOther, asciiBytes]
    have hNeWrongName : (entryWrongName == entryOther) = false := by
      simp [entryWrongName, entryOk, entryOther, rootName, asciiBytes]
    simp [sTransFound, sTrans, sNoSec, PasswdState.withTransientNssUnavail, allowedStep,
      allowedStepCore, isUserspaceInvalidReq, isValidNssFallbackOutcome, lookupPasswdByUid_set_self,
      lookupPasswdByName_set_self, hRootValid, hRootSize, hBadValid, hOverValid, hOverSize,
      hEntryOkNul, hWrongUidF, hWrongNameF, hNeOther, hNeWrongName, isAllowedPasswdOsErrno,
      Errno.EPIPE, Errno.ERANGE, Errno.EINTR, Errno.EIO, Errno.EMFILE, Errno.ENFILE,
      Errno.ENOMEM, Errno.EPERM, Errno.EACCES, Errno.ENOENT, Errno.ENXIO, Errno.EAGAIN,
      Errno.ENODEV, Errno.ENOTDIR, Errno.EISDIR, Errno.ESPIPE, Errno.ENAMETOOLONG, Errno.ELOOP,
      entryOk]
  rcases hBase with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
  rcases hSecF with ⟨sf0, sf1, sf2, sf3, sf4, sf5, sf6, sf7, sf8⟩
  rcases hTransF with ⟨tf0, tf1, tf2, tf3, tf4, tf5, tf6, tf7, tf8⟩
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
    sf0, sf1, sf2, sf3, sf4, sf5, sf6, sf7, sf8,
    tf0, tf1, tf2, tf3, tf4, tf5, tf6, tf7, tf8, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_allowedStep_withOuterSeccomp`. -/
theorem reach_passwd_allowedStep_withOuterSeccomp :
    CanReach test_passwd_allowedStep_withOuterSeccomp := by
  refine ⟨PasswdState.initial, 0, overCapWitness,
    validPasswdName_overCapWitness, overCapWitness_size_gt, ?_⟩
  exact proof_passwd_allowedStep_withOuterSeccomp PasswdState.initial 0 overCapWitness
    validPasswdName_overCapWitness overCapWitness_size_gt

/-- Proof of `test_passwd_modelOps_soundAgainstAllowedStep` for `modelOps` and `allowedStep`. -/
theorem proof_passwd_modelOps_soundAgainstAllowedStep :
    AllPass (test_passwd_modelOps_soundAgainstAllowedStep modelOps) := by
  intro s uid name hwf
  simp only [PasswdState.isWellFormed, Bool.and_eq_true] at hwf
  have ⟨hwfUid, hwfName⟩ := hwf
  dsimp only [test_passwd_modelOps_soundAgainstAllowedStep, NondetTest.assert, Bind.bind]
  change allowedStep s (.getpwuid uid) (outcomeOfEntryOpt (modelOps.getpwuid uid s).1) =
      some (modelOps.getpwuid uid s).2 ∧
    (modelOps.getpwuid uid s).2.isWellFormed = true ∧
    allowedStep s (.getpwnam name) (outcomeOfEntryOpt (modelOps.getpwnam name s).1) =
      some (modelOps.getpwnam name s).2 ∧
    (modelOps.getpwnam name s).2.isWellFormed = true ∧ True
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [modelOps_getpwuid_eval]
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb]
    | some opt =>
      cases opt with
      | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb]
      | some e =>
        have hv := lookupPasswdByUid_wellFormed hwfUid hdb
        simp only [isValidUidEntry, Bool.and_eq_true] at hv
        have ⟨hNul, hUid⟩ := hv
        simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb, hNul, hUid]
  · rw [modelOps_getpwuid_eval]
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none =>
      simp only [PasswdState.isWellFormed, Bool.and_eq_true]
      exact ⟨setPasswdByUid_wellFormed s.byUid uid none hwfUid rfl, hwfName⟩
    | some opt =>
      cases opt with
      | none =>
        simp only [PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
      | some e =>
        have hv := lookupPasswdByUid_wellFormed hwfUid hdb
        simp only [isValidUidEntry, Bool.and_eq_true] at hv
        simp only [hv.1, hv.2, PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
  · rw [modelOps_getpwnam_eval]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, Errno.ENAMETOOLONG]
      · simp only [hlen, ↓reduceIte]
        cases hdb : lookupPasswdByName s.byName name with
        | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb]
        | some opt =>
          cases opt with
          | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb]
          | some e =>
            have hve := lookupPasswdByName_wellFormed hwfName hdb
            simp only [isValidNameEntry, Bool.and_eq_true] at hve
            rcases hve with ⟨⟨⟨_, _⟩, hNul⟩, hNam⟩
            simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb, hNul, hNam]
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, outcomeOfEntryOpt, allowedStep, allowedStepCore, Errno.EINVAL]
  · rw [modelOps_getpwnam_eval]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp only [hlen, ↓reduceIte, PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hValidNone : isValidNameEntry name none = true := by
          simp [isValidNameEntry, hv, hlenLe]
        cases hdb : lookupPasswdByName s.byName name with
        | none =>
          simp only [PasswdState.isWellFormed, Bool.and_eq_true]
          exact ⟨hwfUid, setPasswdByName_wellFormed s.byName name none hwfName hValidNone⟩
        | some opt =>
          cases opt with
          | none =>
            simp only [PasswdState.isWellFormed, Bool.and_eq_true]
            exact ⟨hwfUid, hwfName⟩
          | some e =>
            have hve := lookupPasswdByName_wellFormed hwfName hdb
            simp only [isValidNameEntry, Bool.and_eq_true] at hve
            rcases hve with ⟨⟨⟨_, _⟩, hNul⟩, hNam⟩
            simp only [hNul, hNam, PasswdState.isWellFormed, Bool.and_eq_true]
            exact ⟨hwfUid, hwfName⟩
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp only [hvF, Bool.not_false, ↓reduceIte, PasswdState.isWellFormed, Bool.and_eq_true]
      exact ⟨hwfUid, hwfName⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_modelOps_soundAgainstAllowedStep`. -/
theorem reach_passwd_modelOps_soundAgainstAllowedStep :
    CanReach (test_passwd_modelOps_soundAgainstAllowedStep modelOps) := by
  refine ⟨PasswdState.initial, 0, ByteArray.empty, by decide, ?_⟩
  exact proof_passwd_modelOps_soundAgainstAllowedStep PasswdState.initial 0 ByteArray.empty (by decide)

end LeanSwe.LinuxSyscall.Passwd.Proofs
