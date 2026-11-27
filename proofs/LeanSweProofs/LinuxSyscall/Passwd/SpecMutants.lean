import LeanSweProofs.LinuxSyscall.Passwd.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.LinuxSyscall.Passwd`. -/

namespace LeanSwe.LinuxSyscall.Passwd

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def overCapMutantName : ByteArray :=
  ByteArray.mk (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) 97)

private theorem hasEmbeddedNulLoop_overCapMutantName :
    ∀ k i : Nat, hasEmbeddedNulLoop overCapMutantName i k = false
  | 0, _ => rfl
  | k + 1, i => by
    unfold hasEmbeddedNulLoop
    split
    · rename_i hlt
      have hElem : overCapMutantName[i] = (97 : UInt8) := by
        show (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) (97 : UInt8))[i] = (97 : UInt8)
        exact Array.getElem_replicate ..
      rw [hElem]
      exact hasEmbeddedNulLoop_overCapMutantName k (i + 1)
    · rfl

private theorem validPasswdName_overCapMutantName :
    validPasswdName overCapMutantName = true := by
  unfold validPasswdName hasEmbeddedNul
  rw [hasEmbeddedNulLoop_overCapMutantName]
  rfl

private theorem overCapMutantName_size_gt :
    overCapMutantName.size > MAX_PASSWD_NAME_BYTES := by
  change (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) (97 : UInt8)).size > MAX_PASSWD_NAME_BYTES
  rw [Array.size_replicate]
  omega

example : ¬ Core.AllPass (test_passwd_errno_classificationAndTransient
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    PasswdErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_passwd_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ERANGE then .invalidArg else PasswdErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ERANGE
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_passwd_errno_classificationAndTransient
    Errno.isTransientOsErrno
    PasswdErrorKind.ofErrno
    65536) := by
  intro h
  have h0 := h Errno.EINVAL
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_passwd_entry_utf8Accessors (fun _ => some "")) := by
  intro h
  let bad : PasswdEntry := { (default : PasswdEntry) with homeDir := ByteArray.mk #[0xFF] }
  have h0 := h bad
  dsimp [Core.NondetTest.assert, Bind.bind] at h0
  rcases h0 with ⟨_, _, hHome, _⟩
  exact absurd hHome (by decide)

example : ¬ Core.AllPass (test_passwd_ops_exactContracts
    { modelOps with getpwnam := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h {} 0 ByteArray.empty (ByteArray.mk #[0]) overCapMutantName
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
    (by decide) (by decide) validPasswdName_overCapMutantName overCapMutantName_size_gt
    (by decide) (by decide) (by decide) rfl rfl
  have h1 := h0.1
  dsimp [Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_ops_exactContracts
    { modelOps with getpwuid := fun _ => pure (.ok none) }) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have h0 := h {} 0 ByteArray.empty (ByteArray.mk #[0]) overCapMutantName e
    (by decide) (by decide) validPasswdName_overCapMutantName overCapMutantName_size_gt
    (by decide) (by decide) (by decide) rfl rfl
  have h1 := h0.2.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h1
  have hFst := congrArg Prod.fst h1
  dsimp at hFst
  cases hFst

example : ¬ Core.AllPass (test_passwd_ops_exactContracts
    { modelOps with
      getpwnam := fun name =>
        if !validPasswdName name then pure (.error Errno.EINVAL) else pure (.ok none) }) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have h0 := h {} 0 ByteArray.empty (ByteArray.mk #[0]) overCapMutantName e
    (by decide) (by decide) validPasswdName_overCapMutantName overCapMutantName_size_gt
    (by decide) (by decide) (by decide) rfl rfl
  have h1 := h0.2.1
  dsimp only [PasswdOpsM.getpwnam] at h1
  rw [validPasswdName_overCapMutantName] at h1
  dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_allowedStep_nssSemantics
    (fun s req out =>
      match req, out with
      | .getpwnam _, .notFound => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName (by decide) validPasswdName_overCapMutantName
    overCapMutantName_size_gt
  have h1 := h0.1
  cases h1

example : ¬ Core.AllPass (test_passwd_allowedStep_nssSemantics
    (fun s req out =>
      match req, out with
      | .getpwuid _, .err e => if e == Errno.EPIPE then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName (by decide) validPasswdName_overCapMutantName
    overCapMutantName_size_gt
  have h1 := h0.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_allowedStep_nssSemantics
    (fun s req out =>
      match req, out with
      | .getpwnam nm, .notFound =>
        if nm.size > MAX_PASSWD_NAME_BYTES then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName (by decide) validPasswdName_overCapMutantName
    overCapMutantName_size_gt
  have h1 := h0.2.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h1
  simp [overCapMutantName_size_gt] at h1

example : ¬ Core.AllPass (test_passwd_allowedStep_withOuterSeccomp
    (fun s req out => allowedStep { s with ambientSeccomp := false } req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName validPasswdName_overCapMutantName overCapMutantName_size_gt
  have h1 := h0.2.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind, PasswdState.withOuterSeccomp,
    allowedStep, allowedStepCore, isAllowedPasswdOsErrno, Errno.ENOSYS] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_allowedStep_withOuterSeccomp
    (fun s req out => allowedStep { s with transientNssUnavail := false } req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName validPasswdName_overCapMutantName overCapMutantName_size_gt
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTrans0, _⟩
  dsimp [Core.NondetTest.assert, Bind.bind, PasswdState.withTransientNssUnavail,
    allowedStep, allowedStepCore, isUserspaceInvalidReq, isValidNssFallbackOutcome,
    lookupPasswdByUid, setPasswdByUid] at hTrans0
  cases hTrans0

example : ¬ Core.AllPass (test_passwd_allowedStep_withOuterSeccomp
    (fun s req out =>
      match req, out with
      | .getpwnam nm, .err e =>
        if s.ambientSeccomp && nm.size > MAX_PASSWD_NAME_BYTES && e == Errno.ENOSYS then some s
        else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName validPasswdName_overCapMutantName overCapMutantName_size_gt
  rcases h0 with ⟨_, _, _, _, _, _, _, hOverSec, _⟩
  dsimp [Core.NondetTest.assert, Bind.bind, PasswdState.withOuterSeccomp, Errno.ENOSYS] at hOverSec
  simp [overCapMutantName_size_gt] at hOverSec

example : ¬ Core.AllPass (test_passwd_allowedStep_withOuterSeccomp
    (fun s req out =>
      match out with
      | .err e =>
        if s.ambientSeccomp && !isUserspaceInvalidReq req && e == Errno.EFAULT then some s
        else allowedStep s req out
      | _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName validPasswdName_overCapMutantName overCapMutantName_size_gt
  rcases h0 with ⟨_, _, _, _, _, _, _, _, hEfault, _⟩
  dsimp [Core.NondetTest.assert, Bind.bind, PasswdState.withOuterSeccomp,
    isUserspaceInvalidReq, Errno.EFAULT] at hEfault
  cases hEfault

example : ¬ Core.AllPass (test_passwd_allowedStep_withOuterSeccomp
    (fun s req out =>
      match out with
      | .found _ =>
        if s.ambientSeccomp && !isUserspaceInvalidReq req then some s
        else allowedStep s req out
      | _ => allowedStep s req out)) := by
  intro h
  have h0 := h {} 0 overCapMutantName validPasswdName_overCapMutantName overCapMutantName_size_gt
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWrongUid, _⟩
  dsimp [Core.NondetTest.assert, Bind.bind, PasswdState.withOuterSeccomp,
    isUserspaceInvalidReq] at hWrongUid
  cases hWrongUid

example : ¬ Core.AllPass (test_passwd_modelOps_soundAgainstAllowedStep
    { modelOps with getpwnam := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h {} 0 (ByteArray.mk #[0]) (by decide)
  rcases h0 with ⟨_, _, h2, _⟩
  have hv : validPasswdName (ByteArray.mk #[0]) = false := by decide
  dsimp [Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure,
    outcomeOfEntryOpt, allowedStep, allowedStepCore] at h2
  rw [hv] at h2
  cases h2

private def refPasswdBufSizes : List UInt32 :=
  [4096, 8192, 16384, 32768, 65536]

private def refValidateRawPasswd (pred : PasswdEntry → Bool) :
    Except Errno (Option RawPasswdTuple) → Except Errno (Option PasswdEntry)
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some t) =>
    let entry : PasswdEntry :=
      { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
        homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
    if pred entry then .ok (some entry) else .error Errno.EIO

private def refRetryPasswdLookup {m : Type → Type} [Monad m]
    (once : UInt32 → m (Except Errno (Option RawPasswdTuple)))
    (pred : PasswdEntry → Bool) : List UInt32 → m (Except Errno (Option PasswdEntry))
  | [] => pure (.error Errno.ERANGE)
  | [sz] => return refValidateRawPasswd pred (← once sz)
  | sz :: rest => do
    match ← once sz with
    | .error e =>
      if e == Errno.ERANGE then refRetryPasswdLookup once pred rest else return .error e
    | .ok opt => return refValidateRawPasswd pred (.ok opt)

private def refMkPasswdOpsM {m : Type → Type} [Monad m]
    (gUid : UInt32 → UInt32 → m (Except Errno (Option RawPasswdTuple)))
    (gNam : ByteArray → UInt32 → m (Except Errno (Option RawPasswdTuple))) : PasswdOpsM m :=
  { getpwuid := fun uid =>
      refRetryPasswdLookup (gUid uid) (fun e => e.hasNoEmbeddedNul && e.uid == uid) refPasswdBufSizes
    getpwnam := fun name =>
      if !validPasswdName name then pure (.error Errno.EINVAL)
      else if name.size > MAX_PASSWD_NAME_BYTES then pure (.error Errno.ENAMETOOLONG)
      else refRetryPasswdLookup (gNam name) (fun e => e.hasNoEmbeddedNul && e.name == name) refPasswdBufSizes }

private def refMkPasswdOps := @refMkPasswdOpsM Id _

private def refIoPasswdOps : PasswdOps :=
  @refMkPasswdOpsM IO _ (fun _ _ => pure (.ok none)) (fun _ _ => pure (.ok none))

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_soundAgainstAllowedStep
    (fun gUid gNam => { refMkPasswdOpsM gUid gNam with getpwuid := fun _ => pure (.error Errno.EFAULT) })) := by
  intro h
  let rawGetpwuidStub : UInt32 → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)) :=
    fun _ _ => pure (.error Errno.EIO)
  let rawGetpwnamStub : ByteArray → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)) :=
    fun _ _ => pure (.error Errno.EIO)
  have h0 := h PasswdState.initial 0 ByteArray.empty (ByteArray.mk #[0]) overCapMutantName
    rawGetpwuidStub rawGetpwnamStub
    (by decide) (by decide) validPasswdName_overCapMutantName overCapMutantName_size_gt
    (fun _ _ => by
      dsimp only [rawGetpwuidStub, pure, StateT.pure]
      refine ⟨fun _ => rfl, ?_, ?_⟩
      · simp [PasswdState.initial, EmptyCollection.emptyCollection, Std.TreeMap.empty,
          Std.DTreeMap.empty]
        rfl
      · decide)
    (fun _ _ _ _ => by
      dsimp only [rawGetpwnamStub, pure, StateT.pure]
      refine ⟨fun _ => rfl, ?_, ?_⟩
      · simp [PasswdState.initial, EmptyCollection.emptyCollection, Std.TreeMap.empty,
          Std.DTreeMap.empty]
        rfl
      · decide)
  have h1 := h0.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure,
    outcomeOfEntryOpt, allowedStep, allowedStepCore, isAllowedPasswdOsErrno, Errno.EFAULT] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_soundAgainstAllowedStep
    (fun gUid gNam =>
      { refMkPasswdOpsM gUid gNam with
        getpwnam := fun name =>
          if !validPasswdName name then pure (.error Errno.EINVAL) else pure (.ok none) })) := by
  intro h
  let rawGetpwuidStub : UInt32 → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)) :=
    fun _ _ => pure (.error Errno.EIO)
  let rawGetpwnamStub : ByteArray → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)) :=
    fun _ _ => pure (.error Errno.EIO)
  have h0 := h PasswdState.initial 0 ByteArray.empty (ByteArray.mk #[0]) overCapMutantName
    rawGetpwuidStub rawGetpwnamStub
    (by decide) (by decide) validPasswdName_overCapMutantName overCapMutantName_size_gt
    (fun _ _ => by
      dsimp only [rawGetpwuidStub, pure, StateT.pure]
      refine ⟨fun _ => rfl, ?_, ?_⟩
      · simp [PasswdState.initial, EmptyCollection.emptyCollection, Std.TreeMap.empty,
          Std.DTreeMap.empty]
        rfl
      · decide)
    (fun _ _ _ _ => by
      dsimp only [rawGetpwnamStub, pure, StateT.pure]
      refine ⟨fun _ => rfl, ?_, ?_⟩
      · simp [PasswdState.initial, EmptyCollection.emptyCollection, Std.TreeMap.empty,
          Std.DTreeMap.empty]
        rfl
      · decide)
  have hOver := h0.2.1
  dsimp only [PasswdOpsM.getpwnam] at hOver
  rw [validPasswdName_overCapMutantName] at hOver
  dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run, pure, StateT.pure] at hOver
  cases hOver

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
    (fun gUid gNam =>
      { refMkPasswdOps gUid gNam with getpwuid := fun _ => .error Errno.ERANGE })
    refPasswdBufSizes
    refMkPasswdOps) := by
  intro h
  have h0 := h (fun _ _ => .ok none) (fun _ _ => .ok none) 0 ByteArray.empty
  have h1 := h0.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h1
  cases h1

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
    refMkPasswdOps
    [0]
    refMkPasswdOps) := by
  intro h
  have h0 := h (fun _ _ => .ok none) (fun _ _ => .ok none) 0 ByteArray.empty
  have h1 := h0.1
  cases h1

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
    refMkPasswdOps
    refPasswdBufSizes
    (fun gUid gNam =>
      { refMkPasswdOps gUid gNam with getpwuid := fun _ => .ok none })) := by
  intro h
  have h0 := h (fun _ _ => .error Errno.EIO) (fun _ _ => .ok none) 0 ByteArray.empty
  have hAlias := h0.2.1
  dsimp [Core.NondetTest.assert, Bind.bind, refMkPasswdOps, refMkPasswdOpsM, refPasswdBufSizes,
    refRetryPasswdLookup] at hAlias
  cases hAlias

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
    (fun gUid gNam =>
      { refMkPasswdOps gUid gNam with
        getpwnam := fun name =>
          if !validPasswdName name then
            return .error Errno.EINVAL
          else
            refRetryPasswdLookup
              (gNam name)
              (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
              refPasswdBufSizes })
    refPasswdBufSizes
    refMkPasswdOps) := by
  intro h
  have h0 := h (fun _ _ => .ok none) (fun _ _ => .ok none) 0 overCapMutantName
  have hNam := h0.2.2.2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at hNam
  rw [validPasswdName_overCapMutantName] at hNam
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, overCapMutantName_size_gt,
    refPasswdBufSizes, refRetryPasswdLookup, refValidateRawPasswd,
    bind, pure] at hNam
  cases hNam

example : ¬ Core.AllPass (test_passwd_mkPasswdOps_exactRetryAndDelegation
    (fun gUid gNam =>
      { getpwuid := fun uid =>
          refRetryPasswdLookup
            (gUid uid)
            (fun _ => true)
            refPasswdBufSizes
        getpwnam := (refMkPasswdOps gUid gNam).getpwnam })
    refPasswdBufSizes
    refMkPasswdOps) := by
  intro h
  let badTuple : RawPasswdTuple :=
    (ByteArray.empty, 1, 0, ByteArray.empty, ByteArray.empty, ByteArray.empty)
  have h0 := h (fun _ _ => .ok (some badTuple)) (fun _ _ => .ok none) 0 ByteArray.empty
  dsimp [Core.NondetTest.assert, Bind.bind, refPasswdBufSizes,
    refRetryPasswdLookup, refValidateRawPasswd, bind, pure] at h0
  have hUid := h0.2.2.2.1
  simp [badTuple, PasswdEntry.hasNoEmbeddedNul] at hUid

example : ¬ Core.AllPass (test_passwd_interface_wiringAndSoundness
    refIoPasswdOps
    refIoPasswdOps.getpwuid
    (fun _ => pure (.error Errno.EFAULT))) := by
  intro h
  have h0 := h 0 (ByteArray.mk #[0])
  dsimp [Core.NondetTest.assert, Bind.bind] at h0
  have hFn := h0.2.1
  exact Nonempty.elim (inferInstance : Nonempty (Void IO.RealWorld)) fun w => by
    have hRes := congrArg (fun act => act w) hFn
    dsimp only [refIoPasswdOps, refMkPasswdOpsM] at hRes
    have hv : validPasswdName (ByteArray.mk #[0]) = false := by decide
    simp [hv, pure, instMonadEIO._aux_5, EST.pure, Errno.EFAULT, Errno.EINVAL] at hRes

example : ¬ Core.AllPass (test_passwd_interface_wiringAndSoundness
    { refIoPasswdOps with getpwnam := fun _ => pure (.error Errno.EFAULT) }
    refIoPasswdOps.getpwuid
    refIoPasswdOps.getpwnam) := by
  intro h
  have h0 := h 0 (ByteArray.mk #[0])
  dsimp [Core.NondetTest.assert, Bind.bind] at h0
  have hv : validPasswdName (ByteArray.mk #[0]) = false := by decide
  have hNam := h0.2.2.1 hv
  exact Nonempty.elim (inferInstance : Nonempty (Void IO.RealWorld)) fun w => by
    have hRes := congrArg (fun act => act w) hNam
    simp [pure, instMonadEIO._aux_5, EST.pure, Errno.EFAULT, Errno.EINVAL] at hRes

example : ¬ Core.AllPass (test_passwd_interface_wiringAndSoundness
    { refIoPasswdOps with
      getpwnam := fun name =>
        if !validPasswdName name then pure (.error Errno.EINVAL) else pure (.ok none) }
    refIoPasswdOps.getpwuid
    refIoPasswdOps.getpwnam) := by
  intro h
  have h0 := h 0 overCapMutantName
  have hOver := h0.2.2.2.1 validPasswdName_overCapMutantName overCapMutantName_size_gt
  exact Nonempty.elim (inferInstance : Nonempty (Void IO.RealWorld)) fun w => by
    have hRes := congrArg (fun act => act w) hOver
    dsimp only [PasswdOpsM.getpwnam] at hRes
    rw [validPasswdName_overCapMutantName] at hRes
    simp [pure, instMonadEIO._aux_5, EST.pure, Errno.ENAMETOOLONG] at hRes

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (ops := { getpwuid := fun _ => pure (.error Errno.EMFILE)
              getpwnam := fun name =>
                if !validPasswdName name then pure (.error Errno.EINVAL)
                else if name.size > MAX_PASSWD_NAME_BYTES then pure (.error Errno.ENAMETOOLONG)
                else pure (.error Errno.EMFILE) })) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have hWf1 : (HealthyEnv.initial 1).wf = true := by
    change (HealthyEnv.initial 0 true).wf = true
    decide
  have h0 := h.2.2.2.2.2 (HealthyEnv.initial 1) hWf1 0 ByteArray.empty e
    (by decide) (by decide) (by decide) rfl rfl
  have hPres := congrArg Prod.fst h0.2.2.1.1
  cases hPres

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      healthyStep { env with state := { env.state with transientNssUnavail := false } } req out)) := by
  intro h
  have hSynth := h.2.2.2.2.1.2.2.2.1
  dsimp only [healthyStep, isCriticalFault] at hSynth
  have hAl :
      allowedStep
        { byUid := setPasswdByUid (HealthyEnv.initial 1).state.byUid 0
            (some { name := asciiBytes ['r', 'o', 'o', 't'], uid := 0, gid := 0,
                    gecos := asciiBytes ['r', 'o', 'o', 't'], homeDir := asciiBytes ['/', 'r', 'o', 'o', 't'],
                    shell := asciiBytes ['/', 'b', 'i', 'n', '/', 'b', 'a', 's', 'h'] })
          byName := (HealthyEnv.initial 1).state.byName
          ambientSeccomp := (HealthyEnv.initial 1).state.ambientSeccomp
          transientNssUnavail := false }
        (.getpwuid 0)
        (.found { name := asciiBytes ['r', 'o', 'o', 't'], uid := 0, gid := 0,
                  gecos := asciiBytes ['S', 'u', 'p', 'e', 'r'], homeDir := asciiBytes ['/', 'r', 'o', 'o', 't'],
                  shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }) = none := rfl
  rw [hAl] at hSynth
  simp only at hSynth
  cases hSynth

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      match out with
      | .err e => if e == Errno.EMFILE then none else healthyStep env req out
      | _ => healthyStep env req out)) := by
  intro h
  have hEmf := h.2.2.1.1
  dsimp [Errno.EMFILE] at hEmf
  cases hEmf

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if !env.wf then none
      else (allowedStep env.state req out).map (fun s' => { state := s', eintrBudget := env.eintrBudget }))) := by
  intro h
  have hEio := h.2.2.2.1.2.1
  have hWf1 : (HealthyEnv.initial 1).wf = true := by
    change (HealthyEnv.initial 0 true).wf = true
    decide
  change (if !(HealthyEnv.initial 1).wf then none
    else (allowedStep (HealthyEnv.initial 1).state (.getpwuid 0) (.err Errno.EIO)).map
      (fun s' => ({ state := s', eintrBudget := (HealthyEnv.initial 1).eintrBudget } : HealthyEnv))) = none at hEio
  rw [hWf1] at hEio
  have hAl : allowedStep (HealthyEnv.initial 1).state (.getpwuid 0) (.err Errno.EIO) =
      some (HealthyEnv.initial 1).state := rfl
  rw [hAl] at hEio
  cases hEio

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (ops := { getpwuid := fun uid env =>
                match lookupPasswdByUid env.state.byUid uid with
                | some _ => healthyModelOps.getpwuid uid env
                | none => (.error Errno.EMFILE, env)
              getpwnam := healthyModelOps.getpwnam })) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.mk #[97], uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have hWf1 : (HealthyEnv.initial 1).wf = true := by
    change (HealthyEnv.initial 0).wf = true
    decide
  have h0 := h.2.2.2.2.2 (HealthyEnv.initial 1) hWf1 0 (ByteArray.mk #[97]) e
    (by decide) (by decide) (by decide) rfl rfl
  have hEq := congrArg Prod.fst h0.1.1
  have hInitNone : lookupPasswdByUid (HealthyEnv.initial 1).state.byUid 0 = none := rfl
  dsimp only [StateT.run, modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set] at hEq
  rw [hInitNone] at hEq
  cases hEq

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (ops := { getpwuid := healthyModelOps.getpwuid
              getpwnam := fun name env =>
                if !validPasswdName name || decide (name.size > MAX_PASSWD_NAME_BYTES) then
                  (.ok none, env)
                else
                  healthyModelOps.getpwnam name env })) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have hWf1 : (HealthyEnv.initial 1).wf = true := by
    change (HealthyEnv.initial 0).wf = true
    decide
  have hRest := h.2.2.2.2.2 (HealthyEnv.initial 1) hWf1 0 ByteArray.empty e
    (by decide) (by decide) (by decide) rfl rfl
  have hRaw := congrArg Prod.fst (hRest.2.2.2 (ByteArray.mk #[0])).1.1
  have hvBad : validPasswdName (ByteArray.mk #[0]) = false := by decide
  dsimp only [StateT.run, modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure] at hRaw
  rw [hvBad] at hRaw
  cases hRaw

example : ¬ Core.AllPass (test_passwd_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if decide (env.eintrBudget ≥ 2) && isEintrOutcome out then
        (healthyStep env req out).map (fun env' => { env' with eintrBudget := env.eintrBudget })
      else
        healthyStep env req out)) := by
  intro h
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have hWf1 : (HealthyEnv.initial 1).wf = true := by
    change (HealthyEnv.initial 0).wf = true
    decide
  have hRest := h.2.2.2.2.2 (HealthyEnv.initial 1) hWf1 0 ByteArray.empty e
    (by decide) (by decide) (by decide) rfl rfl
  have hStep := ((hRest.2.2.2 ByteArray.empty).2 (HealthyEnv.initial 2) (.getpwuid 0) (.err Errno.EINTR)).1
  have hWf2 : (HealthyEnv.initial 2).wf = true := by
    change (HealthyEnv.initial 0).wf = true
    decide
  have hAl : allowedStep (HealthyEnv.initial 2).state (.getpwuid 0) (.err Errno.EINTR) =
      some (HealthyEnv.initial 2).state := rfl
  dsimp only [healthyStep] at hStep
  rw [hWf2, hAl] at hStep
  exact absurd (congrArg (Option.map HealthyEnv.eintrBudget) hStep) (by decide)

end LeanSwe.LinuxSyscall.Passwd
