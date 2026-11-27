import LeanSweProofs.LinuxSyscall.Passwd.Proofs.ModelSoundness

/-!
Healthy-host step refinement (`healthyStep`, `healthyModelOps`, and lens lifting) for
`LeanSwe.LinuxSyscall.Passwd`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

private theorem allowedStepCore_preserves_wf_and_ambient
    (s s' : PasswdState) (req : PasswdReq) (out : PasswdOutcome)
    (hwf : s.isWellFormed = true)
    (h : allowedStepCore s req out = some s') :
    s'.isWellFormed = true ∧ s'.ambientSeccomp = s.ambientSeccomp := by
  simp only [PasswdState.isWellFormed, Bool.and_eq_true] at hwf
  rcases hwf with ⟨hwfUid, hwfName⟩
  cases req with
  | getpwuid uid =>
    simp only [allowedStepCore] at h
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none =>
      rw [hdb] at h
      cases out with
      | notFound =>
        dsimp only at h
        injection h with hEq; subst hEq
        exact ⟨Bool.and_eq_true_iff.mpr ⟨setPasswdByUid_wellFormed s.byUid uid none hwfUid rfl, hwfName⟩, rfl⟩
      | found entry =>
        dsimp only at h
        split at h
        · rename_i hok
          injection h with hEq; subst hEq
          exact ⟨Bool.and_eq_true_iff.mpr ⟨setPasswdByUid_wellFormed s.byUid uid (some entry) hwfUid hok, hwfName⟩, rfl⟩
        · contradiction
      | err e =>
        dsimp only at h
        split at h <;> simp_all [PasswdState.isWellFormed]
    | some opt =>
      rw [hdb] at h
      cases opt with
      | none =>
        cases out with
        | notFound =>
          dsimp only at h
          injection h with hEq; subst hEq
          exact ⟨Bool.and_eq_true_iff.mpr ⟨hwfUid, hwfName⟩, rfl⟩
        | found _ => contradiction
        | err e =>
          dsimp only at h
          split at h <;> simp_all [PasswdState.isWellFormed]
      | some expected =>
        cases out with
        | notFound => contradiction
        | found entry =>
          dsimp only at h
          split at h <;> simp_all [PasswdState.isWellFormed]
        | err e =>
          dsimp only at h
          split at h <;> simp_all [PasswdState.isWellFormed]
  | getpwnam name =>
    unfold allowedStepCore at h
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp only [hlen, ↓reduceIte] at h
        cases out with
        | err e =>
          dsimp only at h
          split at h <;> simp_all [PasswdState.isWellFormed]
        | _ => simp at h
      · simp only [hlen, ↓reduceIte] at h
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        cases hdb : lookupPasswdByName s.byName name with
        | none =>
          rw [hdb] at h
          cases out with
          | notFound =>
            dsimp only at h
            injection h with hEq; subst hEq
            have hvn : isValidNameEntry name none = true := by
              simp [isValidNameEntry, hv, hlenLe]
            exact ⟨Bool.and_eq_true_iff.mpr ⟨hwfUid, setPasswdByName_wellFormed s.byName name none hwfName hvn⟩, rfl⟩
          | found entry =>
            dsimp only at h
            split at h
            · rename_i hok
              injection h with hEq; subst hEq
              have hve : isValidNameEntry name (some entry) = true := by
                simp only [Bool.and_eq_true] at hok
                simp [isValidNameEntry, hv, hlenLe, hok.1, hok.2]
              exact ⟨Bool.and_eq_true_iff.mpr ⟨hwfUid, setPasswdByName_wellFormed s.byName name (some entry) hwfName hve⟩, rfl⟩
            · contradiction
          | err e =>
            dsimp only at h
            split at h <;> simp_all [PasswdState.isWellFormed]
        | some opt =>
          rw [hdb] at h
          cases opt with
          | none =>
            cases out with
            | notFound =>
              dsimp only at h
              injection h with hEq; subst hEq
              exact ⟨Bool.and_eq_true_iff.mpr ⟨hwfUid, hwfName⟩, rfl⟩
            | found _ => contradiction
            | err e =>
              dsimp only at h
              split at h <;> simp_all [PasswdState.isWellFormed]
          | some expected =>
            cases out with
            | notFound => contradiction
            | found entry =>
              dsimp only at h
              split at h <;> simp_all [PasswdState.isWellFormed]
            | err e =>
              dsimp only at h
              split at h <;> simp_all [PasswdState.isWellFormed]
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp only [hvF, Bool.not_false, ↓reduceIte] at h
      cases out with
      | err e =>
        simp only at h
        split at h <;> simp_all [PasswdState.isWellFormed]
      | _ => simp at h

private theorem allowedStep_preserves_wf_and_ambient
    (s s' : PasswdState) (req : PasswdReq) (out : PasswdOutcome)
    (hwf : s.isWellFormed = true)
    (h : allowedStep s req out = some s') :
    s'.isWellFormed = true ∧ s'.ambientSeccomp = s.ambientSeccomp := by
  unfold allowedStep at h
  cases hc : allowedStepCore s req out with
  | some sc =>
    rw [hc] at h
    injection h with hEq; subst hEq
    exact allowedStepCore_preserves_wf_and_ambient s sc req out hwf hc
  | none =>
    rw [hc] at h
    dsimp only at h
    split at h
    · cases out <;> dsimp only at h <;> split at h <;> simp_all
    · contradiction

/-- Initial healthy `Passwd` environments satisfy `HealthyEnv.wf` for both `transientNssUnavail` settings. -/
theorem healthyEnv_initial_wf (budget : Nat) (transientNssUnavail : Bool := true) :
    (HealthyEnv.initial budget transientNssUnavail).wf = true := by
  cases transientNssUnavail <;>
    (first
      | (change (HealthyEnv.initial 0 false).wf = true; decide)
      | (change (HealthyEnv.initial 0 true).wf = true; decide))

/-- Tightness by construction: every `allowedStep` transition from a healthy `Passwd` environment without curated critical faults (and with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    (env : HealthyEnv) (req : PasswdReq) (out : PasswdOutcome) (s' : PasswdState)
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget)
    (hNoCrit : isCriticalFault out = false) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hb : env.eintrBudget > 0 := hBudget hEi
    simp [hb]

/-- Soundness of `healthyStep` with respect to `allowedStep`: every `healthyStep` transition is a valid `allowedStep` transition, preserves `HealthyEnv.wf`, excludes curated critical OS faults, and strictly decreases `eintrBudget` on `EINTR`. -/
theorem healthyStep_implies_allowedStep
    (env env' : HealthyEnv) (req : PasswdReq) (out : PasswdOutcome)
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    env.wf = true ∧
    env'.wf = true ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env'.eintrBudget < env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by
      cases hw : env.wf <;> simp_all
    have hNoCrit : isCriticalFault out = false := by
      cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => rw [hAl] at h; contradiction
    | some s' =>
      rw [hAl] at h
      dsimp only at h
      have hWfParts : env.state.ambientSeccomp = false ∧ env.state.isWellFormed = true := by
        unfold HealthyEnv.wf at hWf
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hWf
        exact hWf
      rcases allowedStep_preserves_wf_and_ambient env.state s' req out hWfParts.2 hAl with ⟨hwf', hamb'⟩
      have hSec' : s'.ambientSeccomp = false := hamb'.trans hWfParts.1
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        dsimp only
        exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec', hwf'], hNoCrit, Nat.le_refl _, fun hc => by cases hc⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hb : env.eintrBudget > 0
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          subst h
          dsimp only
          exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec', hwf'], hNoCrit, Nat.sub_le _ _, fun _ => by omega⟩
        · simp [hb] at h

/-- Reference `healthyModelOps` refines `healthyStep` universally across all `getpwuid` and `getpwnam` requests. -/
theorem healthyModelOps_refinesHealthyPasswd :
    RefinesHealthyPasswd healthyModelOps := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  have hWfParts : env.state.ambientSeccomp = false ∧ env.state.isWellFormed = true := by
    unfold HealthyEnv.wf at hWf
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hWf
    exact hWf
  have hwfUid : (env.state.byUid.foldl (fun acc k v => acc && isValidUidEntry k v) true) = true := by
    simp only [PasswdState.isWellFormed, Bool.and_eq_true] at hWfParts
    exact hWfParts.2.1
  have hwfNam : (env.state.byName.foldl (fun acc k v => acc && isValidNameEntry k v) true) = true := by
    simp only [PasswdState.isWellFormed, Bool.and_eq_true] at hWfParts
    exact hWfParts.2.2
  cases req with
  | getpwuid uid =>
    have hSound := (proof_passwd_modelOps_soundAgainstAllowedStep env.state uid ByteArray.empty hWfParts.2).1
    have hNoErr : isCriticalFault (outcomeOfEntryOpt (modelOps.getpwuid uid env.state).1) = false ∧
        isEintrOutcome (outcomeOfEntryOpt (modelOps.getpwuid uid env.state).1) = false := by
      rw [modelOps_getpwuid_eval]
      cases hdb : lookupPasswdByUid env.state.byUid uid with
      | none => exact ⟨rfl, rfl⟩
      | some opt =>
        cases opt with
        | none => exact ⟨rfl, rfl⟩
        | some e =>
          have hv := lookupPasswdByUid_wellFormed hwfUid hdb
          simp only [isValidUidEntry, Bool.and_eq_true] at hv
          simp [hv.1, hv.2, outcomeOfEntryOpt, isCriticalFault, isEintrOutcome]
    have hTight := allowedStep_healthy_tight env (.getpwuid uid) _ _ hSound hWf (by simp [hNoErr.2]) hNoErr.1
    simp only [hNoErr.2, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execPasswdReq, healthyModelOps, PasswdOpsM.getpwuid, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight
  | getpwnam name =>
    have hSound := (proof_passwd_modelOps_soundAgainstAllowedStep env.state 0 name hWfParts.2).2.2.1
    have hNoErr : isCriticalFault (outcomeOfEntryOpt (modelOps.getpwnam name env.state).1) = false ∧
        isEintrOutcome (outcomeOfEntryOpt (modelOps.getpwnam name env.state).1) = false := by
      rw [modelOps_getpwnam_eval]
      by_cases hv : validPasswdName name = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
        · simp only [hlen, ↓reduceIte]
          exact ⟨by decide, by decide⟩
        · simp only [hlen, ↓reduceIte]
          cases hdb : lookupPasswdByName env.state.byName name with
          | none => exact ⟨rfl, rfl⟩
          | some opt =>
            cases opt with
            | none => exact ⟨rfl, rfl⟩
            | some e =>
              have hve := lookupPasswdByName_wellFormed hwfNam hdb
              simp only [isValidNameEntry, Bool.and_eq_true] at hve
              rcases hve with ⟨⟨⟨_, _⟩, hNul⟩, hNam⟩
              simp [hNul, hNam, outcomeOfEntryOpt, isCriticalFault, isEintrOutcome]
      · have hvF : validPasswdName name = false := by
          cases hb : validPasswdName name <;> simp_all
        simp only [hvF, Bool.not_false, ↓reduceIte]
        exact ⟨by decide, by decide⟩
    have hTight := allowedStep_healthy_tight env (.getpwnam name) _ _ hSound hWf (by simp [hNoErr.2]) hNoErr.1
    simp only [hNoErr.2, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execPasswdReq, healthyModelOps, PasswdOpsM.getpwnam, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight

/-- Lens-lifting composition theorem: lifting any `ops` satisfying `RefinesHealthyPasswd` along `(getEnv, setEnv)` with `∀ w e, getEnv (setEnv w e) = e` satisfies `RefinesHealthyPasswdAt getEnv`. -/
theorem refinesHealthyPasswdAt_of_lens
    {W : Type} (getEnv : W → HealthyEnv) (setEnv : W → HealthyEnv → W)
    (hGetSet : ∀ (w : W) (e : HealthyEnv), getEnv (setEnv w e) = e)
    {ops : PasswdOpsM (StateM HealthyEnv)} (hRef : RefinesHealthyPasswd ops) :
    RefinesHealthyPasswdAt getEnv
      { getpwuid := fun uid w =>
          let (res, e') := (ops.getpwuid uid).run (getEnv w)
          (res, setEnv w e')
        getpwnam := fun name w =>
          let (res, e') := (ops.getpwnam name).run (getEnv w)
          (res, setEnv w e') } := by
  intro w req hWf
  have hStep := hRef (getEnv w) req hWf
  cases req with
  | getpwuid uid =>
    dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.getpwuid uid (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep
  | getpwnam name =>
    dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.getpwnam name (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep

/-- Proof of `test_passwd_healthyStep_and_healthyModelOps`. -/
theorem proof_passwd_healthyStep_and_healthyModelOps :
    AllPass test_passwd_healthyStep_and_healthyModelOps := by
  dsimp only [test_passwd_healthyStep_and_healthyModelOps, NondetTest.assert, Bind.bind, Pure.pure]
  have hWf1 : (HealthyEnv.initial 1).wf = true := healthyEnv_initial_wf 1 true
  have hWf0 : (HealthyEnv.initial 0).wf = true := healthyEnv_initial_wf 0 true
  have hWfS1 : (HealthyEnv.initial 1 false).wf = true := healthyEnv_initial_wf 1 false
  have hGuard1 : ∀ out, isCriticalFault out = false →
      (!(HealthyEnv.initial 1).wf || isCriticalFault out) = false := by
    intro out hc; simp [hWf1, hc]
  have hGuard0 : ∀ out, isCriticalFault out = false →
      (!(HealthyEnv.initial 0).wf || isCriticalFault out) = false := by
    intro out hc; simp [hWf0, hc]
  refine ⟨⟨hWf1, hWf0, hWfS1⟩, rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · unfold healthyStep
      rw [hGuard1 _ (by decide)]
      rfl
    · unfold healthyStep
      rw [hGuard1 _ (by decide)]
      rfl
    · unfold healthyStep
      rw [hGuard1 _ (by decide)]
      rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold healthyStep
      have hc : isCriticalFault (.err Errno.ENOMEM) = true := by decide
      simp [hc]
    · unfold healthyStep
      have hc : isCriticalFault (.err Errno.EIO) = true := by decide
      simp [hc]
    · unfold healthyStep
      have hc : isCriticalFault (.err Errno.ENFILE) = true := by decide
      simp [hc]
    · unfold healthyStep
      rw [hGuard1 _ (by decide)]
      rfl
  · let rootEtc : PasswdEntry :=
      { name := asciiBytes ['r', 'o', 'o', 't']
        uid := 0
        gid := 0
        gecos := asciiBytes ['r', 'o', 'o', 't']
        homeDir := asciiBytes ['/', 'r', 'o', 'o', 't']
        shell := asciiBytes ['/', 'b', 'i', 'n', '/', 'b', 'a', 's', 'h'] }
    have hEtcValid : isValidUidEntry 0 (some rootEtc) = true := by decide
    let e1Found : HealthyEnv :=
      { state := { (HealthyEnv.initial 1).state with
                    byUid := setPasswdByUid (HealthyEnv.initial 1).state.byUid 0 (some rootEtc) }
        eintrBudget := (HealthyEnv.initial 1).eintrBudget }
    let eStrictFound : HealthyEnv :=
      { state := { (HealthyEnv.initial 1 false).state with
                    byUid := setPasswdByUid (HealthyEnv.initial 1 false).state.byUid 0 (some rootEtc) }
        eintrBudget := (HealthyEnv.initial 1 false).eintrBudget }
    have hWfE1Found : e1Found.wf = true := by
      simp only [e1Found, HealthyEnv.wf, HealthyEnv.initial, PasswdState.initial,
        PasswdState.isWellFormed, Bool.not_false, Bool.true_and, Bool.and_eq_true]
      exact ⟨setPasswdByUid_wellFormed ∅ 0 (some rootEtc) (by decide) hEtcValid, by decide⟩
    have hWfEStrictFound : eStrictFound.wf = true := by
      simp only [eStrictFound, HealthyEnv.wf, HealthyEnv.initial, PasswdState.initial,
        PasswdState.isWellFormed, Bool.not_false, Bool.true_and, Bool.and_eq_true]
      exact ⟨setPasswdByUid_wellFormed ∅ 0 (some rootEtc) (by decide) hEtcValid, by decide⟩
    have hGE1Found : ∀ out, isCriticalFault out = false →
        (!e1Found.wf || isCriticalFault out) = false := by
      intro out hc; simp [hWfE1Found, hc]
    have hGEStrictFound : ∀ out, isCriticalFault out = false →
        (!eStrictFound.wf || isCriticalFault out) = false := by
      intro out hc; simp [hWfEStrictFound, hc]
    have hStepE1Etc : healthyStep (HealthyEnv.initial 1) (.getpwuid 0) (.found rootEtc) =
        some e1Found := by
      unfold healthyStep
      rw [hGuard1 _ rfl]
      rfl
    have hStepS1Etc : healthyStep (HealthyEnv.initial 1 false) (.getpwuid 0) (.found rootEtc) =
        some eStrictFound := by
      unfold healthyStep
      have hGS1 : (!(HealthyEnv.initial 1 false).wf || isCriticalFault (.found rootEtc)) = false := by
        simp [hWfS1, isCriticalFault]
      rw [hGS1]
      rfl
    refine ⟨?_, ?_, hStepE1Etc, ?_, ?_, ?_, ?_, hStepS1Etc, ?_, ?_⟩
    · unfold healthyStep; rw [hGuard1 _ (by decide)]; rfl
    · unfold healthyStep; rw [hGuard0 _ (by decide)]; rfl
    · unfold healthyStep; rw [hGE1Found _ rfl]; rfl
    · unfold healthyStep; rw [hGE1Found _ rfl]; rfl
    · unfold healthyStep; rw [hGE1Found _ rfl]; rfl
    · unfold healthyStep; rw [hGE1Found _ rfl]; rfl
    · unfold healthyStep; rw [hGEStrictFound _ rfl]; rfl
    · unfold healthyStep; rw [hGEStrictFound _ rfl]; rfl
  · intro env hWf uid name entry hNamValid hNamLen hNul hUid hName
    subst hUid
    subst hName
    have hNamNotGt : ¬ (entry.name.size > MAX_PASSWD_NAME_BYTES) := by omega
    have hStepUid := healthyModelOps_refinesHealthyPasswd env (.getpwuid entry.uid) hWf
    dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepUid
    have hStepNam := healthyModelOps_refinesHealthyPasswd env (.getpwnam entry.name) hWf
    dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepNam
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hLiftU : (healthyModelOps.getpwuid entry.uid).run env =
          (let (mUid, sUid) := (modelOps.getpwuid entry.uid).run env.state; (mUid, { env with state := sUid })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.getpwuid entry.uid).run env.state <;> rfl
      show (healthyModelOps.getpwuid entry.uid).run env =
          (let (mUid, sUid) := (modelOps.getpwuid entry.uid).run env.state; (mUid, { env with state := sUid })) ∧
        healthyStep env (.getpwuid entry.uid)
          (outcomeOfEntryOpt (healthyModelOps.getpwuid entry.uid env).1) =
          some (healthyModelOps.getpwuid entry.uid env).2 ∧
        (healthyModelOps.getpwuid entry.uid env).2.wf = true ∧
        (healthyModelOps.getpwuid entry.uid env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftU, ?_⟩
      cases hU : healthyModelOps.getpwuid entry.uid env with
      | mk rUid envUid =>
        rw [hU] at hStepUid
        dsimp only at hStepUid ⊢
        have hWfU := (healthyStep_implies_allowedStep env envUid _ _ hStepUid).2.2.1
        have hBudU : envUid.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hU
          cases (modelOps.getpwuid entry.uid).run env.state with
          | mk r0 s0 =>
            injection hU with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepUid, hWfU, hBudU⟩
    · have hLiftN : (healthyModelOps.getpwnam entry.name).run env =
          (let (mNam, sNam) := (modelOps.getpwnam entry.name).run env.state; (mNam, { env with state := sNam })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.getpwnam entry.name).run env.state <;> rfl
      show (healthyModelOps.getpwnam entry.name).run env =
          (let (mNam, sNam) := (modelOps.getpwnam entry.name).run env.state; (mNam, { env with state := sNam })) ∧
        healthyStep env (.getpwnam entry.name)
          (outcomeOfEntryOpt (healthyModelOps.getpwnam entry.name env).1) =
          some (healthyModelOps.getpwnam entry.name env).2 ∧
        (healthyModelOps.getpwnam entry.name env).2.wf = true ∧
        (healthyModelOps.getpwnam entry.name env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftN, ?_⟩
      cases hN : healthyModelOps.getpwnam entry.name env with
      | mk rNam envNam =>
        rw [hN] at hStepNam
        dsimp only at hStepNam ⊢
        have hWfN := (healthyStep_implies_allowedStep env envNam _ _ hStepNam).2.2.1
        have hBudN : envNam.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hN
          cases (modelOps.getpwnam entry.name).run env.state with
          | mk r0 s0 =>
            injection hN with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepNam, hWfN, hBudN⟩
    · let envPres : HealthyEnv :=
        { env with
          state := { env.state with
                     byUid := setPasswdByUid env.state.byUid entry.uid (some entry)
                     byName := setPasswdByName env.state.byName entry.name (some entry) } }
      refine ⟨?_, ?_⟩
      · dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        rw [modelOps_getpwuid_eval]
        have hLookup : lookupPasswdByUid envPres.state.byUid entry.uid = some (some entry) :=
          lookupPasswdByUid_set_self _ _ _
        simp only [envPres, hLookup, hNul, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        rfl
      · dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        rw [modelOps_getpwnam_eval]
        have hLookup : lookupPasswdByName envPres.state.byName entry.name = some (some entry) :=
          lookupPasswdByName_set_self _ _ _
        simp only [envPres, hLookup, hNul, hNamValid, Bool.not_true, Bool.false_eq_true,
          hNamNotGt, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        rfl
    · intro rawName
      have hStepRawNam := healthyModelOps_refinesHealthyPasswd env (.getpwnam rawName) hWf
      dsimp only [id, execPasswdReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepRawNam
      have hLiftRaw : (healthyModelOps.getpwnam rawName).run env =
          (let (mNam, sNam) := (modelOps.getpwnam rawName).run env.state; (mNam, { env with state := sNam })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.getpwnam rawName).run env.state <;> rfl
      refine ⟨?_, fun _ _ _ => ⟨rfl, trivial⟩⟩
      show (healthyModelOps.getpwnam rawName).run env =
          (let (mNam, sNam) := (modelOps.getpwnam rawName).run env.state; (mNam, { env with state := sNam })) ∧
        healthyStep env (.getpwnam rawName)
          (outcomeOfEntryOpt (healthyModelOps.getpwnam rawName env).1) =
          some (healthyModelOps.getpwnam rawName env).2 ∧
        (healthyModelOps.getpwnam rawName env).2.wf = true ∧
        (healthyModelOps.getpwnam rawName env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftRaw, ?_⟩
      cases hNR : healthyModelOps.getpwnam rawName env with
      | mk rRawNam envRawNam =>
        rw [hNR] at hStepRawNam
        dsimp only at hStepRawNam ⊢
        have hWfNR := (healthyStep_implies_allowedStep env envRawNam _ _ hStepRawNam).2.2.1
        have hBudNR : envRawNam.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hNR
          cases (modelOps.getpwnam rawName).run env.state with
          | mk r0 s0 =>
            injection hNR with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepRawNam, hWfNR, hBudNR⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_healthyStep_and_healthyModelOps`. -/
theorem reach_passwd_healthyStep_and_healthyModelOps :
    CanReach test_passwd_healthyStep_and_healthyModelOps := by
  have hAll := proof_passwd_healthyStep_and_healthyModelOps
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  have hRest := hAll.2.2.2.2.2 (HealthyEnv.initial 1) (healthyEnv_initial_wf 1 true) 0 ByteArray.empty e
    (by decide) (by decide) (by decide) rfl rfl
  refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    HealthyEnv.initial 1, healthyEnv_initial_wf 1 true, 0, ByteArray.empty, e,
    by decide, by decide, by decide, rfl, rfl,
    hRest.1, hRest.2.1, hRest.2.2.1, ByteArray.empty,
    (hRest.2.2.2 ByteArray.empty).1,
    HealthyEnv.initial 1, .getpwuid 0, .notFound, ?_⟩
  exact (hRest.2.2.2 ByteArray.empty).2 (HealthyEnv.initial 1) (.getpwuid 0) .notFound

end LeanSwe.LinuxSyscall.Passwd.Proofs
