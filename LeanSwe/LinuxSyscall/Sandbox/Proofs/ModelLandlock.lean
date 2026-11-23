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

private theorem assocSetAux_all_lt {α : Type} :
    ∀ (l acc : List (Nat × α)) (k : Nat) (v : α) (m : Nat),
      l.all (fun p => decide (p.1 < m)) = true →
      acc.all (fun p => decide (p.1 < m)) = true → k < m →
      (assocSetAux l k v acc).all (fun p => decide (p.1 < m)) = true
  | [], acc, k, v, m, _, hAcc, hk => by
    simp only [assocSetAux, List.reverseAux_eq, List.all_append, List.all_reverse,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hAcc, hk⟩
  | (a, b) :: rest, acc, k, v, m, h, hAcc, hk => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold assocSetAux
    by_cases heq : (a == k)
    · simp only [heq, ↓reduceIte, List.reverseAux_eq, List.all_append, List.all_reverse,
        List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hAcc, hk, h.2⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      exact assocSetAux_all_lt rest ((a, b) :: acc) k v m h.2
        (by simp [List.all_cons, h.1, hAcc]) hk

private theorem assocSet_all_lt {α : Type} (l : List (Nat × α)) (k : Nat) (v : α) (m : Nat)
    (h : l.all (fun p => decide (p.1 < m)) = true) (hk : k < m) :
    (assocSet l k v).all (fun p => decide (p.1 < m)) = true :=
  assocSetAux_all_lt l [] k v m h rfl hk

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
  exact (Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _ |>.mp hwf).1)).1)).1

/-- Extract passed-NNP-gate consistency invariant from `SandboxSysState.wf`. -/
theorem wf_nnpGate_of_wf (s : SandboxSysState) (hwf : s.wf = true) :
    !(s.passedNnpGate && s.noNewPrivs? == some false && s.hasCapSysAdmin? == some false) = true := by
  unfold SandboxSysState.wf at hwf
  exact (Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _ |>.mp hwf).1)).1)).2

/-- Extract maximum Landlock ABI invariant from `SandboxSysState.wf`. -/
theorem wf_maxAbi_of_wf (s : SandboxSysState) (hwf : s.wf = true) :
    (match s.landlockMaxAbi? with | none => true | some m => decide (4 ≤ m && s.landlockMinAbi ≤ m)) = true := by
  unfold SandboxSysState.wf at hwf
  exact (Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _ |>.mp hwf).1)).2

/-- Extract minimum Landlock ABI invariant from `SandboxSysState.wf`. -/
theorem wf_abi_of_wf (s : SandboxSysState) (hwf : s.wf = true) :
    (match s.landlockAbi? with
     | none => true
     | some v => decide (v ≥ 4 && v ≥ s.landlockMinAbi &&
         match s.landlockMaxAbi? with | none => true | some m => v ≤ m)) = true := by
  unfold SandboxSysState.wf at hwf
  exact (Bool.and_eq_true _ _ |>.mp hwf).2

/-- Construct `SandboxSysState.wf` from its four component invariants. -/
theorem wf_mk {s : SandboxSysState}
    (h1 : s.fds.all (fun p => decide (p.1 < s.nextHid)) = true)
    (h2 : !(s.passedNnpGate && s.noNewPrivs? == some false && s.hasCapSysAdmin? == some false) = true)
    (h3 : (match s.landlockMaxAbi? with | none => true | some m => decide (4 ≤ m && s.landlockMinAbi ≤ m)) = true)
    (h4 : (match s.landlockAbi? with
      | none => true
      | some v => decide (v ≥ 4 && v ≥ s.landlockMinAbi &&
          match s.landlockMaxAbi? with | none => true | some m => v ≤ m)) = true) :
    s.wf = true := by
  unfold SandboxSysState.wf
  exact Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨h1, h2⟩, h3⟩, h4⟩

/-- `SandboxSysState.wf` is invariant under setting `landlockEnabled := true`. -/
theorem wf_with_enabled (s : SandboxSysState) (hwf : s.wf = true) :
    ({ s with landlockEnabled := true }).wf = true :=
  wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)

private theorem wf_pinPassed (s : SandboxSysState) (hwf : s.wf = true) :
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

private theorem wf_restrict_pin (s : SandboxSysState) (hwf : s.wf = true) (layers : Nat) :
    ({ pinPassedNnpGate s with landlockEnabled := true, landlockLayers := layers }).wf = true := by
  have hp := wf_pinPassed s hwf
  exact wf_mk (wf_fds_of_wf _ hp) (wf_nnpGate_of_wf _ hp) (wf_maxAbi_of_wf _ hp) (wf_abi_of_wf _ hp)

private theorem wf_restrict_nopin (s : SandboxSysState) (hwf : s.wf = true) (layers : Nat) :
    ({ s with landlockEnabled := true, landlockLayers := layers }).wf = true :=
  wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)

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

private theorem mask_not_known_mono (fs : UInt64) {a b : UInt32} (hab : a ≤ b)
    (h : (fs &&& ~~~landlockKnownFsMask b) != 0) :
    (fs &&& ~~~landlockKnownFsMask a) != 0 := by
  simp only [bne_iff_ne, ne_eq] at h ⊢
  unfold landlockKnownFsMask at h ⊢
  by_cases ha4 : a ≤ 4
  · simp only [ha4, ↓reduceIte]
    split at h
    · exact h
    · split at h
      · have hSub : ~~~(((1 : UInt64) <<< 16) - 1) =
            ~~~(((1 : UInt64) <<< 15) - 1) &&& ~~~(((1 : UInt64) <<< 16) - 1) := by decide
        intro hz; apply h; rw [hSub, ← ui64_and_assoc, hz]; decide
      · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
            ~~~(((1 : UInt64) <<< 15) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
        intro hz; apply h; rw [hSub, ← ui64_and_assoc, hz]; decide
  · by_cases ha8 : a ≤ 8
    · have hb4 : ¬(b ≤ 4) := fun hb => ha4 (UInt32.le_trans hab hb)
      simp only [ha4, ha8, ↓reduceIte]
      simp only [hb4, ↓reduceIte] at h
      split at h
      · exact h
      · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
            ~~~(((1 : UInt64) <<< 16) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
        intro hz; apply h; rw [hSub, ← ui64_and_assoc, hz]; decide
    · have hb4 : ¬(b ≤ 4) := fun hb => ha4 (UInt32.le_trans hab hb)
      have hb8 : ¬(b ≤ 8) := fun hb => ha8 (UInt32.le_trans hab hb)
      simp only [ha4, ha8, ↓reduceIte]
      simp only [hb4, hb8, ↓reduceIte] at h
      exact h

private theorem maxU32_le_iff (a b c : UInt32) : maxU32 a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  unfold maxU32
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    exact ⟨fun hb => ⟨UInt32.le_trans (UInt32.le_of_lt h) hb, hb⟩, fun ⟨_, hb⟩ => hb⟩
  · simp only [h, ↓reduceIte]
    have hba : b ≤ a := UInt32.not_lt.mp h
    exact ⟨fun ha => ⟨ha, UInt32.le_trans hba ha⟩, fun ⟨ha, _⟩ => ha⟩

private theorem maxU32_ge_right (a b : UInt32) : b ≤ maxU32 a b := by
  unfold maxU32
  by_cases h : a < b
  · simp [h]
  · simp [h, UInt32.not_lt.mp h]

private theorem maxU32_ge_left (a b : UInt32) : a ≤ maxU32 a b := by
  unfold maxU32
  by_cases h : a < b
  · simp [h, UInt32.le_of_lt h]
  · simp [h]

private theorem impliedLandlockAbi_le (fs : UInt64) (abi : UInt32) (hGe4 : 4 ≤ abi)
    (h : (fs &&& ~~~landlockKnownFsMask abi) = 0) :
    impliedLandlockAbi fs ≤ abi := by
  unfold impliedLandlockAbi
  unfold landlockKnownFsMask at h
  by_cases h4 : abi ≤ 4
  · simp only [h4, ↓reduceIte] at h
    have hRes : (fs &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) = 0 := by
      have hSub : LANDLOCK_ACCESS_FS_RESOLVE_UNIX =
          ~~~(((1 : UInt64) <<< 15) - 1) &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX := by decide
      rw [hSub, ← ui64_and_assoc, h]; decide
    have hIoc : (fs &&& LANDLOCK_ACCESS_FS_IOCTL_DEV) = 0 := by
      have hSub : LANDLOCK_ACCESS_FS_IOCTL_DEV =
          ~~~(((1 : UInt64) <<< 15) - 1) &&& LANDLOCK_ACCESS_FS_IOCTL_DEV := by decide
      rw [hSub, ← ui64_and_assoc, h]; decide
    simp [hRes, hIoc, hGe4]
  · simp only [h4, ↓reduceIte] at h
    by_cases h8 : abi ≤ 8
    · simp only [h8, ↓reduceIte] at h
      have hRes : (fs &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) = 0 := by
        have hSub : LANDLOCK_ACCESS_FS_RESOLVE_UNIX =
            ~~~(((1 : UInt64) <<< 16) - 1) &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX := by decide
        rw [hSub, ← ui64_and_assoc, h]; decide
      have hGe5 : (5 : UInt32) ≤ abi := by
        have hGt4 : (4 : UInt32) < abi := UInt32.not_le.mp h4
        have hLtNat := UInt32.lt_iff_toNat_lt.mp hGt4
        exact UInt32.le_iff_toNat_le.mpr (by change 5 ≤ abi.toNat; change 4 < abi.toNat at hLtNat; omega)
      by_cases hIoc : (fs &&& LANDLOCK_ACCESS_FS_IOCTL_DEV) = 0
      · simp [hRes, hIoc, hGe4]
      · simp [hRes, hIoc, hGe5]
    · simp only [h8, ↓reduceIte] at h
      have hGt8 : (8 : UInt32) < abi := UInt32.not_le.mp h8
      have hGe9 : (9 : UInt32) ≤ abi := by
        have hLtNat := UInt32.lt_iff_toNat_lt.mp hGt8
        exact UInt32.le_iff_toNat_le.mpr (by change 9 ≤ abi.toNat; change 8 < abi.toNat at hLtNat; omega)
      have hGe5 : (5 : UInt32) ≤ abi := UInt32.le_trans (by decide) hGe9
      by_cases hRes : (fs &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) = 0
      · by_cases hIoc : (fs &&& LANDLOCK_ACCESS_FS_IOCTL_DEV) = 0
        · simp [hRes, hIoc, hGe4]
        · simp [hRes, hIoc, hGe5]
      · simp [hRes, hGe9]

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

/-- Helper linking `modelOps` NNP failure condition (with `passedNnpGate`) to `allowedStepCore`. -/
theorem nnpGate_fail_iff {s : SandboxSysState} (hwf : s.wf = true)
    (h : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
          !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = true) :
    canFailNnpGate s = true := by
  have h2 := wf_nnpGate_of_wf s hwf
  unfold canFailNnpGate
  cases hp : s.passedNnpGate <;> cases h1 : s.noNewPrivs? <;> cases h3 : s.hasCapSysAdmin? <;>
    simp_all [Bool.and_eq_true]

/-- Helper linking `modelOps` NNP pass condition (with `passedNnpGate`) to `allowedStepCore`. -/
theorem nnpGate_pass_iff {s : SandboxSysState} (hwf : s.wf = true)
    (h : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
          !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = false) :
    canPassNnpGate s = true := by
  have h2 := wf_nnpGate_of_wf s hwf
  unfold canPassNnpGate
  cases hp : s.passedNnpGate <;> cases h1 : s.noNewPrivs? <;> cases h3 : s.hasCapSysAdmin?
  all_goals simp_all
  · rename_i a b; cases a <;> cases b <;> simp_all

private theorem minU32_le_right (a b : UInt32) : minU32 a b ≤ b := by
  unfold minU32
  by_cases h : a < b
  · simp [h, UInt32.le_of_lt h]
  · simp [h]

private theorem minU32_ge_of_ge {a b c : UInt32} (ha : c ≤ a) (hb : c ≤ b) : c ≤ minU32 a b := by
  unfold minU32
  by_cases h : a < b
  · simp [h, ha]
  · simp [h, hb]

private theorem effectiveAbi_ge_minAbi (s : SandboxSysState) (hwf : s.wf = true) :
    s.landlockMinAbi ≤ effectiveModelLandlockAbi s := by
  unfold effectiveModelLandlockAbi
  have hAbi := wf_abi_of_wf s hwf
  cases hOpt : s.landlockAbi? with
  | some v =>
    rw [hOpt] at hAbi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbi
    exact hAbi.1.2
  | none =>
    exact maxU32_ge_right _ s.landlockMinAbi

private theorem effectiveAbi_le_maxAbi (s : SandboxSysState) (hwf : s.wf = true)
    (m : UInt32) (hMax : s.landlockMaxAbi? = some m) :
    effectiveModelLandlockAbi s ≤ m := by
  unfold effectiveModelLandlockAbi
  have hAbi := wf_abi_of_wf s hwf
  have hMaxWf := wf_maxAbi_of_wf s hwf
  rw [hMax] at hMaxWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf
  cases hOpt : s.landlockAbi? with
  | some v =>
    rw [hOpt, hMax] at hAbi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbi
    exact hAbi.2
  | none =>
    rw [hMax]
    exact (maxU32_le_iff _ _ _).mpr ⟨minU32_le_right _ _, hMaxWf.2⟩

private theorem effectiveAbi_lt4_implies_none (s : SandboxSysState) (hwf : s.wf = true)
    (hLt : effectiveModelLandlockAbi s < 4) :
    s.landlockAbi? = none ∧ hasLandlockEvidence s = false := by
  unfold effectiveModelLandlockAbi at hLt
  have hAbi := wf_abi_of_wf s hwf
  have hMaxWf := wf_maxAbi_of_wf s hwf
  cases hOpt : s.landlockAbi? with
  | some v =>
    rw [hOpt] at hLt hAbi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbi
    have : ¬(v < 4) := UInt32.not_lt.mpr hAbi.1.1
    exact absurd hLt this
  | none =>
    rw [hOpt] at hLt
    refine ⟨rfl, ?_⟩
    have hCapLt : (match s.landlockMaxAbi? with
      | none => if s.defaultLandlockAbi < 4 && hasLandlockEvidence s then 4 else s.defaultLandlockAbi
      | some m => minU32 (if s.defaultLandlockAbi < 4 && hasLandlockEvidence s then 4 else s.defaultLandlockAbi) m) < 4 :=
      UInt32.lt_of_le_of_lt (maxU32_ge_left _ _) hLt
    cases hEv : hasLandlockEvidence s
    · rfl
    · have hBaseGe4 : (4 : UInt32) ≤ (if s.defaultLandlockAbi < 4 && true then 4 else s.defaultLandlockAbi) := by
        by_cases hDef : s.defaultLandlockAbi < 4
        · simp [hDef]
        · simp [hDef, UInt32.not_lt.mp hDef]
      cases hMax : s.landlockMaxAbi? with
      | none =>
        rw [hEv, hMax] at hCapLt
        exact absurd hCapLt (UInt32.not_lt.mpr hBaseGe4)
      | some m =>
        rw [hMax] at hMaxWf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf
        rw [hEv, hMax] at hCapLt
        have hGe4 : (4 : UInt32) ≤ minU32 (if s.defaultLandlockAbi < 4 && true then 4 else s.defaultLandlockAbi) m :=
          minU32_ge_of_ge hBaseGe4 hMaxWf.1
        exact absurd hCapLt (UInt32.not_lt.mpr hGe4)

private theorem mask_known_mono_rev (fs : UInt64) {a b : UInt32} (hab : a ≤ b)
    (h : (fs &&& ~~~landlockKnownFsMask a) = 0) :
    (fs &&& ~~~landlockKnownFsMask b) = 0 := by
  by_cases hNz : (fs &&& ~~~landlockKnownFsMask b) = 0
  · exact hNz
  · have hBad : (fs &&& ~~~landlockKnownFsMask b) != 0 := bne_iff_ne.mpr hNz
    have hBadA := mask_not_known_mono fs hab hBad
    simp only [bne_iff_ne, ne_eq] at hBadA
    exact absurd h hBadA

private theorem impliedMaxEinval_ge (fs : UInt64) (effAbi b s_min : UInt32)
    (hMin : s_min ≤ effAbi)
    (hFs : (fs &&& ~~~landlockKnownFsMask effAbi) != 0)
    (hImp : impliedMaxLandlockAbiOnEinval fs = some b) :
    (4 : UInt32) ≤ b ∧ s_min ≤ b := by
  unfold impliedMaxLandlockAbiOnEinval at hImp
  simp only [bne_iff_ne, ne_eq] at hFs
  by_cases h8 : (fs &&& ~~~landlockKnownFsMask 8) == 0
  · simp only [h8, ↓reduceIte, Option.some.injEq] at hImp
    subst hImp
    have hZ8 : (fs &&& ~~~landlockKnownFsMask 8) = 0 := by simpa using h8
    have hLe4 : effAbi ≤ 4 := by
      by_cases hGt : 4 < effAbi
      · have h5 : (5 : UInt32) ≤ effAbi := by
          have hLtNat := UInt32.lt_iff_toNat_lt.mp hGt
          exact UInt32.le_iff_toNat_le.mpr (by change 5 ≤ effAbi.toNat; change 4 < effAbi.toNat at hLtNat; omega)
        have hEq58 : landlockKnownFsMask 5 = landlockKnownFsMask 8 := by decide
        have hZ5 : (fs &&& ~~~landlockKnownFsMask 5) = 0 := by rw [hEq58]; exact hZ8
        exact absurd (mask_known_mono_rev fs h5 hZ5) hFs
      · exact UInt32.not_lt.mp hGt
    exact ⟨by decide, UInt32.le_trans hMin hLe4⟩
  · simp only [h8, Bool.false_eq_true, ↓reduceIte] at hImp
    by_cases h9 : (fs &&& ~~~landlockKnownFsMask 9) == 0
    · simp only [h9, ↓reduceIte, Option.some.injEq] at hImp
      subst hImp
      have hZ9 : (fs &&& ~~~landlockKnownFsMask 9) = 0 := by simpa using h9
      have hLe8 : effAbi ≤ 8 := by
        by_cases hGt : 8 < effAbi
        · have h9e : (9 : UInt32) ≤ effAbi := by
            have hLtNat := UInt32.lt_iff_toNat_lt.mp hGt
            exact UInt32.le_iff_toNat_le.mpr (by change 9 ≤ effAbi.toNat; change 8 < effAbi.toNat at hLtNat; omega)
          exact absurd (mask_known_mono_rev fs h9e hZ9) hFs
        · exact UInt32.not_lt.mp hGt
      exact ⟨by decide, UInt32.le_trans hMin hLe8⟩
    · simp only [h9, Bool.false_eq_true, ↓reduceIte] at hImp
      cases hImp

private theorem minU32_le_iff {a b c : UInt32} : c ≤ minU32 a b ↔ c ≤ a ∧ c ≤ b := by
  unfold minU32
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    exact ⟨fun ha => ⟨ha, UInt32.le_trans ha (UInt32.le_of_lt h)⟩, fun ⟨ha, _⟩ => ha⟩
  · simp only [h, ↓reduceIte]
    have hba : b ≤ a := UInt32.not_lt.mp h
    exact ⟨fun hb => ⟨UInt32.le_trans hb hba, hb⟩, fun ⟨_, hb⟩ => hb⟩

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
        have hGeMin : effectiveModelLandlockAbi s ≥ s.landlockMinAbi := effectiveAbi_ge_minAbi s hwf
        by_cases hVer : flags == LANDLOCK_CREATE_RULESET_VERSION
        · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer]
          have hMaxWf := wf_maxAbi_of_wf s hwf
          cases hOpt : s.landlockAbi? with
          | none =>
            have hNotLtMin : ¬(effectiveModelLandlockAbi s < s.landlockMinAbi) := UInt32.not_lt.mpr hGeMin
            have hMaxOk : (match s.landlockMaxAbi? with | none => true | some m => decide (effectiveModelLandlockAbi s ≤ m)) = true := by
              cases hM : s.landlockMaxAbi? with
              | none => rfl
              | some m => exact decide_eq_true (effectiveAbi_le_maxAbi s hwf m hM)
            have hWfV : ({ s with landlockEnabled := true, landlockAbi? := some (effectiveModelLandlockAbi s) }).wf = true := by
              refine wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) hMaxWf ?_
              simp [decide_eq_true hGe4, decide_eq_true hGeMin, hMaxOk]
            refine ⟨?_, hWfV⟩
            cases hSec : s.seccompMayIntercept <;>
              (simp [allowedStep, allowedStepCore, hVer, hOpt, hGe4, hNotLtMin, hSec];
               cases hM : s.landlockMaxAbi? with
               | none => simp
               | some m => simp [effectiveAbi_le_maxAbi s hwf m hM])
          | some prev =>
            have hEq : effectiveModelLandlockAbi s = prev := by simp [effectiveModelLandlockAbi, hOpt]
            have hAbi := wf_abi_of_wf s hwf
            rw [hOpt] at hAbi
            have hAbiAnd : (decide (prev ≥ 4) && decide (prev ≥ s.landlockMinAbi) &&
                match s.landlockMaxAbi? with | none => true | some m => decide (prev ≤ m)) = true := by
              simpa using hAbi
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbiAnd
            have hP4 : 4 ≤ prev := hAbiAnd.1.1
            have hPMin : s.landlockMinAbi ≤ prev := hAbiAnd.1.2
            have hPMax : (match s.landlockMaxAbi? with | none => true | some m => decide (prev ≤ m)) = true := hAbiAnd.2
            have hWfV : ({ s with landlockEnabled := true, landlockAbi? := some (effectiveModelLandlockAbi s) }).wf = true := by
              rw [hEq]
              exact wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) hMaxWf (by simp [hP4, hPMin, hPMax])
            refine ⟨?_, hWfV⟩
            cases hSec : s.seccompMayIntercept <;>
              simp [allowedStep, allowedStepCore, hVer, hOpt, hEq, hSec, hP4]
        · by_cases hErr : flags == LANDLOCK_CREATE_RULESET_ERRATA
          · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer, hErr]
            cases hEr : s.landlockErrata? with
            | some er =>
              cases er with
              | none =>
                cases hSec : s.seccompMayIntercept
                · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]; exact wf_with_enabled s hwf⟩
                  simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFl0, hVer, hErr, hEr, hSec,
                    Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT,
                    show isNonFdTransientErrno 22 = false by decide]
                · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
                  exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hFl0])
                    hSec (by decide) (by decide) (by decide)
              | some mask =>
                refine ⟨?_, wf_with_enabled s hwf⟩
                cases hSec : s.seccompMayIntercept <;>
                  simp [allowedStep, allowedStepCore, hVer, hErr, hEr, hSec]
            | none =>
              have hWfE : ({ s with landlockEnabled := true, landlockErrata? := some (some 0) }).wf = true :=
                wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
              refine ⟨?_, hWfE⟩
              cases hSec : s.seccompMayIntercept <;>
                simp [allowedStep, allowedStepCore, hVer, hErr, hEr, hSec]
          · simp only [hFl0, Bool.false_eq_true, ↓reduceIte, hLt4, hVer, hErr]
            cases hSec : s.seccompMayIntercept
            · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]; exact wf_with_enabled s hwf⟩
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFl0, hVer, hErr, hSec,
                Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT,
                show isNonFdTransientErrno 22 = false by decide]
            · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
              exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hFl0])
                hSec (by decide) (by decide) (by decide)
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
        simp [allowedStepCore, hFl, hNoEv, enosys_ne_efault]
      · by_cases hEmpty : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
        · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty]
          cases hSec : s.seccompMayIntercept
          · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]; exact wf_with_enabled s hwf⟩
            simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFl, hEmpty, hSec,
              ENOMSG, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
          · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
            exact allowedStep_seccomp_err s _ ENOMSG (by simp [failsPureWrapperGuard, hFl])
              hSec (by decide) (by decide) (by decide)
        · by_cases hNet : (attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0
          · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet]
            cases hSec : s.seccompMayIntercept
            · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]; exact wf_with_enabled s hwf⟩
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFl, hEmpty, hNet, hSec,
                Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
            · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
              exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hFl])
                hSec (by decide) (by decide) (by decide)
          · by_cases hFs : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) != 0
            · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs]
              have hGeMin := effectiveAbi_ge_minAbi s hwf
              have hMaxWf := wf_maxAbi_of_wf s hwf
              have hWfEinval : ({ s with
                  landlockEnabled := true,
                  landlockMaxAbi? := match s.landlockAbi? with
                    | some _ => s.landlockMaxAbi?
                    | none => match impliedMaxLandlockAbiOnEinval attr.handledAccessFs with
                      | none => s.landlockMaxAbi?
                      | some b => tightenMaxAbi s.landlockMaxAbi? b } : SandboxSysState).wf = true := by
                cases hOpt : s.landlockAbi? with
                | some _ =>
                  have hW := wf_with_enabled s hwf
                  simp only [hOpt] at hW ⊢
                  exact hW
                | none =>
                  cases hImp : impliedMaxLandlockAbiOnEinval attr.handledAccessFs with
                  | none =>
                    have hW := wf_with_enabled s hwf
                    simp only [hOpt] at hW ⊢
                    exact hW
                  | some b =>
                    have ⟨hb4, hbMin⟩ := impliedMaxEinval_ge attr.handledAccessFs (effectiveModelLandlockAbi s) b s.landlockMinAbi hGeMin hFs hImp
                    refine wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) ?_ (by simp)
                    cases hCur : s.landlockMaxAbi? with
                    | none => simp [tightenMaxAbi, decide_eq_true hb4, decide_eq_true hbMin]
                    | some m =>
                      rw [hCur] at hMaxWf
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf
                      simp only [tightenMaxAbi]
                      exact Bool.and_eq_true _ _ |>.mpr
                        ⟨decide_eq_true (minU32_le_iff.mpr ⟨hMaxWf.1, hb4⟩),
                         decide_eq_true (minU32_le_iff.mpr ⟨hMaxWf.2, hbMin⟩)⟩
              cases hSec : s.seccompMayIntercept
              · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]; exact hWfEinval⟩
                simp only [allowedStep, failsPureWrapperGuard, hFl, hSec, Bool.false_eq_true, Bool.not_false, Bool.and_false, ↓reduceIte]
                simp only [allowedStepCore, hFl, Bool.false_eq_true, ↓reduceIte, hEmpty, hNet,
                  Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                cases hOpt : s.landlockAbi? with
                | none =>
                  have hLe : maxU32 4 s.landlockMinAbi ≤ effectiveModelLandlockAbi s :=
                    (maxU32_le_iff 4 s.landlockMinAbi (effectiveModelLandlockAbi s)).mpr ⟨UInt32.not_lt.mp hLt4, hGeMin⟩
                  have hKnown := mask_not_known_mono attr.handledAccessFs hLe hFs
                  simp [hSec, hKnown]
                | some abi =>
                  have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                  rw [hEq] at hFs
                  simp [hSec, hFs]
              · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
                exact allowedStep_seccomp_err s _ Errno.EINVAL (by simp [failsPureWrapperGuard, hFl])
                  hSec (by decide) (by decide) (by decide)
            · by_cases hEmf : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = true
              · simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs, hEmf]
                refine ⟨allowedStep_err_eq s _ _ (by simp [failsPureWrapperGuard, hFl]) (by decide) (by decide) ?_, hwf⟩
                intro _
                simp only [allowedStepCore, hFl, Bool.false_eq_true, ↓reduceIte, hEmpty, hNet]
                cases hOpt : s.landlockAbi? with
                | none =>
                  by_cases hM : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (maxU32 4 s.landlockMinAbi)) != 0 <;>
                    simp [hM, isFdAllocTransientErrno, Errno.isCriticalOsErrno, Errno.isResourceLimitErrno,
                      show Errno.EMFILE ≠ Errno.EINVAL by decide,
                      show Errno.EMFILE ≠ Errno.EOPNOTSUPP by decide, show Errno.EMFILE ≠ Errno.ENOSYS by decide,
                      emfile_ne_efault]
                | some abi =>
                  have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                  have hFsA : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0) = false := by
                    rw [← hEq]; exact Bool.eq_false_iff.mpr hFs
                  simp [hFsA, isFdAllocTransientErrno, Errno.isCriticalOsErrno, Errno.isResourceLimitErrno,
                    emfile_ne_efault]
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
                have hFds' := assocSet_nextHid_all_lt s
                  { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true } hwf
                have hAbi := wf_abi_of_wf s hwf
                have hMaxWf := wf_maxAbi_of_wf s hwf
                have hGe4 : 4 ≤ effectiveModelLandlockAbi s := UInt32.not_lt.mp hLt4
                have hRawFs0 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) = 0 := by
                  cases h1 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) == 0
                  · simp_all
                  · simpa using h1
                have hImpEff : impliedLandlockAbi attr.handledAccessFs ≤ effectiveModelLandlockAbi s :=
                  impliedLandlockAbi_le attr.handledAccessFs (effectiveModelLandlockAbi s) hGe4 hRawFs0
                have hCeilOk : (match s.landlockMaxAbi? with | none => true | some m => decide (impliedLandlockAbi attr.handledAccessFs ≤ m)) = true := by
                  cases hM : s.landlockMaxAbi? with
                  | none => rfl
                  | some m => exact decide_eq_true (UInt32.le_trans hImpEff (effectiveAbi_le_maxAbi s hwf m hM))
                have hMaxWf' : (match s.landlockMaxAbi? with | none => true | some m => decide (4 ≤ m && maxU32 s.landlockMinAbi (impliedLandlockAbi attr.handledAccessFs) ≤ m)) = true := by
                  cases hM : s.landlockMaxAbi? with
                  | none => rfl
                  | some m =>
                    rw [hM] at hMaxWf
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf
                    have hm : maxU32 s.landlockMinAbi (impliedLandlockAbi attr.handledAccessFs) ≤ m :=
                      (maxU32_le_iff _ _ _).mpr ⟨hMaxWf.2, UInt32.le_trans hImpEff (effectiveAbi_le_maxAbi s hwf m hM)⟩
                    exact Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hMaxWf.1, decide_eq_true hm⟩
                have hWf' : ({ s with
                    fds := assocSet s.fds s.nextHid
                      { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true },
                    nextHid := Nat.max s.nextHid (s.nextHid + 1),
                    landlockEnabled := true,
                    landlockMinAbi := maxU32 s.landlockMinAbi (impliedLandlockAbi attr.handledAccessFs) } : SandboxSysState).wf = true := by
                  refine wf_mk hFds' (wf_nnpGate_of_wf s hwf) hMaxWf' ?_
                  cases hOpt : s.landlockAbi? with
                  | none => rfl
                  | some abi =>
                    rw [hOpt] at hAbi
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbi
                    have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                    have hImp : impliedLandlockAbi attr.handledAccessFs ≤ abi := by rw [← hEq]; exact hImpEff
                    have hm : maxU32 s.landlockMinAbi (impliedLandlockAbi attr.handledAccessFs) ≤ abi :=
                      (maxU32_le_iff _ _ _).mpr ⟨hAbi.1.2, hImp⟩
                    exact Bool.and_eq_true _ _ |>.mpr
                      ⟨Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hAbi.1.1, decide_eq_true hm⟩,
                       by cases hM : s.landlockMaxAbi? <;> simp_all⟩
                simp only [hFl, Bool.false_eq_true, ↓reduceIte, hLt4, hEmpty, hNet, hFs, hEmf]
                refine ⟨?_, hWf'⟩
                cases hOpt : s.landlockAbi? with
                | none =>
                  have hFs9 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask 9) = 0 :=
                    mask_known_to_9 attr.handledAccessFs (effectiveModelLandlockAbi s) hRawFs0
                  cases hSec : s.seccompMayIntercept <;>
                    (simp [allowedStep, allowedStepCore, hFl, hEmpty, hNet, hNoneHid, hEmf0, hOpt, hFs9, hSec,
                      Nat.max_eq_right (Nat.le_succ s.nextHid)];
                     cases hM : s.landlockMaxAbi? with
                     | none => simp
                     | some m => simp [UInt32.le_trans hImpEff (effectiveAbi_le_maxAbi s hwf m hM)])
                | some abi =>
                  have hFsA : (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) = 0 := by
                    have hEq : effectiveModelLandlockAbi s = abi := by simp [effectiveModelLandlockAbi, hOpt]
                    rw [← hEq]; exact hRawFs0
                  cases hSec : s.seccompMayIntercept <;>
                    (simp [allowedStep, allowedStepCore, hFl, hEmpty, hNet, hNoneHid, hEmf0, hOpt, hFsA, hSec,
                      Nat.max_eq_right (Nat.le_succ s.nextHid)];
                     cases hM : s.landlockMaxAbi? with
                     | none => simp
                     | some m => simp [UInt32.le_trans hImpEff (effectiveAbi_le_maxAbi s hwf m hM)])

private theorem allowedStep_err_enabled (s : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hGuard : failsPureWrapperGuard req = false)
    (hEf : e ≠ Errno.EFAULT) (hRng : 1 ≤ e.toNat ∧ e.toNat ≤ 4095)
    (hCore : s.seccompMayIntercept = false → allowedStepCore s req (.err e) = some { s with landlockEnabled := true }) :
    allowedStep s req (.err e) = some (if !s.seccompMayIntercept then { s with landlockEnabled := true } else s) := by
  unfold allowedStep
  cases hSec : s.seccompMayIntercept
  · simp [hSec, hGuard, hCore hSec]
  · simp [hGuard, hEf, hRng]

private theorem addRule_err_pair (s : SandboxSysState) (hwf : s.wf = true)
    (ruleset : HandleId) (rule : LandlockRule HandleId) (e : Errno)
    (hEf : e ≠ Errno.EFAULT) (hRng : 1 ≤ e.toNat ∧ e.toNat ≤ 4095)
    (hCore : s.seccompMayIntercept = false →
      allowedStepCore s (.landlockAddRule ruleset rule) (.err e) = some { s with landlockEnabled := true }) :
    let m : StateM SandboxSysState (Except Errno Unit) := do
      if !s.seccompMayIntercept then set { s with landlockEnabled := true }
      return .error e
    let r := (do match ← m with | .ok () => return SandboxOutcome.unit | .error err => return SandboxOutcome.err err).run s
    allowedStep s (.landlockAddRule ruleset rule) r.1 = some r.2 ∧ r.2.wf = true := by
  dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.run, StateT.set, set, Id.run]
  cases hSec : s.seccompMayIntercept
  · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_with_enabled s hwf⟩
    simp [hSec, allowedStep, failsPureWrapperGuard, hCore hSec]
  · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
    simp [hSec, allowedStep, failsPureWrapperGuard, hEf, hRng]

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
      refine addRule_err_pair s hwf ruleset rule Errno.EBADF (by decide) (by decide) ?_
      intro _; simp [allowedStepCore, hRs, Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
    | some rsDesc =>
      by_cases hOp : rsDesc.oPath
      · simp only [hOp, ↓reduceIte]
        refine addRule_err_pair s hwf ruleset rule Errno.EBADF (by decide) (by decide) ?_
        intro _; simp [allowedStepCore, hRs, hOp, Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
      · rcases rsDesc with ⟨rsKind, rsClo, rsOp⟩
        dsimp only at hOp
        simp only [Bool.not_eq_true] at hOp
        subst hOp
        cases hKind : rsKind with
        | memfd _ _ | hostPath _ | pseudoFs =>
          refine addRule_err_pair s hwf ruleset rule EBADFD (by decide) (by decide) ?_
          intro _; simp [allowedStepCore, hRs, hKind, EBADFD, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
        | landlockRuleset handledFs handledNet =>
          cases rule with
          | pathBeneath parentHid allowedAccess =>
            by_cases hZero : allowedAccess == 0
            · simp only [hZero]
              refine addRule_err_pair s hwf ruleset (.pathBeneath parentHid allowedAccess) ENOMSG (by decide) (by decide) ?_
              intro _; simp [allowedStepCore, hRs, hKind, hZero, ENOMSG, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
            · by_cases hUnh : (allowedAccess &&& ~~~handledFs) != 0
              · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh]
                refine addRule_err_pair s hwf ruleset (.pathBeneath parentHid allowedAccess) Errno.EINVAL (by decide) (by decide) ?_
                intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
              · cases hPar : assocGet s.fds parentHid with
                | none =>
                  simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar]
                  refine addRule_err_pair s hwf ruleset (.pathBeneath parentHid allowedAccess) Errno.EBADF (by decide) (by decide) ?_
                  intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                | some pDesc =>
                  rcases pDesc with ⟨pKind, pClo, pOp⟩
                  cases hPK : pKind with
                  | landlockRuleset _ _ | memfd _ _ | pseudoFs =>
                    simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK]
                    refine addRule_err_pair s hwf ruleset (.pathBeneath parentHid allowedAccess) EBADFD (by decide) (by decide) ?_
                    intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, EBADFD, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                  | hostPath isDir =>
                    by_cases hDirErr : (!isDir && (allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0) = true
                    · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK, hDirErr]
                      refine addRule_err_pair s hwf ruleset (.pathBeneath parentHid allowedAccess) Errno.EINVAL (by decide) (by decide) ?_
                      intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, hDirErr, Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                    · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hUnh, hPar, hPK, hDirErr]
                      refine ⟨?_, wf_with_enabled s hwf⟩
                      cases hSec : s.seccompMayIntercept <;>
                        simp [allowedStep, allowedStepCore, hRs, hKind, hZero, hUnh, hPar, hPK, hDirErr, hSec]
          | netPort port allowedAccess =>
            by_cases hZero : allowedAccess == 0
            · simp only [hZero]
              refine addRule_err_pair s hwf ruleset (.netPort port allowedAccess) ENOMSG (by decide) (by decide) ?_
              intro _; simp [allowedStepCore, hRs, hKind, hZero, ENOMSG, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
            · by_cases hUnh : ((allowedAccess &&& ~~~handledNet) != 0 || port > 65535) = true
              · have hBad : (allowedAccess &&& ~~~handledNet) != 0 ∨ port > 65535 := by
                  simpa [Bool.or_eq_true] using hUnh
                rcases hBad with hA | hP
                · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA]
                  refine addRule_err_pair s hwf ruleset (.netPort port allowedAccess) Errno.EINVAL (by decide) (by decide) ?_
                  intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                · by_cases hA : (allowedAccess &&& ~~~handledNet) != 0
                  · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA]
                    refine addRule_err_pair s hwf ruleset (.netPort port allowedAccess) Errno.EINVAL (by decide) (by decide) ?_
                    intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
                  · simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA, hP]
                    refine addRule_err_pair s hwf ruleset (.netPort port allowedAccess) Errno.EINVAL (by decide) (by decide) ?_
                    intro _; simp [allowedStepCore, hRs, hKind, hZero, hUnh, Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
              · have hA : ((allowedAccess &&& ~~~handledNet) != 0) = false := by
                  cases h1 : (allowedAccess &&& ~~~handledNet) != 0 <;> simp_all
                have hP : ¬(port > 65535) := by
                  intro hp; simp [hp] at hUnh
                simp only [hZero, Bool.false_eq_true, ↓reduceIte, hA, hP]
                refine ⟨?_, wf_with_enabled s hwf⟩
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
  · by_cases hGate : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
        !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = true
    · have hFail := nnpGate_fail_iff hwf hGate
      have hNp : s.passedNnpGate = false := by
        unfold canFailNnpGate at hFail; simp_all
      simp only [hLt4, ↓reduceIte, hGate]
      cases hSec : s.seccompMayIntercept
      · refine ⟨?_, by
          simp only [Bool.not_false, ↓reduceIte, st_bind, st_set, st_pure]
          exact wf_mk (wf_fds_of_wf s hwf) (by simp [pinFailedNnpGate, hNp]) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)⟩
        simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hFail, hSec,
          Errno.EPERM, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EFAULT]
      · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_pure]; exact hwf⟩
        simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.EPERM ≠ Errno.EFAULT by decide,
          show 1 ≤ Errno.EPERM.toNat ∧ Errno.EPERM.toNat ≤ 4095 by decide]
    · have hGateF : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
          !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = false :=
        Bool.eq_false_iff.mpr hGate
      have hPassT := nnpGate_pass_iff hwf hGateF
      have hWfPass : ({ pinPassedNnpGate s with landlockEnabled := true } : SandboxSysState).wf = true :=
        wf_with_enabled _ (wf_pinPassed s hwf)
      simp only [hLt4, ↓reduceIte, hGateF]
      cases hRs : assocGet s.fds ruleset with
      | none =>
        cases hSec : s.seccompMayIntercept
        · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfPass⟩
          simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hSec,
            Errno.EBADF, Errno.EOPNOTSUPP, Errno.ENOSYS, Errno.EPERM, Errno.EFAULT]
        · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
          simp [allowedStep, failsPureWrapperGuard, hSec, show Errno.EBADF ≠ Errno.EFAULT by decide,
            show 1 ≤ Errno.EBADF.toNat ∧ Errno.EBADF.toNat ≤ 4095 by decide]
      | some desc =>
        by_cases hOp : desc.oPath
        · simp only [hOp, ↓reduceIte]
          cases hSec : s.seccompMayIntercept
          · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfPass⟩
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
            · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact hWfPass⟩
              simp [allowedStep, failsPureWrapperGuard, allowedStepCore, hPassT, hRs, hKind, hSec,
                hE1, hE2, hE3, hE4]
            · refine ⟨?_, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hwf⟩
              simp [allowedStep, failsPureWrapperGuard, hSec, hE4,
                show 1 ≤ EBADFD.toNat ∧ EBADFD.toNat ≤ 4095 by decide]
          | landlockRuleset _ _ =>
            by_cases hCap : s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS
            · simp only [hCap, ↓reduceIte]
              cases hSec : s.seccompMayIntercept
              · refine ⟨?_, by simp only [Bool.not_false, ↓reduceIte]; exact wf_restrict_pin s hwf LANDLOCK_MAX_STACKED_LAYERS⟩
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
