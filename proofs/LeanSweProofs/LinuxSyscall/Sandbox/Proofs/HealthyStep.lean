import LeanSweProofs.LinuxSyscall.Sandbox.Proofs.Model

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

@[local simp] private theorem st_pure_h {S α : Type} (a : α) (s : S) :
    StateT.pure (m := Id) a s = (a, s) := rfl

@[local simp] private theorem st_bind_h {S α β : Type} (m : StateT S Id α)
    (f : α → StateT S Id β) (s : S) :
    StateT.bind m f s = let p := m s; f p.1 p.2 := rfl

@[local simp] private theorem st_set_h {S : Type} (s' s : S) :
    StateT.set (m := Id) s' s = ((), s') := rfl

@[local simp] private theorem st_get_h {S : Type} (s : S) :
    StateT.get (m := Id) s = (s, s) := rfl

private theorem wf_of_eq_core {s s' : SandboxSysState} (hwf : s.wf = true)
    (hFds : s'.fds = s.fds) (hHid : s'.nextHid = s.nextHid)
    (hGate : s'.passedNnpGate = s.passedNnpGate)
    (hNnp : s'.noNewPrivs? = s.noNewPrivs?)
    (hCapA : s'.hasCapSysAdmin? = s.hasCapSysAdmin?)
    (hMax : s'.landlockMaxAbi? = s.landlockMaxAbi?)
    (hMin : s'.landlockMinAbi = s.landlockMinAbi)
    (hAbi : s'.landlockAbi? = s.landlockAbi?) :
    s'.wf = true := by
  unfold SandboxSysState.wf at hwf ⊢
  rw [hFds, hHid, hGate, hNnp, hCapA, hMax, hMin, hAbi]
  exact hwf

private theorem wf_setRlimit_h (s : SandboxSysState) (res : RlimitResource) (st : RlimitState)
    (hwf : s.wf = true) :
    (s.setRlimit res st).wf = true := by
  cases res <;> exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl

private theorem wf_pinFailed_of_canFail (s : SandboxSysState) (hwf : s.wf = true)
    (hFail : canFailNnpGate s = true) :
    (pinFailedNnpGate s).wf = true := by
  have hNp : s.passedNnpGate = false := by
    unfold canFailNnpGate at hFail
    cases hp : s.passedNnpGate <;> simp_all
  exact wf_mk (wf_fds_of_wf s hwf) (by simp [pinFailedNnpGate, hNp])
    (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)

private theorem wf_pinPassed_h (s : SandboxSysState) (hwf : s.wf = true) :
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

private theorem assocSet_hid_all_lt_h (s : SandboxSysState) (hid : HandleId) (d : SandboxFdDesc)
    (hwf : s.wf = true) :
    (assocSet s.fds hid d).all (fun p => decide (p.1 < Nat.max s.nextHid (hid + 1))) = true := by
  have hMono : ∀ (l : List (Nat × SandboxFdDesc)) {a b : Nat},
      l.all (fun p => decide (p.1 < a)) = true → a ≤ b →
      l.all (fun p => decide (p.1 < b)) = true := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons hd tl ih =>
      intro a b h hab
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨Nat.lt_of_lt_of_le h.1 hab, ih h.2 hab⟩
  have hSet : ∀ (l acc : List (Nat × SandboxFdDesc)) (k : Nat) (v : SandboxFdDesc) (m : Nat),
      l.all (fun p => decide (p.1 < m)) = true →
      acc.all (fun p => decide (p.1 < m)) = true → k < m →
      (assocSetAux l k v acc).all (fun p => decide (p.1 < m)) = true := by
    intro l
    induction l with
    | nil =>
      intro acc k v m _ hAcc hk
      simp only [assocSetAux, List.reverseAux_eq, List.all_append, List.all_reverse,
        List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hAcc, hk⟩
    | cons hd tl ih =>
      intro acc k v m h hAcc hk
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      unfold assocSetAux
      by_cases heq : (hd.1 == k)
      · simp only [heq, ↓reduceIte, List.reverseAux_eq, List.all_append, List.all_reverse,
          List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hAcc, hk, h.2⟩
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        exact ih (hd :: acc) k v m h.2 (by simp [List.all_cons, h.1, hAcc]) hk
  exact hSet s.fds [] hid d (Nat.max s.nextHid (hid + 1))
    (hMono s.fds (wf_fds_of_wf s hwf) (Nat.le_max_left s.nextHid (hid + 1))) rfl
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self hid) (Nat.le_max_right s.nextHid (hid + 1)))

private theorem ui64_and_assoc_h (a b c : UInt64) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, Nat.and_assoc]

private theorem maxU32_le_iff_h (a b c : UInt32) : maxU32 a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  unfold maxU32
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    exact ⟨fun hb => ⟨UInt32.le_trans (UInt32.le_of_lt h) hb, hb⟩, fun ⟨_, hb⟩ => hb⟩
  · simp only [h, ↓reduceIte]
    have hba : b ≤ a := UInt32.not_lt.mp h
    exact ⟨fun ha => ⟨ha, UInt32.le_trans hba ha⟩, fun ⟨ha, _⟩ => ha⟩

private theorem maxU32_ge_right_h (a b : UInt32) : b ≤ maxU32 a b := by
  unfold maxU32
  by_cases h : a < b
  · simp [h]
  · simp [h, UInt32.not_lt.mp h]

private theorem minU32_ge_of_ge_h {a b c : UInt32} (ha : c ≤ a) (hb : c ≤ b) : c ≤ minU32 a b := by
  unfold minU32
  by_cases h : a < b
  · simp [h, ha]
  · simp [h, hb]

private theorem impliedLandlockAbi_le_h (fs : UInt64) (abi : UInt32) (hGe4 : 4 ≤ abi)
    (h : (fs &&& ~~~landlockKnownFsMask abi) = 0) :
    impliedLandlockAbi fs ≤ abi := by
  unfold impliedLandlockAbi
  unfold landlockKnownFsMask at h
  by_cases h4 : abi ≤ 4
  · simp only [h4, ↓reduceIte] at h
    have hRes : (fs &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) = 0 := by
      have hSub : LANDLOCK_ACCESS_FS_RESOLVE_UNIX =
          ~~~(((1 : UInt64) <<< 15) - 1) &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX := by decide
      rw [hSub, ← ui64_and_assoc_h, h]; decide
    have hIoc : (fs &&& LANDLOCK_ACCESS_FS_IOCTL_DEV) = 0 := by
      have hSub : LANDLOCK_ACCESS_FS_IOCTL_DEV =
          ~~~(((1 : UInt64) <<< 15) - 1) &&& LANDLOCK_ACCESS_FS_IOCTL_DEV := by decide
      rw [hSub, ← ui64_and_assoc_h, h]; decide
    simp [hRes, hIoc, hGe4]
  · simp only [h4, ↓reduceIte] at h
    by_cases h8 : abi ≤ 8
    · simp only [h8, ↓reduceIte] at h
      have hRes : (fs &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX) = 0 := by
        have hSub : LANDLOCK_ACCESS_FS_RESOLVE_UNIX =
            ~~~(((1 : UInt64) <<< 16) - 1) &&& LANDLOCK_ACCESS_FS_RESOLVE_UNIX := by decide
        rw [hSub, ← ui64_and_assoc_h, h]; decide
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

private theorem mask_not_known_mono_h (fs : UInt64) {a b : UInt32} (hab : a ≤ b)
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
        intro hz; apply h; rw [hSub, ← ui64_and_assoc_h, hz]; decide
      · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
            ~~~(((1 : UInt64) <<< 15) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
        intro hz; apply h; rw [hSub, ← ui64_and_assoc_h, hz]; decide
  · by_cases ha8 : a ≤ 8
    · have hb4 : ¬(b ≤ 4) := fun hb => ha4 (UInt32.le_trans hab hb)
      simp only [ha4, ha8, ↓reduceIte]
      simp only [hb4, ↓reduceIte] at h
      split at h
      · exact h
      · have hSub : ~~~(((1 : UInt64) <<< 17) - 1) =
            ~~~(((1 : UInt64) <<< 16) - 1) &&& ~~~(((1 : UInt64) <<< 17) - 1) := by decide
        intro hz; apply h; rw [hSub, ← ui64_and_assoc_h, hz]; decide
    · have hb4 : ¬(b ≤ 4) := fun hb => ha4 (UInt32.le_trans hab hb)
      have hb8 : ¬(b ≤ 8) := fun hb => ha8 (UInt32.le_trans hab hb)
      simp only [ha4, ha8, ↓reduceIte]
      simp only [hb4, hb8, ↓reduceIte] at h
      exact h

private theorem mask_known_mono_rev_h (fs : UInt64) {a b : UInt32} (hab : a ≤ b)
    (h : (fs &&& ~~~landlockKnownFsMask a) = 0) :
    (fs &&& ~~~landlockKnownFsMask b) = 0 := by
  by_cases hNz : (fs &&& ~~~landlockKnownFsMask b) = 0
  · exact hNz
  · have hBad : (fs &&& ~~~landlockKnownFsMask b) != 0 := bne_iff_ne.mpr hNz
    have hBadA := mask_not_known_mono_h fs hab hBad
    simp only [bne_iff_ne, ne_eq] at hBadA
    exact absurd h hBadA

private theorem impliedMaxEinval_ge_h (fs : UInt64) (effAbi b s_min : UInt32)
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
        exact absurd (mask_known_mono_rev_h fs h5 hZ5) hFs
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
          exact absurd (mask_known_mono_rev_h fs h9e hZ9) hFs
        · exact UInt32.not_lt.mp hGt
      exact ⟨by decide, UInt32.le_trans hMin hLe8⟩
    · have h9F : ((fs &&& ~~~landlockKnownFsMask 9) == 0) = false := Bool.eq_false_iff.mpr h9
      simp [h9F] at hImp

private theorem allowedStepCore_err_landlockCreate_wf
    (s s' : SandboxSysState) (attr? : Option LandlockRulesetAttr) (flags : UInt32) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.landlockCreateRuleset attr? flags) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases attr? with
    | none =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
        | split at h
    | some attr =>
      dsimp only at h
      by_cases hFl : (flags != 0) = true
      · simp only [hFl, ↓reduceIte] at h
        split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
      · have hFlF : (flags != 0) = false := Bool.eq_false_iff.mpr hFl
        simp only [hFlF, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hDis : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = true
        · simp only [hDis, ↓reduceIte, Option.some.injEq] at h; subst h; exact hwf
        · have hDisF : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = false :=
            Bool.eq_false_iff.mpr hDis
          simp only [hDisF, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hEmp : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
          · simp only [hEmp, ↓reduceIte] at h
            repeat first
              | contradiction
              | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
              | split at h
          · have hEmpF : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = false :=
              Bool.eq_false_iff.mpr hEmp
            simp only [hEmpF, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hNet : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = true
            · simp only [hNet, ↓reduceIte] at h
              repeat first
                | contradiction
                | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
                | split at h
            · have hNetF : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = false :=
                Bool.eq_false_iff.mpr hNet
              simp only [hNetF, Bool.false_eq_true, ↓reduceIte] at h
              cases hAbi : s.landlockAbi? with
              | some abi =>
                rw [hAbi] at h
                dsimp only at h
                by_cases hFs : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0) = true
                · simp only [hFs, ↓reduceIte] at h
                  by_cases hEv : (e == Errno.EINVAL) = true
                  · simp only [hEv, ↓reduceIte, Option.some.injEq] at h
                    subst h
                    exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl hAbi.symm
                  · have hEvF : (e == Errno.EINVAL) = false := Bool.eq_false_iff.mpr hEv
                    simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at h
                    split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
                · have hFsF : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0) = false :=
                    Bool.eq_false_iff.mpr hFs
                  simp only [hFsF, Bool.false_eq_true, ↓reduceIte] at h
                  split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
              | none =>
                rw [hAbi] at h
                dsimp only at h
                by_cases hFs : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask (maxU32 4 s.landlockMinAbi)) != 0) = true
                · simp only [hFs, ↓reduceIte] at h
                  by_cases hEv : (e == Errno.EINVAL) = true
                  · simp only [hEv, ↓reduceIte, Option.some.injEq] at h
                    cases hImp : impliedMaxLandlockAbiOnEinval attr.handledAccessFs with
                    | none =>
                      rw [hImp] at h
                      subst h
                      exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl hAbi.symm
                    | some b =>
                      rw [hImp] at h
                      subst h
                      have ⟨hb4, hbMin⟩ := impliedMaxEinval_ge_h attr.handledAccessFs
                        (maxU32 4 s.landlockMinAbi) b s.landlockMinAbi
                        (maxU32_ge_right_h 4 s.landlockMinAbi) hFs hImp
                      have hMaxWf := wf_maxAbi_of_wf s hwf
                      refine wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) ?_ rfl
                      dsimp only
                      cases hCur : s.landlockMaxAbi? with
                      | none =>
                        simp [tightenMaxAbi, decide_eq_true hb4, decide_eq_true hbMin]
                      | some m =>
                        rw [hCur] at hMaxWf
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf
                        simp only [tightenMaxAbi]
                        exact Bool.and_eq_true _ _ |>.mpr
                          ⟨decide_eq_true (minU32_ge_of_ge_h hMaxWf.1 hb4),
                           decide_eq_true (minU32_ge_of_ge_h hMaxWf.2 hbMin)⟩
                  · have hEvF : (e == Errno.EINVAL) = false := Bool.eq_false_iff.mpr hEv
                    simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at h
                    split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
                · have hFsF : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask (maxU32 4 s.landlockMinAbi)) != 0) = false :=
                    Bool.eq_false_iff.mpr hFs
                  simp only [hFsF, Bool.false_eq_true, ↓reduceIte] at h
                  split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)

private theorem allowedStepCore_err_landlockAdd_wf
    (s s' : SandboxSysState) (ruleset : HandleId) (rule : LandlockRule HandleId) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.landlockAddRule ruleset rule) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
      | split at h

private theorem allowedStepCore_err_landlockRestrict_wf
    (s s' : SandboxSysState) (ruleset : HandleId) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.landlockRestrictSelf ruleset) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hDis : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = true
    · simp only [hDis, ↓reduceIte, Option.some.injEq] at h; subst h; exact hwf
    · have hDisF : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = false :=
        Bool.eq_false_iff.mpr hDis
      simp only [hDisF, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hFailG : (e == Errno.EPERM && canFailNnpGate s) = true
      · simp only [hFailG, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hCf : canFailNnpGate s = true := (Bool.and_eq_true _ _ |>.mp hFailG).2
        exact wf_of_eq_core (wf_pinFailed_of_canFail s hwf hCf) rfl rfl rfl rfl rfl rfl rfl rfl
      · have hFailGF : (e == Errno.EPERM && canFailNnpGate s) = false := Bool.eq_false_iff.mpr hFailG
        simp only [hFailGF, Bool.false_eq_true, ↓reduceIte] at h
        have hPassWf := wf_pinPassed_h s hwf
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq;
             first
               | exact hwf
               | exact wf_of_eq_core hPassWf rfl rfl rfl rfl rfl rfl rfl rfl)
          | split at h

private theorem allowedStepCore_err_seccomp_wf
    (s s' : SandboxSysState) (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.seccomp op flags filterBytes) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases op with
    | getActionAvail action =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
        | split at h
    | setModeFilter =>
      dsimp only at h
      by_cases hG : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = true
      · simp only [hG, ↓reduceIte] at h
        split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
      · have hGF : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = false :=
          Bool.eq_false_iff.mpr hG
        simp only [hGF, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hWk : flags.waitKillableRecv = true
        · simp only [hWk, ↓reduceIte] at h
          repeat first
            | contradiction
            | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
            | split at h
        · have hWkF : flags.waitKillableRecv = false := Bool.eq_false_iff.mpr hWk
          simp only [hWkF, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hDis : (e == Errno.ENOSYS && !hasSeccompEvidence s) = true
          · simp only [hDis, ↓reduceIte, Option.some.injEq] at h; subst h; exact hwf
          · have hDisF : (e == Errno.ENOSYS && !hasSeccompEvidence s) = false := Bool.eq_false_iff.mpr hDis
            simp only [hDisF, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hFailG : (e == Errno.EACCES && canFailNnpGate s) = true
            · simp only [hFailG, ↓reduceIte, Option.some.injEq] at h
              subst h
              have hCf : canFailNnpGate s = true := (Bool.and_eq_true _ _ |>.mp hFailG).2
              exact wf_of_eq_core (wf_pinFailed_of_canFail s hwf hCf) rfl rfl rfl rfl rfl rfl rfl rfl
            · have hFailGF : (e == Errno.EACCES && canFailNnpGate s) = false := Bool.eq_false_iff.mpr hFailG
              simp only [hFailGF, Bool.false_eq_true, ↓reduceIte] at h
              have hPassWf := wf_pinPassed_h s hwf
              repeat first
                | contradiction
                | (injection h with hEq; subst hEq;
                   first
                     | exact hwf
                     | exact wf_of_eq_core hPassWf rfl rfl rfl rfl rfl rfl rfl rfl)
                | split at h

private theorem allowedStepCore_err_prctl_wf
    (s s' : SandboxSysState) (op : PrctlOp) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.prctl op) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases op <;> dsimp only at h <;>
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact hwf)
        | split at h

private theorem allowedStepCore_err_setrlimit_wf
    (s s' : SandboxSysState) (res : RlimitResource) (cur max : UInt64) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.setrlimit res cur max) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq;
         first
           | exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl
           | exact wf_setRlimit_h _ res _ (wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl))
      | split at h

private theorem allowedStepCore_err_memfd_wf
    (s s' : SandboxSysState) (name : ByteArray) (flags : MemfdFlags) (e : Errno)
    (hwf : s.wf = true)
    (h : allowedStepCore s (.memfdCreate name flags) (.err e) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
      | split at h

private theorem allowedStepCore_landlockVersion_wf
    (s s' : SandboxSysState) (req : SandboxReq) (v : UInt32)
    (hwf : s.wf = true)
    (h : allowedStepCore s req (.landlockVersion v) = some s') :
    s'.wf = true := by
  dsimp only [allowedStepCore] at h
  cases req with
  | landlockAddRule _ _ | landlockRestrictSelf _ | seccomp _ _ _ | prctl _ | setrlimit _ _ _ | memfdCreate _ _ =>
    contradiction
  | landlockCreateRuleset attr? flags =>
    cases attr? with
    | some _ => contradiction
    | none =>
      dsimp only at h
      by_cases hVer : (flags == LANDLOCK_CREATE_RULESET_VERSION) = true
      · simp only [hVer, ↓reduceIte] at h
        by_cases hLt4 : v < 4
        · simp [hLt4] at h
        · simp only [hLt4, ↓reduceIte] at h
          have hGe4 : (4 : UInt32) ≤ v := UInt32.not_lt.mp hLt4
          cases hAbi : s.landlockAbi? with
          | none =>
            rw [hAbi] at h
            dsimp only at h
            cases hM : s.landlockMaxAbi? with
            | none =>
              rw [hM] at h
              dsimp only at h
              by_cases hLtMin : v < s.landlockMinAbi
              · simp [hLtMin] at h
              · simp only [decide_eq_false hLtMin, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
                subst h
                have hGeMin : s.landlockMinAbi ≤ v := UInt32.not_lt.mp hLtMin
                have hMaxWf := wf_maxAbi_of_wf s hwf
                rw [hM] at hMaxWf
                refine wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) hMaxWf ?_
                simp [decide_eq_true hGe4, decide_eq_true hGeMin]
            | some m =>
              rw [hM] at h
              dsimp only at h
              by_cases hLtMin : v < s.landlockMinAbi
              · simp [hLtMin] at h
              · by_cases hLeM : v ≤ m
                · simp only [decide_eq_false hLtMin, decide_eq_true hLeM, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  have hGeMin : s.landlockMinAbi ≤ v := UInt32.not_lt.mp hLtMin
                  have hMaxWf := wf_maxAbi_of_wf s hwf
                  rw [hM] at hMaxWf
                  refine wf_mk (wf_fds_of_wf s hwf) (wf_nnpGate_of_wf s hwf) hMaxWf ?_
                  simp [decide_eq_true hGe4, decide_eq_true hGeMin, decide_eq_true hLeM]
                · simp [hLtMin, decide_eq_false hLeM] at h
          | some prev =>
            rw [hAbi] at h
            dsimp only at h
            by_cases hEqP : (v == prev) = true
            · simp only [hEqP, ↓reduceIte, Option.some.injEq] at h
              subst h
              have hvEq : v = prev := eq_of_beq hEqP
              subst hvEq
              exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl hAbi.symm
            · have hEqPF : (v == prev) = false := Bool.eq_false_iff.mpr hEqP
              simp [hEqPF] at h
      · have hVerF : (flags == LANDLOCK_CREATE_RULESET_VERSION) = false := Bool.eq_false_iff.mpr hVer
        simp only [hVerF, Bool.false_eq_true, ↓reduceIte] at h
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
          | split at h

private theorem allowedStepCore_opened_wf
    (s s' : SandboxSysState) (req : SandboxReq) (hid : HandleId)
    (hwf : s.wf = true)
    (h : allowedStepCore s req (.opened hid) = some s') :
    s'.wf = true := by
  unfold allowedStepCore at h
  by_cases hDup : ((assocGet s.fds hid).isSome || (s.rlimitNofile.curExact && s.rlimitNofile.cur == 0)) = true
  · simp [hDup] at h
  · simp only [hDup, Bool.false_eq_true, ↓reduceIte] at h
    cases req with
    | landlockAddRule _ _ | landlockRestrictSelf _ | seccomp _ _ _ | prctl _ | setrlimit _ _ _ =>
      contradiction
    | landlockCreateRuleset attr? flags =>
      cases attr? with
      | none => contradiction
      | some attr =>
        dsimp only at h
        by_cases hFl : (flags != 0) = true
        · simp [hFl] at h
        · simp only [hFl, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hEmp : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
          · simp [hEmp] at h
          · simp only [hEmp, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hNet : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = true
            · simp [hNet] at h
            · simp only [hNet, Bool.false_eq_true, ↓reduceIte] at h
              let fsOk := match s.landlockAbi? with
                | some abi => (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) == 0
                | none => (attr.handledAccessFs &&& ~~~landlockKnownFsMask 9) == 0
              let impMin := impliedLandlockAbi attr.handledAccessFs
              let abiCeilingOk := match s.landlockMaxAbi? with
                | none => true
                | some m => decide (impMin ≤ m)
              change (if !fsOk || !abiCeilingOk then none else some _) = some s' at h
              by_cases hBad : (!fsOk || !abiCeilingOk) = true
              · simp [hBad] at h
              · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
                subst h
                have hFsOk : fsOk = true := by cases hf : fsOk <;> simp_all
                have hCeilOk : abiCeilingOk = true := by cases hc : abiCeilingOk <;> simp_all
                have hFds' := assocSet_hid_all_lt_h s hid
                  { kind := .landlockRuleset attr.handledAccessFs attr.handledAccessNet, cloexec := true } hwf
                have hMaxWf := wf_maxAbi_of_wf s hwf
                have hAbiWf := wf_abi_of_wf s hwf
                have hMaxWf' : (match s.landlockMaxAbi? with
                    | none => true
                    | some m => decide (4 ≤ m && maxU32 s.landlockMinAbi impMin ≤ m)) = true := by
                  cases hM : s.landlockMaxAbi? with
                  | none => rfl
                  | some m =>
                    rw [hM] at hMaxWf
                    dsimp only [abiCeilingOk] at hCeilOk
                    rw [hM] at hCeilOk
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hMaxWf hCeilOk
                    exact Bool.and_eq_true _ _ |>.mpr
                      ⟨decide_eq_true hMaxWf.1,
                       decide_eq_true ((maxU32_le_iff_h _ _ _).mpr ⟨hMaxWf.2, hCeilOk⟩)⟩
                refine wf_mk hFds' (wf_nnpGate_of_wf s hwf) hMaxWf' ?_
                dsimp only
                cases hA : s.landlockAbi? with
                | none => rfl
                | some abi =>
                  rw [hA] at hAbiWf
                  dsimp only [fsOk] at hFsOk
                  rw [hA] at hFsOk
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbiWf
                  have hRaw0 : (attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) = 0 := eq_of_beq hFsOk
                  have hImpLe : impMin ≤ abi := impliedLandlockAbi_le_h attr.handledAccessFs abi hAbiWf.1.1 hRaw0
                  have hMaxLe : maxU32 s.landlockMinAbi impMin ≤ abi :=
                    (maxU32_le_iff_h _ _ _).mpr ⟨hAbiWf.1.2, hImpLe⟩
                  exact Bool.and_eq_true _ _ |>.mpr
                    ⟨Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hAbiWf.1.1, decide_eq_true hMaxLe⟩,
                     hAbiWf.2⟩
    | memfdCreate name flags =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq;
           exact wf_mk (assocSet_hid_all_lt_h s hid _ hwf) (wf_nnpGate_of_wf s hwf)
             (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf))
        | split at h

private theorem allowedStepCore_unit_wf
    (s s' : SandboxSysState) (req : SandboxReq)
    (hwf : s.wf = true)
    (h : allowedStepCore s req .unit = some s') :
    s'.wf = true := by
  unfold allowedStepCore at h
  cases req with
  | landlockCreateRuleset _ _ | seccomp _ _ _ | prctl _ | memfdCreate _ _ =>
    contradiction
  | landlockAddRule ruleset rule =>
    dsimp only at h
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
      | split at h
  | landlockRestrictSelf ruleset =>
    dsimp only at h
    have hPassWf := wf_pinPassed_h s hwf
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq; exact wf_of_eq_core hPassWf rfl rfl rfl rfl rfl rfl rfl rfl)
      | split at h
  | setrlimit res cur max =>
    dsimp only at h
    repeat first
      | contradiction
      | (injection h with hEq; subst hEq;
         exact wf_setRlimit_h _ res _ (wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl))
      | split at h

private theorem allowedStepCore_u32_wf
    (s s' : SandboxSysState) (req : SandboxReq) (val : UInt32)
    (hwf : s.wf = true)
    (h : allowedStepCore s req (.u32 val) = some s') :
    s'.wf = true := by
  unfold allowedStepCore at h
  cases req with
  | landlockCreateRuleset _ _ | landlockAddRule _ _ | landlockRestrictSelf _ | setrlimit _ _ _ | memfdCreate _ _ =>
    contradiction
  | seccomp op flags filterBytes =>
    cases op with
    | getActionAvail action =>
      dsimp only at h
      split at h <;> first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
    | setModeFilter =>
      dsimp only at h
      have hPassWf := wf_pinPassed_h s hwf
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hPassWf rfl rfl rfl rfl rfl rfl rfl rfl)
        | split at h
  | prctl op =>
    cases op with
    | setNoNewPrivs =>
      dsimp only at h
      split at h <;> first
        | contradiction
        | (injection h with hEq; subst hEq;
           exact wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf))
    | getNoNewPrivs =>
      dsimp only at h
      by_cases h0 : (val == 0 && s.noNewPrivs? != some true && !(s.passedNnpGate && s.hasCapSysAdmin? == some false)) = true
      · simp only [h0, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine wf_mk (wf_fds_of_wf s hwf) ?_ (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf)
        cases hp : s.passedNnpGate <;> simp
      · have h0F : (val == 0 && s.noNewPrivs? != some true && !(s.passedNnpGate && s.hasCapSysAdmin? == some false)) = false :=
          Bool.eq_false_iff.mpr h0
        simp only [h0F, Bool.false_eq_true, ↓reduceIte] at h
        split at h <;> first
          | contradiction
          | (injection h with hEq; subst hEq;
             exact wf_mk (wf_fds_of_wf s hwf) (by simp) (wf_maxAbi_of_wf s hwf) (wf_abi_of_wf s hwf))
    | setChildSubreaper enable =>
      dsimp only at h
      split at h <;> first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)
    | setPdeathsig sig =>
      dsimp only at h
      split at h <;> first
        | contradiction
        | (injection h with hEq; subst hEq; exact wf_of_eq_core hwf rfl rfl rfl rfl rfl rfl rfl rfl)

/-- Relational `SandboxSysState.wf` preservation across arbitrary `allowedStepCore` transitions. -/
theorem allowedStepCore_preserves_wf
    (s s' : SandboxSysState) (req : SandboxReq) (out : SandboxOutcome)
    (hwf : s.wf = true)
    (h : allowedStepCore s req out = some s') :
    s'.wf = true := by
  cases out with
  | err e =>
    cases req with
    | landlockCreateRuleset attr? flags =>
      exact allowedStepCore_err_landlockCreate_wf s s' attr? flags e hwf h
    | landlockAddRule ruleset rule =>
      exact allowedStepCore_err_landlockAdd_wf s s' ruleset rule e hwf h
    | landlockRestrictSelf ruleset =>
      exact allowedStepCore_err_landlockRestrict_wf s s' ruleset e hwf h
    | seccomp op flags filterBytes =>
      exact allowedStepCore_err_seccomp_wf s s' op flags filterBytes e hwf h
    | prctl op =>
      exact allowedStepCore_err_prctl_wf s s' op e hwf h
    | setrlimit res cur max =>
      exact allowedStepCore_err_setrlimit_wf s s' res cur max e hwf h
    | memfdCreate name flags =>
      exact allowedStepCore_err_memfd_wf s s' name flags e hwf h
  | landlockVersion v =>
    exact allowedStepCore_landlockVersion_wf s s' req v hwf h
  | opened hid =>
    exact allowedStepCore_opened_wf s s' req hid hwf h
  | unit =>
    exact allowedStepCore_unit_wf s s' req hwf h
  | u32 val =>
    exact allowedStepCore_u32_wf s s' req val hwf h

/-- Relational `SandboxSysState.wf` preservation across arbitrary `allowedStep` transitions. -/
theorem allowedStep_preserves_wf
    (s s' : SandboxSysState) (req : SandboxReq) (out : SandboxOutcome)
    (hwf : s.wf = true)
    (h : allowedStep s req out = some s') :
    s'.wf = true := by
  unfold allowedStep at h
  by_cases hInt : (!failsPureWrapperGuard req && s.seccompMayIntercept) = true
  · simp only [hInt, ↓reduceIte] at h
    cases out with
    | err e =>
      dsimp only at h
      split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hwf)
    | landlockVersion v =>
      exact allowedStepCore_preserves_wf s s' req (.landlockVersion v) hwf h
    | opened hid =>
      exact allowedStepCore_preserves_wf s s' req (.opened hid) hwf h
    | unit =>
      exact allowedStepCore_preserves_wf s s' req .unit hwf h
    | u32 val =>
      exact allowedStepCore_preserves_wf s s' req (.u32 val) hwf h
  · have hIntF : (!failsPureWrapperGuard req && s.seccompMayIntercept) = false := Bool.eq_false_iff.mpr hInt
    simp only [hIntF, Bool.false_eq_true, ↓reduceIte] at h
    exact allowedStepCore_preserves_wf s s' req out hwf h

private theorem pinFailedNnpGate_seccomp (s : SandboxSysState) :
    (pinFailedNnpGate s).seccompMayIntercept = s.seccompMayIntercept := rfl

private theorem pinPassedNnpGate_seccomp (s : SandboxSysState) :
    (pinPassedNnpGate s).seccompMayIntercept = s.seccompMayIntercept := by
  unfold pinPassedNnpGate
  repeat first | rfl | split

private theorem setRlimit_seccomp (s : SandboxSysState) (res : RlimitResource) (st : RlimitState) :
    (s.setRlimit res st).seccompMayIntercept = s.seccompMayIntercept := by
  cases res <;> rfl

private theorem installsInterceptingSeccomp_non_u32 (req : SandboxReq) (out : SandboxOutcome)
    (hNotU32 : match out with | .u32 _ => false | _ => true) :
    installsInterceptingSeccomp req out = false := by
  cases out with
  | u32 _ => cases hNotU32
  | err _ | landlockVersion _ | opened _ | unit =>
    cases req with
    | seccomp op _ _ => cases op <;> rfl
    | _ => rfl

private theorem allowedStepCore_err_landlock_seccomp_false
    (s s' : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hSecF : s.seccompMayIntercept = false)
    (hLand : match req with | .landlockCreateRuleset _ _ | .landlockAddRule _ _ | .landlockRestrictSelf _ => true | _ => false)
    (h : allowedStepCore s req (.err e) = some s') :
    s'.seccompMayIntercept = false := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases req with
    | seccomp _ _ _ | prctl _ | setrlimit _ _ _ | memfdCreate _ _ => cases hLand
    | landlockCreateRuleset attr? flags =>
      cases attr? with
      | none =>
        dsimp only at h
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact hSecF)
          | split at h
      | some attr =>
        dsimp only at h
        by_cases hFl : (flags != 0) = true
        · simp only [hFl, ↓reduceIte] at h
          split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
        · have hFlF : (flags != 0) = false := Bool.eq_false_iff.mpr hFl
          simp only [hFlF, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hDis : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = true
          · simp only [hDis, ↓reduceIte, Option.some.injEq] at h; subst h; exact hSecF
          · have hDisF : ((e == Errno.EOPNOTSUPP || e == Errno.ENOSYS) && !hasLandlockEvidence s) = false :=
              Bool.eq_false_iff.mpr hDis
            simp only [hDisF, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hEmp : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
            · simp only [hEmp, ↓reduceIte] at h
              repeat first
                | contradiction
                | (injection h with hEq; subst hEq; exact hSecF)
                | split at h
            · have hEmpF : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = false :=
                Bool.eq_false_iff.mpr hEmp
              simp only [hEmpF, Bool.false_eq_true, ↓reduceIte] at h
              by_cases hNet : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = true
              · simp only [hNet, ↓reduceIte] at h
                repeat first
                  | contradiction
                  | (injection h with hEq; subst hEq; exact hSecF)
                  | split at h
              · have hNetF : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = false :=
                  Bool.eq_false_iff.mpr hNet
                simp only [hNetF, Bool.false_eq_true, ↓reduceIte] at h
                cases hAbi : s.landlockAbi? with
                | some abi =>
                  rw [hAbi] at h
                  dsimp only at h
                  by_cases hFs : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0) = true
                  · simp only [hFs, ↓reduceIte] at h
                    by_cases hEv : (e == Errno.EINVAL) = true
                    · simp only [hEv, ↓reduceIte, Option.some.injEq] at h; subst h; exact hSecF
                    · have hEvF : (e == Errno.EINVAL) = false := Bool.eq_false_iff.mpr hEv
                      simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at h
                      split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
                  · have hFsF : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask abi) != 0) = false :=
                      Bool.eq_false_iff.mpr hFs
                    simp only [hFsF, Bool.false_eq_true, ↓reduceIte] at h
                    split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
                | none =>
                  rw [hAbi] at h
                  dsimp only at h
                  by_cases hFs : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask (maxU32 4 s.landlockMinAbi)) != 0) = true
                  · simp only [hFs, ↓reduceIte] at h
                    by_cases hEv : (e == Errno.EINVAL) = true
                    · simp only [hEv, ↓reduceIte, Option.some.injEq] at h; subst h; exact hSecF
                    · have hEvF : (e == Errno.EINVAL) = false := Bool.eq_false_iff.mpr hEv
                      simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at h
                      split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
                  · have hFsF : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask (maxU32 4 s.landlockMinAbi)) != 0) = false :=
                      Bool.eq_false_iff.mpr hFs
                    simp only [hFsF, Bool.false_eq_true, ↓reduceIte] at h
                    split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
    | landlockAddRule _ _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact hSecF)
        | split at h
    | landlockRestrictSelf _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq;
           first | exact hSecF | exact (pinPassedNnpGate_seccomp s).trans hSecF)
        | split at h

private theorem allowedStepCore_err_seccomp_op_false
    (s s' : SandboxSysState) (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray) (e : Errno)
    (hSecF : s.seccompMayIntercept = false)
    (h : allowedStepCore s (.seccomp op flags filterBytes) (.err e) = some s') :
    s'.seccompMayIntercept = false := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases op with
    | getActionAvail _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact hSecF)
        | split at h
    | setModeFilter =>
      dsimp only at h
      by_cases hG : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = true
      · simp only [hG, ↓reduceIte] at h
        split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
      · have hGF : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = false :=
          Bool.eq_false_iff.mpr hG
        simp only [hGF, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hWk : flags.waitKillableRecv = true
        · simp only [hWk, ↓reduceIte] at h
          repeat first
            | contradiction
            | (injection h with hEq; subst hEq; exact hSecF)
            | split at h
        · have hWkF : flags.waitKillableRecv = false := Bool.eq_false_iff.mpr hWk
          simp only [hWkF, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hDis : (e == Errno.ENOSYS && !hasSeccompEvidence s) = true
          · simp only [hDis, ↓reduceIte, Option.some.injEq] at h; subst h; exact hSecF
          · have hDisF : (e == Errno.ENOSYS && !hasSeccompEvidence s) = false := Bool.eq_false_iff.mpr hDis
            simp only [hDisF, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hFailG : (e == Errno.EACCES && canFailNnpGate s) = true
            · simp only [hFailG, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact (pinFailedNnpGate_seccomp s).trans hSecF
            · have hFailGF : (e == Errno.EACCES && canFailNnpGate s) = false := Bool.eq_false_iff.mpr hFailG
              simp only [hFailGF, Bool.false_eq_true, ↓reduceIte] at h
              repeat first
                | contradiction
                | (injection h with hEq; subst hEq;
                   first | exact hSecF | exact (pinPassedNnpGate_seccomp s).trans hSecF)
                | split at h

private theorem allowedStepCore_err_other_seccomp_false
    (s s' : SandboxSysState) (req : SandboxReq) (e : Errno)
    (hSecF : s.seccompMayIntercept = false)
    (hOther : match req with | .prctl _ | .setrlimit _ _ _ | .memfdCreate _ _ => true | _ => false)
    (h : allowedStepCore s req (.err e) = some s') :
    s'.seccompMayIntercept = false := by
  dsimp only [allowedStepCore] at h
  by_cases hEf : (e == Errno.EFAULT) = true
  · simp [hEf] at h
  · have hEfF : (e == Errno.EFAULT) = false := Bool.eq_false_iff.mpr hEf
    simp only [hEfF, Bool.false_eq_true, ↓reduceIte] at h
    cases req with
    | landlockCreateRuleset _ _ | landlockAddRule _ _ | landlockRestrictSelf _ | seccomp _ _ _ => cases hOther
    | prctl op =>
      cases op <;> dsimp only at h <;>
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact hSecF)
          | split at h
    | setrlimit res _ _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq;
           first | exact hSecF | exact (setRlimit_seccomp _ res _).trans hSecF)
        | split at h
    | memfdCreate _ _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact hSecF)
        | split at h

private theorem allowedStepCore_seccomp_of_false
    (s s' : SandboxSysState) (req : SandboxReq) (out : SandboxOutcome)
    (hSecF : s.seccompMayIntercept = false)
    (h : allowedStepCore s req out = some s') :
    s'.seccompMayIntercept = installsInterceptingSeccomp req out := by
  cases out with
  | err e =>
    rw [installsInterceptingSeccomp_non_u32 req (.err e) rfl]
    cases req with
    | landlockCreateRuleset _ _ | landlockAddRule _ _ | landlockRestrictSelf _ =>
      exact allowedStepCore_err_landlock_seccomp_false s s' _ e hSecF rfl h
    | seccomp op flags filterBytes =>
      exact allowedStepCore_err_seccomp_op_false s s' op flags filterBytes e hSecF h
    | prctl _ | setrlimit _ _ _ | memfdCreate _ _ =>
      exact allowedStepCore_err_other_seccomp_false s s' _ e hSecF rfl h
  | landlockVersion v =>
    rw [installsInterceptingSeccomp_non_u32 req (.landlockVersion v) rfl]
    dsimp only [allowedStepCore] at h
    cases req with
    | landlockAddRule _ _ | landlockRestrictSelf _ | seccomp _ _ _ | prctl _ | setrlimit _ _ _ | memfdCreate _ _ =>
      contradiction
    | landlockCreateRuleset attr? _ =>
      cases attr? with
      | some _ => contradiction
      | none =>
        dsimp only at h
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact hSecF)
          | split at h
  | opened hid =>
    rw [installsInterceptingSeccomp_non_u32 req (.opened hid) rfl]
    dsimp only [allowedStepCore] at h
    split at h
    · contradiction
    · cases req with
      | landlockAddRule _ _ | landlockRestrictSelf _ | seccomp _ _ _ | prctl _ | setrlimit _ _ _ =>
        contradiction
      | landlockCreateRuleset attr? _ =>
        cases attr? with
        | none => contradiction
        | some _ =>
          dsimp only at h
          repeat first
            | contradiction
            | (injection h with hEq; subst hEq; exact hSecF)
            | split at h
      | memfdCreate _ _ =>
        dsimp only at h
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact hSecF)
          | split at h
  | unit =>
    rw [installsInterceptingSeccomp_non_u32 req .unit rfl]
    dsimp only [allowedStepCore] at h
    cases req with
    | landlockCreateRuleset _ _ | seccomp _ _ _ | prctl _ | memfdCreate _ _ => contradiction
    | landlockAddRule _ _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact hSecF)
        | split at h
    | landlockRestrictSelf _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact (pinPassedNnpGate_seccomp s).trans hSecF)
        | split at h
    | setrlimit res _ _ =>
      dsimp only at h
      repeat first
        | contradiction
        | (injection h with hEq; subst hEq; exact (setRlimit_seccomp _ res _).trans hSecF)
        | split at h
  | u32 val =>
    dsimp only [allowedStepCore] at h
    cases req with
    | landlockCreateRuleset _ _ | landlockAddRule _ _ | landlockRestrictSelf _ | setrlimit _ _ _ | memfdCreate _ _ =>
      contradiction
    | prctl op =>
      have hInst : installsInterceptingSeccomp (.prctl op) (.u32 val) = false := rfl
      rw [hInst]
      cases op <;> dsimp only at h <;>
        repeat first
          | contradiction
          | (injection h with hEq; subst hEq; exact hSecF)
          | split at h
    | seccomp op flags filterBytes =>
      cases op with
      | getActionAvail action =>
        have hInst : installsInterceptingSeccomp (.seccomp (.getActionAvail action) flags filterBytes) (.u32 val) = false := rfl
        rw [hInst]
        dsimp only at h
        split at h <;> first | contradiction | (injection h with hEq; subst hEq; exact hSecF)
      | setModeFilter =>
        dsimp only [installsInterceptingSeccomp]
        dsimp only at h
        by_cases hG : (!isValidSeccompFilterByteLen filterBytes.data.size ||
            !hasSafeSeccompRetBytes filterBytes || flags.waitKillableRecv) = true
        · simp only [hG, ↓reduceIte] at h
          contradiction
        · have hGF : (!isValidSeccompFilterByteLen filterBytes.data.size ||
              !hasSafeSeccompRetBytes filterBytes || flags.waitKillableRecv) = false := Bool.eq_false_iff.mpr hG
          simp only [hGF, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hNp : (!canPassNnpGate s) = true
          · simp [hNp] at h
          · have hNpF : (!canPassNnpGate s) = false := Bool.eq_false_iff.mpr hNp
            simp only [hNpF, Bool.false_eq_true, ↓reduceIte] at h
            cases hDec : decodeSockFilters filterBytes with
            | none => rw [hDec] at h; contradiction
            | some prog =>
              rw [hDec] at h
              dsimp only at h ⊢
              by_cases hBpf : (!checkSeccompBpf prog) = true
              · simp [hBpf] at h
              · have hBpfF : (!checkSeccompBpf prog) = false := Bool.eq_false_iff.mpr hBpf
                simp only [hBpfF, Bool.false_eq_true, ↓reduceIte] at h
                by_cases hVal0 : (val == 0) = true
                · simp only [hVal0, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  simp [hSecF, hVal0]
                · have hVal0F : (val == 0) = false := Bool.eq_false_iff.mpr hVal0
                  simp only [hVal0F, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at h ⊢
                  split at h <;> first
                    | contradiction
                    | (injection h with hEq; subst hEq; exact (pinPassedNnpGate_seccomp s).trans hSecF)

/-- Initial healthy `Sandbox` environments satisfy `HealthyEnv.wf`. -/
theorem healthyEnv_initial_wf (budget : Nat) :
    (HealthyEnv.initial budget).wf = true :=
  rfl

/-- Unprivileged healthy `Sandbox` environments satisfy `HealthyEnv.wf`. -/
theorem healthyEnv_unprivileged_wf (budget : Nat) :
    ({ state := SandboxSysState.unprivileged, eintrBudget := budget } : HealthyEnv).wf = true :=
  rfl

/-- Tightness by construction: every `allowedStep` transition from a healthy `Sandbox` environment without curated critical faults (and with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    (env : HealthyEnv) (req : SandboxReq) (out : SandboxOutcome) (s' : SandboxSysState)
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

/-- Soundness of `healthyStep` with respect to `allowedStep`: every `healthyStep` transition is a valid `allowedStep` and `allowedStepCore` transition from a well-formed environment without ambient `seccomp`, preserves `SandboxSysState.wf` (and `HealthyEnv.wf` whenever `installsInterceptingSeccomp req out = false`), excludes curated critical OS faults, and strictly decreases `eintrBudget` on `EINTR`. -/
theorem healthyStep_implies_allowedStep
    (env env' : HealthyEnv) (req : SandboxReq) (out : SandboxOutcome)
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    allowedStepCore env.state req out = some env'.state ∧
    env.wf = true ∧
    env'.state.wf = true ∧
    env'.state.seccompMayIntercept = installsInterceptingSeccomp req out ∧
    (installsInterceptingSeccomp req out = false → env'.wf = true) ∧
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
    have hSecF : env.state.seccompMayIntercept = false := by
      unfold HealthyEnv.wf at hWf
      cases hb : env.state.seccompMayIntercept <;> simp_all
    have hStWf : env.state.wf = true := by
      unfold HealthyEnv.wf at hWf
      simp [hSecF] at hWf
      exact hWf
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => rw [hAl] at h; contradiction
    | some s' =>
      rw [hAl] at h
      dsimp only at h
      have hCore : allowedStepCore env.state req out = some s' := by
        unfold allowedStep at hAl
        simp [hSecF] at hAl
        exact hAl
      have hStWf' : s'.wf = true := allowedStepCore_preserves_wf env.state s' req out hStWf hCore
      have hSec' : s'.seccompMayIntercept = installsInterceptingSeccomp req out :=
        allowedStepCore_seccomp_of_false env.state s' req out hSecF hCore
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        dsimp only
        exact ⟨rfl, hCore, hWf, hStWf', hSec',
          fun hNoInt => by simp [HealthyEnv.wf, hSec', hNoInt, hStWf'],
          hNoCrit, Nat.le_refl _, fun hc => by cases hc⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hb : env.eintrBudget > 0
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          subst h
          dsimp only
          exact ⟨rfl, hCore, hWf, hStWf', hSec',
            fun hNoInt => by simp [HealthyEnv.wf, hSec', hNoInt, hStWf'],
            hNoCrit, Nat.sub_le _ _, fun _ => by omega⟩
        · simp [hb] at h

/-- Tightness of `prctl(PR_SET_NO_NEW_PRIVS)` under `healthyStep`: either `EINTR` strictly consumes `eintrBudget` without mutating state, or `prctl` succeeds with `.u32 0`, pins `noNewPrivs? := some true`, and preserves `HealthyEnv.wf`. -/
theorem healthyStep_prctl_setNoNewPrivs_tight
    (env env' : HealthyEnv) (out : SandboxOutcome)
    (hStep : healthyStep env (.prctl .setNoNewPrivs) out = some env') :
    (out = .err Errno.EINTR ∧ env'.state = env.state ∧ env'.eintrBudget < env.eintrBudget ∧ env'.wf = true) ∨
    (out = .u32 0 ∧ env'.state = { env.state with noNewPrivs? := some true } ∧
      env'.eintrBudget = env.eintrBudget ∧ env'.wf = true) := by
  rcases healthyStep_implies_allowedStep env env' (.prctl .setNoNewPrivs) out hStep with
    ⟨_, hCore, hWf, _, _, hWfNext, hNoCrit, _, hDec⟩
  have hSecF : env.state.seccompMayIntercept = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.seccompMayIntercept <;> simp_all
  have hWf' : env'.wf = true := hWfNext rfl
  cases out with
  | err e =>
    simp only [allowedStepCore] at hCore
    by_cases hEf : (e == Errno.EFAULT) = true
    · simp [hEf] at hCore
    · simp only [hEf, Bool.false_eq_true, ↓reduceIte] at hCore
      by_cases hTr : isNonFdTransientErrno e = true
      · simp only [hTr, ↓reduceIte, Option.some.injEq] at hCore
        have hCritF : Errno.isCriticalOsErrno e = false := hNoCrit
        unfold isNonFdTransientErrno at hTr
        simp [hCritF] at hTr
        subst hTr
        exact Or.inl ⟨rfl, hCore.symm, hDec rfl, hWf'⟩
      · simp [hTr] at hCore
  | landlockVersion _ | opened _ | unit =>
    simp [allowedStepCore] at hCore
  | u32 val =>
    simp only [allowedStepCore] at hCore
    by_cases hv : (val == 0) = true
    · simp only [hv, ↓reduceIte, Option.some.injEq] at hCore
      have hVal0 : val = 0 := eq_of_beq hv
      subst hVal0
      unfold healthyStep at hStep
      simp only [hWf, Bool.not_true, isCriticalFault, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hAl : allowedStep env.state (.prctl .setNoNewPrivs) (.u32 0) with
      | none =>
        unfold allowedStep at hAl
        simp [hSecF, allowedStepCore] at hAl
      | some s2 =>
        rw [hAl] at hStep
        dsimp only at hStep
        simp only [isEintrOutcome, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hStep
        have hBud : env'.eintrBudget = env.eintrBudget := (congrArg HealthyEnv.eintrBudget hStep).symm
        exact Or.inr ⟨rfl, hCore.symm, hBud, hWf'⟩
    · simp [hv] at hCore

/-- Universal corollary over any `ops` satisfying `RefinesHealthySandboxAt proj ops`: `prctl(PR_SET_NO_NEW_PRIVS)` either encounters `EINTR` (strictly consuming `eintrBudget` without mutating `state`) or succeeds with `.ok 0` and pins `noNewPrivs? := some true` without consuming `eintrBudget`, preserving `(proj w').wf = true` in both branches. -/
theorem refinesHealthy_prctl_setNoNewPrivs_ok
    {W : Type} {proj : W → HealthyEnv} {ops : SandboxOpsM (StateM W) HandleId}
    (hRef : RefinesHealthySandboxAt proj ops)
    (w : W) (hWf : (proj w).wf = true) :
    let (res, w') := (ops.prctl .setNoNewPrivs).run w
    (res = .error Errno.EINTR ∧ (proj w').state = (proj w).state ∧
      (proj w').eintrBudget < (proj w).eintrBudget ∧ (proj w').wf = true) ∨
    (res = .ok 0 ∧ (proj w').state = { (proj w).state with noNewPrivs? := some true } ∧
      (proj w').eintrBudget = (proj w).eintrBudget ∧ (proj w').wf = true) := by
  have hStep := hRef w (.prctl .setNoNewPrivs) hWf
  dsimp only [execSandboxReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
  cases hRun : ops.prctl .setNoNewPrivs w with
  | mk res w' =>
    rw [hRun] at hStep
    dsimp only at hStep ⊢
    cases res with
    | ok val =>
      dsimp only at hStep
      rcases healthyStep_prctl_setNoNewPrivs_tight (proj w) (proj w') (.u32 val) hStep with
        ⟨hBad, _⟩ | ⟨hOk, hSt, hBud, hWf'⟩
      · cases hBad
      · injection hOk with hv
        subst hv
        exact Or.inr ⟨rfl, hSt, hBud, hWf'⟩
    | error e =>
      dsimp only at hStep
      rcases healthyStep_prctl_setNoNewPrivs_tight (proj w) (proj w') (.err e) hStep with
        ⟨hErr, hSt, hLt, hWf'⟩ | ⟨hBad, _⟩
      · injection hErr with he
        subst he
        exact Or.inl ⟨rfl, hSt, hLt, hWf'⟩
      · cases hBad

private theorem execSandboxReq_healthyModelOps (env : HealthyEnv) (req : SandboxReq) :
    (execSandboxReq healthyModelOps req).run env =
      let (out, s') := (execSandboxReq modelOps req).run env.state
      (out, { env with state := s' }) := by
  cases req with
  | landlockCreateRuleset attr? flags =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.landlockCreateRuleset attr? flags env.state with
    | mk res s' =>
      dsimp only
      cases res with
      | ok okv => cases okv <;> rfl
      | error _ => rfl
  | landlockAddRule ruleset rule =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.landlockAddRule ruleset rule env.state with
    | mk res s' => dsimp only; cases res <;> rfl
  | landlockRestrictSelf ruleset =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.landlockRestrictSelf ruleset env.state with
    | mk res s' => dsimp only; cases res <;> rfl
  | seccomp op flags filterBytes =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.seccomp op flags filterBytes env.state with
    | mk res s' => dsimp only; cases res <;> rfl
  | prctl op =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.prctl op env.state with
    | mk res s' => dsimp only; cases res <;> rfl
  | setrlimit res cur max =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.setrlimit res cur max env.state with
    | mk resOut s' => dsimp only; cases resOut <;> rfl
  | memfdCreate name flags =>
    dsimp only [execSandboxReq, healthyModelOps, StateT.run, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
    cases h : modelOps.memfdCreate name flags env.state with
    | mk res s' => dsimp only; cases res <;> rfl

private theorem modelOps_landlockCreateRuleset_no_crit_eintr (s : SandboxSysState)
    (attr? : Option LandlockRulesetAttr) (flags : UInt32) :
    let out := ((execSandboxReq modelOps (.landlockCreateRuleset attr? flags)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  cases attr? with
  | none =>
    by_cases h1 : (flags == 0) = true
    · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : effectiveModelLandlockAbi s < 4
      · simp only [h2, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [h2, ↓reduceIte]
        by_cases h3 : (flags == LANDLOCK_CREATE_RULESET_VERSION) = true
        · simp only [h3, ↓reduceIte]; exact ⟨rfl, rfl⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (flags == LANDLOCK_CREATE_RULESET_ERRATA) = true
          · simp only [h4, ↓reduceIte]
            cases s.landlockErrata? with
            | none => exact ⟨rfl, rfl⟩
            | some opt =>
              cases opt with
              | none => cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
              | some _ => exact ⟨rfl, rfl⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
  | some attr =>
    by_cases h1 : (flags != 0) = true
    · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : effectiveModelLandlockAbi s < 4
      · simp only [h2, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [h2, ↓reduceIte]
        by_cases h3 : (attr.handledAccessFs == 0 && attr.handledAccessNet == 0) = true
        · simp only [h3, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : ((attr.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0) = true
          · simp only [h4, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            by_cases h5 : ((attr.handledAccessFs &&& ~~~landlockKnownFsMask (effectiveModelLandlockAbi s)) != 0) = true
            · simp only [h5, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              by_cases h6 : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = true
              · simp only [h6, ↓reduceIte]; exact ⟨rfl, rfl⟩
              · simp only [h6, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_landlockAddRule_no_crit_eintr (s : SandboxSysState)
    (ruleset : HandleId) (rule : LandlockRule HandleId) :
    let out := ((execSandboxReq modelOps (.landlockAddRule ruleset rule)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  by_cases h1 : effectiveModelLandlockAbi s < 4
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [h1, ↓reduceIte]
    cases assocGet s.fds ruleset with
    | none => cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
    | some rsDesc =>
      by_cases ho : rsDesc.oPath = true
      · simp only [ho, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
      · simp only [ho, Bool.false_eq_true, ↓reduceIte]
        cases hk : rsDesc.kind with
        | memfd _ _ | hostPath _ | pseudoFs =>
          dsimp only; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
        | landlockRuleset handledFs handledNet =>
          dsimp only
          cases rule with
          | pathBeneath parentHid allowedAccess =>
            by_cases ha0 : (allowedAccess == 0) = true
            · simp only [ha0, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
            · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
              by_cases haM : ((allowedAccess &&& ~~~handledFs) != 0) = true
              · simp only [haM, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
              · simp only [haM, Bool.false_eq_true, ↓reduceIte]
                cases assocGet s.fds parentHid with
                | none => cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
                | some pDesc =>
                  cases hpk : pDesc.kind with
                  | landlockRuleset _ _ | memfd _ _ | pseudoFs =>
                    simp only [hpk]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
                  | hostPath isDir =>
                    simp only [hpk]
                    by_cases hd : (!isDir && ((allowedAccess &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0)) = true
                    · simp only [hd, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
                    · simp only [hd, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩
          | netPort port allowedAccess =>
            by_cases ha0 : (allowedAccess == 0) = true
            · simp only [ha0, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
            · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
              by_cases haM : ((allowedAccess &&& ~~~handledNet) != 0) = true
              · simp only [haM, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
              · simp only [haM, Bool.false_eq_true, ↓reduceIte]
                by_cases hp : port > 65535
                · simp only [hp, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
                · simp only [hp, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_landlockRestrictSelf_no_crit_eintr (s : SandboxSysState) (ruleset : HandleId) :
    let out := ((execSandboxReq modelOps (.landlockRestrictSelf ruleset)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  by_cases h1 : effectiveModelLandlockAbi s < 4
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
        !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = true
    · simp only [h2, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases assocGet s.fds ruleset with
      | none => cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
      | some desc =>
        by_cases ho : desc.oPath = true
        · simp only [ho, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
        · simp only [ho, Bool.false_eq_true, ↓reduceIte]
          cases hdk : desc.kind with
          | memfd _ _ | hostPath _ | pseudoFs =>
            dsimp only; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
          | landlockRuleset _ _ =>
            dsimp only
            by_cases hl : s.landlockLayers ≥ LANDLOCK_MAX_STACKED_LAYERS
            · simp only [hl, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
            · simp only [hl, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_seccomp_no_crit_eintr (s : SandboxSysState)
    (op : SeccompOp) (flags : SeccompFlags) (filterBytes : ByteArray) :
    let out := ((execSandboxReq modelOps (.seccomp op flags filterBytes)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  cases op with
  | getActionAvail action =>
    by_cases h1 : (flags.toBits != 0) = true
    · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : isKnownSeccompAction action = true
      · simp only [h2, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
  | setModeFilter =>
    by_cases h1 : (!isValidSeccompFilterByteLen filterBytes.data.size || !hasSafeSeccompRetBytes filterBytes) = true
    · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : flags.waitKillableRecv = true
      · simp only [h2, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : (!(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false)) &&
            !(s.hasCapSysAdmin?.getD (s.passedNnpGate && !(s.noNewPrivs?.getD (s.passedNnpGate && s.hasCapSysAdmin? == some false))))) = true
        · simp only [h3, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          cases decodeSockFilters filterBytes with
          | none => cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
          | some prog =>
            by_cases h4 : (!checkSeccompBpf prog) = true
            · simp only [h4, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_prctl_no_crit_eintr (s : SandboxSysState) (op : PrctlOp) :
    let out := ((execSandboxReq modelOps (.prctl op)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  cases op with
  | setNoNewPrivs | getNoNewPrivs | setChildSubreaper _ => exact ⟨rfl, rfl⟩
  | setPdeathsig sig =>
    by_cases h : sig > MAX_LINUX_SIGNAL
    · simp only [h, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_setrlimit_no_crit_eintr (s : SandboxSysState)
    (res : RlimitResource) (cur max : UInt64) :
    let out := ((execSandboxReq modelOps (.setrlimit res cur max)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  by_cases h1 : cur > max
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (res == .nofile && decide (max > s.nofileNrOpenCeil)) = true
    · simp only [h2, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!(s.hasCapSysResource?.getD false) && decide (max > (s.getRlimit res).hardUpper)) = true
      · simp only [h3, ↓reduceIte]
        cases s.seccompMayIntercept
        · by_cases h4 : (res == .nofile && s.hasCapSysResource?.isNone) = true <;>
            simp only [Bool.not_false, ↓reduceIte, h4, Bool.false_eq_true] <;> exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_memfdCreate_no_crit_eintr (s : SandboxSysState)
    (name : ByteArray) (flags : MemfdFlags) :
    let out := ((execSandboxReq modelOps (.memfdCreate name flags)).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  dsimp only [execSandboxReq, modelOps, StateT.run, Pure.pure, Bind.bind,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, st_pure_h, st_bind_h, st_set_h, st_get_h]
  by_cases h1 : (hasEmbeddedNul name || decide (name.data.size > MFD_NAME_MAX)) = true
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (flags.noexecSeal && flags.exec) = true
    · simp only [h2, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (flags.exec && (s.memfdNoexecStrict? == some true)) = true
      · simp only [h3, ↓reduceIte]; cases s.seccompMayIntercept <;> exact ⟨rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (s.rlimitNofile.curExact && decide (s.fds.length ≥ s.rlimitNofile.cur.toNat)) = true
        · simp only [h4, ↓reduceIte]; exact ⟨rfl, rfl⟩
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem modelOps_not_critical_or_eintr (s : SandboxSysState) (req : SandboxReq) :
    let out := ((execSandboxReq modelOps req).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  cases req with
  | landlockCreateRuleset attr? flags => exact modelOps_landlockCreateRuleset_no_crit_eintr s attr? flags
  | landlockAddRule ruleset rule => exact modelOps_landlockAddRule_no_crit_eintr s ruleset rule
  | landlockRestrictSelf ruleset => exact modelOps_landlockRestrictSelf_no_crit_eintr s ruleset
  | seccomp op flags filterBytes => exact modelOps_seccomp_no_crit_eintr s op flags filterBytes
  | prctl op => exact modelOps_prctl_no_crit_eintr s op
  | setrlimit res cur max => exact modelOps_setrlimit_no_crit_eintr s res cur max
  | memfdCreate name flags => exact modelOps_memfdCreate_no_crit_eintr s name flags

private theorem modelOps_refines_allowedStep_single (s : SandboxSysState) (hwf : s.wf = true)
    (req : SandboxReq) :
    let r := (execSandboxReq modelOps req).run s
    allowedStep s req r.1 = some r.2 ∧ r.2.wf = true := by
  cases req with
  | landlockCreateRuleset attr? flags => exact refine_landlockCreateRuleset s hwf attr? flags
  | landlockAddRule ruleset rule => exact refine_landlockAddRule s hwf ruleset rule
  | landlockRestrictSelf ruleset => exact refine_landlockRestrictSelf s hwf ruleset
  | seccomp op flags filterBytes => exact refine_seccomp s hwf op flags filterBytes
  | prctl op => exact refine_prctl s hwf op
  | setrlimit res cur max => exact refine_setrlimit s hwf res cur max
  | memfdCreate name flags => exact refine_memfdCreate s hwf name flags

/-- Witness theorem: `healthyModelOps` universally satisfies `RefinesHealthySandbox`. -/
theorem healthyModelOps_refinesHealthySandbox :
    RefinesHealthySandbox healthyModelOps := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  rw [execSandboxReq_healthyModelOps]
  have hStWf : env.state.wf = true := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.seccompMayIntercept <;> simp_all
  have hRef := modelOps_refines_allowedStep_single env.state hStWf req
  have hNoCE := modelOps_not_critical_or_eintr env.state req
  cases hRun : (execSandboxReq modelOps req).run env.state with
  | mk out s' =>
    rw [hRun] at hRef hNoCE
    dsimp only at hRef hNoCE ⊢
    rw [allowedStep_healthy_tight env req out s' hRef.1 hWf (by simp [hNoCE.2]) hNoCE.1]
    simp [hNoCE.2]

/-- Lens-lifting composition theorem: lifting any `ops` satisfying `RefinesHealthySandbox` along `(getEnv, setEnv)` with `∀ w e, getEnv (setEnv w e) = e` satisfies `RefinesHealthySandboxAt getEnv`. -/
theorem refinesHealthySandboxAt_of_lens
    {W : Type} (getEnv : W → HealthyEnv) (setEnv : W → HealthyEnv → W)
    (hGetSet : ∀ (w : W) (e : HealthyEnv), getEnv (setEnv w e) = e)
    {ops : SandboxOpsM (StateM HealthyEnv) HandleId} (hRef : RefinesHealthySandbox ops) :
    RefinesHealthySandboxAt getEnv
      { landlockCreateRuleset := fun attr? flags w =>
          let (res, e') := (ops.landlockCreateRuleset attr? flags).run (getEnv w); (res, setEnv w e')
        landlockAddRule := fun ruleset rule w =>
          let (res, e') := (ops.landlockAddRule ruleset rule).run (getEnv w); (res, setEnv w e')
        landlockRestrictSelf := fun ruleset w =>
          let (res, e') := (ops.landlockRestrictSelf ruleset).run (getEnv w); (res, setEnv w e')
        seccomp := fun op flags filterBytes w =>
          let (res, e') := (ops.seccomp op flags filterBytes).run (getEnv w); (res, setEnv w e')
        prctl := fun op w =>
          let (res, e') := (ops.prctl op).run (getEnv w); (res, setEnv w e')
        setrlimit := fun res cur max w =>
          let (outRes, e') := (ops.setrlimit res cur max).run (getEnv w); (outRes, setEnv w e')
        memfdCreate := fun name flags w =>
          let (res, e') := (ops.memfdCreate name flags).run (getEnv w); (res, setEnv w e') } := by
  intro w req hWf
  have hStep := hRef (getEnv w) req hWf
  cases req with
  | landlockCreateRuleset attr? flags =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.landlockCreateRuleset attr? flags (getEnv w) with
    | mk res e' =>
      rw [hC] at hStep
      cases res with
      | error _ => simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep
      | ok cr => cases cr <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | landlockAddRule ruleset rule =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.landlockAddRule ruleset rule (getEnv w) with
    | mk res e' => rw [hC] at hStep; cases res <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | landlockRestrictSelf ruleset =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.landlockRestrictSelf ruleset (getEnv w) with
    | mk res e' => rw [hC] at hStep; cases res <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | seccomp op flags filterBytes =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.seccomp op flags filterBytes (getEnv w) with
    | mk res e' => rw [hC] at hStep; cases res <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | prctl op =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.prctl op (getEnv w) with
    | mk res e' => rw [hC] at hStep; cases res <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | setrlimit res cur max =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.setrlimit res cur max (getEnv w) with
    | mk outRes e' => rw [hC] at hStep; cases outRes <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)
  | memfdCreate name flags =>
    dsimp only [id, execSandboxReq, Bind.bind, Pure.pure, StateT.run, st_bind_h, st_pure_h] at hStep ⊢
    cases hC : ops.memfdCreate name flags (getEnv w) with
    | mk res e' => rw [hC] at hStep; cases res <;> (simp only [st_pure_h, hGetSet] at hStep ⊢; exact hStep)

private theorem sandbox_errno_transient_partition (e : Errno) :
    Errno.isTransientOsErrno e =
      (e == Errno.EINTR || Errno.isCriticalOsErrno e || Errno.isResourceLimitErrno e) ∧
    (Errno.isCriticalOsErrno e && Errno.isResourceLimitErrno e) = false := by
  refine ⟨?_, ?_⟩
  · unfold Errno.isTransientOsErrno Errno.isCriticalOsErrno Errno.isResourceLimitErrno
    cases e == Errno.EINTR <;> cases e == Errno.EIO <;> cases e == Errno.ENOMEM <;>
      cases e == Errno.ENFILE <;> cases e == Errno.EMFILE <;> cases e == Errno.ENOSPC <;> rfl
  · by_cases h1 : e == Errno.ENOMEM
    · have : e = Errno.ENOMEM := eq_of_beq h1
      subst this; decide
    · by_cases h2 : e == Errno.EIO
      · have : e = Errno.EIO := eq_of_beq h2
        subst this; decide
      · by_cases h3 : e == Errno.ENFILE
        · have : e = Errno.ENFILE := eq_of_beq h3
          subst this; decide
        · simp [Errno.isCriticalOsErrno, h1, h2, h3]

/-- Proof of `test_sandbox_healthyStep_and_healthyModelOps`. -/
theorem sandbox_healthyStep_and_healthyModelOps_allPass :
    AllPass test_sandbox_healthyStep_and_healthyModelOps := by
  intro e
  have hPart := sandbox_errno_transient_partition e
  dsimp only [test_sandbox_healthyStep_and_healthyModelOps, NondetTest.assert, Bind.bind, Pure.pure]
  refine ⟨hPart.1, hPart.2, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro env hWf req
    have hStep := healthyModelOps_refinesHealthySandbox env req hWf
    dsimp only [id] at hStep
    have hEq := execSandboxReq_healthyModelOps env req
    cases hRun : (execSandboxReq healthyModelOps req).run env with
    | mk out env' =>
      rw [hRun] at hStep hEq
      dsimp only at hStep ⊢
      have hImp := healthyStep_implies_allowedStep env env' req out hStep
      cases hM : (execSandboxReq modelOps req).run env.state with
      | mk outM sM =>
        rw [hM] at hEq
        dsimp only at hEq ⊢
        have hBud : env'.eintrBudget = env.eintrBudget := by
          injection hEq with _ hEnvEq
          rw [hEnvEq]
        exact ⟨⟨hEq, hStep, hBud, hImp.2.2.2.1, hImp.2.2.2.2.2.1⟩, fun _ _ _ => ⟨rfl, trivial⟩⟩

/-- Reachability witness for `test_sandbox_healthyStep_and_healthyModelOps`. -/
theorem sandbox_healthyStep_and_healthyModelOps_canReach :
    CanReach test_sandbox_healthyStep_and_healthyModelOps := by
  have hAll := sandbox_healthyStep_and_healthyModelOps_allPass Errno.EINTR
  have hRest := hAll.2.2.2.2.2.2.2.2.2.2 (HealthyEnv.initial 1) rfl (.prctl .setNoNewPrivs)
  refine ⟨Errno.EINTR, hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    hAll.2.2.2.2.2.1, hAll.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.2.1,
    hAll.2.2.2.2.2.2.2.2.2.1, HealthyEnv.initial 1, rfl, .prctl .setNoNewPrivs,
    hRest.1, HealthyEnv.initial 1, .prctl .setNoNewPrivs, .u32 0, ?_⟩
  exact hRest.2 (HealthyEnv.initial 1) (.prctl .setNoNewPrivs) (.u32 0)

end LeanSwe.LinuxSyscall.Sandbox
