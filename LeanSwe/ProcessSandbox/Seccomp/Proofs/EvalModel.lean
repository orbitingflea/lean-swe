import LeanSwe.ProcessSandbox.Seccomp.Proofs.BlockSpecs

namespace LeanSwe.ProcessSandbox.Seccomp.Proofs

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Seccomp

/-- Pure reference verdict computed by the compiled `seccomp` filter on `(arch, inp)`. -/
def seccompModelVerdict (arch : SeccompArch) (inp : SeccompData) : UInt32 :=
  if inp.arch != auditArchOf arch then
    SECCOMP_RET_ERRNO_EPERM
  else if arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT) then
    SECCOMP_RET_ERRNO_EPERM
  else
    let nrs := syscallNumbersFor arch
    if inp.nr == nrs.clone3 then
      SECCOMP_RET_ERRNO_ENOSYS
    else if inp.nr == nrs.clone then
      if (inp.args.a0.toUInt32 &&& CLONE_NEW_NS_MASK) != 0 then
        SECCOMP_RET_ERRNO_EPERM
      else
        SECCOMP_RET_ALLOW
    else if inp.nr == nrs.socket then
      let dom := inp.args.a0.toUInt32
      if dom == LINUX_AF_UNIX || dom == LINUX_AF_SMC then
        SECCOMP_RET_ERRNO_EPERM
      else
        SECCOMP_RET_ALLOW
    else if inp.nr == nrs.socketpair then
      let dom := inp.args.a0.toUInt32
      let baseType := inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS
      let proto := inp.args.a2.toUInt32
      if dom == LINUX_AF_UNIX && proto == 0 && (baseType == LINUX_SOCK_STREAM || baseType == LINUX_SOCK_SEQPACKET) then
        SECCOMP_RET_ALLOW
      else
        SECCOMP_RET_ERRNO_EPERM
    else if inp.nr == nrs.sendto then
      if (inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        SECCOMP_RET_ERRNO_EPERM
      else
        SECCOMP_RET_ALLOW
    else if inp.nr == nrs.sendmsg then
      if (inp.args.a2.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        SECCOMP_RET_ERRNO_EPERM
      else
        SECCOMP_RET_ALLOW
    else if inp.nr == nrs.sendmmsg then
      if (inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        SECCOMP_RET_ERRNO_EPERM
      else
        SECCOMP_RET_ALLOW
    else if (denySyscallNumbers nrs).contains inp.nr then
      SECCOMP_RET_ERRNO_EPERM
    else
      SECCOMP_RET_ALLOW

/-- `evalBpf` on `Seccomp.Impl.compileSeccompBpf arch` evaluates to `some (seccompModelVerdict arch inp)`. -/
theorem evalBpf_compileSeccompBpf_eq_model (arch : SeccompArch) (inp : SeccompData) :
    evalBpf (Seccomp.Impl.compileSeccompBpf arch) inp = some (seccompModelVerdict arch inp) := by
  unfold evalBpf Seccomp.Impl.compileSeccompBpf
  have hList : (Seccomp.Impl.compileSeccompBpfList arch).toArray.toList = Seccomp.Impl.compileSeccompBpfList arch := rfl
  rw [hList]
  let nrs := syscallNumbersFor arch
  let rest9 := [bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]
  let rest8 := Seccomp.Impl.denyListBlock (denySyscallNumbers nrs) ++ rest9
  let rest7 := Seccomp.Impl.guardMaskBlock nrs.sendmmsg (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN ++ rest8
  let rest6 := Seccomp.Impl.guardMaskBlock nrs.sendmsg (seccompArgLowOffset 2) LINUX_MSG_FASTOPEN ++ rest7
  let rest5 := Seccomp.Impl.guardMaskBlock nrs.sendto (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN ++ rest6
  let rest4 := Seccomp.Impl.socketpairBlock nrs.socketpair ++ rest5
  let rest3 := Seccomp.Impl.socketBlock nrs.socket ++ rest4
  let rest2 := Seccomp.Impl.guardMaskBlock nrs.clone (seccompArgLowOffset 0) CLONE_NEW_NS_MASK ++ rest3
  let rest1 := Seccomp.Impl.clone3Block nrs.clone3 ++ rest2
  let rest0 := Seccomp.Impl.x32GuardBlock arch ++ rest1
  have hProg : Seccomp.Impl.compileSeccompBpfList arch = Seccomp.Impl.archHeaderBlock arch ++ rest0 := by
    simp [Seccomp.Impl.compileSeccompBpfList, nrs, rest0, rest1, rest2, rest3, rest4, rest5, rest6, rest7, rest8, rest9,
      List.append_assoc]
  rw [hProg]
  have h0 := archHeaderBlock_spec arch inp rest0 _ (Nat.le_refl _)
  by_cases hArch : inp.arch != auditArchOf arch
  · simp only [hArch, ↓reduceIte] at h0
    simp only [seccompModelVerdict, hArch, ↓reduceIte]
    exact h0
  · simp only [hArch, Bool.false_eq_true, ↓reduceIte] at h0
    rcases h0 with ⟨f1, hf1, hs1⟩
    have h1 := x32GuardBlock_spec arch inp rest1 f1 inp.nr hf1
    by_cases hX32 : arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)
    · simp only [hX32, ↓reduceIte] at h1
      simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32]
      exact hs1.trans h1
    · simp only [hX32, Bool.false_eq_true, ↓reduceIte] at h1
      rcases h1 with ⟨f2, hf2, hs2⟩
      have h2 := clone3Block_spec nrs.clone3 inp rest2 f2 inp.nr hf2
      by_cases hC3 : inp.nr == nrs.clone3
      · simp only [hC3, ↓reduceIte] at h2
        simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, nrs]
        exact hs1.trans (hs2.trans h2)
      · simp only [hC3, Bool.false_eq_true, ↓reduceIte] at h2
        rcases h2 with ⟨f3, hf3, hs3⟩
        have h3 := guardMaskBlock_spec nrs.clone (seccompArgLowOffset 0) CLONE_NEW_NS_MASK _ inp
          (readSeccompDataWord_arg0 inp) rest3 f3 inp.nr hf3
        by_cases hCl : inp.nr == nrs.clone
        · simp only [hCl, ↓reduceIte] at h3
          simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, nrs]
          exact hs1.trans (hs2.trans (hs3.trans h3))
        · simp only [hCl, Bool.false_eq_true, ↓reduceIte] at h3
          rcases h3 with ⟨f4, hf4, hs4⟩
          have h4 := socketBlock_spec nrs.socket inp rest4 f4 inp.nr hf4
          by_cases hSo : inp.nr == nrs.socket
          · simp only [hSo, ↓reduceIte] at h4
            simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, nrs]
            exact hs1.trans (hs2.trans (hs3.trans (hs4.trans h4)))
          · simp only [hSo, Bool.false_eq_true, ↓reduceIte] at h4
            rcases h4 with ⟨f5, hf5, hs5⟩
            have h5 := socketpairBlock_spec nrs.socketpair inp rest5 f5 inp.nr hf5
            by_cases hSp : inp.nr == nrs.socketpair
            · simp only [hSp, ↓reduceIte] at h5
              simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, nrs]
              exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans h5))))
            · simp only [hSp, Bool.false_eq_true, ↓reduceIte] at h5
              rcases h5 with ⟨f6, hf6, hs6⟩
              have h6 := guardMaskBlock_spec nrs.sendto (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN _ inp
                (readSeccompDataWord_arg3 inp) rest6 f6 inp.nr hf6
              by_cases hSto : inp.nr == nrs.sendto
              · simp only [hSto, ↓reduceIte] at h6
                simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, hSto, nrs]
                exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans h6)))))
              · simp only [hSto, Bool.false_eq_true, ↓reduceIte] at h6
                rcases h6 with ⟨f7, hf7, hs7⟩
                have h7 := guardMaskBlock_spec nrs.sendmsg (seccompArgLowOffset 2) LINUX_MSG_FASTOPEN _ inp
                  (readSeccompDataWord_arg2 inp) rest7 f7 inp.nr hf7
                by_cases hSm : inp.nr == nrs.sendmsg
                · simp only [hSm, ↓reduceIte] at h7
                  simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, hSto, hSm, nrs]
                  exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans h7))))))
                · simp only [hSm, Bool.false_eq_true, ↓reduceIte] at h7
                  rcases h7 with ⟨f8, hf8, hs8⟩
                  have h8 := guardMaskBlock_spec nrs.sendmmsg (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN _ inp
                    (readSeccompDataWord_arg3 inp) rest8 f8 inp.nr hf8
                  by_cases hSmm : inp.nr == nrs.sendmmsg
                  · simp only [hSmm, ↓reduceIte] at h8
                    simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, hSto, hSm, hSmm, nrs]
                    exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans (hs8.trans h8)))))))
                  · simp only [hSmm, Bool.false_eq_true, ↓reduceIte] at h8
                    rcases h8 with ⟨f9, hf9, hs9⟩
                    have h9 := denyListBlock_spec (denySyscallNumbers nrs) inp rest9 f9 inp.nr hf9
                    by_cases hDen : (denySyscallNumbers nrs).contains inp.nr
                    · simp only [hDen, ↓reduceIte] at h9
                      simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, hSto, hSm, hSmm, hDen, nrs]
                      exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans (hs8.trans (hs9.trans h9))))))))
                    · simp only [hDen, Bool.false_eq_true, ↓reduceIte] at h9
                      rcases h9 with ⟨f10, hf10, hs10⟩
                      obtain ⟨f11, rfl⟩ : ∃ f11, f10 = f11 + 1 := ⟨f10 - 1, by simp [rest9] at hf10; omega⟩
                      have hRet := bpf_ret_step inp f11 SECCOMP_RET_ALLOW [] inp.nr
                      simp only [seccompModelVerdict, hArch, Bool.false_eq_true, ↓reduceIte, hX32, hC3, hCl, hSo, hSp, hSto, hSm, hSmm, hDen, nrs]
                      exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans (hs8.trans (hs9.trans (hs10.trans hRet)))))))))

private theorem isSome_if_some (c : Bool) (a : AdminOp) (o : Option AdminOp) :
    (if c = true then some a else o).isSome = (c || o.isSome) := by
  cases c <;> rfl

private theorem beq_sym_bool (a b : UInt32) : (a == b) = (b == a) := by
  cases h : a == b
  · exact (beq_false_of_ne (fun he => by rw [he, beq_self_eq_true] at h; cases h)).symm
  · exact (beq_iff_eq.mpr (beq_iff_eq.mp h).symm).symm

/-- `classifyDeniedSyscallNr` returns `some _` iff `nr` belongs to `denySyscallNumbers`. -/
theorem classifyDeniedSyscallNr_isSome_iff (nrs : SyscallNumbers) (nr : UInt32) :
    (classifyDeniedSyscallNr nrs nr).isSome = (denySyscallNumbers nrs).contains nr := by
  rw [classifyDeniedSyscallNr]
  simp only [isSome_if_some, Option.isSome_none, Bool.or_false]
  simp only [denySyscallNumbers, List.contains_cons, List.contains_nil, Bool.or_false]
  simp only [beq_sym_bool nr _]
  by_cases hP : (nrs.perf_event_open == nr) = true
  · simp [hP]
  · simp only [hP, Bool.or_false, Bool.false_or]
    by_cases hU : (nrs.userfaultfd == nr) = true
    · simp [hU]
    · simp only [hU, Bool.or_false, Bool.false_or, Bool.or_assoc]

/-- Every `seccompModelVerdict` is one of `ALLOW`, `ERRNO(EPERM)`, or `ERRNO(ENOSYS)`. -/
theorem seccompModelVerdict_cases (arch : SeccompArch) (inp : SeccompData) :
    seccompModelVerdict arch inp = 0x7fff0000 ∨
    seccompModelVerdict arch inp = 0x00050001 ∨
    seccompModelVerdict arch inp = 0x00050026 := by
  unfold seccompModelVerdict SECCOMP_RET_ALLOW SECCOMP_RET_ERRNO_EPERM SECCOMP_RET_ERRNO_ENOSYS
  dsimp only
  split; · exact Or.inr (Or.inl rfl)
  split; · exact Or.inr (Or.inl rfl)
  split; · exact Or.inr (Or.inr rfl)
  split; · split <;> simp
  split; · split <;> simp
  split; · split <;> simp
  split; · split <;> simp
  split; · split <;> simp
  split; · split <;> simp
  split <;> simp

/-- `seccompModelVerdict .x86_64` returns `SECCOMP_RET_ERRNO_EPERM` on every unconditional deny-table syscall. -/
theorem seccompModelVerdict_x86_deny_mem (nr : UInt32) (inp : SeccompData)
    (hMem : (denySyscallNumbers x86_64SyscallNumbers).contains nr = true)
    (hLt : decide (nr ≥ X32_SYSCALL_BIT) = false)
    (hDisj : ([435, 56, 41, 53, 44, 46, 307] : List UInt32).contains nr = false) :
    seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := nr } = SECCOMP_RET_ERRNO_EPERM := by
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff] at hDisj
  rcases hDisj with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hA : (({ inp with arch := 0xc000003e, nr := nr }.arch) != auditArchOf .x86_64) = false := by
    simp [auditArchOf, AUDIT_ARCH_X86_64]
  have hx : (SeccompArch.x86_64 == .x86_64) = true := rfl
  simp only [seccompModelVerdict, hA, hx, hLt, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
    syscallNumbersFor, x86_64SyscallNumbers, h1, h2, h3, h4, h5, h6, h7]
  change (if (denySyscallNumbers x86_64SyscallNumbers).contains nr = true then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW) = SECCOMP_RET_ERRNO_EPERM
  rw [hMem]
  rfl

/-- `seccompModelVerdict .aarch64` returns `SECCOMP_RET_ERRNO_EPERM` on every unconditional deny-table syscall. -/
theorem seccompModelVerdict_aarch64_deny_mem (nr : UInt32) (inp : SeccompData)
    (hMem : (denySyscallNumbers aarch64SyscallNumbers).contains nr = true)
    (hDisj : ([435, 220, 198, 199, 206, 211, 269] : List UInt32).contains nr = false) :
    seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := nr } = SECCOMP_RET_ERRNO_EPERM := by
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff] at hDisj
  rcases hDisj with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hA : (({ inp with arch := 0xc00000b7, nr := nr }.arch) != auditArchOf .aarch64) = false := by
    simp [auditArchOf, AUDIT_ARCH_AARCH64]
  have ha : (SeccompArch.aarch64 == .x86_64) = false := rfl
  simp only [seccompModelVerdict, hA, ha, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    syscallNumbersFor, aarch64SyscallNumbers, h1, h2, h3, h4, h5, h6, h7]
  change (if (denySyscallNumbers aarch64SyscallNumbers).contains nr = true then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW) = SECCOMP_RET_ERRNO_EPERM
  rw [hMem]
  rfl

/-- `seccompModelVerdict .x86_64` returns `SECCOMP_RET_ALLOW` on native non-x32 syscalls outside guarded/denied tables. -/
theorem seccompModelVerdict_x86_allow_of_not_mem (inp : SeccompData)
    (hArch : inp.arch = 0xc000003e) (hX32 : inp.nr < 0x40000000)
    (hNot : ([435, 56, 41, 53, 44, 46, 307] ++ denySyscallNumbers x86_64SyscallNumbers).contains inp.nr = false) :
    seccompModelVerdict .x86_64 inp = SECCOMP_RET_ALLOW := by
  simp only [List.contains_append, Bool.or_eq_false_iff, List.contains_cons, List.contains_nil,
    Bool.or_false] at hNot
  rcases hNot with ⟨⟨h435, h56, h41, h53, h44, h46, h307⟩, hDen⟩
  have hn1 : (inp.arch != auditArchOf .x86_64) = false := by simp [auditArchOf, AUDIT_ARCH_X86_64, hArch]
  have hn2 : (SeccompArch.x86_64 == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)) = false := by
    simp [X32_SYSCALL_BIT]
    intro _
    exact hX32
  simp only [seccompModelVerdict, hn1, Bool.false_eq_true, ↓reduceIte, hn2, syscallNumbersFor, x86_64SyscallNumbers]
  simp only [h435, h56, h41, h53, h44, h46, h307, Bool.false_eq_true, ↓reduceIte]
  change (if (denySyscallNumbers x86_64SyscallNumbers).contains inp.nr = true then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW) = SECCOMP_RET_ALLOW
  rw [hDen]
  rfl

/-- `seccompModelVerdict .aarch64` returns `SECCOMP_RET_ALLOW` on native syscalls outside guarded/denied tables. -/
theorem seccompModelVerdict_aarch64_allow_of_not_mem (inp : SeccompData)
    (hArch : inp.arch = 0xc00000b7)
    (hNot : ([435, 220, 198, 199, 206, 211, 269] ++ denySyscallNumbers aarch64SyscallNumbers).contains inp.nr = false) :
    seccompModelVerdict .aarch64 inp = SECCOMP_RET_ALLOW := by
  simp only [List.contains_append, Bool.or_eq_false_iff, List.contains_cons, List.contains_nil,
    Bool.or_false] at hNot
  rcases hNot with ⟨⟨h435, h220, h198, h199, h206, h211, h269⟩, hDen⟩
  have hn1 : (inp.arch != auditArchOf .aarch64) = false := by simp [auditArchOf, AUDIT_ARCH_AARCH64, hArch]
  have ha : (SeccompArch.aarch64 == .x86_64) = false := rfl
  simp only [seccompModelVerdict, hn1, ha, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    syscallNumbersFor, aarch64SyscallNumbers]
  simp only [h435, h220, h198, h199, h206, h211, h269, Bool.false_eq_true, ↓reduceIte]
  change (if (denySyscallNumbers aarch64SyscallNumbers).contains inp.nr = true then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW) = SECCOMP_RET_ALLOW
  rw [hDen]
  rfl

/-- `seccompModelVerdict` agrees pointwise with `decodeSeccompSyscall` classification. -/
theorem seccompModelVerdict_eq_decoded (arch : SeccompArch) (inp : SeccompData) :
    seccompModelVerdict arch inp =
      (match decodeSeccompSyscall arch inp with
        | none => SECCOMP_RET_ALLOW
        | some .clone3Attempt => SECCOMP_RET_ERRNO_ENOSYS
        | some (.anonUnixSocketpair .stream) => SECCOMP_RET_ALLOW
        | some (.anonUnixSocketpair .seqpacket) => SECCOMP_RET_ALLOW
        | some (.cloneProc _ false) => SECCOMP_RET_ALLOW
        | some _ => SECCOMP_RET_ERRNO_EPERM) := by
  unfold seccompModelVerdict decodeSeccompSyscall
  by_cases hArch : inp.arch != auditArchOf arch
  · simp [hArch]
  · simp only [hArch, Bool.false_eq_true, ↓reduceIte]
    by_cases hX32 : (arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)) = true
    · have hA : (arch == .x86_64) = true := (Bool.and_eq_true _ _).mp hX32 |>.1
      have hN : inp.nr ≥ X32_SYSCALL_BIT := of_decide_eq_true ((Bool.and_eq_true _ _).mp hX32 |>.2)
      simp [hA, hN]
    · have hX32f : (arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)) = false := Bool.eq_false_iff.mpr hX32
      simp only [hX32f, Bool.false_eq_true, ↓reduceIte]
      by_cases hC3 : inp.nr == (syscallNumbersFor arch).clone3
      · simp [hC3]
      · simp only [hC3, Bool.false_eq_true, ↓reduceIte]
        by_cases hCl : inp.nr == (syscallNumbersFor arch).clone
        · simp only [hCl, ↓reduceIte]
          cases ((inp.args.a0.toUInt32 &&& CLONE_NEW_NS_MASK) != 0) <;> rfl
        · simp only [hCl, Bool.false_eq_true, ↓reduceIte]
          by_cases hSo : inp.nr == (syscallNumbersFor arch).socket
          · simp only [hSo, ↓reduceIte]
            by_cases hU : inp.args.a0.toUInt32 == LINUX_AF_UNIX
            · simp [hU]
            · by_cases hS : inp.args.a0.toUInt32 == LINUX_AF_SMC <;> simp [hU, hS]
          · simp only [hSo, Bool.false_eq_true, ↓reduceIte]
            by_cases hSp : inp.nr == (syscallNumbersFor arch).socketpair
            · simp only [hSp, ↓reduceIte]
              by_cases hU : inp.args.a0.toUInt32 == LINUX_AF_UNIX
              · have hNotNe : (inp.args.a0.toUInt32 != LINUX_AF_UNIX) = false := by simp [bne, beq_iff_eq.mp hU]
                by_cases hPr : inp.args.a2.toUInt32 == 0
                · have hNotPr : (inp.args.a2.toUInt32 != 0) = false := by simp [bne, beq_iff_eq.mp hPr]
                  by_cases hStr : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_STREAM
                  · simp [hU, hNotNe, hPr, hNotPr, hStr]
                  · by_cases hSeq : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_SEQPACKET <;>
                      simp [hU, hNotNe, hPr, hNotPr, hStr, hSeq]
                · have hNotPr : (inp.args.a2.toUInt32 != 0) = true := bne_iff_ne.mpr fun h => hPr (beq_iff_eq.mpr h)
                  simp [hU, hNotNe, hPr, hNotPr]
              · have hNe : (inp.args.a0.toUInt32 != LINUX_AF_UNIX) = true := bne_iff_ne.mpr fun h => hU (beq_iff_eq.mpr h)
                simp [hU, hNe]
            · simp only [hSp, Bool.false_eq_true, ↓reduceIte]
              by_cases hSto : inp.nr == (syscallNumbersFor arch).sendto
              · simp only [hSto, ↓reduceIte]
                cases ((inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) <;> rfl
              · simp only [hSto, Bool.false_eq_true, ↓reduceIte]
                by_cases hSm : inp.nr == (syscallNumbersFor arch).sendmsg
                · simp only [hSm, ↓reduceIte]
                  cases ((inp.args.a2.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) <;> rfl
                · simp only [hSm, Bool.false_eq_true, ↓reduceIte]
                  by_cases hSmm : inp.nr == (syscallNumbersFor arch).sendmmsg
                  · simp only [hSmm, ↓reduceIte]
                    cases ((inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) <;> rfl
                  · simp only [hSmm, Bool.false_eq_true, ↓reduceIte]
                    have hSame := classifyDeniedSyscallNr_isSome_iff (syscallNumbersFor arch) inp.nr
                    cases hCls : classifyDeniedSyscallNr (syscallNumbersFor arch) inp.nr with
                    | none =>
                      have hNot : (denySyscallNumbers (syscallNumbersFor arch)).contains inp.nr = false := by
                        rw [← hSame, hCls]; rfl
                      rw [hNot]; rfl
                    | some op =>
                      have hMem : (denySyscallNumbers (syscallNumbersFor arch)).contains inp.nr = true := by
                        rw [← hSame, hCls]; rfl
                      rw [hMem]
                      cases op <;> rfl

end LeanSwe.ProcessSandbox.Seccomp.Proofs
