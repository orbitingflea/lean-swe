import Core.Obeys
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Impl
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Seccomp.SpecTests
import LeanSwe.ProcessSandbox.Seccomp.Proofs.EvalModel

namespace LeanSwe.ProcessSandbox.Seccomp.Proofs

open Core
open Core.NondetTest
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Seccomp

private theorem byteArray_ext_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      cases da with
      | mk la =>
        cases db with
        | mk lb =>
          simp at h
          subst h
          rfl

private theorem encodeSockFilterList_eq (insn : SockFilter) :
    Seccomp.Impl.encodeSockFilterList insn = encodeSockFilterBytes insn := rfl

private theorem encodeSeccompBpf_eq_model (prog : Array SockFilter) :
    Seccomp.Impl.encodeSeccompBpf prog = encodeSeccompBpfModel prog := by
  apply byteArray_ext_toList
  unfold Seccomp.Impl.encodeSeccompBpf encodeSeccompBpfModel
  change prog.toList.flatMap Seccomp.Impl.encodeSockFilterList = prog.toList.flatMap encodeSockFilterBytes
  rw [show Seccomp.Impl.encodeSockFilterList = encodeSockFilterBytes from funext encodeSockFilterList_eq]

private theorem flatMap_encodeSockFilter_length (xs : List SockFilter) :
    (xs.flatMap encodeSockFilterBytes).length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hlen : (encodeSockFilterBytes x).length = 8 := rfl
    rw [List.flatMap_cons, List.length_append, hlen, ih, List.length_cons]
    omega

private theorem encodeSeccompBpfModel_size (prog : Array SockFilter) :
    (encodeSeccompBpfModel prog).size = 8 * prog.size := by
  unfold encodeSeccompBpfModel
  change (prog.toList.flatMap encodeSockFilterBytes).toArray.size = 8 * prog.size
  rw [List.size_toArray, flatMap_encodeSockFilter_length, Array.length_toList]

private theorem flatMap_encodeSockFilter_get (xs : List SockFilter) (idx j : Nat)
    (hidx : idx < xs.length) (hj : j < 8) :
    (xs.flatMap encodeSockFilterBytes)[8 * idx + j]'(by rw [flatMap_encodeSockFilter_length]; omega) =
      (encodeSockFilterBytes xs[idx])[j]'(by simp [encodeSockFilterBytes]; exact hj) := by
  induction xs generalizing idx with
  | nil => contradiction
  | cons x rest ih =>
    cases idx with
    | zero =>
      have hlen : (encodeSockFilterBytes x).length = 8 := rfl
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem_append_left (by omega)
    | succ i =>
      have hlen : (encodeSockFilterBytes x).length = 8 := rfl
      have hlt : i < rest.length := by simp at hidx; exact hidx
      have hge : (encodeSockFilterBytes x).length ≤ 8 * (i + 1) + j := by omega
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem_append_right hge]
      have hsub : 8 * (i + 1) + j - (encodeSockFilterBytes x).length = 8 * i + j := by omega
      simp only [hsub]
      exact ih i hlt

private theorem encodeSeccompBpfModel_getElem (prog : Array SockFilter) (idx j : Nat)
    (hidx : idx < prog.size) (hj : j < 8) :
    (encodeSeccompBpfModel prog)[8 * idx + j]! =
      (encodeSockFilterBytes prog[idx])[j]'(by simp [encodeSockFilterBytes]; exact hj) := by
  have hsz := encodeSeccompBpfModel_size prog
  have hlt : 8 * idx + j < (encodeSeccompBpfModel prog).size := by rw [hsz]; omega
  rw [getElem!_pos (encodeSeccompBpfModel prog) (8 * idx + j) hlt]
  change (prog.toList.flatMap encodeSockFilterBytes).toArray[8 * idx + j]'(by
    rw [List.size_toArray, flatMap_encodeSockFilter_length, Array.length_toList]; omega) = _
  rw [List.getElem_toArray]
  have hget := flatMap_encodeSockFilter_get prog.toList idx j (by simpa using hidx) hj
  simpa [Array.getElem_toList] using hget

/-- Proof of `test_seccomp_compileAndEncode_validProgAndLittleEndianWire` for `defaultApi`. -/
theorem proof_seccomp_compileAndEncode_validProgAndLittleEndianWire :
    AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire defaultApi) := by
  dsimp only [test_seccomp_compileAndEncode_validProgAndLittleEndianWire, Bind.bind,
    defaultApi]
  intro arch inp
  dsimp only [assert]
  constructor
  · cases arch
    · exact valid_x86_64
    · exact valid_aarch64
  · rw [evalBpf_compileSeccompBpf_eq_model]
    have hV := seccompModelVerdict_cases arch inp
    constructor
    · rcases hV with h | h | h
      · exact Or.inl (congrArg some h)
      · exact Or.inr (Or.inl (congrArg some h))
      · exact Or.inr (Or.inr (congrArg some h))
    · intro rawProg
      rw [encodeSeccompBpf_eq_model]
      refine ⟨encodeSeccompBpfModel_size rawProg, rfl, ?_⟩
      intro idx hidx
      refine ⟨?_, trivial⟩
      have hget : rawProg[idx]! = rawProg[idx]'hidx := getElem!_pos rawProg idx hidx
      rw [hget]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 0 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 1 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 2 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 3 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 4 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 5 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 6 hidx (by decide)
      · simpa [encodeSockFilterBytes] using encodeSeccompBpfModel_getElem rawProg idx 7 hidx (by decide)

/-- Non-vacuity `CanReach` witness for `test_seccomp_compileAndEncode_validProgAndLittleEndianWire`. -/
theorem reach_seccomp_compileAndEncode_validProgAndLittleEndianWire :
    CanReach (test_seccomp_compileAndEncode_validProgAndLittleEndianWire defaultApi) :=
  ⟨.x86_64, {},
    (proof_seccomp_compileAndEncode_validProgAndLittleEndianWire .x86_64 {}).1,
    (proof_seccomp_compileAndEncode_validProgAndLittleEndianWire .x86_64 {}).2.1,
    #[bpfStmt BPF_RET_K SECCOMP_RET_ALLOW],
    ((proof_seccomp_compileAndEncode_validProgAndLittleEndianWire .x86_64 {}).2.2 #[bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]).1,
    ((proof_seccomp_compileAndEncode_validProgAndLittleEndianWire .x86_64 {}).2.2 #[bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]).2.1,
    0, by decide,
    ((proof_seccomp_compileAndEncode_validProgAndLittleEndianWire .x86_64 {}).2.2 #[bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]).2.2 0 (by decide)⟩

/-- Proof of `test_seccomp_evalBpf_matchesStepGuestSyscallModel` for `defaultApi`. -/
theorem proof_seccomp_evalBpf_matchesStepGuestSyscallModel :
    AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel defaultApi) := by
  dsimp only [test_seccomp_evalBpf_matchesStepGuestSyscallModel, Bind.bind,
    defaultApi]
  intro arch plan st inp hValid
  have hAllowPair : plan.allowAnonUnixSocketpair = true := by
    simp only [isValidCompiledPlan, Bool.and_eq_true, and_assoc] at hValid
    exact hValid.2.2.2.2.2.2.2.1
  rw [evalBpf_compileSeccompBpf_eq_model]
  unfold decodeSeccompSyscall seccompModelVerdict
  by_cases hArch : inp.arch != auditArchOf arch
  · simp [assert, hArch, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
  · simp only [hArch, Bool.false_eq_true, ↓reduceIte]
    by_cases hX32 : (arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)) = true
    · have hA : (arch == .x86_64) = true := (Bool.and_eq_true _ _).mp hX32 |>.1
      have hN : inp.nr ≥ X32_SYSCALL_BIT := of_decide_eq_true ((Bool.and_eq_true _ _).mp hX32 |>.2)
      simp [assert, hA, hN, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
    · have hX32' : (arch == .x86_64 && decide (inp.nr ≥ X32_SYSCALL_BIT)) = false := Bool.eq_false_iff.mpr hX32
      simp only [hX32', Bool.false_eq_true, ↓reduceIte]
      by_cases hC3 : inp.nr == (syscallNumbersFor arch).clone3
      · simp [assert, hC3, SECCOMP_RET_ERRNO_ENOSYS, stepGuestSyscall]
      · simp only [hC3, Bool.false_eq_true, ↓reduceIte]
        by_cases hCl : inp.nr == (syscallNumbersFor arch).clone
        · simp only [hCl, ↓reduceIte, stepGuestSyscall]
          by_cases hFlg : ((inp.args.a0.toUInt32 &&& CLONE_NEW_NS_MASK) != 0) = true
          · simp [assert, hFlg, SECCOMP_RET_ERRNO_EPERM]
          · simp only [hFlg, Bool.false_eq_true, ↓reduceIte, SECCOMP_RET_ALLOW,
              beq_iff_eq, Option.some.injEq]
            simp [assert]
            split
            · simp
            · split
              · split <;> simp
              · simp
        · simp only [hCl, Bool.false_eq_true, ↓reduceIte]
          by_cases hSo : inp.nr == (syscallNumbersFor arch).socket
          · simp only [hSo, ↓reduceIte]
            by_cases hU : inp.args.a0.toUInt32 == LINUX_AF_UNIX
            · simp [assert, hU, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
            · by_cases hS : inp.args.a0.toUInt32 == LINUX_AF_SMC
              · simp [assert, hU, hS, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
              · simp [assert, hU, hS, SECCOMP_RET_ALLOW]
          · simp only [hSo, Bool.false_eq_true, ↓reduceIte]
            by_cases hSp : inp.nr == (syscallNumbersFor arch).socketpair
            · simp only [hSp, ↓reduceIte]
              by_cases hU : inp.args.a0.toUInt32 == LINUX_AF_UNIX
              · have hNotNe : (inp.args.a0.toUInt32 != LINUX_AF_UNIX) = false := by
                  simp [bne, beq_iff_eq.mp hU]
                by_cases hPr : inp.args.a2.toUInt32 == 0
                · have hNotPr : (inp.args.a2.toUInt32 != 0) = false := by
                    simp [bne, beq_iff_eq.mp hPr]
                  by_cases hStr : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_STREAM
                  · simp [assert, hU, hNotNe, hPr, hNotPr, hStr, hAllowPair, SECCOMP_RET_ALLOW, stepGuestSyscall]
                  · by_cases hSeq : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_SEQPACKET
                    · simp [assert, hU, hNotNe, hPr, hNotPr, hStr, hSeq, hAllowPair, SECCOMP_RET_ALLOW, stepGuestSyscall]
                    · simp [assert, hU, hNotNe, hPr, hNotPr, hStr, hSeq, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
                · have hNotPr : (inp.args.a2.toUInt32 != 0) = true := by
                    rw [bne_iff_ne]; exact fun h => hPr (beq_iff_eq.mpr h)
                  simp [assert, hU, hNotNe, hPr, hNotPr, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
              · have hNe : (inp.args.a0.toUInt32 != LINUX_AF_UNIX) = true := by
                  rw [bne_iff_ne]; exact fun h => hU (beq_iff_eq.mpr h)
                simp [assert, hU, hNe, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
            · simp only [hSp, Bool.false_eq_true, ↓reduceIte]
              by_cases hSto : inp.nr == (syscallNumbersFor arch).sendto
              · simp only [hSto, ↓reduceIte]
                by_cases hF : ((inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) = true
                · simp [assert, hF, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
                · simp [assert, hF, SECCOMP_RET_ALLOW]
              · simp only [hSto, Bool.false_eq_true, ↓reduceIte]
                by_cases hSm : inp.nr == (syscallNumbersFor arch).sendmsg
                · simp only [hSm, ↓reduceIte]
                  by_cases hF : ((inp.args.a2.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) = true
                  · simp [assert, hF, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
                  · simp [assert, hF, SECCOMP_RET_ALLOW]
                · simp only [hSm, Bool.false_eq_true, ↓reduceIte]
                  by_cases hSmm : inp.nr == (syscallNumbersFor arch).sendmmsg
                  · simp only [hSmm, ↓reduceIte]
                    by_cases hF : ((inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0) = true
                    · simp [assert, hF, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]
                    · simp [assert, hF, SECCOMP_RET_ALLOW]
                  · simp only [hSmm, Bool.false_eq_true, ↓reduceIte]
                    have hSame := classifyDeniedSyscallNr_isSome_iff (syscallNumbersFor arch) inp.nr
                    cases hCls : classifyDeniedSyscallNr (syscallNumbersFor arch) inp.nr with
                    | none =>
                      have hNot : (denySyscallNumbers (syscallNumbersFor arch)).contains inp.nr = false := by
                        rw [← hSame, hCls]; rfl
                      simp only [hNot, Bool.false_eq_true, ↓reduceIte]
                      simp [assert, SECCOMP_RET_ALLOW]
                    | some op =>
                      have hMem : (denySyscallNumbers (syscallNumbersFor arch)).contains inp.nr = true := by
                        rw [← hSame, hCls]; rfl
                      simp only [hMem, ↓reduceIte]
                      simp [assert, SECCOMP_RET_ERRNO_EPERM, stepGuestSyscall]

/-- Non-vacuity `CanReach` witness for `test_seccomp_evalBpf_matchesStepGuestSyscallModel`. -/
theorem reach_seccomp_evalBpf_matchesStepGuestSyscallModel :
    CanReach (test_seccomp_evalBpf_matchesStepGuestSyscallModel defaultApi) :=
  ⟨.x86_64, { program := "/bin/true" }, {}, {}, rfl,
    proof_seccomp_evalBpf_matchesStepGuestSyscallModel .x86_64 { program := "/bin/true" } {} {} rfl⟩

/-- Proof of `test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit` for `defaultApi`. -/
theorem proof_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit :
    AllPass (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit defaultApi) := by
  dsimp only [test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit, Bind.bind,
    defaultApi]
  intro inpBadX hBadX
  dsimp only [assert]
  refine ⟨?_, ?_⟩
  · rw [evalBpf_compileSeccompBpf_eq_model]
    have hNe : (inpBadX.arch != auditArchOf .x86_64) = true := by
      simp [auditArchOf, AUDIT_ARCH_X86_64, hBadX]
    simp [seccompModelVerdict, hNe, SECCOMP_RET_ERRNO_EPERM]
  · intro inpBadA hBadA
    refine ⟨?_, ?_⟩
    · rw [evalBpf_compileSeccompBpf_eq_model]
      have hNe : (inpBadA.arch != auditArchOf .aarch64) = true := by
        simp [auditArchOf, AUDIT_ARCH_AARCH64, hBadA]
      simp [seccompModelVerdict, hNe, SECCOMP_RET_ERRNO_EPERM]
    · intro inpX32 hX32
      rw [evalBpf_compileSeccompBpf_eq_model]
      have hArch : (inpX32.arch != auditArchOf .x86_64) = false := by
        simp [auditArchOf, AUDIT_ARCH_X86_64, hX32.1]
      have hGe : decide (inpX32.nr ≥ X32_SYSCALL_BIT) = true := decide_eq_true hX32.2
      have hx : (SeccompArch.x86_64 == .x86_64) = true := rfl
      simp [seccompModelVerdict, hArch, hGe, hx, SECCOMP_RET_ERRNO_EPERM]

/-- Non-vacuity `CanReach` witness for `test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit`. -/
theorem reach_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit :
    CanReach (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit defaultApi) :=
  ⟨{ arch := 0 }, by decide,
    (proof_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit { arch := 0 } (by decide)).1,
    { arch := 0 }, by decide,
    ((proof_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit { arch := 0 } (by decide)).2 { arch := 0 } (by decide)).1,
    { arch := 0xc000003e, nr := 0x40000000 }, ⟨rfl, by decide⟩,
    ((proof_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit { arch := 0 } (by decide)).2 { arch := 0 } (by decide)).2 { arch := 0xc000003e, nr := 0x40000000 } ⟨rfl, by decide⟩⟩

/-- Proof of `test_seccomp_rawClone3AndClone_enosysAndNamespaceMask` for `defaultApi`. -/
theorem proof_seccomp_rawClone3AndClone_enosysAndNamespaceMask :
    AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask defaultApi) := by
  dsimp only [test_seccomp_rawClone3AndClone_enosysAndNamespaceMask, Bind.bind,
    defaultApi]
  intro inp
  dsimp only [assert]
  simp only [evalBpf_compileSeccompBpf_eq_model]
  have hx : (SeccompArch.x86_64 == .x86_64) = true := rfl
  have ha : (SeccompArch.aarch64 == .x86_64) = false := rfl
  have hx435 : decide ((435 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have hx56 : decide ((56 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have h1 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 435 } = 0x00050026 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx435, SECCOMP_RET_ERRNO_ENOSYS]
  have h2 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 435 } = 0x00050026 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, SECCOMP_RET_ERRNO_ENOSYS]
  have h3 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 56 } =
      if (inp.args.a0.toUInt32 &&& 0x7e020000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx56, CLONE_NEW_NS_MASK, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h4 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 220 } =
      if (inp.args.a0.toUInt32 &&& 0x7e020000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, CLONE_NEW_NS_MASK, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  exact ⟨congrArg some h1, congrArg some h2, congrArg some h3, congrArg some h4, trivial⟩

/-- Proof of `test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair` for `defaultApi`. -/
theorem proof_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair :
    AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair defaultApi) := by
  dsimp only [test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair, Bind.bind,
    defaultApi]
  intro inp
  dsimp only [assert]
  simp only [evalBpf_compileSeccompBpf_eq_model]
  have hx : (SeccompArch.x86_64 == .x86_64) = true := rfl
  have ha : (SeccompArch.aarch64 == .x86_64) = false := rfl
  have hx41 : decide ((41 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have hx53 : decide ((53 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have h1 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 41 } =
      if inp.args.a0.toUInt32 == 1 || inp.args.a0.toUInt32 == 43 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx41, LINUX_AF_UNIX, LINUX_AF_SMC, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h2 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 198 } =
      if inp.args.a0.toUInt32 == 1 || inp.args.a0.toUInt32 == 43 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, LINUX_AF_UNIX, LINUX_AF_SMC, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h3 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 53 } =
      if inp.args.a0.toUInt32 == 1 && inp.args.a2.toUInt32 == 0 &&
          ((inp.args.a1.toUInt32 &&& 0xfff7f7ff) == 1 || (inp.args.a1.toUInt32 &&& 0xfff7f7ff) == 5) then
        0x7fff0000
      else
        0x00050001 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx53, LINUX_AF_UNIX, LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS, LINUX_SOCK_STREAM, LINUX_SOCK_SEQPACKET,
      SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h4 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 199 } =
      if inp.args.a0.toUInt32 == 1 && inp.args.a2.toUInt32 == 0 &&
          ((inp.args.a1.toUInt32 &&& 0xfff7f7ff) == 1 || (inp.args.a1.toUInt32 &&& 0xfff7f7ff) == 5) then
        0x7fff0000
      else
        0x00050001 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, LINUX_AF_UNIX, LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS, LINUX_SOCK_STREAM, LINUX_SOCK_SEQPACKET,
      SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  exact ⟨congrArg some h1, congrArg some h2, congrArg some h3, congrArg some h4, trivial⟩

/-- Proof of `test_seccomp_rawSendFastopen_exactArgIndices` for `defaultApi`. -/
theorem proof_seccomp_rawSendFastopen_exactArgIndices :
    AllPass (test_seccomp_rawSendFastopen_exactArgIndices defaultApi) := by
  dsimp only [test_seccomp_rawSendFastopen_exactArgIndices, Bind.bind,
    defaultApi]
  intro inp
  dsimp only [assert]
  simp only [evalBpf_compileSeccompBpf_eq_model]
  have hx : (SeccompArch.x86_64 == .x86_64) = true := rfl
  have ha : (SeccompArch.aarch64 == .x86_64) = false := rfl
  have hx44 : decide ((44 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have hx46 : decide ((46 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have hx307 : decide ((307 : UInt32) ≥ X32_SYSCALL_BIT) = false := by decide
  have h1 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 44 } =
      if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx44, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h2 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 206 } =
      if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h3 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 46 } =
      if (inp.args.a2.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx46, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h4 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 211 } =
      if (inp.args.a2.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h5 : seccompModelVerdict .x86_64 { inp with arch := 0xc000003e, nr := 307 } =
      if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_X86_64, syscallNumbersFor, x86_64SyscallNumbers,
      hx, hx307, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  have h6 : seccompModelVerdict .aarch64 { inp with arch := 0xc00000b7, nr := 269 } =
      if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000 := by
    simp [seccompModelVerdict, auditArchOf, AUDIT_ARCH_AARCH64, syscallNumbersFor, aarch64SyscallNumbers,
      ha, LINUX_MSG_FASTOPEN, SECCOMP_RET_ERRNO_EPERM, SECCOMP_RET_ALLOW]
  exact ⟨congrArg some h1, congrArg some h2, congrArg some h3, congrArg some h4, congrArg some h5, congrArg some h6, trivial⟩

/-- Proof of `test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls` for `defaultApi`. -/
theorem proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls :
    AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls defaultApi) := by
  dsimp only [test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls, Bind.bind,
    defaultApi]
  dsimp only [assert]
  refine ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, ?_⟩
  intro inp
  have hXCheck : (denySyscallNumbers x86_64SyscallNumbers).all (fun nr =>
      (denySyscallNumbers x86_64SyscallNumbers).contains nr &&
      !(decide (nr ≥ X32_SYSCALL_BIT)) &&
      !([435, 56, 41, 53, 44, 46, 307] : List UInt32).contains nr) = true := by
    decide
  have hACheck : (denySyscallNumbers aarch64SyscallNumbers).all (fun nr =>
      (denySyscallNumbers aarch64SyscallNumbers).contains nr &&
      !([435, 220, 198, 199, 206, 211, 269] : List UInt32).contains nr) = true := by
    decide
  have hEqX : denySyscallNumbers x86_64SyscallNumbers =
      [169, 246, 320, 165, 166, 155, 167, 168, 432, 430, 433, 429, 428, 442, 175, 313, 176, 163, 164, 227,
        305, 159, 321, 425, 426, 427, 250, 248, 249, 298, 323, 272, 308] := rfl
  have hEqA : denySyscallNumbers aarch64SyscallNumbers =
      [142, 104, 294, 40, 39, 41, 224, 225, 432, 430, 433, 429, 428, 442, 105, 273, 106, 89, 170, 112, 266,
        171, 280, 425, 426, 427, 219, 217, 218, 241, 282, 97, 268] := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [evalBpf_compileSeccompBpf_eq_model, List.all_eq_true]
    intro nr hMem
    have hP := List.all_eq_true.mp hXCheck nr hMem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hP
    rw [seccompModelVerdict_x86_deny_mem nr inp hP.1.1 hP.1.2 hP.2]
    rfl
  · simp only [evalBpf_compileSeccompBpf_eq_model, List.all_eq_true]
    intro nr hMem
    have hP := List.all_eq_true.mp hACheck nr hMem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hP
    rw [seccompModelVerdict_aarch64_deny_mem nr inp hP.1 hP.2]
    rfl
  · intro inpAllowX hX
    have hNotX : ([435, 56, 41, 53, 44, 46, 307] ++ denySyscallNumbers x86_64SyscallNumbers).contains inpAllowX.nr = false := by
      rw [hEqX]
      simpa only [Bool.not_eq_true'] using hX.2.2
    refine ⟨?_, ?_⟩
    · rw [evalBpf_compileSeccompBpf_eq_model,
        seccompModelVerdict_x86_allow_of_not_mem inpAllowX hX.1 hX.2.1 hNotX]
      rfl
    · intro inpAllowA hA
      have hNotA : ([435, 220, 198, 199, 206, 211, 269] ++ denySyscallNumbers aarch64SyscallNumbers).contains inpAllowA.nr = false := by
        rw [hEqA]
        simpa only [Bool.not_eq_true'] using hA.2
      rw [evalBpf_compileSeccompBpf_eq_model,
        seccompModelVerdict_aarch64_allow_of_not_mem inpAllowA hA.1 hNotA]
      exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls`. -/
theorem reach_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls :
    CanReach (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls defaultApi) :=
  ⟨proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.1,
    proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.2.1,
    {},
    (proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.2.2 {}).1,
    (proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.2.2 {}).2.1,
    { arch := 0xc000003e, nr := 0 }, ⟨rfl, by decide, by decide⟩,
    ((proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.2.2 {}).2.2
      { arch := 0xc000003e, nr := 0 } ⟨rfl, by decide, by decide⟩).1,
    { arch := 0xc00000b7, nr := 0 }, ⟨rfl, by decide⟩,
    ((proof_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls.2.2 {}).2.2
      { arch := 0xc000003e, nr := 0 } ⟨rfl, by decide, by decide⟩).2
      { arch := 0xc00000b7, nr := 0 } ⟨rfl, by decide⟩⟩

/-- Compiled seccomp BPF programs pass `isValidLinuxSeccompProg` for all supported architectures. -/
theorem compileSeccompBpf_valid (arch : SeccompArch) :
    isValidLinuxSeccompProg (Seccomp.compileSeccompBpf arch) = true := by
  dsimp only [Seccomp.compileSeccompBpf, Seccomp.defaultApi]
  cases arch
  · exact valid_x86_64
  · exact valid_aarch64

/-- `Seccomp.encodeSeccompBpf` matches the specification `encodeSeccompBpfModel` on all inputs. -/
theorem encodeSeccompBpf_eq_model_pub (prog : Array SockFilter) :
    Seccomp.encodeSeccompBpf prog = encodeSeccompBpfModel prog := by
  dsimp only [Seccomp.encodeSeccompBpf, Seccomp.defaultApi]
  exact encodeSeccompBpf_eq_model prog

/-- Compiled filters allow syscall `0` under the matching host `AUDIT_ARCH_*`. -/
theorem eval_compiled_nr0_allow (arch : SeccompArch) :
    evalBpf (Seccomp.compileSeccompBpf arch) { arch := auditArchOf arch, nr := 0 } =
      some 0x7fff0000 := by
  dsimp only [Seccomp.compileSeccompBpf, Seccomp.defaultApi]
  rw [evalBpf_compileSeccompBpf_eq_model]
  cases arch <;> rfl

/-- Compiled filters fail closed with `SECCOMP_RET_ERRNO 1` (`EPERM`) when `arch = 0`. -/
theorem eval_compiled_bad_arch_eperm (arch : SeccompArch) :
    evalBpf (Seccomp.compileSeccompBpf arch) { arch := 0, nr := 0 } =
      some 0x00050001 := by
  dsimp only [Seccomp.compileSeccompBpf, Seccomp.defaultApi]
  rw [evalBpf_compileSeccompBpf_eq_model]
  cases arch <;> rfl

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.ProcessSandbox.Seccomp` against `Model`. -/
theorem obeys_model :
    Core.ObeysPure Seccomp.compileSeccompBpf allowedCompileSeccompBpf ∧
    Core.ObeysPureEq Seccomp.encodeSeccompBpf encodeSeccompBpfModel :=
  ⟨fun arch => ⟨compileSeccompBpf_valid arch, fun inp => by
      dsimp only [Seccomp.compileSeccompBpf, Seccomp.defaultApi]
      rw [evalBpf_compileSeccompBpf_eq_model]
      exact congrArg some (seccompModelVerdict_eq_decoded arch inp)⟩,
   encodeSeccompBpf_eq_model_pub⟩

end LeanSwe.ProcessSandbox.Seccomp.Proofs
