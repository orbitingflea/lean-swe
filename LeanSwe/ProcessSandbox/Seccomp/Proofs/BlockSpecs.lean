import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Impl

namespace LeanSwe.ProcessSandbox.Seccomp.Proofs

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Seccomp

/-- Compiled `x86_64` seccomp filter satisfies `isValidLinuxSeccompProg`. -/
theorem valid_x86_64 :
    isValidLinuxSeccompProg (Seccomp.Impl.compileSeccompBpf .x86_64) = true := by
  decide

/-- Compiled `aarch64` seccomp filter satisfies `isValidLinuxSeccompProg`. -/
theorem valid_aarch64 :
    isValidLinuxSeccompProg (Seccomp.Impl.compileSeccompBpf .aarch64) = true := by
  decide

private theorem readSeccompDataWord_arch (inp : SeccompData) :
    readSeccompDataWord inp SECCOMP_OFFSET_ARCH = some inp.arch := by
  simp [readSeccompDataWord, SECCOMP_OFFSET_ARCH]

private theorem readSeccompDataWord_nr (inp : SeccompData) :
    readSeccompDataWord inp SECCOMP_OFFSET_NR = some inp.nr := by
  simp [readSeccompDataWord, SECCOMP_OFFSET_NR]

/-- Reading low 32-bit word of syscall argument `0` from `SeccompData` yields `inp.args.a0.toUInt32`. -/
theorem readSeccompDataWord_arg0 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 0) = some inp.args.a0.toUInt32 := by
  have h : seccompArgLowOffset 0 = 16 := by decide
  simp [readSeccompDataWord, h]

private theorem readSeccompDataWord_arg1 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 1) = some inp.args.a1.toUInt32 := by
  have h : seccompArgLowOffset 1 = 24 := by decide
  simp [readSeccompDataWord, h]

/-- Reading low 32-bit word of syscall argument `2` from `SeccompData` yields `inp.args.a2.toUInt32`. -/
theorem readSeccompDataWord_arg2 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 2) = some inp.args.a2.toUInt32 := by
  have h : seccompArgLowOffset 2 = 32 := by decide
  simp [readSeccompDataWord, h]

/-- Reading low 32-bit word of syscall argument `3` from `SeccompData` yields `inp.args.a3.toUInt32`. -/
theorem readSeccompDataWord_arg3 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 3) = some inp.args.a3.toUInt32 := by
  have h : seccompArgLowOffset 3 = 40 := by decide
  simp [readSeccompDataWord, h]

private theorem u8_0 : (0 : UInt8).toNat = 0 := by decide
private theorem u8_1 : (1 : UInt8).toNat = 1 := by decide
private theorem u8_2 : (2 : UInt8).toNat = 2 := by decide
private theorem u8_4 : (4 : UInt8).toNat = 4 := by decide
private theorem u8_5 : (5 : UInt8).toNat = 5 := by decide
private theorem u8_6 : (6 : UInt8).toNat = 6 := by decide
private theorem u8_10 : (10 : UInt8).toNat = 10 := by decide

private theorem bpf_ld_step (inp : SeccompData) (fuel : Nat) (k : UInt32) (rest : List SockFilter)
    (acc w : UInt32) (hw : readSeccompDataWord inp k = some w) :
    evalBpfSteps inp (fuel + 1) (bpfStmt BPF_LD_W_ABS k :: rest) acc =
      evalBpfSteps inp fuel rest w := by
  simp [evalBpfSteps, bpfStmt, BPF_LD_W_ABS, hw]

private theorem bpf_and_step (inp : SeccompData) (fuel : Nat) (k : UInt32) (rest : List SockFilter)
    (acc : UInt32) :
    evalBpfSteps inp (fuel + 1) (bpfStmt BPF_ALU_AND_K k :: rest) acc =
      evalBpfSteps inp fuel rest (acc &&& k) := by
  simp [evalBpfSteps, bpfStmt, BPF_LD_W_ABS, BPF_ALU_AND_K]

private theorem bpf_jeq_step (inp : SeccompData) (fuel : Nat) (k : UInt32) (jt jf : UInt8)
    (rest : List SockFilter) (acc : UInt32) :
    evalBpfSteps inp (fuel + 1) (bpfJump BPF_JMP_JEQ_K k jt jf :: rest) acc =
      evalBpfSteps inp fuel (rest.drop (if acc == k then jt.toNat else jf.toNat)) acc := by
  simp [evalBpfSteps, bpfJump, BPF_LD_W_ABS, BPF_ALU_AND_K, BPF_JMP_JA, BPF_JMP_JEQ_K]

private theorem bpf_jge_step (inp : SeccompData) (fuel : Nat) (k : UInt32) (jt jf : UInt8)
    (rest : List SockFilter) (acc : UInt32) :
    evalBpfSteps inp (fuel + 1) (bpfJump BPF_JMP_JGE_K k jt jf :: rest) acc =
      evalBpfSteps inp fuel (rest.drop (if acc ≥ k then jt.toNat else jf.toNat)) acc := by
  simp [evalBpfSteps, bpfJump, BPF_LD_W_ABS, BPF_ALU_AND_K, BPF_JMP_JA, BPF_JMP_JEQ_K,
    BPF_JMP_JGT_K, BPF_JMP_JGE_K]

/-- Single-step symbolic evaluation of a `BPF_RET_K` return instruction. -/
theorem bpf_ret_step (inp : SeccompData) (fuel : Nat) (k : UInt32)
    (rest : List SockFilter) (acc : UInt32) :
    evalBpfSteps inp (fuel + 1) (bpfStmt BPF_RET_K k :: rest) acc = some k := by
  simp [evalBpfSteps, bpfStmt, BPF_LD_W_ABS, BPF_ALU_AND_K, BPF_JMP_JA, BPF_JMP_JEQ_K,
    BPF_JMP_JGT_K, BPF_JMP_JGE_K, BPF_JMP_JSET_K, BPF_RET_K]

/-- Symbolic specification of `Seccomp.Impl.archHeaderBlock`. -/
theorem archHeaderBlock_spec (arch : SeccompArch) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat)
    (hf : (Seccomp.Impl.archHeaderBlock arch ++ rest).length ≤ fuel) :
    if inp.arch != auditArchOf arch then
      evalBpfSteps inp fuel (Seccomp.Impl.archHeaderBlock arch ++ rest) 0 = some SECCOMP_RET_ERRNO_EPERM
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.archHeaderBlock arch ++ rest) 0 =
          evalBpfSteps inp f' rest inp.nr := by
  have hlen : (Seccomp.Impl.archHeaderBlock arch ++ rest).length = rest.length + 4 := by
    simp [Seccomp.Impl.archHeaderBlock]
  obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
  obtain ⟨f3, rfl⟩ : ∃ f3, f2 = f3 + 1 := ⟨f2 - 1, by omega⟩
  have hld : evalBpfSteps inp (f3 + 1 + 1 + 1) (Seccomp.Impl.archHeaderBlock arch ++ rest) 0 =
      evalBpfSteps inp (f3 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_LD_W_ABS SECCOMP_OFFSET_NR :: rest) inp.arch := by
    simpa [Seccomp.Impl.archHeaderBlock] using
      bpf_ld_step inp (f3 + 1 + 1) SECCOMP_OFFSET_ARCH _ 0 inp.arch (readSeccompDataWord_arch inp)
  by_cases hEq : inp.arch = auditArchOf arch
  · have hb : (inp.arch == auditArchOf arch) = true := beq_iff_eq.mpr hEq
    have hne : (inp.arch != auditArchOf arch) = false := by simp [hEq]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f3, by omega, ?_⟩
    rw [hld, bpf_jeq_step]
    simp only [hb, ↓reduceIte, u8_1]
    exact bpf_ld_step inp f3 SECCOMP_OFFSET_NR rest inp.arch inp.nr (readSeccompDataWord_nr inp)
  · have hb : (inp.arch == auditArchOf arch) = false := beq_false_of_ne hEq
    have hne : (inp.arch != auditArchOf arch) = true := by simp [hEq]
    simp only [hne, ↓reduceIte]
    rw [hld, bpf_jeq_step]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, u8_0]
    exact bpf_ret_step inp f3 SECCOMP_RET_ERRNO_EPERM _ inp.arch

/-- Symbolic specification of `Seccomp.Impl.x32GuardBlock`. -/
theorem x32GuardBlock_spec (arch : SeccompArch) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.x32GuardBlock arch ++ rest).length ≤ fuel) :
    if arch == .x86_64 && decide (acc ≥ X32_SYSCALL_BIT) then
      evalBpfSteps inp fuel (Seccomp.Impl.x32GuardBlock arch ++ rest) acc = some SECCOMP_RET_ERRNO_EPERM
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.x32GuardBlock arch ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  cases arch with
  | aarch64 =>
    simp [Seccomp.Impl.x32GuardBlock]
    exact ⟨fuel, hf, rfl⟩
  | x86_64 =>
    have hlen : (Seccomp.Impl.x32GuardBlock .x86_64 ++ rest).length = rest.length + 2 := by
      simp [Seccomp.Impl.x32GuardBlock]
    obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
    have hxx : (SeccompArch.x86_64 == .x86_64) = true := rfl
    by_cases hge : acc ≥ X32_SYSCALL_BIT
    · have hCond : (SeccompArch.x86_64 == .x86_64 && decide (acc ≥ X32_SYSCALL_BIT)) = true := by
        simp [hxx, hge]
      simp only [hCond, ↓reduceIte]
      change evalBpfSteps inp (f2 + 1 + 1)
          (bpfJump BPF_JMP_JGE_K X32_SYSCALL_BIT 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM :: rest) acc = _
      rw [bpf_jge_step]
      simp only [hge, ↓reduceIte, u8_0]
      exact bpf_ret_step inp f2 SECCOMP_RET_ERRNO_EPERM rest acc
    · have hCond : (SeccompArch.x86_64 == .x86_64 && decide (acc ≥ X32_SYSCALL_BIT)) = false := by
        simp [hxx, hge]
      simp only [hCond, Bool.false_eq_true, ↓reduceIte]
      refine ⟨f2 + 1, by omega, ?_⟩
      change evalBpfSteps inp (f2 + 1 + 1)
          (bpfJump BPF_JMP_JGE_K X32_SYSCALL_BIT 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM :: rest) acc = _
      rw [bpf_jge_step]
      simp [hge, u8_1]

/-- Symbolic specification of `Seccomp.Impl.clone3Block`. -/
theorem clone3Block_spec (nr : UInt32) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.clone3Block nr ++ rest).length ≤ fuel) :
    if acc == nr then
      evalBpfSteps inp fuel (Seccomp.Impl.clone3Block nr ++ rest) acc = some SECCOMP_RET_ERRNO_ENOSYS
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.clone3Block nr ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  have hlen : (Seccomp.Impl.clone3Block nr ++ rest).length = rest.length + 2 := by
    simp [Seccomp.Impl.clone3Block]
  obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
  by_cases heq : acc == nr
  · simp only [heq, ↓reduceIte]
    change evalBpfSteps inp (f2 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_ENOSYS :: rest) acc = _
    rw [bpf_jeq_step]
    simp only [heq, ↓reduceIte, u8_0]
    exact bpf_ret_step inp f2 SECCOMP_RET_ERRNO_ENOSYS rest acc
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f2 + 1, by omega, ?_⟩
    change evalBpfSteps inp (f2 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_ENOSYS :: rest) acc = _
    rw [bpf_jeq_step]
    simp [heq, u8_1]

/-- Symbolic specification of `Seccomp.Impl.guardMaskBlock`. -/
theorem guardMaskBlock_spec (nr argOff mask w : UInt32) (inp : SeccompData)
    (hw : readSeccompDataWord inp argOff = some w)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.guardMaskBlock nr argOff mask ++ rest).length ≤ fuel) :
    if acc == nr then
      evalBpfSteps inp fuel (Seccomp.Impl.guardMaskBlock nr argOff mask ++ rest) acc =
        some (if (w &&& mask) != 0 then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW)
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.guardMaskBlock nr argOff mask ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  have hlen : (Seccomp.Impl.guardMaskBlock nr argOff mask ++ rest).length = rest.length + 6 := by
    simp [Seccomp.Impl.guardMaskBlock]
  obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
  obtain ⟨f3, rfl⟩ : ∃ f3, f2 = f3 + 1 := ⟨f2 - 1, by omega⟩
  obtain ⟨f4, rfl⟩ : ∃ f4, f3 = f4 + 1 := ⟨f3 - 1, by omega⟩
  obtain ⟨f5, rfl⟩ : ∃ f5, f4 = f5 + 1 := ⟨f4 - 1, by omega⟩
  by_cases heq : acc == nr
  · simp only [heq, ↓reduceIte]
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 5 ::
         bpfStmt BPF_LD_W_ABS argOff ::
         bpfStmt BPF_ALU_AND_K mask ::
         bpfJump BPF_JMP_JEQ_K 0 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp only [heq, ↓reduceIte, u8_0]
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1)
        (bpfStmt BPF_LD_W_ABS argOff ::
         bpfStmt BPF_ALU_AND_K mask ::
         bpfJump BPF_JMP_JEQ_K 0 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_ld_step _ _ _ _ _ w hw, bpf_and_step, bpf_jeq_step]
    by_cases hz : (w &&& mask) = 0
    · have hb : ((w &&& mask) == 0) = true := beq_iff_eq.mpr hz
      have hnz : ((w &&& mask) != 0) = false := by simp [hz]
      simp only [hb, ↓reduceIte, u8_1, hnz, Bool.false_eq_true]
      exact bpf_ret_step inp f5 SECCOMP_RET_ALLOW rest (w &&& mask)
    · have hb : ((w &&& mask) == 0) = false := beq_false_of_ne hz
      have hnz : ((w &&& mask) != 0) = true := by simp [hz]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, u8_0, hnz]
      exact bpf_ret_step inp f5 SECCOMP_RET_ERRNO_EPERM _ (w &&& mask)
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f5 + 4, by omega, ?_⟩
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 5 ::
         bpfStmt BPF_LD_W_ABS argOff ::
         bpfStmt BPF_ALU_AND_K mask ::
         bpfJump BPF_JMP_JEQ_K 0 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp [heq, u8_5]

/-- Symbolic specification of `Seccomp.Impl.socketBlock`. -/
theorem socketBlock_spec (nr : UInt32) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.socketBlock nr ++ rest).length ≤ fuel) :
    if acc == nr then
      let dom := inp.args.a0.toUInt32
      evalBpfSteps inp fuel (Seccomp.Impl.socketBlock nr ++ rest) acc =
        some (if dom == LINUX_AF_UNIX || dom == LINUX_AF_SMC then SECCOMP_RET_ERRNO_EPERM else SECCOMP_RET_ALLOW)
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.socketBlock nr ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  have hlen : (Seccomp.Impl.socketBlock nr ++ rest).length = rest.length + 6 := by
    simp [Seccomp.Impl.socketBlock]
  obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
  obtain ⟨f3, rfl⟩ : ∃ f3, f2 = f3 + 1 := ⟨f2 - 1, by omega⟩
  obtain ⟨f4, rfl⟩ : ∃ f4, f3 = f4 + 1 := ⟨f3 - 1, by omega⟩
  obtain ⟨f5, rfl⟩ : ∃ f5, f4 = f5 + 1 := ⟨f4 - 1, by omega⟩
  by_cases heq : acc == nr
  · simp only [heq, ↓reduceIte]
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 5 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 1 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_SMC 0 1 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp only [heq, ↓reduceIte, u8_0]
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1)
        (bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 1 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_SMC 0 1 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_ld_step _ _ _ _ _ inp.args.a0.toUInt32 (readSeccompDataWord_arg0 inp)]
    rw [bpf_jeq_step]
    by_cases hUnix : inp.args.a0.toUInt32 == LINUX_AF_UNIX
    · simp only [hUnix, ↓reduceIte, u8_1, Bool.true_or]
      exact bpf_ret_step inp (f5 + 1) SECCOMP_RET_ERRNO_EPERM _ inp.args.a0.toUInt32
    · simp only [hUnix, Bool.false_eq_true, ↓reduceIte, u8_0, Bool.false_or]
      change evalBpfSteps inp (f5 + 1 + 1)
          (bpfJump BPF_JMP_JEQ_K LINUX_AF_SMC 0 1 ::
           bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
           bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) inp.args.a0.toUInt32 = _
      rw [bpf_jeq_step]
      by_cases hSmc : inp.args.a0.toUInt32 == LINUX_AF_SMC
      · simp only [hSmc, ↓reduceIte, u8_0]
        exact bpf_ret_step inp f5 SECCOMP_RET_ERRNO_EPERM _ inp.args.a0.toUInt32
      · simp only [hSmc, Bool.false_eq_true, ↓reduceIte, u8_1]
        exact bpf_ret_step inp f5 SECCOMP_RET_ALLOW rest inp.args.a0.toUInt32
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f5 + 4, by omega, ?_⟩
    change evalBpfSteps inp (f5 + 1 + 1 + 1 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 5 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 1 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_SMC 0 1 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp [heq, u8_5]

/-- Symbolic specification of `Seccomp.Impl.socketpairBlock`. -/
theorem socketpairBlock_spec (nr : UInt32) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.socketpairBlock nr ++ rest).length ≤ fuel) :
    if acc == nr then
      let dom := inp.args.a0.toUInt32
      let baseType := inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS
      let proto := inp.args.a2.toUInt32
      evalBpfSteps inp fuel (Seccomp.Impl.socketpairBlock nr ++ rest) acc =
        some (if dom == LINUX_AF_UNIX && proto == 0 && (baseType == LINUX_SOCK_STREAM || baseType == LINUX_SOCK_SEQPACKET) then
          SECCOMP_RET_ALLOW
        else
          SECCOMP_RET_ERRNO_EPERM)
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.socketpairBlock nr ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  have hlen : (Seccomp.Impl.socketpairBlock nr ++ rest).length = rest.length + 11 := by
    simp [Seccomp.Impl.socketpairBlock]
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 10 := ⟨fuel - 10, by omega⟩
  by_cases heq : acc == nr
  · simp only [heq, ↓reduceIte]
    change evalBpfSteps inp (f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 10 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 0 6 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 2) ::
         bpfJump BPF_JMP_JEQ_K 0 0 4 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1) ::
         bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp only [heq, ↓reduceIte, u8_0]
    change evalBpfSteps inp (f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 0 6 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 2) ::
         bpfJump BPF_JMP_JEQ_K 0 0 4 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1) ::
         bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_ld_step _ _ _ _ _ inp.args.a0.toUInt32 (readSeccompDataWord_arg0 inp)]
    rw [bpf_jeq_step]
    by_cases hDom : inp.args.a0.toUInt32 == LINUX_AF_UNIX
    · simp only [hDom, ↓reduceIte, u8_0, Bool.true_and]
      change evalBpfSteps inp (f + 1 + 1 + 1 + 1 + 1 + 1 + 1)
          (bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 2) ::
           bpfJump BPF_JMP_JEQ_K 0 0 4 ::
           bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1) ::
           bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS ::
           bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0 ::
           bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
           bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
           bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) inp.args.a0.toUInt32 = _
      rw [bpf_ld_step _ _ _ _ _ inp.args.a2.toUInt32 (readSeccompDataWord_arg2 inp)]
      rw [bpf_jeq_step]
      by_cases hProto : inp.args.a2.toUInt32 == 0
      · simp only [hProto, ↓reduceIte, u8_0, Bool.true_and]
        change evalBpfSteps inp (f + 1 + 1 + 1 + 1 + 1)
            (bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1) ::
             bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS ::
             bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0 ::
             bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
             bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
             bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) inp.args.a2.toUInt32 = _
        rw [bpf_ld_step _ _ _ _ _ inp.args.a1.toUInt32 (readSeccompDataWord_arg1 inp)]
        rw [bpf_and_step, bpf_jeq_step]
        by_cases hStr : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_STREAM
        · simp only [hStr, ↓reduceIte, u8_2, Bool.true_or]
          exact bpf_ret_step inp (f + 1) SECCOMP_RET_ALLOW rest _
        · simp only [hStr, Bool.false_eq_true, ↓reduceIte, u8_0, Bool.false_or]
          change evalBpfSteps inp (f + 1 + 1)
              (bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
               bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
               bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) _ = _
          rw [bpf_jeq_step]
          by_cases hSeq : (inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS) == LINUX_SOCK_SEQPACKET
          · simp only [hSeq, ↓reduceIte, u8_1]
            exact bpf_ret_step inp f SECCOMP_RET_ALLOW rest _
          · simp only [hSeq, Bool.false_eq_true, ↓reduceIte, u8_0]
            exact bpf_ret_step inp f SECCOMP_RET_ERRNO_EPERM _ _
      · simp only [hProto, Bool.false_eq_true, ↓reduceIte, u8_4, Bool.false_and]
        exact bpf_ret_step inp (f + 1 + 1 + 1 + 1) SECCOMP_RET_ERRNO_EPERM _ inp.args.a2.toUInt32
    · simp only [hDom, Bool.false_eq_true, ↓reduceIte, u8_6, Bool.false_and]
      exact bpf_ret_step inp (f + 1 + 1 + 1 + 1 + 1 + 1) SECCOMP_RET_ERRNO_EPERM _ inp.args.a0.toUInt32
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f + 9, by omega, ?_⟩
    change evalBpfSteps inp (f + 9 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 10 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0) ::
         bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 0 6 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 2) ::
         bpfJump BPF_JMP_JEQ_K 0 0 4 ::
         bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1) ::
         bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0 ::
         bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0 ::
         bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM ::
         bpfStmt BPF_RET_K SECCOMP_RET_ALLOW :: rest) acc = _
    rw [bpf_jeq_step]
    simp [heq, u8_10]

private theorem denyNrBlock_spec (nr : UInt32) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.denyNrBlock nr ++ rest).length ≤ fuel) :
    if acc == nr then
      evalBpfSteps inp fuel (Seccomp.Impl.denyNrBlock nr ++ rest) acc = some SECCOMP_RET_ERRNO_EPERM
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.denyNrBlock nr ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  have hlen : (Seccomp.Impl.denyNrBlock nr ++ rest).length = rest.length + 2 := by
    simp [Seccomp.Impl.denyNrBlock]
  obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 1 := ⟨f1 - 1, by omega⟩
  by_cases heq : acc == nr
  · simp only [heq, ↓reduceIte]
    change evalBpfSteps inp (f2 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM :: rest) acc = _
    rw [bpf_jeq_step]
    simp only [heq, ↓reduceIte, u8_0]
    exact bpf_ret_step inp f2 SECCOMP_RET_ERRNO_EPERM rest acc
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨f2 + 1, by omega, ?_⟩
    change evalBpfSteps inp (f2 + 1 + 1)
        (bpfJump BPF_JMP_JEQ_K nr 0 1 :: bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM :: rest) acc = _
    rw [bpf_jeq_step]
    simp [heq, u8_1]

/-- Symbolic specification of `Seccomp.Impl.denyListBlock` over a list of denied syscall numbers. -/
theorem denyListBlock_spec (nrs : List UInt32) (inp : SeccompData)
    (rest : List SockFilter) (fuel : Nat) (acc : UInt32)
    (hf : (Seccomp.Impl.denyListBlock nrs ++ rest).length ≤ fuel) :
    if nrs.contains acc then
      evalBpfSteps inp fuel (Seccomp.Impl.denyListBlock nrs ++ rest) acc = some SECCOMP_RET_ERRNO_EPERM
    else
      ∃ f', rest.length ≤ f' ∧
        evalBpfSteps inp fuel (Seccomp.Impl.denyListBlock nrs ++ rest) acc =
          evalBpfSteps inp f' rest acc := by
  induction nrs generalizing fuel with
  | nil =>
    simp [Seccomp.Impl.denyListBlock]
    exact ⟨fuel, hf, rfl⟩
  | cons hd tl ih =>
    have hcons : Seccomp.Impl.denyListBlock (hd :: tl) =
        Seccomp.Impl.denyNrBlock hd ++ Seccomp.Impl.denyListBlock tl := by
      simp [Seccomp.Impl.denyListBlock, List.flatMap_cons]
    rw [hcons, List.append_assoc] at hf ⊢
    have hhd := denyNrBlock_spec hd inp (Seccomp.Impl.denyListBlock tl ++ rest) fuel acc hf
    by_cases hEq : acc == hd
    · have hmem : (hd :: tl).contains acc = true := by
        rw [List.contains_cons, hEq]
        rfl
      simp only [hEq, ↓reduceIte] at hhd
      simp only [hmem, ↓reduceIte]
      exact hhd
    · have hEqF : (acc == hd) = false := Bool.eq_false_iff.mpr hEq
      have hmem : (hd :: tl).contains acc = tl.contains acc := by
        rw [List.contains_cons, hEqF]
        rfl
      simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hhd
      rcases hhd with ⟨f1, hf1, hstep1⟩
      have htl := ih f1 hf1
      rw [hmem]
      by_cases hInTl : tl.contains acc
      · simp only [hInTl, ↓reduceIte] at htl ⊢
        rw [hstep1, htl]
      · simp only [hInTl, Bool.false_eq_true, ↓reduceIte] at htl ⊢
        rcases htl with ⟨f2, hf2, hstep2⟩
        exact ⟨f2, hf2, hstep1.trans hstep2⟩

end LeanSwe.ProcessSandbox.Seccomp.Proofs
