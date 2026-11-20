import Core.Refines
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Impl
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Seccomp.SpecTests

namespace LeanSwe.ProcessSandbox.Seccomp.Proofs

open Core
open Core.NondetTest
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Seccomp

private theorem valid_x86_64 :
    isValidLinuxSeccompProg (Seccomp.Impl.compileSeccompBpf .x86_64) = true := by
  decide

private theorem valid_aarch64 :
    isValidLinuxSeccompProg (Seccomp.Impl.compileSeccompBpf .aarch64) = true := by
  decide

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

private theorem readSeccompDataWord_arch (inp : SeccompData) :
    readSeccompDataWord inp SECCOMP_OFFSET_ARCH = some inp.arch := by
  simp [readSeccompDataWord, SECCOMP_OFFSET_ARCH]

private theorem readSeccompDataWord_nr (inp : SeccompData) :
    readSeccompDataWord inp SECCOMP_OFFSET_NR = some inp.nr := by
  simp [readSeccompDataWord, SECCOMP_OFFSET_NR]

private theorem readSeccompDataWord_arg0 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 0) = some inp.args.a0.toUInt32 := by
  have h : seccompArgLowOffset 0 = 16 := by decide
  simp [readSeccompDataWord, h]

private theorem readSeccompDataWord_arg1 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 1) = some inp.args.a1.toUInt32 := by
  have h : seccompArgLowOffset 1 = 24 := by decide
  simp [readSeccompDataWord, h]

private theorem readSeccompDataWord_arg2 (inp : SeccompData) :
    readSeccompDataWord inp (seccompArgLowOffset 2) = some inp.args.a2.toUInt32 := by
  have h : seccompArgLowOffset 2 = 32 := by decide
  simp [readSeccompDataWord, h]

private theorem readSeccompDataWord_arg3 (inp : SeccompData) :
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

private theorem bpf_ret_step (inp : SeccompData) (fuel : Nat) (k : UInt32)
    (rest : List SockFilter) (acc : UInt32) :
    evalBpfSteps inp (fuel + 1) (bpfStmt BPF_RET_K k :: rest) acc = some k := by
  simp [evalBpfSteps, bpfStmt, BPF_LD_W_ABS, BPF_ALU_AND_K, BPF_JMP_JA, BPF_JMP_JEQ_K,
    BPF_JMP_JGT_K, BPF_JMP_JGE_K, BPF_JMP_JSET_K, BPF_RET_K]

private theorem archHeaderBlock_spec (arch : SeccompArch) (inp : SeccompData)
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

private theorem x32GuardBlock_spec (arch : SeccompArch) (inp : SeccompData)
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

private theorem clone3Block_spec (nr : UInt32) (inp : SeccompData)
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

private theorem guardMaskBlock_spec (nr argOff mask w : UInt32) (inp : SeccompData)
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

private theorem socketBlock_spec (nr : UInt32) (inp : SeccompData)
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

private theorem socketpairBlock_spec (nr : UInt32) (inp : SeccompData)
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

private theorem denyListBlock_spec (nrs : List UInt32) (inp : SeccompData)
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

private def seccompModelVerdict (arch : SeccompArch) (inp : SeccompData) : UInt32 :=
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

private theorem evalBpf_compileSeccompBpf_eq_model (arch : SeccompArch) (inp : SeccompData) :
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

private theorem classifyDeniedSyscallNr_isSome_iff (nrs : SyscallNumbers) (nr : UInt32) :
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

private theorem seccompModelVerdict_cases (arch : SeccompArch) (inp : SeccompData) :
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

private theorem seccompModelVerdict_x86_deny_mem (nr : UInt32) (inp : SeccompData)
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

private theorem seccompModelVerdict_aarch64_deny_mem (nr : UInt32) (inp : SeccompData)
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

private theorem seccompModelVerdict_x86_allow_of_not_mem (inp : SeccompData)
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

private theorem seccompModelVerdict_aarch64_allow_of_not_mem (inp : SeccompData)
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

private theorem seccompModelVerdict_eq_decoded (arch : SeccompArch) (inp : SeccompData) :
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

/-- Full public `Interface` refinement of `LeanSwe.ProcessSandbox.Seccomp` against `Model`. -/
theorem refines_model :
    Core.RefinesPure Seccomp.compileSeccompBpf allowedCompileSeccompBpf ∧
    Core.RefinesPureEq Seccomp.encodeSeccompBpf encodeSeccompBpfModel :=
  ⟨fun arch => ⟨compileSeccompBpf_valid arch, fun inp => by
      dsimp only [Seccomp.compileSeccompBpf, Seccomp.defaultApi]
      rw [evalBpf_compileSeccompBpf_eq_model]
      exact congrArg some (seccompModelVerdict_eq_decoded arch inp)⟩,
   encodeSeccompBpf_eq_model_pub⟩

end LeanSwe.ProcessSandbox.Seccomp.Proofs
