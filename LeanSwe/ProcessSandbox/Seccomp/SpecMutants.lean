import Core.NondetTest
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.ProcessSandbox.Seccomp`. -/

namespace LeanSwe.ProcessSandbox.Seccomp

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ProcessSandbox.Model

private def stubCompileSeccompBpf (arch : SeccompArch) : Array SockFilter :=
  #[ bpfStmt BPF_LD_W_ABS 4
   , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
   , bpfStmt BPF_RET_K 0x00050001
   , bpfStmt BPF_RET_K 0x7fff0000 ]

private def stubSeccompApi : SeccompApi :=
  { compileSeccompBpf := stubCompileSeccompBpf
    encodeSeccompBpf := encodeSeccompBpfModel }

private def encodeSeccompBigEndianMutant (prog : Array SockFilter) : ByteArray :=
  ByteArray.mk (prog.toList.flatMap fun insn =>
    let c := insn.code.toNat
    let k := insn.k.toNat
    [ UInt8.ofNat ((c / 256) % 256)
    , UInt8.ofNat (c % 256)
    , insn.jt
    , insn.jf
    , UInt8.ofNat ((k / 16777216) % 256)
    , UInt8.ofNat ((k / 65536) % 256)
    , UInt8.ofNat ((k / 256) % 256)
    , UInt8.ofNat (k % 256) ]).toArray

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => (List.replicate 161 (bpfStmt BPF_RET_K 0x7fff0000)).toArray
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have hValid := (h .x86_64 {}).1
  unfold isValidLinuxSeccompProg SECCOMP_MAX_INSNS at hValid
  have hSz : ((List.replicate 161 (bpfStmt BPF_RET_K 0x7fff0000)).toArray).size = 161 := by simp
  dsimp only [stubSeccompApi] at hValid
  rw [hSz] at hValid
  have hGt : decide (161 ≤ 160) = false := rfl
  have hPos : decide (0 < 161) = true := rfl
  rw [hPos, hGt] at hValid
  cases hValid

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_LD_W_ABS 20, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfJump BPF_JMP_JEQ_K 0 5 0, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt 0x0000 0, bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBpfModel }) := by
  intro h
  have h0 := h .x86_64 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000]
      encodeSeccompBpf := encodeSeccompBigEndianMutant }) := by
  intro h
  have h0 := h .x86_64 {}
  have hWire := h0.2.2 #[bpfStmt BPF_RET_K 0x7fff0000]
  have hIdx := hWire.2.2 0 (by decide)
  exact absurd hIdx.1.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000] }) := by
  intro h
  let validPlan := LeanSwe.ProcessSandbox.Model.compilePlan default {}
  have hv : isValidCompiledPlan validPlan = true := rfl
  have h0 := h .x86_64 validPlan {} { arch := 0xc000003e, nr := 169 } hv
  exact h0.1.2.1 rfl

example : ¬ Core.AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  let validPlan := LeanSwe.ProcessSandbox.Model.compilePlan default {}
  have hv : isValidCompiledPlan validPlan = true := rfl
  have h0 := h .x86_64 validPlan {} { arch := 0xc000003e, nr := 435 } hv
  cases h0.1

example : ¬ Core.AllPass (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x7fff0000] }) := by
  intro h
  have h0 := h { arch := 0x40000003, nr := 0 } (by decide)
  exact absurd h0.1 (by decide)

private def mutantX32JsetInsteadOfJgeBpf : SeccompArch → Array SockFilter
  | .x86_64 =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K 0xc000003e 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JSET_K 0x40000000 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000 ]
  | .aarch64 =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K 0xc00000b7 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    { stubSeccompApi with compileSeccompBpf := mutantX32JsetInsteadOfJgeBpf }) := by
  intro h
  have h1 := h { arch := 0x40000003 } (by decide)
  have h2 := h1.2 { arch := 0x40000028 } (by decide)
  have h3 := h2.2 { arch := 0xc000003e, nr := 0x80000000 } ⟨rfl, by decide⟩
  exact absurd h3.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  have h0 := h {}
  exact absurd h0.1 (by decide)

private def mutantCloneMask0x80CollisionBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfStmt BPF_ALU_AND_K 0x7e020080
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubSeccompApi with compileSeccompBpf := mutantCloneMask0x80CollisionBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x80 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantCloneOmitNewnsBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfStmt BPF_ALU_AND_K 0x7e000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubSeccompApi with compileSeccompBpf := mutantCloneOmitNewnsBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x00020000 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantCloneHighWordEndianBpf : SeccompArch → Array SockFilter
  | arch =>
    let cloneNr : UInt32 := match arch with | .x86_64 => 56 | .aarch64 => 220
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K cloneNr 0 5
     , bpfStmt BPF_LD_W_ABS 20
     , bpfStmt BPF_ALU_AND_K 0x7e020000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubSeccompApi with compileSeccompBpf := mutantCloneHighWordEndianBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x10000000 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSocketAllowSmcBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 4
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubSeccompApi with compileSeccompBpf := mutantSocketAllowSmcBpf }) := by
  intro h
  have h0 := h { args := { a0 := 43 } }
  exact absurd h0.1 (by decide)

private def mutantSocketpairUnmaskedCloexecBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    let pairNr : UInt32 := match arch with | .x86_64 => 53 | .aarch64 => 199
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 1 0
     , bpfJump BPF_JMP_JEQ_K 43 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K pairNr 0 9
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfJump BPF_JMP_JEQ_K 0 0 3
     , bpfStmt BPF_LD_W_ABS 24
     , bpfJump BPF_JMP_JEQ_K 1 2 0
     , bpfJump BPF_JMP_JEQ_K 5 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubSeccompApi with compileSeccompBpf := mutantSocketpairUnmaskedCloexecBpf }) := by
  intro h
  have h0 := h { args := { a0 := 1, a1 := 0x00080001, a2 := 0 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSocketpairIgnoreProtoBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    let pairNr : UInt32 := match arch with | .x86_64 => 53 | .aarch64 => 199
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 1 0
     , bpfJump BPF_JMP_JEQ_K 43 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K pairNr 0 8
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 4
     , bpfStmt BPF_LD_W_ABS 24
     , bpfStmt BPF_ALU_AND_K 0xfff7f7ff
     , bpfJump BPF_JMP_JEQ_K 1 2 0
     , bpfJump BPF_JMP_JEQ_K 5 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubSeccompApi with compileSeccompBpf := mutantSocketpairIgnoreProtoBpf }) := by
  intro h
  have h0 := h { args := { a0 := 1, a1 := 1, a2 := 6 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantSendtoWrongArg2Bpf : SeccompArch → Array SockFilter
  | arch =>
    let sendtoNr : UInt32 := match arch with | .x86_64 => 44 | .aarch64 => 206
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sendtoNr 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSendFastopen_exactArgIndices
    { stubSeccompApi with compileSeccompBpf := mutantSendtoWrongArg2Bpf }) := by
  intro h
  have h0 := h { args := { a2 := 0, a3 := 0x20000000 } }
  exact absurd h0.1 (by decide)

private def mutantSendmsgWrongArg3Bpf : SeccompArch → Array SockFilter
  | arch =>
    let sendtoNr : UInt32 := match arch with | .x86_64 => 44 | .aarch64 => 206
    let sendmsgNr : UInt32 := match arch with | .x86_64 => 46 | .aarch64 => 211
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sendtoNr 0 5
     , bpfStmt BPF_LD_W_ABS 40
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K sendmsgNr 0 5
     , bpfStmt BPF_LD_W_ABS 40
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSendFastopen_exactArgIndices
    { stubSeccompApi with compileSeccompBpf := mutantSendmsgWrongArg3Bpf }) := by
  intro h
  have h0 := h { args := { a2 := 0x20000000, a3 := 0 } }
  exact absurd h0.2.2.1 (by decide)

private def mutantOmitAcctBpf : SeccompArch → Array SockFilter
  | arch =>
    let acctNr : UInt32 := match arch with | .x86_64 => 163 | .aarch64 => 89
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K acctNr 0 1
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubSeccompApi with compileSeccompBpf := mutantOmitAcctBpf }) := by
  intro h
  have h0 := h.2.2 {}
  exact absurd h0.1 (by decide)

private def mutantOmitMountSetattrBpf : SeccompArch → Array SockFilter
  | _ =>
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 442 0 1
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubSeccompApi with compileSeccompBpf := mutantOmitMountSetattrBpf }) := by
  intro h
  have h0 := h.2.2 {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubSeccompApi with
      compileSeccompBpf := fun _ => #[bpfStmt BPF_RET_K 0x00050001] }) := by
  intro h
  have h0 := h.2.2 {}
  have hAllowX := h0.2.2 { arch := 0xc000003e, nr := 431 } ⟨rfl, by decide, by decide⟩
  exact absurd hAllowX.1 (by decide)

private def mutantAarch64UsesX86CloneNrBpf : SeccompArch → Array SockFilter
  | arch =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K 435 0 1
     , bpfStmt BPF_RET_K 0x00050026
     , bpfJump BPF_JMP_JEQ_K 56 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfStmt BPF_ALU_AND_K 0x7e020000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    { stubSeccompApi with compileSeccompBpf := mutantAarch64UsesX86CloneNrBpf }) := by
  intro h
  have h0 := h { args := { a0 := 0x00020000 } }
  exact absurd h0.2.2.2.1 (by decide)

private def mutantAarch64EmitsX32CheckBpf : SeccompArch → Array SockFilter
  | arch =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JGE_K 0x40000000 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_evalBpf_matchesStepGuestSyscallModel
    { stubSeccompApi with compileSeccompBpf := mutantAarch64EmitsX32CheckBpf }) := by
  intro h
  let validPlan := LeanSwe.ProcessSandbox.Model.compilePlan default {}
  have hv : isValidCompiledPlan validPlan = true := rfl
  have h0 := h .aarch64 validPlan {} { arch := 0xc00000b7, nr := 0x40000000 } hv
  exact absurd h0.1 (by decide)

private def mutantDenyBelow500AndX32OnAllArchsBpf : SeccompArch → Array SockFilter
  | arch =>
    #[ bpfStmt BPF_LD_W_ABS 4
     , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JGE_K 0x40000000 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfJump BPF_JMP_JGE_K 500 0 1
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x00050001 ]

example : ¬ Core.AllPass (test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    { stubSeccompApi with compileSeccompBpf := mutantDenyBelow500AndX32OnAllArchsBpf }) := by
  intro h
  have h0 := h.2.2 {}
  have hAllowX := h0.2.2 { arch := 0xc000003e, nr := 500 } ⟨rfl, by decide, by decide⟩
  have hAllowA := hAllowX.2 { arch := 0xc00000b7, nr := 0x40000000 } ⟨rfl, by decide⟩
  exact absurd hAllowA.1 (by decide)

private def mutantSendmmsgWrongArg2Bpf : SeccompArch → Array SockFilter
  | arch =>
    let sendtoNr : UInt32 := match arch with | .x86_64 => 44 | .aarch64 => 206
    let sendmsgNr : UInt32 := match arch with | .x86_64 => 46 | .aarch64 => 211
    let sendmmsgNr : UInt32 := match arch with | .x86_64 => 307 | .aarch64 => 269
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sendtoNr 0 5
     , bpfStmt BPF_LD_W_ABS 40
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K sendmsgNr 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K sendmmsgNr 0 5
     , bpfStmt BPF_LD_W_ABS 32
     , bpfStmt BPF_ALU_AND_K 0x20000000
     , bpfJump BPF_JMP_JEQ_K 0 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSendFastopen_exactArgIndices
    { stubSeccompApi with compileSeccompBpf := mutantSendmmsgWrongArg2Bpf }) := by
  intro h
  have h0 := h { args := { a2 := 0, a3 := 0x20000000 } }
  exact absurd h0.2.2.2.2.2.1 (by decide)

private def mutantSocketpairAllowDgramBpf : SeccompArch → Array SockFilter
  | arch =>
    let sockNr : UInt32 := match arch with | .x86_64 => 41 | .aarch64 => 198
    let pairNr : UInt32 := match arch with | .x86_64 => 53 | .aarch64 => 199
    #[ bpfStmt BPF_LD_W_ABS 0
     , bpfJump BPF_JMP_JEQ_K sockNr 0 5
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 1 0
     , bpfJump BPF_JMP_JEQ_K 43 0 1
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfJump BPF_JMP_JEQ_K pairNr 0 11
     , bpfStmt BPF_LD_W_ABS 16
     , bpfJump BPF_JMP_JEQ_K 1 0 7
     , bpfStmt BPF_LD_W_ABS 32
     , bpfJump BPF_JMP_JEQ_K 0 0 5
     , bpfStmt BPF_LD_W_ABS 24
     , bpfStmt BPF_ALU_AND_K 0xfff7f7ff
     , bpfJump BPF_JMP_JEQ_K 1 3 0
     , bpfJump BPF_JMP_JEQ_K 2 2 0
     , bpfJump BPF_JMP_JEQ_K 5 1 0
     , bpfStmt BPF_RET_K 0x00050001
     , bpfStmt BPF_RET_K 0x7fff0000
     , bpfStmt BPF_RET_K 0x7fff0000 ]

example : ¬ Core.AllPass (test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    { stubSeccompApi with compileSeccompBpf := mutantSocketpairAllowDgramBpf }) := by
  intro h
  have h0 := h { args := { a0 := 1, a1 := 2, a2 := 0 } }
  exact absurd h0.2.2.2.1 (by decide)

end LeanSwe.ProcessSandbox.Seccomp
