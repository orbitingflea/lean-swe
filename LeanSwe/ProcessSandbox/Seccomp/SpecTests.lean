import Core.NondetTest
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Model

namespace LeanSwe.ProcessSandbox.Seccomp

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ProcessSandbox.Model

/-- `api.compileSeccompBpf` emits a structurally valid Linux `seccomp_check_filter` cBPF program (`1..160` instructions, forward in-bounds jumps, aligned low-word `BPF_ABS` offsets `{0, 4, 16 + 8 * i}`, total `{ALLOW, EPERM, ENOSYS}` verdicts), and `api.encodeSeccompBpf` serializes contiguous `8 * n`-byte little-endian `struct sock_filter` records. -/
def test_seccomp_compileAndEncode_validProgAndLittleEndianWire
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let arch ← nondet SeccompArch
  let inp ← nondet SeccompData
  let compiled := api.compileSeccompBpf arch
  NondetTest.assert (isValidLinuxSeccompProg compiled = true)
  let verdict := evalBpf compiled inp
  NondetTest.assert (verdict = some 0x7fff0000 ∨ verdict = some 0x00050001 ∨ verdict = some 0x00050026)
  let rawProg ← nondet (Array SockFilter)
  let wire := api.encodeSeccompBpf rawProg
  NondetTest.assert (wire.size = 8 * rawProg.size)
  NondetTest.assert (wire = encodeSeccompBpfModel rawProg)
  let idx ← nondet Nat
  assume (idx < rawProg.size)
  let insn := rawProg[idx]!
  let base := 8 * idx
  NondetTest.assert (
    wire[base]! = UInt8.ofNat (insn.code.toNat % 256) ∧
    wire[base + 1]! = UInt8.ofNat ((insn.code.toNat / 256) % 256) ∧
    wire[base + 2]! = insn.jt ∧
    wire[base + 3]! = insn.jf ∧
    wire[base + 4]! = UInt8.ofNat (insn.k.toNat % 256) ∧
    wire[base + 5]! = UInt8.ofNat ((insn.k.toNat / 256) % 256) ∧
    wire[base + 6]! = UInt8.ofNat ((insn.k.toNat / 65536) % 256) ∧
    wire[base + 7]! = UInt8.ofNat ((insn.k.toNat / 16777216) % 256))

/-- Across every `SeccompArch`, `ValidCompiledPlan`, `SandboxWorldState`, and `SeccompData`, `evalBpf (api.compileSeccompBpf arch) inp` agrees bidirectionally with `Model.stepGuestSyscall` via `decodeSeccompSyscall` (`ENOSYS` iff `.clone3Attempt`, `EPERM` iff `.blockedBySeccompOrNamespace`, and `ALLOW` iff `none | .anonUnixSocketpair (.stream | .seqpacket) | .cloneProc _ false`). -/
def test_seccomp_evalBpf_matchesStepGuestSyscallModel
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let arch ← nondet SeccompArch
  let plan ← nondet CompiledSandboxPlan
  let st ← nondet SandboxWorldState
  let inp ← nondet SeccompData
  assume (isValidCompiledPlan plan = true)
  let verdict := evalBpf (api.compileSeccompBpf arch) inp
  match decodeSeccompSyscall arch inp with
  | none =>
    NondetTest.assert (verdict = some 0x7fff0000)
  | some sc =>
    if verdict == some 0x00050026 then
      NondetTest.assert (sc = .clone3Attempt ∧ stepGuestSyscall plan st sc = .error .clone3FallbackEnosys)
    else if verdict == some 0x00050001 then
      NondetTest.assert (stepGuestSyscall plan st sc = .error .blockedBySeccompOrNamespace)
    else
      NondetTest.assert (verdict = some 0x7fff0000 ∧
        stepGuestSyscall plan st sc ≠ .error .blockedBySeccompOrNamespace ∧
        stepGuestSyscall plan st sc ≠ .error .clone3FallbackEnosys ∧
        (sc = .anonUnixSocketpair .stream ∨
          sc = .anonUnixSocketpair .seqpacket ∨
          ∃ pid, sc = .cloneProc pid false))

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 1 and 2): mismatched `seccomp_data.arch` on either `x86_64` (`0xc000003e`) or `aarch64` (`0xc00000b7`) and `x86_64` unsigned `nr ≥ 0x40000000` (`__X32_SYSCALL_BIT` / negative `int nr`) always return `SECCOMP_RET_ERRNO | EPERM` (`0x00050001`). -/
def test_seccomp_rawArchAndX32_rejectsMismatchAndX32Bit
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let inpBadX ← nondet SeccompData
  assume (inpBadX.arch ≠ 0xc000003e)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpBadX = some 0x00050001)
  let inpBadA ← nondet SeccompData
  assume (inpBadA.arch ≠ 0xc00000b7)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .aarch64) inpBadA = some 0x00050001)
  let inpX32 ← nondet SeccompData
  assume (inpX32.arch = 0xc000003e ∧ inpX32.nr ≥ 0x40000000)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpX32 = some 0x00050001)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 3 and 4): `clone3` (`435`) returns `SECCOMP_RET_ERRNO | ENOSYS` (`0x00050026`), and `clone` (`56` on `x86_64`, `220` on `aarch64`) returns `EPERM` (`0x00050001`) iff `(args[0].lo32 &&& 0x7e020000) != 0` and `ALLOW` (`0x7fff0000`) otherwise (preserving `0x80` `CSIGNAL` and `SIGCHLD`). -/
def test_seccomp_rawClone3AndClone_enosysAndNamespaceMask
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let inp ← nondet SeccompData
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 435 } = some 0x00050026)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 435 } = some 0x00050026)
  let expectedClone : UInt32 :=
    if (inp.args.a0.toUInt32 &&& 0x7e020000) != 0 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 56 } = some expectedClone)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 220 } = some expectedClone)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 5 and 6): `socket` (`41` on `x86_64`, `198` on `aarch64`) blocks `AF_UNIX` (`1`) and `AF_SMC` (`43`) with `EPERM` and allows all other domains, while `socketpair` (`53` on `x86_64`, `199` on `aarch64`) allows iff `args[0].lo32 == 1 ∧ args[2].lo32 == 0 ∧ (args[1].lo32 &&& 0xfff7f7ff) ∈ {1, 5}` and returns `EPERM` otherwise. -/
def test_seccomp_rawSocketAndSocketpair_afUnixSmcAndAnonPair
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let inp ← nondet SeccompData
  let dom := inp.args.a0.toUInt32
  let expectedSock : UInt32 := if dom == 1 || dom == 43 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 41 } = some expectedSock)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 198 } = some expectedSock)
  let baseType := inp.args.a1.toUInt32 &&& 0xfff7f7ff
  let proto := inp.args.a2.toUInt32
  let expectedPair : UInt32 :=
    if dom == 1 && proto == 0 && (baseType == 1 || baseType == 5) then 0x7fff0000 else 0x00050001
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 53 } = some expectedPair)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 199 } = some expectedPair)

/-- Direct non-circular raw `(arch, nr, args)` rule check (class 7): `sendto` (`44` / `206`, `args[3].lo32`), `sendmsg` (`46` / `211`, `args[2].lo32`), and `sendmmsg` (`307` / `269`, `args[3].lo32`) return `EPERM` (`0x00050001`) iff `MSG_FASTOPEN` (`0x20000000`) is set in the exact per-syscall `flags` argument and `ALLOW` (`0x7fff0000`) otherwise. -/
def test_seccomp_rawSendFastopen_exactArgIndices
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let inp ← nondet SeccompData
  let expArg3 : UInt32 :=
    if (inp.args.a3.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000
  let expArg2 : UInt32 :=
    if (inp.args.a2.toUInt32 &&& 0x20000000) != 0 then 0x00050001 else 0x7fff0000
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 44 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 206 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 46 } = some expArg2)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 211 } = some expArg2)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := 307 } = some expArg3)
  NondetTest.assert (
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := 269 } = some expArg3)

/-- Direct non-circular raw `(arch, nr, args)` rule check (classes 8 and 9): all 33 admin/escape syscalls (including `acct` `163`/`89` and `mount_setattr` `442`/`442`, excluding `fsconfig` `431`) return `EPERM` (`0x00050001`) on both `x86_64` and `aarch64`, and every other native in-range syscall returns `ALLOW` (`0x7fff0000`). -/
def test_seccomp_rawDenyTableAndDefaultAllow_all33AndOtherSyscalls
    {runner} [NondetTest runner] (api : SeccompApi) : runner Unit := do
  let rawX86Deny33 : List UInt32 :=
    [ 169, 246, 320, 165, 166, 155, 167, 168, 432, 430, 433, 429, 428, 442
    , 175, 313, 176, 163, 164, 227, 305, 159, 321, 425, 426, 427, 250, 248
    , 249, 298, 323, 272, 308 ]
  let rawAarch64Deny33 : List UInt32 :=
    [ 142, 104, 294, 40, 39, 41, 224, 225, 432, 430, 433, 429, 428, 442
    , 105, 273, 106, 89, 170, 112, 266, 171, 280, 425, 426, 427, 219, 217
    , 218, 241, 282, 97, 268 ]
  NondetTest.assert (rawX86Deny33.length = 33 ∧ allDistinct rawX86Deny33 = true)
  NondetTest.assert (rawAarch64Deny33.length = 33 ∧ allDistinct rawAarch64Deny33 = true)
  let inp ← nondet SeccompData
  NondetTest.assert (rawX86Deny33.all (fun nr =>
    evalBpf (api.compileSeccompBpf .x86_64) { inp with arch := 0xc000003e, nr := nr } == some 0x00050001) = true)
  NondetTest.assert (rawAarch64Deny33.all (fun nr =>
    evalBpf (api.compileSeccompBpf .aarch64) { inp with arch := 0xc00000b7, nr := nr } == some 0x00050001) = true)
  let inpAllowX ← nondet SeccompData
  assume (inpAllowX.arch = 0xc000003e ∧ inpAllowX.nr < 0x40000000 ∧
    !([435, 56, 41, 53, 44, 46, 307] ++ rawX86Deny33).contains inpAllowX.nr)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .x86_64) inpAllowX = some 0x7fff0000)
  let inpAllowA ← nondet SeccompData
  assume (inpAllowA.arch = 0xc00000b7 ∧
    !([435, 220, 198, 199, 206, 211, 269] ++ rawAarch64Deny33).contains inpAllowA.nr)
  NondetTest.assert (evalBpf (api.compileSeccompBpf .aarch64) inpAllowA = some 0x7fff0000)

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
