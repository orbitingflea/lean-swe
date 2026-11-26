import LeanSwe.LinuxSyscall.Sandbox.SpecTests
import LeanSwe.LinuxSyscall.Sandbox.SpecMutants.Extra
import LeanSwe.LinuxSyscall.Sandbox.SpecMutants.WrapperGuards

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    SandboxErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ENOMSG then .permissionDenied else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ENOMSG
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EBADFD then .invalidArg else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.EBADFD
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ENOENT then .invalidArg else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ENOENT
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encSeccomp := fun f => { f with tsyncEsrch := false }.toBits)) := by
  intro h
  have h0 := h { tsyncEsrch := false } { tsyncEsrch := true }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encSeccomp := fun f =>
      (if f.tsync then (2 : UInt32) else 0) |||
      (if f.log then (1 : UInt32) else 0) |||
      (if f.specAllow then (4 : UInt32) else 0) |||
      (if f.tsyncEsrch then (16 : UInt32) else 0))) := by
  intro h
  have h0 := h {} {}
  exact absurd h0.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encPrctl := fun
      | .setChildSubreaper _ => (2, 0)
      | other => other.toRaw)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 (.setChildSubreaper false) (.setChildSubreaper true) 0
  exact absurd h1.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encRlimit := fun _ => 0)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .nofile
  exact absurd h2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encMemfd := fun f =>
      (if f.cloexec then (1 : UInt32) else 0) |||
      (if f.allowSealing then (2 : UInt32) else 0) |||
      (if f.noexecSeal then (4 : UInt32) else 0) |||
      (if f.exec then (16 : UInt32) else 0))) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  exact absurd h3.2.1.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encBpf := fun prog =>
      ByteArray.mk ((prog.flatMap fun insn =>
        encodeSockFilterInsn { insn with jt := insn.jf, jf := insn.jt }).toArray))
    (decBpf := fun b =>
      (decodeSockFilters b).map (List.map fun insn => { insn with jt := insn.jf, jf := insn.jt }))) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  have h4 := h3.2.2.2 { code := 0x0015, jt := 1, jf := 2, k := 0 }
  have hWire := h4.1
  have hNe : ByteArray.mk #[0x15, 0, 2, 1, 0, 0, 0, 0] ≠
      ByteArray.mk #[0x15, 0, 1, 2, 0, 0, 0, 0] := by
    intro heq
    have hd : (#[0x15, 0, 2, 1, 0, 0, 0, 0] : Array UInt8) = #[0x15, 0, 1, 2, 0, 0, 0, 0] :=
      congrArg ByteArray.data heq
    exact absurd hd (by decide)
  exact hNe hWire

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (decBpf := fun b =>
      match decodeSockFilters b with
      | some p => some p
      | none => some [])) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  have h4 := h3.2.2.2 { code := 0x0006, jt := 0, jf := 0, k := 0 }
  have h5 := h4.2 []
  have h6 := h5.2 (ByteArray.mk #[0]) (by decide)
  cases h6.1

end LeanSwe.LinuxSyscall.Sandbox
