import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Impl
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests

namespace LeanSwe.ProcessSandbox.Proofs

open LeanSwe.ProcessSandbox.Model

private theorem encodeSockFilterList_length (insn : SockFilter) :
    (Seccomp.Impl.encodeSockFilterList insn).length = 8 := rfl

private theorem flatMap_encodeSockFilterList_length (xs : List SockFilter) :
    (xs.flatMap Seccomp.Impl.encodeSockFilterList).length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.flatMap_cons, List.length_append, encodeSockFilterList_length, ih, List.length_cons]
    omega

private theorem encodeSeccompBpf_size (prog : Array SockFilter) :
    (Seccomp.Impl.encodeSeccompBpf prog).size = 8 * prog.size := by
  unfold Seccomp.Impl.encodeSeccompBpf
  change (prog.toList.flatMap Seccomp.Impl.encodeSockFilterList).toArray.size = 8 * prog.size
  rw [List.size_toArray, flatMap_encodeSockFilterList_length, Array.length_toList]

private theorem compileSeccompBpf_size_bounds (arch : SeccompArch) :
    0 < (Seccomp.Impl.compileSeccompBpf arch).size ∧
      (Seccomp.Impl.compileSeccompBpf arch).size ≤ SECCOMP_MAX_INSNS := by
  cases arch <;> exact ⟨by decide, by decide⟩

/-- Compiled seccomp BPF byte payloads satisfy mock filter size and 8-byte alignment checks. -/
theorem isValidMockSeccompBytes_compiled (arch : SeccompArch) :
    isValidMockSeccompBytes (Internal.encodedSeccompFilter arch) = true := by
  unfold Internal.encodedSeccompFilter
  have ⟨hGt0, hLeMax⟩ := compileSeccompBpf_size_bounds arch
  unfold isValidMockSeccompBytes
  rw [encodeSeccompBpf_size]
  have h1 : (8 * (Seccomp.Impl.compileSeccompBpf arch).size != 0) = true := by
    simp only [bne_iff_ne, ne_eq]; omega
  have h3 : decide (8 * (Seccomp.Impl.compileSeccompBpf arch).size ≤ 8 * SECCOMP_MAX_INSNS) = true := by
    simp only [decide_eq_true_eq]; omega
  simp [h1, h3]

end LeanSwe.ProcessSandbox.Proofs
