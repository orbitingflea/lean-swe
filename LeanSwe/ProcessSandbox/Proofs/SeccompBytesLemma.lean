import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests

namespace LeanSwe.ProcessSandbox.Proofs

open LeanSwe.ProcessSandbox.Model

private theorem flatMap_length_eight {α β : Type} (f : α → List β)
    (hf : ∀ x, (f x).length = 8) (xs : List α) :
    (xs.flatMap f).length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.flatMap_cons, List.length_append, hf x, ih, List.length_cons]
    omega

private theorem encodeSeccompBpf_size (prog : Array SockFilter) :
    (Seccomp.encodeSeccompBpf prog).size = 8 * prog.size := by
  change (prog.toList.flatMap _).toArray.size = 8 * prog.size
  rw [List.size_toArray, flatMap_length_eight _ (fun _ => rfl), Array.length_toList]

private theorem compileSeccompBpf_size_bounds (arch : SeccompArch) :
    0 < (Seccomp.compileSeccompBpf arch).size ∧
      (Seccomp.compileSeccompBpf arch).size ≤ SECCOMP_MAX_INSNS := by
  cases arch <;> exact ⟨by decide, by decide⟩

/-- Compiled seccomp BPF byte payloads satisfy mock filter size and 8-byte alignment checks. -/
theorem isValidMockSeccompBytes_compiled (arch : SeccompArch) :
    isValidMockSeccompBytes (Internal.encodedSeccompFilter arch) = true := by
  unfold Internal.encodedSeccompFilter
  have ⟨hGt0, hLeMax⟩ := compileSeccompBpf_size_bounds arch
  unfold isValidMockSeccompBytes
  rw [encodeSeccompBpf_size]
  have h1 : (8 * (Seccomp.compileSeccompBpf arch).size != 0) = true := by
    simp only [bne_iff_ne, ne_eq]; omega
  have h3 : decide (8 * (Seccomp.compileSeccompBpf arch).size ≤ 8 * SECCOMP_MAX_INSNS) = true := by
    simp only [decide_eq_true_eq]; omega
  simp [h1, h3]

end LeanSwe.ProcessSandbox.Proofs
