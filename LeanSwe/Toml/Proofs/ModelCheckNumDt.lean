import LeanSwe.Toml.Proofs.ModelCheckNumDtErrFloat

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

/-- Verify `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_model_valid : numberDatetimeOkCases.all checkOneOkModel = true := by
  have h0 := numberDatetimeOk_0
  have h1 := numberDatetimeOk_1
  have h2 := numberDatetimeOk_2
  have h3 := numberDatetimeOk_3
  simp only [numberDatetimeOkCases, List.drop_zero, List.drop_succ_cons, List.head?_cons,
    Option.map_some, Option.getD_some] at h0 h1 h2 h3
  simp only [numberDatetimeOkCases, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h0, ⟨h1, ⟨h2, h3⟩⟩⟩

end LeanSwe.Toml.Proofs
