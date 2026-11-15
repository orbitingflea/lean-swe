import LeanSwe.Toml.Proofs.ModelCheckNumDt23

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

set_option Elab.async false

/-- Verify `numberDatetimeErrCases` under `modelNumApi`. -/
theorem numberDatetimeErr_model_valid : numberDatetimeErrCases.all checkOneErrModel = true := by
  simp only [numberDatetimeErrCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

/-- Verify `floatBitCases` under `modelNumApi`. -/
theorem floatBit_model_valid : floatBitCases.all checkOneFloatBitModel = true := by
  simp only [floatBitCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

end LeanSwe.Toml.Proofs
