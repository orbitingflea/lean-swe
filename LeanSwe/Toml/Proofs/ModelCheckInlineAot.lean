import LeanSwe.Toml.Proofs.ModelCheckKeysStrings

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

set_option Elab.async false

set_option maxRecDepth 2048 in
/-- Verify `inlineAotOkCases` under `modelNumApi`. -/
theorem inlineAotOk_model_valid : inlineAotOkCases.all checkOneOkModel = true := by
  simp only [inlineAotOkCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

/-- Verify `inlineAotErrCases` under `modelNumApi`. -/
theorem inlineAotErr_model_valid : inlineAotErrCases.all checkOneErrModel = true := by
  simp only [inlineAotErrCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

end LeanSwe.Toml.Proofs
