import LeanSwe.Toml.Proofs.ModelCheckInlineAot

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

set_option Elab.async false

/-- Verify element 0 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_0 :
    ((numberDatetimeOkCases.drop 0).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]
  cbv

end LeanSwe.Toml.Proofs
