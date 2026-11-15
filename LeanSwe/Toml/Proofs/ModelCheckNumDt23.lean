import LeanSwe.Toml.Proofs.ModelCheckNumDt1

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

set_option Elab.async false

/-- Verify element 2 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_2 :
    ((numberDatetimeOkCases.drop 2).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

/-- Verify element 3 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_3 :
    ((numberDatetimeOkCases.drop 3).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

end LeanSwe.Toml.Proofs
