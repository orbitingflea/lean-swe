import LeanSwe.Toml.Proofs.ModelCheckNumDt0

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

set_option Elab.async false

set_option maxRecDepth 4096 in
/-- Verify element 1 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_1 :
    ((numberDatetimeOkCases.drop 1).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  cbv

end LeanSwe.Toml.Proofs
