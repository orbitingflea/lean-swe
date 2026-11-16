import LeanSwe.Toml.Proofs.ModelCheckNumDtErrFloat

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml

private theorem list_all_four {α : Type} (p : α → Bool) (l : List α)
    (hlen : l.length = 4)
    (h0 : ((l.drop 0).head?.map p).getD false = true)
    (h1 : ((l.drop 1).head?.map p).getD false = true)
    (h2 : ((l.drop 2).head?.map p).getD false = true)
    (h3 : ((l.drop 3).head?.map p).getD false = true) :
    l.all p = true := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩ <;> simp at hlen
  simp only [List.drop_zero, List.drop_succ_cons, List.head?_cons, Option.map_some, Option.getD_some] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

/-- Verify `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_model_valid : numberDatetimeOkCases.all checkOneOkModel = true :=
  list_all_four checkOneOkModel numberDatetimeOkCases rfl
    numberDatetimeOk_0 numberDatetimeOk_1 numberDatetimeOk_2 numberDatetimeOk_3

end LeanSwe.Toml.Proofs
