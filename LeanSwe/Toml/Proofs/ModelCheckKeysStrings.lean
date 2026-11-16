import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.SpecTests
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

set_option Elab.async false

/-- Reference `NumParseApi` built directly from the `NumParse` mathematical model specs. -/
def modelNumApi : NumParseApi :=
  { parseInt := fun s =>
      match parseIntModel s with
      | .ok n => .ok n
      | .error k => .error { kind := k, message := "model error" }
  , parseInt64 := fun s =>
      match parseInt64Model s with
      | .ok n => .ok n
      | .error k => .error { kind := k, message := "model error" }
  , parseFloat := fun s =>
      match parseFloatModel s with
      | .ok f => .ok f
      | .error k => .error { kind := k, message := "model error" }
  , formatInt := fun _ => ""
  , formatFloat := fun _ => ""
  }

/-- Evaluate one positive parse spec case against `modelNumApi`. -/
def checkOneOkModel (p : String × TomlTable) : Bool :=
  match parseWithNum modelNumApi p.1 with
  | .ok t => tomlValueBeq (.table p.2) (.table t)
  | .error _ => false

/-- Evaluate one negative parse error spec case against `modelNumApi`. -/
def checkOneErrModel (p : String × TomlErrorKind) : Bool :=
  match parseWithNum modelNumApi p.1 with
  | .ok _ => false
  | .error e => e.kind == p.2

/-- Evaluate one float bit-pattern spec case against `modelNumApi`. -/
def checkOneFloatBitModel (p : String × String × Option UInt64) : Bool :=
  match parseWithNum modelNumApi p.1 with
  | .error _ => false
  | .ok parsed =>
    match lookupKey p.2.1 parsed with
    | some (.float f) =>
      match p.2.2 with
      | none => f.isNaN
      | some bits => !f.isNaN && f.toBits == bits
    | _ => false

private theorem list_drop_succ_tail {α : Type} (l : List α) (i : Nat) :
    l.drop (i + 1) = (l.drop i).tail := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ k ih =>
    cases l with
    | nil => rfl
    | cons _ t => simp [List.drop_succ_cons]

private theorem le_length_of_drop_nil {α : Type} (l : List α) (i : Nat) (h : l.drop i = []) :
    l.length ≤ i := by
  induction l generalizing i with
  | nil => exact Nat.zero_le i
  | cons _ t ih =>
    cases i with
    | zero => cases h
    | succ k =>
      simp only [List.drop_succ_cons] at h
      simp only [List.length_cons]
      have := ih k h
      omega

private theorem list_drop_len_all {α : Type} (p : α → Bool) (l : List α) :
    (l.drop l.length).all p = true := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.length_cons, List.drop_succ_cons]
    exact ih

private theorem list_all_drop_step {α : Type} (p : α → Bool) (l : List α) (i : Nat)
    (hi : i < l.length)
    (h0 : ((l.drop i).head?.map p).getD false = true)
    (ht : (l.drop (i + 1)).all p = true) :
    (l.drop i).all p = true := by
  cases hd : l.drop i with
  | nil =>
    have := le_length_of_drop_nil l i hd
    omega
  | cons _ _ =>
    rw [hd] at h0
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at h0
    rw [list_drop_succ_tail, hd] at ht
    simp only [List.tail_cons] at ht
    simp [h0, ht]

private theorem kpOk_0 : ((keyProvenanceOkCases.drop 0).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_1 : ((keyProvenanceOkCases.drop 1).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_2 : ((keyProvenanceOkCases.drop 2).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_3 : ((keyProvenanceOkCases.drop 3).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_4 : ((keyProvenanceOkCases.drop 4).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_5 : ((keyProvenanceOkCases.drop 5).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_6 : ((keyProvenanceOkCases.drop 6).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpOk_7 : ((keyProvenanceOkCases.drop 7).head?.map checkOneOkModel).getD false = true := by
  simp only [keyProvenanceOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

/-- Verify `keyProvenanceOkCases` under `modelNumApi`. -/
theorem keyProvenanceOk_model_valid : keyProvenanceOkCases.all checkOneOkModel = true := by
  have hlen : keyProvenanceOkCases.length = 8 := rfl
  have h8 : (keyProvenanceOkCases.drop 8).all checkOneOkModel = true := by
    rw [← hlen]; exact list_drop_len_all _ _
  have h7 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 7 (by rw [hlen]; omega) kpOk_7 h8
  have h6 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 6 (by rw [hlen]; omega) kpOk_6 h7
  have h5 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 5 (by rw [hlen]; omega) kpOk_5 h6
  have h4 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 4 (by rw [hlen]; omega) kpOk_4 h5
  have h3 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 3 (by rw [hlen]; omega) kpOk_3 h4
  have h2 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 2 (by rw [hlen]; omega) kpOk_2 h3
  have h1 := list_all_drop_step checkOneOkModel keyProvenanceOkCases 1 (by rw [hlen]; omega) kpOk_1 h2
  exact list_all_drop_step checkOneOkModel keyProvenanceOkCases 0 (by rw [hlen]; omega) kpOk_0 h1

private theorem kpErr_0 : ((keyProvenanceErrCases.drop 0).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_1 : ((keyProvenanceErrCases.drop 1).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_2 : ((keyProvenanceErrCases.drop 2).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_3 : ((keyProvenanceErrCases.drop 3).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_4 : ((keyProvenanceErrCases.drop 4).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_5 : ((keyProvenanceErrCases.drop 5).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_6 : ((keyProvenanceErrCases.drop 6).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_7 : ((keyProvenanceErrCases.drop 7).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_8 : ((keyProvenanceErrCases.drop 8).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_9 : ((keyProvenanceErrCases.drop 9).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_10 : ((keyProvenanceErrCases.drop 10).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_11 : ((keyProvenanceErrCases.drop 11).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_12 : ((keyProvenanceErrCases.drop 12).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_13 : ((keyProvenanceErrCases.drop 13).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_14 : ((keyProvenanceErrCases.drop 14).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_15 : ((keyProvenanceErrCases.drop 15).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_16 : ((keyProvenanceErrCases.drop 16).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_17 : ((keyProvenanceErrCases.drop 17).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem kpErr_18 : ((keyProvenanceErrCases.drop 18).head?.map checkOneErrModel).getD false = true := by
  simp only [keyProvenanceErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

/-- Verify `keyProvenanceErrCases` under `modelNumApi`. -/
theorem keyProvenanceErr_model_valid : keyProvenanceErrCases.all checkOneErrModel = true := by
  have hlen : keyProvenanceErrCases.length = 19 := rfl
  have h19 : (keyProvenanceErrCases.drop 19).all checkOneErrModel = true := by
    rw [← hlen]; exact list_drop_len_all _ _
  have h18 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 18 (by rw [hlen]; omega) kpErr_18 h19
  have h17 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 17 (by rw [hlen]; omega) kpErr_17 h18
  have h16 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 16 (by rw [hlen]; omega) kpErr_16 h17
  have h15 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 15 (by rw [hlen]; omega) kpErr_15 h16
  have h14 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 14 (by rw [hlen]; omega) kpErr_14 h15
  have h13 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 13 (by rw [hlen]; omega) kpErr_13 h14
  have h12 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 12 (by rw [hlen]; omega) kpErr_12 h13
  have h11 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 11 (by rw [hlen]; omega) kpErr_11 h12
  have h10 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 10 (by rw [hlen]; omega) kpErr_10 h11
  have h9 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 9 (by rw [hlen]; omega) kpErr_9 h10
  have h8 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 8 (by rw [hlen]; omega) kpErr_8 h9
  have h7 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 7 (by rw [hlen]; omega) kpErr_7 h8
  have h6 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 6 (by rw [hlen]; omega) kpErr_6 h7
  have h5 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 5 (by rw [hlen]; omega) kpErr_5 h6
  have h4 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 4 (by rw [hlen]; omega) kpErr_4 h5
  have h3 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 3 (by rw [hlen]; omega) kpErr_3 h4
  have h2 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 2 (by rw [hlen]; omega) kpErr_2 h3
  have h1 := list_all_drop_step checkOneErrModel keyProvenanceErrCases 1 (by rw [hlen]; omega) kpErr_1 h2
  exact list_all_drop_step checkOneErrModel keyProvenanceErrCases 0 (by rw [hlen]; omega) kpErr_0 h1

private theorem strOk_0 : ((stringOkCases.drop 0).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strOk_1 : ((stringOkCases.drop 1).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strOk_2 : ((stringOkCases.drop 2).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strOk_3 : ((stringOkCases.drop 3).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strOk_4 : ((stringOkCases.drop 4).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strOk_5 : ((stringOkCases.drop 5).head?.map checkOneOkModel).getD false = true := by
  simp only [stringOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

/-- Verify `stringOkCases` under `modelNumApi`. -/
theorem stringOk_model_valid : stringOkCases.all checkOneOkModel = true := by
  have hlen : stringOkCases.length = 6 := rfl
  have h6 : (stringOkCases.drop 6).all checkOneOkModel = true := by
    rw [← hlen]; exact list_drop_len_all _ _
  have h5 := list_all_drop_step checkOneOkModel stringOkCases 5 (by rw [hlen]; omega) strOk_5 h6
  have h4 := list_all_drop_step checkOneOkModel stringOkCases 4 (by rw [hlen]; omega) strOk_4 h5
  have h3 := list_all_drop_step checkOneOkModel stringOkCases 3 (by rw [hlen]; omega) strOk_3 h4
  have h2 := list_all_drop_step checkOneOkModel stringOkCases 2 (by rw [hlen]; omega) strOk_2 h3
  have h1 := list_all_drop_step checkOneOkModel stringOkCases 1 (by rw [hlen]; omega) strOk_1 h2
  exact list_all_drop_step checkOneOkModel stringOkCases 0 (by rw [hlen]; omega) strOk_0 h1

private theorem strErr_0 : ((stringErrCases.drop 0).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_1 : ((stringErrCases.drop 1).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_2 : ((stringErrCases.drop 2).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_3 : ((stringErrCases.drop 3).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_4 : ((stringErrCases.drop 4).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_5 : ((stringErrCases.drop 5).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_6 : ((stringErrCases.drop 6).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_7 : ((stringErrCases.drop 7).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_8 : ((stringErrCases.drop 8).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_9 : ((stringErrCases.drop 9).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_10 : ((stringErrCases.drop 10).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_11 : ((stringErrCases.drop 11).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_12 : ((stringErrCases.drop 12).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_13 : ((stringErrCases.drop 13).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_14 : ((stringErrCases.drop 14).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_15 : ((stringErrCases.drop 15).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_16 : ((stringErrCases.drop 16).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_17 : ((stringErrCases.drop 17).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_18 : ((stringErrCases.drop 18).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv
private theorem strErr_19 : ((stringErrCases.drop 19).head?.map checkOneErrModel).getD false = true := by
  simp only [stringErrCases, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some, Option.getD_some]; cbv

/-- Verify `stringErrCases` under `modelNumApi`. -/
theorem stringErr_model_valid : stringErrCases.all checkOneErrModel = true := by
  have hlen : stringErrCases.length = 20 := rfl
  have h20 : (stringErrCases.drop 20).all checkOneErrModel = true := by
    rw [← hlen]; exact list_drop_len_all _ _
  have h19 := list_all_drop_step checkOneErrModel stringErrCases 19 (by rw [hlen]; omega) strErr_19 h20
  have h18 := list_all_drop_step checkOneErrModel stringErrCases 18 (by rw [hlen]; omega) strErr_18 h19
  have h17 := list_all_drop_step checkOneErrModel stringErrCases 17 (by rw [hlen]; omega) strErr_17 h18
  have h16 := list_all_drop_step checkOneErrModel stringErrCases 16 (by rw [hlen]; omega) strErr_16 h17
  have h15 := list_all_drop_step checkOneErrModel stringErrCases 15 (by rw [hlen]; omega) strErr_15 h16
  have h14 := list_all_drop_step checkOneErrModel stringErrCases 14 (by rw [hlen]; omega) strErr_14 h15
  have h13 := list_all_drop_step checkOneErrModel stringErrCases 13 (by rw [hlen]; omega) strErr_13 h14
  have h12 := list_all_drop_step checkOneErrModel stringErrCases 12 (by rw [hlen]; omega) strErr_12 h13
  have h11 := list_all_drop_step checkOneErrModel stringErrCases 11 (by rw [hlen]; omega) strErr_11 h12
  have h10 := list_all_drop_step checkOneErrModel stringErrCases 10 (by rw [hlen]; omega) strErr_10 h11
  have h9 := list_all_drop_step checkOneErrModel stringErrCases 9 (by rw [hlen]; omega) strErr_9 h10
  have h8 := list_all_drop_step checkOneErrModel stringErrCases 8 (by rw [hlen]; omega) strErr_8 h9
  have h7 := list_all_drop_step checkOneErrModel stringErrCases 7 (by rw [hlen]; omega) strErr_7 h8
  have h6 := list_all_drop_step checkOneErrModel stringErrCases 6 (by rw [hlen]; omega) strErr_6 h7
  have h5 := list_all_drop_step checkOneErrModel stringErrCases 5 (by rw [hlen]; omega) strErr_5 h6
  have h4 := list_all_drop_step checkOneErrModel stringErrCases 4 (by rw [hlen]; omega) strErr_4 h5
  have h3 := list_all_drop_step checkOneErrModel stringErrCases 3 (by rw [hlen]; omega) strErr_3 h4
  have h2 := list_all_drop_step checkOneErrModel stringErrCases 2 (by rw [hlen]; omega) strErr_2 h3
  have h1 := list_all_drop_step checkOneErrModel stringErrCases 1 (by rw [hlen]; omega) strErr_1 h2
  exact list_all_drop_step checkOneErrModel stringErrCases 0 (by rw [hlen]; omega) strErr_0 h1

end LeanSwe.Toml.Proofs

namespace LeanSwe.Toml.ProofsInternal

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.Proofs

/-- Clean character lists pass `normalizeChars` unchanged. -/
theorem normalizeChars_clean (cs : List Char)
    (h : cs.all (fun c => !isDisallowedControl c && c != '\r') = true) (line col : Nat) :
    normalizeChars line col cs = .ok cs := by
  induction cs generalizing line col with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    rcases h with ⟨⟨hc_ctrl, hc_cr⟩, hrest⟩
    have hrest' := ih hrest
    by_cases hnl : c = '\n'
    · subst hnl
      simp only [normalizeChars, hrest' (line + 1) 1, bind, Except.bind]
    · unfold normalizeChars
      split <;> rename_i heq
      · simp at heq
      · simp [hc_cr] at heq
      · simp [hc_cr] at heq
      · simp [hnl] at heq
      · cases heq
        simp only [hc_ctrl, Bool.false_eq_true, ↓reduceIte, hrest' line (col + 1), bind, Except.bind]

/-- Bare-key prefix followed by a non-bare delimiter splits cleanly in `takeBareKeyChars`. -/
theorem takeBareKeyChars_append (acc ks : List Char) (d : Char) (rest : List Char)
    (hks : ks.all isBareKeyChar = true) (hd : isBareKeyChar d = false) :
    takeBareKeyChars acc (ks ++ d :: rest) = (acc.reverse ++ ks, d :: rest) := by
  induction ks generalizing acc with
  | nil => simp [takeBareKeyChars, hd]
  | cons k ks ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hks
    simp only [List.cons_append, takeBareKeyChars, hks.1, ↓reduceIte]
    rw [ih (k :: acc) hks.2]
    simp

/-- `skipTriviaNewlines` preserves a non-whitespace non-comment leading character. -/
theorem skipTriviaNewlines_eq_of (c : Char)
    (hmatch : ∀ r, skipTriviaNewlines (c :: r) =
      if isHorizWs c then skipTriviaNewlinesAux false r
      else if c == '#' then skipTriviaNewlinesAux true r
      else c :: r)
    (hws : isHorizWs c = false) (hc : (c == '#') = false) :
    ∀ r, skipTriviaNewlines (c :: r) = c :: r := fun r => by
  rw [hmatch r, hws, hc]; rfl

/-- Key-value statement body step for `parseDocumentFuel modelNumApi`. -/
def docKeyValBody (fuel : Nat) (cs : List Char) (ap : List String)
    (rt : List (String × Node)) : Except TomlError (List (String × Node)) := do
  let (relPath, r1) ← parseDottedKey cs
  match skipHorizWs r1 with
  | '=' :: r2 => do
    let (val, r3) ← parseValue modelNumApi (skipHorizWs r2)
    let nextCs ← consumeStatementEnd r3
    let nextRoot ← insertAtActivePath (ap ++ relPath) rt ap relPath (valueToInlineNode val)
    parseDocumentFuel modelNumApi fuel nextCs ap nextRoot
  | _ => .error (mkErr .parseError "expected '=' after key")

/-- Array-of-tables header body step for `parseDocumentFuel modelNumApi`. -/
def docAotBody (fuel : Nat) (rest : List Char) (rt : List (String × Node)) :
    Except TomlError (List (String × Node)) := do
  let (path, r1) ← parseDottedKey (skipHorizWs rest)
  match skipHorizWs r1 with
  | ']' :: ']' :: r2 => do
    let nextCs ← consumeStatementEnd r2
    let nextRoot ← applyAotHeader path rt path
    parseDocumentFuel modelNumApi fuel nextCs path nextRoot
  | _ => .error (mkErr .parseError "expected ']]' closing array-of-tables header")

/-- Table header body step for `parseDocumentFuel modelNumApi`. -/
def docTableBody (fuel : Nat) (rest : List Char) (rt : List (String × Node)) :
    Except TomlError (List (String × Node)) := do
  let (path, r1) ← parseDottedKey (skipHorizWs rest)
  match skipHorizWs r1 with
  | ']' :: r2 => do
    let nextCs ← consumeStatementEnd r2
    let nextRoot ← applyTableHeader path rt path
    parseDocumentFuel modelNumApi fuel nextCs path nextRoot
  | _ => .error (mkErr .parseError "expected ']' closing table header")

/-- Lift `parseDocumentFuel modelNumApi (fuel + 1)` on a key-value leading char to `docKeyValBody`. -/
theorem docKeyVal_of (c : Char)
    (hskip : ∀ r, skipTriviaNewlines (c :: r) = c :: r)
    (hmatch : ∀ fuel r ap rt,
      (match c :: r with
       | [] => .ok rt
       | '[' :: '[' :: rest => docAotBody fuel rest rt
       | '[' :: rest => docTableBody fuel rest rt
       | cs1 => docKeyValBody fuel cs1 ap rt) = docKeyValBody fuel (c :: r) ap rt) :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) (c :: r) ap rt = docKeyValBody fuel (c :: r) ap rt :=
  fun fuel r ap rt => by
    change (match skipTriviaNewlines (c :: r) with
      | [] => .ok rt
      | '[' :: '[' :: rest => docAotBody fuel rest rt
      | '[' :: rest => docTableBody fuel rest rt
      | cs1 => docKeyValBody fuel cs1 ap rt) = docKeyValBody fuel (c :: r) ap rt
    rw [hskip r]
    exact hmatch fuel r ap rt

end LeanSwe.Toml.ProofsInternal
