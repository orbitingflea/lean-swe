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

/-- Verify `keyProvenanceOkCases` under `modelNumApi`. -/
theorem keyProvenanceOk_model_valid : keyProvenanceOkCases.all checkOneOkModel = true := by
  simp only [keyProvenanceOkCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

/-- Verify `keyProvenanceErrCases` under `modelNumApi`. -/
theorem keyProvenanceErr_model_valid : keyProvenanceErrCases.all checkOneErrModel = true := by
  simp only [keyProvenanceErrCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

/-- Verify `stringOkCases` under `modelNumApi`. -/
theorem stringOk_model_valid : stringOkCases.all checkOneOkModel = true := by
  simp only [stringOkCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

/-- Verify `stringErrCases` under `modelNumApi`. -/
theorem stringErr_model_valid : stringErrCases.all checkOneErrModel = true := by
  simp only [stringErrCases, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true]
  repeat' (apply And.intro; cbv)
  cbv

end LeanSwe.Toml.Proofs
