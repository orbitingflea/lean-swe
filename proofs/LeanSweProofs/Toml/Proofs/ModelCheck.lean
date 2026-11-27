import LeanSweProofs.Toml.Proofs.Core
import LeanSweProofs.Toml.Proofs.NumParseContract
import LeanSweProofs.Toml.SpecTests.Cases

/-!
Concrete model-oracle conformance proofs for `LeanSwe/Toml`.

Evaluates all 9 concrete parser, error-kind, and IEEE-754 float-bit suites from
`LeanSwe.Toml.SpecTests.Cases` by reducing only the input `String.toList` via `cbv`
and closing each pure `List Char` parser check via kernel `decide`.
-/

set_option Elab.async false
set_option maxRecDepth 20000

open LeanSwe.Toml
open LeanSwe.Toml.Impl
open LeanSwe.Toml.Model
open LeanSwe.NumParse

namespace LeanSwe.Toml.Proofs

/-- Executable `Bool` form of `checkOneOkModel` over decoded characters. -/
def checkModelOk (cs : List Char) (expected : TomlTable) : Bool :=
  match parseCharsWithNum modelCharNumApi cs with
  | .ok t => tomlValueBeq (TomlValue.table expected) (TomlValue.table t)
  | .error _ => false

/-- Executable `Bool` form of `checkOneErrModel` over decoded characters. -/
def checkModelErr (cs : List Char) (kind : TomlErrorKind) : Bool :=
  match parseCharsWithNum modelCharNumApi cs with
  | .ok _ => false
  | .error e => e.kind == kind

/-- Executable `Bool` form of `checkOneFloatBitModel` over decoded characters. -/
def checkModelFloatBits (cs : List Char) (key : String) (bits? : Option UInt64) : Bool :=
  match parseCharsWithNum modelCharNumApi cs with
  | .error _ => false
  | .ok t =>
    match lookupKey key t with
    | some (.float f) =>
      match bits? with
      | none => f.isNaN
      | some bits => !f.isNaN && f.toBits == bits
    | _ => false

private theorem ok_step {s : String} {t : TomlTable} {xs : List (String × TomlTable)}
    (hx : checkModelOk s.toList t = true) (hxs : xs.all checkOneOkModel = true) :
    ((s, t) :: xs).all checkOneOkModel = true := by
  simp only [List.all_cons, hxs, Bool.and_true]
  simp only [checkOneOkModel, checkModelOk, parseWithNum_model_eq] at hx ⊢
  cases hp : parseCharsWithNum modelCharNumApi s.toList <;> simp [hp] at hx ⊢ <;> exact hx

private theorem err_step {s : String} {k : TomlErrorKind} {xs : List (String × TomlErrorKind)}
    (hx : checkModelErr s.toList k = true) (hxs : xs.all checkOneErrModel = true) :
    ((s, k) :: xs).all checkOneErrModel = true := by
  simp only [List.all_cons, hxs, Bool.and_true]
  simp only [checkOneErrModel, checkModelErr, parseWithNum_model_eq] at hx ⊢
  cases hp : parseCharsWithNum modelCharNumApi s.toList <;> simp [hp] at hx ⊢ <;> exact hx

private theorem flt_step {s : String} {key : String} {b : Option UInt64}
    {xs : List (String × String × Option UInt64)}
    (hx : checkModelFloatBits s.toList key b = true) (hxs : xs.all checkOneFloatBitModel = true) :
    ((s, key, b) :: xs).all checkOneFloatBitModel = true := by
  simp only [List.all_cons, hxs, Bool.and_true]
  simp only [checkOneFloatBitModel, checkModelFloatBits, parseWithNum_model_eq] at hx ⊢
  cases hp : parseCharsWithNum modelCharNumApi s.toList with
  | error _ => simp [hp] at hx
  | ok tbl =>
    simp only [hp] at hx ⊢
    cases hl : lookupKey key tbl with
    | none => simp [hl] at hx
    | some val => cases val <;> simp [hl] at hx ⊢ <;> exact hx

/-- Unfold a concrete suite, step element-by-element, decode `s.toList` via `cbv`, and close via `decide`. -/
macro "prove_suite_with" name:ident step:ident : tactic =>
  `(tactic| (
    unfold $name:ident
    repeat' (refine $step:ident ?_ ?_; · ((conv => lhs; arg 1; cbv); first | decide | cbv))
    rfl))

private theorem keyProvenanceOk_model_valid : keyProvenanceOkCases.all checkOneOkModel = true := by
  prove_suite_with keyProvenanceOkCases ok_step

private theorem keyProvenanceErr_model_valid : keyProvenanceErrCases.all checkOneErrModel = true := by
  prove_suite_with keyProvenanceErrCases err_step

private theorem inlineAotOk_model_valid : inlineAotOkCases.all checkOneOkModel = true := by
  prove_suite_with inlineAotOkCases ok_step

private theorem inlineAotErr_model_valid : inlineAotErrCases.all checkOneErrModel = true := by
  prove_suite_with inlineAotErrCases err_step

private theorem stringOk_model_valid : stringOkCases.all checkOneOkModel = true := by
  prove_suite_with stringOkCases ok_step

private theorem stringErr_model_valid : stringErrCases.all checkOneErrModel = true := by
  prove_suite_with stringErrCases err_step

private theorem numberDatetimeOk_model_valid : numberDatetimeOkCases.all checkOneOkModel = true := by
  prove_suite_with numberDatetimeOkCases ok_step

private theorem numberDatetimeErr_model_valid : numberDatetimeErrCases.all checkOneErrModel = true := by
  prove_suite_with numberDatetimeErrCases err_step

private theorem floatBit_model_valid : floatBitCases.all checkOneFloatBitModel = true := by
  prove_suite_with floatBitCases flt_step

section
attribute [local irreducible] parseWithNum

/-- Prove `test_toml_keysAndProvenance_conformsToSpec` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_keysAndProvenance (numApi : NumParseApi) :
    Core.AllPass (test_toml_keysAndProvenance_conformsToSpec Internal.mkApi numApi) := by
  intro hobeys
  have hnum := validNumApi_of_obeysApi hobeys
  exact allPass_forM_seq keyProvenanceOkCases keyProvenanceErrCases _ _
    (checkParseEquiv_allPass numApi hnum keyProvenanceOkCases keyProvenanceOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum keyProvenanceErrCases keyProvenanceErr_model_valid)

/-- Witness `CanReach` for `test_toml_keysAndProvenance_conformsToSpec` using `NumParse.Model.modelApi`. -/
theorem canReach_keysAndProvenance :
    Core.CanReach (test_toml_keysAndProvenance_conformsToSpec Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  refine ⟨LeanSwe.NumParse.Model.modelApi_obeys, ?_⟩
  have hnum := validNumApi_of_obeysApi LeanSwe.NumParse.Model.modelApi_obeys
  exact canReach_forM_seq keyProvenanceOkCases keyProvenanceErrCases _ _
    (checkParseEquiv_canReach _ hnum keyProvenanceOkCases keyProvenanceOk_model_valid)
    (checkParseErrorKind_canReach _ hnum keyProvenanceErrCases keyProvenanceErr_model_valid)

/-- Prove `test_toml_inlineTablesAndAot_conformsToSpec` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_inlineTablesAndAot (numApi : NumParseApi) :
    Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec Internal.mkApi numApi) := by
  intro hobeys
  have hnum := validNumApi_of_obeysApi hobeys
  exact allPass_forM_seq inlineAotOkCases inlineAotErrCases _ _
    (checkParseEquiv_allPass numApi hnum inlineAotOkCases inlineAotOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum inlineAotErrCases inlineAotErr_model_valid)

/-- Witness `CanReach` for `test_toml_inlineTablesAndAot_conformsToSpec` using `NumParse.Model.modelApi`. -/
theorem canReach_inlineTablesAndAot :
    Core.CanReach (test_toml_inlineTablesAndAot_conformsToSpec Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  refine ⟨LeanSwe.NumParse.Model.modelApi_obeys, ?_⟩
  have hnum := validNumApi_of_obeysApi LeanSwe.NumParse.Model.modelApi_obeys
  exact canReach_forM_seq inlineAotOkCases inlineAotErrCases _ _
    (checkParseEquiv_canReach _ hnum inlineAotOkCases inlineAotOk_model_valid)
    (checkParseErrorKind_canReach _ hnum inlineAotErrCases inlineAotErr_model_valid)

/-- Prove `test_toml_stringsAndControls_conformsToSpec` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_stringsAndControls (numApi : NumParseApi) :
    Core.AllPass (test_toml_stringsAndControls_conformsToSpec Internal.mkApi numApi) := by
  intro hobeys
  have hnum := validNumApi_of_obeysApi hobeys
  exact allPass_forM_seq stringOkCases stringErrCases _ _
    (checkParseEquiv_allPass numApi hnum stringOkCases stringOk_model_valid)
    (checkParseErrorKind_allPass numApi hnum stringErrCases stringErr_model_valid)

/-- Witness `CanReach` for `test_toml_stringsAndControls_conformsToSpec` using `NumParse.Model.modelApi`. -/
theorem canReach_stringsAndControls :
    Core.CanReach (test_toml_stringsAndControls_conformsToSpec Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  refine ⟨LeanSwe.NumParse.Model.modelApi_obeys, ?_⟩
  have hnum := validNumApi_of_obeysApi LeanSwe.NumParse.Model.modelApi_obeys
  exact canReach_forM_seq stringOkCases stringErrCases _ _
    (checkParseEquiv_canReach _ hnum stringOkCases stringOk_model_valid)
    (checkParseErrorKind_canReach _ hnum stringErrCases stringErr_model_valid)

/-- Prove `test_toml_numbersAndDatetimes_conformsToSpec` for `Internal.mkApi` over any `numApi`. -/
theorem allPass_numbersAndDatetimes (numApi : NumParseApi) :
    Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec Internal.mkApi numApi) := by
  intro hobeys
  have hnum := validNumApi_of_obeysApi hobeys
  exact allPass_forM_seq3 numberDatetimeOkCases floatBitCases numberDatetimeErrCases _ _ _
    (checkParseEquiv_allPass numApi hnum numberDatetimeOkCases numberDatetimeOk_model_valid)
    (checkParseFloatBits_allPass numApi hnum floatBit_model_valid)
    (checkParseErrorKind_allPass numApi hnum numberDatetimeErrCases numberDatetimeErr_model_valid)

/-- Witness `CanReach` for `test_toml_numbersAndDatetimes_conformsToSpec` using `NumParse.Model.modelApi`. -/
theorem canReach_numbersAndDatetimes :
    Core.CanReach (test_toml_numbersAndDatetimes_conformsToSpec Internal.mkApi LeanSwe.NumParse.Model.modelApi) := by
  refine ⟨LeanSwe.NumParse.Model.modelApi_obeys, ?_⟩
  have hnum := validNumApi_of_obeysApi LeanSwe.NumParse.Model.modelApi_obeys
  exact canReach_forM_seq3 numberDatetimeOkCases floatBitCases numberDatetimeErrCases _ _ _
    (checkParseEquiv_canReach _ hnum numberDatetimeOkCases numberDatetimeOk_model_valid)
    (checkParseFloatBits_canReach _ hnum floatBit_model_valid)
    (checkParseErrorKind_canReach _ hnum numberDatetimeErrCases numberDatetimeErr_model_valid)

end

end LeanSwe.Toml.Proofs
