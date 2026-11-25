import Core.Obeys
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.Model.FormatIntWitness
import LeanSwe.NumParse.Model.FormatFloatWitness

namespace LeanSwe.NumParse.Model

/-- Allowed outcome relation for `NumParse.formatFloat` against `FloatFormatSpec`. -/
abbrev allowedFormatFloat (x : Float) (s : String) : Prop :=
  FloatFormatSpec x s

/-- Full `NumParse.Model` refinement contract for an arbitrary `NumParseApi` bundle. -/
def ObeysApi (num : NumParseApi) : Prop :=
  Core.ObeysPure num.parseInt allowedParseInt ∧
  Core.ObeysPure num.parseInt64 allowedParseInt64 ∧
  Core.ObeysPure num.formatInt allowedFormatInt ∧
  Core.ObeysPure num.parseFloat allowedParseFloat ∧
  Core.ObeysPure num.formatFloat allowedFormatFloat

/-- Pure mathematical reference `NumParseApi` witness built solely from `LeanSwe.NumParse.Model`. -/
def modelApi : NumParseApi :=
  { parseInt := fun s =>
      match parseIntModel s with
      | .ok n => .ok n
      | .error k => .error { kind := k, message := "model error" }
  , parseInt64 := fun s =>
      match parseInt64Model s with
      | .ok n => .ok n
      | .error k => .error { kind := k, message := "model error" }
  , formatInt := witnessFormatInt
  , parseFloat := fun s =>
      match parseFloatModel s with
      | .ok x => .ok x
      | .error k => .error { kind := k, message := "model error" }
  , formatFloat := witnessFormatFloat }

/-- The pure mathematical `modelApi` satisfies `ObeysApi`. -/
theorem modelApi_obeys : ObeysApi modelApi := by
  refine ⟨?_, ?_, allowedFormatInt_witnessFormatInt, ?_, floatFormatSpec_witnessFormatFloat⟩
  · intro s
    unfold allowedParseInt modelApi
    dsimp only
    cases parseIntModel s with
    | ok _ => exact ⟨rfl, fun _ h => nomatch h⟩
    | error _ => exact ⟨rfl, fun _ h => by cases h; change "model error" ≠ ""; decide⟩
  · intro s
    unfold allowedParseInt64 modelApi
    dsimp only
    cases parseInt64Model s with
    | ok _ => exact ⟨rfl, fun _ h => nomatch h⟩
    | error _ => exact ⟨rfl, fun _ h => by cases h; change "model error" ≠ ""; decide⟩
  · intro s
    unfold allowedParseFloat modelApi
    dsimp only
    cases parseFloatModel s with
    | ok _ => exact ⟨rfl, fun _ h => nomatch h⟩
    | error _ => exact ⟨rfl, fun _ h => by cases h; change "model error" ≠ ""; decide⟩

/-- Non-vacuity witness showing `ObeysApi` is inhabited solely from `NumParse.Model`. -/
theorem obeysApi_satisfiable : ∃ num : NumParseApi, ObeysApi num :=
  ⟨modelApi, modelApi_obeys⟩

end LeanSwe.NumParse.Model
