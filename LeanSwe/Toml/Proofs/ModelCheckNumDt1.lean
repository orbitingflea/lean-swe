import LeanSwe.Toml.Proofs.ModelCheckNumDt0

set_option Elab.async false

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.ProofsInternal

private theorem docKeyVal_o1 :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('o' :: r) ap rt = docKeyValBody fuel ('o' :: r) ap rt :=
  docKeyVal_of 'o' (skipTriviaNewlines_eq_of 'o' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private def dt1Dt : Std.Time.PlainDateTime :=
  Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0)

private def dt1Val : TomlValue :=
  TomlValue.offsetDateTime { dateTime := dt1Dt, offset := specOffset 0 }

private theorem cls_odt1 :
    classifyScalarToken modelNumApi "1979-05-27T07:32:00Z" = .ok dt1Val := by cbv

private theorem cls_odt2 :
    classifyScalarToken modelNumApi "1979-05-27t07:32:00z" = .ok dt1Val := by cbv

private theorem cls_odt3 :
    classifyScalarToken modelNumApi "1979-05-27 07:32:00+00:00" = .ok dt1Val := by cbv

private theorem cls_odt4 :
    classifyScalarToken modelNumApi "1979-05-27T07:32:00-00:00" = .ok dt1Val := by cbv

private theorem tok_odt3 :
    ∀ rest, takeUnquotedToken ("1979-05-27 07:32:00+00:00".toList ++ '\n' :: rest) =
      ("1979-05-27 07:32:00+00:00", '\n' :: rest) := by
  intro rest
  have hs : "1979-05-27 07:32:00+00:00".toList =
      ['1', '9', '7', '9', '-', '0', '5', '-', '2', '7', ' ',
       '0', '7', ':', '3', '2', ':', '0', '0'] ++ "+00:00".toList := by cbv
  have hstr : String.ofList
      (['1', '9', '7', '9', '-', '0', '5', '-', '2', '7', ' ',
        '0', '7', ':', '3', '2', ':', '0', '0'] ++ "+00:00".toList) =
      "1979-05-27 07:32:00+00:00" := by cbv
  rw [hs]
  rw [takeUnquotedToken_spaceDateTime '1' '9' '7' '9' '0' '5' '2' '7' '0' '7' '3' '2' '0' '0'
    "+00:00".toList ('\n' :: rest)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by cbv) (fun _ _ h => by injection h with hc _; subst hc; decide)]
  rw [hstr]

private def dt1Str : String :=
  "odt1 = 1979-05-27T07:32:00Z\nodt2 = 1979-05-27t07:32:00z\nodt3 = 1979-05-27 07:32:00+00:00\nodt4 = 1979-05-27T07:32:00-00:00"

private theorem elem1_clean :
    (dt1Str.toList.all (fun c => !isDisallowedControl c && c != '\r')) = true := by
  cbv

private theorem dt1_hs_eq :
    dt1Str.toList =
      ("odt1" ++ " = " ++ "1979-05-27T07:32:00Z").toList ++ '\n' ::
      (("odt2" ++ " = " ++ "1979-05-27t07:32:00z").toList ++ '\n' ::
      (("odt3" ++ " = " ++ "1979-05-27 07:32:00+00:00").toList ++ '\n' ::
      ("odt4" ++ " = " ++ "1979-05-27T07:32:00-00:00").toList)) := by
  cbv

private def dt1R1 : List (String × Node) := [("odt1", .leaf dt1Val)]
private def dt1R2 : List (String × Node) := dt1R1 ++ [("odt2", .leaf dt1Val)]
private def dt1R3 : List (String × Node) := dt1R2 ++ [("odt3", .leaf dt1Val)]
private def dt1R4 : List (String × Node) := dt1R3 ++ [("odt4", .leaf dt1Val)]

private theorem dt1_hi1 : insertAtActivePath ["odt1"] [] [] ["odt1"] (valueToInlineNode dt1Val) = .ok dt1R1 := by cbv
private theorem dt1_hi2 : insertAtActivePath ["odt2"] dt1R1 [] ["odt2"] (valueToInlineNode dt1Val) = .ok dt1R2 := by cbv
private theorem dt1_hi3 : insertAtActivePath ["odt3"] dt1R2 [] ["odt3"] (valueToInlineNode dt1Val) = .ok dt1R3 := by cbv
private theorem dt1_hi4 : insertAtActivePath ["odt4"] dt1R3 [] ["odt4"] (valueToInlineNode dt1Val) = .ok dt1R4 := by cbv

private theorem elem1_beq :
    tomlValueBeq
      (.table #[("odt1", dt1Val), ("odt2", dt1Val), ("odt3", dt1Val), ("odt4", dt1Val)])
      (.table (entriesToTomlList dt1R4).toArray) = true := by
  cbv

private theorem dt1_hdoc :
    parseDocumentFuel modelNumApi (dt1Str.toList.length + 1) dt1Str.toList [] [] = .ok dt1R4 := by
  have hlen : dt1Str.toList.length + 1 ≥ 4 := by
    rw [dt1_hs_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have hsplit : ∃ f, dt1Str.toList.length + 1 = (((f + 1) + 1) + 1) + 1 :=
    ⟨dt1Str.toList.length + 1 - 4, by omega⟩
  rcases hsplit with ⟨f, hf⟩
  rw [hf, dt1_hs_eq]
  rw [parseDoc_step_nl_noSpace "odt1" "1979-05-27T07:32:00Z" 'o' ['d', 't', '1'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_o1 '1' ("979-05-27T07:32:00Z".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt1Val cls_odt1 [] [] dt1R1 dt1_hi1]
  rw [parseDoc_step_nl_noSpace "odt2" "1979-05-27t07:32:00z" 'o' ['d', 't', '2'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_o1 '1' ("979-05-27t07:32:00z".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt1Val cls_odt2 [] dt1R1 dt1R2 dt1_hi2]
  rw [parseDoc_step_nl_tok "odt3" "1979-05-27 07:32:00+00:00" 'o' ['d', 't', '3'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_o1 '1' ("979-05-27 07:32:00+00:00".toList) (by cbv) (by decide) (fun _ _ => rfl)
    tok_odt3 dt1Val cls_odt3 [] dt1R2 dt1R3 dt1_hi3]
  exact parseDoc_step_eof_noSpace "odt4" "1979-05-27T07:32:00-00:00" 'o' ['d', 't', '4'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_o1 '1' ("979-05-27T07:32:00-00:00".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt1Val cls_odt4 [] dt1R3 dt1R4 dt1_hi4 f

private theorem elem1_valid :
    checkOneOkModel
      (dt1Str, #[("odt1", dt1Val), ("odt2", dt1Val), ("odt3", dt1Val), ("odt4", dt1Val)]) = true := by
  have hnorm : normalizeChars 1 1 dt1Str.toList = .ok dt1Str.toList :=
    normalizeChars_clean _ elem1_clean 1 1
  simp only [checkOneOkModel, parseWithNum, hnorm, dt1_hdoc, bind, Except.bind]
  exact elem1_beq

/-- Verify element 1 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_1 :
    ((numberDatetimeOkCases.drop 1).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  exact elem1_valid

end LeanSwe.Toml.Proofs
