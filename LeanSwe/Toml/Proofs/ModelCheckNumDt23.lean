import LeanSwe.Toml.Proofs.ModelCheckNumDt1

set_option Elab.async false

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.Toml.ProofsInternal

private theorem docKeyVal_p23 :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('p' :: r) ap rt = docKeyValBody fuel ('p' :: r) ap rt :=
  docKeyVal_of 'p' (skipTriviaNewlines_eq_of 'p' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_n23 :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('n' :: r) ap rt = docKeyValBody fuel ('n' :: r) ap rt :=
  docKeyVal_of 'n' (skipTriviaNewlines_eq_of 'n' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private theorem docKeyVal_l23 :
    ∀ fuel r ap rt, parseDocumentFuel modelNumApi (fuel + 1) ('l' :: r) ap rt = docKeyValBody fuel ('l' :: r) ap rt :=
  docKeyVal_of 'l' (skipTriviaNewlines_eq_of 'l' (fun _ => rfl) (by decide) (by decide)) (fun _ _ _ _ => rfl)

private def dt2ValPos : TomlValue :=
  .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0),
                    offset := specOffset 19800 }

private def dt2ValNeg : TomlValue :=
  .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0 123456789),
                    offset := specOffset (-25200) }

private theorem cls_dt2Pos :
    classifyScalarToken modelNumApi "1979-05-27T07:32:00+05:30" = .ok dt2ValPos := by cbv

private theorem cls_dt2Neg :
    classifyScalarToken modelNumApi "1979-05-27T07:32:00.1234567899-07:00" = .ok dt2ValNeg := by cbv

private def dt2Str : String :=
  "pos = 1979-05-27T07:32:00+05:30\nneg = 1979-05-27T07:32:00.1234567899-07:00"

private theorem elem2_clean :
    (dt2Str.toList.all (fun c => !isDisallowedControl c && c != '\r')) = true := by cbv

private theorem dt2_hs_eq :
    dt2Str.toList =
      ("pos" ++ " = " ++ "1979-05-27T07:32:00+05:30").toList ++ '\n' ::
      ("neg" ++ " = " ++ "1979-05-27T07:32:00.1234567899-07:00").toList := by cbv

private def dt2R1 : List (String × Node) := [("pos", .leaf dt2ValPos)]
private def dt2R2 : List (String × Node) := dt2R1 ++ [("neg", .leaf dt2ValNeg)]

private theorem dt2_hi1 : insertAtActivePath ["pos"] [] [] ["pos"] (valueToInlineNode dt2ValPos) = .ok dt2R1 := by cbv
private theorem dt2_hi2 : insertAtActivePath ["neg"] dt2R1 [] ["neg"] (valueToInlineNode dt2ValNeg) = .ok dt2R2 := by cbv

private theorem elem2_beq :
    tomlValueBeq
      (.table #[("pos", dt2ValPos), ("neg", dt2ValNeg)])
      (.table (entriesToTomlList dt2R2).toArray) = true := by cbv

private theorem dt2_hdoc :
    parseDocumentFuel modelNumApi (dt2Str.toList.length + 1) dt2Str.toList [] [] = .ok dt2R2 := by
  have hlen : dt2Str.toList.length + 1 ≥ 2 := by
    rw [dt2_hs_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have hsplit : ∃ f, dt2Str.toList.length + 1 = (f + 1) + 1 :=
    ⟨dt2Str.toList.length + 1 - 2, by omega⟩
  rcases hsplit with ⟨f, hf⟩
  rw [hf, dt2_hs_eq]
  rw [parseDoc_step_nl_noSpace "pos" "1979-05-27T07:32:00+05:30" 'p' ['o', 's'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_p23 '1' ("979-05-27T07:32:00+05:30".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt2ValPos cls_dt2Pos [] [] dt2R1 dt2_hi1]
  exact parseDoc_step_eof_noSpace "neg" "1979-05-27T07:32:00.1234567899-07:00" 'n' ['e', 'g'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_n23 '1' ("979-05-27T07:32:00.1234567899-07:00".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt2ValNeg cls_dt2Neg [] dt2R1 dt2R2 dt2_hi2 f

private theorem elem2_valid :
    checkOneOkModel (dt2Str, #[("pos", dt2ValPos), ("neg", dt2ValNeg)]) = true := by
  have hnorm : normalizeChars 1 1 dt2Str.toList = .ok dt2Str.toList :=
    normalizeChars_clean _ elem2_clean 1 1
  simp only [checkOneOkModel, parseWithNum, hnorm, dt2_hdoc, bind, Except.bind]
  exact elem2_beq

private def dt3ValLdt : TomlValue :=
  .localDateTime (Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0 500000000))
private def dt3ValLd0 : TomlValue := .localDate (specDate 0 1 1)
private def dt3ValLeap : TomlValue := .localDate (specDate 2024 2 29)
private def dt3ValLdmax : TomlValue := .localDate (specDate 9999 12 31)
private def dt3ValLt : TomlValue := .localTime (specTime 23 59 59 999999999)

private theorem cls_dt3Ldt :
    classifyScalarToken modelNumApi "1979-05-27 07:32:00.5" = .ok dt3ValLdt := by cbv
private theorem cls_dt3Ld0 :
    classifyScalarToken modelNumApi "0000-01-01" = .ok dt3ValLd0 := by cbv
private theorem cls_dt3Leap :
    classifyScalarToken modelNumApi "2024-02-29" = .ok dt3ValLeap := by cbv
private theorem cls_dt3Ldmax :
    classifyScalarToken modelNumApi "9999-12-31" = .ok dt3ValLdmax := by cbv
private theorem cls_dt3Lt :
    classifyScalarToken modelNumApi "23:59:59.9999999999" = .ok dt3ValLt := by cbv

private theorem tok_ldt :
    ∀ rest, takeUnquotedToken ("1979-05-27 07:32:00.5".toList ++ '\n' :: rest) =
      ("1979-05-27 07:32:00.5", '\n' :: rest) := by
  intro rest
  have hs : "1979-05-27 07:32:00.5".toList =
      ['1', '9', '7', '9', '-', '0', '5', '-', '2', '7', ' ',
       '0', '7', ':', '3', '2', ':', '0', '0'] ++ ".5".toList := by cbv
  have hstr : String.ofList
      (['1', '9', '7', '9', '-', '0', '5', '-', '2', '7', ' ',
        '0', '7', ':', '3', '2', ':', '0', '0'] ++ ".5".toList) =
      "1979-05-27 07:32:00.5" := by cbv
  rw [hs]
  rw [takeUnquotedToken_spaceDateTime '1' '9' '7' '9' '0' '5' '2' '7' '0' '7' '3' '2' '0' '0'
    ".5".toList ('\n' :: rest)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by cbv) (fun _ _ h => by injection h with hc _; subst hc; decide)]
  rw [hstr]

private def dt3Str : String :=
  "ldt = 1979-05-27 07:32:00.5\nld0 = 0000-01-01\nleap = 2024-02-29\nldmax = 9999-12-31\nlt = 23:59:59.9999999999"

private theorem elem3_clean :
    (dt3Str.toList.all (fun c => !isDisallowedControl c && c != '\r')) = true := by cbv

private theorem dt3_hs_eq :
    dt3Str.toList =
      ("ldt" ++ " = " ++ "1979-05-27 07:32:00.5").toList ++ '\n' ::
      (("ld0" ++ " = " ++ "0000-01-01").toList ++ '\n' ::
      (("leap" ++ " = " ++ "2024-02-29").toList ++ '\n' ::
      (("ldmax" ++ " = " ++ "9999-12-31").toList ++ '\n' ::
      ("lt" ++ " = " ++ "23:59:59.9999999999").toList))) := by cbv

private def dt3R1 : List (String × Node) := [("ldt", .leaf dt3ValLdt)]
private def dt3R2 : List (String × Node) := dt3R1 ++ [("ld0", .leaf dt3ValLd0)]
private def dt3R3 : List (String × Node) := dt3R2 ++ [("leap", .leaf dt3ValLeap)]
private def dt3R4 : List (String × Node) := dt3R3 ++ [("ldmax", .leaf dt3ValLdmax)]
private def dt3R5 : List (String × Node) := dt3R4 ++ [("lt", .leaf dt3ValLt)]

private theorem dt3_hi1 : insertAtActivePath ["ldt"] [] [] ["ldt"] (valueToInlineNode dt3ValLdt) = .ok dt3R1 := by cbv
private theorem dt3_hi2 : insertAtActivePath ["ld0"] dt3R1 [] ["ld0"] (valueToInlineNode dt3ValLd0) = .ok dt3R2 := by cbv
private theorem dt3_hi3 : insertAtActivePath ["leap"] dt3R2 [] ["leap"] (valueToInlineNode dt3ValLeap) = .ok dt3R3 := by cbv
private theorem dt3_hi4 : insertAtActivePath ["ldmax"] dt3R3 [] ["ldmax"] (valueToInlineNode dt3ValLdmax) = .ok dt3R4 := by cbv
private theorem dt3_hi5 : insertAtActivePath ["lt"] dt3R4 [] ["lt"] (valueToInlineNode dt3ValLt) = .ok dt3R5 := by cbv

private theorem elem3_beq :
    tomlValueBeq
      (.table #[("ldt", dt3ValLdt), ("ld0", dt3ValLd0), ("leap", dt3ValLeap),
        ("ldmax", dt3ValLdmax), ("lt", dt3ValLt)])
      (.table (entriesToTomlList dt3R5).toArray) = true := by cbv

private theorem dt3_hdoc :
    parseDocumentFuel modelNumApi (dt3Str.toList.length + 1) dt3Str.toList [] [] = .ok dt3R5 := by
  have hlen : dt3Str.toList.length + 1 ≥ 5 := by
    rw [dt3_hs_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have hsplit : ∃ f, dt3Str.toList.length + 1 = ((((f + 1) + 1) + 1) + 1) + 1 :=
    ⟨dt3Str.toList.length + 1 - 5, by omega⟩
  rcases hsplit with ⟨f, hf⟩
  rw [hf, dt3_hs_eq]
  rw [parseDoc_step_nl_tok "ldt" "1979-05-27 07:32:00.5" 'l' ['d', 't'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_l23 '1' ("979-05-27 07:32:00.5".toList) (by cbv) (by decide) (fun _ _ => rfl)
    tok_ldt dt3ValLdt cls_dt3Ldt [] [] dt3R1 dt3_hi1]
  rw [parseDoc_step_nl_noSpace "ld0" "0000-01-01" 'l' ['d', '0'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_l23 '0' ("000-01-01".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt3ValLd0 cls_dt3Ld0 [] dt3R1 dt3R2 dt3_hi2]
  rw [parseDoc_step_nl_noSpace "leap" "2024-02-29" 'l' ['e', 'a', 'p'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_l23 '2' ("024-02-29".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt3ValLeap cls_dt3Leap [] dt3R2 dt3R3 dt3_hi3]
  rw [parseDoc_step_nl_noSpace "ldmax" "9999-12-31" 'l' ['d', 'm', 'a', 'x'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_l23 '9' ("999-12-31".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt3ValLdmax cls_dt3Ldmax [] dt3R3 dt3R4 dt3_hi4]
  exact parseDoc_step_eof_noSpace "lt" "23:59:59.9999999999" 'l' ['t'] (by cbv) (by cbv)
    (fun _ => rfl) docKeyVal_l23 '2' ("3:59:59.9999999999".toList) (by cbv) (by decide) (fun _ _ => rfl) (by cbv)
    dt3ValLt cls_dt3Lt [] dt3R4 dt3R5 dt3_hi5 f

private theorem elem3_valid :
    checkOneOkModel
      (dt3Str, #[("ldt", dt3ValLdt), ("ld0", dt3ValLd0), ("leap", dt3ValLeap),
        ("ldmax", dt3ValLdmax), ("lt", dt3ValLt)]) = true := by
  have hnorm : normalizeChars 1 1 dt3Str.toList = .ok dt3Str.toList :=
    normalizeChars_clean _ elem3_clean 1 1
  simp only [checkOneOkModel, parseWithNum, hnorm, dt3_hdoc, bind, Except.bind]
  exact elem3_beq

/-- Verify element 2 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_2 :
    ((numberDatetimeOkCases.drop 2).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  exact elem2_valid

/-- Verify element 3 of `numberDatetimeOkCases` under `modelNumApi`. -/
theorem numberDatetimeOk_3 :
    ((numberDatetimeOkCases.drop 3).head?.map checkOneOkModel).getD false = true := by
  simp only [numberDatetimeOkCases, List.drop_succ_cons, List.drop_zero, List.head?_cons,
    Option.map_some, Option.getD_some]
  exact elem3_valid

end LeanSwe.Toml.Proofs
