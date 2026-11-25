import Lean.Data.Json.Basic
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import LeanSwe.Json.Impl
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.Utf8Ws
import LeanSwe.Json.Proofs.StringSound
import LeanSwe.Json.Proofs.NumberParse

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Non-whitespace head property of `isDelimOrEof`. -/
theorem nonWsHead_of_delimOrEof (after : List Char) :
    isDelimOrEof after = true → (match after with | [] => True | c :: _ => isJsonWsChar c = false) := by
  intro h
  cases after with
  | nil => trivial
  | cons c _ =>
    simp only [isDelimOrEof, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | rfl) | rfl <;> rfl

/-- `skipWsSub` across a JSON whitespace prefix `wb` before a non-whitespace character `c`. -/
theorem skipWsSub_to_nonWs {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    {wb : String} (hwb : isJsonWs wb = true) {c : Char} (hc : isJsonWsChar c = false)
    (tail : List Char) (hSlice : ByteSliceAt bytes pos (wb.toList ++ c :: tail)) :
    let p := (skipWsSub bytes pos hPos).1
    p < bytes.size ∧ ByteSliceAt bytes p (c :: tail) := by
  have hsp := splitJsonWs_ws_append (ws := wb.toList) (rest := c :: tail) hwb hc
  obtain ⟨hpEq, _, _, hRestSlice⟩ := skipWsSub_spec (wb.toList ++ c :: tail) hPos hSlice
  rw [hsp] at hpEq hRestSlice
  exact ⟨byteSliceAt_cons_lt_size hRestSlice, hRestSlice⟩

/-- `parseAfterValue` absorbs any JSON whitespace prefix before a delimiter or EOF. -/
theorem parseAfterValue_ws_prefix {bytes : ByteArray} {pos1 : Nat} (h1 : pos1 ≤ bytes.size)
    {wa : String} (hwa : isJsonWs wa = true) {after : List Char} (hafter : isDelimOrEof after = true)
    (frames : List ParseFrame) (val : Lean.Json)
    (hSlice : ByteSliceAt bytes pos1 (wa.toList ++ after)) :
    ∃ (pos2 : Nat) (h2 : pos2 ≤ bytes.size),
      parseAfterValue bytes pos1 h1 frames val = parseAfterValue bytes pos2 h2 frames val ∧
      ByteSliceAt bytes pos2 after := by
  have hnw := nonWsHead_of_delimOrEof after hafter
  have hsp1 := splitJsonWs_ws_append (ws := wa.toList) (rest := after) hwa hnw
  have hSpec1 := skipWsSub_spec (wa.toList ++ after) h1 hSlice
  rw [hsp1] at hSpec1; dsimp only at hSpec1
  rcases hSpec1 with ⟨hp1, _, _, hAfterSlice⟩
  let pos2 := pos1 + wa.toList.length
  rw [hp1] at hAfterSlice
  have h2 : pos2 ≤ bytes.size := by have := byteSliceAt_size hAfterSlice; omega
  have hsp2 := splitJsonWs_ws_append (ws := []) (rest := after) rfl hnw
  rw [List.nil_append] at hsp2
  have hSpec2 := skipWsSub_spec after h2 hAfterSlice
  rw [hsp2] at hSpec2; dsimp only at hSpec2
  rcases hSpec2 with ⟨hp2, _, _, _⟩
  simp only [List.length_nil, Nat.add_zero] at hp2
  refine ⟨pos2, h2, ?_, hAfterSlice⟩
  unfold parseAfterValue
  rcases hSub1 : skipWsSub bytes pos1 h1 with ⟨pA, _, _⟩
  rcases hSub2 : skipWsSub bytes pos2 h2 with ⟨pB, _, _⟩
  rw [hSub1] at hp1; rw [hSub2] at hp2
  dsimp only at hp1 hp2 ⊢
  subst hp1; subst hp2; rfl

/-- `parseAfterValue` at EOF with empty frame stack returns `.ok val`. -/
theorem parseAfterValue_nil_eof {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (val : Lean.Json) (hSlice : ByteSliceAt bytes pos []) :
    parseAfterValue bytes pos hPos [] val = .ok val := by
  have heq := byteSliceAt_nil_eq_size hSlice
  obtain ⟨hp, _, _, _⟩ := skipWsSub_spec [] hPos hSlice
  dsimp only [splitJsonWs, List.length_nil] at hp
  rw [Nat.add_zero] at hp
  unfold parseAfterValue
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, _, _⟩
  rw [hSub] at hp; dsimp only at hp ⊢
  rcases hp with rfl
  simp [heq]

/-- Soundness of `parseWantValue` on `RenderTape.null`. -/
theorem parseWantValue_null {wb wa : String} {j : Lean.Json} {seg : String} (after : List Char)
    {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) (frames : List ParseFrame)
    (hr : renderVal j (.null wb wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal] at hr
  rcases hr with ⟨⟨hwb, hwa⟩, rfl⟩
  simp only [String.toList_append, List.append_assoc] at hSlice
  change ByteSliceAt bytes pos (wb.toList ++ ('n' :: 'u' :: 'l' :: 'l' :: (wa.toList ++ after))) at hSlice
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgP, _⟩ := byteSliceAt_ascii_cons hsP (by decide)
  have hkw : matchesKeyword bytes p kwNull = true :=
    (matchesKeyword_ascii_spec ['n', 'u', 'l', 'l'] (by decide) hsP).mpr
      ⟨wa.toList ++ after, rfl, byteSliceAt_append_chars (mid := ['n', 'u', 'l', 'l']) hsP⟩
  have hsEnd : ByteSliceAt bytes (p + 4) (wa.toList ++ after) :=
    byteSliceAt_append_chars (mid := ['n', 'u', 'l', 'l']) hsP
  have hEnd : p + 4 ≤ bytes.size := by have := byteSliceAt_size hsEnd; omega
  obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
    parseAfterValue_ws_prefix hEnd hwa hafter frames .null hsEnd
  refine ⟨.null, afterPos, hAfterPos, ?_, by simp [JsonEquiv], by simp [wellFormedJsonBool], hAfterSlice⟩
  conv => lhs; unfold parseWantValue
  rw [hSub]; dsimp only
  have hbN : ('n').val.toUInt8 = 0x6e := rfl
  simp only [hltP, hEnd, ↓reduceDIte, hgP, hbN,
    (by decide : ((0x6e : UInt8) == 0x5b) = false), (by decide : ((0x6e : UInt8) == 0x7b) = false),
    (by decide : ((0x6e : UInt8) == 0x22) = false), (by decide : ((0x6e : UInt8) == 0x74) = false),
    (by decide : ((0x6e : UInt8) == 0x66) = false), (by decide : ((0x6e : UInt8) == 0x6e) = true),
    Bool.false_eq_true, ↓reduceIte, hkw, hAfterEq]

/-- Soundness of `parseWantValue` on `RenderTape.bool`. -/
theorem parseWantValue_bool {wb wa : String} {j : Lean.Json} {seg : String} (after : List Char)
    {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) (frames : List ParseFrame)
    (hr : renderVal j (.bool wb wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal] at hr
  rename_i b
  rcases hr with ⟨⟨hwb, hwa⟩, rfl⟩
  cases b with
  | true =>
    simp only [↓reduceIte, String.toList_append, List.append_assoc] at hSlice
    change ByteSliceAt bytes pos (wb.toList ++ ('t' :: 'r' :: 'u' :: 'e' :: (wa.toList ++ after))) at hSlice
    obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
    rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
    rw [hSub] at hltP hsP; dsimp only at hltP hsP
    obtain ⟨_, hgP, _⟩ := byteSliceAt_ascii_cons hsP (by decide)
    have hkw : matchesKeyword bytes p kwTrue = true :=
      (matchesKeyword_ascii_spec ['t', 'r', 'u', 'e'] (by decide) hsP).mpr
        ⟨wa.toList ++ after, rfl, byteSliceAt_append_chars (mid := ['t', 'r', 'u', 'e']) hsP⟩
    have hsEnd : ByteSliceAt bytes (p + 4) (wa.toList ++ after) :=
      byteSliceAt_append_chars (mid := ['t', 'r', 'u', 'e']) hsP
    have hEnd : p + 4 ≤ bytes.size := by have := byteSliceAt_size hsEnd; omega
    obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
      parseAfterValue_ws_prefix hEnd hwa hafter frames (.bool true) hsEnd
    refine ⟨.bool true, afterPos, hAfterPos, ?_, by simp [JsonEquiv], by simp [wellFormedJsonBool], hAfterSlice⟩
    conv => lhs; unfold parseWantValue
    rw [hSub]; dsimp only
    have hbT : ('t').val.toUInt8 = 0x74 := rfl
    simp only [hltP, hEnd, ↓reduceDIte, hgP, hbT,
      (by decide : ((0x74 : UInt8) == 0x5b) = false), (by decide : ((0x74 : UInt8) == 0x7b) = false),
      (by decide : ((0x74 : UInt8) == 0x22) = false), (by decide : ((0x74 : UInt8) == 0x74) = true),
      Bool.false_eq_true, ↓reduceIte, hkw, hAfterEq]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append, List.append_assoc] at hSlice
    change ByteSliceAt bytes pos (wb.toList ++ ('f' :: 'a' :: 'l' :: 's' :: 'e' :: (wa.toList ++ after))) at hSlice
    obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
    rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
    rw [hSub] at hltP hsP; dsimp only at hltP hsP
    obtain ⟨_, hgP, _⟩ := byteSliceAt_ascii_cons hsP (by decide)
    have hkw : matchesKeyword bytes p kwFalse = true :=
      (matchesKeyword_ascii_spec ['f', 'a', 'l', 's', 'e'] (by decide) hsP).mpr
        ⟨wa.toList ++ after, rfl, byteSliceAt_append_chars (mid := ['f', 'a', 'l', 's', 'e']) hsP⟩
    have hsEnd : ByteSliceAt bytes (p + 5) (wa.toList ++ after) :=
      byteSliceAt_append_chars (mid := ['f', 'a', 'l', 's', 'e']) hsP
    have hEnd : p + 5 ≤ bytes.size := by have := byteSliceAt_size hsEnd; omega
    obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
      parseAfterValue_ws_prefix hEnd hwa hafter frames (.bool false) hsEnd
    refine ⟨.bool false, afterPos, hAfterPos, ?_, by simp [JsonEquiv], by simp [wellFormedJsonBool], hAfterSlice⟩
    conv => lhs; unfold parseWantValue
    rw [hSub]; dsimp only
    have hbF : ('f').val.toUInt8 = 0x66 := rfl
    simp only [hltP, hEnd, ↓reduceDIte, hgP, hbF,
      (by decide : ((0x66 : UInt8) == 0x5b) = false), (by decide : ((0x66 : UInt8) == 0x7b) = false),
      (by decide : ((0x66 : UInt8) == 0x22) = false), (by decide : ((0x66 : UInt8) == 0x74) = false),
      (by decide : ((0x66 : UInt8) == 0x66) = true), Bool.false_eq_true, ↓reduceIte, hkw, hAfterEq]

/-- Soundness of `parseWantValue` on `RenderTape.num`. -/
theorem parseWantValue_num {wb : String} {nt : NumTape} {wa : String} {j : Lean.Json}
    {seg : String} (after : List Char) {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (frames : List ParseFrame) (hLim : numTapeWithinLimits nt = true)
    (hr : renderVal j (.num wb nt wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal, renderNum] at hr
  rename_i n
  rcases hr with ⟨⟨hwb, hwa⟩, ⟨hvnt, heqv⟩, rfl⟩
  have hStopWa : isNumStop (wa.toList ++ after) = true := by
    cases hwaL : wa.toList with
    | nil =>
      simp only [List.nil_append]
      cases after with
      | nil => rfl
      | cons c _ =>
        simp only [isDelimOrEof, Bool.or_eq_true, beq_iff_eq] at hafter
        rcases hafter with (rfl | rfl) | rfl <;> rfl
    | cons c _ =>
      have hcWs : isJsonWsChar c = true := by
        have hwAll : wa.toList.all isJsonWsChar = true := hwa
        rw [hwaL, List.all_cons, Bool.and_eq_true] at hwAll; exact hwAll.1
      simp only [List.cons_append, isJsonWsChar, Bool.or_eq_true, beq_iff_eq] at hcWs ⊢
      rcases hcWs with ((rfl | rfl) | rfl) | rfl <;> rfl
  simp only [String.toList_append, List.append_assoc] at hSlice
  have hNumHead : ∃ c0 ntl, (renderNumTape nt).toList = c0 :: ntl ∧
      isJsonWsChar c0 = false ∧ c0.toNat < 0x80 ∧
      (c0.val.toUInt8 == 0x5b) = false ∧ (c0.val.toUInt8 == 0x7b) = false ∧
      (c0.val.toUInt8 == 0x22) = false ∧ (c0.val.toUInt8 == 0x74) = false ∧
      (c0.val.toUInt8 == 0x66) = false ∧ (c0.val.toUInt8 == 0x6e) = false ∧
      (c0.val.toUInt8 == 0x2d || (0x30 ≤ c0.val.toUInt8 && c0.val.toUInt8 ≤ 0x39)) = true := by
    cases hm : nt.minus with
    | true =>
      refine ⟨'-', _, by simp only [renderNumTape, hm, ↓reduceIte, show "-".toList = ['-'] from rfl,
        String.toList_append, List.cons_append, List.nil_append, List.append_assoc]; rfl,
        rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | false =>
      obtain ⟨hwNe, hwAll, _⟩ := repr_nat_props nt.whole
      cases hw : nt.whole.repr.toList with
      | nil => exact absurd hw hwNe
      | cons d dtl =>
        rw [hw, List.all_cons, Bool.and_eq_true] at hwAll
        have hdDig : isAsciiDigit d = true := hwAll.1
        have hdBnd : 0x30 ≤ d.toNat ∧ d.toNat ≤ 0x39 := by
          simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hdDig
          exact hdDig
        have htoNat : d.val.toUInt8.toNat = d.toNat := by
          rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change d.toNat < 256; omega)
        have hNeByte : ∀ (k : UInt8), (k.toNat < 48 ∨ 57 < k.toNat) → (d.val.toUInt8 == k) = false := by
          intro k hk
          apply Bool.eq_false_iff.mpr
          rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat]
          change 48 ≤ d.toNat ∧ d.toNat ≤ 57 at hdBnd
          omega
        have hdBnd8 : (0x30 : UInt8) ≤ d.val.toUInt8 ∧ d.val.toUInt8 ≤ 0x39 := by
          rw [UInt8.le_iff_toNat_le, UInt8.le_iff_toNat_le, htoNat]; exact hdBnd
        refine ⟨d, _, by simp only [renderNumTape, hm, Bool.false_eq_true, ↓reduceIte, String.empty_append,
          String.toList_append, List.append_assoc, List.cons_append, hw]; rfl,
          ?_, by omega,
          hNeByte 0x5b (Or.inr (by decide)), hNeByte 0x7b (Or.inr (by decide)),
          hNeByte 0x22 (Or.inl (by decide)), hNeByte 0x74 (Or.inr (by decide)),
          hNeByte 0x66 (Or.inr (by decide)), hNeByte 0x6e (Or.inr (by decide)),
          by rw [Bool.or_eq_true, Bool.and_eq_true]; exact Or.inr ⟨decide_eq_true hdBnd8.1, decide_eq_true hdBnd8.2⟩⟩
        cases hws : isJsonWsChar d
        · rfl
        · simp only [isJsonWsChar, Bool.or_eq_true, beq_iff_eq] at hws
          rcases hws with ((rfl | rfl) | rfl) | rfl <;> simp at hdBnd
  obtain ⟨c0, ntl, hnEq, hc0NotWs, hc0A, h5b, h7b, h22, h74, h66, h6e, hNumB⟩ := hNumHead
  have hSlice2 : ByteSliceAt bytes pos (wb.toList ++ (c0 :: (ntl ++ (wa.toList ++ after)))) := by
    simpa [hnEq] using hSlice
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb hc0NotWs _ hSlice2
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgP, _⟩ := byteSliceAt_ascii_cons hsP hc0A
  have hsP' : ByteSliceAt bytes p ((renderNumTape nt).toList ++ (wa.toList ++ after)) := by
    simpa [hnEq] using hsP
  obtain ⟨pSub, hNumOk, hsAfterNum⟩ := parseNumberAt_of_renderNumTape (wa.toList ++ after) hvnt hLim hStopWa hsP'
  obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
    parseAfterValue_ws_prefix pSub.2.2 hwa hafter frames (.num (evalNumTape nt)) hsAfterNum
  refine ⟨.num (evalNumTape nt), afterPos, hAfterPos, ?_,
    by simp [JsonEquiv, (numEquivBool_iff n (evalNumTape nt)).mp heqv], by simp [wellFormedJsonBool], hAfterSlice⟩
  conv => lhs; unfold parseWantValue
  rw [hSub]; dsimp only
  rcases pSub with ⟨p1, hp1a, hp1b⟩
  simp only [hltP, ↓reduceDIte, hgP, h5b, h7b, h22, h74, h66, h6e, hNumB,
    Bool.false_eq_true, ↓reduceIte, hNumOk, hAfterEq]

/-- Soundness of `parseWantValue` on `RenderTape.str`. -/
theorem parseWantValue_str {wb : String} {st : List CharEscapeStyle} {wa : String}
    {j : Lean.Json} {seg : String} (after : List Char) {bytes : ByteArray} {pos : Nat}
    (hPos : pos ≤ bytes.size) (frames : List ParseFrame)
    (hr : renderVal j (.str wb st wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal] at hr
  rename_i s
  rcases hr with ⟨⟨hwb, hwa⟩, lit, hlit, rfl⟩
  have hQuote : ∃ body, lit.toList = '"' :: body := by
    simp only [renderStringLiteral, bind, Option.bind] at hlit
    cases hb : renderStringChars s.toList st <;> rw [hb] at hlit <;> simp at hlit
    subst hlit; exact ⟨_, by simp [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl]; rfl⟩
  obtain ⟨body, hbody⟩ := hQuote
  simp only [String.toList_append, List.append_assoc] at hSlice
  have hSlice2 : ByteSliceAt bytes pos (wb.toList ++ ('"' :: (body ++ (wa.toList ++ after)))) := by
    simpa [hbody] using hSlice
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice2
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgP, _⟩ := byteSliceAt_ascii_cons hsP (by decide)
  have hsP' : ByteSliceAt bytes p (lit.toList ++ (wa.toList ++ after)) := by
    simpa [hbody] using hsP
  obtain ⟨pSub, hStrOk, hsAfterStr⟩ := parseStringAt_of_renderStringLiteral (wa.toList ++ after) hlit hsP'
  obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
    parseAfterValue_ws_prefix pSub.2.2 hwa hafter frames (.str s) hsAfterStr
  refine ⟨.str s, afterPos, hAfterPos, ?_, by simp [JsonEquiv], by simp [wellFormedJsonBool], hAfterSlice⟩
  conv => lhs; unfold parseWantValue
  rw [hSub]; dsimp only
  rcases pSub with ⟨p1, hp1a, hp1b⟩
  have hbQ : ('"').val.toUInt8 = 0x22 := rfl
  simp only [hltP, ↓reduceDIte, hgP, hbQ,
    (by decide : ((0x22 : UInt8) == 0x5b) = false), (by decide : ((0x22 : UInt8) == 0x7b) = false),
    (by decide : ((0x22 : UInt8) == 0x22) = true), Bool.false_eq_true, ↓reduceIte, hStrOk, hAfterEq]

/-- Soundness of `parseWantValue` on `RenderTape.emptyArr`. -/
theorem parseWantValue_emptyArr {wb wi wa : String} {j : Lean.Json} {seg : String} (after : List Char)
    {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) (frames : List ParseFrame)
    (hr : renderVal j (.emptyArr wb wi wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal] at hr
  simp only [and_assoc] at hr
  rcases hr with ⟨hempty, hwb, hwi, hwa, rfl⟩
  subst hempty
  simp only [String.toList_append, List.append_assoc] at hSlice
  change ByteSliceAt bytes pos (wb.toList ++ ('[' :: (wi.toList ++ (']' :: (wa.toList ++ after))))) at hSlice
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgP, hsAfterOpen⟩ := byteSliceAt_ascii_cons hsP (by decide)
  obtain ⟨hltP1, hsP1⟩ := skipWsSub_to_nonWs hltP hwi rfl _ hsAfterOpen
  rcases hSub1 : skipWsSub bytes (p + 1) hltP with ⟨p1, hp1Ge, hp1Le⟩
  rw [hSub1] at hltP1 hsP1; dsimp only at hltP1 hsP1
  obtain ⟨_, hgP1, hsAfterClose⟩ := byteSliceAt_ascii_cons hsP1 (by decide)
  obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
    parseAfterValue_ws_prefix hltP1 hwa hafter frames (.arr #[]) hsAfterClose
  refine ⟨.arr #[], afterPos, hAfterPos, ?_, by simp [JsonEquiv, JsonListEquiv],
    by simp [wellFormedJsonBool, wellFormedJsonListBool], hAfterSlice⟩
  conv => lhs; unfold parseWantValue
  rw [hSub]; dsimp only
  have hbOpen : ('[').val.toUInt8 = 0x5b := rfl
  have hbClose : (']').val.toUInt8 = 0x5d := rfl
  simp only [hltP, ↓reduceDIte, hgP, hbOpen, beq_self_eq_true, ↓reduceIte]
  rw [hSub1]; dsimp only
  simp only [hltP1, ↓reduceDIte, hgP1, hbClose, beq_self_eq_true, ↓reduceIte, hAfterEq]

/-- Soundness of `parseWantValue` on `RenderTape.emptyObj`. -/
theorem parseWantValue_emptyObj {wb wi wa : String} {j : Lean.Json} {seg : String} (after : List Char)
    {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) (frames : List ParseFrame)
    (hr : renderVal j (.emptyObj wb wi wa) = some seg) (hafter : isDelimOrEof after = true)
    (hSlice : ByteSliceAt bytes pos (seg.toList ++ after)) :
    ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
      JsonEquiv j outVal ∧ wellFormedJsonBool outVal = true ∧ ByteSliceAt bytes afterPos after := by
  cases j <;> simp [renderVal] at hr
  rename_i kvs
  simp only [and_assoc] at hr
  rcases hr with ⟨hnil, hwb, hwi, hwa, rfl⟩
  have hEmptyEntries : objEntries (∅ : Std.TreeMap.Raw String Lean.Json compare) = [] := rfl
  simp only [String.toList_append, List.append_assoc] at hSlice
  change ByteSliceAt bytes pos (wb.toList ++ ('{' :: (wi.toList ++ ('}' :: (wa.toList ++ after))))) at hSlice
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgP, hsAfterOpen⟩ := byteSliceAt_ascii_cons hsP (by decide)
  obtain ⟨hltP1, hsP1⟩ := skipWsSub_to_nonWs hltP hwi rfl _ hsAfterOpen
  rcases hSub1 : skipWsSub bytes (p + 1) hltP with ⟨p1, hp1Ge, hp1Le⟩
  rw [hSub1] at hltP1 hsP1; dsimp only at hltP1 hsP1
  obtain ⟨_, hgP1, hsAfterClose⟩ := byteSliceAt_ascii_cons hsP1 (by decide)
  obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
    parseAfterValue_ws_prefix hltP1 hwa hafter frames (.obj ∅) hsAfterClose
  refine ⟨.obj ∅, afterPos, hAfterPos, ?_, ?_, ?_, hAfterSlice⟩
  · conv => lhs; unfold parseWantValue
    rw [hSub]; dsimp only
    have hbOpen : ('{').val.toUInt8 = 0x7b := rfl
    have hbClose : ('}').val.toUInt8 = 0x7d := rfl
    simp only [hltP, ↓reduceDIte, hgP, hbOpen,
      (by decide : ((0x7b : UInt8) == 0x5b) = false), beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    rw [hSub1]; dsimp only
    simp only [hltP1, ↓reduceDIte, hgP1, hbClose, beq_self_eq_true, ↓reduceIte, hAfterEq]
  · simp [JsonEquiv, JsonObjEquivList, hnil, hEmptyEntries, lookupKeyList]
  · have hLeaf : (∅ : Std.TreeMap.Raw String Lean.Json compare).inner.inner = .leaf := rfl
    simp [wellFormedJsonBool, hLeaf, wellFormedJsonTreeBool, objEntries, treeEntries, isStrictlySortedKeys]

/-- Step `parseAfterValue` across `']'` closing an array frame. -/
theorem parseAfterValue_arr_close {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (acc : Array Lean.Json) (frames : List ParseFrame) (v : Lean.Json) (rest : List Char)
    (hSlice : ByteSliceAt bytes pos (']' :: rest)) :
    ∃ (hLt : pos < bytes.size),
      parseAfterValue bytes pos hPos (.arr acc :: frames) v =
        parseAfterValue bytes (pos + 1) hLt frames (.arr (acc.push v)) ∧
      ByteSliceAt bytes (pos + 1) rest := by
  have hSpec := skipWsSub_spec (']' :: rest) hPos hSlice
  rw [show splitJsonWs (']' :: rest) = ([], ']' :: rest) from rfl] at hSpec
  dsimp only [List.length_nil] at hSpec
  rcases hSpec with ⟨hpEq, _, _, _⟩
  rw [Nat.add_zero] at hpEq
  obtain ⟨hLt, hg, hsNext⟩ := byteSliceAt_ascii_cons hSlice (by decide)
  refine ⟨hLt, ?_, hsNext⟩
  conv => lhs; unfold parseAfterValue
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, _, _⟩
  rw [hSub] at hpEq; dsimp only at hpEq ⊢; rcases hpEq with rfl
  simp [hLt, hg]

/-- Step `parseAfterValue` across `','` continuing an array frame. -/
theorem parseAfterValue_arr_comma {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (acc : Array Lean.Json) (frames : List ParseFrame) (v : Lean.Json) (rest : List Char)
    (hSlice : ByteSliceAt bytes pos (',' :: rest)) :
    ∃ (hLt : pos < bytes.size),
      parseAfterValue bytes pos hPos (.arr acc :: frames) v =
        parseWantValue bytes (pos + 1) hLt (.arr (acc.push v) :: frames) ∧
      ByteSliceAt bytes (pos + 1) rest := by
  have hSpec := skipWsSub_spec (',' :: rest) hPos hSlice
  rw [show splitJsonWs (',' :: rest) = ([], ',' :: rest) from rfl] at hSpec
  dsimp only [List.length_nil] at hSpec
  rcases hSpec with ⟨hpEq, _, _, _⟩
  rw [Nat.add_zero] at hpEq
  obtain ⟨hLt, hg, hsNext⟩ := byteSliceAt_ascii_cons hSlice (by decide)
  refine ⟨hLt, ?_, hsNext⟩
  conv => lhs; unfold parseAfterValue
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, _, _⟩
  rw [hSub] at hpEq; dsimp only at hpEq ⊢; rcases hpEq with rfl
  simp [hLt, hg]

/-- Step `parseAfterValue` across `'}'` closing an object frame. -/
theorem parseAfterValue_obj_close {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (kvs : Std.TreeMap.Raw String Lean.Json compare) (key : String)
    (frames : List ParseFrame) (v : Lean.Json) (rest : List Char)
    (hSlice : ByteSliceAt bytes pos ('}' :: rest)) :
    ∃ (hLt : pos < bytes.size),
      parseAfterValue bytes pos hPos (.obj kvs key :: frames) v =
        parseAfterValue bytes (pos + 1) hLt frames (.obj (kvs.insert key v)) ∧
      ByteSliceAt bytes (pos + 1) rest := by
  have hSpec := skipWsSub_spec ('}' :: rest) hPos hSlice
  rw [show splitJsonWs ('}' :: rest) = ([], '}' :: rest) from rfl] at hSpec
  dsimp only [List.length_nil] at hSpec
  rcases hSpec with ⟨hpEq, _, _, _⟩
  rw [Nat.add_zero] at hpEq
  obtain ⟨hLt, hg, hsNext⟩ := byteSliceAt_ascii_cons hSlice (by decide)
  refine ⟨hLt, ?_, hsNext⟩
  conv => lhs; unfold parseAfterValue
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, _, _⟩
  rw [hSub] at hpEq; dsimp only at hpEq ⊢; rcases hpEq with rfl
  simp [hLt, hg]

/-- Step `parseAfterValue` across `','` and the next object member header `kt1.wsBeforeKey ++ rk1 ++ kt1.wsBeforeColon ++ ":"`. -/
theorem parseAfterValue_obj_comma {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (kvs : Std.TreeMap.Raw String Lean.Json compare) (key : String)
    (frames : List ParseFrame) (v : Lean.Json)
    (kt1 : ObjKeyTape) {rk1 : String} (valRest : List Char)
    (hwsK1 : isJsonWs kt1.wsBeforeKey = true) (hwsC1 : isJsonWs kt1.wsBeforeColon = true)
    (hrk1 : renderStringLiteral kt1.key kt1.keyChars = some rk1)
    (hNotMem : (kvs.insert key v).contains kt1.key = false)
    (hSlice : ByteSliceAt bytes pos
      (',' :: (kt1.wsBeforeKey.toList ++ (rk1.toList ++ (kt1.wsBeforeColon.toList ++ (':' :: valRest)))))) :
    ∃ (valPos : Nat) (hValPos : valPos ≤ bytes.size),
      parseAfterValue bytes pos hPos (.obj kvs key :: frames) v =
        parseWantValue bytes valPos hValPos (.obj (kvs.insert key v) kt1.key :: frames) ∧
      ByteSliceAt bytes valPos valRest := by
  have hSpec := skipWsSub_spec _ hPos hSlice
  rw [show splitJsonWs (',' :: (kt1.wsBeforeKey.toList ++ (rk1.toList ++ (kt1.wsBeforeColon.toList ++ (':' :: valRest))))) =
    ([], ',' :: (kt1.wsBeforeKey.toList ++ (rk1.toList ++ (kt1.wsBeforeColon.toList ++ (':' :: valRest))))) from rfl] at hSpec
  dsimp only [List.length_nil] at hSpec
  rcases hSpec with ⟨hpEq, _, _, _⟩
  rw [Nat.add_zero] at hpEq
  obtain ⟨hLt, hgComma, hsAfterComma⟩ := byteSliceAt_ascii_cons hSlice (by decide)
  have hQuote1 : ∃ body1, rk1.toList = '"' :: body1 := by
    simp only [renderStringLiteral, bind, Option.bind] at hrk1
    cases hb : renderStringChars kt1.key.toList kt1.keyChars <;> simp [hb] at hrk1
    subst hrk1; exact ⟨_, by simp [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl]; rfl⟩
  obtain ⟨body1, hbody1⟩ := hQuote1
  have hsAfterComma' : ByteSliceAt bytes (pos + 1)
      (kt1.wsBeforeKey.toList ++ ('"' :: (body1 ++ (kt1.wsBeforeColon.toList ++ (':' :: valRest))))) := by
    simpa [hbody1] using hsAfterComma
  obtain ⟨hltP1, hsP1⟩ := skipWsSub_to_nonWs hLt hwsK1 rfl _ hsAfterComma'
  rcases hSub1 : skipWsSub bytes (pos + 1) hLt with ⟨p1, hp1Ge, hp1Le⟩
  rw [hSub1] at hltP1 hsP1; dsimp only at hltP1 hsP1
  have hsP1' : ByteSliceAt bytes p1
      (rk1.toList ++ (kt1.wsBeforeColon.toList ++ (':' :: valRest))) := by
    simpa [hbody1] using hsP1
  obtain ⟨⟨p2, hp2a, hp2b⟩, hKey1Ok, hsP2⟩ := parseStringAt_of_renderStringLiteral _ hrk1 hsP1'
  dsimp only at hsP2
  obtain ⟨hltP3, hsP3⟩ := skipWsSub_to_nonWs hp2b hwsC1 rfl _ hsP2
  rcases hSub3 : skipWsSub bytes p2 hp2b with ⟨p3, hp3Ge, hp3Le⟩
  rw [hSub3] at hltP3 hsP3; dsimp only at hltP3 hsP3
  obtain ⟨_, hgCol, hsVal1⟩ := byteSliceAt_ascii_cons hsP3 (by decide)
  refine ⟨p3 + 1, hltP3, ?_, hsVal1⟩
  conv => lhs; unfold parseAfterValue
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, _, _⟩
  rw [hSub] at hpEq; dsimp only at hpEq ⊢; rcases hpEq with rfl
  have hbComma : (',').val.toUInt8 = 0x2c := rfl
  simp only [hLt, ↓reduceDIte, hgComma, hbComma,
    (by decide : ((0x2c : UInt8) == 0x7d) = false), beq_self_eq_true, ↓reduceIte]
  rw [hSub1]; dsimp only
  simp only [hKey1Ok, hNotMem, Bool.false_eq_true, ↓reduceIte]
  rw [hSub3]; dsimp only
  simp [hltP3, hgCol]

/-- Step `parseWantValue` across `'{'` and the first object member header `kt0.wsBeforeKey ++ rk0 ++ kt0.wsBeforeColon ++ ":"`. -/
theorem parseWantValue_obj_open {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
    (frames : List ParseFrame) {wb : String} (hwb : isJsonWs wb = true)
    (kt0 : ObjKeyTape) {rk0 : String} (valRest : List Char)
    (hwsK0 : isJsonWs kt0.wsBeforeKey = true) (hwsC0 : isJsonWs kt0.wsBeforeColon = true)
    (hrk0 : renderStringLiteral kt0.key kt0.keyChars = some rk0)
    (hSlice : ByteSliceAt bytes pos
      (wb.toList ++ ('{' :: (kt0.wsBeforeKey.toList ++ (rk0.toList ++ (kt0.wsBeforeColon.toList ++ (':' :: valRest))))))) :
    ∃ (valPos : Nat) (hValPos : valPos ≤ bytes.size),
      parseWantValue bytes pos hPos frames =
        parseWantValue bytes valPos hValPos (.obj ∅ kt0.key :: frames) ∧
      ByteSliceAt bytes valPos valRest := by
  obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
  rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
  rw [hSub] at hltP hsP; dsimp only at hltP hsP
  obtain ⟨_, hgOpen, hsAfterOpen⟩ := byteSliceAt_ascii_cons hsP (by decide)
  have hQuote0 : ∃ body0, rk0.toList = '"' :: body0 := by
    simp only [renderStringLiteral, bind, Option.bind] at hrk0
    cases hb : renderStringChars kt0.key.toList kt0.keyChars <;> simp [hb] at hrk0
    subst hrk0; exact ⟨_, by simp [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl]; rfl⟩
  obtain ⟨body0, hbody0⟩ := hQuote0
  have hsAfterOpen' : ByteSliceAt bytes (p + 1)
      (kt0.wsBeforeKey.toList ++ ('"' :: (body0 ++ (kt0.wsBeforeColon.toList ++ (':' :: valRest))))) := by
    simpa [hbody0] using hsAfterOpen
  obtain ⟨hltP1, hsP1⟩ := skipWsSub_to_nonWs hltP hwsK0 rfl _ hsAfterOpen'
  rcases hSub1 : skipWsSub bytes (p + 1) hltP with ⟨p1, hp1Ge, hp1Le⟩
  rw [hSub1] at hltP1 hsP1; dsimp only at hltP1 hsP1
  obtain ⟨_, hgQ0, _⟩ := byteSliceAt_ascii_cons hsP1 (by decide)
  have hsP1' : ByteSliceAt bytes p1
      (rk0.toList ++ (kt0.wsBeforeColon.toList ++ (':' :: valRest))) := by
    simpa [hbody0] using hsP1
  obtain ⟨⟨p2, hp2a, hp2b⟩, hKey0Ok, hsP2⟩ := parseStringAt_of_renderStringLiteral _ hrk0 hsP1'
  dsimp only at hsP2
  obtain ⟨hltP3, hsP3⟩ := skipWsSub_to_nonWs hp2b hwsC0 rfl _ hsP2
  rcases hSub3 : skipWsSub bytes p2 hp2b with ⟨p3, hp3Ge, hp3Le⟩
  rw [hSub3] at hltP3 hsP3; dsimp only at hltP3 hsP3
  obtain ⟨_, hgCol, hsVal0⟩ := byteSliceAt_ascii_cons hsP3 (by decide)
  refine ⟨p3 + 1, hltP3, ?_, hsVal0⟩
  conv => lhs; unfold parseWantValue
  rw [hSub]; dsimp only
  have hbOpen : ('{').val.toUInt8 = 0x7b := rfl
  have hbQ : ('"').val.toUInt8 = 0x22 := rfl
  simp only [hltP, ↓reduceDIte, hgOpen, hbOpen,
    (by decide : ((0x7b : UInt8) == 0x5b) = false), beq_self_eq_true, ↓reduceIte]
  rw [hSub1]; dsimp only
  simp only [hltP1, ↓reduceDIte, hgQ0, hbQ,
    (by decide : ((0x22 : UInt8) == 0x7d) = false), Bool.false_eq_true, ↓reduceIte, hKey0Ok]
  rw [hSub3]; dsimp only
  simp [hltP3, hgCol]

end LeanSwe.Json.Proofs
