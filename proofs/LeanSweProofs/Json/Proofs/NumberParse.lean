import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex
import LeanSweProofs.Json.Proofs.Utf8Ws
import LeanSweProofs.Json.Proofs.DigitsScan

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Any list of ASCII decimal digits has UTF-8 byte length equal to its character length. -/
theorem utf8Encode_size_of_digits {ds : List Char} (hds : ds.all isAsciiDigit = true) :
    ds.utf8Encode.size = ds.length := by
  induction ds with
  | nil => simp [List.utf8Encode_nil, ByteArray.size_empty]
  | cons d tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    have hc1 : d.utf8Size = 1 := by
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hds
      change (0x30 ≤ d.toNat ∧ d.toNat ≤ 0x39) ∧ _ at hds
      simp only [Char.utf8Size]
      have hle : d.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change d.toNat ≤ 0x7f; omega
      simp [hle]
    rw [List.utf8Encode_cons, ByteArray.size_append, List.utf8Encode_singleton,
      List.size_toByteArray, String.length_utf8EncodeChar, hc1, ih hds.2]
    simp [Nat.add_comm]

/-- `spanDigits cs` produces an all-digit prefix whose length is bounded by `bytes.size - pos`. -/
theorem spanDigits_props {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (hSlice : ByteSliceAt bytes pos cs) :
    let (ds, rest) := spanDigits cs
    cs = ds ++ rest ∧ ds.all isAsciiDigit = true ∧ notDigitHead rest = true ∧
      pos + ds.length ≤ bytes.size := by
  have h1 : ∀ l : List Char,
      l = (spanDigits l).1 ++ (spanDigits l).2 ∧
        (spanDigits l).1.all isAsciiDigit = true ∧ notDigitHead (spanDigits l).2 = true := by
    intro l
    induction l with
    | nil => simp [spanDigits, notDigitHead]
    | cons c tl ih =>
      by_cases hd : isAsciiDigit c = true
      · simp only [spanDigits, hd, ↓reduceIte]
        exact ⟨by rw [List.cons_append, ← ih.1], by simp [hd, ih.2.1], ih.2.2⟩
      · simp only [Bool.not_eq_true] at hd
        simp [spanDigits, hd, notDigitHead]
  rcases hsp : spanDigits cs with ⟨ds, rest⟩
  have h1c := h1 cs; rw [hsp] at h1c; dsimp only at h1c
  rcases h1c with ⟨heq, hall, hnd⟩
  have hs := byteSliceAt_size hSlice
  rw [heq, List.utf8Encode_append, ByteArray.size_append, utf8Encode_size_of_digits hall] at hs
  exact ⟨heq, hall, hnd, by omega⟩

/-- Wrapper lemma for `scanDigits` on integer tails (`initCount = 1, limitCount = bytes.size, hasValCap = false`). -/
theorem scanDigits_intTail_spec {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (hPos : pos ≤ bytes.size) (hPosGe1 : 1 ≤ pos) (d0 : Nat) (hd0 : d0 < 10)
    (hSlice : ByteSliceAt bytes pos cs) :
    let (ds, rest) := spanDigits cs
    let (acc, cnt, pSub) := scanDigits bytes pos hPos d0 1 bytes.size false 0
    acc = parseDecDigitsLoop d0 ds ∧ cnt = 1 + ds.length ∧
      pSub.1 = pos + ds.length ∧ ByteSliceAt bytes pSub.1 rest := by
  have hspP := spanDigits_props hSlice
  rcases hsp : spanDigits cs with ⟨ds, rest⟩
  rw [hsp] at hspP
  rcases hspP with ⟨_, _, _, hBnd⟩
  have hCntLe : 1 + ds.length ≤ bytes.size := by omega
  have hLoop := scanDigitsLoop_noValCap_spec cs 0 d0 1 1 bytes.size 0 hSlice (by decide) (by simpa using hd0)
  rw [hsp] at hLoop
  dsimp only at hLoop
  rw [ite_eq_left hCntLe] at hLoop
  rcases hLoop with ⟨hEq, hRestSlice⟩
  simp only [Nat.zero_mul, Nat.zero_add] at hEq
  unfold scanDigits
  have hp : pos ≤ pos + ds.length ∧ pos + ds.length ≤ bytes.size := ⟨by omega, hBnd⟩
  simp [hEq, hp, hRestSlice]

/-- Wrapper lemma for `scanDigits` on fractional digits (`initCount = 0, limitCount = 100_000, hasValCap = false`). -/
theorem scanDigits_frac_spec {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (hPos : pos ≤ bytes.size) (hSlice : ByteSliceAt bytes pos cs) :
    let (ds, rest) := spanDigits cs
    let (acc, cnt, pSub) := scanDigits bytes pos hPos 0 0 100_000 false 0
    if ds.length ≤ 100_000 then
      acc = parseDecDigitsLoop 0 ds ∧ cnt = ds.length ∧
        pSub.1 = pos + ds.length ∧ ByteSliceAt bytes pSub.1 rest
    else
      cnt = 100_001 := by
  have hspP := spanDigits_props hSlice
  rcases hsp : spanDigits cs with ⟨ds, rest⟩
  rw [hsp] at hspP
  rcases hspP with ⟨_, _, _, hBnd⟩
  have hLoop := scanDigitsLoop_noValCap_spec cs 0 0 0 0 100_000 0 hSlice (by decide) (by decide)
  rw [hsp] at hLoop
  dsimp only at hLoop
  simp only [Nat.zero_add, Nat.zero_mul] at hLoop
  unfold scanDigits
  simp only [beq_self_eq_true, ↓reduceIte]
  by_cases hle : ds.length ≤ 100_000
  · rw [ite_eq_left hle] at hLoop
    rcases hLoop with ⟨hEq, hRestSlice⟩
    have hp : pos ≤ pos + ds.length ∧ pos + ds.length ≤ bytes.size := ⟨by omega, hBnd⟩
    simp [hle, hEq, hp, hRestSlice]
  · rw [ite_eq_right hle] at hLoop
    have hcnt := hLoop (Nat.zero_le _)
    simp only [hle, ↓reduceIte]
    split <;> exact hcnt

/-- Wrapper lemma for `scanDigits` on exponent digits (`initCount = 0, limitCount = bytes.size, hasValCap = true, limitVal = 100_000`). -/
theorem scanDigits_exp_spec {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (hPos : pos ≤ bytes.size) (hSlice : ByteSliceAt bytes pos cs) :
    let (ds, rest) := spanDigits cs
    let (acc, cnt, pSub) := scanDigits bytes pos hPos 0 0 bytes.size true 100_000
    if parseDecDigitsLoop 0 ds ≤ 100_000 then
      acc = parseDecDigitsLoop 0 ds ∧ cnt = ds.length ∧
        pSub.1 = pos + ds.length ∧ ByteSliceAt bytes pSub.1 rest
    else
      100_000 < acc ∧ 1 ≤ cnt := by
  have hspP := spanDigits_props hSlice
  rcases hsp : spanDigits cs with ⟨ds, rest⟩
  rw [hsp] at hspP
  rcases hspP with ⟨_, _, _, hBnd⟩
  have hCntLe : 0 + ds.length ≤ bytes.size := by omega
  have hLoop := scanDigitsLoop_valCap_spec cs 0 0 0 0 bytes.size 100_000 hSlice (by decide) (by decide) (by rw [hsp]; exact hCntLe)
  rw [hsp] at hLoop
  dsimp only at hLoop
  simp only [Nat.zero_add, Nat.zero_mul] at hLoop
  unfold scanDigits
  simp only [beq_self_eq_true, ↓reduceIte]
  by_cases hle : parseDecDigitsLoop 0 ds ≤ 100_000
  · rw [ite_eq_left hle] at hLoop
    rcases hLoop with ⟨hEq, hRestSlice⟩
    have hp : pos ≤ pos + ds.length ∧ pos + ds.length ≤ bytes.size := ⟨by omega, hBnd⟩
    simp [hle, hEq, hp, hRestSlice]
  · rw [ite_eq_right hle] at hLoop
    obtain ⟨hGt, hCnt⟩ := hLoop (Nat.zero_le _)
    simp only [hle, ↓reduceIte]
    split <;> exact ⟨hGt, hCnt⟩

private theorem parseNumberWhole_sound {bytes : ByteArray} {pos p0 : Nat}
    (whole : Nat) (tail : List Char) (hp0Ge : pos ≤ p0)
    (hNoDig : notDigitHead tail = true)
    (hSlice : ByteSliceAt bytes p0 (whole.repr.toList ++ tail)) :
    ∃ (hltP0 : p0 < bytes.size) (p1Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }),
      parseNumberWhole bytes pos p0 hp0Ge hltP0 = .ok (whole, p1Sub) ∧
      ByteSliceAt bytes p1Sub.1 tail := by
  obtain ⟨hwNe, hwAll, hwParse⟩ := repr_nat_props whole
  by_cases hw0 : whole = 0
  · subst hw0
    change ByteSliceAt bytes p0 ('0' :: tail) at hSlice
    obtain ⟨hltP0, hg0, hsP1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
    refine ⟨hltP0, ⟨p0 + 1, by omega, by omega⟩, ?_, hsP1⟩
    unfold parseNumberWhole
    simp [hg0]
  · cases hw : whole.repr.toList with
    | nil => exact absurd hw hwNe
    | cons d0 dtl =>
      have hd0Ne0 : d0 ≠ '0' := by
        intro heq; subst heq
        have hr : whole.repr.toList = Nat.toDigits 10 whole := String.toList_ofList
        rw [hr] at hw
        have hnz : ∀ (fuel n : Nat) (acc : List Char), n ≠ 0 → n < fuel →
            ∀ c tl, Nat.toDigitsCore 10 fuel n acc = c :: tl → c ≠ '0' := by
          intro fuel
          induction fuel with
          | zero => intros; omega
          | succ f ih =>
            intro n acc hn hf c tl heq
            have hstep : Nat.toDigitsCore 10 (f + 1) n acc =
                if n / 10 = 0 then Nat.digitChar (n % 10) :: acc
                else Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: acc) := rfl
            rw [hstep] at heq
            by_cases hq : n / 10 = 0
            · rw [ite_eq_left hq] at heq
              injection heq with hcEq _
              subst hcEq
              have ⟨_, hv⟩ := digitChar_lt10_props (Nat.mod_lt n (by decide))
              intro hc0; rw [hc0] at hv; simp at hv; omega
            · rw [ite_eq_right hq] at heq
              exact ih (n / 10) _ hq (by omega) c tl heq
        exact hnz (whole + 1) whole [] hw0 (by omega) '0' dtl hw rfl
      rw [hw] at hSlice hwAll hwParse
      simp only [List.all_cons, Bool.and_eq_true] at hwAll
      rcases hwAll with ⟨hd0Dig, hdtlAll⟩
      have hd0Bounds : 0x31 ≤ d0.toNat ∧ d0.toNat ≤ 0x39 := by
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hd0Dig
        change 0x30 ≤ d0.toNat ∧ d0.toNat ≤ 0x39 at hd0Dig
        have : d0.toNat ≠ 0x30 := fun h => hd0Ne0 (Char.ext (UInt32.toNat_inj.mp h))
        omega
      simp only [List.cons_append] at hSlice
      obtain ⟨hltP0, hg0, hsAfterD0⟩ := byteSliceAt_ascii_cons hSlice (by omega)
      have htoNat0 : (d0.val.toUInt8).toNat = d0.toNat := by
        rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change d0.toNat < 256; omega)
      have hb0Ne30 : (d0.val.toUInt8 == 0x30) = false := by
        apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat0]; change d0.toNat ≠ 0x30; omega
      have hb019 : (0x31 ≤ d0.val.toUInt8 && d0.val.toUInt8 ≤ 0x39) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, htoNat0]
        exact hd0Bounds
      have hScan := scanDigits_intTail_spec hltP0 (by omega) (d0.toNat - 0x30) (by omega) hsAfterD0
      rw [spanDigits_append hdtlAll hNoDig] at hScan
      rcases hRes : scanDigits bytes (p0 + 1) hltP0 (d0.toNat - 0x30) 1 bytes.size false 0 with ⟨w, cnt, pSub⟩
      rw [hRes] at hScan
      rcases hScan with ⟨hwEq, _, _, hsP1⟩
      simp only [parseDecDigitsLoop_cons, Nat.zero_mul, Nat.zero_add] at hwParse
      rw [hwParse] at hwEq
      subst hwEq
      refine ⟨hltP0, ⟨pSub.1, by have := pSub.2; omega, pSub.2.2⟩, ?_, hsP1⟩
      unfold parseNumberWhole
      dsimp only
      rw [hg0]
      simp only [hb0Ne30, hb019, Bool.false_eq_true, ↓reduceIte, htoNat0, hRes]

/-- Soundness of `parseNumberAt` on any valid, resource-bounded `NumTape` followed by a numeric stop stream. -/
theorem parseNumberAt_of_renderNumTape {bytes : ByteArray} {pos : Nat}
    {nt : NumTape} (after : List Char)
    (hVal : validNumTape nt = true) (hLim : numTapeWithinLimits nt = true)
    (hStop : isNumStop after = true)
    (hSlice : ByteSliceAt bytes pos ((renderNumTape nt).toList ++ after)) :
    ∃ pSub, parseNumberAt bytes pos = .ok (evalNumTape nt, pSub) ∧ ByteSliceAt bytes pSub.1 after := by
  simp only [validNumTape, numTapeWithinLimits, Bool.and_eq_true] at hVal hLim
  rcases hVal with ⟨hFracVal, hExpVal⟩
  rcases hLim with ⟨hFracLim0, hExpLim0⟩
  have hFracLim := of_decide_eq_true hFracLim0
  have hExpLim := of_decide_eq_true hExpLim0
  simp only [maxFracDigits] at hFracLim
  simp only [maxAbsExponent] at hExpLim
  obtain ⟨hwNe, hwAll, _⟩ := repr_nat_props nt.whole
  have hStopNoDig : notDigitHead after = true := by
    cases after with
    | nil => rfl
    | cons c _ => simp only [isNumStop, Bool.and_eq_true] at hStop; exact hStop.1.1.1
  let expChars := (match nt.exp with
    | none => ""
    | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList
  let fracChars := (match nt.fracDigits with | none => "" | some f => "." ++ f).toList
  have hExpTailNoDig : notDigitHead (expChars ++ after) = true := by
    dsimp only [expChars]
    cases nt.exp with
    | none => exact hStopNoDig
    | some e =>
      dsimp only
      cases e.upperE <;>
        simp [String.toList_append, show "e".toList = ['e'] from rfl,
          show "E".toList = ['E'] from rfl, notDigitHead, isAsciiDigit]
  have hAfterIntNoDig : notDigitHead (fracChars ++ (expChars ++ after)) = true := by
    dsimp only [fracChars]
    cases nt.fracDigits with
    | none => exact hExpTailNoDig
    | some f => simp [String.toList_append, show ".".toList = ['.'] from rfl, notDigitHead, isAsciiDigit]
  have hRenderSplit : (renderNumTape nt).toList ++ after =
      (if nt.minus then ['-'] else []) ++ (nt.whole.repr.toList ++ (fracChars ++ (expChars ++ after))) := by
    unfold renderNumTape
    dsimp only [fracChars, expChars]
    cases nt.minus <;> simp [String.toList_append, List.append_assoc, show "-".toList = ['-'] from rfl] <;> rfl
  rw [hRenderSplit] at hSlice
  have hSignStep : ∃ (hlt0 : pos < bytes.size),
      (bytes[pos]'hlt0 == 0x2d) = nt.minus ∧
      ByteSliceAt bytes (if nt.minus then pos + 1 else pos)
        (nt.whole.repr.toList ++ (fracChars ++ (expChars ++ after))) := by
    cases hminus : nt.minus with
    | true =>
      rw [hminus] at hSlice
      simp only [↓reduceIte, List.singleton_append] at hSlice ⊢
      obtain ⟨hlt0, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
      exact ⟨hlt0, by rw [hg0]; rfl, hs1⟩
    | false =>
      rw [hminus] at hSlice
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at hSlice ⊢
      cases hw : nt.whole.repr.toList with
      | nil => exact absurd hw hwNe
      | cons d0 dtl =>
        rw [hw, List.cons_append] at hSlice
        rw [hw, List.all_cons, Bool.and_eq_true] at hwAll
        have hd0Dig : isAsciiDigit d0 = true := hwAll.1
        have hd0A : d0.toNat < 0x80 := by
          simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hd0Dig
          change 0x30 ≤ d0.toNat ∧ d0.toNat ≤ 0x39 at hd0Dig; omega
        obtain ⟨hlt0, hg0, _⟩ := byteSliceAt_ascii_cons hSlice hd0A
        have hne2d : (d0.val.toUInt8 == 0x2d) = false := by
          apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8,
            Nat.mod_eq_of_lt (by change d0.toNat < 256; omega)]
          rintro h; have : d0 = '-' := Char.ext (UInt32.toNat_inj.mp h); subst this; simp [isAsciiDigit] at hd0Dig
        exact ⟨hlt0, by rw [hg0, hne2d], by simpa [hw, List.cons_append] using hSlice⟩
  obtain ⟨hlt0, hNegEq, hsP0⟩ := hSignStep
  let p0 := if nt.minus then pos + 1 else pos
  have hp0Ge : pos ≤ p0 := by dsimp [p0]; split <;> omega
  obtain ⟨hltP0, p1Sub, hWholeOk, hsP1⟩ :=
    parseNumberWhole_sound nt.whole (fracChars ++ (expChars ++ after)) hp0Ge hAfterIntNoDig hsP0
  let sign : Int := if nt.minus then -1 else 1
  let baseNum : Lean.JsonNumber :=
    match nt.fracDigits with
    | none => Lean.JsonNumber.fromInt (sign * (nt.whole : Int))
    | some f =>
      let d := f.toList.length
      Lean.JsonNumber.mk (sign * (nt.whole * (10 ^ d) + parseDecDigits f)) d
  have hFracStep : ∃ (p2Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }),
      parseNumberFrac bytes pos sign nt.whole p1Sub = .ok (baseNum, p2Sub) ∧
      ByteSliceAt bytes p2Sub.1 (expChars ++ after) := by
    unfold parseNumberFrac
    dsimp only
    cases hf : nt.fracDigits with
    | none =>
      simp only [fracChars, hf, String.toList_empty, List.nil_append] at hsP1
      by_cases hDot : p1Sub.1 < bytes.size
      · have hNot2e : (bytes[p1Sub.1]'hDot == 0x2e) = false := by
          cases hexpC : expChars ++ after with
          | nil => rw [hexpC] at hsP1; have := byteSliceAt_nil_eq_size hsP1; omega
          | cons c tl =>
            have hcNeDot : c ≠ '.' := by
              cases he : nt.exp with
              | none =>
                simp only [expChars, he, String.toList_empty, List.nil_append] at hexpC
                rw [hexpC] at hStop
                simp only [isNumStop, Bool.and_eq_true, bne_iff_ne] at hStop
                exact hStop.1.1.2
              | some e =>
                simp only [expChars, he, String.toList_append, List.append_assoc] at hexpC
                cases hu : e.upperE <;>
                  (rw [hu] at hexpC
                   simp [show "E".toList = ['E'] from rfl, show "e".toList = ['e'] from rfl] at hexpC
                   rcases hexpC with ⟨rfl, _⟩
                   decide)
            rw [hexpC] at hsP1
            by_cases ha : c.toNat < 0x80
            · obtain ⟨_, hg, _⟩ := byteSliceAt_ascii_cons hsP1 ha
              rw [hg]; apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8,
                Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]
              intro h; exact hcNeDot (Char.ext (UInt32.toNat_inj.mp h))
            · have h128 := byteSliceAt_nonAscii_ge_128 hsP1 (by omega) hDot
              rw [UInt8.le_iff_toNat_le] at h128
              apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj]
              change (bytes[p1Sub.1]'hDot).toNat ≠ 46; change 128 ≤ (bytes[p1Sub.1]'hDot).toNat at h128; omega
        exact ⟨p1Sub, by simp [hDot, hNot2e, baseNum, hf], hsP1⟩
      · exact ⟨p1Sub, by simp [hDot, baseNum, hf], hsP1⟩
    | some f =>
      rw [hf] at hFracVal hFracLim
      dsimp only at hFracLim
      simp only [isNonEmptyDigits, Bool.and_eq_true, Bool.not_eq_true'] at hFracVal
      rcases hFracVal with ⟨hfNe, hfAll⟩
      have hsP1' : ByteSliceAt bytes p1Sub.1 ('.' :: (f.toList ++ (expChars ++ after))) := by
        simpa [fracChars, hf, String.toList_append, show ".".toList = ['.'] from rfl] using hsP1
      obtain ⟨hDot, hgDot, hsAfterDot⟩ := byteSliceAt_ascii_cons hsP1' (by decide)
      have hScan := scanDigits_frac_spec hDot hsAfterDot
      rw [spanDigits_append hfAll hExpTailNoDig] at hScan
      dsimp only at hScan
      rw [ite_eq_left hFracLim] at hScan
      rcases hRes : scanDigits bytes (p1Sub.1 + 1) hDot 0 0 100_000 false 0 with ⟨frac, d, pSub⟩
      rw [hRes] at hScan
      dsimp only at hScan
      rcases hScan with ⟨hfracEq, hdEq, _, hsP2⟩
      have hdNe0 : (d == 0) = false := by
        rw [hdEq]; cases hfl : f.toList with | nil => simp [hfl] at hfNe | cons _ _ => rfl
      have hNotGt : ¬(100_000 < d) := by omega
      refine ⟨⟨pSub.1, by have := pSub.2; have := p1Sub.2; omega, pSub.2.2⟩, ?_, hsP2⟩
      simp only [hDot, ↓reduceDIte, hgDot, (by decide : ('.'.val.toUInt8 == 0x2e) = true),
        ↓reduceIte, hRes, hdNe0, gt_iff_lt, hNotGt, Bool.false_eq_true]
      simp [baseNum, hf, hdEq, hfracEq, parseDecDigits]
  obtain ⟨p2Sub, hFracOk, hsP2⟩ := hFracStep
  have hExpStep : ∃ (pOut : { p : Nat // pos < p ∧ p ≤ bytes.size }),
      parseNumberExp bytes pos baseNum p2Sub = .ok (evalNumTape nt, pOut) ∧
      ByteSliceAt bytes pOut.1 after := by
    unfold parseNumberExp
    dsimp only
    cases he : nt.exp with
    | none =>
      simp only [expChars, he, String.toList_empty, List.nil_append] at hsP2
      have hEvalEq : evalNumTape nt = baseNum := by simp [evalNumTape, he, baseNum, sign]; rfl
      by_cases hExpLt : p2Sub.1 < bytes.size
      · have hNotE : (bytes[p2Sub.1]'hExpLt == 0x65 || bytes[p2Sub.1]'hExpLt == 0x45) = false := by
          cases hafterC : after with
          | nil => rw [hafterC] at hsP2; have := byteSliceAt_nil_eq_size hsP2; omega
          | cons c tl =>
            rw [hafterC] at hsP2 hStop
            simp only [isNumStop, Bool.and_eq_true, bne_iff_ne] at hStop
            by_cases ha : c.toNat < 0x80
            · obtain ⟨_, hg, _⟩ := byteSliceAt_ascii_cons hsP2 ha
              rw [hg, Bool.eq_false_iff, Ne, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
                ← UInt8.toNat_inj, ← UInt8.toNat_inj, UInt32.toNat_toUInt8,
                Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]
              rintro (h1 | h2)
              · exact hStop.1.2 (Char.ext (UInt32.toNat_inj.mp h1))
              · exact hStop.2 (Char.ext (UInt32.toNat_inj.mp h2))
            · have h128 := byteSliceAt_nonAscii_ge_128 hsP2 (by omega) hExpLt
              rw [UInt8.le_iff_toNat_le] at h128
              rw [Bool.eq_false_iff, Ne, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
                ← UInt8.toNat_inj, ← UInt8.toNat_inj]
              change ¬((bytes[p2Sub.1]'hExpLt).toNat = 101 ∨ (bytes[p2Sub.1]'hExpLt).toNat = 69)
              change 128 ≤ (bytes[p2Sub.1]'hExpLt).toNat at h128; omega
        exact ⟨p2Sub, by simp [hExpLt, hNotE, hEvalEq], hsP2⟩
      · exact ⟨p2Sub, by simp [hExpLt, hEvalEq], hsP2⟩
    | some e =>
      rw [he] at hExpVal hExpLim
      simp only [isNonEmptyDigits, Bool.and_eq_true, Bool.not_eq_true', parseDecDigits] at hExpVal hExpLim
      rcases hExpVal with ⟨heNe, heAll⟩
      simp only [expChars, he, String.toList_append, List.append_assoc] at hsP2
      have hEChStep : ∃ (hExpLt : p2Sub.1 < bytes.size),
          (bytes[p2Sub.1]'hExpLt == 0x65 || bytes[p2Sub.1]'hExpLt == 0x45) = true ∧
          ByteSliceAt bytes (p2Sub.1 + 1) ((renderExpSign e.sign).toList ++ (e.digits.toList ++ after)) := by
        cases huE : e.upperE with
        | false =>
          rw [huE] at hsP2
          change ByteSliceAt bytes p2Sub.1 ('e' :: ((renderExpSign e.sign).toList ++ (e.digits.toList ++ after))) at hsP2
          obtain ⟨hltE, hgE, hsP3⟩ := byteSliceAt_ascii_cons hsP2 (by decide)
          exact ⟨hltE, by rw [hgE]; rfl, hsP3⟩
        | true =>
          rw [huE] at hsP2
          change ByteSliceAt bytes p2Sub.1 ('E' :: ((renderExpSign e.sign).toList ++ (e.digits.toList ++ after))) at hsP2
          obtain ⟨hltE, hgE, hsP3⟩ := byteSliceAt_ascii_cons hsP2 (by decide)
          exact ⟨hltE, by rw [hgE]; rfl, hsP3⟩
      obtain ⟨hExpLt, hbE, hsP3⟩ := hEChStep
      let p3 := p2Sub.1 + 1
      have hSignEStep : ∃ (p4Sub : { p : Nat // p3 ≤ p ∧ p ≤ bytes.size }),
          (if hSign : p3 < bytes.size then
             if bytes[p3]'hSign == 0x2d then (true, (⟨p3 + 1, by omega, hSign⟩ : { p : Nat // p3 ≤ p ∧ p ≤ bytes.size }))
             else if bytes[p3]'hSign == 0x2b then (false, ⟨p3 + 1, by omega, hSign⟩)
             else (false, ⟨p3, Nat.le_refl _, Nat.le_of_lt hSign⟩)
           else (false, ⟨p3, Nat.le_refl _, hExpLt⟩)) = (e.sign == .minus, p4Sub) ∧
          ByteSliceAt bytes p4Sub.1 (e.digits.toList ++ after) := by
        cases hsgn : e.sign with
        | minus =>
          rw [hsgn] at hsP3
          change ByteSliceAt bytes p3 ('-' :: (e.digits.toList ++ after)) at hsP3
          obtain ⟨hltS, hgS, hsP4⟩ := byteSliceAt_ascii_cons hsP3 (by decide)
          exact ⟨⟨p3 + 1, by omega, hltS⟩, by simp [hltS, hgS, (by decide : (ExpSign.minus == .minus) = true)], hsP4⟩
        | plus =>
          rw [hsgn] at hsP3
          change ByteSliceAt bytes p3 ('+' :: (e.digits.toList ++ after)) at hsP3
          obtain ⟨hltS, hgS, hsP4⟩ := byteSliceAt_ascii_cons hsP3 (by decide)
          exact ⟨⟨p3 + 1, by omega, hltS⟩, by simp [hltS, hgS, (by decide : (ExpSign.plus == .minus) = false)], hsP4⟩
        | none =>
          rw [hsgn] at hsP3
          change ByteSliceAt bytes p3 (e.digits.toList ++ after) at hsP3
          cases hd : e.digits.toList with
          | nil => simp [hd] at heNe
          | cons d0 dtl =>
            rw [hd, List.cons_append] at hsP3
            rw [hd, List.all_cons, Bool.and_eq_true] at heAll
            have hd0Dig : isAsciiDigit d0 = true := heAll.1
            have hd0A : d0.toNat < 0x80 := by
              simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hd0Dig
              change 0x30 ≤ d0.toNat ∧ d0.toNat ≤ 0x39 at hd0Dig; omega
            obtain ⟨hltS, hgS, _⟩ := byteSliceAt_ascii_cons hsP3 hd0A
            have htoNat0 : d0.val.toUInt8.toNat = d0.toNat := by
              rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change d0.toNat < 256; omega)
            have hneM : (d0.val.toUInt8 == 0x2d) = false := by
              apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat0]
              rintro h; have : d0 = '-' := Char.ext (UInt32.toNat_inj.mp h); subst this; simp [isAsciiDigit] at hd0Dig
            have hneP : (d0.val.toUInt8 == 0x2b) = false := by
              apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat0]
              rintro h; have : d0 = '+' := Char.ext (UInt32.toNat_inj.mp h); subst this; simp [isAsciiDigit] at hd0Dig
            refine ⟨⟨p3, Nat.le_refl _, Nat.le_of_lt hltS⟩, ?_, by simpa [hd, List.cons_append] using hsP3⟩
            simp only [hltS, ↓reduceDIte]
            rw [hgS]
            simp only [hneM, hneP, Bool.false_eq_true, ↓reduceIte, (by decide : (ExpSign.none == .minus) = false)]
      obtain ⟨p4Sub, hSignEOk, hsP4⟩ := hSignEStep
      have hScanE := scanDigits_exp_spec p4Sub.2.2 hsP4
      rw [spanDigits_append heAll hStopNoDig] at hScanE
      dsimp only at hScanE
      rw [ite_eq_left hExpLim] at hScanE
      rcases hResE : scanDigits bytes p4Sub.1 p4Sub.2.2 0 0 bytes.size true 100_000 with ⟨expVal, expDigs, pSub⟩
      rw [hResE] at hScanE
      dsimp only at hScanE
      rcases hScanE with ⟨hexpValEq, hexpDigsEq, _, hsEnd⟩
      have hexpNe0 : (expDigs == 0) = false := by
        rw [hexpDigsEq]; cases hd : e.digits.toList with | nil => simp [hd] at heNe | cons _ _ => rfl
      have hNotGtE : ¬(100_000 < expVal) := by omega
      have hShiftEq : (if e.sign == .minus then baseNum.shiftr expVal else baseNum.shiftl expVal) = evalNumTape nt := by
        simp only [evalNumTape, he, baseNum, sign, parseDecDigits, hexpValEq]
        cases e.sign <;> rfl
      refine ⟨⟨pSub.1, by have := pSub.2; have := p4Sub.2; have := p2Sub.2; omega, pSub.2.2⟩, ?_, hsEnd⟩
      simp only [hExpLt, ↓reduceDIte, hbE, ↓reduceIte]
      dsimp only [p3] at hSignEOk
      rw [hSignEOk]
      dsimp only
      simp [hResE, hexpNe0, gt_iff_lt, hNotGtE, hShiftEq]
  obtain ⟨pOut, hExpOk, hsEnd⟩ := hExpStep
  refine ⟨pOut, ?_, hsEnd⟩
  unfold parseNumberAt
  simp only [hlt0, ↓reduceDIte, hNegEq]
  dsimp only [p0, sign] at hltP0 hWholeOk hFracOk
  simp [hltP0, hWholeOk, hFracOk, hExpOk]

end LeanSwe.Json.Proofs
