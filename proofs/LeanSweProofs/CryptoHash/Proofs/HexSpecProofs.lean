import Core.Obeys
import LeanSweProofs.CryptoHash.Proofs.HexHelpers

namespace LeanSwe.CryptoHash.Proofs

open Core
open Core.NondetTest
open LeanSwe.CryptoHash

private theorem decodeHexPairsAcc_spec (accRev : List UInt8) (cs : List Char) :
    Internal.decodeHexPairsAcc accRev cs =
      (decodeHexPairs cs).map (fun tail => accRev.reverse ++ tail) := by
  match cs with
  | [] => simp [Internal.decodeHexPairsAcc, decodeHexPairs]
  | [_] => simp [Internal.decodeHexPairsAcc, decodeHexPairs]
  | hi :: lo :: rest =>
    simp only [Internal.decodeHexPairsAcc, decodeHexPairs]
    cases Internal.hexCharsToByte hi lo with
    | none => rfl
    | some b =>
      dsimp only
      rw [decodeHexPairsAcc_spec (b :: accRev) rest]
      cases decodeHexPairs rest <;> simp [List.reverse_cons, List.append_assoc]

/-- `Internal.decodeHexPairsAcc []` equals `decodeHexPairs`. -/
theorem decodeHexPairsAcc_nil (cs : List Char) :
    Internal.decodeHexPairsAcc [] cs = decodeHexPairs cs := by
  rw [decodeHexPairsAcc_spec]
  cases decodeHexPairs cs <;> rfl

/-- `defaultApi` satisfies `test_cryptohash_toHex_formatAndRoundTrip`. -/
theorem cryptohash_toHex_formatAndRoundTrip :
    AllPass (test_cryptohash_toHex_formatAndRoundTrip defaultApi) := by
  intro d hd
  dsimp only
  dsimp [test_cryptohash_toHex_formatAndRoundTrip, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert,
    Core.NondetTest.nondet, Core.NondetTest.assume]
  rw [decodeHexPairsAcc_nil]
  have hlen : (String.ofList (Internal.formatHexList d.bytes.data.toList)).length = 2 * digestLen d.alg := by
    rw [String.length_ofList, formatHexList_length, Array.length_toList, ← ByteArray.size, hd]
  have hall : (String.ofList (Internal.formatHexList d.bytes.data.toList)).toList.all isLowerHexChar = true := by
    rw [String.toList_ofList]
    exact formatHexList_all_lowerHex d.bytes.data.toList
  have hrt :
      (match decodeHexPairs (String.ofList (Internal.formatHexList d.bytes.data.toList)).toList with
        | none => Except.error ({ kind := .invalidHex, message := "hex string must have even length and contain only ASCII hex digits" } : CryptoHashError)
        | some bs =>
          let ba := ByteArray.mk bs.toArray
          if (ba.size != digestLen d.alg) = true then
            Except.error ({ kind := .lengthMismatch, message := s!"expected {digestLen d.alg} digest bytes, got {ba.size}" } : CryptoHashError)
          else
            Except.ok ({ alg := d.alg, bytes := ba } : Digest)) = Except.ok d := by
    rw [String.toList_ofList, decodeHexPairs_formatHexList]
    have hba : ByteArray.mk d.bytes.data.toList.toArray = d.bytes := by
      cases d.bytes
      simp
    have hsz : ((ByteArray.mk d.bytes.data.toList.toArray).size != digestLen d.alg) = false := by
      rw [hba]
      exact bne_eq_false_iff_eq.mpr hd
    simp only [hsz, Bool.false_eq_true, ↓reduceIte, hba]
  refine ⟨hlen, hall, hrt, ?_⟩
  intro i hi
  have hi_list : i < d.bytes.data.toList.length := by
    change i < d.bytes.data.size
    change d.bytes.data.size = digestLen d.alg at hd
    omega
  have hget := formatHexList_getElem? d.bytes.data.toList i hi_list
  have hb_eq : d.bytes.data.toList[i] = d.bytes[i]! := by
    have hi_ba : i < d.bytes.size := hd ▸ hi
    rw [getElem!_pos d.bytes i hi_ba]
    rfl
  rw [hb_eq] at hget
  obtain ⟨hd_lt, hr_lt⟩ := uint8_nibble_bounds (d.bytes[i]!)
  have hdg1 := fin16_lowerHexDigit_eq ⟨(d.bytes[i]!).toNat / 16, hd_lt⟩
  have hdg2 := fin16_lowerHexDigit_eq ⟨(d.bytes[i]!).toNat % 16, hr_lt⟩
  dsimp only [lowerHexDigitSpec] at hdg1 hdg2
  rw [String.toList_ofList]
  refine ⟨?_, ?_, trivial⟩
  · rw [hget.1, ← hdg1]
    rfl
  · rw [hget.2, ← hdg2]
    rfl

/-- Non-vacuity witness for `test_cryptohash_toHex_formatAndRoundTrip`. -/
theorem reach_cryptohash_toHex_formatAndRoundTrip :
    CanReach (test_cryptohash_toHex_formatAndRoundTrip defaultApi) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  have h := cryptohash_toHex_formatAndRoundTrip d (by decide)
  dsimp [AllPass, AllPassRun, test_cryptohash_toHex_formatAndRoundTrip,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind] at h
  exact ⟨d, by decide, h.1, h.2.1, h.2.2.1, 0, by decide, h.2.2.2 0 (by decide)⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips`. -/
theorem cryptohash_fromHex_acceptsUppercaseAndRoundTrips :
    AllPass (test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips defaultApi) := by
  intro d hd
  dsimp only
  dsimp [test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  rw [decodeHexPairsAcc_nil, String.toList_ofList, String.toList_ofList, decodeHexPairs_upper_formatHexList]
  have hba : ByteArray.mk d.bytes.data.toList.toArray = d.bytes := by
    cases d.bytes
    simp
  have hsz : ((ByteArray.mk d.bytes.data.toList.toArray).size != digestLen d.alg) = false := by
    rw [hba]
    exact bne_eq_false_iff_eq.mpr hd
  simp only [hsz, Bool.false_eq_true, ↓reduceIte, hba]
  exact ⟨trivial, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips`. -/
theorem reach_cryptohash_fromHex_acceptsUppercaseAndRoundTrips :
    CanReach (test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips defaultApi) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨d, by decide, cryptohash_fromHex_acceptsUppercaseAndRoundTrips d (by decide)⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip`. -/
theorem cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip :
    AllPass (test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip defaultApi) := by
  intro alg s
  dsimp [test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip, AllPassRun, defaultApi,
    Internal.mkApiM, Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  rw [decodeHexPairsAcc_nil]
  cases hdec : decodeHexPairs s.toList with
  | none =>
    refine ⟨?_, trivial⟩
    decide
  | some bs =>
    dsimp only
    by_cases hsz : (ByteArray.mk bs.toArray).size = digestLen alg
    · have hf : ((ByteArray.mk bs.toArray).size != digestLen alg) = false := bne_eq_false_iff_eq.mpr hsz
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      have hvalid : ValidDigest { alg := alg, bytes := ByteArray.mk bs.toArray } := hsz
      have hisValid : Digest.isValid { alg := alg, bytes := ByteArray.mk bs.toArray } = true := by
        simp [Digest.isValid, hsz]
      refine ⟨⟨trivial, hsz, hvalid, hisValid⟩, ?_, trivial⟩
      rw [String.toList_ofList]
      change Internal.formatHexList bs.toArray.toList = s.toList.map Char.toLower
      rw [toList_toArray_eq]
      exact decodeHexPairs_some_format hdec
    · have ht : ((ByteArray.mk bs.toArray).size != digestLen alg) = true := bne_iff_ne.mpr hsz
      simp only [ht, ↓reduceIte]
      refine ⟨?_, trivial⟩
      intro hempty
      have hlen := congrArg String.length hempty
      simp only [String.length_append, String.length_empty] at hlen
      have hpref : (toString "expected ").length = 9 := by decide
      rw [hpref] at hlen
      omega

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsNonHexChar`. -/
theorem cryptohash_fromHex_rejectsNonHexChar :
    AllPass (test_cryptohash_fromHex_rejectsNonHexChar defaultApi) := by
  intro alg s idx ⟨hidx, hbad⟩
  dsimp only at hidx hbad ⊢
  change isHexChar s.toList[idx]! = false at hbad
  dsimp [test_cryptohash_fromHex_rejectsNonHexChar, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have hidx_list : idx < s.toList.length := by simpa [String.length_toList] using hidx
  have hbad' : isHexChar s.toList[idx] = false := by
    rwa [list_getElem!_eq s.toList idx hidx_list] at hbad
  rw [decodeHexPairsAcc_nil, decodeHexPairs_none_of_nonHex hidx_list hbad']
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsNonHexChar`. -/
theorem reach_cryptohash_fromHex_rejectsNonHexChar :
    CanReach (test_cryptohash_fromHex_rejectsNonHexChar defaultApi) :=
  ⟨.sha256, "z", 0, ⟨by decide, by decide⟩,
    cryptohash_fromHex_rejectsNonHexChar .sha256 "z" 0 ⟨by decide, by decide⟩⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsOddLengthHex`. -/
theorem cryptohash_fromHex_rejectsOddLengthHex :
    AllPass (test_cryptohash_fromHex_rejectsOddLengthHex defaultApi) := by
  intro alg s ⟨hodd, _⟩
  dsimp only at hodd ⊢
  dsimp [test_cryptohash_fromHex_rejectsOddLengthHex, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have hodd_list : s.toList.length % 2 = 1 := by simpa [String.length_toList] using hodd
  rw [decodeHexPairsAcc_nil, decodeHexPairs_none_of_odd hodd_list]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsOddLengthHex`. -/
theorem reach_cryptohash_fromHex_rejectsOddLengthHex :
    CanReach (test_cryptohash_fromHex_rejectsOddLengthHex defaultApi) :=
  ⟨.sha256, "a", ⟨by decide, by decide⟩,
    cryptohash_fromHex_rejectsOddLengthHex .sha256 "a" ⟨by decide, by decide⟩⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsWrongEvenHexLength`. -/
theorem cryptohash_fromHex_rejectsWrongEvenHexLength :
    AllPass (test_cryptohash_fromHex_rejectsWrongEvenHexLength defaultApi) := by
  intro alg s ⟨heven, hlen, hall⟩
  dsimp only at heven hlen hall ⊢
  change s.toList.all isHexChar = true at hall
  dsimp [test_cryptohash_fromHex_rejectsWrongEvenHexLength, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have heven_list : s.toList.length % 2 = 0 := by simpa [String.length_toList] using heven
  obtain ⟨bs, hbs, h2⟩ := decodeHexPairs_some_of_all_hex heven_list hall
  rw [decodeHexPairsAcc_nil, hbs]
  have hne : ((ByteArray.mk bs.toArray).size != digestLen alg) = true := by
    apply bne_iff_ne.mpr
    intro heq
    have hs_eq : s.length = 2 * digestLen alg := by
      rw [← String.length_toList, ← h2]
      have hbs_len : bs.length = (ByteArray.mk bs.toArray).size := by
        simp [ByteArray.size]
      omega
    exact hlen hs_eq
  simp only [hne, ↓reduceIte]
  refine ⟨⟨trivial, ?_⟩, trivial⟩
  intro hempty
  have hlen2 := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen2
  have hpref : (toString "expected ").length = 9 := by decide
  rw [hpref] at hlen2
  omega

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsWrongEvenHexLength`. -/
theorem reach_cryptohash_fromHex_rejectsWrongEvenHexLength :
    CanReach (test_cryptohash_fromHex_rejectsWrongEvenHexLength defaultApi) :=
  ⟨.sha256, "", ⟨by decide, by decide, by decide⟩,
    cryptohash_fromHex_rejectsWrongEvenHexLength .sha256 "" ⟨by decide, by decide, by decide⟩⟩

private theorem fromHex_toHex_of_validHex (alg : HashAlg) (s expected : String)
    (hlen : s.length = 2 * digestLen alg)
    (hall : s.toList.all isHexChar = true)
    (hlow : s.toList.map Char.toLower = expected.toList) :
    ∃ d, Internal.fromHex alg s = .ok d ∧ Internal.toHex d = expected := by
  have heven : s.toList.length % 2 = 0 := by
    rw [String.length_toList, hlen]
    omega
  obtain ⟨bs, hbs, h2⟩ := decodeHexPairs_some_of_all_hex heven hall
  have hsz : (ByteArray.mk bs.toArray).size = digestLen alg := by
    have hbs_len : bs.length = (ByteArray.mk bs.toArray).size := by
      simp [ByteArray.size]
    have hsl : s.toList.length = 2 * digestLen alg := by
      simpa [String.length_toList] using hlen
    omega
  have hf : ((ByteArray.mk bs.toArray).size != digestLen alg) = false :=
    bne_eq_false_iff_eq.mpr hsz
  refine ⟨{ alg := alg, bytes := ByteArray.mk bs.toArray }, ?_, ?_⟩
  · unfold Internal.fromHex
    rw [decodeHexPairsAcc_nil, hbs]
    simp [hf]
  · unfold Internal.toHex
    change String.ofList (Internal.formatHexList bs.toArray.toList) = expected
    rw [toList_toArray_eq, decodeHexPairs_some_format hbs, hlow, String.ofList_toList]

private def checkUpperLowerHex (c : Fin 128) : Bool :=
  let ch := Char.ofNat c.1
  if isLowerHexChar ch then
    isHexChar (Char.toUpper ch) && Char.toLower (Char.toUpper ch) == ch
  else true

private theorem fin128_upper_lower_hex : ∀ c : Fin 128, checkUpperLowerHex c = true := by
  decide

private theorem isHexChar_toUpper_of_isLowerHex {c : Char} (h : isLowerHexChar c = true) :
    isHexChar (Char.toUpper c) = true ∧ Char.toLower (Char.toUpper c) = c := by
  have hlt : c.toNat < 128 := by
    unfold isLowerHexChar at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨_, hle⟩ | ⟨_, hle⟩
    · have h1 : c.toNat ≤ '9'.toNat := UInt32.le_iff_toNat_le.mp hle
      simp at h1; omega
    · have h1 : c.toNat ≤ 'f'.toNat := UInt32.le_iff_toNat_le.mp hle
      simp at h1; omega
  have hm := fin128_upper_lower_hex ⟨c.toNat, hlt⟩
  unfold checkUpperLowerHex at hm
  dsimp only at hm
  have hc : isLowerHexChar (Char.ofNat c.toNat) = true := by simpa [Char.ofNat_toNat] using h
  rw [hc] at hm
  simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
  simpa [Char.ofNat_toNat] using hm

private theorem map_toLower_toUpper_of_all_lowerHex :
    ∀ cs : List Char, cs.all isLowerHexChar = true → cs.map (Char.toLower ∘ Char.toUpper) = cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, Function.comp_apply,
      (isHexChar_toUpper_of_isLowerHex h.1).2,
      map_toLower_toUpper_of_all_lowerHex cs h.2]

private theorem fromHex_toUpper_toHex_of_lowerHex (alg : HashAlg) (s : String)
    (hlen : s.length = 2 * digestLen alg)
    (hall : s.toList.all isLowerHexChar = true) :
    ∃ d, Internal.fromHex alg (String.ofList (s.toList.map Char.toUpper)) = .ok d ∧
      Internal.toHex d = s := by
  have hall_up : (String.ofList (s.toList.map Char.toUpper)).toList.all isHexChar = true := by
    rw [String.toList_ofList, List.all_map]
    rw [List.all_eq_true] at hall ⊢
    intro c hc
    exact (isHexChar_toUpper_of_isLowerHex (hall c hc)).1
  have hlow_up : (String.ofList (s.toList.map Char.toUpper)).toList.map Char.toLower = s.toList := by
    rw [String.toList_ofList, List.map_map]
    exact map_toLower_toUpper_of_all_lowerHex s.toList hall
  have hlen_up : (String.ofList (s.toList.map Char.toUpper)).length = 2 * digestLen alg := by
    rw [String.length_ofList, List.length_map, String.length_toList, hlen]
  exact fromHex_toHex_of_validHex alg (String.ofList (s.toList.map Char.toUpper)) s hlen_up hall_up hlow_up

set_option maxRecDepth 2048 in
/-- `defaultApi` satisfies `test_cryptohash_vectorHexRoundTrip`. -/
theorem cryptohash_vectorHexRoundTrip :
    AllPass (test_cryptohash_vectorHexRoundTrip defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cryptohash_vectorHexRoundTrip, defaultApi, Internal.mkApiM,
    Core.NondetTest.assert, Bind.bind, Pure.pure]
  obtain ⟨d1, h1_ok, h1_hex⟩ := fromHex_toHex_of_validHex .sha256
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    (by decide) (by decide) (by decide)
  obtain ⟨d2, h2_ok, h2_hex⟩ := fromHex_toHex_of_validHex .sha512
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    (by decide) (by decide) (by decide)
  obtain ⟨d3, h3_ok, h3_hex⟩ := fromHex_toUpper_toHex_of_lowerHex .sha256
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    (by decide) (by decide)
  rw [h1_ok, h2_ok, h3_ok]
  exact ⟨h1_hex, h2_hex, h3_hex, trivial⟩


end LeanSwe.CryptoHash.Proofs
