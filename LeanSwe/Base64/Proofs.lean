import Core.Obeys
import LeanSwe.Base64.Interface
import LeanSwe.Base64.Model
import LeanSwe.Base64.SpecTests
import LeanSwe.Base64.Proofs.CodecEquiv
import LeanSwe.Base64.Proofs.RoundTrip

namespace LeanSwe.Base64.Proofs

open Core
open Core.NondetTest
open LeanSwe.Base64
open LeanSwe.Base64.Model

private theorem decodeModelChars_canonical_unique (decOpts : DecodeOptions)
    (chars : List Char) (bs : List UInt8)
    (hstrict : decOpts.strictCanonicalBits = true)
    (hfixed : decOpts.padding ≠ .optional)
    (hdec : decodeModelChars decOpts chars = .ok bs) :
    chars = encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs := by
  unfold decodeModelChars at hdec
  cases hscan : scanInvalidChar decOpts.alphabet 0 chars with
  | some idx => simp [hscan] at hdec
  | none =>
    simp only [hscan] at hdec
    cases heq : findFirstEq 0 chars with
    | some p =>
      simp only [heq] at hdec
      by_cases hforb : decOpts.padding = .forbidden
      · simp [hforb] at hdec
      · cases hall : (chars.drop p).all (· == '=')
        · simp [hforb, hall] at hdec
        · by_cases hmod : chars.length % 4 ≠ 0
          · simp [hforb, hall, hmod] at hdec
          · by_cases hgt : chars.length - p > 2
            · simp [hforb, hall, hmod, hgt] at hdec
            · have hreq : decOpts.padding = .required := by
                cases hp : decOpts.padding <;> simp_all
              have hreqBool : (decOpts.padding == .required) = true := by rw [hreq]; rfl
              rw [hreqBool]
              simp only [hforb, ↓reduceIte, hall, Bool.not_true, Bool.false_eq_true, hmod,
                gt_iff_lt, hgt] at hdec
              rw [hstrict] at hdec
              have hdata := decodeDataChars_strict_eq_encode decOpts.alphabet 0 (chars.take p) bs hdec
              have hdropRep := list_all_eq_replicate hall
              have hsplit : chars = chars.take p ++ chars.drop p := (List.take_append_drop p chars).symm
              have hlenDrop : (chars.drop p).length = chars.length - p := List.length_drop
              have hpLt : p < chars.length := by
                have := findFirstEq_lt_length 0 chars p heq
                omega
              have hlenTake : (chars.take p).length = p := by
                rw [List.length_take]
                omega
              have hlenData := (encodeBytesList_unpadded_props decOpts.alphabet bs).1
              rw [← hdata, hlenTake] at hlenData
              have hpEq : p = (bs.length * 4 + 2) / 3 := by
                simpa [expectedEncodedLength] using hlenData
              have hpMod := unpadded_len_mod4 bs.length
              have hEqCount : chars.length - p = (3 - bs.length % 3) % 3 := by
                have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
                rcases hmod3 with h0 | h1 | h2
                · exfalso
                  have h0' : p % 4 = 0 := by rw [hpEq]; exact hpMod.1 h0
                  omega
                · have hp4 : p % 4 = 2 := by rw [hpEq]; exact hpMod.2.1 h1
                  omega
                · have hp4 : p % 4 = 3 := by rw [hpEq]; exact hpMod.2.2 h2
                  omega
              rw [hsplit, hdata, hdropRep, hlenDrop, hEqCount]
              have henc := encodeBytesList_split decOpts.alphabet true bs
              simpa [expectedPaddingCount] using henc.symm
    | none =>
      simp only [heq] at hdec
      by_cases hmod1 : (chars.length % 4 == 1) = true
      · simp [hmod1] at hdec
      · by_cases hreq : (decOpts.padding = .required && decide (chars.length % 4 ≠ 0)) = true
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hdec hreq
          simp [hreq] at hdec
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq] at hdec
          rw [hstrict] at hdec
          have hdata := decodeDataChars_strict_eq_encode decOpts.alphabet 0 chars bs hdec
          have hpCases : decOpts.padding = .required ∨ decOpts.padding = .forbidden := by
            cases hpad : decOpts.padding <;> simp_all
          rcases hpCases with hp | hp
          · rw [hp] at hreq
            simp only [Bool.and_eq_true, decide_eq_true_eq, true_and] at hreq
            have hmod4 : chars.length % 4 = 0 := by omega
            have hlenData := (encodeBytesList_unpadded_props decOpts.alphabet bs).1
            have hpEq : chars.length = (bs.length * 4 + 2) / 3 := by
              rw [hdata, hlenData, expectedEncodedLength]; rfl
            have hpMod := unpadded_len_mod4 bs.length
            have hbs3 : bs.length % 3 = 0 := by
              have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
              rcases hmod3 with h0 | h1 | h2
              · exact h0
              · have := hpMod.2.1 h1; omega
              · have := hpMod.2.2 h2; omega
            have henc := encodeBytesList_split decOpts.alphabet true bs
            have hrep0 : List.replicate (expectedPaddingCount { alphabet := decOpts.alphabet, pad := true } bs.length) '=' = [] := by
              simp [expectedPaddingCount, hbs3]
            rw [hrep0, List.append_nil] at henc
            have hreqB : (PaddingMode.required == PaddingMode.required) = true := rfl
            rw [hp, hreqB, henc, hdata]
          · have hreqB : (PaddingMode.forbidden == PaddingMode.required) = false := rfl
            rw [hp, hreqB, hdata]

/-- `test_base64_onError_returnsNonEmptyMessage` holds for `defaultApi`. -/
theorem allPass_onError_returnsNonEmptyMessage :
    AllPass (test_base64_onError_returnsNonEmptyMessage defaultApi) := by
  intro opts s
  have hd := decodeWith_matchesModel_aux { alphabet := .standard, padding := .required, strictCanonicalBits := true } s
  have hu := decodeWith_matchesModel_aux { alphabet := .urlSafe, padding := .optional, strictCanonicalBits := true } s
  have hw := decodeWith_matchesModel_aux opts s
  dsimp [test_base64_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi,
    bind, pure, Core.NondetTest.assert]
  cases h1 : Internal.decode s with
  | ok _ =>
    cases h2 : Internal.decodeUrl s with
    | ok _ =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨trivial, trivial, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨trivial, trivial, hw.2 e3 h3, trivial⟩
    | error e2 =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨trivial, hu.2 e2 h2, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨trivial, hu.2 e2 h2, hw.2 e3 h3, trivial⟩
  | error e1 =>
    cases h2 : Internal.decodeUrl s with
    | ok _ =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨hd.2 e1 h1, trivial, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨hd.2 e1 h1, trivial, hw.2 e3 h3, trivial⟩
    | error e2 =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨hd.2 e1 h1, hu.2 e2 h2, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨hd.2 e1 h1, hu.2 e2 h2, hw.2 e3 h3, trivial⟩

/-- `test_base64_wrappers_matchOptions` holds for `defaultApi`. -/
theorem allPass_wrappers_matchOptions :
    AllPass (test_base64_wrappers_matchOptions defaultApi) := by
  intro bs s
  dsimp [test_base64_wrappers_matchOptions, defaultApi, bind, pure, Core.NondetTest.assert]
  exact ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- `test_base64_encodeWith_matchesModel` holds for `defaultApi`. -/
theorem allPass_encodeWith_matchesModel :
    AllPass (test_base64_encodeWith_matchesModel defaultApi) := by
  intro opts bs
  dsimp [test_base64_encodeWith_matchesModel, defaultApi, Core.NondetTest.assert]
  exact ⟨encodeWith_eq_encodeModel opts bs, trivial⟩

/-- `test_base64_decodeWith_matchesModel` holds for `defaultApi`. -/
theorem allPass_decodeWith_matchesModel :
    AllPass (test_base64_decodeWith_matchesModel defaultApi) := by
  intro opts s
  have h := decodeWith_matchesModel_aux opts s
  dsimp [test_base64_decodeWith_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  cases ha : Internal.decodeWith opts s with
  | ok actual =>
    have ha' : decodeWith opts s = .ok actual := ha
    have hm : decodeModel opts s = .ok actual := by rw [← h.1, ha']; rfl
    simp [hm]
  | error e =>
    have ha' : decodeWith opts s = .error e := ha
    have hm : decodeModel opts s = .error (e.kind, e.offset) := by rw [← h.1, ha']; rfl
    simp [hm, h.2 e ha']

/-- Generalized round-trip theorem: `decodeWith decOpts (encodeWith encOpts bs) = .ok bs` under compatible alphabet and padding options. -/
theorem decodeWith_encodeWith_roundTrip
    (encOpts : EncodeOptions) (decOpts : DecodeOptions) (bs : ByteArray)
    (halph : decOpts.alphabet = encOpts.alphabet)
    (hpad1 : encOpts.pad = false ∨ decOpts.padding ≠ .forbidden ∨ bs.size % 3 = 0)
    (hpad2 : encOpts.pad = true ∨ decOpts.padding ≠ .required ∨ bs.size % 3 = 0) :
    decodeWith decOpts (encodeWith encOpts bs) = .ok bs := by
  have hmod := decodeWith_matchesModel_aux decOpts (encodeWith encOpts bs)
  have hsz : bs.data.toList.length = bs.size := by
    cases bs with
    | mk arr => simp [ByteArray.size]
  have hmc : decodeModelChars decOpts (encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList) =
      .ok bs.data.toList := by
    apply decodeModelChars_encodeBytesList encOpts decOpts bs.data.toList halph
    · simpa [hsz] using hpad1
    · simpa [hsz] using hpad2
  have htoList : (encodeWith encOpts bs).toList = encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList := by
    change (String.ofList (Internal.encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList)).toList =
      encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList
    rw [encodeBytesList_eq, String.toList_ofList]
  have hdm : decodeModel decOpts (encodeWith encOpts bs) = .ok bs := by
    unfold decodeModel
    rw [htoList, hmc]
    cases bs with
    | mk arr => simp [Except.map]
  cases ha : decodeWith decOpts (encodeWith encOpts bs) with
  | ok actual =>
    have : decodeModel decOpts (encodeWith encOpts bs) = .ok actual := by
      rw [← hmod.1, ha]; rfl
    rw [hdm] at this
    cases this
    rfl
  | error e =>
    have : decodeModel decOpts (encodeWith encOpts bs) = .error (e.kind, e.offset) := by
      rw [← hmod.1, ha]; rfl
    rw [hdm] at this
    cases this

/-- Standard `encode` / `decode` round-trip theorem for arbitrary `ByteArray`. -/
theorem decode_encode_roundTrip (bs : ByteArray) :
    decode (encode bs) = .ok bs :=
  decodeWith_encodeWith_roundTrip defaultEncodeOptions defaultDecodeOptions bs rfl
    (Or.inr (Or.inl (by decide))) (Or.inl rfl)

/-- URL-safe `encodeUrl` / `decodeUrl` round-trip theorem for arbitrary `ByteArray`. -/
theorem decodeUrl_encodeUrl_roundTrip (bs : ByteArray) :
    decodeUrl (encodeUrl bs) = .ok bs :=
  decodeWith_encodeWith_roundTrip urlEncodeOptions urlDecodeOptions bs rfl
    (Or.inl rfl) (Or.inr (Or.inl (by decide)))

/-- `test_base64_roundTrip_defaultAndUrl` holds for `defaultApi`. -/
theorem allPass_roundTrip_defaultAndUrl :
    AllPass (test_base64_roundTrip_defaultAndUrl defaultApi) := by
  intro bs
  dsimp [test_base64_roundTrip_defaultAndUrl, defaultApi, bind, pure, Core.NondetTest.assert]
  exact ⟨decode_encode_roundTrip bs, decodeUrl_encodeUrl_roundTrip bs, trivial⟩

/-- `test_base64_roundTrip_compatibleOptions` holds for `defaultApi`. -/
theorem allPass_roundTrip_compatibleOptions :
    AllPass (test_base64_roundTrip_compatibleOptions defaultApi) := by
  intro bs encOpts decOpts halph hpad1 hpad2
  dsimp [test_base64_roundTrip_compatibleOptions, defaultApi, Core.NondetTest.assert]
  exact ⟨decodeWith_encodeWith_roundTrip encOpts decOpts bs halph hpad1 hpad2, trivial⟩

/-- `CanReach` witness for `test_base64_roundTrip_compatibleOptions`. -/
theorem canReach_roundTrip_compatibleOptions :
    CanReach (test_base64_roundTrip_compatibleOptions defaultApi) := by
  dsimp [Core.CanReach, test_base64_roundTrip_compatibleOptions, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  refine ⟨ByteArray.empty, defaultEncodeOptions, defaultDecodeOptions, rfl,
    Or.inr (Or.inl (by decide)), Or.inl rfl, ?_, trivial⟩
  exact decode_encode_roundTrip ByteArray.empty

/-- Output length, alphabet character-set, and trailing `'='` count invariants for `encodeWith`. -/
theorem encodeWith_charset_and_length (opts : EncodeOptions) (bs : ByteArray) :
    let chars := (encodeWith opts bs).toList
    let expLen := expectedEncodedLength opts bs.size
    let expEq := expectedPaddingCount opts bs.size
    chars.length = expLen ∧
    (chars.take (chars.length - expEq)).all (isAlphabetChar opts.alphabet) = true ∧
    (chars.drop (chars.length - expEq)).all (· == '=') = true ∧
    (chars.drop (chars.length - expEq)).length = expEq := by
  have htoList : (encodeWith opts bs).toList = encodeBytesList opts.alphabet opts.pad bs.data.toList := by
    change (String.ofList (Internal.encodeBytesList opts.alphabet opts.pad bs.data.toList)).toList =
      encodeBytesList opts.alphabet opts.pad bs.data.toList
    rw [encodeBytesList_eq, String.toList_ofList]
  have hsplit := encodeBytesList_split opts.alphabet opts.pad bs.data.toList
  have hprops := encodeBytesList_unpadded_props opts.alphabet bs.data.toList
  have hsz : bs.data.toList.length = bs.size := by
    cases bs with
    | mk arr => simp [ByteArray.size]
  have heqCount : expectedPaddingCount { alphabet := opts.alphabet, pad := opts.pad } bs.data.toList.length =
      expectedPaddingCount opts bs.size := by
    simp [expectedPaddingCount, hsz]
  rw [heqCount] at hsplit
  have hlenData : (encodeBytesList opts.alphabet false bs.data.toList).length =
      expectedEncodedLength { alphabet := opts.alphabet, pad := false } bs.size := by
    rw [← hsz]; exact hprops.1
  have hlenTot : (encodeBytesList opts.alphabet false bs.data.toList ++
      List.replicate (expectedPaddingCount opts bs.size) '=').length =
      expectedEncodedLength opts bs.size := by
    simp only [List.length_append, List.length_replicate, hlenData, expectedEncodedLength,
      expectedPaddingCount, Bool.false_eq_true, ↓reduceIte]
    cases opts.pad
    · simp
    · simp only [↓reduceIte]
      have hmod3 : bs.size % 3 = 0 ∨ bs.size % 3 = 1 ∨ bs.size % 3 = 2 := by omega
      rcases hmod3 with h0 | h1 | h2
      · have hk : bs.size = 3 * (bs.size / 3) := by omega
        have ha : (3 * (bs.size / 3) * 4 + 2) / 3 = 4 * (bs.size / 3) := by omega
        have hb : (3 * (bs.size / 3) + 2) / 3 * 4 = 4 * (bs.size / 3) := by omega
        rw [hk, ha, hb]; omega
      · have hk : bs.size = 3 * (bs.size / 3) + 1 := by omega
        have ha : ((3 * (bs.size / 3) + 1) * 4 + 2) / 3 = 4 * (bs.size / 3) + 2 := by omega
        have hb : (3 * (bs.size / 3) + 1 + 2) / 3 * 4 = 4 * (bs.size / 3) + 4 := by omega
        rw [hk, ha, hb]; omega
      · have hk : bs.size = 3 * (bs.size / 3) + 2 := by omega
        have ha : ((3 * (bs.size / 3) + 2) * 4 + 2) / 3 = 4 * (bs.size / 3) + 3 := by omega
        have hb : (3 * (bs.size / 3) + 2 + 2) / 3 * 4 = 4 * (bs.size / 3) + 4 := by omega
        rw [hk, ha, hb]; omega
  have hdiff : (encodeBytesList opts.alphabet false bs.data.toList ++
      List.replicate (expectedPaddingCount opts bs.size) '=').length -
      expectedPaddingCount opts bs.size =
      (encodeBytesList opts.alphabet false bs.data.toList).length := by
    simp [List.length_append, List.length_replicate]
  dsimp only
  rw [htoList, hsplit]
  refine ⟨hlenTot, ?_, ?_, ?_⟩
  · rw [hdiff, List.take_left]; exact hprops.2.1
  · rw [hdiff, List.drop_left]; simp
  · rw [hdiff, List.drop_left, List.length_replicate]

/-- `test_base64_encodeWith_outputInvariants` holds for `defaultApi`. -/
theorem allPass_encodeWith_outputInvariants :
    AllPass (test_base64_encodeWith_outputInvariants defaultApi) := by
  intro encOpts bs
  dsimp [test_base64_encodeWith_outputInvariants, defaultApi, Core.NondetTest.assert]
  have h := encodeWith_charset_and_length encOpts bs
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, trivial⟩

/-- Canonical uniqueness: when `strictCanonicalBits = true` and `padding ≠ .optional`, any accepted string equals the canonical encoding of its decoded bytes. -/
theorem decodeWith_encodeWith_canonical_unique
    (decOpts : DecodeOptions) (s : String) (bs : ByteArray)
    (hstrict : decOpts.strictCanonicalBits = true)
    (hfixed : decOpts.padding ≠ .optional)
    (hdec : decodeWith decOpts s = .ok bs) :
    s = encodeWith { alphabet := decOpts.alphabet, pad := (decOpts.padding == .required) } bs := by
  have hmod := decodeWith_matchesModel_aux decOpts s
  have hdm : decodeModel decOpts s = .ok bs := by rw [← hmod.1, hdec]; rfl
  unfold decodeModel at hdm
  cases hmc : decodeModelChars decOpts s.toList with
  | error e => simp [hmc, Except.map] at hdm
  | ok bsList =>
    simp only [hmc, Except.map, Except.ok.injEq] at hdm
    have huniq := decodeModelChars_canonical_unique decOpts s.toList bsList hstrict hfixed hmc
    have hbs : bs.data.toList = bsList := by
      rw [← hdm]
    rw [← hbs] at huniq
    have hs : s = String.ofList s.toList := by simp [String.ofList_toList]
    rw [hs, huniq]
    change String.ofList (Model.encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs.data.toList) =
      String.ofList (Internal.encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs.data.toList)
    rw [encodeBytesList_eq]

/-- `test_base64_decodeWith_injectiveFixedPadding` holds for `defaultApi`. -/
theorem allPass_decodeWith_injectiveFixedPadding :
    AllPass (test_base64_decodeWith_injectiveFixedPadding defaultApi) := by
  intro decOpts s1 s2 bs1 bs2 ⟨hstrict, hfixed⟩ h1 h2 heq
  dsimp [test_base64_decodeWith_injectiveFixedPadding, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  have hs1 := decodeWith_encodeWith_canonical_unique decOpts s1 bs1 hstrict hfixed h1
  have hs2 := decodeWith_encodeWith_canonical_unique decOpts s2 bs2 hstrict hfixed h2
  refine ⟨?_, trivial⟩
  rw [hs1, hs2, heq]

/-- `CanReach` witness for `test_base64_decodeWith_injectiveFixedPadding`. -/
theorem canReach_decodeWith_injectiveFixedPadding :
    CanReach (test_base64_decodeWith_injectiveFixedPadding defaultApi) := by
  dsimp [Core.CanReach, test_base64_decodeWith_injectiveFixedPadding, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  refine ⟨defaultDecodeOptions, "", "", ByteArray.empty, ByteArray.empty,
    ⟨rfl, by decide⟩, rfl, rfl, rfl, rfl, trivial⟩

/-- Structural characterization equivalence for `ValidEncodedChars` and `decodeModelChars`. -/
theorem validEncodedChars_iff_decodeModelChars (opts : DecodeOptions) (chars : List Char) :
    ValidEncodedChars opts chars ↔ (decodeModelChars opts chars).isOk = true := by
  unfold ValidEncodedChars decodeModelChars
  cases hscan : scanInvalidChar opts.alphabet 0 chars with
  | some idx =>
    simp [Except.isOk, Except.toBool]
  | none =>
    simp only [true_and]
    cases heq : findFirstEq 0 chars with
    | some p =>
      simp only []
      by_cases hforb : opts.padding = .forbidden
      · simp [hforb, Except.isOk, Except.toBool]
      · cases hall : (chars.drop p).all (· == '=')
        · simp [hforb, Except.isOk, Except.toBool]
        · by_cases hmod : chars.length % 4 = 0
          · by_cases hle : chars.length - p ≤ 2
            · have hnotgt : ¬(chars.length - p > 2) := by omega
              simp [hforb, hmod, hle, hnotgt]
            · have hgt : chars.length - p > 2 := by omega
              simp [hforb, hmod, hle, hgt, Except.isOk, Except.toBool]
          · simp [hforb, hmod, Except.isOk, Except.toBool]
    | none =>
      by_cases hmod1 : chars.length % 4 = 1
      · simp [hmod1, Except.isOk, Except.toBool]
      · have hmod1b : (chars.length % 4 == 1) = false := by simp [hmod1]
        by_cases hreq : opts.padding = .required
        · by_cases hmod0 : chars.length % 4 = 0
          · simp [hreq, hmod0]
          · simp [hmod1b, hreq, hmod0, Except.isOk, Except.toBool]
        · simp [hmod1b, hreq, hmod1]

/-- `ValidEncoded` holds iff `decodeModel` succeeds on some `ByteArray`. -/
theorem validEncoded_iff_decodeModel (opts : DecodeOptions) (s : String) :
    ValidEncoded opts s ↔ ∃ bs, decodeModel opts s = .ok bs :=
  validEncoded_iff_exists opts s

/-- `test_base64_concreteVectorsAndErrors` holds for `defaultApi`. -/
theorem allPass_concreteVectorsAndErrors :
    AllPass (test_base64_concreteVectorsAndErrors defaultApi) := by
  dsimp [Core.AllPass, test_base64_concreteVectorsAndErrors, defaultApi,
    List.forM, bind, pure, Core.NondetTest.assert]
  repeat'
    first
    | exact True.intro
    | apply And.intro
    | exact makeError_msg_ne_empty _ _ _
    | rfl

/-- Full public `Interface` obedience of `LeanSwe.Base64` against `LeanSwe.Base64.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Base64.encode Model.encodeDefaultModel ∧
    Core.ObeysPureEq LeanSwe.Base64.encodeUrl Model.encodeUrlModel ∧
    Core.ObeysPureEq2 LeanSwe.Base64.encodeWith Model.encodeModel ∧
    Core.ObeysPure LeanSwe.Base64.decode Model.allowedDecode ∧
    Core.ObeysPure LeanSwe.Base64.decodeUrl Model.allowedDecodeUrl ∧
    Core.ObeysPure2 LeanSwe.Base64.decodeWith Model.allowedDecodeWith :=
  ⟨fun bs => encodeWith_eq_encodeModel Model.defaultEncodeOptions bs,
   fun bs => encodeWith_eq_encodeModel Model.urlEncodeOptions bs,
   encodeWith_eq_encodeModel,
   fun s => decodeWith_matchesModel_aux Model.defaultDecodeOptions s,
   fun s => decodeWith_matchesModel_aux Model.urlDecodeOptions s,
   decodeWith_matchesModel_aux⟩

end LeanSwe.Base64.Proofs
