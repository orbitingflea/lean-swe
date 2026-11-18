import Core.NondetTest
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Uuid`. -/

namespace LeanSwe.Uuid

open Core (NondetTest)
open Core.NondetTest

private def zeros16 : ByteArray :=
  ByteArray.mk (Array.replicate 16 0)

private def validNilV4Bytes : ByteArray :=
  ((zeros16.set! 6 0x40).set! 8 0x80)

private def validNilV4Str : String :=
  "00000000-0000-4000-8000-000000000000"

private def validNilV4Hex : String :=
  "00000000000040008000000000000000"

private def stubUuidApi : UuidApi :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "stub" }
    fromRandomBytes := fun bs =>
      if bs.size != 16 then
        .error { kind := .invalidLength, message := "bad len" }
      else
        let b6 := (bs[6]! &&& 0x0F) ||| 0x40
        let b8 := (bs[8]! &&& 0x3F) ||| 0x80
        .ok { bytes := (bs.set! 6 b6).set! 8 b8 }
    toString := fun _ => validNilV4Str
    toHex := fun _ => validNilV4Hex
    parse := fun s =>
      if s == validNilV4Str then .ok { bytes := validNilV4Bytes }
      else .error { kind := .invalidFormat, message := "bad" }
    parseHex := fun s =>
      if s == validNilV4Hex then .ok { bytes := validNilV4Bytes }
      else .error { kind := .invalidFormat, message := "bad" }
    isValid := fun s => s == validNilV4Str
    getUuid := pure (.ok { bytes := validNilV4Bytes }) }

private def stubMkApi (ops : RawUuidOpsM (StateM MockRngState)) : UuidApiM (StateM MockRngState) :=
  { mapRawError := stubUuidApi.mapRawError
    fromRandomBytes := stubUuidApi.fromRandomBytes
    toString := stubUuidApi.toString
    toHex := stubUuidApi.toHex
    parse := stubUuidApi.parse
    parseHex := stubUuidApi.parseHex
    isValid := stubUuidApi.isValid
    getUuid := do
      match ← ops.randomBytes16 with
      | .error e => return .error e
      | .ok bs => return stubUuidApi.fromRandomBytes bs }

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .entropyFailed, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .invalidFormat, message := "bad" } }) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .entropyFailed, errnoCode := none, message := "bad" } }) := by
  intro h
  have h0 := h (.osError 5 "EIO")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload
    { stubUuidApi with fromRandomBytes := fun bs => .ok { bytes := bs } }) := by
  intro h
  have h0 := h zeros16 rfl
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload
    { stubUuidApi with fromRandomBytes := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  let bs := ByteArray.mk (Array.replicate 16 0xFF)
  have h0 := h bs rfl
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload,
    Core.NondetTest.assert, Bind.bind] at h0
  have h1 := h0.2.2.2.2.2 0 (by decide)
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_uuid_fromRandomBytes_invalidLen_returnsError
    { stubUuidApi with fromRandomBytes := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h ByteArray.empty (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_toString_formatAndRoundTrip
    { stubUuidApi with toString := fun _ => "BAD" }) := by
  intro h
  have h0 := h zeros16 rfl
  dsimp [test_uuid_toString_formatAndRoundTrip, stubUuidApi, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_toHex_formatAndRoundTrip
    { stubUuidApi with
      toHex := fun _ => validNilV4Str
      parseHex := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h zeros16 rfl
  dsimp [test_uuid_toHex_formatAndRoundTrip, stubUuidApi, zeros16, validNilV4Str,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_toHex_bigEndianNibbleOrder stubUuidApi) := by
  intro h
  let bs := ByteArray.mk (Array.replicate 16 0xFF)
  have h0 := h bs rfl 0 (by decide)
  dsimp [test_uuid_toHex_bigEndianNibbleOrder, stubUuidApi, validNilV4Hex,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_parse_acceptsUppercaseHex
    { stubUuidApi with
      toString := fun _ => "aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa"
      parse := fun s =>
        if s == "aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa" then .ok { bytes := validNilV4Bytes }
        else .error { kind := .invalidFormat, message := "lowercase only" } }) := by
  intro h
  have h0 := h zeros16 rfl
  dsimp [test_uuid_parse_acceptsUppercaseHex, stubUuidApi, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  have h1 := h0.1
  cases h1

example : ¬ Core.AllPass (test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip
    { stubUuidApi with
      parse := fun _ => .ok { bytes := zeros16 } }) := by
  intro h
  have h0 := h validNilV4Str
  dsimp [test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip
    { stubUuidApi with
      parseHex := fun _ => .ok { bytes := zeros16 } }) := by
  intro h
  have h0 := h validNilV4Hex
  dsimp [test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_uuid_parse_rejectsInvalidLength
    { stubUuidApi with
      parse := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h "" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_parse_rejectsNonHexChar
    { stubUuidApi with
      parse := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h "gggggggg-gggg-4ggg-8ggg-gggggggggggg" rfl 0 (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_parse_rejectsMissingHyphen
    { stubUuidApi with
      parse := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h "000000000000040008000000000000000000" rfl (Or.inl (by decide))
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_parse_rejectsNonV4VersionOrVariant
    { stubUuidApi with
      parse := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h zeros16 rfl '1' (by decide) '0' (by decide)
  dsimp [test_uuid_parse_rejectsNonV4VersionOrVariant, stubUuidApi, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  exact h0.1

example : ¬ Core.AllPass (test_uuid_parseHex_rejectsInvalidLength
    { stubUuidApi with
      parseHex := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h "" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_parseHex_rejectsNonHexChar
    { stubUuidApi with
      parseHex := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h "gggggggggggg4ggg8ggggggggggggggg" rfl 0 (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_uuid_parseHex_rejectsNonV4VersionOrVariant
    { stubUuidApi with
      parseHex := fun _ => .ok { bytes := validNilV4Bytes } }) := by
  intro h
  have h0 := h zeros16 rfl '1' (by decide) '0' (by decide)
  dsimp [test_uuid_parseHex_rejectsNonV4VersionOrVariant, stubUuidApi, zeros16,
    Core.NondetTest.assert, Bind.bind] at h0
  exact h0.1

example : ¬ Core.AllPass (test_uuid_getUuid_consecutiveDistinctValidAndDeterministic
    (fun ops => { stubMkApi ops with getUuid := pure (.ok { bytes := validNilV4Bytes }) })) := by
  intro h
  have h0 := h { counter := 0, failWith := none, draws := 0 } rfl
  dsimp [test_uuid_getUuid_consecutiveDistinctValidAndDeterministic, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  have h2 := h0.2.1
  simp at h2

example : ¬ Core.AllPass (test_uuid_getUuid_propagatesEntropyError
    (fun ops => { stubMkApi ops with getUuid := pure (.ok { bytes := validNilV4Bytes }) })) := by
  intro h
  let err : UuidError := { kind := .entropyFailed, message := "entropy down" }
  have h0 := h { counter := 0, failWith := some err, draws := 0 } err (by decide) rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_uuid_getUuid_rejectsWrongRawByteCount
    (fun ops => { stubMkApi ops with
      getUuid := do
        match ← ops.randomBytes16 with
        | .error e => return .error e
        | .ok _ => return .ok { bytes := validNilV4Bytes } })) := by
  intro h
  have h0 := h ByteArray.empty (by decide) { counter := 0, failWith := none, draws := 0 }
  dsimp [test_uuid_getUuid_rejectsWrongRawByteCount, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, pure, StateT.pure] at h0
  exact h0.2.1

example : ¬ Core.AllPass (test_uuid_getUuid_usesRawRandomBytes
    (fun ops => { stubMkApi ops with
      getUuid := do
        match ← ops.randomBytes16 with
        | .error e => return .error e
        | .ok _ => return .ok { bytes := validNilV4Bytes } })) := by
  intro h
  have h0 := h (ByteArray.mk (Array.replicate 16 0xFF)) rfl { counter := 0, failWith := none, draws := 0 }
  dsimp [test_uuid_getUuid_usesRawRandomBytes, stubMkApi, stubUuidApi, validNilV4Bytes, zeros16,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, pure, StateT.pure] at h0
  have h2 := h0.2.1
  split at h2
  · cases h2
  · simp at h2
    exact absurd h2 (by decide)

end LeanSwe.Uuid
