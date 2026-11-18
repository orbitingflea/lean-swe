import Core.NondetTest
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Uuid`. -/

namespace LeanSwe.Uuid

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM TimeRandState GrndFlags)

private def zeros16 : ByteArray :=
  ByteArray.mk (Array.replicate 16 0)

private def validNilV4Bytes : ByteArray :=
  ((zeros16.set! 6 0x40).set! 8 0x80)

private def validNilV4Str : String :=
  "00000000-0000-4000-8000-000000000000"

private def validNilV4Hex : String :=
  "00000000000040008000000000000000"

private def stubUuidApi : UuidApi :=
  { mapRawError := fun
      | .osError code _ => { kind := .entropyFailed, errnoCode := some code, message := "stub" }
      | .shortRead _ _ => { kind := .entropyFailed, errnoCode := none, message := "stub" }
      | .userError _ => { kind := .entropyFailed, errnoCode := none, message := "stub" }
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

private def stubMkApi {m : Type → Type} [Monad m] (_ : TimeRandOpsM m) : UuidApiM m :=
  { mapRawError := stubUuidApi.mapRawError
    fromRandomBytes := stubUuidApi.fromRandomBytes
    toString := stubUuidApi.toString
    toHex := stubUuidApi.toHex
    parse := stubUuidApi.parse
    parseHex := stubUuidApi.parseHex
    isValid := stubUuidApi.isValid
    getUuid := pure (.ok { bytes := validNilV4Bytes }) }

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .entropyFailed, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .invalidFormat, message := "bad" } }) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_uuid_mapRawError_returnsNonEmptyMessage
    { stubUuidApi with mapRawError := fun _ => { kind := .entropyFailed, errnoCode := none, message := "bad" } }) := by
  intro h
  have h0 := h (.osError 5 "EIO")
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2.1 (by decide)

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
  exact absurd h1.1 (by decide)

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
  cases h0.1

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

example : ¬ Core.AllPass (test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid stubMkApi) := by
  intro h
  have h0 := h {}
  dsimp [test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.2.1.1 (by decide)

example : ¬ Core.AllPass (test_uuid_getUuid_usesExact16BytesFromGetrandom stubMkApi) := by
  intro h
  have h0 := h (ByteArray.mk (Array.replicate 16 0xFF)) rfl
  dsimp [test_uuid_getUuid_usesExact16BytesFromGetrandom, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr
    (fun sys => { stubMkApi sys with
      getUuid := do
        match ← sys.getrandom 16 {} with
        | .error e => return .error { kind := .entropyFailed, errnoCode := some e, message := "err" }
        | .ok bs =>
          if bs.size != 16 then
            return .error { kind := .entropyFailed, message := "no partial read loop" }
          else
            return stubUuidApi.fromRandomBytes bs })) := by
  intro h
  let b8 := ByteArray.mk (Array.replicate 8 0xAA)
  have h0 := h b8 b8 1 (by decide) (by decide)
  dsimp [test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr, scriptedGetrandomOps,
    stubMkApi, stubUuidApi, Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry stubMkApi) := by
  intro h
  have h0 := h Errno.EIO (by decide)
  dsimp [test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed
    (fun sys => { stubMkApi sys with
      getUuid := do
        match ← sys.getrandom 16 {} with
        | .error e => return .error { kind := .entropyFailed, errnoCode := some e, message := "err" }
        | .ok bs => return stubUuidApi.fromRandomBytes bs })) := by
  intro h
  have h0 := h (ByteArray.mk #[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]) (by decide)
  dsimp [test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed,
    countingFixedGetrandomOps, stubMkApi, stubUuidApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure] at h0
  rcases h0.2.1.2 with ⟨err, herr, hkind, _⟩
  cases herr
  cases hkind

end LeanSwe.Uuid
