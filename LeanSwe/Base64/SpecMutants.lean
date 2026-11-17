import Core.NondetTest
import Core.Assumptions
import LeanSwe.Base64.Types
import LeanSwe.Base64.Model
import LeanSwe.Base64.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Base64`. -/

namespace LeanSwe.Base64

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.Base64.Model

private def bytesOf (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

example : encodeModel defaultEncodeOptions (bytesOf []) = "" := rfl

example : encodeModel defaultEncodeOptions (bytesOf [0x66]) = "Zg==" := rfl

example : encodeModel defaultEncodeOptions (bytesOf [0x66, 0x6f]) = "Zm8=" := rfl

example : encodeModel defaultEncodeOptions (bytesOf [0x66, 0x6f, 0x6f]) = "Zm9v" := rfl

example : encodeModel urlEncodeOptions (bytesOf [0xfb, 0xff]) = "-_8" := rfl

example : decodeModel defaultDecodeOptions "QQ" = .error (.invalidPadding, 2) := rfl

example : decodeModel defaultDecodeOptions "AR==" = .error (.nonCanonicalEncoding, 1) := rfl

example : decodeModel urlDecodeOptions "AR" = .error (.nonCanonicalEncoding, 1) := rfl

example : decodeModel urlDecodeOptions "QUJ" = .error (.nonCanonicalEncoding, 2) := rfl

example : decodeModel defaultDecodeOptions "QQ=!" = .error (.invalidCharacter, 3) := rfl

example : decodeModel defaultDecodeOptions "QQ=A" = .error (.invalidPadding, 2) := rfl

private def stubBase64Api : Base64Api :=
  { encode := fun _ => ""
  , encodeUrl := fun _ => ""
  , encodeWith := fun _ _ => ""
  , decode := fun _ => .error { kind := .invalidLength, offset := 0, message := "" }
  , decodeUrl := fun _ => .error { kind := .invalidLength, offset := 0, message := "" }
  , decodeWith := fun _ _ => .error { kind := .invalidLength, offset := 0, message := "" }
  }

example : ¬ Core.AllPass (test_base64_onError_returnsNonEmptyMessage stubBase64Api) := by
  intro h
  have h0 := h defaultDecodeOptions "A"
  simp [stubBase64Api, bind, assert] at h0

private def buggyEncodeUrlStdCharsApi : Base64Api :=
  { stubBase64Api with
    encodeUrl := fun bs => encodeModel { alphabet := .standard, pad := true } bs
    encodeWith := fun opts bs => encodeModel opts bs }

example : ¬ Core.AllPass (test_base64_wrappers_matchOptions buggyEncodeUrlStdCharsApi) := by
  intro h
  have h0 := h (bytesOf [0xfb, 0xff]) "A"
  simp [buggyEncodeUrlStdCharsApi, encodeModel, urlEncodeOptions, encodeBytesList,
    encodeSextet, bytesOf, bind, assert] at h0

private def buggyDecodeAcceptsUnpaddedApi : Base64Api :=
  { stubBase64Api with
    decode := fun s => decodeModel { alphabet := .standard, padding := .optional, strictCanonicalBits := true } s
      |>.mapError (fun (k, o) => { kind := k, offset := o, message := "err" })
    decodeWith := fun opts s => decodeModel opts s
      |>.mapError (fun (k, o) => { kind := k, offset := o, message := "err" }) }

example : ¬ Core.AllPass (test_base64_wrappers_matchOptions buggyDecodeAcceptsUnpaddedApi) := by
  intro h
  have h0 := h ByteArray.empty "QQ"
  have hm1 : decodeModel { alphabet := .standard, padding := .optional, strictCanonicalBits := true } "QQ" =
      .ok (bytesOf [0x41]) := rfl
  have hm2 : decodeModel defaultDecodeOptions "QQ" = .error (.invalidPadding, 2) := rfl
  simp [buggyDecodeAcceptsUnpaddedApi, hm1, hm2, Except.mapError, bind, assert] at h0

private def buggyIgnoresForbiddenPaddingApi : Base64Api :=
  { stubBase64Api with
    decodeWith := fun opts s =>
      if s == "QQ==" && opts.padding == .forbidden then .ok (bytesOf [0x41])
      else .error { kind := .invalidLength, offset := 0, message := "err" } }

example : ¬ Core.AllPass (test_base64_decodeWith_matchesModel buggyIgnoresForbiddenPaddingApi) := by
  intro h
  have h0 := h { alphabet := .standard, padding := .forbidden, strictCanonicalBits := true } "QQ=="
  have hm : decodeModel { alphabet := .standard, padding := .forbidden, strictCanonicalBits := true } "QQ==" =
      .error (.invalidPadding, 2) := rfl
  have hp : (PaddingMode.forbidden == PaddingMode.forbidden) = true := rfl
  simp [buggyIgnoresForbiddenPaddingApi, hm, hp, assert] at h0

private def buggyAcceptsPaddedNonCanonicalApi : Base64Api :=
  { stubBase64Api with
    decodeWith := fun opts s =>
      if s == "AR==" && opts.strictCanonicalBits then .ok (bytesOf [0x01])
      else .error { kind := .invalidLength, offset := 0, message := "err" } }

example : ¬ Core.AllPass (test_base64_decodeWith_matchesModel buggyAcceptsPaddedNonCanonicalApi) := by
  intro h
  have h0 := h defaultDecodeOptions "AR=="
  have hm : decodeModel defaultDecodeOptions "AR==" = .error (.nonCanonicalEncoding, 1) := rfl
  have hst : defaultDecodeOptions.strictCanonicalBits = true := rfl
  simp [buggyAcceptsPaddedNonCanonicalApi, hst, hm, assert] at h0

private def buggyAcceptsUnpaddedNonCanonicalApi : Base64Api :=
  { stubBase64Api with
    decodeWith := fun opts s =>
      if (s == "AR" || s == "AQ") && opts.padding == .forbidden then .ok (bytesOf [0x01])
      else .error { kind := .invalidLength, offset := 0, message := "err" } }

example : ¬ Core.AllPass (test_base64_decodeWith_injectiveFixedPadding buggyAcceptsUnpaddedNonCanonicalApi) := by
  intro h
  let opts : DecodeOptions := { alphabet := .urlSafe, padding := .forbidden, strictCanonicalBits := true }
  have h0 := h opts "AQ" "AR" (bytesOf [0x01]) (bytesOf [0x01])
  dsimp [test_base64_decodeWith_injectiveFixedPadding, buggyAcceptsUnpaddedNonCanonicalApi, opts,
    bind, pure, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert] at h0
  have h1 := h0 (by decide) (by rfl) (by rfl) rfl
  simp at h1

example : ¬ Core.AllPass (test_base64_decodeWith_matchesModel buggyAcceptsUnpaddedNonCanonicalApi) := by
  intro h
  let opts : DecodeOptions := { alphabet := .urlSafe, padding := .forbidden, strictCanonicalBits := true }
  have h0 := h opts "AR"
  have hm : decodeModel opts "AR" = .error (.nonCanonicalEncoding, 1) := rfl
  have hp : (opts.padding == PaddingMode.forbidden) = true := rfl
  simp [buggyAcceptsUnpaddedNonCanonicalApi, opts, hm, hp, assert] at h0

private def buggyDecodeUrlAcceptsPlusSlashApi : Base64Api :=
  { stubBase64Api with
    decodeUrl := fun s =>
      if s == "ab+/" then .ok (bytesOf [0x69, 0xbf, 0xbf])
      else .error { kind := .invalidLength, offset := 0, message := "err" }
    decodeWith := fun opts s => decodeModel opts s
      |>.mapError (fun (k, o) => { kind := k, offset := o, message := "err" }) }

example : ¬ Core.AllPass (test_base64_wrappers_matchOptions buggyDecodeUrlAcceptsPlusSlashApi) := by
  intro h
  have h0 := h ByteArray.empty "ab+/"
  have hm : decodeModel urlDecodeOptions "ab+/" = .error (.invalidCharacter, 2) := rfl
  simp [buggyDecodeUrlAcceptsPlusSlashApi, hm, Except.mapError, bind, assert] at h0

private def buggySkipsNonAsciiAndWhitespaceApi : Base64Api :=
  { stubBase64Api with
    decodeWith := fun _ s =>
      if s == " QQ==" || s == "é" then .ok ByteArray.empty
      else .error { kind := .invalidLength, offset := 0, message := "err" } }

example : ¬ Core.AllPass (test_base64_decodeWith_matchesModel buggySkipsNonAsciiAndWhitespaceApi) := by
  intro h
  have h0 := h defaultDecodeOptions "é"
  have hm : decodeModel defaultDecodeOptions "é" = .error (.invalidCharacter, 0) := rfl
  simp [buggySkipsNonAsciiAndWhitespaceApi, hm, assert] at h0

example : ¬ Core.AllPass (test_base64_concreteVectorsAndErrors stubBase64Api) := by
  intro h
  dsimp [Core.AllPass, test_base64_concreteVectorsAndErrors, stubBase64Api,
    List.forM, bind, pure, Core.NondetTest.assert] at h
  have hBad : "" = "Zg==" := h.2.2.2.2.1
  exact (by decide : "" ≠ "Zg==") hBad

end LeanSwe.Base64
