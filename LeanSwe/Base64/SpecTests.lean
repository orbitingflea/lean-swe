import Core.NondetTest
import Core.Assumptions
import LeanSwe.Base64.Types
import LeanSwe.Base64.Model

namespace LeanSwe.Base64

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.Base64.Model

/-- Every error returned by `decode`, `decodeUrl`, or `decodeWith` carries a non-empty diagnostic message. -/
def test_base64_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let opts ← nondet DecodeOptions
  let s ← nondet String
  match api.decode s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")
  match api.decodeUrl s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")
  match api.decodeWith opts s with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.message ≠ "")

/-- Convenience wrappers `encode`, `encodeUrl`, `decode`, and `decodeUrl` match `encodeWith` and `decodeWith` on their canonical option records. -/
def test_base64_wrappers_matchOptions
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let bs ← nondet ByteArray
  let s ← nondet String
  NondetTest.assert (api.encode bs = api.encodeWith defaultEncodeOptions bs)
  NondetTest.assert (api.encodeUrl bs = api.encodeWith urlEncodeOptions bs)
  NondetTest.assert (api.decode s = api.decodeWith defaultDecodeOptions s)
  NondetTest.assert (api.decodeUrl s = api.decodeWith urlDecodeOptions s)

/-- `api.encodeWith` agrees with `encodeModel` for every `EncodeOptions` and `ByteArray`. -/
def test_base64_encodeWith_matchesModel
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let opts ← nondet EncodeOptions
  let bs ← nondet ByteArray
  NondetTest.assert (api.encodeWith opts bs = encodeModel opts bs)

/-- `api.decodeWith` agrees with `decodeModel` on decoded bytes, error kind, and error offset, with non-empty error messages. -/
def test_base64_decodeWith_matchesModel
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let opts ← nondet DecodeOptions
  let s ← nondet String
  match api.decodeWith opts s, decodeModel opts s with
  | .ok actual, .ok expected => NondetTest.assert (actual = expected)
  | .error e, .error (expectedKind, expectedOffset) =>
    NondetTest.assert (e.kind = expectedKind ∧ e.offset = expectedOffset ∧ e.message ≠ "")
  | _, _ => NondetTest.assert False

/-- Standard `encode`/`decode` and URL-safe `encodeUrl`/`decodeUrl` round-trip every `ByteArray`. -/
def test_base64_roundTrip_defaultAndUrl
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let bs ← nondet ByteArray
  NondetTest.assert (api.decode (api.encode bs) = .ok bs)
  NondetTest.assert (api.decodeUrl (api.encodeUrl bs) = .ok bs)

/-- `decodeWith` inverts `encodeWith` whenever `alphabet` matches and padding policies are compatible for `bs.size`. -/
def test_base64_roundTrip_compatibleOptions
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let bs ← nondet ByteArray
  let encOpts ← nondet EncodeOptions
  let decOpts ← nondet DecodeOptions
  assume (decOpts.alphabet = encOpts.alphabet)
  assume (encOpts.pad = false ∨ decOpts.padding ≠ .forbidden ∨ bs.size % 3 = 0)
  assume (encOpts.pad = true ∨ decOpts.padding ≠ .required ∨ bs.size % 3 = 0)
  NondetTest.assert (api.decodeWith decOpts (api.encodeWith encOpts bs) = .ok bs)

/-- `encodeWith` emits exact length, chosen-alphabet data prefix, and exact trailing `'='` count. -/
def test_base64_encodeWith_outputInvariants
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let encOpts ← nondet EncodeOptions
  let bs ← nondet ByteArray
  let chars := (api.encodeWith encOpts bs).toList
  let expLen := expectedEncodedLength encOpts bs.size
  let expEq := expectedPaddingCount encOpts bs.size
  NondetTest.assert (chars.length = expLen)
  NondetTest.assert ((chars.take (chars.length - expEq)).all (isAlphabetChar encOpts.alphabet))
  NondetTest.assert ((chars.drop (chars.length - expEq)).all (· == '='))
  NondetTest.assert ((chars.drop (chars.length - expEq)).length = expEq)

/-- Under `strictCanonicalBits = true` and fixed padding (`required` or `forbidden`), `decodeWith` is injective. -/
def test_base64_decodeWith_injectiveFixedPadding
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let decOpts ← nondet DecodeOptions
  let s1 ← nondet String
  let s2 ← nondet String
  let bs1 ← nondet ByteArray
  let bs2 ← nondet ByteArray
  assume (decOpts.strictCanonicalBits = true ∧ decOpts.padding ≠ .optional)
  assume (api.decodeWith decOpts s1 = .ok bs1)
  assume (api.decodeWith decOpts s2 = .ok bs2)
  assume (bs1 = bs2)
  NondetTest.assert (s1 = s2)

private def bytesOf (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

private def checkDecodeOk {runner} [NondetTest runner]
    (fn : String → Except Base64Error ByteArray) (cases : List (String × List UInt8)) :
    runner Unit :=
  cases.forM fun (s, expected) =>
    NondetTest.assert (fn s = .ok (bytesOf expected))

private def checkDecodeErr {runner} [NondetTest runner]
    (fn : String → Except Base64Error ByteArray) (cases : List (String × Base64ErrorKind × Nat)) :
    runner Unit :=
  cases.forM fun (s, expectedKind, expectedOffset) =>
    match fn s with
    | .ok _ => NondetTest.assert False
    | .error e =>
      NondetTest.assert (e.kind = expectedKind ∧ e.offset = expectedOffset ∧ e.message ≠ "")

/-- Concrete RFC 4648 §10 vectors, URL-safe vectors, padding modes, non-canonical bit checks, alphabet isolation, and error offset precedence. -/
def test_base64_concreteVectorsAndErrors
    {runner} [NondetTest runner] (api : Base64Api) : runner Unit := do
  let rfcVectors : List (List UInt8 × String × String) :=
    [ ([], "", "")
    , ([0x66], "Zg==", "Zg")
    , ([0x66, 0x6f], "Zm8=", "Zm8")
    , ([0x66, 0x6f, 0x6f], "Zm9v", "Zm9v")
    , ([0x66, 0x6f, 0x6f, 0x62], "Zm9vYg==", "Zm9vYg")
    , ([0x66, 0x6f, 0x6f, 0x62, 0x61], "Zm9vYmE=", "Zm9vYmE")
    , ([0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72], "Zm9vYmFy", "Zm9vYmFy")
    , ([0xfb, 0xff], "+/8=", "-_8")
    ]
  rfcVectors.forM fun (bs, stdEnc, urlEnc) => do
    NondetTest.assert (api.encode (bytesOf bs) = stdEnc)
    NondetTest.assert (api.encodeUrl (bytesOf bs) = urlEnc)
    NondetTest.assert (api.decode stdEnc = .ok (bytesOf bs))
    NondetTest.assert (api.decodeUrl urlEnc = .ok (bytesOf bs))
  checkDecodeOk api.decodeUrl
    [ ("", [])
    , ("QQ==", [0x41])
    , ("QQ", [0x41])
    , ("QUI=", [0x41, 0x42])
    , ("QUI", [0x41, 0x42])
    , ("-_8=", [0xfb, 0xff])
    , ("-_8", [0xfb, 0xff])
    ]
  checkDecodeOk (api.decodeWith { alphabet := .standard, padding := .forbidden, strictCanonicalBits := true })
    [ ("", []), ("QQ", [0x41]), ("QUI", [0x41, 0x42]), ("Zm9vYmFy", [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]) ]
  checkDecodeOk (api.decodeWith { alphabet := .standard, padding := .required, strictCanonicalBits := false })
    [ ("AR==", [0x01]), ("QUJ=", [0x41, 0x42]), ("QUJDAR==", [0x41, 0x42, 0x43, 0x01]) ]
  checkDecodeOk (api.decodeWith { alphabet := .urlSafe, padding := .forbidden, strictCanonicalBits := false })
    [ ("AR", [0x01]), ("QUJ", [0x41, 0x42]) ]
  checkDecodeErr api.decode
    [ ("QQ", .invalidPadding, 2)
    , ("QUI", .invalidPadding, 3)
    , ("QQ=", .invalidPadding, 2)
    , ("QQ===", .invalidPadding, 2)
    , ("=", .invalidPadding, 0)
    , ("==", .invalidPadding, 0)
    , ("===", .invalidPadding, 0)
    , ("====", .invalidPadding, 0)
    , ("A===", .invalidPadding, 1)
    , ("A=BC", .invalidPadding, 1)
    , ("A=B=", .invalidPadding, 1)
    , ("QQ=A", .invalidPadding, 2)
    , ("QQ==AA==", .invalidPadding, 2)
    , ("A", .invalidLength, 0)
    , ("AAAAA", .invalidLength, 4)
    , ("QQJDA", .invalidLength, 4)
    , ("AR==", .nonCanonicalEncoding, 1)
    , ("QUJ=", .nonCanonicalEncoding, 2)
    , ("QUJDAR==", .nonCanonicalEncoding, 5)
    , ("ab-_", .invalidCharacter, 2)
    , (" QQ==", .invalidCharacter, 0)
    , ("QQ==\n", .invalidCharacter, 4)
    , ("QQ\x00==", .invalidCharacter, 2)
    , ("é", .invalidCharacter, 0)
    , ("QQ=!", .invalidCharacter, 3)
    , ("A=B!", .invalidCharacter, 3)
    ]
  checkDecodeErr api.decodeUrl
    [ ("QQ=", .invalidPadding, 2)
    , ("QQ===", .invalidPadding, 2)
    , ("A=B=", .invalidPadding, 1)
    , ("QQ=A", .invalidPadding, 2)
    , ("A", .invalidLength, 0)
    , ("AAAAA", .invalidLength, 4)
    , ("AR==", .nonCanonicalEncoding, 1)
    , ("QUJ=", .nonCanonicalEncoding, 2)
    , ("AR", .nonCanonicalEncoding, 1)
    , ("QUJ", .nonCanonicalEncoding, 2)
    , ("ab+/", .invalidCharacter, 2)
    , ("QQ=!", .invalidCharacter, 3)
    ]
  checkDecodeErr (api.decodeWith { alphabet := .urlSafe, padding := .forbidden, strictCanonicalBits := true })
    [ ("QQ==", .invalidPadding, 2)
    , ("QUI=", .invalidPadding, 3)
    , ("AR", .nonCanonicalEncoding, 1)
    , ("QUJ", .nonCanonicalEncoding, 2)
    , ("ab+/", .invalidCharacter, 2)
    ]

/-- Declared error-coverage matrix for `LeanSwe.Base64` fallible requests (`Base64ErrorKind`). -/
def errorCoverage : List (ErrorObligation Base64ErrorKind) :=
  [ { request := "LeanSwe.Base64.decode"
      errorKind := .invalidCharacter
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidCharacter" .real }
  , { request := "LeanSwe.Base64.decode"
      errorKind := .invalidLength
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidLength" .real }
  , { request := "LeanSwe.Base64.decode"
      errorKind := .invalidPadding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidPadding" .real }
  , { request := "LeanSwe.Base64.decode"
      errorKind := .nonCanonicalEncoding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decode_nonCanonicalEncoding" .real }
  , { request := "LeanSwe.Base64.decodeUrl"
      errorKind := .invalidCharacter
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidCharacter" .real }
  , { request := "LeanSwe.Base64.decodeUrl"
      errorKind := .invalidLength
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidLength" .real }
  , { request := "LeanSwe.Base64.decodeUrl"
      errorKind := .invalidPadding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidPadding" .real }
  , { request := "LeanSwe.Base64.decodeUrl"
      errorKind := .nonCanonicalEncoding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_nonCanonicalEncoding" .real }
  , { request := "LeanSwe.Base64.decodeWith"
      errorKind := .invalidCharacter
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidCharacter" .real }
  , { request := "LeanSwe.Base64.decodeWith"
      errorKind := .invalidLength
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidLength" .real }
  , { request := "LeanSwe.Base64.decodeWith"
      errorKind := .invalidPadding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidPadding" .real }
  , { request := "LeanSwe.Base64.decodeWith"
      errorKind := .nonCanonicalEncoding
      justification := .tested "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_nonCanonicalEncoding" .real } ]

end LeanSwe.Base64
