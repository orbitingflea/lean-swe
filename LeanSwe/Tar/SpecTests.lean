import Core.NondetTest
import Core.Assumptions
import LeanSwe.Tar.Types
import LeanSwe.Tar.Model
import LeanSwe.Tar.Helpers.Model

namespace LeanSwe.Tar

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.Tar.Model

/-- Construct a 512-byte USTAR header block with recomputed unsigned checksum after applying byte patches. -/
def patchHeaderChecksum (hdr : ByteArray) : ByteArray :=
  let chk := ustarChecksum hdr
  let chkField := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  blitFixed hdr 148 8 chkField

/-- Construct a valid `'x'` PAX header block + padded payload for `paxPayload`. -/
def mkPaxFrame (paxPayload : ByteArray) : ByteArray :=
  let hdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 paxPayload.size 0 0x78 "" "" "" ""
  hdr ++ padBlock512 paxPayload

/-- Construct a valid regular-file USTAR header + padded data block without a trailer. -/
def mkRegularFrame (name : String) (payload : ByteArray) : ByteArray :=
  let hdr := mkUstarHeader name 0o644 0 0 payload.size 0 0x30 "" "" "" ""
  hdr ++ padBlock512 payload

/-- Two-zero-block end-of-archive trailer (`1024` bytes of `0x00`). -/
def twoZeroBlocks : ByteArray :=
  zeroBlock ++ zeroBlock

/-- Every error returned by `pack`, `packWith`, `unpack`, or `unpackWith` carries a non-empty message. -/
def test_tar_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let entries ← nondet (List TarEntry)
  let packOpts ← nondet PackOptions
  let bytes ← nondet ByteArray
  let unpackOpts ← nondet UnpackOptions
  (match api.pack entries with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.packWith packOpts entries with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.unpack bytes with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.unpackWith unpackOpts bytes with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))

/-- Default `pack` and `unpack` match `packWith {}` and `unpackWith {}` respectively. -/
def test_tar_defaultWrappers_matchOptionsDefaults
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let entries ← nondet (List TarEntry)
  let bytes ← nondet ByteArray
  NondetTest.assert (api.pack entries = api.packWith {} entries)
  NondetTest.assert (api.unpack bytes = api.unpackWith {} bytes)

/-- `packWith` succeeds iff `ValidArchive opts.allowAbsolute opts.allowParentTraversal entries` holds. -/
def test_tar_packWith_iffValidArchive
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let opts ← nondet PackOptions
  let entries ← nondet (List TarEntry)
  match api.packWith opts entries with
  | .ok _ => NondetTest.assert (ValidArchive opts.allowAbsolute opts.allowParentTraversal entries)
  | .error e =>
    NondetTest.assert (¬ ValidArchive opts.allowAbsolute opts.allowParentTraversal entries ∧ !e.message.isEmpty = true)

/-- Every `unpackWith` success yields a `ValidArchive` respecting `maxEntries` and `maxTotalBytes`. -/
def test_tar_unpackWith_returnsValidArchiveWithinLimits
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let opts ← nondet UnpackOptions
  let bytes ← nondet ByteArray
  match api.unpackWith opts bytes with
  | .error _ => pure ()
  | .ok entries =>
    NondetTest.assert (ValidArchive opts.allowAbsolute opts.allowParentTraversal entries)
    NondetTest.assert (entries.length ≤ opts.maxEntries)
    NondetTest.assert (totalDataBytes entries ≤ opts.maxTotalBytes)

/-- Every valid archive within unpack resource limits round-trips through `packWith` and `unpackWith` up to `TarEquiv`. -/
def test_tar_packUnpack_roundTrip
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let entries ← nondet (List TarEntry)
  let packOpts ← nondet PackOptions
  let unpackOpts ← nondet UnpackOptions
  assume (ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
  assume ((!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
  assume ((!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
  assume (entries.length ≤ unpackOpts.maxEntries)
  assume (totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
  assume (entries.all fitsPaxLimit = true)
  match api.packWith packOpts entries with
  | .error _ => NondetTest.assert False
  | .ok bytes =>
    match api.unpackWith unpackOpts bytes with
    | .error _ => NondetTest.assert False
    | .ok decoded =>
      let expected := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
      NondetTest.assert (TarEquiv expected decoded)

/-- Concrete USTAR split, PAX long/UTF-8 metadata, mode masking, deterministic mode, and empty-archive round-trips succeed. -/
def test_tar_packWith_concreteUstarAndPaxCases_roundTrip
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  match api.pack [] with
  | .error _ => NondetTest.assert False
  | .ok emptyBytes =>
    NondetTest.assert (emptyBytes.size = 1024)
    match api.unpackWith { maxEntries := 0, maxTotalBytes := 0 } emptyBytes with
    | .error _ => NondetTest.assert False
    | .ok res => NondetTest.assert (res = [])
  let splitPath := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')
  let splitEntry : TarEntry := { path := splitPath, kind := .regular, data := "hi".toUTF8 }
  match api.pack [splitEntry] with
  | .error _ => NondetTest.assert False
  | .ok splitBytes =>
    NondetTest.assert (splitBytes.size = 2048)
    match api.unpack splitBytes with
    | .error _ => NondetTest.assert False
    | .ok res => NondetTest.assert (TarEquiv [splitEntry] res)
  let paxBoundaryPath := String.ofList (List.replicate 91 'p')
  let paxLongPath := String.ofList (List.replicate 260 'x') ++ "/café.txt"
  let e1 : TarEntry :=
    { path := paxBoundaryPath, kind := .regular, mode := 0o100755
    , uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9, mtime := ustarOctal11Limit + 42
    , uname := "üser", gname := "grøup", data := "payload".toUTF8 }
  let e2 : TarEntry := { path := "sub/", kind := .directory, mode := 0o755 }
  let e3 : TarEntry := { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := "../" ++ paxBoundaryPath }
  let e4 : TarEntry := { path := paxLongPath, kind := .regular, mode := 0o644, data := ByteArray.empty }
  checkRoundTripCase api {} {} [e1, e2, e3, e4]
  checkRoundTripCase api { deterministic := true } {} [e1, e2, e3, e4]

/-- `packWith` enforces exact 5-step path validation precedence, `"."` rejection, and duplicate normalized path rejection. -/
def test_tar_packWith_invalidAndUnsafePaths_rejected
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  checkPackError api {} [{ path := "a\x00b", kind := .regular }] .invalidPath
  checkPackError api {} [{ path := "", kind := .regular }] .invalidPath
  checkPackError api {} [{ path := "/abs", kind := .regular }] .unsafePath
  checkPackError api {} [{ path := "/", kind := .directory }] .unsafePath
  checkPackError api { allowAbsolute := true } [{ path := "/", kind := .directory }] .invalidPath
  checkPackError api { allowAbsolute := true } [{ path := "///", kind := .directory }] .invalidPath
  checkPackError api {} [{ path := "dir/", kind := .regular }] .invalidPath
  checkPackError api {} [{ path := "link/", kind := .symlink, linkTarget := "t" }] .invalidPath
  checkPackError api {} [{ path := "a//b", kind := .regular }] .invalidPath
  checkPackError api { allowAbsolute := true } [{ path := "//a", kind := .regular }] .invalidPath
  checkPackError api { allowParentTraversal := true } [{ path := "./a", kind := .regular }] .unsafePath
  checkPackError api { allowParentTraversal := true } [{ path := "a/./b", kind := .regular }] .unsafePath
  checkPackError api {} [{ path := "../a", kind := .regular }] .unsafePath
  checkPackError api {} [{ path := "a/../b", kind := .regular }] .unsafePath
  checkRoundTripCase api { allowAbsolute := true, allowParentTraversal := true }
    { allowAbsolute := true, allowParentTraversal := true }
    [{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }]
  checkPackError api {}
    [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }] .duplicatePath
  checkPackError api {}
    [{ path := "", kind := .regular }, { path := "", kind := .regular }] .invalidPath

/-- `packWith` enforces symlink parent-directory depth safety and entry field invariants. -/
def test_tar_packWith_symlinkAndEntryInvariants_rejected
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  checkPackError api {} [{ path := "s", kind := .symlink, linkTarget := "" }] .invalidPath
  checkPackError api {} [{ path := "s", kind := .symlink, linkTarget := "a\x00b" }] .invalidPath
  checkPackError api {} [{ path := "s", kind := .symlink, linkTarget := "/etc/passwd" }] .unsafePath
  checkPackError api {} [{ path := "escape", kind := .symlink, linkTarget := "../etc/passwd" }] .unsafePath
  checkPackError api {} [{ path := "sub/escape", kind := .symlink, linkTarget := "../../secret" }] .unsafePath
  checkPackError api {} [{ path := "sub/escape2", kind := .symlink, linkTarget := "x/../../../secret" }] .unsafePath
  checkRoundTripCase api {} {}
    [ { path := "sub/ok1", kind := .symlink, linkTarget := "../target" }
    , { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }
    ]
  checkPackError api {} [{ path := "d", kind := .directory, data := "x".toUTF8 }] .invalidHeader
  checkPackError api {} [{ path := "s", kind := .symlink, linkTarget := "t", data := "x".toUTF8 }] .invalidHeader
  checkPackError api {} [{ path := "f", kind := .regular, linkTarget := "t" }] .invalidHeader
  checkPackError api {} [{ path := "d", kind := .directory, linkTarget := "t" }] .invalidHeader
  checkPackError api {} [{ path := "f", kind := .regular, uname := "a\x00b" }] .invalidHeader
  checkPackError api {} [{ path := "f", kind := .regular, gname := "a\x00b" }] .invalidHeader
  checkPackError api {} [{ path := "f", kind := .regular, uid := u64Limit }] .sizeOverflow
  checkPackError api {} [{ path := "f", kind := .regular, gid := u64Limit }] .sizeOverflow
  checkPackError api {} [{ path := "f", kind := .regular, mtime := u64Limit }] .sizeOverflow

/-- `unpackWith` enforces 512-byte alignment, two-zero-block trailers, record-padded trailers, and ignores data padding bytes. -/
def test_tar_unpackWith_framingAndTrailer_validated
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
  checkUnpackError api {} ByteArray.empty .truncatedArchive
  checkUnpackError api {} (ByteArray.mk #[0]) .truncatedArchive
  checkUnpackError api {} (twoZeroBlocks ++ ByteArray.mk #[1]) .truncatedArchive
  checkUnpackError api {} regFrame .truncatedArchive
  checkUnpackError api {} (regFrame ++ zeroBlock) .truncatedArchive
  checkUnpackError api {} (regFrame ++ zeroBlock ++ regFrame) .invalidHeader
  checkUnpackError api {} paxHdr .truncatedArchive
  checkUnpackError api {} (paxHdr ++ twoZeroBlocks) .invalidHeader
  checkUnpackError api {} (paxHdr ++ paxHdr ++ regFrame ++ twoZeroBlocks) .invalidHeader
  checkUnpackError api {} (regFrame ++ twoZeroBlocks ++ regFrame) .invalidHeader
  let paddedArchive := regFrame ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock
  match api.unpack paddedArchive with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular, data := "hi".toUTF8 }] res)
  let hdr := mkUstarHeader "p.txt" 0o644 0 0 2 0 0x30 "" "" "" ""
  let dirtyData := ByteArray.mk (#[0x41, 0x42] ++ Array.replicate 510 0xff)
  match api.unpack (hdr ++ dirtyData ++ twoZeroBlocks) with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] res)

/-- `unpackWith` enforces USTAR checksum, magic, numeric/base-256 bounds, unsupported typeflags, and PAX parsing rules. -/
def test_tar_unpackWith_checksumNumericAndUnsupported_validated
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let baseHdr := mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" ""
  let badChkVal := baseHdr.set! 148 0x37
  checkUnpackError api {} (badChkVal ++ twoZeroBlocks) .checksumMismatch
  let badChkSyntax := baseHdr.set! 148 0x58
  checkUnpackError api {} (badChkSyntax ++ twoZeroBlocks) .invalidHeader
  let allNulChk := blitFixed baseHdr 148 8 (ByteArray.mk (Array.replicate 8 0))
  checkUnpackError api {} (allNulChk ++ twoZeroBlocks) .invalidHeader
  let badMagic := patchHeaderChecksum (blitFixed baseHdr 257 6 "notust".toUTF8)
  checkUnpackError api {} (badMagic ++ twoZeroBlocks) .invalidHeader
  let negBase256 := patchHeaderChecksum (blitFixed baseHdr 124 12 (ByteArray.mk (Array.replicate 12 0xff)))
  checkUnpackError api {} (negBase256 ++ twoZeroBlocks) .sizeOverflow
  let posBase256Uid := patchHeaderChecksum (blitFixed baseHdr 108 8 (ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42]))
  match api.unpack (posBase256Uid ++ twoZeroBlocks) with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular, uid := 42 }] res)
  let nulSize := patchHeaderChecksum (blitFixed baseHdr 124 12 (ByteArray.mk (Array.replicate 12 0)))
  checkUnpackError api {} (nulSize ++ twoZeroBlocks) .invalidHeader
  let nulUid := patchHeaderChecksum (blitFixed baseHdr 108 8 (ByteArray.mk (Array.replicate 8 0)))
  match api.unpack (nulUid ++ twoZeroBlocks) with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular, uid := 0 }] res)
  let hardlink := patchHeaderChecksum (baseHdr.set! 156 0x31)
  checkUnpackError api {} (hardlink ++ twoZeroBlocks) .unsupportedEntry
  let globalPax := patchHeaderChecksum (baseHdr.set! 156 0x67)
  checkUnpackError api {} (globalPax ++ twoZeroBlocks) .unsupportedEntry
  let badDir := patchHeaderChecksum (blitFixed (baseHdr.set! 156 0x35) 124 12 (encodeOctalField 5 11))
  checkUnpackError api {} (badDir ++ padBlock512 "12345".toUTF8 ++ twoZeroBlocks) .invalidHeader
  checkUnpackError api {} (mkPaxFrame (encodePaxRecord "GNU.sparse.major" "1") ++ baseHdr ++ twoZeroBlocks) .unsupportedEntry
  checkUnpackError api {} (mkPaxFrame (encodePaxRecord "uname" "a\x00b") ++ baseHdr ++ twoZeroBlocks) .invalidHeader
  checkUnpackError api {} (mkPaxFrame (encodePaxRecord "path" "a" ++ encodePaxRecord "path" "b") ++ baseHdr ++ twoZeroBlocks) .invalidHeader
  checkUnpackError api {} (mkPaxFrame "09 path=a\n".toUTF8 ++ baseHdr ++ twoZeroBlocks) .invalidHeader
  let validPax := mkPaxFrame (encodePaxRecord "mtime" "1794744353.8699822" ++ encodePaxRecord "SCHILY.xattr.user" "ok")
  match api.unpack (validPax ++ baseHdr ++ twoZeroBlocks) with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }] res)
  let badUtf8Name := patchHeaderChecksum (baseHdr.set! 0 0xff)
  checkUnpackError api {} (badUtf8Name ++ twoZeroBlocks) .invalidEncoding
  let garbageLink := patchHeaderChecksum (baseHdr.set! 157 0xff)
  match api.unpack (garbageLink ++ twoZeroBlocks) with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular }] res)

/-- `unpackWith` enforces `maxEntries`, `maxTotalBytes`, and `maxPaxHeaderBytes` before payload slicing, including crafted `size >= 2^33` PAX bombs. -/
def test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let regFrame := mkRegularFrame "a.txt" "hello".toUTF8
  checkUnpackError api { maxEntries := 0 } (regFrame ++ twoZeroBlocks) .resourceLimitExceeded
  checkUnpackError api { maxTotalBytes := 4 } (regFrame ++ twoZeroBlocks) .resourceLimitExceeded
  let paxZeroFile := mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkRegularFrame "a.txt" ByteArray.empty ++ twoZeroBlocks
  match api.unpackWith { maxTotalBytes := 0 } paxZeroFile with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "a.txt", kind := .regular }] res)
  let bigSizePax := mkPaxFrame (encodePaxRecord "size" "8589934592") ++ mkRegularFrame "big.bin" ByteArray.empty ++ twoZeroBlocks
  checkUnpackError api { maxTotalBytes := 1024 } bigSizePax .resourceLimitExceeded
  checkUnpackError api { maxTotalBytes := 10737418240 } bigSizePax .truncatedArchive
  let hugePaxHdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 (maxPaxHeaderBytes + 1) 0 0x78 "" "" "" ""
  checkUnpackError api {} (hugePaxHdr ++ twoZeroBlocks) .resourceLimitExceeded

/-- `unpackWith` rejects traversal paths, escaping symlinks, and duplicate normalized paths on wire under default options. -/
def test_tar_unpackWith_securityOnWire_enforced
    {runner} [NondetTest runner] (api : TarApi) : runner Unit := do
  let travHdr := mkUstarHeader "../evil" 0o644 0 0 0 0 0x30 "" "" "" ""
  checkUnpackError api {} (travHdr ++ twoZeroBlocks) .unsafePath
  let absHdr := mkUstarHeader "/etc/passwd" 0o644 0 0 0 0 0x30 "" "" "" ""
  checkUnpackError api {} (absHdr ++ twoZeroBlocks) .unsafePath
  let escSym := mkUstarHeader "escape" 0o777 0 0 0 0 0x32 "../etc/passwd" "" "" ""
  checkUnpackError api {} (escSym ++ twoZeroBlocks) .unsafePath
  let dupA := mkUstarHeader "sub/" 0o755 0 0 0 0 0x35 "" "" "" ""
  let dupB := mkUstarHeader "sub" 0o644 0 0 0 0 0x30 "" "" "" ""
  checkUnpackError api {} (dupA ++ dupB ++ twoZeroBlocks) .duplicatePath
  let safePax := mkPaxFrame (encodePaxRecord "path" "safe.txt") ++ mkRegularFrame "safe.txt" ByteArray.empty ++ twoZeroBlocks
  match api.unpack safePax with
  | .error _ => NondetTest.assert False
  | .ok res => NondetTest.assert (TarEquiv [{ path := "safe.txt", kind := .regular }] res)

/-- Declared error-coverage matrix for `LeanSwe.Tar` fallible requests (`TarErrorKind`). -/
def errorCoverage : List (ErrorObligation TarErrorKind) :=
  [ { request := "LeanSwe.Tar.pack"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_pack_invalidPath" .real }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .unsafePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_pack_unsafePath" .real }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .duplicatePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_pack_duplicatePath" .real }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .invalidHeader
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_pack_invalidHeader" .real }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .checksumMismatch
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_pack_never_checksumMismatch" }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .truncatedArchive
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_pack_never_truncatedArchive" }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .unsupportedEntry
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_pack_never_unsupportedEntry" }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .sizeOverflow
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_pack_sizeOverflow" .real }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .invalidEncoding
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_pack_never_invalidEncoding" }
  , { request := "LeanSwe.Tar.pack"
      errorKind := .resourceLimitExceeded
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_pack_never_resourceLimitExceeded" }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_packWith_invalidPath" .real }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .unsafePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_packWith_unsafePath" .real }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .duplicatePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_packWith_duplicatePath" .real }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .invalidHeader
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_packWith_invalidHeader" .real }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .checksumMismatch
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_packWith_never_checksumMismatch" }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .truncatedArchive
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_packWith_never_truncatedArchive" }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .unsupportedEntry
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_packWith_never_unsupportedEntry" }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .sizeOverflow
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_packWith_sizeOverflow" .real }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .invalidEncoding
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_packWith_never_invalidEncoding" }
  , { request := "LeanSwe.Tar.packWith"
      errorKind := .resourceLimitExceeded
      justification := .provedImpossible "LeanSwe.Tar.Proofs.tar_packWith_never_resourceLimitExceeded" }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidPath" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .unsafePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_unsafePath" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .duplicatePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_duplicatePath" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .invalidHeader
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidHeader" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .checksumMismatch
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_checksumMismatch" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .truncatedArchive
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_truncatedArchive" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .unsupportedEntry
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_unsupportedEntry" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .sizeOverflow
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_sizeOverflow" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .invalidEncoding
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidEncoding" .real }
  , { request := "LeanSwe.Tar.unpack"
      errorKind := .resourceLimitExceeded
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpack_resourceLimitExceeded" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidPath" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .unsafePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_unsafePath" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .duplicatePath
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_duplicatePath" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .invalidHeader
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidHeader" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .checksumMismatch
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_checksumMismatch" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .truncatedArchive
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_truncatedArchive" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .unsupportedEntry
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_unsupportedEntry" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .sizeOverflow
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_sizeOverflow" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .invalidEncoding
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidEncoding" .real }
  , { request := "LeanSwe.Tar.unpackWith"
      errorKind := .resourceLimitExceeded
      justification := .tested "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_resourceLimitExceeded" .real } ]

end LeanSwe.Tar
