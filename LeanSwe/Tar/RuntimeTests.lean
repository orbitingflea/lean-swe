import Core.Assumptions
import LeanSwe.Tar.Interface

namespace LeanSwe.Tar.RuntimeTests

open LeanSwe.Tar

local instance : Repr ByteArray where
  reprPrec bs _ := reprByteArray bs

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except TarError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} [Repr α]
    (res : Except TarError α) (expectedKind : TarErrorKind) (msg : String) : IO Unit := do
  match res with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expectedKind}, got {repr v})")
  | .error e =>
    if e.kind != expectedKind || e.message.isEmpty then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expectedKind})")

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

private def encodeHex (bs : ByteArray) : String :=
  String.join (bs.toList.map fun b => String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeHex (s : String) : IO ByteArray := do
  let cs := s.trimAscii.toString.toList
  let rec loop : List Char → List UInt8 → IO (List UInt8)
    | [], acc => return acc.reverse
    | a :: b :: rest, acc =>
      match hexVal? a, hexVal? b with
      | some hi, some lo => loop rest (UInt8.ofNat (hi * 16 + lo) :: acc)
      | _, _ => throw (IO.userError s!"invalid hex digits in python output: {a}{b}")
    | [_], _ => throw (IO.userError "odd-length hex string from python")
  return ByteArray.mk (← loop cs []).toArray

private def runPython3 (script : String) (stdinData : String) : IO String := do
  let out ← IO.Process.output
    { cmd := "python3"
    , args := #["-c", script]
    }
    (some stdinData)
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 failed (exit={out.exitCode}): {out.stderr}")
  return out.stdout

private def testLeanPackToPythonUnpack : IO Unit := do
  let longSeg := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')
  let veryLongPath := String.ofList (List.replicate 260 'p') ++ "/café.txt"
  let bigData := ByteArray.mk ((List.range 1200).map (fun i => UInt8.ofNat (i % 251))).toArray
  let entries : List TarEntry :=
    [ { path := "hello.txt", kind := .regular, mode := 0o100644, uid := 1000, gid := 1001, mtime := 1700000000
      , uname := "alice", gname := "staff", data := "hello world\n".toUTF8 }
    , { path := longSeg, kind := .regular, mode := 0o755, uid := 42, gid := 43, mtime := 1234567
      , uname := "bob", gname := "dev", data := bigData }
    , { path := "sub/", kind := .directory, mode := 0o755, uid := 10, gid := 20, mtime := 555 }
    , { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := "../hello.txt" }
    , { path := veryLongPath, kind := .regular, mode := 0o640, uid := 3000000, gid := 4000000, mtime := 9000000000
      , uname := "üser", gname := "grøup", data := "pax-utf8".toUTF8 }
    ]
  let packed ← assertOk (pack entries) "Lean pack entries"
  let pyScript :=
    "import io, json, sys, tarfile\n" ++
    "raw = bytes.fromhex(sys.stdin.read().strip())\n" ++
    "out = []\n" ++
    "with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as tf:\n" ++
    "    for m in tf.getmembers():\n" ++
    "        data = tf.extractfile(m).read().hex() if m.isfile() else ''\n" ++
    "        kind = 'reg' if m.isfile() else ('dir' if m.isdir() else ('sym' if m.issym() else 'other'))\n" ++
    "        out.append({'name': m.name, 'kind': kind, 'mode': m.mode, 'uid': m.uid, 'gid': m.gid, 'mtime': int(m.mtime), 'uname': m.uname, 'gname': m.gname, 'linkname': m.linkname, 'data': data})\n" ++
    "print(json.dumps(out))\n"
  let pyJson ← runPython3 pyScript (encodeHex packed)
  let expected :=
    "[{\"name\": \"hello.txt\", \"kind\": \"reg\", \"mode\": 420, \"uid\": 1000, \"gid\": 1001, \"mtime\": 1700000000, \"uname\": \"alice\", \"gname\": \"staff\", \"linkname\": \"\", \"data\": \"" ++ encodeHex "hello world\n".toUTF8 ++ "\"}, " ++
    "{\"name\": \"" ++ longSeg ++ "\", \"kind\": \"reg\", \"mode\": 493, \"uid\": 42, \"gid\": 43, \"mtime\": 1234567, \"uname\": \"bob\", \"gname\": \"dev\", \"linkname\": \"\", \"data\": \"" ++ encodeHex bigData ++ "\"}, " ++
    "{\"name\": \"sub\", \"kind\": \"dir\", \"mode\": 493, \"uid\": 10, \"gid\": 20, \"mtime\": 555, \"uname\": \"\", \"gname\": \"\", \"linkname\": \"\", \"data\": \"\"}, " ++
    "{\"name\": \"sub/link\", \"kind\": \"sym\", \"mode\": 511, \"uid\": 0, \"gid\": 0, \"mtime\": 0, \"uname\": \"\", \"gname\": \"\", \"linkname\": \"../hello.txt\", \"data\": \"\"}, " ++
    "{\"name\": \"" ++ String.ofList (List.replicate 260 'p') ++ "/caf\\u00e9.txt\", \"kind\": \"reg\", \"mode\": 416, \"uid\": 3000000, \"gid\": 4000000, \"mtime\": 9000000000, \"uname\": \"\\u00fcser\", \"gname\": \"gr\\u00f8up\", \"linkname\": \"\", \"data\": \"" ++ encodeHex "pax-utf8".toUTF8 ++ "\"}]"
  assertTrue (pyJson.trimAscii.toString == expected) s!"Python tarfile unpack mismatch:\ngot: {pyJson}\nexp: {expected}"
  let unpacked ← assertOk (unpack packed) "Lean unpack own output"
  assertTrue (unpacked.length == entries.length) "unpacked entry count"
  assertTrue (unpacked[0]!.mode == 0o644 && unpacked[0]!.path == "hello.txt") "unpacked entry 0"
  assertTrue (unpacked[2]!.path == "sub" && unpacked[2]!.kind == .directory) "unpacked dir normalized"
  assertTrue (unpacked[4]!.mtime == 9000000000 && unpacked[4]!.uname == "üser") "unpacked pax metadata"

private def testDeterministicPack : IO Unit := do
  let e1 : TarEntry := { path := "a.txt", kind := .regular, uid := 123, gid := 456, mtime := 999, uname := "u1", gname := "g1", data := "abc".toUTF8 }
  let e2 : TarEntry := { path := "a.txt", kind := .regular, uid := 999, gid := 888, mtime := 123456, uname := "u2", gname := "g2", data := "abc".toUTF8 }
  let b1 ← assertOk (packWith { deterministic := true } [e1]) "det pack 1"
  let b2 ← assertOk (packWith { deterministic := true } [e2]) "det pack 2"
  assertTrue (b1.toList == b2.toList) "deterministic tar bytes must be identical"
  let out ← assertOk (unpack b1) "unpack deterministic"
  assertTrue (out.length == 1 && out[0]!.uid == 0 && out[0]!.gid == 0 && out[0]!.mtime == 0 && out[0]!.uname == "" && out[0]!.gname == "") "deterministic metadata zeroed"

private def testPythonPackToLeanUnpack : IO Unit := do
  let pyUstarScript :=
    "import io, tarfile\n" ++
    "buf = io.BytesIO()\n" ++
    "with tarfile.open(fileobj=buf, mode='w', format=tarfile.USTAR_FORMAT) as tf:\n" ++
    "    t1 = tarfile.TarInfo('alpha/beta.txt')\n" ++
    "    d1 = b'ustar-body'\n" ++
    "    t1.size = len(d1); t1.mode = 0o644; t1.uid = 7; t1.gid = 8; t1.mtime = 1700000100; t1.uname = 'pyu'; t1.gname = 'pyg'\n" ++
    "    tf.addfile(t1, io.BytesIO(d1))\n" ++
    "    t2 = tarfile.TarInfo('alpha')\n" ++
    "    t2.type = tarfile.DIRTYPE; t2.mode = 0o755\n" ++
    "    tf.addfile(t2)\n" ++
    "print(buf.getvalue().hex())\n"
  let ustarHex ← runPython3 pyUstarScript ""
  let ustarBytes ← decodeHex ustarHex
  let ustarEntries ← assertOk (unpack ustarBytes) "Lean unpack Python USTAR_FORMAT (10240-byte padded)"
  assertTrue (ustarEntries.length == 2) "ustar entries count"
  assertTrue (ustarEntries[0]!.path == "alpha/beta.txt" && ustarEntries[0]!.data.toList == "ustar-body".toUTF8.toList) "ustar entry 0"
  assertTrue (ustarEntries[1]!.path == "alpha" && ustarEntries[1]!.kind == .directory) "ustar entry 1 dir"
  let pyPaxScript :=
    "import io, tarfile\n" ++
    "buf = io.BytesIO()\n" ++
    "with tarfile.open(fileobj=buf, mode='w', format=tarfile.PAX_FORMAT) as tf:\n" ++
    "    long_name = 'deep/' + 'z' * 140 + '/caf\\u00e9.bin'\n" ++
    "    t1 = tarfile.TarInfo(long_name)\n" ++
    "    d1 = b'pax-data-123'\n" ++
    "    t1.size = len(d1); t1.mode = 0o640; t1.uid = 5000000; t1.gid = 6000000\n" ++
    "    t1.mtime = 1794744353.8699822; t1.uname = '\\u00fcser'; t1.gname = 'grp'\n" ++
    "    t1.pax_headers['SCHILY.xattr.user'] = 'custom'\n" ++
    "    tf.addfile(t1, io.BytesIO(d1))\n" ++
    "    t2 = tarfile.TarInfo('deep/link')\n" ++
    "    t2.type = tarfile.SYMTYPE; t2.linkname = '../target'\n" ++
    "    tf.addfile(t2)\n" ++
    "print(buf.getvalue().hex())\n"
  let paxHex ← runPython3 pyPaxScript ""
  let paxBytes ← decodeHex paxHex
  let paxEntries ← assertOk (unpack paxBytes) "Lean unpack Python PAX_FORMAT"
  assertTrue (paxEntries.length == 2) "pax entries count"
  assertTrue (paxEntries[0]!.path == ("deep/" ++ String.ofList (List.replicate 140 'z') ++ "/café.bin")) "pax long utf8 path"
  assertTrue (paxEntries[0]!.mtime == 1794744353 && paxEntries[0]!.uid == 5000000 && paxEntries[0]!.uname == "üser") "pax metadata and fractional mtime"
  assertTrue (paxEntries[1]!.kind == .symlink && paxEntries[1]!.linkTarget == "../target") "pax symlink"

private def testCorruptAndSecurityFuzzing : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular, data := "hello".toUTF8 }]) "valid pack"
  let flipped := valid.set! 10 (valid[10]! ^^^ 0x01)
  assertErrKind (unpack flipped) .checksumMismatch "flipped header byte triggers checksumMismatch"
  let truncated := valid.extract 0 (valid.size - 512)
  assertErrKind (unpack truncated) .truncatedArchive "missing second zero block triggers truncatedArchive"
  let unaligned := valid.extract 0 (valid.size - 1)
  assertErrKind (unpack unaligned) .truncatedArchive "non-512 aligned input triggers truncatedArchive"
  assertErrKind (pack [{ path := "escape", kind := .symlink, linkTarget := "../etc/passwd" }]) .unsafePath "root symlink escape rejected"
  assertErrKind (pack [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }]) .duplicatePath "duplicate normalized path rejected"

private def zeroTrailer : ByteArray :=
  ByteArray.mk (Array.replicate 1024 0)

private def pad512Bytes (bs : ByteArray) : ByteArray :=
  let rem := bs.size % 512
  if rem == 0 then bs
  else bs ++ ByteArray.mk (Array.replicate (512 - rem) 0)

private def recomputeHeaderChecksum (hdr : ByteArray) : ByteArray := Id.run do
  let mut h := hdr
  for i in [148:156] do
    h := h.set! i 0x20
  let mut sum : Nat := 0
  for i in [:512] do
    sum := sum + h[i]!.toNat
  let oct := Nat.toDigits 8 sum
  let padded := (List.replicate (6 - oct.length) '0') ++ oct
  for j in [:6] do
    h := h.set! (148 + j) (UInt8.ofNat padded[j]!.toNat)
  h := h.set! 154 0
  h := h.set! 155 0x20
  pure h

private def mkHeaderWithType (name : String) (size : Nat) (typeflag : UInt8) : ByteArray :=
  Impl.buildUstarHeader name 0o644 0 0 size 0 typeflag "" "" "" ""

/-- Verify `pack` rejects empty entry path with `.invalidPath`. -/
def err_tar_pack_invalidPath : IO Unit :=
  assertErrKind (pack [{ path := "", kind := .regular }]) .invalidPath "pack empty path"

/-- Verify `pack` rejects traversal path with `.unsafePath`. -/
def err_tar_pack_unsafePath : IO Unit :=
  assertErrKind (pack [{ path := "../escape.txt", kind := .regular }]) .unsafePath "pack traversal path"

/-- Verify `pack` rejects colliding normalized paths with `.duplicatePath`. -/
def err_tar_pack_duplicatePath : IO Unit :=
  assertErrKind (pack [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }])
    .duplicatePath "pack duplicate path"

/-- Verify `pack` rejects non-regular entry carrying payload bytes with `.invalidHeader`. -/
def err_tar_pack_invalidHeader : IO Unit :=
  assertErrKind (pack [{ path := "dir/", kind := .directory, data := "x".toUTF8 }])
    .invalidHeader "pack directory with payload"

/-- Verify `pack` rejects `uid >= 2^64` with `.sizeOverflow`. -/
def err_tar_pack_sizeOverflow : IO Unit :=
  assertErrKind (pack [{ path := "a.txt", kind := .regular, uid := 2 ^ 64 }])
    .sizeOverflow "pack uid overflow"

/-- Verify `packWith` rejects empty entry path with `.invalidPath`. -/
def err_tar_packWith_invalidPath : IO Unit :=
  assertErrKind (packWith {} [{ path := "", kind := .regular }]) .invalidPath "packWith empty path"

/-- Verify `packWith` rejects traversal path with `.unsafePath`. -/
def err_tar_packWith_unsafePath : IO Unit :=
  assertErrKind (packWith {} [{ path := "../escape.txt", kind := .regular }]) .unsafePath "packWith traversal path"

/-- Verify `packWith` rejects colliding normalized paths with `.duplicatePath`. -/
def err_tar_packWith_duplicatePath : IO Unit :=
  assertErrKind (packWith {} [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }])
    .duplicatePath "packWith duplicate path"

/-- Verify `packWith` rejects non-regular entry carrying payload bytes with `.invalidHeader`. -/
def err_tar_packWith_invalidHeader : IO Unit :=
  assertErrKind (packWith {} [{ path := "dir/", kind := .directory, data := "x".toUTF8 }])
    .invalidHeader "packWith directory with payload"

/-- Verify `packWith` rejects `uid >= 2^64` with `.sizeOverflow`. -/
def err_tar_packWith_sizeOverflow : IO Unit :=
  assertErrKind (packWith {} [{ path := "a.txt", kind := .regular, uid := 2 ^ 64 }])
    .sizeOverflow "packWith uid overflow"

private def mkInvalidPathArchive : ByteArray :=
  mkHeaderWithType "" 0 0x30 ++ zeroTrailer

private def mkUnsafePathArchive : ByteArray :=
  mkHeaderWithType "../escape.txt" 0 0x30 ++ zeroTrailer

private def mkDuplicatePathArchive : ByteArray :=
  let h := mkHeaderWithType "dup.txt" 0 0x30
  h ++ h ++ zeroTrailer

private def mkInvalidHeaderArchive : ByteArray :=
  mkHeaderWithType "d" 5 0x35 ++ ByteArray.mk (Array.replicate 512 0) ++ zeroTrailer

private def mkUnsupportedEntryArchive : ByteArray :=
  mkHeaderWithType "fifo" 0 0x36 ++ zeroTrailer

private def mkSizeOverflowArchive : ByteArray :=
  let paxBody := "29 size=18446744073709551616\n".toUTF8
  let paxHdr := mkHeaderWithType "PaxHeader/a.txt" paxBody.size 0x78
  let regHdr := mkHeaderWithType "a.txt" 0 0x30
  paxHdr ++ pad512Bytes paxBody ++ regHdr ++ zeroTrailer

private def mkInvalidEncodingArchive : ByteArray :=
  let rawHdr := (mkHeaderWithType "aa.txt" 0 0x30).set! 0 0xff
  recomputeHeaderChecksum rawHdr ++ zeroTrailer

private def mkHugeSizeArchive : ByteArray :=
  mkHeaderWithType "huge.bin" 300000000 0x30 ++ zeroTrailer

/-- Verify `unpack` rejects empty archive entry path with `.invalidPath`. -/
def err_tar_unpack_invalidPath : IO Unit :=
  assertErrKind (unpack mkInvalidPathArchive) .invalidPath "unpack empty path"

/-- Verify `unpack` rejects traversal archive entry path with `.unsafePath`. -/
def err_tar_unpack_unsafePath : IO Unit :=
  assertErrKind (unpack mkUnsafePathArchive) .unsafePath "unpack traversal path"

/-- Verify `unpack` rejects duplicate archive entry paths with `.duplicatePath`. -/
def err_tar_unpack_duplicatePath : IO Unit :=
  assertErrKind (unpack mkDuplicatePathArchive) .duplicatePath "unpack duplicate path"

/-- Verify `unpack` rejects non-regular header with non-zero size with `.invalidHeader`. -/
def err_tar_unpack_invalidHeader : IO Unit :=
  assertErrKind (unpack mkInvalidHeaderArchive) .invalidHeader "unpack invalid header"

/-- Verify `unpack` rejects corrupted header checksum with `.checksumMismatch`. -/
def err_tar_unpack_checksumMismatch : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular, data := "hello".toUTF8 }]) "valid pack"
  let flipped := valid.set! 10 (valid[10]! ^^^ 0x01)
  assertErrKind (unpack flipped) .checksumMismatch "unpack checksumMismatch"

/-- Verify `unpack` rejects archive missing trailing zero block with `.truncatedArchive`. -/
def err_tar_unpack_truncatedArchive : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular, data := "hello".toUTF8 }]) "valid pack"
  assertErrKind (unpack (valid.extract 0 (valid.size - 512))) .truncatedArchive "unpack truncatedArchive"

/-- Verify `unpack` rejects unsupported typeflag with `.unsupportedEntry`. -/
def err_tar_unpack_unsupportedEntry : IO Unit :=
  assertErrKind (unpack mkUnsupportedEntryArchive) .unsupportedEntry "unpack unsupportedEntry"

/-- Verify `unpack` rejects PAX size >= 2^64 with `.sizeOverflow`. -/
def err_tar_unpack_sizeOverflow : IO Unit :=
  assertErrKind (unpack mkSizeOverflowArchive) .sizeOverflow "unpack sizeOverflow"

/-- Verify `unpack` rejects invalid UTF-8 header string with `.invalidEncoding`. -/
def err_tar_unpack_invalidEncoding : IO Unit :=
  assertErrKind (unpack mkInvalidEncodingArchive) .invalidEncoding "unpack invalidEncoding"

/-- Verify `unpack` rejects declared entry size exceeding `maxTotalBytes` with `.resourceLimitExceeded`. -/
def err_tar_unpack_resourceLimitExceeded : IO Unit :=
  assertErrKind (unpack mkHugeSizeArchive) .resourceLimitExceeded "unpack resourceLimitExceeded"

/-- Verify `unpackWith` rejects empty archive entry path with `.invalidPath`. -/
def err_tar_unpackWith_invalidPath : IO Unit :=
  assertErrKind (unpackWith {} mkInvalidPathArchive) .invalidPath "unpackWith empty path"

/-- Verify `unpackWith` rejects traversal archive entry path with `.unsafePath`. -/
def err_tar_unpackWith_unsafePath : IO Unit :=
  assertErrKind (unpackWith {} mkUnsafePathArchive) .unsafePath "unpackWith traversal path"

/-- Verify `unpackWith` rejects duplicate archive entry paths with `.duplicatePath`. -/
def err_tar_unpackWith_duplicatePath : IO Unit :=
  assertErrKind (unpackWith {} mkDuplicatePathArchive) .duplicatePath "unpackWith duplicate path"

/-- Verify `unpackWith` rejects non-regular header with non-zero size with `.invalidHeader`. -/
def err_tar_unpackWith_invalidHeader : IO Unit :=
  assertErrKind (unpackWith {} mkInvalidHeaderArchive) .invalidHeader "unpackWith invalid header"

/-- Verify `unpackWith` rejects corrupted header checksum with `.checksumMismatch`. -/
def err_tar_unpackWith_checksumMismatch : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular, data := "hello".toUTF8 }]) "valid pack"
  let flipped := valid.set! 10 (valid[10]! ^^^ 0x01)
  assertErrKind (unpackWith {} flipped) .checksumMismatch "unpackWith checksumMismatch"

/-- Verify `unpackWith` rejects archive missing trailing zero block with `.truncatedArchive`. -/
def err_tar_unpackWith_truncatedArchive : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular, data := "hello".toUTF8 }]) "valid pack"
  assertErrKind (unpackWith {} (valid.extract 0 (valid.size - 512))) .truncatedArchive "unpackWith truncatedArchive"

/-- Verify `unpackWith` rejects unsupported typeflag with `.unsupportedEntry`. -/
def err_tar_unpackWith_unsupportedEntry : IO Unit :=
  assertErrKind (unpackWith {} mkUnsupportedEntryArchive) .unsupportedEntry "unpackWith unsupportedEntry"

/-- Verify `unpackWith` rejects PAX size >= 2^64 with `.sizeOverflow`. -/
def err_tar_unpackWith_sizeOverflow : IO Unit :=
  assertErrKind (unpackWith {} mkSizeOverflowArchive) .sizeOverflow "unpackWith sizeOverflow"

/-- Verify `unpackWith` rejects invalid UTF-8 header string with `.invalidEncoding`. -/
def err_tar_unpackWith_invalidEncoding : IO Unit :=
  assertErrKind (unpackWith {} mkInvalidEncodingArchive) .invalidEncoding "unpackWith invalidEncoding"

/-- Verify `unpackWith` rejects entry count exceeding `maxEntries` with `.resourceLimitExceeded`. -/
def err_tar_unpackWith_resourceLimitExceeded : IO Unit := do
  let valid ← assertOk (pack [{ path := "a.txt", kind := .regular }, { path := "b.txt", kind := .regular }]) "two entries"
  assertErrKind (unpackWith { maxEntries := 1 } valid) .resourceLimitExceeded "unpackWith maxEntries exceeded"

/-- Registered error-coverage tests for `LeanSwe.Tar`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Tar.RuntimeTests.err_tar_pack_invalidPath", mode := .real, run := err_tar_pack_invalidPath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_pack_unsafePath", mode := .real, run := err_tar_pack_unsafePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_pack_duplicatePath", mode := .real, run := err_tar_pack_duplicatePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_pack_invalidHeader", mode := .real, run := err_tar_pack_invalidHeader }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_pack_sizeOverflow", mode := .real, run := err_tar_pack_sizeOverflow }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_packWith_invalidPath", mode := .real, run := err_tar_packWith_invalidPath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_packWith_unsafePath", mode := .real, run := err_tar_packWith_unsafePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_packWith_duplicatePath", mode := .real, run := err_tar_packWith_duplicatePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_packWith_invalidHeader", mode := .real, run := err_tar_packWith_invalidHeader }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_packWith_sizeOverflow", mode := .real, run := err_tar_packWith_sizeOverflow }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidPath", mode := .real, run := err_tar_unpack_invalidPath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_unsafePath", mode := .real, run := err_tar_unpack_unsafePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_duplicatePath", mode := .real, run := err_tar_unpack_duplicatePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidHeader", mode := .real, run := err_tar_unpack_invalidHeader }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_checksumMismatch", mode := .real, run := err_tar_unpack_checksumMismatch }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_truncatedArchive", mode := .real, run := err_tar_unpack_truncatedArchive }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_unsupportedEntry", mode := .real, run := err_tar_unpack_unsupportedEntry }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_sizeOverflow", mode := .real, run := err_tar_unpack_sizeOverflow }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_invalidEncoding", mode := .real, run := err_tar_unpack_invalidEncoding }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpack_resourceLimitExceeded", mode := .real, run := err_tar_unpack_resourceLimitExceeded }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidPath", mode := .real, run := err_tar_unpackWith_invalidPath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_unsafePath", mode := .real, run := err_tar_unpackWith_unsafePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_duplicatePath", mode := .real, run := err_tar_unpackWith_duplicatePath }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidHeader", mode := .real, run := err_tar_unpackWith_invalidHeader }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_checksumMismatch", mode := .real, run := err_tar_unpackWith_checksumMismatch }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_truncatedArchive", mode := .real, run := err_tar_unpackWith_truncatedArchive }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_unsupportedEntry", mode := .real, run := err_tar_unpackWith_unsupportedEntry }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_sizeOverflow", mode := .real, run := err_tar_unpackWith_sizeOverflow }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_invalidEncoding", mode := .real, run := err_tar_unpackWith_invalidEncoding }
   , { testName := "LeanSwe.Tar.RuntimeTests.err_tar_unpackWith_resourceLimitExceeded", mode := .real, run := err_tar_unpackWith_resourceLimitExceeded } ]

/-- Run all differential and runtime verification tests for `LeanSwe.Tar`. -/
def runAll : IO Unit := do
  testLeanPackToPythonUnpack
  testDeterministicPack
  testPythonPackToLeanUnpack
  testCorruptAndSecurityFuzzing
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Tar runtime tests"

end LeanSwe.Tar.RuntimeTests
