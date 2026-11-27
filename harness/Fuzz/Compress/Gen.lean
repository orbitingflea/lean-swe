import Fuzz.Common.Rng
import LeanSweProofs.Compress.Model

namespace Fuzz.Compress

open Fuzz.Common
open LeanSwe.Compress

/-- Single concrete differential fuzz operation for `LeanSwe.Compress`. -/
inductive CompressFuzzOp where
  /-- Probe `LeanSwe.Compress.isToolAvailable codec`. -/
  | isToolAvailable (codec : Codec)
  /-- Compress `payload` via `LeanSwe.Compress.compress codec payload`. -/
  | compress (codec : Codec) (payload : ByteArray)
  /-- Compress `payload` via `LeanSwe.Compress.compressWith codec opts payload`. -/
  | compressWith (codec : Codec) (opts : CompressOptions) (payload : ByteArray)
  /-- Decompress `input` via `LeanSwe.Compress.decompress codec input`. -/
  | decompress (codec : Codec) (input : ByteArray) (tag : String := "")
  /-- Decompress `input` via `LeanSwe.Compress.decompressWith codec opts input`. -/
  | decompressWith (codec : Codec) (opts : DecompressOptions) (input : ByteArray) (tag : String := "")
  deriving DecidableEq, BEq

private def hexDigitLower (n : Nat) : Char :=
  let v := n &&& 0x0F
  if v < 10 then Char.ofNat ('0'.toNat + v)
  else Char.ofNat ('a'.toNat + (v - 10))

private def fmtBytesPreview (bs : ByteArray) : String := Id.run do
  let cap := min bs.size 64
  let mut chars : Array Char := Array.mkEmpty (cap * 2)
  for i in [0:cap] do
    let b := (bs.get! i).toNat
    chars := chars.push (hexDigitLower (b >>> 4))
    chars := chars.push (hexDigitLower b)
  let sfx := if bs.size > cap then "..." else ""
  return s!"bytes[{bs.size}:0x{String.ofList chars.toList}{sfx}]"

instance : Repr CompressFuzzOp where
  reprPrec
    | .isToolAvailable c, _ => s!"isToolAvailable({repr c})"
    | .compress c p, _ => s!"compress({repr c}, size={p.size}, {fmtBytesPreview p})"
    | .compressWith c opts p, _ => s!"compressWith({repr c}, {repr opts}, size={p.size}, {fmtBytesPreview p})"
    | .decompress c inp tag, _ => s!"decompress({repr c}, tag={repr tag}, size={inp.size}, {fmtBytesPreview inp})"
    | .decompressWith c opts inp tag, _ =>
      s!"decompressWith({repr c}, {repr opts}, tag={repr tag}, size={inp.size}, {fmtBytesPreview inp})"

/-- Input generator family selector matching the 10-family + OS-subpass distribution. -/
inductive GenFamily where
  /-- Pure `Model.encodeStored` round-trip streams. -/
  | storedModel
  /-- Real CLI-compressed payloads across valid levels and thread counts. -/
  | cliValid
  /-- Python-compressed streams and crafted rich container headers. -/
  | pythonValidAndRichHeaders
  /-- Multi-frame concatenations, skippable frames, and valid/invalid NUL padding. -/
  | multiFrameAndPadding
  /-- Cross-codec and legacy/unsupported format confusion vectors. -/
  | foreignAndLegacyConfusion
  /-- Bit-flips and surgical checksum/flag/VLI/block corruptions. -/
  | surgicalCorrupt
  /-- Strict stream prefixes `0 ≤ k < size`. -/
  | truncatedPrefixes
  /-- High-ratio repetitive bombs and corrupt-after-limit streams with tight `maxOutputBytes`. -/
  | bombsAndOutputLimits
  /-- Option and input boundary rejections (`level`, `threads`, `maxInputBytes`, `maxOutputBytes`, `timeoutMs`). -/
  | invalidOptions
  /-- Unrestricted random byte arrays `0 .. 2048` bytes. -/
  | rawRandomBytes
  deriving Repr, DecidableEq, BEq

/-- Sample one of the 3 codecs uniformly. -/
def genCodec (r : Rng) : Codec × Rng :=
  r.choose #[.zstd, .xz, .gzip] .zstd

/-- Select a fuzz family according to the approved blueprint weights. -/
def genFamily (r : Rng) : GenFamily × Rng :=
  r.chooseWeighted #[
    (10, .storedModel),
    (13, .cliValid),
    (12, .pythonValidAndRichHeaders),
    (10, .multiFrameAndPadding),
    (8, .foreignAndLegacyConfusion),
    (11, .surgicalCorrupt),
    (7, .truncatedPrefixes),
    (14, .bombsAndOutputLimits),
    (10, .invalidOptions),
    (5, .rawRandomBytes)
  ] .rawRandomBytes

/-- Generate a payload emphasizing LZ/chunk boundaries, UTF-8 text, structured text, and PRNG bytes. -/
def genBoundaryPayload (r : Rng) : ByteArray × Rng :=
  let (kind, r1) := r.nextNat 10
  if kind == 0 then
    (ByteArray.empty, r1)
  else if kind == 1 then
    (ByteArray.mk #[0x00, 0xFF, 0x1F, 0x8B, 0x28, 0xB5, 0x2F, 0xFD], r1)
  else if kind == 2 then
    let (sub, r2) := r1.nextNat 4
    let txt :=
      if sub == 0 then "hello lean-swe! gzip zstd xz differential check\n"
      else if sub == 1 then "aaaaabaaaaac"
      else if sub == 2 then "hello_world_1234 hello_world_5678"
      else "hellohellohellohellohellohellohellohellohellohello"
    (txt.toUTF8, r2)
  else if kind == 3 then
    let (sz, r2) := r1.choose #[1, 17, 4096, 65535, 65536, 65537, 131072, 131073] 17
    (pushReplicateByte ByteArray.empty 0x41 sz, r2)
  else if kind == 4 then
    let (tier, r2) := r1.nextNat 3
    let (sz, r3) :=
      if tier == 0 then r2.nextRange 32760 32780
      else if tier == 1 then r2.nextRange 65530 65550
      else r2.nextRange 131068 131084
    r3.nextBytes sz
  else if kind == 5 then
    let (reps, r2) := r1.nextRange 4 40
    let (flipIdx, r3) := r2.nextNat 16
    let rec buildJson (i : Nat) (acc : ByteArray) : ByteArray :=
      if i >= reps then acc
      else
        let tag := if i % 5 == flipIdx % 5 then "bob" else "alice"
        let row := s!"\{\"id\":{12340 + i % 17},\"name\":\"{tag}\",\"tags\":[\"a\",\"b\",\"c\"],\"active\":true}\n".toUTF8
        buildJson (i + 1) (acc ++ row)
    (buildJson 0 ByteArray.empty, r3)
  else if kind == 6 then
    let (reps, r2) := r1.nextRange 6 64
    let (mutMask, r3) := r2.nextU8
    let motif := "compress_boundary_check_xyz_12345_".toUTF8
    let out := Id.run do
      let mut acc := ByteArray.emptyWithCapacity (reps * motif.size)
      for i in [0:reps] do
        acc := acc ++ motif
        if i % 3 == 0 then
          let idx := acc.size - 1 - (i % motif.size)
          acc := acc.set! idx (acc.get! idx ^^^ mutMask ^^^ UInt8.ofNat (i % 7 + 1))
      return acc
    (out, r3)
  else if kind == 7 then
    let (sz, r2) := r1.nextRange 512 4096
    let (m, r3) := r2.nextRange 3 29
    let (d, r4) := r3.nextRange 5 31
    let (off, r5) := r4.nextNat 256
    let out := Id.run do
      let mut ba := ByteArray.emptyWithCapacity sz
      for i in [0:sz] do
        ba := ba.push (UInt8.ofNat ((i * m + i / d + off) % 256))
      return ba
    (out, r5)
  else if kind == 8 then
    let (sz, r2) := r1.nextRange 128 1024
    let (alpha, r3) := r2.nextRange 6 64
    let (base, r4) := r3.nextNat 256
    let out := Id.run do
      let mut ba := ByteArray.emptyWithCapacity sz
      let mut rCur := r4
      for _ in [0:sz] do
        let (pick, rN) := rCur.nextNat 10
        rCur := rN
        if pick < 6 then
          ba := ba.push (UInt8.ofNat (base % 256))
        else
          let (delta, rD) := rCur.nextNat alpha
          rCur := rD
          ba := ba.push (UInt8.ofNat ((base + delta) % 256))
      return (ba, rCur)
    out
  else
    r1.nextBytesRange 0 1024

/-- Generate a repetitive bomb payload (`64 KiB` to `256 KiB`) plus byte seed. -/
def genBombPayload (r : Rng) : ByteArray × Rng :=
  let (sz, r1) := r.choose #[65536, 131072, 196608, 262144] 65536
  let (b, r2) := r1.nextU8
  (pushReplicateByte ByteArray.empty b sz, r2)

/-- Generate valid codec-specific `CompressOptions` for CLI diversity. -/
def genValidCompressOptions (codec : Codec) (r : Rng) : CompressOptions × Rng :=
  let (lvl, r1) :=
    match codec with
    | .gzip => r.choose #[none, some 1, some 5, some 9] none
    | .xz => r.choose #[none, some 0, some 3, some 6, some 9] none
    | .zstd => r.choose #[none, some 1, some 3, some 10, some 19] none
  let (thr, r2) :=
    match codec with
    | .gzip => (none, r1)
    | .xz => r1.choose #[none, some 0, some 1, some 2, some 4, some 16384] none
    | .zstd => r1.choose #[none, some 0, some 1, some 2, some 4, some 4294967295] none
  ({ level := lvl, threads := thr }, r2)

private def pushU16BE (out : ByteArray) (v : Nat) : ByteArray :=
  (out.push (UInt8.ofNat ((v >>> 8) &&& 0xFF))).push (UInt8.ofNat (v &&& 0xFF))

private def mkGzipMember (plain : ByteArray) (flg : UInt8) (withHcrc : Bool) : ByteArray :=
  let effFlg : UInt8 := flg &&& 0x1F ||| (if withHcrc then 0x02 else 0x00)
  let base := ByteArray.mk #[0x1F, 0x8B, 0x08, effFlg, 0, 0, 0, 0, 0, 0x03]
  let withExtra :=
    if (effFlg &&& 0x04) != 0 then base ++ ByteArray.mk #[0x03, 0x00, 0x41, 0x42, 0x43]
    else base
  let withName :=
    if (effFlg &&& 0x08) != 0 then withExtra ++ "f.bin".toUTF8.push 0x00
    else withExtra
  let withComment :=
    if (effFlg &&& 0x10) != 0 then withName ++ "note".toUTF8.push 0x00
    else withName
  let hdr :=
    if (effFlg &&& 0x02) != 0 then
      let hc := (crc32 withComment 0 withComment.size).toNat &&& 0xFFFF
      pushU16LE withComment (UInt16.ofNat hc)
    else withComment
  let u := min plain.size 65535
  let sub := plain.extract 0 u
  let blk := pushU16LE (pushU16LE (ByteArray.empty.push 0x01) (UInt16.ofNat u)) (UInt16.ofNat u ^^^ 0xFFFF) ++ sub
  let crc := crc32 sub 0 sub.size
  let isz := UInt32.ofNat (sub.size % 4294967296)
  pushU32LE (pushU32LE (hdr ++ blk) crc) isz

private def mkZstdSkippable (n : Nat) (payload : ByteArray) : ByteArray :=
  let magic := UInt32.ofNat (0x184D2A50 + (n % 16))
  pushU32LE (pushU32LE ByteArray.empty magic) (UInt32.ofNat payload.size) ++ payload

private def mkZstdSingleFrameWithDid (plain : ByteArray) (withCrc : Bool) (didFlag : UInt8)
    (didRaw : ByteArray) : ByteArray :=
  let magic := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]
  let fcsFlag : UInt8 := if plain.size < 256 then 0x00 else 0x40
  let crcBit : UInt8 := if withCrc then 0x04 else 0x00
  let fhd : UInt8 := fcsFlag ||| 0x20 ||| crcBit ||| (didFlag &&& 0x03)
  let b1 := (magic.push fhd) ++ didRaw
  let hdr :=
    if plain.size < 256 then b1.push (UInt8.ofNat plain.size)
    else pushU16LE b1 (UInt16.ofNat (plain.size - 256))
  let body :=
    if plain.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
    else
      let u := min plain.size 131072
      let bh := (u <<< 3) ||| 1
      let bHdr := ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF), UInt8.ofNat ((bh >>> 16) &&& 0xFF)]
      hdr ++ bHdr ++ plain.extract 0 u
  if withCrc then pushU32LE body (xxh64Low32 (plain.extract 0 (min plain.size 131072))) else body

private def mkZstdSingleFrame (plain : ByteArray) (withCrc : Bool) (didByte : Option UInt8) : ByteArray :=
  match didByte with
  | some d => mkZstdSingleFrameWithDid plain withCrc 0x01 (ByteArray.mk #[d])
  | none => mkZstdSingleFrameWithDid plain withCrc 0x00 ByteArray.empty

private def mkZstdRleFrame (b : UInt8) (len : Nat) (withCrc : Bool) : ByteArray :=
  let magic := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]
  let fhd : UInt8 := 0x20 ||| (if withCrc then 0x04 else 0x00)
  let hdr := (magic.push fhd).push (UInt8.ofNat (min len 255))
  let take := min len 255
  let bh := (take <<< 3) ||| (1 <<< 1) ||| 1
  let bHdr := ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF), UInt8.ofNat ((bh >>> 16) &&& 0xFF)]
  let frame := hdr ++ bHdr.push b
  if withCrc then pushU32LE frame (xxh64Low32 (pushReplicateByte ByteArray.empty b take)) else frame

/-- Build a Zstandard frame with an explicit 8-byte `Frame_Content_Size` (`fcsFlag = 3`). -/
def mkZstdFrameFcs8 (plain : ByteArray) (fcs8 : UInt64) : ByteArray :=
  let magic := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0xC0, 0x38]
  let hdr := pushU64LE magic fcs8
  if plain.isEmpty then
    hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
  else
    let u := min plain.size 131072
    let bh := (u <<< 3) ||| 1
    let bHdr := ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF), UInt8.ofNat ((bh >>> 16) &&& 0xFF)]
    hdr ++ bHdr ++ plain.extract 0 u

private def sha256KLocal : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def sha256BytesLocal (bs : ByteArray) : ByteArray := Id.run do
  let rotr32 (x r : UInt32) : UInt32 := (x >>> r) ^^^ (x <<< (32 - r))
  let pushU32BE (out : ByteArray) (v : UInt32) : ByteArray :=
    let n := v.toNat
    (((out.push (UInt8.ofNat ((n >>> 24) &&& 0xFF))).push
      (UInt8.ofNat ((n >>> 16) &&& 0xFF))).push
      (UInt8.ofNat ((n >>> 8) &&& 0xFF))).push
      (UInt8.ofNat (n &&& 0xFF))
  let readU32BE (bs : ByteArray) (pos : Nat) : UInt32 :=
    UInt32.ofNat (
      ((bs.get! pos).toNat <<< 24) |||
      ((bs.get! (pos + 1)).toNat <<< 16) |||
      ((bs.get! (pos + 2)).toNat <<< 8) |||
      (bs.get! (pos + 3)).toNat)
  let bitLen : UInt64 := UInt64.ofNat (bs.size * 8)
  let rem := (bs.size + 1) % 64
  let zeroPad := if rem <= 56 then 56 - rem else 64 + 56 - rem
  let mut padded := bs.push 0x80
  padded := pushReplicateByte padded 0x00 zeroPad
  padded := pushU32BE padded (bitLen >>> 32).toUInt32
  padded := pushU32BE padded bitLen.toUInt32
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  let blocks := padded.size / 64
  let mut w := Array.replicate 64 (0 : UInt32)
  for b in [0:blocks] do
    let base := b * 64
    for i in [0:16] do
      w := w.set! i (readU32BE padded (base + i * 4))
    for i in [16:64] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := (rotr32 w15 7) ^^^ (rotr32 w15 18) ^^^ (w15 >>> 3)
      let s1 := (rotr32 w2 17) ^^^ (rotr32 w2 19) ^^^ (w2 >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h0
    let mut b_ := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    let mut f := h5
    let mut g := h6
    let mut h := h7
    for i in [0:64] do
      let s1 := (rotr32 e 6) ^^^ (rotr32 e 11) ^^^ (rotr32 e 25)
      let ch := (e &&& f) ^^^ ((e ^^^ 0xFFFFFFFF) &&& g)
      let temp1 := h + s1 + ch + sha256KLocal[i]! + w[i]!
      let s0 := (rotr32 a 2) ^^^ (rotr32 a 13) ^^^ (rotr32 a 22)
      let maj := (a &&& b_) ^^^ (a &&& c) ^^^ (b_ &&& c)
      let temp2 := s0 + maj
      h := g; g := f; f := e; e := d + temp1
      d := c; c := b_; b_ := a; a := temp1 + temp2
    h0 := h0 + a; h1 := h1 + b_; h2 := h2 + c; h3 := h3 + d
    h4 := h4 + e; h5 := h5 + f; h6 := h6 + g; h7 := h7 + h
  let mut out := ByteArray.emptyWithCapacity 32
  out := pushU32BE out h0; out := pushU32BE out h1; out := pushU32BE out h2; out := pushU32BE out h3
  out := pushU32BE out h4; out := pushU32BE out h5; out := pushU32BE out h6; out := pushU32BE out h7
  return out

private def mkXzCheckBytes (checkId : UInt8) (plain : ByteArray) : ByteArray :=
  if checkId == 0x00 then ByteArray.empty
  else if checkId == 0x01 then pushU32LE ByteArray.empty (crc32 plain 0 plain.size)
  else if checkId == 0x04 then pushU64LE ByteArray.empty (crc64Xz plain 0 plain.size)
  else sha256BytesLocal plain

private def mkXzBlockHdrWithSizes (compSz? uncompSz? : Option Nat) (dictProp : UInt8 := 0x16) : ByteArray :=
  let bflags : UInt8 :=
    (if compSz?.isSome then 0x40 else 0x00) |||
    (if uncompSz?.isSome then 0x80 else 0x00)
  let cBytes := match compSz? with | some c => Model.encodeXzVli c | none => ByteArray.empty
  let uBytes := match uncompSz? with | some u => Model.encodeXzVli u | none => ByteArray.empty
  let body0 := (ByteArray.empty.push bflags) ++ cBytes ++ uBytes ++ ByteArray.mk #[0x21, 0x01, dictProp]
  let rawLen := 1 + body0.size + 4
  let pad := (4 - (rawLen % 4)) % 4
  let hdrByte := UInt8.ofNat ((rawLen + pad) / 4 - 1)
  let bhPre := pushReplicateByte ((ByteArray.empty.push hdrByte) ++ body0) 0x00 pad
  pushU32LE bhPre (crc32 bhPre 0 bhPre.size)

private def mkXzUncompChunk (ctrl : UInt8) (chunk : ByteArray) : ByteArray :=
  let u16 := chunk.size - 1
  ((ByteArray.empty.push ctrl).push (UInt8.ofNat ((u16 >>> 8) &&& 0xFF))).push (UInt8.ofNat (u16 &&& 0xFF)) ++ chunk

/-- Build a 1-block `.xz` stream with explicit optional Block Header `compSz?` and `uncompSz?` fields. -/
def mkXzStreamWithBlockSizes (checkId : UInt8) (plain : ByteArray)
    (bhComp? bhUncomp? : Option Nat) : ByteArray :=
  let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, checkId]
  let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
  let l2Raw :=
    if plain.isEmpty then ByteArray.mk #[0x00]
    else (mkXzUncompChunk 0x01 (plain.extract 0 (min plain.size 65536))).push 0x00
  let plainSub := plain.extract 0 (min plain.size 65536)
  let bhdr := mkXzBlockHdrWithSizes bhComp? bhUncomp?
  let l2Pad := (4 - l2Raw.size % 4) % 4
  let l2Padded := pushReplicateByte l2Raw 0x00 l2Pad
  let chk := mkXzCheckBytes checkId plainSub
  let unpadded := bhdr.size + l2Raw.size + chk.size
  let buf1 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 1 ++
    Model.encodeXzVli unpadded ++ Model.encodeXzVli plainSub.size
  let ipad := (4 - buf1.size % 4) % 4
  let buf2 := pushReplicateByte buf1 0x00 ipad
  let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
  let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
  let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, checkId]
  let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
  shdr ++ bhdr ++ l2Padded ++ chk ++ idxRaw ++ ftr

/-- Build a valid 2-block `.xz` stream (`numRecs = 2`) with `checkId` over non-empty chunks `p1` and `p2`. -/
def mkXzTwoBlockStream (checkId : UInt8) (p1 p2 : ByteArray) : ByteArray :=
  let s1 := if p1.isEmpty then ByteArray.mk #[0x41] else p1.extract 0 (min p1.size 65536)
  let s2 := if p2.isEmpty then ByteArray.mk #[0x42] else p2.extract 0 (min p2.size 65536)
  let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, checkId]
  let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
  let mkBlk (sub : ByteArray) : ByteArray × Nat × Nat :=
    let l2 := (mkXzUncompChunk 0x01 sub).push 0x00
    let bh := mkXzBlockHdrWithSizes (some l2.size) (some sub.size)
    let pad := (4 - l2.size % 4) % 4
    let chk := mkXzCheckBytes checkId sub
    let unpad := bh.size + l2.size + chk.size
    (bh ++ pushReplicateByte l2 0x00 pad ++ chk, unpad, sub.size)
  let (blk1, u1, uc1) := mkBlk s1
  let (blk2, u2, uc2) := mkBlk s2
  let buf1 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 2 ++
    Model.encodeXzVli u1 ++ Model.encodeXzVli uc1 ++
    Model.encodeXzVli u2 ++ Model.encodeXzVli uc2
  let ipad := (4 - buf1.size % 4) % 4
  let buf2 := pushReplicateByte buf1 0x00 ipad
  let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
  let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
  let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, checkId]
  let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
  shdr ++ blk1 ++ blk2 ++ idxRaw ++ ftr

private def mkXzStreamWithCheck (checkId : UInt8) (chunks : Array ByteArray) (plain : ByteArray) : ByteArray :=
  let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, checkId]
  let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
  let bhdr := mkXzBlockHdrWithSizes none none
  let l2Raw := (chunks.foldl (· ++ ·) ByteArray.empty).push 0x00
  let l2Pad := (4 - l2Raw.size % 4) % 4
  let l2Padded := pushReplicateByte l2Raw 0x00 l2Pad
  let chk := mkXzCheckBytes checkId plain
  let unpadded := bhdr.size + l2Raw.size + chk.size
  let buf0 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 1
  let buf1 := buf0 ++ Model.encodeXzVli unpadded ++ Model.encodeXzVli plain.size
  let ipad := (4 - buf1.size % 4) % 4
  let buf2 := pushReplicateByte buf1 0x00 ipad
  let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
  let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
  let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, checkId]
  let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
  shdr ++ bhdr ++ l2Padded ++ chk ++ idxRaw ++ ftr

/-- Build crafted spec-valid rich header streams covering `gzip` optional fields, `zstd` variants, and `.xz` check types. -/
def genRichHeaderStream (codec : Codec) (r : Rng) : ByteArray × Rng :=
  match codec with
  | .gzip =>
    let (flg, r1) := r.choose #[0x01, 0x04, 0x08, 0x10, 0x1D] 0x08
    let (hcrc, r2) := r1.nextBool
    let (p, r3) := r2.nextBytesRange 0 64
    (mkGzipMember p flg hcrc, r3)
  | .zstd =>
    let (variant, r1) := r.nextNat 6
    let (withCrc, r2) := r1.nextBool
    if variant == 0 then
      let (p, r3) := r2.nextBytesRange 0 64
      (mkZstdSingleFrame p withCrc (some 0x00), r3)
    else if variant == 1 then
      let (b, r3) := r2.nextU8
      let (len, r4) := r3.nextRange 0 32
      (mkZstdRleFrame b len withCrc, r4)
    else if variant == 2 then
      (mkZstdSingleFrame ByteArray.empty withCrc none, r2)
    else if variant == 3 then
      let (p, r3) := r2.nextBytesRange 1 300
      (mkZstdSingleFrame p withCrc none, r3)
    else if variant == 4 then
      let (use4ByteDid, r3) := r2.nextBool
      let (p, r4) := r3.nextBytesRange 0 48
      if use4ByteDid then
        (mkZstdSingleFrameWithDid p withCrc 0x03 (ByteArray.mk #[0x00, 0x00, 0x00, 0x00]), r4)
      else
        (mkZstdSingleFrameWithDid p withCrc 0x02 (ByteArray.mk #[0x00, 0x00]), r4)
    else
      let (unknownSentinel, r3) := r2.nextBool
      let (p, r4) := r3.nextBytesRange 0 48
      let fcs8 : UInt64 := if unknownSentinel then 0xFFFFFFFFFFFFFFFF else UInt64.ofNat p.size
      (mkZstdFrameFcs8 p fcs8, r4)
  | .xz =>
    let (checkId, r1) := r.choose #[0x00, 0x01, 0x04, 0x0A] 0x04
    let (mode, r2) := r1.nextNat 5
    if mode == 0 then
      (mkXzStreamWithCheck checkId #[] ByteArray.empty, r2)
    else if mode == 1 then
      let (p1, r3) := r2.nextBytesRange 1 32
      let (p2, r4) := r3.nextBytesRange 1 32
      let c1 := mkXzUncompChunk 0x01 p1
      let c2 := mkXzUncompChunk 0x02 p2
      (mkXzStreamWithCheck checkId #[c1, c2] (p1 ++ p2), r4)
    else if mode == 2 then
      let (p, r3) := r2.nextBytesRange 1 48
      let compLen := 3 + p.size + 1
      (mkXzStreamWithBlockSizes checkId p (some compLen) (some p.size), r3)
    else if mode == 3 then
      let (p1, r3) := r2.nextBytesRange 1 24
      let (p2, r4) := r3.nextBytesRange 1 24
      (mkXzTwoBlockStream checkId p1 p2, r4)
    else
      let (dp, r3) := r2.choose #[29, 30, 40] 29
      let bhdrBody := ByteArray.mk #[0x02, 0x00, 0x21, 0x01, dp, 0x00, 0x00, 0x00]
      let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]
      let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
      let bhdr := pushU32LE bhdrBody (crc32 bhdrBody 0 bhdrBody.size)
      let chk := pushU64LE ByteArray.empty (crc64Xz ByteArray.empty 0 0)
      let unpadded := bhdr.size + 1 + chk.size
      let buf1 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 1 ++
        Model.encodeXzVli unpadded ++ Model.encodeXzVli 0
      let ipad := (4 - buf1.size % 4) % 4
      let buf2 := pushReplicateByte buf1 0x00 ipad
      let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
      let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
      let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, 0x04]
      let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
      (shdr ++ bhdr ++ ByteArray.mk #[0x00, 0x00, 0x00, 0x00] ++ chk ++ idxRaw ++ ftr, r3)

private def mkXzEmptyBlockWithHdr (bhdrBody : ByteArray) : ByteArray :=
  let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]
  let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
  let bhdr := pushU32LE bhdrBody (crc32 bhdrBody 0 bhdrBody.size)
  let l2Padded := ByteArray.mk #[0x00, 0x00, 0x00, 0x00]
  let chk := pushU64LE ByteArray.empty (crc64Xz ByteArray.empty 0 0)
  let unpadded := bhdr.size + 1 + chk.size
  let buf1 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 1 ++
    Model.encodeXzVli unpadded ++ Model.encodeXzVli 0
  let ipad := (4 - buf1.size % 4) % 4
  let buf2 := pushReplicateByte buf1 0x00 ipad
  let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
  let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
  let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, 0x04]
  let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
  shdr ++ bhdr ++ l2Padded ++ chk ++ idxRaw ++ ftr

/-- Build a cross-codec, legacy, or invalid-header confusion vector for `codec`. -/
def genForeignOrLegacyStream (codec : Codec) (r : Rng) : ByteArray × Rng :=
  let gzEmpty := Model.encodeStored .gzip ByteArray.empty
  let zstEmpty := Model.encodeStored .zstd ByteArray.empty
  let xzEmpty := Model.encodeStored .xz ByteArray.empty
  let lz4 := ByteArray.mk #[0x04, 0x22, 0x4D, 0x18, 0x64, 0x40, 0xA7, 0x00, 0x00, 0x00, 0x00]
  let legacyZstd := ByteArray.mk #[0x25, 0xB5, 0x2F, 0xFD, 0x00, 0x00, 0x00, 0x00, 0x00]
  let lzw := ByteArray.mk #[0x1F, 0x9D, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let oldGz := ByteArray.mk #[0x1F, 0x9E, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03]
  let pack := ByteArray.mk #[0x1F, 0x1E, 0x00, 0x04, 0x00, 0x00]
  let lzh := ByteArray.mk #[0x1F, 0xA0, 0x00, 0x00, 0x00, 0x00]
  let pkzip := ByteArray.mk #[0x50, 0x4B, 0x03, 0x04, 0x0A, 0x00, 0x00, 0x00, 0x00, 0x00]
  let lzmaAlone := ByteArray.mk #[0x5D, 0x00, 0x00, 0x80, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00]
  let mkXzBadDict41 : ByteArray :=
    mkXzEmptyBlockWithHdr (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 41, 0x00, 0x00, 0x00])
  let mkXzBadFilter : ByteArray :=
    mkXzEmptyBlockWithHdr (ByteArray.mk #[0x02, 0x01, 0x7E, 0x00, 0x21, 0x01, 0x16, 0x00])
  match codec with
  | .zstd =>
    r.choose #[gzEmpty, xzEmpty, lz4, legacyZstd, zstEmpty ++ gzEmpty] gzEmpty
  | .gzip =>
    r.choose #[lzw, oldGz, pack, lzh, pkzip, zstEmpty, xzEmpty, gzEmpty ++ lzw] lzw
  | .xz =>
    r.choose #[gzEmpty, zstEmpty, lzmaAlone, lz4, pkzip, mkXzBadDict41, mkXzBadFilter] lzmaAlone

/-- Apply surgical bit/flag/checksum/trailer/VLI corruptions to `base` for `codec`. -/
def corruptStreamSurgically (codec : Codec) (base : ByteArray) (r : Rng) : ByteArray × Rng :=
  let (kind, r1) := r.nextNat 7
  if base.isEmpty then
    (ByteArray.mk #[0xFF, 0x00], r1)
  else if kind == 0 then
    let (idx, r2) := r1.nextNat base.size
    let (mask, r3) := r2.choose #[0x01, 0x80, 0xFF] 0x01
    (base.set! idx (base.get! idx ^^^ mask), r3)
  else if kind == 1 then
    match codec with
    | .gzip =>
      if base.size >= 4 then
        let (bit, r2) := r1.choose #[0x20, 0x40, 0x80] 0x80
        (base.set! 3 (base.get! 3 ||| bit), r2)
      else (base.push 0xFF, r1)
    | .zstd =>
      if base.size >= 5 then (base.set! 4 (base.get! 4 ||| 0x08), r1)
      else (base.push 0xFF, r1)
    | .xz =>
      if base.size >= 14 then (base.set! 13 (base.get! 13 ||| 0x04), r1)
      else (base.push 0xFF, r1)
  else if kind == 2 then
    match codec with
    | .xz =>
      let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]
      let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
      let nonCanonIdx := ByteArray.mk #[0x00, 0x80, 0x00, 0x00]
      let icrc := pushU32LE nonCanonIdx (crc32 nonCanonIdx 0 4)
      let ftrBody := pushU32LE ByteArray.empty 1 ++ ByteArray.mk #[0x00, 0x04]
      let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
      (shdr ++ icrc ++ ftr, r1)
    | _ =>
      let idx := base.size - 1
      (base.set! idx (base.get! idx ^^^ 0x01), r1)
  else if kind == 3 then
    match codec with
    | .xz =>
      let c1 := mkXzUncompChunk 0x02 (ByteArray.mk #[0x41])
      (mkXzStreamWithCheck 0x04 #[c1] (ByteArray.mk #[0x41]), r1)
    | .gzip =>
      if base.size >= 10 then
        let (sub, r2) := r1.nextNat 2
        if sub == 0 then
          (base.set! 2 0x09, r2)
        else
          let idx := base.size - 1 - (if base.size > 4 then 4 else 0)
          (base.set! idx (base.get! idx ^^^ 0x42), r2)
      else
        (base.push 0xFF, r1)
    | .zstd =>
      if base.size >= 8 then
        (base.extract 0 (base.size - 1), r1)
      else
        (base.push 0xFF, r1)
  else if kind == 4 then
    match codec with
    | .zstd =>
      let (d, r2) := r1.nextRange 1 200
      let (didWidth, r3) := r2.nextNat 3
      let b := UInt8.ofNat d
      if didWidth == 0 then
        (mkZstdSingleFrame (ByteArray.mk #[0x41]) true (some b), r3)
      else if didWidth == 1 then
        (mkZstdSingleFrameWithDid (ByteArray.mk #[0x41]) true 0x02 (ByteArray.mk #[0x00, b]), r3)
      else
        (mkZstdSingleFrameWithDid (ByteArray.mk #[0x41]) true 0x03 (ByteArray.mk #[0x00, b, 0x00, b]), r3)
    | .gzip =>
      if base.size > 4 then
        let (drop, r2) := r1.nextRange 1 (min 9 (base.size - 1))
        (base.extract 0 (base.size - drop), r2)
      else
        (base.push 0xFF, r1)
    | .xz =>
      if base.size >= 24 then
        let (sub, r2) := r1.nextNat 2
        if sub == 0 then
          (base.set! (base.size - 1) 0x00, r2)
        else
          let (drop, r3) := r2.nextRange 1 (min 8 (base.size - 1))
          (base.extract 0 (base.size - drop), r3)
      else
        (base.push 0xFF, r1)
  else if kind == 5 then
    match codec with
    | .zstd =>
      (mkZstdFrameFcs8 ("hello".toUTF8) 99, r1)
    | .xz =>
      let (sub, r2) := r1.nextNat 2
      if sub == 0 then
        (mkXzStreamWithBlockSizes 0x04 ("test".toUTF8) none (some 5), r2)
      else
        let okS := mkXzStreamWithBlockSizes 0x0A ("sha256".toUTF8) (some 10) (some 6)
        (okS.set! (okS.size - 24) (okS.get! (okS.size - 24) ^^^ 0x01), r2)
    | .gzip =>
      let gz := Model.encodeStored .gzip ("hello".toUTF8)
      (gz.set! (gz.size - 6) (gz.get! (gz.size - 6) ^^^ 0x01), r1)
  else
    let (extra, r2) := r1.choose #[ByteArray.mk #[0x01], ByteArray.mk #[0xFF, 0xFE]] (ByteArray.mk #[0x01])
    (base ++ extra, r2)

/-- Build multi-frame, skippable, and NUL-padded variants from two valid streams `s1` and `s2`. -/
def genMultiOrPadded (codec : Codec) (s1 s2 : ByteArray) (r : Rng) : (ByteArray × String) × Rng :=
  let (kind, r1) := r.nextNat 5
  match codec with
  | .gzip =>
    if kind == 0 then ((s1 ++ s2, "multi"), r1)
    else if kind == 1 then ((s1 ++ pushReplicateByte ByteArray.empty 0x00 4, "padded"), r1)
    else if kind == 2 then ((s1 ++ ByteArray.mk #[0x00, 0x00] ++ s2, "badPad"), r1)
    else if kind == 3 then ((s1 ++ ByteArray.mk #[0x00, 0x00, 0x01], "badPad"), r1)
    else ((ByteArray.mk #[0x00, 0x00, 0x00, 0x00] ++ s1, "leadPad"), r1)
  | .zstd =>
    let skip0 := mkZstdSkippable 0 (ByteArray.mk #[0x11, 0x22, 0x33])
    if kind == 0 then ((s1 ++ s2, "multi"), r1)
    else if kind == 1 then ((skip0, "skipOnly"), r1)
    else if kind == 2 then ((skip0 ++ s1, "skipPre"), r1)
    else if kind == 3 then ((s1 ++ skip0, "skipPost"), r1)
    else ((s1 ++ ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x0A, 0x00, 0x00, 0x00], "badSkip"), r1)
  | .xz =>
    if kind == 0 then ((s1 ++ s2, "multi"), r1)
    else if kind == 1 then ((s1 ++ ByteArray.mk #[0x00, 0x00, 0x00, 0x00], "padded"), r1)
    else if kind == 2 then ((s1 ++ ByteArray.mk #[0x00, 0x00, 0x00, 0x00] ++ s2, "padMulti"), r1)
    else if kind == 3 then ((s1 ++ ByteArray.mk #[0x00, 0x00, 0x00], "oddPad"), r1)
    else ((ByteArray.mk #[0x00, 0x00, 0x00, 0x00] ++ s1, "leadPad"), r1)

private def pushU16Gen (ba : ByteArray) (v : Nat) : ByteArray :=
  (ba.push (UInt8.ofNat (v &&& 0xFF))).push (UInt8.ofNat ((v >>> 8) &&& 0xFF))

private def pushU32Gen (ba : ByteArray) (v : Nat) : ByteArray :=
  (((ba.push (UInt8.ofNat (v &&& 0xFF))).push (UInt8.ofNat ((v >>> 8) &&& 0xFF))).push
    (UInt8.ofNat ((v >>> 16) &&& 0xFF))).push (UInt8.ofNat ((v >>> 24) &&& 0xFF))

private def mkZstdSkipFrame (n : Nat) : ByteArray :=
  let body := ByteArray.mk (Array.replicate n 0xAA)
  let hdr := pushU32Gen (pushU32Gen ByteArray.empty 0x184D2A50) n
  hdr ++ body

private def mkZstdBlockHdr (last : Bool) (btype bsize : Nat) : ByteArray :=
  let v := (bsize <<< 3) ||| (btype <<< 1) ||| (if last then 1 else 0)
  ((ByteArray.empty.push (UInt8.ofNat (v &&& 0xFF))).push
    (UInt8.ofNat ((v >>> 8) &&& 0xFF))).push (UInt8.ofNat ((v >>> 16) &&& 0xFF))

private def mkZstdFrameCustom (wd : UInt8) (fcs4? : Option Nat) (blocks : List ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]
  let fhd : UInt8 := match fcs4? with | some _ => 0x80 | none => 0x00
  out := out.push fhd
  out := out.push wd
  if let some fcs := fcs4? then
    out := pushU32Gen out fcs
  for blk in blocks do
    out := out ++ blk
  return out

private def crc32XzGen (ba : ByteArray) : UInt32 :=
  LeanSwe.Compress.crc32 ba 0 ba.size

private def mkXzBadUncompLenStream (uncompLen : Nat) (lzma2Body : ByteArray) : ByteArray :=
  let sflags := ByteArray.mk #[0x00, 0x00]
  let hdr := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ sflags ++
    pushU32Gen ByteArray.empty (crc32XzGen sflags).toNat
  let hi := (uncompLen - 1) >>> 16
  let lo := (uncompLen - 1) &&& 0xFFFF
  let csz := lzma2Body.size - 1
  let ctrl : UInt8 := UInt8.ofNat (0xE0 ||| (hi &&& 0x1F))
  let chunk := ByteArray.mk #[ctrl, UInt8.ofNat (lo >>> 8), UInt8.ofNat (lo &&& 0xFF),
    UInt8.ofNat (csz >>> 8), UInt8.ofNat (csz &&& 0xFF), 0x5D] ++ lzma2Body ++ ByteArray.mk #[0x00]
  let bhPre := ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]
  let bh := bhPre ++ pushU32Gen ByteArray.empty (crc32XzGen bhPre).toNat
  let unpSz := bh.size + chunk.size
  let padCnt := (4 - chunk.size % 4) % 4
  let blk := bh ++ chunk ++ ByteArray.mk (Array.replicate padCnt 0x00)
  let rec encodeVli (n : Nat) (fuel : Nat) : ByteArray :=
    match fuel with
    | 0 => ByteArray.empty
    | fuel + 1 =>
      if n < 128 then ByteArray.mk #[UInt8.ofNat n]
      else ByteArray.mk #[UInt8.ofNat ((n &&& 0x7F) ||| 0x80)] ++ encodeVli (n >>> 7) fuel
  let idxBody := ByteArray.mk #[0x00, 0x01] ++ encodeVli unpSz 9 ++ encodeVli uncompLen 9
  let idxPad := (4 - idxBody.size % 4) % 4
  let idxPadded := idxBody ++ ByteArray.mk (Array.replicate idxPad 0x00)
  let idxRaw := idxPadded ++ pushU32Gen ByteArray.empty (crc32XzGen idxPadded).toNat
  let bwd : Nat := idxRaw.size / 4 - 1
  let ftrPre := pushU32Gen ByteArray.empty bwd ++ sflags
  let ftr := pushU32Gen ByteArray.empty (crc32XzGen ftrPre).toNat ++ ftrPre ++ ByteArray.mk #[0x59, 0x5A]
  hdr ++ blk ++ idxRaw ++ ftr

private def mkZstdRawSplitRingStream (curInTarget : Nat) : ByteArray := Id.run do
  let warmupOut := 524288 + 131073 - 262208
  let mut f := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x38]
  f := f ++ mkZstdBlockHdr false 1 131072 ++ ByteArray.mk #[0x58]
  f := f ++ mkZstdBlockHdr false 1 131072 ++ ByteArray.mk #[0x58]
  f := f ++ mkZstdBlockHdr false 1 (warmupOut - 262144) ++ ByteArray.mk #[0x58]
  f := f ++ mkZstdBlockHdr false 1 131072 ++ ByteArray.mk #[0x41]
  let rawLen := curInTarget - (f.size + 4 + 3)
  let rleB := 262208 - 131072 - rawLen
  f := f ++ mkZstdBlockHdr false 1 rleB ++ ByteArray.mk #[0x42]
  f := f ++ mkZstdBlockHdr false 0 rawLen ++ ByteArray.mk (Array.replicate rawLen 0x42)
  f := f ++ mkZstdBlockHdr false 0 100000 ++ ByteArray.mk (Array.replicate 100000 0x5A)
  let blk := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 18, 0x01, 0xE3, 0x93, 0x04]
  f ++ mkZstdBlockHdr true 2 blk.size ++ blk

private def mkGzipPkzipChunkBoundaryStream (nulPad : Nat) : ByteArray := Id.run do
  let mut hdr := ByteArray.mk #[0x1F, 0x8B, 0x08, 0x0C, 0, 0, 0, 0, 0, 0x03]
  hdr := pushU16LE hdr 65535
  hdr := pushReplicateByte hdr 0x41 65535
  hdr := pushReplicateByte hdr 0x42 196591
  hdr := hdr.push 0x00
  let mut plain := ByteArray.mk #[0x50, 0x4B, 0x03, 0x04]
  plain := pushReplicateByte plain 0x43 44
  let len16 := UInt16.ofNat plain.size
  let nlen16 := len16 ^^^ 0xFFFF
  let mut m1 := hdr.push 0x01
  m1 := pushU16LE (pushU16LE m1 len16) nlen16
  m1 := m1 ++ plain
  m1 := pushU32LE m1 (crc32 plain 0 plain.size)
  m1 := pushU32LE m1 (UInt32.ofNat plain.size)
  pushReplicateByte m1 0x00 nulPad

/-- Generate codec boundary edge-case operations targeting zstd single-pass/ring-wrap, gzip FEXTRA/PKZIP-rewind, and LZMA2 bounds. -/
def genCodecBoundaryEdgeOp (codec : Codec) (r : Rng) : CompressFuzzOp × Rng :=
  match codec with
  | .zstd =>
    let (kind, r1) := r.nextNat 6
    if kind == 0 then
      let (fcs, r2) := r1.nextRange 65537 131073
      let (wd, r3) := r2.choose #[0x89, 0x00] 0x89
      let rle1 := mkZstdBlockHdr false 1 65535 ++ ByteArray.mk #[0x41]
      let rem := fcs - 65535
      let rle2 := mkZstdBlockHdr true 1 rem ++ ByteArray.mk #[0x41]
      let (skipLen, r4) := r3.choose #[70000, 131052, 131070] 131052
      let (longFrame, r5) := r4.nextBool
      let s :=
        if longFrame then
          mkZstdFrameCustom wd (some 2000) [mkZstdBlockHdr false 0 2000 ++ ByteArray.mk (Array.replicate 2000 0x41),
            mkZstdBlockHdr false 0 131072 ++ ByteArray.mk (Array.replicate 131072 0x41), mkZstdBlockHdr true 1 1 ++ ByteArray.mk #[0x41]]
        else
          mkZstdSkipFrame skipLen ++ mkZstdFrameCustom wd (some fcs) [rle1, rle2]
      (.decompress .zstd s "zstdFcsBoundary", r5)
    else if kind == 1 then
      let (mode, r2) := r1.nextNat 4
      let bt2 := mkZstdBlockHdr false 2 0
      let raw5 := mkZstdBlockHdr true 0 5 ++ "hello".toUTF8
      let f := mkZstdFrameCustom 0x00 (some 5) [bt2, raw5]
      let s :=
        if mode == 0 then f
        else if mode == 1 then mkZstdSkipFrame 131080 ++ f
        else if mode == 2 then mkZstdSkipFrame 131052 ++ mkZstdSkipFrame 131075 ++ f
        else mkZstdSkipFrame 99992 ++ mkZstdSkipFrame 40007 ++ f
      (.decompress .zstd s "zstdBt2Zero", r2)
    else if kind == 2 then
      let f := mkZstdFrameCustom 0x00 (some 12) [mkZstdBlockHdr false 0 12 ++ "hello_world!".toUTF8, mkZstdBlockHdr true 0 0]
      let fLong := mkZstdFrameCustom 0x00 (some 131080)
        [mkZstdBlockHdr false 0 131072 ++ ByteArray.mk (Array.replicate 131072 0x42),
         mkZstdBlockHdr false 0 8 ++ "12345678".toUTF8,
         mkZstdBlockHdr true 0 0]
      let fGtFcs := mkZstdFrameCustom 0x00 (some 4) [mkZstdBlockHdr false 0 12 ++ "hello_world!".toUTF8, mkZstdBlockHdr true 0 0]
      let fLtFcs := mkZstdFrameCustom 0x00 (some 20) [mkZstdBlockHdr false 0 12 ++ "hello_world!".toUTF8, mkZstdBlockHdr true 0 0]
      let fCoalLt := mkZstdSkipFrame 131050 ++ fLtFcs
      let fCoalAf := mkZstdSkipFrame 131050 ++ ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0xAF, 0x28, 0x00, 0x00] ++ "hello".toUTF8
      let fEmptyLastOver := mkZstdFrameCustom 0x00 (some 2000)
        [mkZstdBlockHdr false 1 1000 ++ ByteArray.mk #[0x41],
         mkZstdBlockHdr false 1 1500 ++ ByteArray.mk #[0x41],
         mkZstdBlockHdr true 0 0]
      let (pick, r2) := r1.nextNat 7
      let s :=
        if pick == 0 then f
        else if pick == 1 then fLong
        else if pick == 2 then fGtFcs
        else if pick == 3 then fLtFcs
        else if pick == 4 then fCoalLt
        else if pick == 5 then fCoalAf
        else fEmptyLastOver
      (.decompress .zstd s "zstdEmptyRaw", r2)
    else if kind == 3 then
      let rle2k := mkZstdBlockHdr false 1 2000 ++ ByteArray.mk #[0x41]
      let lastRle := mkZstdBlockHdr true 1 1 ++ ByteArray.mk #[0x42]
      let (fcs, r2) := r1.choose #[2001, 131072] 2001
      let (sub, r3) := r2.nextNat 4
      if sub == 0 then
        let s := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0xA0] ++ pushU32Gen ByteArray.empty fcs ++ rle2k ++ lastRle
        (.decompress .zstd s "zstdBlockMax", r3)
      else if sub == 1 then
        let s := mkZstdSkipFrame 131072 ++ ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x00] ++
          mkZstdBlockHdr true 1 0 ++ ByteArray.mk #[0x41]
        (.decompress .zstd s "zstdSingleSegZero", r3)
      else if sub == 2 then
        let rleBig := mkZstdBlockHdr false 1 131072 ++ ByteArray.mk #[0x41]
        let s := mkZstdFrameCustom 0x50 (some 200000) [rleBig, rleBig, rleBig, rleBig, rleBig, lastRle]
        (.decompressWith .zstd { maxOutputBytes := 250000 } s "zstdCapFcs", r3)
      else
        (.decompress .zstd (mkZstdFrameCustom 0x00 (some fcs) [rle2k, lastRle]) "zstdBlockMax", r3)
    else if kind == 4 then
      let (mode, r2) := r1.nextNat 6
      if mode == 0 then
        let b0 := mkZstdBlockHdr false 0 800 ++ ByteArray.mk (Array.replicate 800 0x41)
        let b1 := mkZstdBlockHdr false 0 800 ++ ByteArray.mk (Array.replicate 800 0x42)
        let b2 := mkZstdBlockHdr false 0 800 ++ ByteArray.mk (Array.replicate 800 0x43)
        let seq := ByteArray.mk #[0x01, 0x00, 0x00] ++ ByteArray.mk #[0x01, 0x54, 0x00, 0x08, 0x05]
        let b3 := mkZstdBlockHdr true 2 seq.size ++ seq
        (.decompress .zstd (mkZstdFrameCustom 0x00 none [b0, b1, b2, b3]) "zstdRing", r2)
      else if mode == 1 then
        let blocks4 := [0x41, 0x42, 0x43, 0x44].map fun b => mkZstdBlockHdr false 1 1000 ++ ByteArray.mk #[UInt8.ofNat b]
        let seq := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 0x0b, 0x00, 0xaf, 0x0d]
        let lastSeq := mkZstdBlockHdr true 2 seq.size ++ seq
        (.decompress .zstd (mkZstdFrameCustom 0x00 none (blocks4 ++ [lastSeq])) "zstdRing", r2)
      else if mode == 2 then
        let f1 := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x50] ++ mkZstdBlockHdr true 1 1000 ++ ByteArray.mk #[0x5A]
        let blocks8 := [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48].map fun b =>
          mkZstdBlockHdr false 1 700 ++ ByteArray.mk #[UInt8.ofNat b]
        let seq := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 0x0b, 0x00, 0xbb, 0x0b]
        let lastSeq := mkZstdBlockHdr true 2 seq.size ++ seq
        let f2 := mkZstdFrameCustom 0x00 none (blocks8 ++ [lastSeq])
        (.decompress .zstd (f1 ++ f2) "zstdRing", r2)
      else if mode == 3 then
        let blocks4 := [0x41, 0x42, 0x43, 0x44].map fun b => mkZstdBlockHdr false 1 1000 ++ ByteArray.mk #[UInt8.ofNat b]
        let seq := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 0x0b, 0x00, 0xaf, 0x0d]
        let lastSeq := mkZstdBlockHdr true 2 seq.size ++ seq
        (.decompress .zstd (mkZstdSkipFrame 131072 ++ mkZstdFrameCustom 0x00 (some 4004) (blocks4 ++ [lastSeq])) "zstdSmallFcsRing", r2)
      else if mode == 4 then
        let f1 := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x50] ++ mkZstdBlockHdr true 1 1000 ++ ByteArray.mk #[0x5A]
        let skips := Id.run do
          let mut acc := ByteArray.empty
          for _ in [0:127] do
            acc := acc ++ mkZstdSkipFrame 0
          return acc
        let blocks8 := [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48].map fun b =>
          mkZstdBlockHdr false 1 700 ++ ByteArray.mk #[UInt8.ofNat b]
        let seq := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 0x0b, 0x00, 0xbb, 0x0b]
        let lastSeq := mkZstdBlockHdr true 2 seq.size ++ seq
        let f2 := mkZstdFrameCustom 0x00 none (blocks8 ++ [lastSeq])
        (.decompress .zstd (f1 ++ skips ++ f2) "zstdOversized128", r2)
      else
        let rle100k := mkZstdBlockHdr false 1 100000 ++ ByteArray.mk #[0x41]
        let rle60k := mkZstdBlockHdr true 1 60000 ++ ByteArray.mk #[0x42]
        (.decompressWith .zstd { maxOutputBytes := 140000 } (mkZstdFrameCustom 0x50 none [rle100k, rle60k]) "zstdRing", r2)
    else
      let (curIn, r2) := r1.choose #[131069, 131070, 131071, 131072] 131070
      (.decompress .zstd (mkZstdRawSplitRingStream curIn) "zstdRawSplitRing", r2)
  | .gzip =>
    let (usePkRewind, r0) := r.nextBool
    if usePkRewind then
      let (nulPad, r1) := r0.choose #[1, 2, 4] 2
      let s := mkGzipPkzipChunkBoundaryStream nulPad
      let (useBounded, r2) := r1.nextBool
      if useBounded then
        let (lim, r3) := r2.choose #[16, 48, 64] 48
        (.decompressWith .gzip { maxOutputBytes := lim } s "gzipPkzipRewind", r3)
      else
        (.decompress .gzip s "gzipPkzipRewind", r2)
    else
      let payload := ByteArray.mk (Array.replicate 4096 0x41)
      let base := Model.encodeStored .gzip payload
      let fextra := ByteArray.mk #[0x02, 0x00, 0x1F, 0x9D]
      let withExtra := base.extract 0 3 ++ ByteArray.mk #[0x04] ++ base.extract 4 10 ++ fextra ++ base.extract 10 base.size
      let (lim, r1) := r0.choose #[1, 64, 1024, 4096] 64
      (.decompressWith .gzip { maxOutputBytes := lim } withExtra "gzipFextra", r1)
  | .xz =>
    let (kind, r1) := r.nextNat 3
    if kind == 0 then
      let xzComp88 := ByteArray.mk #[
        0xfd, 0x37, 0x7a, 0x58, 0x5a, 0x00, 0x00, 0x04, 0xe6, 0xd6, 0xb4, 0x46, 0x02, 0x00, 0x21, 0x01,
        0x10, 0x00, 0x00, 0x00, 0xa8, 0x70, 0x8e, 0x86, 0xe0, 0x06, 0x3f, 0x00, 0x17, 0x5d, 0x00, 0x30,
        0x98, 0x88, 0x98, 0x3b, 0xf8, 0xbb, 0xf1, 0x55, 0x8a, 0x0d, 0xa7, 0xd6, 0x59, 0x19, 0x2c, 0x7e,
        0x81, 0xd5, 0x11, 0x17, 0x14, 0x00, 0x00, 0x00, 0xb5, 0xa6, 0x26, 0x4c, 0x08, 0xeb, 0xf5, 0x35,
        0x00, 0x01, 0x33, 0xc0, 0x0c, 0x00, 0x00, 0x00, 0xbd, 0xf6, 0x78, 0xe2, 0xb1, 0xc4, 0x67, 0xfb,
        0x02, 0x00, 0x00, 0x00, 0x00, 0x04, 0x59, 0x5a]
      let (lim, r2) := r1.choose #[1, 8, 64, 512, 1024, 1599, 1600, 1601] 1024
      (.decompressWith .xz { maxOutputBytes := lim } xzComp88 "xzPartialCopy", r2)
    else if kind == 1 then
      let cut47 := ByteArray.mk #[
        0xfd, 0x37, 0x7a, 0x58, 0x5a, 0x00, 0x00, 0x00, 0xff, 0x12, 0xd9, 0x41, 0x02, 0x00, 0x21, 0x01,
        0x00, 0x00, 0x00, 0x00, 0x37, 0x27, 0x97, 0xd6, 0xe0, 0x35, 0xb6, 0x00, 0x2e, 0x5d, 0x00, 0x28,
        0xef, 0xcd, 0xbf, 0x29, 0x7d, 0x3e, 0x27, 0x1d, 0x47, 0x22, 0x2e, 0xc5, 0x00, 0xd9, 0x3e, 0x8b,
        0xad, 0x4e, 0x2e, 0x27, 0xc4, 0x7e, 0xb1, 0x49, 0x76, 0x34, 0xc5, 0x26, 0xf3, 0xff, 0xd4, 0x0d,
        0xd3, 0x5e, 0x06, 0xf5, 0x56, 0x34, 0xc9, 0x0d, 0x2d, 0x9f, 0x4e, 0x18, 0x3e, 0x00, 0x00, 0x00,
        0x00, 0x01, 0x42, 0xb7, 0x6b, 0x00, 0x00, 0x00, 0xbc, 0xdb, 0x05, 0xcf, 0xa8, 0x00, 0x0a, 0xfc,
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59, 0x5a]
      let (lim, r2) := r1.choose #[8480, 12288, 12500, 12750, 12751, 13000] 12500
      (.decompressWith .xz { maxOutputBytes := lim } cut47 "xzDictWrap", r2)
    else
      let (uLen, r2) := r1.nextRange 2 16
      let (lim, r3) := r2.nextRange 1 uLen
      let s := mkXzBadUncompLenStream uLen (ByteArray.mk #[0x00, 0x21, 0x18, 0x00, 0x00])
      (.decompressWith .xz { maxOutputBytes := lim } s "xzPartialCopy", r3)

/-- Generate an invalid-options operation exercising option/size validation paths. -/
def genInvalidOptionOp (codec : Codec) (r : Rng) : CompressFuzzOp × Rng :=
  let (kind, r1) := r.nextNat 9
  if kind == 0 then
    (.compressWith codec { timeoutMs := 0 } ByteArray.empty, r1)
  else if kind == 1 then
    (.decompressWith codec { timeoutMs := 0 } (Model.encodeStored codec ByteArray.empty), r1)
  else if kind == 2 then
    (.compressWith codec { maxOutputBytes := 0 } ByteArray.empty, r1)
  else if kind == 3 then
    let (p, r2) := r1.nextBytesRange 4 16
    (.compressWith codec { maxInputBytes := some (p.size - 1) } p, r2)
  else if kind == 4 then
    let (p, r2) := r1.nextBytesRange 4 16
    (.decompressWith codec { maxInputBytes := some (p.size - 1) } p, r2)
  else if kind == 5 then
    let (lowEdge, r2) := r1.nextBool
    let badLvl :=
      match codec with
      | .gzip => if lowEdge then some 0 else some 10
      | .xz => some 10
      | .zstd => if lowEdge then some 0 else some 20
    (.compressWith codec { level := badLvl } (ByteArray.mk #[0x41]), r2)
  else if kind == 6 then
    let (badThr, r2) :=
      match codec with
      | .gzip => r1.choose #[some 0, some 1, some 2] (some 0)
      | .xz => (some 16385, r1)
      | .zstd => (some 4294967296, r1)
    (.compressWith codec { threads := badThr } (ByteArray.mk #[0x41]), r2)
  else if kind == 7 then
    (.decompressWith codec { maxOutputBytes := 0 } (Model.encodeStored codec ByteArray.empty), r1)
  else
    (.decompressWith codec { maxInputBytes := some 0 } (Model.encodeStored codec ByteArray.empty), r1)

private def collectZeroRuns (bs : ByteArray) : Array (Nat × Nat) := Id.run do
  let mut runs : Array (Nat × Nat) := #[]
  let mut i : Nat := 0
  while i < bs.size do
    if bs.get! i == 0 then
      let zStart := i
      while i < bs.size && bs.get! i == 0 do
        i := i + 1
      runs := runs.push (zStart, i)
    else
      i := i + 1
  return runs

private def shrinkBytes (bs : ByteArray) : List ByteArray := Id.run do
  if bs.isEmpty then
    return []
  let mut cands : Array ByteArray := #[ByteArray.empty]
  let mut nzIndices : Array Nat := Array.mkEmpty bs.size
  for i in [0:bs.size] do
    if bs.get! i != 0 then
      nzIndices := nzIndices.push i
  let mut prefs : Array ByteArray := #[]
  let mut suffs : Array ByteArray := #[]
  let mut mids : Array ByteArray := #[]
  let mut extraCuts : Array ByteArray := #[]
  if bs.size > 1 then
    let mut step := bs.size / 2
    while step >= 1 do
      let keep := bs.size - step
      prefs := prefs.push (bs.extract 0 keep)
      suffs := suffs.push (bs.extract step bs.size)
      if keep > 1 then
        let mid := keep / 2
        mids := mids.push (bs.extract 0 mid ++ bs.extract (mid + step) bs.size)
      if step == 1 then
        break
      step := step / 2
    for parts in #[4, 8] do
      if bs.size >= parts then
        for j in [0:parts] do
          let a := (bs.size * j) / parts
          let b := (bs.size * (j + 1)) / parts
          if a < b && a > 0 && b < bs.size then
            extraCuts := extraCuts.push (bs.extract 0 a ++ bs.extract b bs.size)
    if bs.size >= 16 && nzIndices.size > 8 then
      for j in [0:16] do
        let a := (bs.size * j) / 16
        let b := (bs.size * (j + 1)) / 16
        if a < b && a > 0 && b < bs.size then
          extraCuts := extraCuts.push (bs.extract 0 a ++ bs.extract b bs.size)
    if bs.size <= 64 || (bs.size <= 128 && nzIndices.size > 8) then
      for i in [0:bs.size] do
        if i > 0 && i + 1 < bs.size then
          extraCuts := extraCuts.push (bs.extract 0 i ++ bs.extract (i + 1) bs.size)
    if nzIndices.size >= 2 then
      let zRuns := collectZeroRuns bs
      if zRuns.size <= 64 then
        for (zStart, zEnd) in zRuns do
          let zLen := zEnd - zStart
          extraCuts := extraCuts.push (bs.extract 0 zStart ++ bs.extract zEnd bs.size)
          if zLen >= 2 then
            extraCuts := extraCuts.push (bs.extract 0 (zStart + 1) ++ bs.extract zEnd bs.size)
            extraCuts := extraCuts.push (bs.extract 0 zStart ++ bs.extract (zEnd - 1) bs.size)
          if zLen >= 3 then
            extraCuts := extraCuts.push (bs.extract 0 (zStart + 1) ++ bs.extract (zEnd - 1) bs.size)
          if zLen >= 4 then
            extraCuts := extraCuts.push (bs.extract 0 (zStart + zLen / 2) ++ bs.extract zEnd bs.size)
  if bs.size > 4096 then
    cands := cands ++ prefs ++ suffs ++ mids
  let zeroNzSlice := fun (a b : Nat) => Id.run do
    let mut out := bs
    for idx in [a:b] do
      if h : idx < nzIndices.size then
        out := out.set! (nzIndices[idx]'h) 0
    return out
  if nzIndices.size >= 2 then
    let n := nzIndices.size
    let half := n / 2
    cands := cands.push (zeroNzSlice 0 n)
    cands := cands.push (zeroNzSlice 0 half)
    cands := cands.push (zeroNzSlice half n)
    if 1 < half then
      cands := cands.push (zeroNzSlice 1 half)
    if half < n - 1 then
      cands := cands.push (zeroNzSlice half (n - 1))
    if n > 32 then
      let maxParts := if n > 4096 then 32 else 128
      let mut parts := 4
      while true do
        for j in [0:parts] do
          let a := (n * j) / parts
          let b := (n * (j + 1)) / parts
          if a < b then
            cands := cands.push (zeroNzSlice a b)
        if parts >= n || parts >= maxParts then
          break
        parts := parts * 2
  if bs.size > 1 then
    if bs.size <= 4096 then
      cands := cands ++ prefs ++ suffs ++ mids ++ extraCuts
    else
      cands := cands ++ extraCuts
  if nzIndices.size <= 32 then
    for i in nzIndices do
      cands := cands.push (bs.set! i 0)
  return cands.toList

private def shrinkDecodeCap : Nat := 1048576

private def shrinkPlainCandidates (plain : ByteArray) : Array ByteArray := Id.run do
  if plain.isEmpty then
    return #[]
  let mut out : Array ByteArray := #[ByteArray.empty]
  if plain.size > 1 then
    out := out.push (plain.extract 0 1)
    out := out.push (plain.extract (plain.size - 1) plain.size)
  if plain.size > 2 then
    out := out.push (plain.extract 0 2)
    out := out.push (plain.extract (plain.size - 2) plain.size)
  if plain.size <= 1024 then
    for p' in shrinkBytes plain do
      if !p'.isEmpty then
        out := out.push p'
  else
    let minStep := max 1 (plain.size / 16)
    let mut step := plain.size / 2
    while step >= minStep do
      let keep := plain.size - step
      out := out.push (plain.extract 0 keep)
      out := out.push (plain.extract step plain.size)
      if keep > 1 then
        let mid := keep / 2
        out := out.push (plain.extract 0 mid ++ plain.extract (mid + step) plain.size)
      if step <= minStep then
        break
      step := step / 2
  return out

/-- Lightweight decoder for stored/RLE single-frame fuzz streams used solely by shrinker helpers and self-tests. -/
def decodeStoredForShrink (c : Codec) (inp : ByteArray) : Option ByteArray :=
  match c with
  | .gzip => Id.run do
    if inp.size < 23 then return none
    if inp.extract 0 10 != ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03] then return none
    let mut pos := 10
    let mut out := ByteArray.empty
    let stop := inp.size - 8
    while pos < stop do
      if pos + 5 > stop then return none
      let hdr := inp.get! pos
      if hdr != 0x00 && hdr != 0x01 then return none
      let len := (inp.get! (pos + 1)).toNat ||| ((inp.get! (pos + 2)).toNat <<< 8)
      let nlen := (inp.get! (pos + 3)).toNat ||| ((inp.get! (pos + 4)).toNat <<< 8)
      if (len ^^^ nlen) != 0xFFFF || pos + 5 + len > stop then return none
      out := out ++ inp.extract (pos + 5) (pos + 5 + len)
      pos := pos + 5 + len
      if hdr == 0x01 then
        if pos == stop then return some out else return none
    return none
  | .zstd => Id.run do
    if inp.size < 8 then return none
    if inp.extract 0 4 != ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD] then return none
    let fhd := inp.get! 4
    if (fhd &&& 0x08) != 0 then return none
    let hasChk := (fhd &&& 0x04) != 0
    let singleSeg := (fhd &&& 0x20) != 0
    let didSz := match fhd &&& 0x03 with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4
    let fcsCode := (fhd >>> 6).toNat
    let fcsSz := if fcsCode == 0 then (if singleSeg then 1 else 0) else if fcsCode == 1 then 2 else if fcsCode == 2 then 4 else 8
    let hdrLen := 5 + (if singleSeg then 0 else 1) + didSz + fcsSz
    let trailSz := if hasChk then 4 else 0
    if inp.size < hdrLen + 3 + trailSz then return none
    let mut pos := hdrLen
    let mut out := ByteArray.empty
    let stop := inp.size - trailSz
    while pos < stop do
      if pos + 3 > stop then return none
      let bh := (inp.get! pos).toNat ||| ((inp.get! (pos + 1)).toNat <<< 8) ||| ((inp.get! (pos + 2)).toNat <<< 16)
      let last := bh &&& 1
      let bt := (bh >>> 1) &&& 3
      let bsz := bh >>> 3
      if bt == 0 then
        if pos + 3 + bsz > stop then return none
        out := out ++ inp.extract (pos + 3) (pos + 3 + bsz)
        pos := pos + 3 + bsz
      else if bt == 1 then
        if pos + 4 > stop || out.size + bsz > 2097152 then return none
        let b := inp.get! (pos + 3)
        for _ in [0:bsz] do
          out := out.push b
        pos := pos + 4
      else
        return none
      if last == 1 then
        if pos == stop then return some out else return none
    return none
  | .xz => Id.run do
    if inp.size < 32 then return none
    if inp.extract 0 8 != ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04] then return none
    if inp.get! 12 == 0x00 then return some ByteArray.empty
    if inp.size < 40 then return none
    let mut pos := 24
    let mut out := ByteArray.empty
    while pos < inp.size do
      let ctrl := inp.get! pos
      if ctrl == 0x00 then
        return some out
      if ctrl != 0x01 && ctrl != 0x02 then return none
      if pos + 3 > inp.size then return none
      let ulen := (((inp.get! (pos + 1)).toNat <<< 8) ||| (inp.get! (pos + 2)).toNat) + 1
      if pos + 3 + ulen > inp.size then return none
      out := out ++ inp.extract (pos + 3) (pos + 3 + ulen)
      pos := pos + 3 + ulen
    return none

private def shrinkDecodedStream (c : Codec) (inp : ByteArray) : List ByteArray := Id.run do
  if inp.isEmpty || inp.size > shrinkDecodeCap then
    return []
  match decodeStoredForShrink c inp with
  | some plain =>
    let mut cands : Array ByteArray := #[]
    for p' in shrinkPlainCandidates plain do
      cands := cands.push (Model.encodeStored c p')
    let storedFull := Model.encodeStored c plain
    if inp != storedFull && storedFull.size < inp.size then
      cands := cands.push storedFull
    return cands.toList
  | none => return []

private def shrinkNatDown (n : Nat) : List Nat := Id.run do
  if n == 0 then
    return []
  let mut out : List Nat := [0]
  if n > 1 then
    out := out ++ [1]
    let mut step := n / 2
    while step >= 1 do
      let cand := n - step
      if cand > 1 then
        out := out ++ [cand]
      if step == 1 then
        break
      step := step / 2
  return out

private def shrinkCompressOpts (opts : CompressOptions) : List CompressOptions := Id.run do
  let c0 : CompressOptions := {}
  let mut out : List CompressOptions := []
  if opts != c0 then
    out := out ++ [c0]
  if let some lvl := opts.level then
    out := out ++ [{ opts with level := none }]
    for v in shrinkNatDown lvl do
      out := out ++ [{ opts with level := some v }]
  if let some thr := opts.threads then
    out := out ++ [{ opts with threads := none }]
    for v in shrinkNatDown thr do
      out := out ++ [{ opts with threads := some v }]
  if let some mi := opts.maxInputBytes then
    out := out ++ [{ opts with maxInputBytes := none }]
    for v in shrinkNatDown mi do
      out := out ++ [{ opts with maxInputBytes := some v }]
  if opts.maxOutputBytes != c0.maxOutputBytes then
    if opts.maxOutputBytes < c0.maxOutputBytes then
      out := out ++ [{ opts with maxOutputBytes := c0.maxOutputBytes }]
    for v in shrinkNatDown opts.maxOutputBytes do
      out := out ++ [{ opts with maxOutputBytes := v }]
  if opts.timeoutMs != c0.timeoutMs then
    out := out ++ [{ opts with timeoutMs := c0.timeoutMs }]
    for v in shrinkNatDown opts.timeoutMs do
      if v != c0.timeoutMs then
        out := out ++ [{ opts with timeoutMs := v }]
  return out

private def shrinkDecompressOpts (opts : DecompressOptions) : List DecompressOptions := Id.run do
  let c0 : DecompressOptions := {}
  let mut out : List DecompressOptions := []
  if opts != c0 then
    out := out ++ [c0]
  if let some mi := opts.maxInputBytes then
    out := out ++ [{ opts with maxInputBytes := none }]
    for v in shrinkNatDown mi do
      out := out ++ [{ opts with maxInputBytes := some v }]
  if opts.maxOutputBytes != c0.maxOutputBytes then
    if opts.maxOutputBytes < c0.maxOutputBytes then
      out := out ++ [{ opts with maxOutputBytes := c0.maxOutputBytes }]
    for v in shrinkNatDown opts.maxOutputBytes do
      out := out ++ [{ opts with maxOutputBytes := v }]
  if opts.timeoutMs != c0.timeoutMs then
    out := out ++ [{ opts with timeoutMs := c0.timeoutMs }]
    for v in shrinkNatDown opts.timeoutMs do
      if v != c0.timeoutMs then
        out := out ++ [{ opts with timeoutMs := v }]
  return out

/-- Shrink a single `CompressFuzzOp` payload and options toward minimal failing reproducers. -/
def shrinkOp : CompressFuzzOp → List CompressFuzzOp
  | .isToolAvailable _ => []
  | .compress c p =>
    (shrinkBytes p).map (.compress c ·)
  | .compressWith c opts p =>
    let byteCands := shrinkBytes p
    let byOpts := (shrinkCompressOpts opts).map (.compressWith c · p)
    let byBytes := byteCands.map (.compressWith c opts ·)
    let byCoupled :=
      match opts.maxInputBytes with
      | some mi =>
        if mi <= p.size && p.size <= mi + 2 then
          let delta := p.size - mi
          byteCands.filterMap fun p' =>
            if p'.size >= delta then
              some (.compressWith c { opts with maxInputBytes := some (p'.size - delta) } p')
            else none
        else []
      | none => []
    byOpts ++ byBytes ++ byCoupled
  | .decompress c inp tag =>
    (shrinkDecodedStream c inp ++ shrinkBytes inp).map (.decompress c · tag)
  | .decompressWith c opts inp tag =>
    let byteCands := shrinkDecodedStream c inp ++ shrinkBytes inp
    let byOpts := (shrinkDecompressOpts opts).map (.decompressWith c · inp tag)
    let byBytes := byteCands.map (.decompressWith c opts · tag)
    let byCoupledIn :=
      match opts.maxInputBytes with
      | some mi =>
        if mi <= inp.size && inp.size <= mi + 2 then
          let delta := inp.size - mi
          byteCands.filterMap fun inp' =>
            if inp'.size >= delta then
              some (.decompressWith c { opts with maxInputBytes := some (inp'.size - delta) } inp' tag)
            else none
        else []
      | none => []
    let byCoupledOut :=
      if opts.maxOutputBytes >= 1 && inp.size <= shrinkDecodeCap then
        match decodeStoredForShrink c inp with
        | some plain =>
          let plainCands := (shrinkPlainCandidates plain).toList
          if opts.maxOutputBytes <= plain.size && plain.size <= opts.maxOutputBytes + 2 then
            let outDelta := plain.size - opts.maxOutputBytes
            plainCands.filterMap fun p' =>
              if p'.size > outDelta && p'.size < plain.size then
                some (.decompressWith c { opts with maxOutputBytes := p'.size - outDelta }
                  (Model.encodeStored c p') tag)
              else none
          else if plain.size < opts.maxOutputBytes && opts.maxOutputBytes <= plain.size + 2 then
            let outPlus := opts.maxOutputBytes - plain.size
            plainCands.filterMap fun p' =>
              if p'.size < plain.size then
                some (.decompressWith c { opts with maxOutputBytes := p'.size + outPlus }
                  (Model.encodeStored c p') tag)
              else none
          else []
        | none => []
      else []
    byOpts ++ byBytes ++ byCoupledIn ++ byCoupledOut

end Fuzz.Compress
