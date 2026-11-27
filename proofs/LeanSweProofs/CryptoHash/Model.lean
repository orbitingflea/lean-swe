import LeanSwe.CryptoHash.Types

namespace LeanSwe.CryptoHash.Model

/-- Initial 8-word hash state `H^(0)` for FIPS 180-4 SHA-256. -/
def h256Init : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- FIPS 180-4 SHA-256 64-entry round constants `K_0..K_63`. -/
def k256 : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial 8-word hash state `H^(0)` for FIPS 180-4 SHA-512. -/
def h512Init : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- FIPS 180-4 SHA-512 80-entry round constants `K_0..K_79`. -/
def k512 : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- 32-bit right rotation for `1 ≤ n < 32`. -/
@[inline] def rotr32 (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- FIPS 180-4 32-bit choice function `Ch(x, y, z)`. -/
@[inline] def ch32 (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

/-- FIPS 180-4 32-bit majority function `Maj(x, y, z)`. -/
@[inline] def maj32 (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 SHA-256 `Σ_0(x)`. -/
@[inline] def bigSigma0_32 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

/-- FIPS 180-4 SHA-256 `Σ_1(x)`. -/
@[inline] def bigSigma1_32 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

/-- FIPS 180-4 SHA-256 `σ_0(x)`. -/
@[inline] def smallSigma0_32 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)

/-- FIPS 180-4 SHA-256 `σ_1(x)`. -/
@[inline] def smallSigma1_32 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

/-- Read byte `i` from `bs` in `O(1)` time without copying `ByteArray`, returning `0` if out of bounds. -/
@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

/-- Decode a big-endian 32-bit word from `bs` at byte offset `off`. -/
@[inline] def readU32BE (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (byteAt bs off).toUInt32
  let b1 := (byteAt bs (off + 1)).toUInt32
  let b2 := (byteAt bs (off + 2)).toUInt32
  let b3 := (byteAt bs (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Tail-recursive initial 16-word message schedule loader for SHA-256. -/
def loadW256Init (block : ByteArray) (off idx rem : Nat) (acc : Array UInt32) : Array UInt32 :=
  match rem with
  | 0 => acc
  | r + 1 =>
    loadW256Init block off (idx + 1) r (acc.push (readU32BE block (off + idx * 4)))

/-- Tail-recursive SHA-256 message schedule expansion (`W[16..63]`). -/
def expandW256 (idx rem : Nat) (w : Array UInt32) : Array UInt32 :=
  match rem with
  | 0 => w
  | r + 1 =>
    let w2 := w.getD (idx - 2) 0
    let w7 := w.getD (idx - 7) 0
    let w15 := w.getD (idx - 15) 0
    let w16 := w.getD (idx - 16) 0
    let wt := smallSigma1_32 w2 + w7 + smallSigma0_32 w15 + w16
    expandW256 (idx + 1) r (w.push wt)

/-- Tail-recursive 64-round SHA-256 compression loop over expanded schedule `w`. -/
def sha256Rounds (w : Array UInt32) (idx rem : Nat)
    (a b c d e f g h : UInt32) : Array UInt32 :=
  match rem with
  | 0 => #[a, b, c, d, e, f, g, h]
  | r + 1 =>
    let t1 := h + bigSigma1_32 e + ch32 e f g + k256.getD idx 0 + w.getD idx 0
    let t2 := bigSigma0_32 a + maj32 a b c
    sha256Rounds w (idx + 1) r (t1 + t2) a b c (d + t1) e f g

/-- Compress one 64-byte block at `block[off .. off+64]` into the 8-word SHA-256 state. -/
def sha256CompressBlock (state : Array UInt32) (block : ByteArray) (off : Nat) : Array UInt32 :=
  let w0 := loadW256Init block off 0 16 (Array.mkEmpty 64)
  let w := expandW256 16 48 w0
  let s0 := state.getD 0 0
  let s1 := state.getD 1 0
  let s2 := state.getD 2 0
  let s3 := state.getD 3 0
  let s4 := state.getD 4 0
  let s5 := state.getD 5 0
  let s6 := state.getD 6 0
  let s7 := state.getD 7 0
  let d := sha256Rounds w 0 64 s0 s1 s2 s3 s4 s5 s6 s7
  #[s0 + d.getD 0 0, s1 + d.getD 1 0, s2 + d.getD 2 0, s3 + d.getD 3 0,
    s4 + d.getD 4 0, s5 + d.getD 5 0, s6 + d.getD 6 0, s7 + d.getD 7 0]

/-- Tail-recursive compression of `count` consecutive 64-byte SHA-256 blocks from `chunk` starting at `off`. -/
def compressBlocks256 (h : Array UInt32) (chunk : ByteArray) (off count : Nat) : Array UInt32 :=
  match count with
  | 0 => h
  | k + 1 => compressBlocks256 (sha256CompressBlock h chunk off) chunk (off + 64) k

/-- Serialize an 8-word SHA-256 state as an exact 32-byte big-endian `ByteArray`. -/
def wordsToBytes32 (h : Array UInt32) : ByteArray :=
  let w0 := h.getD 0 0
  let w1 := h.getD 1 0
  let w2 := h.getD 2 0
  let w3 := h.getD 3 0
  let w4 := h.getD 4 0
  let w5 := h.getD 5 0
  let w6 := h.getD 6 0
  let w7 := h.getD 7 0
  ByteArray.mk #[
    UInt8.ofNat ((w0 >>> 24).toNat % 256), UInt8.ofNat ((w0 >>> 16).toNat % 256),
    UInt8.ofNat ((w0 >>> 8).toNat % 256), UInt8.ofNat (w0.toNat % 256),
    UInt8.ofNat ((w1 >>> 24).toNat % 256), UInt8.ofNat ((w1 >>> 16).toNat % 256),
    UInt8.ofNat ((w1 >>> 8).toNat % 256), UInt8.ofNat (w1.toNat % 256),
    UInt8.ofNat ((w2 >>> 24).toNat % 256), UInt8.ofNat ((w2 >>> 16).toNat % 256),
    UInt8.ofNat ((w2 >>> 8).toNat % 256), UInt8.ofNat (w2.toNat % 256),
    UInt8.ofNat ((w3 >>> 24).toNat % 256), UInt8.ofNat ((w3 >>> 16).toNat % 256),
    UInt8.ofNat ((w3 >>> 8).toNat % 256), UInt8.ofNat (w3.toNat % 256),
    UInt8.ofNat ((w4 >>> 24).toNat % 256), UInt8.ofNat ((w4 >>> 16).toNat % 256),
    UInt8.ofNat ((w4 >>> 8).toNat % 256), UInt8.ofNat (w4.toNat % 256),
    UInt8.ofNat ((w5 >>> 24).toNat % 256), UInt8.ofNat ((w5 >>> 16).toNat % 256),
    UInt8.ofNat ((w5 >>> 8).toNat % 256), UInt8.ofNat (w5.toNat % 256),
    UInt8.ofNat ((w6 >>> 24).toNat % 256), UInt8.ofNat ((w6 >>> 16).toNat % 256),
    UInt8.ofNat ((w6 >>> 8).toNat % 256), UInt8.ofNat (w6.toNat % 256),
    UInt8.ofNat ((w7 >>> 24).toNat % 256), UInt8.ofNat ((w7 >>> 16).toNat % 256),
    UInt8.ofNat ((w7 >>> 8).toNat % 256), UInt8.ofNat (w7.toNat % 256)]

/-- Encode a `UInt64` as 8 big-endian bytes. -/
def u64ToBytesBE (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((x >>> 56).toNat % 256), UInt8.ofNat ((x >>> 48).toNat % 256),
    UInt8.ofNat ((x >>> 40).toNat % 256), UInt8.ofNat ((x >>> 32).toNat % 256),
    UInt8.ofNat ((x >>> 24).toNat % 256), UInt8.ofNat ((x >>> 16).toNat % 256),
    UInt8.ofNat ((x >>> 8).toNat % 256), UInt8.ofNat (x.toNat % 256)]

/-- Incremental FIPS 180-4 SHA-256 streaming state. -/
structure Sha256State where
  /-- Current 8-word chaining state. -/
  h : Array UInt32
  /-- Unprocessed partial block tail (`< 64` bytes). -/
  buf : ByteArray
  /-- Total input bytes absorbed so far. -/
  totalBytes : Nat
  deriving BEq, DecidableEq

/-- Initial empty SHA-256 streaming state. -/
def Sha256State.init : Sha256State :=
  { h := h256Init, buf := ByteArray.empty, totalBytes := 0 }

/-- Feed `chunk` into `st`, compressing every complete 64-byte block immediately. -/
def Sha256State.update (st : Sha256State) (chunk : ByteArray) : Sha256State :=
  if chunk.size == 0 then
    st
  else if st.buf.size == 0 then
    let fullBlocks := chunk.size / 64
    let h1 := compressBlocks256 st.h chunk 0 fullBlocks
    let tailOff := fullBlocks * 64
    { h := h1
      buf := chunk.extract tailOff chunk.size
      totalBytes := st.totalBytes + chunk.size }
  else if st.buf.size < 64 then
    if st.buf.size + chunk.size < 64 then
      { h := st.h
        buf := st.buf ++ chunk
        totalBytes := st.totalBytes + chunk.size }
    else
      let need := 64 - st.buf.size
      let firstBlock := st.buf ++ chunk.extract 0 need
      let h1 := sha256CompressBlock st.h firstBlock 0
      let leftover := chunk.size - need
      let fullBlocks := leftover / 64
      let h2 := compressBlocks256 h1 chunk need fullBlocks
      let tailOff := need + fullBlocks * 64
      { h := h2
        buf := chunk.extract tailOff chunk.size
        totalBytes := st.totalBytes + chunk.size }
  else
    let combined := st.buf ++ chunk
    let fullBlocks := combined.size / 64
    let h1 := compressBlocks256 st.h combined 0 fullBlocks
    let tailOff := fullBlocks * 64
    { h := h1
      buf := combined.extract tailOff combined.size
      totalBytes := st.totalBytes + chunk.size }

/-- Apply FIPS 180-4 SHA-256 padding and output the 32-byte digest. -/
def Sha256State.finalize (st : Sha256State) : ByteArray :=
  let tail := st.buf.push 0x80
  let remMod := tail.size % 64
  let zeroCount := if remMod ≤ 56 then 56 - remMod else 120 - remMod
  let lenBytes := u64ToBytesBE (UInt64.ofNat (st.totalBytes * 8))
  let padded := (tail ++ ByteArray.mk (Array.replicate zeroCount 0)) ++ lenBytes
  let hFinal := compressBlocks256 st.h padded 0 (padded.size / 64)
  wordsToBytes32 hFinal

/-- One-shot pure FIPS 180-4 SHA-256 digest of `msg`. -/
def sha256Bytes (msg : ByteArray) : ByteArray :=
  (Sha256State.init.update msg).finalize

/-- Streaming multi-chunk pure FIPS 180-4 SHA-256 digest over `chunks`. -/
def sha256Chunks (chunks : Array ByteArray) : ByteArray :=
  (chunks.foldl Sha256State.update Sha256State.init).finalize

/-- 64-bit right rotation for `1 ≤ n < 64`. -/
@[inline] def rotr64 (x n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- FIPS 180-4 64-bit choice function `Ch(x, y, z)`. -/
@[inline] def ch64 (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

/-- FIPS 180-4 64-bit majority function `Maj(x, y, z)`. -/
@[inline] def maj64 (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 SHA-512 `Σ_0(x)`. -/
@[inline] def bigSigma0_64 (x : UInt64) : UInt64 :=
  rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39

/-- FIPS 180-4 SHA-512 `Σ_1(x)`. -/
@[inline] def bigSigma1_64 (x : UInt64) : UInt64 :=
  rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41

/-- FIPS 180-4 SHA-512 `σ_0(x)`. -/
@[inline] def smallSigma0_64 (x : UInt64) : UInt64 :=
  rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)

/-- FIPS 180-4 SHA-512 `σ_1(x)`. -/
@[inline] def smallSigma1_64 (x : UInt64) : UInt64 :=
  rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

/-- Decode a big-endian 64-bit word from `bs` at byte offset `off`. -/
@[inline] def readU64BE (bs : ByteArray) (off : Nat) : UInt64 :=
  let b0 := (byteAt bs off).toUInt64
  let b1 := (byteAt bs (off + 1)).toUInt64
  let b2 := (byteAt bs (off + 2)).toUInt64
  let b3 := (byteAt bs (off + 3)).toUInt64
  let b4 := (byteAt bs (off + 4)).toUInt64
  let b5 := (byteAt bs (off + 5)).toUInt64
  let b6 := (byteAt bs (off + 6)).toUInt64
  let b7 := (byteAt bs (off + 7)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
    (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-- Tail-recursive initial 16-word message schedule loader for SHA-512. -/
def loadW512Init (block : ByteArray) (off idx rem : Nat) (acc : Array UInt64) : Array UInt64 :=
  match rem with
  | 0 => acc
  | r + 1 =>
    loadW512Init block off (idx + 1) r (acc.push (readU64BE block (off + idx * 8)))

/-- Tail-recursive SHA-512 message schedule expansion (`W[16..79]`). -/
def expandW512 (idx rem : Nat) (w : Array UInt64) : Array UInt64 :=
  match rem with
  | 0 => w
  | r + 1 =>
    let w2 := w.getD (idx - 2) 0
    let w7 := w.getD (idx - 7) 0
    let w15 := w.getD (idx - 15) 0
    let w16 := w.getD (idx - 16) 0
    let wt := smallSigma1_64 w2 + w7 + smallSigma0_64 w15 + w16
    expandW512 (idx + 1) r (w.push wt)

/-- Tail-recursive 80-round SHA-512 compression loop over expanded schedule `w`. -/
def sha512Rounds (w : Array UInt64) (idx rem : Nat)
    (a b c d e f g h : UInt64) : Array UInt64 :=
  match rem with
  | 0 => #[a, b, c, d, e, f, g, h]
  | r + 1 =>
    let t1 := h + bigSigma1_64 e + ch64 e f g + k512.getD idx 0 + w.getD idx 0
    let t2 := bigSigma0_64 a + maj64 a b c
    sha512Rounds w (idx + 1) r (t1 + t2) a b c (d + t1) e f g

/-- Compress one 128-byte block at `block[off .. off+128]` into the 8-word SHA-512 state. -/
def sha512CompressBlock (state : Array UInt64) (block : ByteArray) (off : Nat) : Array UInt64 :=
  let w0 := loadW512Init block off 0 16 (Array.mkEmpty 80)
  let w := expandW512 16 64 w0
  let s0 := state.getD 0 0
  let s1 := state.getD 1 0
  let s2 := state.getD 2 0
  let s3 := state.getD 3 0
  let s4 := state.getD 4 0
  let s5 := state.getD 5 0
  let s6 := state.getD 6 0
  let s7 := state.getD 7 0
  let d := sha512Rounds w 0 80 s0 s1 s2 s3 s4 s5 s6 s7
  #[s0 + d.getD 0 0, s1 + d.getD 1 0, s2 + d.getD 2 0, s3 + d.getD 3 0,
    s4 + d.getD 4 0, s5 + d.getD 5 0, s6 + d.getD 6 0, s7 + d.getD 7 0]

/-- Tail-recursive compression of `count` consecutive 128-byte SHA-512 blocks from `chunk` starting at `off`. -/
def compressBlocks512 (h : Array UInt64) (chunk : ByteArray) (off count : Nat) : Array UInt64 :=
  match count with
  | 0 => h
  | k + 1 => compressBlocks512 (sha512CompressBlock h chunk off) chunk (off + 128) k

/-- Serialize an 8-word SHA-512 state as an exact 64-byte big-endian `ByteArray`. -/
def wordsToBytes64 (h : Array UInt64) : ByteArray :=
  let w0 := h.getD 0 0
  let w1 := h.getD 1 0
  let w2 := h.getD 2 0
  let w3 := h.getD 3 0
  let w4 := h.getD 4 0
  let w5 := h.getD 5 0
  let w6 := h.getD 6 0
  let w7 := h.getD 7 0
  ByteArray.mk #[
    UInt8.ofNat ((w0 >>> 56).toNat % 256), UInt8.ofNat ((w0 >>> 48).toNat % 256),
    UInt8.ofNat ((w0 >>> 40).toNat % 256), UInt8.ofNat ((w0 >>> 32).toNat % 256),
    UInt8.ofNat ((w0 >>> 24).toNat % 256), UInt8.ofNat ((w0 >>> 16).toNat % 256),
    UInt8.ofNat ((w0 >>> 8).toNat % 256), UInt8.ofNat (w0.toNat % 256),
    UInt8.ofNat ((w1 >>> 56).toNat % 256), UInt8.ofNat ((w1 >>> 48).toNat % 256),
    UInt8.ofNat ((w1 >>> 40).toNat % 256), UInt8.ofNat ((w1 >>> 32).toNat % 256),
    UInt8.ofNat ((w1 >>> 24).toNat % 256), UInt8.ofNat ((w1 >>> 16).toNat % 256),
    UInt8.ofNat ((w1 >>> 8).toNat % 256), UInt8.ofNat (w1.toNat % 256),
    UInt8.ofNat ((w2 >>> 56).toNat % 256), UInt8.ofNat ((w2 >>> 48).toNat % 256),
    UInt8.ofNat ((w2 >>> 40).toNat % 256), UInt8.ofNat ((w2 >>> 32).toNat % 256),
    UInt8.ofNat ((w2 >>> 24).toNat % 256), UInt8.ofNat ((w2 >>> 16).toNat % 256),
    UInt8.ofNat ((w2 >>> 8).toNat % 256), UInt8.ofNat (w2.toNat % 256),
    UInt8.ofNat ((w3 >>> 56).toNat % 256), UInt8.ofNat ((w3 >>> 48).toNat % 256),
    UInt8.ofNat ((w3 >>> 40).toNat % 256), UInt8.ofNat ((w3 >>> 32).toNat % 256),
    UInt8.ofNat ((w3 >>> 24).toNat % 256), UInt8.ofNat ((w3 >>> 16).toNat % 256),
    UInt8.ofNat ((w3 >>> 8).toNat % 256), UInt8.ofNat (w3.toNat % 256),
    UInt8.ofNat ((w4 >>> 56).toNat % 256), UInt8.ofNat ((w4 >>> 48).toNat % 256),
    UInt8.ofNat ((w4 >>> 40).toNat % 256), UInt8.ofNat ((w4 >>> 32).toNat % 256),
    UInt8.ofNat ((w4 >>> 24).toNat % 256), UInt8.ofNat ((w4 >>> 16).toNat % 256),
    UInt8.ofNat ((w4 >>> 8).toNat % 256), UInt8.ofNat (w4.toNat % 256),
    UInt8.ofNat ((w5 >>> 56).toNat % 256), UInt8.ofNat ((w5 >>> 48).toNat % 256),
    UInt8.ofNat ((w5 >>> 40).toNat % 256), UInt8.ofNat ((w5 >>> 32).toNat % 256),
    UInt8.ofNat ((w5 >>> 24).toNat % 256), UInt8.ofNat ((w5 >>> 16).toNat % 256),
    UInt8.ofNat ((w5 >>> 8).toNat % 256), UInt8.ofNat (w5.toNat % 256),
    UInt8.ofNat ((w6 >>> 56).toNat % 256), UInt8.ofNat ((w6 >>> 48).toNat % 256),
    UInt8.ofNat ((w6 >>> 40).toNat % 256), UInt8.ofNat ((w6 >>> 32).toNat % 256),
    UInt8.ofNat ((w6 >>> 24).toNat % 256), UInt8.ofNat ((w6 >>> 16).toNat % 256),
    UInt8.ofNat ((w6 >>> 8).toNat % 256), UInt8.ofNat (w6.toNat % 256),
    UInt8.ofNat ((w7 >>> 56).toNat % 256), UInt8.ofNat ((w7 >>> 48).toNat % 256),
    UInt8.ofNat ((w7 >>> 40).toNat % 256), UInt8.ofNat ((w7 >>> 32).toNat % 256),
    UInt8.ofNat ((w7 >>> 24).toNat % 256), UInt8.ofNat ((w7 >>> 16).toNat % 256),
    UInt8.ofNat ((w7 >>> 8).toNat % 256), UInt8.ofNat (w7.toNat % 256)]

/-- Incremental FIPS 180-4 SHA-512 streaming state. -/
structure Sha512State where
  /-- Current 8-word chaining state. -/
  h : Array UInt64
  /-- Unprocessed partial block tail (`< 128` bytes). -/
  buf : ByteArray
  /-- Total input bytes absorbed so far. -/
  totalBytes : Nat
  deriving BEq, DecidableEq

/-- Initial empty SHA-512 streaming state. -/
def Sha512State.init : Sha512State :=
  { h := h512Init, buf := ByteArray.empty, totalBytes := 0 }

/-- Feed `chunk` into `st`, compressing every complete 128-byte block immediately. -/
def Sha512State.update (st : Sha512State) (chunk : ByteArray) : Sha512State :=
  if chunk.size == 0 then
    st
  else if st.buf.size == 0 then
    let fullBlocks := chunk.size / 128
    let h1 := compressBlocks512 st.h chunk 0 fullBlocks
    let tailOff := fullBlocks * 128
    { h := h1
      buf := chunk.extract tailOff chunk.size
      totalBytes := st.totalBytes + chunk.size }
  else if st.buf.size < 128 then
    if st.buf.size + chunk.size < 128 then
      { h := st.h
        buf := st.buf ++ chunk
        totalBytes := st.totalBytes + chunk.size }
    else
      let need := 128 - st.buf.size
      let firstBlock := st.buf ++ chunk.extract 0 need
      let h1 := sha512CompressBlock st.h firstBlock 0
      let leftover := chunk.size - need
      let fullBlocks := leftover / 128
      let h2 := compressBlocks512 h1 chunk need fullBlocks
      let tailOff := need + fullBlocks * 128
      { h := h2
        buf := chunk.extract tailOff chunk.size
        totalBytes := st.totalBytes + chunk.size }
  else
    let combined := st.buf ++ chunk
    let fullBlocks := combined.size / 128
    let h1 := compressBlocks512 st.h combined 0 fullBlocks
    let tailOff := fullBlocks * 128
    { h := h1
      buf := combined.extract tailOff combined.size
      totalBytes := st.totalBytes + chunk.size }

/-- Apply FIPS 180-4 SHA-512 padding with 128-bit bit length and output the 64-byte digest. -/
def Sha512State.finalize (st : Sha512State) : ByteArray :=
  let tail := st.buf.push 0x80
  let remMod := tail.size % 128
  let zeroCount := if remMod ≤ 112 then 112 - remMod else 240 - remMod
  let bitLen := st.totalBytes * 8
  let hiLen := UInt64.ofNat (bitLen >>> 64)
  let loLen := UInt64.ofNat bitLen
  let lenBytes := u64ToBytesBE hiLen ++ u64ToBytesBE loLen
  let padded := (tail ++ ByteArray.mk (Array.replicate zeroCount 0)) ++ lenBytes
  let hFinal := compressBlocks512 st.h padded 0 (padded.size / 128)
  wordsToBytes64 hFinal

/-- One-shot pure FIPS 180-4 SHA-512 digest of `msg`. -/
def sha512Bytes (msg : ByteArray) : ByteArray :=
  (Sha512State.init.update msg).finalize

/-- Streaming multi-chunk pure FIPS 180-4 SHA-512 digest over `chunks`. -/
def sha512Chunks (chunks : Array ByteArray) : ByteArray :=
  (chunks.foldl Sha512State.update Sha512State.init).finalize

/-- Normalize an arbitrary HMAC key to a 64-byte block per RFC 2104 (hashing if `> 64` bytes, right-zero-padding otherwise). -/
def hmacKeyBlock256 (key : ByteArray) : ByteArray :=
  let k := if key.size > 64 then sha256Bytes key else key
  if k.size < 64 then
    k ++ ByteArray.mk (Array.replicate (64 - k.size) 0)
  else
    k.extract 0 64

/-- Incremental RFC 2104 HMAC-SHA256 streaming state. -/
structure HmacSha256State where
  /-- Outer padded key block (`K' XOR 0x5c`). -/
  opadKey : ByteArray
  /-- Inner SHA-256 streaming state seeded with `K' XOR 0x36`. -/
  inner : Sha256State
  deriving BEq, DecidableEq

/-- Tail-recursive structural bytewise XOR helper for HMAC key padding. -/
def xorBytesLoop (bs : ByteArray) (pad : UInt8) (idx rem : Nat) (acc : ByteArray) : ByteArray :=
  match rem with
  | 0 => acc
  | r + 1 => xorBytesLoop bs pad (idx + 1) r (acc.push ((byteAt bs idx) ^^^ pad))

/-- XOR every byte in `bs` with `pad` using structural `Nat` recursion. -/
def xorBytes (bs : ByteArray) (pad : UInt8) : ByteArray :=
  xorBytesLoop bs pad 0 bs.size (ByteArray.emptyWithCapacity bs.size)

/-- Initialize an RFC 2104 HMAC-SHA256 streaming state from `key`. -/
def HmacSha256State.init (key : ByteArray) : HmacSha256State :=
  let kBlock := hmacKeyBlock256 key
  let ipadKey := xorBytes kBlock 0x36
  let opadKey := xorBytes kBlock 0x5c
  { opadKey := opadKey
    inner := Sha256State.init.update ipadKey }

/-- Feed `chunk` into the inner SHA-256 stream of `st`. -/
def HmacSha256State.update (st : HmacSha256State) (chunk : ByteArray) : HmacSha256State :=
  { st with inner := st.inner.update chunk }

/-- Finalize RFC 2104 HMAC-SHA256 as `SHA256(opadKey || SHA256(ipadKey || msg))`. -/
def HmacSha256State.finalize (st : HmacSha256State) : ByteArray :=
  ((Sha256State.init.update st.opadKey).update st.inner.finalize).finalize

/-- One-shot pure RFC 2104 HMAC-SHA256 tag over `key` and `msg`. -/
def hmacSha256Bytes (key msg : ByteArray) : ByteArray :=
  ((HmacSha256State.init key).update msg).finalize

/-- Streaming multi-chunk pure RFC 2104 HMAC-SHA256 tag over `key` and `chunks`. -/
def hmacSha256Chunks (key : ByteArray) (chunks : Array ByteArray) : ByteArray :=
  (chunks.foldl HmacSha256State.update (HmacSha256State.init key)).finalize

/-- Pure digest model dispatching on `HashAlg`. -/
def digestBytesModel : HashAlg → ByteArray → ByteArray
  | .sha256, m => sha256Bytes m
  | .sha512, m => sha512Bytes m

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsgModel (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Pure total error-mapping model from `CryptoHashRawError` to `CryptoHashError`. -/
def mapRawErrorModel : CryptoHashRawError → CryptoHashError
  | .invalidArgument detail =>
    { kind := .invalidInput
      opensslCode := none
      message := nonEmptyMsgModel "invalid cryptohash argument" detail }
  | .invalidHexInput detail =>
    { kind := .invalidHex
      opensslCode := none
      message := nonEmptyMsgModel "invalid hex input" detail }
  | .lengthError expected got detail =>
    { kind := .lengthMismatch
      opensslCode := none
      message := nonEmptyMsgModel s!"length mismatch: expected {expected} bytes, got {got}" detail }
  | .opensslError code detail =>
    { kind := .cryptoError
      opensslCode := code
      message := nonEmptyMsgModel "openssl crypto error" detail }
  | .userError detail =>
    { kind := .cryptoError
      opensslCode := none
      message := nonEmptyMsgModel "cryptohash error" detail }

/-- Pure model of equal-length raw constant-time comparison. -/
def ctEqualRawModel (a b : ByteArray) : Except CryptoHashError Bool :=
  if a.size != b.size then
    .error (mapRawErrorModel (.lengthError a.size b.size s!"length mismatch: expected {a.size} bytes, got {b.size}"))
  else
    .ok (a == b)

/-- Pure `RawCryptoHashOpsM Id` behavior model. -/
def modelRawOps : RawCryptoHashOpsM Id :=
  { mapRawError := mapRawErrorModel
    digestRaw := fun alg data => .ok (digestBytesModel alg data)
    hmacSha256Raw := fun key msg => .ok (hmacSha256Bytes key msg)
    ctEqualRaw := ctEqualRawModel }

/-- Pure model of `LeanSwe.CryptoHash.hash`. -/
def hashModel (alg : HashAlg) (msg : ByteArray) : Except CryptoHashError Digest :=
  .ok { alg, bytes := digestBytesModel alg msg }

/-- Pure model of `LeanSwe.CryptoHash.sha256`. -/
def sha256Model (msg : ByteArray) : Except CryptoHashError Digest :=
  hashModel .sha256 msg

/-- Pure model of `LeanSwe.CryptoHash.sha512`. -/
def sha512Model (msg : ByteArray) : Except CryptoHashError Digest :=
  hashModel .sha512 msg

/-- Pure model of `LeanSwe.CryptoHash.hmacSha256`. -/
def hmacSha256Model (key msg : ByteArray) : Except CryptoHashError Digest :=
  .ok { alg := .sha256, bytes := hmacSha256Bytes key msg }

/-- Pure model of `LeanSwe.CryptoHash.verifyHmacSha256`. -/
def verifyHmacSha256Model (key msg : ByteArray) (expected : Digest) : Except CryptoHashError Bool :=
  if expected.alg != .sha256 then
    .error { kind := .invalidInput, message := "expected HMAC-SHA256 digest algorithm" }
  else if expected.bytes.size != 32 then
    .error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {expected.bytes.size}" }
  else
    .ok (hmacSha256Bytes key msg == expected.bytes)

/-- Convert a nibble `0..15` to its lowercase ASCII hexadecimal character. -/
def lowerHexDigitModel (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Parse an ASCII hexadecimal character (`0-9`, `a-f`, `A-F`) into a nibble `0..15`. -/
def hexCharToNibbleModel (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else none

/-- Encode a single byte into big-endian high and low lowercase hexadecimal characters. -/
def byteToHexCharsModel (b : UInt8) : List Char :=
  [lowerHexDigitModel (b.toNat / 16), lowerHexDigitModel (b.toNat % 16)]

/-- Decode two ASCII hexadecimal characters (high nibble, low nibble) into a byte. -/
def hexCharsToByteModel (hi lo : Char) : Option UInt8 :=
  match hexCharToNibbleModel hi, hexCharToNibbleModel lo with
  | some h, some l => some (UInt8.ofNat (h.toNat * 16 + l.toNat))
  | _, _ => none

/-- Pure model of `LeanSwe.CryptoHash.toHex`. -/
def toHexModel (d : Digest) : String :=
  String.ofList (d.bytes.data.toList.flatMap byteToHexCharsModel)

/-- Tail-recursive hex pair decoder model. -/
def decodeHexPairsAccModel (accRev : List UInt8) : List Char → Option (List UInt8)
  | [] => some accRev.reverse
  | hi :: lo :: rest =>
    match hexCharsToByteModel hi lo with
    | some b => decodeHexPairsAccModel (b :: accRev) rest
    | none => none
  | _ => none

/-- Pure model of `LeanSwe.CryptoHash.fromHex`. -/
def fromHexModel (alg : HashAlg) (s : String) : Except CryptoHashError Digest :=
  match decodeHexPairsAccModel [] s.toList with
  | none =>
    .error { kind := .invalidHex, message := "hex string must have even length and contain only ASCII hex digits" }
  | some bs =>
    let ba := ByteArray.mk bs.toArray
    if ba.size != digestLen alg then
      .error { kind := .lengthMismatch, message := s!"expected {digestLen alg} digest bytes, got {ba.size}" }
    else
      .ok { alg, bytes := ba }

/-- Pure model of `LeanSwe.CryptoHash.ctEq`. -/
def ctEqModel (a b : ByteArray) : Except CryptoHashError Bool :=
  .ok (a == b)

/-- Pure `CryptoHashApiM Id` behavior model. -/
def modelApi : CryptoHashApiM Id :=
  { mapRawError := mapRawErrorModel
    hash := hashModel
    sha256 := sha256Model
    sha512 := sha512Model
    hmacSha256 := hmacSha256Model
    verifyHmacSha256 := verifyHmacSha256Model
    toHex := toHexModel
    fromHex := fromHexModel
    ctEq := ctEqModel }

end LeanSwe.CryptoHash.Model
