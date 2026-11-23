import LeanSwe.Compress.Types

namespace LeanSwe.Compress

/-- Explicit environment removals clearing inherited codec configuration variables and pinning `LC_ALL=C` while keeping `PATH`. -/
def codecSanitizedEnv : Array (String × Option String) :=
  #[("XZ_OPT", none),
    ("XZ_DEFAULTS", none),
    ("ZSTD_CLEVEL", none),
    ("ZSTD_NBTHREADS", none),
    ("GZIP", none),
    ("LC_ALL", some "C")]

/-- Read a little-endian 32-bit unsigned integer at `pos`. -/
@[inline] def readU32LE (bs : ByteArray) (pos : Nat) : UInt32 :=
  UInt32.ofNat (
    (bs.get! pos).toNat |||
    ((bs.get! (pos + 1)).toNat <<< 8) |||
    ((bs.get! (pos + 2)).toNat <<< 16) |||
    ((bs.get! (pos + 3)).toNat <<< 24))

/-- Read a little-endian 64-bit unsigned integer at `pos`. -/
@[inline] def readU64LE (bs : ByteArray) (pos : Nat) : UInt64 :=
  (readU32LE bs pos).toUInt64 ||| ((readU32LE bs (pos + 4)).toUInt64 <<< 32)

/-- Append a 16-bit little-endian integer to `out`. -/
def pushU16LE (out : ByteArray) (v : UInt16) : ByteArray :=
  let n := v.toNat
  (out.push (UInt8.ofNat (n &&& 0xFF))).push (UInt8.ofNat ((n >>> 8) &&& 0xFF))

/-- Append a 32-bit little-endian integer to `out`. -/
def pushU32LE (out : ByteArray) (v : UInt32) : ByteArray :=
  let n := v.toNat
  (((out.push (UInt8.ofNat (n &&& 0xFF))).push
    (UInt8.ofNat ((n >>> 8) &&& 0xFF))).push
    (UInt8.ofNat ((n >>> 16) &&& 0xFF))).push
    (UInt8.ofNat ((n >>> 24) &&& 0xFF))

/-- Append a 64-bit little-endian integer to `out`. -/
def pushU64LE (out : ByteArray) (v : UInt64) : ByteArray :=
  pushU32LE (pushU32LE out v.toUInt32) (v >>> 32).toUInt32

/-- Append `src[start .. min stop src.size)` to `dst`. -/
def pushBytesRange (dst src : ByteArray) (start stop : Nat) : ByteArray :=
  let hi := min stop src.size
  let rec go (fuel idx : Nat) (acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if idx >= hi then acc
      else go fuel (idx + 1) (acc.push (src.get! idx))
  go (hi - start) start dst

/-- Append `count` copies of `b` to `dst`. -/
def pushReplicateByte (dst : ByteArray) (b : UInt8) (count : Nat) : ByteArray :=
  let rec go (fuel : Nat) (acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 => go fuel (acc.push b)
  go count dst

/-- Step one byte into an IEEE 802.3 CRC-32 state. -/
def crc32Byte (c : UInt32) (b : UInt8) : UInt32 :=
  let rec go (fuel : Nat) (v : UInt32) : UInt32 :=
    match fuel with
    | 0 => v
    | fuel + 1 => go fuel (if (v &&& 1) != 0 then (v >>> 1) ^^^ 0xEDB88320 else v >>> 1)
  go 8 (c ^^^ b.toUInt32)

/-- Compute IEEE 802.3 CRC-32 over `bs[start .. stop)`. -/
def crc32 (bs : ByteArray) (start : Nat := 0) (stop : Nat := bs.size) : UInt32 :=
  let hi := min stop bs.size
  let rec go (fuel idx : Nat) (c : UInt32) : UInt32 :=
    match fuel with
    | 0 => c ^^^ 0xFFFFFFFF
    | fuel + 1 =>
      if idx >= hi then c ^^^ 0xFFFFFFFF
      else go fuel (idx + 1) (crc32Byte c (bs.get! idx))
  go (hi - start) start 0xFFFFFFFF

/-- Step one byte into an ECMA-182 CRC-64 state. -/
def crc64Byte (c : UInt64) (b : UInt8) : UInt64 :=
  let rec go (fuel : Nat) (v : UInt64) : UInt64 :=
    match fuel with
    | 0 => v
    | fuel + 1 => go fuel (if (v &&& 1) != 0 then (v >>> 1) ^^^ 0xC96C5795D7870F42 else v >>> 1)
  go 8 (c ^^^ b.toUInt64)

/-- Compute ECMA-182 CRC-64 (`.xz` polynomial) over `bs[start .. stop)`. -/
def crc64Xz (bs : ByteArray) (start : Nat := 0) (stop : Nat := bs.size) : UInt64 :=
  let hi := min stop bs.size
  let rec go (fuel idx : Nat) (c : UInt64) : UInt64 :=
    match fuel with
    | 0 => c ^^^ 0xFFFFFFFFFFFFFFFF
    | fuel + 1 =>
      if idx >= hi then c ^^^ 0xFFFFFFFFFFFFFFFF
      else go fuel (idx + 1) (crc64Byte c (bs.get! idx))
  go (hi - start) start 0xFFFFFFFFFFFFFFFF

/-- Rotate a 64-bit unsigned integer left by `r` bits. -/
@[inline] def rotl64 (x r : UInt64) : UInt64 :=
  (x <<< r) ||| (x >>> (64 - r))

/-- xxHash64 prime constant 1. -/
def xxhPrime1 : UInt64 := 0x9E3779B185EBCA87
/-- xxHash64 prime constant 2. -/
def xxhPrime2 : UInt64 := 0xC2B2AE3D27D4EB4F
/-- xxHash64 prime constant 3. -/
def xxhPrime3 : UInt64 := 0x165667B19E3779F9
/-- xxHash64 prime constant 4. -/
def xxhPrime4 : UInt64 := 0x85EBCA77C2B2AE63
/-- xxHash64 prime constant 5. -/
def xxhPrime5 : UInt64 := 0x27D4EB2F165667C5

/-- xxHash64 stripe round update. -/
@[inline] def xxh64Round (acc lane : UInt64) : UInt64 :=
  rotl64 (acc + lane * xxhPrime2) 31 * xxhPrime1

/-- xxHash64 accumulator merge round. -/
@[inline] def xxh64MergeRound (acc val : UInt64) : UInt64 :=
  (acc ^^^ xxh64Round 0 val) * xxhPrime1 + xxhPrime4

/-- Compute the low 32 bits of xxHash64 (`seed = 0`) used for RFC 8878 Zstandard frame checksums. -/
def xxh64Low32 (bs : ByteArray) : UInt32 :=
  let n := bs.size
  let rec stripeLoop (fuel pos : Nat) (v1 v2 v3 v4 : UInt64) : Nat × UInt64 × UInt64 × UInt64 × UInt64 :=
    match fuel with
    | 0 => (pos, v1, v2, v3, v4)
    | fuel + 1 =>
      if pos + 32 > n then (pos, v1, v2, v3, v4)
      else
        let v1' := xxh64Round v1 (readU64LE bs pos)
        let v2' := xxh64Round v2 (readU64LE bs (pos + 8))
        let v3' := xxh64Round v3 (readU64LE bs (pos + 16))
        let v4' := xxh64Round v4 (readU64LE bs (pos + 24))
        stripeLoop fuel (pos + 32) v1' v2' v3' v4'
  let rec tail8Loop (fuel pos : Nat) (h64 : UInt64) : Nat × UInt64 :=
    match fuel with
    | 0 => (pos, h64)
    | fuel + 1 =>
      if pos + 8 > n then (pos, h64)
      else
        let k1 := xxh64Round 0 (readU64LE bs pos)
        let h' := rotl64 (h64 ^^^ k1) 27 * xxhPrime1 + xxhPrime4
        tail8Loop fuel (pos + 8) h'
  let rec tail1Loop (fuel pos : Nat) (h64 : UInt64) : UInt64 :=
    match fuel with
    | 0 => h64
    | fuel + 1 =>
      if pos >= n then h64
      else
        let h' := rotl64 (h64 ^^^ ((bs.get! pos).toUInt64 * xxhPrime5)) 11 * xxhPrime1
        tail1Loop fuel (pos + 1) h'
  let (pos0, h0) :=
    if n >= 32 then
      let (p, v1, v2, v3, v4) := stripeLoop (n / 32 + 1) 0 (xxhPrime1 + xxhPrime2) xxhPrime2 0 (0 - xxhPrime1)
      let h := rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18
      let h := xxh64MergeRound h v1
      let h := xxh64MergeRound h v2
      let h := xxh64MergeRound h v3
      let h := xxh64MergeRound h v4
      (p, h)
    else
      (0, xxhPrime5)
  let h1 := h0 + UInt64.ofNat n
  let (pos1, h2) := tail8Loop 4 pos0 h1
  let (pos2, h3) :=
    if pos1 + 4 <= n then
      (pos1 + 4, rotl64 (h2 ^^^ ((readU32LE bs pos1).toUInt64 * xxhPrime1)) 23 * xxhPrime2 + xxhPrime3)
    else
      (pos1, h2)
  let h4 := tail1Loop 4 pos2 h3
  let h5 := (h4 ^^^ (h4 >>> 33)) * xxhPrime2
  let h6 := (h5 ^^^ (h5 >>> 29)) * xxhPrime3
  (h6 ^^^ (h6 >>> 32)).toUInt32

namespace Model

/-- O(1) RFC 1952 `.gzip` header check (`1f 8b 08` and at least 20 bytes) rejecting legacy `.Z`/pack/lzh/PKZIP containers at byte 0. -/
def hasGzipHeader (input : ByteArray) : Bool :=
  input.size ≥ 20 && input.get! 0 == 0x1F && input.get! 1 == 0x8B && input.get! 2 == 0x08

/-- Encode `n` as a canonical `.xz` variable-length integer. -/
def encodeXzVli (n : Nat) : ByteArray :=
  let rec go (fuel v : Nat) (acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let b := v &&& 0x7F
      let v' := v >>> 7
      if v' == 0 then acc.push (UInt8.ofNat b)
      else go fuel v' (acc.push (UInt8.ofNat (b ||| 0x80)))
  go 9 n ByteArray.empty

/-- Encode `input` as a valid stored `.gzip` stream. -/
def encodeGzipStored (input : ByteArray) : ByteArray :=
  let hdr := ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]
  let rec chunkLoop (fuel pos : Nat) (acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let rem := input.size - pos
      let take := min rem 65535
      let isLast : UInt8 := if pos + take == input.size then 0x01 else 0x00
      let len16 := UInt16.ofNat take
      let nlen16 := len16 ^^^ 0xFFFF
      let acc1 := pushU16LE (pushU16LE (acc.push isLast) len16) nlen16
      let acc2 := pushBytesRange acc1 input pos (pos + take)
      if pos + take == input.size then acc2
      else chunkLoop fuel (pos + take) acc2
  let body :=
    if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]
    else chunkLoop (input.size / 65535 + 2) 0 hdr
  let crc := crc32 input 0 input.size
  let isize := UInt32.ofNat (input.size % 4294967296)
  pushU32LE (pushU32LE body crc) isize

/-- Encode `input` as a valid raw-block `.zstd` stream. -/
def encodeZstdStored (input : ByteArray) : ByteArray :=
  let magic := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]
  let use8 := input.size >= 4294967296
  let fhd : UInt8 := if use8 then 0xC4 else 0x84
  let wd : UInt8 := 0x38
  let hdrBase := (magic.push fhd).push wd
  let hdr :=
    if use8 then pushU64LE hdrBase (UInt64.ofNat input.size)
    else pushU32LE hdrBase (UInt32.ofNat input.size)
  let rec chunkLoop (fuel pos : Nat) (acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let rem := input.size - pos
      let take := min rem 131072
      let last := if pos + take == input.size then 1 else 0
      let bhdr := (take <<< 3) ||| last
      let acc1 := ((acc.push (UInt8.ofNat (bhdr &&& 0xFF))).push
        (UInt8.ofNat ((bhdr >>> 8) &&& 0xFF))).push
        (UInt8.ofNat ((bhdr >>> 16) &&& 0xFF))
      let acc2 := pushBytesRange acc1 input pos (pos + take)
      if pos + take == input.size then acc2
      else chunkLoop fuel (pos + take) acc2
  let body :=
    if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
    else chunkLoop (input.size / 131072 + 2) 0 hdr
  pushU32LE body (xxh64Low32 input)

/-- Encode `input` as a valid stored-`LZMA2` `.xz` stream. -/
def encodeXzStored (input : ByteArray) : ByteArray :=
  let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]
  let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
  let (blocksBytes, idxRecords) : ByteArray × Array (Nat × Nat) :=
    if input.isEmpty then
      (ByteArray.empty, #[])
    else
      let bhdrBody := ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]
      let bhdr := pushU32LE bhdrBody (crc32 bhdrBody 0 8)
      let rec chunkLoop (fuel pos : Nat) (first : Bool) (acc : ByteArray) : ByteArray :=
        match fuel with
        | 0 => acc
        | fuel + 1 =>
          let rem := input.size - pos
          let take := min rem 65536
          let ctrl : UInt8 := if first then 0x01 else 0x02
          let u16 := take - 1
          let acc1 := ((acc.push ctrl).push (UInt8.ofNat ((u16 >>> 8) &&& 0xFF))).push (UInt8.ofNat (u16 &&& 0xFF))
          let acc2 := pushBytesRange acc1 input pos (pos + take)
          if pos + take == input.size then acc2.push 0x00
          else chunkLoop fuel (pos + take) false acc2
      let lzma2Data := chunkLoop (input.size / 65536 + 2) 0 true ByteArray.empty
      let pad := (4 - (lzma2Data.size % 4)) % 4
      let paddedData := pushReplicateByte lzma2Data 0x00 pad
      let chk := pushU64LE ByteArray.empty (crc64Xz input 0 input.size)
      let unpadded := bhdr.size + lzma2Data.size + 8
      (bhdr ++ paddedData ++ chk, #[(unpadded, input.size)])
  let rec buildIdx (fuel i : Nat) (buf : ByteArray) : ByteArray :=
    match fuel with
    | 0 => buf
    | fuel + 1 =>
      if i >= idxRecords.size then buf
      else
        let (u, uc) := idxRecords[i]!
        buildIdx fuel (i + 1) (buf ++ encodeXzVli u ++ encodeXzVli uc)
  let buf0 := (ByteArray.empty.push 0x00) ++ encodeXzVli idxRecords.size
  let buf1 := buildIdx idxRecords.size 0 buf0
  let pad := (4 - (buf1.size % 4)) % 4
  let buf2 := pushReplicateByte buf1 0x00 pad
  let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
  let bwdSize := UInt32.ofNat (idxRaw.size / 4 - 1)
  let ftrBody := pushU32LE ByteArray.empty bwdSize ++ ByteArray.mk #[0x00, 0x04]
  let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
  shdr ++ blocksBytes ++ idxRaw ++ ftr

/-- Encode `input` as a spec-valid uncompressed/stored stream for `codec`. -/
def encodeStored (codec : Codec) (input : ByteArray) : ByteArray :=
  match codec with
  | .gzip => encodeGzipStored input
  | .zstd => encodeZstdStored input
  | .xz => encodeXzStored input

/-- Reachable `PATH` / executable state for a `Codec` binary. -/
inductive ToolEnvStatus where
  /-- Codec binary exists and is executable. -/
  | available
  /-- Codec binary is missing (`ENOENT`) or non-executable (`EACCES`). -/
  | missingOrNonExec
  /-- `PATH` resolution hits a symlink loop (`ELOOP`). -/
  | pathSymlinkLoop
  /-- `PATH` resolution or pipe/spawn triggers an OS I/O error (`ENAMETOOLONG` etc.). -/
  | pathOrPipeIoError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- External OS environment state for `LeanSwe.Compress`. -/
structure CompressEnv where
  /-- Per-codec `PATH` resolution status. -/
  toolStatus : Codec → ToolEnvStatus := fun _ => .available
  /-- Whether transient subprocess timeouts are permitted by the environment. -/
  allowTimeout : Bool := false
  /-- Whether transient OS resource/pipe I/O errors are permitted. -/
  allowResourceIoError : Bool := false
  /-- Whether external signal termination is permitted. -/
  allowExternalSignal : Bool := false
  deriving Inhabited

/-- Healthy host environment with all three codec binaries installed and executable. -/
def CompressEnv.standard : CompressEnv := {}

/-- CLI executable name for `codec`. -/
def codecProgram : Codec → String
  | .zstd => "zstd"
  | .xz => "xz"
  | .gzip => "gzip"

/-- Valid compression level predicate per `Codec`. -/
def isValidLevel (codec : Codec) : Option Nat → Bool
  | none => true
  | some lvl =>
    match codec with
    | .zstd => 1 ≤ lvl && lvl ≤ 19
    | .xz => lvl ≤ 9
    | .gzip => 1 ≤ lvl && lvl ≤ 9

/-- Valid worker thread count predicate per `Codec`. -/
def isValidThreads (codec : Codec) : Option Nat → Bool
  | none => true
  | some t =>
    match codec with
    | .zstd => t ≤ 4294967295
    | .xz => t ≤ 16384
    | .gzip => false

/-- Valid input and options predicate for `compressWith`. -/
def isValidCompressInput (codec : Codec) (opts : CompressOptions) (input : ByteArray) : Bool :=
  opts.timeoutMs > 0 &&
  opts.maxOutputBytes > 0 &&
  isValidLevel codec opts.level &&
  isValidThreads codec opts.threads &&
  match opts.maxInputBytes with
  | none => true
  | some lim => input.size ≤ lim

/-- Valid input and options predicate for `decompressWith`. -/
def isValidDecompressInput (opts : DecompressOptions) (input : ByteArray) : Bool :=
  opts.timeoutMs > 0 &&
  opts.maxOutputBytes > 0 &&
  match opts.maxInputBytes with
  | none => true
  | some lim => input.size ≤ lim

/-- Minimum valid compressed stream byte length per `Codec`. -/
def minCompressedSize : Codec → Nat
  | .zstd => 9
  | .gzip => 20
  | .xz => 32

/-- Conservative upper bound on worst-case compressed stream size for `input.size = n`. -/
def maxCompressedBound (_codec : Codec) (n : Nat) : Nat :=
  n + (n / 1024 + 1) * 64 + 256

/-- Canonical container header/footer check for compressed outputs produced by `compressWith` / `encodeStored`. -/
def hasCanonicalCompressedFraming (codec : Codec) (bs : ByteArray) : Bool :=
  match codec with
  | .gzip =>
    bs.size ≥ 20 && bs.get! 0 == 0x1F && bs.get! 1 == 0x8B && bs.get! 2 == 0x08 &&
    bs.get! 3 == 0x00 && bs.get! 4 == 0x00 && bs.get! 5 == 0x00 && bs.get! 6 == 0x00 && bs.get! 7 == 0x00
  | .zstd =>
    bs.size ≥ 9 && bs.get! 0 == 0x28 && bs.get! 1 == 0xB5 && bs.get! 2 == 0x2F && bs.get! 3 == 0xFD
  | .xz =>
    bs.size ≥ 32 &&
    bs.extract 0 6 == ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] &&
    bs.extract (bs.size - 2) bs.size == ByteArray.mk #[0x59, 0x5A]

/-- Structural invariant for every `CompressError` returned by `LeanSwe.Compress`. -/
def isWellFormedCompressError (codec : Codec) (e : CompressError) : Bool :=
  let stderrOk := match e.stderr with | some s => !s.isEmpty | none => true
  let kindOk :=
    match e.kind with
    | .toolNotFound => e.exitCode.isNone && e.stderr.isNone
    | .invalidInput => e.exitCode.isNone && e.stderr.isNone
    | .outputLimitExceeded => e.exitCode.isNone
    | .timedOut => e.exitCode.isNone
    | .ioError => e.exitCode.isNone
    | .corruptData =>
      match e.exitCode with
      | some c => c != 0
      | none => true
    | .commandFailed =>
      match e.exitCode with
      | some c => c != 0
      | none => true
  e.codec == some codec && !e.message.isEmpty && stderrOk && kindOk

/-- Return `true` iff `e` is a well-formed transient process/environment error permitted by `env`. -/
def allowedTransientError (env : CompressEnv) (codec : Codec) (e : CompressError) : Bool :=
  isWellFormedCompressError codec e &&
  ((env.allowTimeout && e.kind == .timedOut) ||
   (env.allowResourceIoError && e.kind == .ioError) ||
   (env.allowExternalSignal && e.kind == .commandFailed))

/-- Stateful knowledge base recording `(codec, compressed) ↦ plaintext` round-trip pairs. -/
structure State where
  /-- Association list mapping observed `(codec, compressed)` streams to their exact uncompressed payload. -/
  known : List ((Codec × ByteArray) × ByteArray) := []
  deriving BEq, DecidableEq, Inhabited

/-- Empty initial `Model.State` with no recorded compressed streams. -/
def State.empty : State := {}

/-- Look up the recorded plaintext for `(codec, compressed)`, if known. -/
def State.lookup (st : State) (codec : Codec) (compressed : ByteArray) : Option ByteArray :=
  match st.known.find? (fun entry => entry.1.1 == codec && entry.1.2 == compressed) with
  | some entry => some entry.2
  | none => none

/-- Record `(codec, compressed) ↦ plain` in `st` when `(codec, compressed)` is not already recorded. -/
def State.record (st : State) (codec : Codec) (compressed plain : ByteArray) : State :=
  match st.lookup codec compressed with
  | some _ => st
  | none => { known := ((codec, compressed), plain) :: st.known }

/-- Stateful relational transition predicate for `compressWith` from `st₀` to `(res, st₁)` under `env`. -/
def allowedCompressStep (env : CompressEnv) (st₀ : State) (codec : Codec)
    (opts : CompressOptions) (input : ByteArray)
    (res : Except CompressError ByteArray) (st₁ : State) : Bool :=
  if !isValidCompressInput codec opts input then
    st₁ == st₀ &&
    match res with
    | .error e => e.kind == .invalidInput && isWellFormedCompressError codec e
    | .ok _ => false
  else
    match res with
    | .error e =>
      st₁ == st₀ &&
      (allowedTransientError env codec e ||
        match env.toolStatus codec with
        | .missingOrNonExec => e.kind == .toolNotFound && isWellFormedCompressError codec e
        | .pathSymlinkLoop => e.kind == .invalidInput && isWellFormedCompressError codec e
        | .pathOrPipeIoError => e.kind == .ioError && isWellFormedCompressError codec e
        | .available =>
          e.kind == .outputLimitExceeded &&
          isWellFormedCompressError codec e &&
          opts.maxOutputBytes < maxCompressedBound codec input.size)
    | .ok comp =>
      env.toolStatus codec == .available &&
      comp.size ≤ opts.maxOutputBytes &&
      hasCanonicalCompressedFraming codec comp &&
      (match st₀.lookup codec comp with
       | some prev => prev == input
       | none => true) &&
      st₁ == st₀.record codec comp input

/-- Stateful relational transition predicate for `decompressWith` from `st₀` to `(res, st₁)` under `env`. -/
def allowedDecompressStep (env : CompressEnv) (st₀ : State) (codec : Codec)
    (opts : DecompressOptions) (input : ByteArray)
    (res : Except CompressError ByteArray) (st₁ : State) : Bool :=
  if !isValidDecompressInput opts input then
    st₁ == st₀ &&
    match res with
    | .error e => e.kind == .invalidInput && isWellFormedCompressError codec e
    | .ok _ => false
  else
    match env.toolStatus codec with
    | .missingOrNonExec =>
      st₁ == st₀ &&
      match res with
      | .error e =>
        allowedTransientError env codec e ||
        (e.kind == .toolNotFound && isWellFormedCompressError codec e)
      | .ok _ => false
    | .pathSymlinkLoop =>
      st₁ == st₀ &&
      match res with
      | .error e =>
        allowedTransientError env codec e ||
        (e.kind == .invalidInput && isWellFormedCompressError codec e)
      | .ok _ => false
    | .pathOrPipeIoError =>
      st₁ == st₀ &&
      match res with
      | .error e =>
        allowedTransientError env codec e ||
        (e.kind == .ioError && isWellFormedCompressError codec e)
      | .ok _ => false
    | .available =>
      match st₀.lookup codec input with
      | some expected =>
        st₁ == st₀ &&
        match res with
        | .error e =>
          allowedTransientError env codec e ||
          (expected.size > opts.maxOutputBytes &&
            e.kind == .outputLimitExceeded &&
            isWellFormedCompressError codec e)
        | .ok out =>
          expected.size ≤ opts.maxOutputBytes && out == expected
      | none =>
        match res with
        | .error e =>
          st₁ == st₀ &&
          (allowedTransientError env codec e ||
            ((e.kind == .outputLimitExceeded || e.kind == .corruptData) &&
             isWellFormedCompressError codec e))
        | .ok out =>
          out.size ≤ opts.maxOutputBytes &&
          (codec != .gzip || hasGzipHeader input) &&
          st₁ == st₀.record codec input out

/-- Single-step stateless convenience wrapper for `allowedCompressStep` from `State.empty`. -/
def allowedCompressWith (env : CompressEnv) (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (res : Except CompressError ByteArray) : Bool :=
  let st₁ := match res with | .ok comp => State.empty.record codec comp input | .error _ => State.empty
  allowedCompressStep env State.empty codec opts input res st₁

/-- Single-step stateless convenience wrapper for `allowedDecompressStep` from `State.empty`. -/
def allowedDecompressWith (env : CompressEnv) (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (res : Except CompressError ByteArray) : Bool :=
  let st₁ := match res with | .ok out => State.empty.record codec input out | .error _ => State.empty
  allowedDecompressStep env State.empty codec opts input res st₁

/-- Relational specification predicate for `isToolAvailable`. -/
def allowedIsToolAvailable (env : CompressEnv) (codec : Codec) (avail : Bool) : Bool :=
  match env.toolStatus codec with
  | .available =>
    if env.allowTimeout || env.allowResourceIoError || env.allowExternalSignal then true
    else avail == true
  | _ => avail == false

/-- Map non-`.available` `toolStatus` values to deterministic pre-check `CompressError`s. -/
def envPrecheckError (env : CompressEnv) (codec : Codec) : Option CompressError :=
  match env.toolStatus codec with
  | .available => none
  | .missingOrNonExec =>
    some { kind := .toolNotFound, codec := some codec, message := codecProgram codec ++ " not found or not executable" }
  | .pathSymlinkLoop =>
    some { kind := .invalidInput, codec := some codec, message := codecProgram codec ++ " PATH symlink loop" }
  | .pathOrPipeIoError =>
    some { kind := .ioError, codec := some codec, message := codecProgram codec ++ " PATH or pipe I/O error" }

/-- Pure deterministic stateful `CompressApiM` witness over `StateT State (ReaderM CompressEnv)`. -/
def modelApi : CompressApiM (StateT State (ReaderM CompressEnv)) :=
  let doCompressWith (codec : Codec) (opts : CompressOptions) (input : ByteArray) :
      StateT State (ReaderM CompressEnv) (Except CompressError ByteArray) := do
    if !isValidCompressInput codec opts input then
      return .error { kind := .invalidInput, codec := some codec, message := "invalid compress options or input size" }
    else
      let env ← read
      match envPrecheckError env codec with
      | some e => return .error e
      | none =>
        let comp := encodeStored codec input
        if comp.size > opts.maxOutputBytes then
          return .error { kind := .outputLimitExceeded, codec := some codec, message := codecProgram codec ++ " output exceeded maxOutputBytes" }
        else
          let st ← get
          set (st.record codec comp input)
          return .ok comp
  let doDecompressWith (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
      StateT State (ReaderM CompressEnv) (Except CompressError ByteArray) := do
    if !isValidDecompressInput opts input then
      return .error { kind := .invalidInput, codec := some codec, message := "invalid decompress options or input size" }
    else
      let env ← read
      match envPrecheckError env codec with
      | some e => return .error e
      | none =>
        let st ← get
        match st.lookup codec input with
        | some expected =>
          if expected.size > opts.maxOutputBytes then
            return .error { kind := .outputLimitExceeded, codec := some codec, message := codecProgram codec ++ " output exceeded maxOutputBytes" }
          else
            return .ok expected
        | none =>
          return .error { kind := .corruptData, codec := some codec, message := codecProgram codec ++ " corrupt compressed stream" }
  { compress := fun codec input => doCompressWith codec {} input
    decompress := fun codec input => doDecompressWith codec {} input
    compressWith := doCompressWith
    decompressWith := doDecompressWith
    isToolAvailable := fun codec => do
      let env ← read
      return env.toolStatus codec == .available }

end Model

end LeanSwe.Compress
