import LeanSwe.Compress.Types

namespace Fuzz.Compress

open LeanSwe.Compress

/-- Outcome returned by the persistent Python reference codec oracle. -/
inductive PyOracleOutcome where
  /-- Input decoded cleanly into `plain` (or encoded cleanly into `plain`). -/
  | ok (plain : ByteArray)
  /-- Input failed container or checksum validation. -/
  | corrupt
  deriving DecidableEq, BEq

instance : Repr PyOracleOutcome where
  reprPrec
    | .ok bs, _ => s!"PyOracleOutcome.ok (size={bs.size})"
    | .corrupt, _ => "PyOracleOutcome.corrupt"

/-- Persistent `python3` child process speaking binary length-prefixed codec requests. -/
structure PyOracle where
  /-- Spawned `python3` child process handle (`stdin` piped). -/
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }

private def codecToByte : Codec → UInt8
  | .zstd => 0
  | .xz => 1
  | .gzip => 2

private def encodeU32LE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 24) &&& 0xFF)
  ]

private def decodeU32LE (bs : ByteArray) : Nat :=
  if bs.size < 4 then 0
  else
    (bs.get! 0).toNat |||
    ((bs.get! 1).toNat <<< 8) |||
    ((bs.get! 2).toNat <<< 16) |||
    ((bs.get! 3).toNat <<< 24)

private def readExact (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let mut acc := ByteArray.emptyWithCapacity n
  while acc.size < n do
    let got ← h.read (USize.ofNat (n - acc.size))
    if got.isEmpty then
      throw (IO.userError s!"PY_ORACLE_EOF remaining={n - acc.size}")
    acc := acc ++ got
  return acc

private def pyOracleScript : String := String.intercalate "\n" [
  "import gzip, io, lzma, struct, sys, zlib, zstandard",
  "stdin = sys.stdin.buffer",
  "stdout = sys.stdout.buffer",
  "def read_exact(n):",
  "    buf = bytearray()",
  "    while len(buf) < n:",
  "        chunk = stdin.read(n - len(buf))",
  "        if not chunk:",
  "            return None",
  "        buf.extend(chunk)",
  "    return bytes(buf)",
  "MAX_OUT = 64 * 1024 * 1024 + 4096",
  "def decomp_zstd(data):",
  "    pos, n, out, seen = 0, len(data), bytearray(), False",
  "    while pos < n:",
  "        if pos + 4 > n: return None",
  "        magic = struct.unpack_from('<I', data, pos)[0]",
  "        if 0x184D2A50 <= magic <= 0x184D2A5F:",
  "            if pos + 8 > n: return None",
  "            slen = struct.unpack_from('<I', data, pos + 4)[0]",
  "            if pos + 8 + slen > n: return None",
  "            pos += 8 + slen",
  "            seen = True",
  "            continue",
  "        chk_len, first_chunks = len(out), bytearray()",
  "        try:",
  "            for c in zstandard.ZstdDecompressor().read_to_iter(io.BytesIO(data[pos:])):",
  "                chk_len += len(c)",
  "                if chk_len > MAX_OUT:",
  "                    return None",
  "                first_chunks.extend(c)",
  "        except Exception:",
  "            return None",
  "        d = zstandard.ZstdDecompressor().decompressobj()",
  "        try:",
  "            _ = d.decompress(data[pos:])",
  "        except Exception:",
  "            return None",
  "        if not d.eof:",
  "            return None",
  "        frame_end = n - len(d.unused_data)",
  "        if frame_end == n:",
  "            out.extend(first_chunks)",
  "        else:",
  "            try:",
  "                for c in zstandard.ZstdDecompressor().read_to_iter(io.BytesIO(data[pos:frame_end])):",
  "                    out.extend(c)",
  "                    if len(out) > MAX_OUT:",
  "                        return None",
  "            except Exception:",
  "                return None",
  "        pos = frame_end",
  "        seen = True",
  "    return bytes(out) if seen else None",
  "def decomp_xz(data):",
  "    pos, n, out, seen = 0, len(data), bytearray(), False",
  "    while pos < n:",
  "        if seen and data[pos] == 0:",
  "            zstart = pos",
  "            while pos < n and data[pos] == 0:",
  "                pos += 1",
  "            if pos == n and (pos - zstart) % 4 == 0:",
  "                return bytes(out)",
  "            return None",
  "        d = lzma.LZMADecompressor(format=lzma.FORMAT_XZ)",
  "        rem = MAX_OUT + 1 - len(out)",
  "        try:",
  "            chunk = d.decompress(data[pos:], max_length=rem)",
  "        except lzma.LZMAError:",
  "            return None",
  "        if not d.eof or len(out) + len(chunk) > MAX_OUT:",
  "            return None",
  "        out.extend(chunk)",
  "        pos = n - len(d.unused_data)",
  "        seen = True",
  "    return bytes(out) if seen else None",
  "def decomp_gzip(data):",
  "    pos, n, out, seen = 0, len(data), bytearray(), False",
  "    while pos < n:",
  "        d = zlib.decompressobj(31)",
  "        rem = MAX_OUT + 1 - len(out)",
  "        try:",
  "            chunk = d.decompress(data[pos:], rem)",
  "            if d.unconsumed_tail:",
  "                return None",
  "            chunk += d.flush(max(1, rem - len(chunk)))",
  "        except zlib.error:",
  "            return None",
  "        if not d.eof or len(out) + len(chunk) > MAX_OUT:",
  "            return None",
  "        out.extend(chunk)",
  "        pos = n - len(d.unused_data)",
  "        seen = True",
  "    return bytes(out) if seen else None",
  "while True:",
  "    hdr = read_exact(6)",
  "    if hdr is None:",
  "        break",
  "    op, codec_b, plen = struct.unpack('<BBI', hdr)",
  "    payload = read_exact(plen) if plen > 0 else b''",
  "    if payload is None:",
  "        break",
  "    if op == 0:",
  "        if codec_b == 0: res = decomp_zstd(payload)",
  "        elif codec_b == 1: res = decomp_xz(payload)",
  "        else: res = decomp_gzip(payload)",
  "        if res is None:",
  "            stdout.write(b'\\x01\\x00\\x00\\x00\\x00')",
  "        else:",
  "            stdout.write(struct.pack('<BI', 0, len(res)) + res)",
  "    elif op == 2:",
  "        try:",
  "            res = lzma.compress(payload, format=lzma.FORMAT_XZ, filters=[{'id': lzma.FILTER_X86}, {'id': lzma.FILTER_LZMA2, 'preset': 1}])",
  "            stdout.write(struct.pack('<BI', 0, len(res)) + res)",
  "        except Exception:",
  "            stdout.write(b'\\x01\\x00\\x00\\x00\\x00')",
  "    else:",
  "        try:",
  "            if codec_b == 0: res = zstandard.ZstdCompressor().compress(payload)",
  "            elif codec_b == 1: res = lzma.compress(payload, format=lzma.FORMAT_XZ)",
  "            else: res = gzip.compress(payload, mtime=0)",
  "            stdout.write(struct.pack('<BI', 0, len(res)) + res)",
  "        except Exception:",
  "            stdout.write(b'\\x01\\x00\\x00\\x00\\x00')",
  "    stdout.flush()"
]

/-- Spawn the persistent Python reference oracle child process. -/
def PyOracle.spawn : IO PyOracle := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-I", "-u", "-c", pyOracleScript]
    stdin := .piped
    stdout := .piped
    stderr := .null
    env := #[
      ("LD_PRELOAD", none),
      ("XZ_OPT", none),
      ("XZ_DEFAULTS", none),
      ("ZSTD_CLEVEL", none),
      ("ZSTD_NBTHREADS", none),
      ("GZIP", none),
      ("LC_ALL", some "C"),
      ("LANG", some "C")
    ]
  }
  return { child := child }

/-- Terminate the persistent Python reference oracle and wait for exit. -/
def PyOracle.close (oracle : PyOracle) : IO Unit := do
  let res ← try (some <$> oracle.child.takeStdin) catch _ => pure none
  match res with
  | some (_, child) =>
    let _ ← try child.tryWait catch _ => pure none
    let _ ← try child.kill catch _ => pure ()
    let _ ← try child.wait catch _ => pure 0
  | none =>
    let _ ← try oracle.child.tryWait catch _ => pure none
    let _ ← try oracle.child.kill catch _ => pure ()
    let _ ← try oracle.child.wait catch _ => pure 0

private def callOracle (oracle : PyOracle) (opByte codecByte : UInt8) (payload : ByteArray) : IO PyOracleOutcome := do
  let hdr := (ByteArray.mk #[opByte, codecByte]) ++ encodeU32LE payload.size
  oracle.child.stdin.write hdr
  unless payload.isEmpty do
    oracle.child.stdin.write payload
  oracle.child.stdin.flush
  let respHdr ← readExact oracle.child.stdout 5
  let status := respHdr.get! 0
  let outLen := decodeU32LE (respHdr.extract 1 5)
  let out ← if outLen == 0 then pure ByteArray.empty else readExact oracle.child.stdout outLen
  if status == 0 then
    return .ok out
  else
    return .corrupt

/-- Reference-decompress `input` under `codec` using the Python oracle. -/
def PyOracle.decompress (oracle : PyOracle) (codec : Codec) (input : ByteArray) : IO PyOracleOutcome :=
  callOracle oracle 0 (codecToByte codec) input

/-- Reference-compress `payload` under `codec` using the Python oracle. -/
def PyOracle.compress (oracle : PyOracle) (codec : Codec) (payload : ByteArray) : IO ByteArray := do
  match ← callOracle oracle 1 (codecToByte codec) payload with
  | .ok out => return out
  | .corrupt => throw (IO.userError s!"PY_ORACLE_COMPRESS_FAILED codec={repr codec}")

/-- Reference-compress `payload` into a multi-filter x86 BCJ + LZMA2 `.xz` stream using Python `lzma`. -/
def PyOracle.compressXzBcj (oracle : PyOracle) (payload : ByteArray) : IO ByteArray := do
  match ← callOracle oracle 2 1 payload with
  | .ok out => return out
  | .corrupt => throw (IO.userError "PY_ORACLE_COMPRESS_XZ_BCJ_FAILED")

end Fuzz.Compress
