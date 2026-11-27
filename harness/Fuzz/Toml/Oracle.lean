import LeanSwe.Toml.Types
import LeanSweProofs.Toml.Model
import Fuzz.Toml.YearZero

namespace Fuzz.Toml

open LeanSwe.Toml

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Encode a `ByteArray` as lowercase hexadecimal ASCII. -/
def bytesToHex (bs : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0 : bs.size] do
    let b := bs[i]!.toNat
    out := out.push (hexDigit (b / 16))
    out := out.push (hexDigit (b % 16))
  return out

private def pushU32BE (acc : ByteArray) (n : Nat) : ByteArray :=
  acc.push (UInt8.ofNat ((n >>> 24) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 16) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 8) &&& 0xff))
    |>.push (UInt8.ofNat (n &&& 0xff))

private def pushU64BE (acc : ByteArray) (u : UInt64) : ByteArray :=
  acc.push ((u >>> 56).toUInt8)
    |>.push ((u >>> 48).toUInt8)
    |>.push ((u >>> 40).toUInt8)
    |>.push ((u >>> 32).toUInt8)
    |>.push ((u >>> 24).toUInt8)
    |>.push ((u >>> 16).toUInt8)
    |>.push ((u >>> 8).toUInt8)
    |>.push u.toUInt8

private def byteArrayLexLt (a b : ByteArray) : Bool := Id.run do
  let lim := min a.size b.size
  for i in [0 : lim] do
    let ba := a[i]!
    let bb := b[i]!
    if ba != bb then
      return ba < bb
  return a.size < b.size

private def pushDateBytes (acc : ByteArray) (d : Std.Time.PlainDate) : ByteArray :=
  (pushU32BE acc d.year.toNat)
    |>.push (UInt8.ofNat d.month.val.toNat)
    |>.push (UInt8.ofNat d.day.val.toNat)

private def pushTimeBytes (pyMode : Bool) (acc : ByteArray) (t : Std.Time.PlainTime) : ByteArray :=
  let rawNs := t.nanosecond.val.toNat
  let subsec := if pyMode then rawNs / 1000 else rawNs
  let a1 := acc.push (UInt8.ofNat t.hour.val.toNat)
    |>.push (UInt8.ofNat t.minute.val.toNat)
    |>.push (UInt8.ofNat t.second.val.toNat)
  pushU32BE a1 subsec

mutual
  /-- Encode a `TomlValue` into canonical binary TLV (`pyMode = false` for `Model`, `true` for Python `tomllib`). -/
  def encodeCanonValue (pyMode : Bool) (acc : ByteArray) : TomlValue → ByteArray
    | .bool false => acc.push 0x01
    | .bool true => acc.push 0x02
    | .int n =>
      let bs := (toString n.toInt).toUTF8
      pushU32BE (acc.push 0x03) bs.size ++ bs
    | .float f =>
      if f.isNaN then
        acc.push 0x04 |>.push 0x01
      else if !pyMode && f == 0.0 then
        pushU64BE (acc.push 0x04 |>.push 0x00) 0
      else
        pushU64BE (acc.push 0x04 |>.push 0x00) f.toBits
    | .string s =>
      let bs := s.toUTF8
      pushU32BE (acc.push 0x05) bs.size ++ bs
    | .offsetDateTime odt =>
      let a1 := pushDateBytes (acc.push 0x06) odt.dateTime.date
      let a2 := pushTimeBytes pyMode a1 odt.dateTime.time
      let ob := (toString odt.offset.second.val).toUTF8
      pushU32BE a2 ob.size ++ ob
    | .localDateTime dt =>
      let a1 := pushDateBytes (acc.push 0x07) dt.date
      pushTimeBytes pyMode a1 dt.time
    | .localDate d =>
      pushDateBytes (acc.push 0x08) d
    | .localTime t =>
      pushTimeBytes pyMode (acc.push 0x09) t
    | .array xs =>
      let a1 := pushU32BE (acc.push 0x0a) xs.size
      encodeCanonList pyMode a1 xs.toList
    | .table t =>
      let rawPairs := encodeCanonEntries pyMode t.toList
      let sorted := rawPairs.toArray.qsort fun a b => byteArrayLexLt a.1 b.1
      let a1 := pushU32BE (acc.push 0x0b) sorted.size
      sorted.foldl (fun cur (kb, vb) => pushU32BE cur kb.size ++ kb ++ vb) a1
  termination_by v => sizeOf v
  decreasing_by
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)

  /-- Encode ordered `List TomlValue` elements into canonical binary TLV. -/
  def encodeCanonList (pyMode : Bool) (acc : ByteArray) : List TomlValue → ByteArray
    | [] => acc
    | x :: xs => encodeCanonList pyMode (encodeCanonValue pyMode acc x) xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith

  /-- Encode `(keyBytes, valTlv)` pairs for a table association list. -/
  def encodeCanonEntries (pyMode : Bool) : List (String × TomlValue) → List (ByteArray × ByteArray)
    | [] => []
    | (k, v) :: rest =>
      (k.toUTF8, encodeCanonValue pyMode ByteArray.empty v) :: encodeCanonEntries pyMode rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp +arith
end

/-- Canonical TLV encoding invariant under `Model.TomlTableEquiv` (full 9-digit nanosecond precision). -/
def encodeCanonTomlModel (doc : TomlTable) : ByteArray :=
  encodeCanonValue false ByteArray.empty (.table doc)

/-- Canonical TLV encoding matching Python 3 `tomllib.loads` (exact `-0.0`/`+0.0` bits and microsecond precision). -/
def encodeCanonTomlPy (doc : TomlTable) : ByteArray :=
  encodeCanonValue true ByteArray.empty (.table doc)

/-- Computable `Model.TomlTableEquiv` check on `WellFormedTable` values via canonical TLV equality. -/
def tomlTableEquivBool (a b : TomlTable) : Bool :=
  encodeCanonTomlModel a == encodeCanonTomlModel b

/-- Expected Python `tomllib.loads` outcome classification for a queued parse item. -/
inductive PyParseMode where
  /-- Expect `tomllib.loads` to succeed with all integers in `Int64` and exact TLV match. -/
  | ok
  /-- Expect `tomllib.loads` to raise `TOMLDecodeError`. -/
  | errSyntax
  /-- Expect `tomllib.loads` to parse valid TOML syntax with at least one integer outside `Int64` bounds. -/
  | errOverflowStrict
  /-- Expect `tomllib.loads` to raise `TOMLDecodeError` or produce an integer outside `Int64` bounds. -/
  | errOverflowAny
  /-- Expect `tomllib.loads` to raise `TOMLDecodeError` due to Python `datetime.MINYEAR == 1` on year `0000`. -/
  | yearZero
  deriving BEq, Repr, Inhabited

private def pyParseModeWire : PyParseMode → String
  | .ok => "OK"
  | .errSyntax => "ERR_SYNTAX"
  | .errOverflowStrict => "ERR_OVERFLOW_STRICT"
  | .errOverflowAny => "ERR_OVERFLOW_ANY"
  | .yearZero => "YEAR0"

/-- Queued differential parse parity item (`LeanSwe.Toml.parse` vs Python 3 `tomllib.loads`). -/
structure PyParseCheck where
  /-- UTF-8 input bytes of the TOML document. -/
  rawBytes : ByteArray
  /-- Expected Python `tomllib` behavior classification. -/
  mode : PyParseMode
  /-- Expected Python-compatible canonical TLV when `mode == .ok`. -/
  expectedPyTlv : ByteArray
  /-- Diagnostic label for failure reporting. -/
  label : String
  deriving Inhabited

/-- Queued check that `LeanSwe.Toml.format` output is accepted by Python `tomllib.loads` with equal AST. -/
structure PyFormatCheck where
  /-- Canonical TOML text emitted by `LeanSwe.Toml.format`. -/
  rendered : String
  /-- Expected Python-compatible canonical TLV bytes. -/
  expectedPyTlv : ByteArray
  /-- Diagnostic label for failure reporting. -/
  label : String
  deriving Inhabited

/-- Batched Python 3 `tomllib` differential oracle worklist for one fuzz episode. -/
structure PyOracleBatch where
  /-- Parse accept/reject, overflow-divergence, year-0-divergence, and AST parity items. -/
  parses : Array PyParseCheck := #[]
  /-- `LeanSwe.Toml.format` -> `tomllib.loads` roundtrip parity items. -/
  formats : Array PyFormatCheck := #[]
  deriving Inhabited

/-- Check whether `batch` has zero queued items. -/
def PyOracleBatch.isEmpty (b : PyOracleBatch) : Bool :=
  b.parses.isEmpty && b.formats.isEmpty

private def pyTomlOracleScript : String := String.intercalate "\n" [
  "import datetime, math, struct, sys, tomllib",
  "sys.set_int_max_str_digits(0)",
  "sys.setrecursionlimit(10000)",
  "INT64_MIN = -(1 << 63)",
  "INT64_MAX = (1 << 63) - 1",
  "class Int64OverflowError(Exception):",
  "    pass",
  "def has_surrogate(s):",
  "    for ch in s:",
  "        o = ord(ch)",
  "        if 0xD800 <= o <= 0xDFFF:",
  "            return True",
  "    return False",
  "def encode_tlv(v, out):",
  "    if isinstance(v, bool):",
  "        out.append(2 if v else 1)",
  "    elif isinstance(v, int):",
  "        if v < INT64_MIN or v > INT64_MAX:",
  "            raise Int64OverflowError(f'int64 overflow: {v}')",
  "        sb = str(v).encode('ascii')",
  "        out.append(3)",
  "        out.extend(struct.pack('>I', len(sb)))",
  "        out.extend(sb)",
  "    elif isinstance(v, float):",
  "        if math.isnan(v):",
  "            out.extend(b'\\x04\\x01')",
  "        else:",
  "            bits = struct.unpack('>Q', struct.pack('>d', v))[0]",
  "            out.extend(b'\\x04\\x00')",
  "            out.extend(struct.pack('>Q', bits))",
  "    elif isinstance(v, str):",
  "        if has_surrogate(v):",
  "            raise ValueError('lone surrogate in string')",
  "        bs = v.encode('utf-8')",
  "        out.append(5)",
  "        out.extend(struct.pack('>I', len(bs)))",
  "        out.extend(bs)",
  "    elif isinstance(v, datetime.datetime):",
  "        if v.tzinfo is not None:",
  "            off_sec = int(v.utcoffset().total_seconds())",
  "            ob = str(off_sec).encode('ascii')",
  "            out.append(6)",
  "            out.extend(struct.pack('>IBBBBBII', v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, len(ob)))",
  "            out.extend(ob)",
  "        else:",
  "            out.append(7)",
  "            out.extend(struct.pack('>IBBBBBI', v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond))",
  "    elif isinstance(v, datetime.date):",
  "        out.append(8)",
  "        out.extend(struct.pack('>IBB', v.year, v.month, v.day))",
  "    elif isinstance(v, datetime.time):",
  "        out.append(9)",
  "        out.extend(struct.pack('>BBBI', v.hour, v.minute, v.second, v.microsecond))",
  "    elif isinstance(v, list):",
  "        out.append(10)",
  "        out.extend(struct.pack('>I', len(v)))",
  "        for elem in v:",
  "            encode_tlv(elem, out)",
  "    elif isinstance(v, dict):",
  "        items = []",
  "        for k, val in v.items():",
  "            if has_surrogate(k):",
  "                raise ValueError('lone surrogate in key')",
  "            sub = bytearray()",
  "            encode_tlv(val, sub)",
  "            items.append((k.encode('utf-8'), bytes(sub)))",
  "        items.sort(key=lambda kv: kv[0])",
  "        out.append(11)",
  "        out.extend(struct.pack('>I', len(items)))",
  "        for kb, vb in items:",
  "            out.extend(struct.pack('>I', len(kb)))",
  "            out.extend(kb)",
  "            out.extend(vb)",
  "    else:",
  "        raise TypeError('unexpected type: ' + str(type(v)))",
  "batch_err = None",
  "for raw_line in sys.stdin:",
  "    line = raw_line.rstrip('\\r\\n')",
  "    if not line:",
  "        continue",
  "    if line == 'QUIT':",
  "        break",
  "    if line == 'END':",
  "        if batch_err is not None:",
  "            sys.stdout.write('ERR:' + batch_err + '\\n')",
  "        else:",
  "            sys.stdout.write('OK\\n')",
  "        sys.stdout.flush()",
  "        batch_err = None",
  "        continue",
  "    if batch_err is not None:",
  "        continue",
  "    try:",
  "        parts = line.split(' ')",
  "        op = parts[0]",
  "        if op == 'P':",
  "            mode = parts[1]",
  "            raw_b = bytes.fromhex(parts[2])",
  "            exp_tlv = bytes.fromhex(parts[3]) if parts[3] != '-' else b''",
  "            lbl = bytes.fromhex(parts[4]).decode('utf-8', 'replace')",
  "            text = raw_b.decode('utf-8', 'strict')",
  "            if mode == 'OK':",
  "                try:",
  "                    doc = tomllib.loads(text)",
  "                    buf = bytearray()",
  "                    encode_tlv(doc, buf)",
  "                    got_tlv = bytes(buf)",
  "                except Exception as e:",
  "                    raise AssertionError(f'P_LEAN_OK_PY_ERR[{lbl}]: {type(e).__name__}: {e} raw={text[:80]!r}')",
  "                if got_tlv != exp_tlv:",
  "                    raise AssertionError(f'P_AST_MISMATCH[{lbl}]: raw={text[:80]!r}')",
  "            elif mode == 'ERR_SYNTAX':",
  "                try:",
  "                    doc = tomllib.loads(text)",
  "                    py_parsed = True",
  "                except (tomllib.TOMLDecodeError, ValueError):",
  "                    py_parsed = False",
  "                if py_parsed:",
  "                    raise AssertionError(f'P_LEAN_ERR_PY_OK[{lbl}]: raw={text[:80]!r}')",
  "            elif mode == 'ERR_OVERFLOW_STRICT':",
  "                try:",
  "                    doc = tomllib.loads(text)",
  "                except Exception as e:",
  "                    raise AssertionError(f'P_OVERFLOW_STRICT_PY_SYNTAX_ERR[{lbl}]: {e} raw={text[:80]!r}')",
  "                try:",
  "                    buf = bytearray()",
  "                    encode_tlv(doc, buf)",
  "                    overflowed = False",
  "                except Int64OverflowError:",
  "                    overflowed = True",
  "                if not overflowed:",
  "                    raise AssertionError(f'P_OVERFLOW_STRICT_PY_IN_RANGE[{lbl}]: raw={text[:80]!r}')",
  "            elif mode == 'ERR_OVERFLOW_ANY':",
  "                try:",
  "                    doc = tomllib.loads(text)",
  "                    buf = bytearray()",
  "                    encode_tlv(doc, buf)",
  "                    accepted_in_range = True",
  "                except (tomllib.TOMLDecodeError, Int64OverflowError, ValueError):",
  "                    accepted_in_range = False",
  "                if accepted_in_range:",
  "                    raise AssertionError(f'P_OVERFLOW_ANY_PY_OK[{lbl}]: raw={text[:80]!r}')",
  "            elif mode == 'YEAR0':",
  "                try:",
  "                    doc = tomllib.loads(text)",
  "                    py_ok = True",
  "                    err_str = ''",
  "                except tomllib.TOMLDecodeError as e:",
  "                    py_ok = False",
  "                    err_str = str(e)",
  "                if py_ok:",
  "                    raise AssertionError(f'P_YEAR0_PY_OK[{lbl}]: raw={text[:80]!r}')",
  "                if 'Invalid date or datetime' not in err_str:",
  "                    raise AssertionError(f'P_YEAR0_UNEXPECTED_ERR[{lbl}]: err={err_str!r} raw={text[:80]!r}')",
  "            else:",
  "                raise AssertionError('unknown P mode ' + repr(mode))",
  "        elif op == 'F':",
  "            rend_b = bytes.fromhex(parts[1])",
  "            exp_tlv = bytes.fromhex(parts[2])",
  "            lbl = bytes.fromhex(parts[3]).decode('utf-8', 'replace')",
  "            text = rend_b.decode('utf-8', 'strict')",
  "            try:",
  "                doc = tomllib.loads(text)",
  "                buf = bytearray()",
  "                encode_tlv(doc, buf)",
  "                got_tlv = bytes(buf)",
  "            except Exception as e:",
  "                raise AssertionError(f'F_PY_ERR[{lbl}]: {type(e).__name__}: {e} rend={text[:80]!r}')",
  "            if got_tlv != exp_tlv:",
  "                raise AssertionError(f'F_AST_MISMATCH[{lbl}]: rend={text[:80]!r}')",
  "        else:",
  "            raise AssertionError('unknown op ' + repr(op))",
  "    except Exception as exc:",
  "        msg = str(exc).replace('\\n', ' ').strip()",
  "        batch_err = msg if msg else type(exc).__name__"
]

private def encodeBatchPayload (batch : PyOracleBatch) : String := Id.run do
  let total := batch.parses.size + batch.formats.size
  let mut lines : Array String := Array.mkEmpty (total + 1)
  for item in batch.parses do
    let modeStr := pyParseModeWire item.mode
    let tlvHex := if item.mode == .ok then bytesToHex item.expectedPyTlv else "-"
    let lblHex := bytesToHex item.label.toUTF8
    lines := lines.push s!"P {modeStr} {bytesToHex item.rawBytes} {tlvHex} {lblHex}"
  for item in batch.formats do
    let lblHex := bytesToHex item.label.toUTF8
    lines := lines.push s!"F {bytesToHex item.rendered.toUTF8} {bytesToHex item.expectedPyTlv} {lblHex}"
  lines := lines.push "END"
  return "\n".intercalate lines.toList ++ "\n"

private def drainPipeToDiscard (h : IO.FS.Handle) : IO Unit := do
  while true do
    let chunk ← h.read 8192
    if chunk.isEmpty then
      break

private def drainStderrLoop (h : IO.FS.Handle) (ref : IO.Ref String) : IO Unit := do
  while true do
    let chunk ← h.read 4096
    if chunk.isEmpty then
      break
    let text := match String.fromUTF8? chunk with
      | some s => s
      | none => s!"<non-utf8 {chunk.size}B>"
    ref.modify fun cur =>
      if cur.length < 16384 then cur ++ text else cur

/-- Persistent Python 3 `tomllib` differential oracle co-process handle. -/
structure PyOracleClient where
  /-- Spawned `python3` child process. -/
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  /-- Bounded captured `stderr` buffer drained asynchronously. -/
  stderrRef : IO.Ref String
  /-- Background task draining `child.stderr`. -/
  stderrTask : Task (Except IO.Error Unit)

/-- Spawn the persistent Python 3 `tomllib.loads` oracle in isolated mode (`-I`). -/
def startPyOracleClient : IO PyOracleClient := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-I", "-B", "-u", "-c", pyTomlOracleScript]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stderrRef ← IO.mkRef ""
  let stderrTask ← IO.asTask (drainStderrLoop child.stderr stderrRef)
  return { child, stderrRef, stderrTask }

/-- Flush one episode's `PyOracleBatch` to Python `tomllib` and check parity. -/
def flushPyBatch (client : PyOracleClient) (batch : PyOracleBatch) : IO (Except String Unit) := do
  if batch.isEmpty then
    return .ok ()
  let payload := encodeBatchPayload batch
  try
    client.child.stdin.putStr payload
    client.child.stdin.flush
  catch e =>
    let stderr ← client.stderrRef.get
    return .error s!"PYTHON_ORACLE_EOF: write failed ({e}); stderr={stderr.trimAscii.toString}"
  let mut errMsg? : Option String := none
  while true do
    let rawLine ← client.child.stdout.getLine
    if rawLine.isEmpty then
      let stderr ← client.stderrRef.get
      errMsg? := some s!"PYTHON_ORACLE_EOF: {stderr.trimAscii.toString}"
      break
    let line := rawLine.trimAscii.toString
    if line == "OK" then
      break
    else if line.startsWith "ERR:" then
      let detail := (line.drop 4).toString
      errMsg? := some s!"PYTHON_ORACLE_MISMATCH: {detail}"
      break
    else
      errMsg? := some s!"PYTHON_ORACLE_UNEXPECTED_LINE: {line}"
      break
  if let some err := errMsg? then
    return .error err
  return .ok ()

@[noinline]
private def closeChildStdin
    (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }) :
    IO (IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }) := do
  let (h, c) ← child.takeStdin
  let _ := h
  return c

/-- Cleanly shut down `client` and assert exit code `0`. -/
def closePyOracleClient (client : PyOracleClient) : IO Unit := do
  let { child, stderrRef, stderrTask } := client
  try
    child.stdin.putStr "QUIT\n"
    child.stdin.flush
  catch _ =>
    pure ()
  let child ← closeChildStdin child
  let stdoutTask ← IO.asTask (drainPipeToDiscard child.stdout)
  let exitCode ← child.wait
  let _ ← IO.ofExcept stdoutTask.get
  let _ ← IO.ofExcept stderrTask.get
  let stderr ← stderrRef.get
  if exitCode != 0 then
    throw (IO.userError s!"PYTHON_ORACLE_NONZERO_EXIT code={exitCode} stderr={stderr.trimAscii.toString}")

/-- Best-effort quiet cleanup of `client` on exception paths. -/
def closePyOracleClientQuiet (client : PyOracleClient) : IO Unit := do
  try
    closePyOracleClient client
  catch _ =>
    pure ()

end Fuzz.Toml
