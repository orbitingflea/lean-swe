import Lean.Data.Json.Basic
import LeanSweProofs.Json.Model

namespace Fuzz.Json

open LeanSwe.Json

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

private def parseHexNib? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

/-- Decode an even-length hexadecimal string into a `ByteArray`. -/
def hexToBytes (hex : String) : Except String ByteArray := do
  let chars := hex.toList
  if chars.length % 2 != 0 then
    throw s!"PYTHON_ORACLE_ODD_HEX_LEN: {chars.length}"
  let rec loop : List Char → ByteArray → Except String ByteArray
    | [], acc => .ok acc
    | hi :: lo :: rest, acc =>
      match parseHexNib? hi, parseHexNib? lo with
      | some h, some l => loop rest (acc.push (UInt8.ofNat (h * 16 + l)))
      | _, _ => .error s!"PYTHON_ORACLE_BAD_HEX_BYTE: {hi}{lo}"
    | [_], _ => .error "PYTHON_ORACLE_ODD_HEX"
  loop chars ByteArray.empty

/-- Decode a hexadecimal UTF-8 string returned by the Python oracle. -/
def hexToUtf8String (hex : String) : Except String String := do
  let bs ← hexToBytes hex
  match String.fromUTF8? bs with
  | some s => .ok s
  | none => .error "PYTHON_ORACLE_INVALID_UTF8"

private def pushU32BE (acc : ByteArray) (n : Nat) : ByteArray :=
  acc.push (UInt8.ofNat ((n >>> 24) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 16) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 8) &&& 0xff))
    |>.push (UInt8.ofNat (n &&& 0xff))

private def stripTrailingZerosCount (cs : List Char) : List Char × Nat :=
  let rec dropRev : List Char → Nat → List Char × Nat
    | '0' :: rest, k => dropRev rest (k + 1)
    | xs, k => (xs.reverse, k)
  dropRev cs.reverse 0

/-- Compute canonical `(isZero, isNeg, sigDigits, exp10)` for exact `Lean.JsonNumber` equivalence. -/
def canonNumParts (n : Lean.JsonNumber) : Bool × Bool × String × Int :=
  if n.mantissa == 0 then
    (true, false, "0", 0)
  else
    let isNeg := n.mantissa < 0
    let rawDigits := n.mantissa.natAbs.repr.toList
    let (sigChars, tz) := stripTrailingZerosCount rawDigits
    let sig := String.ofList sigChars
    let exp10 : Int := Int.ofNat tz - Int.ofNat n.exponent
    (false, isNeg, sig, exp10)

private def byteArrayLexLt (a b : ByteArray) : Bool := Id.run do
  let lim := min a.size b.size
  for i in [0 : lim] do
    let ba := a[i]!
    let bb := b[i]!
    if ba != bb then
      return ba < bb
  return a.size < b.size

/-- Encode a `Lean.Json` value into a canonical tagged binary TLV invariant under `Model.JsonEquiv`. -/
partial def encodeCanonJson (j : Lean.Json) : ByteArray :=
  go ByteArray.empty j
where
  go (acc : ByteArray) : Lean.Json → ByteArray
    | .null => acc.push 0x00
    | .bool false => acc.push 0x01
    | .bool true => acc.push 0x02
    | .num n =>
      let (isZero, isNeg, sig, exp10) := canonNumParts n
      if isZero then
        acc.push 0x03 |>.push 0x00
      else
        let sgnByte : UInt8 := if isNeg then 0x2d else 0x2b
        let sigBytes := sig.toUTF8
        let expBytes := (toString exp10).toUTF8
        let a1 := acc.push 0x03 |>.push sgnByte
        let a2 := pushU32BE a1 sigBytes.size ++ sigBytes
        pushU32BE a2 expBytes.size ++ expBytes
    | .str s =>
      let bs := s.toUTF8
      pushU32BE (acc.push 0x04) bs.size ++ bs
    | .arr xs =>
      let a1 := pushU32BE (acc.push 0x05) xs.size
      xs.foldl go a1
    | .obj kvs =>
      let entries := (Model.objEntries kvs).toArray.map fun (k, v) => (k.toUTF8, v)
      let sorted := entries.qsort fun a b => byteArrayLexLt a.1 b.1
      let a1 := pushU32BE (acc.push 0x06) sorted.size
      sorted.foldl (fun cur (kb, v) => go (pushU32BE cur kb.size ++ kb) v) a1

/-- Computable exact semantic equivalence check on `WellFormedJson` values via canonical TLV equality. -/
def jsonEquivBool (a b : Lean.Json) : Bool :=
  encodeCanonJson a == encodeCanonJson b

/-- Check whether every numeric literal in `j` can be losslessly round-tripped through Python `json.dumps`. -/
partial def isDumpsEligibleJson : Lean.Json → Bool
  | .null | .bool _ | .str _ => true
  | .num n =>
    let (isZero, _, sig, exp10) := canonNumParts n
    if isZero then true
    else if exp10 >= 0 && sig.length + exp10.toNat ≤ 120 then true
    else sig.length ≤ 12 && decide (-12 ≤ exp10) && decide (exp10 ≤ 12)
  | .arr xs => xs.all isDumpsEligibleJson
  | .obj kvs => (Model.objEntries kvs).all fun (_, v) => isDumpsEligibleJson v

/-- Queued differential parse parity item (`LeanSwe.Json.parse` / `parseWantValue` vs Python `json.loads`). -/
structure PyParseCheck where
  /-- Raw input bytes (valid UTF-8 for `parse`, or arbitrary bytes for `invalidUtf8`). -/
  rawBytes : ByteArray
  /-- Whether `LeanSwe.Json` accepted the input. -/
  expectedOk : Bool
  /-- Expected canonical TLV bytes when `expectedOk` is `true`. -/
  expectedCanonTlv : ByteArray
  /-- Diagnostic label for failure reporting. -/
  label : String
  deriving Inhabited

/-- Queued check that `LeanSwe.Json.compress` or `pretty` output is accepted by Python `json.loads` with equal AST. -/
structure PyRenderCheck where
  /-- Short label (`"compress"` or `"pretty"`). -/
  kindTag : String
  /-- Rendered JSON text produced by `LeanSwe.Json`. -/
  rendered : String
  /-- Expected canonical TLV bytes of the source `Lean.Json` value. -/
  expectedCanonTlv : ByteArray
  deriving Inhabited

/-- Queued request for Python `json.dumps` serialization followed by `LeanSwe.Json.parse` roundtrip verification. -/
structure PyDumpsItem where
  /-- Bitmask selecting `ensure_ascii`, `sort_keys`, `indent`, and separator formatting in Python `json.dumps`. -/
  modeFlags : UInt8
  /-- Original `Lean.Json` value sent to Python. -/
  origVal : Lean.Json
  /-- Expected canonical TLV bytes. -/
  expectedCanonTlv : ByteArray
  deriving Inhabited

/-- Batched Python 3 differential oracle worklist for one fuzz episode. -/
structure PyOracleBatch where
  /-- Parse accept/reject and AST parity items. -/
  parses : Array PyParseCheck := #[]
  /-- `compress` / `pretty` -> Python `json.loads` items. -/
  renders : Array PyRenderCheck := #[]
  /-- Python `json.dumps` -> `LeanSwe.Json.parse` roundtrip items. -/
  dumps : Array PyDumpsItem := #[]
  deriving Inhabited

/-- Check whether `batch` has zero queued items. -/
def PyOracleBatch.isEmpty (b : PyOracleBatch) : Bool :=
  b.parses.isEmpty && b.renders.isEmpty && b.dumps.isEmpty

private def pyJsonOracleScript : String := String.intercalate "\n" [
  "import json, struct, sys",
  "sys.set_int_max_str_digits(0)",
  "sys.setrecursionlimit(10000)",
  "MAX_LIMIT = 100000",
  "class CanonNum:",
  "    __slots__ = ('sign', 'sig', 'exp10')",
  "    def __init__(self, sign, sig, exp10):",
  "        self.sign = sign",
  "        self.sig = sig",
  "        self.exp10 = exp10",
  "def strict_pairs_hook(pairs):",
  "    out = {}",
  "    for k, v in pairs:",
  "        if k in out:",
  "            raise ValueError('duplicate key')",
  "        out[k] = v",
  "    return out",
  "def reject_constant(tok):",
  "    raise ValueError('invalid constant: ' + str(tok))",
  "def parse_num_tok(tok):",
  "    s = tok",
  "    neg = s.startswith('-')",
  "    if neg:",
  "        s = s[1:]",
  "    if 'e' in s or 'E' in s:",
  "        mant, exp_s = s.replace('E', 'e').split('e', 1)",
  "        exp_clean = exp_s[1:] if (exp_s.startswith('+') or exp_s.startswith('-')) else exp_s",
  "        exp_mag = int(exp_clean)",
  "        if exp_mag > MAX_LIMIT:",
  "            raise ValueError('exponent exceeds resource limit')",
  "        exp_val = -exp_mag if exp_s.startswith('-') else exp_mag",
  "    else:",
  "        mant, exp_val = s, 0",
  "    if '.' in mant:",
  "        w_part, f_part = mant.split('.', 1)",
  "        if len(f_part) > MAX_LIMIT:",
  "            raise ValueError('frac digits exceed resource limit')",
  "        digits = w_part + f_part",
  "        exp_val = exp_val - len(f_part)",
  "    else:",
  "        digits = mant",
  "    nz = digits.lstrip('0')",
  "    if not nz:",
  "        return CanonNum(0, '0', 0)",
  "    sig = nz.rstrip('0')",
  "    tz = len(nz) - len(sig)",
  "    return CanonNum(-1 if neg else 1, sig, exp_val + tz)",
  "def has_surrogate(s):",
  "    for ch in s:",
  "        o = ord(ch)",
  "        if 0xD800 <= o <= 0xDFFF:",
  "            return True",
  "    return False",
  "def encode_tlv(v, out):",
  "    if v is None:",
  "        out.append(0)",
  "    elif v is False:",
  "        out.append(1)",
  "    elif v is True:",
  "        out.append(2)",
  "    elif isinstance(v, CanonNum):",
  "        if v.sign == 0:",
  "            out.extend(b'\\x03\\x00')",
  "        else:",
  "            out.append(3)",
  "            out.append(45 if v.sign < 0 else 43)",
  "            sb = v.sig.encode('ascii')",
  "            eb = str(v.exp10).encode('ascii')",
  "            out.extend(struct.pack('>I', len(sb)))",
  "            out.extend(sb)",
  "            out.extend(struct.pack('>I', len(eb)))",
  "            out.extend(eb)",
  "    elif isinstance(v, str):",
  "        if has_surrogate(v):",
  "            raise ValueError('lone surrogate in string')",
  "        bs = v.encode('utf-8')",
  "        out.append(4)",
  "        out.extend(struct.pack('>I', len(bs)))",
  "        out.extend(bs)",
  "    elif isinstance(v, list):",
  "        out.append(5)",
  "        out.extend(struct.pack('>I', len(v)))",
  "        for elem in v:",
  "            encode_tlv(elem, out)",
  "    elif isinstance(v, dict):",
  "        items = []",
  "        for k, val in v.items():",
  "            if has_surrogate(k):",
  "                raise ValueError('lone surrogate in key')",
  "            items.append((k.encode('utf-8'), val))",
  "        items.sort(key=lambda kv: kv[0])",
  "        out.append(6)",
  "        out.extend(struct.pack('>I', len(items)))",
  "        for kb, val in items:",
  "            out.extend(struct.pack('>I', len(kb)))",
  "            out.extend(kb)",
  "            encode_tlv(val, out)",
  "    else:",
  "        raise TypeError('unexpected type: ' + str(type(v)))",
  "def strict_loads_tlv(raw_bytes):",
  "    text = raw_bytes.decode('utf-8', 'strict')",
  "    val = json.loads(text, object_pairs_hook=strict_pairs_hook, parse_float=parse_num_tok, parse_int=parse_num_tok, parse_constant=reject_constant)",
  "    buf = bytearray()",
  "    encode_tlv(val, buf)",
  "    return bytes(buf)",
  "def decode_tlv_to_py(data, pos):",
  "    tag = data[pos]",
  "    pos = pos + 1",
  "    if tag == 0:",
  "        return None, pos",
  "    if tag == 1:",
  "        return False, pos",
  "    if tag == 2:",
  "        return True, pos",
  "    if tag == 3:",
  "        sgn = data[pos]",
  "        pos = pos + 1",
  "        if sgn == 0:",
  "            return 0, pos",
  "        slen = struct.unpack_from('>I', data, pos)[0]",
  "        pos = pos + 4",
  "        sig = data[pos:pos + slen].decode('ascii')",
  "        pos = pos + slen",
  "        elen = struct.unpack_from('>I', data, pos)[0]",
  "        pos = pos + 4",
  "        exp10 = int(data[pos:pos + elen].decode('ascii'))",
  "        pos = pos + elen",
  "        neg_pfx = '-' if sgn == 45 else ''",
  "        if exp10 >= 0 and len(sig) + exp10 <= 120:",
  "            ival = int(sig) * (10 ** exp10)",
  "            return (-ival if sgn == 45 else ival), pos",
  "        return float(f'{neg_pfx}{sig}e{exp10}'), pos",
  "    if tag == 4:",
  "        blen = struct.unpack_from('>I', data, pos)[0]",
  "        pos = pos + 4",
  "        s = data[pos:pos + blen].decode('utf-8', 'strict')",
  "        return s, pos + blen",
  "    if tag == 5:",
  "        cnt = struct.unpack_from('>I', data, pos)[0]",
  "        pos = pos + 4",
  "        arr = []",
  "        for _ in range(cnt):",
  "            el, pos = decode_tlv_to_py(data, pos)",
  "            arr.append(el)",
  "        return arr, pos",
  "    if tag == 6:",
  "        cnt = struct.unpack_from('>I', data, pos)[0]",
  "        pos = pos + 4",
  "        obj = {}",
  "        for _ in range(cnt):",
  "            klen = struct.unpack_from('>I', data, pos)[0]",
  "            pos = pos + 4",
  "            k = data[pos:pos + klen].decode('utf-8', 'strict')",
  "            pos = pos + klen",
  "            val, pos = decode_tlv_to_py(data, pos)",
  "            obj[k] = val",
  "        return obj, pos",
  "    raise ValueError('bad tlv tag ' + str(tag))",
  "out_lines = []",
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
  "            if out_lines:",
  "                sys.stdout.write('\\n'.join(out_lines) + '\\n')",
  "            sys.stdout.write('OK\\n')",
  "        sys.stdout.flush()",
  "        out_lines = []",
  "        batch_err = None",
  "        continue",
  "    if batch_err is not None:",
  "        continue",
  "    try:",
  "        parts = line.split(' ')",
  "        op = parts[0]",
  "        if op == 'P':",
  "            exp_ok = int(parts[1])",
  "            raw_b = bytes.fromhex(parts[2])",
  "            exp_tlv = bytes.fromhex(parts[3]) if parts[3] != '-' else b''",
  "            lbl = bytes.fromhex(parts[4]).decode('utf-8', 'replace')",
  "            try:",
  "                got_tlv = strict_loads_tlv(raw_b)",
  "                py_ok = True",
  "                py_err = ''",
  "            except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as e:",
  "                got_tlv = b''",
  "                py_ok = False",
  "                py_err = f'{type(e).__name__}: {e}'",
  "            if exp_ok == 1 and not py_ok:",
  "                raise AssertionError(f'P_LEAN_OK_PY_ERR[{lbl}]: {py_err} raw={raw_b[:80]!r}')",
  "            if exp_ok == 0 and py_ok:",
  "                raise AssertionError(f'P_LEAN_ERR_PY_OK[{lbl}]: raw={raw_b[:80]!r}')",
  "            if exp_ok == 1 and got_tlv != exp_tlv:",
  "                raise AssertionError(f'P_AST_MISMATCH[{lbl}]: raw={raw_b[:80]!r}')",
  "        elif op == 'C':",
  "            ktag = parts[1]",
  "            rend_b = bytes.fromhex(parts[2])",
  "            exp_tlv = bytes.fromhex(parts[3])",
  "            got_tlv = strict_loads_tlv(rend_b)",
  "            if got_tlv != exp_tlv:",
  "                raise AssertionError(f'C_AST_MISMATCH[{ktag}]: rend={rend_b[:80]!r}')",
  "        elif op == 'D':",
  "            req_id = parts[1]",
  "            flags = int(parts[2])",
  "            tlv_b = bytes.fromhex(parts[3])",
  "            py_obj, end_p = decode_tlv_to_py(tlv_b, 0)",
  "            if end_p != len(tlv_b):",
  "                raise AssertionError('D_TLV_TRAILING_BYTES')",
  "            ens_ascii = bool(flags & 1)",
  "            s_keys = bool(flags & 2)",
  "            ind_sel = (flags >> 2) & 3",
  "            indent = None if ind_sel == 0 else (0 if ind_sel == 1 else (2 if ind_sel == 2 else 4))",
  "            seps = (',', ':') if (indent is None and (flags & 16)) else None",
  "            dumped = json.dumps(py_obj, ensure_ascii=ens_ascii, allow_nan=False, indent=indent, sort_keys=s_keys, separators=seps)",
  "            check_tlv = strict_loads_tlv(dumped.encode('utf-8'))",
  "            if check_tlv != tlv_b:",
  "                raise AssertionError(f'D_PY_SELF_MISMATCH: dumped={dumped[:80]!r}')",
  "            out_lines.append('D ' + req_id + ' ' + dumped.encode('utf-8').hex())",
  "        else:",
  "            raise AssertionError('unknown op ' + repr(op))",
  "    except Exception as exc:",
  "        msg = str(exc).replace('\\n', ' ').strip()",
  "        batch_err = msg if msg else type(exc).__name__"
]

private def encodeBatchPayload (batch : PyOracleBatch) : String := Id.run do
  let total := batch.parses.size + batch.renders.size + batch.dumps.size
  let mut lines : Array String := Array.mkEmpty (total + 1)
  for item in batch.parses do
    let okFlag := if item.expectedOk then "1" else "0"
    let tlvHex := if item.expectedOk then bytesToHex item.expectedCanonTlv else "-"
    let lblHex := bytesToHex item.label.toUTF8
    lines := lines.push s!"P {okFlag} {bytesToHex item.rawBytes} {tlvHex} {lblHex}"
  for item in batch.renders do
    lines := lines.push s!"C {item.kindTag} {bytesToHex item.rendered.toUTF8} {bytesToHex item.expectedCanonTlv}"
  for idx in [0 : batch.dumps.size] do
    let item := batch.dumps[idx]!
    lines := lines.push s!"D {idx} {item.modeFlags.toNat} {bytesToHex item.expectedCanonTlv}"
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

/-- Persistent Python 3 `json` differential oracle co-process handle. -/
structure PyOracleClient where
  /-- Spawned `python3` child process. -/
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  /-- Bounded captured `stderr` buffer drained asynchronously. -/
  stderrRef : IO.Ref String
  /-- Background task draining `child.stderr`. -/
  stderrTask : Task (Except IO.Error Unit)

/-- Spawn the persistent Python 3 `json.loads` / `json.dumps` oracle in isolated mode (`-I`). -/
def startPyOracleClient : IO PyOracleClient := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-I", "-B", "-u", "-c", pyJsonOracleScript]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stderrRef ← IO.mkRef ""
  let stderrTask ← IO.asTask (drainStderrLoop child.stderr stderrRef)
  return { child, stderrRef, stderrTask }

/-- Flush one episode's `PyOracleBatch` to Python and verify all `json.dumps` -> `LeanSwe.Json.parse` roundtrips. -/
def flushPyBatch (client : PyOracleClient) (batch : PyOracleBatch)
    (parseFn : String → Except JsonError Lean.Json) : IO (Except String Unit) := do
  if batch.isEmpty then
    return .ok ()
  let payload := encodeBatchPayload batch
  try
    client.child.stdin.putStr payload
    client.child.stdin.flush
  catch e =>
    let stderr ← client.stderrRef.get
    return .error s!"PYTHON_ORACLE_EOF: write failed ({e}); stderr={stderr.trimAscii.toString}"
  let mut dumpReplies : Array (Nat × String) := Array.mkEmpty batch.dumps.size
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
      if errMsg?.isNone then
        errMsg? := some s!"PYTHON_ORACLE_MISMATCH: {detail}"
      break
    else if line.startsWith "D " then
      match line.splitOn " " with
      | ["D", idStr, hexBody] =>
        match idStr.toNat?, hexToUtf8String hexBody with
        | some idx, .ok dumpedStr => dumpReplies := dumpReplies.push (idx, dumpedStr)
        | _, .error e => if errMsg?.isNone then errMsg? := some e
        | none, _ => if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_BAD_DUMP_ID: {idStr}"
      | _ =>
        if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_BAD_LINE: {line}"
    else
      if errMsg?.isNone then errMsg? := some s!"PYTHON_ORACLE_UNEXPECTED_LINE: {line}"
  if let some err := errMsg? then
    return .error err
  if dumpReplies.size != batch.dumps.size then
    return .error s!"PYTHON_ORACLE_DUMP_COUNT_MISMATCH: expected {batch.dumps.size}, got {dumpReplies.size}"
  for idx in [0 : dumpReplies.size] do
    let (echoIdx, dumpedStr) := dumpReplies[idx]!
    let req := batch.dumps[idx]!
    if echoIdx != idx then
      return .error s!"PYTHON_ORACLE_DUMP_ID_MISMATCH: got {echoIdx}, expected {idx}"
    match parseFn dumpedStr with
    | .error err =>
      return .error s!"PYTHON_DUMPS_PARSE_ERR: flags={req.modeFlags} err={repr err} dumped={repr (dumpedStr.take 80).toString}"
    | .ok parsed =>
      if !Model.wellFormedJsonBool parsed then
        return .error s!"PYTHON_DUMPS_NOT_WF: flags={req.modeFlags}"
      if encodeCanonJson parsed != req.expectedCanonTlv then
        return .error s!"PYTHON_DUMPS_AST_MISMATCH: flags={req.modeFlags} dumped={repr (dumpedStr.take 80).toString}"
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

end Fuzz.Json
