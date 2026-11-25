import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import LeanSwe.Json.Types
import LeanSwe.Json.Impl.Format

namespace LeanSwe.Json.Internal

/-- Check whether `b` is RFC 8259 whitespace (`' '`, `'\t'`, `'\n'`, `'\r'`). -/
def isWsByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

/-- Advance past RFC 8259 whitespace bytes in `bytes` starting at `pos`, returning bounded position. -/
def skipWsSub (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size) :
    { p : Nat // pos ≤ p ∧ p ≤ bytes.size } :=
  if h : pos < bytes.size then
    if isWsByte bytes[pos] then
      let ⟨p, _, hp2⟩ := skipWsSub bytes (pos + 1) h
      ⟨p, by omega, hp2⟩
    else ⟨pos, Nat.le_refl _, hPos⟩
  else ⟨pos, Nat.le_refl _, hPos⟩
termination_by bytes.size - pos

/-- Parse a single ASCII hexadecimal byte into `0..15`, or `none`. -/
def hexValByte? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else none

/-- Parse 4 consecutive ASCII hex bytes starting at `pos` into a 16-bit code unit. -/
def parseHex4? (bytes : ByteArray) (pos : Nat) : Option Nat :=
  if h : pos + 4 ≤ bytes.size then do
    let d0 ← hexValByte? bytes[pos]
    let d1 ← hexValByte? bytes[pos + 1]
    let d2 ← hexValByte? bytes[pos + 2]
    let d3 ← hexValByte? bytes[pos + 3]
    some (d0 * 4096 + d1 * 256 + d2 * 16 + d3)
  else none

/-- Append the UTF-8 encoding of `c` onto `acc`. -/
def pushUtf8Char (acc : ByteArray) (c : Char) : ByteArray :=
  let v := c.val
  if v ≤ 0x7f then
    acc.push v.toUInt8
  else if v ≤ 0x7ff then
    acc.push ((v >>> 6).toUInt8 &&& 0x1f ||| 0xc0)
      |>.push (v.toUInt8 &&& 0x3f ||| 0x80)
  else if v ≤ 0xffff then
    acc.push ((v >>> 12).toUInt8 &&& 0x0f ||| 0xe0)
      |>.push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)
      |>.push (v.toUInt8 &&& 0x3f ||| 0x80)
  else
    acc.push ((v >>> 18).toUInt8 &&& 0x07 ||| 0xf0)
      |>.push ((v >>> 12).toUInt8 &&& 0x3f ||| 0x80)
      |>.push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)
      |>.push (v.toUInt8 &&& 0x3f ||| 0x80)

/-- Tail-recursively parse the interior and closing `'"'` of a JSON string starting right after `'"'`. -/
def parseStringBody (bytes : ByteArray) (pos : Nat) (acc : ByteArray) :
    Except String (String × Nat) :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if b == 0x22 then
      match String.fromUTF8? acc with
      | some s => .ok (s, pos + 1)
      | none => .error "invalid UTF-8 sequence in string"
    else if b < 0x20 then .error "unescaped control character in string"
    else if b == 0x5c then
      if h1 : pos + 1 < bytes.size then
        let esc := bytes[pos + 1]
        let simple? : Option UInt8 :=
          if esc == 0x22 then some 0x22
          else if esc == 0x5c then some 0x5c
          else if esc == 0x2f then some 0x2f
          else if esc == 0x62 then some 0x08
          else if esc == 0x66 then some 0x0c
          else if esc == 0x6e then some 0x0a
          else if esc == 0x72 then some 0x0d
          else if esc == 0x74 then some 0x09
          else none
        match simple? with
        | some ch => parseStringBody bytes (pos + 2) (acc.push ch)
        | none =>
          if esc == 0x75 then
            match parseHex4? bytes (pos + 2) with
            | none => .error "invalid \\u escape sequence"
            | some u1 =>
              if 0xD800 ≤ u1 && u1 < 0xDC00 then
                let paired? : Option Nat :=
                  if hPair : pos + 12 ≤ bytes.size then
                    if bytes[pos + 6] == 0x5c && bytes[pos + 7] == 0x75 then
                      match parseHex4? bytes (pos + 8) with
                      | some u2 =>
                        if 0xDC00 ≤ u2 && u2 < 0xE000 then
                          some (0x10000 + (u1 - 0xD800) * 1024 + (u2 - 0xDC00))
                        else none
                      | none => none
                    else none
                  else none
                match paired? with
                | some cp => parseStringBody bytes (pos + 12) (pushUtf8Char acc (Char.ofNat cp))
                | none => .error "unpaired high UTF-16 surrogate in string"
              else if 0xDC00 ≤ u1 && u1 < 0xE000 then
                .error "lone low UTF-16 surrogate in string"
              else parseStringBody bytes (pos + 6) (pushUtf8Char acc (Char.ofNat u1))
          else .error "invalid escape sequence in string"
      else .error "unterminated escape sequence in string"
    else parseStringBody bytes (pos + 1) (acc.push b)
  else .error "unterminated string literal"
termination_by bytes.size - pos

/-- Parse a JSON string literal starting at `pos` (expecting `'"'`). -/
def parseStringAt (bytes : ByteArray) (pos : Nat) :
    Except String (String × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  if h : pos < bytes.size then
    if bytes[pos] == 0x22 then
      match parseStringBody bytes (pos + 1) ByteArray.empty with
      | .ok (s, p) =>
        if hp : pos < p ∧ p ≤ bytes.size then .ok (s, ⟨p, hp⟩)
        else .error "internal string parser bounds error"
      | .error e => .error e
    else .error "expected '\"' to start JSON string"
  else .error "unexpected end of input while expecting string"

/-- Decimal chunk base `10^18` fitting in a single unboxed 64-bit Lean scalar `Nat`. -/
def decChunkBase : Nat := 1000000000000000000

/-- Tail-recursively scan ASCII decimal digits using 18-digit chunking with early caps on digit count and value. -/
def scanDigitsLoop (bytes : ByteArray) (pos bigAcc chunkAcc chunkLen count limitCount : Nat)
    (hasValCap : Bool) (limitVal : Nat) : Nat × Nat × Nat :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if 0x30 ≤ b && b ≤ 0x39 then
      let count' := count + 1
      if count' > limitCount then (bigAcc * (10 ^ chunkLen) + chunkAcc, count', pos)
      else
        let d := b.toNat - 0x30
        let (bigAcc', chunkAcc', chunkLen') :=
          if chunkLen == 18 then (bigAcc * decChunkBase + chunkAcc, d, 1)
          else (bigAcc, chunkAcc * 10 + d, chunkLen + 1)
        let overVal :=
          if hasValCap then
            bigAcc' > limitVal ||
              (bigAcc' > 0 && bigAcc' * (10 ^ chunkLen') + chunkAcc' > limitVal) ||
              (bigAcc' == 0 && chunkAcc' > limitVal)
          else false
        if overVal then (bigAcc' * (10 ^ chunkLen') + chunkAcc', count', pos + 1)
        else scanDigitsLoop bytes (pos + 1) bigAcc' chunkAcc' chunkLen' count' limitCount hasValCap limitVal
    else (bigAcc * (10 ^ chunkLen) + chunkAcc, count, pos)
  else (bigAcc * (10 ^ chunkLen) + chunkAcc, count, pos)
termination_by bytes.size - pos

/-- Tail-recursively scan digits and wrap the final end position with its interval proof. -/
def scanDigits (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size)
    (initAcc initCount limitCount : Nat) (hasValCap : Bool) (limitVal : Nat) :
    Nat × Nat × { p : Nat // pos ≤ p ∧ p ≤ bytes.size } :=
  let (acc, count, p) := scanDigitsLoop bytes pos 0 initAcc (if initCount == 0 then 0 else 1)
    initCount limitCount hasValCap limitVal
  if hp : pos ≤ p ∧ p ≤ bytes.size then (acc, count, ⟨p, hp⟩)
  else (acc, count, ⟨pos, Nat.le_refl _, hPos⟩)

/-- Parse the integer part of a JSON number at `p0`, given `pos ≤ p0` and `p0 < bytes.size`. -/
def parseNumberWhole (bytes : ByteArray) (pos p0 : Nat) (hp0Ge : pos ≤ p0) (h1 : p0 < bytes.size) :
    Except String (Nat × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  let b0 := bytes[p0]
  if b0 == 0x30 then
    .ok (0, ⟨p0 + 1, by omega, by omega⟩)
  else if 0x31 ≤ b0 && b0 ≤ 0x39 then
    let (w, _, pSub) := scanDigits bytes (p0 + 1) h1 (b0.toNat - 0x30) 1 bytes.size false 0
    .ok (w, ⟨pSub.1, by have := pSub.2; omega, pSub.2.2⟩)
  else .error "expected digit in number"

/-- Parse the optional fractional part of a JSON number starting at `p1Sub`. -/
def parseNumberFrac (bytes : ByteArray) (pos : Nat) (sign : Int) (whole : Nat)
    (p1Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }) :
    Except String (Lean.JsonNumber × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  let p1 := p1Sub.1
  if hDot : p1 < bytes.size then
    if bytes[p1] == 0x2e then
      let (frac, d, pSub) := scanDigits bytes (p1 + 1) hDot 0 0 100_000 false 0
      if d == 0 then .error "expected digit after decimal point"
      else if d > 100_000 then .error "too many decimal digits"
      else .ok (Lean.JsonNumber.mk (sign * (whole * (10 ^ d) + frac)) d,
        ⟨pSub.1, by have := pSub.2; have := p1Sub.2; omega, pSub.2.2⟩)
    else .ok (Lean.JsonNumber.fromInt (sign * whole), p1Sub)
  else .ok (Lean.JsonNumber.fromInt (sign * whole), p1Sub)

/-- Parse the optional exponent part of a JSON number starting at `p2Sub`. -/
def parseNumberExp (bytes : ByteArray) (pos : Nat) (baseNum : Lean.JsonNumber)
    (p2Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }) :
    Except String (Lean.JsonNumber × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  let p2 := p2Sub.1
  if hExp : p2 < bytes.size then
    let be := bytes[p2]
    if be == 0x65 || be == 0x45 then
      let p3 := p2 + 1
      let (expNeg, p4Sub) : Bool × { p : Nat // p3 ≤ p ∧ p ≤ bytes.size } :=
        if hSign : p3 < bytes.size then
          if bytes[p3] == 0x2d then (true, ⟨p3 + 1, by omega, hSign⟩)
          else if bytes[p3] == 0x2b then (false, ⟨p3 + 1, by omega, hSign⟩)
          else (false, ⟨p3, Nat.le_refl _, Nat.le_of_lt hSign⟩)
        else (false, ⟨p3, Nat.le_refl _, hExp⟩)
      let (expVal, expDigits, pSub) :=
        scanDigits bytes p4Sub.1 p4Sub.2.2 0 0 bytes.size true 100_000
      if expDigits == 0 then .error "expected digit in exponent"
      else if expVal > 100_000 then .error "exponent too large"
      else
        let shifted := if expNeg then baseNum.shiftr expVal else baseNum.shiftl expVal
        .ok (shifted, ⟨pSub.1, by have := pSub.2; have := p4Sub.2; have := p2Sub.2; omega, pSub.2.2⟩)
    else .ok (baseNum, p2Sub)
  else .ok (baseNum, p2Sub)

/-- Parse an RFC 8259 JSON number starting at `pos` under symmetric `100_000` fractional/exponent limits. -/
def parseNumberAt (bytes : ByteArray) (pos : Nat) :
    Except String (Lean.JsonNumber × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  if h0 : pos < bytes.size then
    let neg := bytes[pos] == 0x2d
    let p0 := if neg then pos + 1 else pos
    have hp0Ge : pos ≤ p0 := by dsimp [p0]; split <;> omega
    let sign : Int := if neg then -1 else 1
    if h1 : p0 < bytes.size then
      match parseNumberWhole bytes pos p0 hp0Ge h1 with
      | .error e => .error e
      | .ok (whole, p1Sub) =>
        match parseNumberFrac bytes pos sign whole p1Sub with
        | .error e => .error e
        | .ok (baseNum, p2Sub) => parseNumberExp bytes pos baseNum p2Sub
    else .error "unexpected end of input in number"
  else .error "unexpected end of input in number"

/-- Check whether `bytes` matches the ASCII bytes of `kw` starting at `pos`. -/
def matchesKeyword (bytes : ByteArray) (pos : Nat) (kw : ByteArray) : Bool :=
  if h : pos + kw.size ≤ bytes.size then go 0 h else false
where
  go (i : Nat) (h : pos + kw.size ≤ bytes.size) : Bool :=
    if hi : i < kw.size then
      if bytes[pos + i]'(by omega) == kw[i] then go (i + 1) h else false
    else true
  termination_by kw.size - i

/-- Pre-encoded UTF-8 bytes of `"true"`. -/
def kwTrue : ByteArray := "true".toUTF8

/-- Pre-encoded UTF-8 bytes of `"false"`. -/
def kwFalse : ByteArray := "false".toUTF8

/-- Pre-encoded UTF-8 bytes of `"null"`. -/
def kwNull : ByteArray := "null".toUTF8

/-- Open container frame for the tail-recursive total JSON parser. -/
inductive ParseFrame where
  /-- Enclosing JSON array with accumulated elements. -/
  | arr (elems : Array Lean.Json)
  /-- Enclosing JSON object with accumulated entries and pending key. -/
  | obj (kvs : Std.TreeMap.Raw String Lean.Json compare) (key : String)

mutual
  /-- Parse the next JSON value starting at or after `pos`, then continue with `frames`. -/
  def parseWantValue (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size)
      (frames : List ParseFrame) : Except String Lean.Json :=
    let ⟨p, hpGe, hpLe⟩ := skipWsSub bytes pos hPos
    if hLt : p < bytes.size then
      let b := bytes[p]
      if b == 0x5b then
        let ⟨p1, hp1Ge, hp1Le⟩ := skipWsSub bytes (p + 1) hLt
        if hClose : p1 < bytes.size then
          if bytes[p1] == 0x5d then parseAfterValue bytes (p1 + 1) hClose frames (Lean.Json.arr #[])
          else parseWantValue bytes p1 hp1Le (.arr #[] :: frames)
        else .error "unclosed JSON array"
      else if b == 0x7b then
        let ⟨p1, hp1Ge, hp1Le⟩ := skipWsSub bytes (p + 1) hLt
        if hClose : p1 < bytes.size then
          if bytes[p1] == 0x7d then parseAfterValue bytes (p1 + 1) hClose frames (Lean.Json.obj ∅)
          else
            match parseStringAt bytes p1 with
            | .error e => .error e
            | .ok (k, ⟨p2, hp2a, hp2b⟩) =>
              let ⟨p3, hp3Ge, _⟩ := skipWsSub bytes p2 hp2b
              if hCol : p3 < bytes.size then
                if bytes[p3] == 0x3a then parseWantValue bytes (p3 + 1) hCol (.obj ∅ k :: frames)
                else .error "expected ':' after object key"
              else .error "expected ':' after object key"
        else .error "unclosed JSON object"
      else if b == 0x22 then
        match parseStringAt bytes p with
        | .error e => .error e
        | .ok (s, ⟨p1, hp1a, hp1b⟩) => parseAfterValue bytes p1 hp1b frames (Lean.Json.str s)
      else if b == 0x74 then
        if matchesKeyword bytes p kwTrue then
          if hEnd : p + 4 ≤ bytes.size then parseAfterValue bytes (p + 4) hEnd frames (Lean.Json.bool true)
          else .error "unexpected input"
        else .error "invalid literal starting with 't'"
      else if b == 0x66 then
        if matchesKeyword bytes p kwFalse then
          if hEnd : p + 5 ≤ bytes.size then parseAfterValue bytes (p + 5) hEnd frames (Lean.Json.bool false)
          else .error "unexpected input"
        else .error "invalid literal starting with 'f'"
      else if b == 0x6e then
        if matchesKeyword bytes p kwNull then
          if hEnd : p + 4 ≤ bytes.size then parseAfterValue bytes (p + 4) hEnd frames Lean.Json.null
          else .error "unexpected input"
        else .error "invalid literal starting with 'n'"
      else if b == 0x2d || (0x30 ≤ b && b ≤ 0x39) then
        match parseNumberAt bytes p with
        | .error e => .error e
        | .ok (n, ⟨p1, hp1a, hp1b⟩) => parseAfterValue bytes p1 hp1b frames (Lean.Json.num n)
      else .error "unexpected character in JSON value"
    else .error "unexpected end of JSON input"
  termination_by bytes.size - pos

  /-- Continue after completing `val`, checking enclosing array/object delimiters or EOF. -/
  def parseAfterValue (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size)
      (frames : List ParseFrame) (val : Lean.Json) : Except String Lean.Json :=
    let ⟨p, hpGe, _⟩ := skipWsSub bytes pos hPos
    match frames with
    | [] =>
      if p == bytes.size then .ok val
      else .error "unexpected trailing characters after JSON value"
    | .arr elems :: rest =>
      if hLt : p < bytes.size then
        let b := bytes[p]
        if b == 0x5d then parseAfterValue bytes (p + 1) hLt rest (Lean.Json.arr (elems.push val))
        else if b == 0x2c then parseWantValue bytes (p + 1) hLt (.arr (elems.push val) :: rest)
        else .error "expected ',' or ']' in array"
      else .error "unclosed JSON array"
    | .obj kvs key :: rest =>
      let kvs' := kvs.insert key val
      if hLt : p < bytes.size then
        let b := bytes[p]
        if b == 0x7d then parseAfterValue bytes (p + 1) hLt rest (Lean.Json.obj kvs')
        else if b == 0x2c then
          let ⟨p1, hp1Ge, _⟩ := skipWsSub bytes (p + 1) hLt
          match parseStringAt bytes p1 with
          | .error e => .error e
          | .ok (nextKey, ⟨p2, hp2a, hp2b⟩) =>
            if kvs'.contains nextKey then .error s!"duplicate object key {nextKey.quote}"
            else
              let ⟨p3, hp3Ge, _⟩ := skipWsSub bytes p2 hp2b
              if hCol : p3 < bytes.size then
                if bytes[p3] == 0x3a then parseWantValue bytes (p3 + 1) hCol (.obj kvs' nextKey :: rest)
                else .error "expected ':' after object key"
              else .error "expected ':' after object key"
        else .error "expected ',' or '}' in object"
      else .error "unclosed JSON object"
  termination_by bytes.size - pos
end

/-- Pure total RFC 8259 JSON parser returning an `Except String Lean.Json`. -/
def parsePure (raw : String) : Except String Lean.Json :=
  parseWantValue raw.toUTF8 0 (Nat.zero_le _) []

/-- Parse a JSON text string into `Lean.Json`. -/
def parse (raw : String) : Except JsonError Lean.Json :=
  match parsePure raw with
  | .ok j => .ok j
  | .error msg => .error { kind := .parseError, message := ensureNonEmpty "JSON parse error" msg, path := none }

/-- Render a `Lean.Json` value as compact single-line JSON. -/
def compress (j : Lean.Json) : String :=
  compactDocLoop "" [renderFormat j]

/-- Render a `Lean.Json` value as formatted JSON targeting `lineWidth` columns. -/
def pretty (j : Lean.Json) (lineWidth : Nat := 80) : String :=
  formatDocLoop lineWidth 0 "" [⟨false, 0, renderFormat j⟩]

/-- Decode a `Lean.Json` value using its `Lean.FromJson` instance. -/
def decode {α : Type} [Lean.FromJson α] (j : Lean.Json) : Except JsonError α :=
  match Lean.fromJson? j with
  | .ok a => .ok a
  | .error msg => .error { kind := .decodeError, message := ensureNonEmpty "JSON decode error" msg, path := none }

/-- Encode a value into `Lean.Json` using its `Lean.ToJson` instance. -/
def encode {α : Type} [Lean.ToJson α] (a : α) : Lean.Json :=
  Lean.toJson a

/-- Extract the key-value map from a JSON object, failing with `.typeMismatch` on non-objects. -/
def getObject (j : Lean.Json) : Except JsonError (Std.TreeMap.Raw String Lean.Json compare) :=
  match j with
  | .obj kvs => .ok kvs
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Extract the element array from a JSON array, failing with `.typeMismatch` on non-arrays. -/
def getArray (j : Lean.Json) : Except JsonError (Array Lean.Json) :=
  match j with
  | .arr xs => .ok xs
  | _ => .error { kind := .typeMismatch, message := "expected JSON array", path := none }

/-- Look up required field `key` on a JSON object and decode it as `α`. -/
def getField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) : Except JsonError α :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | some v =>
      match decode v with
      | .ok a => .ok a
      | .error e => .error { e with path := some key }
    | none => .error { kind := .missingField, message := s!"missing field: {key}", path := some key }
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Look up optional field `key` on a JSON object, returning `none` when absent or `null`. -/
def getOptField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) :
    Except JsonError (Option α) :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | none => .ok none
    | some .null => .ok none
    | some v =>
      match decode v with
      | .ok a => .ok (some a)
      | .error e => .error { e with path := some key }
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Traverse `keys` accumulating `revPrefix` and decode the leaf JSON value. -/
def getPathAux {α : Type} [Lean.FromJson α]
    (revPrefix : List String) (j : Lean.Json) : List String → Except JsonError α
  | [] =>
    match decode j with
    | .ok a => .ok a
    | .error e => if revPrefix.isEmpty then .error e else .error { e with path := joinPath revPrefix }
  | key :: rest =>
    match j with
    | .obj kvs =>
      let nextPrefix := key :: revPrefix
      match kvs.get? key with
      | some v => getPathAux nextPrefix v rest
      | none => .error { kind := .missingField, message := s!"missing field: {key}", path := joinPath nextPrefix }
    | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := joinPath revPrefix }

/-- Traverse a list of object keys and decode the leaf JSON value as `α`. -/
def getPath {α : Type} [Lean.FromJson α] (j : Lean.Json) (keys : List String) : Except JsonError α :=
  getPathAux [] j keys

/-- Concrete `JsonApi` record bundling the pure `LeanSwe.Json` operations. -/
def defaultApi : JsonApi :=
  { parse := parse
    compress := compress
    pretty := fun j w => pretty j w
    decode := decode
    encode := encode
    getObject := getObject
    getArray := getArray
    getField := getField
    getOptField := getOptField
    getPath := getPath }

end LeanSwe.Json.Internal
