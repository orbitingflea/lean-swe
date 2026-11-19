import Lean.Data.Format
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import LeanSwe.Json.Types

namespace LeanSwe.Json.Internal

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def ensureNonEmpty (fallback msg : String) : String :=
  if msg == "" then fallback else msg

/-- Tail-recursive helper joining path segments with `"."`. -/
def joinSegmentsAux (acc : String) : List String → String
  | [] => acc
  | k :: rest => joinSegmentsAux (acc ++ "." ++ k) rest

/-- Join path segments with `"."`. -/
def joinSegments : List String → String
  | [] => ""
  | k :: rest => joinSegmentsAux k rest

/-- Format a reversed path prefix as an optional dot-separated field path. -/
def joinPath (revPrefix : List String) : Option String :=
  if revPrefix.isEmpty then none else some (joinSegments revPrefix.reverse)

/-- Tail-recursive helper counting base-10 digits of a natural number. -/
def countDigitsAux (n digits : Nat) : Nat :=
  if h : n ≤ 9 then
    digits
  else
    have : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
    countDigitsAux (n / 10) (digits + 1)
termination_by n

/-- Count base-10 digits of `n` (`countDigits 0 = 1`). -/
def countDigits (n : Nat) : Nat :=
  countDigitsAux n 1

/-- Scan backwards past trailing `'0'` ASCII bytes in `s`. -/
def stripTrailingZerosEnd (s : String) (pos : Nat) (hPos : pos ≤ s.utf8ByteSize) : Nat :=
  match pos with
  | 0 => 0
  | p + 1 =>
    have hp : p < s.utf8ByteSize := by omega
    if s.getUTF8Byte ⟨p⟩ hp == 0x30 then
      stripTrailingZerosEnd s p (by omega)
    else
      p + 1

/-- Extract the ASCII prefix of `s` up to `len` bytes. -/
def takeAsciiPrefix (s : String) (len : Nat) : String :=
  (String.fromUTF8? (s.toUTF8.extract 0 len)).getD ""

/-- Tail-recursive helper appending `n` `'0'` bytes to `acc`. -/
def pushZeroBytes (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => pushZeroBytes (acc.push 0x30) n

/-- Format `k` fractional decimal digits of `rem < 10^k` with trailing `'0'`s stripped in near-linear time. -/
def formatFracStr (k rem : Nat) : String :=
  let s := rem.repr
  let sBytes := s.toUTF8
  let trimmedEnd := stripTrailingZerosEnd s s.utf8ByteSize (Nat.le_refl _)
  if trimmedEnd == 0 then
    ""
  else if sBytes.size < k then
    let pad := k - sBytes.size
    let buf := pushZeroBytes (ByteArray.emptyWithCapacity (pad + trimmedEnd)) pad
    let buf := sBytes.copySlice 0 buf pad trimmedEnd
    (String.fromUTF8? buf).getD ""
  else
    takeAsciiPrefix s trimmedEnd

/-- Format a `Lean.JsonNumber` as an RFC 8259 number string using total arithmetic. -/
def jsonNumberToString : Lean.JsonNumber → String
  | ⟨0, _⟩ => "0"
  | ⟨m, 0⟩ => m.repr
  | ⟨m, e⟩ =>
    let sign := if m ≥ 0 then "" else "-"
    let mAbs := m.natAbs
    let exp : Int := 9 + countDigits mAbs - (e : Int)
    let exp := if exp < 0 then exp else 0
    let k := e - exp.natAbs
    let e' := 10 ^ k
    let left := (mAbs / e').repr
    let rem := mAbs % e'
    if rem == 0 && exp == 0 then
      s!"{sign}{left}"
    else
      let right := formatFracStr k rem
      let expStr := if exp == 0 then "" else "e" ++ exp.repr
      s!"{sign}{left}.{right}{expStr}"

/-- Escape a single character according to JSON string escaping rules. -/
def escapeChar (acc : String) (c : Char) : String :=
  if c == '"' then
    acc ++ "\\\""
  else if c == '\\' then
    acc ++ "\\\\"
  else if c == '\n' then
    acc ++ "\\n"
  else if c == '\r' then
    acc ++ "\\r"
  else if 0x0020 ≤ c.val && c.val ≤ 0x10ffff then
    acc.push c
  else
    let n := c.toNat
    let d1 := Nat.digitChar (n / 4096)
    let d2 := Nat.digitChar ((n % 4096) / 256)
    let d3 := Nat.digitChar ((n % 256) / 16)
    let d4 := Nat.digitChar (n % 16)
    ((((acc ++ "\\u").push d1).push d2).push d3).push d4

/-- Scan UTF-8 bytes from `i` to check whether any character in `s` requires JSON escaping. -/
def needEscapeAux (s : String) (i : Nat) : Bool :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if b < 0x20 || b == 0x22 || b == 0x5c then
      true
    else
      needEscapeAux s (i + 1)
  else
    false
termination_by s.utf8ByteSize - i

/-- Escape `s` for JSON string output, appending onto `acc`. -/
def escapeString (s : String) (acc : String := "") : String :=
  if needEscapeAux s 0 then
    s.foldl escapeChar acc
  else
    acc ++ s

/-- Render `s` as a quoted JSON string literal, appending onto `acc`. -/
def renderString (s : String) (acc : String := "") : String :=
  escapeString s (acc ++ "\"") ++ "\""

mutual
  /-- Structural weight of a `Lean.Json` value for total serialization. -/
  def jsonWeight : Lean.Json → Nat
    | .null | .bool _ | .num _ | .str _ => 2
    | .arr elems => 2 + arrWeight elems.toList
    | .obj kvs => 3 + treeWeight kvs.inner.inner
  termination_by j => sizeOf j
  decreasing_by
    · cases elems; simp; omega
    · cases kvs with | mk inner => cases inner; simp; omega

  /-- Structural weight of a JSON array element list. -/
  def arrWeight : List Lean.Json → Nat
    | [] => 0
    | x :: xs => jsonWeight x + 1 + arrWeight xs
  termination_by xs => sizeOf xs

  /-- Structural weight of a `Std.DTreeMap` internal tree of JSON values. -/
  def treeWeight : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → Nat
    | .leaf => 0
    | .inner _ _ v l r => treeWeight l + (jsonWeight v + 5) + treeWeight r
  termination_by t => sizeOf t
end

/-- Worklist task for tail-recursive total JSON compression. -/
inductive CompressTask where
  /-- Serialize a JSON value. -/
  | val (j : Lean.Json)
  /-- Emit literal syntax text. -/
  | text (s : String)
  /-- Emit a `"key":` prefix and serialize `v`. -/
  | field (k : String) (v : Lean.Json)
  /-- Emit remaining array elements and closing `"]"`. -/
  | arrTail (elems : List Lean.Json)
  /-- Emit tree entries in ascending key order, inserting `","` if `needComma` is true. -/
  | treeIn (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) (needComma : Bool)

/-- Termination weight of a single compression task. -/
def taskWeight : CompressTask → Nat
  | .val j => jsonWeight j
  | .text _ => 1
  | .field _ v => jsonWeight v + 1
  | .arrTail xs => arrWeight xs + 1
  | .treeIn t _ => treeWeight t + 1

/-- Total termination weight of a compression task worklist. -/
def tasksWeight : List CompressTask → Nat
  | [] => 0
  | t :: ts => taskWeight t + tasksWeight ts

/-- Tail-recursive total JSON compression loop. -/
def compressLoop (acc : String) : (tasks : List CompressTask) → String
  | [] => acc
  | .text s :: rest => compressLoop (acc ++ s) rest
  | .field k v :: rest => compressLoop (renderString k acc ++ ":") (.val v :: rest)
  | .arrTail [] :: rest => compressLoop (acc ++ "]") rest
  | .arrTail (x :: xs) :: rest =>
    compressLoop (acc ++ ",") (.val x :: .arrTail xs :: rest)
  | .treeIn .leaf _ :: rest => compressLoop acc rest
  | .treeIn (.inner _ k v l r) needComma :: rest =>
    let commaBeforeV := needComma || match l with | .leaf => false | .inner _ _ _ _ _ => true
    let next0 := match r with
      | .leaf => rest
      | .inner _ _ _ _ _ => .treeIn r true :: rest
    let next1 := .field k v :: next0
    let next2 := if commaBeforeV then .text "," :: next1 else next1
    let next3 := match l with
      | .leaf => next2
      | .inner _ _ _ _ _ => .treeIn l needComma :: next2
    compressLoop acc next3
  | .val j :: rest =>
    match j with
    | .null => compressLoop (acc ++ "null") rest
    | .bool true => compressLoop (acc ++ "true") rest
    | .bool false => compressLoop (acc ++ "false") rest
    | .num n => compressLoop (acc ++ jsonNumberToString n) rest
    | .str s => compressLoop (renderString s acc) rest
    | .arr elems =>
      match heq : elems.toList with
      | [] =>
        have : 0 < jsonWeight (.arr elems) := by simp [jsonWeight]; omega
        compressLoop (acc ++ "[]") rest
      | x :: xs =>
        have hDec : tasksWeight (.val x :: .arrTail xs :: rest) <
            tasksWeight (.val (.arr elems) :: rest) := by
          simp only [tasksWeight, taskWeight, jsonWeight]
          rw [heq]
          simp [arrWeight]
          omega
        compressLoop (acc ++ "[") (.val x :: .arrTail xs :: rest)
    | .obj kvs =>
      match heq : kvs.inner.inner with
      | .leaf =>
        have : 0 < jsonWeight (.obj kvs) := by simp [jsonWeight]; omega
        compressLoop (acc ++ "{}") rest
      | t =>
        have hDec : tasksWeight (.treeIn t false :: .text "}" :: rest) <
            tasksWeight (.val (.obj kvs) :: rest) := by
          simp only [tasksWeight, taskWeight, jsonWeight]
          rw [heq]
          omega
        compressLoop (acc ++ "{") (.treeIn t false :: .text "}" :: rest)
termination_by tasks => tasksWeight tasks
decreasing_by
  all_goals simp_wf
  · simp [tasksWeight, taskWeight]
  · simp [tasksWeight, taskWeight]
  · simp [tasksWeight, taskWeight]
  · simp only [tasksWeight, taskWeight, arrWeight]
    omega
  · simp [tasksWeight, taskWeight]
  · cases needComma <;> cases l <;> cases r <;>
      simp [tasksWeight, taskWeight, treeWeight] <;> omega
  · simp [tasksWeight, taskWeight, jsonWeight]
  · simp [tasksWeight, taskWeight, jsonWeight]
  · simp [tasksWeight, taskWeight, jsonWeight]
  · simp [tasksWeight, taskWeight, jsonWeight]
  · simp [tasksWeight, taskWeight, jsonWeight]
  · simp [tasksWeight, taskWeight, jsonWeight]; omega
  · exact hDec
  · simp [tasksWeight, taskWeight, jsonWeight]; omega
  · exact hDec

/-- Worklist item for iterative in-order traversal of JSON object trees during pretty-printing. -/
inductive ObjWalkItem where
  /-- Traverse subtree `t` in-order. -/
  | tree (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json))
  /-- Format object entry `(k, v)`. -/
  | emitKv (k : String) (v : Lean.Json)

/-- Termination weight of one object walk item. -/
def objWalkWeight : ObjWalkItem → Nat
  | .tree t => treeWeight t + 1
  | .emitKv _ v => jsonWeight v + 3

/-- Total termination weight of pending object walk items. -/
def pendingWeight : List ObjWalkItem → Nat
  | [] => 0
  | w :: ws => objWalkWeight w + pendingWeight ws

/-- Continuation frame for tail-recursive total JSON `Std.Format` construction. -/
inductive PrettyFrame where
  /-- Waiting for the current array element, with reversed prior formats and remaining elements. -/
  | arr (accRev : List Std.Format) (remaining : List Lean.Json)
  /-- Waiting for the value format of key `k`, with accumulated object field formats and pending walk items. -/
  | objKv (k : String) (acc : List Std.Format) (pending : List ObjWalkItem)

/-- Termination weight of one pretty-printing frame. -/
def prettyFrameWeight : PrettyFrame → Nat
  | .arr _ rem => arrWeight rem + 1
  | .objKv _ _ pending => pendingWeight pending + 2

/-- Total termination weight of a pretty-printing continuation stack. -/
def prettyFramesWeight : List PrettyFrame → Nat
  | [] => 0
  | f :: fs => prettyFrameWeight f + prettyFramesWeight fs

/-- Tail-recursively join a non-empty reversed list of `Std.Format` values with `sep`. -/
def joinSepRevAux (sep acc : Std.Format) : List Std.Format → Std.Format
  | [] => acc
  | x :: xs => joinSepRevAux sep (x ++ sep ++ acc) xs

mutual
  /-- Tail-recursively render `j` into `Std.Format` using an explicit frame stack. -/
  def renderEval (j : Lean.Json) (frames : List PrettyFrame) : Std.Format :=
    match j with
    | .null => renderApply "null" frames
    | .bool true => renderApply "true" frames
    | .bool false => renderApply "false" frames
    | .num n => renderApply (jsonNumberToString n) frames
    | .str s => renderApply (renderString s) frames
    | .arr elems =>
      match heq : elems.toList with
      | [] =>
        have : 0 < jsonWeight (.arr elems) := by simp [jsonWeight]; omega
        renderApply (Std.Format.bracket "[" .nil "]") frames
      | x :: xs =>
        have hDec : jsonWeight x + prettyFramesWeight (.arr [] xs :: frames) <
            jsonWeight (.arr elems) + prettyFramesWeight frames := by
          simp only [jsonWeight, prettyFramesWeight, prettyFrameWeight]
          rw [heq]
          simp [arrWeight]
          omega
        renderEval x (.arr [] xs :: frames)
    | .obj kvs =>
      match heq : kvs.inner.inner with
      | .leaf =>
        have : 0 < jsonWeight (.obj kvs) := by simp [jsonWeight]; omega
        renderApply (Std.Format.bracket "{" .nil "}") frames
      | t =>
        have hDec : 1 + pendingWeight [.tree t] + prettyFramesWeight frames <
            jsonWeight (.obj kvs) + prettyFramesWeight frames := by
          simp only [jsonWeight, pendingWeight, objWalkWeight]
          rw [heq]
          omega
        renderObjNext [] [.tree t] frames
  termination_by jsonWeight j + prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]; omega
    · exact hDec
    · simp [jsonWeight]; omega
    · omega

  /-- Tail-recursively advance through `pending` object tree walk items. -/
  def renderObjNext (acc : List Std.Format) (pending : List ObjWalkItem)
      (frames : List PrettyFrame) : Std.Format :=
    match pending with
    | [] =>
      let body := match acc.reverse with
        | [] => .nil
        | last :: restRev => joinSepRevAux ("," ++ Std.Format.line) last restRev
      renderApply (Std.Format.bracket "{" body "}") frames
    | .tree .leaf :: rest => renderObjNext acc rest frames
    | .tree (.inner _ k v l r) :: rest =>
      let next0 := match r with
        | .leaf => rest
        | .inner _ _ _ _ _ => .tree r :: rest
      let next1 := .emitKv k v :: next0
      let next2 := match l with
        | .leaf => next1
        | .inner _ _ _ _ _ => .tree l :: next1
      renderObjNext acc next2 frames
    | .emitKv k v :: rest =>
      renderEval v (.objKv k acc rest :: frames)
  termination_by 1 + pendingWeight pending + prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · omega
    · simp [pendingWeight, objWalkWeight]
    · cases l <;> cases r <;>
        simp [pendingWeight, objWalkWeight, treeWeight] <;> omega
    · simp [pendingWeight, objWalkWeight, prettyFramesWeight, prettyFrameWeight]
      omega

  /-- Tail-recursively feed a completed `Std.Format` value into the enclosing continuation frame. -/
  def renderApply (valFmt : Std.Format) (frames : List PrettyFrame) : Std.Format :=
    match frames with
    | [] => valFmt
    | .arr accRev [] :: rest =>
      let body := joinSepRevAux ("," ++ Std.Format.line) valFmt accRev
      renderApply (Std.Format.bracket "[" body "]") rest
    | .arr accRev (x :: xs) :: rest =>
      renderEval x (.arr (valFmt :: accRev) xs :: rest)
    | .objKv k acc pending :: rest =>
      let kvFmt := Std.Format.group (renderString k ++ ":" ++ Std.Format.line ++ valFmt)
      renderObjNext (kvFmt :: acc) pending rest
  termination_by prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · simp [prettyFramesWeight, prettyFrameWeight]
    · simp only [prettyFramesWeight, prettyFrameWeight, arrWeight]
      omega
    · simp [prettyFramesWeight, prettyFrameWeight]
      omega
end

/-- Render a `Lean.Json` value into a `Std.Format` document iteratively without recursion. -/
def renderFormat (j : Lean.Json) : Std.Format :=
  renderEval j []

/-- Check whether `b` is RFC 8259 whitespace (`' '`, `'\t'`, `'\n'`, `'\r'`). -/
def isWsByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

/-- Advance past RFC 8259 whitespace bytes in `bytes` starting at `pos`, returning bounded position. -/
def skipWsSub (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size) :
    { p : Nat // pos ≤ p ∧ p ≤ bytes.size } :=
  if h : pos < bytes.size then
    if isWsByte bytes[pos] then
      let ⟨p, hp1, hp2⟩ := skipWsSub bytes (pos + 1) h
      ⟨p, by omega, hp2⟩
    else
      ⟨pos, Nat.le_refl _, hPos⟩
  else
    ⟨pos, Nat.le_refl _, hPos⟩
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
    some ((d0 <<< 12) ||| (d1 <<< 8) ||| (d2 <<< 4) ||| d3)
  else
    none

/-- Append the UTF-8 encoding of Unicode scalar value `cp` onto `acc`. -/
def pushUtf8Cp (acc : ByteArray) (cp : Nat) : ByteArray :=
  if cp < 0x80 then
    acc.push cp.toUInt8
  else if cp < 0x800 then
    acc.push (0xC0 ||| (cp >>> 6)).toUInt8
      |>.push (0x80 ||| (cp &&& 0x3F)).toUInt8
  else if cp < 0x10000 then
    acc.push (0xE0 ||| (cp >>> 12)).toUInt8
      |>.push (0x80 ||| ((cp >>> 6) &&& 0x3F)).toUInt8
      |>.push (0x80 ||| (cp &&& 0x3F)).toUInt8
  else
    acc.push (0xF0 ||| (cp >>> 18)).toUInt8
      |>.push (0x80 ||| ((cp >>> 12) &&& 0x3F)).toUInt8
      |>.push (0x80 ||| ((cp >>> 6) &&& 0x3F)).toUInt8
      |>.push (0x80 ||| (cp &&& 0x3F)).toUInt8

/-- Tail-recursively parse the interior and closing `'"'` of a JSON string starting right after `'"'`. -/
def parseStringBody (bytes : ByteArray) (pos : Nat) (acc : ByteArray) :
    Except String (String × Nat) :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if b == 0x22 then
      match String.fromUTF8? acc with
      | some s => .ok (s, pos + 1)
      | none => .error "invalid UTF-8 sequence in string"
    else if b < 0x20 then
      .error "unescaped control character in string"
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
                          some (0x10000 + (((u1 - 0xD800) <<< 10) ||| (u2 - 0xDC00)))
                        else
                          none
                      | none => none
                    else
                      none
                  else
                    none
                match paired? with
                | some cp => parseStringBody bytes (pos + 12) (pushUtf8Cp acc cp)
                | none => parseStringBody bytes (pos + 6) (pushUtf8Cp acc 0xFFFD)
              else if 0xDC00 ≤ u1 && u1 < 0xE000 then
                parseStringBody bytes (pos + 6) (pushUtf8Cp acc 0xFFFD)
              else
                parseStringBody bytes (pos + 6) (pushUtf8Cp acc u1)
          else
            .error "invalid escape sequence in string"
      else
        .error "unterminated escape sequence in string"
    else
      parseStringBody bytes (pos + 1) (acc.push b)
  else
    .error "unterminated string literal"
termination_by bytes.size - pos

/-- Parse a JSON string literal starting at `pos` (expecting `'"'`). -/
def parseStringAt (bytes : ByteArray) (pos : Nat) :
    Except String (String × { p : Nat // pos < p ∧ p ≤ bytes.size }) :=
  if h : pos < bytes.size then
    if bytes[pos] == 0x22 then
      match parseStringBody bytes (pos + 1) ByteArray.empty with
      | .ok (s, p) =>
        if hp : pos < p ∧ p ≤ bytes.size then
          .ok (s, ⟨p, hp⟩)
        else
          .error "internal string parser bounds error"
      | .error e => .error e
    else
      .error "expected '\"' to start JSON string"
  else
    .error "unexpected end of input while expecting string"

/-- Decimal chunk base `10^18` fitting in a single unboxed 64-bit Lean scalar `Nat`. -/
private def decChunkBase : Nat := 1000000000000000000

/-- Tail-recursively scan ASCII decimal digits using 18-digit chunking with early caps on digit count and optional value cap. -/
def scanDigitsLoop (bytes : ByteArray) (pos bigAcc chunkAcc chunkLen count limitCount : Nat)
    (hasValCap : Bool) (limitVal : Nat) : Nat × Nat × Nat :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if 0x30 ≤ b && b ≤ 0x39 then
      let count' := count + 1
      if count' > limitCount then
        (bigAcc * (10 ^ chunkLen) + chunkAcc, count', pos)
      else
        let d := b.toNat - 0x30
        let (bigAcc', chunkAcc', chunkLen') :=
          if chunkLen == 18 then
            (bigAcc * decChunkBase + chunkAcc, d, 1)
          else
            (bigAcc, chunkAcc * 10 + d, chunkLen + 1)
        let overVal :=
          if hasValCap then
            bigAcc' > limitVal ||
              (bigAcc' > 0 && bigAcc' * (10 ^ chunkLen') + chunkAcc' > limitVal) ||
              (bigAcc' == 0 && chunkAcc' > limitVal)
          else
            false
        if overVal then
          (bigAcc' * (10 ^ chunkLen') + chunkAcc', count', pos + 1)
        else
          scanDigitsLoop bytes (pos + 1) bigAcc' chunkAcc' chunkLen' count' limitCount hasValCap limitVal
    else
      (bigAcc * (10 ^ chunkLen) + chunkAcc, count, pos)
  else
    (bigAcc * (10 ^ chunkLen) + chunkAcc, count, pos)
termination_by bytes.size - pos

/-- Tail-recursively scan digits and wrap the final end position with its interval proof. -/
def scanDigits (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size)
    (initAcc initCount limitCount : Nat) (hasValCap : Bool) (limitVal : Nat) :
    Nat × Nat × { p : Nat // pos ≤ p ∧ p ≤ bytes.size } :=
  let (acc, count, p) := scanDigitsLoop bytes pos 0 initAcc (if initCount == 0 then 0 else 1)
    initCount limitCount hasValCap limitVal
  if hp : pos ≤ p ∧ p ≤ bytes.size then
    (acc, count, ⟨p, hp⟩)
  else
    (acc, count, ⟨pos, Nat.le_refl _, hPos⟩)

/-- Parse an RFC 8259 JSON number starting at `pos`. -/
def parseNumberAt (bytes : ByteArray) (pos : Nat) :
    Except String (Lean.JsonNumber × { p : Nat // pos < p ∧ p ≤ bytes.size }) := do
  if h0 : pos < bytes.size then
    let neg := bytes[pos] == 0x2d
    let p0 := if neg then pos + 1 else pos
    have hp0Ge : pos ≤ p0 := by dsimp [p0]; split <;> omega
    let sign : Int := if neg then -1 else 1
    if h1 : p0 < bytes.size then
      let b0 := bytes[p0]
      let res1 ←
        if b0 == 0x30 then
          Except.ok (0, (⟨p0 + 1, by omega, by omega⟩ : { p : Nat // pos < p ∧ p ≤ bytes.size }))
        else if 0x31 ≤ b0 && b0 ≤ 0x39 then
          let (w, _, pSub) := scanDigits bytes (p0 + 1) h1 (b0.toNat - 0x30) 1 bytes.size false 0
          Except.ok (w, (⟨pSub.1, by have := pSub.2; omega, pSub.2.2⟩ :
            { p : Nat // pos < p ∧ p ≤ bytes.size }))
        else
          Except.error "expected digit in number"
      let whole := res1.1
      let p1 := res1.2.1
      have hp1a : pos < p1 := res1.2.2.1
      have hp1b : p1 ≤ bytes.size := res1.2.2.2
      let res2 ←
        if hDot : p1 < bytes.size then
          if bytes[p1] == 0x2e then
            let (frac, d, pSub) := scanDigits bytes (p1 + 1) hDot 0 0 100_000 false 0
            if d == 0 then
              Except.error "expected digit after decimal point"
            else if d > 100_000 then
              Except.error "too many decimal digits"
            else
              Except.ok (Lean.JsonNumber.mk (sign * (whole * (10 ^ d) + frac)) d,
                (⟨pSub.1, by have := pSub.2; omega, pSub.2.2⟩ :
                  { p : Nat // pos < p ∧ p ≤ bytes.size }))
          else
            Except.ok (Lean.JsonNumber.fromInt (sign * whole),
              (⟨p1, hp1a, hp1b⟩ : { p : Nat // pos < p ∧ p ≤ bytes.size }))
        else
          Except.ok (Lean.JsonNumber.fromInt (sign * whole),
            (⟨p1, hp1a, hp1b⟩ : { p : Nat // pos < p ∧ p ≤ bytes.size }))
      let baseNum := res2.1
      let p2 := res2.2.1
      have hp2a : pos < p2 := res2.2.2.1
      have hp2b : p2 ≤ bytes.size := res2.2.2.2
      if hExp : p2 < bytes.size then
        let be := bytes[p2]
        if be == 0x65 || be == 0x45 then
          let p3 := p2 + 1
          let (expNeg, p4Sub) : Bool × { p : Nat // p3 ≤ p ∧ p ≤ bytes.size } :=
            if hSign : p3 < bytes.size then
              if bytes[p3] == 0x2d then (true, ⟨p3 + 1, by omega, hSign⟩)
              else if bytes[p3] == 0x2b then (false, ⟨p3 + 1, by omega, hSign⟩)
              else (false, ⟨p3, Nat.le_refl _, Nat.le_of_lt hSign⟩)
            else
              (false, ⟨p3, Nat.le_refl _, hExp⟩)
          let countCap := if expNeg then 100_000 else bytes.size
          let (expVal, expDigits, pSub) :=
            scanDigits bytes p4Sub.1 p4Sub.2.2 0 0 countCap (!expNeg) 100_000
          if expDigits == 0 then
            Except.error "expected digit in exponent"
          else if expNeg then
            if expDigits > 100_000 then
              Except.error "exponent too large"
            else
              Except.ok (baseNum.shiftr expVal, ⟨pSub.1, by have := pSub.2; have := p4Sub.2; omega, pSub.2.2⟩)
          else if expVal > 100_000 then
            Except.error "exponent too large"
          else
            Except.ok (baseNum.shiftl expVal, ⟨pSub.1, by have := pSub.2; have := p4Sub.2; omega, pSub.2.2⟩)
        else
          Except.ok (baseNum, ⟨p2, hp2a, hp2b⟩)
      else
        Except.ok (baseNum, ⟨p2, hp2a, hp2b⟩)
    else
      Except.error "unexpected end of input in number"
  else
    Except.error "unexpected end of input in number"

/-- Check whether `bytes` matches the ASCII bytes of `kw` starting at `pos`. -/
def matchesKeyword (bytes : ByteArray) (pos : Nat) (kw : ByteArray) : Bool :=
  if h : pos + kw.size ≤ bytes.size then
    go 0 h
  else
    false
where
  go (i : Nat) (h : pos + kw.size ≤ bytes.size) : Bool :=
    if hi : i < kw.size then
      if bytes[pos + i]'(by omega) == kw[i] then
        go (i + 1) h
      else
        false
    else
      true
  termination_by kw.size - i

private def kwTrue : ByteArray := "true".toUTF8
private def kwFalse : ByteArray := "false".toUTF8
private def kwNull : ByteArray := "null".toUTF8

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
          if bytes[p1] == 0x5d then
            parseAfterValue bytes (p1 + 1) hClose frames (Lean.Json.arr #[])
          else
            parseWantValue bytes p1 hp1Le (.arr #[] :: frames)
        else
          .error "unclosed JSON array"
      else if b == 0x7b then
        let ⟨p1, hp1Ge, hp1Le⟩ := skipWsSub bytes (p + 1) hLt
        if hClose : p1 < bytes.size then
          if bytes[p1] == 0x7d then
            parseAfterValue bytes (p1 + 1) hClose frames (Lean.Json.obj ∅)
          else
            match parseStringAt bytes p1 with
            | .error e => .error e
            | .ok (k, ⟨p2, hp2a, hp2b⟩) =>
              let ⟨p3, hp3Ge, _⟩ := skipWsSub bytes p2 hp2b
              if hCol : p3 < bytes.size then
                if bytes[p3] == 0x3a then
                  parseWantValue bytes (p3 + 1) hCol (.obj ∅ k :: frames)
                else
                  .error "expected ':' after object key"
              else
                .error "expected ':' after object key"
        else
          .error "unclosed JSON object"
      else if b == 0x22 then
        match parseStringAt bytes p with
        | .error e => .error e
        | .ok (s, ⟨p1, hp1a, hp1b⟩) =>
          parseAfterValue bytes p1 hp1b frames (Lean.Json.str s)
      else if b == 0x74 then
        if matchesKeyword bytes p kwTrue then
          if hEnd : p + 4 ≤ bytes.size then
            parseAfterValue bytes (p + 4) hEnd frames (Lean.Json.bool true)
          else
            .error "unexpected input"
        else
          .error "invalid literal starting with 't'"
      else if b == 0x66 then
        if matchesKeyword bytes p kwFalse then
          if hEnd : p + 5 ≤ bytes.size then
            parseAfterValue bytes (p + 5) hEnd frames (Lean.Json.bool false)
          else
            .error "unexpected input"
        else
          .error "invalid literal starting with 'f'"
      else if b == 0x6e then
        if matchesKeyword bytes p kwNull then
          if hEnd : p + 4 ≤ bytes.size then
            parseAfterValue bytes (p + 4) hEnd frames Lean.Json.null
          else
            .error "unexpected input"
        else
          .error "invalid literal starting with 'n'"
      else if b == 0x2d || (0x30 ≤ b && b ≤ 0x39) then
        match parseNumberAt bytes p with
        | .error e => .error e
        | .ok (n, ⟨p1, hp1a, hp1b⟩) =>
          parseAfterValue bytes p1 hp1b frames (Lean.Json.num n)
      else
        .error "unexpected character in JSON value"
    else
      .error "unexpected end of JSON input"
  termination_by bytes.size - pos

  /-- Continue after completing `val`, checking enclosing array/object delimiters or EOF. -/
  def parseAfterValue (bytes : ByteArray) (pos : Nat) (hPos : pos ≤ bytes.size)
      (frames : List ParseFrame) (val : Lean.Json) : Except String Lean.Json :=
    let ⟨p, hpGe, _⟩ := skipWsSub bytes pos hPos
    match frames with
    | [] =>
      if p == bytes.size then
        .ok val
      else
        .error "unexpected trailing characters after JSON value"
    | .arr elems :: rest =>
      if hLt : p < bytes.size then
        let b := bytes[p]
        if b == 0x5d then
          parseAfterValue bytes (p + 1) hLt rest (Lean.Json.arr (elems.push val))
        else if b == 0x2c then
          parseWantValue bytes (p + 1) hLt (.arr (elems.push val) :: rest)
        else
          .error "expected ',' or ']' in array"
      else
        .error "unclosed JSON array"
    | .obj kvs key :: rest =>
      let kvs' := kvs.insert key val
      if hLt : p < bytes.size then
        let b := bytes[p]
        if b == 0x7d then
          parseAfterValue bytes (p + 1) hLt rest (Lean.Json.obj kvs')
        else if b == 0x2c then
          let ⟨p1, hp1Ge, _⟩ := skipWsSub bytes (p + 1) hLt
          match parseStringAt bytes p1 with
          | .error e => .error e
          | .ok (nextKey, ⟨p2, hp2a, hp2b⟩) =>
            if kvs'.contains nextKey then
              .error s!"duplicate object key {nextKey.quote}"
            else
              let ⟨p3, hp3Ge, _⟩ := skipWsSub bytes p2 hp2b
              if hCol : p3 < bytes.size then
                if bytes[p3] == 0x3a then
                  parseWantValue bytes (p3 + 1) hCol (.obj kvs' nextKey :: rest)
                else
                  .error "expected ':' after object key"
              else
                .error "expected ':' after object key"
        else
          .error "expected ',' or '}' in object"
      else
        .error "unclosed JSON object"
  termination_by bytes.size - pos
end

/-- Pure total RFC 8259 JSON parser returning an `Except String Lean.Json`. -/
def parsePure (raw : String) : Except String Lean.Json :=
  let bytes := raw.toUTF8
  parseWantValue bytes 0 (Nat.zero_le _) []

/-- Parse a JSON text string into `Lean.Json`. -/
def parse (raw : String) : Except JsonError Lean.Json :=
  match parsePure raw with
  | .ok j => .ok j
  | .error msg =>
    .error { kind := .parseError, message := ensureNonEmpty "JSON parse error" msg, path := none }

/-- Render a `Lean.Json` value as compact single-line JSON. -/
def compress (j : Lean.Json) : String :=
  compressLoop "" [.val j]

/-- Render a `Lean.Json` value as formatted JSON targeting `lineWidth` columns. -/
def pretty (j : Lean.Json) (lineWidth : Nat := 80) : String :=
  Std.Format.pretty (renderFormat j) lineWidth

/-- Decode a `Lean.Json` value using its `Lean.FromJson` instance. -/
def decode {α : Type} [Lean.FromJson α] (j : Lean.Json) : Except JsonError α :=
  match Lean.fromJson? j with
  | .ok a => .ok a
  | .error msg =>
    .error { kind := .decodeError, message := ensureNonEmpty "JSON decode error" msg, path := none }

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
    | .error e =>
      if revPrefix.isEmpty then .error e
      else .error { e with path := joinPath revPrefix }
  | key :: rest =>
    match j with
    | .obj kvs =>
      let nextPrefix := key :: revPrefix
      match kvs.get? key with
      | some v => getPathAux nextPrefix v rest
      | none =>
        .error { kind := .missingField, message := s!"missing field: {key}", path := joinPath nextPrefix }
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
