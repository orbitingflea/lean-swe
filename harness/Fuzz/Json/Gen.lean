import Fuzz.Common.Rng
import LeanSwe.Json.Interface
import LeanSwe.Json.Model

namespace Fuzz.Json

open Fuzz.Common
open LeanSwe.Json

/-- One differential fuzz case for `Fuzz.Json.suite`. -/
inductive JsonFuzzCase where
  /-- Valid RFC 8259 JSON rendered from `(doc, tape)` via `Model.render`, plus `pretty` width and `json.dumps` flags. -/
  | validRender (doc : Lean.Json) (raw : String) (prettyWidth : Nat) (dumpsFlags : UInt8) (tags : List String)
  /-- Arbitrary or syntactically/semantically malformed UTF-8 JSON string candidate. -/
  | malformedStr (raw : String) (tag : String)
  /-- Raw `ByteArray` containing invalid UTF-8 sequences or byte-corrupted JSON payloads. -/
  | invalidUtf8 (rawBytes : ByteArray) (tag : String)
  /-- Combined `encode`/`decode`/`getObject`/`getArray`/`getField`/`getOptField`/`getPath` differential check. -/
  | codecAndAccessors (doc : Lean.Json) (primBool : Bool) (primNat : Nat) (primInt : Int)
      (primStr : String) (optVal : Option Int) (arrVals : Array String)
      (key1 key2 : String) (pathKeys : List String)
  deriving BEq, Inhabited

private def truncPreview (s : String) (lim : Nat := 48) : String :=
  let cs := s.toList
  if cs.length ≤ lim then reprStr s
  else reprStr (String.ofList (cs.take lim) ++ "...")

/-- Concise human-readable formatting for shrunk `JsonFuzzCase` counterexamples. -/
def reprJsonFuzzCase : JsonFuzzCase → String
  | .validRender doc raw pw df tags =>
    s!"validRender(doc={truncPreview (LeanSwe.Json.compress doc)}, raw={truncPreview raw}, pw={pw}, df={df}, tags={reprStr tags})"
  | .malformedStr raw tag =>
    s!"malformedStr(tag={reprStr tag}, raw={truncPreview raw})"
  | .invalidUtf8 bs tag =>
    s!"invalidUtf8(tag={reprStr tag}, len={bs.size})"
  | .codecAndAccessors doc b n i s opt xs k1 k2 pks =>
    s!"codecAndAccessors(doc={truncPreview (LeanSwe.Json.compress doc)}, b={b}, n={n}, i={i}, s={truncPreview s}, opt={reprStr opt}, xs={reprStr xs}, k1={reprStr k1}, k2={reprStr k2}, path={reprStr pks})"

instance : Repr JsonFuzzCase where
  reprPrec c _ := reprJsonFuzzCase c

private def genWs (r : Rng) (maxLen : Nat := 4) : String × Rng := Id.run do
  let (useWs, r0) := r.chance 2 5
  if !useWs then
    return ("", r0)
  let (len, r1) := r0.nextRange 1 maxLen
  let mut cur := r1
  let mut cs : List Char := []
  let wsChars : Array Char := #[' ', '\t', '\n', '\r']
  for _ in [0 : len] do
    let (ch, rn) := cur.choose wsChars ' '
    cur := rn
    cs := ch :: cs
  return (String.ofList cs.reverse, cur)

private def genHexCase4 (r : Rng) : Model.HexCase4 × Rng :=
  let (b0, r1) := r.nextBool
  let (b1, r2) := r1.nextBool
  let (b2, r3) := r2.nextBool
  let (b3, r4) := r3.nextBool
  ({ u0 := b0, u1 := b1, u2 := b2, u3 := b3 }, r4)

private def genValidChar (r : Rng) : Char × Rng :=
  let (bucketPick, r1) := r.nextNat 10
  if bucketPick < 4 then
    let (code, r2) := r1.nextRange 0x20 0x7e
    (Char.ofNat code, r2)
  else if bucketPick < 6 then
    let specials : Array Char := #['"', '\\', '/', '\x08', '\x0c', '\n', '\r', '\t', '\x00', '\x01', '\x1f', '\x7f']
    r1.choose specials 'a'
  else if bucketPick < 8 then
    let bmpPool : Array Nat := #[0x00a9, 0x00e9, 0x03b1, 0x03a9, 0x0416, 0x20ac, 0x2603, 0x4e2d, 0x65e5, 0xfeff, 0xfffd]
    let (cp, r2) := r1.choose bmpPool 0x03b1
    (Char.ofNat cp, r2)
  else
    let astralPool : Array Nat := #[0x10000, 0x10348, 0x1d11e, 0x1f600, 0x1f680, 0x1f980, 0x10ffff]
    let (cp, r2) := r1.choose astralPool 0x1f680
    (Char.ofNat cp, r2)

private def genStyleForChar (c : Char) (r : Rng) : Model.CharEscapeStyle × List String × Rng :=
  let code := c.toNat
  if code ≥ 0x10000 then
    let (asPair, r1) := r.nextBool
    if asPair then
      let (hc, r2) := genHexCase4 r1
      let (lc, r3) := genHexCase4 r2
      (.surrogatePair hc lc, ["surrogate_pair", "str_unicode"], r3)
    else
      (.raw, ["str_unicode"], r1)
  else if c == '"' || c == '\\' then
    let (asShort, r1) := r.chance 3 4
    if asShort then (.shortEscape, ["short_escape"], r1)
    else
      let (hc, r2) := genHexCase4 r1
      (.unicodeHex hc, ["unicode_hex"], r2)
  else if c == '\x08' || c == '\x0c' || c == '\n' || c == '\r' || c == '\t' then
    let (asShort, r1) := r.chance 3 4
    if asShort then (.shortEscape, ["short_escape"], r1)
    else
      let (hc, r2) := genHexCase4 r1
      (.unicodeHex hc, ["unicode_hex"], r2)
  else if c == '/' then
    let (sel, r1) := r.nextNat 3
    if sel == 0 then (.raw, [], r1)
    else if sel == 1 then (.shortEscape, ["short_escape"], r1)
    else
      let (hc, r2) := genHexCase4 r1
      (.unicodeHex hc, ["unicode_hex"], r2)
  else if code < 0x20 then
    let (hc, r1) := genHexCase4 r
    (.unicodeHex hc, ["unicode_hex"], r1)
  else
    let (asHex, r1) := r.chance 1 5
    let uniTag := if code ≥ 0x80 then ["str_unicode"] else []
    if asHex then
      let (hc, r2) := genHexCase4 r1
      (.unicodeHex hc, "unicode_hex" :: uniTag, r2)
    else
      (.raw, uniTag, r1)

/-- Generate a UTF-8 `String` paired with valid RFC 8259 per-character `CharEscapeStyle` instructions. -/
def genStyledString (r : Rng) (maxLen : Nat := 12) :
    String × List Model.CharEscapeStyle × List String × Rng := Id.run do
  let (len, r0) := r.nextRange 0 maxLen
  let mut cur := r0
  let mut chars : List Char := []
  let mut styles : List Model.CharEscapeStyle := []
  let mut tags : List String := []
  for _ in [0 : len] do
    let (c, r1) := genValidChar cur
    let (st, tgs, r2) := genStyleForChar c r1
    cur := r2
    chars := c :: chars
    styles := st :: styles
    tags := tgs ++ tags
  let s := String.ofList chars.reverse
  let baseTag := if s.toList.all (fun c => c.toNat < 0x80) then ["str_ascii"] else ["str_unicode"]
  return (s, styles.reverse, baseTag ++ tags, cur)

private def genDigitsStr (r : Rng) (minLen maxLen : Nat) : String × Rng := Id.run do
  let (len, r0) := r.nextRange minLen maxLen
  let mut cur := r0
  let mut cs : List Char := []
  for _ in [0 : len] do
    let (d, rn) := cur.nextRange 0 9
    cur := rn
    cs := Char.ofNat ('0'.toNat + d) :: cs
  return (String.ofList cs.reverse, cur)

private def genNumTapeWithinLimits (r : Rng) : Model.NumTape × List String × Rng := Id.run do
  let (kind, r0) := r.nextNat 12
  if kind == 0 then
    let (hasFrac, r1) := r0.nextBool
    let frac? := if hasFrac then some "00" else none
    return ({ minus := true, whole := 0, fracDigits := frac?, exp := none }, ["num_neg_zero"], r1)
  else if kind < 4 then
    let (minus, r1) := r0.nextBool
    let (whole, r2) := r1.nextRange 0 1000000
    return ({ minus, whole, fracDigits := none, exp := none }, ["num_int"], r2)
  else if kind == 4 then
    let (minus, r1) := r0.nextBool
    let (hi, r2) := r1.nextRange 1 999999999999999
    let (lo, r3) := r2.nextRange 0 999999999999999
    let bigWhole := hi * 100000000000000000000 + lo
    return ({ minus, whole := bigWhole, fracDigits := none, exp := none }, ["num_big", "num_int"], r3)
  else if kind < 8 then
    let (minus, r1) := r0.nextBool
    let (whole, r2) := r1.nextRange 0 5000
    let (frac, r3) := genDigitsStr r2 1 16
    return ({ minus, whole, fracDigits := some frac, exp := none }, ["num_frac"], r3)
  else if kind < 11 then
    let (minus, r1) := r0.nextBool
    let (whole, r2) := r1.nextRange 0 999
    let (hasFrac, r3) := r2.nextBool
    let (frac?, r4) :=
      if hasFrac then
        let (f, rf) := genDigitsStr r3 1 8
        (some f, rf)
      else (none, r3)
    let (upperE, r5) := r4.nextBool
    let (sgn, r6) := r5.choose #[Model.ExpSign.none, .plus, .minus] .none
    let (leadZeros, r7) := r6.nextRange 0 3
    let (expVal, r8) := r7.nextRange 0 400
    let digits := String.ofList (List.replicate leadZeros '0') ++ expVal.repr
    let extra := if expVal > 310 then ["num_big"] else []
    return ({ minus, whole, fracDigits := frac?, exp := some { upperE, sign := sgn, digits } },
      "num_exp" :: extra, r8)
  else
    let (minus, r1) := r0.nextBool
    let (upperE, r2) := r1.nextBool
    let (isNegExp, r3) := r2.nextBool
    if isNegExp then
      return ({ minus, whole := 1, fracDigits := some "25", exp := some { upperE, sign := .minus, digits := "100000" } },
        ["num_exp", "limit_boundary"], r3)
    else
      return ({ minus, whole := 0, fracDigits := none, exp := some { upperE, sign := .plus, digits := "00100000" } },
        ["num_exp", "limit_boundary"], r3)

private def shuffleArray {α : Type} [Inhabited α] (xs : Array α) (r : Rng) : Array α × Rng := Id.run do
  let mut arr := xs
  let mut cur := r
  if arr.size ≤ 1 then
    return (arr, cur)
  for idx in [0 : arr.size - 1] do
    let (j, rn) := cur.nextRange idx (arr.size - 1)
    cur := rn
    if idx != j then
      let tmp := arr[idx]!
      arr := arr.set! idx arr[j]!
      arr := arr.set! j tmp
  return (arr, cur)

/-- Generate a well-formed `Lean.Json` document jointly with a valid `Model.RenderTape` within resource limits. -/
partial def genJsonAndTape (depth : Nat) (r : Rng) :
    Lean.Json × Model.RenderTape × List String × Rng := Id.run do
  let (wb, r1) := genWs r 3
  let (wa, r2) := genWs r1 3
  let wsTag := if !wb.isEmpty || !wa.isEmpty then ["whitespace"] else []
  let maxChoice := if depth == 0 then 4 else 6
  let (kind, r3) := r2.nextNat maxChoice
  if kind == 0 then
    return (.null, .null wb wa, "null" :: wsTag, r3)
  else if kind == 1 then
    let (b, r4) := r3.nextBool
    let bTag := if b then "bool_true" else "bool_false"
    return (.bool b, .bool wb wa, bTag :: wsTag, r4)
  else if kind == 2 then
    let (nt, nTags, r4) := genNumTapeWithinLimits r3
    let numVal := Model.evalNumTape nt
    return (.num numVal, .num wb nt wa, nTags ++ wsTag, r4)
  else if kind == 3 then
    let (s, styles, sTags, r4) := genStyledString r3 10
    return (.str s, .str wb styles wa, sTags ++ wsTag, r4)
  else if kind == 4 then
    let (cnt, r4) := r3.nextRange 0 4
    if cnt == 0 then
      let (wi, r5) := genWs r4 3
      let wt := if !wi.isEmpty then ["whitespace"] else wsTag
      return (.arr #[], .emptyArr wb wi wa, "arr_empty" :: wt, r5)
    else
      let mut cur := r4
      let mut elems : Array Lean.Json := Array.mkEmpty cnt
      let mut tapes : List Model.RenderTape := []
      let mut tags : List String := "arr_nonempty" :: wsTag
      for _ in [0 : cnt] do
        let (ej, et, etags, rn) := genJsonAndTape (depth - 1) cur
        cur := rn
        elems := elems.push ej
        tapes := et :: tapes
        tags := etags ++ tags
      return (.arr elems, .arr wb tapes.reverse wa, tags, cur)
  else
    let (cnt, r4) := r3.nextRange 0 4
    if cnt == 0 then
      let (wi, r5) := genWs r4 3
      let wt := if !wi.isEmpty then ["whitespace"] else wsTag
      return (.obj ∅, .emptyObj wb wi wa, "obj_empty" :: wt, r5)
    else
      let mut cur := r4
      let mut rawTriples : Array (String × Lean.Json × Model.RenderTape) := Array.mkEmpty cnt
      let mut usedKeys : List String := []
      let mut tags : List String := "obj_nonempty" :: wsTag
      for idx in [0 : cnt] do
        let (k0, _, kTags, rk1) := genStyledString cur 6
        let k := if usedKeys.contains k0 then s!"{k0}_{idx}" else k0
        let (vj, vTape, vTags, rk2) := genJsonAndTape (depth - 1) rk1
        cur := rk2
        usedKeys := k :: usedKeys
        rawTriples := rawTriples.push (k, vj, vTape)
        tags := kTags ++ vTags ++ tags
      let docObj := Lean.Json.mkObj (rawTriples.toList.map fun (k, v, _) => (k, v))
      let (permArr, r5) := shuffleArray rawTriples cur
      let mut cur2 := r5
      let mut entryTapes : List (Model.ObjKeyTape × Model.RenderTape) := []
      for (k, _, vTape) in permArr do
        let (wbk, ra) := genWs cur2 2
        let (wbc, rb) := genWs ra 2
        let mut curK := rb
        let mut kStyles : List Model.CharEscapeStyle := []
        for ch in k.toList do
          let (st, stTags, rc) := genStyleForChar ch curK
          curK := rc
          kStyles := st :: kStyles
          tags := stTags ++ tags
        cur2 := curK
        if !wbk.isEmpty || !wbc.isEmpty then
          tags := "whitespace" :: tags
        entryTapes := ({ wsBeforeKey := wbk, key := k, keyChars := kStyles.reverse, wsBeforeColon := wbc }, vTape) :: entryTapes
      let objTape : Model.RenderTape := .obj wb entryTapes.reverse wa
      match Model.render docObj objTape with
      | some _ => return (docObj, objTape, tags, cur2)
      | none =>
        return (.obj ∅, .emptyObj wb "" wa, "obj_empty" :: wsTag, cur2)

/-- Construct a randomized `Model.RenderTape` witnessing an existing well-formed `Lean.Json` value. -/
partial def buildCanonicalTape (j : Lean.Json) (r : Rng) :
    Model.RenderTape × List String × Rng := Id.run do
  let (wb, r1) := genWs r 2
  let (wa, r2) := genWs r1 2
  let wsTag := if !wb.isEmpty || !wa.isEmpty then ["whitespace"] else []
  match j with
  | .null => return (.null wb wa, "null" :: wsTag, r2)
  | .bool b => return (.bool wb wa, (if b then "bool_true" else "bool_false") :: wsTag, r2)
  | .num n =>
    let nt : Model.NumTape :=
      if n.mantissa == 0 then { minus := false, whole := 0 }
      else
        let mAbs := n.mantissa.natAbs
        if n.exponent == 0 then { minus := n.mantissa < 0, whole := mAbs }
        else if n.exponent ≤ Model.maxAbsExponent then
          { minus := n.mantissa < 0, whole := mAbs, exp := some { sign := .minus, digits := n.exponent.repr } }
        else
          let extra := n.exponent - Model.maxAbsExponent
          let base10 := 10 ^ extra
          let wPart := mAbs / base10
          let remDigits := (mAbs % base10).repr.toList
          let padFrac := String.ofList (List.replicate (extra - remDigits.length) '0' ++ remDigits)
          { minus := n.mantissa < 0
            whole := wPart
            fracDigits := some padFrac
            exp := some { sign := .minus, digits := Model.maxAbsExponent.repr } }
    return (.num wb nt wa, "num_int" :: wsTag, r2)
  | .str s =>
    let mut cur := r2
    let mut styles : List Model.CharEscapeStyle := []
    let mut tags : List String := wsTag
    for ch in s.toList do
      let (st, tgs, rn) := genStyleForChar ch cur
      cur := rn
      styles := st :: styles
      tags := tgs ++ tags
    return (.str wb styles.reverse wa, tags, cur)
  | .arr elems =>
    if elems.isEmpty then
      let (wi, r3) := genWs r2 2
      return (.emptyArr wb wi wa, "arr_empty" :: wsTag, r3)
    else
      let mut cur := r2
      let mut ts : List Model.RenderTape := []
      let mut tags : List String := "arr_nonempty" :: wsTag
      for el in elems do
        let (et, etags, rn) := buildCanonicalTape el cur
        cur := rn
        ts := et :: ts
        tags := etags ++ tags
      return (.arr wb ts.reverse wa, tags, cur)
  | .obj kvs =>
    let entries := Model.objEntries kvs
    if entries.isEmpty then
      let (wi, r3) := genWs r2 2
      return (.emptyObj wb wi wa, "obj_empty" :: wsTag, r3)
    else
      let (perm, r3) := shuffleArray entries.toArray r2
      let mut cur := r3
      let mut es : List (Model.ObjKeyTape × Model.RenderTape) := []
      let mut tags : List String := "obj_nonempty" :: wsTag
      for (k, v) in perm do
        let (wbk, ra) := genWs cur 2
        let (wbc, rb) := genWs ra 2
        let mut ck := rb
        let mut ks : List Model.CharEscapeStyle := []
        for ch in k.toList do
          let (st, stTags, rc) := genStyleForChar ch ck
          ck := rc
          ks := st :: ks
          tags := stTags ++ tags
        let (vt, vtags, rd) := buildCanonicalTape v ck
        cur := rd
        if !wbk.isEmpty || !wbc.isEmpty then
          tags := "whitespace" :: tags
        tags := vtags ++ tags
        es := ({ wsBeforeKey := wbk, key := k, keyChars := ks.reverse, wsBeforeColon := wbc }, vt) :: es
      return (.obj wb es.reverse wa, tags, cur)

/-- Generate a well-formed `Lean.Json` AST up to `depth` container levels. -/
partial def genAstOnly (depth : Nat) (r : Rng) : Lean.Json × Rng := Id.run do
  let maxChoice := if depth == 0 then 4 else 6
  let (kind, r1) := r.nextNat maxChoice
  if kind == 0 then
    return (.null, r1)
  else if kind == 1 then
    let (b, r2) := r1.nextBool
    return (.bool b, r2)
  else if kind == 2 then
    let (nt, _, r2) := genNumTapeWithinLimits r1
    return (.num (Model.evalNumTape nt), r2)
  else if kind == 3 then
    let (s, _, _, r2) := genStyledString r1 10
    return (.str s, r2)
  else if kind == 4 then
    let (cnt, r2) := r1.nextRange 0 4
    let mut cur := r2
    let mut xs : Array Lean.Json := Array.mkEmpty cnt
    for _ in [0 : cnt] do
      let (el, rn) := genAstOnly (depth - 1) cur
      cur := rn
      xs := xs.push el
    return (.arr xs, cur)
  else
    let (cnt, r2) := r1.nextRange 0 4
    let mut cur := r2
    let mut kvs : List (String × Lean.Json) := []
    let mut seen : List String := []
    for idx in [0 : cnt] do
      let (k0, _, _, rk) := genStyledString cur 6
      let k := if seen.contains k0 then s!"{k0}_{idx}" else k0
      let (v, rv) := genAstOnly (depth - 1) rk
      cur := rv
      seen := k :: seen
      kvs := (k, v) :: kvs
    return (Lean.Json.mkObj kvs, cur)

/-- Generate a deeply nested (`20..56` levels) JSON container case to exercise stack-safe tail recursion. -/
def genDeepNestedCase (r : Rng) : JsonFuzzCase × Rng := Id.run do
  let (depth, r1) := r.nextRange 20 56
  let (leafStr, _, _, r2) := genStyledString r1 6
  let mut doc : Lean.Json := Lean.Json.mkObj [("leaf", .str leafStr)]
  let mut cur := r2
  for idx in [0 : depth] do
    let (asObj, rn) := cur.nextBool
    cur := rn
    if asObj then
      doc := Lean.Json.mkObj [(s!"d{idx}", doc)]
    else
      doc := .arr #[doc, .num (Lean.JsonNumber.fromInt (Int.ofNat idx))]
  let (pw, r3) := cur.choose #[0, 12, 40, 80] 40
  let (df, r4) := r3.nextU8
  let raw := LeanSwe.Json.compress doc
  return (.validRender doc raw pw df ["deep_nested", "obj_nonempty", "arr_nonempty"], r4)

end Fuzz.Json
