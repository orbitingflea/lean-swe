import Fuzz.Common.Rng
import Fuzz.Toml.GenScalar
import LeanSwe.Toml.Interface
import LeanSweProofs.Toml.Model

namespace Fuzz.Toml

open Fuzz.Common
open LeanSwe.Toml

private def genArrayElemsLoop
    (genElem : Rng → TomlValue × Model.ValueTape × List String × Rng) :
    Nat → List TomlValue → List (String × Model.ValueTape × String) → Bool → List String → Rng →
      List TomlValue × List (String × Model.ValueTape × String) × Bool × List String × Rng
  | 0, valsRev, elemsRev, nested, tags, r =>
    (valsRev.reverse, elemsRev.reverse, nested, tags, r)
  | rem + 1, valsRev, elemsRev, nested, tags, r =>
    let (pre, pt, ra) := genClosedTrivia r
    let (v, vt, vtags, rb) := genElem ra
    let (post, pot, rc) := genClosedTrivia rb
    let nested' := match v with | .array _ => true | _ => nested
    genArrayElemsLoop genElem rem (v :: valsRev) ((pre, vt, post) :: elemsRev)
      nested' (pt ++ vtags ++ pot ++ tags) rc

private def genInlineAssignsLoop
    (genElem : Rng → TomlValue × Model.ValueTape × List String × Rng) :
    Nat → Nat → List String → List (String × TomlValue) →
    List (String × Model.DottedKeyTape × String × String × Model.ValueTape × String) →
    List String → Rng →
      List (String × TomlValue) ×
      List (String × Model.DottedKeyTape × String × String × Model.ValueTape × String) ×
      List String × Rng
  | 0, _, _, entriesRev, assignsRev, tags, r =>
    (entriesRev.reverse, assignsRev.reverse, tags, r)
  | rem + 1, idx, seen, entriesRev, assignsRev, tags, r =>
    let (k0, kst0, kTags, ra) := genKeyAndStyle r
    let (k, kst, ktFinal) :=
      if seen.contains k0 then (s!"k{idx}", Model.KeyStyle.bare, ["key_bare"])
      else (k0, kst0, kTags)
    let (useDot, rb) := ra.chance 1 4
    let (wPre, rc) := genHorizWs rb 1
    let (wEqL, rd) := genHorizWs rc 1
    let (wEqR, re) := genHorizWs rd 1
    let (wPost, rf) := genHorizWs re 1
    let (v, vt, vTags, rg) := genElem rf
    let seen' := k :: seen
    if useDot then
      let (subK, subSt, subTags, rh) := genKeyAndStyle rg
      let dk : Model.DottedKeyTape := {
        firstKey := k, firstStyle := kst,
        rest := [{ key := subK, style := subSt }]
      }
      genInlineAssignsLoop genElem rem (idx + 1) seen'
        ((k, .table #[(subK, v)]) :: entriesRev)
        ((wPre, dk, wEqL, wEqR, vt, wPost) :: assignsRev)
        ("key_dotted" :: (ktFinal ++ subTags ++ vTags ++ tags)) rh
    else
      let dk : Model.DottedKeyTape := { firstKey := k, firstStyle := kst }
      genInlineAssignsLoop genElem rem (idx + 1) seen'
        ((k, v) :: entriesRev)
        ((wPre, dk, wEqL, wEqR, vt, wPost) :: assignsRev)
        (ktFinal ++ vTags ++ tags) rg

private def genScalarValueAndTape (allowYearZero : Bool) (r : Rng) :
    TomlValue × Model.ValueTape × List String × Rng :=
  let (pick, r1) := r.nextNat 5
  if pick == 0 then
    let (s, st, tgs, r2) := genStringAndStyle r1
    (.string s, .string st, tgs, r2)
  else if pick == 1 then
    let (n, vt, tgs, r2) := genIntAndTape r1
    (.int n, vt, tgs, r2)
  else if pick == 2 then
    let (f, vt, tgs, r2) := genFloatAndTape r1
    (.float f, vt, tgs, r2)
  else if pick == 3 then
    let (b, r2) := r1.nextBool
    (.bool b, .bool, [if b then "bool_true" else "bool_false"], r2)
  else
    genDateTimeAndTape allowYearZero r1

/-- Generate an inline `TomlValue` paired with a `Model.ValueTape` bounded by container `depth`. -/
def genInlineValueAndTape (allowYearZero : Bool) :
    Nat → Rng → TomlValue × Model.ValueTape × List String × Rng
  | 0, r => genScalarValueAndTape allowYearZero r
  | depth + 1, r =>
    let (pick, r1) := r.nextNat 8
    if pick < 6 then
      genScalarValueAndTape allowYearZero r1
    else if pick == 6 then
      let (cnt, r2) := r1.nextRange 0 3
      if cnt == 0 then
        let (trv, tTags, r3) := genClosedTrivia r2
        (.array #[], .array [] (some trv), "array_empty" :: tTags, r3)
      else
        let (vals, elems, isNested, tags, r3) :=
          genArrayElemsLoop (genInlineValueAndTape allowYearZero depth) cnt [] [] false [] r2
        let (hasTrail, r4) := r3.nextBool
        let (trail?, trTags, r5) :=
          if hasTrail then
            let (trv, tt, rn) := genClosedTrivia r4
            (some trv, "array_nested_trailing" :: tt, rn)
          else
            (none, if isNested then ["array_nested_trailing"] else [], r4)
        (.array vals.toArray, .array elems trail?, trTags ++ tags, r5)
    else
      let (cnt, r2) := r1.nextRange 0 3
      if cnt == 0 then
        let (ws, r3) := genHorizWs r2 2
        (.table #[], .inlineTable [] ws, ["inline_table_empty"], r3)
      else
        let (entries, assigns, tags, r3) :=
          genInlineAssignsLoop (genInlineValueAndTape allowYearZero depth)
            cnt 0 [] [] [] ["inline_table_nonempty"] r2
        (.table entries.toArray, .inlineTable assigns "", tags, r3)

/-- Generate a well-formed `TomlTable` jointly with a rendered TOML 1.0 document and exact tags. -/
def genTableAndTape (allowYearZero : Bool) (depth : Nat) (r : Rng) :
    TomlTable × String × List String × Rng := Id.run do
  let (inlineCnt, r1) := r.nextRange 0 3
  let (secCnt, r2) := r1.nextRange 0 2
  let mut cur := r2
  let mut rootEntries : Array (String × TomlValue) := #[]
  let mut inlineStmts : List Model.StmtTape := []
  let mut secStmts : List Model.StmtTape := []
  let mut seen : List String := []
  let mut tags : List String := []
  for idx in [0 : inlineCnt] do
    let (k0, kst0, kt0, ra) := genKeyAndStyle cur
    let (k, kst, kt) :=
      if seen.contains k0 then (s!"f_{idx}", Model.KeyStyle.bare, ["key_bare"]) else (k0, kst0, kt0)
    seen := k :: seen
    let (pre, pTags, rb) := genClosedTrivia ra
    let (wL, rc) := genHorizWs rb 2
    let (wR, rd) := genHorizWs rc 2
    let (suf, sTags, re) := genLineSuffix rd
    let (useDotted, rf) := re.chance 1 3
    if useDotted then
      let (subK, subSt, subKt, rg) := genKeyAndStyle rf
      let (v, vt, vTags, rh) := genInlineValueAndTape allowYearZero depth rg
      cur := rh
      rootEntries := rootEntries.push (k, .table #[(subK, v)])
      let dk : Model.DottedKeyTape := {
        firstKey := k, firstStyle := kst,
        rest := [{ wsBeforeDot := " ", wsAfterDot := "", key := subK, style := subSt }]
      }
      inlineStmts := (.assign pre dk wL wR vt suf) :: inlineStmts
      tags := "key_dotted" :: (pTags ++ kt ++ subKt ++ vTags ++ sTags ++ tags)
    else
      let (v, vt, vTags, rg) := genInlineValueAndTape allowYearZero depth rf
      cur := rg
      rootEntries := rootEntries.push (k, v)
      let dk : Model.DottedKeyTape := { firstKey := k, firstStyle := kst }
      inlineStmts := (.assign pre dk wL wR vt suf) :: inlineStmts
      tags := pTags ++ kt ++ vTags ++ sTags ++ tags
  for idx in [0 : secCnt] do
    let (k0, kst0, kt0, ra) := genKeyAndStyle cur
    let (k, kst, kt) :=
      if seen.contains k0 then (s!"sec_{idx}", Model.KeyStyle.bare, ["key_bare"]) else (k0, kst0, kt0)
    seen := k :: seen
    let (isAot, rb) := ra.nextBool
    if !isAot then
      let (pre, pTags, rc) := genClosedTrivia rb
      let (wO, rd) := genHorizWs rc 1
      let (wC, re) := genHorizWs rd 1
      let (suf, sTags, rf) := genLineSuffix re
      let (fldCnt, rg) := rf.nextRange 0 2
      cur := rg
      let hdrDk : Model.DottedKeyTape := { firstKey := k, firstStyle := kst }
      secStmts := (.tableHeader pre wO hdrDk wC suf) :: secStmts
      tags := "table_header" :: (pTags ++ kt ++ sTags ++ tags)
      let mut subEntries : Array (String × TomlValue) := #[]
      let mut subSeen : List String := []
      for fIdx in [0 : fldCnt] do
        let (fk0, fkst0, fkt0, rka) := genKeyAndStyle cur
        let (fk, fkst, fkt) :=
          if subSeen.contains fk0 then (s!"v_{fIdx}", Model.KeyStyle.bare, ["key_bare"]) else (fk0, fkst0, fkt0)
        subSeen := fk :: subSeen
        let (fv, fvt, fvTags, rkb) := genInlineValueAndTape allowYearZero (depth - 1) rka
        let (fsuf, fsTags, rkc) := genLineSuffix rkb
        cur := rkc
        subEntries := subEntries.push (fk, fv)
        secStmts := (.assign "" { firstKey := fk, firstStyle := fkst } " " " " fvt fsuf) :: secStmts
        tags := fkt ++ fvTags ++ fsTags ++ tags
      rootEntries := rootEntries.push (k, .table subEntries)
    else
      let (elemCnt, rc) := rb.nextRange 1 3
      cur := rc
      let hdrDk : Model.DottedKeyTape := { firstKey := k, firstStyle := kst }
      let mut aotVals : Array TomlValue := #[]
      tags := "aot_header" :: (kt ++ tags)
      for _ in [0 : elemCnt] do
        let (pre, pTags, r1a) := genClosedTrivia cur
        let (suf, sTags, r1b) := genLineSuffix r1a
        let (fldCnt, r1c) := r1b.nextRange 0 2
        cur := r1c
        secStmts := (.aotHeader pre "" hdrDk "" suf) :: secStmts
        tags := pTags ++ sTags ++ tags
        let mut elemEntries : Array (String × TomlValue) := #[]
        for fIdx in [0 : fldCnt] do
          let fk := s!"item_{fIdx}"
          let (fv, fvt, fvTags, r2a) := genInlineValueAndTape allowYearZero (depth - 1) cur
          cur := r2a
          elemEntries := elemEntries.push (fk, fv)
          secStmts := (.assign "" { firstKey := fk, firstStyle := .bare } " " " " fvt {}) :: secStmts
          tags := "key_bare" :: (fvTags ++ tags)
        aotVals := aotVals.push (.table elemEntries)
      rootEntries := rootEntries.push (k, .array aotVals)
  let allStmts := inlineStmts.reverse ++ secStmts.reverse
  let (trailNl, r3) :=
    if allStmts.isEmpty then (true, cur) else cur.chance 3 4
  let (eofTrv, eofTags, r4) :=
    if !allStmts.isEmpty && !trailNl then ("", [], r3)
    else
      let (pickEof, rn) := r3.nextNat 5
      if pickEof == 0 then ("# eof comment", ["comments_blank_lines"], rn)
      else ("", [], rn)
  let noNlTag := if !allStmts.isEmpty && !trailNl && eofTrv.isEmpty then ["no_trailing_newline"] else []
  let baseTape : Model.RenderTape := {
    stmts := allStmts
    trailingNewline := trailNl
    eofTrivia := eofTrv
    crlfMask := []
  }
  match Model.renderLF rootEntries baseTape with
  | none =>
    return (rootEntries, LeanSwe.Toml.format rootEntries, [], r4)
  | some lfStr =>
    let nlCount := (lfStr.toList.filter (· == '\n')).length
    let (wantCrlf, r5) := r4.chance 1 3
    if wantCrlf && nlCount > 0 then
      let mut curM := r5
      let mut maskRev : List Bool := []
      let mut anyTrue := false
      for idx in [0 : nlCount] do
        let (bRaw, rm) := curM.nextBool
        curM := rm
        let b := if idx + 1 == nlCount && !anyTrue then true else bRaw
        if b then anyTrue := true
        maskRev := b :: maskRev
      let crlfTape := { baseTape with crlfMask := maskRev.reverse }
      match Model.render rootEntries crlfTape with
      | some raw =>
        let cTag := if anyTrue then ["crlf"] else []
        return (rootEntries, raw, cTag ++ noNlTag ++ eofTags ++ tags, curM)
      | none =>
        return (rootEntries, lfStr, noNlTag ++ eofTags ++ tags, curM)
    else
      return (rootEntries, lfStr, noNlTag ++ eofTags ++ tags, r5)

/-- Generate a deeply nested (`18..36` levels) TOML container document to exercise stack-safe parsing/formatting. -/
def genDeepNestedTomlCase (r : Rng) : TomlFuzzCase × Rng := Id.run do
  let (depth, r1) := r.nextRange 18 36
  let (leafInt, r2) := r1.nextIntRange (-999) 999
  let mut val : TomlValue := .table #[("leaf", .int (Int64.ofInt leafInt))]
  let mut cur := r2
  for idx in [0 : depth] do
    let (asTbl, rn) := cur.nextBool
    cur := rn
    if asTbl then
      val := .table #[(s!"d{idx}", val)]
    else
      val := .array #[val, .int (Int64.ofInt (Int.ofNat idx))]
  let doc : TomlTable := #[("root", val)]
  let raw := LeanSwe.Toml.format doc
  return (.validRender doc raw ["deep_nested", "key_bare", "int_dec"], cur)

end Fuzz.Toml
