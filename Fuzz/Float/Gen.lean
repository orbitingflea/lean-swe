import Fuzz.Common.Rng
import Init.Data.Float.Model

/-!
Deterministic regression corpus and weighted generators for `Fuzz/Float/`,
including exact Clinger/Paxson/Eisel-Lemire binary64 midpoints, `±1`-ULP perturbations,
multi-word `OfScientific` inputs, and full `Int32` `scaleB` / `frExp` / `Float32` extern probes.
-/

namespace Fuzz.Float

open Fuzz.Common

/-- Single fuzzing test case dispatched by `Fuzz/Float/Suite.lean`. -/
inductive FloatFuzzCase where
  /-- Differential string parsing (`NumParse.parseFloat` vs `parseFloatModel`, `Toml.parse`, `strtod_l`, Python). -/
  | parseStr (s : String)
  /-- Bit-pattern, raw FFI NaN ABI, formatting round-trip, `snprintf`, and `Toml` round-trip. -/
  | checkBits (u : UInt64)
  /-- Binary arithmetic, IEEE-754-2019 min/max, comparisons, `pow`, and `DecidableEq`. -/
  | checkBinOp (ua ub : UInt64)
  /-- Ternary fused multiply-add (`Float.fma` vs `Float.Model.fma` vs C `fma`). -/
  | checkFma (ua ub uc : UInt64)
  /-- Unary ops (`-`, `abs`, `sqrt`) and integer-float conversions (`< 2^53` and `>= 2^53`). -/
  | checkIntConv (u : UInt64)
  /-- `OfScientific.ofScientific` and `Lean.JsonNumber.toFloat` fast/slow and multi-word GMP path checks. -/
  | checkSci (m : Nat) (negExp : Bool) (e : Nat)
  /-- Deterministic `Float` / `Float32` externs (`frExp`, `scaleB` on `Int32`, `ceil`, `floor`, `round`, `Float32`, `FloatArray`, transcendentals). -/
  | checkExtern (u : UInt64) (u32 : UInt32) (scaleExp : Int32)
  deriving Repr, DecidableEq, BEq, Inhabited

private def specialBitsList : Array UInt64 := #[
  0x0000000000000000,
  0x8000000000000000,
  0x7ff0000000000000,
  0xfff0000000000000,
  0x7ff8000000000000,
  0xfff8000000000000
]

private def subnormalEdgeBits : Array UInt64 := #[
  0x0000000000000001,
  0x0000000000000002,
  0x0000000000000003,
  0x000ffffffffffffe,
  0x000fffffffffffff,
  0x0010000000000000,
  0x0010000000000001
]

private def edgeMantissas : Array UInt64 := #[
  0,
  1,
  2,
  0x000ffffffffffffe,
  0x000fffffffffffff
]

private def namedBoundaryBits : Array UInt64 := #[
  0x3fe0000000000000,
  0xbfe0000000000000,
  0x3ff0000000000000,
  0xbff0000000000000,
  0x405fc00000000000,
  0x4060000000000000,
  0xc060000000000000,
  0xc060200000000000,
  0x406fe00000000000,
  0x4070000000000000,
  0x40dfffc000000000,
  0x40e0000000000000,
  0xc0e0000000000000,
  0xc0e0002000000000,
  0x40efffe000000000,
  0x40f0000000000000,
  0x41dfffffffc00000,
  0x41e0000000000000,
  0xc1e0000000000000,
  0xc1e0000000200000,
  0x41f0000000000000,
  0x4330000000000000,
  0xc330000000000000,
  0x4340000000000000,
  0xc340000000000000,
  0x43e0000000000000,
  0xc3e0000000000000,
  0x43f0000000000000,
  0xc3f0000000000000,
  0x7fefffffffffffff,
  0xffefffffffffffff
]

private def genSignBit (r : Rng) : UInt64 × Rng :=
  let (neg, r1) := r.nextBool
  (if neg then 0x8000000000000000 else 0, r1)

/-- Generate a 64-bit IEEE-754 binary64 pattern biased toward NaNs, subnormals, boundaries, and structured carries. -/
def genFloatBits (r : Rng) : UInt64 × Rng :=
  let (bucket, r1) := r.nextNat 100
  if bucket < 15 then
    let (kind, r2) := r1.nextNat 8
    if kind < 6 then
      (specialBitsList.getD kind 0, r2)
    else if kind == 6 then
      let (sign, r3) := genSignBit r2
      let (rawPay, r4) := r3.nextU64
      (sign ||| 0x7ff8000000000000 ||| (rawPay &&& 0x0007ffffffffffff), r4)
    else
      let (sign, r3) := genSignBit r2
      let (rawPay, r4) := r3.nextU64
      let pay := (rawPay % ((1 <<< 51) - 1)) + 1
      (sign ||| 0x7ff0000000000000 ||| pay, r4)
  else if bucket < 35 then
    let (sign, r2) := genSignBit r1
    let (useEdge, r3) := r2.nextBool
    if useEdge then
      let (base, r4) := r3.choose subnormalEdgeBits 1
      (sign ||| base, r4)
    else
      let (mant, r4) := r3.nextRange 1 0x000fffffffffffff
      (sign ||| UInt64.ofNat mant, r4)
  else if bucket < 55 then
    let (mode, r2) := r1.nextNat 4
    if mode == 0 then
      let (base, r3) := r2.choose namedBoundaryBits 0x3ff0000000000000
      let (deltaIdx, r4) := r3.nextNat 5
      let bits := if deltaIdx < 2 then base - UInt64.ofNat (2 - deltaIdx)
        else base + UInt64.ofNat (deltaIdx - 2)
      (bits, r4)
    else if mode < 3 then
      let (sign, r3) := genSignBit r2
      let (exp, r4) := r3.nextRange 1 2046
      let (mant, r5) := r4.choose edgeMantissas 0
      (sign ||| (UInt64.ofNat exp <<< 52) ||| mant, r5)
    else
      let (sign, r3) := genSignBit r2
      let (k, r4) := r3.nextIntRange (-324) 308
      let base := (Float.Model.ofScientific 1 k).toBits
      let (deltaIdx, r5) := r4.nextNat 5
      let adjusted :=
        if deltaIdx == 0 && base >= 2 then base - 2
        else if deltaIdx == 1 && base >= 1 then base - 1
        else if deltaIdx >= 3 && base + UInt64.ofNat (deltaIdx - 2) <= 0x7ff0000000000000 then
          base + UInt64.ofNat (deltaIdx - 2)
        else base
      (sign ||| adjusted, r5)
  else if bucket < 75 then
    let (sign, r2) := genSignBit r1
    let (exp, r3) := r2.nextRange 0 2047
    let (patKind, r4) := r3.nextNat 5
    let (k, r5) := r4.nextRange 0 51
    let bitK : UInt64 := (1 : UInt64) <<< UInt64.ofNat k
    let mant : UInt64 :=
      if patKind == 0 then 0x5555555555555
      else if patKind == 1 then 0xaaaaaaaaaaaaa
      else if patKind == 2 then bitK
      else if patKind == 3 then bitK - 1
      else 0xfffffffffffff ^^^ bitK
    (sign ||| (UInt64.ofNat exp <<< 52) ||| mant, r5)
  else
    r1.nextU64

private def natToDecString (n : Nat) : String :=
  toString n

private def insertValidUnderscores (r : Rng) (s : String) : String × Rng := Id.run do
  let cs := s.toList
  let arr := cs.toArray
  let mut out : Array Char := Array.mkEmpty (arr.size + 4)
  let mut cur := r
  let mut inExp := false
  let mut sawDot := false
  let mut intDigitCount : Nat := 0
  let mut prevWasZeroLead := false
  for i in [0 : arr.size] do
    let c := arr[i]!
    out := out.push c
    let isDigit := '0' ≤ c && c ≤ '9'
    if c == '.' then
      sawDot := true
    else if c == 'e' || c == 'E' then
      inExp := true
    else if isDigit && !sawDot && !inExp then
      if intDigitCount == 0 && c == '0' then
        prevWasZeroLead := true
      intDigitCount := intDigitCount + 1
    if i + 1 < arr.size && isDigit then
      let nxt := arr[i + 1]!
      let nxtDigit := '0' ≤ nxt && nxt ≤ '9'
      if nxtDigit && !prevWasZeroLead then
        let (doIns, r1) := cur.chance 1 8
        cur := r1
        if doIns then
          out := out.push '_'
    if c == '.' || c == 'e' || c == 'E' then
      prevWasZeroLead := false
  return (String.ofList out.toList, cur)

private def formatDecimalSci (signStr : String) (upperE : Bool) (mant : Nat) (exp10 : Int) : String :=
  let sep := if upperE then "E" else "e"
  if mant == 0 then
    s!"{signStr}0.0"
  else
    let ds := (natToDecString mant).toList
    match ds with
    | [] => s!"{signStr}0.0"
    | [d] =>
      let expStr := if exp10 >= 0 then s!"+{exp10}" else s!"{exp10}"
      s!"{signStr}{d}{sep}{expStr}"
    | d :: rest =>
      let adjExp := exp10 + Int.ofNat rest.length
      let expStr := if adjExp >= 0 then s!"+{adjExp}" else s!"{adjExp}"
      s!"{signStr}{String.singleton d}.{String.ofList rest}{sep}{expStr}"

private def formatDecimalFixed? (signStr : String) (mant : Nat) (exp10 : Int) : Option String :=
  if mant == 0 then
    some s!"{signStr}0.0"
  else
    let ds := natToDecString mant
    let len := ds.length
    if exp10 >= 0 then
      let pad := exp10.toNat
      if len + pad + 4 <= 1200 then
        some (signStr ++ ds ++ String.ofList (List.replicate pad '0') ++ ".0")
      else
        none
    else
      let k := (-exp10).toNat
      if k < len then
        if len + 4 <= 1200 then
          let cs := ds.toList
          some (signStr ++ String.ofList (cs.take (len - k)) ++ "." ++ String.ofList (cs.drop (len - k)))
        else
          none
      else
        let zeros := k - len
        if zeros + len + 4 <= 1200 then
          some (signStr ++ "0." ++ String.ofList (List.replicate zeros '0') ++ ds)
        else
          none

private def exactBinaryToDecimal (num : Nat) (pow2Exp : Int) : Nat × Int :=
  if pow2Exp >= 0 then
    (num <<< pow2Exp.toNat, 0)
  else
    let p := (-pow2Exp).toNat
    (num * (5 ^ p), -Int.ofNat p)

/-- Generate an exact binary64 midpoint or `±1`-ULP decimal string (Clinger/Paxson/Eisel-Lemire stress cases). -/
def genExactMidpointString (r : Rng) : String × Rng :=
  let (signKind, r1) := r.nextNat 4
  let signStr := if signKind < 2 then "-" else if signKind == 2 then "+" else ""
  let (isSubnormal, r2) := r1.chance 1 3
  let (num, pow2Exp, r3) :=
    if isSubnormal then
      let (m, rA) := r2.nextRange 0 ((1 <<< 52) - 1)
      (2 * m + 1, (-1075 : Int), rA)
    else
      let (pickDblMax, rA) := r2.chance 1 10
      if pickDblMax then
        ((1 <<< 54) - 1, (970 : Int), rA)
      else
        let (useLower, rB) := rA.chance 1 4
        let (e2, rC) := rB.nextIntRange (-1074) 971
        if useLower && e2 > -1074 then
          ((1 <<< 54) - 1, e2 - 2, rC)
        else
          let (m, rD) := rC.nextRange (1 <<< 52) ((1 <<< 53) - 1)
          (2 * m + 1, e2 - 1, rD)
  let (decMant, decExp10) := exactBinaryToDecimal num pow2Exp
  let (pert, r4) := r3.nextNat 3
  let (finalMant, finalExp, r5) :=
    if pert == 0 then
      (decMant, decExp10, r4)
    else if pert == 1 then
      let (pad, rA) := r4.nextRange 1 16
      (decMant * (10 ^ pad) + 1, decExp10 - Int.ofNat pad, rA)
    else
      let (pad, rA) := r4.nextRange 0 16
      let scaled := decMant * (10 ^ pad)
      let tweaked := if scaled > 0 then scaled - 1 else 0
      (tweaked, decExp10 - Int.ofNat pad, rA)
  let (useFixed, r6) := r5.chance 2 5
  let (upperE, r6b) := r6.nextBool
  let raw :=
    if useFixed then
      match formatDecimalFixed? signStr finalMant finalExp with
      | some s => s
      | none => formatDecimalSci signStr upperE finalMant finalExp
    else
      formatDecimalSci signStr upperE finalMant finalExp
  let (addUnder, r7) := r6b.chance 1 5
  if addUnder then
    insertValidUnderscores r7 raw
  else
    (raw, r7)

private def validTomlVariants : Array String := #[
  "inf", "+inf", "-inf", "nan", "+nan", "-nan",
  "0.0", "+0.0", "-0.0", "0e0", "-0e-999", "+0E+007",
  "1.5e007", "-2.5E-000", "1_2_3.4_5_6e+0_1", "0.0_0_1",
  "9_999_999.0_0_0_1", "1e+00", "-1E-00", "5_0e+1_0"
]

private def invalidTomlLiterals : Array String := #[
  "",
  "00.5", "+01.2", "-00e1", "0_1.5", "0_0e0",
  "_1.0", "1_.0", "1._0", "1.0_", "1__0.0", "1.0__2", "1.0e_1", "1.0e+_1", "1.0e1_", "1.0e1__2",
  "1.5x", "1.5 ", "1.5\t", "1.5\n", "1.5\r", "1.5\x00", "1.5\x01", "1.5\x0b", "1.5\x0c", "1.5\x7f",
  "infx", "+inf ", "-inf ", "nan ", "nan(1)", "nan0", "1.5e2.3", "1.5_.",
  "42", "-0", "+0", ".5", "+.5", "1.", "+1.", "1.e2", "1.E2", "1e", "1e+", "1e-",
  "Inf", "INF", "Infinity", "-Infinity", "NaN", "NAN",
  "0x1p0", "0x1.8p1", "-0x1p-2", "+0x1.0p0", "0x1.0p+10", "-0x1.fffffffffffffp1023",
  " 1.5", "\t0.0", "+", "-", "\x00", "\x7f"
]

private def extremeExponents : Array Int := #[
  -1000000000, -2049, -2048, -2047, -1075, -325, -324, -323, -308,
  308, 309, 1075, 2047, 2048, 2049, 1000000000
]

private def mutationAlphabet : Array Char := #[
  '0', '9', '5', '.', 'e', 'E', '+', '-', '_', ' ', '\n', '\r', '\x00', '\x01', '\x0b', '\x0c', '\x7f',
  'x', 'p', 'i', 'n', 'f', 'a', 'N'
]

private def mutateString (r : Rng) (s : String) : String × Rng := Id.run do
  let mut cs := s.toList.toArray
  let (edits, r1) := r.nextRange 1 3
  let mut cur := r1
  for _ in List.range edits do
    let (kind, r2) := cur.nextNat 3
    let (ch, r3) := r2.choose mutationAlphabet 'x'
    cur := r3
    if cs.isEmpty then
      cs := #[ch]
    else if kind == 0 then
      let (pos, r4) := cur.nextRange 0 cs.size
      cur := r4
      cs := cs.extract 0 pos ++ #[ch] ++ cs.extract pos cs.size
    else if kind == 1 then
      let (pos, r4) := cur.nextNat cs.size
      cur := r4
      cs := cs.extract 0 pos ++ cs.extract (pos + 1) cs.size
    else
      let (pos, r4) := cur.nextNat cs.size
      cur := r4
      cs := cs.set! pos ch
  return (String.ofList cs.toList, cur)

private def utf8ChaosChars : Array Char := #[
  '0', '1', '9', '.', 'e', 'E', '+', '-', '_', ' ', '\t', '\n', '\r', '\x00', '\x01', '\x0b', '\x0c', '\x7f',
  'i', 'n', 'f', 'a', 'x', 'p', '٠', '−', '∞', '\ufeff'
]

/-- Generate a fuzz input string covering exact midpoints, TOML variants, extreme exponents, rejections, and chaos bytes. -/
def genFloatString (r : Rng) : String × Rng :=
  let (bucket, r1) := r.nextNat 100
  if bucket < 25 then
    genExactMidpointString r1
  else if bucket < 40 then
    r1.choose validTomlVariants "0.0"
  else if bucket < 55 then
    let (mode, r2) := r1.nextNat 3
    let (signKind, r3) := r2.nextNat 4
    let signStr := if signKind < 2 then "-" else if signKind == 2 then "+" else ""
    let (upperE, r3b) := r3.nextBool
    let sep := if upperE then "E" else "e"
    if mode == 0 then
      let (expVal, r4) := r3b.choose extremeExponents 308
      let (mant, r5) := r4.nextRange 1 999999999
      (s!"{signStr}{mant}.5{sep}{expVal}", r5)
    else if mode == 1 then
      let (hugeExp, r4) := r3b.nextBool
      if hugeExp then
        (s!"{signStr}1.25{sep}999999999999999999999", r4)
      else
        (s!"{signStr}1.25{sep}-999999999999999999999", r4)
    else
      let (k, r4) := r3b.nextRange 1 400
      let (d, r5) := r4.nextRange 1 9999
      let (expVal, r6) := r5.nextIntRange (-350) 350
      let s := signStr ++ "0." ++ String.ofList (List.replicate k '0') ++ toString d ++ s!"{sep}{expVal}"
      (s, r6)
  else if bucket < 75 then
    r1.choose invalidTomlLiterals ""
  else if bucket < 90 then
    let (base, r2) := genExactMidpointString r1
    mutateString r2 base
  else
    let (len, r2) := r1.nextRange 0 64
    Id.run do
      let mut out : Array Char := Array.mkEmpty len
      let mut cur := r2
      for _ in List.range len do
        let (c, rN) := cur.choose utf8ChaosChars '0'
        cur := rN
        out := out.push c
      return (String.ofList out.toList, cur)

private def genBinOpCase (r : Rng) : FloatFuzzCase × Rng :=
  let (zeroPair, r0) := r.chance 1 25
  if zeroPair then
    let (flip, r1) := r0.nextBool
    if flip then
      (.checkBinOp 0x8000000000000000 0x0000000000000000, r1)
    else
      (.checkBinOp 0x0000000000000000 0x8000000000000000, r1)
  else
    let (ua, r1) := genFloatBits r0
    let (corr, r2) := r1.chance 3 10
    if corr then
      let (kind, r3) := r2.nextNat 4
      let ub :=
        if kind == 0 then ua
        else if kind == 1 then ua ^^^ 0x8000000000000000
        else if kind == 2 then ua + 1
        else ua - 1
      (.checkBinOp ua ub, r3)
    else
      let (ub, r3) := genFloatBits r2
      (.checkBinOp ua ub, r3)

private def genFmaCase (r : Rng) : FloatFuzzCase × Rng :=
  let (mode, r1) := r.nextNat 10
  if mode < 2 then
    let (exp, r2) := r1.nextRange 1 2000
    let (m1, r3) := r2.nextRange 1 0x000fffffffffffff
    let (m2, r4) := r3.nextRange 1 0x000fffffffffffff
    let ua : UInt64 := (UInt64.ofNat exp <<< 52) ||| UInt64.ofNat m1
    let ub : UInt64 := (0x3ff0000000000000 : UInt64) ||| UInt64.ofNat m2
    let prod := (Float.Model.ofBits ua).mul (Float.Model.ofBits ub)
    let negProdBits := prod.toBits ^^^ 0x8000000000000000
    (.checkFma ua ub negProdBits, r4)
  else if mode < 6 then
    let (ua, r2) := genFloatBits r1
    let (ub, r3) := genFloatBits r2
    let prod := (Float.Model.ofBits ua).mul (Float.Model.ofBits ub)
    let negProdBits := prod.toBits ^^^ 0x8000000000000000
    let (delta, r4) := r3.nextRange 0 4
    let uc := if delta < 2 then negProdBits ^^^ UInt64.ofNat delta else negProdBits + UInt64.ofNat delta
    (.checkFma ua ub uc, r4)
  else
    let (ua, r2) := genFloatBits r1
    let (ub, r3) := genFloatBits r2
    let (uc, r4) := genFloatBits r3
    (.checkFma ua ub uc, r4)

private def genMultiWordNat (r : Rng) : Nat × Rng :=
  let (words, r1) := r.nextRange 2 4
  Id.run do
    let mut acc : Nat := 0
    let mut cur := r1
    for _ in List.range words do
      let (w, rN) := cur.nextU64
      cur := rN
      acc := acc * UInt64.size + w.toNat
    return (acc, cur)

private def genSciCase (r : Rng) : FloatFuzzCase × Rng :=
  let (mode, r1) := r.nextNat 4
  let (negExp, r2) := r1.nextBool
  if mode == 0 then
    let (delta, r3) := r2.nextIntRange (-4) 4
    let base := (1 <<< 53 : Int) + delta
    let (e, r4) := r3.nextRange 0 25
    (.checkSci base.toNat negExp e, r4)
  else if mode == 1 then
    let (useExactPow, r3) := r2.nextBool
    let (m, r4) :=
      if useExactPow then
        let (powChoice, rA) := r3.nextBool
        let (delta, rB) := rA.nextIntRange (-3) 3
        let base := if powChoice then (1 <<< 64 : Int) else (1 <<< 128 : Int)
        ((base + delta).toNat, rB)
      else
        genMultiWordNat r3
    let (e, r5) := r4.nextRange 0 350
    (.checkSci m negExp e, r5)
  else if mode == 2 then
    let (useBigM, r3) := r2.nextBool
    let (m, r4) := if useBigM then genMultiWordNat r3 else r3.nextRange 0 (1 <<< 60)
    let cutoff : Nat := if negExp then 2048 + m.log2 else 2048
    let (useHuge, r5) := r4.chance 1 5
    let (e, r6) :=
      if useHuge then
        (cutoff + 10000, r5)
      else
        let lo := if cutoff >= 2 then cutoff - 2 else 0
        r5.nextRange lo (cutoff + 2)
    (.checkSci m negExp e, r6)
  else
    let (m, r3) := r2.nextRange 0 (1 <<< 60)
    let (e, r4) := r3.nextRange 0 350
    (.checkSci m negExp e, r4)

private def edgeScaleExps : Array Int32 := #[
  Int32.ofInt (-2147483648),
  Int32.ofInt (-2147483647),
  Int32.ofInt (-2098),
  Int32.ofInt (-1075),
  Int32.ofInt (-1022),
  Int32.ofInt (-53),
  Int32.ofInt (-1),
  0,
  1,
  53,
  1023,
  2098,
  2147483646,
  2147483647
]

private def specialF32Bits : Array UInt32 := #[
  0x00000000,
  0x80000000,
  0x7f800000,
  0xff800000,
  0x7fc00000,
  0xffc00000,
  0x00000001,
  0x007fffff,
  0x00800000,
  0x7f7fffff,
  0x3f800000,
  0xbf800000
]

/-- Generate a genuine 32-bit IEEE-754 binary32 pattern covering `±0.0f`, `±Inf`, subnormals, `qNaN`, and `sNaN`. -/
def genFloat32Bits (r : Rng) : UInt32 × Rng :=
  let (bucket, r1) := r.nextNat 100
  if bucket < 25 then
    let (kind, r2) := r1.nextNat 14
    if kind < 12 then
      (specialF32Bits.getD kind 0, r2)
    else if kind == 12 then
      let (neg, r3) := r2.nextBool
      let (pay, r4) := r3.nextU32
      let sign : UInt32 := if neg then 0x80000000 else 0
      (sign ||| 0x7fc00000 ||| (pay &&& 0x003fffff), r4)
    else
      let (neg, r3) := r2.nextBool
      let (rawPay, r4) := r3.nextU32
      let sign : UInt32 := if neg then 0x80000000 else 0
      let pay := (rawPay % ((1 <<< 22) - 1)) + 1
      (sign ||| 0x7f800000 ||| pay, r4)
  else if bucket < 50 then
    let (neg, r2) := r1.nextBool
    let (mant, r3) := r2.nextRange 1 0x007fffff
    let sign : UInt32 := if neg then 0x80000000 else 0
    (sign ||| UInt32.ofNat mant, r3)
  else if bucket < 75 then
    let (neg, r2) := r1.nextBool
    let (exp, r3) := r2.nextRange 1 254
    let (mantIdx, r4) := r3.nextNat 4
    let mant : UInt32 :=
      if mantIdx == 0 then 0
      else if mantIdx == 1 then 1
      else if mantIdx == 2 then 0x007ffffe
      else 0x007fffff
    let sign : UInt32 := if neg then 0x80000000 else 0
    (sign ||| (UInt32.ofNat exp <<< 23) ||| mant, r4)
  else
    r1.nextU32

private def genScaleExp (r : Rng) : Int32 × Rng :=
  let (mode, r1) := r.nextNat 3
  if mode == 0 then
    r1.choose edgeScaleExps 0
  else if mode == 1 then
    let (e, r2) := r1.nextIntRange (-1100) 1100
    (Int32.ofInt e, r2)
  else
    let (raw, r2) := r1.nextU32
    (Int32.ofUInt32 raw, r2)

/-- Generate a weighted `FloatFuzzCase` across all 4 differential verification tracks. -/
def genFloatFuzzCase (r : Rng) : FloatFuzzCase × Rng :=
  let (w, r1) := r.nextNat 100
  if w < 32 then
    let (s, r2) := genFloatString r1
    (.parseStr s, r2)
  else if w < 54 then
    let (u, r2) := genFloatBits r1
    (.checkBits u, r2)
  else if w < 68 then
    genBinOpCase r1
  else if w < 77 then
    genFmaCase r1
  else if w < 85 then
    let (u, r2) := genFloatBits r1
    (.checkIntConv u, r2)
  else if w < 92 then
    genSciCase r1
  else
    let (u, r2) := genFloatBits r1
    let (u32, r3) := genFloat32Bits r2
    let (sc, r4) := genScaleExp r3
    (.checkExtern u u32 sc, r4)

/--
Deterministic regression corpus covering famous binary64 boundary literals, raw FFI NaNs, externs, and large inputs.
Note: `"1." ++ 300000 * '0'` is deferred for follow-up once `NumParse.parseFloat` `O(N^2)` trailing-zero DoS is fixed;
a bounded 1000-zero regression is included below.
-/
def smokeCases : Array FloatFuzzCase :=
  let pow5_1075 := 5 ^ 1075
  let dblMaxMid := ((1 <<< 54) - 1) * (1 <<< 970)
  let bigZeros := String.ofList (List.replicate 300000 '0')
  let trailZeros := String.ofList (List.replicate 1000 '0')
  let bigJunk := String.ofList (List.replicate 300000 'a')
  #[
    .checkBits 0x0000000000000000,
    .checkBits 0x8000000000000000,
    .checkBits 0x0000000000000001,
    .checkBits 0x0000000000000002,
    .checkBits 0x000fffffffffffff,
    .checkBits 0x0010000000000000,
    .checkBits 0x3ff0000000000000,
    .checkBits 0x41cdcd6500000000,
    .checkBits 0x7fefffffffffffff,
    .checkBits 0x7ff0000000000000,
    .checkBits 0xfff0000000000000,
    .checkBits 0x7ff8000000000000,
    .checkBits 0xfff800000000dead,
    .checkBits 0x7ff0000000000001,
    .checkBits 0xfff0000000000001,
    .parseStr "0.0",
    .parseStr "-0.0",
    .parseStr "inf",
    .parseStr "+inf",
    .parseStr "-inf",
    .parseStr "nan",
    .parseStr "+nan",
    .parseStr "-nan",
    .parseStr "1_2.3_4",
    .parseStr "1e500",
    .parseStr "-1e500",
    .parseStr "1e-500",
    .parseStr "-1e-500",
    .parseStr s!"{pow5_1075}e-1075",
    .parseStr s!"{pow5_1075 * (10 ^ 20) + 1}e-1095",
    .parseStr s!"{3 * pow5_1075}e-1075",
    .parseStr s!"{3 * pow5_1075 - 1}e-1075",
    .parseStr s!"{dblMaxMid}.0",
    .parseStr s!"{dblMaxMid - 1}.0",
    .parseStr "2.2250738585072011e-308",
    .parseStr "2.2250738585072012e-308",
    .parseStr "2.2250738585072013e-308",
    .parseStr "2.2250738585072014e-308",
    .parseStr "1.4012984643248170709237295832899161312802619418765e-45",
    .parseStr "8928695385828866048e19",
    .parseStr "9007199254740992.5",
    .parseStr "9007199254740993.5",
    .parseStr "9007199254740993.0",
    .parseStr ("0." ++ bigZeros ++ "5e-323"),
    .parseStr ("1." ++ trailZeros),
    .parseStr ("1." ++ trailZeros ++ "5"),
    .parseStr ("1.0" ++ bigJunk),
    .parseStr "",
    .parseStr "00.5",
    .parseStr "1__0.0",
    .parseStr "1.5x",
    .parseStr "42",
    .parseStr ".5",
    .parseStr "1.",
    .parseStr " 1.0",
    .parseStr "0x1.0p0",
    .parseStr "Infinity",
    .parseStr "NaN",
    .parseStr "1.0\x00",
    .parseStr "1.0\x01",
    .parseStr "1.0\x0b",
    .parseStr "1.0\r",
    .parseStr "1.0\x7f",
    .parseStr "1.0٠",
    .checkSci ((1 <<< 53) - 1) false 22,
    .checkSci (1 <<< 53) false 22,
    .checkSci ((1 <<< 53) - 1) false 23,
    .checkSci ((1 <<< 53) - 1) true 22,
    .checkSci (1 <<< 53) true 22,
    .checkSci ((1 <<< 53) - 1) true 23,
    .checkSci ((1 <<< 64) + 7) false 0,
    .checkSci ((1 <<< 128) + 1) true 2048,
    .checkSci 12345 false 2049,
    .checkSci 12345 true 2065,
    .checkBinOp 0x8000000000000000 0x0000000000000000,
    .checkBinOp 0x0000000000000000 0x8000000000000000,
    .checkBinOp 0x7ff8000000000000 0x3ff0000000000000,
    .checkBinOp 0x3ff0000000000000 0xfff800000000dead,
    .checkBinOp 0x7ff0000000000001 0x3ff0000000000000,
    .checkBinOp 0x3ff0000000000000 0x3ff0000000000000,
    .checkBinOp 0x0000000000000001 0x0000000000000001,
    .checkBinOp 0x7fe0000000000000 0x7fe0000000000000,
    .checkBinOp 0x0010000000000000 0x0010000000000000,
    .checkBinOp 0x3ff0000000000000 0x0000000000000000,
    .checkBinOp 0x3ff0000000000000 0x4008000000000000,
    .checkBinOp 0x3ff0000000000000 0x401c000000000000,
    .checkFma 0x3ff0000000000001 0x3feffffffffffffe 0xbff0000000000000,
    .checkFma 0x8010000000000000 0x0010000000000000 0x0000000000000000,
    .checkIntConv 0x4045000000000000,
    .checkIntConv 0xbff0000000000000,
    .checkIntConv 0x4620000000000000,
    .checkIntConv 0x7ff8000000000000,
    .checkExtern 0x0000000000000000 0x00000000 0,
    .checkExtern 0x8000000000000000 0x80000000 (Int32.ofInt (-2147483648)),
    .checkExtern 0xbff0000000000000 0xbf800000 (Int32.ofInt (-2147483648)),
    .checkExtern 0x0000000000000001 0x7f800000 1023,
    .checkExtern 0x3ff8000000000000 0xff800000 (Int32.ofInt (-1075)),
    .checkExtern 0xbff8000000000000 0x7fc00000 2147483647,
    .checkExtern 0x7fefffffffffffff 0x7f800001 1,
    .checkExtern 0x7ff0000000000000 0xff800001 (Int32.ofInt (-2147483648)),
    .checkExtern 0xfff0000000000000 0x00000001 (Int32.ofInt (-2147483647)),
    .checkExtern 0x7ff0000000000001 0x7f7fffff 2147483647
  ]

end Fuzz.Float
