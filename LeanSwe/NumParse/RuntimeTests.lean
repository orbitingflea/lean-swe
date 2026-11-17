import Core.Assumptions
import LeanSwe.NumParse.Interface

namespace LeanSwe.NumParse.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except NumParseError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except NumParseError α) (expected : α) (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")

private def assertErrKind {α : Type} [Repr α]
    (res : Except NumParseError α) (expectedKind : NumParseErrorKind) (msg : String) : IO Unit := do
  match res with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expectedKind}, got {repr v})")
  | .error e =>
    if e.kind != expectedKind || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expectedKind})")

private def assertFloatBits (res : Except NumParseError Float) (expected : Float) (msg : String) : IO Unit := do
  let actual ← assertOk res msg
  if expected.isNaN then
    assertTrue actual.isNaN s!"{msg}: expected NaN, got bits={actual.toBits}"
  else
    assertTrue (actual.toBits == expected.toBits)
      s!"{msg}: bit mismatch got={actual.toBits} expected={expected.toBits}"

private def runPython3 (script : String) (stdinData : String) : IO String := do
  let out ← IO.Process.output
    { cmd := "python3"
    , args := #["-c", script]
    }
    (some stdinData)
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 failed (exit={out.exitCode}): {out.stderr}")
  return out.stdout

private def testIntParsingAndFormatting : IO Unit := do
  let validInts : List (String × Int) :=
    [ ("0", 0)
    , ("+0", 0)
    , ("-0", 0)
    , ("42", 42)
    , ("-1_000", -1000)
    , ("+1_2_3_4", 1234)
    , ("0xdead_BEEF", 0xdeadbeef)
    , ("0X00_ff", 255)
    , ("0o7_5_5", 493)
    , ("0O007", 7)
    , ("0b1010_0101", 165)
    , ("0B0001", 1)
    , ("999999999999999999999999999999", 999999999999999999999999999999)
    , ("-9223372036854775808", -9223372036854775808)
    , ("9223372036854775807", 9223372036854775807)
    , ("0x8000_0000_0000_0000", 0x8000000000000000)
    ]
  for (s, expected) in validInts do
    assertOkEq (parseInt s) expected s!"parseInt({repr s})"
    let formatted := formatInt expected
    assertTrue (!(formatted.contains '_')) s!"formatInt({expected}) has underscore: {formatted}"
    assertOkEq (parseInt formatted) expected s!"parseInt(formatInt({expected}))"

  assertOkEq (parseInt64 "-9223372036854775808") Int64.minValue "Int64.minValue"
  assertOkEq (parseInt64 "9223372036854775807") Int64.maxValue "Int64.maxValue"
  assertOkEq (parseInt64 "0x7fff_ffff_ffff_ffff") Int64.maxValue "hex Int64.maxValue"
  assertErrKind (parseInt64 "-9223372036854775809") .overflow "Int64 min - 1 overflow"
  assertErrKind (parseInt64 "9223372036854775808") .overflow "Int64 max + 1 overflow"
  assertErrKind (parseInt64 "0x8000_0000_0000_0000") .overflow "hex 2^63 overflow"
  assertErrKind (parseInt64 "0xffff_ffff_ffff_ffff") .overflow "hex 2^64-1 overflow"

  let badInts : List (String × NumParseErrorKind) :=
    [ ("", .emptyInput)
    , ("+", .invalidSyntax)
    , ("-", .invalidSyntax)
    , ("0x", .invalidSyntax)
    , ("0X", .invalidSyntax)
    , ("0o", .invalidSyntax)
    , ("0O", .invalidSyntax)
    , ("0b", .invalidSyntax)
    , ("0B", .invalidSyntax)
    , ("+0x1", .invalidSignForBase)
    , ("-0x1", .invalidSignForBase)
    , ("+0X1", .invalidSignForBase)
    , ("-0o7", .invalidSignForBase)
    , ("+0b1", .invalidSignForBase)
    , ("01", .leadingZero)
    , ("-01", .leadingZero)
    , ("00", .leadingZero)
    , ("0_1", .leadingZero)
    , ("_1", .invalidUnderscore)
    , ("1_", .invalidUnderscore)
    , ("1__2", .invalidUnderscore)
    , ("0x_1", .invalidUnderscore)
    , ("0x1_", .invalidUnderscore)
    , ("0x1__2", .invalidUnderscore)
    , ("0o_7", .invalidUnderscore)
    , ("0b_1", .invalidUnderscore)
    , ("12abc", .trailingChars)
    , ("0x1g", .trailingChars)
    , ("0o8", .invalidSyntax)
    , ("0b2", .invalidSyntax)
    , ("0o18", .trailingChars)
    , ("0b12", .trailingChars)
    , ("42 ", .trailingChars)
    ]
  for (s, k) in badInts do
    assertErrKind (parseInt s) k s!"parseInt error for {repr s}"
    assertErrKind (parseInt64 s) k s!"parseInt64 error for {repr s}"

private def testFloatParsingAndFormatting : IO Unit := do
  assertFloatBits (parseFloat "inf") Float.inf "inf"
  assertFloatBits (parseFloat "+inf") Float.inf "+inf"
  assertFloatBits (parseFloat "-inf") (-Float.inf) "-inf"
  assertFloatBits (parseFloat "nan") Float.nan "nan"
  assertFloatBits (parseFloat "+nan") Float.nan "+nan"
  assertFloatBits (parseFloat "-nan") Float.nan "-nan"
  assertFloatBits (parseFloat "0.0") 0.0 "0.0"
  assertFloatBits (parseFloat "+0.0") 0.0 "+0.0"
  assertFloatBits (parseFloat "-0.0") (-0.0) "-0.0"
  assertTrue ((0.0 : Float).toBits != (-0.0 : Float).toBits) "+0.0 vs -0.0 bit distinction"
  assertFloatBits (parseFloat "5e-324") (Float.ofBits 1) "smallest subnormal 5e-324"
  assertFloatBits (parseFloat "2.47e-324") (Float.ofBits 0) "subnormal round down 2.47e-324"
  assertFloatBits (parseFloat "2.5e-324") (Float.ofBits 1) "subnormal midpoint 2.5e-324"
  assertFloatBits (parseFloat "1e400") Float.inf "1e400 overflow"
  assertFloatBits (parseFloat "-1e400") (-Float.inf) "-1e400 overflow"
  assertFloatBits (parseFloat "1e-400") 0.0 "1e-400 underflow"
  assertFloatBits (parseFloat "-1e-400") (-0.0) "-1e-400 underflow"
  assertFloatBits (parseFloat "1e1000000000") Float.inf "extreme positive exponent"
  assertFloatBits (parseFloat "-1e1000000000") (-Float.inf) "extreme negative-sign overflow"
  assertFloatBits (parseFloat "1e-1000000000") 0.0 "extreme negative exponent underflow"
  assertFloatBits (parseFloat "-1e-1000000000") (-0.0) "extreme negative-sign underflow"

  let formatSamples : Array Float :=
    #[ Float.nan
     , Float.inf
     , -Float.inf
     , 0.0
     , -0.0
     , 1.0
     , -1.0
     , 0.1
     , 0.3
     , 3.141592653589793
     , -1.5e-10
     , 1e100
     , Float.ofBits 1
     , Float.ofBits 2
     , Float.ofBits 0x000fffffffffffff
     , Float.ofBits 0x0010000000000000
     , Float.ofBits 0x7fefffffffffffff
     , Float.ofBits 0xffefffffffffffff
     ]
  for x in formatSamples do
    let s := formatFloat x
    assertTrue (!(s.contains '_')) s!"formatFloat contains underscore: {s}"
    if x.isNaN then
      assertTrue (s == "nan") s!"formatFloat NaN must be nan, got {s}"
    else if x == Float.inf then
      assertTrue (s == "inf") s!"formatFloat +inf must be inf, got {s}"
    else if x == -Float.inf then
      assertTrue (s == "-inf") s!"formatFloat -inf must be -inf, got {s}"
    else
      assertTrue (s.contains '.' || s.contains 'e' || s.contains 'E')
        s!"formatFloat must contain . or e: {s}"
    assertFloatBits (parseFloat s) x s!"parseFloat(formatFloat({repr x}))"
  assertTrue (formatFloat 100.0 == "100.0") s!"expected 100.0, got {formatFloat 100.0}"
  assertTrue (formatFloat 0.1 == "0.1") s!"expected 0.1, got {formatFloat 0.1}"
  assertTrue (formatFloat 1e30 == "1e30") s!"expected 1e30, got {formatFloat 1e30}"

private def testDifferentialPythonIntAndTomllib : IO Unit := do
  let pyIntLiterals : List String :=
    [ "0", "+0", "-0", "42", "-1_000", "+9_876_543"
    , "0xdead_BEEF", "0X00_ff", "0x7fff_ffff_ffff_ffff", "0x8000_0000_0000_0000"
    , "0o7_5_5", "0O007", "0b1010_0101", "0B0001"
    , "1234567890123456789012345678901234567890"
    , "-9223372036854775808", "9223372036854775807"
    ]
  let intScript :=
    "import sys\n" ++
    "for line in sys.stdin.read().splitlines():\n" ++
    "  print(int(line, 0))\n"
  let pyIntOut ← runPython3 intScript (String.intercalate "\n" pyIntLiterals ++ "\n")
  let pyIntLines := pyIntOut.splitOn "\n" |>.filter (!·.isEmpty)
  assertTrue (pyIntLines.length == pyIntLiterals.length) "python int line count mismatch"
  for (lit, pyValStr) in pyIntLiterals.zip pyIntLines do
    let v ← assertOk (parseInt lit) s!"differential parseInt({lit})"
    assertTrue (formatInt v == pyValStr)
      s!"differential int mismatch for {lit}: lean={formatInt v} py={pyValStr}"

  let tomlCases : List (String × Bool × String) :=
    [ ("0", true, "int")
    , ("+99", true, "int")
    , ("-42", true, "int")
    , ("1_000_000", true, "int")
    , ("0xdead_beef", true, "int")
    , ("0o0_755", true, "int")
    , ("0b1101_0010", true, "int")
    , ("+0x1", false, "int")
    , ("-0x1", false, "int")
    , ("01", false, "int")
    , ("0_1", false, "int")
    , ("1_", false, "int")
    , ("1__2", false, "int")
    , ("0x_1", false, "int")
    , ("0.0", true, "float")
    , ("+0.0", true, "float")
    , ("-0.0", true, "float")
    , ("1.5", true, "float")
    , ("-0.01", true, "float")
    , ("5e+22", true, "float")
    , ("1e05", true, "float")
    , ("1e-00", true, "float")
    , ("1e+01", true, "float")
    , ("-2E-2", true, "float")
    , ("6.626e-34", true, "float")
    , ("224_617.445_991_228", true, "float")
    , ("inf", true, "float")
    , ("+inf", true, "float")
    , ("-inf", true, "float")
    , ("nan", true, "float")
    , ("+nan", true, "float")
    , ("-nan", true, "float")
    , ("5e-324", true, "float")
    , ("2.47e-324", true, "float")
    , ("2.5e-324", true, "float")
    , ("1e-323", true, "float")
    , ("1.7976931348623157e308", true, "float")
    , ("1e400", true, "float")
    , ("-1e400", true, "float")
    , ("1e-400", true, "float")
    , ("-1e-400", true, "float")
    , ("Inf", false, "float")
    , ("Infinity", false, "float")
    , ("NaN", false, "float")
    , ("01.5", false, "float")
    , ("-00e1", false, "float")
    , ("1.", false, "float")
    , (".5", false, "float")
    , ("1._5", false, "float")
    , ("1.5e_", false, "float")
    ]
  assertErrKind (parseFloat "42") .invalidSyntax "parseFloat rejects pure integer 42"
  let tomlScript :=
    "import sys, tomllib, struct, math\n" ++
    "for line in sys.stdin.read().splitlines():\n" ++
    "  try:\n" ++
    "    v = tomllib.loads('x = ' + line)['x']\n" ++
    "    if isinstance(v, float):\n" ++
    "      if math.isnan(v):\n" ++
    "        print('OK nan')\n" ++
    "      else:\n" ++
    "        bits = struct.unpack('>Q', struct.pack('>d', v))[0]\n" ++
    "        print(f'OK float {bits}')\n" ++
    "    else:\n" ++
    "      print(f'OK int {v}')\n" ++
    "  except Exception:\n" ++
    "    print('ERR')\n"
  let tomlInput := String.intercalate "\n" (tomlCases.map (·.1)) ++ "\n"
  let tomlOut ← runPython3 tomlScript tomlInput
  let tomlLines := tomlOut.splitOn "\n" |>.filter (!·.isEmpty)
  assertTrue (tomlLines.length == tomlCases.length) "tomllib output line count mismatch"
  for ((lit, expectOk, kind), pyLine) in tomlCases.zip tomlLines do
    if !expectOk then
      assertTrue (pyLine == "ERR") s!"tomllib unexpectedly accepted {lit}: {pyLine}"
      if kind == "int" then
        assertTrue ((parseInt lit).toBool == false) s!"Lean parseInt unexpectedly accepted {lit}"
      else
        assertTrue ((parseFloat lit).toBool == false) s!"Lean parseFloat unexpectedly accepted {lit}"
    else if kind == "int" then
      let v ← assertOk (parseInt lit) s!"tomllib int parseInt({lit})"
      assertTrue (pyLine == s!"OK int {formatInt v}")
        s!"tomllib int mismatch for {lit}: lean={formatInt v} py={pyLine}"
    else
      let f ← assertOk (parseFloat lit) s!"tomllib float parseFloat({lit})"
      if pyLine == "OK nan" then
        assertTrue f.isNaN s!"expected NaN for {lit}, got bits={f.toBits}"
      else
        assertTrue (pyLine == s!"OK float {f.toBits}")
          s!"tomllib float bits mismatch for {lit}: lean={f.toBits} py={pyLine}"

  let pyFmtScript :=
    "import sys, tomllib, struct, math\n" ++
    "for line in sys.stdin.read().splitlines():\n" ++
    "  v = tomllib.loads('x = ' + line)['x']\n" ++
    "  assert isinstance(v, float)\n" ++
    "  if math.isnan(v):\n" ++
    "    print('nan')\n" ++
    "  else:\n" ++
    "    print(struct.unpack('>Q', struct.pack('>d', v))[0])\n"
  let roundTripFloats : List Float :=
    [ Float.nan, Float.inf, -Float.inf, 0.0, -0.0, 1.0, -1.0, 0.1, 0.3, 123456.789
    , Float.ofBits 1, Float.ofBits 2, Float.ofBits 0x000fffffffffffff
    , Float.ofBits 0x0010000000000000, Float.ofBits 0x3fefffffffffffff
    , Float.ofBits 0x7fefffffffffffff, Float.ofBits 0xffefffffffffffff
    ]
  let formattedList := roundTripFloats.map formatFloat
  let fmtOut ← runPython3 pyFmtScript (String.intercalate "\n" formattedList ++ "\n")
  let fmtLines := fmtOut.splitOn "\n" |>.filter (!·.isEmpty)
  assertTrue (fmtLines.length == roundTripFloats.length) "python format round-trip count mismatch"
  for ((x, s), pyOut) in (roundTripFloats.zip formattedList).zip fmtLines do
    if x.isNaN then
      assertTrue (pyOut == "nan") s!"tomllib did not parse formatFloat(NaN)={s} as nan: {pyOut}"
    else
      assertTrue (pyOut == toString x.toBits)
        s!"tomllib formatFloat round-trip mismatch for bits={x.toBits} str={s}: py={pyOut}"

/-- Error test for `parseInt` returning `.emptyInput`. -/
def err_numparse_parseInt_emptyInput : IO Unit :=
  assertErrKind (parseInt "") .emptyInput "parseInt empty input"

/-- Error test for `parseInt` returning `.invalidSyntax`. -/
def err_numparse_parseInt_invalidSyntax : IO Unit :=
  assertErrKind (parseInt "0x") .invalidSyntax "parseInt invalid syntax"

/-- Error test for `parseInt` returning `.invalidSignForBase`. -/
def err_numparse_parseInt_invalidSignForBase : IO Unit :=
  assertErrKind (parseInt "+0x1") .invalidSignForBase "parseInt signed base prefix"

/-- Error test for `parseInt` returning `.leadingZero`. -/
def err_numparse_parseInt_leadingZero : IO Unit :=
  assertErrKind (parseInt "01") .leadingZero "parseInt leading zero"

/-- Error test for `parseInt` returning `.invalidUnderscore`. -/
def err_numparse_parseInt_invalidUnderscore : IO Unit :=
  assertErrKind (parseInt "1__2") .invalidUnderscore "parseInt invalid underscore"

/-- Error test for `parseInt` returning `.trailingChars`. -/
def err_numparse_parseInt_trailingChars : IO Unit :=
  assertErrKind (parseInt "12abc") .trailingChars "parseInt trailing chars"

/-- Error test for `parseInt64` returning `.emptyInput`. -/
def err_numparse_parseInt64_emptyInput : IO Unit :=
  assertErrKind (parseInt64 "") .emptyInput "parseInt64 empty input"

/-- Error test for `parseInt64` returning `.invalidSyntax`. -/
def err_numparse_parseInt64_invalidSyntax : IO Unit :=
  assertErrKind (parseInt64 "0x") .invalidSyntax "parseInt64 invalid syntax"

/-- Error test for `parseInt64` returning `.invalidSignForBase`. -/
def err_numparse_parseInt64_invalidSignForBase : IO Unit :=
  assertErrKind (parseInt64 "-0x1") .invalidSignForBase "parseInt64 signed base prefix"

/-- Error test for `parseInt64` returning `.leadingZero`. -/
def err_numparse_parseInt64_leadingZero : IO Unit :=
  assertErrKind (parseInt64 "01") .leadingZero "parseInt64 leading zero"

/-- Error test for `parseInt64` returning `.invalidUnderscore`. -/
def err_numparse_parseInt64_invalidUnderscore : IO Unit :=
  assertErrKind (parseInt64 "_1") .invalidUnderscore "parseInt64 invalid underscore"

/-- Error test for `parseInt64` returning `.overflow`. -/
def err_numparse_parseInt64_overflow : IO Unit :=
  assertErrKind (parseInt64 "9223372036854775808") .overflow "parseInt64 overflow"

/-- Error test for `parseInt64` returning `.trailingChars`. -/
def err_numparse_parseInt64_trailingChars : IO Unit :=
  assertErrKind (parseInt64 "42 ") .trailingChars "parseInt64 trailing chars"

/-- Error test for `parseFloat` returning `.emptyInput`. -/
def err_numparse_parseFloat_emptyInput : IO Unit :=
  assertErrKind (parseFloat "") .emptyInput "parseFloat empty input"

/-- Error test for `parseFloat` returning `.invalidSyntax`. -/
def err_numparse_parseFloat_invalidSyntax : IO Unit :=
  assertErrKind (parseFloat "1.") .invalidSyntax "parseFloat invalid syntax"

/-- Error test for `parseFloat` returning `.leadingZero`. -/
def err_numparse_parseFloat_leadingZero : IO Unit :=
  assertErrKind (parseFloat "01.5") .leadingZero "parseFloat leading zero"

/-- Error test for `parseFloat` returning `.invalidUnderscore`. -/
def err_numparse_parseFloat_invalidUnderscore : IO Unit :=
  assertErrKind (parseFloat "1._0") .invalidUnderscore "parseFloat invalid underscore"

/-- Error test for `parseFloat` returning `.trailingChars`. -/
def err_numparse_parseFloat_trailingChars : IO Unit :=
  assertErrKind (parseFloat "1.5abc") .trailingChars "parseFloat trailing chars"

/-- Registered error-coverage tests for `LeanSwe.NumParse`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_emptyInput"
     , mode := .real
     , run := err_numparse_parseInt_emptyInput }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidSyntax"
     , mode := .real
     , run := err_numparse_parseInt_invalidSyntax }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidSignForBase"
     , mode := .real
     , run := err_numparse_parseInt_invalidSignForBase }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_leadingZero"
     , mode := .real
     , run := err_numparse_parseInt_leadingZero }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_invalidUnderscore"
     , mode := .real
     , run := err_numparse_parseInt_invalidUnderscore }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt_trailingChars"
     , mode := .real
     , run := err_numparse_parseInt_trailingChars }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_emptyInput"
     , mode := .real
     , run := err_numparse_parseInt64_emptyInput }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidSyntax"
     , mode := .real
     , run := err_numparse_parseInt64_invalidSyntax }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidSignForBase"
     , mode := .real
     , run := err_numparse_parseInt64_invalidSignForBase }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_leadingZero"
     , mode := .real
     , run := err_numparse_parseInt64_leadingZero }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_invalidUnderscore"
     , mode := .real
     , run := err_numparse_parseInt64_invalidUnderscore }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_overflow"
     , mode := .real
     , run := err_numparse_parseInt64_overflow }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseInt64_trailingChars"
     , mode := .real
     , run := err_numparse_parseInt64_trailingChars }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_emptyInput"
     , mode := .real
     , run := err_numparse_parseFloat_emptyInput }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_invalidSyntax"
     , mode := .real
     , run := err_numparse_parseFloat_invalidSyntax }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_leadingZero"
     , mode := .real
     , run := err_numparse_parseFloat_leadingZero }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_invalidUnderscore"
     , mode := .real
     , run := err_numparse_parseFloat_invalidUnderscore }
   , { testName := "LeanSwe.NumParse.RuntimeTests.err_numparse_parseFloat_trailingChars"
     , mode := .real
     , run := err_numparse_parseFloat_trailingChars }
   ]

/-- Run all `LeanSwe.NumParse` deterministic and Python differential runtime tests. -/
def runAll : IO Unit := do
  testIntParsingAndFormatting
  testFloatParsingAndFormatting
  testDifferentialPythonIntAndTomllib
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.NumParse runtime tests"

end LeanSwe.NumParse.RuntimeTests
