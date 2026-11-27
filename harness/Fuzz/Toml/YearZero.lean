import LeanSwe.Toml.Types
import LeanSweProofs.Toml.Model

namespace Fuzz.Toml

open LeanSwe.Toml

mutual
  /-- Check whether a `TomlValue` contains any proleptic Gregorian year-`0000` date or datetime. -/
  def hasYearZeroValue : TomlValue → Bool
    | .string _ | .int _ | .float _ | .bool _ | .localTime _ => false
    | .offsetDateTime odt => odt.dateTime.date.year == 0
    | .localDateTime dt => dt.date.year == 0
    | .localDate d => d.year == 0
    | .array xs => hasYearZeroList xs.toList
    | .table t => hasYearZeroEntries t.toList
  termination_by v => sizeOf v
  decreasing_by
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)

  /-- Check whether any element in a `List TomlValue` contains year `0000`. -/
  def hasYearZeroList : List TomlValue → Bool
    | [] => false
    | x :: xs => hasYearZeroValue x || hasYearZeroList xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith

  /-- Check whether any value in a table association list contains year `0000`. -/
  def hasYearZeroEntries : List (String × TomlValue) → Bool
    | [] => false
    | (_, v) :: rest => hasYearZeroValue v || hasYearZeroEntries rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp +arith
end

/-- Check whether `doc` contains any year-`0000` date/datetime (`datetime.MINYEAR == 1` in Python). -/
def hasYearZeroTable (doc : TomlTable) : Bool :=
  hasYearZeroEntries doc.toList

private def mapDateYearZeroTo2000 (d : Std.Time.PlainDate) : Std.Time.PlainDate :=
  if d.year == 0 then
    Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 2000) d.month d.day
  else
    d

mutual
  /-- Shift any year-`0000` date or datetime in a `TomlValue` to leap year `2000`. -/
  def mapYearZeroTo2000Value : TomlValue → TomlValue
    | .string s => .string s
    | .int n => .int n
    | .float f => .float f
    | .bool b => .bool b
    | .localTime t => .localTime t
    | .offsetDateTime odt =>
      .offsetDateTime { odt with
        dateTime := Std.Time.PlainDateTime.mk (mapDateYearZeroTo2000 odt.dateTime.date) odt.dateTime.time }
    | .localDateTime dt =>
      .localDateTime (Std.Time.PlainDateTime.mk (mapDateYearZeroTo2000 dt.date) dt.time)
    | .localDate d => .localDate (mapDateYearZeroTo2000 d)
    | .array xs => .array (mapYearZeroTo2000List xs.toList).toArray
    | .table t => .table (mapYearZeroTo2000Entries t.toList).toArray
  termination_by v => sizeOf v
  decreasing_by
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)
    · exact Nat.lt_trans (Model.sizeOf_toList_lt_array _) (by simp +arith)

  /-- Shift any year-`0000` date or datetime in a `List TomlValue` to leap year `2000`. -/
  def mapYearZeroTo2000List : List TomlValue → List TomlValue
    | [] => []
    | x :: xs => mapYearZeroTo2000Value x :: mapYearZeroTo2000List xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith

  /-- Shift any year-`0000` date or datetime across table entries to leap year `2000`. -/
  def mapYearZeroTo2000Entries : List (String × TomlValue) → List (String × TomlValue)
    | [] => []
    | (k, v) :: rest => (k, mapYearZeroTo2000Value v) :: mapYearZeroTo2000Entries rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp +arith
end

/-- Shift any year-`0000` date or datetime in `doc` to leap year `2000` (preserving Feb 29 validity). -/
def mapYearZeroTo2000Table (doc : TomlTable) : TomlTable :=
  (mapYearZeroTo2000Entries doc.toList).toArray

private def isAsciiDecDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Lexer-aware rewrite of value-position `0000-MM-DD` date prefixes to leap year `2000-MM-DD`,
leaving strings, comments, headers, and keys untouched. -/
def rewriteYearZeroTokensTo2000 (raw : String) : String := Id.run do
  let cs := raw.toList.toArray
  let n := cs.size
  let mut out : Array Char := Array.mkEmpty n
  let mut i : Nat := 0
  let mut ctx : List Bool := []
  let mut afterEq : Bool := false
  let mut prevBoundary : Bool := true
  while i < n do
    let c := cs[i]!
    if i + 2 < n && c == '"' && cs[i + 1]! == '"' && cs[i + 2]! == '"' then
      out := out.push '"' |>.push '"' |>.push '"'
      i := i + 3
      let mut closed := false
      while i < n && !closed do
        let sc := cs[i]!
        if sc == '\\' then
          out := out.push '\\'
          i := i + 1
          if i < n then
            out := out.push cs[i]!
            i := i + 1
        else if i + 2 < n && sc == '"' && cs[i + 1]! == '"' && cs[i + 2]! == '"' then
          while i + 3 < n && cs[i + 3]! == '"' do
            out := out.push '"'
            i := i + 1
          out := out.push '"' |>.push '"' |>.push '"'
          i := i + 3
          closed := true
        else
          out := out.push sc
          i := i + 1
      prevBoundary := false
    else if c == '"' then
      out := out.push '"'
      i := i + 1
      let mut closed := false
      while i < n && !closed do
        let sc := cs[i]!
        if sc == '\\' then
          out := out.push '\\'
          i := i + 1
          if i < n then
            out := out.push cs[i]!
            i := i + 1
        else if sc == '"' then
          out := out.push '"'
          i := i + 1
          closed := true
        else
          out := out.push sc
          i := i + 1
      prevBoundary := false
    else if i + 2 < n && c == '\'' && cs[i + 1]! == '\'' && cs[i + 2]! == '\'' then
      out := out.push '\'' |>.push '\'' |>.push '\''
      i := i + 3
      let mut closed := false
      while i < n && !closed do
        let sc := cs[i]!
        if i + 2 < n && sc == '\'' && cs[i + 1]! == '\'' && cs[i + 2]! == '\'' then
          while i + 3 < n && cs[i + 3]! == '\'' do
            out := out.push '\''
            i := i + 1
          out := out.push '\'' |>.push '\'' |>.push '\''
          i := i + 3
          closed := true
        else
          out := out.push sc
          i := i + 1
      prevBoundary := false
    else if c == '\'' then
      out := out.push '\''
      i := i + 1
      let mut closed := false
      while i < n && !closed do
        let sc := cs[i]!
        out := out.push sc
        i := i + 1
        if sc == '\'' then
          closed := true
      prevBoundary := false
    else if c == '#' then
      while i < n && cs[i]! != '\n' do
        out := out.push cs[i]!
        i := i + 1
    else
      let inValPos := afterEq || ctx.head? == some true
      if inValPos && prevBoundary && i + 9 < n &&
          c == '0' && cs[i + 1]! == '0' && cs[i + 2]! == '0' && cs[i + 3]! == '0' &&
          cs[i + 4]! == '-' && isAsciiDecDigit cs[i + 5]! && isAsciiDecDigit cs[i + 6]! &&
          cs[i + 7]! == '-' && isAsciiDecDigit cs[i + 8]! && isAsciiDecDigit cs[i + 9]! then
        out := out.push '2' |>.push '0' |>.push '0' |>.push '0' |>.push '-'
          |>.push cs[i + 5]! |>.push cs[i + 6]! |>.push '-'
          |>.push cs[i + 8]! |>.push cs[i + 9]!
        i := i + 10
        prevBoundary := false
      else
        out := out.push c
        i := i + 1
        if c == '=' then
          afterEq := true
          prevBoundary := true
        else if c == '[' then
          if inValPos then
            ctx := true :: ctx
            afterEq := false
          prevBoundary := true
        else if c == ']' then
          if let true :: rest := ctx then
            ctx := rest
            afterEq := false
          prevBoundary := false
        else if c == '{' then
          if inValPos then
            ctx := false :: ctx
            afterEq := false
          prevBoundary := true
        else if c == '}' then
          if let false :: rest := ctx then
            ctx := rest
            afterEq := false
          prevBoundary := false
        else if c == ',' then
          if ctx.head? == some false then
            afterEq := false
          prevBoundary := true
        else if c == '\n' then
          if ctx.isEmpty then
            afterEq := false
          prevBoundary := true
        else if c == ' ' || c == '\t' || c == '\r' then
          prevBoundary := true
        else
          prevBoundary := false
  return String.ofList out.toList

end Fuzz.Toml
