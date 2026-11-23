import Std.Data.HashMap
import Std.Data.HashSet
import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Raw.Model

namespace LeanSwe.Sqlite.Model

open LeanSwe.Sqlite

/-- Maximum curated SQL byte length accepted by `parseCuratedSqlWith`. -/
def maxCuratedSqlBytes : Nat := 65536

/-- Maximum identifier byte length accepted by the curated SQL lexer. -/
def maxIdentBytes : Nat := 128

/-- Maximum byte length of a single bound `.text`/`.bytes` parameter (`SQLITE_MAX_LENGTH`). -/
def maxBindValueBytes : Nat := 1000000000

private def maxSqlExprDepth : Nat := 1000
private def lemonMaxStack : Nat := 2500
private def maxSqlColumns : Nat := 2000
private def maxUnixPathnameBytes : Nat := 504
private def maxMemdbPathnameBytes : Nat := 1016

private def hasZeroByteList : List UInt8 → Bool
  | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
    a == 0 || b == 0 || c == 0 || d == 0 ||
    e == 0 || f == 0 || g == 0 || h == 0 ||
    hasZeroByteList rest
  | a :: b :: c :: d :: rest =>
    a == 0 || b == 0 || c == 0 || d == 0 || hasZeroByteList rest
  | a :: b :: rest => a == 0 || b == 0 || hasZeroByteList rest
  | [a] => a == 0
  | [] => false

private def hasZeroByteLoop (bs : ByteArray) (sz idx : Nat) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    if idx < sz then
      if bs.get! idx == 0 then true else hasZeroByteLoop bs sz (idx + 1) rem
    else
      false

/-- Scan checking whether `bs` contains an embedded `0x00` byte from `idx`. -/
def hasZeroByteIdx (bs : ByteArray) (idx : Nat) : Bool :=
  let sz := bs.size
  if idx ≥ sz then false
  else if sz ≤ 256 then hasZeroByteList (bs.data.toList.drop idx)
  else hasZeroByteLoop bs sz idx (sz - idx)

/-- Return `true` iff `bs` begins with the case-sensitive ASCII prefix `"file:"`. -/
def hasFileUriPrefix (bs : ByteArray) : Bool :=
  bs.size ≥ 5 &&
    bs.get! 0 == 0x66 && bs.get! 1 == 0x69 && bs.get! 2 == 0x6C &&
    bs.get! 3 == 0x65 && bs.get! 4 == 0x3A

private def baToListLoop (bs : ByteArray) (sz idx : Nat) : Nat → List UInt8 → List UInt8
  | 0, rev => rev.reverse
  | rem + 1, rev =>
    if idx < sz then baToListLoop bs sz (idx + 1) rem (bs.get! idx :: rev)
    else rev.reverse

private def baToListSlice (bs : ByteArray) (start stop : Nat) : List UInt8 :=
  let sz := min stop bs.size
  if start ≥ sz then []
  else if bs.size ≤ 256 then (bs.data.toList.drop start).take (sz - start)
  else baToListLoop bs sz start (sz - start) []

/-- Lowercase an ASCII uppercase byte `'A'..'Z'` to `'a'..'z'`. -/
def asciiLowerByte (b : UInt8) : UInt8 :=
  if 0x41 ≤ b && b ≤ 0x5A then b + 32 else b

/-- Lowercase all ASCII letters in `s`. -/
def asciiLower (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Map a primary SQLite result code (`code &&& 0xFF`) into `SqliteErrorKind`. -/
def classifySqliteCode (code : UInt32) (defaultKind : SqliteErrorKind) : SqliteErrorKind :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy
  | 14 => .notFound
  | 19 => .constraint
  | 21 => .misuse
  | 25 => .invalidInput
  | _ => defaultKind

/-- Convert a pure `SqliteRawError` into a normalized `SqliteError` with non-empty message. -/
def mapRawError : SqliteRawError → SqliteError
  | .cantOpen path? code detail =>
    { kind := .notFound
      sqliteCode := some code
      path := path?
      message := nonEmptyMsg "unable to open sqlite database" detail }
  | .busy code detail =>
    { kind := .busy
      sqliteCode := some code
      message := nonEmptyMsg "sqlite database is busy" detail }
  | .constraint code detail =>
    { kind := .constraint
      sqliteCode := some code
      message := nonEmptyMsg "sqlite constraint failed" detail }
  | .misuse code detail =>
    { kind := .misuse
      sqliteCode := some code
      message := nonEmptyMsg "sqlite library misuse" detail }
  | .invalidArgument detail =>
    { kind := .invalidInput
      message := nonEmptyMsg "invalid sqlite argument" detail }
  | .ioFailure code detail =>
    { kind := .ioError
      sqliteCode := some code
      message := nonEmptyMsg s!"sqlite io failure ({code})" detail }
  | .sqliteCodeError code detail =>
    { kind := classifySqliteCode code .ioError
      sqliteCode := some code
      message := nonEmptyMsg s!"sqlite error ({code})" detail }
  | .userError detail =>
    { kind := .ioError
      message := nonEmptyMsg "sqlite error" detail }

/-- Validate `OpenConfig`, returning an unmapped `SqliteRawError` on failure. -/
def validateConfigRaw (cfg : OpenConfig) : Except SqliteRawError Unit :=
  if cfg.readOnly && cfg.createIfMissing then
    .error (.invalidArgument "cannot combine readOnly = true with createIfMissing = true")
  else if cfg.busyTimeoutMs > maxBusyTimeoutMs then
    .error (.invalidArgument
      s!"busyTimeoutMs {cfg.busyTimeoutMs} exceeds maxBusyTimeoutMs ({maxBusyTimeoutMs})")
  else
    .ok ()

/-- Validate `OpenConfig` using `mapRaw` to produce typed `SqliteError` diagnostics. -/
def validateConfigWith (mapRaw : SqliteRawError → SqliteError) (cfg : OpenConfig) :
    Except SqliteError Unit :=
  (validateConfigRaw cfg).mapError mapRaw

/-- Validate `OpenConfig` using `Model.mapRawError`. -/
def validateConfig (cfg : OpenConfig) : Except SqliteError Unit :=
  validateConfigWith mapRawError cfg

/-- Supported SQLite column type keywords in the curated relational SQL subset. -/
inductive SqlColType where
  /-- `INTEGER` (`INTEGER PRIMARY KEY` aliases `rowid`). -/
  | integer
  /-- `INT` (`INTEGER` affinity, never a `rowid` alias). -/
  | int
  /-- `REAL` (`REAL` affinity). -/
  | real
  /-- `TEXT` (`TEXT` affinity). -/
  | text
  /-- `BLOB` (`NONE` affinity). -/
  | blob
  /-- `ANY` (allowed only in `STRICT` tables; `NONE` affinity). -/
  | any
  deriving Repr, BEq, DecidableEq

/-- Column definition in a curated `CREATE TABLE` statement. -/
structure ColDef where
  /-- Column name as written. -/
  name : String
  /-- Declared column type. -/
  colType : SqlColType
  /-- Whether `PRIMARY KEY` is specified on this column. -/
  primaryKey : Bool := false
  /-- Whether `AUTOINCREMENT` is specified (only valid with `.integer` and `primaryKey = true`). -/
  autoIncrement : Bool := false
  /-- Whether `NOT NULL` is explicitly specified on this column. -/
  notNull : Bool := false
  /-- Whether `UNIQUE` is specified on this column. -/
  unique : Bool := false
  /-- Optional foreign key target `(parentTable, parentCol)`. -/
  references? : Option (String × String) := none
  deriving Repr, BEq, DecidableEq

/-- Scalar literal or positional `?` parameter expression. -/
inductive ScalarExpr where
  /-- SQL `NULL` literal. -/
  | litNull
  /-- Signed 64-bit integer literal. -/
  | litInt (v : Int64)
  /-- UTF-8 string literal. -/
  | litText (s : String)
  /-- Hexadecimal `X'...'` blob literal. -/
  | litBlob (b : ByteArray)
  /-- 0-based positional `?` parameter index. -/
  | param (idx : Nat)
  deriving BEq, DecidableEq

/-- Value expression allowed in `SELECT` projections and `WHERE` comparisons. -/
inductive ValExpr where
  /-- Scalar literal or parameter. -/
  | scalar (e : ScalarExpr)
  /-- Unqualified column reference. -/
  | col (name : String)
  deriving BEq, DecidableEq

/-- Binary SQL comparison operator in `WHERE` predicates. -/
inductive CmpOp where
  /-- Equality `=`. -/
  | eq
  /-- Inequality `!=` or `<>`. -/
  | ne
  /-- Less-than `<`. -/
  | lt
  /-- Less-than-or-equal `<=`. -/
  | le
  /-- Greater-than `>`. -/
  | gt
  /-- Greater-than-or-equal `>=`. -/
  | ge
  deriving Repr, BEq, DecidableEq

/-- Boolean predicate AST for `WHERE` clauses. -/
inductive WhereExpr where
  /-- Binary comparison `lhs op rhs`. -/
  | cmp (op : CmpOp) (lhs rhs : ValExpr)
  /-- `expr IS NULL` (when `negated = false`) or `expr IS NOT NULL` (when `negated = true`). -/
  | isNull (negated : Bool) (expr : ValExpr)
  /-- Logical negation `NOT sub`. -/
  | not (sub : WhereExpr)
  /-- Logical conjunction `lhs AND rhs`. -/
  | and (lhs rhs : WhereExpr)
  /-- Logical disjunction `lhs OR rhs`. -/
  | or (lhs rhs : WhereExpr)
  deriving BEq, DecidableEq

/-- Projection list for a curated `SELECT` statement. -/
inductive SelectProj where
  /-- `SELECT *`. -/
  | star
  /-- Explicit non-empty list of projected expressions. -/
  | items (exprs : List ValExpr)
  deriving BEq, DecidableEq

/-- Sort direction for an `ORDER BY` item. -/
inductive SortDir where
  /-- Ascending order (`ASC`, default). -/
  | asc
  /-- Descending order (`DESC`). -/
  | desc
  deriving Repr, BEq, DecidableEq

/-- `NULL` placement policy for an `ORDER BY` item. -/
inductive NullsOrder where
  /-- Default SQLite ordering (`NULLS FIRST` for `ASC`, `NULLS LAST` for `DESC`). -/
  | auto
  /-- Explicit `NULLS FIRST`. -/
  | first
  /-- Explicit `NULLS LAST`. -/
  | last
  deriving Repr, BEq, DecidableEq

/-- Single `ORDER BY` sort key specification. -/
structure OrderItem where
  /-- Target column name. -/
  col : String
  /-- Sort direction. -/
  dir : SortDir := .asc
  /-- Null ordering preference. -/
  nulls : NullsOrder := .auto
  deriving Repr, BEq, DecidableEq

/-- Transaction acquisition mode for `BEGIN`. -/
inductive TxMode where
  /-- `BEGIN` or `BEGIN DEFERRED`. -/
  | deferred
  /-- `BEGIN IMMEDIATE`. -/
  | immediate
  deriving Repr, BEq, DecidableEq

/-- Curated relational SQL statement AST. -/
inductive SqlStmt where
  /-- `CREATE TABLE [IF NOT EXISTS] table (cols...) [STRICT]`. -/
  | createTable (ifNotExists : Bool) (table : String) (cols : List ColDef) (strict : Bool)
  /-- `INSERT INTO table [(cols...)] VALUES (...), ...`. -/
  | insert (table : String) (cols? : Option (List String)) (rows : List (List ScalarExpr))
  /-- `SELECT proj [FROM table] [WHERE where?] [ORDER BY orderBy...] [LIMIT limit?]`. -/
  | select (proj : SelectProj) (table? : Option String) (where? : Option WhereExpr)
      (orderBy : List OrderItem) (limit? : Option ScalarExpr)
  /-- `UPDATE table SET assigns... [WHERE where?]`. -/
  | update (table : String) (assigns : List (String × ScalarExpr)) (where? : Option WhereExpr)
  /-- `DELETE FROM table [WHERE where?]`. -/
  | delete (table : String) (where? : Option WhereExpr)
  /-- `BEGIN [DEFERRED | IMMEDIATE] [TRANSACTION]`. -/
  | begin (mode : TxMode)
  /-- `COMMIT [TRANSACTION]`. -/
  | commit
  /-- `ROLLBACK [TRANSACTION]`. -/
  | rollback
  deriving BEq, DecidableEq

private inductive SqlToken where
  | ident (raw : String) (lower : String)
  | digits (raw : String)
  | strLit (val : String)
  | blobLit (val : ByteArray)
  | qmark
  | lparen
  | rparen
  | comma
  | semi
  | star
  | plus
  | minus
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving BEq

private def isSqlSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D

private def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  bs.get! i

private inductive LexCursor where
  | list (cs : List UInt8)
  | bytes (bs : ByteArray) (sz idx : Nat)

private def mkLexCursor (bs : ByteArray) : LexCursor :=
  if bs.size ≤ maxCuratedSqlBytes then .list bs.data.toList
  else .bytes bs bs.size 0

private def lexCursorPop? : LexCursor → Option (UInt8 × LexCursor)
  | .list [] => none
  | .list (b :: rest) => some (b, .list rest)
  | .bytes bs sz idx =>
    if idx < sz then some (bs.get! idx, .bytes bs sz (idx + 1)) else none

private def lexCursorPeek? : LexCursor → Option UInt8
  | .list [] => none
  | .list (b :: _) => some b
  | .bytes bs sz idx => if idx < sz then some (bs.get! idx) else none

private def lexCursorConsumeBom? : LexCursor → Option LexCursor
  | .list (0xEF :: 0xBB :: 0xBF :: rest) => some (.list rest)
  | .list _ => none
  | .bytes bs sz idx =>
    if idx + 2 < sz && bs.get! idx == 0xEF && bs.get! (idx + 1) == 0xBB && bs.get! (idx + 2) == 0xBF then
      some (.bytes bs sz (idx + 3))
    else
      none

private def skipCCSpaceBaLoop : LexCursor → Nat → LexCursor
  | cur, 0 => cur
  | cur, f + 1 =>
    match lexCursorPop? cur with
    | some (b, cur') =>
      if isSqlSpaceByte b || b == 0x0B then skipCCSpaceBaLoop cur' f else cur
    | none => cur

private inductive TailScanState where
  | normal
  | inSpace
  | sawDash
  | inLineComment
  | sawSlash
  | inBlockComment
  | inBlockSawStar
  | sawBom1
  | sawBom2

private def scanSqlTailBaLoop : TailScanState → LexCursor → Nat → Bool
  | state, cur, 0 =>
    match lexCursorPeek? cur with
    | none =>
      match state with
      | .normal | .inSpace | .inLineComment => true
      | _ => false
    | some _ => false
  | state, cur, f + 1 =>
    match lexCursorPop? cur with
    | none =>
      match state with
      | .normal | .inSpace | .inLineComment => true
      | _ => false
    | some (b, cur') =>
      match state with
      | .normal =>
        if isSqlSpaceByte b then scanSqlTailBaLoop .inSpace cur' f
        else if b == 0xEF then scanSqlTailBaLoop .sawBom1 cur' f
        else if b == 0x2D then scanSqlTailBaLoop .sawDash cur' f
        else if b == 0x2F then scanSqlTailBaLoop .sawSlash cur' f
        else false
      | .inSpace =>
        if isSqlSpaceByte b || b == 0x0B then scanSqlTailBaLoop .inSpace cur' f
        else if b == 0xEF then scanSqlTailBaLoop .sawBom1 cur' f
        else if b == 0x2D then scanSqlTailBaLoop .sawDash cur' f
        else if b == 0x2F then scanSqlTailBaLoop .sawSlash cur' f
        else false
      | .sawDash =>
        if b == 0x2D then scanSqlTailBaLoop .inLineComment cur' f else false
      | .inLineComment =>
        if b == 0x0A then scanSqlTailBaLoop .inSpace cur' f
        else scanSqlTailBaLoop .inLineComment cur' f
      | .sawSlash =>
        if b == 0x2A then scanSqlTailBaLoop .inBlockComment cur' f else false
      | .inBlockComment =>
        if b == 0x2A then scanSqlTailBaLoop .inBlockSawStar cur' f
        else scanSqlTailBaLoop .inBlockComment cur' f
      | .inBlockSawStar =>
        if b == 0x2F then scanSqlTailBaLoop .normal cur' f
        else if b == 0x2A then scanSqlTailBaLoop .inBlockSawStar cur' f
        else scanSqlTailBaLoop .inBlockComment cur' f
      | .sawBom1 =>
        if b == 0xBB then scanSqlTailBaLoop .sawBom2 cur' f else false
      | .sawBom2 =>
        if b == 0xBF then scanSqlTailBaLoop .normal cur' f else false

private def isDigitByte (b : UInt8) : Bool :=
  0x30 ≤ b && b ≤ 0x39

private def isIdentStartByte (b : UInt8) : Bool :=
  (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A) || b == 0x5F

private def isIdentContByte (b : UInt8) : Bool :=
  isIdentStartByte b || isDigitByte b

private def hexValByte? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x61 + 10)
  else none

private def skipLineCommentBaLoop : LexCursor → Nat → LexCursor
  | cur, 0 => cur
  | cur, f + 1 =>
    match lexCursorPop? cur with
    | none => cur
    | some (b, cur') =>
      if b == 0x0A then skipCCSpaceBaLoop cur' f
      else skipLineCommentBaLoop cur' f

private def skipBlockCommentBaLoop : LexCursor → Nat → Option LexCursor
  | _, 0 => none
  | cur, f + 1 =>
    match lexCursorPop? cur with
    | none => none
    | some (b, cur1) =>
      if b == 0x2A then
        match lexCursorPop? cur1 with
        | some (0x2F, cur2) => some cur2
        | some _ => skipBlockCommentBaLoop cur1 f
        | none => none
      else skipBlockCommentBaLoop cur1 f

private def scanIdentBaLoop : LexCursor → Nat → List UInt8 → Nat → Nat × List UInt8 × LexCursor
  | cur, len, acc, 0 => (len, acc, cur)
  | cur, len, acc, f + 1 =>
    match lexCursorConsumeBom? cur with
    | some cur' => scanIdentBaLoop cur' (len + 3) (0xBF :: 0xBB :: 0xEF :: acc) f
    | none =>
      match lexCursorPop? cur with
      | some (b, cur') =>
        if isIdentContByte b then scanIdentBaLoop cur' (len + 1) (b :: acc) f
        else (len, acc, cur)
      | none => (len, acc, cur)

private def scanDigitsBaLoop : LexCursor → List UInt8 → Nat → List UInt8 × LexCursor
  | cur, acc, 0 => (acc, cur)
  | cur, acc, f + 1 =>
    match lexCursorPop? cur with
    | some (b, cur') =>
      if isDigitByte b then scanDigitsBaLoop cur' (b :: acc) f
      else (acc, cur)
    | none => (acc, cur)

private def scanStringLitBaLoop : LexCursor → List UInt8 → Nat → Option (String × LexCursor)
  | _, _, 0 => none
  | cur, acc, f + 1 =>
    match lexCursorPop? cur with
    | none => none
    | some (b, cur1) =>
      if b == 0x27 then
        match lexCursorPop? cur1 with
        | some (0x27, cur2) => scanStringLitBaLoop cur2 (0x27 :: acc) f
        | _ =>
          match String.fromUTF8? (ByteArray.mk acc.reverse.toArray) with
          | some s => some (s, cur1)
          | none => none
      else
        scanStringLitBaLoop cur1 (b :: acc) f

private def pairHexDigitsRev : List UInt8 → List UInt8 → List UInt8
  | lo :: hi :: rest, out => pairHexDigitsRev rest (((hi <<< 4) ||| lo) :: out)
  | _, out => out

private def scanBlobLitBaLoop : LexCursor → List UInt8 → Nat → Nat → Option (ByteArray × LexCursor)
  | _, _, _, 0 => none
  | cur, acc, len, f + 1 =>
    match lexCursorPop? cur with
    | none => none
    | some (b, cur1) =>
      if b == 0x27 then
        if len % 2 == 0 then
          some (ByteArray.mk (pairHexDigitsRev acc []).toArray, cur1)
        else
          none
      else
        match hexValByte? b with
        | some v => scanBlobLitBaLoop cur1 (v :: acc) (len + 1) f
        | none => none

private def lexSqlBaAux (allowTail : Bool) :
    LexCursor → List SqlToken → Nat → Except SqliteRawError (List SqlToken)
  | _, acc, 0 => .ok acc.reverse
  | cur, acc, fuel + 1 =>
    match lexCursorConsumeBom? cur with
    | some cur' => lexSqlBaAux allowTail cur' acc fuel
    | none =>
      match lexCursorPop? cur with
      | none => .ok acc.reverse
      | some (b, cur1) =>
        if isSqlSpaceByte b then
          lexSqlBaAux allowTail (skipCCSpaceBaLoop cur1 (fuel + 1)) acc fuel
        else if b == 0x2D then
          match lexCursorPop? cur1 with
          | some (0x2D, cur2) =>
            lexSqlBaAux allowTail (skipLineCommentBaLoop cur2 (fuel + 1)) acc fuel
          | _ =>
            lexSqlBaAux allowTail cur1 (.minus :: acc) fuel
        else if b == 0x2F then
          match lexCursorPop? cur1 with
          | some (0x2A, cur2) =>
            if (lexCursorPeek? cur2).isSome then
              match skipBlockCommentBaLoop cur2 (fuel + 1) with
              | none => .ok acc.reverse
              | some cur3 => lexSqlBaAux allowTail cur3 acc fuel
            else
              .error (.invalidArgument "unexpected '/' in SQL")
          | _ =>
            .error (.invalidArgument "unexpected '/' in SQL")
        else if b == 0x27 then
          match scanStringLitBaLoop cur1 [] (fuel + 1) with
          | none => .error (.invalidArgument "unterminated string literal in SQL")
          | some (s, cur2) => lexSqlBaAux allowTail cur2 (.strLit s :: acc) fuel
        else if b == 0x58 || b == 0x78 then
          match lexCursorPop? cur1 with
          | some (0x27, cur2) =>
            match scanBlobLitBaLoop cur2 [] 0 (fuel + 1) with
            | none => .error (.invalidArgument "invalid hex blob literal in SQL")
            | some (ba, cur3) => lexSqlBaAux allowTail cur3 (.blobLit ba :: acc) fuel
          | _ =>
            let (idLen, idRev, cur2) := scanIdentBaLoop cur1 1 [b] (fuel + 1)
            if idLen > maxIdentBytes then
              .error (.invalidArgument "identifier exceeds maximum byte length")
            else
              match String.fromUTF8? (ByteArray.mk idRev.reverse.toArray) with
              | some s => lexSqlBaAux allowTail cur2 (.ident s (asciiLower s) :: acc) fuel
              | none => .error (.invalidArgument "invalid UTF-8 in identifier")
        else if isDigitByte b then
          let (digRev, cur2) := scanDigitsBaLoop cur1 [b] (fuel + 1)
          let badTrail :=
            (lexCursorConsumeBom? cur2).isSome ||
              match lexCursorPeek? cur2 with
              | some bNext => bNext == 0x2E || bNext == 0x65 || bNext == 0x45 || isIdentStartByte bNext
              | none => false
          if badTrail then
            .error (.invalidArgument "unsupported numeric literal format in SQL")
          else
            match String.fromUTF8? (ByteArray.mk digRev.reverse.toArray) with
            | some s => lexSqlBaAux allowTail cur2 (.digits s :: acc) fuel
            | none => .error (.invalidArgument "invalid UTF-8 in integer literal")
        else if isIdentStartByte b then
          let (idLen, idRev, cur2) := scanIdentBaLoop cur1 1 [b] (fuel + 1)
          if idLen > maxIdentBytes then
            .error (.invalidArgument "identifier exceeds maximum byte length")
          else
            match String.fromUTF8? (ByteArray.mk idRev.reverse.toArray) with
            | some s => lexSqlBaAux allowTail cur2 (.ident s (asciiLower s) :: acc) fuel
            | none => .error (.invalidArgument "invalid UTF-8 in identifier")
        else if b == 0x3F then
          let badParam :=
            match lexCursorPeek? cur1 with
            | some bNext => isDigitByte bNext || isIdentStartByte bNext
            | none => false
          if badParam then
            .error (.invalidArgument "numbered or named parameters are not supported")
          else
            lexSqlBaAux allowTail cur1 (.qmark :: acc) fuel
        else if b == 0x28 then lexSqlBaAux allowTail cur1 (.lparen :: acc) fuel
        else if b == 0x29 then lexSqlBaAux allowTail cur1 (.rparen :: acc) fuel
        else if b == 0x2C then lexSqlBaAux allowTail cur1 (.comma :: acc) fuel
        else if b == 0x3B then
          if acc.isEmpty then
            lexSqlBaAux allowTail cur1 [] fuel
          else if allowTail || scanSqlTailBaLoop .normal cur1 (fuel + 1) then
            .ok acc.reverse
          else
            .error (.misuse 21 "multiple SQL statements are not allowed")
        else if b == 0x2A then lexSqlBaAux allowTail cur1 (.star :: acc) fuel
        else if b == 0x2B then lexSqlBaAux allowTail cur1 (.plus :: acc) fuel
        else if b == 0x3D then lexSqlBaAux allowTail cur1 (.eq :: acc) fuel
        else if b == 0x21 then
          match lexCursorPop? cur1 with
          | some (0x3D, cur2) => lexSqlBaAux allowTail cur2 (.ne :: acc) fuel
          | _ => .error (.invalidArgument "unexpected '!' in SQL")
        else if b == 0x3C then
          match lexCursorPop? cur1 with
          | some (0x3D, cur2) => lexSqlBaAux allowTail cur2 (.le :: acc) fuel
          | some (0x3E, cur2) => lexSqlBaAux allowTail cur2 (.ne :: acc) fuel
          | _ => lexSqlBaAux allowTail cur1 (.lt :: acc) fuel
        else if b == 0x3E then
          match lexCursorPop? cur1 with
          | some (0x3D, cur2) => lexSqlBaAux allowTail cur2 (.ge :: acc) fuel
          | _ => lexSqlBaAux allowTail cur1 (.gt :: acc) fuel
        else
          .error (.invalidArgument "unexpected or unsupported character in SQL")

private def lexSqlBaRaw (bs : ByteArray) : Except SqliteRawError (List SqlToken) :=
  lexSqlBaAux false (mkLexCursor bs) [] (bs.size + 1)

private def reservedKeywords : List String :=
  [ "select", "from", "where", "insert", "into", "values", "update", "set", "delete",
    "create", "table", "primary", "key", "not", "null", "unique", "references", "strict",
    "autoincrement", "if", "exists", "order", "by", "asc", "desc", "nulls", "first", "last",
    "limit", "and", "or", "is", "begin", "deferred", "immediate", "exclusive", "transaction",
    "commit", "end", "rollback", "as", "on", "in", "like", "glob", "between", "case", "when",
    "then", "else", "cast", "distinct", "all", "join", "left", "right", "inner", "outer",
    "cross", "natural", "using", "group", "having", "union", "intersect", "except", "offset",
    "default", "check", "collate", "constraint", "foreign", "index", "drop", "alter", "view",
    "trigger", "pragma", "vacuum", "attach", "detach", "with", "returning",
    "add", "deferrable", "escape", "isnull", "nothing", "notnull", "to", "raise",
    "true", "false", "current_date", "current_time", "current_timestamp" ]

private def isAllowedSqlIdent (lower : String) : Bool :=
  !lower.startsWith "sqlite_" &&
  lower != "rowid" &&
  lower != "_rowid_" &&
  lower != "oid" &&
  !reservedKeywords.contains lower

private def parseSignedInt64Digits (neg : Bool) (raw : String) : Option Int64 :=
  let ds := raw.toList.dropWhile (· == '0')
  if ds.length > 19 then
    none
  else
    let mag : Nat := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if neg then
      if mag > 9223372036854775808 then none
      else if mag == 9223372036854775808 then some Int64.minValue
      else some (- (Int64.ofInt (Int.ofNat mag)))
    else
      if mag > 9223372036854775807 then none
      else some (Int64.ofInt (Int.ofNat mag))

private def expectKw (kw : String) : List SqlToken → Option (List SqlToken)
  | .ident _ lo :: rest => if lo == kw then some rest else none
  | _ => none

private def parseIdentTok : List SqlToken → Option (String × List SqlToken)
  | .ident raw lo :: rest =>
    if isAllowedSqlIdent lo then some (raw, rest) else none
  | _ => none

private def parseColType : List SqlToken → Option (SqlColType × List SqlToken)
  | .ident _ lo :: rest =>
    if lo == "integer" then some (.integer, rest)
    else if lo == "int" then some (.int, rest)
    else if lo == "real" then some (.real, rest)
    else if lo == "text" then some (.text, rest)
    else if lo == "blob" then some (.blob, rest)
    else if lo == "any" then some (.any, rest)
    else none
  | _ => none

private def parseColConstraints (fuel : Nat) (col : ColDef) (toks : List SqlToken) :
    Option (ColDef × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match toks with
    | .ident _ "primary" :: .ident _ "key" :: rest =>
      if col.primaryKey then none
      else
        match rest with
        | .ident _ "autoincrement" :: rest2 =>
          if col.colType != .integer then none
          else parseColConstraints f { col with primaryKey := true, autoIncrement := true } rest2
        | _ => parseColConstraints f { col with primaryKey := true } rest
    | .ident _ "not" :: .ident _ "null" :: rest =>
      if col.notNull then none
      else parseColConstraints f { col with notNull := true } rest
    | .ident _ "unique" :: rest =>
      if col.unique then none
      else parseColConstraints f { col with unique := true } rest
    | .ident _ "references" :: rest =>
      if col.references?.isSome then none
      else
        match parseIdentTok rest with
        | some (pTab, .lparen :: rest2) =>
          match parseIdentTok rest2 with
          | some (pCol, .rparen :: rest3) =>
            parseColConstraints f { col with references? := some (pTab, pCol) } rest3
          | _ => none
        | _ => none
    | _ => some (col, toks)

private def parseColDef (toks : List SqlToken) : Option (ColDef × List SqlToken) := do
  let (colName, r1) ← parseIdentTok toks
  let (ty, r2) ← parseColType r1
  parseColConstraints 8 { name := colName, colType := ty } r2

private def parseColDefList (fuel : Nat) (toks : List SqlToken) (accRev : List ColDef) :
    Option (List ColDef × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (cd, r1) ← parseColDef toks
    let acc' := cd :: accRev
    match r1 with
    | .comma :: r2 => parseColDefList f r2 acc'
    | _ => some (acc'.reverse, r1)

private def parseIdentList (fuel : Nat) (toks : List SqlToken) (accRev : List String) :
    Option (List String × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (nm, r1) ← parseIdentTok toks
    let acc' := nm :: accRev
    match r1 with
    | .comma :: r2 => parseIdentList f r2 acc'
    | _ => some (acc'.reverse, r1)

private def parseScalarExprH (pIdx : Nat) :
    List SqlToken → Option (ScalarExpr × Nat × Nat × List SqlToken)
  | .ident _ "null" :: rest => some (.litNull, 1, pIdx, rest)
  | .digits d :: rest =>
    match parseSignedInt64Digits false d with
    | some v => some (.litInt v, 1, pIdx, rest)
    | none => none
  | .plus :: .digits d :: rest =>
    match parseSignedInt64Digits false d with
    | some v => some (.litInt v, 2, pIdx, rest)
    | none => none
  | .minus :: .digits d :: rest =>
    match parseSignedInt64Digits true d with
    | some v => some (.litInt v, 2, pIdx, rest)
    | none => none
  | .strLit s :: rest => some (.litText s, 1, pIdx, rest)
  | .blobLit b :: rest => some (.litBlob b, 1, pIdx, rest)
  | .qmark :: rest => some (.param pIdx, 1, pIdx + 1, rest)
  | _ => none

private def parseScalarExpr (pIdx : Nat) (toks : List SqlToken) :
    Option (ScalarExpr × Nat × List SqlToken) :=
  (parseScalarExprH pIdx toks).map fun (e, _, p1, r1) => (e, p1, r1)

private def parseScalarList (fuel : Nat) (pIdx : Nat) (toks : List SqlToken)
    (accRev : List ScalarExpr) : Option (List ScalarExpr × Nat × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (e, p1, r1) ← parseScalarExpr pIdx toks
    let acc' := e :: accRev
    match r1 with
    | .comma :: r2 => parseScalarList f p1 r2 acc'
    | _ => some (acc'.reverse, p1, r1)

private def parseValueTupleList (fuel : Nat) (pIdx : Nat) (expectedLen : Option Nat)
    (toks : List SqlToken) (accRev : List (List ScalarExpr)) :
    Option (List (List ScalarExpr) × Nat × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match toks with
    | .lparen :: r1 => do
      let colCap := (expectedLen.getD maxSqlColumns) + 2
      let (vals, p1, r2) ← parseScalarList colCap pIdx r1 []
      match r2 with
      | .rparen :: r3 =>
        let okLen := match expectedLen with | none => true | some n => vals.length == n
        if !okLen then none
        else
          let acc' := vals :: accRev
          match r3 with
          | .comma :: r4 => parseValueTupleList f p1 (some vals.length) r4 acc'
          | _ => some (acc'.reverse, p1, r3)
      | _ => none
    | _ => none

private def parseValExprH (allowCol : Bool) (pIdx : Nat) (toks : List SqlToken) :
    Option (ValExpr × Nat × Nat × List SqlToken) :=
  match parseScalarExprH pIdx toks with
  | some (se, h, p1, r1) => some (.scalar se, h, p1, r1)
  | none =>
    if allowCol then
      match parseIdentTok toks with
      | some (nm, r1) => some (.col nm, 1, pIdx, r1)
      | none => none
    else
      none

private def parseValExpr (allowCol : Bool) (pIdx : Nat) (toks : List SqlToken) :
    Option (ValExpr × Nat × List SqlToken) :=
  (parseValExprH allowCol pIdx toks).map fun (ve, _, p1, r1) => (ve, p1, r1)

private def parseSelectItems (fuel : Nat) (allowCol : Bool) (pIdx : Nat) (toks : List SqlToken)
    (accRev : List ValExpr) : Option (List ValExpr × Nat × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (ve, p1, r1) ← parseValExpr allowCol pIdx toks
    let acc' := ve :: accRev
    match r1 with
    | .comma :: r2 => parseSelectItems f allowCol p1 r2 acc'
    | _ => some (acc'.reverse, p1, r1)

private def parseCmpOp : List SqlToken → Option (CmpOp × List SqlToken)
  | .eq :: rest => some (.eq, rest)
  | .ne :: rest => some (.ne, rest)
  | .lt :: rest => some (.lt, rest)
  | .le :: rest => some (.le, rest)
  | .gt :: rest => some (.gt, rest)
  | .ge :: rest => some (.ge, rest)
  | _ => none

private inductive WhereOp where
  | lparen
  | notOp
  | andOp
  | orOp

private def isNonNullConstExpr : ValExpr → Bool
  | .scalar (.litInt _) | .scalar (.litText _) | .scalar (.litBlob _) => true
  | _ => false

private def parseWhereAtomLeaf (pIdx : Nat) (toks : List SqlToken) :
    Option (WhereExpr × Nat × Bool × Nat × Nat × List SqlToken) := do
  let (lhs, lhsH, p1, r1) ← parseValExprH true pIdx toks
  match r1 with
  | .ident _ "is" :: .ident _ "not" :: .ident _ "null" :: r2 =>
    if isNonNullConstExpr lhs then
      some (.isNull true lhs, 1, false, 4, p1, r2)
    else
      some (.isNull true lhs, 1 + lhsH, false, 4, p1, r2)
  | .ident _ "is" :: .ident _ "null" :: r2 =>
    if isNonNullConstExpr lhs then
      some (.isNull false lhs, 1, true, 3, p1, r2)
    else
      some (.isNull false lhs, 1 + lhsH, false, 3, p1, r2)
  | _ => do
    let (op, r2) ← parseCmpOp r1
    let (rhs, rhsH, p2, r3) ← parseValExprH true p1 r2
    let leafSlots := if rhsH == 2 then 4 else 3
    some (.cmp op lhs rhs, 1 + max lhsH rhsH, false, leafSlots, p2, r3)

private def popWhereOps (enforcePostInit popOr : Bool) (stackSlots : Nat) :
    List WhereOp → List (WhereExpr × Nat × Bool) → Option (List WhereOp × Nat × List (WhereExpr × Nat × Bool))
  | .notOp :: ops, (e, d, _) :: vs =>
    if enforcePostInit && d + 1 > maxSqlExprDepth then none
    else popWhereOps enforcePostInit popOr (stackSlots - 1) ops ((.not e, d + 1, false) :: vs)
  | .andOp :: ops, (r, rd, rf) :: (l, ld, lf) :: vs =>
    if lf || rf then
      popWhereOps enforcePostInit popOr (stackSlots - 2) ops ((.isNull false (.scalar (.litInt 0)), 1, true) :: vs)
    else
      let nd := 1 + max ld rd
      if nd > maxSqlExprDepth then none
      else popWhereOps enforcePostInit popOr (stackSlots - 2) ops ((.and l r, nd, false) :: vs)
  | .orOp :: ops, (r, rd, _) :: (l, ld, _) :: vs =>
    if popOr then
      let nd := 1 + max ld rd
      if nd > maxSqlExprDepth then none
      else popWhereOps enforcePostInit popOr (stackSlots - 2) ops ((.or l r, nd, false) :: vs)
    else
      some (.orOp :: ops, stackSlots, (r, rd, false) :: (l, ld, false) :: vs)
  | ops, vs => some (ops, stackSlots, vs)

private def parseWhereLoop (enforcePostInit : Bool) (fuel baseSlots : Nat) (wantOp : Bool) (stackSlots : Nat)
    (ops : List WhereOp) (vals : List (WhereExpr × Nat × Bool)) (pIdx : Nat) (toks : List SqlToken) :
    Option (WhereExpr × Nat × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if wantOp then
      match toks with
      | .lparen :: rest =>
        if baseSlots + stackSlots + 1 > lemonMaxStack then none
        else parseWhereLoop enforcePostInit f baseSlots true (stackSlots + 1) (.lparen :: ops) vals pIdx rest
      | .ident _ "not" :: rest =>
        if baseSlots + stackSlots + 1 > lemonMaxStack then none
        else parseWhereLoop enforcePostInit f baseSlots true (stackSlots + 1) (.notOp :: ops) vals pIdx rest
      | _ => do
        let (atom, atomDepth, isConstFalse, leafPeakSlots, p1, r1) ← parseWhereAtomLeaf pIdx toks
        if atomDepth > maxSqlExprDepth || baseSlots + stackSlots + leafPeakSlots > lemonMaxStack then none
        else parseWhereLoop enforcePostInit f baseSlots false stackSlots ops ((atom, atomDepth, isConstFalse) :: vals) p1 r1
    else
      match toks with
      | .ident _ "and" :: rest => do
        let (ops1, ss1, vals1) ← popWhereOps enforcePostInit false stackSlots ops vals
        if baseSlots + ss1 + 2 > lemonMaxStack then none
        else parseWhereLoop enforcePostInit f baseSlots true (ss1 + 2) (.andOp :: ops1) vals1 pIdx rest
      | .ident _ "or" :: rest => do
        let (ops1, ss1, vals1) ← popWhereOps enforcePostInit true stackSlots ops vals
        if baseSlots + ss1 + 2 > lemonMaxStack then none
        else parseWhereLoop enforcePostInit f baseSlots true (ss1 + 2) (.orOp :: ops1) vals1 pIdx rest
      | .rparen :: rest => do
        let (ops1, ss1, vals1) ← popWhereOps enforcePostInit true stackSlots ops vals
        match ops1 with
        | .lparen :: ops2 =>
          parseWhereLoop enforcePostInit f baseSlots false (ss1 - 1) ops2 vals1 pIdx rest
        | _ => none
      | _ => do
        let (ops1, _, vals1) ← popWhereOps enforcePostInit true stackSlots ops vals
        match ops1, vals1 with
        | [], [(e, _, _)] => some (e, pIdx, toks)
        | _, _ => none

private def parseNullsOrder : List SqlToken → Option (NullsOrder × List SqlToken)
  | .ident _ "nulls" :: .ident _ "first" :: rest => some (.first, rest)
  | .ident _ "nulls" :: .ident _ "last" :: rest => some (.last, rest)
  | .ident _ "nulls" :: _ => none
  | toks => some (.auto, toks)

private def parseOrderItem (toks : List SqlToken) : Option (OrderItem × List SqlToken) := do
  let (colName, r1) ← parseIdentTok toks
  let (dir, r2) :=
    match r1 with
    | .ident _ "asc" :: rest => (SortDir.asc, rest)
    | .ident _ "desc" :: rest => (SortDir.desc, rest)
    | _ => (SortDir.asc, r1)
  let (nullsOrd, r3) ← parseNullsOrder r2
  some ({ col := colName, dir := dir, nulls := nullsOrd }, r3)

private def parseOrderList (fuel : Nat) (toks : List SqlToken) (accRev : List OrderItem) :
    Option (List OrderItem × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (item, r1) ← parseOrderItem toks
    let acc' := item :: accRev
    match r1 with
    | .comma :: r2 => parseOrderList f r2 acc'
    | _ => some (acc'.reverse, r1)

private def parseAssignList (fuel : Nat) (pIdx : Nat) (toks : List SqlToken)
    (accRev : List (String × ScalarExpr)) : Option (List (String × ScalarExpr) × Nat × List SqlToken) :=
  match fuel with
  | 0 => none
  | f + 1 => do
    let (colName, r1) ← parseIdentTok toks
    match r1 with
    | .eq :: r2 => do
      let (rhs, p1, r3) ← parseScalarExpr pIdx r2
      let acc' := (colName, rhs) :: accRev
      match r3 with
      | .comma :: r4 => parseAssignList f p1 r4 acc'
      | _ => some (acc'.reverse, p1, r3)
    | _ => none

private def parseOptionalWhere (enforcePostInit : Bool) (baseSlots pIdx : Nat) (toks : List SqlToken) :
    Option (Option WhereExpr × Nat × List SqlToken) :=
  match toks with
  | .ident _ "where" :: rest => do
    let (w, p1, r1) ← parseWhereLoop enforcePostInit (rest.length + 1) baseSlots true 0 [] [] pIdx rest
    some (some w, p1, r1)
  | _ => some (none, pIdx, toks)

private def parseCreateTableStmt (enforcePostInit : Bool) (toks : List SqlToken) : Option (SqlStmt × Nat) := do
  let (ifNotExists, r1) :=
    match toks with
    | .ident _ "if" :: .ident _ "not" :: .ident _ "exists" :: rest => (true, rest)
    | _ => (false, toks)
  let (tblName, r2) ← parseIdentTok r1
  match r2 with
  | .lparen :: r3 =>
    match parseColDefList (r3.length + 1) r3 [] with
    | none =>
      if !enforcePostInit then some (.createTable ifNotExists tblName [] false, 0) else none
    | some (cols, r4) =>
      if enforcePostInit && cols.length > maxSqlColumns then none
      else
        match r4 with
        | .rparen :: r5 =>
          let (isStrict, r6) :=
            match r5 with
            | .ident _ "strict" :: rest => (true, rest)
            | _ => (false, r5)
          if !r6.isEmpty then none
          else if !isStrict && cols.any (fun c => c.colType == .any) then none
          else some (.createTable ifNotExists tblName cols isStrict, 0)
        | _ => none
  | _ => none

private def parseInsertStmt (enforcePostInit : Bool) (toks : List SqlToken) : Option (SqlStmt × Nat) := do
  let r1 ← expectKw "into" toks
  let (tblName, r2) ← parseIdentTok r1
  let (cols?, r3) ←
    match r2 with
    | .lparen :: rest => do
      let (cs, rAfter) ← parseIdentList (rest.length + 1) rest []
      if enforcePostInit && cs.length > maxSqlColumns then none
      else
        match rAfter with
        | .rparen :: rAfter2 => some (some cs, rAfter2)
        | _ => none
    | _ => some (none, r2)
  let r4 ← expectKw "values" r3
  let (tuples, pCount, r5) ← parseValueTupleList (r4.length + 1) 0 none r4 []
  if !r5.isEmpty then none
  else
    match tuples with
    | firstRow :: _ =>
      if enforcePostInit && firstRow.length > maxSqlColumns then none
      else
        match cols? with
        | some cs =>
          if firstRow.length == cs.length then some (.insert tblName (some cs) tuples, pCount)
          else none
        | none => some (.insert tblName none tuples, pCount)
    | [] => none

private def parseSelectStmt (enforcePostInit : Bool) (toks : List SqlToken) : Option (SqlStmt × Nat) := do
  let (proj, p1, r1) ←
    match toks with
    | .star :: rest => some (.star, 0, rest)
    | _ => do
      let (exprs, pA, rA) ← parseSelectItems (toks.length + 1) true 0 toks []
      if enforcePostInit && exprs.length > maxSqlColumns then none
      else some (.items exprs, pA, rA)
  let (tbl?, r2) ←
    match r1 with
    | .ident _ "from" :: rest => do
      let (tblName, rAfter) ← parseIdentTok rest
      some (some tblName, rAfter)
    | _ => some (none, r1)
  let hasColInProj :=
    match proj with
    | .star => true
    | .items es => es.any fun
      | .col _ => true
      | .scalar _ => false
  if tbl?.isNone && hasColInProj then
    none
  else do
    let (where?, p2, r3) ← parseOptionalWhere enforcePostInit 6 p1 r2
    if tbl?.isNone && where?.isSome then none
    else do
      let (orderBy, r4) ←
        match r3 with
        | .ident _ "order" :: .ident _ "by" :: rest =>
          parseOrderList (rest.length + 1) rest []
        | _ => some ([], r3)
      if enforcePostInit && orderBy.length > maxSqlColumns then none
      else if tbl?.isNone && !orderBy.isEmpty then none
      else do
        let (limit?, p3, r5) ←
          match r4 with
          | .ident _ "limit" :: rest => do
            let (lim, pL, rL) ← parseScalarExpr p2 rest
            some (some lim, pL, rL)
          | _ => some (none, p2, r4)
        if !r5.isEmpty then none
        else some (.select proj tbl? where? orderBy limit?, p3)

private def parseUpdateStmt (enforcePostInit : Bool) (toks : List SqlToken) : Option (SqlStmt × Nat) := do
  let (tblName, r1) ← parseIdentTok toks
  let r2 ← expectKw "set" r1
  let (assigns, p1, r3) ← parseAssignList (r2.length + 1) 0 r2 []
  if enforcePostInit && assigns.length > maxSqlColumns then none
  else
    let (where?, p2, r4) ← parseOptionalWhere enforcePostInit 10 p1 r3
    if !r4.isEmpty then none
    else some (.update tblName assigns where?, p2)

private def parseDeleteStmt (enforcePostInit : Bool) (toks : List SqlToken) : Option (SqlStmt × Nat) := do
  let r1 ← expectKw "from" toks
  let (tblName, r2) ← parseIdentTok r1
  let (where?, p1, r3) ← parseOptionalWhere enforcePostInit 7 0 r2
  if !r3.isEmpty then none
  else some (.delete tblName where?, p1)

private def parseBeginStmt (toks : List SqlToken) : Option (SqlStmt × Nat) :=
  match toks with
  | [] => some (.begin .deferred, 0)
  | [.ident _ "transaction"] => some (.begin .deferred, 0)
  | [.ident _ "deferred"] => some (.begin .deferred, 0)
  | [.ident _ "deferred", .ident _ "transaction"] => some (.begin .deferred, 0)
  | [.ident _ "immediate"] => some (.begin .immediate, 0)
  | [.ident _ "immediate", .ident _ "transaction"] => some (.begin .immediate, 0)
  | _ => none

private def parseTokensToStmtWith (enforcePostInit : Bool) : List SqlToken → Option (SqlStmt × Nat)
  | .ident _ "create" :: .ident _ "table" :: rest => parseCreateTableStmt enforcePostInit rest
  | .ident _ "insert" :: rest => parseInsertStmt enforcePostInit rest
  | .ident _ "select" :: rest => parseSelectStmt enforcePostInit rest
  | .ident _ "update" :: rest => parseUpdateStmt enforcePostInit rest
  | .ident _ "delete" :: rest => parseDeleteStmt enforcePostInit rest
  | .ident _ "begin" :: rest => parseBeginStmt rest
  | .ident _ "commit" :: rest =>
    match rest with
    | [] | [.ident _ "transaction"] => some (.commit, 0)
    | _ => none
  | .ident _ "rollback" :: rest =>
    match rest with
    | [] | [.ident _ "transaction"] => some (.rollback, 0)
    | _ => none
  | _ => none

private def parseTokensToStmt (toks : List SqlToken) : Option (SqlStmt × Nat) :=
  parseTokensToStmtWith true toks

/-- Lex and parse `sql` into `(stmt, paramCount)`, returning an unmapped `SqliteRawError` on failure. -/
def parseCuratedSqlRaw (sql : String) : Except SqliteRawError (SqlStmt × Nat) := do
  let bs := sql.toUTF8
  if hasZeroByteIdx bs 0 then
    .error (.invalidArgument "SQL string contains embedded NUL byte")
  else if bs.size > maxCuratedSqlBytes then
    .error (.invalidArgument "SQL statement exceeds maximum curated byte length")
  else
    let toks ← lexSqlBaRaw bs
    if toks.isEmpty then
      .error (.misuse 21 "empty SQL statement")
    else
      match parseTokensToStmt toks with
      | some res => .ok res
      | none => .error (.invalidArgument "SQL statement is outside the curated subset or has a syntax error")

/-- Lex and parse `sql` into `(stmt, paramCount)`, enforcing curated SQL subset, comment, NUL, and framing rules. -/
def parseCuratedSqlWith (mapRaw : SqliteRawError → SqliteError) (sql : String) :
    Except SqliteError (SqlStmt × Nat) :=
  (parseCuratedSqlRaw sql).mapError mapRaw

/-- Validate both `sql` and `params` arity, returning an unmapped `SqliteRawError` on failure. -/
def validateStmtRaw (sql : String) (params : Array SqliteValue) : Except SqliteRawError SqlStmt := do
  let (stmt, paramCount) ← parseCuratedSqlRaw sql
  if params.size != paramCount then
    .error (.invalidArgument s!"parameter count mismatch: expected {paramCount}, got {params.size}")
  else
    .ok stmt

/-- Validate both `sql` and `params` arity against `parseCuratedSqlWith`. -/
def validateStmtWith (mapRaw : SqliteRawError → SqliteError) (sql : String)
    (params : Array SqliteValue) : Except SqliteError SqlStmt :=
  (validateStmtRaw sql params).mapError mapRaw

private def parseRawSqlNoCapWith (enforcePostInit : Bool) (bs : ByteArray) : Except SqliteRawError (SqlStmt × Nat) := do
  let toks ← lexSqlBaRaw bs
  if toks.isEmpty then
    .error (.misuse 21 "empty SQL statement")
  else
    match parseTokensToStmtWith enforcePostInit toks with
    | some res => .ok res
    | none => .error (.invalidArgument "SQL statement is outside the curated subset or has a syntax error")

private def parseRawSqlNoCap (bs : ByteArray) : Except SqliteRawError (SqlStmt × Nat) :=
  parseRawSqlNoCapWith true bs

/-- Parse `sql` without the 64 KiB curated byte cap (still bounded by `maxSqlByteLen` and NUL checks). -/
def parseCuratedSqlNoCapRaw (sql : String) : Except SqliteRawError (SqlStmt × Nat) := do
  let bs := sql.toUTF8
  if bs.size > LeanSwe.Sqlite.Raw.maxSqlByteLen then
    .error (.invalidArgument "SQL statement exceeds maximum byte length")
  else if hasZeroByteIdx bs 0 then
    .error (.invalidArgument "SQL string contains embedded NUL byte")
  else
    parseRawSqlNoCap bs

private def validateStmtNoCapWith (mapRaw : SqliteRawError → SqliteError) (sql : String)
    (params : Array SqliteValue) : Except SqliteError SqlStmt :=
  let bs := sql.toUTF8
  let rawRes : Except SqliteRawError SqlStmt := do
    if bs.size > LeanSwe.Sqlite.Raw.maxSqlByteLen then
      .error (.invalidArgument "SQL statement exceeds maximum byte length")
    else if hasZeroByteIdx bs 0 then
      .error (.invalidArgument "SQL string contains embedded NUL byte")
    else
      let (stmt, paramCount) ← parseRawSqlNoCap bs
      if params.size != paramCount then
        .error (.invalidArgument s!"parameter count mismatch: expected {paramCount}, got {params.size}")
      else
        .ok stmt
  rawRes.mapError mapRaw

/-- Normalize a bound `SqliteValue` matching `sqlite3_bind_double` (`NaN` becomes `.null`). -/
def normalizeBoundParam : SqliteValue → SqliteValue
  | .real f => if f != f then .null else .real f
  | v => v

private def countLeadingZerosU64Loop (u : UInt64) : Nat → Nat
  | 0 => if (u &&& 1) == 1 then 63 else 64
  | bit' + 1 =>
    let bit := bit' + 1
    if ((u >>> UInt64.ofNat bit) &&& 1) == 1 then
      63 - bit
    else
      countLeadingZerosU64Loop u bit'

private def countLeadingZerosU64 (u : UInt64) : Nat :=
  if u == 0 then 64 else countLeadingZerosU64Loop u 63

/-- Bit-exact IEEE-754 round-to-nearest-even `(double)(int64_t)i`, matching C without GMP truncation. -/
def int64ToFloatRNE (i : Int64) : Float :=
  if i == 0 then
    Float.ofBits 0
  else
    let neg := i < 0
    let u : UInt64 :=
      if i == Int64.minValue then 0x8000000000000000
      else UInt64.ofNat i.toInt.natAbs
    let clz := countLeadingZerosU64 u
    let msb := 63 - clz
    let (expBits, mantBits) : UInt64 × UInt64 :=
      if msb ≤ 52 then
        let m := (u <<< UInt64.ofNat (52 - msb)) &&& 0x000fffffffffffff
        (UInt64.ofNat (1023 + msb), m)
      else
        let shift := msb - 52
        let q := u >>> UInt64.ofNat shift
        let mask := ((1 : UInt64) <<< UInt64.ofNat shift) - 1
        let rem := u &&& mask
        let half := (1 : UInt64) <<< UInt64.ofNat (shift - 1)
        let roundUp := rem > half || (rem == half && (q &&& 1) == 1)
        let qRounded := if roundUp then q + 1 else q
        if qRounded == ((1 : UInt64) <<< 53) then
          (UInt64.ofNat (1023 + msb + 1), 0)
        else
          (UInt64.ofNat (1023 + msb), qRounded &&& 0x000fffffffffffff)
    let signBit : UInt64 := if neg then 0x8000000000000000 else 0
    Float.ofBits (signBit ||| (expBits <<< 52) ||| mantBits)

/-- Exact port of `sqlite3RealToI64` (`sqlite3.c:86066`). -/
def sqliteRealToI64 (r : Float) : Int64 :=
  if r != r then 0
  else if r < -9223372036854774784.0 then Int64.minValue
  else if r > 9223372036854774784.0 then Int64.maxValue
  else r.toInt64

/-- Exact port of `sqlite3RealSameAsInt` (`sqlite3.c:86055`). -/
def sqliteRealSameAsInt (r1 : Float) (i : Int64) : Bool :=
  let r2 := int64ToFloatRNE i
  r1 == 0.0 ||
  (r1.toBits == r2.toBits && i >= -2251799813685248 && i < 2251799813685248)

/-- Exact port of `sqlite3VdbeIntegerAffinity` on a `.real r` value (`sqlite3.c:85989`). -/
def sqliteIntegerAffinityReal (r : Float) : SqliteValue :=
  let ix := sqliteRealToI64 r
  if r == int64ToFloatRNE ix && ix > Int64.minValue && ix < Int64.maxValue then
    .int ix
  else
    .real r

private def mul128 (a b : UInt64) : UInt64 × UInt64 :=
  let m32 : UInt64 := 0xffffffff
  let a0 := a &&& m32
  let a1 := a >>> 32
  let b0 := b &&& m32
  let b1 := b >>> 32
  let a0b0 := a0 * b0
  let a1b1 := a1 * b1
  let a0b1 := a0 * b1
  let a1b0 := a1 * b0
  let t := (a0b0 >>> 32) + (a0b1 &&& m32) + (a1b0 &&& m32)
  let lo := (a0b0 &&& m32) ||| (t <<< 32)
  let hi := a1b1 + (a0b1 >>> 32) + (a1b0 >>> 32) + (t >>> 32)
  (hi, lo)

private def mul160 (a : UInt64) (aLo : UInt32) (b : UInt64) : UInt64 × UInt32 :=
  let m32 : UInt64 := 0xffffffff
  let x2 := a >>> 32
  let x1 := a &&& m32
  let x0 := aLo.toUInt64
  let y1 := b >>> 32
  let y0 := b &&& m32
  let x2y1 := x2 * y1
  let r4 := x2y1 >>> 32
  let x2y0 := x2 * y0
  let x1y1 := x1 * y1
  let r3 := (x2y1 &&& m32) + (x2y0 >>> 32) + (x1y1 >>> 32)
  let x1y0 := x1 * y0
  let x0y1 := x0 * y1
  let r2 := (x2y0 &&& m32) + (x1y1 &&& m32) + (x1y0 >>> 32) + (x0y1 >>> 32)
  let x0y0 := x0 * y0
  let r1 := (x1y0 &&& m32) + (x0y1 &&& m32) + (x0y0 >>> 32)
  let r2' := r2 + (r1 >>> 32)
  let r3' := r3 + (r2' >>> 32)
  let hi := (r4 <<< 32) + r3'
  let lo := UInt32.ofNat (r2' &&& m32).toNat
  (hi, lo)

private def fpBaseTable : Array UInt64 :=
  #[ 0x8000000000000000, 0xa000000000000000, 0xc800000000000000, 0xfa00000000000000
   , 0x9c40000000000000, 0xc350000000000000, 0xf424000000000000, 0x9896800000000000
   , 0xbebc200000000000, 0xee6b280000000000, 0x9502f90000000000, 0xba43b74000000000
   , 0xe8d4a51000000000, 0x9184e72a00000000, 0xb5e620f480000000, 0xe35fa931a0000000
   , 0x8e1bc9bf04000000, 0xb1a2bc2ec5000000, 0xde0b6b3a76400000, 0x8ac7230489e80000
   , 0xad78ebc5ac620000, 0xd8d726b7177a8000, 0x878678326eac9000, 0xa968163f0a57b400
   , 0xd3c21bcecceda100, 0x84595161401484a0, 0xa56fa5b99019a5c8 ]

private def fpScaleTable : Array UInt64 :=
  #[ 0x8049a4ac0c5811ae, 0xcf42894a5dce35ea, 0xa76c582338ed2621, 0x873e4f75e2224e68
   , 0xda7f5bf590966848, 0xb080392cc4349dec, 0x8e938662882af53e, 0xe65829b3046b0afa
   , 0xba121a4650e4ddeb, 0x964e858c91ba2655, 0xf2d56790ab41c2a2, 0xc428d05aa4751e4c
   , 0x9e74d1b791e07e48, 0xcccccccccccccccc, 0xcecb8f27f4200f3a, 0xa70c3c40a64e6c51
   , 0x86f0ac99b4e8dafd, 0xda01ee641a708de9, 0xb01ae745b101e9e4, 0x8e41ade9fbebc27d
   , 0xe5d3ef282a242e81, 0xb9a74a0637ce2ee1, 0x95f83d0a1fb69cd9, 0xf24a01a73cf2dccf
   , 0xc3b8358109e84f07, 0x9e19db92b4e31ba9 ]

private def fpScaleLoTable : Array UInt32 :=
  #[ 0x205b896d, 0x52064cad, 0xaf2af2b8, 0x5a7744a7
   , 0xaf39a475, 0xbd8d794e, 0x547eb47b, 0x0cb4a5a3
   , 0x92f34d62, 0x3a6a07f9, 0xfae27299, 0xaa97e14c
   , 0x775ea265, 0xcccccccc, 0x00000000, 0x999090b6
   , 0x69a028bb, 0xe80e6f48, 0x5ec05dd0, 0x14588f14
   , 0x8f1668c9, 0x6d953e2c, 0x4abdaf10, 0xbc633b39
   , 0x0a862f81, 0x6c07a2c2 ]

private def powerOfTen (p : Int) : UInt64 × UInt32 :=
  if p == -1 then
    (fpScaleTable.getD 13 0, fpScaleLoTable.getD 13 0)
  else if 0 ≤ p && p < 27 then
    (fpBaseTable.getD p.toNat 0, 0)
  else
    let g : Int := Int.ediv p 27
    let n : Int := Int.emod p 27
    let idx := (g + 13).toNat
    let s := fpScaleTable.getD idx 0
    let sLo := fpScaleLoTable.getD idx 0
    if n == 0 then
      (s, sLo)
    else
      let (x, lo) := mul160 s sLo (fpBaseTable.getD n.toNat 0)
      if (x &&& ((1 : UInt64) <<< 63)) == 0 then
        let x' := (x <<< 1) ||| ((lo.toUInt64 >>> 31) &&& 1)
        let lo' := (lo <<< 1) ||| 1
        (x', lo')
      else
        (x, lo)

private def pwr10to2 (p : Int) : Int :=
  Int.ediv (p * 108853) 32768

private def pwr2to10 (p : Int) : Int :=
  Int.ediv (p * 78913) 262144

private def fp2Convert10 (m : UInt64) (e : Int) (n : Nat) : UInt64 × Int :=
  let p : Int := (Int.ofNat n) - 1 - pwr2to10 (e + 63)
  let (pwrH, _) := powerOfTen p
  let (h, _) := mul128 m pwrH
  if n == 18 then
    let sh := (-(e + pwr10to2 p + 2)).toNat
    let h' := if sh < 64 then h >>> UInt64.ofNat sh else 0
    let dOut := (h' + ((h' <<< 1) &&& 2)) >>> 1
    (dOut, -p)
  else
    let sh := (-(e + pwr10to2 p + 1)).toNat
    let dOut := if sh < 64 then h >>> UInt64.ofNat sh else 0
    (dOut, -p)

private def fp10Convert2 (d : UInt64) (p : Int) : Float :=
  if p < -348 then
    Float.ofBits 0
  else if p > 347 then
    Float.ofBits 0x7ff0000000000000
  else
    let b : Int := Int.ofNat (64 - countLeadingZerosU64 d)
    let lp := pwr10to2 p
    let e0 : Int := 53 - b - lp
    let e : Int := if e0 > 1074 then 1074 else e0
    if e0 ≥ 1130 then
      Float.ofBits 0
    else
      let sInt : Int := -(e - (64 - b) + lp + 3)
      let sNat := sInt.toNat
      let (pwr10h0, pwr10l0) := powerOfTen p
      let (pwr10h, pwr10l) :=
        if pwr10l0 != 0 then (pwr10h0 + 1, pwr10l0 ^^^ 0xffffffff)
        else (pwr10h0, pwr10l0)
      let shiftX := (64 - b).toNat
      let x := if shiftX < 64 then d <<< UInt64.ofNat shiftX else 0
      let (hi0, lo) := mul128 x pwr10h
      let mid1 : UInt32 := UInt32.ofNat (lo >>> 32).toNat
      let lowMask : UInt64 := if sNat < 64 then ((1 : UInt64) <<< UInt64.ofNat sNat) - 1 else 0xffffffffffffffff
      let (hi1, sticky) : UInt64 × UInt64 :=
        if (hi0 &&& lowMask) == 0 then
          let (hi2, _) := mul128 x (pwr10l.toUInt64 <<< 32)
          let mid2 : UInt32 := UInt32.ofNat (hi2 >>> 32).toNat
          let st : UInt64 := if (mid1 - mid2).toNat > 1 then 1 else 0
          let hiAdj := if mid1 < mid2 then hi0 - 1 else hi0
          (hiAdj, st)
        else
          (hi0, 1)
      let u0 : UInt64 := (if sNat < 64 then hi1 >>> UInt64.ofNat sNat else 0) ||| sticky
      let adj : Bool := u0 ≥ (((1 : UInt64) <<< 55) - 2)
      let (u1, eFinal) : UInt64 × Int :=
        if adj then ((u0 >>> 1) ||| (u0 &&& 1), e - 1)
        else (u0, e)
      let one64 : UInt64 := 1
      let m0 : UInt64 := (u1 + one64 + ((u1 >>> 2) &&& one64)) >>> 2
      if eFinal ≤ -972 then
        Float.ofBits 0x7ff0000000000000
      else
        let bit52 : UInt64 := (1 : UInt64) <<< 52
        let allOnes : UInt64 := 0xffffffffffffffff
        let mFinal : UInt64 :=
          if (m0 &&& bit52) != 0 then
            (m0 &&& (allOnes ^^^ bit52)) |||
              (UInt64.ofNat (1075 - eFinal).toNat <<< 52)
          else
            m0
        Float.ofBits mFinal

private def takeBeforeNulFuel (bs : ByteArray) (idx : Nat) : Nat → ByteArray
  | 0 => bs
  | fuel + 1 =>
    if h : idx < bs.size then
      if bs[idx] == 0 then bs.extract 0 idx
      else takeBeforeNulFuel bs (idx + 1) fuel
    else
      bs

private def takeBeforeNul (bs : ByteArray) (idx : Nat) : ByteArray :=
  takeBeforeNulFuel bs idx (bs.size - idx)

private def isNumericSpaceByte (b : UInt8) : Bool :=
  isSqlSpaceByte b || b == 0x0B

private def skipAsciiSpacesFuel (bs : ByteArray) (idx : Nat) : Nat → Nat
  | 0 => idx
  | fuel + 1 =>
    if h : idx < bs.size then
      if isNumericSpaceByte bs[idx] then skipAsciiSpacesFuel bs (idx + 1) fuel
      else idx
    else
      idx

private def skipAsciiSpaces (bs : ByteArray) (idx : Nat) : Nat :=
  skipAsciiSpacesFuel bs idx (bs.size - idx)

private def scanDigitsEndFuel (bs : ByteArray) (idx : Nat) : Nat → Nat
  | 0 => idx
  | fuel + 1 =>
    if h : idx < bs.size then
      if isDigitByte bs[idx] then scanDigitsEndFuel bs (idx + 1) fuel
      else idx
    else
      idx

private def scanDigitsEnd (bs : ByteArray) (idx : Nat) : Nat :=
  scanDigitsEndFuel bs idx (bs.size - idx)

private def parseAtoFIntPartFuel (bs : ByteArray) (idx : Nat) (s : UInt64) (d : Int) (mState : Nat) :
    Nat → Nat × UInt64 × Int × Nat
  | 0 => (idx, s, d, mState)
  | fuel + 1 =>
    if h : idx < bs.size then
      let b := bs[idx]
      if isDigitByte b then
        let v := (b - 0x30).toUInt64
        let s1 := s * 10 + v
        if s1 ≥ (0xffffffffffffffff - 9) / 10 then
          let stop := scanDigitsEnd bs (idx + 1)
          (stop, s1, d + Int.ofNat (stop - (idx + 1)), 9)
        else
          parseAtoFIntPartFuel bs (idx + 1) s1 d mState fuel
      else
        (idx, s, d, mState)
    else
      (idx, s, d, mState)

private def parseAtoFIntPart (bs : ByteArray) (idx : Nat) (s : UInt64) (d : Int) (mState : Nat) :
    Nat × UInt64 × Int × Nat :=
  parseAtoFIntPartFuel bs idx s d mState (bs.size - idx)

private def parseAtoFFracPartFuel (bs : ByteArray) (idx : Nat) (s : UInt64) (d : Int) (mState : Nat) :
    Nat → Nat × UInt64 × Int × Nat
  | 0 => (idx, s, d, mState)
  | fuel + 1 =>
    if h : idx < bs.size then
      let b := bs[idx]
      if isDigitByte b then
        let v := (b - 0x30).toUInt64
        if s < (0xffffffffffffffff - 9) / 10 then
          parseAtoFFracPartFuel bs (idx + 1) (s * 10 + v) (d - 1) mState fuel
        else
          parseAtoFFracPartFuel bs (idx + 1) s d 11 fuel
      else
        (idx, s, d, mState)
    else
      (idx, s, d, mState)

private def parseAtoFFracPart (bs : ByteArray) (idx : Nat) (s : UInt64) (d : Int) (mState : Nat) :
    Nat × UInt64 × Int × Nat :=
  parseAtoFFracPartFuel bs idx s d mState (bs.size - idx)

private def parseAtoFExpDigitsFuel (bs : ByteArray) (idx : Nat) (expVal : Int) : Nat → Nat × Int
  | 0 => (idx, expVal)
  | fuel + 1 =>
    if h : idx < bs.size then
      let b := bs[idx]
      if isDigitByte b then
        let v := Int.ofNat (b - 0x30).toNat
        let nextExp := if expVal < 10000 then expVal * 10 + v else 10000
        parseAtoFExpDigitsFuel bs (idx + 1) nextExp fuel
      else
        (idx, expVal)
    else
      (idx, expVal)

private def parseAtoFExpDigits (bs : ByteArray) (idx : Nat) (expVal : Int) : Nat × Int :=
  parseAtoFExpDigitsFuel bs idx expVal (bs.size - idx)

/-- Exact port of `sqlite3AtoF` (`sqlite3.c:37713`) operating on bytes before the first NUL (`0x00`).
    Returns `(rc, result)` where `rc > 0` iff the entire prefix before NUL (ignoring spaces) is a valid number. -/
def sqliteAtoF (rawBytes : ByteArray) : Int × Float :=
  let bs := takeBeforeNul rawBytes 0
  let i0 := skipAsciiSpaces bs 0
  let (neg, i1) : Bool × Nat :=
    if h : i0 < bs.size then
      if bs[i0] == 0x2D then (true, i0 + 1)
      else if bs[i0] == 0x2B then (false, i0 + 1)
      else (false, i0)
    else
      (false, i0)
  let (i2, s2, d2, m2) : Nat × UInt64 × Int × Nat :=
    if h : i1 < bs.size then
      if isDigitByte bs[i1] then
        let v := (bs[i1] - 0x30).toUInt64
        parseAtoFIntPart bs (i1 + 1) v 0 1
      else
        (i1, 0, 0, 0)
    else
      (i1, 0, 0, 0)
  let (abortEarly, i3, s3, d3, m3) : Bool × Nat × UInt64 × Int × Nat :=
    if h : i2 < bs.size then
      if bs[i2] == 0x2E then
        if h2 : i2 + 1 < bs.size then
          if isDigitByte bs[i2 + 1] then
            let (iF, sF, dF, mF) := parseAtoFFracPart bs (i2 + 1) s2 d2 (m2 ||| 1)
            (false, iF, sF, dF, mF ||| 2)
          else if m2 == 0 then
            (true, i2 + 1, 0, 0, 0)
          else
            (false, i2 + 1, s2, d2, m2 ||| 2)
        else if m2 == 0 then
          (true, i2 + 1, 0, 0, 0)
        else
          (false, i2 + 1, s2, d2, m2 ||| 2)
      else if m2 == 0 then
        (true, i2, 0, 0, 0)
      else
        (false, i2, s2, d2, m2)
    else if m2 == 0 then
      (true, i2, 0, 0, 0)
    else
      (false, i2, s2, d2, m2)
  if abortEarly then
    (0, Float.ofBits 0)
  else
    let (i4, d4, m4) : Nat × Int × Nat :=
      if h : i3 < bs.size then
        if bs[i3] == 0x65 || bs[i3] == 0x45 then
          let iSign := i3 + 1
          let (eSign, iDig) : Int × Nat :=
            if h2 : iSign < bs.size then
              if bs[iSign] == 0x2D then (-1, iSign + 1)
              else if bs[iSign] == 0x2B then (1, iSign + 1)
              else (1, iSign)
            else
              (1, iSign)
          if h3 : iDig < bs.size then
            if isDigitByte bs[iDig] then
              let v := Int.ofNat (bs[iDig] - 0x30).toNat
              let (iExpEnd, expVal) := parseAtoFExpDigits bs (iDig + 1) v
              (iExpEnd, d3 + eSign * expVal, m3 ||| 2)
            else
              (i3, d3, m3)
          else
            (i3, d3, m3)
        else
          (i3, d3, m3)
      else
        (i3, d3, m3)
    let (rPos, m5) :=
      if s3 == 0 then (Float.ofBits 0, m4 ||| 4)
      else (fp10Convert2 s3 d4, m4)
    let rFinal := if neg then -rPos else rPos
    let iEnd := skipAsciiSpaces bs i4
    if iEnd == bs.size then
      (Int.ofNat m5, rFinal)
    else
      (Int.ofNat (m5 &&& 0xF) - 16, rFinal)

private def compare2Pow63 (bs : ByteArray) (idx : Nat) : Int :=
  let pow63 := "922337203685477580".toUTF8
  let rec loop (k : Nat) : Int :=
    if h : k < 18 then
      let c1 := (byteAt bs (idx + k)).toNat
      let c2 := (pow63[k]!).toNat
      if c1 != c2 then (Int.ofNat c1 - Int.ofNat c2) * 10
      else loop (k + 1)
    else
      Int.ofNat (byteAt bs (idx + 18)).toNat - Int.ofNat 0x38
  loop 0

private def skipZerosIdxFuel (bs : ByteArray) (idx : Nat) : Nat → Nat
  | 0 => idx
  | fuel + 1 =>
    if h : idx < bs.size then
      if bs[idx] == 0x30 then skipZerosIdxFuel bs (idx + 1) fuel else idx
    else
      idx

private def skipZerosIdx (bs : ByteArray) (idx : Nat) : Nat :=
  skipZerosIdxFuel bs idx (bs.size - idx)

private def parseAtoi64DigitsFuel (bs : ByteArray) (idx : Nat) (u : UInt64) (cnt : Nat) :
    Nat → Nat × UInt64 × Nat
  | 0 => (idx, u, cnt)
  | fuel + 1 =>
    if h : idx < bs.size then
      let b := bs[idx]
      if isDigitByte b then
        parseAtoi64DigitsFuel bs (idx + 1) (u * 10 + (b - 0x30).toUInt64) (cnt + 1) fuel
      else
        (idx, u, cnt)
    else
      (idx, u, cnt)

private def parseAtoi64Digits (bs : ByteArray) (idx : Nat) (u : UInt64) (cnt : Nat) :
    Nat × UInt64 × Nat :=
  parseAtoi64DigitsFuel bs idx u cnt (bs.size - idx)

/-- Exact port of `sqlite3Atoi64` (`sqlite3.c:38008`) for UTF-8 byte arrays.
    Returns `(rc, value)` where `rc == 0` iff the full string fits in signed `Int64`. -/
def sqliteAtoi64 (bs : ByteArray) : Int × Int64 :=
  let i0 := skipAsciiSpaces bs 0
  let (neg, i1) :=
    if h : i0 < bs.size then
      if bs[i0] == 0x2D then (true, i0 + 1)
      else if bs[i0] == 0x2B then (false, i0 + 1)
      else (false, i0)
    else
      (false, i0)
  let iDigits := skipZerosIdx bs i1
  let (iAfter, u, cnt) := parseAtoi64Digits bs iDigits 0 0
  let outVal : Int64 :=
    if u > 0x7fffffffffffffff then
      if neg then Int64.minValue else Int64.maxValue
    else if neg then
      - (Int64.ofUInt64 u)
    else
      Int64.ofUInt64 u
  let rcBase : Int :=
    if cnt == 0 && iDigits == i1 then -1
    else if skipAsciiSpaces bs iAfter < bs.size then 1
    else 0
  if cnt < 19 then
    (rcBase, outVal)
  else
    let cmp := if cnt > 19 then 1 else compare2Pow63 bs iDigits
    if cmp < 0 then
      (rcBase, outVal)
    else
      let clamped := if neg then Int64.minValue else Int64.maxValue
      if cmp > 0 then (2, clamped)
      else if neg then (rcBase, Int64.minValue)
      else (3, Int64.maxValue)

private def alsoAnInt (bs : ByteArray) (rValue : Float) : Option Int64 :=
  let ix := sqliteRealToI64 rValue
  if sqliteRealSameAsInt rValue ix then
    some ix
  else
    let (rc, iv) := sqliteAtoi64 bs
    if rc == 0 then some iv else none

/-- Exact port of `applyNumericAffinity` (`sqlite3.c:96630`) on a `.text s` value. -/
def applyNumericAffinityText (s : String) (tryForInt : Bool) : SqliteValue :=
  let bs := s.toUTF8
  let (rc, rValue) := sqliteAtoF bs
  if rc ≤ 0 then
    .text s
  else if (rc.toNat &&& 2) == 0 then
    match alsoAnInt bs rValue with
    | some iv => .int iv
    | none => if tryForInt then sqliteIntegerAffinityReal rValue else .real rValue
  else if tryForInt then
    sqliteIntegerAffinityReal rValue
  else
    .real rValue

private def natToDecDigits (n : Nat) : Array Char :=
  let rec go (k : Nat) (acc : List Char) : List Char :=
    if k < 10 then Char.ofNat ('0'.toNat + k) :: acc
    else go (k / 10) (Char.ofNat ('0'.toNat + (k % 10)) :: acc)
  (go n []).toArray

private def digitsToUInt64 (ds : Array Char) (stop : Nat) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if i < stop then
      let d := UInt64.ofNat ((ds.getD i '0').toNat - '0'.toNat)
      go (i + 1) (acc * 10 + d)
    else
      acc
  go 0 0

private def countTrailingNines (ds : Array Char) (j : Nat) : Nat :=
  if h : j > 0 then
    if ds.getD (j - 1) '0' == '9' then countTrailingNines ds (j - 1)
    else j
  else
    j
termination_by j

private def countTrailingZerosIdx (ds : Array Char) (j : Nat) : Nat :=
  if h : j > 0 then
    if ds.getD (j - 1) '0' == '0' then countTrailingZerosIdx ds (j - 1)
    else j
  else
    j
termination_by j

private def roundDigitsUpGo : Nat → Array Char → Array Char × Bool
  | 0, cur =>
    let c := cur.getD 0 '0'
    if c < '9' then (cur.set! 0 (Char.ofNat (c.toNat + 1)), false)
    else (#['1'] ++ cur.set! 0 '0', true)
  | j' + 1, cur =>
    let j := j' + 1
    let c := cur.getD j '0'
    if c < '9' then (cur.set! j (Char.ofNat (c.toNat + 1)), false)
    else roundDigitsUpGo j' (cur.set! j '0')

private def roundDigitsUp (ds : Array Char) (len : Nat) : Array Char × Bool :=
  if len == 0 then (ds, false) else roundDigitsUpGo (len - 1) ds

private def stripTrailingZeroChars (ds : Array Char) (n : Nat) : Nat :=
  if h : n > 1 then
    if ds.getD (n - 1) '0' == '0' then stripTrailingZeroChars ds (n - 1)
    else n
  else
    n
termination_by n

private def formatTwoOrThreeExp (eAbs : Nat) : String :=
  if eAbs ≥ 100 then
    let c100 := Char.ofNat ('0'.toNat + eAbs / 100)
    let rem := eAbs % 100
    let c10 := Char.ofNat ('0'.toNat + rem / 10)
    let c1 := Char.ofNat ('0'.toNat + rem % 10)
    String.ofList [c100, c10, c1]
  else
    let c10 := Char.ofNat ('0'.toNat + eAbs / 10)
    let c1 := Char.ofNat ('0'.toNat + eAbs % 10)
    String.ofList [c10, c1]

/-- Exact port of SQLite `3.54.1` `sqlite3FpDecode` + `%!.17g` real-to-text formatting (`sqlite3.c:33297, 38227`). -/
def sqliteRenderReal17g (rIn : Float) : String :=
  if rIn != rIn then
    "NaN"
  else if rIn == 0.0 then
    "0.0"
  else
    let neg := rIn < 0.0
    let r := if neg then -rIn else rIn
    let bits := r.toBits
    let eRaw := ((bits >>> 52) &&& 0x7ff).toNat
    if eRaw == 0x7ff then
      if neg then "-Inf" else "Inf"
    else
      let mant := bits &&& 0x000fffffffffffff
      let (v0, exp2) : UInt64 × Int :=
        if eRaw == 0 then
          let nn := countLeadingZerosU64 mant
          (mant <<< UInt64.ofNat nn, -1074 - Int.ofNat nn)
        else
          ((mant <<< 11) ||| ((1 : UInt64) <<< 63), Int.ofNat eRaw - 1086)
      let (decVal, exp10) := fp2Convert10 v0 exp2 18
      let ds0 := natToDecDigits decVal.toNat
      let n0 := ds0.size
      let iDP0 : Int := Int.ofNat n0 + exp10
      let iRound : Nat :=
        if 17 < n0 then
          if ds0.getD 15 '0' == '9' && ds0.getD 14 '0' == '9' then
            let jj := countTrailingNines ds0 14
            let v2 : UInt64 := if jj == 0 then 1 else digitsToUInt64 ds0 jj + 1
            if r == fp10Convert2 v2 (exp10 + Int.ofNat n0 - Int.ofNat jj) then jj + 1 else 17
          else if iDP0 ≥ Int.ofNat n0 ||
              (ds0.getD 15 '0' == '0' && ds0.getD 14 '0' == '0' && ds0.getD 13 '0' == '0') then
            let jj := countTrailingZerosIdx ds0 13
            let v2 := digitsToUInt64 ds0 jj
            if r == fp10Convert2 v2 (exp10 + Int.ofNat n0 - Int.ofNat jj) then jj + 1 else 17
          else
            17
        else
          17
      let (ds1, n1, iDP1) : Array Char × Nat × Int :=
        if iRound < n0 then
          let needRound := ds0.getD iRound '0' ≥ '5'
          let pref := ds0.extract 0 iRound
          if needRound then
            let (rounded, carried) := roundDigitsUp pref iRound
            (rounded, rounded.size, if carried then iDP0 + 1 else iDP0)
          else
            (pref, iRound, iDP0)
        else
          (ds0, n0, iDP0)
      let nFinal := stripTrailingZeroChars ds1 n1
      let ds := ds1.extract 0 nFinal
      let exp := iDP1 - 1
      let signStr := if neg then "-" else ""
      let isExp := exp < -4 || exp > 16
      let prec : Int := if isExp then 16 else 16 - exp
      let (intStr, jUsed, e2After) : String × Nat × Int :=
        if isExp || exp < 0 then
          if isExp then
            (String.singleton (ds.getD 0 '0'), 1, 0)
          else
            ("0", 0, exp)
        else
          let takeInt := min (exp.toNat + 1) nFinal
          let headChars := String.ofList (ds.extract 0 takeInt).toList
          let zeroPad := (exp.toNat + 1) - takeInt
          let padStr := String.ofList (List.replicate zeroPad '0')
          (headChars ++ padStr, takeInt, -1)
      let preZeroStr :=
        if e2After < -1 && prec > 0 then
          let nn := min (-1 - e2After).toNat prec.toNat
          String.ofList (List.replicate nn '0')
        else
          ""
      let remPrec : Nat :=
        if e2After < -1 && prec > 0 then
          prec.toNat - min (-1 - e2After).toNat prec.toNat
        else if prec > 0 then
          prec.toNat
        else
          0
      let fracTake := min (nFinal - jUsed) remPrec
      let fracRaw := String.ofList (ds.extract jUsed (jUsed + fracTake)).toList
      let fracCombined := preZeroStr ++ fracRaw
      let fracTrimmed :=
        let cs := fracCombined.toList.reverse.dropWhile (· == '0')
        String.ofList cs.reverse
      let fracFinal := if fracTrimmed.isEmpty then "0" else fracTrimmed
      let expSuffix :=
        if isExp then
          let eSign := if exp < 0 then "-" else "+"
          "e" ++ eSign ++ formatTwoOrThreeExp exp.natAbs
        else
          ""
      signStr ++ intStr ++ "." ++ fracFinal ++ expSuffix

/-- Apply SQLite column/expression affinity (`SqlColType`, with `.any` meaning `NONE` affinity). -/
def applySqlAffinity (colType : SqlColType) (tryForInt : Bool) (v : SqliteValue) : SqliteValue :=
  match colType with
  | .blob | .any => v
  | .text =>
    match v with
    | .int i => .text (toString i)
    | .real f => .text (sqliteRenderReal17g f)
    | other => other
  | .integer | .int =>
    match v with
    | .real f => sqliteIntegerAffinityReal f
    | .text s => applyNumericAffinityText s tryForInt
    | other => other
  | .real =>
    let v1 :=
      match v with
      | .real f => sqliteIntegerAffinityReal f
      | .text s => applyNumericAffinityText s tryForInt
      | other => other
    match v1 with
    | .int i => .real (int64ToFloatRNE i)
    | other => other

/-- Exact port of `sqlite3IntFloatCompare` (`sqlite3.c:91997`). -/
def sqliteIntFloatCompare (i : Int64) (r : Float) : Ordering :=
  if r != r then
    .gt
  else if r < -9223372036854775808.0 then
    .gt
  else if r >= 9223372036854775808.0 then
    .lt
  else
    let y := r.toInt64
    if i < y then .lt
    else if i > y then .gt
    else
      let fi := int64ToFloatRNE i
      if fi < r then .lt
      else if fi > r then .gt
      else .eq

private def cmpByteArrayLoop (a b : ByteArray) (n i : Nat) : Nat → Ordering
  | 0 => compare a.size b.size
  | fuel + 1 =>
    if i < n then
      let x := byteAt a i
      let y := byteAt b i
      if x < y then .lt
      else if x > y then .gt
      else cmpByteArrayLoop a b n (i + 1) fuel
    else
      compare a.size b.size

private def cmpByteArray (a b : ByteArray) : Ordering :=
  let n := min a.size b.size
  cmpByteArrayLoop a b n 0 n

/-- Exact port of `sqlite3MemCompare` (`sqlite3.c:92025`) using `BINARY` UTF-8 collation. -/
def sqliteMemCompare (a b : SqliteValue) : Ordering :=
  let a' := normalizeBoundParam a
  let b' := normalizeBoundParam b
  match a', b' with
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .int i1, .int i2 => compare i1 i2
  | .real r1, .real r2 =>
    if r1 < r2 then .lt
    else if r1 > r2 then .gt
    else .eq
  | .int i1, .real r2 => sqliteIntFloatCompare i1 r2
  | .real r1, .int i2 =>
    match sqliteIntFloatCompare i2 r1 with
    | .lt => .gt
    | .gt => .lt
    | .eq => .eq
  | .int _, _ => .lt
  | .real _, _ => .lt
  | _, .int _ => .gt
  | _, .real _ => .gt
  | .text s1, .text s2 => cmpByteArray s1.toUTF8 s2.toUTF8
  | .text _, .bytes _ => .lt
  | .bytes _, .text _ => .gt
  | .bytes b1, .bytes b2 => cmpByteArray b1 b2

/-- Strict bitwise equality on `SqliteValue` (`Float.toBits` for `.real`, distinguishing `-0.0` from `+0.0`). -/
def sqliteValueBitEq (a b : SqliteValue) : Bool :=
  match a, b with
  | .null, .null => true
  | .int x, .int y => x == y
  | .real x, .real y => x.toBits == y.toBits
  | .text x, .text y => x == y
  | .bytes x, .bytes y => x == y
  | _, _ => false

private def sqliteRowBitEqAux (a b : SqliteRow) (i : Nat) : Nat → Bool
  | 0 => true
  | f + 1 =>
    if i < a.size then
      sqliteValueBitEq (a.getD i .null) (b.getD i .null) && sqliteRowBitEqAux a b (i + 1) f
    else true

/-- Strict bitwise equality on two result rows. -/
def sqliteRowBitEq (a b : SqliteRow) : Bool :=
  a.size == b.size && sqliteRowBitEqAux a b 0 a.size

private def sqliteValueBitCompare (a b : SqliteValue) : Ordering :=
  match a, b with
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .int x, .int y => compare x y
  | .int _, _ => .lt
  | _, .int _ => .gt
  | .real x, .real y => compare x.toBits y.toBits
  | .real _, _ => .lt
  | _, .real _ => .gt
  | .text x, .text y => cmpByteArray x.toUTF8 y.toUTF8
  | .text _, .bytes _ => .lt
  | .bytes _, .text _ => .gt
  | .bytes x, .bytes y => cmpByteArray x y

private def sqliteRowBitCompareAux (a b : SqliteRow) (i : Nat) : Nat → Ordering
  | 0 => .eq
  | f + 1 =>
    if i < a.size then
      match sqliteValueBitCompare (a.getD i .null) (b.getD i .null) with
      | .eq => sqliteRowBitCompareAux a b (i + 1) f
      | ord => ord
    else .eq

private def sqliteRowBitCompare (a b : SqliteRow) : Ordering :=
  match compare a.size b.size with
  | .eq => sqliteRowBitCompareAux a b 0 a.size
  | ord => ord

private def isIntegerPrimaryKey (col : ColDef) : Bool :=
  col.colType == .integer && col.primaryKey

private def mustBeIntValue (v : SqliteValue) : Option Int64 :=
  match normalizeBoundParam v with
  | .int i => some i
  | .real r =>
    if r >= -9223372036854775808.0 && r < 9223372036854775808.0 then
      let ix := sqliteRealToI64 r
      if int64ToFloatRNE ix == r then some ix else none
    else
      none
  | .text s =>
    match applyNumericAffinityText s true with
    | .int i => some i
    | _ => none
  | _ => none

/-- Coerce and validate a single non-auto-rowid column value during `INSERT`/`UPDATE`. -/
def coerceForColumn (strict : Bool) (col : ColDef) (rawVal : SqliteValue) :
    Except SqliteError SqliteValue :=
  let v := normalizeBoundParam rawVal
  if isIntegerPrimaryKey col then
    match mustBeIntValue v with
    | some i => .ok (.int i)
    | none => .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
  else if v == .null then
    if col.notNull || (strict && col.primaryKey) then
      .error (mapRawError (.constraint 1299 s!"NOT NULL constraint failed: {col.name}"))
    else
      .ok .null
  else
    let effType := if !strict && col.colType == .any then .int else col.colType
    let coerced := applySqlAffinity effType true v
    if !strict then
      .ok coerced
    else
      let okType :=
        match col.colType, coerced with
        | .integer, .int _ => true
        | .int, .int _ => true
        | .real, .real _ => true
        | .text, .text _ => true
        | .blob, .bytes _ => true
        | .any, _ => true
        | _, _ => false
      if okType then
        .ok coerced
      else
        .error (mapRawError (.constraint 3091 s!"cannot store value in STRICT column {col.name}"))

/-- Stored table schema and row multiset (sorted ascending by internal `rowid`). -/
structure TableData where
  /-- Original table name. -/
  name : String
  /-- Ordered column definitions. -/
  cols : List ColDef
  /-- Whether `STRICT` was specified. -/
  strict : Bool
  /-- Whether any column is `INTEGER PRIMARY KEY AUTOINCREMENT`. -/
  hasAutoincrement : Bool := false
  /-- High-water `sqlite_sequence` value when `hasAutoincrement = true`. -/
  maxAutoRowid : Int64 := 0
  /-- Rows `(rowid, values)` ordered by `rowid`. -/
  rows : List (Int64 × Array SqliteValue) := []
  deriving Repr, BEq

/-- Database catalog mapping lowercase table names to `TableData`. -/
structure DbCatalog where
  /-- Association list keyed by `asciiLower name`. -/
  tables : List (String × TableData) := []
  deriving Repr, BEq

/-- Abstract filesystem node for file-backed SQLite databases in `SqliteWorldState`. -/
inductive FileNode where
  /-- Normal SQLite database file with WAL flag, OS read-only bit, commit epoch, and committed catalog. -/
  | dbFile (isWal : Bool) (osReadOnly : Bool) (commitEpoch : Nat) (committed : DbCatalog)
  /-- Non-SQLite/corrupt file header (`SQLITE_NOTADB`). -/
  | corruptFile
  /-- Directory at path (`SQLITE_CANTOPEN`). -/
  | directory
  deriving Repr, BEq

/-- Per-connection transaction state in `SqliteWorldState`. -/
inductive ConnTxState where
  /-- No explicit transaction active. -/
  | autocommit
  /-- `BEGIN DEFERRED` transaction, optionally holding a pinned read snapshot `(epoch, catalog)`. -/
  | deferred (readSnap? : Option (Nat × DbCatalog))
  /-- Active write transaction (`BEGIN IMMEDIATE` or upgraded deferred) with staged catalog. -/
  | write (baseEpoch : Nat) (staged : DbCatalog)
  deriving Repr, BEq

/-- Storage backing for an open SQLite connection. -/
inductive ConnBacking where
  /-- Isolated ephemeral `:memory:` database. -/
  | memory (committed : DbCatalog) (commitEpoch : Nat)
  /-- Shared in-memory store (`memdb` `/name` or `?cache=shared` memory URI) identified by `storeKey`. -/
  | sharedMemory (storeKey : String)
  /-- Shared file-backed database identified by `canonicalPath`. -/
  | file (canonicalPath : String)
  deriving Repr, BEq

/-- Open SQLite connection record in `SqliteWorldState`. -/
structure ConnState where
  /-- Unique `DbHandle.id`. -/
  id : UInt64
  /-- Memory or file backing. -/
  backing : ConnBacking
  /-- Whether the connection is effectively read-only (`cfg.readOnly || osReadOnly`). -/
  effectiveReadOnly : Bool
  /-- Whether `PRAGMA foreign_keys = ON` is active on this connection. -/
  foreignKeys : Bool
  /-- Current transaction state. -/
  tx : ConnTxState := .autocommit
  /-- Whether the active write transaction has modified the catalog (`M8`). -/
  writeDirty : Bool := false
  /-- Whether a failed `COMMIT` promoted this connection to a `PENDING` lock (`M9`). -/
  pendingLock : Bool := false
  /-- Per-connection cached schema table names (`DB_SchemaLoaded`) when loaded. -/
  schemaCache? : Option (List String) := none
  /-- Whether the active write transaction modified schema DDL (`DBFLAG_SchemaChange`). -/
  schemaDirty : Bool := false
  /-- Pinned WAL read snapshot `(epoch, catalog)` while an autocommit scan holds a read lock. -/
  readSnap? : Option (Nat × DbCatalog) := none
  /-- VFS name (`"unix"`, `"unix-dotfile"`, `"unix-none"`, `"unix-excl"`, `"memdb"`). -/
  vfsName : String := "unix"
  /-- Whether OS-level pager locking is disabled (`unix-none`, `nolock=1`, or `immutable=1`). -/
  noLock : Bool := false
  /-- Whether `immutable=1` (`tempFile = 1` on real file, bypassing WAL open). -/
  immutableUri : Bool := false
  /-- Shared-cache `BtShared` identity `(vfsName, fullName)` when `?cache=shared` is active. -/
  sharedGroup? : Option (String × String) := none
  /-- Lowercased table names (`"*"` for schema DDL) write-locked in the active shared-cache write transaction. -/
  sharedWriteTables : List String := []
  /-- Lowercased table names read-locked in the active shared-cache transaction or active scan. -/
  sharedReadTables : List String := []
  /-- Whether an active shared-cache write transaction hit a table-lock conflict (`BTS_PENDING`). -/
  sharedPending : Bool := false
  /-- Whether `readonly_shm=1` is active on this connection's pager. -/
  readonlyShm : Bool := false
  /-- Whether WAL shared-memory (`<db>-shm`) has been attached by this connection's pager. -/
  shmAttached : Bool := false
  deriving Repr, BEq

/-- Live-cursor row entry tagged with a unique monotonic `uid` within the scan. -/
structure RelLiveEntry where
  /-- Unique row instance identifier within this cursor scan. -/
  uid : Nat
  /-- Rowid in `TableData.rows`. -/
  rid : Int64
  /-- Full table column values of the row. -/
  vals : Array SqliteValue
  /-- Projected `SELECT` result row for this table row. -/
  projRow : SqliteRow
  deriving BEq

/-- Compressed consumption obligation recording `demand` steps each picking a distinct `uid` from `candUids`. -/
structure RelConsumeGroup where
  /-- Candidate `RelLiveEntry.uid`s eligible at the step(s). -/
  candUids : List Nat
  /-- Number of steps that consumed from `candUids`. -/
  demand : Nat
  deriving BEq

/-- Execution branch state for relational `Raw` `SELECT` stepping across sorter and live-cursor outcomes. -/
structure RelBranch where
  /-- Mode lock: `none` until DML/ROLLBACK separates sorter vs live cursor, `some true` for sorter, `some false` for live. -/
  isSorter? : Option Bool := none
  /-- Remaining unyielded rows from the initial `step 0` snapshot (for sorter or unmutated cursor). -/
  sorterPool : List (Int64 × Array SqliteValue × SqliteRow) := []
  /-- Next fresh `uid` for newly inserted or updated live rows. -/
  nextUid : Nat := 0
  /-- Current live-cursor candidate rows `(uid, rid, vals, projRow)`. -/
  liveEntries : List RelLiveEntry := []
  /-- `uid`s of initial-snapshot rows still unchanged in the table that a live cursor must not skip before EOF. -/
  mustUids : List Nat := []
  /-- Consumed live-cursor row groups `(candUids, demand)` accumulated across steps. -/
  consumedGroups : List RelConsumeGroup := []
  /-- Original row values of the last yielded row (for `ORDER BY` monotonicity in live mode). -/
  lastOrig? : Option (Array SqliteValue) := none
  /-- Remaining `LIMIT` row count when bounded. -/
  remLimit? : Option Nat := none
  /-- Schema metadata of the scanned table (rows empty). -/
  tblSchema : TableData := { name := "", cols := [], strict := false }
  /-- `mutGen` when `liveEntries` was last synced to the table. -/
  syncedGen : Nat := 0
  /-- Target table's rows at last sync, to detect newly inserted, deleted, or updated rows. -/
  lastTblRows : List (Int64 × Array SqliteValue) := []
  deriving BEq

/-- In-flight prepared statement entry in `SqliteWorldState`. -/
structure ModelStmtState where
  /-- Public statement handle. -/
  handle : StmtHandle
  /-- Parsed curated SQL AST. -/
  stmt : SqlStmt
  /-- Expected `?` parameter count. -/
  paramCount : Nat
  /-- Bound parameters once `bind` succeeds. -/
  boundParams? : Option (Array SqliteValue) := none
  /-- Next result row index to yield. -/
  stepIdx : Nat := 0
  /-- Materialized result rows once stepped. -/
  resultRows? : Option (Array SqliteRow) := none
  /-- Whether an active table-scanning cursor holds a `SHARED` read lock. -/
  holdsReadLock : Bool := false
  /-- Active candidate cursor branches for relational `Raw` `SELECT` verification. -/
  relBranches : List RelBranch := []
  /-- Whether an enclosing schema-changing `ROLLBACK` may have aborted this cursor (`SQLITE_ABORT_ROLLBACK`). -/
  rollbackMayAbort : Bool := false
  /-- Sticky error produced during step, if any. -/
  err? : Option SqliteError := none
  deriving BEq

/-- Complete pure-Lean world state modeling filesystem nodes, connections, transactions, and statements. -/
structure SqliteWorldState where
  /-- Next monotonic `DbHandle.id`. -/
  nextDbId : UInt64 := 1
  /-- Next monotonic `StmtHandle.id`. -/
  nextStmtId : UInt64 := 1
  /-- Known existing parent directories (default `["/"]`). -/
  existingDirs : List String := ["/"]
  /-- Symbolic links `(linkPath, targetPath)` resolved during `openDb`. -/
  symlinks : List (String × String) := []
  /-- File nodes keyed by path string. -/
  files : List (String × FileNode) := []
  /-- Currently open database connections. -/
  conns : List ConnState := []
  /-- Currently active prepared statements. -/
  stmts : List ModelStmtState := []
  /-- Monotonic counter incremented on connection/catalog updates to invalidate cursor caches. -/
  mutGen : Nat := 0
  /-- Optional current working directory used for `maxUnixPathnameBytes` resolution on relative paths. -/
  cwd : String := ""
  /-- Reference-counted shared in-memory stores `(storeKey, commitEpoch, committed)` for named `memdb` and `?cache=shared`. -/
  memStores : List (String × Nat × DbCatalog) := []
  deriving BEq

private def lookupTable? (cat : DbCatalog) (name : String) : Option TableData :=
  let key := asciiLower name
  (cat.tables.find? fun p => p.1 == key).map (·.2)

private def setTable (cat : DbCatalog) (tbl : TableData) : DbCatalog :=
  let key := asciiLower tbl.name
  let filtered := cat.tables.filter (fun p => p.1 != key)
  { tables := filtered ++ [(key, tbl)] }

private def findColIdx? (cols : List ColDef) (name : String) : Option (Nat × ColDef) :=
  let key := asciiLower name
  let rec go (i : Nat) : List ColDef → Option (Nat × ColDef)
    | [] => none
    | c :: rest => if asciiLower c.name == key then some (i, c) else go (i + 1) rest
  go 0 cols

private def evalScalar (params : Array SqliteValue) : ScalarExpr → SqliteValue
  | .litNull => .null
  | .litInt v => .int v
  | .litText s => .text s
  | .litBlob b => .bytes b
  | .param idx => normalizeBoundParam (params.getD idx .null)

private def evalVal (tbl? : Option TableData) (rowVals : Array SqliteValue)
    (params : Array SqliteValue) : ValExpr → SqliteValue × Option SqlColType
  | .scalar e => (evalScalar params e, none)
  | .col name =>
    match tbl? with
    | none => (.null, none)
    | some tbl =>
      match findColIdx? tbl.cols name with
      | none => (.null, none)
      | some (idx, cd) =>
        let raw := rowVals.getD idx .null
        let effType :=
          if isIntegerPrimaryKey cd then some .integer
          else if !tbl.strict && cd.colType == .any then some .int
          else some cd.colType
        (raw, effType)

private def isNumericSqlType : SqlColType → Bool
  | .integer | .int | .real => true
  | _ => false

private def compareAffinityPair (aff1? aff2? : Option SqlColType) : Option SqlColType :=
  match aff1?, aff2? with
  | some t1, some t2 =>
    if isNumericSqlType t1 || isNumericSqlType t2 then
      some .integer
    else if t1 == .blob || t1 == .any || t2 == .blob || t2 == .any then
      none
    else
      some .text
  | some t1, none =>
    if t1 == .blob || t1 == .any then none else some t1
  | none, some t2 =>
    if t2 == .blob || t2 == .any then none else some t2
  | none, none => none

private def applyCompareAff (aff? : Option SqlColType) (v : SqliteValue) : SqliteValue :=
  match aff?, v with
  | some .integer, .text s => applyNumericAffinityText s false
  | some .int, .text s => applyNumericAffinityText s false
  | some .real, .text s => applyNumericAffinityText s false
  | some .text, .int i => .text (toString i)
  | some .text, .real f => .text (sqliteRenderReal17g f)
  | _, other => other

private inductive SqlTri where
  | tTrue
  | tFalse
  | tUnknown
  deriving Repr, BEq

private def triNot : SqlTri → SqlTri
  | .tTrue => .tFalse
  | .tFalse => .tTrue
  | .tUnknown => .tUnknown

private def triAnd : SqlTri → SqlTri → SqlTri
  | .tFalse, _ => .tFalse
  | _, .tFalse => .tFalse
  | .tTrue, .tTrue => .tTrue
  | _, _ => .tUnknown

private def triOr : SqlTri → SqlTri → SqlTri
  | .tTrue, _ => .tTrue
  | _, .tTrue => .tTrue
  | .tFalse, .tFalse => .tFalse
  | _, _ => .tUnknown

private def evalCmpOp (op : CmpOp) (v1 v2 : SqliteValue) : Bool :=
  let ord := sqliteMemCompare v1 v2
  match op with
  | .eq => ord == .eq
  | .ne => ord != .eq
  | .lt => ord == .lt
  | .le => ord != .gt
  | .gt => ord == .gt
  | .ge => ord != .lt

private inductive WhereEvalTask where
  | eval (w : WhereExpr)
  | doNot
  | andRight (r : WhereExpr)
  | andWait (v1 : SqlTri)
  | orRight (r : WhereExpr)
  | orWait (v1 : SqlTri)

private def evalWhereStep (tbl : TableData) (rowVals : Array SqliteValue)
    (params : Array SqliteValue) :
    Nat → List WhereEvalTask → List SqlTri → SqlTri
  | 0, _, vals => vals.headD .tUnknown
  | _, [], vals => vals.headD .tUnknown
  | fuel + 1, task :: rest, vals =>
    match task with
    | .eval (.isNull negated ve) =>
      let (v, _) := evalVal (some tbl) rowVals params ve
      let isN := v == .null
      let tri := if (if negated then !isN else isN) then .tTrue else .tFalse
      evalWhereStep tbl rowVals params fuel rest (tri :: vals)
    | .eval (.cmp op lhs rhs) =>
      let (v1, t1?) := evalVal (some tbl) rowVals params lhs
      let (v2, t2?) := evalVal (some tbl) rowVals params rhs
      let tri :=
        if v1 == .null || v2 == .null then
          .tUnknown
        else
          let aff? := compareAffinityPair t1? t2?
          let v1' := applyCompareAff aff? v1
          let v2' := applyCompareAff aff? v2
          if evalCmpOp op v1' v2' then .tTrue else .tFalse
      evalWhereStep tbl rowVals params fuel rest (tri :: vals)
    | .eval (.not sub) =>
      evalWhereStep tbl rowVals params fuel (.eval sub :: .doNot :: rest) vals
    | .eval (.and l r) =>
      evalWhereStep tbl rowVals params fuel (.eval l :: .andRight r :: rest) vals
    | .eval (.or l r) =>
      evalWhereStep tbl rowVals params fuel (.eval l :: .orRight r :: rest) vals
    | .doNot =>
      match vals with
      | v :: vrest => evalWhereStep tbl rowVals params fuel rest (triNot v :: vrest)
      | [] => .tUnknown
    | .andRight r =>
      match vals with
      | v1 :: vrest =>
        if v1 == .tFalse then
          evalWhereStep tbl rowVals params fuel rest (.tFalse :: vrest)
        else
          evalWhereStep tbl rowVals params fuel (.eval r :: .andWait v1 :: rest) vrest
      | [] => .tUnknown
    | .andWait v1 =>
      match vals with
      | v2 :: vrest => evalWhereStep tbl rowVals params fuel rest (triAnd v1 v2 :: vrest)
      | [] => .tUnknown
    | .orRight r =>
      match vals with
      | v1 :: vrest =>
        if v1 == .tTrue then
          evalWhereStep tbl rowVals params fuel rest (.tTrue :: vrest)
        else
          evalWhereStep tbl rowVals params fuel (.eval r :: .orWait v1 :: rest) vrest
      | [] => .tUnknown
    | .orWait v1 =>
      match vals with
      | v2 :: vrest => evalWhereStep tbl rowVals params fuel rest (triOr v1 v2 :: vrest)
      | [] => .tUnknown

private def evalWhereTri (tbl : TableData) (rowVals : Array SqliteValue)
    (params : Array SqliteValue) (w : WhereExpr) : SqlTri :=
  evalWhereStep tbl rowVals params (maxCuratedSqlBytes * 4 + 8) [.eval w] []

private def evalWhere (tbl : TableData) (rowVals : Array SqliteValue)
    (params : Array SqliteValue) (w? : Option WhereExpr) : Bool :=
  match w? with
  | none => true
  | some w => evalWhereTri tbl rowVals params w == .tTrue

private def validateWhereColsLoop (tbl : TableData) : Nat → List WhereExpr → Except SqliteError Unit
  | 0, _ => .ok ()
  | _, [] => .ok ()
  | fuel + 1, w :: rest =>
    match w with
    | .cmp _ l r => do
      match l with
      | .col c =>
        if (findColIdx? tbl.cols c).isNone then
          .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
        else .ok ()
      | .scalar _ => .ok ()
      match r with
      | .col c =>
        if (findColIdx? tbl.cols c).isNone then
          .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
        else .ok ()
      | .scalar _ => .ok ()
      validateWhereColsLoop tbl fuel rest
    | .isNull _ e => do
      match e with
      | .col c =>
        if (findColIdx? tbl.cols c).isNone then
          .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
        else .ok ()
      | .scalar _ => .ok ()
      validateWhereColsLoop tbl fuel rest
    | .not sub => validateWhereColsLoop tbl fuel (sub :: rest)
    | .and l r => validateWhereColsLoop tbl fuel (l :: r :: rest)
    | .or l r => validateWhereColsLoop tbl fuel (l :: r :: rest)

private def validateWhereCols (tbl : TableData) (w : WhereExpr) : Except SqliteError Unit :=
  validateWhereColsLoop tbl (maxCuratedSqlBytes * 2 + 8) [w]

private def hasDuplicateColNames (cols : List String) : Option String :=
  let rec go (seen : List String) : List String → Option String
    | [] => none
    | c :: rest =>
      let lo := asciiLower c
      if seen.contains lo then some c else go (lo :: seen) rest
  go [] cols

private def hasFkTargetError (cat : DbCatalog) (selfTbl : TableData) : List ColDef → Option String
  | [] => none
  | cd :: rest =>
    match cd.references? with
    | none => hasFkTargetError cat selfTbl rest
    | some (pTabName, pColName) =>
      let pTbl? :=
        if asciiLower pTabName == asciiLower selfTbl.name then some selfTbl
        else lookupTable? cat pTabName
      match pTbl? with
      | none => some s!"no such table: {pTabName}"
      | some pTbl =>
        match findColIdx? pTbl.cols pColName with
        | none => some s!"foreign key mismatch - {selfTbl.name} referencing {pTabName}"
        | some (_, pCol) =>
          if pCol.primaryKey || pCol.unique then
            hasFkTargetError cat selfTbl rest
          else
            some s!"foreign key mismatch - {selfTbl.name} referencing {pTabName}"

private def checkAllTableFksSchema (cat : DbCatalog) (tbl : TableData) (foreignKeys : Bool)
    (onlyCols? : Option (List String) := none) : Except SqliteError Unit :=
  if !foreignKeys then .ok ()
  else
    let selfLo := asciiLower tbl.name
    let colsToCheck :=
      match onlyCols? with
      | none => tbl.cols
      | some cs =>
        let loSet := cs.map asciiLower
        tbl.cols.filter fun cd =>
          loSet.contains (asciiLower cd.name) ||
            match cd.references? with
            | some (pTab, pCol) => asciiLower pTab == selfLo && loSet.contains (asciiLower pCol)
            | none => false
    match hasFkTargetError cat tbl colsToCheck with
    | none => .ok ()
    | some msg => .error (mapRawError (.sqliteCodeError 1 msg))

private def checkReferencedByFksSchema (cat : DbCatalog) (targetTable : String)
    (foreignKeys : Bool) (onlyParentCols? : Option (List String) := none) :
    Except SqliteError Unit :=
  if !foreignKeys then .ok ()
  else
    let targetLo := asciiLower targetTable
    let rec go : List (String × TableData) → Except SqliteError Unit
      | [] => .ok ()
      | (_, tbl) :: rest =>
        let matchedCols := tbl.cols.filter fun c =>
          match c.references? with
          | some (pTab, pCol) =>
            asciiLower pTab == targetLo &&
              match onlyParentCols? with
              | none => true
              | some pcs => (pcs.map asciiLower).contains (asciiLower pCol)
          | none => false
        if !matchedCols.isEmpty then
          match hasFkTargetError cat tbl matchedCols with
          | none => go rest
          | some msg => .error (mapRawError (.sqliteCodeError 1 msg))
        else
          go rest
    go cat.tables

private def validateStmtSchema (cat : DbCatalog) (foreignKeys : Bool) :
    SqlStmt → Except SqliteError Unit
  | .createTable ifNotExists tblName cols _ =>
    match lookupTable? cat tblName with
    | some _ =>
      if ifNotExists then .ok ()
      else .error (mapRawError (.sqliteCodeError 1 s!"table {tblName} already exists"))
    | none =>
      match hasDuplicateColNames (cols.map (·.name)) with
      | some dup => .error (mapRawError (.sqliteCodeError 1 s!"duplicate column name: {dup}"))
      | none =>
        let pkCount := (cols.filter (·.primaryKey)).length
        if pkCount > 1 then
          .error (mapRawError (.sqliteCodeError 1 s!"table {tblName} has more than one primary key"))
        else
          .ok ()
  | .insert tblName cols? valRows => do
    let tbl ← match lookupTable? cat tblName with
      | some t => .ok t
      | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
    checkAllTableFksSchema cat tbl foreignKeys
    if valRows.length > 1 then
      checkReferencedByFksSchema cat tblName foreignKeys
    match cols? with
    | none =>
      for rowExprs in valRows do
        if rowExprs.length != tbl.cols.length then
          .error (mapRawError (.sqliteCodeError 1
            s!"table {tblName} has {tbl.cols.length} columns but {rowExprs.length} values were supplied"))
      .ok ()
    | some cs => do
      for c in cs do
        if (findColIdx? tbl.cols c).isNone then
          .error (mapRawError (.sqliteCodeError 1 s!"table {tblName} has no column named {c}"))
      for rowExprs in valRows do
        if rowExprs.length != cs.length then
          .error (mapRawError (.sqliteCodeError 1
            s!"{rowExprs.length} values for {cs.length} columns"))
      .ok ()
  | .select proj tbl? where? orderBy _ =>
    match tbl? with
    | none => .ok ()
    | some tblName => do
      let tbl ← match lookupTable? cat tblName with
        | some t => .ok t
        | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
      match proj with
      | .star => .ok ()
      | .items es =>
        for e in es do
          match e with
          | .col c =>
            if (findColIdx? tbl.cols c).isNone then
              .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
          | .scalar _ => .ok ()
      match where? with
      | none => .ok ()
      | some w => validateWhereCols tbl w
      for oi in orderBy do
        if (findColIdx? tbl.cols oi.col).isNone then
          .error (mapRawError (.sqliteCodeError 1 s!"no such column: {oi.col}"))
  | .update tblName assigns where? => do
    let tbl ← match lookupTable? cat tblName with
      | some t => .ok t
      | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
    let assignedCols := assigns.map (·.1)
    let loAssigned := assignedCols.map asciiLower
    let touchesOutFk := tbl.cols.any fun cd =>
      cd.references?.isSome && loAssigned.contains (asciiLower cd.name)
    let tblLo := asciiLower tblName
    let touchesInFk := cat.tables.any fun (_, childTbl) =>
      childTbl.cols.any fun cd =>
        match cd.references? with
        | some (pTab, pCol) => asciiLower pTab == tblLo && loAssigned.contains (asciiLower pCol)
        | none => false
    if touchesOutFk || touchesInFk then
      checkAllTableFksSchema cat tbl foreignKeys (some assignedCols)
      checkReferencedByFksSchema cat tblName foreignKeys none
    for (c, _) in assigns do
      if (findColIdx? tbl.cols c).isNone then
        .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
    match where? with
    | none => .ok ()
    | some w => validateWhereCols tbl w
  | .delete tblName where? => do
    let tbl ← match lookupTable? cat tblName with
      | some t => .ok t
      | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
    checkAllTableFksSchema cat tbl foreignKeys
    checkReferencedByFksSchema cat tblName foreignKeys
    match where? with
    | none => .ok ()
    | some w => validateWhereCols tbl w
  | .begin _ | .commit | .rollback => .ok ()

private def isReadOnlyStmt : SqlStmt → Bool
  | .select _ _ _ _ _ | .begin .deferred | .commit | .rollback => true
  | _ => false

private def insertSortedRowAux (rid : Int64) (vals : Array SqliteValue)
    (accRev : List (Int64 × Array SqliteValue)) :
    List (Int64 × Array SqliteValue) → List (Int64 × Array SqliteValue)
  | [] => accRev.reverseAux [(rid, vals)]
  | (r0, v0) :: rest =>
    if rid < r0 then accRev.reverseAux ((rid, vals) :: (r0, v0) :: rest)
    else insertSortedRowAux rid vals ((r0, v0) :: accRev) rest

private def insertSortedRow (rid : Int64) (vals : Array SqliteValue)
    (rows : List (Int64 × Array SqliteValue)) : List (Int64 × Array SqliteValue) :=
  insertSortedRowAux rid vals [] rows

private def checkColUniqueness (tbl : TableData) (newVals : Array SqliteValue) :
    Except SqliteError Unit :=
  let rec indexCols (i : Nat) (acc : List (Nat × ColDef)) : List ColDef → List (Nat × ColDef)
    | [] => acc
    | cd :: rest => indexCols (i + 1) ((i, cd) :: acc) rest
  let rec go : List (Nat × ColDef) → Except SqliteError Unit
    | [] => .ok ()
    | (i, cd) :: rest =>
      if cd.unique || (cd.primaryKey && !isIntegerPrimaryKey cd) then
        let nv := newVals.getD i .null
        if nv == .null then
          go rest
        else
          let dup := tbl.rows.any fun (_, rVals) =>
            let ov := rVals.getD i .null
            ov != .null && sqliteMemCompare nv ov == .eq
          if dup then
            let errCode : UInt32 := if cd.primaryKey then 1555 else 2067
            .error (mapRawError (.constraint errCode s!"UNIQUE constraint failed: {tbl.name}.{cd.name}"))
          else
            go rest
      else
        go rest
  go (indexCols 0 [] tbl.cols)

private def indexFkAff (pTbl : TableData) (pCol : ColDef) : SqlColType :=
  if !pTbl.strict && pCol.colType == .any then .int
  else if pCol.colType == .real || pCol.colType == .integer then .int
  else pCol.colType

private def colStorageAff (tbl : TableData) (col : ColDef) : SqlColType :=
  if isIntegerPrimaryKey col then .integer
  else if !tbl.strict && col.colType == .any then .int
  else col.colType

private def mergeSortedRowsAux (accRev : List (Int64 × Array SqliteValue)) :
    List (Int64 × Array SqliteValue) → List (Int64 × Array SqliteValue) →
      List (Int64 × Array SqliteValue)
  | [], bs => accRev.reverseAux bs
  | as, [] => accRev.reverseAux as
  | a :: ar, b :: br =>
    if b.1 < a.1 then mergeSortedRowsAux (b :: accRev) (a :: ar) br
    else mergeSortedRowsAux (a :: accRev) ar (b :: br)

private def mergeSortedRows (xs ys : List (Int64 × Array SqliteValue)) :
    List (Int64 × Array SqliteValue) :=
  mergeSortedRowsAux [] xs ys

private def mergeSortedFuelAux {α : Type} (lt : α → α → Bool) (accRev : List α) :
    Nat → List α → List α → List α
  | 0, xs, ys => accRev.reverseAux (xs ++ ys)
  | _ + 1, [], ys => accRev.reverseAux ys
  | _ + 1, xs, [] => accRev.reverseAux xs
  | f + 1, x :: xs, y :: ys =>
    if !lt y x then mergeSortedFuelAux lt (x :: accRev) f xs (y :: ys)
    else mergeSortedFuelAux lt (y :: accRev) f (x :: xs) ys

private def mergeSortedFuel {α : Type} (lt : α → α → Bool) (fuel : Nat) (xs ys : List α) : List α :=
  mergeSortedFuelAux lt [] fuel xs ys

private def mergePairsAux {α : Type} (lt : α → α → Bool) (accRev : List (List α)) :
    List (List α) → List (List α)
  | a :: b :: rest =>
    mergePairsAux lt (mergeSortedFuel lt (a.length + b.length + 1) a b :: accRev) rest
  | [a] => (a :: accRev).reverse
  | [] => accRev.reverse

private def mergePairs {α : Type} (lt : α → α → Bool) (xs : List (List α)) : List (List α) :=
  mergePairsAux lt [] xs

private def mergeAllFuel {α : Type} (lt : α → α → Bool) : Nat → List (List α) → List α
  | 0, xs => xs.flatten
  | _, [] => []
  | _, [x] => x
  | f + 1, xs => mergeAllFuel lt f (mergePairs lt xs)

private def sortList {α : Type} (lt : α → α → Bool) (xs : List α) : List α :=
  mergeAllFuel lt (xs.length + 1) (xs.map fun x => [x])

private def uniqueValueHash (v : SqliteValue) : UInt64 :=
  match normalizeBoundParam v with
  | .null => 0
  | .int i => mixHash 1 (hash i)
  | .real r =>
    if r != r then 2
    else if r == 0.0 then mixHash 1 (hash (0 : Int64))
    else if r >= -9223372036854775808.0 && r < 9223372036854775808.0 && int64ToFloatRNE r.toInt64 == r then
      mixHash 1 (hash r.toInt64)
    else mixHash 3 (hash r.toBits)
  | .text s => mixHash 4 (hash s)
  | .bytes b => b.foldl (fun h x => h * 1315423911 + x.toUInt64) 5

private def pickSmallestUnusedPos62By (used : Int64 → Bool)
    (totalCount : Nat) (startCand : Int64 := 1) : Except SqliteError Int64 :=
  let cand0 := if startCand < 1 then 1 else startCand
  let rec go (cand : Int64) : Nat → Except SqliteError Int64
    | 0 => .error (mapRawError (.ioFailure 13 "database or disk is full"))
    | f + 1 =>
      if used cand then
        let nextCand := if cand >= Int64.maxValue then 1 else cand + 1
        go nextCand f
      else
        .ok cand
  go cand0 (totalCount + 1024)

private def findIpkColIdx? (i : Nat) : List ColDef → Option Nat
  | [] => none
  | cd :: rest => if isIntegerPrimaryKey cd then some i else findIpkColIdx? (i + 1) rest

private def allocInsertRowid (tbl : TableData) (ipkIdx? : Option Nat) (rawByCol : Array SqliteValue)
    (maxExisting? : Option Int64) (curMaxAuto : Int64) (used : Int64 → Bool)
    (totalCount : Nat) (fallbackCand : Int64 := 1) :
    Except SqliteError (Int64 × Int64 × Array SqliteValue) :=
  let nextAuto? : Option Int64 := match maxExisting? with
    | none => some (1 : Int64)
    | some m => if m ≥ Int64.maxValue then none else some (m + 1)
  match ipkIdx? with
  | none =>
    if tbl.hasAutoincrement then
      match nextAuto? with
      | none => .error (mapRawError (.ioFailure 13 "database or disk is full"))
      | some base =>
        if curMaxAuto == Int64.maxValue then
          .error (mapRawError (.ioFailure 13 "database or disk is full"))
        else
          let cand := if base < curMaxAuto + 1 then curMaxAuto + 1 else base
          .ok (cand, cand, rawByCol)
    else
      match nextAuto? with
      | some base => .ok (base, curMaxAuto, rawByCol)
      | none => (pickSmallestUnusedPos62By used totalCount fallbackCand).map fun p => (p, curMaxAuto, rawByCol)
  | some ipkIdx =>
    let ipkRaw := normalizeBoundParam (rawByCol.getD ipkIdx .null)
    if ipkRaw == .null then
      if tbl.hasAutoincrement then
        match nextAuto? with
        | none => .error (mapRawError (.ioFailure 13 "database or disk is full"))
        | some base =>
          if curMaxAuto == Int64.maxValue then
            .error (mapRawError (.ioFailure 13 "database or disk is full"))
          else
            let cand := if base < curMaxAuto + 1 then curMaxAuto + 1 else base
            .ok (cand, cand, rawByCol.set! ipkIdx (.int cand))
      else
        match nextAuto? with
        | some base => .ok (base, curMaxAuto, rawByCol.set! ipkIdx (.int base))
        | none =>
          (pickSmallestUnusedPos62By used totalCount fallbackCand).map fun p =>
            (p, curMaxAuto, rawByCol.set! ipkIdx (.int p))
    else
      match mustBeIntValue ipkRaw with
      | none => .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
      | some rId =>
        let newMax := if tbl.hasAutoincrement && rId > curMaxAuto then rId else curMaxAuto
        .ok (rId, newMax, rawByCol.set! ipkIdx (.int rId))

private def validateNotNullCols (tbl : TableData) (valsWithRid : Array SqliteValue) :
    Except SqliteError Unit :=
  let rec checkNn (idx : Nat) : List ColDef → Except SqliteError Unit
    | [] => .ok ()
    | cd :: rest =>
      if !isIntegerPrimaryKey cd then
        let rawV := normalizeBoundParam (valsWithRid.getD idx .null)
        if rawV == .null && (cd.notNull || (tbl.strict && cd.primaryKey)) then
          .error (mapRawError (.constraint 1299 s!"NOT NULL constraint failed: {cd.name}"))
        else checkNn (idx + 1) rest
      else checkNn (idx + 1) rest
  checkNn 0 tbl.cols

private def coerceInsertedCols (tbl : TableData) (valsWithRid : Array SqliteValue) :
    Except SqliteError (Array SqliteValue) :=
  let rec coerceAll (idx : Nat) (acc : Array SqliteValue) : List ColDef → Except SqliteError (Array SqliteValue)
    | [] => .ok acc
    | cd :: rest =>
      if isIntegerPrimaryKey cd then
        coerceAll (idx + 1) (acc.push (valsWithRid.getD idx .null)) rest
      else do
        let c ← coerceForColumn tbl.strict cd (valsWithRid.getD idx .null)
        coerceAll (idx + 1) (acc.push c) rest
  coerceAll 0 (Array.mkEmpty tbl.cols.length) tbl.cols

private def execInsertSinglePure (tbl : TableData) (cols? : Option (List String))
    (tup : List ScalarExpr) (params : Array SqliteValue) :
    Except (SqliteError × Bool × TableData) (TableData × Array (Int64 × Array SqliteValue)) := do
  let rawByCol ← match cols? with
    | none =>
      if tup.length != tbl.cols.length then
        .error (mapRawError (.sqliteCodeError 1
          s!"table {tbl.name} has {tbl.cols.length} columns but {tup.length} values were supplied"),
          false, tbl)
      else
        .ok (tup.map (evalScalar params)).toArray
    | some cs =>
      let rec fill (remCols : List String) (remExprs : List ScalarExpr)
          (seenNonIpk : List Nat) (arr : Array SqliteValue) : Except SqliteError (Array SqliteValue) :=
        match remCols, remExprs with
        | [], [] => .ok arr
        | c :: cs', e :: es' =>
          match findColIdx? tbl.cols c with
          | none => .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
          | some (idx, cd) =>
            let val := evalScalar params e
            if isIntegerPrimaryKey cd then fill cs' es' seenNonIpk (arr.set! idx val)
            else if seenNonIpk.contains idx then fill cs' es' seenNonIpk arr
            else fill cs' es' (idx :: seenNonIpk) (arr.set! idx val)
        | _, _ => .error (mapRawError (.sqliteCodeError 1 "column count mismatch"))
      match fill cs tup [] (Array.replicate tbl.cols.length (.null : SqliteValue)) with
      | .ok a => .ok a
      | .error e => .error (e, false, tbl)
  let ipkIdx? := findIpkColIdx? 0 tbl.cols
  let maxExisting? := tbl.rows.foldl (fun acc (rid, _) =>
    match acc with | none => some rid | some m => some (if rid > m then rid else m)) none
  let usedRid : Int64 → Bool := fun r => tbl.rows.any (fun row => row.1 == r)
  let (rid, nextMaxAuto, valsWithRid) ←
    match allocInsertRowid tbl ipkIdx? rawByCol maxExisting? tbl.maxAutoRowid
        usedRid tbl.rows.length with
    | .ok v => .ok v
    | .error e => .error (e, false, tbl)
  match validateNotNullCols tbl valsWithRid with
  | .error e => .error (e, false, tbl)
  | .ok () =>
    if usedRid rid then
      .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"), false, tbl)
    else
      let finalVals ← match coerceInsertedCols tbl valsWithRid with
        | .ok a => .ok a
        | .error e => .error (e, false, tbl)
      match checkColUniqueness tbl finalVals with
      | .error e => .error (e, false, tbl)
      | .ok () =>
        let tbl' := { tbl with maxAutoRowid := nextMaxAuto, rows := insertSortedRow rid finalVals tbl.rows }
        .ok (tbl', #[(rid, finalVals)])

private def buildInsertColMap? (tbl : TableData) (cols? : Option (List String)) :
    Except SqliteError (Option (Array (Nat × Bool))) :=
  match cols? with
  | none => .ok none
  | some cs =>
    let rec mapCols (rem : List String) (seenNonIpk : Std.HashSet Nat)
        (acc : Array (Nat × Bool)) : Except SqliteError (Array (Nat × Bool)) :=
      match rem with
      | [] => .ok acc
      | c :: rest =>
        match findColIdx? tbl.cols c with
        | none => .error (mapRawError (.sqliteCodeError 1 s!"no such column: {c}"))
        | some (idx, cd) =>
          if isIntegerPrimaryKey cd then
            mapCols rest seenNonIpk (acc.push (idx, true))
          else if seenNonIpk.contains idx then
            mapCols rest seenNonIpk (acc.push (idx, false))
          else
            mapCols rest (seenNonIpk.insert idx) (acc.push (idx, true))
    mapCols cs {} #[]

private def evalTupleByColMap (tbl : TableData) (colMap? : Option (Array (Nat × Bool)))
    (tup : List ScalarExpr) (params : Array SqliteValue) : Except SqliteError (Array SqliteValue) :=
  match colMap? with
  | none =>
    if tup.length != tbl.cols.length then
      .error (mapRawError (.sqliteCodeError 1
        s!"table {tbl.name} has {tbl.cols.length} columns but {tup.length} values were supplied"))
    else
      .ok (tup.map (evalScalar params)).toArray
  | some cmap =>
    if tup.length != cmap.size then
      .error (mapRawError (.sqliteCodeError 1 "column count mismatch"))
    else
      Id.run do
        let mut arr := Array.replicate tbl.cols.length (.null : SqliteValue)
        let mut remE := tup
        for (cIdx, writeIt) in cmap do
          match remE with
          | [] => break
          | e :: es =>
            if writeIt then
              arr := arr.set! cIdx (evalScalar params e)
            remE := es
        return .ok arr

private def execInsertBatchFast (tbl : TableData) (cols? : Option (List String))
    (tuples : List (List ScalarExpr)) (params : Array SqliteValue) :
    Except (SqliteError × Bool × TableData) (TableData × Array (Int64 × Array SqliteValue)) :=
  match tuples with
  | [] => .ok (tbl, #[])
  | [tup] => execInsertSinglePure tbl cols? tup params
  | _ => do
  let ipkIdx? := findIpkColIdx? 0 tbl.cols
  let colMap? ← match buildInsertColMap? tbl cols? with
    | .ok m => .ok m
    | .error e => .error (e, false, tbl)
  let uniqueSpecs : Array (Nat × ColDef) := Id.run do
    let mut specs := #[]
    let mut i := 0
    for cd in tbl.cols do
      if cd.unique || (cd.primaryKey && !isIntegerPrimaryKey cd) then
        specs := specs.push (i, cd)
      i := i + 1
    return specs.reverse
  Id.run do
    let mut rowidSet : Std.HashSet Int64 := Std.HashSet.emptyWithCapacity (tbl.rows.length + tuples.length)
    let mut maxExisting? : Option Int64 := none
    for (rid, _) in tbl.rows do
      rowidSet := rowidSet.insert rid
      maxExisting? := match maxExisting? with
        | none => some rid
        | some m => some (if rid > m then rid else m)
    let mut uniqueMaps : Array (Std.HashMap UInt64 (List SqliteValue)) :=
      Array.replicate uniqueSpecs.size {}
    if uniqueSpecs.size > 0 then
      for (_, rVals) in tbl.rows do
        for h : uIdx in [0 : uniqueSpecs.size] do
          let colIdx := uniqueSpecs[uIdx].1
          let ov := rVals.getD colIdx .null
          if ov != .null then
            let hk := uniqueValueHash ov
            let m := uniqueMaps.getD uIdx {}
            uniqueMaps := uniqueMaps.set! uIdx (m.insert hk (ov :: m.getD hk []))
    let mut curMaxAuto := tbl.maxAutoRowid
    let mut curFallbackCand : Int64 := 1
    let mut newRows : Array (Int64 × Array SqliteValue) := Array.mkEmpty tuples.length
    let finishTable := fun (rowsToAdd : Array (Int64 × Array SqliteValue)) (maxA : Int64) =>
      let sortedNew := sortList (fun a b => a.1 < b.1) rowsToAdd.toList
      { tbl with maxAutoRowid := maxA, rows := mergeSortedRows tbl.rows sortedNew }
    for tup in tuples do
      let rawByCol : Array SqliteValue ←
        match evalTupleByColMap tbl colMap? tup params with
        | .error e => return .error (e, newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
        | .ok a => pure a
      let usedFallback : Bool :=
        match maxExisting? with
        | some m =>
          (if m ≥ Int64.maxValue then true else false) &&
            match ipkIdx? with
            | none => !tbl.hasAutoincrement
            | some i => !tbl.hasAutoincrement && normalizeBoundParam (rawByCol.getD i .null) == .null
        | none => false
      let allocRes := allocInsertRowid tbl ipkIdx? rawByCol maxExisting? curMaxAuto
        (fun r => rowidSet.contains r) rowidSet.size curFallbackCand
      let (rid, nextMaxAuto, valsWithRid) ←
        match allocRes with
        | .error e => return .error (e, newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
        | .ok v => pure v
      if usedFallback then
        curFallbackCand := if rid >= Int64.maxValue then 1 else rid + 1
      match validateNotNullCols tbl valsWithRid with
      | .error e => return .error (e, newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
      | .ok () => pure ()
      if rowidSet.contains rid then
        return .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"),
          newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
      let finalVals ←
        match coerceInsertedCols tbl valsWithRid with
        | .error e => return .error (e, newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
        | .ok v => pure v
      for h : uIdx in [0 : uniqueSpecs.size] do
        let (colIdx, cd) := uniqueSpecs[uIdx]
        let nv := finalVals.getD colIdx .null
        if nv != .null then
          let hk := uniqueValueHash nv
          let m := uniqueMaps.getD uIdx {}
          let bucket := m.getD hk []
          if bucket.any (fun ov => sqliteMemCompare nv ov == .eq) then
            let errCode : UInt32 := if cd.primaryKey then 1555 else 2067
            return .error (mapRawError (.constraint errCode s!"UNIQUE constraint failed: {tbl.name}.{cd.name}"),
              newRows.size > 0, finishTable newRows tbl.maxAutoRowid)
          uniqueMaps := uniqueMaps.set! uIdx (m.insert hk (nv :: bucket))
      rowidSet := rowidSet.insert rid
      maxExisting? := match maxExisting? with
        | none => some rid
        | some m => some (if rid > m then rid else m)
      curMaxAuto := nextMaxAuto
      newRows := newRows.push (rid, finalVals)
    return .ok (finishTable newRows curMaxAuto, newRows)

private def removeFirstMatchAux {α : Type} (p : α → Bool) (accRev : List α) :
    List α → Option α × List α
  | [] => (none, accRev.reverse)
  | x :: xs =>
    if p x then (some x, accRev.reverseAux xs)
    else removeFirstMatchAux p (x :: accRev) xs

private def removeFirstMatch {α : Type} (p : α → Bool) (xs : List α) : Option α × List α :=
  removeFirstMatchAux p [] xs

private def rowsMatchExceptCol (ipkIdx : Nat) (aVals mVals : Array SqliteValue) : Bool :=
  aVals.size == mVals.size &&
    (List.range aVals.size).all fun i =>
      i == ipkIdx || sqliteValueBitEq (aVals.getD i .null) (mVals.getD i .null)

private def sortBitRows (rows : Array SqliteRow) : List SqliteRow :=
  sortList (fun a b => sqliteRowBitCompare a b == .lt) rows.toList

private def sortedBitRowSubmultiset : List SqliteRow → List SqliteRow → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    match sqliteRowBitCompare x y with
    | .eq => sortedBitRowSubmultiset xs ys
    | .gt => sortedBitRowSubmultiset (x :: xs) ys
    | .lt => false

private def isRowMultisetSubset (sub sup : Array SqliteRow) : Bool :=
  sub.size ≤ sup.size && sortedBitRowSubmultiset (sortBitRows sub) (sortBitRows sup)

private def isRowMultisetEq (xs ys : Array SqliteRow) : Bool :=
  xs.size == ys.size && sortedBitRowSubmultiset (sortBitRows xs) (sortBitRows ys)

private def execInsertWithWitness (tbl : TableData) (cols? : Option (List String))
    (tuples : List (List ScalarExpr)) (params : Array SqliteValue) (actualPostRows : List SqliteRow) :
    Except SqliteError (TableData × Array (Int64 × Array SqliteValue)) := do
  match findIpkColIdx? 0 tbl.cols with
  | none =>
    match execInsertBatchFast tbl cols? tuples params with
    | .error (e, _, _) => .error e
    | .ok (curTbl, insertedArr) =>
      if isRowMultisetEq (curTbl.rows.map (·.2)).toArray actualPostRows.toArray then
        .ok (curTbl, insertedArr)
      else
        .error (mapRawError (.sqliteCodeError 1 "relational insert post-state mismatch"))
  | some ipkIdx =>
    if tuples.isEmpty then
      if isRowMultisetEq (tbl.rows.map (·.2)).toArray actualPostRows.toArray then
        .ok (tbl, #[])
      else
        .error (mapRawError (.sqliteCodeError 1 "relational insert post-state mismatch"))
    else
      let actualPairs ← Id.run do
        let mut pairs : Array (Int64 × Array SqliteValue) := Array.mkEmpty actualPostRows.length
        let mut seen : Std.HashSet Int64 := Std.HashSet.emptyWithCapacity actualPostRows.length
        for row in actualPostRows do
          match (row[ipkIdx]? : Option SqliteValue) with
          | some (.int rid) =>
            if seen.contains rid then
              return .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"))
            seen := seen.insert rid
            pairs := pairs.push (rid, row)
          | _ =>
            return .error (mapRawError (.sqliteCodeError 20 "relational insert missing integer rowid"))
        return .ok pairs.toList
      let remAfterExisting ← Id.run do
        let mut rem := actualPairs
        for (mRid, mVals) in tbl.rows do
          let (found?, rem') := removeFirstMatch
            (fun (aRid, aVals) => aRid == mRid && sqliteRowBitEq aVals mVals) rem
          if found?.isNone then
            return .error (mapRawError (.sqliteCodeError 1 "relational insert lost existing row"))
          rem := rem'
        return .ok rem
      if remAfterExisting.length != tuples.length then
        .error (mapRawError (.sqliteCodeError 1 "relational insert row count mismatch"))
      else
        let colMap? ← buildInsertColMap? tbl cols?
        let prepared ← Id.run do
          let mut specs : Array (Option Int64 × Array SqliteValue) := Array.mkEmpty tuples.length
          for tup in tuples do
            let rawByCol ← match evalTupleByColMap tbl colMap? tup params with
              | .error e => return .error e
              | .ok a => pure a
            let rawIpk : SqliteValue := normalizeBoundParam (rawByCol.getD ipkIdx (.null : SqliteValue))
            let expRid? : Option Int64 ←
              if rawIpk == .null then pure (none : Option Int64)
              else
                match mustBeIntValue rawIpk with
                | none => return .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
                | some rExp => pure (some rExp)
            match validateNotNullCols tbl rawByCol with
            | .error e => return .error e
            | .ok () => pure ()
            let valsWithDummyRid :=
              match expRid? with
              | some r => rawByCol.set! ipkIdx (.int r)
              | none => rawByCol.set! ipkIdx (.int 0)
            let coerced ← match coerceInsertedCols tbl valsWithDummyRid with
              | .error e => return .error e
              | .ok a => pure a
            specs := specs.push (expRid?, coerced)
          return .ok specs
        let matchedOpt ← Id.run do
          let mut rem := remAfterExisting
          let mut assigned : Array (Option (Int64 × Array SqliteValue)) :=
            Array.replicate prepared.size none
          for h : i in [0 : prepared.size] do
            let (expRid?, expVals) := prepared[i]
            if let some rExp := expRid? then
              let (found?, rem') := removeFirstMatch
                (fun (aRid, aVals) => aRid == rExp && rowsMatchExceptCol ipkIdx aVals expVals) rem
              match found? with
              | none => return .error (mapRawError (.sqliteCodeError 1 "relational insert explicit rowid mismatch"))
              | some pair =>
                assigned := assigned.set! i (some pair)
                rem := rem'
          rem := sortList (fun a b => a.1 < b.1) rem
          for h : i in [0 : prepared.size] do
            let (expRid?, expVals) := prepared[i]
            if expRid?.isNone then
              let (found?, rem') := removeFirstMatch
                (fun (_, aVals) => rowsMatchExceptCol ipkIdx aVals expVals) rem
              match found? with
              | none => return .error (mapRawError (.sqliteCodeError 1 "relational insert auto-rowid row mismatch"))
              | some pair =>
                assigned := assigned.set! i (some pair)
                rem := rem'
          if !rem.isEmpty then
            return .error (mapRawError (.sqliteCodeError 1 "relational insert extra rows remain"))
          let mut out : Array (Int64 × Array SqliteValue) := Array.mkEmpty assigned.size
          for opt in assigned do
            match opt with
            | none => return .error (mapRawError (.sqliteCodeError 1 "relational insert unassigned tuple"))
            | some pair => out := out.push pair
          return .ok out
        let uniqueSpecs : Array (Nat × ColDef) := Id.run do
          let mut specs := #[]
          let mut i := 0
          for cd in tbl.cols do
            if cd.unique || (cd.primaryKey && !isIntegerPrimaryKey cd) then
              specs := specs.push (i, cd)
            i := i + 1
          return specs.reverse
        Id.run do
          let mut rowidSet : Std.HashSet Int64 := Std.HashSet.emptyWithCapacity (tbl.rows.length + tuples.length)
          for (rid, _) in tbl.rows do
            rowidSet := rowidSet.insert rid
          let mut uniqueMaps : Array (Std.HashMap UInt64 (List SqliteValue)) :=
            Array.replicate uniqueSpecs.size {}
          if uniqueSpecs.size > 0 then
            for (_, rVals) in tbl.rows do
              for h : uIdx in [0 : uniqueSpecs.size] do
                let colIdx := uniqueSpecs[uIdx].1
                let ov := rVals.getD colIdx .null
                if ov != .null then
                  let hk := uniqueValueHash ov
                  let m := uniqueMaps.getD uIdx {}
                  uniqueMaps := uniqueMaps.set! uIdx (m.insert hk (ov :: m.getD hk []))
          let mut curMaxAuto := tbl.maxAutoRowid
          let mut insertedArr : Array (Int64 × Array SqliteValue) := Array.mkEmpty matchedOpt.size
          for h : i in [0 : matchedOpt.size] do
            let (aRid, aVals) := matchedOpt[i]
            let (expRid?, _) := prepared[i]!
            if expRid?.isNone && tbl.hasAutoincrement then
              if curMaxAuto >= Int64.maxValue || !(aRid > curMaxAuto) then
                return .error (mapRawError (.sqliteCodeError 1 "AUTOINCREMENT sequence monotonicity violated"))
            if rowidSet.contains aRid then
              return .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"))
            let finalVals := aVals
            for hU : uIdx in [0 : uniqueSpecs.size] do
              let (colIdx, cd) := uniqueSpecs[uIdx]
              let nv := finalVals.getD colIdx .null
              if nv != .null then
                let hk := uniqueValueHash nv
                let m := uniqueMaps.getD uIdx {}
                let bucket := m.getD hk []
                if bucket.any (fun ov => sqliteMemCompare nv ov == .eq) then
                  let errCode : UInt32 := if cd.primaryKey then 1555 else 2067
                  return .error (mapRawError (.constraint errCode s!"UNIQUE constraint failed: {tbl.name}.{cd.name}"))
                uniqueMaps := uniqueMaps.set! uIdx (m.insert hk (nv :: bucket))
            rowidSet := rowidSet.insert aRid
            if tbl.hasAutoincrement && aRid > curMaxAuto then
              curMaxAuto := aRid
            insertedArr := insertedArr.push (aRid, finalVals)
          let sortedNew := sortList (fun a b => a.1 < b.1) insertedArr.toList
          let curTbl := { tbl with maxAutoRowid := curMaxAuto, rows := mergeSortedRows tbl.rows sortedNew }
          return .ok (curTbl, insertedArr)

private def fkParentHasMatch (pTbl : TableData) (pIdx : Nat) (pCol : ColDef) (cv : SqliteValue) : Bool :=
  if cv == .null then true
  else if isIntegerPrimaryKey pCol then
    match mustBeIntValue cv with
    | none => false
    | some r => pTbl.rows.any fun (rid, _) => rid == r
  else
    let coerced := applySqlAffinity (indexFkAff pTbl pCol) true cv
    pTbl.rows.any fun (_, pVals) =>
      let pv := pVals.getD pIdx .null
      pv != .null && sqliteMemCompare coerced pv == .eq

private def fkCountMatchingChildren (pTbl : TableData) (pCol : ColDef) (pv : SqliteValue)
    (cTbl : TableData) (cIdx : Nat) (cCol : ColDef) : Int :=
  if pv == .null then 0
  else
    let aff? := compareAffinityPair (some (colStorageAff pTbl pCol)) (some (colStorageAff cTbl cCol))
    let pv' := applyCompareAff aff? pv
    cTbl.rows.foldl (fun acc (_, cVals) =>
      let cv := cVals.getD cIdx .null
      if cv != .null && sqliteMemCompare (applyCompareAff aff? cv) pv' == .eq then acc + 1 else acc) 0

private def fkStepInsertRow (catBefore : DbCatalog) (tblName : String)
    (rid : Int64) (newVals : Array SqliteValue) (nDef : Int)
    (onlyCols? : Option (List String) := none) (checkIncoming : Bool := true) :
    Except SqliteError (DbCatalog × Int) := do
  let curTbl ← match lookupTable? catBefore tblName with
    | some t => .ok t
    | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
  let tblLo := asciiLower tblName
  let loSet? := onlyCols?.map (·.map asciiLower)
  let mut acc := nDef
  let mut cIdx := 0
  for cd in curTbl.cols do
    if let some (pTabName, pColName) := cd.references? then
      let isSelfRef := asciiLower pTabName == tblLo
      let checkOut := isSelfRef || match loSet? with
        | none => true
        | some lo => lo.contains (asciiLower cd.name)
      if checkOut then
        let cv := newVals.getD cIdx .null
        if cv != .null then
          let pTbl ← match lookupTable? catBefore pTabName with
            | some t => .ok t
            | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {pTabName}"))
          let (pIdx, pCol) ← match findColIdx? pTbl.cols pColName with
            | some p =>
              if p.2.primaryKey || p.2.unique then .ok p
              else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
            | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
          let selfMatch :=
            if isSelfRef then
              if isIntegerPrimaryKey pCol then
                match mustBeIntValue cv with
                | some cvInt => cvInt == rid
                | none => false
              else
                let newPv := newVals.getD pIdx .null
                newPv != .null && sqliteMemCompare cv newPv == .eq
            else false
          if !selfMatch && !fkParentHasMatch pTbl pIdx pCol cv then
            acc := acc + 1
    cIdx := cIdx + 1
  if checkIncoming && acc > 0 then
    for (_, childTbl) in catBefore.tables do
      let mut chIdx := 0
      for cd in childTbl.cols do
        if let some (pTabName, pColName) := cd.references? then
          let isSelfRef := asciiLower childTbl.name == tblLo
          let checkIn := asciiLower pTabName == tblLo &&
            match loSet? with
            | none => true
            | some lo => lo.contains (asciiLower pColName) || isSelfRef
          if checkIn && acc > 0 then
            let (pIdx, pCol) ← match findColIdx? curTbl.cols pColName with
              | some p =>
                if p.2.primaryKey || p.2.unique then .ok p
                else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
              | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
            let newPv := if isIntegerPrimaryKey pCol then .int rid else newVals.getD pIdx .null
            let dec := fkCountMatchingChildren curTbl pCol newPv childTbl chIdx cd
            acc := max 0 (acc - dec)
        chIdx := chIdx + 1
  let tblAfter := { curTbl with rows := insertSortedRow rid newVals curTbl.rows }
  let catAfter := setTable catBefore tblAfter
  .ok (catAfter, acc)

private def fkStepDeleteRow (catBefore : DbCatalog) (tblName : String)
    (oldRid : Int64) (oldVals : Array SqliteValue) (nDef : Int)
    (onlyCols? : Option (List String) := none) : Except SqliteError (DbCatalog × Int) := do
  let curTbl ← match lookupTable? catBefore tblName with
    | some t => .ok t
    | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
  let tblAfter := { curTbl with rows := curTbl.rows.filter (fun r => r.1 != oldRid) }
  let catAfter := setTable catBefore tblAfter
  let tblLo := asciiLower tblName
  let loSet? := onlyCols?.map (·.map asciiLower)
  let mut acc := nDef
  let mut cIdx := 0
  for cd in curTbl.cols do
    if let some (pTabName, pColName) := cd.references? then
      let isSelfRef := asciiLower pTabName == tblLo
      let checkOut := isSelfRef || match loSet? with
        | none => true
        | some lo => lo.contains (asciiLower cd.name)
      if checkOut && acc > 0 then
        let cv := oldVals.getD cIdx .null
        if cv != .null then
          let pTbl ← match lookupTable? catBefore pTabName with
            | some t => .ok t
            | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {pTabName}"))
          let (pIdx, pCol) ← match findColIdx? pTbl.cols pColName with
            | some p =>
              if p.2.primaryKey || p.2.unique then .ok p
              else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
            | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
          if !fkParentHasMatch pTbl pIdx pCol cv then
            acc := acc - 1
    cIdx := cIdx + 1
  for (_, childTbl) in catAfter.tables do
    let mut chIdx := 0
    for cd in childTbl.cols do
      if let some (pTabName, pColName) := cd.references? then
        let isSelfRef := asciiLower childTbl.name == tblLo
        let checkIn := asciiLower pTabName == tblLo &&
          match loSet? with
          | none => true
          | some lo => lo.contains (asciiLower pColName) || isSelfRef
        if checkIn then
          let (pIdx, pCol) ← match findColIdx? tblAfter.cols pColName with
            | some p =>
              if p.2.primaryKey || p.2.unique then .ok p
              else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
            | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
          acc := acc + fkCountMatchingChildren tblAfter pCol (oldVals.getD pIdx .null) childTbl chIdx cd
      chIdx := chIdx + 1
  .ok (catAfter, acc)

private def fkBatchInsertCheck (catBefore : DbCatalog) (tblName : String)
    (insertedArr : Array (Int64 × Array SqliteValue)) : Except SqliteError Unit := do
  let curTbl ← match lookupTable? catBefore tblName with
    | some t => .ok t
    | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
  let tblLo := asciiLower tblName
  let mut outSpecs :
      Array (Nat × Bool × Nat × TableData × ColDef × Std.HashSet Int64 × Std.HashMap UInt64 (List SqliteValue)) := #[]
  let mut cIdx := 0
  for cd in curTbl.cols do
    if let some (pTabName, pColName) := cd.references? then
      let isSelfRef := asciiLower pTabName == tblLo
      let pTbl ← match lookupTable? catBefore pTabName with
        | some t => .ok t
        | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {pTabName}"))
      let (pIdx, pCol) ← match findColIdx? pTbl.cols pColName with
        | some p =>
          if p.2.primaryKey || p.2.unique then .ok p
          else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
        | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
      let mut ipkSet : Std.HashSet Int64 := {}
      let mut valMap : Std.HashMap UInt64 (List SqliteValue) := {}
      if isIntegerPrimaryKey pCol then
        for (pRid, _) in pTbl.rows do
          ipkSet := ipkSet.insert pRid
      else
        for (_, pVals) in pTbl.rows do
          let pv := pVals.getD pIdx .null
          if pv != .null then
            let hk := uniqueValueHash pv
            valMap := valMap.insert hk (pv :: valMap.getD hk [])
      outSpecs := outSpecs.push (cIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap)
    cIdx := cIdx + 1
  let mut inSpecs :
      Array (Bool × Nat × ColDef × Nat × ColDef × Option SqlColType × Std.HashMap UInt64 (List SqliteValue)) := #[]
  for (_, childTbl) in catBefore.tables do
    let isSelfChild := asciiLower childTbl.name == tblLo
    let mut chIdx := 0
    for cd in childTbl.cols do
      if let some (pTabName, pColName) := cd.references? then
        if asciiLower pTabName == tblLo then
          let (pIdx, pCol) ← match findColIdx? curTbl.cols pColName with
            | some p =>
              if p.2.primaryKey || p.2.unique then .ok p
              else .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
            | none => .error (mapRawError (.sqliteCodeError 1 "foreign key mismatch"))
          let aff? := compareAffinityPair (some (colStorageAff curTbl pCol)) (some (colStorageAff childTbl cd))
          let mut chMap : Std.HashMap UInt64 (List SqliteValue) := {}
          for (_, cVals) in childTbl.rows do
            let cv := cVals.getD chIdx .null
            if cv != .null then
              let cv' := applyCompareAff aff? cv
              let hk := uniqueValueHash cv'
              chMap := chMap.insert hk (cv' :: chMap.getD hk [])
          inSpecs := inSpecs.push (isSelfChild, pIdx, pCol, chIdx, cd, aff?, chMap)
      chIdx := chIdx + 1
  let mut acc : Int := 0
  for (rid, newVals) in insertedArr do
    for h : oIdx in [0 : outSpecs.size] do
      let (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap) := outSpecs[oIdx]
      let cv := newVals.getD colIdx .null
      if cv != .null then
        let matched :=
          if isIntegerPrimaryKey pCol then
            match mustBeIntValue cv with
            | none => false
            | some r =>
              let selfHit := isSelfRef && r == rid
              selfHit || ipkSet.contains r
          else
            let coerced := applySqlAffinity (indexFkAff pTbl pCol) true cv
            let selfHit :=
              if isSelfRef then
                let newPv := newVals.getD pIdx .null
                newPv != .null && sqliteMemCompare cv newPv == .eq
              else false
            selfHit ||
              let bucket := valMap.getD (uniqueValueHash coerced) []
              bucket.any (fun pv => sqliteMemCompare coerced pv == .eq)
        if !matched then
          acc := acc + 1
    if acc > 0 then
      for h : iIdx in [0 : inSpecs.size] do
        if acc > 0 then
          let (_, pIdx, pCol, _, _, aff?, chMap) := inSpecs[iIdx]
          let newPv := if isIntegerPrimaryKey pCol then .int rid else newVals.getD pIdx .null
          if newPv != .null then
            let pv' := applyCompareAff aff? newPv
            let bucket := chMap.getD (uniqueValueHash pv') []
            let dec : Int := bucket.foldl (fun n cv' => if sqliteMemCompare cv' pv' == .eq then n + 1 else n) 0
            acc := max 0 (acc - dec)
    outSpecs := outSpecs.map fun (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap) =>
      if !isSelfRef then
        (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap)
      else if isIntegerPrimaryKey pCol then
        (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet.insert rid, valMap)
      else
        let pv := newVals.getD pIdx .null
        if pv != .null then
          let hk := uniqueValueHash pv
          (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap.insert hk (pv :: valMap.getD hk []))
        else
          (colIdx, isSelfRef, pIdx, pTbl, pCol, ipkSet, valMap)
    inSpecs := inSpecs.map fun (isSelfChild, pIdx, pCol, chIdx, cd, aff?, chMap) =>
      if !isSelfChild then
        (isSelfChild, pIdx, pCol, chIdx, cd, aff?, chMap)
      else
        let cv := newVals.getD chIdx .null
        if cv != .null then
          let cv' := applyCompareAff aff? cv
          let hk := uniqueValueHash cv'
          (isSelfChild, pIdx, pCol, chIdx, cd, aff?, chMap.insert hk (cv' :: chMap.getD hk []))
        else
          (isSelfChild, pIdx, pCol, chIdx, cd, aff?, chMap)
  if acc > 0 then
    .error (mapRawError (.constraint 787 "FOREIGN KEY constraint failed"))
  else
    .ok ()

private def hasIncomingFk (cat : DbCatalog) (tblName : String) : Bool :=
  let targetLo := asciiLower tblName
  cat.tables.any fun (_, tbl) =>
    tbl.cols.any fun cd =>
      match cd.references? with
      | some (pTab, _) => asciiLower pTab == targetLo
      | none => false

/-- `true` when SQLite opens a statement journal (`mayAbort && isMultiWrite`) so errors roll back the statement rather than persisting partial rows (`M2`) or auto-rolling back the transaction on `SQLITE_FULL` (`M1`). -/
private def stmtUsesStmtJournal (cat : DbCatalog) (foreignKeys : Bool) : SqlStmt → Bool
  | .insert tblName cols? tuples =>
    if tuples.length ≤ 1 then false
    else
      match lookupTable? cat tblName with
      | none => false
      | some tbl =>
        let targetsIpk :=
          match cols? with
          | none => true
          | some cs =>
            cs.any fun colName =>
              match findColIdx? tbl.cols colName with
              | some (_, cd) => isIntegerPrimaryKey cd
              | none => false
        tbl.cols.any (fun c => (!isIntegerPrimaryKey c && c.primaryKey) || c.unique || c.notNull) ||
          (targetsIpk && tbl.cols.any isIntegerPrimaryKey) ||
          (foreignKeys && tbl.cols.any (·.references?.isSome))
  | .update _ _ _ | .delete _ _ => true
  | _ => false

private def finishInsertCat (cat : DbCatalog) (tblName : String) (tbl curTbl : TableData)
    (insertedArr : Array (Int64 × Array SqliteValue)) (isMultiWrite foreignKeys : Bool) :
    Except SqliteError (Bool × DbCatalog) × (Bool × DbCatalog) :=
  let cat' := setTable cat curTbl
  let hasOutFk := tbl.cols.any (·.references?.isSome)
  if foreignKeys && (hasOutFk || (isMultiWrite && hasIncomingFk cat tblName)) then
    let fkRes : Except SqliteError Unit :=
      if insertedArr.size ≤ 1 then
        Id.run do
          let mut catCur := cat
          let mut nDef : Int := 0
          for (rid, newVals) in insertedArr do
            match fkStepInsertRow catCur tblName rid newVals nDef none isMultiWrite with
            | .error err => return .error err
            | .ok (nextCat, nextDef) =>
              catCur := nextCat
              nDef := nextDef
          if nDef > 0 then
            return .error (mapRawError (.constraint 787 "FOREIGN KEY constraint failed"))
          return .ok ()
      else
        fkBatchInsertCheck cat tblName insertedArr
    match fkRes with
    | .error e => (.error e, (false, cat'))
    | .ok () => (.ok (insertedArr.size > 0, cat'), (insertedArr.size > 0, cat'))
  else
    (.ok (insertedArr.size > 0, cat'), (insertedArr.size > 0, cat'))

/-- Apply `stmt` returning `(Except err (dirty × newCat), (partialDirty × partialCatOnAbort))`. -/
private def applyWriteStmtEx (cat : DbCatalog) (foreignKeys : Bool)
    (stmt : SqlStmt) (params : Array SqliteValue) :
    Except SqliteError (Bool × DbCatalog) × (Bool × DbCatalog) :=
  match stmt with
  | .createTable ifNotExists tblName cols strict =>
    match lookupTable? cat tblName with
    | some _ =>
      if ifNotExists then (.ok (false, cat), (false, cat))
      else (.error (mapRawError (.sqliteCodeError 1 s!"table {tblName} already exists")), (false, cat))
    | none =>
      let hasAuto := cols.any (fun c => c.autoIncrement)
      let newTbl : TableData :=
        { name := tblName
          cols := cols
          strict := strict
          hasAutoincrement := hasAuto
          maxAutoRowid := 0
          rows := [] }
      let cat' := setTable cat newTbl
      (.ok (true, cat'), (true, cat'))
  | .insert tblName cols? tuples =>
    match lookupTable? cat tblName with
    | none => (.error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}")), (false, cat))
    | some tbl =>
      match execInsertBatchFast tbl cols? tuples params with
      | .error (e, didPartial, partialTbl) =>
        (.error e, (didPartial, setTable cat partialTbl))
      | .ok (curTbl, insertedArr) =>
        finishInsertCat cat tblName tbl curTbl insertedArr (tuples.length > 1) foreignKeys
  | .update tblName assigns where? =>
    match lookupTable? cat tblName with
    | none => (.error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}")), (false, cat))
    | some tbl =>
      let ipkIdx? :=
        let rec findIpk (i : Nat) : List ColDef → Option Nat
          | [] => none
          | cd :: rest => if isIntegerPrimaryKey cd then some i else findIpk (i + 1) rest
        findIpk 0 tbl.cols
      let scanRes : Except SqliteError (Array (Int64 × Array SqliteValue) × Array (Int64 × Int64 × Array SqliteValue)) := Id.run do
        let mut oldUpdatedArr : Array (Int64 × Array SqliteValue) := #[]
        let mut matchedJobs : Array (Int64 × Int64 × Array SqliteValue) := #[]
        for (oldRid, oldVals) in tbl.rows do
          if evalWhere tbl oldVals params where? then
            oldUpdatedArr := oldUpdatedArr.push (oldRid, oldVals)
            let mut newVals := oldVals
            for (colName, expr) in assigns do
              match findColIdx? tbl.cols colName with
              | none => return .error (mapRawError (.sqliteCodeError 1 s!"no such column: {colName}"))
              | some (cIdx, _) =>
                newVals := newVals.set! cIdx (evalScalar params expr)
            let newRid : Int64 :=
              match ipkIdx? with
              | none => oldRid
              | some ipkIdx =>
                match mustBeIntValue (newVals.getD ipkIdx .null) with
                | some r => r
                | none => 0
            if let some ipkIdx := ipkIdx? then
              if (mustBeIntValue (newVals.getD ipkIdx .null)).isNone then
                return .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
            matchedJobs := matchedJobs.push (oldRid, newRid, newVals)
        return .ok (oldUpdatedArr, matchedJobs)
      match scanRes with
      | .error e => (.error e, (false, cat))
      | .ok (oldUpdatedArr, matchedJobs) =>
        let buildRes : Except SqliteError (TableData × Array (Int64 × Array SqliteValue)) :=
          if matchedJobs.size ≤ 1 then
            Id.run do
              let mut curTbl : TableData := tbl
              let mut coercedUpdated := Array.mkEmpty matchedJobs.size
              for (oldRid, newRid, rawVals) in matchedJobs do
                let rowsWithoutOld := curTbl.rows.filter (fun r => r.1 != oldRid)
                let tblWithoutOld := { curTbl with rows := rowsWithoutOld }
                let mut idx := 0
                for cd in tbl.cols do
                  if !isIntegerPrimaryKey cd then
                    let rawV := normalizeBoundParam (rawVals.getD idx .null)
                    if rawV == .null && (cd.notNull || (tbl.strict && cd.primaryKey)) then
                      return .error (mapRawError (.constraint 1299 s!"NOT NULL constraint failed: {cd.name}"))
                  idx := idx + 1
                if tblWithoutOld.rows.any (fun r => r.1 == newRid) then
                  return .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"))
                let mut coercedVals := Array.mkEmpty tbl.cols.length
                let mut cIdx := 0
                for cd in tbl.cols do
                  if isIntegerPrimaryKey cd then
                    coercedVals := coercedVals.push (.int newRid)
                  else
                    match coerceForColumn tbl.strict cd (rawVals.getD cIdx .null) with
                    | .error e => return .error e
                    | .ok cv => coercedVals := coercedVals.push cv
                  cIdx := cIdx + 1
                if let .error e := checkColUniqueness tblWithoutOld coercedVals then
                  return .error e
                curTbl := { curTbl with rows := insertSortedRow newRid coercedVals rowsWithoutOld }
                coercedUpdated := coercedUpdated.push (newRid, coercedVals)
              return .ok (curTbl, coercedUpdated)
          else
            Id.run do
              let uniqueSpecs : Array (Nat × ColDef) := Id.run do
                let mut specs := #[]
                let mut i := 0
                for cd in tbl.cols do
                  if cd.unique || (cd.primaryKey && !isIntegerPrimaryKey cd) then
                    specs := specs.push (i, cd)
                  i := i + 1
                return specs.reverse
              let mut rowMap : Std.HashMap Int64 (Array SqliteValue) :=
                Std.HashMap.emptyWithCapacity tbl.rows.length
              let mut uniqueMaps : Array (Std.HashMap UInt64 (List (Int64 × SqliteValue))) :=
                Array.replicate uniqueSpecs.size {}
              for (rid, rVals) in tbl.rows do
                rowMap := rowMap.insert rid rVals
                for h : uIdx in [0 : uniqueSpecs.size] do
                  let colIdx := uniqueSpecs[uIdx].1
                  let ov := rVals.getD colIdx .null
                  if ov != .null then
                    let hk := uniqueValueHash ov
                    let m := uniqueMaps.getD uIdx {}
                    uniqueMaps := uniqueMaps.set! uIdx (m.insert hk ((rid, ov) :: m.getD hk []))
              let mut coercedUpdated := Array.mkEmpty matchedJobs.size
              for (oldRid, newRid, rawVals) in matchedJobs do
                let oldVals := rowMap.getD oldRid #[]
                rowMap := rowMap.erase oldRid
                for h : uIdx in [0 : uniqueSpecs.size] do
                  let colIdx := uniqueSpecs[uIdx].1
                  let ov := oldVals.getD colIdx .null
                  if ov != .null then
                    let hk := uniqueValueHash ov
                    let m := uniqueMaps.getD uIdx {}
                    let filtered := (m.getD hk []).filter (fun p => p.1 != oldRid)
                    uniqueMaps := uniqueMaps.set! uIdx (m.insert hk filtered)
                let mut idx := 0
                for cd in tbl.cols do
                  if !isIntegerPrimaryKey cd then
                    let rawV := normalizeBoundParam (rawVals.getD idx .null)
                    if rawV == .null && (cd.notNull || (tbl.strict && cd.primaryKey)) then
                      return .error (mapRawError (.constraint 1299 s!"NOT NULL constraint failed: {cd.name}"))
                  idx := idx + 1
                if rowMap.contains newRid then
                  return .error (mapRawError (.constraint 1555 s!"UNIQUE constraint failed: {tbl.name}"))
                let mut coercedVals := Array.mkEmpty tbl.cols.length
                let mut cIdx := 0
                for cd in tbl.cols do
                  if isIntegerPrimaryKey cd then
                    coercedVals := coercedVals.push (.int newRid)
                  else
                    match coerceForColumn tbl.strict cd (rawVals.getD cIdx .null) with
                    | .error e => return .error e
                    | .ok cv => coercedVals := coercedVals.push cv
                  cIdx := cIdx + 1
                for h : uIdx in [0 : uniqueSpecs.size] do
                  let (colIdx, cd) := uniqueSpecs[uIdx]
                  let nv := coercedVals.getD colIdx .null
                  if nv != .null then
                    let hk := uniqueValueHash nv
                    let m := uniqueMaps.getD uIdx {}
                    let bucket := m.getD hk []
                    if bucket.any (fun (_, ov) => sqliteMemCompare nv ov == .eq) then
                      let errCode : UInt32 := if cd.primaryKey then 1555 else 2067
                      return .error (mapRawError (.constraint errCode s!"UNIQUE constraint failed: {tbl.name}.{cd.name}"))
                    uniqueMaps := uniqueMaps.set! uIdx (m.insert hk ((newRid, nv) :: bucket))
                rowMap := rowMap.insert newRid coercedVals
                coercedUpdated := coercedUpdated.push (newRid, coercedVals)
              let sortedRows := sortList (fun a b => a.1 < b.1) rowMap.toList
              return .ok ({ tbl with rows := sortedRows }, coercedUpdated)
        match buildRes with
        | .error e => (.error e, (false, cat))
        | .ok (rebuiltTbl, coercedUpdated) =>
          let cat' := setTable cat rebuiltTbl
          if foreignKeys then
            let assignedCols := assigns.map (·.1)
            let loAssigned := assignedCols.map asciiLower
            let tblLo := asciiLower tblName
            let touchesOutFk := tbl.cols.any fun cd =>
              cd.references?.isSome && loAssigned.contains (asciiLower cd.name)
            let touchesInFk := cat'.tables.any fun (_, childTbl) =>
              childTbl.cols.any fun cd =>
                match cd.references? with
                | some (pTab, pCol) => asciiLower pTab == tblLo && loAssigned.contains (asciiLower pCol)
                | none => false
            let fkRes : Except SqliteError Unit :=
              if !(touchesOutFk || touchesInFk) then .ok ()
              else Id.run do
                let mut catCur := cat
                let mut nDef : Int := 0
                for h : i in [0 : coercedUpdated.size] do
                  let (oldRid, oldVals) := oldUpdatedArr[i]!
                  let (newRid, newVals) := coercedUpdated[i]
                  match fkStepDeleteRow catCur tblName oldRid oldVals nDef (some assignedCols) with
                  | .error e => return .error e
                  | .ok (catMid, def1) =>
                    match fkStepInsertRow catMid tblName newRid newVals def1 (some assignedCols) with
                    | .error e => return .error e
                    | .ok (catNext, def2) =>
                      catCur := catNext
                      nDef := def2
                if nDef > 0 then
                  return .error (mapRawError (.constraint 787 "FOREIGN KEY constraint failed"))
                return .ok ()
            match fkRes with
            | .error e => (.error e, (false, cat))
            | .ok () => (.ok (oldUpdatedArr.size > 0, cat'), (oldUpdatedArr.size > 0, cat'))
          else
            (.ok (oldUpdatedArr.size > 0, cat'), (oldUpdatedArr.size > 0, cat'))
  | .delete tblName where? =>
    match lookupTable? cat tblName with
    | none => (.error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}")), (false, cat))
    | some tbl =>
      let kept := tbl.rows.filter fun (_, vals) => !evalWhere tbl vals params where?
      let deleted := tbl.rows.filter fun (_, vals) => evalWhere tbl vals params where?
      let cat' := setTable cat { tbl with rows := kept }
      let hasOutFk := tbl.cols.any (·.references?.isSome)
      if foreignKeys && !deleted.isEmpty && (hasOutFk || hasIncomingFk cat tblName) then
        let fkRes : Except SqliteError Unit := Id.run do
          let mut catCur := cat
          let mut nDef : Int := 0
          for (oldRid, oldVals) in deleted do
            match fkStepDeleteRow catCur tblName oldRid oldVals nDef with
            | .error e => return .error e
            | .ok (nextCat, nextDef) =>
              catCur := nextCat
              nDef := nextDef
          if nDef > 0 then
            return .error (mapRawError (.constraint 787 "FOREIGN KEY constraint failed"))
          return .ok ()
        match fkRes with
        | .error e => (.error e, (false, cat))
        | .ok () => (.ok (!deleted.isEmpty, cat'), (!deleted.isEmpty, cat'))
      else
        (.ok (!deleted.isEmpty, cat'), (!deleted.isEmpty, cat'))
  | _ => (.ok (false, cat), (false, cat))

private def compareOrderItem (tbl : TableData) (oi : OrderItem) (r1 r2 : Array SqliteValue) : Ordering :=
  match findColIdx? tbl.cols oi.col with
  | none => .eq
  | some (idx, _) =>
    let v1 := normalizeBoundParam (r1.getD idx .null)
    let v2 := normalizeBoundParam (r2.getD idx .null)
    let nullFirst : Bool :=
      match oi.nulls with
      | .first => true
      | .last => false
      | .auto => oi.dir == .asc
    match v1, v2 with
    | .null, .null => .eq
    | .null, _ => if nullFirst == true then .lt else .gt
    | _, .null => if nullFirst == true then .gt else .lt
    | _, _ =>
      let ord := sqliteMemCompare v1 v2
      match oi.dir with
      | .asc => ord
      | .desc =>
        match ord with
        | .lt => .gt
        | .gt => .lt
        | .eq => .eq

private def compareByOrderItems (tbl : TableData) (orderBy : List OrderItem)
    (r1 r2 : Array SqliteValue) : Ordering :=
  match orderBy with
  | [] => .eq
  | oi :: rest =>
    match compareOrderItem tbl oi r1 r2 with
    | .eq => compareByOrderItems tbl rest r1 r2
    | ord => ord

private def evalSelectQuery (cat : DbCatalog) (proj : SelectProj) (tbl? : Option String)
    (where? : Option WhereExpr) (orderBy : List OrderItem) (limit? : Option ScalarExpr)
    (params : Array SqliteValue) : Except SqliteError (Array SqliteRow) := do
  let limitInt? ←
    match limit? with
    | none => .ok none
    | some e =>
      match mustBeIntValue (evalScalar params e) with
      | some iv => .ok (some iv)
      | none => .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
  let rawRows ←
    match tbl? with
    | none =>
      let projected : SqliteRow :=
        match proj with
        | .star => #[]
        | .items es => (es.map fun e => (evalVal none #[] params e).1).toArray
      .ok #[projected]
    | some tblName =>
      match lookupTable? cat tblName with
      | none => .error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}"))
      | some tbl =>
        let matched := (tbl.rows.map (·.2)).filter fun vals => evalWhere tbl vals params where?
        let sorted :=
          if orderBy.isEmpty then matched.toArray
          else (sortList (fun a b => compareByOrderItems tbl orderBy a b == .lt) matched).toArray
        let projected := sorted.map fun vals =>
          match proj with
          | .star => vals
          | .items es => (es.map fun e => (evalVal (some tbl) vals params e).1).toArray
        .ok projected
  match limitInt? with
  | none => .ok rawRows
  | some n =>
    if n < 0 then .ok rawRows
    else .ok (rawRows.extract 0 (min rawRows.size n.toNatClampNeg))

private def scanTieGroupEndFuel (tbl : TableData) (orderBy : List OrderItem)
    (sortedTableRows : Array (Array SqliteValue)) (head : Array SqliteValue) (j : Nat) : Nat → Nat
  | 0 => j
  | fuel + 1 =>
    if h : j < sortedTableRows.size then
      if compareByOrderItems tbl orderBy head sortedTableRows[j] == .eq then
        scanTieGroupEndFuel tbl orderBy sortedTableRows head (j + 1) fuel
      else j
    else j

private def scanTieGroupEnd (tbl : TableData) (orderBy : List OrderItem)
    (sortedTableRows : Array (Array SqliteValue)) (head : Array SqliteValue) (j : Nat) : Nat :=
  scanTieGroupEndFuel tbl orderBy sortedTableRows head j (sortedTableRows.size - j)

private def projectTableRows (tbl : TableData) (proj : SelectProj) (params : Array SqliteValue)
    (rows : Array (Array SqliteValue)) : Array SqliteRow :=
  rows.map fun vals =>
    match proj with
    | .star => vals
    | .items es => (es.map fun e => (evalVal (some tbl) vals params e).1).toArray

private def checkOrderTieGroupsLoop (tbl : TableData) (proj : SelectProj) (orderBy : List OrderItem)
    (params : Array SqliteValue) (sortedTableRows : Array (Array SqliteValue))
    (actualRows : Array SqliteRow) (limitTotal idx : Nat) : Nat → Bool
  | 0 => idx ≥ limitTotal
  | fuel + 1 =>
    if idx < limitTotal then
      let head := sortedTableRows.getD idx #[]
      let stop := scanTieGroupEnd tbl orderBy sortedTableRows head (idx + 1)
      let expGroup := projectTableRows tbl proj params (sortedTableRows.extract idx stop)
      if stop ≤ limitTotal then
        let actSlice := actualRows.extract idx stop
        if isRowMultisetEq expGroup actSlice then
          if idx < stop then
            checkOrderTieGroupsLoop tbl proj orderBy params sortedTableRows actualRows limitTotal stop fuel
          else false
        else false
      else
        let actSub := actualRows.extract idx limitTotal
        isRowMultisetSubset actSub expGroup
    else true

private def checkOrderByRelational (tbl : TableData) (proj : SelectProj) (where? : Option WhereExpr)
    (orderBy : List OrderItem) (limit? : Option ScalarExpr) (params : Array SqliteValue)
    (actualRows : Array SqliteRow) : Bool :=
  let limitNat? : Option (Option Nat) :=
    match limit? with
    | none => some none
    | some e =>
      match mustBeIntValue (evalScalar params e) with
      | some iv => some (if iv < 0 then none else some iv.toNatClampNeg)
      | none => none
  match limitNat? with
  | none => false
  | some limNat? =>
    let matched := (tbl.rows.map (·.2)).filter fun vals => evalWhere tbl vals params where?
    let sortedTableRows := (sortList (fun a b => compareByOrderItems tbl orderBy a b == .lt) matched).toArray
    let totalTarget :=
      match limNat? with
      | none => sortedTableRows.size
      | some k => min sortedTableRows.size k
    if actualRows.size != totalTarget then
      false
    else
      checkOrderTieGroupsLoop tbl proj orderBy params sortedTableRows actualRows totalTarget 0 (totalTarget + 1)

/-- Relational `SELECT` row-set equivalence predicate allowing SQLite index/scan tie-breaking
    while verifying strict `Float.toBits` values and exact `ORDER BY` preorder + `LIMIT` semantics. -/
def allowedSelectRows (cat : DbCatalog) (sql : String) (params : Array SqliteValue)
    (actualRows : Array SqliteRow) (foreignKeys : Bool := false) : Bool :=
  match validateStmtNoCapWith mapRawError sql params with
  | .ok stmt@(.select proj tbl? where? orderBy limit?) =>
    if !(validateStmtSchema cat foreignKeys stmt).isOk then false
    else
      match tbl? with
      | none =>
        match evalSelectQuery cat proj none where? orderBy limit? params with
        | .ok expRows =>
          expRows.size == actualRows.size &&
            (List.range expRows.size).all fun i =>
              sqliteRowBitEq (expRows.getD i #[]) (actualRows.getD i #[])
        | .error _ => false
      | some tblName =>
        match lookupTable? cat tblName with
        | none => false
        | some tbl =>
          if orderBy.isEmpty then
            match evalSelectQuery cat proj tbl? where? [] none params with
            | .error _ => false
            | .ok fullRows =>
              match limit? with
              | none => isRowMultisetEq fullRows actualRows
              | some e =>
                match mustBeIntValue (evalScalar params e) with
                | none => false
                | some lim =>
                  if lim < 0 then isRowMultisetEq fullRows actualRows
                  else
                    let k := min fullRows.size lim.toNatClampNeg
                    actualRows.size == k && isRowMultisetSubset actualRows fullRows
          else
            checkOrderByRelational tbl proj where? orderBy limit? params actualRows
  | .ok stmt =>
    (validateStmtSchema cat foreignKeys stmt).isOk && actualRows.isEmpty
  | .error _ => false

/-- Relational `SELECT` single-row equivalence predicate for `queryOne` (effective `LIMIT 1` unless `LIMIT 0`). -/
def allowedQueryOneRow (cat : DbCatalog) (sql : String) (params : Array SqliteValue)
    (actualRow? : Option SqliteRow) (foreignKeys : Bool := false) : Bool :=
  match validateStmtNoCapWith mapRawError sql params with
  | .ok stmt@(.select proj tbl? where? orderBy limit?) =>
    if !(validateStmtSchema cat foreignKeys stmt).isOk then false
    else
      let effLimExpr? : Option ScalarExpr :=
        match limit? with
        | none => some (.litInt 1)
        | some e =>
          match mustBeIntValue (evalScalar params e) with
          | none => none
          | some iv => some (if iv == 0 then .litInt 0 else .litInt 1)
      match effLimExpr? with
      | none => false
      | some effLimExpr =>
        let effLim? := some effLimExpr
        let actualRows := match actualRow? with | none => #[] | some r => #[r]
        match tbl? with
        | none =>
          match evalSelectQuery cat proj none where? orderBy effLim? params with
          | .ok expRows =>
            expRows.size == actualRows.size &&
              (List.range expRows.size).all fun i =>
                sqliteRowBitEq (expRows.getD i #[]) (actualRows.getD i #[])
          | .error _ => false
        | some tblName =>
          match lookupTable? cat tblName with
          | none => false
          | some tbl =>
            if orderBy.isEmpty then
              match evalSelectQuery cat proj tbl? where? [] none params with
              | .error _ => false
              | .ok fullRows =>
                if effLimExpr == .litInt 0 then
                  actualRows.isEmpty
                else
                  let k := min fullRows.size 1
                  actualRows.size == k && isRowMultisetSubset actualRows fullRows
            else
              checkOrderByRelational tbl proj where? orderBy effLim? params actualRows
  | .ok stmt =>
    (validateStmtSchema cat foreignKeys stmt).isOk && actualRow?.isNone
  | .error _ => false

private def lookupConn? (st : SqliteWorldState) (dbId : UInt64) : Option ConnState :=
  st.conns.find? (·.id == dbId)

private def replaceConn (st : SqliteWorldState) (c : ConnState) : SqliteWorldState :=
  { st with
    conns := st.conns.map fun x => if x.id == c.id then c else x
    mutGen := st.mutGen + 1 }

private def connRefsMemStore (k : String) (c : ConnState) : Bool :=
  match c.backing with
  | .sharedMemory sk => sk == k
  | _ => false

private def lookupMemStore? (st : SqliteWorldState) (key : String) : Option (Nat × DbCatalog) :=
  (st.memStores.find? fun p => p.1 == key).map (·.2)

private def setMemStore (st : SqliteWorldState) (key : String) (epoch : Nat) (cat : DbCatalog) :
    SqliteWorldState :=
  { st with
    memStores := st.memStores.filter (fun p => p.1 != key) ++ [(key, epoch, cat)]
    mutGen := st.mutGen + 1 }

private def rawByteEscChar : Char := Char.ofNat 0x10FFFD

private def hasRawByteEscChars : List Char → Bool
  | [] => false
  | c :: rest => if c == rawByteEscChar then true else hasRawByteEscChars rest

private def encodeModelPathCharsAux (accRev : List Char) : List Char → List Char
  | [] => accRev.reverse
  | c :: rest =>
    if c == rawByteEscChar then
      encodeModelPathCharsAux (rawByteEscChar :: rawByteEscChar :: accRev) rest
    else
      encodeModelPathCharsAux (c :: accRev) rest

private def encodeModelPathString (s : String) : String :=
  let cs := s.toList
  if hasRawByteEscChars cs then
    String.ofList (encodeModelPathCharsAux [] cs)
  else
    s

private def lookupFile? (st : SqliteWorldState) (path : String) : Option FileNode :=
  (st.files.find? fun p => p.1 == path || encodeModelPathString p.1 == path).map (·.2)

private def setFileNode (st : SqliteWorldState) (path : String) (node : FileNode) : SqliteWorldState :=
  { st with
    files := st.files.filter (fun p => p.1 != path && encodeModelPathString p.1 != path) ++ [(path, node)]
    mutGen := st.mutGen + 1 }

private def connVisibleCatalog (st : SqliteWorldState) (c : ConnState) : DbCatalog :=
  match c.tx with
  | .write _ staged => staged
  | .deferred (some (_, snap)) => snap
  | _ =>
    let pinned? :=
      if c.sharedGroup?.isNone then c.readSnap?
      else
        c.readSnap? <|>
          st.conns.findSome? fun other =>
            if c.id != other.id && other.sharedGroup? == c.sharedGroup? then
              match other.tx with
              | .deferred (some s) => some s
              | _ => other.readSnap?
            else none
    match pinned? with
    | some (_, snap) => snap
    | none =>
      match c.backing with
      | .memory cat _ => cat
      | .sharedMemory k =>
        match lookupMemStore? st k with
        | some (_, cat) => cat
        | none => {}
      | .file p =>
        match lookupFile? st p with
        | some (.dbFile _ _ _ cat) => cat
        | _ => {}

private def connCommittedCatalog (st : SqliteWorldState) (c : ConnState) : Nat × DbCatalog × Bool :=
  match c.backing with
  | .memory cat epoch => (epoch, cat, true)
  | .sharedMemory k =>
    let isMemdbPager := k.startsWith "memdb:"
    match lookupMemStore? st k with
    | some (epoch, cat) => (epoch, cat, !isMemdbPager)
    | none => (0, {}, !isMemdbPager)
  | .file p =>
    match lookupFile? st p with
    | some (.dbFile isWal _ epoch cat) => (epoch, cat, isWal)
    | _ => (0, {}, true)

private def hasActiveScanOnConn (st : SqliteWorldState) (dbId : UInt64) : Bool :=
  st.stmts.any fun s => s.handle.dbId == dbId && s.holdsReadLock

private def samePagerResource (a b : ConnBacking) : Bool :=
  match a, b with
  | .file p1, .file p2 => p1 == p2
  | .sharedMemory k1, .sharedMemory k2 => k1 == k2 && k1.startsWith "memdb:"
  | _, _ => false

private def peerContendsAtPager (self other : ConnState) : Bool :=
  self.id != other.id &&
  !self.noLock &&
  !other.noLock &&
  ((self.vfsName == "unix-dotfile") == (other.vfsName == "unix-dotfile")) &&
  !(self.sharedGroup?.isSome && self.sharedGroup? == other.sharedGroup?) &&
  samePagerResource self.backing other.backing

private def connHoldsAnyPagerLock (st : SqliteWorldState) (c : ConnState) : Bool :=
  c.pendingLock || hasActiveScanOnConn st c.id || match c.tx with
  | .write _ _ => true
  | .deferred (some _) => true
  | _ => false

private def hasOtherPagerWriter (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    peerContendsAtPager self other &&
    match other.tx with
    | .write _ _ => true
    | _ => false

private def hasOtherPagerReader (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    peerContendsAtPager self other &&
    (hasActiveScanOnConn st other.id || match other.tx with | .deferred (some _) => true | _ => false)

private def hasOtherPagerPending (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    peerContendsAtPager self other &&
    (other.pendingLock ||
      (self.vfsName == "memdb" && match other.tx with | .write _ _ => true | _ => false) ||
      (self.vfsName == "unix-dotfile" && other.vfsName == "unix-dotfile" &&
        connHoldsAnyPagerLock st other))

private def hasDotfileExclusiveConflict (st : SqliteWorldState) (self : ConnState) : Bool :=
  self.vfsName == "unix-dotfile" && !self.noLock &&
  st.conns.any fun other =>
    peerContendsAtPager self other &&
    other.vfsName == "unix-dotfile" &&
    connHoldsAnyPagerLock st other

private def sameSharedGroup (self other : ConnState) : Bool :=
  self.id != other.id && self.sharedGroup?.isSome && self.sharedGroup? == other.sharedGroup?

private def connHasSharedBtTrans (st : SqliteWorldState) (c : ConnState) : Bool :=
  hasActiveScanOnConn st c.id || match c.tx with
  | .write _ _ | .deferred (some _) => true
  | _ => false

private def hasSharedGroupPending (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other => sameSharedGroup self other && other.sharedPending

private def hasAnySharedGroupTxOrLock (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    sameSharedGroup self other && (other.sharedPending || connHasSharedBtTrans st other)

private def sharedGroupPinnedSnap? (st : SqliteWorldState) (self : ConnState) :
    Option (Nat × DbCatalog) :=
  if self.sharedGroup?.isNone then none
  else
    st.conns.findSome? fun other =>
      if !sameSharedGroup self other then none
      else
        match other.tx with
        | .deferred (some s) => some s
        | _ => other.readSnap?

private def syncSharedGroupSchema (st : SqliteWorldState) (grp? : Option (String × String))
    (sc? : Option (List String)) : SqliteWorldState :=
  match grp? with
  | none => st
  | some grp =>
    { st with conns := st.conns.map fun x =>
        if x.sharedGroup? == some grp then { x with schemaCache? := sc? } else x }

private def clearSharedPendingIfLastReader (st : SqliteWorldState)
    (grp? : Option (String × String)) : SqliteWorldState :=
  match grp? with
  | none => st
  | some grp =>
    let hasPendingWriter := st.conns.any fun c =>
      c.sharedGroup? == some grp && c.sharedPending
    if !hasPendingWriter then st
    else
      let hasOtherReader := st.conns.any fun c =>
        c.sharedGroup? == some grp &&
        (match c.tx with | .write _ _ => false | _ => true) &&
        connHasSharedBtTrans st c
      if hasOtherReader then st
      else
        { st with conns := st.conns.map fun c =>
            if c.sharedGroup? == some grp && c.sharedPending then
              { c with sharedPending := false }
            else c }

private def findOpenSharedPeer? (st : SqliteWorldState) (grp : String × String) : Option ConnState :=
  st.conns.find? fun c => c.sharedGroup? == some grp

private def removeConn (st : SqliteWorldState) (dbId : UInt64) : SqliteWorldState :=
  let removed? := lookupConn? st dbId
  let nextConns := st.conns.filter (·.id != dbId)
  let nextMemStores :=
    if st.memStores.isEmpty then []
    else st.memStores.filter fun (k, _, _) => nextConns.any (connRefsMemStore k)
  let st1 := { st with conns := nextConns, memStores := nextMemStores }
  match removed? with
  | none => st1
  | some oldConn =>
    let st2 :=
      if oldConn.schemaDirty then syncSharedGroupSchema st1 oldConn.sharedGroup? none
      else st1
    clearSharedPendingIfLastReader st2 oldConn.sharedGroup?

private def hasSharedGroupWriter (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    sameSharedGroup self other &&
    match other.tx with
    | .write _ _ => true
    | _ => false

private def hasSharedSchemaWriteConflict (st : SqliteWorldState) (self : ConnState) : Bool :=
  st.conns.any fun other =>
    sameSharedGroup self other && other.sharedWriteTables.contains "*"

private def hasSharedGroupDirtyWriter (st : SqliteWorldState) (self : ConnState) (zeroPageDb : Bool) : Bool :=
  st.conns.any fun other =>
    sameSharedGroup self other &&
    match other.tx with
    | .write _ _ => other.writeDirty || zeroPageDb
    | _ => false

private def hasSharedTableReadConflict (st : SqliteWorldState) (self : ConnState) (tblName : String) : Bool :=
  let tLo := asciiLower tblName
  st.conns.any fun other =>
    sameSharedGroup self other &&
    (other.sharedWriteTables.contains "*" || other.sharedWriteTables.contains tLo)

private def connHoldsSharedReadOnTable (st : SqliteWorldState) (c : ConnState) (tLo : String) : Bool :=
  c.sharedReadTables.contains tLo ||
  c.sharedWriteTables.contains tLo ||
  st.stmts.any fun s =>
    s.handle.dbId == c.id && s.holdsReadLock &&
    match s.stmt with
    | .select _ (some stbl) _ _ _ => asciiLower stbl == tLo
    | _ => false

private def writeTouchedTables (stmt : SqlStmt) : List String :=
  match stmt with
  | .createTable _ _ _ _ => ["*"]
  | .insert tblName _ _ | .update tblName _ _ | .delete tblName _ => [asciiLower tblName]
  | _ => []

private def fkReadTouchedTables (cat : DbCatalog) (foreignKeys : Bool) (stmt : SqlStmt) : List String :=
  if !foreignKeys then []
  else
    match stmt with
    | .insert tblName _ tuples =>
      let selfLo := asciiLower tblName
      let outFks :=
        match lookupTable? cat tblName with
        | none => []
        | some tbl =>
          tbl.cols.filterMap fun cd =>
            match cd.references? with
            | some (pTab, _) =>
              let pLo := asciiLower pTab
              if (lookupTable? cat pLo).isSome then some pLo else none
            | none => none
      let inFks :=
        if tuples.length > 1 then
          cat.tables.filterMap fun (kLo, childTbl) =>
            if childTbl.cols.any (fun cd =>
                match cd.references? with
                | some (pTab, _) => asciiLower pTab == selfLo
                | none => false) then
              some kLo
            else none
        else []
      (outFks ++ inFks).filter (· != selfLo)
    | .update tblName assigns _ =>
      let selfLo := asciiLower tblName
      let loAssigned := assigns.map fun (colName, _) => asciiLower colName
      let outFks :=
        match lookupTable? cat tblName with
        | none => []
        | some tbl =>
          tbl.cols.filterMap fun cd =>
            match cd.references? with
            | some (pTab, _) =>
              let pLo := asciiLower pTab
              if loAssigned.contains (asciiLower cd.name) && (lookupTable? cat pLo).isSome then
                some pLo
              else none
            | none => none
      let inFks :=
        cat.tables.filterMap fun (kLo, childTbl) =>
          if childTbl.cols.any (fun cd =>
              match cd.references? with
              | some (pTab, pCol) => asciiLower pTab == selfLo && loAssigned.contains (asciiLower pCol)
              | none => false) then
            some kLo
          else none
      (outFks ++ inFks).filter (· != selfLo)
    | .delete tblName _ =>
      let selfLo := asciiLower tblName
      let outFks :=
        match lookupTable? cat tblName with
        | none => []
        | some tbl =>
          tbl.cols.filterMap fun cd =>
            match cd.references? with
            | some (pTab, _) =>
              let pLo := asciiLower pTab
              if (lookupTable? cat pLo).isSome then some pLo else none
            | none => none
      let inFks :=
        cat.tables.filterMap fun (kLo, childTbl) =>
          if childTbl.cols.any (fun cd =>
              match cd.references? with
              | some (pTab, _) => asciiLower pTab == selfLo
              | none => false) then
            some kLo
          else none
      (outFks ++ inFks).filter (· != selfLo)
    | _ => []

private def hasSharedWriteLockConflict (st : SqliteWorldState) (self : ConnState)
    (_cat : DbCatalog) (stmt : SqlStmt) : Bool :=
  if self.sharedGroup?.isNone then false
  else if hasSharedGroupWriter st self then true
  else
    let touched := writeTouchedTables stmt
    st.conns.any fun other =>
      sameSharedGroup self other &&
      if touched.contains "*" then
        connHasSharedBtTrans st other || !other.sharedReadTables.isEmpty
      else
        touched.any (connHoldsSharedReadOnTable st other)

private def addUniqueStrings (cur add : List String) : List String :=
  add.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) cur

private def retainedSharedReadTablesAfterEnd (st : SqliteWorldState) (c : ConnState)
    (extraRead : List String := []) (extraWrite : List String := []) : List String :=
  if c.sharedGroup?.isNone || !hasActiveScanOnConn st c.id then []
  else
    let allWrites := addUniqueStrings c.sharedWriteTables extraWrite
    let downgraded := allWrites.filter (· != "*")
    addUniqueStrings (addUniqueStrings c.sharedReadTables extraRead) downgraded

private def vfsSupportsWal (vfsName : String) (noLock : Bool) : Bool :=
  (vfsName == "unix" || vfsName == "unix-excl") && !noLock

private def fileHasLiveShm (st : SqliteWorldState) (p : String) : Bool :=
  st.conns.any fun x => x.backing == .file p && x.shmAttached

private def canAttachWalShm (st : SqliteWorldState) (p : String)
    (vfsName : String) (effRo readonlyShm : Bool) : Bool :=
  !readonlyShm || (vfsName == "unix-excl" && !effRo) || fileHasLiveShm st p

private def markConnShmAttached (st : SqliteWorldState) (c : ConnState) : SqliteWorldState × ConnState :=
  if c.shmAttached then (st, c)
  else
    let c' := { c with shmAttached := true }
    let st' := { st with conns := st.conns.map fun x =>
      if x.id == c.id || (c.sharedGroup?.isSome && x.sharedGroup? == c.sharedGroup?) then
        { x with shmAttached := true }
      else x }
    (st', c')

private def ensureWalShmAttachedConn (st : SqliteWorldState) (c : ConnState)
    (errPath? : Option String) : Except SqliteError (SqliteWorldState × ConnState) :=
  if c.immutableUri || c.shmAttached then .ok (st, c)
  else
    match c.backing with
    | .file p =>
      match lookupFile? st p with
      | some (.dbFile true _ _ _) =>
        if !vfsSupportsWal c.vfsName c.noLock then
          .error (mapRawError (.cantOpen errPath? 14 "unable to open database file"))
        else if canAttachWalShm st p c.vfsName c.effectiveReadOnly c.readonlyShm then
          .ok (markConnShmAttached st c)
        else
          .error (mapRawError (.cantOpen errPath? 14 "unable to open database file"))
      | _ => .ok (st, c)
    | _ => .ok (st, c)

private def isCorruptFileConn (st : SqliteWorldState) (c : ConnState) : Bool :=
  match c.backing with
  | .file p => lookupFile? st p == some .corruptFile
  | _ => false

private def isUnsupportedWalConn (st : SqliteWorldState) (c : ConnState) : Bool :=
  if c.immutableUri then false
  else
    match c.backing with
    | .file p =>
      match lookupFile? st p with
      | some (.dbFile true _ _ _) => !vfsSupportsWal c.vfsName c.noLock
      | _ => false
    | _ => false

private def splitSlashChars (cur : List Char) (acc : List (List Char)) : List Char → List (List Char)
  | [] => (if cur.isEmpty then acc else cur.reverse :: acc).reverse
  | '/' :: rest =>
    let acc' := if cur.isEmpty then acc else cur.reverse :: acc
    splitSlashChars [] acc' rest
  | c :: rest => splitSlashChars (c :: cur) acc rest

private def joinSegCharsAux (sepRev : List Char) (accRev : List Char) : List (List Char) → List Char
  | [] => accRev.reverse
  | [s] => accRev.reverseAux s
  | s :: rest => joinSegCharsAux sepRev (sepRev ++ s.reverse ++ accRev) rest

private def joinSegChars (sep : List Char) (segs : List (List Char)) : List Char :=
  joinSegCharsAux sep.reverse [] segs

private def prependDotDots : Nat → List (List Char) → List (List Char)
  | 0, segs => segs
  | n + 1, segs => prependDotDots n (['.', '.'] :: segs)

private def foldPathSegChars (abs : Bool) (up : Nat) (stack : List (List Char)) :
    List (List Char) → List Char
  | [] =>
    if abs then
      if stack.isEmpty then ['/'] else '/' :: joinSegChars ['/'] stack.reverse
    else if stack.isEmpty then
      if up == 0 then ['.'] else joinSegChars ['/'] (prependDotDots up [])
    else
      joinSegChars ['/'] (prependDotDots up stack.reverse)
  | ['.'] :: rest => foldPathSegChars abs up stack rest
  | ['.', '.'] :: rest =>
    match stack with
    | _ :: tail => foldPathSegChars abs up tail rest
    | [] => foldPathSegChars abs (if abs then 0 else up + 1) [] rest
  | seg :: rest => foldPathSegChars abs up (seg :: stack) rest

private def normalizePath (path : String) : String :=
  let cs := path.toList
  let abs := match cs with | '/' :: _ => true | _ => false
  String.ofList (foldPathSegChars abs 0 [] (splitSlashChars [] [] cs))

private def isRelativeDotDir (p : String) : Bool :=
  match p.toList with
  | ['.'] => true
  | '/' :: _ => false
  | cs => (splitSlashChars [] [] cs).all (· == ['.', '.'])

private def buildPathFromParts (abs : Bool) (up : Nat) (stackRev : List (List Char)) : String :=
  String.ofList (foldPathSegChars abs up stackRev [])

private def lookupSymlink? (st : SqliteWorldState) (p : String) : Option String :=
  let np := normalizePath p
  (st.symlinks.find? fun (k, _) =>
    let ek := encodeModelPathString k
    ek == p || normalizePath ek == np).map (fun (_, v) => encodeModelPathString v)

private def modelCharsByteLenLoop (esc : Bool) (acc : Nat) : List Char → Nat
  | [] => if esc then acc + 4 else acc
  | c :: rest =>
    if esc then
      modelCharsByteLenLoop false (acc + (if c == rawByteEscChar then 4 else 1)) rest
    else if c == rawByteEscChar then
      modelCharsByteLenLoop true acc rest
    else
      modelCharsByteLenLoop false (acc + c.utf8Size) rest

private def modelCharsByteLenAux (acc : Nat) (cs : List Char) : Nat :=
  modelCharsByteLenLoop false acc cs

private def modelStringByteLen (s : String) : Nat :=
  modelCharsByteLenAux 0 s.toList

private def hasSegmentOver255CharsLoop (esc : Bool) (curLen : Nat) : List Char → Bool
  | [] => if esc then curLen + 4 > 255 else false
  | c :: rest =>
    if esc then
      let next := curLen + (if c == rawByteEscChar then 4 else 1)
      if next > 255 then true
      else hasSegmentOver255CharsLoop false next rest
    else if c == '/' then
      hasSegmentOver255CharsLoop false 0 rest
    else if c == rawByteEscChar then
      hasSegmentOver255CharsLoop true curLen rest
    else
      let next := curLen + c.utf8Size
      if next > 255 then true
      else hasSegmentOver255CharsLoop false next rest

private def hasSegmentOver255CharsAux (curLen : Nat) (cs : List Char) : Bool :=
  hasSegmentOver255CharsLoop false curLen cs

private def hasSegmentOver255 (p : String) : Bool :=
  hasSegmentOver255CharsAux 0 p.toList

private def effectivePathnameBytes (st : SqliteWorldState) (p : String) : Nat :=
  let pLen := modelStringByteLen p
  if st.cwd == "" then
    pLen
  else
    match p.toList with
    | '/' :: _ => pLen
    | _ => modelStringByteLen (encodeModelPathString st.cwd) + 1 + pLen

private def parentDirOfPath (path : String) : String :=
  match (path.toList.reverse.dropWhile (· != '/')).reverse with
  | [] => "."
  | ['/'] => "/"
  | cs => String.ofList cs.dropLast

private def hasNonDirAncestorLoop (st : SqliteWorldState) (cur : String) : Nat → Bool
  | 0 => false
  | f + 1 =>
    let par := parentDirOfPath cur
    if par == cur || par == "/" || par == "." then false
    else
      match lookupFile? st par with
      | some (.dbFile _ _ _ _) | some .corruptFile => true
      | _ => hasNonDirAncestorLoop st par f

private def hasNonDirAncestor (st : SqliteWorldState) (p : String) : Bool :=
  hasNonDirAncestorLoop st p (p.length + 1)

private def resolvePathWithSymlinks (st : SqliteWorldState) (rawP : String) :
    Except SqliteRawError String :=
  let cs := rawP.toList
  let abs0 := match cs with | '/' :: _ => true | _ => false
  let segs0 := splitSlashChars [] [] cs
  let (initAbs, initSegs, cwdLen) :=
    if !abs0 && st.cwd != "" then
      let cwdEnc := encodeModelPathString st.cwd
      let cwdCs := cwdEnc.toList
      let cAbs := match cwdCs with | '/' :: _ => true | _ => false
      (cAbs, splitSlashChars [] [] cwdCs ++ segs0, cwdEnc.length)
    else
      (abs0, segs0, 0)
  let rec go (abs : Bool) (up : Nat) (stackRev : List (List Char))
      (rem : List (List Char)) (hops : Nat) (fuel : Nat) : Except SqliteRawError String :=
    match fuel with
    | 0 => .error (.cantOpen (some rawP) 14 "unable to open database file")
    | f + 1 =>
      match rem with
      | [] => .ok (buildPathFromParts abs up stackRev)
      | ['.'] :: rest => go abs up stackRev rest hops f
      | ['.', '.'] :: rest =>
        match stackRev with
        | _ :: tail => go abs up tail rest hops f
        | [] => go abs (if abs then 0 else up + 1) [] rest hops f
      | seg :: rest =>
        if modelCharsByteLenAux 0 seg > 255 then
          .error (.cantOpen (some rawP) 14 "unable to open database file")
        else
          let candPath := buildPathFromParts abs up (seg :: stackRev)
          if effectivePathnameBytes st candPath ≥ 512 || hasNonDirAncestor st candPath then
            .error (.cantOpen (some rawP) 14 "unable to open database file")
          else
            match lookupSymlink? st candPath with
            | some target =>
              if hops == 0 then
                .error (.cantOpen (some rawP) 14 "unable to open database file")
              else
                let tCs := target.toList
                let tAbs := match tCs with | '/' :: _ => true | _ => false
                let tSegs := splitSlashChars [] [] tCs
                if tAbs then
                  go true 0 [] (tSegs ++ rest) (hops - 1) f
                else
                  go abs up stackRev (tSegs ++ rest) (hops - 1) f
            | none =>
              go abs up (seg :: stackRev) rest hops f
  go initAbs 0 [] initSegs 201 (cwdLen + rawP.length + 201 * 64 + 512)

private def isDirPrefixChars : List Char → List Char → Bool
  | [], [] => true
  | [], '/' :: _ => true
  | p :: ps, d :: ds => p == d && isDirPrefixChars ps ds
  | _, _ => false

private def isKnownExistingDir (st : SqliteWorldState) (p : String) : Bool :=
  if p == "/" then true
  else if lookupFile? st p == some .directory then true
  else
    let pChars := p.toList
    let cwdMatch :=
      st.cwd != "" &&
      isDirPrefixChars pChars (normalizePath (encodeModelPathString st.cwd)).toList
    cwdMatch || st.existingDirs.any fun rawD =>
      isDirPrefixChars pChars (normalizePath (encodeModelPathString rawD)).toList

private def isValidParentDir (st : SqliteWorldState) (dir : String) : Bool :=
  dir == "." || isRelativeDotDir dir || isKnownExistingDir st dir

private def resolveStatPathWithSymlinks? (st : SqliteWorldState) (rawP : String) : Option String :=
  if rawP == "" || hasSegmentOver255 rawP then none
  else
    let cs := rawP.toList
    let abs0 := match cs with | '/' :: _ => true | _ => false
    let segs0 := splitSlashChars [] [] cs
    let (initAbs, initSegs, cwdLen) :=
      if !abs0 && st.cwd != "" then
        let cwdEnc := encodeModelPathString st.cwd
        let cwdCs := cwdEnc.toList
        let cAbs := match cwdCs with | '/' :: _ => true | _ => false
        (cAbs, splitSlashChars [] [] cwdCs ++ segs0, cwdEnc.length)
      else
        (abs0, segs0, 0)
    let rec go (abs : Bool) (up : Nat) (stackRev : List (List Char))
        (rem : List (List Char)) (hops : Nat) (fuel : Nat) : Option String :=
      match fuel with
      | 0 => none
      | f + 1 =>
        match rem with
        | [] => some (buildPathFromParts abs up stackRev)
        | ['.'] :: rest => go abs up stackRev rest hops f
        | ['.', '.'] :: rest =>
          match stackRev with
          | _ :: tail => go abs up tail rest hops f
          | [] => go abs (if abs then 0 else up + 1) [] rest hops f
        | seg :: rest =>
          if modelCharsByteLenAux 0 seg > 255 then none
          else
            let candPath := buildPathFromParts abs up (seg :: stackRev)
            if effectivePathnameBytes st candPath ≥ 4096 || hasNonDirAncestor st candPath then
              none
            else
              match lookupSymlink? st candPath with
              | some target =>
                if hops == 0 then none
                else
                  let tCs := target.toList
                  let tAbs := match tCs with | '/' :: _ => true | _ => false
                  let tSegs := splitSlashChars [] [] tCs
                  if tAbs then
                    go true 0 [] (tSegs ++ rest) (hops - 1) f
                  else
                    go abs up stackRev (tSegs ++ rest) (hops - 1) f
              | none =>
                go abs up (seg :: stackRev) rest hops f
    go initAbs 0 [] initSegs 40 (cwdLen + rawP.length + 40 * 64 + 512)

private def statModeofTarget (st : SqliteWorldState) (rawMode : String) :
    Except SqliteRawError Bool :=
  match resolveStatPathWithSymlinks? st rawMode with
  | none => .error (.ioFailure 1802 "disk I/O error")
  | some p =>
    if hasSegmentOver255 p || hasNonDirAncestor st p then
      .error (.ioFailure 1802 "disk I/O error")
    else if p == "/" || isRelativeDotDir p || isKnownExistingDir st p || lookupFile? st p == some .directory then
      .ok false
    else if rawMode.toList.getLast? == some '/' then
      .error (.ioFailure 1802 "disk I/O error")
    else
      match lookupFile? st p with
      | some (.dbFile _ osRo _ _) => .ok osRo
      | some .corruptFile => .ok false
      | _ => .error (.ioFailure 1802 "disk I/O error")

private def hexNibble? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x61 + 10)
  else none

private def pushRawByteEsc (b0 : UInt8) (acc : List Char) : List Char :=
  Char.ofNat (0x100 + b0.toNat) :: rawByteEscChar :: acc

private def decodeUriBytesToModelCharsAux (acc : List Char) : Nat → List UInt8 → List Char
  | 0, _ => acc.reverse
  | _, [] => acc.reverse
  | fuel + 1, b0 :: rest =>
    if b0 < 0x80 then
      decodeUriBytesToModelCharsAux (Char.ofNat b0.toNat :: acc) fuel rest
    else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
      match rest with
      | b1 :: rest1 =>
        if (b1 &&& 0xC0) == 0x80 then
          let cp := ((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F)
          decodeUriBytesToModelCharsAux (Char.ofNat cp :: acc) fuel rest1
        else
          decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
      | [] =>
        decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
    else if 0xE0 ≤ b0 && b0 ≤ 0xEF then
      match rest with
      | b1 :: b2 :: rest2 =>
        if (b1 &&& 0xC0) == 0x80 && (b2 &&& 0xC0) == 0x80 then
          let cp := ((b0.toNat &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| (b2.toNat &&& 0x3F)
          if cp ≥ 0x800 && !(0xD800 ≤ cp && cp ≤ 0xDFFF) then
            decodeUriBytesToModelCharsAux (Char.ofNat cp :: acc) fuel rest2
          else
            decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
        else
          decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
      | _ =>
        decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
    else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: rest3 =>
        if (b1 &&& 0xC0) == 0x80 && (b2 &&& 0xC0) == 0x80 && (b3 &&& 0xC0) == 0x80 then
          let cp := ((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) |||
                    ((b2.toNat &&& 0x3F) <<< 6) ||| (b3.toNat &&& 0x3F)
          if 0x10000 ≤ cp && cp ≤ 0x10FFFF then
            let acc' :=
              if cp == rawByteEscChar.toNat then rawByteEscChar :: rawByteEscChar :: acc
              else Char.ofNat cp :: acc
            decodeUriBytesToModelCharsAux acc' fuel rest3
          else
            decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
        else
          decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
      | _ =>
        decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest
    else
      decodeUriBytesToModelCharsAux (pushRawByteEsc b0 acc) fuel rest

private def decodeUriBytesToModelString (bs : List UInt8) : String :=
  String.ofList (decodeUriBytesToModelCharsAux [] bs.length bs)

private def splitFirstByteModelAux (delim : UInt8) (acc : List UInt8) :
    List UInt8 → List UInt8 × Option (List UInt8)
  | [] => (acc.reverse, none)
  | b :: bs =>
    if b == delim then (acc.reverse, some bs)
    else splitFirstByteModelAux delim (b :: acc) bs

private def splitOnByteModelAux (delim : UInt8) (cur : List UInt8) (acc : List (List UInt8)) :
    List UInt8 → List (List UInt8)
  | [] => (cur.reverse :: acc).reverse
  | b :: bs =>
    if b == delim then splitOnByteModelAux delim [] (cur.reverse :: acc) bs
    else splitOnByteModelAux delim (b :: cur) acc bs

private def parseHexNatAux (acc cnt : Nat) : List UInt8 → Option (Nat × Nat)
  | [] => some (acc, cnt)
  | b :: rest =>
    match hexValByte? b with
    | none => some (acc, cnt)
    | some nib =>
      if cnt ≥ 9 then none
      else parseHexNatAux (acc * 16 + nib.toNat) (cnt + 1) rest

private def parseDecNatAux (acc cnt : Nat) : List UInt8 → Option (Nat × Nat)
  | [] => some (acc, cnt)
  | b :: rest =>
    if 0x30 ≤ b && b ≤ 0x39 then
      if cnt ≥ 11 then none
      else parseDecNatAux (acc * 10 + (b - 0x30).toNat) (cnt + 1) rest
    else
      some (acc, cnt)

private def parseUriBoolBytes : List UInt8 → Bool
  | [] => false
  | b0 :: rest0 =>
    if 0x30 ≤ b0 && b0 ≤ 0x39 then
      match b0, rest0 with
      | 0x30, xByte :: h0 :: hRest =>
        if (xByte == 0x78 || xByte == 0x58) && (hexValByte? h0).isSome then
          let nz := (h0 :: hRest).dropWhile (· == 0x30)
          match parseHexNatAux 0 0 nz with
          | some (u, cnt) => cnt > 0 && cnt ≤ 8 && u < 0x80000000
          | none => false
        else
          let nz := (b0 :: rest0).dropWhile (· == 0x30)
          match parseDecNatAux 0 0 nz with
          | some (v, cnt) => cnt > 0 && cnt ≤ 10 && v ≤ 2147483647
          | none => false
      | _, _ =>
        let nz := (b0 :: rest0).dropWhile (· == 0x30)
        match parseDecNatAux 0 0 nz with
        | some (v, cnt) => cnt > 0 && cnt ≤ 10 && v ≤ 2147483647
        | none => false
    else
      let lo := (b0 :: rest0).map asciiLowerByte
      lo == [0x74, 0x72, 0x75, 0x65] || lo == [0x6F, 0x6E] || lo == [0x79, 0x65, 0x73]

private def isKnownSqliteVfs (v : String) : Bool :=
  v == "unix" || v == "unix-none" || v == "unix-dotfile" || v == "unix-excl" || v == "memdb"

private inductive RawOpenBackingSpec where
  | isolatedMemory
  | sharedMemory (storeKey : String) (sharedGroup? : Option (String × String))
  | file (rawPath : String) (sharedCache : Bool)

private def catTableNames (cat : DbCatalog) : List String :=
  cat.tables.map (·.1)

private def syncTableNames (cur? : Option (List String)) (cat : DbCatalog) : List String :=
  let base := (cur?.getD []).filter fun b => (lookupTable? cat b).isSome
  let extra := (catTableNames cat).filter fun k => !(base.any fun b => asciiLower b == asciiLower k)
  base ++ extra

private structure ParsedRawOpen where
  backing : RawOpenBackingSpec
  effRo : Bool
  effCreate : Bool
  uriRo : Bool
  enableWal : Bool := false
  vfsName : String := "unix"
  noLock : Bool := false
  immutableUri : Bool := false
  modeof? : Option String := none
  readonlyShm : Bool := false

private def findByteInBaAux (bs : ByteArray) (delim : UInt8) (idx stop : Nat) : Nat → Nat
  | 0 => stop
  | fuel + 1 =>
    if idx < stop then
      if byteAt bs idx == delim then idx
      else findByteInBaAux bs delim (idx + 1) stop fuel
    else
      stop

private def findByteInBa (bs : ByteArray) (delim : UInt8) (start stop : Nat) : Nat :=
  let stop' := min stop bs.size
  if start ≥ stop' then stop'
  else findByteInBaAux bs delim start stop' (stop' - start)

private def sliceBaToList (bs : ByteArray) (start stop : Nat) : List UInt8 :=
  baToListSlice bs start stop

private def decodeModelUriCompBaAux (bs : ByteArray) (idx stop : Nat) (acc : ByteArray) :
    Nat → ByteArray
  | 0 => acc
  | fuel + 1 =>
    if idx < stop then
      let b := byteAt bs idx
      if b == 0x25 && idx + 2 < stop then
        match hexValByte? (byteAt bs (idx + 1)), hexValByte? (byteAt bs (idx + 2)) with
        | some hi, some lo =>
          let decoded := (hi <<< 4) ||| lo
          if decoded == 0 then acc
          else decodeModelUriCompBaAux bs (idx + 3) stop (acc.push decoded) fuel
        | _, _ =>
          decodeModelUriCompBaAux bs (idx + 1) stop (acc.push b) fuel
      else if b == 0 then
        acc
      else
        decodeModelUriCompBaAux bs (idx + 1) stop (acc.push b) fuel
    else
      acc

private def decodeModelUriCompBa (bs : ByteArray) (start stop : Nat) (prefixSlash : Bool := false) :
    ByteArray :=
  let stop' := min stop bs.size
  let init :=
    if prefixSlash then (ByteArray.emptyWithCapacity 32).push 0x2F
    else ByteArray.emptyWithCapacity 32
  if start ≥ stop' then init
  else decodeModelUriCompBaAux bs start stop' init (stop' - start)

private def validateRawOpen (path : String) (cfg : OpenConfig) :
    Except SqliteRawError ParsedRawOpen := do
  validateConfigRaw cfg
  let bs := path.toUTF8
  if bs.size == 0 then
    .error (.invalidArgument "database path must not be empty")
  else if hasZeroByteIdx bs 0 then
    .error (.invalidArgument "database path contains embedded NUL byte")
  else if path == ":memory:" then
    .ok { backing := .isolatedMemory, effRo := cfg.readOnly, effCreate := false,
          uriRo := cfg.readOnly, enableWal := false }
  else if hasFileUriPrefix bs then
    let (pathStart, prefixSlash, emptyAfterAuth) ←
      if 6 < bs.size && byteAt bs 5 == 0x2F && byteAt bs 6 == 0x2F then
        let slashPos := findByteInBa bs 0x2F 7 bs.size
        if slashPos - 7 > 64 then
          let authSample := decodeUriBytesToModelString (sliceBaToList bs 7 (7 + 64))
          .error (.sqliteCodeError 1 s!"invalid uri authority: {authSample}")
        else
          let authStr := decodeUriBytesToModelString (sliceBaToList bs 7 slashPos)
          if authStr == "" || authStr == "localhost" then
            if slashPos < bs.size then .ok (slashPos + 1, true, false)
            else .ok (bs.size, false, true)
          else
            .error (.sqliteCodeError 1 s!"invalid uri authority: {authStr}")
      else
        .ok (5, false, false)
    let stopFrag := if emptyAfterAuth then pathStart else findByteInBa bs 0x23 pathStart bs.size
    let qPos := findByteInBa bs 0x3F pathStart stopFrag
    let decodedFileBa :=
      if emptyAfterAuth then ByteArray.empty
      else decodeModelUriCompBa bs pathStart qPos prefixSlash
    let initFlags : Nat := if cfg.readOnly then 1 else if cfg.createIfMissing then 6 else 2
    let mut curModeFlags : Nat := initFlags
    let mut immutableVal? : Option (List UInt8) := none
    let mut nolockVal? : Option (List UInt8) := none
    let mut modeofVal? : Option String := none
    let mut readonlyShmVal? : Option (List UInt8) := none
    let mut lastVfs? : Option String := none
    let mut lastCache : String := "private"
    if qPos < stopFrag then
      let mut segStart := qPos + 1
      let mut qDone := false
      for _ in [0 : stopFrag - qPos] do
        if !qDone then
          let segEnd := findByteInBa bs 0x26 segStart stopFrag
          let eqPos := findByteInBa bs 0x3D segStart segEnd
          if eqPos - segStart ≤ 64 then
            let rkDecBa := decodeModelUriCompBa bs segStart eqPos
            if rkDecBa.size > 0 then
              let k := decodeUriBytesToModelString (sliceBaToList rkDecBa 0 rkDecBa.size)
              let rvDecBa :=
                if eqPos < segEnd then decodeModelUriCompBa bs (eqPos + 1) segEnd
                else ByteArray.empty
              let rvDec :=
                if rvDecBa.size ≤ maxMemdbPathnameBytes + 64 then
                  sliceBaToList rvDecBa 0 rvDecBa.size
                else
                  sliceBaToList rvDecBa 0 (maxMemdbPathnameBytes + 64)
              let v := decodeUriBytesToModelString rvDec
              if k == "cache" then
                if v != "shared" && v != "private" then
                  .error (.sqliteCodeError 1 s!"no such cache mode: {v}")
                lastCache := v
              else if k == "vfs" then
                lastVfs? := some v
              else if k == "immutable" then
                if immutableVal?.isNone then
                  immutableVal? := some rvDec
              else if k == "nolock" then
                if nolockVal?.isNone then
                  nolockVal? := some rvDec
              else if k == "modeof" then
                if modeofVal?.isNone then
                  modeofVal? := some v
              else if k == "readonly_shm" then
                if readonlyShmVal?.isNone then
                  readonlyShmVal? := some rvDec
              else if k == "mode" then
                let modeBits ←
                  if v == "ro" then .ok 1
                  else if v == "rw" then .ok 2
                  else if v == "rwc" then .ok 6
                  else if v == "memory" then .ok 0x80
                  else .error (.sqliteCodeError 1 s!"no such access mode: {v}")
                if (modeBits &&& 0x7F) > curModeFlags then
                  .error (.sqliteCodeError 3 s!"access mode not allowed: {v}")
                curModeFlags := modeBits
          if segEnd < stopFrag then
            segStart := segEnd + 1
          else
            qDone := true
    if let some vfsArg := lastVfs? then
      if !isKnownSqliteVfs vfsArg then
        .error (.sqliteCodeError 1 s!"no such vfs: {vfsArg}")
    let effVfs := lastVfs?.getD "unix"
    let immutableFlag := match immutableVal? with | some iv => parseUriBoolBytes iv | none => false
    let nolockFlag := match nolockVal? with | some nv => parseUriBoolBytes nv | none => false
    let readonlyShmFlag := match readonlyShmVal? with | some rv => parseUriBoolBytes rv | none => false
    let isSharedCache := lastCache == "shared" && decodedFileBa.size > 0
    if decodedFileBa.size > maxMemdbPathnameBytes && curModeFlags != 0x80 then
      .error (.cantOpen (some path) 14 "unable to open database file")
    else if curModeFlags == 0x80 && !isSharedCache then
      let isRo := curModeFlags == 1
      let uriRo := curModeFlags == 0x80 || isRo || cfg.readOnly
      .ok { backing := .isolatedMemory, effRo := isRo, effCreate := false, uriRo := uriRo,
            enableWal := false, vfsName := effVfs }
    else
      let decodedFile := sliceBaToList decodedFileBa 0 decodedFileBa.size
      let fileStr := decodeUriBytesToModelString decodedFile
      let enableWal :=
        !cfg.readOnly && cfg.walMode && fileStr != ":memory:" && curModeFlags != 0x80 && curModeFlags != 1
      if decodedFile.isEmpty then
        let isRo := curModeFlags == 1
        .ok { backing := .isolatedMemory, effRo := isRo, effCreate := false,
              uriRo := curModeFlags == 0x80 || isRo || cfg.readOnly,
              enableWal := enableWal, vfsName := effVfs }
      else if curModeFlags == 0x80 || fileStr == ":memory:" then
        let isRo := curModeFlags == 1
        let uriRo := curModeFlags == 0x80 || isRo || cfg.readOnly
        if isSharedCache then
          .ok { backing := .sharedMemory ("shared:" ++ effVfs ++ ":" ++ fileStr) (some (effVfs, fileStr)),
                effRo := isRo, effCreate := false, uriRo := uriRo,
                enableWal := false, vfsName := effVfs }
        else
          .ok { backing := .isolatedMemory, effRo := isRo, effCreate := false, uriRo := uriRo,
                enableWal := false, vfsName := effVfs }
      else if effVfs == "memdb" then
        let fLen := decodedFile.length
        if fLen > maxMemdbPathnameBytes then
          .error (.cantOpen (some path) 14 "unable to open database file")
        else
          let isRo := curModeFlags == 1 || immutableFlag
          let uriRo := curModeFlags == 1 || cfg.readOnly
          let noLock := nolockFlag || immutableFlag
          let b0 := decodedFile.headD 0
          let isNamedMemdb := fLen ≥ 2 && (b0 == 0x2F || b0 == 0x5C)
          let grp? := if isSharedCache then some ("memdb", fileStr) else none
          if isNamedMemdb then
            .ok { backing := .sharedMemory ("memdb:" ++ fileStr) grp?,
                  effRo := isRo, effCreate := false, uriRo := uriRo, enableWal := enableWal,
                  vfsName := "memdb", noLock := noLock, immutableUri := immutableFlag }
          else if isSharedCache then
            .ok { backing := .sharedMemory ("shared:memdb:" ++ fileStr) grp?,
                  effRo := isRo, effCreate := false, uriRo := uriRo, enableWal := enableWal,
                  vfsName := "memdb", noLock := noLock, immutableUri := immutableFlag }
          else
            .ok { backing := .isolatedMemory, effRo := isRo, effCreate := false, uriRo := uriRo,
                  enableWal := enableWal, vfsName := "memdb", noLock := noLock, immutableUri := immutableFlag }
      else
        let isRo := if curModeFlags == 1 then true else immutableFlag
        let effCreate := if curModeFlags == 6 then !immutableFlag else false
        let uriRo := if curModeFlags == 1 then true else cfg.readOnly
        let noLock := effVfs == "unix-none" || nolockFlag || immutableFlag
        .ok { backing := .file fileStr isSharedCache,
              effRo := isRo, effCreate := effCreate, uriRo := uriRo, enableWal := enableWal,
              vfsName := effVfs, noLock := noLock, immutableUri := immutableFlag,
              modeof? := modeofVal?, readonlyShm := readonlyShmFlag }
  else
    .ok { backing := .file (encodeModelPathString path) false, effRo := cfg.readOnly, effCreate := cfg.createIfMissing,
          uriRo := cfg.readOnly, enableWal := !cfg.readOnly && cfg.walMode }

private def openAttachedSharedPeer (path : String) (cfg : OpenConfig) (parsed : ParsedRawOpen)
    (grp : String × String) (peer : ConnState) (st : SqliteWorldState) :
    Except SqliteError DbHandle × SqliteWorldState :=
  let runsFkPragma := cfg.foreignKeys
  let runsWalPragma := parsed.enableWal
  let id := st.nextDbId
  let conn : ConnState :=
    { id := id
      backing := peer.backing
      effectiveReadOnly := peer.effectiveReadOnly
      foreignKeys := cfg.foreignKeys
      schemaCache? := peer.schemaCache?
      vfsName := peer.vfsName
      noLock := peer.noLock
      immutableUri := peer.immutableUri
      sharedGroup? := some grp
      readonlyShm := peer.readonlyShm
      shmAttached := peer.shmAttached }
  if (runsFkPragma || runsWalPragma) && hasSharedSchemaWriteConflict st conn then
    (.error (mapRawError (.busy 262 "database schema is locked: main")), st)
  else if runsWalPragma then
    match peer.backing with
    | .sharedMemory sk =>
      if peer.schemaCache?.isNone && hasOtherPagerPending st conn then
        (.error (mapRawError (.busy 5 "database is locked")), st)
      else
        let existingCat := match lookupMemStore? st sk with | some (_, cat) => cat | none => {}
        let sc := some (syncTableNames peer.schemaCache? existingCat)
        let stAdded := { st with nextDbId := id + 1, conns := st.conns ++ [{ conn with schemaCache? := sc }] }
        (.ok { id := id }, syncSharedGroupSchema stAdded (some grp) sc)
    | .file p =>
      match lookupFile? st p with
      | some .corruptFile =>
        (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
      | some (.dbFile isWal osRo epoch cat) =>
        let walSup := vfsSupportsWal peer.vfsName peer.noLock
        let schemaReadBusy :=
          peer.schemaCache?.isNone &&
          (if isWal then hasDotfileExclusiveConflict st conn else hasOtherPagerPending st conn)
        let sc := some (syncTableNames peer.schemaCache? cat)
        if isWal && !walSup && !peer.immutableUri then
          (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
        else if isWal && walSup && !peer.immutableUri && !peer.shmAttached &&
            !canAttachWalShm st p peer.vfsName peer.effectiveReadOnly peer.readonlyShm then
          (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
        else if schemaReadBusy then
          (.error (mapRawError (.busy 5 "database is locked")), st)
        else if !isWal && walSup && !peer.immutableUri then
          if hasSharedGroupDirtyWriter st conn (epoch == 0) then
            let stAdded := { st with nextDbId := id + 1, conns := st.conns ++ [{ conn with schemaCache? := sc }] }
            (.ok { id := id }, syncSharedGroupSchema stAdded (some grp) sc)
          else if peer.effectiveReadOnly || osRo then
            (.error (mapRawError (.ioFailure 8 "attempt to write a readonly database")), st)
          else if hasAnySharedGroupTxOrLock st conn then
            (.error (mapRawError (.busy 262 "database table is locked")), st)
          else if !peer.noLock &&
              (hasOtherPagerWriter st conn || hasOtherPagerReader st conn ||
               hasOtherPagerPending st conn) then
            (.error (mapRawError (.busy 5 "database is locked")), st)
          else
            let st1 := setFileNode st p (.dbFile true osRo epoch cat)
            let id1 := st1.nextDbId
            let stAdded := { st1 with nextDbId := id1 + 1, conns := st1.conns ++ [{ conn with id := id1, schemaCache? := sc }] }
            (.ok { id := id1 }, syncSharedGroupSchema stAdded (some grp) sc)
        else
          let attachNow := isWal && walSup && !peer.immutableUri
          let connAdd := { conn with schemaCache? := sc, shmAttached := conn.shmAttached || attachNow }
          let stBase :=
            if attachNow && !peer.shmAttached then (markConnShmAttached st peer).1 else st
          let stAdded := { stBase with nextDbId := id + 1, conns := stBase.conns ++ [connAdd] }
          (.ok { id := id }, syncSharedGroupSchema stAdded (some grp) sc)
      | _ =>
        (.ok { id := id }, { st with nextDbId := id + 1, conns := st.conns ++ [conn] })
    | .memory _ _ =>
      (.ok { id := id }, { st with nextDbId := id + 1, conns := st.conns ++ [conn] })
  else
    (.ok { id := id }, { st with nextDbId := id + 1, conns := st.conns ++ [conn] })

private def modelOpenDb (path : String) (cfg : OpenConfig) (st : SqliteWorldState) :
    Except SqliteError DbHandle × SqliteWorldState :=
  match validateRawOpen path cfg with
  | .error rawErr => (.error (mapRawError rawErr), st)
  | .ok parsed =>
    match parsed.backing with
    | .isolatedMemory =>
      let id := st.nextDbId
      let conn : ConnState :=
        { id := id
          backing := .memory {} 0
          effectiveReadOnly := parsed.effRo
          foreignKeys := cfg.foreignKeys
          vfsName := parsed.vfsName
          noLock := parsed.noLock
          immutableUri := parsed.immutableUri
          schemaCache? := if parsed.enableWal then some [] else none }
      (.ok { id := id }, { st with nextDbId := id + 1, conns := st.conns ++ [conn] })
    | .sharedMemory storeKey grp? =>
      match grp?.bind (fun g => (findOpenSharedPeer? st g).map (g, ·)) with
      | some (grp, peer) =>
        openAttachedSharedPeer path cfg parsed grp peer st
      | none =>
        let id := st.nextDbId
        let existingCat := match lookupMemStore? st storeKey with | some (_, cat) => cat | none => {}
        let conn : ConnState :=
          { id := id
            backing := .sharedMemory storeKey
            effectiveReadOnly := parsed.effRo
            foreignKeys := cfg.foreignKeys
            vfsName := parsed.vfsName
            noLock := parsed.noLock
            immutableUri := parsed.immutableUri
            sharedGroup? := grp?
            schemaCache? := if parsed.enableWal then some (catTableNames existingCat) else none }
        if parsed.enableWal && hasOtherPagerPending st conn then
          (.error (mapRawError (.busy 5 "database is locked")), st)
        else
          let st1 :=
            match lookupMemStore? st storeKey with
            | some _ => st
            | none => { st with memStores := st.memStores ++ [(storeKey, 0, DbCatalog.mk [])] }
          (.ok { id := id }, { st1 with nextDbId := id + 1, conns := st1.conns ++ [conn] })
    | .file rawP isSharedCache =>
      if hasSegmentOver255 rawP then
        (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
      else
        match resolvePathWithSymlinks st rawP with
        | .error (.cantOpen _ code detail) => (.error (mapRawError (.cantOpen (some path) code detail)), st)
        | .error rawErr => (.error (mapRawError rawErr), st)
        | .ok p =>
          match if isSharedCache then findOpenSharedPeer? st (parsed.vfsName, p) else none with
          | some peer =>
            openAttachedSharedPeer path cfg parsed (parsed.vfsName, p) peer st
          | none =>
            if effectivePathnameBytes st p > maxUnixPathnameBytes || hasSegmentOver255 p || hasNonDirAncestor st p then
              (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
            else if p == "/" then
              (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
            else
              match match parsed.modeof? with | some zm => statModeofTarget st zm | none => .ok false with
              | .error rawErr =>
                (.error (mapRawError rawErr), st)
              | .ok modeRo =>
                if isRelativeDotDir p || isKnownExistingDir st p || lookupFile? st p == some .directory then
                  if parsed.effRo then
                    (.error (mapRawError (.ioFailure 266 "disk I/O error")), st)
                  else
                    (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
                else
                  let dir := parentDirOfPath p
                  if !isValidParentDir st dir then
                    (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
                  else
                    let grp? := if isSharedCache then some (parsed.vfsName, p) else none
                    let mkConn := fun (cid : UInt64) (ro : Bool) (cache? : Option (List String)) (shm : Bool) =>
                      ({ id := cid
                         backing := .file p
                         effectiveReadOnly := ro
                         foreignKeys := cfg.foreignKeys
                         vfsName := parsed.vfsName
                         noLock := parsed.noLock
                         immutableUri := parsed.immutableUri
                         sharedGroup? := grp?
                         schemaCache? := cache?
                         readonlyShm := parsed.readonlyShm
                         shmAttached := shm } : ConnState)
                    match lookupFile? st p with
                    | some .directory =>
                      if parsed.effRo then
                        (.error (mapRawError (.ioFailure 266 "disk I/O error")), st)
                      else
                        (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
                    | some .corruptFile =>
                      if parsed.enableWal then
                        (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
                      else
                        let id := st.nextDbId
                        (.ok { id := id }, { st with nextDbId := id + 1, conns := st.conns ++ [mkConn id parsed.effRo none false] })
                    | none =>
                      if !parsed.effCreate then
                        (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st)
                      else
                        let walSup := vfsSupportsWal parsed.vfsName parsed.noLock
                        let walActive := parsed.enableWal && walSup
                        let initCache? := if parsed.enableWal then some [] else none
                        let st1 := setFileNode st p (.dbFile walActive modeRo 0 {})
                        let id := st1.nextDbId
                        (.ok { id := id }, { st1 with nextDbId := id + 1, conns := st1.conns ++ [mkConn id parsed.effRo initCache? false] })
                    | some (.dbFile isWal osRo epoch cat) =>
                      let finalRo := parsed.effRo || osRo
                      let diskRo := if parsed.modeof?.isSome && epoch == 0 && !finalRo then modeRo else osRo
                      let st0 := if diskRo != osRo then setFileNode st p (.dbFile isWal diskRo epoch cat) else st
                      let walSup := vfsSupportsWal parsed.vfsName parsed.noLock
                      let probeConn := mkConn st0.nextDbId finalRo none false
                      if parsed.enableWal then
                        let schemaReadBusy :=
                          if isWal then hasDotfileExclusiveConflict st0 probeConn
                          else hasOtherPagerPending st0 probeConn
                        if isWal && !walSup && !parsed.immutableUri then
                          (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st0)
                        else if isWal && walSup && !parsed.immutableUri &&
                            !canAttachWalShm st0 p parsed.vfsName finalRo parsed.readonlyShm then
                          (.error (mapRawError (.cantOpen (some path) 14 "unable to open database file")), st0)
                        else if schemaReadBusy then
                          (.error (mapRawError (.busy 5 "database is locked")), st0)
                        else if !isWal && walSup then
                          if osRo then
                            (.error (mapRawError (.ioFailure 8 "attempt to write a readonly database")), st0)
                          else if hasOtherPagerWriter st0 probeConn || hasOtherPagerReader st0 probeConn ||
                              hasOtherPagerPending st0 probeConn then
                            (.error (mapRawError (.busy 5 "database is locked")), st0)
                          else
                            let st1 := setFileNode st0 p (.dbFile true diskRo epoch cat)
                            let id := st1.nextDbId
                            (.ok { id := id }, { st1 with nextDbId := id + 1,
                                                          conns := st1.conns ++ [mkConn id finalRo (some (catTableNames cat)) false] })
                        else
                          let attachNow := isWal && walSup && !parsed.immutableUri
                          let id := st0.nextDbId
                          (.ok { id := id }, { st0 with nextDbId := id + 1,
                                                        conns := st0.conns ++ [mkConn id finalRo (some (catTableNames cat)) attachNow] })
                      else
                        let id := st0.nextDbId
                        (.ok { id := id }, { st0 with nextDbId := id + 1, conns := st0.conns ++ [mkConn id finalRo none false] })

private def modelCloseDb (db : DbHandle) (st : SqliteWorldState) :
    Except SqliteError Unit × SqliteWorldState :=
  match lookupConn? st db.id with
  | none => (.error (mapRawError (.misuse 21 "invalid or closed database handle")), st)
  | some _ =>
    if st.stmts.any (fun s => s.handle.dbId == db.id) then
      (.error (mapRawError (.busy 5 "unable to close database due to unfinalized statements")), st)
    else
      (.ok (), removeConn st db.id)

private def isDdlStmt : SqlStmt → Bool
  | .createTable _ _ _ _ => true
  | _ => false

private def modelPrepare (db : DbHandle) (sql : String) (st : SqliteWorldState) :
    Except SqliteError StmtHandle × SqliteWorldState :=
  let bs := sql.toUTF8
  if bs.size > LeanSwe.Sqlite.Raw.maxSqlByteLen then
    (.error (mapRawError (.invalidArgument "SQL statement exceeds maximum byte length")), st)
  else if hasZeroByteIdx bs 0 then
    (.error (mapRawError (.invalidArgument "SQL string contains embedded NUL byte")), st)
  else
    match lookupConn? st db.id with
    | none => (.error (mapRawError (.misuse 21 "invalid or closed database handle")), st)
    | some conn =>
      if hasSharedSchemaWriteConflict st conn then
        (.error (mapRawError (.busy 262 "database schema is locked: main")), st)
      else
        let effReadSnap? := conn.readSnap? <|> sharedGroupPinnedSnap? st conn
        let initSharedPendingBlocked :=
          conn.schemaCache?.isNone && !connHasSharedBtTrans st conn && hasSharedGroupPending st conn
        let initPagerSharedBlocked :=
          conn.schemaCache?.isNone && effReadSnap?.isNone &&
          (conn.tx == .autocommit || conn.tx == .deferred none) &&
          let (_, _, isWal) := connCommittedCatalog st conn
          if isWal then hasDotfileExclusiveConflict st conn else hasOtherPagerPending st conn
        match parseRawSqlNoCap bs with
        | .error rawErr =>
          let (immediateErr, firstNonTx, mappedErr) : Bool × Bool × SqliteRawError :=
            match rawErr with
            | .invalidArgument msg =>
              if (parseRawSqlNoCapWith false bs).isOk then
                (false, true, .sqliteCodeError 1 msg)
              else
                (true, false, .sqliteCodeError 1 msg)
            | _ =>
              let fnt :=
                match lexSqlBaAux true (mkLexCursor bs) [] (bs.size + 1) with
                | .ok firstToks =>
                  match parseTokensToStmt firstToks with
                  | some (.begin _, _) | some (.commit, _) | some (.rollback, _) | none => false
                  | some _ => true
                | .error _ => false
              (false, fnt, rawErr)
          if immediateErr then
            (.error (mapRawError mappedErr), st)
          else if isCorruptFileConn st conn && firstNonTx then
            (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
          else if isUnsupportedWalConn st conn && firstNonTx then
            (.error (mapRawError (.cantOpen none 14 "unable to open database file")), st)
          else
            match if firstNonTx && conn.schemaCache?.isNone then ensureWalShmAttachedConn st conn none else .ok (st, conn) with
            | .error e => (.error e, st)
            | .ok (stShm, _) =>
              if initSharedPendingBlocked && firstNonTx then
                (.error (mapRawError (.busy 262 "database table is locked")), stShm)
              else if initPagerSharedBlocked && firstNonTx then
                (.error (mapRawError (.busy 5 "database is locked")), stShm)
              else
                (.error (mapRawError mappedErr), stShm)
        | .ok (parsed, paramCount) =>
          let allowCorrupt :=
            match parsed with
            | .begin _ | .commit | .rollback => true
            | _ => false
          if isCorruptFileConn st conn && !allowCorrupt then
            (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
          else if isUnsupportedWalConn st conn && !allowCorrupt then
            (.error (mapRawError (.cantOpen none 14 "unable to open database file")), st)
          else
            match if !allowCorrupt && conn.schemaCache?.isNone then ensureWalShmAttachedConn st conn none else .ok (st, conn) with
            | .error e => (.error e, st)
            | .ok (stShm, connShm) =>
              if !allowCorrupt && initSharedPendingBlocked then
                (.error (mapRawError (.busy 262 "database table is locked")), stShm)
              else if !allowCorrupt && initPagerSharedBlocked then
                (.error (mapRawError (.busy 5 "database is locked")), stShm)
              else
                let visCat := connVisibleCatalog stShm connShm
                let (valRes, nextCache?) :=
                  match parsed with
                  | .begin _ | .commit | .rollback =>
                    (validateStmtSchema visCat connShm.foreignKeys parsed, connShm.schemaCache?)
                  | .createTable ifNotExists tblName cols _ =>
                    let cachedNames := connShm.schemaCache?.getD (catTableNames visCat)
                    let createVal : Except SqliteError Unit :=
                      if cachedNames.any (fun k => asciiLower k == asciiLower tblName) then
                        if ifNotExists then .ok ()
                        else .error (mapRawError (.sqliteCodeError 1 s!"table {tblName} already exists"))
                      else
                        match hasDuplicateColNames (cols.map ColDef.name) with
                        | some dup => .error (mapRawError (.sqliteCodeError 1 s!"duplicate column name: {dup}"))
                        | none =>
                          if (cols.filter ColDef.primaryKey).length > 1 then
                            .error (mapRawError (.sqliteCodeError 1 s!"table {tblName} has more than one primary key"))
                          else
                            .ok ()
                    (createVal, some cachedNames)
                  | .select _ none _ _ _ =>
                    let cachedNames := connShm.schemaCache?.getD (catTableNames visCat)
                    (validateStmtSchema visCat connShm.foreignKeys parsed, some cachedNames)
                  | _ =>
                    let cachedNames := connShm.schemaCache?.getD (catTableNames visCat)
                    let res := validateStmtSchema visCat connShm.foreignKeys parsed
                    let nextNames :=
                      match res with
                      | .error _ => syncTableNames connShm.schemaCache? visCat
                      | .ok () => cachedNames
                    (res, some nextNames)
                let stCached :=
                  syncSharedGroupSchema (replaceConn stShm { connShm with schemaCache? := nextCache? })
                    connShm.sharedGroup? nextCache?
                match valRes with
                | .error e => (.error e, stCached)
                | .ok () =>
                  let sh : StmtHandle := { id := stCached.nextStmtId, dbId := db.id }
                  let entry : ModelStmtState :=
                    { handle := sh, stmt := parsed, paramCount := paramCount }
                  (.ok sh, { stCached with nextStmtId := stCached.nextStmtId + 1, stmts := stCached.stmts ++ [entry] })

private def isTooBigValue : SqliteValue → Bool
  | .text s => s.toUTF8.size > maxBindValueBytes
  | .bytes ba => ba.size > maxBindValueBytes
  | _ => false

private def findTooBigIdxAux (params : Array SqliteValue) (i : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
    if h : i < params.size then
      if isTooBigValue params[i] then some i else findTooBigIdxAux params (i + 1) rem
    else none

private def truncateParamsFromAux (params : Array SqliteValue) (k i : Nat) (acc : Array SqliteValue) :
    Nat → Array SqliteValue
  | 0 => acc
  | rem + 1 =>
    if h : i < params.size then
      let v := if i < k then params[i] else .null
      truncateParamsFromAux params k (i + 1) (acc.push v) rem
    else acc

private def clearReadSnapIfIdle (st : SqliteWorldState) (dbId : UInt64) : SqliteWorldState :=
  if hasActiveScanOnConn st dbId then st
  else
    match lookupConn? st dbId with
    | none => st
    | some conn =>
      let clearSharedReads := conn.tx == .autocommit && !conn.sharedReadTables.isEmpty
      let st1 :=
        if conn.readSnap?.isNone && !clearSharedReads then st
        else
          { st with conns := st.conns.map fun x =>
              if x.id == dbId then
                { x with readSnap? := none,
                         sharedReadTables := if conn.tx == .autocommit then [] else x.sharedReadTables }
              else x }
      clearSharedPendingIfLastReader st1 conn.sharedGroup?

private def modelBind (stmt : StmtHandle) (params : Array SqliteValue) (st : SqliteWorldState) :
    Except SqliteError Unit × SqliteWorldState :=
  match st.stmts.find? (fun s => s.handle == stmt) with
  | none => (.error (mapRawError (.misuse 21 "invalid or finalized statement handle")), st)
  | some entry =>
    match entry.err? with
    | some e =>
      let resetErr := st.stmts.map fun s =>
        if s.handle == stmt then
          { s with stepIdx := 0, resultRows? := none, holdsReadLock := false, relBranches := [], rollbackMayAbort := false, err? := none }
        else s
      (.error e, clearReadSnapIfIdle { st with stmts := resetErr } entry.handle.dbId)
    | none =>
      let resetStmts := st.stmts.map fun s =>
        if s.handle == stmt then
          { s with boundParams? := none, stepIdx := 0, resultRows? := none, holdsReadLock := false, relBranches := [], rollbackMayAbort := false, err? := none }
        else s
      let st0 := clearReadSnapIfIdle { st with stmts := resetStmts } entry.handle.dbId
      if params.size != entry.paramCount then
        (.error (mapRawError (.invalidArgument
          s!"parameter count mismatch: expected {entry.paramCount}, got {params.size}")),
          st0)
      else
        match findTooBigIdxAux params 0 params.size with
        | some k =>
          let partialParams := truncateParamsFromAux params k 0 (Array.mkEmpty params.size) params.size
          let updated := st0.stmts.map fun s =>
            if s.handle == stmt then { s with boundParams? := some partialParams } else s
          (.error (mapRawError (.sqliteCodeError 18 "string or blob too big")),
            { st0 with stmts := updated })
        | none =>
          let updated := st0.stmts.map fun s =>
            if s.handle == stmt then { s with boundParams? := some params } else s
          (.ok (), { st0 with stmts := updated })

private def commitStagedCatalog (st : SqliteWorldState) (c : ConnState) (newCat : DbCatalog)
    (newTx : ConnTxState) : SqliteWorldState :=
  let (curEp, _, _) := connCommittedCatalog st c
  let newEp := curEp + 1
  let nextSnap? :=
    if newTx == .autocommit && (c.readSnap?.isSome || hasActiveScanOnConn st c.id) then
      some (newEp, newCat)
    else
      c.readSnap?
  let nextSc := some (syncTableNames c.schemaCache? newCat)
  let nextSR :=
    if newTx == .autocommit then retainedSharedReadTablesAfterEnd st c
    else c.sharedReadTables
  let c' := { c with tx := newTx, writeDirty := false, schemaDirty := false, pendingLock := false,
                     schemaCache? := nextSc,
                     readSnap? := nextSnap?,
                     sharedWriteTables := [], sharedReadTables := nextSR, sharedPending := false }
  let stCommitted :=
    match c.backing with
    | .memory _ epoch =>
      replaceConn st { c' with backing := .memory newCat (epoch + 1) }
    | .sharedMemory storeKey =>
      let st1 :=
        match lookupMemStore? st storeKey with
        | some (epoch, _) => setMemStore st storeKey (epoch + 1) newCat
        | none => setMemStore st storeKey 1 newCat
      replaceConn st1 c'
    | .file p =>
      let st1 :=
        match lookupFile? st p with
        | some (.dbFile isWal osRo epoch _) => setFileNode st p (.dbFile isWal osRo (epoch + 1) newCat)
        | _ => st
      replaceConn st1 c'
  match c.sharedGroup? with
  | none => stCommitted
  | some grp =>
    { stCommitted with conns := stCommitted.conns.map fun x =>
        if x.id != c.id && x.sharedGroup? == some grp then
          let xTx :=
            match x.tx with
            | .deferred (some _) => .deferred (some (newEp, newCat))
            | other => other
          let xSnap? := x.readSnap?.map fun _ => (newEp, newCat)
          { x with tx := xTx, readSnap? := xSnap?,
                   schemaCache? := some (syncTableNames x.schemaCache? newCat) }
        else x }

private def rollbackConnState (st : SqliteWorldState) (conn : ConnState)
    (curEpoch : Nat) (curCat : DbCatalog) : SqliteWorldState :=
  let trippedStmts :=
    if conn.schemaDirty then
      st.stmts.map fun s =>
        if s.handle.dbId == conn.id && s.holdsReadLock then
          { s with rollbackMayAbort := true }
        else s
    else
      st.stmts
  let stWithStmts := { st with stmts := trippedStmts }
  let nextCache? := if conn.schemaDirty then none else conn.schemaCache?
  let nextReadSnap? :=
    if hasActiveScanOnConn stWithStmts conn.id then
      conn.readSnap? <|> some (curEpoch, curCat)
    else
      none
  let nextSR := retainedSharedReadTablesAfterEnd stWithStmts conn
  let stRb :=
    replaceConn stWithStmts
      { conn with tx := .autocommit, writeDirty := false, schemaDirty := false, pendingLock := false,
                  schemaCache? := nextCache?, readSnap? := nextReadSnap?,
                  sharedWriteTables := [], sharedReadTables := nextSR, sharedPending := false }
  let stSynced :=
    if conn.schemaDirty then syncSharedGroupSchema stRb conn.sharedGroup? none
    else stRb
  clearSharedPendingIfLastReader stSynced conn.sharedGroup?

private def applyInsertWithWitness (actualRows : List SqliteRow)
    (cat : DbCatalog) (foreignKeys : Bool) (stmt : SqlStmt) (params : Array SqliteValue) :
    Except SqliteError (Bool × DbCatalog) × (Bool × DbCatalog) :=
  match stmt with
  | .insert tblName cols? tuples =>
    match lookupTable? cat tblName with
    | none => (.error (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}")), (false, cat))
    | some tbl =>
      match execInsertWithWitness tbl cols? tuples params actualRows with
      | .error e => (.error e, (false, cat))
      | .ok (curTbl, insertedArr) =>
        finishInsertCat cat tblName tbl curTbl insertedArr (tuples.length > 1) foreignKeys
  | _ => applyWriteStmtEx cat foreignKeys stmt params

private def executeModelWriteStmtWith
    (applyFn : DbCatalog → Bool → SqlStmt → Array SqliteValue →
      Except SqliteError (Bool × DbCatalog) × (Bool × DbCatalog))
    (st : SqliteWorldState) (conn : ConnState) (writeStmt : SqlStmt)
    (params : Array SqliteValue) : Except SqliteError (Array SqliteRow) × SqliteWorldState :=
  let (curEpoch, curCat, isWal) := connCommittedCatalog st conn
  let effReadSnap? := conn.readSnap? <|> sharedGroupPinnedSnap? st conn
  let otherPending :=
    if isWal then hasDotfileExclusiveConflict st conn
    else hasOtherPagerPending st conn
  let cachedNames := conn.schemaCache?.getD (catTableNames (connVisibleCatalog st conn))
  let noopCreate :=
    match writeStmt with
    | .createTable true tblName _ _ =>
      cachedNames.any (fun k => asciiLower k == asciiLower tblName)
    | _ => false
  if isReadOnlyStmt writeStmt then
    (.ok #[], st)
  else if noopCreate then
    if hasSharedSchemaWriteConflict st conn ||
        (!connHasSharedBtTrans st conn && hasSharedGroupPending st conn) then
      (.error (mapRawError (.busy 262 "database table is locked: sqlite_master")), st)
    else
      match conn.tx with
      | .deferred none =>
        match ensureWalShmAttachedConn st conn none with
        | .error e => (.error e, st)
        | .ok (stShm, connShm) =>
          if effReadSnap?.isNone && otherPending then
            (.error (mapRawError (.busy 5 "database is locked")), stShm)
          else
            let (snapEp, snapCat) := effReadSnap?.getD (curEpoch, curCat)
            let sc := some (syncTableNames connShm.schemaCache? snapCat)
            (.ok #[], syncSharedGroupSchema
              (replaceConn stShm { connShm with tx := .deferred (some (snapEp, snapCat)), schemaCache? := sc })
              connShm.sharedGroup? sc)
      | .autocommit =>
        match ensureWalShmAttachedConn st conn none with
        | .error e => (.error e, st)
        | .ok (stShm, connShm) =>
          if effReadSnap?.isNone && otherPending then
            (.error (mapRawError (.busy 5 "database is locked")), stShm)
          else
            let (_, snapCat) := effReadSnap?.getD (curEpoch, curCat)
            let sc := some (syncTableNames connShm.schemaCache? snapCat)
            (.ok #[], syncSharedGroupSchema (replaceConn stShm { connShm with schemaCache? := sc }) connShm.sharedGroup? sc)
      | _ => (.ok #[], st)
  else if conn.effectiveReadOnly then
    (.error (mapRawError (.ioFailure 8 "attempt to write a readonly database")), st)
  else
    match ensureWalShmAttachedConn st conn none with
    | .error e => (.error e, st)
    | .ok (st, conn) =>
      let isDdl := isDdlStmt writeStmt
      let otherWriter := hasOtherPagerWriter st conn
      let addWTabs := fun (cur : List String) =>
        if conn.sharedGroup?.isSome then
          addUniqueStrings cur (writeTouchedTables writeStmt)
        else []
      let addFkRTabs := fun (cur : List String) (cat : DbCatalog) =>
        if conn.sharedGroup?.isSome then
          addUniqueStrings cur (fkReadTouchedTables cat conn.foreignKeys writeStmt)
        else []
      match conn.tx with
      | .write baseEp staged =>
        if hasSharedWriteLockConflict st conn staged writeStmt then
          let stPend :=
            if conn.sharedGroup?.isSome && !conn.sharedPending then
              replaceConn st { conn with sharedPending := true }
            else st
          (.error (mapRawError (.busy 262 "database table is locked")), stPend)
        else
          let (res, (didPartial, partialCat)) := applyFn staged conn.foreignKeys writeStmt params
          let wt := addWTabs conn.sharedWriteTables
          let rt := addFkRTabs conn.sharedReadTables staged
          match res with
          | .ok (didMutate, staged') =>
            let sc := some (syncTableNames conn.schemaCache? staged')
            (.ok #[], replaceConn st { conn with tx := .write baseEp staged', writeDirty := conn.writeDirty || didMutate, schemaDirty := conn.schemaDirty || (isDdl && didMutate), schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
          | .error e =>
            let usesJ := stmtUsesStmtJournal staged conn.foreignKeys writeStmt
            if e.sqliteCode == some 13 && !usesJ then
              (.error e, rollbackConnState st { conn with sharedWriteTables := wt, sharedReadTables := rt } curEpoch curCat)
            else if e.sqliteCode == some 3091 && !usesJ then
              let sc := some (syncTableNames conn.schemaCache? partialCat)
              (.error e, replaceConn st { conn with tx := .write baseEp partialCat, writeDirty := conn.writeDirty || didPartial, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
            else
              let sc := some (syncTableNames conn.schemaCache? staged)
              (.error e, replaceConn st { conn with schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
      | .deferred (some (snapEp, snap)) =>
        if hasSharedGroupWriter st conn || hasSharedSchemaWriteConflict st conn then
          (.error (mapRawError (.busy 262 "database table is locked")), st)
        else if otherWriter then
          (.error (mapRawError (.busy 5 "database is locked")), st)
        else if isWal && snapEp != curEpoch then
          (.error (mapRawError (.busy 517 "database schema/snapshot changed")), st)
        else if hasSharedWriteLockConflict st conn snap writeStmt then
          let sc := some (syncTableNames conn.schemaCache? snap)
          (.error (mapRawError (.busy 262 "database table is locked")),
            syncSharedGroupSchema
              (replaceConn st { conn with tx := .write curEpoch snap, writeDirty := false, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedPending := conn.sharedGroup?.isSome })
              conn.sharedGroup? sc)
        else
          let (res, (didPartial, partialCat)) := applyFn snap conn.foreignKeys writeStmt params
          let wt := addWTabs []
          let rt := addFkRTabs conn.sharedReadTables snap
          match res with
          | .ok (didMutate, staged') =>
            let sc := some (syncTableNames conn.schemaCache? staged')
            (.ok #[], replaceConn st { conn with tx := .write curEpoch staged', writeDirty := didMutate, schemaDirty := isDdl && didMutate, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
          | .error e =>
            let usesJ := stmtUsesStmtJournal snap conn.foreignKeys writeStmt
            if e.sqliteCode == some 13 && !usesJ then
              (.error e, rollbackConnState st { conn with sharedWriteTables := wt, sharedReadTables := rt } curEpoch curCat)
            else if e.sqliteCode == some 3091 && !usesJ then
              let sc := some (syncTableNames conn.schemaCache? partialCat)
              (.error e, replaceConn st { conn with tx := .write curEpoch partialCat, writeDirty := didPartial, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
            else
              let sc := some (syncTableNames conn.schemaCache? snap)
              (.error e, replaceConn st { conn with tx := .write curEpoch snap, writeDirty := false, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
      | .deferred none =>
        let (snapEp, snapCat) := effReadSnap?.getD (curEpoch, curCat)
        if hasSharedGroupWriter st conn || hasSharedSchemaWriteConflict st conn then
          (.error (mapRawError (.busy 262 "database table is locked")), st)
        else if otherWriter || (effReadSnap?.isNone && otherPending) then
          (.error (mapRawError (.busy 5 "database is locked")), st)
        else if isWal && snapEp != curEpoch then
          (.error (mapRawError (.busy 517 "database schema/snapshot changed")), st)
        else if hasSharedWriteLockConflict st conn snapCat writeStmt then
          let sc := some (syncTableNames conn.schemaCache? snapCat)
          (.error (mapRawError (.busy 262 "database table is locked")),
            syncSharedGroupSchema
              (replaceConn st { conn with tx := .write curEpoch snapCat, writeDirty := false, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedPending := conn.sharedGroup?.isSome })
              conn.sharedGroup? sc)
        else
          let (res, (didPartial, partialCat)) := applyFn snapCat conn.foreignKeys writeStmt params
          let wt := addWTabs []
          let rt := addFkRTabs conn.sharedReadTables snapCat
          match res with
          | .ok (didMutate, staged') =>
            let sc := some (syncTableNames conn.schemaCache? staged')
            (.ok #[], replaceConn st { conn with tx := .write curEpoch staged', writeDirty := didMutate, schemaDirty := isDdl && didMutate, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
          | .error e =>
            let usesJ := stmtUsesStmtJournal snapCat conn.foreignKeys writeStmt
            if e.sqliteCode == some 13 && !usesJ then
              (.error e, rollbackConnState st { conn with sharedWriteTables := wt, sharedReadTables := rt } curEpoch curCat)
            else if e.sqliteCode == some 3091 && !usesJ then
              let sc := some (syncTableNames conn.schemaCache? partialCat)
              (.error e, replaceConn st { conn with tx := .write curEpoch partialCat, writeDirty := didPartial, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
            else
              let sc := some (syncTableNames conn.schemaCache? snapCat)
              (.error e, replaceConn st { conn with tx := .write curEpoch snapCat, writeDirty := false, schemaDirty := false, pendingLock := false, schemaCache? := sc, sharedWriteTables := wt, sharedReadTables := rt })
      | .autocommit =>
        if hasSharedGroupWriter st conn || hasSharedSchemaWriteConflict st conn then
          (.error (mapRawError (.busy 262 "database table is locked")), st)
        else if otherWriter || (effReadSnap?.isNone && otherPending) then
          (.error (mapRawError (.busy 5 "database is locked")), st)
        else if isWal && (match effReadSnap? with | some (se, _) => se != curEpoch | none => false) then
          (.error (mapRawError (.busy 517 "database schema/snapshot changed")), st)
        else if hasSharedWriteLockConflict st conn curCat writeStmt then
          let sc := some (syncTableNames conn.schemaCache? curCat)
          (.error (mapRawError (.busy 262 "database table is locked")),
            syncSharedGroupSchema (replaceConn st { conn with schemaCache? := sc }) conn.sharedGroup? sc)
        else
          let (res, _) := applyFn curCat conn.foreignKeys writeStmt params
          let sc := some (syncTableNames conn.schemaCache? curCat)
          let wTabs := writeTouchedTables writeStmt
          let rTabs := fkReadTouchedTables curCat conn.foreignKeys writeStmt
          let retained := retainedSharedReadTablesAfterEnd st conn rTabs wTabs
          match res with
          | .error e =>
            (.error e, syncSharedGroupSchema (replaceConn st { conn with schemaCache? := sc, sharedReadTables := retained }) conn.sharedGroup? sc)
          | .ok (didMutate, cat') =>
            if !didMutate then
              (.ok #[], syncSharedGroupSchema (replaceConn st { conn with schemaCache? := sc, sharedReadTables := retained }) conn.sharedGroup? sc)
            else
              let blockedByReader :=
                if isWal then false
                else hasOtherPagerReader st conn
              if blockedByReader then
                (.error (mapRawError (.busy 5 "database is locked")),
                  syncSharedGroupSchema (replaceConn st { conn with schemaCache? := sc, sharedReadTables := retained }) conn.sharedGroup? sc)
              else
                let cWithLocks :=
                  if conn.sharedGroup?.isSome then
                    { conn with sharedReadTables := addUniqueStrings conn.sharedReadTables rTabs,
                                sharedWriteTables := addUniqueStrings conn.sharedWriteTables wTabs }
                  else conn
                (.ok #[], commitStagedCatalog st cWithLocks cat' .autocommit)

private def executeModelStmt (st : SqliteWorldState) (conn : ConnState) (stmt : SqlStmt)
    (params : Array SqliteValue) : Except SqliteError (Array SqliteRow) × SqliteWorldState :=
  let (curEpoch, curCat, isWal) := connCommittedCatalog st conn
  let effReadSnap? := conn.readSnap? <|> sharedGroupPinnedSnap? st conn
  let otherPending :=
    if isWal then hasDotfileExclusiveConflict st conn
    else hasOtherPagerPending st conn
  match stmt with
  | .begin .deferred =>
    if conn.tx != .autocommit then
      (.error (mapRawError (.sqliteCodeError 1 "cannot start a transaction within a transaction")), st)
    else
      let nextTx : ConnTxState :=
        match conn.readSnap? with
        | some s => .deferred (some s)
        | none => .deferred none
      (.ok #[], replaceConn st { conn with tx := nextTx, readSnap? := none })
  | .begin .immediate =>
    match conn.tx with
    | .write _ _ =>
      (.error (mapRawError (.sqliteCodeError 1 "cannot start a transaction within a transaction")), st)
    | .deferred snap? =>
      if isCorruptFileConn st conn then
        (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
      else if isUnsupportedWalConn st conn then
        (.error (mapRawError (.cantOpen none 14 "unable to open database file")), st)
      else
        match ensureWalShmAttachedConn st conn none with
        | .error e => (.error e, st)
        | .ok (stShm, connShm) =>
          if connShm.effectiveReadOnly then
            if hasSharedSchemaWriteConflict stShm connShm ||
                (snap?.isNone && !connHasSharedBtTrans stShm connShm && hasSharedGroupPending stShm connShm) then
              (.error (mapRawError (.busy 262 "database table is locked")), stShm)
            else if snap?.isNone && effReadSnap?.isNone && otherPending then
              (.error (mapRawError (.busy 5 "database is locked")), stShm)
            else
              let newTx := match snap? <|> effReadSnap? with
                | some s => .deferred (some s)
                | none => .deferred (some (curEpoch, curCat))
              (.error (mapRawError (.sqliteCodeError 1 "cannot start a transaction within a transaction")),
                replaceConn stShm { connShm with tx := newTx })
          else if hasSharedGroupWriter stShm connShm || hasSharedSchemaWriteConflict stShm connShm then
            (.error (mapRawError (.busy 262 "database table is locked")), stShm)
          else if hasOtherPagerWriter stShm connShm || (snap?.isNone && effReadSnap?.isNone && otherPending) then
            (.error (mapRawError (.busy 5 "database is locked")), stShm)
          else
            match snap? <|> effReadSnap? with
            | some (snapEp, snap) =>
              if isWal && snapEp != curEpoch then
                (.error (mapRawError (.busy 517 "database schema/snapshot changed")), stShm)
              else
                let st1 := replaceConn stShm { connShm with tx := .write curEpoch snap, writeDirty := false, schemaDirty := false, pendingLock := false }
                (.error (mapRawError (.sqliteCodeError 1 "cannot start a transaction within a transaction")), st1)
            | none =>
              let st1 := replaceConn stShm { connShm with tx := .write curEpoch curCat, writeDirty := false, schemaDirty := false, pendingLock := false }
              (.error (mapRawError (.sqliteCodeError 1 "cannot start a transaction within a transaction")), st1)
    | .autocommit =>
      if isCorruptFileConn st conn then
        (.error (mapRawError (.ioFailure 26 "file is not a database")), st)
      else if isUnsupportedWalConn st conn then
        (.error (mapRawError (.cantOpen none 14 "unable to open database file")), st)
      else
        match ensureWalShmAttachedConn st conn none with
        | .error e => (.error e, st)
        | .ok (stShm, connShm) =>
          if connShm.effectiveReadOnly then
            if hasSharedSchemaWriteConflict stShm connShm ||
                (!connHasSharedBtTrans stShm connShm && hasSharedGroupPending stShm connShm) then
              (.error (mapRawError (.busy 262 "database table is locked")), stShm)
            else if effReadSnap?.isNone && otherPending then
              (.error (mapRawError (.busy 5 "database is locked")), stShm)
            else
              let (snapEp, snap) := effReadSnap?.getD (curEpoch, curCat)
              (.ok #[], replaceConn stShm { connShm with tx := .deferred (some (snapEp, snap)) })
          else if hasSharedGroupWriter stShm connShm || hasSharedSchemaWriteConflict stShm connShm then
            (.error (mapRawError (.busy 262 "database table is locked")), stShm)
          else if hasOtherPagerWriter stShm connShm || (effReadSnap?.isNone && otherPending) then
            (.error (mapRawError (.busy 5 "database is locked")), stShm)
          else if isWal && (match effReadSnap? with | some (se, _) => se != curEpoch | none => false) then
            (.error (mapRawError (.busy 517 "database schema/snapshot changed")), stShm)
          else
            let (snapEp, snap) := effReadSnap?.getD (curEpoch, curCat)
            (.ok #[], replaceConn stShm { connShm with tx := .write snapEp snap, writeDirty := false, schemaDirty := false, pendingLock := false })
  | .commit =>
    match conn.tx with
    | .autocommit =>
      (.error (mapRawError (.sqliteCodeError 1 "cannot commit - no transaction is active")), st)
    | .deferred snap? =>
      let nextReadSnap? :=
        if hasActiveScanOnConn st conn.id then
          conn.readSnap? <|> snap? <|> some (curEpoch, curCat)
        else
          none
      let nextSR := retainedSharedReadTablesAfterEnd st conn
      let st1 := replaceConn st { conn with tx := .autocommit, writeDirty := false, schemaDirty := false, pendingLock := false, readSnap? := nextReadSnap?, sharedWriteTables := [], sharedReadTables := nextSR, sharedPending := false }
      (.ok #[], clearSharedPendingIfLastReader st1 conn.sharedGroup?)
    | .write baseEp staged =>
      if !conn.writeDirty then
        let nextReadSnap? :=
          if hasActiveScanOnConn st conn.id then
            conn.readSnap? <|> some (baseEp, staged)
          else
            none
        let nextSR := retainedSharedReadTablesAfterEnd st conn
        let st1 := replaceConn st { conn with tx := .autocommit, writeDirty := false, schemaDirty := false, pendingLock := false, readSnap? := nextReadSnap?, sharedWriteTables := [], sharedReadTables := nextSR, sharedPending := false }
        (.ok #[], clearSharedPendingIfLastReader st1 conn.sharedGroup?)
      else
        let blockedByReader :=
          if isWal then false
          else hasOtherPagerReader st conn
        if blockedByReader then
          (.error (mapRawError (.busy 5 "database is locked")),
            replaceConn st { conn with pendingLock := true })
        else
          (.ok #[], commitStagedCatalog st conn staged .autocommit)
  | .rollback =>
    if conn.tx == .autocommit then
      (.error (mapRawError (.sqliteCodeError 1 "cannot rollback - no transaction is active")), st)
    else
      (.ok #[], rollbackConnState st conn curEpoch curCat)
  | .select proj tbl? where? orderBy limit? =>
    match if tbl?.isSome && (conn.tx == .deferred none || conn.tx == .autocommit) then
            ensureWalShmAttachedConn st conn none
          else .ok (st, conn) with
    | .error e => (.error e, st)
    | .ok (st, conn) =>
      let sharedReadConflict :=
        match tbl? with
        | some t => hasSharedTableReadConflict st conn t
        | none => false
      if sharedReadConflict then
        let tName := tbl?.getD ""
        (.error (mapRawError (.busy 262 s!"database table is locked: {tName}")), st)
      else if tbl?.isSome && !connHasSharedBtTrans st conn && hasSharedGroupPending st conn then
        (.error (mapRawError (.busy 262 "database table is locked")), st)
      else
        let addRTab := fun (cur : List String) =>
          if conn.sharedGroup?.isSome then
            match tbl? with
            | some t => addUniqueStrings cur [asciiLower t]
            | none => cur
          else []
        let syncReadConn := fun (stIn : SqliteWorldState) (cNew : ConnState) =>
          let stReplaced := replaceConn stIn cNew
          if tbl?.isSome then syncSharedGroupSchema stReplaced cNew.sharedGroup? cNew.schemaCache?
          else stReplaced
        let connWithReadCache := fun (c : ConnState) (readCat : DbCatalog) =>
          if tbl?.isSome then { c with schemaCache? := some (syncTableNames c.schemaCache? readCat) } else c
        match conn.tx with
        | .write _ staged =>
          let st1 := syncReadConn st (connWithReadCache conn staged)
          match evalSelectQuery staged proj tbl? where? orderBy limit? params with
          | .error e => (.error e, st1)
          | .ok rows => (.ok rows, st1)
        | .deferred (some (_, snap)) =>
          let cRead := { (connWithReadCache conn snap) with sharedReadTables := addRTab conn.sharedReadTables }
          let st1 := syncReadConn st cRead
          match evalSelectQuery snap proj tbl? where? orderBy limit? params with
          | .error e => (.error e, st1)
          | .ok rows => (.ok rows, st1)
        | .deferred none =>
          if tbl?.isSome && effReadSnap?.isNone && otherPending then
            (.error (mapRawError (.busy 5 "database is locked")), st)
          else
            let (snapEp, snapCat) := effReadSnap?.getD (curEpoch, curCat)
            let st1 :=
              if tbl?.isSome then
                syncReadConn st { conn with tx := .deferred (some (snapEp, snapCat)),
                                            schemaCache? := some (syncTableNames conn.schemaCache? snapCat),
                                            sharedReadTables := addRTab conn.sharedReadTables }
              else st
            match evalSelectQuery snapCat proj tbl? where? orderBy limit? params with
            | .error e => (.error e, st1)
            | .ok rows => (.ok rows, st1)
        | .autocommit =>
          let readCat := match effReadSnap? with | some (_, s) => s | none => curCat
          if tbl?.isSome && effReadSnap?.isNone && otherPending then
            (.error (mapRawError (.busy 5 "database is locked")), st)
          else
            let cRead := { (connWithReadCache conn readCat) with sharedReadTables := addRTab conn.sharedReadTables }
            let st1 := syncReadConn st cRead
            match evalSelectQuery readCat proj tbl? where? orderBy limit? params with
            | .error e => (.error e, st1)
            | .ok rows => (.ok rows, st1)
  | writeStmt => executeModelWriteStmtWith applyWriteStmtEx st conn writeStmt params

private def projectSelectRow (tbl : TableData) (proj : SelectProj) (params : Array SqliteValue)
    (vals : Array SqliteValue) : SqliteRow :=
  match proj with
  | .star => vals
  | .items es => (es.map fun e => (evalVal (some tbl) vals params e).1).toArray

private def markStmtStepErr (st : SqliteWorldState) (stmt : StmtHandle) (dbId : UInt64)
    (e : SqliteError) : Except SqliteError StepResult × SqliteWorldState :=
  let updated := st.stmts.map fun s =>
    if s.handle == stmt then
      { s with err? := some e, resultRows? := none, relBranches := [],
               rollbackMayAbort := false, stepIdx := 0, holdsReadLock := false }
    else s
  (.error e, clearReadSnapIfIdle { st with stmts := updated } dbId)

private def markStmtDone (st : SqliteWorldState) (stmt : StmtHandle) (dbId : UInt64) :
    Except SqliteError StepResult × SqliteWorldState :=
  let updated := st.stmts.map fun s =>
    if s.handle == stmt then
      { s with resultRows? := none, relBranches := [], rollbackMayAbort := false,
               stepIdx := 0, holdsReadLock := false, err? := none }
    else s
  (.ok .done, clearReadSnapIfIdle { st with stmts := updated } dbId)

private def selectStepPrelude (stmt : StmtHandle) (st : SqliteWorldState) (conn : ConnState)
    (tblName : String) (limit? : Option ScalarExpr) (params : Array SqliteValue) :
    Except (Except SqliteError StepResult × SqliteWorldState)
      (TableData × Option Nat × SqliteWorldState) :=
  let shmRes :=
    if conn.tx == .deferred none || conn.tx == .autocommit then
      ensureWalShmAttachedConn st conn none
    else .ok (st, conn)
  match shmRes with
  | .error e => .error (markStmtStepErr st stmt conn.id e)
  | .ok (st0, conn0) =>
    if hasSharedTableReadConflict st0 conn0 tblName then
      .error (markStmtStepErr st0 stmt conn0.id
        (mapRawError (.busy 262 s!"database table is locked: {tblName}")))
    else if !connHasSharedBtTrans st0 conn0 && hasSharedGroupPending st0 conn0 then
      .error (markStmtStepErr st0 stmt conn0.id
        (mapRawError (.busy 262 "database table is locked")))
    else
      let (curEpoch, curCat, isWal) := connCommittedCatalog st0 conn0
      let effReadSnap? := conn0.readSnap? <|> sharedGroupPinnedSnap? st0 conn0
      let otherPending :=
        if isWal then hasDotfileExclusiveConflict st0 conn0
        else hasOtherPagerPending st0 conn0
      let addRTab := fun (cur : List String) =>
        if conn0.sharedGroup?.isSome then addUniqueStrings cur [asciiLower tblName] else []
      let syncLiveConn := fun (cNew : ConnState) =>
        syncSharedGroupSchema (replaceConn st0 cNew) cNew.sharedGroup? cNew.schemaCache?
      let (visCat, st1, lockErr?) :=
        match conn0.tx with
        | .write _ staged =>
          (staged, syncLiveConn { conn0 with schemaCache? := some (syncTableNames conn0.schemaCache? staged) }, none)
        | .deferred (some (_, snap)) =>
          (snap, syncLiveConn { conn0 with
            schemaCache? := some (syncTableNames conn0.schemaCache? snap)
            sharedReadTables := addRTab conn0.sharedReadTables }, none)
        | .deferred none =>
          if effReadSnap?.isNone && otherPending then
            (curCat, st0, some (mapRawError (.busy 5 "database is locked")))
          else
            let (snapEp, snapCat) := effReadSnap?.getD (curEpoch, curCat)
            (snapCat, syncLiveConn { conn0 with
              tx := .deferred (some (snapEp, snapCat))
              schemaCache? := some (syncTableNames conn0.schemaCache? snapCat)
              sharedReadTables := addRTab conn0.sharedReadTables }, none)
        | .autocommit =>
          let (snapEp, snapCat) := effReadSnap?.getD (curEpoch, curCat)
          if effReadSnap?.isNone && otherPending then
            (curCat, st0, some (mapRawError (.busy 5 "database is locked")))
          else
            (snapCat, syncLiveConn { conn0 with
              schemaCache? := some (syncTableNames conn0.schemaCache? snapCat)
              readSnap? := conn0.readSnap? <|> some (snapEp, snapCat)
              sharedReadTables := addRTab conn0.sharedReadTables }, none)
      match lockErr? with
      | some e => .error (markStmtStepErr st0 stmt conn0.id e)
      | none =>
        let limRes : Except SqliteError (Option Nat) :=
          match limit? with
          | none => .ok none
          | some le =>
            match mustBeIntValue (evalScalar params le) with
            | none => .error (mapRawError (.sqliteCodeError 20 "datatype mismatch"))
            | some iv => if iv < 0 then .ok none else .ok (some iv.toNatClampNeg)
        match limRes with
        | .error e => .error (markStmtStepErr st1 stmt conn0.id e)
        | .ok remLimit? =>
          match lookupTable? visCat tblName with
          | none =>
            .error (markStmtStepErr st1 stmt conn0.id
              (mapRawError (.sqliteCodeError 1 s!"no such table: {tblName}")))
          | some tbl => .ok (tbl, remLimit?, st1)

private def stmtReachedLimit (entry : ModelStmtState) : Bool :=
  match entry.stmt with
  | .select _ (some _) _ _ (some le) =>
    match mustBeIntValue (evalScalar (entry.boundParams?.getD #[]) le) with
    | some iv => 0 ≤ iv && entry.stepIdx ≥ iv.toNatClampNeg
    | none => false
  | _ => false

private def modelStep (stmt : StmtHandle) (st : SqliteWorldState) :
    Except SqliteError StepResult × SqliteWorldState :=
  match st.stmts.find? (fun s => s.handle == stmt) with
  | none => (.error (mapRawError (.misuse 21 "invalid or finalized statement handle")), st)
  | some entry =>
    if entry.rollbackMayAbort && !stmtReachedLimit entry then
      markStmtStepErr st stmt entry.handle.dbId
        (mapRawError (.ioFailure 516 "abort due to ROLLBACK"))
    else
      match entry.resultRows? with
      | some rows =>
        if h : entry.stepIdx < rows.size then
          let row := rows[entry.stepIdx]
          let updated := st.stmts.map fun s =>
            if s.handle == stmt then { s with stepIdx := s.stepIdx + 1 } else s
          (.ok (.row row), { st with stmts := updated })
        else
          markStmtDone st stmt entry.handle.dbId
      | none =>
        match lookupConn? st entry.handle.dbId with
        | none => (.error (mapRawError (.misuse 21 "invalid or closed database handle")), st)
        | some conn =>
          let params := entry.boundParams?.getD #[]
          match entry.stmt with
          | .select proj (some tblName) where? orderBy limit? =>
            match selectStepPrelude stmt st conn tblName limit? params with
            | .error out => out
            | .ok (tbl, remLimit?, st1) =>
              if remLimit? == some 0 then
                markStmtDone st1 stmt conn.id
              else
                let matched := (tbl.rows.map (·.2)).filter fun vals =>
                  evalWhere tbl vals params where?
                let sorted :=
                  if orderBy.isEmpty then matched.toArray
                  else (sortList (fun a b => compareByOrderItems tbl orderBy a b == .lt) matched).toArray
                let projected := sorted.map (projectSelectRow tbl proj params)
                let rows :=
                  match remLimit? with
                  | none => projected
                  | some k => projected.extract 0 (min projected.size k)
                if h : 0 < rows.size then
                  let row := rows[0]
                  let updated := st1.stmts.map fun s =>
                    if s.handle == stmt then
                      { s with resultRows? := some rows, stepIdx := 1,
                               holdsReadLock := true, rollbackMayAbort := false, err? := none }
                    else s
                  (.ok (.row row), { st1 with stmts := updated })
                else
                  markStmtDone st1 stmt conn.id
          | _ =>
            let (res, st1) := executeModelStmt st conn entry.stmt params
            match res with
            | .error e => markStmtStepErr st1 stmt conn.id e
            | .ok rows =>
              if h : 0 < rows.size then
                let row := rows[0]
                let holdLock := match entry.stmt with | .select _ (some _) _ _ _ => true | _ => false
                let st2 :=
                  if holdLock then
                    match lookupConn? st1 conn.id with
                    | some c =>
                      if c.tx == .autocommit && c.readSnap?.isNone then
                        let (ce, cc, _) := connCommittedCatalog st1 c
                        replaceConn st1 { c with readSnap? := some (ce, cc) }
                      else st1
                    | none => st1
                  else st1
                let updated := st2.stmts.map fun s =>
                  if s.handle == stmt then
                    { s with resultRows? := some rows, stepIdx := 1,
                             holdsReadLock := holdLock, rollbackMayAbort := false, err? := none }
                  else s
                (.ok (.row row), { st2 with stmts := updated })
              else
                markStmtDone st1 stmt conn.id
private def modelFinalize (stmt : StmtHandle) (st : SqliteWorldState) :
    Except SqliteError Unit × SqliteWorldState :=
  match st.stmts.find? (fun s => s.handle == stmt) with
  | none => (.error (mapRawError (.misuse 21 "invalid or already finalized statement handle")), st)
  | some entry =>
    let st' := clearReadSnapIfIdle { st with stmts := st.stmts.filter (fun s => s.handle != stmt) } entry.handle.dbId
    match entry.err? with
    | some e => (.error e, st')
    | none => (.ok (), st')

/-- Pure `StateM SqliteWorldState` implementation of `RawSqliteOpsM` modeling SQLite `3.54.1`. -/
def modelRawOps : RawSqliteOpsM (StateM SqliteWorldState) :=
  { mapRawError := mapRawError
    openDb := modelOpenDb
    closeDb := modelCloseDb
    prepare := modelPrepare
    bind := modelBind
    step := modelStep
    finalize := modelFinalize
    activeDbCount := fun s => (s.conns.length, s)
    activeStmtCount := fun s => (s.stmts.length, s) }

private def rawStepResultEq (a b : Except SqliteError StepResult) : Bool :=
  match a, b with
  | .ok .done, .ok .done => true
  | .ok (.row r1), .ok (.row r2) => sqliteRowBitEq r1 r2
  | .error e1, .error e2 =>
    e1.kind == e2.kind && !e1.message.isEmpty &&
    e1.sqliteCode == e2.sqliteCode && e1.path == e2.path
  | _, _ => false

private def matchedTableRows (tbl : TableData) (proj : SelectProj) (where? : Option WhereExpr)
    (params : Array SqliteValue) : List (Int64 × Array SqliteValue × SqliteRow) :=
  tbl.rows.filterMap fun (rid, vals) =>
    if evalWhere tbl vals params where? then
      some (rid, vals, projectSelectRow tbl proj params vals)
    else
      none

private def tblRowsBitEq : List (Int64 × Array SqliteValue) → List (Int64 × Array SqliteValue) → Bool
  | [], [] => true
  | (r1, v1) :: xs, (r2, v2) :: ys => r1 == r2 && sqliteRowBitEq v1 v2 && tblRowsBitEq xs ys
  | _, _ => false

private def poolRowsBitEq :
    List (Int64 × Array SqliteValue × SqliteRow) → List (Int64 × Array SqliteValue × SqliteRow) → Bool
  | [], [] => true
  | (r1, v1, p1) :: xs, (r2, v2, p2) :: ys =>
    r1 == r2 && sqliteRowBitEq v1 v2 && sqliteRowBitEq p1 p2 && poolRowsBitEq xs ys
  | _, _ => false

private def liveEntriesBitEq : List RelLiveEntry → List RelLiveEntry → Bool
  | [], [] => true
  | a :: xs, b :: ys =>
    a.uid == b.uid && a.rid == b.rid && sqliteRowBitEq a.vals b.vals &&
      sqliteRowBitEq a.projRow b.projRow && liveEntriesBitEq xs ys
  | _, _ => false

private def optRowBitEq : Option (Array SqliteValue) → Option (Array SqliteValue) → Bool
  | none, none => true
  | some a, some b => sqliteRowBitEq a b
  | _, _ => false

private def relBranchBitEq (a b : RelBranch) : Bool :=
  a.isSorter? == b.isSorter? &&
  poolRowsBitEq a.sorterPool b.sorterPool &&
  a.nextUid == b.nextUid &&
  liveEntriesBitEq a.liveEntries b.liveEntries &&
  a.mustUids == b.mustUids &&
  a.consumedGroups == b.consumedGroups &&
  optRowBitEq a.lastOrig? b.lastOrig? &&
  a.remLimit? == b.remLimit? &&
  a.tblSchema == b.tblSchema &&
  a.syncedGen == b.syncedGen &&
  tblRowsBitEq a.lastTblRows b.lastTblRows

private def removePoolEntry (rid : Int64) (vals : Array SqliteValue) :
    List (Int64 × Array SqliteValue × SqliteRow) →
      List (Int64 × Array SqliteValue × SqliteRow)
  | [] => []
  | (r, v, p) :: rest =>
    if r == rid && sqliteRowBitEq v vals then rest
    else (r, v, p) :: removePoolEntry rid vals rest

private def addConsumeGroup (candUids : List Nat) : List RelConsumeGroup → List RelConsumeGroup
  | [] => [{ candUids := candUids, demand := 1 }]
  | g :: rest =>
    if g.candUids == candUids then
      { g with demand := g.demand + 1 } :: rest
    else
      { candUids := candUids, demand := 1 } :: g :: rest

private def augFromUidFuel (groupArr : Array RelConsumeGroup)
    (uidToGroups : Std.HashMap Nat (List Nat)) :
    Nat → Nat → Std.HashSet Nat → Std.HashMap Nat Nat → Array Nat →
      Option (Std.HashMap Nat Nat × Array Nat) × Std.HashSet Nat
  | 0, _, visG, _, _ => (none, visG)
  | fuel + 1, u, visG0, matchR, usedL =>
    let rec tryGroups : List Nat → Std.HashSet Nat →
        Option (Std.HashMap Nat Nat × Array Nat) × Std.HashSet Nat
      | [], visG => (none, visG)
      | g :: gs, visG =>
        if visG.contains g then
          tryGroups gs visG
        else
          let visG1 := visG.insert g
          let grp := groupArr.getD g { candUids := [], demand := 0 }
          let used := usedL.getD g 0
          if used < grp.demand then
            (some (matchR.insert u g, usedL.set! g (used + 1)), visG1)
          else
            let rec tryMatched : List Nat → Std.HashSet Nat →
                Option (Std.HashMap Nat Nat × Array Nat) × Std.HashSet Nat
              | [], vG => (none, vG)
              | uNext :: us, vG =>
                if matchR.get? uNext == some g then
                  let (res?, vG') := augFromUidFuel groupArr uidToGroups fuel uNext vG matchR usedL
                  match res? with
                  | some (matchR', usedL') => (some (matchR'.insert u g, usedL'), vG')
                  | none => tryMatched us vG'
                else
                  tryMatched us vG
            let (subRes?, visG2) := tryMatched grp.candUids visG1
            match subRes? with
            | some out => (some out, visG2)
            | none => tryGroups gs visG2
    tryGroups (uidToGroups.getD u []) visG0

private def augFromGroupFuel (groupArr : Array RelConsumeGroup) :
    Nat → Nat → Std.HashSet Nat → Std.HashMap Nat Nat →
      Option (Std.HashMap Nat Nat) × Std.HashSet Nat
  | 0, _, visG, _ => (none, visG)
  | fuel + 1, g, visG0, matchR =>
    let visG1 := visG0.insert g
    let grp := groupArr.getD g { candUids := [], demand := 0 }
    match grp.candUids.find? (fun v => !matchR.contains v) with
    | some vFree => (some (matchR.insert vFree g), visG1)
    | none =>
      let rec trySwap : List Nat → Std.HashSet Nat →
          Option (Std.HashMap Nat Nat) × Std.HashSet Nat
        | [], vG => (none, vG)
        | v :: vs, vG =>
          match matchR.get? v with
          | some gNext =>
            if vG.contains gNext then
              trySwap vs vG
            else
              let (res?, vG') := augFromGroupFuel groupArr fuel gNext vG matchR
              match res? with
              | some matchR' => (some (matchR'.insert v g), vG')
              | none => trySwap vs vG'
          | none => (some (matchR.insert v g), vG)
      trySwap grp.candUids visG1

private def canSatisfyConsumed (groups : List RelConsumeGroup) (reqUids : List Nat) : Bool :=
  match groups with
  | [] => reqUids.isEmpty
  | [g] =>
    reqUids.length ≤ g.demand &&
      g.demand ≤ g.candUids.length &&
      reqUids.all (fun u => g.candUids.contains u)
  | _ => Id.run do
    let groupArr := groups.toArray
    let totalDemand := groupArr.foldl (fun s g => s + g.demand) 0
    if reqUids.length > totalDemand then
      return false
    let mut uidToGroups : Std.HashMap Nat (List Nat) := {}
    for h : gIdx in [0 : groupArr.size] do
      for u in groupArr[gIdx].candUids do
        uidToGroups := uidToGroups.insert u (gIdx :: uidToGroups.getD u [])
    let maxDepth := groupArr.size + 1
    let mut matchR : Std.HashMap Nat Nat := {}
    let mut usedL : Array Nat := Array.replicate groupArr.size 0
    for uReq in reqUids do
      if !matchR.contains uReq then
        let (res?, _) := augFromUidFuel groupArr uidToGroups maxDepth uReq {} matchR usedL
        match res? with
        | none => return false
        | some (m', u') =>
          matchR := m'
          usedL := u'
    for h : gIdx in [0 : groupArr.size] do
      let dem := groupArr[gIdx].demand
      for _ in [0 : dem - usedL.getD gIdx 0] do
        let (res?, _) := augFromGroupFuel groupArr maxDepth gIdx {} matchR
        match res? with
        | none => return false
        | some m' =>
          matchR := m'
          usedL := usedL.set! gIdx (usedL.getD gIdx 0 + 1)
    return true

private def syncRelBranchLive (st : SqliteWorldState) (tblNow? : Option TableData)
    (proj : SelectProj) (where? : Option WhereExpr) (params : Array SqliteValue)
    (b : RelBranch) : RelBranch :=
  match tblNow? with
  | none =>
    { b with liveEntries := [], mustUids := [], syncedGen := st.mutGen, lastTblRows := [] }
  | some tblNow =>
    if tblRowsBitEq tblNow.rows b.lastTblRows then
      { b with syncedGen := st.mutGen }
    else
      let keptLive := b.liveEntries.filter fun e =>
        tblNow.rows.any (fun (r, v) => r == e.rid && sqliteRowBitEq v e.vals)
      let keptUids := keptLive.map (·.uid)
      let keptMust := b.mustUids.filter fun u => keptUids.contains u
      let (nextUid', addedRev) :=
        tblNow.rows.foldl (fun (curUid, acc) (rid, vals) =>
          if !(b.lastTblRows.any (fun (r, v) => r == rid && sqliteRowBitEq v vals)) &&
              evalWhere tblNow vals params where? then
            let entry : RelLiveEntry :=
              { uid := curUid, rid := rid, vals := vals, projRow := projectSelectRow tblNow proj params vals }
            (curUid + 1, entry :: acc)
          else
            (curUid, acc)) (b.nextUid, [])
      { b with
        nextUid := nextUid'
        liveEntries := keptLive ++ addedRev.reverse
        mustUids := keptMust
        syncedGen := st.mutGen
        lastTblRows := tblNow.rows }

private def dedupRelBranchesAux (acc : List RelBranch) : List RelBranch → List RelBranch
  | [] => acc.reverse
  | b :: rest =>
    if acc.any (relBranchBitEq b) then dedupRelBranchesAux acc rest
    else dedupRelBranchesAux (b :: acc) rest

private def rowIsOrderMin (tbl : TableData) (orderBy : List OrderItem)
    (pool : List (Int64 × Array SqliteValue × SqliteRow)) (vals : Array SqliteValue) : Bool :=
  orderBy.isEmpty ||
    !(pool.any fun (_, v2, _) => compareByOrderItems tbl orderBy v2 vals == .lt)

private def isRollbackAbortError (r : Except SqliteError StepResult) : Bool :=
  match r with
  | .error e => e.kind == .ioError && e.sqliteCode == some 516 && e.path == none && !e.message.isEmpty
  | .ok _ => false

private def branchAllowsDone (b : RelBranch) : Bool :=
  if b.remLimit? == some 0 then true
  else if b.isSorter? != some false then b.sorterPool.isEmpty
  else canSatisfyConsumed b.consumedGroups b.mustUids

private def expandBranchForEvents (st : SqliteWorldState) (tblNow? : Option TableData)
    (proj : SelectProj) (where? : Option WhereExpr) (params : Array SqliteValue)
    (orderByEmpty : Bool) (hadRollback : Bool) (b : RelBranch) : List RelBranch :=
  let tblChanged :=
    match tblNow? with
    | none => true
    | some tblNow => !tblRowsBitEq tblNow.rows b.lastTblRows
  if hadRollback then
    if b.remLimit? == some 0 then
      [{ b with isSorter? := some true, liveEntries := [], mustUids := [] }]
    else if orderByEmpty then
      if b.isSorter? != some true && branchAllowsDone b then
        [{ b with isSorter? := some true, sorterPool := [], liveEntries := [], mustUids := [] }]
      else
        []
    else if b.isSorter? == some false then
      []
    else if b.isSorter? == some true then
      [{ b with isSorter? := some true, liveEntries := [], mustUids := [] }]
    else
      let bKeep :=
        if tblChanged then syncRelBranchLive st tblNow? proj where? params b
        else b
      [{ b with isSorter? := some true, liveEntries := [], mustUids := [] },
       { bKeep with isSorter? := none }]
  else if tblChanged then
    let bS :=
      if orderByEmpty || b.isSorter? == some false then []
      else [{ b with isSorter? := some true, liveEntries := [], mustUids := [] }]
    let bL :=
      if b.isSorter? == some true then []
      else [{ syncRelBranchLive st tblNow? proj where? params b with isSorter? := some false }]
    bS ++ bL
  else
    [b]

private def groupLiveByOrderKey (tbl : TableData) (orderBy : List OrderItem) :
    List RelLiveEntry → List (Array SqliteValue × List Nat)
  | [] => []
  | e :: rest =>
    let groups := groupLiveByOrderKey tbl orderBy rest
    if orderBy.isEmpty then
      match groups with
      | [] => [(e.vals, [e.uid])]
      | (rep, uids) :: gs => (rep, e.uid :: uids) :: gs
    else
      let rec insertGroup : List (Array SqliteValue × List Nat) → List (Array SqliteValue × List Nat)
        | [] => [(e.vals, [e.uid])]
        | (rep, uids) :: gs =>
          if compareByOrderItems tbl orderBy e.vals rep == .eq then
            (rep, e.uid :: uids) :: gs
          else
            (rep, uids) :: insertGroup gs
      insertGroup groups

private def stepBranchRow (tblNow? : Option TableData) (orderBy : List OrderItem)
    (rRow : SqliteRow) (b : RelBranch) : List RelBranch :=
  if b.remLimit? == some 0 then []
  else if b.isSorter? == some true then
    match b.sorterPool.find? (fun (_, vals, projRow) =>
        sqliteRowBitEq rRow projRow && rowIsOrderMin b.tblSchema orderBy b.sorterPool vals) with
    | none => []
    | some (rid, vals, _) =>
      [{ b with
          sorterPool := removePoolEntry rid vals b.sorterPool
          lastOrig? := if orderBy.isEmpty then none else some vals
          remLimit? := b.remLimit?.map (· - 1) }]
  else if b.isSorter? == none then
    match b.sorterPool.find? (fun (_, vals, projRow) =>
        sqliteRowBitEq rRow projRow && rowIsOrderMin b.tblSchema orderBy b.sorterPool vals) with
    | none => []
    | some (rid, vals, _) =>
      let candUids := (b.liveEntries.filter fun e =>
        sqliteRowBitEq rRow e.projRow &&
          (orderBy.isEmpty || compareByOrderItems b.tblSchema orderBy e.vals vals == .eq)).map (·.uid)
      [{ b with
          sorterPool := removePoolEntry rid vals b.sorterPool
          consumedGroups := addConsumeGroup candUids b.consumedGroups
          lastOrig? := if orderBy.isEmpty then none else some vals
          remLimit? := b.remLimit?.map (· - 1) }]
  else
    match tblNow? with
    | none => []
    | some tblNow =>
      let monoCands := b.liveEntries.filter fun e =>
        let monoOk :=
          orderBy.isEmpty ||
            (match b.lastOrig? with
             | some prev => compareByOrderItems tblNow orderBy prev e.vals != .gt
             | none => true)
        sqliteRowBitEq rRow e.projRow && monoOk
      let tieGroups := groupLiveByOrderKey tblNow orderBy monoCands
      tieGroups.filterMap fun (repVals, candUids) =>
        let reqBefore :=
          if orderBy.isEmpty then []
          else
            b.mustUids.filter fun u =>
              match b.liveEntries.find? (fun e => e.uid == u) with
              | some e0 => compareByOrderItems tblNow orderBy e0.vals repVals == .lt
              | none => false
        let consumed' := addConsumeGroup candUids b.consumedGroups
        if canSatisfyConsumed consumed' reqBefore then
          some { b with
            consumedGroups := consumed'
            lastOrig? := if orderBy.isEmpty then none else some repVals
            remLimit? := b.remLimit?.map (· - 1) }
        else
          none

private def buildInitLiveEntriesAux (uid : Nat) :
    List (Int64 × Array SqliteValue × SqliteRow) → List RelLiveEntry
  | [] => []
  | (rid, vals, projRow) :: rest =>
    { uid := uid, rid := rid, vals := vals, projRow := projRow } ::
      buildInitLiveEntriesAux (uid + 1) rest

/-- Relational `Raw.step` validator admitting valid unordered permutations, sorter/live-cursor
    interleaving under mid-scan DML, optional `SQLITE_ABORT_ROLLBACK (516)`, and relational `INSERT` witnesses. -/
def stepRawRelational (stmt : StmtHandle) (actual : Except SqliteError StepResult)
    (st : SqliteWorldState) (actualInsertRows? : Option (List SqliteRow) := none) :
    Except SqliteError StepResult × Option SqliteWorldState :=
  let fallbackDet := fun () =>
    let (mRes, stNext) := modelStep stmt st
    (mRes, if rawStepResultEq actual mRes then some stNext else none)
  match st.stmts.find? (fun s => s.handle == stmt) with
  | none => fallbackDet ()
  | some entry =>
    if !entry.relBranches.isEmpty then
      match lookupConn? st entry.handle.dbId, entry.stmt with
      | some conn, .select proj (some tblName) where? orderBy _ =>
        let params := entry.boundParams?.getD #[]
        if entry.rollbackMayAbort && isRollbackAbortError actual then
          if entry.relBranches.any (fun b => b.remLimit? != some 0 && b.isSorter? != some true) then
            let e := mapRawError (.ioFailure 516 "abort due to ROLLBACK")
            (.error e, some (markStmtStepErr st stmt conn.id e).2)
          else
            (modelStep stmt st).1 |> fun exp => (exp, none)
        else
          match actual with
          | .error _ =>
            let (mRes, _) := modelStep stmt st
            (mRes, none)
          | .ok resVal =>
            let tblNow? := lookupTable? (connVisibleCatalog st conn) tblName
            let expanded := entry.relBranches.flatMap
              (expandBranchForEvents st tblNow? proj where? params orderBy.isEmpty entry.rollbackMayAbort)
            match resVal with
            | .done =>
              if expanded.any branchAllowsDone then
                (.ok .done, some (markStmtDone st stmt conn.id).2)
              else
                let exp :=
                  if entry.rollbackMayAbort && expanded.isEmpty then
                    .error (mapRawError (.ioFailure 516 "abort due to ROLLBACK"))
                  else
                    match expanded.head? with
                    | some b =>
                      if b.isSorter? != some false then
                        match b.sorterPool.head? with
                        | some (_, _, r) => .ok (.row r)
                        | none => .ok .done
                      else
                        match b.liveEntries.find? (fun e => b.mustUids.contains e.uid) <|> b.liveEntries.head? with
                        | some e => .ok (.row e.projRow)
                        | none => .ok .done
                    | none => .ok .done
                (exp, none)
            | .row rRow =>
              let nextBranches := dedupRelBranchesAux []
                (expanded.flatMap (stepBranchRow tblNow? orderBy rRow))
              if nextBranches.isEmpty then
                let exp :=
                  if entry.rollbackMayAbort && expanded.isEmpty then
                    .error (mapRawError (.ioFailure 516 "abort due to ROLLBACK"))
                  else
                    .ok .done
                (exp, none)
              else
                let updated := st.stmts.map fun s =>
                  if s.handle == stmt then
                    { s with stepIdx := s.stepIdx + 1, relBranches := nextBranches,
                             rollbackMayAbort := entry.rollbackMayAbort && !orderBy.isEmpty,
                             holdsReadLock := true }
                  else s
                (.ok (.row rRow), some { st with stmts := updated })
      | _, _ => fallbackDet ()
    else if !entry.rollbackMayAbort && entry.resultRows?.isNone then
      match lookupConn? st entry.handle.dbId, entry.stmt with
      | some conn, .select proj (some tblName) where? orderBy limit? =>
        let params := entry.boundParams?.getD #[]
        match selectStepPrelude stmt st conn tblName limit? params with
        | .error (mRes, stErr) =>
          (mRes, if rawStepResultEq actual mRes then some stErr else none)
        | .ok (tbl, remLimit?, st1) =>
          let initRows := matchedTableRows tbl proj where? params
          if remLimit? == some 0 || initRows.isEmpty then
            let stDone := (markStmtDone st1 stmt conn.id).2
            (.ok .done, if rawStepResultEq actual (.ok .done) then some stDone else none)
          else
            match actual with
            | .ok (.row rRow) =>
              let schemaTbl := { tbl with rows := [] }
              let initLive : List RelLiveEntry := buildInitLiveEntriesAux 0 initRows
              let initMust : List Nat := initLive.map (·.uid)
              let initBranches : List RelBranch :=
                match initRows.find? (fun (_, vals, projRow) =>
                    sqliteRowBitEq rRow projRow && rowIsOrderMin schemaTbl orderBy initRows vals) with
                | none => []
                | some (rid, vals, _) =>
                  let candUids := (initLive.filter fun e =>
                    sqliteRowBitEq rRow e.projRow &&
                      (orderBy.isEmpty || compareByOrderItems schemaTbl orderBy e.vals vals == .eq)).map (·.uid)
                  [{ isSorter? := none
                     sorterPool := removePoolEntry rid vals initRows
                     nextUid := initLive.length
                     liveEntries := initLive
                     mustUids := initMust
                     consumedGroups := [{ candUids := candUids, demand := 1 }]
                     lastOrig? := if orderBy.isEmpty then none else some vals
                     remLimit? := remLimit?.map (· - 1)
                     tblSchema := schemaTbl
                     syncedGen := st1.mutGen
                     lastTblRows := tbl.rows }]
              if initBranches.isEmpty then
                let det := (sortList (fun a b => compareByOrderItems tbl orderBy a.2.1 b.2.1 == .lt) initRows).head?.map (·.2.2)
                (match det with | some r => .ok (.row r) | none => .ok .done, none)
              else
                let updated := st1.stmts.map fun s =>
                  if s.handle == stmt then
                    { s with stepIdx := 1, relBranches := initBranches, rollbackMayAbort := false,
                             holdsReadLock := true, err? := none }
                  else s
                (.ok (.row rRow), some { st1 with stmts := updated })
            | _ =>
              let det := (sortList (fun a b => compareByOrderItems tbl orderBy a.2.1 b.2.1 == .lt) initRows).head?.map (·.2.2)
              (match det with | some r => .ok (.row r) | none => .ok .done, none)
      | _, _ =>
        match actual, actualInsertRows?, lookupConn? st entry.handle.dbId, entry.stmt with
        | .ok .done, some actualRows, some conn, .insert _ _ _ =>
          if !entry.rollbackMayAbort && entry.resultRows?.isNone then
            let params := entry.boundParams?.getD #[]
            let (res, st1) := executeModelWriteStmtWith (applyInsertWithWitness actualRows) st conn entry.stmt params
            match res with
            | .ok _ => (.ok .done, some (markStmtDone st1 stmt conn.id).2)
            | .error e => (markStmtStepErr st1 stmt conn.id e).1 |> fun exp => (exp, none)
          else
            fallbackDet ()
        | _, _, _, _ => fallbackDet ()
    else
      match actual, actualInsertRows?, lookupConn? st entry.handle.dbId, entry.stmt with
      | .ok .done, some actualRows, some conn, .insert _ _ _ =>
        if !entry.rollbackMayAbort && entry.resultRows?.isNone then
          let params := entry.boundParams?.getD #[]
          let (res, st1) := executeModelWriteStmtWith (applyInsertWithWitness actualRows) st conn entry.stmt params
          match res with
          | .ok _ => (.ok .done, some (markStmtDone st1 stmt conn.id).2)
          | .error e => (markStmtStepErr st1 stmt conn.id e).1 |> fun exp => (exp, none)
        else
          fallbackDet ()
      | _, _, _, _ => fallbackDet ()

/-- Step a model statement until `.done` or fuel exhaustion, discarding yielded rows. -/
def modelExecLoop (ops : RawSqliteOpsM (StateM SqliteWorldState)) (stmt : StmtHandle) :
    Nat → StateM SqliteWorldState (Except SqliteError Unit)
  | 0 => pure (.error (ops.mapRawError (.ioFailure 0 "sqlite statement step limit exceeded")))
  | fuel + 1 => do
    match ← ops.step stmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok ())
    | .ok (.row _) => modelExecLoop ops stmt fuel

/-- Prepare, optionally bind `params?`, step to completion, and always finalize in `StateM SqliteWorldState`. -/
def modelExecMaybeBind (ops : RawSqliteOpsM (StateM SqliteWorldState))
    (db : DbHandle) (sql : String) (params? : Option (Array SqliteValue)) :
    StateM SqliteWorldState (Except SqliteError Unit) := do
  match ← ops.prepare db sql with
  | .error e => pure (.error e)
  | .ok stmt =>
    let (res, finRes) ← tryFinally' (do
      match params? with
      | none => modelExecLoop ops stmt 100000000
      | some params =>
        match ← ops.bind stmt params with
        | .error e => pure (.error e)
        | .ok () => modelExecLoop ops stmt 100000000) (fun _ => ops.finalize stmt)
    match res with
    | .error e => pure (.error e)
    | .ok () =>
      match finRes with
      | .error e => pure (.error e)
      | .ok () => pure (.ok ())

/-- Step a model query statement until `.done` or fuel exhaustion, collecting rows. -/
def modelQueryLoop (ops : RawSqliteOpsM (StateM SqliteWorldState)) (stmt : StmtHandle)
    (acc : Array SqliteRow) : Nat → StateM SqliteWorldState (Except SqliteError (Array SqliteRow))
  | 0 => pure (.error (ops.mapRawError (.ioFailure 0 "sqlite query row limit exceeded")))
  | fuel + 1 => do
    match ← ops.step stmt with
    | .error e => pure (.error e)
    | .ok .done => pure (.ok acc)
    | .ok (.row cols) => modelQueryLoop ops stmt (acc.push cols) fuel

/-- Pure `SqliteApiM (StateM SqliteWorldState)` reference implementation over `modelRawOps` and shared validators. -/
def modelApi : SqliteApiM (StateM SqliteWorldState) :=
  { mapRawError := modelRawOps.mapRawError
    validateConfig := validateConfigWith modelRawOps.mapRawError
    withDb := fun path cfg action => do
      match validateConfigWith modelRawOps.mapRawError cfg with
      | .error e => pure (.error e)
      | .ok () =>
        match ← modelRawOps.openDb path cfg with
        | .error e => pure (.error e)
        | .ok db =>
          let (res, closeRes) ← tryFinally' (action db) (fun _ => modelRawOps.closeDb db)
          match res with
          | .error e => pure (.error e)
          | .ok a =>
            match closeRes with
            | .error e => pure (.error e)
            | .ok () => pure (.ok a)
    withTransaction := fun db action => do
      match ← modelExecMaybeBind modelRawOps db "BEGIN IMMEDIATE" none with
      | .error e => pure (.error e)
      | .ok () =>
        let (res, finRes) ← tryFinally' (action db) fun
          | some (.ok _) => modelExecMaybeBind modelRawOps db "COMMIT" none
          | _ => modelExecMaybeBind modelRawOps db "ROLLBACK" none
        match res with
        | .error e => pure (.error e)
        | .ok a =>
          match finRes with
          | .ok () => pure (.ok a)
          | .error e =>
            let _ ← modelExecMaybeBind modelRawOps db "ROLLBACK" none
            pure (.error e)
    exec := fun db sql params =>
      modelExecMaybeBind modelRawOps db sql (some params)
    query := fun db sql params => do
      match ← modelRawOps.prepare db sql with
      | .error e => pure (.error e)
      | .ok stmt =>
        let (res, finRes) ← tryFinally' (do
          match ← modelRawOps.bind stmt params with
          | .error e => pure (.error e)
          | .ok () => modelQueryLoop modelRawOps stmt #[] 100000000) (fun _ => modelRawOps.finalize stmt)
        match res with
        | .error e => pure (.error e)
        | .ok rows =>
          match finRes with
          | .error e => pure (.error e)
          | .ok () => pure (.ok rows)
    queryOne := fun db sql params => do
      match ← modelRawOps.prepare db sql with
      | .error e => pure (.error e)
      | .ok stmt =>
        let (res, finRes) ← tryFinally' (do
          match ← modelRawOps.bind stmt params with
          | .error e => pure (Except.error e)
          | .ok () =>
            match ← modelRawOps.step stmt with
            | .error e => pure (Except.error e)
            | .ok .done => pure (Except.ok none)
            | .ok (.row cols) => pure (Except.ok (some cols))) (fun _ => modelRawOps.finalize stmt)
        match res with
        | .error e => pure (.error e)
        | .ok row? =>
          match finRes with
          | .error e => pure (.error e)
          | .ok () => pure (.ok row?)
    activeDbCount := modelRawOps.activeDbCount
    activeStmtCount := modelRawOps.activeStmtCount }

/-- Helper returning the currently visible `DbCatalog` for `db` in `st`. -/
def visibleCatalogForDb (st : SqliteWorldState) (db : DbHandle) : Option DbCatalog :=
  (lookupConn? st db.id).map (connVisibleCatalog st)

private def ipkTargetForStmt (st : SqliteWorldState) (db : DbHandle) (stmt : SqlStmt) :
    Option (String × String) :=
  match stmt with
  | .insert tblName _ _ =>
    match visibleCatalogForDb st db with
    | none => none
    | some cat =>
      match lookupTable? cat tblName with
      | none => none
      | some tbl =>
        match tbl.cols.find? isIntegerPrimaryKey with
        | none => none
        | some ipkCol => some (tbl.name, ipkCol.name)
  | _ => none

/-- If `sql` parses as an `INSERT` into a table in `db`'s visible catalog with an
    `INTEGER PRIMARY KEY` column, return `some (tableName, ipkColName)`. -/
def insertIpkTarget? (st : SqliteWorldState) (db : DbHandle) (sql : String) :
    Option (String × String) :=
  match parseRawSqlNoCap sql.toUTF8 with
  | .ok (stmt, _) => ipkTargetForStmt st db stmt
  | .error _ => none

/-- If prepared `stmt` is an `INSERT` into a table in its owning connection's visible catalog
    with an `INTEGER PRIMARY KEY` column, return `some (tableName, ipkColName)`. -/
def stmtInsertIpkTarget? (st : SqliteWorldState) (stmt : StmtHandle) : Option (String × String) :=
  match st.stmts.find? (fun s => s.handle == stmt) with
  | none => none
  | some entry => ipkTargetForStmt st { id := entry.handle.dbId } entry.stmt

/-- Execute a curated SQL statement relationally against `actualRows` when `sql` is an `INSERT`,
    verifying exact explicit rowids, unused `Int64` auto-rowids (strictly increasing for
    `AUTOINCREMENT`), bit-exact non-rowid columns, uniqueness, and foreign keys before advancing state.
    Returns `(.ok (), some stFin)` with the finalized post-state on witness acceptance, and
    `(.error e, none)` without advancing state on any prepare, bind, witness-step, or finalize failure. -/
def stepInsertRelational (st : SqliteWorldState) (db : DbHandle) (sql : String)
    (params : Array SqliteValue) (actualRows : List SqliteRow) :
    Except SqliteError Unit × Option SqliteWorldState :=
  let (prepRes, stPrep) := modelRawOps.prepare db sql st
  match prepRes with
  | .error e => (.error e, none)
  | .ok stmtH =>
    let (bindRes, stBind) := modelRawOps.bind stmtH params stPrep
    match bindRes with
    | .error e => (.error e, none)
    | .ok () =>
      let (stepRes, stStep?) := stepRawRelational stmtH (.ok .done) stBind (some actualRows)
      match stepRes, stStep? with
      | .ok _, some stStep =>
        let (finRes, stFin) := modelRawOps.finalize stmtH stStep
        match finRes with
        | .ok () => (.ok (), some stFin)
        | .error e => (.error e, none)
      | .error e, _ =>
        (.error e, none)
      | .ok _, none =>
        (.error (mapRawError (.sqliteCodeError 1 "relational insert step failed")), none)

/-- Total well-formedness guard on `SqliteWorldState` for `Core.RefinesStepFromFinally`. -/
def rawStepWf (_ : SqliteWorldState) : Bool := true

/-- Execute one `Raw.Model.RawStepReq` against an arbitrary `RawSqliteOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawSqliteOpsM (StateM W))
    (req : Raw.Model.RawStepReq) : StateM W Raw.Model.RawStepOut :=
  Raw.Model.execRawStep raw req

/-- Allowed deterministic single-step relation for `RawSqliteOpsM` pinned to `modelRawOps`. -/
def allowedRawStep (s : SqliteWorldState) (req : Raw.Model.RawStepReq)
    (out : Raw.Model.RawStepOut) (s' : SqliteWorldState) : Prop :=
  let r := (execRawStep modelRawOps req).run s
  out = r.1 ∧ s' = r.2

/-- Finite reified database action used to exercise `withDb` and `withTransaction` inside `Core.RefinesStepFromFinally`. -/
inductive StepAction where
  /-- Return a pure result without calling SQLite. -/
  | ret (res : Except SqliteError Unit)
  /-- Execute one parameterized SQL statement on the scoped `DbHandle`. -/
  | exec (sql : String) (params : Array SqliteValue)
  /-- Sequence two `StepAction` programs, short-circuiting on error. -/
  | seq (first second : StepAction)

/-- Interpret a finite `StepAction` against an arbitrary `SqliteApiM (StateM W)`. -/
def runStepAction {W : Type} (api : SqliteApiM (StateM W)) (db : DbHandle) :
    StepAction → StateM W (Except SqliteError Unit)
  | .ret res => pure res
  | .exec sql params => api.exec db sql params
  | .seq first second => do
    match ← runStepAction api db first with
    | .error e => pure (.error e)
    | .ok () => runStepAction api db second

/-- Request sum covering all effectful `SqliteApiM` operations in `Core.RefinesStepFromFinally`. -/
inductive PkgStepReq where
  /-- Open a connection, execute `act`, and always close the handle. -/
  | withDb (path : String) (cfg : OpenConfig) (act : StepAction)
  /-- Run `act` inside a `BEGIN IMMEDIATE` / `COMMIT` / `ROLLBACK` transaction bracket. -/
  | withTransaction (db : DbHandle) (act : StepAction)
  /-- Execute a parameterized SQL statement without returning rows. -/
  | exec (db : DbHandle) (sql : String) (params : Array SqliteValue)
  /-- Query and collect all rows. -/
  | query (db : DbHandle) (sql : String) (params : Array SqliteValue)
  /-- Query and collect at most one row. -/
  | queryOne (db : DbHandle) (sql : String) (params : Array SqliteValue)
  /-- Read the active database handle count. -/
  | activeDbCount
  /-- Read the active prepared statement handle count. -/
  | activeStmtCount

/-- Output sum for `PkgStepReq` transitions in `Core.RefinesStepFromFinally`. -/
inductive PkgStepOut where
  /-- Result of `withDb`, `withTransaction`, or `exec`. -/
  | unit (res : Except SqliteError Unit)
  /-- Result of `query`. -/
  | rows (res : Except SqliteError (Array SqliteRow))
  /-- Result of `queryOne`. -/
  | rowOpt (res : Except SqliteError (Option SqliteRow))
  /-- Result of `activeDbCount` or `activeStmtCount`. -/
  | count (n : Nat)

/-- Execute one `PkgStepReq` against an arbitrary `SqliteApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : SqliteApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .withDb path cfg act =>
    .unit <$> api.withDb path cfg (fun db => runStepAction api db act)
  | .withTransaction db act =>
    .unit <$> api.withTransaction db (fun txDb => runStepAction api txDb act)
  | .exec db sql params => .unit <$> api.exec db sql params
  | .query db sql params => .rows <$> api.query db sql params
  | .queryOne db sql params => .rowOpt <$> api.queryOne db sql params
  | .activeDbCount => .count <$> api.activeDbCount
  | .activeStmtCount => .count <$> api.activeStmtCount

/-- Allowed deterministic single-step relation for `SqliteApiM` pinned to `modelApi`. -/
def allowedPkgStep (s : SqliteWorldState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : SqliteWorldState) : Prop :=
  let r := (execPkgStep modelApi req).run s
  out = r.1 ∧ s' = r.2

end LeanSwe.Sqlite.Model
