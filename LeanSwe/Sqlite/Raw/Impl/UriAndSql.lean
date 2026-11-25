import LeanSwe.Sqlite.Raw.Types

namespace LeanSwe.Sqlite.Raw.Internal

open LeanSwe.Sqlite.Raw
  (SqliteErrorKind SqliteError SqliteRawError
   sqliteOpenReadOnly sqliteOpenReadWrite sqliteOpenCreate sqliteOpenUri sqliteOpenFullMutex
   OpenConfig)

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

/-- Convert a numeric SQLite result code and diagnostic string into `SqliteRawError`. -/
def classifyRawCode (path? : Option String) (code : UInt32) (detail : String) : SqliteRawError :=
  match (code &&& 0xFF).toNat with
  | 5 | 6 => .busy code detail
  | 14 => .cantOpen path? code detail
  | 19 => .constraint code detail
  | 21 => .misuse code detail
  | 8 | 10 | 11 | 13 | 26 => .ioFailure code detail
  | _ => .sqliteCodeError code detail

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

/-- Attach `some path` to `.cantOpen none ...` errors produced while opening `path`. -/
def attachOpenPath (path : String) : SqliteRawError → SqliteRawError
  | .cantOpen none code detail => .cantOpen (some path) code detail
  | other => other

/-- Return `true` iff `bs` contains a zero byte (`0`). -/
def hasZeroByte : List UInt8 → Bool
  | [] => false
  | b :: bs => b == 0 || hasZeroByte bs

/-- Structural helper for `hasZeroByteBa`. -/
def hasZeroByteBaAux (bs : ByteArray) (idx : Nat) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    if h : idx < bs.size then
      if bs[idx] == 0 then true else hasZeroByteBaAux bs (idx + 1) rem
    else
      false

/-- Return `true` iff `bs` contains a zero byte (`0`) at or after `idx`, without list allocation. -/
@[inline] def hasZeroByteBa (bs : ByteArray) (idx : Nat) : Bool :=
  hasZeroByteBaAux bs idx (bs.size - idx)

/-- Compute the `sqlite3_open_v2` bitmask (`SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_URI | ...`) for `cfg`. -/
def computeOpenFlags (cfg : OpenConfig) : UInt32 :=
  let base := sqliteOpenFullMutex ||| sqliteOpenUri
  if cfg.readOnly then
    base ||| sqliteOpenReadOnly
  else if cfg.createIfMissing then
    base ||| sqliteOpenReadWrite ||| sqliteOpenCreate
  else
    base ||| sqliteOpenReadWrite

/-- Decode one ASCII hexadecimal digit byte into `0..15`, or `none` if non-hex. -/
def hexByteVal? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then
    some (b - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then
    some (b - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then
    some (b - 0x61 + 10)
  else
    none

/-- DFA state for decoding `%HH` percent-escapes in a SQLite URI segment. -/
inductive UriDecodeState where
  /-- Outside any `%HH` escape sequence. -/
  | normal
  /-- Immediately after seeing `'%'` (`0x25`). -/
  | sawPct
  /-- After seeing `'%'` followed by valid hex byte `hiByte` with nibble value `hiVal`. -/
  | sawPctHex (hiByte : UInt8) (hiVal : UInt8)
  deriving Repr, BEq, DecidableEq

/-- Tail-recursive `%HH` decoder helper for `decodeUriBytes`. -/
def decodeUriBytesAux (acc : List UInt8) : UriDecodeState → List UInt8 → List UInt8
  | .normal, [] => acc.reverse
  | .sawPct, [] => (0x25 :: acc).reverse
  | .sawPctHex hiByte _, [] => (hiByte :: 0x25 :: acc).reverse
  | .normal, b :: bs =>
    if b == 0x25 then
      decodeUriBytesAux acc .sawPct bs
    else
      decodeUriBytesAux (b :: acc) .normal bs
  | .sawPct, b :: bs =>
    match hexByteVal? b with
    | some v1 => decodeUriBytesAux acc (.sawPctHex b v1) bs
    | none =>
      if b == 0x25 then
        decodeUriBytesAux (0x25 :: acc) .sawPct bs
      else
        decodeUriBytesAux (b :: 0x25 :: acc) .normal bs
  | .sawPctHex hiByte v1, b :: bs =>
    match hexByteVal? b with
    | some v2 =>
      let octet : UInt8 := (v1 <<< 4) ||| v2
      if octet == 0 then
        acc.reverse
      else
        decodeUriBytesAux (octet :: acc) .normal bs
    | none =>
      if b == 0x25 then
        decodeUriBytesAux (hiByte :: 0x25 :: acc) .sawPct bs
      else
        decodeUriBytesAux (b :: hiByte :: 0x25 :: acc) .normal bs

/-- Tail-recursive decoder for `%HH` percent-escapes in a SQLite URI segment,
    truncating the segment on `%00` per `sqlite3ParseUri`. -/
def decodeUriBytes (st : UriDecodeState) (bs : List UInt8) : List UInt8 :=
  decodeUriBytesAux [] st bs

/-- Decode `%HH` escapes in a SQLite URI path or query component. -/
def decodeUriComponent (bs : List UInt8) : List UInt8 :=
  decodeUriBytes .normal bs

/-- Tail-recursive helper for `takeBeforeByte`. -/
def takeBeforeByteAux (delim : UInt8) (acc : List UInt8) : List UInt8 → List UInt8
  | [] => acc.reverse
  | b :: bs => if b == delim then acc.reverse else takeBeforeByteAux delim (b :: acc) bs

/-- Take all bytes before the first occurrence of `delim`. -/
def takeBeforeByte (delim : UInt8) (bs : List UInt8) : List UInt8 :=
  takeBeforeByteAux delim [] bs

/-- Tail-recursive helper for `splitFirstByte`. -/
def splitFirstByteAux (delim : UInt8) (acc : List UInt8) :
    List UInt8 → List UInt8 × Option (List UInt8)
  | [] => (acc.reverse, none)
  | b :: bs =>
    if b == delim then (acc.reverse, some bs)
    else splitFirstByteAux delim (b :: acc) bs

/-- Split a byte list at the first occurrence of `delim` into `(prefix, afterDelim?)`. -/
def splitFirstByte (delim : UInt8) (bs : List UInt8) : List UInt8 × Option (List UInt8) :=
  splitFirstByteAux delim [] bs

/-- Tail-recursive helper for `splitOnByte`. -/
def splitOnByteAux (delim : UInt8) (cur : List UInt8) (acc : List (List UInt8)) :
    List UInt8 → List (List UInt8)
  | [] => (cur.reverse :: acc).reverse
  | b :: bs =>
    if b == delim then
      splitOnByteAux delim [] (cur.reverse :: acc) bs
    else
      splitOnByteAux delim (b :: cur) acc bs

/-- Split a byte list on every occurrence of `delim`. -/
def splitOnByte (delim : UInt8) (bs : List UInt8) : List (List UInt8) :=
  splitOnByteAux delim [] [] bs

/-- Strip a leading lowercase `"file:"` scheme prefix from `bs` when present. -/
def stripFileScheme : List UInt8 → Option (List UInt8)
  | 0x66 :: 0x69 :: 0x6C :: 0x65 :: 0x3A :: rest => some rest
  | _ => none

/-- Advance past a URI authority segment up to (and keeping) the next `'/'` (`0x2F`). -/
def dropUntilSlash : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if b == 0x2F then b :: bs else dropUntilSlash bs

/-- Strip an optional leading `"//..."` URI authority segment from `bs`. -/
def stripAuthority : List UInt8 → List UInt8
  | 0x2F :: 0x2F :: rest => dropUntilSlash rest
  | other => other

/-- UTF-8 byte sequence for `":memory:"`. -/
def colonMemoryColonBytes : List UInt8 :=
  [0x3A, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x3A]

/-- UTF-8 byte sequence for `"mode"`. -/
def modeKeyBytes : List UInt8 :=
  [0x6D, 0x6F, 0x64, 0x65]

/-- UTF-8 byte sequence for `"memory"`. -/
def memoryModeBytes : List UInt8 :=
  [0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]

/-- UTF-8 byte sequence for `"ro"`. -/
def roModeBytes : List UInt8 :=
  [0x72, 0x6F]

/-- Tail-recursive helper for `extractLastUriMode`. -/
def extractLastUriModeAux (cur : Option (List UInt8)) : List (List UInt8) → Option (List UInt8)
  | [] => cur
  | seg :: rest =>
    let (rawKey, rawVal?) := splitFirstByte 0x3D seg
    let key := decodeUriComponent rawKey
    let next :=
      if key == modeKeyBytes then
        some (match rawVal? with | none => [] | some rv => decodeUriComponent rv)
      else cur
    extractLastUriModeAux next rest

/-- Extract the effective (last) `mode=...` query parameter value from `&`-split URI query segments,
    ignoring empty option names per `sqlite3ParseUri`. -/
def extractLastUriMode (segs : List (List UInt8)) : Option (List UInt8) :=
  extractLastUriModeAux none segs

/-- Advance streaming pattern matcher on one decoded URI byte. -/
@[inline] def feedUriMatchByte (rem? : Option (List UInt8)) (b : UInt8) : Option (List UInt8) :=
  match rem? with
  | some (p :: ps) => if b == p then some ps else none
  | _ => none

/-- Structural helper matching `%HH`-decoded bytes of `bs[idx ..< stop]` against `rem?` without list allocation. -/
def decodeUriMatchBaAux (bs : ByteArray) (stop : Nat) :
    UriDecodeState → Option (List UInt8) → Nat → Nat → Bool
  | .normal, rem?, _, 0 => rem? == some []
  | .sawPct, rem?, _, 0 => feedUriMatchByte rem? 0x25 == some []
  | .sawPctHex hiByte _, rem?, _, 0 => feedUriMatchByte (feedUriMatchByte rem? 0x25) hiByte == some []
  | st, rem?, idx, fuel + 1 =>
    if h : idx < stop ∧ idx < bs.size then
      let b := bs[idx]
      match st with
      | .normal =>
        if b == 0x25 then
          decodeUriMatchBaAux bs stop .sawPct rem? (idx + 1) fuel
        else
          decodeUriMatchBaAux bs stop .normal (feedUriMatchByte rem? b) (idx + 1) fuel
      | .sawPct =>
        match hexByteVal? b with
        | some v1 => decodeUriMatchBaAux bs stop (.sawPctHex b v1) rem? (idx + 1) fuel
        | none =>
          if b == 0x25 then
            decodeUriMatchBaAux bs stop .sawPct (feedUriMatchByte rem? 0x25) (idx + 1) fuel
          else
            decodeUriMatchBaAux bs stop .normal (feedUriMatchByte (feedUriMatchByte rem? 0x25) b) (idx + 1) fuel
      | .sawPctHex hiByte v1 =>
        match hexByteVal? b with
        | some v2 =>
          let octet : UInt8 := (v1 <<< 4) ||| v2
          if octet == 0 then
            rem? == some []
          else
            decodeUriMatchBaAux bs stop .normal (feedUriMatchByte rem? octet) (idx + 1) fuel
        | none =>
          if b == 0x25 then
            decodeUriMatchBaAux bs stop .sawPct
              (feedUriMatchByte (feedUriMatchByte rem? 0x25) hiByte) (idx + 1) fuel
          else
            decodeUriMatchBaAux bs stop .normal
              (feedUriMatchByte (feedUriMatchByte (feedUriMatchByte rem? 0x25) hiByte) b) (idx + 1) fuel
    else
      match st with
      | .normal => rem? == some []
      | .sawPct => feedUriMatchByte rem? 0x25 == some []
      | .sawPctHex hiByte _ => feedUriMatchByte (feedUriMatchByte rem? 0x25) hiByte == some []

/-- Return `true` iff `decodeUriComponent` of `bs[start ..< stop]` equals `pat`, without list allocation. -/
@[inline] def decodeUriMatchBa (bs : ByteArray) (start stop : Nat) (pat : List UInt8) : Bool :=
  decodeUriMatchBaAux bs stop .normal (some pat) start (stop - start)

/-- Return the first index `i ∈ [idx, stop)` with `bs[i] == delim`, or `stop` if absent. -/
def findByteBeforeAux (bs : ByteArray) (delim : UInt8) (stop : Nat) (idx : Nat) : Nat → Nat
  | 0 => stop
  | fuel + 1 =>
    if h : idx < stop ∧ idx < bs.size then
      if bs[idx] == delim then idx else findByteBeforeAux bs delim stop (idx + 1) fuel
    else
      stop

/-- Return the first index `i ∈ [idx, stop)` with `bs[i] == delim`, or `stop` if absent. -/
@[inline] def findByteBefore (bs : ByteArray) (delim : UInt8) (idx stop : Nat) : Nat :=
  findByteBeforeAux bs delim stop idx (stop - idx)

/-- Advance past `"//..."` authority bytes up to `'/'` (`0x2F`) or `stop` without list allocation. -/
@[inline] def stripAuthorityIdx (bs : ByteArray) (start stop : Nat) : Nat :=
  if h : start + 1 < stop ∧ start + 1 < bs.size then
    if bs[start] == 0x2F && bs[start + 1] == 0x2F then
      findByteBefore bs 0x2F (start + 2) stop
    else
      start
  else
    start

/-- Check exact equality of `bs` with `":memory:"` without list allocation. -/
@[inline] def isExactColonMemoryBa (bs : ByteArray) : Bool :=
  if h : bs.size == 8 then
    let _ : 7 < bs.size := by simp only [beq_iff_eq] at h; omega
    bs[0] == 0x3A && bs[1] == 0x6D && bs[2] == 0x65 && bs[3] == 0x6D &&
      bs[4] == 0x6F && bs[5] == 0x72 && bs[6] == 0x79 && bs[7] == 0x3A
  else
    false

/-- Check `"file:"` prefix on `bs` without list allocation. -/
@[inline] def hasFileSchemeBa (bs : ByteArray) : Bool :=
  if h : 4 < bs.size then
    bs[0] == 0x66 && bs[1] == 0x69 && bs[2] == 0x6C && bs[3] == 0x65 && bs[4] == 0x3A
  else
    false

/-- Scan `&`-separated query segments in `bs[idx ..< stop]` tracking `(lastModeIsMemory, lastModeIsRo)` without list allocation. -/
def extractLastUriModeFlagsBaAux (bs : ByteArray) (stop : Nat) (cur : Bool × Bool) (idx : Nat) :
    Nat → Bool × Bool
  | 0 => cur
  | fuel + 1 =>
    let segStop := findByteBefore bs 0x26 idx stop
    let eqIdx := findByteBefore bs 0x3D idx segStop
    let next :=
      if decodeUriMatchBa bs idx eqIdx modeKeyBytes then
        if eqIdx < segStop then
          let valStart := eqIdx + 1
          (decodeUriMatchBa bs valStart segStop memoryModeBytes,
           decodeUriMatchBa bs valStart segStop roModeBytes)
        else
          (false, false)
      else
        cur
    if segStop < stop then
      extractLastUriModeFlagsBaAux bs stop next (segStop + 1) fuel
    else
      next

/-- Classify a UTF-8 path/URI `ByteArray` into `(isMemoryTarget, isUriReadOnly)` without list allocation. -/
def classifyPathBytesBa (bs : ByteArray) : Bool × Bool :=
  if isExactColonMemoryBa bs then
    (true, false)
  else if !hasFileSchemeBa bs then
    (false, false)
  else
    let fragStop := findByteBefore bs 0x23 5 bs.size
    let pathStart := stripAuthorityIdx bs 5 fragStop
    let qIdx := findByteBefore bs 0x3F pathStart fragStop
    let isMemPath := decodeUriMatchBa bs pathStart qIdx colonMemoryColonBytes
    let (isMemMode, isRoMode) :=
      if qIdx < fragStop then
        extractLastUriModeFlagsBaAux bs fragStop (false, false) (qIdx + 1) (fragStop - (qIdx + 1) + 1)
      else
        (false, false)
    (isMemPath || isMemMode, isRoMode)

/-- Classify a UTF-8 path/URI byte list into `(isMemoryTarget, isUriReadOnly)` matching `sqlite3ParseUri`. -/
def classifyPathBytes (bs : List UInt8) : Bool × Bool :=
  if bs == colonMemoryColonBytes then
    (true, false)
  else
    match stripFileScheme bs with
    | none => (false, false)
    | some afterScheme =>
      let beforeFrag := takeBeforeByte 0x23 afterScheme
      let afterAuth := stripAuthority beforeFrag
      let (rawFile, rawQuery?) := splitFirstByte 0x3F afterAuth
      let decodedFile := decodeUriComponent rawFile
      let lastMode? := match rawQuery? with
        | none => none
        | some q => extractLastUriMode (splitOnByte 0x26 q)
      let isMem := decodedFile == colonMemoryColonBytes || lastMode? == some memoryModeBytes
      let isRo := lastMode? == some roModeBytes
      (isMem, isRo)

/-- Return `true` iff `path` opens an in-memory SQLite database (`":memory:"`, `"file::memory:"`,
    or a `"file:..."` URI whose decoded filename is `":memory:"` or whose effective `mode` query parameter is `"memory"`). -/
def isMemoryTarget (path : String) : Bool :=
  (classifyPathBytesBa path.toUTF8).1

/-- Return `true` iff `path` is a `"file:..."` SQLite URI whose effective `mode` query parameter is `"ro"`. -/
def isUriReadOnly (path : String) : Bool :=
  (classifyPathBytesBa path.toUTF8).2

/-- Return `true` iff `openDb` should execute `PRAGMA journal_mode = WAL;` for `(path, cfg)`. -/
def shouldEnableWal (path : String) (cfg : OpenConfig) : Bool :=
  if cfg.readOnly || !cfg.walMode then
    false
  else
    let (isMem, isRo) := classifyPathBytesBa path.toUTF8
    !isMem && !isRo

/-- Return `true` iff `b` is SQLite ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\f'`, `'\r'`). -/
def isSqlAsciiSpace (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D

/-- DFA state for scanning unconsumed SQL tail bytes after `sqlite3_prepare_v2`. -/
inductive SqlTailScanState where
  /-- Outside any SQL comment or whitespace run. -/
  | normal
  /-- Inside an ASCII SQL whitespace run (`CC_SPACE`), where SQLite also consumes `0x0B`. -/
  | inSpace
  /-- Saw a single `'-'` (`0x2D`) outside comments; next byte must be `'-'` (`0x2D`). -/
  | sawDash
  /-- Inside a `--` SQL line comment until `'\n'` (`0x0A`) or end of input. -/
  | inLineComment
  /-- Saw a single `'/'` (`0x2F`) outside comments; next byte must be `'*'` (`0x2A`). -/
  | sawSlash
  /-- Inside a `/* ... */` block comment waiting for `'*'` (`0x2A`). -/
  | inBlockComment
  /-- Inside a `/* ... */` block comment immediately after seeing `'*'` (`0x2A`). -/
  | inBlockSawStar
  /-- Saw leading UTF-8 BOM byte `0xEF`, expecting `0xBB`. -/
  | sawBom1
  /-- Saw UTF-8 BOM prefix `0xEF 0xBB`, expecting `0xBF`. -/
  | sawBom2
  deriving Repr, BEq, DecidableEq

/-- Structurally recursive scanner accepting only SQLite ASCII whitespace (`0x0B` only inside a
    `CC_SPACE` run after `isSqlAsciiSpace` or `'\n'`), UTF-8 BOM (`0xEF 0xBB 0xBF`), `--` line
    comments, and closed `/* ... */` block comments, rejecting unclosed block comments and trailing SQL tokens. -/
def scanSqlTail : SqlTailScanState → List UInt8 → Bool
  | .normal, [] => true
  | .inSpace, [] => true
  | .inLineComment, [] => true
  | .sawDash, [] => false
  | .sawSlash, [] => false
  | .inBlockComment, [] => false
  | .inBlockSawStar, [] => false
  | .sawBom1, [] => false
  | .sawBom2, [] => false
  | .normal, b :: bs =>
    if isSqlAsciiSpace b then
      scanSqlTail .inSpace bs
    else if b == 0xEF then
      scanSqlTail .sawBom1 bs
    else if b == 0x2D then
      scanSqlTail .sawDash bs
    else if b == 0x2F then
      scanSqlTail .sawSlash bs
    else
      false
  | .inSpace, b :: bs =>
    if isSqlAsciiSpace b || b == 0x0B then
      scanSqlTail .inSpace bs
    else if b == 0xEF then
      scanSqlTail .sawBom1 bs
    else if b == 0x2D then
      scanSqlTail .sawDash bs
    else if b == 0x2F then
      scanSqlTail .sawSlash bs
    else
      false
  | .sawBom1, b :: bs =>
    if b == 0xBB then scanSqlTail .sawBom2 bs else false
  | .sawBom2, b :: bs =>
    if b == 0xBF then scanSqlTail .normal bs else false
  | .sawDash, b :: bs =>
    if b == 0x2D then
      scanSqlTail .inLineComment bs
    else
      false
  | .inLineComment, b :: bs =>
    if b == 0x0A then
      scanSqlTail .inSpace bs
    else
      scanSqlTail .inLineComment bs
  | .sawSlash, b :: bs =>
    if b == 0x2A then
      scanSqlTail .inBlockComment bs
    else
      false
  | .inBlockComment, b :: bs =>
    if b == 0x2A then
      scanSqlTail .inBlockSawStar bs
    else
      scanSqlTail .inBlockComment bs
  | .inBlockSawStar, b :: bs =>
    if b == 0x2F then
      scanSqlTail .normal bs
    else if b == 0x2A then
      scanSqlTail .inBlockSawStar bs
    else
      scanSqlTail .inBlockComment bs

/-- Return `true` iff unconsumed SQL tail bytes consist solely of ASCII whitespace,
    `--` line comments, and closed `/* ... */` block comments. -/
def isIgnorableSqlTail (tailBytes : List UInt8) : Bool :=
  scanSqlTail .normal tailBytes

/-- Structural tail-recursive SQL tail lexer helper on `ByteArray`. -/
def scanSqlTailBaAux (st : SqlTailScanState) (bs : ByteArray) (idx : Nat) : Nat → Bool
  | 0 =>
    match st with
    | .normal | .inSpace | .inLineComment => true
    | _ => false
  | rem + 1 =>
    if h : idx < bs.size then
      let b := bs[idx]
      let nextIdx := idx + 1
      match st with
      | .normal =>
        if isSqlAsciiSpace b then scanSqlTailBaAux .inSpace bs nextIdx rem
        else if b == 0xEF then scanSqlTailBaAux .sawBom1 bs nextIdx rem
        else if b == 0x2D then scanSqlTailBaAux .sawDash bs nextIdx rem
        else if b == 0x2F then scanSqlTailBaAux .sawSlash bs nextIdx rem
        else false
      | .inSpace =>
        if isSqlAsciiSpace b || b == 0x0B then scanSqlTailBaAux .inSpace bs nextIdx rem
        else if b == 0xEF then scanSqlTailBaAux .sawBom1 bs nextIdx rem
        else if b == 0x2D then scanSqlTailBaAux .sawDash bs nextIdx rem
        else if b == 0x2F then scanSqlTailBaAux .sawSlash bs nextIdx rem
        else false
      | .sawBom1 => if b == 0xBB then scanSqlTailBaAux .sawBom2 bs nextIdx rem else false
      | .sawBom2 => if b == 0xBF then scanSqlTailBaAux .normal bs nextIdx rem else false
      | .sawDash => if b == 0x2D then scanSqlTailBaAux .inLineComment bs nextIdx rem else false
      | .inLineComment => if b == 0x0A then scanSqlTailBaAux .inSpace bs nextIdx rem else scanSqlTailBaAux .inLineComment bs nextIdx rem
      | .sawSlash => if b == 0x2A then scanSqlTailBaAux .inBlockComment bs nextIdx rem else false
      | .inBlockComment => if b == 0x2A then scanSqlTailBaAux .inBlockSawStar bs nextIdx rem else scanSqlTailBaAux .inBlockComment bs nextIdx rem
      | .inBlockSawStar =>
        if b == 0x2F then scanSqlTailBaAux .normal bs nextIdx rem
        else if b == 0x2A then scanSqlTailBaAux .inBlockSawStar bs nextIdx rem
        else scanSqlTailBaAux .inBlockComment bs nextIdx rem
    else
      match st with
      | .normal | .inSpace | .inLineComment => true
      | _ => false

/-- Tail-recursive SQL tail lexer operating directly on `ByteArray` from byte index `idx`. -/
@[inline] def scanSqlTailBa (st : SqlTailScanState) (bs : ByteArray) (idx : Nat) : Bool :=
  scanSqlTailBaAux st bs idx (bs.size - idx)

end LeanSwe.Sqlite.Raw.Internal
