import LeanSwe.Sqlite.Types

namespace LeanSwe.Sqlite.Model

open LeanSwe.Sqlite
  (SqliteErrorKind SqliteError SqliteRawError
   sqliteOpenReadOnly sqliteOpenReadWrite sqliteOpenCreate sqliteOpenUri sqliteOpenFullMutex
   SqliteValue OpenConfig DbHandle StmtHandle StepResult RawSqliteOpsM)

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

/-- Pure total error-mapping model from `SqliteRawError` to `SqliteError`. -/
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
def attachOpenPathModel (path : String) : SqliteRawError → SqliteRawError
  | .cantOpen none code detail => .cantOpen (some path) code detail
  | other => other

/-- Structural helper for `hasZeroByteBaModel`. -/
def hasZeroByteBaAuxModel (bs : ByteArray) (idx : Nat) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    if h : idx < bs.size then
      if bs[idx] == 0 then true else hasZeroByteBaAuxModel bs (idx + 1) rem
    else
      false

/-- Return `true` iff `bs` contains a zero byte (`0`) at or after `idx`. -/
def hasZeroByteBaModel (bs : ByteArray) (idx : Nat) : Bool :=
  hasZeroByteBaAuxModel bs idx (bs.size - idx)

/-- Compute the `sqlite3_open_v2` bitmask (`SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_URI | ...`) for `cfg`. -/
def computeOpenFlagsModel (cfg : OpenConfig) : UInt32 :=
  let base := sqliteOpenFullMutex ||| sqliteOpenUri
  if cfg.readOnly then
    base ||| sqliteOpenReadOnly
  else if cfg.createIfMissing then
    base ||| sqliteOpenReadWrite ||| sqliteOpenCreate
  else
    base ||| sqliteOpenReadWrite

/-- Decode one ASCII hexadecimal digit byte into `0..15`, or `none` if non-hex. -/
def hexByteValModel? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then
    some (b - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then
    some (b - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then
    some (b - 0x61 + 10)
  else
    none

/-- DFA state for decoding `%HH` percent-escapes in a SQLite URI segment. -/
inductive UriDecodeStateModel where
  /-- Outside any `%HH` escape sequence. -/
  | normal
  /-- Immediately after seeing `'%'` (`0x25`). -/
  | sawPct
  /-- After seeing `'%'` followed by valid hex byte `hiByte` with nibble value `hiVal`. -/
  | sawPctHex (hiByte : UInt8) (hiVal : UInt8)
  deriving Repr, BEq, DecidableEq

/-- UTF-8 byte sequence for `":memory:"`. -/
def colonMemoryColonBytesModel : List UInt8 :=
  [0x3A, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x3A]

/-- UTF-8 byte sequence for `"mode"`. -/
def modeKeyBytesModel : List UInt8 :=
  [0x6D, 0x6F, 0x64, 0x65]

/-- UTF-8 byte sequence for `"memory"`. -/
def memoryModeBytesModel : List UInt8 :=
  [0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]

/-- UTF-8 byte sequence for `"ro"`. -/
def roModeBytesModel : List UInt8 :=
  [0x72, 0x6F]

/-- Advance streaming pattern matcher on one decoded URI byte. -/
def feedUriMatchByteModel (rem? : Option (List UInt8)) (b : UInt8) : Option (List UInt8) :=
  match rem? with
  | some (p :: ps) => if b == p then some ps else none
  | _ => none

/-- Structural helper matching `%HH`-decoded bytes of `bs[idx ..< stop]` against `rem?`. -/
def decodeUriMatchBaAuxModel (bs : ByteArray) (stop : Nat) :
    UriDecodeStateModel → Option (List UInt8) → Nat → Nat → Bool
  | .normal, rem?, _, 0 => rem? == some []
  | .sawPct, rem?, _, 0 => feedUriMatchByteModel rem? 0x25 == some []
  | .sawPctHex hiByte _, rem?, _, 0 =>
    feedUriMatchByteModel (feedUriMatchByteModel rem? 0x25) hiByte == some []
  | st, rem?, idx, fuel + 1 =>
    if h : idx < stop ∧ idx < bs.size then
      let b := bs[idx]
      match st with
      | .normal =>
        if b == 0x25 then
          decodeUriMatchBaAuxModel bs stop .sawPct rem? (idx + 1) fuel
        else
          decodeUriMatchBaAuxModel bs stop .normal (feedUriMatchByteModel rem? b) (idx + 1) fuel
      | .sawPct =>
        match hexByteValModel? b with
        | some v1 => decodeUriMatchBaAuxModel bs stop (.sawPctHex b v1) rem? (idx + 1) fuel
        | none =>
          if b == 0x25 then
            decodeUriMatchBaAuxModel bs stop .sawPct (feedUriMatchByteModel rem? 0x25) (idx + 1) fuel
          else
            decodeUriMatchBaAuxModel bs stop .normal
              (feedUriMatchByteModel (feedUriMatchByteModel rem? 0x25) b) (idx + 1) fuel
      | .sawPctHex hiByte v1 =>
        match hexByteValModel? b with
        | some v2 =>
          let octet : UInt8 := (v1 <<< 4) ||| v2
          if octet == 0 then
            rem? == some []
          else
            decodeUriMatchBaAuxModel bs stop .normal (feedUriMatchByteModel rem? octet) (idx + 1) fuel
        | none =>
          if b == 0x25 then
            decodeUriMatchBaAuxModel bs stop .sawPct
              (feedUriMatchByteModel (feedUriMatchByteModel rem? 0x25) hiByte) (idx + 1) fuel
          else
            decodeUriMatchBaAuxModel bs stop .normal
              (feedUriMatchByteModel (feedUriMatchByteModel (feedUriMatchByteModel rem? 0x25) hiByte) b)
              (idx + 1) fuel
    else
      match st with
      | .normal => rem? == some []
      | .sawPct => feedUriMatchByteModel rem? 0x25 == some []
      | .sawPctHex hiByte _ =>
        feedUriMatchByteModel (feedUriMatchByteModel rem? 0x25) hiByte == some []

/-- Return `true` iff `%HH`-decoded `bs[start ..< stop]` equals `pat`. -/
def decodeUriMatchBaModel (bs : ByteArray) (start stop : Nat) (pat : List UInt8) : Bool :=
  decodeUriMatchBaAuxModel bs stop .normal (some pat) start (stop - start)

/-- Return the first index `i ∈ [idx, stop)` with `bs[i] == delim`, or `stop` if absent. -/
def findByteBeforeAuxModel (bs : ByteArray) (delim : UInt8) (stop : Nat) (idx : Nat) : Nat → Nat
  | 0 => stop
  | fuel + 1 =>
    if h : idx < stop ∧ idx < bs.size then
      if bs[idx] == delim then idx else findByteBeforeAuxModel bs delim stop (idx + 1) fuel
    else
      stop

/-- Return the first index `i ∈ [idx, stop)` with `bs[i] == delim`, or `stop` if absent. -/
def findByteBeforeModel (bs : ByteArray) (delim : UInt8) (idx stop : Nat) : Nat :=
  findByteBeforeAuxModel bs delim stop idx (stop - idx)

/-- Advance past `"//..."` authority bytes up to `'/'` (`0x2F`) or `stop`. -/
def stripAuthorityIdxModel (bs : ByteArray) (start stop : Nat) : Nat :=
  if h : start + 1 < stop ∧ start + 1 < bs.size then
    if bs[start] == 0x2F && bs[start + 1] == 0x2F then
      findByteBeforeModel bs 0x2F (start + 2) stop
    else
      start
  else
    start

/-- Check exact equality of `bs` with `":memory:"`. -/
def isExactColonMemoryBaModel (bs : ByteArray) : Bool :=
  if h : bs.size == 8 then
    let _ : 7 < bs.size := by simp only [beq_iff_eq] at h; omega
    bs[0] == 0x3A && bs[1] == 0x6D && bs[2] == 0x65 && bs[3] == 0x6D &&
      bs[4] == 0x6F && bs[5] == 0x72 && bs[6] == 0x79 && bs[7] == 0x3A
  else
    false

/-- Check `"file:"` prefix on `bs`. -/
def hasFileSchemeBaModel (bs : ByteArray) : Bool :=
  if h : 4 < bs.size then
    bs[0] == 0x66 && bs[1] == 0x69 && bs[2] == 0x6C && bs[3] == 0x65 && bs[4] == 0x3A
  else
    false

/-- Scan `&`-separated query segments in `bs[idx ..< stop]` tracking `(lastModeIsMemory, lastModeIsRo)`. -/
def extractLastUriModeFlagsBaAuxModel (bs : ByteArray) (stop : Nat) (cur : Bool × Bool) (idx : Nat) :
    Nat → Bool × Bool
  | 0 => cur
  | fuel + 1 =>
    let segStop := findByteBeforeModel bs 0x26 idx stop
    let eqIdx := findByteBeforeModel bs 0x3D idx segStop
    let next :=
      if decodeUriMatchBaModel bs idx eqIdx modeKeyBytesModel then
        if eqIdx < segStop then
          let valStart := eqIdx + 1
          (decodeUriMatchBaModel bs valStart segStop memoryModeBytesModel,
           decodeUriMatchBaModel bs valStart segStop roModeBytesModel)
        else
          (false, false)
      else
        cur
    if segStop < stop then
      extractLastUriModeFlagsBaAuxModel bs stop next (segStop + 1) fuel
    else
      next

/-- Classify a UTF-8 path/URI `ByteArray` into `(isMemoryTarget, isUriReadOnly)`. -/
def classifyPathBytesBaModel (bs : ByteArray) : Bool × Bool :=
  if isExactColonMemoryBaModel bs then
    (true, false)
  else if !hasFileSchemeBaModel bs then
    (false, false)
  else
    let fragStop := findByteBeforeModel bs 0x23 5 bs.size
    let pathStart := stripAuthorityIdxModel bs 5 fragStop
    let qIdx := findByteBeforeModel bs 0x3F pathStart fragStop
    let isMemPath := decodeUriMatchBaModel bs pathStart qIdx colonMemoryColonBytesModel
    let (isMemMode, isRoMode) :=
      if qIdx < fragStop then
        extractLastUriModeFlagsBaAuxModel bs fragStop (false, false) (qIdx + 1)
          (fragStop - (qIdx + 1) + 1)
      else
        (false, false)
    (isMemPath || isMemMode, isRoMode)

/-- Pure model of whether `openDb` enables `PRAGMA journal_mode = WAL;` for `(path, cfg)`. -/
def shouldEnableWalModel (path : String) (cfg : OpenConfig) : Bool :=
  if cfg.readOnly || !cfg.walMode then
    false
  else
    let (isMem, isRo) := classifyPathBytesBaModel path.toUTF8
    !isMem && !isRo

/-- Return `true` iff `b` is SQLite ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\f'`, `'\r'`). -/
def isSqlAsciiSpaceModel (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D

/-- DFA state for scanning unconsumed SQL tail bytes after `sqlite3_prepare_v2`. -/
inductive SqlTailScanStateModel where
  /-- Outside any SQL comment or whitespace run. -/
  | normal
  /-- Inside an ASCII SQL whitespace run (`CC_SPACE`). -/
  | inSpace
  /-- Saw a single `'-'` (`0x2D`). -/
  | sawDash
  /-- Inside a `--` SQL line comment. -/
  | inLineComment
  /-- Saw a single `'/'` (`0x2F`). -/
  | sawSlash
  /-- Inside a `/* ... */` block comment. -/
  | inBlockComment
  /-- Inside a `/* ... */` block comment immediately after seeing `'*'` (`0x2A`). -/
  | inBlockSawStar
  /-- Saw leading UTF-8 BOM byte `0xEF`. -/
  | sawBom1
  /-- Saw UTF-8 BOM prefix `0xEF 0xBB`. -/
  | sawBom2
  deriving Repr, BEq, DecidableEq

/-- Structural tail-recursive SQL tail lexer helper on `ByteArray`. -/
def scanSqlTailBaAuxModel (st : SqlTailScanStateModel) (bs : ByteArray) (idx : Nat) : Nat → Bool
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
        if isSqlAsciiSpaceModel b then scanSqlTailBaAuxModel .inSpace bs nextIdx rem
        else if b == 0xEF then scanSqlTailBaAuxModel .sawBom1 bs nextIdx rem
        else if b == 0x2D then scanSqlTailBaAuxModel .sawDash bs nextIdx rem
        else if b == 0x2F then scanSqlTailBaAuxModel .sawSlash bs nextIdx rem
        else false
      | .inSpace =>
        if isSqlAsciiSpaceModel b || b == 0x0B then scanSqlTailBaAuxModel .inSpace bs nextIdx rem
        else if b == 0xEF then scanSqlTailBaAuxModel .sawBom1 bs nextIdx rem
        else if b == 0x2D then scanSqlTailBaAuxModel .sawDash bs nextIdx rem
        else if b == 0x2F then scanSqlTailBaAuxModel .sawSlash bs nextIdx rem
        else false
      | .sawBom1 => if b == 0xBB then scanSqlTailBaAuxModel .sawBom2 bs nextIdx rem else false
      | .sawBom2 => if b == 0xBF then scanSqlTailBaAuxModel .normal bs nextIdx rem else false
      | .sawDash => if b == 0x2D then scanSqlTailBaAuxModel .inLineComment bs nextIdx rem else false
      | .inLineComment =>
        if b == 0x0A then scanSqlTailBaAuxModel .inSpace bs nextIdx rem
        else scanSqlTailBaAuxModel .inLineComment bs nextIdx rem
      | .sawSlash => if b == 0x2A then scanSqlTailBaAuxModel .inBlockComment bs nextIdx rem else false
      | .inBlockComment =>
        if b == 0x2A then scanSqlTailBaAuxModel .inBlockSawStar bs nextIdx rem
        else scanSqlTailBaAuxModel .inBlockComment bs nextIdx rem
      | .inBlockSawStar =>
        if b == 0x2F then scanSqlTailBaAuxModel .normal bs nextIdx rem
        else if b == 0x2A then scanSqlTailBaAuxModel .inBlockSawStar bs nextIdx rem
        else scanSqlTailBaAuxModel .inBlockComment bs nextIdx rem
    else
      match st with
      | .normal | .inSpace | .inLineComment => true
      | _ => false

/-- Tail-recursive SQL tail lexer operating on `ByteArray` from byte index `idx`. -/
def scanSqlTailBaModel (st : SqlTailScanStateModel) (bs : ByteArray) (idx : Nat) : Bool :=
  scanSqlTailBaAuxModel st bs idx (bs.size - idx)


/-- Request sum representing single-step `RawSqliteOpsM` boundary transitions. -/
inductive RawStepReq where
  /-- Normalize a raw `SqliteRawError` into `SqliteError`. -/
  | mapRawError (err : SqliteRawError)
  /-- Open a connection at `path` with `cfg`. -/
  | openDb (path : String) (cfg : OpenConfig)
  /-- Close an existing connection handle. -/
  | closeDb (db : DbHandle)
  /-- Prepare one SQL statement on `db`. -/
  | prepare (db : DbHandle) (sql : String)
  /-- Bind typed parameters to a prepared statement. -/
  | bind (stmt : StmtHandle) (params : Array SqliteValue)
  /-- Step a prepared statement once. -/
  | step (stmt : StmtHandle)
  /-- Finalize and destroy a prepared statement handle. -/
  | finalize (stmt : StmtHandle)
  /-- Read the active database handle count. -/
  | activeDbCount
  /-- Read the active prepared statement handle count. -/
  | activeStmtCount

/-- Output sum for single-step `RawSqliteOpsM` boundary transitions. -/
inductive RawStepOut where
  /-- Result of `RawSqliteOpsM.mapRawError`. -/
  | mapRawError (err : SqliteError)
  /-- Result of `RawSqliteOpsM.openDb`. -/
  | openDb (res : Except SqliteError DbHandle)
  /-- Result of `RawSqliteOpsM.closeDb`. -/
  | closeDb (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.prepare`. -/
  | prepare (res : Except SqliteError StmtHandle)
  /-- Result of `RawSqliteOpsM.bind`. -/
  | bind (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.step`. -/
  | step (res : Except SqliteError StepResult)
  /-- Result of `RawSqliteOpsM.finalize`. -/
  | finalize (res : Except SqliteError Unit)
  /-- Result of `RawSqliteOpsM.activeDbCount`. -/
  | activeDbCount (n : Nat)
  /-- Result of `RawSqliteOpsM.activeStmtCount`. -/
  | activeStmtCount (n : Nat)

/-- Execute one `RawStepReq` against an arbitrary `RawSqliteOpsM (StateM W)`. -/
def execRawStep {W : Type} (ops : RawSqliteOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .mapRawError err => pure (.mapRawError (ops.mapRawError err))
  | .openDb path cfg => .openDb <$> ops.openDb path cfg
  | .closeDb db => .closeDb <$> ops.closeDb db
  | .prepare db sql => .prepare <$> ops.prepare db sql
  | .bind stmt params => .bind <$> ops.bind stmt params
  | .step stmt => .step <$> ops.step stmt
  | .finalize stmt => .finalize <$> ops.finalize stmt
  | .activeDbCount => .activeDbCount <$> ops.activeDbCount
  | .activeStmtCount => .activeStmtCount <$> ops.activeStmtCount

end LeanSwe.Sqlite.Model
