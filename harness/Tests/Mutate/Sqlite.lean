import Tests.Common
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Raw.RuntimeTests
import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.RuntimeTests

namespace Tests.Mutate.Sqlite

open LeanSwe
open Tests.Common

private structure FakeSqliteCState where
  tbl : Sqlite.Raw.RawHandleTable := {}
  preparedSqls : Array String := #[]
  nextTok : UInt64 := 100

private def runSqliteRawUnitTests : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"Sqlite.Raw unit check failed: {msg}")
  let bytes (s : String) : List UInt8 := s.toUTF8.data.toList
  checkB "hex 0" (Sqlite.Raw.Internal.hexByteVal? 0x30 == some 0)
  checkB "hex 9" (Sqlite.Raw.Internal.hexByteVal? 0x39 == some 9)
  checkB "hex A" (Sqlite.Raw.Internal.hexByteVal? 0x41 == some 10)
  checkB "hex F" (Sqlite.Raw.Internal.hexByteVal? 0x46 == some 15)
  checkB "hex a" (Sqlite.Raw.Internal.hexByteVal? 0x61 == some 10)
  checkB "hex f" (Sqlite.Raw.Internal.hexByteVal? 0x66 == some 15)
  checkB "hex /" (Sqlite.Raw.Internal.hexByteVal? 0x2F == none)
  checkB "hex :" (Sqlite.Raw.Internal.hexByteVal? 0x3A == none)
  checkB "hex G" (Sqlite.Raw.Internal.hexByteVal? 0x47 == none)
  checkB "hex g" (Sqlite.Raw.Internal.hexByteVal? 0x67 == none)
  checkB "uri empty" (Sqlite.Raw.Internal.decodeUriComponent (bytes "") == bytes "")
  checkB "uri plain" (Sqlite.Raw.Internal.decodeUriComponent (bytes "abc") == bytes "abc")
  checkB "uri hex" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%41%6a") == bytes "Aj")
  checkB "uri nul" (Sqlite.Raw.Internal.decodeUriComponent (bytes "a%00b") == bytes "a")
  checkB "uri trail %" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%") == bytes "%")
  checkB "uri %%" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%%41") == bytes "%A")
  checkB "uri %ZZ" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%ZZ") == bytes "%ZZ")
  checkB "uri %4" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4") == bytes "%4")
  checkB "uri %4%41" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4%41") == bytes "%4A")
  checkB "uri %4Z" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4Z") == bytes "%4Z")
  checkB "takeBefore hit" (Sqlite.Raw.Internal.takeBeforeByte 0x23 [1, 0x23, 2] == [1])
  checkB "takeBefore miss" (Sqlite.Raw.Internal.takeBeforeByte 0x23 [1, 2] == [1, 2])
  checkB "splitFirst hit" (Sqlite.Raw.Internal.splitFirstByte 0x3F [1, 0x3F, 2, 0x3F] == ([1], some [2, 0x3F]))
  checkB "splitFirst miss" (Sqlite.Raw.Internal.splitFirstByte 0x3F [1] == ([1], none))
  checkB "splitOn" (Sqlite.Raw.Internal.splitOnByte 0x26 [1, 0x26, 2, 0x26] == [[1], [2], []])
  checkB "stripAuth" (Sqlite.Raw.Internal.stripAuthority (bytes "//localhost/a/b") == bytes "/a/b")
  checkB "stripAuth noslash" (Sqlite.Raw.Internal.stripAuthority (bytes "//localhost") == [])
  checkB "mem :memory:" (Sqlite.Raw.Internal.isMemoryTarget ":memory:" && !Sqlite.Raw.Internal.isUriReadOnly ":memory:")
  checkB "mem plain" (!Sqlite.Raw.Internal.isMemoryTarget "plain.db" && !Sqlite.Raw.Internal.isUriReadOnly "plain.db")
  checkB "mem file::memory:" (Sqlite.Raw.Internal.isMemoryTarget "file::memory:?mode=rwc")
  checkB "mem auth slash" (!Sqlite.Raw.Internal.isMemoryTarget "file://localhost/:memory:#frag")
  checkB "mem frag cuts query" (!Sqlite.Raw.Internal.isMemoryTarget "file:a.db#frag?mode=memory")
  checkB "mem auth+query+frag" (Sqlite.Raw.Internal.isMemoryTarget "file://localhost/a.db?mode=memory#frag")
  checkB "mem mode=memory" (Sqlite.Raw.Internal.isMemoryTarget "file:a.db?mode=memory")
  checkB "mem override ro" (!Sqlite.Raw.Internal.isMemoryTarget "file:a.db?mode=memory&mode=ro" &&
    Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode=memory&mode=ro")
  checkB "ro override rwc" (!Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode=ro&mode=rwc")
  checkB "mode bare" (!Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode")
  checkB "mem %00" (Sqlite.Raw.Internal.isMemoryTarget "file:a.db?x=1&mode=memory%00ro")

  checkB "sql tail ok" (Sqlite.Raw.Internal.isIgnorableSqlTail (bytes "  \t\n-- cmt\n /* a * b */ /* ** */ "))
  checkB "sql tail unclosed" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed "))
  checkB "sql tail slash" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed / "))
  checkB "sql tail star" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed *"))
  checkB "sql tail bom ok" (Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0xBF])
  checkB "sql tail bom space ok" (Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0xBF, 0x20])
  checkB "sql tail bom1 eof" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF])
  checkB "sql tail bom1 bad" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0x00])
  checkB "sql tail bom2 eof" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB])
  checkB "sql tail bom2 bad" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0x00])
  checkB "sql tail normal line cmt" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-- tail\n  "))
  checkB "sql tail normal line cmt eof" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-- tail"))
  checkB "sql tail normal dash" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-"))
  checkB "sql tail normal dash bad" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-x"))
  checkB "sql tail normal blk cmt" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/* ok */"))
  checkB "sql tail normal slash" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/"))
  checkB "sql tail normal slash bad" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/x"))
  checkB "sql tail vt normal" (!Sqlite.Raw.Internal.scanSqlTail .normal [0x0B])
  checkB "sql tail vt inSpace" (Sqlite.Raw.Internal.scanSqlTail .inSpace [0x0B])
  let baBom := ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x2D, 0x2D, 0x63]
  checkB "sql tail ba bom+line" (Sqlite.Raw.Internal.scanSqlTailBa .normal baBom 0)
  checkB "sql tail ba blk" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* x */".toUTF8) 0)
  checkB "sql tail ba blk slash" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* a/b */".toUTF8) 0)
  checkB "sql tail ba blk stars" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* **/".toUTF8) 0)
  checkB "sql tail ba blk unclosed" (!Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* a*x".toUTF8) 0)
  checkB "sql tail ba reject" (!Sqlite.Raw.Internal.scanSqlTailBa .normal ("x".toUTF8) 0)
  checkB "hasZeroByteBa empty" (!Sqlite.Raw.Internal.hasZeroByteBa ByteArray.empty 0)
  checkB "hasZeroByteBa hit0" (Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[0, 1]) 0)
  checkB "hasZeroByteBa hitEnd" (Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2, 0]) 0)
  checkB "hasZeroByteBa miss" (!Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2, 3]) 0)
  let rOverTimeout ← Sqlite.Raw.openDb ":memory:" { busyTimeoutMs := 0x80000000 }
  checkB "raw openDb busy_timeout > max" (match rOverTimeout with | .error e => e.kind == .invalidInput | .ok _ => false)
  let rExactTimeout ← Sqlite.Raw.openDb ":memory:" { busyTimeoutMs := 0x7fffffff, walMode := false, foreignKeys := false }
  match rExactTimeout with
  | .error e => throw (IO.userError s!"Sqlite.Raw exact INT_MAX timeout failed: {repr e}")
  | .ok hExact =>
    let rCloseExact ← Sqlite.Raw.closeDb hExact
    checkB "raw closeDb exact timeout" (rCloseExact == .ok ())
  let rDb ← Sqlite.Raw.openDb ":memory:" { walMode := false, foreignKeys := false }
  match rDb with
  | .error e => throw (IO.userError s!"Sqlite.Raw openDb failed: {repr e}")
  | .ok h =>
    let rStmt ← Sqlite.Raw.prepare h "SELECT X'', ?"
    match rStmt with
    | .error e =>
      let _ ← Sqlite.Raw.closeDb h
      throw (IO.userError s!"Sqlite.Raw prepare failed: {repr e}")
    | .ok sh =>
      let rB ← Sqlite.Raw.bind sh #[.bytes ByteArray.empty]
      checkB "shim bind empty blob" (rB == .ok ())
      let rSt ← Sqlite.Raw.step sh
      checkB "shim empty blob not null" (rSt == .ok (.row #[.bytes ByteArray.empty, .bytes ByteArray.empty]))
      let rBusyClose ← Sqlite.Raw.closeDb h
      checkB "shim close with active stmt" (match rBusyClose with | .error e => e.kind == .busy | .ok _ => false)
      let rBusyDefaultClose ← Sqlite.Raw.defaultOps.closeDb h
      checkB "defaultOps close with active stmt"
        (match rBusyDefaultClose with | .error e => e.kind == .busy | .ok _ => false)
      let rFin1 ← Sqlite.Raw.finalize sh
      checkB "shim finalize ok" (rFin1 == .ok ())
      let rFin2 ← Sqlite.Raw.finalize sh
      checkB "shim double finalize misuse" (match rFin2 with | .error e => e.kind == .misuse | .ok _ => false)
      let rCl1 ← Sqlite.Raw.closeDb h
      checkB "shim close ok" (rCl1 == .ok ())
      let rCl2 ← Sqlite.Raw.defaultOps.closeDb h
      checkB "shim double close misuse" (match rCl2 with | .error e => e.kind == .misuse | .ok _ => false)

  let stmts : List (Sqlite.Raw.StmtHandle × Sqlite.Raw.RawStmtHandle) :=
    [({ id := 1, dbId := 1 }, .mock 10), ({ id := 2, dbId := 2 }, .mock 11)]
  checkB "activeStmt db2" (Sqlite.Raw.Internal.hasActiveStmtForDb 2 stmts)
  checkB "activeStmt db3" (!Sqlite.Raw.Internal.hasActiveStmtForDb 3 stmts)

  let fakeCOps : Sqlite.Raw.CSqliteOpsM (StateM FakeSqliteCState) :=
    { openV2 := fun _ _ => modifyGet fun st => (.ok (.mock st.nextTok), { st with nextTok := st.nextTok + 1 })
      close := fun _ => pure (.ok ())
      extendedResultCodes := fun _ _ => pure (.ok ())
      busyTimeout := fun _ _ => pure (.ok ())
      prepareV2 := fun _ sql => modifyGet fun st =>
        let tok := st.nextTok
        let consumed :=
          if sql == "SELECT 1; SELECT 2" then 9
          else if sql == "OVERCONSUME" then 999
          else sql.toUTF8.size
        (.ok (some (.mock tok), consumed),
         { st with nextTok := tok + 1, preparedSqls := st.preparedSqls.push sql })
      step := fun _ => pure (.ok .done)
      reset := fun _ => pure (.ok ())
      clearBindings := fun _ => pure (.ok ())
      finalize := fun _ => pure (.finalized none)
      bindParamCount := fun _ => pure (.ok 0)
      bindNull := fun _ _ => pure (.ok ())
      bindInt64 := fun _ _ _ => pure (.ok ())
      bindDouble := fun _ _ _ => pure (.ok ())
      bindText := fun _ _ _ => pure (.ok ())
      bindBlob := fun _ _ _ => pure (.ok ())
      columnCount := fun _ => pure (.ok 0)
      columnType := fun _ _ => pure (.ok 5)
      columnInt64 := fun _ _ => pure (.ok 0)
      columnDouble := fun _ _ => pure (.ok 0.0)
      columnTextBytes := fun _ _ => pure (.ok ByteArray.empty)
      columnBlob := fun _ _ => pure (.ok ByteArray.empty)
      modifyTable := fun f => modifyGet fun st =>
        let (res, tbl') := f st.tbl
        (res, { st with tbl := tbl' }) }
  let rawOps := Sqlite.Raw.Internal.mkRawOps fakeCOps
  let errDummy : Sqlite.Raw.SqliteError := { kind := .ioError, message := "dummy" }
  let ((r1, r2, rClose1, rClose2, rClose2b), stEnd) := (do
    let db1 ← rawOps.openDb ":memory:" { foreignKeys := false, walMode := false }
    let db2 ← rawOps.openDb "disk.db" { foreignKeys := true, walMode := true }
    match db1, db2 with
    | .ok h1, .ok h2 =>
      let st2 ← rawOps.prepare h2 "SELECT 1"
      let c1 ← rawOps.closeDb h1
      let c2 ← rawOps.closeDb h2
      match st2 with
      | .ok s2 =>
        let _ ← rawOps.finalize s2
        let c2b ← rawOps.closeDb h2
        pure (Except.ok h1, Except.ok h2, c1, c2, c2b)
      | _ => pure (Except.error errDummy, Except.ok h2, c1, c2, Except.error errDummy)
    | e1, e2 => pure (e1, e2, Except.error errDummy, Except.error errDummy, Except.error errDummy)
    ).run {}
  checkB "mkRawOps open1" (r1 matches .ok _)
  checkB "mkRawOps open2" (r2 matches .ok _)
  checkB "mkRawOps pragmas" (stEnd.preparedSqls == #["PRAGMA foreign_keys = ON;", "PRAGMA journal_mode = WAL;", "SELECT 1"])
  checkB "mkRawOps close1" (rClose1 == .ok ())
  checkB "mkRawOps close2 busy" (match rClose2 with | .error e => e.kind == .busy | .ok _ => false)
  checkB "mkRawOps close2 after finalize" (rClose2b == .ok ())
  checkB "uri ba %%" (Sqlite.Raw.Internal.decodeUriMatchBa "%%41".toUTF8 0 4 (bytes "%A"))
  checkB "uri ba %4%41" (Sqlite.Raw.Internal.decodeUriMatchBa "%4%41".toUTF8 0 5 (bytes "%4A"))
  checkB "uri ba over normal ok" (Sqlite.Raw.Internal.decodeUriMatchBa "a".toUTF8 0 5 (bytes "a"))
  checkB "uri ba over normal no" (!Sqlite.Raw.Internal.decodeUriMatchBa "a".toUTF8 0 5 (bytes "ab"))
  checkB "uri ba over pct ok" (Sqlite.Raw.Internal.decodeUriMatchBa "%".toUTF8 0 5 (bytes "%"))
  checkB "uri ba over pct no" (!Sqlite.Raw.Internal.decodeUriMatchBa "%".toUTF8 0 5 (bytes "%%"))
  checkB "uri ba over pcthex ok" (Sqlite.Raw.Internal.decodeUriMatchBa "%4".toUTF8 0 5 (bytes "%4"))
  checkB "uri ba over pcthex no" (!Sqlite.Raw.Internal.decodeUriMatchBa "%4".toUTF8 0 5 (bytes "%41"))
  checkB "classifyBytes :memory:" (Sqlite.Raw.Internal.classifyPathBytes (bytes ":memory:") == (true, false))
  checkB "classifyBytes plain" (Sqlite.Raw.Internal.classifyPathBytes (bytes "plain.db") == (false, false))
  checkB "classifyBytes file::memory:" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file::memory:") == (true, false))
  checkB "classifyBytes mode=memory" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory") == (true, false))
  checkB "classifyBytes mode=ro" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=ro") == (false, true))
  checkB "classifyBytes mode keep" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory&x=1") == (true, false))
  checkB "classifyBytes mode override ro" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory&mode=ro") == (false, true))
  checkB "classifyBytes mode override rwc" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=ro&mode=rwc") == (false, false))
  checkB "classifyBytes mode bare" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode") == (false, false))
  checkB "hasZeroByte empty" (!Sqlite.Raw.Internal.hasZeroByte [])
  checkB "hasZeroByte hit0" (Sqlite.Raw.Internal.hasZeroByte [0, 1])
  checkB "hasZeroByte hitEnd" (Sqlite.Raw.Internal.hasZeroByte [1, 2, 0])
  checkB "hasZeroByte miss" (!Sqlite.Raw.Internal.hasZeroByte [1, 2, 3])
  checkB "hasZeroByteBa oob" (!Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2]) 5)
  checkB "mapRawError empty cantOpen"
    ((Sqlite.Raw.mapRawError (.cantOpen (some "p") 14 "")).message == "unable to open sqlite database")
  checkB "mapRawError custom cantOpen"
    ((Sqlite.Raw.mapRawError (.cantOpen none 14 "custom")).message == "custom")
  checkB "mapRawError empty busy"
    ((Sqlite.Raw.mapRawError (.busy 5 "")).message == "sqlite database is busy")
  checkB "mapRawError empty constraint"
    ((Sqlite.Raw.mapRawError (.constraint 19 "")).message == "sqlite constraint failed")
  checkB "mapRawError empty misuse"
    ((Sqlite.Raw.mapRawError (.misuse 21 "")).message == "sqlite library misuse")
  checkB "mapRawError empty invalidArg"
    ((Sqlite.Raw.mapRawError (.invalidArgument "")).message == "invalid sqlite argument")
  checkB "mapRawError empty ioFailure"
    ((Sqlite.Raw.mapRawError (.ioFailure 8 "")).message == "sqlite io failure (8)")
  checkB "mapRawError empty codeErr"
    ((Sqlite.Raw.mapRawError (.sqliteCodeError 1 "")).message == "sqlite error (1)")
  checkB "mapRawError empty userErr"
    ((Sqlite.Raw.mapRawError (.userError "")).message == "sqlite error")
  checkB "attachOpenPath none"
    (Sqlite.Raw.Internal.attachOpenPath "x.db" (.cantOpen none 14 "d") == .cantOpen (some "x.db") 14 "d")
  checkB "attachOpenPath some"
    (Sqlite.Raw.Internal.attachOpenPath "x.db" (.cantOpen (some "y.db") 14 "d") == .cantOpen (some "y.db") 14 "d")
  checkB "sql tail ba inSpace vt" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0x0B]) 0)
  checkB "sql tail ba normal vt no" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x0B]) 0)
  checkB "sql tail ba inSpace bom" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0xBB, 0xBF]) 0)
  checkB "sql tail ba inSpace bom1 bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0x00]) 0)
  checkB "sql tail ba inSpace bom2 bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0xBB, 0x00]) 0)
  checkB "sql tail ba inSpace cmt" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0x2F, 0x2A, 0x2A, 0x2F]) 0)
  checkB "sql tail ba inSpace bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal " x".toUTF8 0)
  checkB "sql tail ba over ok" (Sqlite.Raw.Internal.scanSqlTailBaAux .normal " ".toUTF8 0 5)
  checkB "sql tail ba over unclosed" (!Sqlite.Raw.Internal.scanSqlTailBaAux .normal "/*".toUTF8 0 5)
  let (emptyOpenRes, _) := (rawOps.openDb "" {}).run {}
  checkB "mkRawOps empty path" (match emptyOpenRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (nulOpenRes, _) := (rawOps.openDb "a\x00b" {}).run {}
  checkB "mkRawOps nul path" (match nulOpenRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (roCreateRes, _) := (rawOps.openDb ":memory:" { readOnly := true, createIfMissing := true }).run {}
  checkB "mkRawOps ro+create" (match roCreateRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (overToRes, _) := (rawOps.openDb ":memory:" { busyTimeoutMs := 0x80000000 }).run {}
  checkB "mkRawOps over timeout" (match overToRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let ((nulPrepRes, badBindRes, multiPrepRes, overConPrepRes), _) := (do
    let .ok h ← rawOps.openDb ":memory:" { walMode := false, foreignKeys := false }
      | pure (Except.error errDummy, Except.error errDummy, Except.error errDummy, Except.error errDummy)
    let pNul ← rawOps.prepare h "SELECT \x001"
    let pMulti ← rawOps.prepare h "SELECT 1; SELECT 2"
    let pOverCon ← rawOps.prepare h "OVERCONSUME"
    let .ok s0 ← rawOps.prepare h "SELECT 1"
      | pure (pNul, Except.error errDummy, pMulti, pOverCon)
    let bMis ← rawOps.bind s0 #[.int 1]
    let _ ← rawOps.finalize s0
    let _ ← rawOps.closeDb h
    pure (pNul, bMis, pMulti, pOverCon)).run {}
  checkB "mkRawOps prepare NUL" (match nulPrepRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  checkB "mkRawOps bind arity" (match badBindRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  checkB "mkRawOps prepare multi" (match multiPrepRes with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false)
  checkB "mkRawOps prepare overconsume" (match overConPrepRes with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false)
  let rPermUri ← Sqlite.Raw.openDb "file::memory:?mode=rw" { readOnly := true, createIfMissing := false }
  checkB "raw openDb mode=rw ro SQLITE_PERM"
    (match rPermUri with | .error e => e.kind == .ioError && e.sqliteCode == some 3 | .ok _ => false)
  let bigSql := String.pushn "" ' ' (Sqlite.Raw.maxSqlByteLen + 1)
  let (overRes, _) := (do
    let dbRes ← rawOps.openDb ":memory:" { walMode := false, foreignKeys := false }
    match dbRes with
    | .ok h =>
      let pRes ← rawOps.prepare h bigSql
      let _ ← rawOps.closeDb h
      pure pRes
    | .error e => pure (.error e)).run {}
  checkB "mkRawOps prepare > maxSqlByteLen" (match overRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  match ← Sqlite.Raw.openDb ":memory:" { walMode := false, foreignKeys := false } with
  | .error e => throw (IO.userError s!"Sqlite.Raw openDb for bigSql failed: {repr e}")
  | .ok hBig =>
    let defOverRes ← Sqlite.Raw.prepare hBig bigSql
    let _ ← Sqlite.Raw.closeDb hBig
    checkB "defaultOps prepare > maxSqlByteLen" (match defOverRes with | .error e => e.kind == .invalidInput | .ok _ => false)

  let hCloseCnt ← IO.mkRef 0
  let hFinCnt ← IO.mkRef 0
  let hClearCnt ← IO.mkRef 0
  let hResetCnt ← IO.mkRef 0
  let hFailSetup ← IO.mkRef true
  let tblRef ← IO.mkRef ({} : Sqlite.Raw.RawHandleTable)
  let isolatedMockC : Sqlite.Raw.CSqliteOps :=
    { modifyTable := fun f => tblRef.modifyGet f
      openV2 := fun _ _ => pure (.ok (.mock 501))
      close := fun _ => do hCloseCnt.modify (· + 1); pure (.ok ())
      extendedResultCodes := fun _ _ => pure (.ok ())
      busyTimeout := fun _ _ => do
        if ← hFailSetup.get then pure (.error (.busy 5 "setup busy")) else pure (.ok ())
      prepareV2 := fun _ sql =>
        let consumed := if sql == "SELECT 1; SELECT 2" then 9 else sql.toUTF8.size
        pure (.ok (some (.mock 601), consumed))
      step := fun _ => pure (.ok .done)
      reset := fun _ => do hResetCnt.modify (· + 1); pure (.ok ())
      clearBindings := fun _ => do hClearCnt.modify (· + 1); pure (.ok ())
      finalize := fun _ => do hFinCnt.modify (· + 1); pure (.finalized none)
      bindParamCount := fun _ => pure (.ok 1)
      bindNull := fun _ _ => pure (.ok ())
      bindInt64 := fun _ _ _ => pure (.ok ())
      bindDouble := fun _ _ _ => pure (.ok ())
      bindText := fun _ _ _ => pure (.ok ())
      bindBlob := fun _ _ _ => pure (.ok ())
      columnCount := fun _ => pure (.ok 0)
      columnType := fun _ _ => pure (.ok 5)
      columnInt64 := fun _ _ => pure (.ok 0)
      columnDouble := fun _ _ => pure (.ok 0.0)
      columnTextBytes := fun _ _ => pure (.ok ByteArray.empty)
      columnBlob := fun _ _ => pure (.ok ByteArray.empty) }
  let isolatedOps := Sqlite.Raw.Internal.mkRawOps isolatedMockC
  let rSetupErr ← isolatedOps.openDb ":memory:" { walMode := false, foreignKeys := false }
  checkB "mkRawOps setup err closes rawDb"
    ((match rSetupErr with | .error e => e.kind == .busy | .ok _ => false) &&
      (← hCloseCnt.get) == 1 && (← isolatedOps.activeDbCount) == 0)
  hFailSetup.set false
  match ← isolatedOps.openDb ":memory:" { walMode := false, foreignKeys := false } with
  | .error e => throw (IO.userError s!"mkRawOps openDb failed: {repr e}")
  | .ok hIsoDb =>
    let rMulti ← isolatedOps.prepare hIsoDb "SELECT 1; SELECT 2"
    checkB "mkRawOps multi-stmt finalizes rawStmt"
      ((match rMulti with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false) &&
        (← hFinCnt.get) == 1 && (← isolatedOps.activeStmtCount) == 0)
    match ← isolatedOps.prepare hIsoDb "SELECT ?" with
    | .error e =>
      let _ ← isolatedOps.closeDb hIsoDb
      throw (IO.userError s!"mkRawOps prepare SELECT ? failed: {repr e}")
    | .ok hIsoSt =>
      let rBindIso ← isolatedOps.bind hIsoSt #[.int 7]
      checkB "mkRawOps bind resets and clears bindings"
        (rBindIso == .ok () && (← hResetCnt.get) == 1 && (← hClearCnt.get) == 1)
      let rFinIso ← isolatedOps.finalize hIsoSt
      let rClIso ← isolatedOps.closeDb hIsoDb
      checkB "mkRawOps finalize+close clean"
        (rFinIso == .ok () && rClIso == .ok () &&
          (← isolatedOps.activeDbCount) == 0 && (← isolatedOps.activeStmtCount) == 0)

private def runSqliteUnitTests : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"Sqlite unit check failed: {msg}")
  let eInv := Sqlite.mapRawError (.invalidArgument "bad")
  checkB "mapRawError invalid" (eInv.kind == .invalidInput && !eInv.message.isEmpty)
  let vBad := Sqlite.validateConfig { readOnly := true, createIfMissing := true }
  checkB "validateConfig ro+create" (match vBad with | .error e => e.kind == .invalidInput | .ok _ => false)
  let dbBad ← Sqlite.withDb "" {} (fun _ => pure (.ok ()))
  checkB "withDb empty path" (match dbBad with | .error e => e.kind == .invalidInput | .ok _ => false)
  let rTxRbFail ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db =>
    Sqlite.withTransaction (α := Unit) db fun h => do
      let _ ← Sqlite.exec h "COMMIT"
      pure (.error { kind := Sqlite.Raw.SqliteErrorKind.busy, message := "body fail" })
  checkB "withTransaction preserves body fail over rollback fail"
    (match rTxRbFail with
     | .error e => e.kind == Sqlite.Raw.SqliteErrorKind.busy && e.message == "body fail"
     | .ok _ => false)
  let rTxComRbFail ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db =>
    Sqlite.withTransaction (α := Unit) db fun h => do
      let _ ← Sqlite.exec h "COMMIT"
      pure (.ok ())
  checkB "withTransaction propagates commit->rollback fail"
    (match rTxComRbFail with
     | .error e => e.kind == Sqlite.Raw.SqliteErrorKind.ioError && e.sqliteCode == some 1
     | .ok _ => false)
  let rQuery ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db => do
    match ← Sqlite.exec db "CREATE TABLE t(id INTEGER PRIMARY KEY, v INT)" with
    | .error e => pure (.error e)
    | .ok () =>
      match ← Sqlite.exec db "INSERT INTO t(id, v) VALUES (1, ?)" #[.int 42] with
      | .error e => pure (.error e)
      | .ok () =>
        match ← Sqlite.query db "SELECT v FROM t ORDER BY id ASC" with
        | .error e => pure (.error e)
        | .ok rows =>
          match ← Sqlite.queryOne db "SELECT v FROM t WHERE id = ?" #[.int 1] with
          | .error e => pure (.error e)
          | .ok one => pure (.ok (rows, one))
  checkB "query+queryOne" (match rQuery with | .ok (rs, some r) => rs == #[#[.int 42]] && r == #[.int 42] | _ => false)
  let nDb ← Sqlite.activeDbCount
  let nSt ← Sqlite.activeStmtCount
  checkB "no leaked handles" (nDb == 0 && nSt == 0)

/-- Mutation test suite for `LeanSwe.Sqlite.Raw`. -/
def sqliteRawSuite : MutateSuite :=
  { name := "Sqlite.Raw"
    runBase := do Sqlite.Raw.RuntimeTests.runAll; return none
    runExtra := runSqliteRawUnitTests }

/-- Mutation test suite for `LeanSwe.Sqlite`. -/
def sqliteSuite : MutateSuite :=
  { name := "Sqlite"
    runBase := do Sqlite.RuntimeTests.runAll; return none
    runExtra := runSqliteUnitTests }

end Tests.Mutate.Sqlite
