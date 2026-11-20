import Fuzz.Common.Rng
import Fuzz.Sqlite.Trace

namespace Fuzz.Sqlite.Gen

open Fuzz.Common
open Fuzz.Sqlite
open LeanSwe.Sqlite

private def chooseFrom {α : Type} [Inhabited α] (xs : Array α) (r : Rng) : α × Rng :=
  if xs.isEmpty then (default, r)
  else
    let (idx, r') := r.nextNat xs.size
    (xs.getD idx default, r')

private def edgeInts : Array Int64 :=
  #[ 0, 1, -1, 2, -2, 7, 10, 42, 99
   , Int64.minValue
   , Int64.maxValue
   , Int64.maxValue - 1
   , Int64.minValue + 1
   , (1 : Int64) <<< 47 - 1
   , -(((1 : Int64) <<< 47) - 1)
   , (1 : Int64) <<< 47
   , -((1 : Int64) <<< 47)
   , (1 : Int64) <<< 51
   , -((1 : Int64) <<< 51)
   , (1 : Int64) <<< 53
   , -((1 : Int64) <<< 53)
   , ((1 : Int64) <<< 53) + 1
   , -(((1 : Int64) <<< 53) + 1) ]

private def edgeFloats : Array Float :=
  #[ Float.ofBits 0
   , Float.ofBits 0x8000000000000000
   , Float.ofBits 0x7ff8000000000000
   , Float.ofBits 0xfff8000000000042
   , Float.ofBits 0x7ff0000000000000
   , Float.ofBits 0xfff0000000000000
   , Float.ofBits 1
   , Float.ofBits 0x8000000000000001
   , Float.ofBits 0x7fefffffffffffff
   , Float.ofBits 0x01a9feab2284814a
   , Float.ofBits 0x01a9feab2284814b
   , Float.ofBits 0xb66de7068330430d
   , 9223372036854775808.0
   , -9223372036854775808.0
   , 9223372036854774784.0
   , -9223372036854774784.0
   , 3500000000000000.2500001
   , 1.5
   , -1.5
   , 1e20
   , -1e-20 ]

private def edgeStrings : Array String :=
  #[ ""
   , "a"
   , "live"
   , "NULL"
   , "0"
   , "-1"
   , " 123 "
   , "48.00"
   , "1e20"
   , "9223372036854775807"
   , "9223372036854775808"
   , "9223372036854775808.0"
   , "-9223372036854775808"
   , "-9223372036854775808.0"
   , "-9223372036854775809"
   , "'; DROP TABLE t0; --"
   , "héllo 🌍"
   , "abc\x00def"
   , "\x00"
   , "123\x0b"
   , "\x0b45.5"
   , "\x0b"
   , "4503599627370496\x00abc"
   , "-9223372036854775808\x00x"
   , "1.213e-300"
   , "1213e-303"
   , "-1.63680654791682e-46"
   , "1.823e-292"
   , "9.11e-290"
   , "1.899e-280" ]

private def edgeBlobs : Array ByteArray :=
  #[ ByteArray.empty
   , ByteArray.mk #[0]
   , ByteArray.mk #[0, 1, 2, 3]
   , ByteArray.mk #[0xFF, 0xFE, 0x80]
   , ByteArray.mk #[0x41, 0x00, 0x42] ]

/-- Generate a `SqliteValue` biased toward edge integers, floats, strings, and blobs. -/
def genValue (r : Rng) : SqliteValue × Rng :=
  let (tag, r1) := r.nextNat 100
  if tag < 15 then
    (.null, r1)
  else if tag < 42 then
    let (useEdge, r2) := r1.chance 3 4
    if useEdge then
      let (iv, r3) := chooseFrom edgeInts r2
      (.int iv, r3)
    else
      let (u, r3) := r2.nextU64
      (.int (Int64.ofInt (Int.ofNat u.toNat - Int.ofNat (1 <<< 63))), r3)
  else if tag < 65 then
    let (useEdge, r2) := r1.chance 4 5
    if useEdge then
      let (fv, r3) := chooseFrom edgeFloats r2
      (.real fv, r3)
    else
      let (u, r3) := r2.nextU64
      (.real (Float.ofBits u), r3)
  else if tag < 85 then
    let (sv, r2) := chooseFrom edgeStrings r1
    (.text sv, r2)
  else
    let (bv, r2) := chooseFrom edgeBlobs r1
    (.bytes bv, r2)

/-- Generate an `Array SqliteValue` of length `n`. -/
def genValues (n : Nat) (r : Rng) : Array SqliteValue × Rng :=
  Id.run do
    let mut cur := r
    let mut out := Array.mkEmpty n
    for _ in List.range n do
      let (v, r') := genValue cur
      cur := r'
      out := out.push v
    return (out, cur)

/-- Generate an `OpenConfig` across all 16 boolean combinations and boundary timeouts. -/
def genOpenConfig (r : Rng) : OpenConfig × Rng :=
  let (bits, r1) := r.nextNat 16
  let ro := (bits &&& 1) != 0
  let cr := (bits &&& 2) != 0
  let wal := (bits &&& 4) != 0
  let fk := (bits &&& 8) != 0
  let (tChoice, r2) := r1.nextNat 10
  let (timeout, r3) :=
    if tChoice < 3 then (0, r2)
    else if tChoice < 5 then (1, r2)
    else if tChoice < 7 then (5, r2)
    else if tChoice == 7 then (maxBusyTimeoutMs, r2)
    else if tChoice == 8 then (maxBusyTimeoutMs + 1, r2)
    else
      let (extra, r2') := r2.nextNat 1000
      (maxBusyTimeoutMs + extra, r2')
  ({ readOnly := ro, createIfMissing := cr, walMode := wal, busyTimeoutMs := timeout, foreignKeys := fk }, r3)

/-- Generate a `OpenConfig` biased toward valid combinations with short busy timeouts for multi-connection fuzzing. -/
def genValidOpenConfig (r : Rng) : OpenConfig × Rng :=
  let (mode, r1) := r.nextNat 8
  let (ro, cr) :=
    if mode < 2 then (true, false)
    else if mode < 5 then (false, true)
    else (false, false)
  let (wal, r2) := r1.nextBool
  let (fk, r3) := r2.nextBool
  let (tIdx, r4) := r3.nextNat 4
  let timeout := if tIdx == 0 then 0 else if tIdx == 1 then 1 else if tIdx == 2 then 2 else 5
  ({ readOnly := ro, createIfMissing := cr, walMode := wal, busyTimeoutMs := timeout, foreignKeys := fk }, r4)

private def genSessionOpenConfig (r : Rng) : OpenConfig × Rng :=
  let (bits, r1) := r.nextNat 16
  let ro := (bits &&& 1) != 0
  let cr := (bits &&& 2) != 0
  let wal := (bits &&& 4) != 0
  let fk := (bits &&& 8) != 0
  let (tChoice, r2) := r1.nextNat 10
  let (timeout, r3) :=
    if tChoice < 4 then (0, r2)
    else if tChoice < 7 then (1, r2)
    else if tChoice < 8 then (5, r2)
    else if tChoice == 8 then (maxBusyTimeoutMs + 1, r2)
    else
      let (extra, r2') := r2.nextNat 1000
      (maxBusyTimeoutMs + extra, r2')
  ({ readOnly := ro, createIfMissing := cr, walMode := wal, busyTimeoutMs := timeout, foreignKeys := fk }, r3)

private def mkRepeated (n : Nat) (s : String) : String :=
  String.join (List.replicate n s)

private def mkManyColsSql (kind : Nat) : String :=
  let cols := (List.range 2001).map fun i => s!"c{i}"
  match kind with
  | 0 => "CREATE TABLE t_wide(" ++ String.intercalate "," (cols.map fun c => s!"{c} INT") ++ ")"
  | 1 => "SELECT " ++ String.intercalate "," cols ++ " FROM t0"
  | _ => "SELECT id FROM t0 ORDER BY " ++ String.intercalate "," cols

private def genRawInvalidPath (r : Rng) : String × Rng :=
  let candidates : Array String :=
    #[ ""
     , "a\x00b"
     , "file::memory:?cache=shared"
     , "file::memory:?mode=memory"
     , "file::memory:?mode=ro"
     , "file::memory:?mode=rw"
     , "file::memory:?mode=rwc"
     , "file::memory:?mode=ro&mode=rw"
     , "file::memory:?mode=memory&mode=rwc"
     , "file:"
     , "file://"
     , "file://#frag"
     , "file://localhost"
     , "file://localhost#frag"
     , "file:priv_mem?vfs=memdb&immutable=1"
     , "file:?mode=ro"
     , "file:?mode=rw"
     , "file:?mode=rwc"
     , "file:/no_such_dir/missing?mode=rwc"
     , "file:/no_such_dir/m.db?vfs=memdb"
     , "file:/no_such_dir/missing"
     , "file:/no_such_dir/x.db?cache=bad"
     , "file::memory:?vfs=bad"
     , "file::memory:?mode=bad"
     , "file://localhost/no_such_dir/:memory:"
     , "file:/no_such_dir/x.db?mode=ro"
     , "/"
     , "//"
     , "/."
     , "/.."
     , "."
     , "./"
     , ".."
     , "../"
     , "/no_such_dir/" ++ String.ofList (List.replicate 256 'a') ++ ".sqlite"
     , String.ofList (List.replicate 551 'a') ]
  chooseFrom candidates r

private def epSuffixCandidates : Array String :=
  #[ "/."
   , "/.."
   , "/./db0.sqlite"
   , "//db0.sqlite"
   , "/db0.sqlite/"
   , "/new_trailing.sqlite/"
   , "/ro0444.sqlite/"
   , "/corrupt.sqlite/"
   , "/subdir/."
   , "/subdir/.."
   , "/subdir/"
   , "/subdir/../db0.sqlite"
   , "/db0.sqlite/../db1.sqlite"
   , "/db0.sqlite/sub/../../db1.sqlite"
   , "/corrupt.sqlite/sub/../../db0.sqlite"
   , "/sym_45.sqlite"
   , mkRepeated 300 "/." ++ "/db0.sqlite"
   , "/" ++ String.ofList (List.replicate 520 'p') ++ ".sqlite" ]

/-- Generate a `TargetSpec` mixing valid slots, normalized relative paths, error paths, and raw strings. -/
def genTargetSpec (r : Rng) : TargetSpec × Rng :=
  let (tag, r1) := r.nextNat 100
  if tag < 22 then (.db0, r1)
  else if tag < 38 then (.db1, r1)
  else if tag < 49 then (.memory, r1)
  else if tag < 55 then (.missing, r1)
  else if tag < 60 then (.missingParent, r1)
  else if tag < 65 then (.subdir, r1)
  else if tag < 71 then (.ro0444, r1)
  else if tag < 75 then (.walRo0444, r1)
  else if tag < 80 then (.corrupt, r1)
  else if tag < 88 then
    let (sTag, r2) := r1.nextNat 6
    let sTgt :=
      if sTag == 0 then TargetSpec.symDeep
      else if sTag == 1 then TargetSpec.sym45
      else if sTag == 2 then TargetSpec.symLoop
      else if sTag == 3 then TargetSpec.symRelDb0
      else if sTag == 4 then TargetSpec.symDirDb0
      else TargetSpec.symDangling
    (sTgt, r2)
  else if tag < 94 then
    let (pKind, r2) := r1.nextNat 3
    if pKind == 0 then
      let (bLen, r3) := chooseFrom #[504, 505, 508, 511, 512] r2
      (.exactPathBytes bLen, r3)
    else if pKind == 1 then
      let (iLen, r3) := chooseFrom #[505, 511, 512, 513] r2
      (.intermDotDotBytes iLen, r3)
    else
      let (s, r3) := chooseFrom epSuffixCandidates r2
      (.epSuffix s, r3)
  else
    let (p, r2) := genRawInvalidPath r1
    (.raw p, r2)

/-- Generate a `SqliteRawError` spanning all 8 constructors and empty/non-empty details. -/
def genRawError (r : Rng) : SqliteRawError × Rng :=
  let (tag, r1) := r.nextNat 8
  let (detail, r2) := chooseFrom #["", "locked", "disk error", "bad arg"] r1
  let (code, r3) := chooseFrom #[0, 1, 5, 6, 8, 10, 11, 13, 14, 19, 21, 25, 26, 261, 1555, 2067, 787] r2
  let err :=
    match tag with
    | 0 => .cantOpen (if code % 2 == 0 then some "x.db" else none) code detail
    | 1 => .busy code detail
    | 2 => .constraint code detail
    | 3 => .misuse code detail
    | 4 => .invalidArgument detail
    | 5 => .ioFailure code detail
    | 6 => .sqliteCodeError code detail
    | _ => .userError detail
  (err, r3)

private def tableNames : Array String := #["t0", "t1", "t2", "T0"]

private def colSetsCreate : Array String :=
  #[ "CREATE TABLE t0(id INTEGER PRIMARY KEY, u INT UNIQUE, v REAL, tag TEXT, bin BLOB, anycol ANY) STRICT"
   , "CREATE TABLE IF NOT EXISTS t0(id INTEGER PRIMARY KEY AUTOINCREMENT, u INT NOT NULL UNIQUE, v REAL, tag TEXT) STRICT"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, pid INT REFERENCES t0(id), u INT UNIQUE, x INT, tag TEXT)"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES t0(id), tag TEXT) STRICT"
   , "CREATE TABLE t2(id INT PRIMARY KEY, pid INT REFERENCES t2(id), a TEXT UNIQUE, b BLOB)"
   , "CREATE TABLE t2(id INTEGER PRIMARY KEY, x INT, y REAL, z TEXT, w BLOB)"
   , "CREATE TABLE t0(id INT NOT NULL UNIQUE, x INTEGER)"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, badref INT REFERENCES no_tbl(id))"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, badcol INT REFERENCES t0(x))"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, dup INT, dup TEXT)"
   , "CREATE TABLE t1(id INTEGER PRIMARY KEY, a INT, anyc ANY) STRICT"
   , "CREATE TABLE t_plain(a INT, tag TEXT) STRICT"
   , "CREATE TABLE fp_r(id INTEGER PRIMARY KEY, r REAL UNIQUE)"
   , "CREATE TABLE fc_r(id INTEGER PRIMARY KEY, pid INT REFERENCES fp_r(r))"
   , "CREATE TABLE t_sref(id INT UNIQUE, pid TEXT REFERENCES t_sref(id), v INT)"
   , "CREATE TABLE fp_mix(id INTEGER PRIMARY KEY, bad INT)"
   , "CREATE TABLE fc_ok(id INTEGER PRIMARY KEY, pid INT REFERENCES fp_mix(id))"
   , "CREATE TABLE fc_bad(id INTEGER PRIMARY KEY, pid INT REFERENCES fp_mix(bad))"
   , "CREATE TABLE t_pk_u(pk INT PRIMARY KEY, u INT UNIQUE)"
   , "CREATE TABLE t_u_pk(u INT UNIQUE, pk INT PRIMARY KEY)"
   , "CREATE TABLE t_tpk(k TEXT PRIMARY KEY, v INT) STRICT"
   , "CREATE TABLE t_bpk(k BLOB PRIMARY KEY, v INT) STRICT"
   , "CREATE TABLE t_auto_str(id INTEGER PRIMARY KEY AUTOINCREMENT, v INT) STRICT"
   , "CREATE TABLE t_fk_txt(id INTEGER PRIMARY KEY, pid TEXT REFERENCES t0(id), bpid BLOB REFERENCES t0(id))"
   , "CREATE TABLE t_chain(id INTEGER PRIMARY KEY, a INT, b TEXT, ut TEXT UNIQUE)"
   , "CREATE TABLE t_bom\uFEFF(x INT)" ]

private def insertStmts : Array (String × Nat) :=
  #[ ("INSERT INTO t0(id, u, v, tag, bin, anycol) VALUES (?, ?, ?, ?, ?, ?)", 6)
   , ("INSERT INTO t0(id, u, v, tag) VALUES (?, ?, ?, ?)", 4)
   , ("INSERT INTO t0(u, v, tag) VALUES (?, ?, ?)", 3)
   , ("INSERT INTO t0(u, v, tag) VALUES (?, ?, ?), (?, ?, ?)", 6)
   , ("INSERT INTO t_auto_str(v) VALUES (?), (?)", 2)
   , ("INSERT INTO t0(v, tag) VALUES (?, 'ok'), ('bad', 'x')", 1)
   , ("INSERT INTO t0(u, v) VALUES ('bad', 1), (2, 10)", 0)
   , ("INSERT INTO t0 VALUES (?, ?, ?, ?, ?, ?)", 6)
   , ("INSERT INTO t0(id, u) VALUES (?, ?), (?, ?)", 4)
   , ("INSERT INTO t0(id, u) VALUES (9223372036854775807, ?), (NULL, ?)", 2)
   , ("INSERT INTO t0(id, u) VALUES (NULL, ?), (1, ?)", 2)
   , ("INSERT INTO t0(id, u) VALUES (NULL, ?), (500, ?)", 2)
   , ("INSERT INTO t0(id, u) VALUES (NULL, ?), (NULL, ?)", 2)
   , ("INSERT INTO t0(u, u, id) VALUES (?, ?, ?)", 3)
   , ("INSERT INTO t0(id, id, u) VALUES (?, ?, ?)", 3)
   , ("INSERT INTO t0(id, id, u) VALUES (?, NULL, ?)", 2)
   , ("INSERT INTO t0(id, u) VALUES (9223372036854775807, ?)", 1)
   , ("INSERT INTO t0(id, u) VALUES (NULL, ?)", 1)
   , ("INSERT INTO t_plain(a, tag) VALUES (?, ?), (?, ?)", 4)
   , ("INSERT INTO fp_r(id, r) VALUES (?, ?)", 2)
   , ("INSERT INTO fc_r(id, pid) VALUES (?, ?)", 2)
   , ("INSERT INTO t_sref(id, pid, v) VALUES (?, ?, ?)", 3)
   , ("INSERT INTO t_sref(id, pid, v) VALUES (1, '1', 10), (2, '2', 20)", 0)
   , ("INSERT INTO t_sref(id, pid, v) VALUES ('1', 2, 10), ('02', 1, 20)", 0)
   , ("CREATE TABLE IF NOT EXISTS t_aff_p(k TEXT PRIMARY KEY, v INT)", 0)
   , ("CREATE TABLE IF NOT EXISTS t_aff_c(id INTEGER PRIMARY KEY, pid INT REFERENCES t_aff_p(k))", 0)
   , ("INSERT INTO t_aff_p(k, v) VALUES ('1', 100)", 0)
   , ("INSERT INTO t_aff_c(id, pid) VALUES (1, 1)", 0)
   , ("INSERT INTO t_aff_c(id, pid) VALUES (1, 1), (2, 999)", 0)
   , ("INSERT INTO t_pk_u(pk, u) VALUES (?, ?)", 2)
   , ("INSERT INTO t_u_pk(u, pk) VALUES (?, ?)", 2)
   , ("INSERT INTO t_tpk(k, v) VALUES (?, ?)", 2)
   , ("INSERT INTO t_bpk(k, v) VALUES (?, ?)", 2)
   , ("INSERT INTO fp_mix(id, bad) VALUES (?, ?)", 2)
   , ("INSERT INTO t1(id, pid, tag) VALUES (?, ?, ?)", 3)
   , ("INSERT INTO t1(id, pid, u, x, tag) VALUES (?, ?, ?, ?, ?)", 5)
   , ("INSERT INTO t2(id, pid, a, b) VALUES (?, ?, ?, ?)", 4)
   , ("INSERT INTO t2(id, x, y, z, w) VALUES (?, ?, ?, ?, ?)", 5)
   , ("INSERT INTO t0(id, u) VALUES (1, 10)", 0)
   , ("INSERT INTO t0(id, u) VALUES (-9223372036854775808, -1)", 0)
   , ("INSERT INTO t_chain VALUES (1, 10, '10', '10'), (2, 10, '010', '010')", 0)
   , ("INSERT INTO t_fk_txt(id, pid, bpid) VALUES (?, ?, ?)", 3) ]

private def updateStmts : Array (String × Nat) :=
  #[ ("UPDATE t0 SET u = ?, tag = ? WHERE id = ?", 3)
   , ("UPDATE t0 SET u = ?, u = ? WHERE id = ?", 3)
   , ("UPDATE t0 SET id = ?, id = ? WHERE id = ?", 3)
   , ("UPDATE t0 SET id = ?, u = ? WHERE id <= ?", 3)
   , ("UPDATE t0 SET tag = ? WHERE id = ?", 2)
   , ("UPDATE t0 SET id = ? WHERE id = ?", 2)
   , ("UPDATE t0 SET v = ? WHERE u >= ? AND tag IS NOT NULL", 2)
   , ("UPDATE t1 SET pid = ?, tag = ? WHERE id = ?", 3)
   , ("UPDATE t_sref SET v = ? WHERE id = ?", 2)
   , ("UPDATE t_sref SET id = ?, pid = ?, v = ? WHERE id = ?", 4)
   , ("UPDATE t_aff_p SET k = '01' WHERE k = '1'", 0)
   , ("UPDATE t_aff_c SET pid = ? WHERE id = ?", 2)
   , ("UPDATE t_plain SET tag = ? WHERE a = ?", 2)
   , ("UPDATE fp_mix SET id = ? WHERE id = ?", 2)
   , ("UPDATE fp_r SET r = ? WHERE id = ?", 2)
   , ("UPDATE t2 SET a = ?, b = ? WHERE id = ? OR pid IS NULL", 3) ]

private def deleteStmts : Array (String × Nat) :=
  #[ ("DELETE FROM t1 WHERE pid = ?", 1)
   , ("DELETE FROM t1 WHERE id = ?", 1)
   , ("DELETE FROM t0 WHERE id = ?", 1)
   , ("DELETE FROM t0 WHERE u < ? OR v IS NULL", 1)
   , ("DELETE FROM t_plain WHERE a = ?", 1)
   , ("DELETE FROM t2 WHERE id = ?", 1)
   , ("DELETE FROM t2", 0)
   , ("DELETE FROM t_sref WHERE id = ?", 1)
   , ("DELETE FROM t_sref", 0)
   , ("DELETE FROM t_sref2 WHERE id = ?", 1)
   , ("DELETE FROM t0_con WHERE id = ?", 1)
   , ("DELETE FROM fp_r WHERE id = ?", 1)
   , ("DELETE FROM t0", 0) ]

private def selectStmts : Array (String × Nat) :=
  #[ ("SELECT * FROM t0 ORDER BY id ASC", 0)
   , ("SELECT id, u FROM t0 WHERE u > ? ORDER BY id ASC", 1)
   , ("SELECT id, u FROM t0 ORDER BY u ASC", 0)
   , ("SELECT id, u FROM t0 ORDER BY u DESC", 0)
   , ("SELECT id, u FROM t0 ORDER BY id ASC, u ASC", 0)
   , ("SELECT id, u FROM t0 WHERE u >= ? ORDER BY u ASC, id ASC", 1)
   , ("SELECT id FROM t0 WHERE 1 IS NULL AND u = ?", 1)
   , ("SELECT id, u, v, tag, bin, anycol FROM t0 WHERE id >= ? AND (u != ? OR tag IS NOT NULL) ORDER BY u DESC NULLS FIRST, id ASC LIMIT ?", 3)
   , ("SELECT id, u, v, tag FROM t0 WHERE ((id = ?)) ORDER BY id ASC", 1)
   , ("SELECT a, tag FROM t_plain ORDER BY a ASC", 0)
   , ("SELECT id, u, v, tag FROM t0 WHERE v = ? ORDER BY v ASC NULLS LAST, id DESC LIMIT ?", 2)
   , ("SELECT * FROM t0 WHERE tag < ? ORDER BY tag ASC", 1)
   , ("SELECT * FROM t1 ORDER BY id DESC LIMIT ?", 1)
   , ("SELECT * FROM t1 WHERE pid = ? AND NOT (tag IS NULL)", 1)
   , ("SELECT * FROM t2 ORDER BY id ASC", 0)
   , ("SELECT 1, NULL, 'abc', X'00FF', ?", 1)
   , ("SELECT 1, ?, 'lim' LIMIT ?", 2)
   , ("SELECT * FROM t_bom", 0)
   , ("SELECT * FROM t_bom\uFEFF", 0)
   , ("SELECT id, v FROM t0 WHERE v = ? OR u = ? ORDER BY id ASC", 2)
   , ("SELECT u FROM t0 WHERE u <= ? OR u > ?", 2)
   , ("SELECT * FROM t0 WHERE tag = bin OR tag = anycol ORDER BY id ASC", 0)
   , ("SELECT id, ut FROM t_chain WHERE a = 10 AND b = a AND ut = b", 0)
   , ("SELECT id, ut FROM t_chain WHERE a = 10 AND b = a AND ut = b ORDER BY id DESC", 0)
   , ("SELECT * FROM t0 WHERE tag < anycol AND bin <= anycol", 0) ]

private def txControlStmts : Array String :=
  #[ "BEGIN"
   , "BEGIN DEFERRED"
   , "BEGIN DEFERRED TRANSACTION"
   , "BEGIN IMMEDIATE"
   , "BEGIN IMMEDIATE TRANSACTION"
   , "COMMIT"
   , "COMMIT TRANSACTION"
   , "ROLLBACK"
   , "ROLLBACK TRANSACTION" ]

private def hostileSqls : Array (String × Nat) :=
  #[ ("", 0)
   , ("   -- just a comment\n /* ok */ ", 0)
   , ("SELECT 1\x0B", 0)
   , ("SELECT  \x0B 1", 0)
   , ("SELECT 1; \x0B", 0)
   , ("SELECT 1;\x0B", 0)
   , ("SELECT 1; /* ok */\x0B", 0)
   , ("SELECT 1; -- c\n\x0B", 0)
   , ("SELECT /* unclosed", 0)
   , ("SELECT 1; SELECT 2", 0)
   , ("SELECT 'embedded\x00nul'", 0)
   , ("SELECT 1\x00", 0)
   , ("CREATE TABLE sqlite_evil(x INT)", 0)
   , ("SELECT X'A'", 0)
   , (String.ofList (List.replicate 65540 ' '), 0)
   , ("!invalid?", 0)
   , ("CREATE TABLE to(x INT)", 0)
   , ("CREATE TABLE add(x INT)", 0)
   , ("CREATE TABLE deferrable(x INT)", 0)
   , ("CREATE TABLE t_kw(isnull INT, notnull TEXT, escape REAL, nothing BLOB)", 0)
   , ("SELECT raise FROM t0", 0)
   , ("SELECT\uFEFF 1", 0)
   , ("SELECT 1\uFEFF", 0)
   , ("\uFEFF\x0BSELECT 1", 0)
   , ("SELECT 1 /*", 0)
   , ("/*", 0)
   , ("SELECT * FROM t0 WHERE " ++ mkRepeated 1005 "NOT " ++ "id = 1", 0)
   , ("SELECT * FROM t0 WHERE " ++ mkRepeated 999 "NOT " ++ "+1 IS NULL", 0)
   , ("SELECT * FROM t0 WHERE 1 IS NULL AND id = 1", 0)
   , ("SELECT * FROM t0 WHERE id = 1" ++ mkRepeated 1005 " OR id = 1", 0)
   , ("SELECT * FROM t0 WHERE " ++ mkRepeated 2600 "(" ++ "id = 1" ++ mkRepeated 2600 ")", 0)
   , ("UPDATE t0 SET u = 1 WHERE " ++ mkRepeated 2492 "(" ++ "id = 1" ++ mkRepeated 2492 ")", 0)
   , ("UPDATE t0 SET u = 1 WHERE " ++ mkRepeated 2495 "(" ++ "id = 1" ++ mkRepeated 2495 ")", 0)
   , ("DELETE FROM t0 WHERE " ++ mkRepeated 2492 "(" ++ "id = 1" ++ mkRepeated 2492 ")", 0)
   , ("DELETE FROM t0 WHERE " ++ mkRepeated 2495 "(" ++ "id = 1" ++ mkRepeated 2495 ")", 0)
   , ("SELECT * FROM t0 WHERE id = 1 OR " ++ mkRepeated 2492 "(" ++ "id = 1" ++ mkRepeated 2492 ")", 0)
   , ("SELECT * FROM t0 WHERE id = 1 AND " ++ mkRepeated 2492 "(" ++ "id = 1" ++ mkRepeated 2492 ")", 0)
   , ("SELECT * FROM t0 WHERE NOT " ++ mkRepeated 2492 "(" ++ "id = 1" ++ mkRepeated 2492 ")", 0)
   , ("SELECT * FROM t0 WHERE " ++ mkRepeated 2494 "(" ++ "id IS NOT NULL" ++ mkRepeated 2494 ")", 0)
   , ("SELECT * FROM t0 WHERE " ++ mkRepeated 2494 "(" ++ "id = +1" ++ mkRepeated 2494 ")", 0)
   , (mkManyColsSql 0, 0)
   , (mkManyColsSql 1, 0)
   , (mkManyColsSql 2, 0) ]

private def genWriteVerb (sql : String) (ps : Array SqliteValue) (r : Rng) : LeafSqlOp × Rng :=
  let (vTag, r1) := r.nextNat 10
  if vTag == 0 then (.query sql ps, r1)
  else if vTag == 1 then (.queryOne sql ps, r1)
  else (.exec sql ps, r1)

private def genCuratedLeaf (r : Rng) : LeafSqlOp × Rng :=
  let (kind, r1) := r.nextNat 100
  if kind < 16 then
    let (sql, r2) := chooseFrom colSetsCreate r1
    (.exec sql #[], r2)
  else if kind < 46 then
    let ((sql, arity), r2) := chooseFrom insertStmts r1
    let (ps, r3) := genValues arity r2
    genWriteVerb sql ps r3
  else if kind < 56 then
    let ((sql, arity), r2) := chooseFrom updateStmts r1
    let (ps, r3) := genValues arity r2
    genWriteVerb sql ps r3
  else if kind < 64 then
    let ((sql, arity), r2) := chooseFrom deleteStmts r1
    let (ps, r3) := genValues arity r2
    genWriteVerb sql ps r3
  else if kind < 74 then
    let (sql, r2) := chooseFrom txControlStmts r1
    (.exec sql #[], r2)
  else if kind < 90 then
    let ((sql, arity), r2) := chooseFrom selectStmts r1
    let (ps, r3) := genValues arity r2
    (.query sql ps, r3)
  else
    let ((sql, arity), r2) := chooseFrom selectStmts r1
    let (ps, r3) := genValues arity r2
    (.queryOne sql ps, r3)

private def genHostileLeaf (r : Rng) : LeafSqlOp × Rng :=
  let (mode, r1) := r.nextNat 10
  let ((sql, baseArity), r2) :=
    if mode < 8 then
      chooseFrom hostileSqls r1
    else if mode == 8 then
      let (tbl, ra) := chooseFrom tableNames r1
      ((s!"SELECT nonexistent FROM {tbl} WHERE ? = ?", 2), ra)
    else
      let (u, ra) := r1.nextU64
      ((s!"RAW_SQL_{u}", 0), ra)
  let (mismatch, r3) := r2.chance 1 3
  let (arity, r3') :=
    if mismatch then
      r3.nextNat 3
    else (baseArity, r3)
  let (ps, r4) := genValues arity r3'
  let (opTag, r5) := r4.nextNat 3
  let op :=
    match opTag with
    | 0 => LeafSqlOp.exec sql ps
    | 1 => LeafSqlOp.query sql ps
    | _ => LeafSqlOp.queryOne sql ps
  (op, r5)

/-- Generate a `LeafSqlOp` obeying the 55% curated / 45% adversarial mix. -/
def genLeafSqlOp (r : Rng) : LeafSqlOp × Rng :=
  let (pct, r1) := r.nextNat 100
  if pct < 55 then genCuratedLeaf r1 else genHostileLeaf r1

/-- Generate an `ExitMode`. -/
def genExitMode (r : Rng) : ExitMode × Rng :=
  let (tag, r1) := r.nextNat 10
  if tag < 6 then (.returnOk, r1)
  else if tag < 8 then
    let (kTag, r2) := r1.nextNat 4
    let kind : SqliteErrorKind :=
      if kTag == 0 then .constraint
      else if kTag == 1 then .busy
      else if kTag == 2 then .invalidInput
      else .ioError
    (.returnCallerErr { kind := kind, message := "caller aborted tx" }, r2)
  else
    (.throwIoUserError "fuzz injected io exception", r1)

/-- Generate a `ClosedHandleRef` targeting forged or escaped closed handles. -/
def genClosedHandleRef (r : Rng) : ClosedHandleRef × Rng :=
  let (tag, r1) := r.nextNat 4
  match tag with
  | 0 => (.zero, r1)
  | 1 => (.huge, r1)
  | 2 =>
    let (u, r2) := r1.nextU64
    (.raw u, r2)
  | _ =>
    let (idx, r2) := r1.nextNat 8
    (.escaped idx, r2)

/-- Generate a `DbConnOp` including leaf statements, transactions, and dual-connection interleavings. -/
def genDbConnOp (r : Rng) : DbConnOp × Rng :=
  let (tag, r1) := r.nextNat 100
  if tag < 62 then
    let (op, r2) := genLeafSqlOp r1
    (.leaf op, r2)
  else if tag < 65 then
    let (useCommit, r2) := r1.nextBool
    let (kTag, r3) := r2.nextNat 4
    let kind : SqliteErrorKind :=
      if kTag == 0 then .constraint
      else if kTag == 1 then .busy
      else if kTag == 2 then .invalidInput
      else .ioError
    let endSql := if useCommit then "COMMIT" else "ROLLBACK"
    let (preOp, r4) := genCuratedLeaf r3
    let (withPre, r5) := r4.nextBool
    let txOps := if withPre then #[preOp, .exec endSql #[]] else #[.exec endSql #[]]
    (.withTx txOps (.returnCallerErr { kind := kind, message := "caller aborted after manual tx end" }), r5)
  else if tag < 82 then
    let (cnt, r2) := r1.nextRange 1 4
    let (txOps, r3) := Id.run do
      let mut cur := r2
      let mut acc := Array.mkEmpty cnt
      for _ in List.range cnt do
        let (op, nxt) := genLeafSqlOp cur
        cur := nxt
        acc := acc.push op
      return (acc, cur)
    let (em, r4) := genExitMode r3
    (.withTx txOps em, r4)
  else
    let (tTag, r2) := r1.nextNat 6
    let target2 :=
      if tTag < 3 then TargetSpec.db0
      else if tTag == 3 then TargetSpec.db1
      else if tTag == 4 then TargetSpec.ro0444
      else TargetSpec.memory
    let (cfg2, r3) := genValidOpenConfig r2
    let (cnt, r4) := r3.nextRange 1 6
    let (dualOps, r5) := Id.run do
      let mut cur := r4
      let mut acc := Array.mkEmpty cnt
      for _ in List.range cnt do
        let (useSecond, rx) := cur.nextBool
        let (op, ry) := genLeafSqlOp rx
        cur := ry
        acc := acc.push (useSecond, op)
      return (acc, cur)
    let (em2, r6) := genExitMode r5
    (.nestedWithDb target2 cfg2 dualOps em2, r6)

private def rawProbeSqls : Array (String × Nat) :=
  #[ ("CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)", 0)
   , ("INSERT INTO r0(id, u, tag) VALUES (?, ?, ?)", 3)
   , ("DELETE FROM r0 WHERE id = ?", 1)
   , ("SELECT id, u, tag FROM r0 ORDER BY id ASC", 0)
   , ("SELECT * FROM r0 WHERE id = ? OR id = ?", 2)
   , ("SELECT ?", 1)
   , ("BEGIN DEFERRED", 0)
   , ("BEGIN IMMEDIATE", 0)
   , ("COMMIT", 0)
   , ("ROLLBACK", 0)
   , ("SELECT 1 /*", 0)
   , ("/*", 0)
   , ("\uFEFF\x0BSELECT 1", 0)
   , ("SELECT 1; SELECT 2", 0)
   , ("SELECT 1\x00", 0)
   , ("SELECT 'a\x00b'", 0)
   , (String.ofList (List.replicate 65540 ' '), 0)
   , ("!bad syntax!", 0)
   , ("", 0) ]

private def genRawSession (r : Rng) : TopAction × Rng :=
  let (tChoice, r1) := r.nextNat 24
  let tgt : TargetSpec :=
    if tChoice < 2 then .memory
    else if tChoice < 4 then .db0
    else if tChoice == 4 then .db1
    else if tChoice == 5 then .corrupt
    else if tChoice == 6 then .ro0444
    else if tChoice == 7 then .missing
    else if tChoice == 8 then .subdir
    else if tChoice == 9 then .raw "file::memory:?mode=ro"
    else if tChoice == 10 then .epSuffix ("/" ++ String.ofList (List.replicate 520 'p') ++ ".sqlite")
    else if tChoice == 11 then .raw ""
    else if tChoice == 12 then .raw "bad\x00path.sqlite"
    else if tChoice == 13 then .raw "file:"
    else if tChoice == 14 then .raw "file:#?mode=memory"
    else if tChoice == 15 then .raw "file::memory:?immutable=1"
    else if tChoice == 16 then .raw "file::memory:?mode=rw"
    else if tChoice == 17 then .raw "file::memory:?mode=rwc"
    else if tChoice == 18 then .raw "file::memory:?mode=rw&immutable=1"
    else if tChoice == 19 then .raw "file:%3Amemory%3A?mode=ro"
    else if tChoice == 20 then .raw "file://badhost/x.db"
    else if tChoice == 21 then .raw "file::memory:?cache=shared&mode=memory"
    else if tChoice == 22 then .epUri "file:" "/db0.sqlite?mode=ro"
    else .epUri "file://localhost" "/db0.sqlite?mode=rw#frag"
  let (useEdgeCfg, r1b) := r1.nextNat 5
  let (cfg, r2) :=
    if useEdgeCfg == 0 then genSessionOpenConfig r1b
    else genValidOpenConfig r1b
  let (pat, r3) := r2.nextNat 28
  if pat == 0 then
    let p0Tgt : TargetSpec := if tChoice % 2 == 0 then .memory else .db0
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT ?"
       , .bind 0 #[]
       , .step 0
       , .bind 0 #[.int 7]
       , .peerExec "INSERT INTO r0(id, u, tag) VALUES (91, 91, 'peer')" #[]
       , .step 0
       , .finalize 0
       , .step 0
       , .bind 0 #[.int 8]
       , .finalize 0 ]
    (.rawSession p0Tgt { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 1 then
    let (walB, r4) := r3.nextBool
    let cbTgt : TargetSpec := if tChoice % 2 == 0 then .memory else .db0
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
       , .step 0
       , .prepare 0 "BEGIN IMMEDIATE"
       , .step 0
       , .prepare 1 "INSERT INTO r0(id, u, tag) VALUES (?, ?, ?)"
       , .bind 1 #[.int 55, .int 55, .text "rb"]
       , .step 1
       , .prepare 0 "ROLLBACK"
       , .step 0
       , .prepare 1 "SELECT id, u, tag FROM r0 ORDER BY id ASC"
       , .step 1
       , .finalize 0 ]
    (.rawSession cbTgt { walMode := walB, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 2 then
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS wal_t0(id INTEGER PRIMARY KEY, u INT UNIQUE)"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO wal_t0(id, u) VALUES (1, 10), (2, 20)"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT id, u FROM wal_t0 WHERE u > 5 ORDER BY u ASC"
       , .step 0
       , .peerExec "INSERT INTO wal_t0(id, u) VALUES (3, 30)" #[]
       , .step 0
       , .finalize 0 ]
    (.rawSession .db0 { walMode := true, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 3 then
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO r0(id, u, tag) VALUES (1, 10, 'a'), (2, 20, 'b')"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT id, u FROM r0 ORDER BY id ASC"
       , .step 0
       , .prepare 1 "BEGIN IMMEDIATE"
       , .step 1
       , .finalize 1
       , .prepare 1 "CREATE TABLE IF NOT EXISTS ghost_rb(x INT)"
       , .step 1
       , .finalize 1
       , .prepare 1 "ROLLBACK"
       , .step 1
       , .finalize 1
       , .step 0
       , .finalize 0 ]
    (.rawSession .db1 { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 4 then
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS mm0(x INT)"
       , .step 0
       , .finalize 0 ]
    (.rawSession (.raw "file::memory:?mode=memory") { readOnly := true, createIfMissing := false, walMode := false } ops, r3)
  else if pat == 5 then
    let (sub, r4) := r3.nextNat 3
    let qSql :=
      if sub == 0 then "SELECT 1"
      else if sub == 1 then "SELECT id, u FROM r0 ORDER BY tag DESC NULLS FIRST"
      else "SELECT id, u FROM r0 ORDER BY id ASC LIMIT 1"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO r0(id, u, tag) VALUES (1, 10, 'a'), (2, 20, 'b')"
       , .step 0
       , .finalize 0
       , .prepare 0 qSql
       , .step 0
       , .prepare 1 "BEGIN IMMEDIATE"
       , .step 1
       , .finalize 1
       , .prepare 1 "CREATE TABLE IF NOT EXISTS ghost_rb2(x INT)"
       , .step 1
       , .finalize 1
       , .prepare 1 "ROLLBACK"
       , .step 1
       , .finalize 1
       , .peerExec "INSERT INTO r0(id, u, tag) VALUES (3, 30, 'c')" #[]
       , .step 0
       , .step 0
       , .finalize 0 ]
    (.rawSession .db1 { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 6 then
    let (sub, r4) := r3.nextNat 3
    let qSql :=
      if sub == 0 then "SELECT id, u FROM r0 WHERE u = 10 ORDER BY tag DESC NULLS FIRST"
      else if sub == 1 then "SELECT id, u FROM r0 WHERE id = 1"
      else "SELECT id, u FROM r0 WHERE u = 10"
    let ops : Array RawStepOp :=
      if sub < 2 then
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
         , .step 0
         , .finalize 0
         , .prepare 0 "INSERT INTO r0(id, u, tag) VALUES (1, 10, 'a'), (2, 20, 'b')"
         , .step 0
         , .finalize 0
         , .prepare 0 qSql
         , .step 0
         , .prepare 1 "BEGIN IMMEDIATE"
         , .step 1
         , .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS ghost_rb3(x INT)"
         , .step 1
         , .finalize 1
         , .prepare 1 "ROLLBACK"
         , .step 1
         , .finalize 1
         , .step 0
         , .finalize 0 ]
      else
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS r0(id INTEGER PRIMARY KEY, u INT UNIQUE, tag TEXT)"
         , .step 0
         , .finalize 0
         , .prepare 0 "INSERT INTO r0(id, u, tag) VALUES (1, 10, 'a'), (2, 20, 'b')"
         , .step 0
         , .finalize 0
         , .prepare 0 qSql
         , .step 0
         , .prepare 1 "DELETE FROM r0 WHERE id = 1"
         , .step 1
         , .finalize 1
         , .prepare 1 "INSERT INTO r0(id, u, tag) VALUES (3, 10, 'c')"
         , .step 1
         , .finalize 1
         , .step 0
         , .finalize 0 ]
    (.rawSession .db1 { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 7 then
    let uriTargets : Array TargetSpec :=
      #[ .raw "file:"
       , .raw "file://"
       , .raw "file:?mode=ro"
       , .raw "file:?mode=rw"
       , .raw "file:?mode=rwc"
       , .raw "file::memory:?mode=rw"
       , .raw "file::memory:?mode=rwc"
       , .raw "file::memory:?mode=ro&mode=rw"
       , .raw "file::memory:?mode=memory&mode=rwc"
       , .raw "file://#frag"
       , .raw "file://localhost#frag"
       , .raw "file://localhost#?mode=memory"
       , .raw "file::memory:?vfs=bad&vfs=unix"
       , .raw "file::memory:?vfs="
       , .raw "file:rel_imm?vfs=memdb&immutable=1"
       , .epUri "file:" "/%"
       , .epUri "file:" "/%4"
       , .epUri "file:" "/%4g"
       , .epUri "file:" "/%FF"
       , .raw "file:%FF?vfs=memdb&immutable=1"
       , .raw "file:/uri_pct_%FF?vfs=memdb"
       , .raw ("file:/" ++ String.ofList (List.replicate 1015 'm') ++ "?vfs=memdb")
       , .raw ("file:/" ++ String.ofList (List.replicate 1016 'm') ++ "?vfs=memdb") ]
    let (idx, r4) := r3.nextNat uriTargets.size
    let uTgt := uriTargets.getD idx .memory
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS u0(x INT)"
       , .step 0
       , .finalize 0 ]
    (.rawSession uTgt cfg ops, r4)
  else if pat == 8 then
    let (qTag, r4) := r3.nextNat 4
    let selSql :=
      if qTag == 0 then "SELECT id, u1, u2, tag FROM lc0 WHERE u1 != 999"
      else if qTag == 1 then "SELECT id, u1, u2, tag FROM lc0 WHERE id > 0 AND u1 > 0"
      else if qTag == 2 then "SELECT id, u1, u2, tag FROM lc0 WHERE u1 > 0 AND u2 > 0"
      else "SELECT id, u1 FROM lc0 WHERE u1 = 30 OR u1 = 10"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS lc0(id INTEGER PRIMARY KEY, u1 INT UNIQUE, u2 INT UNIQUE, tag TEXT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM lc0"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO lc0 VALUES (1, 30, 10, 'a'), (2, 10, 30, 'b'), (3, 20, 20, 'c')"
       , .step 0
       , .finalize 0
       , .prepare 0 selSql
       , .step 0
       , .prepare 1 "INSERT INTO lc0 VALUES (4, 5, 40, 'd')"
       , .step 1
       , .finalize 1
       , .step 0
       , .step 0
       , .step 0
       , .step 0
       , .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 9 then
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS ra0(id INTEGER PRIMARY KEY AUTOINCREMENT, x INT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM ra0"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO ra0 VALUES (9223372036854775807, 1), (1, 2)"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT id, x FROM ra0 ORDER BY id ASC"
       , .step 0
       , .prepare 1 "BEGIN IMMEDIATE"
       , .step 1
       , .finalize 1
       , .prepare 1 "CREATE TABLE IF NOT EXISTS ghost_auto_rb(x INT)"
       , .step 1
       , .finalize 1
       , .prepare 1 "INSERT INTO ra0(x) VALUES (10)"
       , .step 1
       , .finalize 1
       , .peerExec "INSERT INTO ra0(id, x) VALUES (2, 20)" #[]
       , .step 0
       , .finalize 0 ]
    (.rawSession .db1 { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 10 then
    let (sub, r4) := r3.nextNat 7
    let shTgt : TargetSpec :=
      if sub == 0 then .raw "file:/sh_fuzz_sm?vfs=memdb"
      else if sub == 1 then .raw "file:\\sh_fuzz_bs?vfs=memdb"
      else if sub == 2 then .raw "file::memory:?cache=shared"
      else if sub == 3 then .epUri "file:" "/db0.sqlite?cache=shared"
      else if sub == 4 then .raw "file:/shared_cache_sm?vfs=memdb&cache=shared"
      else if sub == 5 then .raw "file::memory:?mode=ro%"
      else .exactPathBytes 505
    let (pWal, r4a) := r4.nextBool
    let (pFk, r4b) := r4a.nextBool
    let (ddlLock, r4c) := r4b.nextBool
    let (ddlKind, r4d) := r4c.nextNat 3
    let ddlPeerSql :=
      if ddlKind == 0 then "SELECT id, x FROM sm0"
      else if ddlKind == 1 then "ROLLBACK"
      else ""
    let peerCfg : OpenConfig := { walMode := pWal, busyTimeoutMs := 0, foreignKeys := pFk }
    let ops : Array RawStepOp :=
      if ddlLock then
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS sm0(id INTEGER PRIMARY KEY, x INT)"
         , .step 0
         , .finalize 0
         , .prepare 1 "BEGIN IMMEDIATE"
         , .step 1
         , .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS sm_ddl_lock(y INT)"
         , .step 1
         , .finalize 1
         , .rawPeerExec shTgt peerCfg ddlPeerSql #[]
         , .prepare 1 "ROLLBACK"
         , .step 1
         , .finalize 1 ]
      else
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS sm0(id INTEGER PRIMARY KEY, x INT)"
         , .step 0
         , .finalize 0
         , .prepare 0 "INSERT INTO sm0(id, x) VALUES (1, 10), (2, 20)"
         , .step 0
         , .finalize 0
         , .rawPeerExec shTgt peerCfg "SELECT id, x FROM sm0 ORDER BY id ASC" #[]
         , .prepare 0 "SELECT id, x FROM sm0 ORDER BY id ASC"
         , .step 0
         , .rawPeerExec shTgt peerCfg "INSERT INTO sm0(id, x) VALUES (3, 30)" #[]
         , .step 0
         , .step 0
         , .finalize 0
         , .prepare 1 "BEGIN IMMEDIATE"
         , .step 1
         , .finalize 1
         , .prepare 1 "INSERT INTO sm0(id, x) VALUES (4, 40)"
         , .step 1
         , .finalize 1
         , .rawPeerExec shTgt peerCfg "SELECT id, x FROM sm0" #[]
         , .rawPeerExec shTgt peerCfg "INSERT INTO sm0(id, x) VALUES (5, 50)" #[]
         , .prepare 1 "COMMIT"
         , .step 1
         , .finalize 1 ]
    (.rawSession shTgt { walMode := true, busyTimeoutMs := 0, foreignKeys := true } ops, r4d)
  else if pat == 11 then
    let (sub, r4) := r3.nextNat 8
    let vTgt : TargetSpec :=
      if sub == 0 then .epUri "file:" "/db1.sqlite?vfs=unix-dotfile"
      else if sub == 1 then .epUri "file:" "/db1.sqlite?vfs=unix-none"
      else if sub == 2 then .epUri "file:" "/db1.sqlite?nolock=1"
      else if sub == 3 then .epUri "file:" "/db1.sqlite?immutable=1&immutable=0"
      else if sub == 4 then .epUri "file:" "/db1.sqlite?immutable=01"
      else if sub == 5 then .epUri "file:" "/walro0444.sqlite?vfs=unix-dotfile"
      else if sub == 6 then .epUri "file:" "/ro0444.sqlite?nolock=1"
      else .epUri "file:" "/walro0444.sqlite?nolock=1"
    let (walB, r5) := r4.nextBool
    let sessCfg : OpenConfig :=
      if sub == 6 then { walMode := walB, createIfMissing := false, busyTimeoutMs := 0, foreignKeys := true }
      else { walMode := walB, busyTimeoutMs := 0, foreignKeys := true }
    let peerCfg : OpenConfig := { walMode := false, createIfMissing := sub != 6, busyTimeoutMs := 0, foreignKeys := true }
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS vf0(id INTEGER PRIMARY KEY, x INT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO vf0(id, x) VALUES (1, 10), (2, 20)"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT id, x FROM vf0 ORDER BY id ASC"
       , .step 0
       , .rawPeerExec vTgt peerCfg "SELECT id, x FROM vf0" #[]
       , .rawPeerExec vTgt peerCfg "INSERT INTO vf0(id, x) VALUES (3, 30)" #[]
       , .step 0
       , .finalize 0 ]
    (.rawSession vTgt sessCfg ops, r5)
  else if pat == 12 then
    let (sub, r4) := r3.nextNat 14
    let selSql :=
      if sub == 0 then "SELECT id, u FROM ob0 ORDER BY u ASC NULLS FIRST"
      else if sub == 1 then "SELECT id, u FROM ob0 ORDER BY u ASC NULLS LAST"
      else if sub == 2 then "SELECT id, u FROM ob0 ORDER BY u DESC NULLS FIRST"
      else if sub == 3 then "SELECT id, u FROM ob0 ORDER BY u DESC NULLS LAST"
      else if sub == 4 then "SELECT id, u, v FROM ob0 ORDER BY u ASC, v DESC"
      else if sub == 5 then "SELECT id, u FROM ob0 WHERE u2 = 2 OR u2 = 3 ORDER BY u ASC"
      else if sub == 6 then "SELECT id, u FROM ob0 WHERE id > 1 AND id < 4 ORDER BY u DESC"
      else if sub == 7 then "SELECT id FROM ob0 WHERE id = 3 OR id = 1 ORDER BY id ASC NULLS LAST"
      else if sub == 8 then "SELECT id, v FROM ob0 WHERE u IS NULL ORDER BY id DESC, v ASC"
      else if sub == 9 then "SELECT id FROM ob0 WHERE u IS NULL ORDER BY u DESC"
      else if sub == 10 then "SELECT id FROM ob0 WHERE (u = 20 OR u = 10) AND (u2 > 0 AND u2 < 10) ORDER BY u DESC"
      else if sub == 11 then "SELECT id FROM ob0 WHERE (u > 5 AND u < 25) AND (u2 > 0 AND u2 < 10) ORDER BY u DESC"
      else if sub == 12 then "SELECT id FROM ob0 WHERE (u = 20 OR u = 10) AND u2 IS NULL ORDER BY u DESC"
      else "SELECT id FROM ob0 WHERE v = u2 AND (v = 2 OR v = 3) ORDER BY u ASC"
    let (doRb, r5) := r4.nextBool
    let ops : Array RawStepOp :=
      if !doRb then
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS ob0(id INTEGER PRIMARY KEY, u INT UNIQUE, u2 INT UNIQUE, v INT)"
         , .step 0
         , .finalize 0
         , .prepare 0 "DELETE FROM ob0"
         , .step 0
         , .finalize 0
         , .prepare 0 "INSERT INTO ob0 VALUES (1, NULL, 1, 10), (2, 10, 2, 200), (3, 20, 3, 300), (4, NULL, 4, 50)"
         , .step 0
         , .finalize 0
         , .prepare 0 selSql
         , .step 0
         , .prepare 1 "INSERT INTO ob0 VALUES (0, NULL, 0, 999), (5, 15, 5, 88), (6, NULL, 6, 1)"
         , .step 1
         , .finalize 1
         , .step 0
         , .step 0
         , .step 0
         , .step 0
         , .step 0
         , .step 0
         , .finalize 0 ]
      else
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS ob0(id INTEGER PRIMARY KEY, u INT UNIQUE, u2 INT UNIQUE, v INT)"
         , .step 0
         , .finalize 0
         , .prepare 0 "DELETE FROM ob0"
         , .step 0
         , .finalize 0
         , .prepare 0 "INSERT INTO ob0 VALUES (1, NULL, 1, 10), (2, 10, 2, 200), (3, 20, 3, 300), (4, NULL, 4, 50)"
         , .step 0
         , .finalize 0
         , .prepare 0 selSql
         , .step 0
         , .prepare 1 "BEGIN"
         , .step 1
         , .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS z_ob_rb(x INT)"
         , .step 1
         , .finalize 1
         , .prepare 1 "ROLLBACK"
         , .step 1
         , .finalize 1
         , .step 0
         , .step 0
         , .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r5)
  else if pat == 13 then
    let (qTag, r4) := r3.nextNat 5
    let selSql :=
      if qTag == 0 then "SELECT id, a, u1, u2 FROM lc2 WHERE a = 10 AND u1 > a"
      else if qTag == 1 then "SELECT id, a, u1, u2 FROM lc2 WHERE (u1 = 30 OR u1 = 10) AND u2 > 0"
      else if qTag == 2 then "SELECT id, a, u1, u2 FROM lc2 WHERE a = 10 AND (u1 = a OR u1 = 30) AND u2 > 0"
      else if qTag == 3 then "SELECT id, a, u1, u2 FROM lc2 WHERE a = u2 AND (a = 30 OR a = 10)"
      else "SELECT id, a, u1, u2 FROM lc2 WHERE a = u2 AND a > 5 AND a < 35 ORDER BY u1 ASC"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS lc2(id INTEGER PRIMARY KEY, a INT, u1 INT UNIQUE, u2 INT UNIQUE)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM lc2"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO lc2 VALUES (1, 10, 30, 10), (2, 10, 20, 20), (3, 10, 10, 30)"
       , .step 0
       , .finalize 0
       , .prepare 0 selSql
       , .step 0
       , .prepare 1 "INSERT INTO lc2 VALUES (0, 10, 25, 40)"
       , .step 1
       , .finalize 1
       , .step 0
       , .step 0
       , .step 0
       , .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 14 then
    let (qTag, r4) := r3.nextNat 3
    let selSql :=
      if qTag == 0 then "SELECT id, u1, u2 FROM rb_nulls WHERE (u1 = 10 OR u1 = 20) ORDER BY id ASC"
      else if qTag == 1 then "SELECT id, u1 FROM rb_nulls ORDER BY u1 ASC NULLS LAST"
      else "SELECT id, u1 FROM rb_nulls ORDER BY u1 DESC NULLS FIRST"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS rb_nulls(id INTEGER PRIMARY KEY, u1 INT UNIQUE, u2 INT UNIQUE)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM rb_nulls"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO rb_nulls VALUES (1, 20, 10), (2, 10, 20), (3, NULL, 30), (4, NULL, 40)"
       , .step 0
       , .finalize 0
       , .prepare 0 selSql
       , .step 0
       , .prepare 1 "BEGIN IMMEDIATE"
       , .step 1
       , .finalize 1
       , .prepare 1 "CREATE TABLE IF NOT EXISTS ghost_nulls_rb(x INT)"
       , .step 1
       , .finalize 1
       , .prepare 1 "ROLLBACK"
       , .step 1
       , .finalize 1
       , .step 0
       , .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 15 then
    let (txB, r4) := r3.nextBool
    let begSql := if txB then "BEGIN IMMEDIATE" else "BEGIN DEFERRED"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS wal_com_scan(id INTEGER PRIMARY KEY, x INT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM wal_com_scan"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO wal_com_scan VALUES (1, 10), (2, 20)"
       , .step 0
       , .finalize 0
       , .prepare 1 begSql
       , .step 1
       , .finalize 1
       , .prepare 1 "SELECT id, x FROM wal_com_scan ORDER BY id ASC"
       , .step 1
       , .prepare 0 "COMMIT"
       , .step 0
       , .finalize 0
       , .peerExec "INSERT INTO wal_com_scan VALUES (3, 30)" #[]
       , .prepare 0 "BEGIN IMMEDIATE"
       , .step 0
       , .finalize 0
       , .step 1
       , .step 1
       , .finalize 1 ]
    (.rawSession .db0 { walMode := true, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 16 then
    let (uTag, r4) := r3.nextNat 6
    if uTag == 0 then
      (.rawSession (.raw "file://#frag") cfg #[.prepare 0 "SELECT 1", .step 0, .finalize 0], r4)
    else if uTag == 1 then
      (.rawSession (.raw "file://localhost#frag") cfg #[.prepare 0 "SELECT 1", .step 0, .finalize 0], r4)
    else if uTag == 2 then
      (.rawSession (.raw "file:priv_mem?vfs=memdb&immutable=1")
        { walMode := true, busyTimeoutMs := 0, foreignKeys := true }
        #[.prepare 0 "CREATE TABLE IF NOT EXISTS im0(x INT)", .step 0, .finalize 0], r4)
    else if uTag == 3 then
      (.rawSession (.epUri "file:" "/a%4Z.sqlite")
        { walMode := false, busyTimeoutMs := 0, foreignKeys := true }
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS pct1(x INT)"
         , .step 0
         , .finalize 0
         , .rawPeerExec (.epSuffix "/a%4Z.sqlite")
             { walMode := false, createIfMissing := false, busyTimeoutMs := 0, foreignKeys := true }
             "SELECT x FROM pct1" #[] ], r4)
    else if uTag == 4 then
      (.rawSession (.epUri "file:" "/b%4.sqlite")
        { walMode := false, busyTimeoutMs := 0, foreignKeys := true }
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS pct2(x INT)"
         , .step 0
         , .finalize 0
         , .rawPeerExec (.epSuffix "/b%4.sqlite")
             { walMode := false, createIfMissing := false, busyTimeoutMs := 0, foreignKeys := true }
             "SELECT x FROM pct2" #[] ], r4)
    else
      let ops : Array RawStepOp :=
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS sm0(id INTEGER PRIMARY KEY, x INT)"
         , .step 0
         , .finalize 0
         , .peerExec "INSERT INTO sm0 VALUES (1, 42)" #[]
         , .prepare 0 "SELECT id, x FROM sm0 ORDER BY id ASC"
         , .step 0
         , .peerExec "INSERT INTO sm0 VALUES (2, 99)" #[]
         , .step 0
         , .finalize 0 ]
      (.rawSession (.raw "file:/shared_fuzz_mem?vfs=memdb")
        { walMode := true, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else if pat == 17 then
    let (sub, r4) := r3.nextNat 3
    if sub == 0 then
      let shRo : TargetSpec := .epUri "file:" "/ro0444.sqlite?mode=ro&cache=shared"
      let shRw : TargetSpec := .epUri "file:" "/ro0444.sqlite?cache=shared"
      let ops : Array RawStepOp :=
        #[ .prepare 0 "SELECT id, x FROM ro_seed"
         , .step 0
         , .finalize 0
         , .rawPeerExec shRw { walMode := false, busyTimeoutMs := 0 } "INSERT INTO ro_seed VALUES (9, 9)" #[]
         , .rawPeerExec shRw { walMode := true, busyTimeoutMs := 0 } "SELECT id, x FROM ro_seed" #[] ]
      (.rawSession shRo { readOnly := true, createIfMissing := false, walMode := false, busyTimeoutMs := 0 } ops, r4)
    else if sub == 1 then
      let shMem : TargetSpec := .epUri "file:" "/ghost_mem_sh.sqlite?mode=memory&cache=shared"
      let shFile : TargetSpec := .epUri "file:" "/ghost_mem_sh.sqlite?cache=shared"
      let ops : Array RawStepOp :=
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS gm(id INTEGER PRIMARY KEY, x INT)"
         , .step 0
         , .finalize 0
         , .rawPeerExec shFile { createIfMissing := false, walMode := false, busyTimeoutMs := 0 } "INSERT INTO gm VALUES (1, 77)" #[]
         , .prepare 0 "SELECT id, x FROM gm"
         , .step 0
         , .finalize 0 ]
      (.rawSession shMem { walMode := false, busyTimeoutMs := 0 } ops, r4)
    else
      let uFF : TargetSpec := .raw "file:/sh_pct_%FF?vfs=memdb"
      let ops : Array RawStepOp :=
        #[ .prepare 0 "CREATE TABLE IF NOT EXISTS mff(id INTEGER PRIMARY KEY, x INT)"
         , .step 0
         , .finalize 0
         , .rawPeerExec uFF { walMode := false, busyTimeoutMs := 0 } "INSERT INTO mff VALUES (1, 55)" #[]
         , .prepare 0 "SELECT id, x FROM mff"
         , .step 0
         , .finalize 0 ]
      (.rawSession uFF { walMode := false, busyTimeoutMs := 0 } ops, r4)
  else if pat == 18 then
    let shTgt : TargetSpec := .epUri "file:" "/db1.sqlite?cache=shared"
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS d0(id INTEGER PRIMARY KEY, x INT)"
       , .step 0
       , .finalize 0
       , .rawPeerExec shTgt { walMode := false, busyTimeoutMs := 0 } "SELECT id, x FROM d0" #[]
       , .prepare 0 "BEGIN IMMEDIATE"
       , .step 0
       , .finalize 0
       , .prepare 0 "CREATE TABLE d_uncom(x INT)"
       , .step 0
       , .finalize 0
       , .rawPeerExec shTgt { walMode := false, foreignKeys := true, busyTimeoutMs := 0 } "SELECT 1" #[]
       , .rawPeerExec shTgt { walMode := false, foreignKeys := false, busyTimeoutMs := 0 } "BEGIN" #[]
       , .rawPeerExec shTgt { walMode := false, foreignKeys := false, busyTimeoutMs := 0 } "" #[]
       , .prepare 0 "ROLLBACK"
       , .step 0
       , .finalize 0
       , .rawPeerExec shTgt { walMode := false, busyTimeoutMs := 0 } "CREATE TABLE IF NOT EXISTS d_com(x INT)" #[]
       , .prepare 0 "CREATE TABLE d_com(x INT)" ]
    (.rawSession shTgt { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 19 then
    let (walB, r4) := r3.nextBool
    let shTgt : TargetSpec := .epUri "file:" (if walB then "/db0.sqlite?cache=shared" else "/db1.sqlite?cache=shared")
    let pCfg : OpenConfig := { walMode := walB, busyTimeoutMs := 0, foreignKeys := true }
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS sp1(id INTEGER PRIMARY KEY, x INT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "CREATE TABLE IF NOT EXISTS sp2(id INTEGER PRIMARY KEY, x INT)"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM sp1"
       , .step 0
       , .finalize 0
       , .prepare 0 "DELETE FROM sp2"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO sp1 VALUES (1, 10)"
       , .step 0
       , .finalize 0
       , .prepare 0 "BEGIN DEFERRED"
       , .step 0
       , .finalize 0
       , .prepare 0 "SELECT id, x FROM sp1"
       , .step 0
       , .finalize 0
       , .rawPeerExec shTgt { walMode := true, busyTimeoutMs := 0 } "INSERT INTO sp2 VALUES (1, 20)" #[]
       , .prepare 0 "SELECT id, x FROM sp2 ORDER BY id ASC"
       , .step 0
       , .finalize 0
       , .prepare 0 "INSERT INTO sp1 VALUES (2, 11)"
       , .step 0
       , .finalize 0
       , .prepare 0 "COMMIT"
       , .step 0
       , .finalize 0 ]
    (.rawSession shTgt pCfg ops, r4)
  else if pat == 20 then
    let (qSub, r4) := r3.nextNat 5
    let (useMidIns, r5) := r4.nextBool
    let schemaSql :=
      if qSub < 3 then "CREATE TABLE IF NOT EXISTS cov0(id INTEGER PRIMARY KEY, u INT UNIQUE, a INT)"
      else if qSub == 3 then "CREATE TABLE IF NOT EXISTS cov0(id INTEGER PRIMARY KEY, u1 TEXT UNIQUE, u2 INT UNIQUE)"
      else "CREATE TABLE IF NOT EXISTS cov0(id INTEGER PRIMARY KEY, u1 INT UNIQUE, u2 TEXT UNIQUE)"
    let insSql :=
      if qSub < 3 then "INSERT INTO cov0 VALUES (1, 200, 10), (2, 100, 20)"
      else if qSub == 3 then "INSERT INTO cov0 VALUES (1, 'a', 200), (2, 'b', 100)"
      else "INSERT INTO cov0 VALUES (1, 200, 'a'), (2, 100, 'b')"
    let selSql :=
      if qSub == 0 then "SELECT id, u FROM cov0"
      else if qSub == 1 then "SELECT 1 FROM cov0"
      else if qSub == 2 then "SELECT id, u FROM cov0 WHERE u IS NOT NULL"
      else "SELECT id FROM cov0"
    let midOps : Array RawStepOp :=
      if useMidIns && qSub < 3 then
        #[.prepare 1 "INSERT INTO cov0 VALUES (0, 150, 30)", .step 1, .finalize 1]
      else
        #[ .prepare 1 "BEGIN", .step 1, .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS cov_rb(x INT)", .step 1, .finalize 1
         , .prepare 1 "ROLLBACK", .step 1, .finalize 1 ]
    let ops : Array RawStepOp :=
      #[ .prepare 0 schemaSql, .step 0, .finalize 0
       , .prepare 0 "DELETE FROM cov0", .step 0, .finalize 0
       , .prepare 0 insSql, .step 0, .finalize 0
       , .prepare 0 selSql, .step 0 ] ++ midOps ++
      #[ .step 0, .step 0, .step 0, .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r5)
  else if pat == 21 then
    let (qSub, r4) := r3.nextNat 8
    let (useMidIns, r5) := r4.nextBool
    let qSql :=
      if qSub == 0 then "SELECT id, u, a FROM ob_idx WHERE u IS NULL ORDER BY id ASC"
      else if qSub == 1 then "SELECT id, u, a FROM ob_idx WHERE u IS NULL ORDER BY id DESC"
      else if qSub == 2 then "SELECT id, u, a FROM ob_idx WHERE u IS NULL ORDER BY id ASC, a DESC"
      else if qSub == 3 then "SELECT id, u, a FROM ob_idx ORDER BY u ASC, id ASC"
      else if qSub == 4 then "SELECT id, u, a FROM ob_idx ORDER BY u DESC, id DESC"
      else if qSub == 5 then "SELECT id, u, a FROM ob_idx ORDER BY u ASC NULLS LAST, id ASC"
      else if qSub == 6 then "SELECT id, u, a FROM ob_idx ORDER BY u DESC NULLS FIRST, id DESC"
      else "SELECT id, u, a FROM ob_idx ORDER BY u ASC, id ASC NULLS LAST"
    let seedSql :=
      if qSub == 4 || qSub == 5 then
        "INSERT INTO ob_idx VALUES (1, NULL, 10), (4, NULL, 40)"
      else
        "INSERT INTO ob_idx VALUES (1, NULL, 10), (4, NULL, 40), (5, 100, 50)"
    let midOps : Array RawStepOp :=
      if useMidIns then
        #[.prepare 1 "INSERT INTO ob_idx VALUES (2, NULL, 20)", .step 1, .finalize 1]
      else
        #[ .prepare 1 "BEGIN", .step 1, .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS ob_rb(x INT)", .step 1, .finalize 1
         , .prepare 1 "ROLLBACK", .step 1, .finalize 1 ]
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS ob_idx(id INTEGER PRIMARY KEY, u INT UNIQUE, a INT)"
       , .step 0, .finalize 0
       , .prepare 0 "DELETE FROM ob_idx", .step 0, .finalize 0
       , .prepare 0 seedSql, .step 0, .finalize 0
       , .prepare 0 qSql, .step 0 ] ++ midOps ++
      #[ .step 0, .step 0, .step 0, .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r5)
  else if pat == 22 then
    let (qSub, r4) := r3.nextNat 7
    let (useMidIns, r5) := r4.nextBool
    let qSql :=
      if qSub == 0 then "SELECT id, a1 FROM eq_ob WHERE a1 = 10 ORDER BY a1 DESC, id ASC"
      else if qSub == 1 then "SELECT id, a1 FROM eq_ob WHERE a1 = 10 ORDER BY a1 DESC"
      else if qSub == 2 then "SELECT id, a1 FROM eq_ob WHERE a1 IS NULL ORDER BY a1 DESC, id ASC"
      else if qSub == 3 then "SELECT id, u FROM eq_ob WHERE u IS NULL ORDER BY u DESC, id ASC"
      else if qSub == 4 then "SELECT id, a1, a2 FROM eq_ob WHERE a1 = 10 AND a2 = a1 ORDER BY a2 DESC, id ASC"
      else if qSub == 5 then "SELECT id, a1, r1 FROM eq_ob WHERE a1 = 10 AND r1 = a1 ORDER BY r1 DESC, id ASC"
      else "SELECT id, b1, b2 FROM eq_ob WHERE b1 = 10 AND b2 = b1 ORDER BY b2 DESC, id ASC"
    let midOps : Array RawStepOp :=
      if useMidIns then
        #[.prepare 1 "INSERT INTO eq_ob VALUES (2, NULL, 10, 10, 10, 10, 10)", .step 1, .finalize 1]
      else
        #[ .prepare 1 "BEGIN", .step 1, .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS eq_rb(x INT)", .step 1, .finalize 1
         , .prepare 1 "ROLLBACK", .step 1, .finalize 1 ]
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS eq_ob(id INTEGER PRIMARY KEY, u INT UNIQUE, a1 INT, a2 INT, r1 REAL, b1 BLOB, b2 BLOB)"
       , .step 0, .finalize 0
       , .prepare 0 "DELETE FROM eq_ob", .step 0, .finalize 0
       , .prepare 0 "INSERT INTO eq_ob VALUES (1, NULL, 10, 10, 10, 10, 10), (4, NULL, 10, 10, 10, 10, 10)"
       , .step 0, .finalize 0
       , .prepare 0 qSql, .step 0 ] ++ midOps ++
      #[ .step 0, .step 0, .step 0, .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r5)
  else if pat == 23 then
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS sc_nul(id INTEGER PRIMARY KEY, txt TEXT, bin BLOB)"
       , .step 0, .finalize 0
       , .prepare 0 "DELETE FROM sc_nul", .step 0, .finalize 0
       , .prepare 0 "INSERT INTO sc_nul VALUES (?, ?, ?)"
       , .bind 0 #[.int 1, .text "ab\x00cd", .bytes (ByteArray.mk #[0x41, 0x00, 0x42])]
       , .step 0, .finalize 0
       , .peerExec "INSERT INTO sc_nul VALUES (?, ?, ?)" #[.int 2, .text "\x00tail", .bytes (ByteArray.mk #[0, 1])]
       , .prepare 0 "SELECT id, txt, bin FROM sc_nul ORDER BY id ASC"
       , .step 0, .step 0, .step 0, .finalize 0 ]
    (.rawSession (.raw "file::memory:?cache=shared&mode=memory")
      { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r3)
  else if pat == 24 then
    let projChoices : Array String :=
      #["*", "id, u, u2, a", "id, u, u2", "id, u", "id", "u", "1"]
    let whereChoices : Array String :=
      #[ ""
       , " WHERE u IS NULL"
       , " WHERE u IS NOT NULL"
       , " WHERE a = 10"
       , " WHERE a IS NULL"
       , " WHERE id > 0"
       , " WHERE u = 100 OR u = 200"
       , " WHERE u = 100 OR u2 = 10"
       , " WHERE u > 150 OR u2 = 10"
       , " WHERE u IS NULL OR u2 = 20"
       , " WHERE u > 50 AND u < 300" ]
    let obItemChoices : Array String :=
      #[ "id ASC", "id DESC", "id ASC NULLS LAST", "id DESC NULLS FIRST"
       , "u ASC", "u DESC", "u ASC NULLS LAST", "u DESC NULLS FIRST"
       , "u2 ASC", "u2 DESC"
       , "a ASC", "a DESC" ]
    let (proj, r4) := chooseFrom projChoices r3
    let (wh, r5) := chooseFrom whereChoices r4
    let (obCnt, r6) := r5.nextNat 3
    let (obClause, r7) := Id.run do
      if obCnt == 0 then
        return ("", r6)
      else
        let mut cur := r6
        let mut items : List String := []
        for _ in List.range obCnt do
          let (it, rn) := chooseFrom obItemChoices cur
          cur := rn
          items := items ++ [it]
        return (" ORDER BY " ++ String.intercalate ", " items, cur)
    let (midKind, r8) := r7.nextNat 4
    let midOps : Array RawStepOp :=
      if midKind == 0 then
        #[.prepare 1 "INSERT INTO rq0 VALUES (2, NULL, 25, 10)", .step 1, .finalize 1]
      else if midKind == 1 then
        #[.prepare 1 "INSERT INTO rq0 VALUES (0, 150, 5, 10)", .step 1, .finalize 1]
      else if midKind == 2 then
        #[ .prepare 1 "DELETE FROM rq0 WHERE id = 5", .step 1, .finalize 1
         , .prepare 1 "INSERT INTO rq0 VALUES (6, 100, 60, 10)", .step 1, .finalize 1 ]
      else
        #[ .prepare 1 "BEGIN", .step 1, .finalize 1
         , .prepare 1 "CREATE TABLE IF NOT EXISTS rq_rb(x INT)", .step 1, .finalize 1
         , .prepare 1 "ROLLBACK", .step 1, .finalize 1 ]
    let qSql := "SELECT " ++ proj ++ " FROM rq0" ++ wh ++ obClause
    let ops : Array RawStepOp :=
      #[ .prepare 0 "CREATE TABLE IF NOT EXISTS rq0(id INTEGER PRIMARY KEY, u INT UNIQUE, u2 INT UNIQUE, a INT)"
       , .step 0, .finalize 0
       , .prepare 0 "DELETE FROM rq0", .step 0, .finalize 0
       , .prepare 0 "INSERT INTO rq0 VALUES (1, NULL, 10, 10), (3, 200, 20, 20), (4, NULL, 30, 10), (5, 100, 40, 10)"
       , .step 0, .finalize 0
       , .prepare 0 qSql, .step 0 ] ++ midOps ++
      #[ .step 0, .step 0, .step 0, .step 0, .finalize 0 ]
    (.rawSession .memory { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r8)
  else if pat == 25 then
    let (useSlot1, r4) := r3.nextBool
    let liveSlot := if useSlot1 then 1 else 0
    let cbTgt : TargetSpec := if tChoice % 2 == 0 then .memory else .db1
    let ops : Array RawStepOp :=
      #[ .prepare liveSlot "CREATE TABLE IF NOT EXISTS cb0(id INTEGER PRIMARY KEY, x INT)"
       , .step liveSlot
       , .finalize liveSlot
       , .prepare liveSlot "INSERT INTO cb0 VALUES (1, 10), (2, 20)"
       , .step liveSlot
       , .finalize liveSlot
       , .prepare liveSlot "SELECT id, x FROM cb0 ORDER BY id ASC"
       , .step liveSlot ]
    (.rawSession cbTgt { walMode := false, busyTimeoutMs := 0, foreignKeys := true } ops, r4)
  else
    let (cnt, r4) := r3.nextRange 2 7
    let (ops, r5) := Id.run do
      let mut cur := r4
      let mut acc := Array.mkEmpty cnt
      for _ in List.range cnt do
        let (kind, rx) := cur.nextNat 10
        let (slot, ry) := rx.nextNat 2
        if kind < 3 then
          let ((sql, _), rz) := chooseFrom rawProbeSqls ry
          cur := rz
          acc := acc.push (.prepare slot sql)
        else if kind < 5 then
          let (arity, rz) := ry.nextRange 0 4
          let (ps, rw) := genValues arity rz
          cur := rw
          acc := acc.push (.bind slot ps)
        else if kind < 8 then
          cur := ry
          acc := acc.push (.step slot)
        else if kind == 8 then
          cur := ry
          acc := acc.push (.finalize slot)
        else
          let ((sql, ar), rz) := chooseFrom rawProbeSqls ry
          let (ps, rw) := genValues ar rz
          cur := rw
          acc := acc.push (.peerExec sql ps)
      return (acc, cur)
    (.rawSession tgt cfg ops, r5)

/-- Generate one top-level `TopAction`. -/
def genTopAction (r : Rng) : TopAction × Rng :=
  let (tag, r1) := r.nextNat 100
  if tag < 7 then
    let (cfg, r2) := genOpenConfig r1
    (.validateConfig cfg, r2)
  else if tag < 12 then
    let (err, r2) := genRawError r1
    (.mapRawError err, r2)
  else if tag < 20 then
    let (ref, r2) := genClosedHandleRef r1
    let (op, r3) := genLeafSqlOp r2
    (.closedHandleOp ref op, r3)
  else if tag < 25 then
    let (ref, r2) := genClosedHandleRef r1
    let (op, r3) := genLeafSqlOp r2
    let (em, r4) := genExitMode r3
    (.closedHandleTx ref #[op] em, r4)
  else if tag < 36 then
    genRawSession r1
  else if tag < 46 then
    let (useDb1, r2) := r1.nextBool
    let tgt := if useDb1 then TargetSpec.db1 else TargetSpec.db0
    let (vTag, r3) := r2.nextNat 16
    let (kVal, r4) := r3.nextNat 1000
    let (walB, r5a) := r4.nextBool
    let (fkB, r5b) := r5a.nextBool
    let writeSql := "INSERT INTO t0_busy(id, x) VALUES (NULL, ?)"
    let (em, r5) := genExitMode r5b
    let ops : Array DbConnOp :=
      if vTag == 3 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_busy(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "BEGIN IMMEDIATE" #[])
         , .leaf (.exec writeSql #[.int (Int64.ofNat kVal)])
         , .nestedWithDb tgt { walMode := true, busyTimeoutMs := 0 } #[] .returnOk
         , .leaf (.exec "ROLLBACK" #[]) ]
      else if vTag == 4 || vTag == 15 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_con(id INTEGER PRIMARY KEY, u INT NOT NULL UNIQUE, pid INT REFERENCES t0_con(id)) STRICT" #[])
         , .leaf (.exec "INSERT INTO t0_con(id, u, pid) VALUES (1, 10, NULL)" #[])
         , .leaf (.exec "INSERT INTO t0_con(id, u, pid) VALUES (1, 20, NULL)" #[])
         , .leaf (.query "INSERT INTO t0_con(id, u, pid) VALUES (1, 20, NULL)" #[])
         , .leaf (.queryOne "INSERT INTO t0_con(id, u, pid) VALUES (1, 20, NULL)" #[])
         , .leaf (.exec "INSERT INTO t0_con(id, u, pid) VALUES (2, NULL, NULL)" #[])
         , .leaf (.exec "INSERT INTO t0_con(id, u, pid) VALUES (3, 30, 999)" #[])
         , .leaf (.exec "INSERT INTO t0_con(id, u, pid) VALUES (4, 'bad_strict', NULL)" #[])
         , .leaf (.queryOne "SELECT id FROM t0_con WHERE id = 999999" #[])
         , .leaf (.exec "DELETE FROM t0_con WHERE id = 1" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_mm(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "INSERT INTO t0_mm(id, x) VALUES ('bad_ipk', 1)" #[]) ]
      else if vTag == 5 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_pend(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "BEGIN IMMEDIATE" #[])
         , .leaf (.exec "INSERT INTO t0_pend(id, x) VALUES (NULL, ?)" #[.int (Int64.ofNat kVal)])
         , .nestedWithDb tgt { walMode := false, busyTimeoutMs := 0 } #[
             (true, .exec "BEGIN DEFERRED" #[]),
             (true, .query "SELECT x FROM t0_pend" #[]),
             (false, .exec "COMMIT" #[]),
             (true, .exec "COMMIT" #[]),
             (false, .exec "COMMIT" #[])
           ] .returnOk
         , .nestedWithDb tgt { walMode := false, readOnly := true, createIfMissing := false, busyTimeoutMs := 0 } #[
             (true, .exec "BEGIN DEFERRED" #[]),
             (true, .exec "BEGIN IMMEDIATE" #[]),
             (true, .exec "ROLLBACK" #[])
           ] .returnOk ]
      else if vTag == 6 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_auto(id INTEGER PRIMARY KEY AUTOINCREMENT, x INT)" #[])
         , .leaf (.exec "INSERT INTO t0_auto(id, x) VALUES (9223372036854775807, 1)" #[])
         , .leaf (.exec "BEGIN IMMEDIATE" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS ghost_tbl(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "INSERT INTO t0_auto(x) VALUES (2), (3)" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS ghost_tbl(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "COMMIT" #[]) ]
      else if vTag == 7 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_sc(id INTEGER PRIMARY KEY, x INT)" #[])
         , .nestedWithDb tgt { walMode := false, readOnly := true, createIfMissing := false } #[
             (true, .query "SELECT id FROM t0_sc" #[]),
             (false, .exec "CREATE TABLE t0_sc_b(x INT)" #[]),
             (true, .exec "BEGIN DEFERRED" #[]),
             (true, .exec "ROLLBACK" #[]),
             (true, .exec "INSERT INTO t0_sc(id, x) VALUES (1, 1)" #[]),
             (true, .exec "CREATE TABLE IF NOT EXISTS t0_sc_b(x INT)" #[])
           ] .returnOk ]
      else if vTag == 8 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_sfk_max(id INTEGER PRIMARY KEY, pid INT REFERENCES t_sfk_max(id))" #[])
         , .leaf (.exec "INSERT INTO t_sfk_max(id, pid) VALUES (9223372036854775807, 9223372036854775807)" #[])
         , .leaf (.exec "INSERT INTO t_sfk_max(id, pid) VALUES (NULL, 1000000000001)" #[]) ]
      else if vTag == 9 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_sref2(id INT UNIQUE, pid TEXT REFERENCES t_sref2(id), v INT)" #[])
         , .leaf (.exec "INSERT INTO t_sref2(id, pid, v) VALUES (1, '1', 10), (2, '2', 20)" #[])
         , .leaf (.exec "UPDATE t_sref2 SET id = 20, pid = '20', v = 30 WHERE id = 1" #[]) ]
      else if vTag == 10 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_dupu(pk INT PRIMARY KEY, u INT UNIQUE)" #[])
         , .leaf (.exec "INSERT INTO t_dupu(pk, u) VALUES (1, 10), (2, 20)" #[])
         , .leaf (.exec "INSERT INTO t_dupu(pk, u) VALUES (1, 10)" #[])
         , .leaf (.exec "UPDATE t_dupu SET pk = 3, u = 20 WHERE pk <= 2" #[]) ]
      else if vTag == 11 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_aff_s(k INT PRIMARY KEY, pid TEXT REFERENCES t_aff_s(k), v INT)" #[])
         , .leaf (.exec "INSERT INTO t_aff_s(k, pid, v) VALUES ('1', 2, 10), ('02', 1, 20)" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS t_aff_p2(k TEXT PRIMARY KEY, v INT)" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS t_aff_c2(id INTEGER PRIMARY KEY, pid INT REFERENCES t_aff_p2(k))" #[])
         , .leaf (.exec "INSERT INTO t_aff_p2(k, v) VALUES ('1', 100)" #[])
         , .leaf (.exec "INSERT INTO t_aff_c2(id, pid) VALUES (1, 1)" #[])
         , .leaf (.exec "UPDATE t_aff_p2 SET k = '01' WHERE k = '1'" #[]) ]
      else if vTag == 12 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_ipk_p(id INTEGER PRIMARY KEY)" #[])
         , .leaf (.exec "CREATE TABLE IF NOT EXISTS t_ipk_c(id INTEGER PRIMARY KEY, pid TEXT REFERENCES t_ipk_p(id), spid TEXT REFERENCES t_ipk_c(id))" #[])
         , .leaf (.exec "INSERT INTO t_ipk_p(id) VALUES (-9223372036854775808)" #[])
         , .leaf (.exec "INSERT INTO t_ipk_c(id, pid, spid) VALUES (1, '-9223372036854775808.0', NULL)" #[])
         , .leaf (.exec "INSERT INTO t_ipk_c(id, pid, spid) VALUES (2, '-9223372036854775809', NULL), (3, '-9223372036854775808', NULL)" #[])
         , .leaf (.exec "INSERT INTO t_ipk_c(id, pid, spid) VALUES (-9223372036854775808, '-9223372036854775808', '-9223372036854775808.0')" #[]) ]
      else if vTag == 13 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t_chain_s(id INTEGER PRIMARY KEY, a INT, b TEXT, ut TEXT UNIQUE)" #[])
         , .leaf (.exec "DELETE FROM t_chain_s" #[])
         , .leaf (.exec "INSERT INTO t_chain_s VALUES (1, 10, '10', '10'), (2, 10, '010', '010')" #[])
         , .leaf (.query "SELECT id, ut FROM t_chain_s WHERE a = 10 AND b = a AND ut = b" #[])
         , .leaf (.queryOne "SELECT id, ut FROM t_chain_s WHERE a = 10 AND b = a AND ut = b ORDER BY id DESC" #[]) ]
      else if vTag == 14 then
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_txend(id INTEGER PRIMARY KEY, x INT)" #[])
         , .withTx #[ .exec "INSERT INTO t0_txend(id, x) VALUES (NULL, ?)" #[.int (Int64.ofNat kVal)]
                    , .exec "COMMIT" #[] ]
             (.returnCallerErr { kind := .invalidInput, message := "caller abort after commit" })
         , .withTx #[ .exec "INSERT INTO t0_txend(id, x) VALUES (NULL, ?)" #[.int (Int64.ofNat kVal)]
                    , .exec "ROLLBACK" #[] ]
             (.returnCallerErr { kind := .constraint, message := "caller abort after rollback" }) ]
      else
        let kv : SqliteValue := .int (Int64.ofNat kVal)
        let busyDualOps : Array (Bool × LeafSqlOp) :=
          #[ (true, .query writeSql #[kv])
           , (true, .queryOne writeSql #[kv])
           , (true, .exec writeSql #[kv]) ]
        #[ .leaf (.exec "CREATE TABLE IF NOT EXISTS t0_busy(id INTEGER PRIMARY KEY, x INT)" #[])
         , .leaf (.exec "BEGIN IMMEDIATE" #[])
         , .leaf (.exec writeSql #[kv])
         , .nestedWithDb tgt { walMode := false, busyTimeoutMs := 0 } busyDualOps .returnOk
         , .nestedWithDb tgt { walMode := true, busyTimeoutMs := 0 } #[] .returnOk
         , .leaf (.exec "ROLLBACK" #[]) ]
    let sessCfg := if vTag == 6 then { walMode := walB, busyTimeoutMs := 0, foreignKeys := fkB }
                   else { walMode := false, busyTimeoutMs := 0, foreignKeys := true }
    (.withDbSession tgt sessCfg ops em, r5)
  else
    let (tgt, r2) := genTargetSpec r1
    let (cfgValid, r3) := r2.chance 4 5
    let (cfg, r4) := if cfgValid then genValidOpenConfig r3 else genSessionOpenConfig r3
    let (cnt, r5) := r4.nextRange 1 8
    let (ops, r6) := Id.run do
      let mut cur := r5
      let mut acc := Array.mkEmpty cnt
      for _ in List.range cnt do
        let (op, nxt) := genDbConnOp cur
        cur := nxt
        acc := acc.push op
      return (acc, cur)
    let (em, r7) := genExitMode r6
    (.withDbSession tgt cfg ops em, r7)

private def genCrossSessionFkPair (r : Rng) : Array TopAction × Rng :=
  let (useDb1, r1) := r.nextBool
  let (wal, r2) := r1.nextBool
  let (v1, r3) := genValue r2
  let (v2, r4) := genValue r3
  let tgt := if useDb1 then TargetSpec.db1 else TargetSpec.db0
  let s1 := TopAction.withDbSession tgt { walMode := wal, foreignKeys := false } #[
    .leaf (.exec "CREATE TABLE IF NOT EXISTS fk_p(id INTEGER PRIMARY KEY, tag TEXT)" #[]),
    .leaf (.exec "CREATE TABLE IF NOT EXISTS fk_c(id INTEGER PRIMARY KEY, pid INT REFERENCES fk_p(id), tag TEXT)" #[]),
    .leaf (.exec "CREATE TABLE IF NOT EXISTS fk_self_u(id INTEGER PRIMARY KEY, u INT UNIQUE, pid INT REFERENCES fk_self_u(u), tag TEXT)" #[]),
    .leaf (.exec "CREATE TABLE IF NOT EXISTS fk_self_bad(id INTEGER PRIMARY KEY, bad INT, pid INT REFERENCES fk_self_bad(bad), tag TEXT)" #[]),
    .leaf (.exec "INSERT INTO fk_p(id, tag) VALUES (1, ?), (2, ?)" #[.text "p1", .text "p2"]),
    .leaf (.exec "INSERT INTO fk_p(id, tag) VALUES ('bad_ipk', 'mm')" #[]),
    .leaf (.exec "INSERT INTO fk_c(id, pid, tag) VALUES (10, 999, ?), (11, 1, ?)" #[.text "broken", .text "ok"]),
    .leaf (.exec "INSERT INTO fk_self_u(id, u, pid, tag) VALUES (1, 10, 999, 'orphan')" #[]),
    .leaf (.exec "INSERT INTO fk_self_bad(id, bad, pid, tag) VALUES (1, 10, 999, 'badschema')" #[])
  ] .returnOk
  let s2 := TopAction.withDbSession tgt { walMode := wal, createIfMissing := false, foreignKeys := true } #[
    .leaf (.exec "UPDATE fk_p SET tag = ? WHERE id = 1" #[v1]),
    .leaf (.exec "UPDATE fk_p SET id = 3 WHERE id = 1" #[]),
    .leaf (.exec "UPDATE fk_c SET tag = ? WHERE id = 10" #[v2]),
    .leaf (.exec "UPDATE fk_c SET pid = ? WHERE id = 10" #[.int 2]),
    .leaf (.exec "UPDATE fk_self_u SET tag = ? WHERE id = 1" #[v1]),
    .leaf (.exec "UPDATE fk_self_u SET id = 2 WHERE id = 1" #[]),
    .leaf (.exec "UPDATE fk_self_u SET u = 20 WHERE id = 2" #[]),
    .leaf (.exec "UPDATE fk_self_bad SET tag = ? WHERE id = 1" #[v2]),
    .leaf (.exec "DELETE FROM fk_p WHERE id = 2" #[]),
    .leaf (.exec "DELETE FROM fk_c WHERE id = 11" #[])
  ] .returnOk
  (#[s1, s2], r4)

/-- Generate a full multi-session `SqliteEpisode`. -/
def genEpisode (r : Rng) : SqliteEpisode × Rng :=
  let (len, r1) := r.nextRange 4 9
  let (withCrossFk, r2) := r1.chance 1 8
  let (base, r3) :=
    if withCrossFk then genCrossSessionFkPair r2
    else (#[], r2)
  Id.run do
    let mut cur := r3
    let mut acc := base
    for _ in List.range len do
      let (act, nxt) := genTopAction cur
      cur := nxt
      acc := acc.push act
    return (acc, cur)

end Fuzz.Sqlite.Gen
