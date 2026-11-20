import LeanSwe.Sqlite.Model
import LeanSwe.Sqlite.SpecTests

namespace LeanSwe.Sqlite.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite

private theorem mt_state_bind_step {S α β : Type} {f : StateM S α} {k : α → StateM S β}
    {s0 s1 : S} {a : α} (hf : f s0 = (a, s1)) :
    StateT.bind f k s0 = k a s1 := by
  simp [StateT.bind, Bind.bind, hf]

private theorem mt_do_bind {S α β : Type} {f : StateM S α} {k : α → StateM S β}
    {s0 s1 : S} {a : α} (hf : f s0 = (a, s1)) :
    (f >>= k) s0 = k a s1 := by
  change (match f s0 with | (a', s') => k a' s') = k a s1
  rw [hf]

private theorem mt_state_tryFinally_step {S α β : Type} {x : StateM S α}
    {f : Option α → StateM S β} {s0 s1 s2 : S} {a : α} {b : β}
    (hx : x s0 = (a, s1)) (hf : f (some a) s1 = (b, s2)) :
    tryFinally' x f s0 = ((a, b), s2) := by
  change (let (a', s') := x s0; let (b', s'') := f (some a') s'; ((a', b'), s'')) = ((a, b), s2)
  rw [hx]
  dsimp only
  rw [hf]

private theorem mt_allPass_assert_bind {P : Prop} {k : Unit → AllPassRun Unit}
    {post : Unit → Prop} :
    (Bind.bind (NondetTest.assert (runner := AllPassRun) P) k) post =
      (P ∧ k () post) := rfl

private theorem mt_allPass_assert_end {P : Prop} :
    (NondetTest.assert (runner := AllPassRun) P) (fun _ => True) = (P ∧ True) := rfl

private def mtTblP0 : Model.TableData :=
  { name := "p"
    cols := [{ name := "id", colType := .integer, primaryKey := true },
             { name := "u", colType := .int, unique := true }]
    strict := true }

private def mtTblC0 : Model.TableData :=
  { name := "c"
    cols := [{ name := "id", colType := .integer, primaryKey := true },
             { name := "pid", colType := .int, notNull := true, references? := some ("p", "id") },
             { name := "tag", colType := .text }]
    strict := true }

private def mtTblP1 : Model.TableData :=
  { mtTblP0 with rows := [(1, #[.int 1, .int 10])] }

private def mtTblP2Rollback : Model.TableData :=
  { mtTblP0 with rows := [(1, #[.int 1, .int 10]), (2, #[.int 2, .int 20])] }

private def mtTblP3 : Model.TableData :=
  { mtTblP0 with rows := [(1, #[.int 1, .int 10]), (3, #[.int 3, .int 30])] }

private def mtTblP4 : Model.TableData :=
  { mtTblP0 with rows := [(1, #[.int 1, .int 10]), (3, #[.int 3, .int 31])] }

private def mtTblP5 : Model.TableData :=
  { mtTblP0 with rows := [(3, #[.int 3, .int 31])] }

private def mtTblC1 : Model.TableData :=
  { mtTblC0 with rows := [(4, #[.int 4, .int 1, .text "live"])] }

private def mtMem (nextStmt : UInt64) (epoch : Nat) (tbls : List (String × Model.TableData))
    (tx : Model.ConnTxState := .autocommit) (writeDirty : Bool := false)
    (cached? : Option (List String) := some ["p", "c"]) : Model.SqliteWorldState :=
  { nextDbId := 2
    nextStmtId := nextStmt
    conns := [{ id := 1, backing := .memory { tables := tbls } epoch,
                effectiveReadOnly := false, foreignKeys := true, tx := tx,
                writeDirty := writeDirty, schemaCache? := cached? }]
    mutGen := 2 * (nextStmt.toNat - 1) }

private def mtS1 : Model.SqliteWorldState := mtMem 1 0 [] .autocommit false none
private def mtS2 : Model.SqliteWorldState := mtMem 2 1 [("p", mtTblP0)] .autocommit false (some ["p"])
private def mtS3 : Model.SqliteWorldState := mtMem 3 2 [("p", mtTblP0), ("c", mtTblC0)]
private def mtS4 : Model.SqliteWorldState := mtMem 4 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS5 : Model.SqliteWorldState := mtMem 5 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS6 : Model.SqliteWorldState := mtMem 6 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS7 : Model.SqliteWorldState := mtMem 7 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS8 : Model.SqliteWorldState := mtMem 8 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS9 : Model.SqliteWorldState := mtMem 9 3 [("c", mtTblC0), ("p", mtTblP1)]
private def mtS10 : Model.SqliteWorldState := mtMem 10 4 [("p", mtTblP1), ("c", mtTblC1)]
private def mtS10a : Model.SqliteWorldState :=
  mtMem 11 4 [("p", mtTblP1), ("c", mtTblC1)] (.write 4 { tables := [("p", mtTblP1), ("c", mtTblC1)] })
private def mtS10b : Model.SqliteWorldState :=
  mtMem 12 4 [("p", mtTblP1), ("c", mtTblC1)] (.write 4 { tables := [("c", mtTblC1), ("p", mtTblP2Rollback)] }) true
private def mtS11 : Model.SqliteWorldState := mtMem 13 4 [("p", mtTblP1), ("c", mtTblC1)]
private def mtS11a : Model.SqliteWorldState :=
  mtMem 14 4 [("p", mtTblP1), ("c", mtTblC1)] (.write 4 { tables := [("p", mtTblP1), ("c", mtTblC1)] })
private def mtS11b : Model.SqliteWorldState :=
  mtMem 15 4 [("p", mtTblP1), ("c", mtTblC1)] (.write 4 { tables := [("c", mtTblC1), ("p", mtTblP3)] }) true
private def mtS12 : Model.SqliteWorldState := mtMem 16 5 [("c", mtTblC1), ("p", mtTblP3)]
private def mtS13 : Model.SqliteWorldState := mtMem 17 5 [("c", mtTblC1), ("p", mtTblP3)]
private def mtS14 : Model.SqliteWorldState := mtMem 18 5 [("c", mtTblC1), ("p", mtTblP3)]
private def mtS15 : Model.SqliteWorldState := mtMem 19 6 [("c", mtTblC1), ("p", mtTblP4)]
private def mtS16 : Model.SqliteWorldState := mtMem 20 7 [("p", mtTblP4), ("c", mtTblC0)]
private def mtS17 : Model.SqliteWorldState := mtMem 21 8 [("c", mtTblC0), ("p", mtTblP5)]
private def mtS18 : Model.SqliteWorldState := mtMem 22 8 [("c", mtTblC0), ("p", mtTblP5)]
private def mtS19 : Model.SqliteWorldState := { mtS18 with conns := [] }

private theorem mt_withDb_step {β : Type} (path : String) (cfg : OpenConfig)
    (body : DbHandle → StateM Model.SqliteWorldState (Except SqliteError β))
    {s0 sOpen s1 s2 : Model.SqliteWorldState} {db : DbHandle} {res : Except SqliteError β}
    (hVal : Model.validateConfigWith Model.modelRawOps.mapRawError cfg = .ok ())
    (hOpen : Model.modelRawOps.openDb path cfg s0 = (.ok db, sOpen))
    (hBody : body db sOpen = (res, s1))
    (hClose : Model.modelRawOps.closeDb db s1 = (.ok (), s2)) :
    Model.modelApi.withDb path cfg body s0 = (res, s2) := by
  dsimp only [Model.modelApi]
  rw [hVal]
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [hOpen]
  dsimp only
  rw [mt_state_bind_step (mt_state_tryFinally_step hBody hClose)]
  cases res <;> rfl

private theorem mt_h_open : Model.modelRawOps.openDb ":memory:" {} {} = (.ok { id := 1 }, mtS1) := rfl
private theorem mt_h_1 :
    Model.modelApi.exec { id := 1 } "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE) STRICT" #[] mtS1 =
      (.ok (), mtS2) := rfl
set_option maxRecDepth 2048 in
private theorem mt_h_2 :
    Model.modelApi.exec { id := 1 } "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES p(id), tag TEXT) STRICT" #[] mtS2 =
      (.ok (), mtS3) := rfl
private theorem mt_h_3 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 10] mtS3 =
      (.ok (), mtS4) := rfl
private theorem mt_h_4 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 20] mtS4 =
      (.error { kind := .constraint, sqliteCode := some 1555, message := "UNIQUE constraint failed: p" }, mtS5) := rfl
private theorem mt_h_5 :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 10] mtS5 =
      (.error { kind := .constraint, sqliteCode := some 2067, message := "UNIQUE constraint failed: p.u" }, mtS6) := rfl
private theorem mt_h_6 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 1, .int 99, .text "bad"] mtS6 =
      (.error { kind := .constraint, sqliteCode := some 787, message := "FOREIGN KEY constraint failed" }, mtS7) := rfl
private theorem mt_h_7 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty] mtS7 =
      (.error { kind := .constraint, sqliteCode := some 3091, message := "cannot store value in STRICT column tag" }, mtS8) := rfl
private theorem mt_h_8 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 3, .null, .text "ok"] mtS8 =
      (.error { kind := .constraint, sqliteCode := some 1299, message := "NOT NULL constraint failed: pid" }, mtS9) := rfl
private theorem mt_h_9 :
    Model.modelApi.exec { id := 1 } "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 4, .int 1, .text "live"] mtS9 =
      (.ok (), mtS10) := rfl

private theorem mt_h_10b :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20] mtS10a =
      (.ok (), mtS10b) := by with_unfolding_all rfl

private theorem mt_h_10 :
    Model.modelApi.withTransaction { id := 1 } (fun txDb => do
      let _ ← Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
      pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit)) mtS10 =
      (.error { kind := .constraint, message := "force rollback" }, mtS11) := by
  have hAct : (do
      let _ ← Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
      pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit))
      mtS10a =
      (.error { kind := .constraint, message := "force rollback" }, mtS10b) := by
    rw [mt_do_bind mt_h_10b]; rfl
  dsimp only [Model.modelApi] at hAct ⊢
  rw [mt_do_bind (s0 := mtS10) (s1 := mtS10a) (a := Except.ok ()) rfl]
  dsimp only
  rw [mt_do_bind (mt_state_tryFinally_step hAct (rfl : _ = (Except.ok (), mtS11)))]
  rfl

private theorem mt_h_11b :
    Model.modelApi.exec { id := 1 } "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30] mtS11a =
      (.ok (), mtS11b) := by with_unfolding_all rfl

private theorem mt_h_11 :
    Model.modelApi.withTransaction { id := 1 }
      (fun txDb => Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]) mtS11 =
      (.ok (), mtS12) := by
  have h11b := mt_h_11b
  dsimp only [Model.modelApi] at h11b ⊢
  rw [mt_do_bind (s0 := mtS11) (s1 := mtS11a) (a := Except.ok ()) rfl]
  dsimp only
  rw [mt_do_bind (mt_state_tryFinally_step h11b (rfl : _ = (Except.ok (), mtS12)))]
  rfl

private theorem mt_h_12 :
    Model.modelApi.query { id := 1 } "SELECT id, u FROM p WHERE id >= ? ORDER BY id DESC LIMIT ?" #[.int 1, .int 2] mtS12 =
      (.ok #[#[.int 3, .int 30], #[.int 1, .int 10]], mtS13) := by with_unfolding_all rfl
private theorem mt_h_13 :
    Model.modelApi.queryOne { id := 1 } "SELECT tag FROM c WHERE id = ?" #[.int 4] mtS13 =
      (.ok (some #[.text "live"]), mtS14) := by with_unfolding_all rfl
private theorem mt_h_14 :
    Model.modelApi.exec { id := 1 } "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3] mtS14 =
      (.ok (), mtS15) := by with_unfolding_all rfl
private theorem mt_h_15 :
    Model.modelApi.exec { id := 1 } "DELETE FROM c WHERE pid = ?" #[.int 1] mtS15 =
      (.ok (), mtS16) := by with_unfolding_all rfl
private theorem mt_h_16 :
    Model.modelApi.exec { id := 1 } "DELETE FROM p WHERE id = ?" #[.int 1] mtS16 =
      (.ok (), mtS17) := by with_unfolding_all rfl
private theorem mt_h_17 :
    Model.modelApi.query { id := 1 } "SELECT id, u FROM p ORDER BY id ASC" #[] mtS17 =
      (.ok #[#[.int 3, .int 31]], mtS18) := by with_unfolding_all rfl
private theorem mt_h_close :
    Model.modelRawOps.closeDb { id := 1 } mtS18 = (.ok (), mtS19) := rfl

private theorem mt_crud_run :
    (Model.modelApi.withDb ":memory:" {} fun db => do
      let _ ← Model.modelApi.exec db "CREATE TABLE p(id INTEGER PRIMARY KEY, u INT UNIQUE) STRICT" #[]
      let _ ← Model.modelApi.exec db "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INT NOT NULL REFERENCES p(id), tag TEXT) STRICT" #[]
      let _ ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 10]
      let dupPk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 1, .int 20]
      let dupUk ← Model.modelApi.exec db "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 10]
      let fkErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 1, .int 99, .text "bad"]
      let strictErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 2, .int 1, .bytes ByteArray.empty]
      let nullErr ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 3, .null, .text "ok"]
      let _ ← Model.modelApi.exec db "INSERT INTO c(id, pid, tag) VALUES (?, ?, ?)" #[.int 4, .int 1, .text "live"]
      let _ ← Model.modelApi.withTransaction db fun txDb => do
        let _ ← Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 2, .int 20]
        pure (Except.error { kind := .constraint, message := "force rollback" } : Except SqliteError Unit)
      let _ ← Model.modelApi.withTransaction db fun txDb =>
        Model.modelApi.exec txDb "INSERT INTO p(id, u) VALUES (?, ?)" #[.int 3, .int 30]
      let pRows ← Model.modelApi.query db "SELECT id, u FROM p WHERE id >= ? ORDER BY id DESC LIMIT ?" #[.int 1, .int 2]
      let cOne ← Model.modelApi.queryOne db "SELECT tag FROM c WHERE id = ?" #[.int 4]
      let _ ← Model.modelApi.exec db "UPDATE p SET u = ? WHERE id = ?" #[.int 31, .int 3]
      let _ ← Model.modelApi.exec db "DELETE FROM c WHERE pid = ?" #[.int 1]
      let _ ← Model.modelApi.exec db "DELETE FROM p WHERE id = ?" #[.int 1]
      let pAfter ← Model.modelApi.query db "SELECT id, u FROM p ORDER BY id ASC" #[]
      pure (Except.ok (dupPk, dupUk, fkErr, strictErr, nullErr, pRows, cOne, pAfter) : Except SqliteError _)) {} =
      (.ok (.error { kind := .constraint, sqliteCode := some 1555, message := "UNIQUE constraint failed: p" },
            .error { kind := .constraint, sqliteCode := some 2067, message := "UNIQUE constraint failed: p.u" },
            .error { kind := .constraint, sqliteCode := some 787, message := "FOREIGN KEY constraint failed" },
            .error { kind := .constraint, sqliteCode := some 3091, message := "cannot store value in STRICT column tag" },
            .error { kind := .constraint, sqliteCode := some 1299, message := "NOT NULL constraint failed: pid" },
            .ok #[#[.int 3, .int 30], #[.int 1, .int 10]],
            .ok (some #[.text "live"]),
            .ok #[#[.int 3, .int 31]]), mtS19) := by
  refine mt_withDb_step ":memory:" {} _ rfl mt_h_open (by
    rw [mt_do_bind mt_h_1]
    rw [mt_do_bind mt_h_2]
    rw [mt_do_bind mt_h_3]
    rw [mt_do_bind mt_h_4]
    rw [mt_do_bind mt_h_5]
    rw [mt_do_bind mt_h_6]
    rw [mt_do_bind mt_h_7]
    rw [mt_do_bind mt_h_8]
    rw [mt_do_bind mt_h_9]
    rw [mt_do_bind mt_h_10]
    rw [mt_do_bind mt_h_11]
    rw [mt_do_bind mt_h_12]
    rw [mt_do_bind mt_h_13]
    rw [mt_do_bind mt_h_14]
    rw [mt_do_bind mt_h_15]
    rw [mt_do_bind mt_h_16]
    rw [mt_do_bind mt_h_17]; rfl) mt_h_close

private def mtRoTbl : Model.TableData :=
  { name := "t", cols := [{ name := "x", colType := .int }], strict := false }
private def mtRoCat : Model.DbCatalog := { tables := [("t", mtRoTbl)] }
private def mtRoFile (epoch : Nat) (cat : Model.DbCatalog) : List (String × Model.FileNode) :=
  [("/tmp/a.db", .dbFile false false epoch cat)]
private def mtRoC1 (tx : Model.ConnTxState := .autocommit)
    (cached? : Option (List String) := some ["t"]) : Model.ConnState :=
  { id := 1, backing := .file "/tmp/a.db", effectiveReadOnly := false, foreignKeys := true,
    tx := tx, schemaCache? := cached? }
private def mtRoS0 : Model.SqliteWorldState := { existingDirs := ["/", "/tmp"] }
private def mtRoS1 : Model.SqliteWorldState :=
  { nextDbId := 2, nextStmtId := 1, existingDirs := ["/", "/tmp"], conns := [mtRoC1 .autocommit none], files := mtRoFile 0 {}, mutGen := 1 }
private def mtRoS2 : Model.SqliteWorldState :=
  { nextDbId := 2, nextStmtId := 2, existingDirs := ["/", "/tmp"], conns := [mtRoC1], files := mtRoFile 1 mtRoCat, mutGen := 4 }
private def mtRoS3 : Model.SqliteWorldState :=
  { nextDbId := 2, nextStmtId := 3, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat)], files := mtRoFile 1 mtRoCat, mutGen := 6 }
private def mtRoC2 (cached? : Option (List String) := none) : Model.ConnState :=
  { id := 2, backing := .file "/tmp/a.db", effectiveReadOnly := false, foreignKeys := true,
    schemaCache? := cached? }
private def mtRoS4 : Model.SqliteWorldState :=
  { nextDbId := 3, nextStmtId := 3, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat), mtRoC2], files := mtRoFile 1 mtRoCat, mutGen := 6 }
private def mtRoS5 : Model.SqliteWorldState :=
  { nextDbId := 3, nextStmtId := 4, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat), mtRoC2 (some ["t"])], files := mtRoFile 1 mtRoCat, mutGen := 7 }
private def mtRoS6 : Model.SqliteWorldState :=
  { nextDbId := 3, nextStmtId := 4, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat)], files := mtRoFile 1 mtRoCat, mutGen := 7 }
private def mtRoC3 (cached? : Option (List String) := none) : Model.ConnState :=
  { id := 3, backing := .file "/tmp/a.db", effectiveReadOnly := true, foreignKeys := true,
    schemaCache? := cached? }
private def mtRoS7 : Model.SqliteWorldState :=
  { nextDbId := 4, nextStmtId := 4, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat), mtRoC3], files := mtRoFile 1 mtRoCat, mutGen := 7 }
private def mtRoS8 : Model.SqliteWorldState :=
  { nextDbId := 4, nextStmtId := 5, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat), mtRoC3 (some ["t"])], files := mtRoFile 1 mtRoCat, mutGen := 8 }
private def mtRoS9 : Model.SqliteWorldState :=
  { nextDbId := 4, nextStmtId := 5, existingDirs := ["/", "/tmp"], conns := [mtRoC1 (.write 1 mtRoCat)], files := mtRoFile 1 mtRoCat, mutGen := 8 }
private def mtRoS10 : Model.SqliteWorldState :=
  { nextDbId := 4, nextStmtId := 6, existingDirs := ["/", "/tmp"], conns := [mtRoC1], files := mtRoFile 1 mtRoCat, mutGen := 10 }
private def mtRoS11 : Model.SqliteWorldState :=
  { nextDbId := 4, nextStmtId := 6, existingDirs := ["/", "/tmp"], files := mtRoFile 1 mtRoCat, mutGen := 10 }

private theorem mt_ro_open : Model.modelRawOps.openDb "/tmp/a.db" { walMode := false } mtRoS0 = (.ok { id := 1 }, mtRoS1) := rfl
private theorem mt_ro_h1 : Model.modelApi.exec { id := 1 } "CREATE TABLE t(x INT)" #[] mtRoS1 = (.ok (), mtRoS2) := rfl
private theorem mt_ro_h2 : Model.modelApi.exec { id := 1 } "BEGIN IMMEDIATE" #[] mtRoS2 = (.ok (), mtRoS3) := rfl
private theorem mt_ro_open2 : Model.modelRawOps.openDb "/tmp/a.db" { walMode := false, busyTimeoutMs := 0 } mtRoS3 = (.ok { id := 2 }, mtRoS4) := rfl
private theorem mt_ro_h3 :
    Model.modelApi.exec { id := 2 } "INSERT INTO t VALUES (?)" #[.int 1] mtRoS4 =
      (.error { kind := .busy, sqliteCode := some 5, message := "database is locked" }, mtRoS5) := rfl
private theorem mt_ro_close2 : Model.modelRawOps.closeDb { id := 2 } mtRoS5 = (.ok (), mtRoS6) := rfl
private theorem mt_ro_open3 : Model.modelRawOps.openDb "/tmp/a.db" { readOnly := true, createIfMissing := false, walMode := false } mtRoS6 = (.ok { id := 3 }, mtRoS7) := rfl
private theorem mt_ro_h4 :
    Model.modelApi.exec { id := 3 } "INSERT INTO t VALUES (?)" #[.int 2] mtRoS7 =
      (.error { kind := .ioError, sqliteCode := some 8, message := "attempt to write a readonly database" }, mtRoS8) := rfl
private theorem mt_ro_close3 : Model.modelRawOps.closeDb { id := 3 } mtRoS8 = (.ok (), mtRoS9) := rfl
private theorem mt_ro_h5 : Model.modelApi.exec { id := 1 } "ROLLBACK" #[] mtRoS9 = (.ok (), mtRoS10) := rfl
private theorem mt_ro_close1 : Model.modelRawOps.closeDb { id := 1 } mtRoS10 = (.ok (), mtRoS11) := rfl

private theorem mt_ro_run :
    (Model.modelApi.withDb "/tmp/a.db" { walMode := false } fun db1 => do
      let _ ← Model.modelApi.exec db1 "CREATE TABLE t(x INT)" #[]
      let _ ← Model.modelApi.exec db1 "BEGIN IMMEDIATE" #[]
      let busyRes ← Model.modelApi.withDb "/tmp/a.db" { walMode := false, busyTimeoutMs := 0 } fun db2 =>
        Model.modelApi.exec db2 "INSERT INTO t VALUES (?)" #[.int 1]
      let roRes ← Model.modelApi.withDb "/tmp/a.db" { readOnly := true, createIfMissing := false, walMode := false } fun dbRo =>
        Model.modelApi.exec dbRo "INSERT INTO t VALUES (?)" #[.int 2]
      let _ ← Model.modelApi.exec db1 "ROLLBACK" #[]
      pure (Except.ok (busyRes, roRes) : Except SqliteError _)) { existingDirs := ["/", "/tmp"] } =
      (.ok (.error { kind := .busy, sqliteCode := some 5, message := "database is locked" },
            .error { kind := .ioError, sqliteCode := some 8, message := "attempt to write a readonly database" }),
       mtRoS11) := by
  refine mt_withDb_step "/tmp/a.db" { walMode := false } _ rfl mt_ro_open (by
    rw [mt_do_bind mt_ro_h1]
    rw [mt_do_bind mt_ro_h2]
    rw [mt_do_bind (mt_withDb_step "/tmp/a.db" { walMode := false, busyTimeoutMs := 0 } _ rfl mt_ro_open2 mt_ro_h3 mt_ro_close2)]
    rw [mt_do_bind (mt_withDb_step "/tmp/a.db" { readOnly := true, createIfMissing := false, walMode := false } _ rfl mt_ro_open3 mt_ro_h4 mt_ro_close3)]
    rw [mt_do_bind mt_ro_h5]; rfl) mt_ro_close1

private theorem mt_closed_run :
    Model.modelApi.exec { id := 999 } "SELECT 1" #[] {} =
      (.error { kind := .misuse, sqliteCode := some 21, message := "invalid or closed database handle" }, {}) := rfl

/-- Proof of `test_sqlite_modelApi_relationalCrudConstraintsAndRollback` for `Model.modelApi`. -/
theorem proof_sqlite_modelApi_relationalCrudConstraintsAndRollback :
    AllPass (test_sqlite_modelApi_relationalCrudConstraintsAndRollback Model.modelApi) := by
  unfold test_sqlite_modelApi_relationalCrudConstraintsAndRollback AllPass
    modelApiCrudBlock modelApiRoBusyBlock
  simp only [mt_allPass_assert_bind, mt_allPass_assert_end]
  dsimp only [StateT.run]
  rw [mt_crud_run, mt_ro_run, mt_closed_run]
  exact ⟨by decide, by decide, by decide, by decide, ⟨_, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_sqlite_modelApi_relationalCrudConstraintsAndRollback`. -/
theorem reach_sqlite_modelApi_relationalCrudConstraintsAndRollback :
    CanReach (test_sqlite_modelApi_relationalCrudConstraintsAndRollback Model.modelApi) :=
  proof_sqlite_modelApi_relationalCrudConstraintsAndRollback

end LeanSwe.Sqlite.Proofs
