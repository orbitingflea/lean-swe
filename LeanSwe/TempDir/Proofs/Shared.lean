import LeanSwe.TempDir.Interface
import LeanSwe.TempDir.SpecTests
/-!
Shared mock filesystem/lock/env/uuid/time model and core proof infrastructure
for `LeanSwe.TempDir` specifications.
-/
namespace LeanSwe.TempDir.Proofs
open Core Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)
/-- Entry kind stored in the `TempDirMockState` filesystem model. -/
inductive MockNode where
  /-- Directory node. -/ | dir (modifiedSec : Int) (mode : Nat)
  /-- Regular file node. -/ | file (inode : Nat) (content : String) (modifiedSec : Int) (mode : Nat)
  /-- Symlink node. -/ | symlink (target : String) (modifiedSec : Int)
  deriving Repr, DecidableEq
/-- Pure mock state backing `TempDir` stateful specifications. -/
structure TempDirMockState where
  /-- Filesystem path-to-node association list. -/ nodes : List (String × MockNode) := [("/tmp", .dir 0 0o755)]
  /-- Active `(inode, mode)` lock entries. -/ locks : List (Nat × LockMode) := []
  /-- Next fresh inode counter. -/ nextInode : Nat := 1
  /-- Optional `TMPDIR` value. -/ tmpdir : Option String := none
  /-- Current mock epoch timestamp in seconds. -/ nowSec : Int := 0
  /-- Next deterministic UUID counter. -/ nextUuid : Nat := 1
  deriving Repr
private def trimTrailingSlashesRev : List Char → List Char
  | [] => [] | ['/'] => ['/'] | '/' :: rest => trimTrailingSlashesRev rest | cs => cs
private def trimSlashChars (cs : List Char) : List Char := (trimTrailingSlashesRev cs.reverse).reverse
/-- Normalize trailing slashes on a mock path. -/
def normKey (p : String) : String := String.ofList (trimSlashChars p.toList)
/-- Join two mock paths. -/
def mockJoin (a b : String) : String :=
  let na := normKey a; if na.isEmpty then b else if na == "/" then "/" ++ b else na ++ "/" ++ b
private def splitLastSlashRev : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c == '/' then some (cs.reverse, []) else match splitLastSlashRev cs with | none => none | some (par, base) => some (par, base ++ [c])
/-- Split a non-root normalized path into `(parent, basename)`. -/
def splitParentChild (p : String) : Option (String × String) :=
  let np := normKey p; if np == "/" || np.isEmpty then none else match splitLastSlashRev np.toList.reverse with
    | none => none | some (parCs, baseCs) => let par := if parCs.isEmpty then "/" else String.ofList parCs; let base := String.ofList baseCs
      if base.isEmpty then none else some (par, base)
/-- Convert a `MockNode` to `FileStat`. -/
def mockNodeStat : MockNode → FileStat
  | .dir t m => { kind := .dir, byteSize := 0, mode := m, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .file _ c t m => { kind := .file, byteSize := c.length, mode := m, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ t => { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
/-- Look up the first matching normalized key in `nodes`. -/
def lookupNode (nodes : List (String × MockNode)) (p : String) : Option MockNode :=
  (nodes.find? (fun e => normKey e.1 == normKey p)).map Prod.snd
/-- Pure `lstat` evaluation. -/
def mockLstatPure (s : TempDirMockState) (p : String) : Except FsError FileStat :=
  match lookupNode s.nodes p with
  | none => .error { kind := .notFound, path := some p, message := "not found" }
  | some node => .ok (mockNodeStat node)
/-- Pure `stat` evaluation. -/
def mockStatPure (s : TempDirMockState) (p : String) : Except FsError FileStat := mockLstatPure s p
/-- Write+execute bits check. -/
def hasWx (st : FileStat) : Bool := st.kind == .dir && (st.mode / 128) % 2 == 1 && (st.mode / 64) % 2 == 1
/-- Read+execute bits check. -/
def hasRx (st : FileStat) : Bool := st.kind == .dir && (st.mode / 256) % 2 == 1 && (st.mode / 64) % 2 == 1
/-- Immediate valid child name of `dir` for `full`. -/
def mockParentChild (dir full : String) : Option String :=
  let nd := normKey dir; let nf := normKey full; let pref := if nd.isEmpty then "" else if nd == "/" then "/" else nd ++ "/"
  if pref.toList.isPrefixOf nf.toList then
    let rest := String.ofList (nf.toList.drop pref.length)
    if !rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList) then some rest else none
  else none
private def eraseDupStringsAux (seen : List String) : List String → List String
  | [] => [] | x :: xs => if x ∈ seen then eraseDupStringsAux seen xs else x :: eraseDupStringsAux (x :: seen) xs
/-- Deduplicate strings preserving first occurrence. -/
def eraseDupStrings (xs : List String) : List String := eraseDupStringsAux [] xs
/-- Check lock conflict on `(ino, m)`. -/
def mockHasConflict (locks : List (Nat × LockMode)) (ino : Nat) (m : LockMode) : Bool :=
  locks.any fun (li, lm) => li == ino && (m == .exclusive || lm == .exclusive)
/-- Remove first matching `(ino, m)` lock entry. -/
def mockRemoveFirstLock (ino : Nat) (m : LockMode) : List (Nat × LockMode) → List (Nat × LockMode)
  | [] => [] | x :: xs => if x == (ino, m) then xs else x :: mockRemoveFirstLock ino m xs
/-- Allocate fresh inode above `s.nextInode` and active locks. -/
def freshInode (s : TempDirMockState) : Nat := s.locks.foldl (fun m l => Nat.max m (l.1 + 1)) s.nextInode
/-- True iff `key` equals `prefixDir` or lies beneath it. -/
def underDir (prefixDir key : String) : Bool :=
  let np := normKey prefixDir; let nk := normKey key; nk == np || (if np == "/" then "/" else np ++ "/").toList.isPrefixOf nk.toList
/-- Pure recursive directory removal. -/
def mockRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempDirMockState (Except FsError Unit) := do
  let s ← get; let rp := normKey p
  match lookupNode s.nodes rp with
  | none => if ignoreMissing then return .ok () else return .error { kind := .notFound, path := some p, message := "not found" }
  | some (.dir _ _) => set { s with nodes := s.nodes.filter (fun e => !underDir rp e.1) }; return .ok ()
  | some _ => return .error { kind := .notADirectory, path := some p, message := "not a dir" }
/-- Deterministic mock UUIDv4 from `n`. -/
def mockUuidOfNat (n : Nat) : Uuid :=
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, UInt8.ofNat ((n / 256) % 256), UInt8.ofNat (n % 256)] }
private def mockHexByte (b : UInt8) : String :=
  let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]
/-- Format mock UUID as canonical lowercase hex string. -/
def mockUuidToString (u : Uuid) : String :=
  "00000000-0000-4000-8000-00000000" ++ mockHexByte (u.bytes[14]?.getD 0) ++ mockHexByte (u.bytes[15]?.getD 0)
/-- Polymorphic lock acquisition helper. -/
def mockLockCore {m : Type → Type} {α β : Type} [Monad m] [MonadFinally m] [MonadStateOf TempDirMockState m]
    (p : String) (mode : LockMode) (createIfMissing : Bool) (onConflict : m (Except FsError β))
    (wrap : Except FsError α → Except FsError β) (action : m (Except FsError α)) : m (Except FsError β) := do
  let s ← get; let rp := normKey p
  match lookupNode s.nodes rp with
  | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
  | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
  | some (.file ino _ _ _) =>
    if mockHasConflict s.locks ino mode then onConflict
    else set { s with locks := (ino, mode) :: s.locks }; let (r, _) ← tryFinally' action fun _ => modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }; return wrap r
  | none =>
    if !createIfMissing then return .error { kind := .notFound, path := some p, message := "not found" }
    let ino := freshInode s; set { s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 }
    let (r, _) ← tryFinally' action fun _ => modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }; return wrap r
private def writeFileMock (p c : String) : StateM TempDirMockState (Except FsError Unit) := do
  let s ← get; let rp := normKey p; let ino := freshInode s
  set { s with nodes := (rp, .file ino c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != rp), nextInode := ino + 1 }; return .ok ()
/-- Mock `FsApiM` over `StateM TempDirMockState`. -/
def mockFs : FsApiM (StateM TempDirMockState) :=
  { join := mockJoin, joinMany := fun ps => ps.foldl mockJoin "", normPath := normKey
    parent := fun p => (splitParentChild p).map Prod.fst, name := fun p => (splitParentChild p).map Prod.snd
    stem := fun _ => none, suffix := fun _ => "", suffixes := fun _ => #[], withName := fun p _ => .ok p, withSuffix := fun p _ => .ok p
    isAbsolute := fun p => p.startsWith "/", relativeTo := fun p _ => .ok p, mapRawError := fun _ => { kind := .ioError, message := "raw" }
    readText := fun p => do match lookupNode (← get).nodes (normKey p) with
      | some (.file _ c _ _) => return .ok c | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
      | _ => return .error { kind := .notFound, path := some p, message := "not found" }
    writeText := writeFileMock, appendText := writeFileMock, readBytes := fun _ => pure (.ok ByteArray.empty), writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ()), atomicWriteText := fun _ _ => pure (.ok ()), touch := fun p _ => writeFileMock p ""
    mkdir := fun p _ existOk => do
      let s ← get; match splitParentChild p with
      | none => return .error { kind := .alreadyExists, path := some p, message := "root" }
      | some (par, base) => match lookupNode s.nodes par with
        | none => return .error { kind := .notFound, path := some par, message := "parent not found" }
        | some parNode =>
          let stPar := mockNodeStat parNode
          if stPar.kind != .dir then return .error { kind := .notADirectory, path := some par, message := "not a dir" }
          if !hasWx stPar then return .error { kind := .permissionDenied, path := some par, message := "no write permission" }
          let rp := mockJoin par base; match lookupNode s.nodes rp with
          | some (.dir _ _) => if existOk then return .ok () else return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | some _ => return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | none => set { s with nodes := (rp, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir rp e.1) }; return .ok ()
    unlink := fun p miss => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => if miss then return .ok () else return .error { kind := .notFound, path := some p, message := "not found" }
      | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
      | some _ => set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }; return .ok ()
    rmdir := fun p => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some (.dir _ _) => set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }; return .ok ()
      | some _ => return .error { kind := .notADirectory, path := some p, message := "not dir" }
    rmtree := mockRmtreePure, rename := fun _ _ => pure (.ok ()), copyFile := fun _ _ => pure (.ok ()), copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun p => do return .ok ((mockStatPure (← get) p).isOk)
    isFile := fun p => do match mockStatPure (← get) p with | .ok st => return .ok (st.kind == .file) | .error _ => return .ok false
    isDir := fun p => do match mockStatPure (← get) p with | .ok st => return .ok (st.kind == .dir) | .error _ => return .ok false
    isSymlink := fun p => do match mockLstatPure (← get) p with | .ok st => return .ok (st.kind == .symlink) | .error _ => return .ok false
    stat := fun p => do return mockStatPure (← get) p, lstat := fun p => do return mockLstatPure (← get) p
    chmod := fun p mode => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some _ => set { s with nodes := s.nodes.map fun (k, n) => if normKey k == rp then
          (k, match (n : MockNode) with | .dir t _ => .dir t mode | .file i c t _ => .file i c t mode | .symlink tgt t => .symlink tgt t) else (k, n) }; return .ok ()
    symlink := fun _ _ => pure (.ok ()), readLink := fun _ => pure (.error { kind := .notFound, message := "no link" }), resolve := fun p => pure (.ok (normKey p)), cwd := pure (.ok "/")
    listDir := fun p => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some node =>
        let st := mockNodeStat node
        if st.kind != .dir then return .error { kind := .notADirectory, path := some p, message := "not dir" }
        if !hasRx st then return .error { kind := .permissionDenied, path := some p, message := "no read/exec permission" }
        return .ok (Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))).toArray
    walk := fun _ => pure (.ok #[]), glob := fun _ _ => pure (.ok #[]), rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun p m c act => mockLockCore p m c (pure (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" })) id act
    tryWithFileLock := fun p m c act => mockLockCore p m c (pure (.ok none)) (Except.map some) act }
/-- Mock `TimeOpsM` over `StateM TempDirMockState`. -/
def mockTime : TimeOpsM (StateM TempDirMockState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec), monoNanosNow := pure 0, sleep := fun _ => pure () }
/-- Mock `UuidApiM` over `StateM TempDirMockState`. -/
def mockUuid : UuidApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "entropy" }, fromRandomBytes := fun _ => .ok (mockUuidOfNat 1), toString := mockUuidToString
    toHex := fun _ => "00000000000040008000000000000001", parse := fun _ => .ok (mockUuidOfNat 1), parseHex := fun _ => .ok (mockUuidOfNat 1), isValid := fun _ => true
    getUuid := do let s ← get; set { s with nextUuid := s.nextUuid + 1 }; return .ok (mockUuidOfNat s.nextUuid) }
/-- Mock `EnvVarsApiM` over `StateM TempDirMockState`. -/
def mockEnv : EnvVarsApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }, getEnv := fun k => do if k == "TMPDIR" then return .ok (← get).tmpdir else return .ok none
    listEnv := pure (.ok #[]), homeDir := pure (.ok "/mock/user"), splitSearchPath := fun _ => #[] }
/-- Mock `FsApiM` lifted to `ExceptT String (StateM TempDirMockState)` with exception-safe locking. -/
def mockFsEx : FsApiM (ExceptT String (StateM TempDirMockState)) :=
  { join := mockFs.join, joinMany := mockFs.joinMany, normPath := mockFs.normPath, parent := mockFs.parent, name := mockFs.name, stem := mockFs.stem, suffix := mockFs.suffix, suffixes := mockFs.suffixes
    withName := mockFs.withName, withSuffix := mockFs.withSuffix, isAbsolute := mockFs.isAbsolute, relativeTo := mockFs.relativeTo, mapRawError := mockFs.mapRawError
    readText := fun p => liftM (mockFs.readText p), writeText := fun p c => liftM (mockFs.writeText p c), appendText := fun p c => liftM (mockFs.appendText p c), readBytes := fun p => liftM (mockFs.readBytes p)
    writeBytes := fun p b => liftM (mockFs.writeBytes p b), atomicWriteBytes := fun p b => liftM (mockFs.atomicWriteBytes p b), atomicWriteText := fun p c => liftM (mockFs.atomicWriteText p c)
    touch := fun p e => liftM (mockFs.touch p e), mkdir := fun p a e => liftM (mockFs.mkdir p a e), unlink := fun p m => liftM (mockFs.unlink p m), rmdir := fun p => liftM (mockFs.rmdir p), rmtree := fun p i => liftM (mockFs.rmtree p i)
    rename := fun a b => liftM (mockFs.rename a b), copyFile := fun a b => liftM (mockFs.copyFile a b), copyTree := fun a b c => liftM (mockFs.copyTree a b c), pathExists := fun p => liftM (mockFs.pathExists p)
    isFile := fun p => liftM (mockFs.isFile p), isDir := fun p => liftM (mockFs.isDir p), isSymlink := fun p => liftM (mockFs.isSymlink p), stat := fun p => liftM (mockFs.stat p), lstat := fun p => liftM (mockFs.lstat p)
    chmod := fun p m => liftM (mockFs.chmod p m), symlink := fun a b => liftM (mockFs.symlink a b), readLink := fun p => liftM (mockFs.readLink p), resolve := fun p => liftM (mockFs.resolve p), cwd := liftM mockFs.cwd
    listDir := fun p => liftM (mockFs.listDir p), walk := fun p => liftM (mockFs.walk p), glob := fun a b => liftM (mockFs.glob a b), rglob := fun a b => liftM (mockFs.rglob a b)
    withFileLock := fun p m c act => mockLockCore p m c (pure (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" })) id act, tryWithFileLock := fun p m c act => mockLockCore p m c (pure (.ok none)) (Except.map some) act }
/-- Mock `TimeOpsM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockTimeEx : TimeOpsM (ExceptT String (StateM TempDirMockState)) :=
  { nowTimestamp := liftM mockTime.nowTimestamp, monoNanosNow := liftM mockTime.monoNanosNow, sleep := fun ms => liftM (mockTime.sleep ms) }
/-- Mock `UuidApiM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockUuidEx : UuidApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockUuid.mapRawError, fromRandomBytes := mockUuid.fromRandomBytes, toString := mockUuid.toString, toHex := mockUuid.toHex
    parse := mockUuid.parse, parseHex := mockUuid.parseHex, isValid := mockUuid.isValid, getUuid := liftM mockUuid.getUuid }
/-- Mock `EnvVarsApiM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockEnvEx : EnvVarsApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockEnv.mapRawError, getEnv := fun k => liftM (mockEnv.getEnv k), listEnv := liftM mockEnv.listEnv, homeDir := liftM mockEnv.homeDir, splitSearchPath := mockEnv.splitSearchPath }
theorem stateM_bind_run {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) : (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl
theorem stateM_pure_run {S α : Type} (a : α) (s : S) : (pure a : StateM S α).run s = (a, s) := rfl
theorem stateM_get_run {S : Type} (s : S) : (get : StateM S S).run s = (s, s) := rfl
theorem stateM_set_run {S : Type} (s' s : S) : (set s' : StateM S Unit).run s = ((), s') := rfl
theorem stateM_modify_run {S : Type} (f : S → S) (s : S) : (modify f : StateM S Unit).run s = ((), f s) := rfl
theorem stateM_tryFinally'_run {S α β : Type} (x : StateM S α) (f : Option α → StateM S β) (s : S) :
    (tryFinally' x f).run s = let (a, s1) := x.run s; let (b, s2) := (f (some a)).run s1; ((a, b), s2) := rfl
theorem exceptT_stateM_bind_run {ε S α β : Type} (x : ExceptT ε (StateM S) α) (k : α → ExceptT ε (StateM S) β) (s : S) :
    (x >>= k).run.run s = match x.run.run s with | (.error e, s1) => (.error e, s1) | (.ok a, s1) => (k a).run.run s1 := by
  change (ExceptT.bind x k).run.run s = _; dsimp only [ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont, StateT.run, Bind.bind, StateT.bind]
  cases x s with | mk r s1 => cases r <;> rfl
theorem exceptT_pure_run {ε S α : Type} (a : α) (s : S) : (pure a : ExceptT ε (StateM S) α).run.run s = (.ok a, s) := rfl
theorem exceptT_throw_run {ε S α : Type} (e : ε) (s : S) : (throw e : ExceptT ε (StateM S) α).run.run s = (.error e, s) := rfl
theorem exceptT_liftM_run {ε S α : Type} (x : StateM S α) (s : S) : (liftM x : ExceptT ε (StateM S) α).run.run s = (.ok (x.run s).1, (x.run s).2) := rfl
theorem exceptT_tryFinally'_error_run {ε S α β : Type} {b : β} {s2 : S}
    (x : ExceptT ε (StateM S) α) (f : Option α → ExceptT ε (StateM S) β) (e : ε) (s s1 : S)
    (hx : x.run.run s = (.error e, s1)) (hf : (f none).run.run s1 = (.ok b, s2)) : (tryFinally' x f).run.run s = (.error e, s2) := by
  dsimp only [tryFinally', MonadFinally.tryFinally', ExceptT.run, ExceptT.mk, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hx hf ⊢; rw [hx]; dsimp only; rw [hf]; rfl
theorem allPass_assume {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) : (assume p >>= k) post = (p → k () post) := rfl
theorem allPass_assert {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) : (assert p >>= k) post = (p ∧ k () post) := rfl
theorem allPass_assert_end (p : Prop) : (assert p : AllPassRun Unit) (fun _ => True) = (p ∧ True) := rfl
theorem canReach_nondet (S : Type) {β : Type} (k : S → CanReachRun β) (post : β → Prop) : (nondet S >>= k) post = ∃ x : S, k x post := rfl
theorem canReach_assume {β : Type} (p : Prop) (k : Unit → CanReachRun β) (post : β → Prop) : (assume p >>= k) post = (p ∧ k () post) := rfl
theorem mkApiM_withTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m) (root? : Option String) (dirPrefix : String) (action : String → m (Except TempDirError α)) :
    (Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action = Internal.withTempDirM fs uuid env root? dirPrefix action := rfl
theorem mkApiM_withLockedTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m) (root? : Option String) (dirPrefix : String) (action : String → m (Except TempDirError α)) :
    (Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action = Internal.withLockedTempDirM fs uuid env root? dirPrefix action := rfl
theorem mkApiM_cleanupStaleTempDirs_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m) (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat) :
    (Internal.mkApiM fs time uuid env).cleanupStaleTempDirs root? dirPrefix maxAgeSec = Internal.cleanupStaleTempDirsM fs time env root? dirPrefix maxAgeSec := rfl
theorem mem_insertSorted (x y : String) (xs : List String) : y ∈ Internal.insertSorted x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with | nil => simp [Internal.insertSorted] | cons z zs ih => simp only [Internal.insertSorted]; split <;> simp [List.mem_cons, ih, or_left_comm]
private theorem pairwise_insertSorted (x : String) (xs : List String) (h : List.Pairwise (· ≤ ·) xs) : List.Pairwise (· ≤ ·) (Internal.insertSorted x xs) := by
  induction xs with | nil => simp [Internal.insertSorted] | cons y ys ih =>
    simp only [Internal.insertSorted]; split
    · next hxy => exact List.Pairwise.cons (fun z hz => by rcases List.mem_cons.mp hz with rfl | hz; exact hxy; exact Std.le_trans hxy (List.rel_of_pairwise_cons h hz)) h
    · next hxy => exact List.Pairwise.cons (fun z hz => by rw [mem_insertSorted] at hz; rcases hz with rfl | hz; exact Std.Asymm.asymm _ _ (Classical.byContradiction (fun hny => hxy hny)); exact List.rel_of_pairwise_cons h hz) (ih (List.pairwise_cons.mp h).2)
theorem pairwise_sortStrings (xs : List String) : List.Pairwise (· ≤ ·) (Internal.sortStrings xs) := by
  induction xs with | nil => simp [Internal.sortStrings] | cons _ _ ih => exact pairwise_insertSorted _ _ ih
theorem mem_sortStrings (y : String) (xs : List String) : y ∈ Internal.sortStrings xs ↔ y ∈ xs := by
  induction xs with | nil => simp [Internal.sortStrings] | cons _ _ ih => simp [Internal.sortStrings, mem_insertSorted, ih]
private theorem mem_eraseDupStringsAux (seen xs : List String) (y : String) (hNot : y ∉ seen) : y ∈ eraseDupStringsAux seen xs ↔ y ∈ xs := by
  induction xs generalizing seen with | nil => simp [eraseDupStringsAux] | cons x xs ih =>
    simp only [eraseDupStringsAux]; split
    · next hx => have hne : y ≠ x := fun h => hNot (h ▸ hx); simp [List.mem_cons, hne, ih seen hNot]
    · by_cases hyx : y = x <;> first | (subst hyx; simp) | simp [List.mem_cons, hyx, ih (x :: seen) (by simp [hyx, hNot])]
theorem mem_eraseDupStrings (xs : List String) (y : String) : y ∈ eraseDupStrings xs ↔ y ∈ xs := mem_eraseDupStringsAux [] xs y (by simp)
theorem nodup_eraseDupStrings (xs : List String) : (eraseDupStrings xs).Nodup := by
  suffices ∀ seen xs : List String, (eraseDupStringsAux seen xs).Nodup ∧ ∀ y ∈ eraseDupStringsAux seen xs, y ∉ seen from (this [] xs).1
  intro seen xs; induction xs generalizing seen with | nil => simp [eraseDupStringsAux] | cons x xs ih =>
    simp only [eraseDupStringsAux]; split <;> first | exact ih seen |
      (next hnx => have ⟨hnd, hsub⟩ := ih (x :: seen); refine ⟨List.nodup_cons.mpr ⟨fun hx => hsub x hx (by simp), hnd⟩, fun y hy => ?_⟩; rcases List.mem_cons.mp hy with rfl | hy <;> first | exact hnx | exact fun h => hsub y hy (by simp [h]))
theorem nodup_sortStrings (xs : List String) (hNd : xs.Nodup) : (Internal.sortStrings xs).Nodup := by
  have hIns : ∀ x zs, x ∉ zs → zs.Nodup → (Internal.insertSorted x zs).Nodup := fun x zs hnx hzs => by
    induction zs with | nil => simp [Internal.insertSorted] | cons z zs ih =>
      simp only [Internal.insertSorted]; split <;> first | exact List.nodup_cons.mpr ⟨hnx, hzs⟩ |
        (have hzNd := List.nodup_cons.mp hzs; exact List.nodup_cons.mpr ⟨fun h => hzNd.1 ((mem_insertSorted x z zs).mp h |>.resolve_left fun e => hnx (e ▸ by simp)), ih (fun h => hnx (by simp [h])) hzNd.2⟩)
  induction xs with | nil => simp [Internal.sortStrings] | cons x xs ih => have h := List.nodup_cons.mp hNd; exact hIns x _ (fun hm => h.1 ((mem_sortStrings x xs).mp hm)) (ih h.2)
theorem string_isEmpty_iff_eq_empty (s : String) : s.isEmpty = true ↔ s = "" := by simp only [String.isEmpty, beq_iff_eq]; exact String.utf8ByteSize_eq_zero_iff
private theorem str_len_pos {s : String} (hs : s ≠ "") : 0 < s.toList.length := by cases h : s.toList with | nil => exact absurd (String.toList_eq_nil_iff.mp h) hs | cons _ _ => simp
private theorem trimTrailingSlashesRev_ne_nil {cs : List Char} (h : cs ≠ []) : trimTrailingSlashesRev cs ≠ [] := by
  induction cs with | nil => exact absurd rfl h | cons c rest ih => cases rest with | nil => by_cases hc : c = '/' <;> simp [trimTrailingSlashesRev, hc] | cons d ds => by_cases hc : c = '/' <;> simp [trimTrailingSlashesRev, hc] <;> exact ih (by simp)
private theorem trimTrailingSlashesRev_idem (cs : List Char) : trimTrailingSlashesRev (trimTrailingSlashesRev cs) = trimTrailingSlashesRev cs := by
  induction cs with | nil => simp [trimTrailingSlashesRev] | cons c rest ih => cases rest with
    | nil => by_cases hc : c = '/' <;> simp [trimTrailingSlashesRev, hc] | cons d ds => by_cases hc : c = '/' <;> first | (subst hc; exact ih) | simp [trimTrailingSlashesRev, hc]
theorem normKey_idem (p : String) : normKey (normKey p) = normKey p := by unfold normKey trimSlashChars; simp [String.toList_ofList, List.reverse_reverse, trimTrailingSlashesRev_idem]
theorem normKey_ne_empty {a : String} (ha : a ≠ "") : normKey a ≠ "" := fun he => trimTrailingSlashesRev_ne_nil (fun h => ha (String.toList_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp h)))
  (by have h1 := congrArg String.toList he; simp only [normKey, trimSlashChars, String.toList_ofList, String.toList_empty, List.reverse_eq_nil_iff] at h1; exact h1)
theorem mockJoin_normKey (a b : String) : mockJoin (normKey a) b = mockJoin a b := by simp [mockJoin, normKey_idem]
theorem mockJoin_ne_empty (a b : String) (hb : b ≠ "") : mockJoin a b ≠ "" := by
  unfold mockJoin; dsimp only; split; · exact hb
  · split <;> intro h <;> have h1 := congrArg String.toList h <;> simp [String.toList_append, List.append_eq_nil_iff] at h1 <;> exact hb (String.toList_eq_nil_iff.mp h1.2)
theorem mockJoin_toList (root nm : String) (hr : root ≠ "") : (mockJoin root nm).toList = (if normKey root == "/" then ['/'] else (normKey root).toList ++ ['/']) ++ nm.toList := by
  have hne : (normKey root).isEmpty = false := Bool.eq_false_iff.mpr fun h => normKey_ne_empty hr ((string_isEmpty_iff_eq_empty _).mp h)
  unfold mockJoin; dsimp only; simp only [hne, Bool.false_eq_true, ↓reduceIte]; split <;> simp [String.toList_append, show ("/" : String).toList = ['/'] from rfl]
private theorem normKey_of_last_ne_slash (s : String) (c : Char) (rest : List Char) (hrev : s.toList.reverse = c :: rest) (hc : c ≠ '/') : normKey s = s := by
  unfold normKey trimSlashChars; have htr : trimTrailingSlashesRev (c :: rest) = c :: rest := by cases rest <;> simp [trimTrailingSlashesRev, hc]
  rw [hrev, htr, ← hrev, List.reverse_reverse, String.ofList_toList]
theorem normKey_mockJoin (a b : String) (hb : b ≠ "") (hslash : '/' ∉ b.toList) : normKey (mockJoin a b) = mockJoin a b := by
  cases h : b.toList.reverse with
  | nil => exact absurd (String.toList_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp h)) hb
  | cons c rest =>
    have hc : c ≠ '/' := fun he => hslash (List.mem_reverse.mp (by rw [h, he]; simp)); unfold mockJoin; dsimp only; split
    · exact normKey_of_last_ne_slash b c rest h hc
    · split; · exact normKey_of_last_ne_slash ("/" ++ b) c (rest ++ ['/']) (by rw [String.toList_append, List.reverse_append, h]; rfl) hc
      · exact normKey_of_last_ne_slash (normKey a ++ "/" ++ b) c (rest ++ '/' :: (normKey a).toList.reverse) (by rw [String.toList_append, String.toList_append, List.reverse_append, List.reverse_append, h]; rfl) hc
private theorem mockJoin_length_gt (root nm : String) (hr : root ≠ "") (hnm : nm ≠ "") : (normKey root).toList.length < (mockJoin root nm).toList.length := by
  have hpos := str_len_pos hnm; rw [mockJoin_toList root nm hr, List.length_append]
  split; · next hs => rw [beq_iff_eq.mp hs, show ("/" : String).toList = ['/'] from rfl]; simp; omega
  · simp; omega
private theorem splitLastSlashRev_append_no_slash (xs ys : List Char) (hno : '/' ∉ xs) :
    splitLastSlashRev (xs.reverse ++ ys) = match splitLastSlashRev ys with | none => none | some (par, base) => some (par, base ++ xs) := by
  suffices ∀ zs : List Char, '/' ∉ zs → splitLastSlashRev (zs ++ ys) = match splitLastSlashRev ys with | none => none | some (par, base) => some (par, base ++ zs.reverse) by
    simpa [List.reverse_reverse] using this xs.reverse (fun h => hno (List.mem_reverse.mp h))
  intro zs hzs; induction zs with | nil => simp only [List.nil_append, List.reverse_nil]; cases splitLastSlashRev ys <;> simp | cons z zs ih =>
    have hz : z ≠ '/' := fun h => hzs (h ▸ by simp); simp only [List.cons_append, splitLastSlashRev, beq_false_of_ne hz, ih (fun h => hzs (by simp [h]))]
    cases splitLastSlashRev ys <;> simp [List.reverse_cons, List.append_assoc]
theorem splitParentChild_mockJoin (a b : String) (ha : a ≠ "") (hb : b ≠ "") (hslash : '/' ∉ b.toList) : splitParentChild (mockJoin a b) = some (normKey a, b) := by
  have hnorm := normKey_mockJoin a b hb hslash; have hna := normKey_ne_empty ha
  have hbE : b.isEmpty = false := Bool.eq_false_iff.mpr fun h => hb ((string_isEmpty_iff_eq_empty _).mp h)
  have hnaE : (normKey a).isEmpty = false := Bool.eq_false_iff.mpr fun h => hna ((string_isEmpty_iff_eq_empty _).mp h)
  have hnaL : (normKey a).toList.isEmpty = false := by cases h : (normKey a).toList with | nil => exact absurd (String.toList_eq_nil_iff.mp h) hna | cons _ _ => rfl
  have hneS : mockJoin a b ≠ "/" := fun he => by have hl := mockJoin_length_gt a b ha hb; have h1 := str_len_pos hna; rw [he, show ("/" : String).toList = ['/'] from rfl, List.length_singleton] at hl; omega
  have hneE : (mockJoin a b).isEmpty = false := Bool.eq_false_iff.mpr fun h => mockJoin_ne_empty a b hb ((string_isEmpty_iff_eq_empty _).mp h)
  have hmj : mockJoin a b = if normKey a == "/" then "/" ++ b else normKey a ++ "/" ++ b := by simp [mockJoin, hnaE]
  unfold splitParentChild; simp only [hnorm, beq_false_of_ne hneS, hneE, Bool.or_self, Bool.false_eq_true, ↓reduceIte]; rw [hmj]
  by_cases hEq : normKey a = "/"
  · simp only [hEq, beq_self_eq_true, ↓reduceIte]; rw [String.toList_append, List.reverse_append, show ("/" : String).toList = ['/'] from rfl, show ['/'].reverse = ['/'] from rfl, splitLastSlashRev_append_no_slash b.toList ['/'] hslash]; simp [splitLastSlashRev, String.ofList_toList, hbE]
  · simp only [beq_false_of_ne hEq, Bool.false_eq_true, ↓reduceIte]; rw [String.toList_append, String.toList_append, List.reverse_append, List.reverse_append, show ("/" : String).toList = ['/'] from rfl, show ['/'].reverse = ['/'] from rfl, List.cons_append, List.nil_append, splitLastSlashRev_append_no_slash b.toList ('/' :: (normKey a).toList.reverse) hslash]; simp [splitLastSlashRev, hnaL, hbE, String.ofList_toList]
theorem mockJoin_ne_slash (root nm : String) (hr : root ≠ "") (hnm : nm ≠ "") : mockJoin root nm ≠ "/" := fun he => by
  have h1 := str_len_pos (normKey_ne_empty hr); have h2 := mockJoin_length_gt root nm hr hnm; rw [he, show ("/" : String).toList = ['/'] from rfl, List.length_singleton] at h2; omega
theorem mockJoin_ne_root (root child : String) (hr : root ≠ "") (hc : child ≠ "") (hslash : '/' ∉ child.toList) : normKey (mockJoin root child) ≠ normKey root := fun heq => by
  rw [normKey_mockJoin root child hc hslash] at heq; have h2 := mockJoin_length_gt root child hr hc; rw [heq] at h2; omega
theorem underDir_refl (d : String) (hn : normKey d = d) : underDir d d = true := by simp [underDir, hn]
theorem underDir_eq_of_normKey_eq (d a b : String) (h : normKey a = normKey b) : underDir d a = underDir d b := by simp [underDir, h]
private theorem takeWhile_ne_slash_append (xs ys : List Char) (hno : '/' ∉ xs) : (xs ++ '/' :: ys).takeWhile (· != '/') = xs := by
  induction xs with | nil => rfl | cons c cs ih => have hc : (c != '/') = true := bne_iff_ne.mpr fun h => hno (by simp [h]); simp [hc, ih fun h => hno (by simp [h])]
private theorem takeWhile_ne_slash_eq_self (xs : List Char) (hno : '/' ∉ xs) : xs.takeWhile (· != '/') = xs := by
  induction xs with | nil => rfl | cons c cs ih => have hc : (c != '/') = true := bne_iff_ne.mpr fun h => hno (by simp [h]); simp [hc, ih fun h => hno (by simp [h])]
private theorem underDir_mockJoin_sub (root nm p : String) (hr : root ≠ "") (hnm : nm ≠ "") (hno : '/' ∉ nm.toList) (hu : underDir (mockJoin root nm) p = true) :
    let pfx := if normKey root == "/" then ['/'] else (normKey root).toList ++ ['/']; ((normKey p).toList.drop pfx.length).takeWhile (· != '/') = nm.toList := by
  have hdn := normKey_mockJoin root nm hnm hno; have hdb : (mockJoin root nm == "/") = false := beq_false_of_ne (mockJoin_ne_slash root nm hr hnm)
  simp only [underDir, hdn, hdb, Bool.or_eq_true, beq_iff_eq] at hu; have hlist := mockJoin_toList root nm hr
  rcases hu with hEq | hPref
  · dsimp only; rw [hEq, hlist, List.drop_left]; exact takeWhile_ne_slash_eq_self nm.toList hno
  · simp only [Bool.false_eq_true, ↓reduceIte] at hPref; obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hPref
    rw [String.toList_append, hlist, show ("/" : String).toList = ['/'] from rfl] at ht; rw [← ht]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rw [List.drop_left]; exact takeWhile_ne_slash_append nm.toList t hno
theorem disjoint_underDir_mockJoin (root n1 n2 p : String) (hr : root ≠ "") (hn1 : n1 ≠ "") (hn2 : n2 ≠ "") (hno1 : '/' ∉ n1.toList) (hno2 : '/' ∉ n2.toList)
    (hne : n1 ≠ n2) (hu1 : underDir (mockJoin root n1) p = true) (hu2 : underDir (mockJoin root n2) p = true) : False :=
  hne (String.toList_inj.mp ((underDir_mockJoin_sub root n1 p hr hn1 hno1 hu1).symm.trans (underDir_mockJoin_sub root n2 p hr hn2 hno2 hu2)))
theorem not_underDir_mockJoin_root (root nm p : String) (hr : root ≠ "") (hnm : nm ≠ "") (hno : '/' ∉ nm.toList) (hp : normKey p = normKey root) :
    underDir (mockJoin root nm) p = false := Bool.eq_false_iff.mpr fun hu => by
  have hdn := normKey_mockJoin root nm hnm hno; have hdb : (mockJoin root nm == "/") = false := beq_false_of_ne (mockJoin_ne_slash root nm hr hnm)
  simp only [underDir, hdn, hdb, Bool.or_eq_true, beq_iff_eq, hp] at hu; have hlt := mockJoin_length_gt root nm hr hnm
  rcases hu with hEq | hPref; · rw [← hEq] at hlt; omega
  · simp only [Bool.false_eq_true, ↓reduceIte] at hPref; have hsub := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hPref)
    rw [String.toList_append, show ("/" : String).toList = ['/'] from rfl, List.length_append, List.length_singleton] at hsub; omega
theorem underDir_mockJoin_child (dir nm p : String) (hd : dir ≠ "") (hdn : normKey dir = dir) (hds : dir ≠ "/") (hnm : nm ≠ "") (hno : '/' ∉ nm.toList)
    (hu : underDir (mockJoin dir nm) p = true) : underDir dir p = true := by
  have hdn2 := normKey_mockJoin dir nm hnm hno; have hdb2 : (mockJoin dir nm == "/") = false := beq_false_of_ne (mockJoin_ne_slash dir nm hd hnm)
  have hdb : (dir == "/") = false := beq_false_of_ne hds; have hde : dir.isEmpty = false := Bool.eq_false_iff.mpr fun h => hd ((string_isEmpty_iff_eq_empty _).mp h)
  have hlist : mockJoin dir nm = dir ++ "/" ++ nm := by simp [mockJoin, hdn, hde, hdb, String.append_assoc]
  simp only [underDir, hdn, hdb, hdn2, hdb2, Bool.or_eq_true, beq_iff_eq] at hu ⊢; right
  rcases hu with hEq | hPref; · rw [hEq, hlist]; simp [String.toList_append]
  · rw [hlist] at hPref; exact List.isPrefixOf_iff_prefix.mpr ((by simp [String.toList_append, List.append_assoc] : (dir ++ "/").toList <+: (dir ++ "/" ++ nm ++ "/").toList).trans (List.isPrefixOf_iff_prefix.mp hPref))
theorem underDir_mockJoin_self (dir nm : String) (hd : dir ≠ "") (hdn : normKey dir = dir) (hds : dir ≠ "/") (hnm : nm ≠ "") (hno : '/' ∉ nm.toList) :
    underDir dir (mockJoin dir nm) = true := underDir_mockJoin_child dir nm (mockJoin dir nm) hd hdn hds hnm hno (underDir_refl _ (normKey_mockJoin dir nm hnm hno))
theorem payload_ne_dir (root child fileName : String) (_hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList) (hfNe : fileName ≠ "") (hfNoSlash : '/' ∉ fileName.toList) :
    normKey (mockJoin (mockJoin root child) fileName) ≠ mockJoin root child := fun hEq => by
  have hlt := mockJoin_length_gt (mockJoin root child) fileName (mockJoin_ne_empty root child hcNe) hfNe
  rw [normKey_mockJoin _ fileName hfNe hfNoSlash] at hEq; rw [normKey_mockJoin root child hcNe hcNoSlash, hEq] at hlt; exact Nat.lt_irrefl _ hlt
theorem validEntryName_of_mockParentChild (dir full rest : String) (h : mockParentChild dir full = some rest) :
    (!rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList)) = true := by
  unfold mockParentChild at h; dsimp only at h; generalize (if (normKey dir).isEmpty then "" else if normKey dir == "/" then "/" else normKey dir ++ "/") = pref at h
  split at h <;> first | (split at h <;> first | (next hcond => simp only [Option.some.injEq] at h; rw [← h]; exact hcond) | contradiction) | contradiction
theorem validPrefix_parts (p : String) (h : (!p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)) = true) : p ≠ "" ∧ '/' ∉ p.toList := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; refine ⟨fun he => by simp [he, String.isEmpty] at h, fun hm => ?_⟩
  have hfalse : decide ('/' ∈ p.toList) = false := h.1.2; rw [decide_eq_true hm] at hfalse; exact Bool.noConfusion hfalse
theorem validRoot_ne_empty (r : String) (h : (!r.isEmpty && !(Char.ofNat 0 ∈ r.toList)) = true) : r ≠ "" := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; intro he; simp [he, String.isEmpty] at h
theorem childName_parts (dirPrefix : String) (u : Uuid) (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    (dirPrefix ++ mockUuidToString u) ≠ "" ∧ '/' ∉ (dirPrefix ++ mockUuidToString u).toList := by
  have ⟨_, hno⟩ := validPrefix_parts dirPrefix hvp
  have huNe : mockUuidToString u ≠ "" := fun h => by have hl := congrArg String.length h; unfold mockUuidToString at hl; have h32 : ("00000000-0000-4000-8000-00000000" : String).length = 32 := rfl; simp [String.length_append, h32] at hl
  have huNo : '/' ∉ (mockUuidToString u).toList := by
    have hd : ∀ k : Nat, k < 16 → (if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)) ≠ '/' := by decide
    have hexNo : ∀ b : UInt8, '/' ∉ (mockHexByte b).toList := fun b => by unfold mockHexByte; simp only [String.toList_ofList, List.mem_cons, List.not_mem_nil, or_false]; rintro (h1 | h1) <;> first | exact hd (b.toNat / 16) (Nat.div_lt_of_lt_mul (UInt8.toNat_lt b)) h1.symm | exact hd (b.toNat % 16) (Nat.mod_lt _ (by decide)) h1.symm
    unfold mockUuidToString; simp only [String.toList_append, List.mem_append]; rintro ((h | h) | h) <;> first | exact absurd h (by decide) | exact hexNo _ h | exact hexNo _ h
  exact ⟨fun h => by have h1 := congrArg String.toList h; rw [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at h1; exact huNe (String.toList_eq_nil_iff.mp h1.2),
    fun h => by rw [String.toList_append] at h; rcases List.mem_append.mp h with hm | hm <;> first | exact hno hm | exact huNo hm⟩
theorem hasWx_of_hasRwx (st : FileStat) (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) : hasWx st = true := by simp [hasWx, h.1, h.2.2.1, h.2.2.2]; decide
theorem hasRx_of_hasRwx (st : FileStat) (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) : hasRx st = true := by simp [hasRx, h.1, h.2.1, h.2.2.2]; decide
theorem lookupNode_cons_eq (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String) (heq : normKey k = normKey p) : lookupNode ((k, v) :: nodes) p = some v := by simp [lookupNode, heq]
theorem lookupNode_cons_ne (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String) (hne : normKey k ≠ normKey p) : lookupNode ((k, v) :: nodes) p = lookupNode nodes p := by simp [lookupNode, beq_false_of_ne hne]
theorem lookupNode_filter_of_preserved (nodes : List (String × MockNode)) (pred : (String × MockNode) → Bool) (p : String)
    (hpres : ∀ e ∈ nodes, normKey e.1 = normKey p → pred e = true) : lookupNode (nodes.filter pred) p = lookupNode nodes p := by
  unfold lookupNode; congr 1; induction nodes with | nil => simp | cons x xs ih =>
    have ih' := ih fun e he h => hpres e (by simp [he]) h; rw [List.filter_cons]; split
    · rw [List.find?_cons, List.find?_cons]; split <;> simp [ih']
    · next hnx => rw [List.find?_cons, beq_false_of_ne fun h => hnx (hpres x (by simp) h)]; exact ih'
theorem lookupNode_filter_none_of_false (nodes : List (String × MockNode)) (pred : (String × MockNode) → Bool) (p : String)
    (h : ∀ e ∈ nodes, pred e = true → normKey e.1 ≠ normKey p) : lookupNode (nodes.filter pred) p = none := by
  unfold lookupNode; induction nodes with | nil => simp | cons x xs ih =>
    have ih' := ih fun e he hk => h e (by simp [he]) hk; rw [List.filter_cons]; split
    · next hkeep => simpa [List.find?_cons, beq_false_of_ne (h x (by simp) hkeep)] using ih'
    · exact ih'
theorem lookupNode_filter_none_of_none (nodes : List (String × MockNode)) (pred : (String × MockNode) → Bool) (p : String) (h : lookupNode nodes p = none) : lookupNode (nodes.filter pred) p = none := by
  unfold lookupNode at h ⊢; induction nodes with | nil => simp | cons x xs ih =>
    cases hb : (normKey x.1 == normKey p) with | true => simp [hb] at h | false =>
      simp only [List.find?_cons, hb] at h; rw [List.filter_cons]; split <;> first | (simp only [List.find?_cons, hb]; exact ih h) | exact ih h
theorem lookupNode_filter_none_of_underDir (nodes : List (String × MockNode)) (d p : String) (hu : underDir d p = true) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) p = none :=
  lookupNode_filter_none_of_false nodes _ p fun e _ hkeep heq => by rw [← underDir_eq_of_normKey_eq d e.1 p heq] at hu; simp [hu] at hkeep
theorem lookupNode_filter_underDir_eq (nodes : List (String × MockNode)) (rp : String) (hnorm : normKey rp = rp) :
    lookupNode (nodes.filter (fun e => !underDir rp e.1)) rp = none := lookupNode_filter_none_of_underDir nodes rp rp (underDir_refl rp hnorm)
theorem list_map_id_of_mem {α : Type} (xs : List α) (f : α → α) (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with | nil => rfl | cons x xs ih => simp [h x (by simp), ih fun y hy => h y (by simp [hy])]
theorem mockFs_join_eq : mockFs.join = mockJoin := rfl
theorem mockUuid_toString_eq : mockUuid.toString = mockUuidToString := rfl
theorem mockUuid_getUuid_run (s : TempDirMockState) : mockUuid.getUuid.run s = (.ok (mockUuidOfNat s.nextUuid), { s with nextUuid := s.nextUuid + 1 }) := rfl
theorem mockFs_stat_run (s : TempDirMockState) (p : String) : (mockFs.stat p).run s = (mockStatPure s p, s) := rfl
theorem mockFs_lstat_run (s : TempDirMockState) (p : String) : (mockFs.lstat p).run s = (mockLstatPure s p, s) := rfl
theorem mockFs_lstat_isOk_false_of_lookup_none (s : TempDirMockState) (p : String) (h : lookupNode s.nodes p = none) :
    ((mockFs.lstat p).run s).1.isOk = false := by simp [mockFs_lstat_run, mockLstatPure, h, Except.isOk, Except.toBool]
theorem lookupNode_of_lstat_ok (s : TempDirMockState) (p : String) (st : FileStat) (h : mockLstatPure s p = .ok st) :
    ∃ nd, lookupNode s.nodes p = some nd ∧ mockNodeStat nd = st := by unfold mockLstatPure at h; cases hl : lookupNode s.nodes p <;> simp_all
theorem mockFs_writeText_run (s : TempDirMockState) (p c : String) :
    (mockFs.writeText p c).run s = (.ok (), { s with nodes := (normKey p, .file (freshInode s) c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != normKey p), nextInode := freshInode s + 1 }) := rfl
private theorem mockLockCore_existing_conflict_run {α β : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (onConflict : StateM TempDirMockState (Except FsError β)) (wrap : Except FsError α → Except FsError β) (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = true) (action : StateM TempDirMockState (Except FsError α)) :
    (mockLockCore p mode createIfMissing onConflict wrap action).run s = onConflict.run s := by
  dsimp only [mockLockCore]; rw [stateM_bind_run, stateM_get_run, hnorm, hLook]; simp [hConf]
private theorem mockLockCore_existing_ok_run {α β : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (onConflict : StateM TempDirMockState (Except FsError β)) (wrap : Except FsError α → Except FsError β) (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = false) (action : StateM TempDirMockState (Except FsError α)) :
    (mockLockCore p mode createIfMissing onConflict wrap action).run s =
      let s1 : TempDirMockState := { s with locks := (ino, mode) :: s.locks }; let (r, s2) := action.run s1; (wrap r, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) := by
  dsimp only [mockLockCore]; rw [stateM_bind_run, stateM_get_run, hnorm, hLook]
  simp only [hConf, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run, stateM_tryFinally'_run, stateM_modify_run, stateM_pure_run]; cases action.run { s with locks := (ino, mode) :: s.locks }; rfl
private theorem mockLockCore_create_run {α β : Type} (s : TempDirMockState) (p : String) (mode : LockMode)
    (onConflict : StateM TempDirMockState (Except FsError β)) (wrap : Except FsError α → Except FsError β) (hnorm : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (action : StateM TempDirMockState (Except FsError α)) :
    (mockLockCore p mode true onConflict wrap action).run s =
      let ino := freshInode s; let s1 : TempDirMockState := { s with nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 }
      let (r, s2) := action.run s1; (wrap r, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) := by
  dsimp only [mockLockCore]; rw [stateM_bind_run, stateM_get_run, hnorm, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run, stateM_tryFinally'_run, stateM_modify_run, stateM_pure_run]; cases action.run _; rfl
theorem mockFs_withFileLock_existing_conflict_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = true)
    (action : StateM TempDirMockState (Except FsError α)) : (mockFs.withFileLock p mode createIfMissing action).run s = (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" }, s) :=
  mockLockCore_existing_conflict_run s p mode createIfMissing _ id ino c t m hnorm hLook hConf action
theorem mockFs_withFileLock_existing_ok_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = false)
    (action : StateM TempDirMockState (Except FsError α)) :
    (mockFs.withFileLock p mode createIfMissing action).run s = let s1 : TempDirMockState := { s with locks := (ino, mode) :: s.locks }; let (r, s2) := action.run s1; (r, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) :=
  mockLockCore_existing_ok_run s p mode createIfMissing _ id ino c t m hnorm hLook hConf action
theorem mockFs_withFileLock_create_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (hnorm : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (action : StateM TempDirMockState (Except FsError α)) :
    (mockFs.withFileLock p mode true action).run s = let ino := freshInode s; let s1 : TempDirMockState := { s with nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 }; let (r, s2) := action.run s1; (r, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) :=
  mockLockCore_create_run s p mode _ id hnorm hNone action
theorem mockFs_tryWithFileLock_existing_conflict_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = true)
    (action : StateM TempDirMockState (Except FsError α)) : (mockFs.tryWithFileLock p mode createIfMissing action).run s = (.ok none, s) :=
  mockLockCore_existing_conflict_run s p mode createIfMissing _ (Except.map some) ino c t m hnorm hLook hConf action
theorem mockFs_tryWithFileLock_existing_ok_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hConf : mockHasConflict s.locks ino mode = false)
    (action : StateM TempDirMockState (Except FsError α)) :
    (mockFs.tryWithFileLock p mode createIfMissing action).run s = let s1 : TempDirMockState := { s with locks := (ino, mode) :: s.locks }; let (r, s2) := action.run s1; (r.map some, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) :=
  mockLockCore_existing_ok_run s p mode createIfMissing _ (Except.map some) ino c t m hnorm hLook hConf action
theorem mockFs_tryWithFileLock_create_run {α : Type} (s : TempDirMockState) (p : String) (mode : LockMode) (hnorm : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (action : StateM TempDirMockState (Except FsError α)) :
    (mockFs.tryWithFileLock p mode true action).run s = let ino := freshInode s; let s1 : TempDirMockState := { s with nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 }; let (r, s2) := action.run s1; (r.map some, { s2 with locks := mockRemoveFirstLock ino mode s2.locks }) :=
  mockLockCore_create_run s p mode _ (Except.map some) hnorm hNone action
theorem mockFs_mkdir_fresh_run (s : TempDirMockState) (root child : String) (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (rootNode : MockNode) (stRoot : FileStat) (hLookRoot : lookupNode s.nodes (normKey root) = some rootNode) (hStRoot : mockNodeStat rootNode = stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : lookupNode s.nodes (mockJoin root child) = none) :
    let dir := mockJoin root child
    (mockFs.mkdir dir false false).run s = (.ok (), { s with nodes := (dir, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [splitParentChild_mockJoin root child hrNe hcNe hcNoSlash]; dsimp only; rw [hLookRoot]; dsimp only; rw [hStRoot]
  simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte, hasWx_of_hasRwx stRoot hRwx, Bool.not_true, mockJoin_normKey, hNone, stateM_bind_run, stateM_set_run, stateM_pure_run]
theorem mockFs_chmod_0o700_head_run (s : TempDirMockState) (dir : String) (t : Int) (m : Nat) (rest : List (String × MockNode))
    (hDirNorm : normKey dir = dir) (hNodes : s.nodes = (dir, .dir t m) :: rest) (hDisj : ∀ e ∈ rest, normKey e.1 ≠ dir) :
    (mockFs.chmod dir 0o700).run s = (.ok (), { s with nodes := (dir, .dir t 0o700) :: rest }) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hDirNorm, hNodes, lookupNode_cons_eq _ _ _ _ rfl]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run, List.map_cons, beq_iff_eq.mpr hDirNorm, ↓reduceIte]
  rw [list_map_id_of_mem _ _ fun x hx => by simp [beq_false_of_ne (hDisj x hx)]]
theorem lookupNode_lock_mk_none (nodes : List (String × MockNode)) (dir : String) (nd : MockNode)
    (hDirNorm : normKey dir = dir) (hNe : normKey (mockJoin dir ".lock") ≠ dir) (hUnder : underDir dir (mockJoin dir ".lock") = true) :
    lookupNode ((dir, nd) :: nodes.filter (fun e => !underDir dir e.1)) (mockJoin dir ".lock") = none := by
  unfold lookupNode; rw [List.find?_cons]; dsimp only; rw [show (normKey dir == normKey (mockJoin dir ".lock")) = false by rw [hDirNorm, beq_false_of_ne (ne_comm.mp hNe)]]
  exact lookupNode_filter_none_of_underDir nodes dir (mockJoin dir ".lock") hUnder
theorem lookupNode_cons_lock_dir (nodes : List (String × MockNode)) (dir : String) (ndL : MockNode) (hDirNorm : normKey dir = dir)
    (hNe : normKey (mockJoin dir ".lock") ≠ dir) : lookupNode ((mockJoin dir ".lock", ndL) :: nodes) dir = lookupNode nodes dir := by
  unfold lookupNode; rw [List.find?_cons]; dsimp only; rw [show (normKey (mockJoin dir ".lock") == normKey dir) = false by rw [hDirNorm, beq_false_of_ne hNe]]
theorem defaultRoot_ok (s₀ : TempDirMockState) (hs₀ : s₀ = {}) :
    ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
  ⟨mockNodeStat (.dir 0 0o755), by rw [hs₀]; rfl, rfl, rfl, rfl, rfl⟩
theorem defaultRoot_afterUuid_ok (s₀ : TempDirMockState) (hs₀ : s₀ = {}) :
    ∃ stTmp, ((mockFs.stat "/tmp").run { s₀ with nextUuid := s₀.nextUuid + 1 }).1 = .ok stTmp ∧ stTmp.kind = .dir ∧ (stTmp.mode / 256) % 2 = 1 ∧ (stTmp.mode / 128) % 2 = 1 ∧ (stTmp.mode / 64) % 2 = 1 :=
  ⟨mockNodeStat (.dir 0 0o755), by rw [hs₀]; rfl, rfl, rfl, rfl, rfl⟩
theorem defaultDir_lstat_none (s₀ : TempDirMockState) (hs₀ : s₀ = {}) :
    ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false := by
  rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq, hs₀]; unfold mockLstatPure; dsimp only
  have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
  rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ (ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash))]; rfl
/-- Minimal `FsApiM` operations required by `resolveRoot` and `createTempDir` success paths. -/
structure CreateFsOps (fs : FsApiM (StateM TempDirMockState)) : Prop where
  /-- `join` agrees with `mockJoin`. -/ hJoin : fs.join = mockJoin
  /-- `stat` agrees with `mockStatPure`. -/ hStat : ∀ p s, (fs.stat p).run s = (mockStatPure s p, s)
  /-- `mkdir` agrees with `mockFs.mkdir`. -/ hMkdir : ∀ p par ex s, (fs.mkdir p par ex).run s = (mockFs.mkdir p par ex).run s
  /-- `chmod` agrees with `mockFs.chmod`. -/ hChmod : ∀ p m s, (fs.chmod p m).run s = (mockFs.chmod p m).run s
theorem createFsOps_mockFs : CreateFsOps mockFs := ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
theorem resolveRoot_some_ok_run {fs : FsApiM (StateM TempDirMockState)} (hStat : ∀ p s, (fs.stat p).run s = (mockStatPure s p, s))
    (s₀ : TempDirMockState) (root : String) (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true) (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hDir : stRoot.kind = .dir) :
    (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  dsimp only [Internal.resolveRoot]; rw [stateM_bind_run, stateM_pure_run]; dsimp only
  simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hStat root s₀, hRoot, hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, stateM_pure_run]
theorem resolveRoot_none_ok_run {fs : FsApiM (StateM TempDirMockState)} (hStat : ∀ p s, (fs.stat p).run s = (mockStatPure s p, s))
    (s₀ : TempDirMockState) (r : String) (hR : r = match s₀.tmpdir with | some v => if v.isEmpty then "/tmp" else v | none => "/tmp")
    (hvr : (!r.isEmpty && !(Char.ofNat 0 ∈ r.toList)) = true) (st : FileStat) (hStatOk : mockStatPure s₀ r = .ok st) (hDir : st.kind = .dir) :
    (Internal.resolveRoot fs mockEnv none).run s₀ = (.ok r, s₀) := by
  have hvr' : Internal.validRoot r = true := by simpa [Internal.validRoot] using hvr
  dsimp only [Internal.resolveRoot]; rw [stateM_bind_run, show (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) from rfl]
  cases ht : s₀.tmpdir <;> rw [ht] at hR <;> dsimp only at hR <;> subst hR <;> (dsimp only; rw [stateM_bind_run, stateM_pure_run]; dsimp only; simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hStat _ s₀, hStatOk, hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, stateM_pure_run])
theorem createTempDir_ok_run {fs : FsApiM (StateM TempDirMockState)} (hOps : CreateFsOps fs) (s₀ : TempDirMockState) (root? : Option String) (root dirPrefix : String)
    (hResRoot : (Internal.resolveRoot fs mockEnv root?).run s₀ = (.ok root, s₀)) (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir fs mockUuid mockEnv root? dirPrefix).run s₀ = (.ok dir, sMk) := by
  intro u dir sMk; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by unfold mockLstatPure at hNone; cases hl : lookupNode s₀.nodes dir with | none => rfl | some _ => rw [hl] at hNone; simp [Except.isOk, Except.toBool] at hNone
  let sMk0 : TempDirMockState := { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
  have hMk : (fs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (), sMk0) := by
    dsimp only [dir, sMk0]; rw [hOps.hMkdir, mockFs_mkdir_fresh_run { s₀ with nextUuid := s₀.nextUuid + 1 } root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash rootNode stRoot hLookRootNorm hStRoot hRwx hLookDirNone]
  have hDisj : ∀ x ∈ s₀.nodes.filter (fun e => !underDir dir e.1), normKey x.1 ≠ dir := fun x hx he => by
    have hu : underDir dir x.1 = true := by rw [underDir_eq_of_normKey_eq dir x.1 dir (he.trans hDirNorm.symm), underDir_refl dir hDirNorm]
    have hf := (List.mem_filter.mp hx).2; simp [hu] at hf
  have hChmod : (fs.chmod dir 0o700).run sMk0 = (.ok (), sMk) := by rw [hOps.hChmod]; exact mockFs_chmod_0o700_head_run sMk0 dir s₀.nowSec 0o755 _ hDirNorm rfl hDisj
  dsimp only [Internal.createTempDir]; simp only [show Internal.validPrefix dirPrefix = true by simpa [Internal.validPrefix] using hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hResRoot]
  rw [mockUuid_getUuid_run]; dsimp only; dsimp only [dir, u] at hMk hChmod; rw [mockUuid_toString_eq, hOps.hJoin, stateM_bind_run, hMk]; dsimp only; rw [stateM_bind_run, hChmod]; exact stateM_pure_run _ _
theorem cleanupDir_mock_run (s : TempDirMockState) (dir : String) (hnorm : normKey dir = dir) (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (Internal.cleanupDirIgnoringNotFound mockFs dir).run s = (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  rcases hnode with ⟨m, mode, hLook⟩; dsimp only [Internal.cleanupDirIgnoringNotFound, mockFs, mockRmtreePure]; rw [stateM_bind_run, stateM_bind_run, stateM_get_run]; dsimp only; rw [hnorm, hLook, stateM_bind_run, stateM_set_run, stateM_pure_run]; rfl
theorem withTempDirM_run {S α : Type} (fs : FsApiM (StateM S)) (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ sMk sAct sFin : S) (root? : Option String) (dirPrefix dir : String) (action : String → StateM S (Except TempDirError α))
    (ra : Except TempDirError α) (rc : Except TempDirError Unit) (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.ok dir, sMk))
    (hAct : (action dir).run sMk = (ra, sAct)) (hCln : (Internal.cleanupDirIgnoringNotFound fs dir).run sAct = (rc, sFin)) :
    (Internal.withTempDirM fs uuid env root? dirPrefix action).run s₀ = (Internal.combineCleanup ra rc, sFin) := by
  dsimp only [Internal.withTempDirM]; rw [stateM_bind_run, hCre]; dsimp only; rw [stateM_bind_run, stateM_tryFinally'_run, hAct]; dsimp only; rw [hCln]; rfl
theorem withTempDirM_create_err {S α : Type} (fs : FsApiM (StateM S)) (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ s1 : S) (root? : Option String) (dirPrefix : String) (action : String → StateM S (Except TempDirError α)) (e : TempDirError)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.error e, s1)) :
    (Internal.withTempDirM fs uuid env root? dirPrefix action).run s₀ = (.error e, s1) := by
  dsimp only [Internal.withTempDirM]; rw [stateM_bind_run, hCre]; rfl
end LeanSwe.TempDir.Proofs
