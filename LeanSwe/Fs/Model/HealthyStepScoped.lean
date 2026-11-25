import LeanSwe.Fs.Model.HealthyStepBase

namespace LeanSwe.Fs.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs

/-- Single-step request sum covering all 19 operations of `ScopedRawFsOpsM`. -/
inductive ScopedRawFsStepReq where
  /-- Pure `mapRawError` normalization. -/
  | mapRawError (raw : FsRawError)
  /-- `stat` (`follow = true`) or `lstat` (`follow = false`). -/
  | stat (follow : Bool) (path : String)
  /-- Unsorted `readDir` excluding `.` and `..`. -/
  | readDir (path : String)
  /-- Single-level `createDir`. -/
  | createDir (path : String)
  /-- `removeDir`. -/
  | removeDir (path : String)
  /-- `unlinkFile`. -/
  | unlinkFile (path : String)
  /-- `readBytes`. -/
  | readBytes (path : String)
  /-- `writeBytes`. -/
  | writeBytes (path : String) (data : ByteArray)
  /-- Exclusive symlink-refusing `createFileNew`. -/
  | createFileNew (path : String) (data : ByteArray)
  /-- `appendText`. -/
  | appendText (path content : String)
  /-- `rename`. -/
  | rename (src dst : String)
  /-- `chmod`. -/
  | chmod (path : String) (mode : Nat)
  /-- `symlink`. -/
  | symlink (target linkPath : String)
  /-- `readLink`. -/
  | readLink (path : String)
  /-- `realPath`. -/
  | realPath (path : String)
  /-- `cwd`. -/
  | cwd
  /-- `monotonicNonce`. -/
  | monotonicNonce
  /-- Bracketed blocking `withFileLock` exercised with pure action outcome `actRes`. -/
  | withFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- Bracketed non-blocking `tryWithFileLock` exercised with pure action outcome `actRes`. -/
  | tryWithFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step output sum for `ScopedRawFsOpsM`. -/
inductive ScopedRawFsStepOut where
  /-- Output of `mapRawError`. -/
  | mapped (err : FsError)
  /-- Output of `stat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `readDir`. -/
  | names (res : Except FsError (Array String))
  /-- Output of `Unit`-returning primitives. -/
  | unit (res : Except FsError Unit)
  /-- Output of `readBytes`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `readLink`, `realPath`, and `cwd`. -/
  | str (res : Except FsError String)
  /-- Output of `monotonicNonce`. -/
  | nonce (n : Nat)
  /-- Output of `withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `ScopedRawFsStepReq` against a `ScopedRawFsOpsM (StateM W)` bundle. -/
def execScopedRawFsStep {W : Type} (ops : ScopedRawFsOpsM (StateM W)) :
    ScopedRawFsStepReq → StateM W ScopedRawFsStepOut
  | .mapRawError raw => pure (.mapped (ops.mapRawError raw))
  | .stat follow path => ScopedRawFsStepOut.stat <$> ops.stat follow path
  | .readDir path => ScopedRawFsStepOut.names <$> ops.readDir path
  | .createDir path => ScopedRawFsStepOut.unit <$> ops.createDir path
  | .removeDir path => ScopedRawFsStepOut.unit <$> ops.removeDir path
  | .unlinkFile path => ScopedRawFsStepOut.unit <$> ops.unlinkFile path
  | .readBytes path => ScopedRawFsStepOut.bytes <$> ops.readBytes path
  | .writeBytes path data => ScopedRawFsStepOut.unit <$> ops.writeBytes path data
  | .createFileNew path data => ScopedRawFsStepOut.unit <$> ops.createFileNew path data
  | .appendText path content => ScopedRawFsStepOut.unit <$> ops.appendText path content
  | .rename src dst => ScopedRawFsStepOut.unit <$> ops.rename src dst
  | .chmod path mode => ScopedRawFsStepOut.unit <$> ops.chmod path mode
  | .symlink target linkPath => ScopedRawFsStepOut.unit <$> ops.symlink target linkPath
  | .readLink path => ScopedRawFsStepOut.str <$> ops.readLink path
  | .realPath path => ScopedRawFsStepOut.str <$> ops.realPath path
  | .cwd => ScopedRawFsStepOut.str <$> ops.cwd
  | .monotonicNonce => ScopedRawFsStepOut.nonce <$> ops.monotonicNonce
  | .withFileLock path mode createIfMissing actRes =>
    ScopedRawFsStepOut.lockVal <$> ops.withFileLock path mode createIfMissing (pure actRes)
  | .tryWithFileLock path mode createIfMissing actRes =>
    ScopedRawFsStepOut.tryLockVal <$> ops.tryWithFileLock path mode createIfMissing (pure actRes)

/-- Behavioral trace-based relational step specification for `ScopedRawFsOpsM`. -/
def allowedScopedRawFsStep (w : FsWorld) (req : ScopedRawFsStepReq)
    (out : ScopedRawFsStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .mapped err =>
    match req with
    | .mapRawError raw => FsWorldTrace w [] w' ∧ w' = w ∧ err = mapRawError raw
    | _ => False
  | .stat res =>
    match req with
    | .stat follow path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok st => StatTrace none path.toUTF8 follow st tr
        | .error e =>
          nonLockErrOk e ∧
          (∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := !follow }, .err err) ∈ tr ∧
            (e.kind = .notFound → err = Errno.ENOENT))
    | _ => False
  | .names res =>
    match req with
    | .readDir path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok xs => ReadDirTrace path.toUTF8 xs tr
        | .error e => nonLockErrOk e ∧ tr ≠ []
    | _ => False
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
      match req, res with
      | .createDir path, .ok () => MkdirTrace none path.toUTF8 0o777 tr
      | .removeDir path, .ok () => UnlinkTrace none path.toUTF8 true tr
      | .unlinkFile path, .ok () => UnlinkTrace none path.toUTF8 false tr
      | .writeBytes path data, .ok () => WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 data tr
      | .createFileNew path data, .ok () => WriteFileTrace none path.toUTF8 createNewOpenFlags 0o644 data tr
      | .appendText path content, .ok () => WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 content.toUTF8 tr
      | .rename src dst, .ok () => RenameTrace none src.toUTF8 none dst.toUTF8 tr
      | .chmod path mode, .ok () => ChmodTrace none path.toUTF8 mode tr
      | .symlink target linkPath, .ok () => SymlinkTrace target.toUTF8 none linkPath.toUTF8 tr
      | .createFileNew path _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))
      | .createDir _, .error e | .removeDir _, .error e | .unlinkFile _, .error e
      | .writeBytes _ _, .error e | .appendText _ _, .error e | .rename _ _, .error e
      | .chmod _ _, .error e | .symlink _ _, .error e =>
        nonLockErrOk e ∧ tr ≠ []
      | _, _ => False
  | .bytes res =>
    match req with
    | .readBytes path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
        | .error e =>
          nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))
    | _ => False
  | .str res =>
    ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
      match req, res with
      | .readLink path, .ok s => ReadLinkTrace path.toUTF8 s tr
      | .realPath _, .ok s => RealPathTrace s tr
      | .cwd, .ok s => GetcwdTrace s tr
      | .readLink _, .error e | .cwd, .error e => nonLockErrOk e ∧ tr ≠ []
      | .realPath path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput)
      | _, _ => False
  | .nonce _ =>
    match req with
    | .monotonicNonce =>
      FsWorldTrace w [] w' ∧ w'.env = w.env
    | _ => False
  | .lockVal res =>
    match req with
    | .withFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok v => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode false true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode false false tr)
    | _ => False
  | .tryLockVal res =>
    match req with
    | .tryWithFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok none => TryLockContendedTrace none path.toUTF8 mode tr
        | .ok (some v) => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode true true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode true false tr)
    | _ => False

/-- Single-step request sum covering all 32 effectful operations of `FsApiM`. -/
inductive FsStepReq where
  /-- `api.readText`. -/
  | readText (path : String)
  /-- `api.writeText`. -/
  | writeText (path content : String)
  /-- `api.appendText`. -/
  | appendText (path content : String)
  /-- `api.readBytes`. -/
  | readBytes (path : String)
  /-- `api.writeBytes`. -/
  | writeBytes (path : String) (data : ByteArray)
  /-- `api.atomicWriteBytes`. -/
  | atomicWriteBytes (path : String) (data : ByteArray)
  /-- `api.atomicWriteText`. -/
  | atomicWriteText (path content : String)
  /-- `api.touch`. -/
  | touch (path : String) (existOk : Bool)
  /-- `api.mkdir`. -/
  | mkdir (path : String) (parents existOk : Bool)
  /-- `api.unlink`. -/
  | unlink (path : String) (missingOk : Bool)
  /-- `api.rmdir`. -/
  | rmdir (path : String)
  /-- `api.rmtree`. -/
  | rmtree (path : String) (ignoreMissing : Bool)
  /-- `api.rename`. -/
  | rename (src dst : String)
  /-- `api.copyFile`. -/
  | copyFile (src dst : String)
  /-- `api.copyTree`. -/
  | copyTree (src dst : String) (dirsExistOk : Bool)
  /-- `api.pathExists`. -/
  | pathExists (path : String)
  /-- `api.isFile`. -/
  | isFile (path : String)
  /-- `api.isDir`. -/
  | isDir (path : String)
  /-- `api.isSymlink`. -/
  | isSymlink (path : String)
  /-- `api.stat`. -/
  | stat (path : String)
  /-- `api.lstat`. -/
  | lstat (path : String)
  /-- `api.chmod`. -/
  | chmod (path : String) (mode : Nat)
  /-- `api.symlink`. -/
  | symlink (target linkPath : String)
  /-- `api.readLink`. -/
  | readLink (path : String)
  /-- `api.resolve`. -/
  | resolve (path : String)
  /-- `api.cwd`. -/
  | cwd
  /-- `api.listDir`. -/
  | listDir (path : String)
  /-- `api.walk`. -/
  | walk (root : String)
  /-- `api.glob`. -/
  | glob (root pattern : String)
  /-- `api.rglob`. -/
  | rglob (root pattern : String)
  /-- `api.withFileLock` exercised with pure action outcome `actRes`. -/
  | withFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- `api.tryWithFileLock` exercised with pure action outcome `actRes`. -/
  | tryWithFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step output sum for `FsApiM`. -/
inductive FsStepOut where
  /-- Output of `Unit`-returning operations. -/
  | unit (res : Except FsError Unit)
  /-- Output of boolean predicate queries (`pathExists`, `isFile`, `isDir`, `isSymlink`). -/
  | flag (res : Except FsError Bool)
  /-- Output of `stat` and `lstat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `readBytes`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `readText`, `readLink`, `resolve`, and `cwd`. -/
  | str (res : Except FsError String)
  /-- Output of sorted string-array queries (`listDir`, `glob`, `rglob`). -/
  | names (res : Except FsError (Array String))
  /-- Output of `walk`. -/
  | walkEntries (res : Except FsError (Array WalkEntry))
  /-- Output of `withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `FsStepReq` against an `FsApiM (StateM W)` bundle. -/
def execFsStep {W : Type} (api : FsApiM (StateM W)) : FsStepReq → StateM W FsStepOut
  | .readText path => FsStepOut.str <$> api.readText path
  | .writeText path content => FsStepOut.unit <$> api.writeText path content
  | .appendText path content => FsStepOut.unit <$> api.appendText path content
  | .readBytes path => FsStepOut.bytes <$> api.readBytes path
  | .writeBytes path data => FsStepOut.unit <$> api.writeBytes path data
  | .atomicWriteBytes path data => FsStepOut.unit <$> api.atomicWriteBytes path data
  | .atomicWriteText path content => FsStepOut.unit <$> api.atomicWriteText path content
  | .touch path existOk => FsStepOut.unit <$> api.touch path existOk
  | .mkdir path parents existOk => FsStepOut.unit <$> api.mkdir path parents existOk
  | .unlink path missingOk => FsStepOut.unit <$> api.unlink path missingOk
  | .rmdir path => FsStepOut.unit <$> api.rmdir path
  | .rmtree path ignoreMissing => FsStepOut.unit <$> api.rmtree path ignoreMissing
  | .rename src dst => FsStepOut.unit <$> api.rename src dst
  | .copyFile src dst => FsStepOut.unit <$> api.copyFile src dst
  | .copyTree src dst dirsExistOk => FsStepOut.unit <$> api.copyTree src dst dirsExistOk
  | .pathExists path => FsStepOut.flag <$> api.pathExists path
  | .isFile path => FsStepOut.flag <$> api.isFile path
  | .isDir path => FsStepOut.flag <$> api.isDir path
  | .isSymlink path => FsStepOut.flag <$> api.isSymlink path
  | .stat path => FsStepOut.stat <$> api.stat path
  | .lstat path => FsStepOut.stat <$> api.lstat path
  | .chmod path mode => FsStepOut.unit <$> api.chmod path mode
  | .symlink target linkPath => FsStepOut.unit <$> api.symlink target linkPath
  | .readLink path => FsStepOut.str <$> api.readLink path
  | .resolve path => FsStepOut.str <$> api.resolve path
  | .cwd => FsStepOut.str <$> api.cwd
  | .listDir path => FsStepOut.names <$> api.listDir path
  | .walk root => FsStepOut.walkEntries <$> api.walk root
  | .glob root pattern => FsStepOut.names <$> api.glob root pattern
  | .rglob root pattern => FsStepOut.names <$> api.rglob root pattern
  | .withFileLock path mode createIfMissing actRes =>
    FsStepOut.lockVal <$> api.withFileLock path mode createIfMissing (pure actRes)
  | .tryWithFileLock path mode createIfMissing actRes =>
    FsStepOut.tryLockVal <$> api.tryWithFileLock path mode createIfMissing (pure actRes)

/-- Behavioral trace witness for `atomicWriteBytes path data`: creates an exclusive `nofollow` sibling temp file with exact `data`, then atomically renames it onto `path`. -/
def AtomicWriteTrace (path : String) (data : ByteArray) (tr : List KernelStep) : Prop :=
  ∃ nonce : Nat,
    let tmpPath := join ((parent path).getD ".") s!".{(name path).getD "tmp"}.tmp.{nonce}"
    ∃ tr1 tr2 tr3,
      tr = tr1 ++ tr2 ++ tr3 ∧
      WriteFileTrace none tmpPath.toUTF8 createNewOpenFlags 0o644 data tr2 ∧
      RenameTrace none tmpPath.toUTF8 none path.toUTF8 tr3

/-- Behavioral trace witness for `mkdir path _ existOk`: either `mkdirat` created `path`, or `existOk = true` and `fstatat` confirmed an existing directory. -/
def MkdirOkTrace (path : String) (existOk : Bool) (tr : List KernelStep) : Prop :=
  MkdirTrace none path.toUTF8 0o777 tr ∨
  (existOk = true ∧ ∃ rawSt nf, (.fstatat none path.toUTF8 { symlinkNofollow := nf }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir)

/-- Behavioral trace witness that `root` was verified as a directory and scanned via `openat(O_DIRECTORY)` + `getdents64` EOF. -/
def WalkRootTrace (root : String) (tr : List KernelStep) : Prop :=
  (∃ rawSt, (.fstatat none root.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir) ∧
  (∃ h eof, (.openat none root.toUTF8 dirOpenFlags 0, .opened h) ∈ tr ∧ (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0)

/-- Behavioral trace-based relational step specification for all 32 effectful `FsApiM` operations over healthy Linux `FsWorld`. -/
def allowedFsStep (w : FsWorld) (req : FsStepReq) (out : FsStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .writeText path content, .ok () =>
        WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 content.toUTF8 tr
      | .appendText path content, .ok () =>
        WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 content.toUTF8 tr
      | .writeBytes path data, .ok () =>
        WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 data tr
      | .atomicWriteBytes path data, .ok () =>
        AtomicWriteTrace path data tr
      | .atomicWriteText path content, .ok () =>
        AtomicWriteTrace path content.toUTF8 tr
      | .touch path existOk, .ok () =>
        (existOk = true ∧ ∃ tr1 tr2, tr = tr1 ++ tr2 ∧
          WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 ByteArray.empty tr2) ∨
        (∃ tr1 tr2, tr = tr1 ++ tr2 ∧
          (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr1 ∧
          WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 ByteArray.empty tr2)
      | .mkdir path _ existOk, .ok () =>
        MkdirOkTrace path existOk tr
      | .unlink path missingOk, .ok () =>
        UnlinkTrace none path.toUTF8 false tr ∨
        (missingOk = true ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr)
      | .rmdir path, .ok () =>
        UnlinkTrace none path.toUTF8 true tr
      | .rmtree path ignoreMissing, .ok () =>
        UnlinkTrace none path.toUTF8 true tr ∨
        (ignoreMissing = true ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr)
      | .rename src dst, .ok () =>
        RenameTrace none src.toUTF8 none dst.toUTF8 tr
      | .copyFile src dst, .ok () =>
        ∃ bs tr1 tr2 tr3,
          tr = tr1 ++ tr2 ++ tr3 ∧
          ReadRegularTrace none src.toUTF8 readOpenFlags bs tr2 ∧
          WriteFileTrace none dst.toUTF8 writeOpenFlags 0o666 bs tr3
      | .copyTree src dst dirsExistOk, .ok () =>
        (∃ rawSt, (.fstatat none src.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir) ∧
        MkdirOkTrace dst dirsExistOk tr
      | .chmod path mode, .ok () =>
        ChmodTrace none path.toUTF8 mode tr
      | .symlink target linkPath, .ok () =>
        SymlinkTrace target.toUTF8 none linkPath.toUTF8 tr
      | .atomicWriteBytes path _, .error e | .atomicWriteText path _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/"))
      | .writeText _ _, .error e | .appendText _ _, .error e | .writeBytes _ _, .error e
      | .touch _ _, .error e | .mkdir _ _ _, .error e | .unlink _ _, .error e
      | .rmdir _, .error e | .rmtree _ _, .error e | .rename _ _, .error e
      | .copyFile _ _, .error e | .copyTree _ _ _, .error e | .chmod _ _, .error e
      | .symlink _ _, .error e =>
        nonLockErrOk e ∧ tr ≠ []
      | _, _ => False
  | .flag res =>
    match res with
    | .ok b =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match req with
        | .pathExists path =>
          (b = true ∧ ∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isFile path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .reg)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isDir path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .dir)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isSymlink path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .symlink)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err err) ∈ tr)
        | _ => False
    | .error _ => False
  | .stat res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .stat path, .ok st => StatTrace none path.toUTF8 true st tr
      | .lstat path, .ok st => StatTrace none path.toUTF8 false st tr
      | .stat path, .error e =>
        nonLockErrOk e ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr
      | .lstat path, .error e =>
        nonLockErrOk e ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err err) ∈ tr
      | _, _ => False
  | .bytes res =>
    match req with
    | .readBytes path =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
        | .error e =>
          nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))
    | _ => False
  | .str res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .readText path, .ok s =>
        ∃ bs, String.fromUTF8? bs = some s ∧ ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
      | .readLink path, .ok s => ReadLinkTrace path.toUTF8 s tr
      | .resolve _, .ok s => RealPathTrace s tr
      | .cwd, .ok s => GetcwdTrace s tr
      | .readText path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))
      | .readLink _, .error e | .cwd, .error e => nonLockErrOk e ∧ tr ≠ []
      | .resolve path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput)
      | _, _ => False
  | .names res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .listDir path, .ok xs =>
        List.Pairwise (· ≤ ·) xs.toList ∧ ReadDirTrace path.toUTF8 xs tr
      | .glob root _, .ok xs | .rglob root _, .ok xs =>
        List.Pairwise (· ≤ ·) xs.toList ∧ WalkRootTrace root tr
      | .listDir _, .error e => nonLockErrOk e ∧ tr ≠ []
      | .glob _ _, .error e | .rglob _ _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput)
      | _, _ => False
  | .walkEntries res =>
    match req with
    | .walk root =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok entries =>
          (∀ e ∈ entries.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
          entries.size > 0 ∧
          WalkRootTrace root tr
        | .error e => nonLockErrOk e ∧ tr ≠ []
    | _ => False
  | .lockVal res =>
    match req with
    | .withFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok v => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode false true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode false false tr)
    | _ => False
  | .tryLockVal res =>
    match req with
    | .tryWithFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok none => TryLockContendedTrace none path.toUTF8 mode tr
        | .ok (some v) => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode true true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode true false tr)
    | _ => False

end LeanSwe.Fs.Model
