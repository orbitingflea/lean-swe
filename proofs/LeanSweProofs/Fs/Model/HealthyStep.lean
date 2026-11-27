import LeanSweProofs.Fs.Model.HealthyStepBase
import LeanSweProofs.Fs.Model.HealthyStepScoped

namespace LeanSwe.Fs.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs

/-- Finite single-operation request inside an open `SubtreeM` capability. -/
inductive SubtreeOpReq where
  /-- `sub.lstat`. -/
  | lstat (rel : RelPath)
  /-- `sub.readRegular`. -/
  | readRegular (rel : RelPath)
  /-- `sub.atomicWriteBytes`. -/
  | atomicWriteBytes (rel : RelPath) (data : ByteArray)
  /-- `sub.mkdir`. -/
  | mkdir (rel : RelPath) (parents existOk : Bool)
  /-- `sub.unlink`. -/
  | unlink (rel : RelPath) (missingOk : Bool)
  /-- `sub.rmdir`. -/
  | rmdir (rel : RelPath)
  /-- `sub.rmtree`. -/
  | rmtree (rel : RelPath) (ignoreMissing : Bool)
  /-- `sub.symlink`. -/
  | symlink (target : String) (rel : RelPath)
  /-- `sub.listDir`. -/
  | listDir (rel : RelPath)
  /-- `sub.walk`. -/
  | walk (rel : RelPath)
  /-- `sub.withFileLock` with pure action outcome `actRes`. -/
  | withFileLock (rel : RelPath) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- `sub.tryWithFileLock` with pure action outcome `actRes`. -/
  | tryWithFileLock (rel : RelPath) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step request opening `rootPath` via `withSubtree` and running `op`. -/
structure SubtreeStepReq where
  /-- Host path to open as the confined subtree root. -/
  rootPath : String
  /-- Operation to execute inside `withSubtree`. -/
  op : SubtreeOpReq

/-- Single-step output sum for `SubtreeOpenerM.withSubtree`. -/
inductive SubtreeStepOut where
  /-- Output of `sub.lstat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `sub.readRegular`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `Unit`-returning subtree operations. -/
  | unit (res : Except FsError Unit)
  /-- Output of `sub.listDir`. -/
  | entryNames (res : Except FsError (Array EntryName))
  /-- Output of `sub.walk`. -/
  | walkEntries (res : Except FsError (Array WalkEntry))
  /-- Output of `sub.withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `sub.tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `SubtreeStepReq` against a `SubtreeOpenerM (StateM W)` capability bundle. -/
def execSubtreeStep {W : Type} (opener : SubtreeOpenerM (StateM W)) (req : SubtreeStepReq) :
    StateM W SubtreeStepOut :=
  match req.op with
  | .lstat rel => SubtreeStepOut.stat <$> opener.withSubtree req.rootPath (·.lstat rel)
  | .readRegular rel => SubtreeStepOut.bytes <$> opener.withSubtree req.rootPath (·.readRegular rel)
  | .atomicWriteBytes rel data =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.atomicWriteBytes rel data)
  | .mkdir rel parents existOk =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.mkdir rel parents existOk)
  | .unlink rel missingOk =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.unlink rel missingOk)
  | .rmdir rel => SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.rmdir rel)
  | .rmtree rel ignoreMissing =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.rmtree rel ignoreMissing)
  | .symlink target rel =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.symlink target rel)
  | .listDir rel => SubtreeStepOut.entryNames <$> opener.withSubtree req.rootPath (·.listDir rel)
  | .walk rel => SubtreeStepOut.walkEntries <$> opener.withSubtree req.rootPath (·.walk rel)
  | .withFileLock rel mode createIfMissing actRes =>
    SubtreeStepOut.lockVal <$>
      opener.withSubtree req.rootPath (·.withFileLock rel mode createIfMissing (pure actRes))
  | .tryWithFileLock rel mode createIfMissing actRes =>
    SubtreeStepOut.tryLockVal <$>
      opener.withSubtree req.rootPath (·.tryWithFileLock rel mode createIfMissing (pure actRes))

/-- Descriptor-confined trace decomposition for an entered `withSubtree rootPath` execution: opens `rootPath` once with `O_DIRECTORY`, runs only `SubtreeConfinedReq` steps inside `trInner` preserving `[rootDh]`, and closes `rootDh` on exit. -/
def SubtreeConfinedTrace (rootPath : String) (tr : List KernelStep)
    (bodyProp : HandleId → List KernelStep → Prop) : Prop :=
  ∃ rootDh trOpen trInner trClose,
    tr = trOpen ++ trInner ++ trClose ∧
    (.openat none rootPath.toUTF8 dirOpenFlags 0, .opened rootDh) ∈ trOpen ∧
    (∀ s ∈ trOpen, ∃ o, s = (.openat none rootPath.toUTF8 dirOpenFlags 0, o)) ∧
    TraceFds [rootDh] trInner [rootDh] ∧
    (∀ s ∈ trInner, SubtreeConfinedReq s.1) ∧
    (∃ co, trClose = [(.close rootDh, co)]) ∧
    bodyProp rootDh trInner

/-- Confined trace witness for any `withSubtree` error: either invalid root path before opening, failed `openat(O_DIRECTORY)` of `rootPath`, or a confined execution that closed `rootDh`. -/
def SubtreeErrTrace (rootPath : String) (e : FsError) (tr : List KernelStep) : Prop :=
  nonLockErrOk e ∧
  ((tr = [] ∧ isValidRawPath rootPath = false ∧ e.kind = .invalidInput) ∨
   (tr ≠ [] ∧ ∀ s ∈ tr, ∃ o, s = (.openat none rootPath.toUTF8 dirOpenFlags 0, o)) ∨
   SubtreeConfinedTrace rootPath tr (fun _ _ => True))

/-- Behavioral and descriptor-confinement relational step specification for `SubtreeOpenerM.withSubtree` and all 12 `SubtreeM` methods over healthy Linux `FsWorld`. -/
def allowedSubtreeStep (w : FsWorld) (req : SubtreeStepReq)
    (out : SubtreeStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .stat res =>
    match req.op with
    | .lstat rel =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok st =>
          SubtreeConfinedTrace req.rootPath tr fun rootDh trInner =>
            match splitLastAux rel.segments [] with
            | none => FstatTrace rootDh st trInner
            | some (_, leaf) => ∃ d, StatTrace (some d) leaf.val.toUTF8 false st trInner
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .bytes res =>
    match req.op with
    | .readRegular rel =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok bs =>
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              ReadRegularTrace (some d) leaf.val.toUTF8 readAtOpenFlags bs sub
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req.op, res with
      | .atomicWriteBytes rel data, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d, ∃ tmp : EntryName, ∃ sub1 sub2,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            Subtrace (sub1 ++ sub2) trInner ∧
            WriteFileTrace (some d) tmp.val.toUTF8 createNewOpenFlags 0o644 data sub1 ∧
            RenameTrace (some d) tmp.val.toUTF8 (some d) leaf.val.toUTF8 sub2
      | .mkdir rel _ existOk, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun rootDh trInner =>
          match splitLastAux rel.segments [] with
          | none => existOk = true ∧ ∃ rawSt, (.fstat rootDh, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir
          | some (_, leaf) =>
            ∃ d, MkdirTrace (some d) leaf.val.toUTF8 0o755 trInner ∨
              (existOk = true ∧ ∃ rawSt, (.fstatat (some d) leaf.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir)
      | .unlink rel missingOk, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 false trInner) ∨
             (missingOk = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner))
      | .rmdir rel, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            UnlinkTrace (some d) leaf.val.toUTF8 true trInner
      | .rmtree rel ignoreMissing, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 true trInner) ∨
             (ignoreMissing = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner))
      | .symlink target rel, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            SymlinkTrace target.toUTF8 (some d) leaf.val.toUTF8 trInner
      | .atomicWriteBytes _ _, .error e | .mkdir _ _ _, .error e | .unlink _ _, .error e
      | .rmdir _, .error e | .rmtree _ _, .error e | .symlink _ _, .error e =>
        SubtreeErrTrace req.rootPath e tr
      | _, _ => False
  | .entryNames res =>
    match req.op with
    | .listDir _ =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok xs =>
          List.Pairwise (fun a b => a.val ≤ b.val) xs.toList ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ h eof,
              (.getdents64 h 8192, .bytes eof) ∈ trInner ∧
              eof.size = 0 ∧
              (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ trInner ∧ buf.size > 0)
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .walkEntries res =>
    match req.op with
    | .walk _ =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok entries =>
          (∀ e ∈ entries.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
          entries.size > 0 ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ trInner ∧ eof.size = 0
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .lockVal res =>
    match req.op with
    | .withFileLock rel mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok v =>
          actRes = .ok v ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              FileLockTrace (some d) leaf.val.toUTF8 mode false true sub
        | .error e =>
          SubtreeErrTrace req.rootPath e tr ∨
          (actRes = .error e ∧
            SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
              ∃ pre leaf d sub,
                splitLastAux rel.segments [] = some (pre, leaf) ∧
                Subtrace sub trInner ∧
                FileLockTrace (some d) leaf.val.toUTF8 mode false false sub)
    | _ => False
  | .tryLockVal res =>
    match req.op with
    | .tryWithFileLock rel mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok none =>
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              TryLockContendedTrace (some d) leaf.val.toUTF8 mode sub
        | .ok (some v) =>
          actRes = .ok v ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              FileLockTrace (some d) leaf.val.toUTF8 mode true true sub
        | .error e =>
          SubtreeErrTrace req.rootPath e tr ∨
          (actRes = .error e ∧
            SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
              ∃ pre leaf d sub,
                splitLastAux rel.segments [] = some (pre, leaf) ∧
                Subtrace sub trInner ∧
                FileLockTrace (some d) leaf.val.toUTF8 mode true false sub)
    | _ => False

end LeanSwe.Fs.Model
