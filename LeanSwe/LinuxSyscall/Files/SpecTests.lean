import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Files.Seed

namespace LeanSwe.LinuxSyscall.Files

open Core (NondetTest ErrorObligation ErrorJustification ErrorTestMode AssumptionObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Errno.isTransientOsErrno` matches exactly `{EINTR, EIO, ENOMEM, ENFILE, EMFILE, ENOSPC}`, excludes `EFAULT`, and `FilesErrorKind.ofErrno` classifies all core Linux errnos into their exact semantic buckets. -/
def test_files_errno_classificationAndTransient
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → FilesErrorKind := FilesErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  NondetTest.assert (classify Errno.ENOENT = .notFound)
  NondetTest.assert (classify Errno.EBADF = .badFd)
  NondetTest.assert (classify Errno.EINVAL = .invalidArg)
  NondetTest.assert (classify Errno.ENAMETOOLONG = .invalidArg)
  NondetTest.assert (classify Errno.EXDEV = .invalidArg)
  NondetTest.assert (classify Errno.ERANGE = .invalidArg)
  NondetTest.assert (classify Errno.EEXIST = .stateConflict)
  NondetTest.assert (classify Errno.ENOTDIR = .stateConflict)
  NondetTest.assert (classify Errno.EISDIR = .stateConflict)
  NondetTest.assert (classify Errno.ENOTEMPTY = .stateConflict)
  NondetTest.assert (classify Errno.ELOOP = .stateConflict)
  NondetTest.assert (classify Errno.EAGAIN = .stateConflict)
  NondetTest.assert (classify Errno.EBUSY = .stateConflict)
  NondetTest.assert (classify Errno.EOPNOTSUPP = .invalidArg)
  NondetTest.assert (classify Errno.ENOSYS = .invalidArg)
  NondetTest.assert (classify Errno.EACCES = .permissionDenied)
  NondetTest.assert (classify Errno.EPERM = .permissionDenied)
  NondetTest.assert (classify Errno.EROFS = .permissionDenied)
  NondetTest.assert (classify Errno.EINTR = .transientOrResource)
  NondetTest.assert (classify Errno.EIO = .transientOrResource)
  NondetTest.assert (classify Errno.ENOMEM = .transientOrResource)
  NondetTest.assert (classify Errno.ENFILE = .transientOrResource)
  NondetTest.assert (classify Errno.EMFILE = .transientOrResource)
  NondetTest.assert (classify Errno.ENOSPC = .transientOrResource)

/-- Exact C-ABI wire bitmasks and tag values decoded by `files_shim.c` across all 9 symbolic encoders. -/
def test_files_flags_exactWireValues
    {runner} [NondetTest runner]
    (encOpen : OpenFlags → UInt32 := OpenFlags.toBits)
    (encResolve : ResolveFlags → UInt64 := ResolveFlags.toBits)
    (encAt : AtFlags → UInt32 := AtFlags.toBits)
    (encAcc : AccessModeMask → UInt32 := AccessModeMask.toBits)
    (encRen : RenameFlags → UInt32 := RenameFlags.toBits)
    (encFlock : FlockOp → UInt32 := FlockOp.toBits)
    (encFcntl : FcntlCmd → UInt32 × UInt32 := FcntlCmd.toRaw)
    (encWhence : SeekWhence → UInt32 := SeekWhence.toRaw)
    (encStdio : StdioFd → UInt32 := StdioFd.toRaw) : runner Unit := do
  let o ← nondet OpenFlags
  let r ← nondet ResolveFlags
  let a ← nondet AtFlags
  let m ← nondet AccessModeMask
  let rn ← nondet RenameFlags
  let s ← nondet UInt32
  NondetTest.assert (encOpen { access := .rdonly, cloexec := false } = 0 ∧
    encOpen { access := .wronly, cloexec := false } = 1 ∧
    encOpen { access := .rdwr, cloexec := false } = 2 ∧
    encOpen { creat := true, cloexec := false } = 4 ∧
    encOpen { excl := true, cloexec := false } = 8 ∧
    encOpen { trunc := true, cloexec := false } = 16 ∧
    encOpen { append := true, cloexec := false } = 32 ∧
    encOpen { nofollow := true, cloexec := false } = 64 ∧
    encOpen { directory := true, cloexec := false } = 128 ∧
    encOpen { nonblock := true, cloexec := false } = 256 ∧
    encOpen { cloexec := true } = 512 ∧
    encOpen { noctty := true, cloexec := false } = 1024 ∧
    encOpen { path := true, cloexec := false } = 2048 ∧
    encOpen o =
      ((match o.access with | .rdonly => 0 | .wronly => 1 | .rdwr => 2) |||
       (if o.creat then 4 else 0) ||| (if o.excl then 8 else 0) |||
       (if o.trunc then 16 else 0) ||| (if o.append then 32 else 0) |||
       (if o.nofollow then 64 else 0) ||| (if o.directory then 128 else 0) |||
       (if o.nonblock then 256 else 0) ||| (if o.cloexec then 512 else 0) |||
       (if o.noctty then 1024 else 0) ||| (if o.path then 2048 else 0)))
  NondetTest.assert (encResolve {} = 0 ∧
    encResolve { noXdev := true } = 1 ∧ encResolve { noMagiclinks := true } = 2 ∧
    encResolve { noSymlinks := true } = 4 ∧ encResolve { beneath := true } = 8 ∧
    encResolve { inRoot := true } = 16 ∧ encResolve { cached := true } = 32 ∧
    encResolve r =
      ((if r.noXdev then 1 else 0) ||| (if r.noMagiclinks then 2 else 0) |||
       (if r.noSymlinks then 4 else 0) ||| (if r.beneath then 8 else 0) |||
       (if r.inRoot then 16 else 0) ||| (if r.cached then 32 else 0)))
  NondetTest.assert (encAt {} = 0 ∧
    encAt { symlinkNofollow := true } = 1 ∧
    encAt { emptyPath := true } = 2 ∧
    encAt { eaccess := true } = 4 ∧
    encAt a =
      ((if a.symlinkNofollow then 1 else 0) ||| (if a.emptyPath then 2 else 0) |||
       (if a.eaccess then 4 else 0)))
  NondetTest.assert (encAcc {} = 0 ∧
    encAcc { read := true } = 1 ∧ encAcc { write := true } = 2 ∧ encAcc { exec := true } = 4 ∧
    encAcc m =
      ((if m.read then 1 else 0) ||| (if m.write then 2 else 0) ||| (if m.exec then 4 else 0)))
  NondetTest.assert (encRen {} = 0 ∧
    encRen { noreplace := true } = 1 ∧ encRen { exchange := true } = 2 ∧ encRen { whiteout := true } = 4 ∧
    encRen rn =
      ((if rn.noreplace then 1 else 0) ||| (if rn.exchange then 2 else 0) |||
       (if rn.whiteout then 4 else 0)))
  NondetTest.assert (encFlock (.shared false) = 1 ∧ encFlock (.shared true) = 9 ∧
    encFlock (.exclusive false) = 2 ∧ encFlock (.exclusive true) = 10 ∧
    encFlock .unlock = 4)
  NondetTest.assert (encFcntl .getFl = (0, 0) ∧
    encFcntl (.setFl false false) = (1, 0) ∧ encFcntl (.setFl true false) = (1, 1) ∧
    encFcntl (.setFl false true) = (1, 2) ∧ encFcntl (.setFl true true) = (1, 3) ∧
    encFcntl .getFd = (2, 0) ∧ encFcntl (.setFd false) = (3, 0) ∧
    encFcntl (.setFd true) = (3, 1) ∧ encFcntl (.addSeals s) = (4, s) ∧
    encFcntl .getSeals = (5, 0))
  NondetTest.assert (encWhence .seekSet = 0 ∧ encWhence .seekCur = 1 ∧ encWhence .seekEnd = 2)
  NondetTest.assert (encStdio .stdin = 0 ∧ encStdio .stdout = 1 ∧ encStdio .stderr = 2)

/-- Portable symbolic flag encoders (`OpenFlags.toBits`, `ResolveFlags.toBits`, `AtFlags.toBits`, `AccessModeMask.toBits`, `RenameFlags.toBits`, `FlockOp.toBits`, `FcntlCmd.toRaw`, `SeekWhence.toRaw`, `StdioFd.toRaw`) are injective with zero bit collisions. -/
def test_files_flags_encodersInjective
    {runner} [NondetTest runner]
    (encOpen : OpenFlags → UInt32 := OpenFlags.toBits)
    (encResolve : ResolveFlags → UInt64 := ResolveFlags.toBits)
    (encAt : AtFlags → UInt32 := AtFlags.toBits)
    (encAcc : AccessModeMask → UInt32 := AccessModeMask.toBits)
    (encRen : RenameFlags → UInt32 := RenameFlags.toBits)
    (encFlock : FlockOp → UInt32 := FlockOp.toBits)
    (encFcntl : FcntlCmd → UInt32 × UInt32 := FcntlCmd.toRaw)
    (encWhence : SeekWhence → UInt32 := SeekWhence.toRaw)
    (encStdio : StdioFd → UInt32 := StdioFd.toRaw) : runner Unit := do
  let o1 ← nondet OpenFlags
  let o2 ← nondet OpenFlags
  NondetTest.assert ((encOpen o1 == encOpen o2) = (o1 == o2))
  let r1 ← nondet ResolveFlags
  let r2 ← nondet ResolveFlags
  NondetTest.assert ((encResolve r1 == encResolve r2) = (r1 == r2))
  let a1 ← nondet AtFlags
  let a2 ← nondet AtFlags
  NondetTest.assert ((encAt a1 == encAt a2) = (a1 == a2))
  let m1 ← nondet AccessModeMask
  let m2 ← nondet AccessModeMask
  NondetTest.assert ((encAcc m1 == encAcc m2) = (m1 == m2))
  let rn1 ← nondet RenameFlags
  let rn2 ← nondet RenameFlags
  NondetTest.assert ((encRen rn1 == encRen rn2) = (rn1 == rn2))
  let fl1 ← nondet FlockOp
  let fl2 ← nondet FlockOp
  NondetTest.assert ((encFlock fl1 == encFlock fl2) = (fl1 == fl2))
  let fc1 ← nondet FcntlCmd
  let fc2 ← nondet FcntlCmd
  NondetTest.assert ((encFcntl fc1 == encFcntl fc2) = (fc1 == fc2))
  let w1 ← nondet SeekWhence
  let w2 ← nondet SeekWhence
  NondetTest.assert ((encWhence w1 == encWhence w2) = (w1 == w2))
  let s1 ← nondet StdioFd
  let s2 ← nondet StdioFd
  NondetTest.assert ((encStdio s1 == encStdio s2) = (s1 == s2))

/-- `StatInfo.ofRawTuple` decodes all 8 `FileKind` tags (`0..6` and `>= 7` -> `.other`), masks `mode` to the lower 12 bits (`0o7777`), and preserves `size`, `ino`, `dev`, `nlink`, `mtime`, and `atime`. -/
def test_files_statInfo_ofRawTuple_decodesAllKindsAndMasksMode
    {runner} [NondetTest runner]
    (decode : RawStatTuple → StatInfo := StatInfo.ofRawTuple) : runner Unit := do
  let sz ← nondet UInt64
  let rawMode ← nondet UInt32
  let ino ← nondet UInt64
  let dev ← nondet UInt64
  let nlink ← nondet UInt64
  let mSec ← nondet Int
  let mNsec ← nondet UInt32
  let aSec ← nondet Int
  let aNsec ← nondet UInt32
  let mk (k : UInt8) : StatInfo := decode (k, sz, rawMode, ino, dev, nlink, mSec, mNsec, aSec, aNsec)
  NondetTest.assert ((mk 0).kind = .reg ∧ (mk 1).kind = .dir ∧ (mk 2).kind = .symlink ∧
    (mk 3).kind = .fifo ∧ (mk 4).kind = .socket ∧ (mk 5).kind = .charDev ∧
    (mk 6).kind = .blockDev ∧ (mk 7).kind = .other ∧ (mk 255).kind = .other)
  let st := mk 0
  NondetTest.assert (st.size = sz.toNat ∧ st.mode = (rawMode &&& 0o7777) ∧
    st.ino = ino ∧ st.dev = dev ∧ st.nlink = nlink.toNat ∧
    st.mtimeSec = mSec ∧ st.mtimeNsec = mNsec ∧ st.atimeSec = aSec ∧ st.atimeNsec = aNsec)

/-- Every path-taking operation in `FilesOpsM` rejects any path containing an embedded NUL byte (`0x00`) with `Errno.EINVAL` and leaves state unchanged. -/
def test_files_ops_embeddedNulRejectedWithEinval
    {S fd : Type} {runner} [NondetTest runner] (ops : FilesOpsM (StateM S) fd) : runner Unit := do
  let s₀ ← nondet S
  let dir ← nondet (Option fd)
  let flags ← nondet OpenFlags
  let how ← nondet OpenHow
  let atFlags ← nondet AtFlags
  let mask ← nondet AccessModeMask
  let mode ← nondet Mode
  let rmDir ← nondet Bool
  let renFlags ← nondet RenameFlags
  let cap ← nondet UInt32
  let badPath ← nondet ByteArray
  assume (hasEmbeddedNul badPath = true)
  let cleanPath := asciiBytes ['o', 'k']
  NondetTest.assert ((ops.openat dir badPath flags mode).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.openat2 dir badPath how).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.fstatat dir badPath atFlags).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.faccessat dir badPath mask atFlags).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.mkdirat dir badPath mode).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.unlinkat dir badPath rmDir).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.renameat2 dir badPath dir cleanPath renFlags).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.renameat2 dir cleanPath dir badPath renFlags).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.symlinkat badPath dir cleanPath).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.symlinkat cleanPath dir badPath).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.readlinkat dir badPath cap).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.fchmodat dir badPath mode).run s₀ = (.error Errno.EINVAL, s₀))

/-- Creating a regular file via `openat`, writing `payload`, re-opening to `read` back, inspecting `fstat`, closing, and re-using the closed descriptor fails deterministically with `Errno.EBADF`. -/
def test_files_ops_openWriteReadStatCloseAndUseAfterClose
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let payload := asciiBytes ['h', 'e', 'l', 'l', 'o', '-', 'l', 'i', 'n', 'u', 'x']
  let name := asciiBytes ['r', 'o', 'u', 'n', 'd', 't', 'r', 'i', 'p', '.', 'b', 'i', 'n']
  let (rOpen, s₁) := (ops.openat none name { access := .rdwr, creat := true, excl := true } 0o644).run s₀
  match rOpen with
  | .error _ => NondetTest.assert False
  | .ok h =>
    let (rDup, sDup) := (ops.openat none name { access := .rdwr, creat := true, excl := true } 0o644).run s₁
    NondetTest.assert (rDup = .error Errno.EEXIST ∧ sDup = s₁)
    let (rWr, s₂) := (ops.write h payload).run s₁
    match rWr with
    | .error _ => NondetTest.assert False
    | .ok n =>
      NondetTest.assert (1 ≤ n.toNat ∧ n.toNat ≤ payload.size)
      let (rSt, s₃) := (ops.fstat h).run s₂
      match rSt with
      | .error _ => NondetTest.assert False
      | .ok st =>
        NondetTest.assert (st.kind = .reg ∧ st.size = n.toNat ∧ st.nlink = 1)
        let (rCl, s₄) := (ops.close h).run s₃
        NondetTest.assert (rCl = .ok ())
        NondetTest.assert (((ops.read h 16).run s₄).1 = .error Errno.EBADF)
        NondetTest.assert (((ops.write h payload).run s₄).1 = .error Errno.EBADF)
        NondetTest.assert (((ops.fstat h).run s₄).1 = .error Errno.EBADF)
        NondetTest.assert (((ops.close h).run s₄).1 = .error Errno.EBADF)
        let (rRdOpen, s₅) := (ops.openat none name { access := .rdonly } 0).run s₄
        match rRdOpen with
        | .error _ => NondetTest.assert False
        | .ok rh =>
          let (rRd, s₆) := (ops.read rh (UInt32.ofNat n.toNat)).run s₅
          match rRd with
          | .error _ => NondetTest.assert False
          | .ok got =>
            NondetTest.assert (1 ≤ got.size ∧ got.size ≤ n.toNat ∧ got = sliceBytes payload 0 got.size)
            let (rWrRo, s₇) := (ops.write rh payload).run s₆
            NondetTest.assert (rWrRo = .error Errno.EBADF ∧ s₇ = s₆)
            let (rCl2, _) := (ops.close rh).run s₇
            NondetTest.assert (rCl2 = .ok ())

/-- `openat2` enforces strict Linux `open_how` validation (`mode != 0` without `O_CREAT`, `mode > 0o7777` with `O_CREAT`, `beneath && inRoot` -> `EINVAL`, `cached` with `O_CREAT` -> `EAGAIN`/`EINVAL`, while `O_EXCL` without `O_CREAT` is ignored and proceeds to lookup), `RESOLVE_BENEATH` escape rejection (`EXDEV`), and `RESOLVE_NO_SYMLINKS` rejection (`ELOOP`). -/
def test_files_ops_openat2_resolveConstraints
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rBadMode, s₁) := (ops.openat2 none (asciiBytes ['a']) { flags := { creat := false }, mode := 0o644 }).run s₀
  NondetTest.assert (rBadMode = .error Errno.EINVAL ∧ s₁ = s₀)
  let (rHighMode, sHm) := (ops.openat2 none (asciiBytes ['a']) { flags := { creat := true }, mode := 0o10644 }).run s₀
  NondetTest.assert (rHighMode = .error Errno.EINVAL ∧ sHm = s₀)
  let (rExclNoCreat, s₂) := (ops.openat2 none (asciiBytes ['a']) { flags := { creat := false, excl := true }, mode := 0 }).run s₀
  NondetTest.assert (rExclNoCreat = .error Errno.ENOENT ∧ s₂ = s₀)
  let (rBothRes, sBr) := (ops.openat2 none (asciiBytes ['a'])
    { flags := { access := .rdonly }, mode := 0, resolve := { beneath := true, inRoot := true } }).run s₀
  NondetTest.assert (rBothRes = .error Errno.EINVAL ∧ sBr = s₀)
  let (rCachedCreat, sCc) := (ops.openat2 none (asciiBytes ['a'])
    { flags := { access := .rdwr, creat := true }, mode := 0o644, resolve := { cached := true } }).run s₀
  NondetTest.assert ((rCachedCreat = .error Errno.EAGAIN ∨ rCachedCreat = .error Errno.EINVAL) ∧ sCc = s₀)
  let (rEscRel, s₃) := (ops.openat2 none (asciiBytes ['.', '.', '/', 'e', 's', 'c', 'a', 'p', 'e'])
    { flags := { access := .rdonly }, mode := 0, resolve := { beneath := true } }).run s₀
  NondetTest.assert (rEscRel = .error Errno.EXDEV ∧ s₃ = s₀)
  let (rEscAbs, s₄) := (ops.openat2 none (asciiBytes ['/', 'e', 't', 'c', '/', 'p', 'a', 's', 's', 'w', 'd'])
    { flags := { access := .rdonly }, mode := 0, resolve := { beneath := true } }).run s₀
  NondetTest.assert (rEscAbs = .error Errno.EXDEV ∧ s₄ = s₀)
  let (rSym, s₅) := (ops.symlinkat (asciiBytes ['t', 'a', 'r', 'g', 'e', 't']) none (asciiBytes ['l', 'i', 'n', 'k'])).run s₀
  NondetTest.assert (rSym = .ok ())
  let (rNoSym, s₆) := (ops.openat2 none (asciiBytes ['l', 'i', 'n', 'k'])
    { flags := { access := .rdonly }, mode := 0, resolve := { noSymlinks := true } }).run s₅
  NondetTest.assert (rNoSym = .error Errno.ELOOP ∧ s₆ = s₅)

/-- Directory lifecycle (`mkdirat`, `unlinkat`, `renameat2`, `getdents64`) enforces duplicate rejection (`EEXIST`), `EISDIR`/`ENOTDIR`/`ENOTEMPTY`, `getdents64` buffer bounds and EOF, trailing-slash `ENOTDIR`, `RENAME_NOREPLACE`, and `RENAME_NOREPLACE | RENAME_EXCHANGE` (`EINVAL`). -/
def test_files_ops_dirLifecycleAndRenameat2
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rMk, s₁) := (ops.mkdirat none (asciiBytes ['s', 'u', 'b']) 0o755).run s₀
  NondetTest.assert (rMk = .ok ())
  let (rMkDup, sDup) := (ops.mkdirat none (asciiBytes ['s', 'u', 'b']) 0o755).run s₁
  NondetTest.assert (rMkDup = .error Errno.EEXIST ∧ sDup = s₁)
  let (rUnFile, sUnF) := (ops.unlinkat none (asciiBytes ['s', 'u', 'b']) false).run s₁
  NondetTest.assert (rUnFile = .error Errno.EISDIR ∧ sUnF = s₁)
  let (rF1, s₂) := (ops.openat none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r']) { access := .wronly, creat := true } 0o644).run s₁
  match rF1 with
  | .error _ => NondetTest.assert False
  | .ok fh =>
    let (rGdReg, _) := (ops.getdents64 fh 4096).run s₂
    NondetTest.assert (rGdReg = .error Errno.ENOTDIR)
    let (rCl, s₃) := (ops.close fh).run s₂
    NondetTest.assert (rCl = .ok ())
    let (rDirOpen, sDo) := (ops.openat none (asciiBytes ['s', 'u', 'b']) { access := .rdonly, directory := true } 0).run s₃
    match rDirOpen with
    | .error _ => NondetTest.assert False
    | .ok dfd =>
      let (rGdSmall, sGs) := (ops.getdents64 dfd 8).run sDo
      NondetTest.assert (rGdSmall = .error Errno.EINVAL)
      let (rGdOk, sGo) := (ops.getdents64 dfd 4096).run sGs
      NondetTest.assert (∃ bs, rGdOk = .ok bs ∧ bs.size ≥ 24)
      let (_, s₃') := (ops.close dfd).run sGo
      let (rNonEmpty, sNe) := (ops.unlinkat none (asciiBytes ['s', 'u', 'b']) true).run s₃'
      NondetTest.assert ((rNonEmpty = .error Errno.ENOTEMPTY ∨ rNonEmpty = .error Errno.EEXIST) ∧ sNe = s₃')
      let (rTrailSrc, sTs) := (ops.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r', '/'])
        none (asciiBytes ['s', 'u', 'b', '/', 'o', 't', 'h', 'e', 'r']) {}).run s₃'
      NondetTest.assert (rTrailSrc = .error Errno.ENOTDIR ∧ sTs = s₃')
      let (rBadRen, sBr) := (ops.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
        none (asciiBytes ['s', 'u', 'b', '/', 'o', 't', 'h', 'e', 'r'])
        { noreplace := true, exchange := true }).run s₃'
      NondetTest.assert (rBadRen = .error Errno.EINVAL ∧ sBr = s₃')
      let (rRen, s₄) := (ops.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
        none (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd'])
        { noreplace := true }).run s₃'
      NondetTest.assert (rRen = .ok ())
      let (rF2, s₅) := (ops.openat none (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y']) { access := .wronly, creat := true } 0o644).run s₄
      match rF2 with
      | .error _ => NondetTest.assert False
      | .ok fh2 =>
        let (_, s₆) := (ops.close fh2).run s₅
        let (rNoRep, sNr) := (ops.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd'])
          none (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y'])
          { noreplace := true }).run s₆
        NondetTest.assert (rNoRep = .error Errno.EEXIST ∧ sNr = s₆)
        let (rUn1, s₇) := (ops.unlinkat none (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd']) false).run s₆
        let (rUn2, s₈) := (ops.unlinkat none (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y']) false).run s₇
        let (rRmDir, _) := (ops.unlinkat none (asciiBytes ['s', 'u', 'b']) true).run s₈
        NondetTest.assert (rUn1 = .ok () ∧ rUn2 = .ok () ∧ rRmDir = .ok ())

/-- `symlinkat`, `readlinkat`, `fstatat`, and `openat(O_NOFOLLOW)` preserve exact link target bytes and symlink `StatInfo` (`size = target.size`, `nlink = 1`), reject `fstatat(AT_EACCESS)` and `readlinkat` on non-symlinks (`EINVAL`), and reject `O_NOFOLLOW` on symlinks (`ELOOP`). -/
def test_files_ops_symlinkReadlinkAndFstatat
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let tgt := asciiBytes ['d', 'e', 's', 't', '.', 't', 'x', 't']
  let (rEacc, sEa) := (ops.fstatat none (asciiBytes ['.']) { eaccess := true }).run s₀
  NondetTest.assert (rEacc = .error Errno.EINVAL ∧ sEa = s₀)
  let (rF, s₁) := (ops.openat none tgt { access := .rdwr, creat := true } 0o644).run s₀
  match rF with
  | .error _ => NondetTest.assert False
  | .ok fh =>
    let (_, s₂) := (ops.close fh).run s₁
    let (rRlNonSym, sRl) := (ops.readlinkat none tgt 64).run s₂
    NondetTest.assert (rRlNonSym = .error Errno.EINVAL ∧ sRl = s₂)
    let (rSym, s₃) := (ops.symlinkat tgt none (asciiBytes ['s', 'y', 'm'])).run s₂
    NondetTest.assert (rSym = .ok ())
    let (rRl, s₄) := (ops.readlinkat none (asciiBytes ['s', 'y', 'm']) 64).run s₃
    NondetTest.assert (rRl = .ok tgt ∧ s₄ = s₃)
    let (rRlTrunc, _) := (ops.readlinkat none (asciiBytes ['s', 'y', 'm']) 4).run s₄
    NondetTest.assert (rRlTrunc = .ok (sliceBytes tgt 0 4))
    let (rLstat, _) := (ops.fstatat none (asciiBytes ['s', 'y', 'm']) { symlinkNofollow := true }).run s₄
    NondetTest.assert (∃ st, rLstat = .ok st ∧ st.kind = .symlink ∧ st.size = tgt.size ∧ st.nlink = 1)
    let (rStat, _) := (ops.fstatat none (asciiBytes ['s', 'y', 'm']) { symlinkNofollow := false }).run s₄
    NondetTest.assert (∃ st, rStat = .ok st ∧ st.kind = .reg)
    let (rNoFol, sNf) := (ops.openat none (asciiBytes ['s', 'y', 'm']) { access := .rdonly, nofollow := true } 0).run s₄
    NondetTest.assert (rNoFol = .error Errno.ELOOP ∧ sNf = s₄)

/-- `fchmod`, `fchmodat`, `faccessat` (including `AT_EMPTY_PATH`), `flock`, `fcntl`, `fsync`, and `getcwd` maintain mode, advisory lock conflict (`EAGAIN`), descriptor/status flag, durability, and CWD invariants. -/
def test_files_ops_chmodAccessFlockFcntlFsyncGetcwd
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rCwdZero, _) := (ops.getcwd 0).run s₀
  NondetTest.assert (rCwdZero = .error Errno.EINVAL ∨ rCwdZero = .error Errno.ERANGE)
  let (rCwdOk, _) := (ops.getcwd 4096).run s₀
  NondetTest.assert (∃ p, rCwdOk = .ok p ∧ p.size > 0 ∧ p.get! 0 = 47 ∧ hasEmbeddedNul p = false)
  let name := asciiBytes ['l', 'o', 'c', 'k', 'a', 'b', 'l', 'e', '.', 'b', 'i', 'n']
  let (r1, s₁) := (ops.openat none name { access := .rdwr, creat := true } 0o644).run s₀
  match r1 with
  | .error _ => NondetTest.assert False
  | .ok h1 =>
    let (r2, s₂) := (ops.openat none name { access := .rdwr } 0).run s₁
    match r2 with
    | .error _ => NondetTest.assert False
    | .ok h2 =>
      let (rCh1, s₃) := (ops.fchmod h1 0o600).run s₂
      NondetTest.assert (rCh1 = .ok ())
      let (rSt1, _) := (ops.fstat h1).run s₃
      NondetTest.assert (∃ st, rSt1 = .ok st ∧ st.mode = 0o600)
      let (rAccEmpty, _) := (ops.faccessat (some h1) (ByteArray.mk #[]) { read := true } { emptyPath := true }).run s₃
      NondetTest.assert (rAccEmpty = .ok ())
      let (rAccNoExec, _) := (ops.faccessat none name { exec := true } {}).run s₃
      NondetTest.assert (rAccNoExec = .error Errno.EACCES)
      let (rCh2, s₄) := (ops.fchmodat none name 0o755).run s₃
      NondetTest.assert (rCh2 = .ok ())
      let (rAccExec, _) := (ops.faccessat none name { read := true, write := true, exec := true } {}).run s₄
      NondetTest.assert (rAccExec = .ok ())
      let (rLk1, s₅) := (ops.flock h1 (.exclusive true)).run s₄
      NondetTest.assert (rLk1 = .ok ())
      let (rLk2, s₆) := (ops.flock h2 (.shared true)).run s₅
      NondetTest.assert (rLk2 = .error Errno.EAGAIN ∧ s₆ = s₅)
      let (rUnlk, s₇) := (ops.flock h1 .unlock).run s₆
      NondetTest.assert (rUnlk = .ok ())
      let (rLk2Ok, s₈) := (ops.flock h2 (.shared true)).run s₇
      NondetTest.assert (rLk2Ok = .ok ())
      let (rSetFd, s₉) := (ops.fcntl h1 (.setFd false)).run s₈
      let (rGetFd, _) := (ops.fcntl h1 .getFd).run s₉
      NondetTest.assert (rSetFd = .ok 0 ∧ rGetFd = .ok 0)
      let (rSetFl, s₁₀) := (ops.fcntl h1 (.setFl true true)).run s₉
      let (rGetFl, _) := (ops.fcntl h1 .getFl).run s₁₀
      NondetTest.assert (rSetFl = .ok 0 ∧ ∃ fl, rGetFl = .ok fl ∧ (fl &&& ((1 : UInt32) <<< 8)) ≠ 0 ∧ (fl &&& ((1 : UInt32) <<< 5)) ≠ 0)
      let (rSync, s₁₁) := (ops.fsync h1).run s₁₀
      NondetTest.assert (rSync = .ok ())
      let (_, s₁₂) := (ops.close h1).run s₁₁
      let (rSyncClosed, _) := (ops.fsync h1).run s₁₂
      NondetTest.assert (rSyncClosed = .error Errno.EBADF)
      let (_, _) := (ops.close h2).run s₁₂
      pure ()

/-- Unlinking an open regular file preserves `read`/`write`/`fstat` (`nlink = 0`) until `close`, whereas unlinking an open directory sets `fstat` `nlink = 0` and rejects `getdents64`, `openat(O_CREAT)`, and `mkdirat` on the dead directory with `ENOENT`. -/
def test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let fname := asciiBytes ['u', 'n', 'l', 'i', 'n', 'k', '.', 'b', 'i', 'n']
  let data := asciiBytes ['k', 'e', 'e', 'p']
  let (rOpen, s₁) := (ops.openat none fname { access := .rdwr, creat := true, excl := true } 0o644).run s₀
  match rOpen with
  | .error _ => NondetTest.assert False
  | .ok fh =>
    let (rOpenRd, s₁') := (ops.openat none fname { access := .rdonly } 0).run s₁
    match rOpenRd with
    | .error _ => NondetTest.assert False
    | .ok rfh =>
      let (rWr, s₂) := (ops.write fh data).run s₁'
      NondetTest.assert (rWr = .ok 4)
      let (rUn, s₃) := (ops.unlinkat none fname false).run s₂
      NondetTest.assert (rUn = .ok ())
      let (rGone, _) := (ops.fstatat none fname {}).run s₃
      NondetTest.assert (rGone = .error Errno.ENOENT)
      let (rStOpen, _) := (ops.fstat fh).run s₃
      NondetTest.assert (∃ st, rStOpen = .ok st ∧ st.kind = .reg ∧ st.size = 4 ∧ st.nlink = 0)
      let (rRdOpen, s₄) := (ops.read rfh 4).run s₃
      NondetTest.assert (rRdOpen = .ok data)
      let (_, s₅) := (ops.close fh).run s₄
      let (_, s₆) := (ops.close rfh).run s₅
      let dname := asciiBytes ['d', 'e', 'a', 'd']
      let (rMk, s₇) := (ops.mkdirat none dname 0o755).run s₆
      NondetTest.assert (rMk = .ok ())
      let (rDo, s₈) := (ops.openat none dname { access := .rdonly, directory := true } 0).run s₇
      match rDo with
      | .error _ => NondetTest.assert False
      | .ok dfd =>
        let (rRmD, s₉) := (ops.unlinkat none dname true).run s₈
        NondetTest.assert (rRmD = .ok ())
        let (rDeadSt, _) := (ops.fstat dfd).run s₉
        NondetTest.assert (∃ dst, rDeadSt = .ok dst ∧ dst.kind = .dir ∧ dst.nlink = 0)
        let (rDeadGd, _) := (ops.getdents64 dfd 4096).run s₉
        NondetTest.assert (rDeadGd = .error Errno.ENOENT)
        let (rDeadCr, _) := (ops.openat (some dfd) (asciiBytes ['x']) { access := .wronly, creat := true } 0o644).run s₉
        NondetTest.assert (rDeadCr = .error Errno.ENOENT)
        let (rDeadMk, _) := (ops.mkdirat (some dfd) (asciiBytes ['y']) 0o755).run s₉
        NondetTest.assert (rDeadMk = .error Errno.ENOENT)
        let (_, _) := (ops.close dfd).run s₉
        pure ()

/-- `O_APPEND` writes at EOF across concurrent descriptors, `O_RDONLY | O_TRUNC` truncates writable (`0o644`) files while failing with `EACCES` on read-only (`0o444`) files, `O_CREAT | O_DIRECTORY` fails, `O_CREAT` on `"missing/"` returns `EISDIR`, and `O_CREAT` through a dangling symlink creates its target. -/
def test_files_ops_appendTruncAndCreatEdgeCases
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rCrDir, sCd) := (ops.openat none (asciiBytes ['c', 'd']) { access := .rdonly, creat := true, directory := true } 0o755).run s₀
  NondetTest.assert ((rCrDir = .error Errno.EINVAL ∨ rCrDir = .error Errno.ENOTDIR ∨ rCrDir = .error Errno.EISDIR) ∧ sCd = s₀)
  let (rTrailCr, sTc) := (ops.openat none (asciiBytes ['m', 'i', 's', 's', '/']) { access := .rdwr, creat := true } 0o644).run s₀
  NondetTest.assert (rTrailCr = .error Errno.EISDIR ∧ sTc = s₀)
  let (rDsym, s₁) := (ops.symlinkat (asciiBytes ['d', 't', 'g', 't']) none (asciiBytes ['d', 's', 'y', 'm'])).run s₀
  NondetTest.assert (rDsym = .ok ())
  let (rOpenDsym, s₂) := (ops.openat none (asciiBytes ['d', 's', 'y', 'm']) { access := .rdwr, creat := true } 0o644).run s₁
  match rOpenDsym with
  | .error _ => NondetTest.assert False
  | .ok dh =>
    let (_, s₃) := (ops.write dh (asciiBytes ['a', 'b'])).run s₂
    let (rApp, s₄) := (ops.openat none (asciiBytes ['d', 't', 'g', 't']) { access := .wronly, append := true } 0).run s₃
    match rApp with
    | .error _ => NondetTest.assert False
    | .ok ah =>
      let (_, s₅) := (ops.write ah (asciiBytes ['c', 'd'])).run s₄
      let (_, s₆) := (ops.close dh).run s₅
      let (_, s₇) := (ops.close ah).run s₆
      let (rStApp, _) := (ops.fstatat none (asciiBytes ['d', 't', 'g', 't']) {}).run s₇
      NondetTest.assert (∃ st, rStApp = .ok st ∧ st.size = 4)
      let (rRoTr, s₈) := (ops.openat none (asciiBytes ['d', 't', 'g', 't']) { access := .rdonly, trunc := true } 0).run s₇
      match rRoTr with
      | .error _ => NondetTest.assert False
      | .ok rth =>
        let (_, s₉) := (ops.close rth).run s₈
        let (rStTr, _) := (ops.fstatat none (asciiBytes ['d', 't', 'g', 't']) {}).run s₉
        NondetTest.assert (∃ st, rStTr = .ok st ∧ st.size = 0)
        let (_, s₁₀) := (ops.fchmodat none (asciiBytes ['d', 't', 'g', 't']) 0o444).run s₉
        let (rRoTrFail, s₁₁) := (ops.openat none (asciiBytes ['d', 't', 'g', 't']) { access := .rdonly, trunc := true } 0).run s₁₀
        NondetTest.assert (rRoTrFail = .error Errno.EACCES ∧ s₁₁ = s₁₀)

/-- Cyclic symlinks fail with `ELOOP` on symlink-following lookups while succeeding as `.symlink` under `AT_SYMLINK_NOFOLLOW`, and paths exceeding `NAME_MAX` (`255`) or reaching `PATH_MAX` (`4096`) fail with `ENAMETOOLONG`. -/
def test_files_ops_symlinkLoopAndNameTooLong
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let longSeg ← nondet ByteArray
  assume (hasEmbeddedNul longSeg = false ∧ longSeg.data.size < PATH_MAX ∧
    longSeg.data.size > NAME_MAX ∧ (splitPathBytes longSeg).2.1 = [longSeg])
  let maxPath ← nondet ByteArray
  assume (hasEmbeddedNul maxPath = false ∧ maxPath.data.size ≥ PATH_MAX)
  let (rSegLong, sSl) := (ops.openat none longSeg { access := .rdonly } 0).run s₀
  NondetTest.assert (rSegLong = .error Errno.ENAMETOOLONG ∧ sSl = s₀)
  let (rPathLong, sPl) := (ops.fstatat none maxPath {}).run s₀
  NondetTest.assert (rPathLong = .error Errno.ENAMETOOLONG ∧ sPl = s₀)
  let (rSymLong, sSml) := (ops.symlinkat maxPath none (asciiBytes ['s'])).run s₀
  NondetTest.assert (rSymLong = .error Errno.ENAMETOOLONG ∧ sSml = s₀)
  let (rS1, s₁) := (ops.symlinkat (asciiBytes ['l', '2']) none (asciiBytes ['l', '1'])).run s₀
  let (rS2, s₂) := (ops.symlinkat (asciiBytes ['l', '1']) none (asciiBytes ['l', '2'])).run s₁
  NondetTest.assert (rS1 = .ok () ∧ rS2 = .ok ())
  let (rLoopOpen, sLo) := (ops.openat none (asciiBytes ['l', '1']) { access := .rdonly } 0).run s₂
  NondetTest.assert (rLoopOpen = .error Errno.ELOOP ∧ sLo = s₂)
  let (rLoopStat, _) := (ops.fstatat none (asciiBytes ['l', '1']) { symlinkNofollow := false }).run s₂
  NondetTest.assert (rLoopStat = .error Errno.ELOOP)
  let (rLoopLstat, _) := (ops.fstatat none (asciiBytes ['l', '1']) { symlinkNofollow := true }).run s₂
  NondetTest.assert (∃ st, rLoopLstat = .ok st ∧ st.kind = .symlink)

/-- `Model.allowedStep` permits valid partial `read` prefixes, rejects corrupted bytes or spurious zero-length reads, enforces `getcwd` `cwdBound` persistence and `ERANGE`, rejects blocking conflicting `flock` `.unit`, and accepts `/dev/shm` `F_GET_SEALS = 1` on regular files. -/
def test_files_model_allowedStep_partialReadAndInvariants
    {runner} [NondetTest runner]
    (step : FilesState → FilesReq → FilesOutcome → Option FilesState := allowedStep) : runner Unit := do
  let s0 := FilesState.initial
  NondetTest.assert ((step s0 (.openat none (ByteArray.mk #[97, 0, 98]) {} 0o644) (.opened 0)).isNone)
  NondetTest.assert ((step s0 (.openat none (ByteArray.mk #[97, 0, 98]) {} 0o644) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.close 0) .unit).isNone)
  NondetTest.assert ((step s0 (.close 0) (.err Errno.EBADF)).isSome)
  NondetTest.assert ((step s0 (.getcwd 4) (.err Errno.ERANGE)).isSome)
  match step s0 (.getcwd 64) (.bytes (asciiBytes ['/', 't', 'm', 'p'])) with
  | none => NondetTest.assert False
  | some sCwd =>
    NondetTest.assert ((step sCwd (.getcwd 4) (.err Errno.ERANGE)).isSome)
    NondetTest.assert ((step sCwd (.getcwd 64) (.bytes (asciiBytes ['/', 'b', 'a', 'd']))).isNone)
    NondetTest.assert ((step sCwd (.getcwd 64) (.bytes (asciiBytes ['/', 't', 'm', 'p']))).isSome)
  match step s0 (.openat none (asciiBytes ['f']) { access := .rdwr, creat := true } 0o644) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.fcntl 0 .getSeals) (.u32 1)).isSome)
    match step s1 (.write 0 (asciiBytes ['a', 'b', 'c', 'd'])) (.u32 4) with
    | none => NondetTest.assert False
    | some s2 =>
      match step s2 (.openat none (asciiBytes ['f']) { access := .rdonly } 0) (.opened 1) with
      | none => NondetTest.assert False
      | some s3 =>
        NondetTest.assert ((step s3 (.read 1 4) (.bytes (asciiBytes ['a', 'b']))).isSome)
        NondetTest.assert ((step s3 (.read 1 4) (.bytes (asciiBytes ['a', 'c']))).isNone)
        NondetTest.assert ((step s3 (.read 1 4) (.bytes (ByteArray.mk #[]))).isNone)
        NondetTest.assert ((step s3 (.read 1 4) (.err Errno.EIO)).isSome)
        match step s3 (.flock 0 (.exclusive false)) .unit with
        | none => NondetTest.assert False
        | some s4 =>
          NondetTest.assert ((step s4 (.flock 1 (.shared false)) .unit).isNone)
          NondetTest.assert ((step s4 (.flock 1 (.shared false)) (.err Errno.EINTR)).isSome)
    let stMaxNsec : StatInfo :=
      { kind := .reg, size := 0, mode := 0o644, ino := 1, dev := 1, nlink := 1,
        mtimeSec := 1700000000, mtimeNsec := 999999999, atimeSec := 1700000000, atimeNsec := 999999999 }
    NondetTest.assert ((step s1 (.fstat 0) (.statted stMaxNsec)).isSome)
    NondetTest.assert ((step s1 (.fstat 0) (.statted { stMaxNsec with mtimeNsec := 1000000000 })).isNone)
    NondetTest.assert ((step s1 (.fstat 0) (.statted { stMaxNsec with atimeNsec := 1000000000 })).isNone)
  let sProc := FilesState.withSeededTree {}
  match step sProc (.dupStdio .stdout) (.opened 0) with
  | none => NondetTest.assert False
  | some sDup =>
    let stBadExt : StatInfo :=
      { kind := .reg, size := 0, mode := 0o644, ino := 99, dev := 9, nlink := 1,
        mtimeSec := 0, mtimeNsec := 1000000000, atimeSec := 0, atimeNsec := 0 }
    NondetTest.assert ((step sDup (.fstat 0) (.statted stBadExt)).isNone)
    match step sDup (.reopenReadOnly 0) (.opened 1) with
    | none => NondetTest.assert False
    | some sRe =>
      NondetTest.assert ((step sRe (.fcntl 1 .getFd) (.u32 1)).isSome)
      NondetTest.assert ((step sRe (.fcntl 1 .getFd) (.u32 0)).isNone)

/-- External trust-boundary assumptions for `LeanSwe.LinuxSyscall.Files` C wrappers (`files_shim.c` + `fd_box.h`) and Linux kernel ABI (`x86_64` + `aarch64`), verified 1-to-1 by `RuntimeTests.lean`, `leanswe-world-fuzz`, and `strace` fault injection. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.LinuxSyscall.Files.assume_files_openat_flagsAndNulGuard"
      subject := "LeanSwe.LinuxSyscall.Files.openat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_openat2_resolveFlagsAndAbi"
      subject := "LeanSwe.LinuxSyscall.Files.openat2"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_close_abaSafeFdBox"
      subject := "LeanSwe.LinuxSyscall.Files.close"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_read_clamped16MiBAndPartial"
      subject := "LeanSwe.LinuxSyscall.Files.read"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_write_partialAndAppend"
      subject := "LeanSwe.LinuxSyscall.Files.write"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fstat_portableStatDecode"
      subject := "LeanSwe.LinuxSyscall.Files.fstat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fstatat_nofollowAndEmptyPath"
      subject := "LeanSwe.LinuxSyscall.Files.fstatat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_faccessat_modeBits"
      subject := "LeanSwe.LinuxSyscall.Files.faccessat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_mkdirat_modeAndNulGuard"
      subject := "LeanSwe.LinuxSyscall.Files.mkdirat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_unlinkat_removeDirFlag"
      subject := "LeanSwe.LinuxSyscall.Files.unlinkat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_renameat2_flagsAbi"
      subject := "LeanSwe.LinuxSyscall.Files.renameat2"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_symlinkat_rawBytesAndNulGuard"
      subject := "LeanSwe.LinuxSyscall.Files.symlinkat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_readlinkat_clampedRawBytes"
      subject := "LeanSwe.LinuxSyscall.Files.readlinkat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_getdents64_rawDirentBuffer"
      subject := "LeanSwe.LinuxSyscall.Files.getdents64"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fchmodat_modeAndNulGuard"
      subject := "LeanSwe.LinuxSyscall.Files.fchmodat"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fchmod_modeUpdate"
      subject := "LeanSwe.LinuxSyscall.Files.fchmod"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_flock_advisoryLockFlags"
      subject := "LeanSwe.LinuxSyscall.Files.flock"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fcntl_curatedCommands"
      subject := "LeanSwe.LinuxSyscall.Files.fcntl"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_fsync_fdSync"
      subject := "LeanSwe.LinuxSyscall.Files.fsync"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_getcwd_clampedBuffer"
      subject := "LeanSwe.LinuxSyscall.Files.getcwd"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_lseek_offsetAndDirRewind"
      subject := "LeanSwe.LinuxSyscall.Files.lseek"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_reopenReadOnly_procSelfFd"
      subject := "LeanSwe.LinuxSyscall.Files.reopenReadOnly"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Files.assume_files_dupStdio_cloexecSlot"
      subject := "LeanSwe.LinuxSyscall.Files.dupStdio"
      formalPred? := none } ]

/-- Complete `(request × FilesErrorKind)` error-coverage matrix for all 23 curated `Files` syscalls (`138` obligations), linked to real Linux tests and `strace`/mocked fault-injection tests in `RuntimeTests.lean`. -/
def errorCoverage : List (ErrorObligation FilesErrorKind) :=
  [ { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.openat2", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_openat2_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.close", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_close_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.read", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_read_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.write", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_write_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fstat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstat_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fstatat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fstatat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.faccessat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_faccessat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.mkdirat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_mkdirat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.unlinkat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_unlinkat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.renameat2", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_renameat2_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.symlinkat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_symlinkat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.readlinkat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_readlinkat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.getdents64", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getdents64_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_notFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmodat", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmodat_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fchmod", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fchmod_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.flock", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_flock_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fcntl", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fcntl_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.fsync", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_fsync_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.getcwd", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_getcwd_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.lseek", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_lseek_transient" .real }

  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_stateConflict" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Files.reopenReadOnly", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_reopenReadOnly_transient" .real }

  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .notFound, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .stateConflict, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Files.dupStdio", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Files.RuntimeTests.err_dupStdio_mocked" .mocked } ]

/-- Verify hardened `allowedStep` invariants covering bound-CWD `getcwd`, `openat` `.` `O_CREAT|O_EXCL`, symlink `O_NOFOLLOW|O_DIRECTORY`, `fstatat` `AT_EMPTY_PATH|AT_EACCESS`, strict `getdents64` framing/EOF, `unlinkat`/`renameat2` `.`/`..`, `symlinkat` trailing slash, `flock` `LOCK_NB` upgrade drop, `F_ADD_SEALS`, and `fsync` error set. -/
def test_files_model_hardenedInvariants {runner} [NondetTest runner]
    (step : FilesState → FilesReq → FilesOutcome → Option FilesState) : runner Unit := do
  let s0 := FilesState.initial (asciiBytes ['/', 'e', 'p'])
  NondetTest.assert ((step s0 (.getcwd 64) (.bytes (asciiBytes ['/', 'e', 'p']))).isSome)
  NondetTest.assert ((step s0 (.getcwd 64) (.bytes (asciiBytes ['/', 'b', 'a', 'd']))).isNone)
  NondetTest.assert ((step s0 (.openat none (asciiBytes ['.', '/']) { access := .rdwr, creat := true, excl := true } 0o644) (.err Errno.EEXIST)).isSome)
  NondetTest.assert ((step s0 (.openat none (asciiBytes ['.', '/']) { access := .rdwr, creat := true, excl := true } 0o644) (.err Errno.EISDIR)).isNone)
  NondetTest.assert ((step s0 (.unlinkat none (asciiBytes ['.']) false) (.err Errno.EISDIR)).isSome)
  NondetTest.assert ((step s0 (.unlinkat none (asciiBytes ['.']) true) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.renameat2 none (asciiBytes ['.']) none (asciiBytes ['x']) {}) (.err Errno.EBUSY)).isSome)
  NondetTest.assert ((step s0 (.renameat2 none (asciiBytes ['.']) none (asciiBytes ['x']) {}) (.err Errno.EINVAL)).isNone)
  NondetTest.assert ((step s0 (.symlinkat (asciiBytes ['t']) none (asciiBytes ['m', 'i', 's', 's', '/'])) (.err Errno.ENOENT)).isSome)
  NondetTest.assert ((step s0 (.symlinkat (asciiBytes ['t']) none (asciiBytes ['m', 'i', 's', 's', '/'])) (.err Errno.EEXIST)).isNone)
  NondetTest.assert ((step s0 (.fstatat none (ByteArray.mk #[]) { emptyPath := true, eaccess := true }) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.fstatat none (ByteArray.mk #[]) { emptyPath := true, eaccess := true }) (.err Errno.EBADF)).isNone)
  match step s0 (.mkdirat none (asciiBytes ['s', 'u', 'b']) 0o755) .unit with
  | none => NondetTest.assert False
  | some sSub =>
    NondetTest.assert ((step sSub (.openat none (asciiBytes ['s', 'u', 'b', '/']) { access := .rdwr, creat := true, excl := true } 0o644) (.err Errno.EISDIR)).isSome)
    NondetTest.assert ((step sSub (.openat none (asciiBytes ['s', 'u', 'b', '/']) { access := .rdwr, creat := true, excl := true } 0o644) (.err Errno.EEXIST)).isNone)
    match step sSub (.openat none (asciiBytes ['s', 'u', 'b']) { access := .rdonly, directory := true } 0) (.opened 0) with
    | none => NondetTest.assert False
    | some sDir =>
      let rec24 := ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 24, 0, 4, 46, 0, 0, 0, 0]
      NondetTest.assert ((step sDir (.getdents64 0 16) (.bytes (ByteArray.mk #[]))).isNone)
      NondetTest.assert ((step sDir (.getdents64 0 16) (.err Errno.EINVAL)).isSome)
      NondetTest.assert ((step sDir (.getdents64 0 24) (.bytes (ByteArray.mk #[1, 2]))).isNone)
      match step sDir (.getdents64 0 24) (.bytes rec24) with
      | none => NondetTest.assert False
      | some sD1 =>
        match step sD1 (.getdents64 0 24) (.bytes rec24) with
        | none => NondetTest.assert False
        | some sD2 =>
          match step sD2 (.getdents64 0 24) (.bytes (ByteArray.mk #[])) with
          | none => NondetTest.assert False
          | some sEof =>
            NondetTest.assert ((step sEof (.getdents64 0 4096) (.bytes rec24)).isNone)
            NondetTest.assert ((step sEof (.getdents64 0 4096) (.bytes (ByteArray.mk #[]))).isSome)
  match step s0 (.symlinkat (asciiBytes ['t']) none (asciiBytes ['l', 'n', 'k'])) .unit with
  | none => NondetTest.assert False
  | some sSym =>
    NondetTest.assert ((step sSym (.openat none (asciiBytes ['l', 'n', 'k']) { access := .rdonly, nofollow := true } 0) (.err Errno.ELOOP)).isSome)
    NondetTest.assert ((step sSym (.openat none (asciiBytes ['l', 'n', 'k']) { access := .rdonly, nofollow := true, directory := true } 0) (.err Errno.ENOTDIR)).isSome)
    NondetTest.assert ((step sSym (.openat none (asciiBytes ['l', 'n', 'k']) { access := .rdonly, nofollow := true, directory := true } 0) (.err Errno.ELOOP)).isNone)
  match step s0 (.openat none (asciiBytes ['f']) { access := .rdwr, creat := true } 0o644) (.opened 0) with
  | none => NondetTest.assert False
  | some sF1 =>
    NondetTest.assert ((step sF1 (.fcntl 0 (.addSeals 0x10000000)) (.err Errno.EINVAL)).isSome)
    NondetTest.assert ((step sF1 (.fcntl 0 (.addSeals 0x10000000)) (.u32 0)).isNone)
    NondetTest.assert ((step sF1 (.fsync 0) (.err Errno.EINVAL)).isNone)
    match step sF1 (.openat none (asciiBytes ['f']) { access := .rdonly } 0) (.opened 1) with
    | none => NondetTest.assert False
    | some sF2 =>
      NondetTest.assert ((step sF2 (.fcntl 1 (.addSeals 0x10000000)) (.err Errno.EPERM)).isSome)
      NondetTest.assert ((step sF2 (.fcntl 1 (.addSeals 0x10000000)) (.err Errno.EINVAL)).isNone)
      match step sF2 (.flock 0 (.shared true)) .unit with
      | none => NondetTest.assert False
      | some sL0 =>
        match step sL0 (.flock 1 (.shared true)) .unit with
        | none => NondetTest.assert False
        | some sL1 =>
          match step sL1 (.flock 1 (.exclusive true)) (.err Errno.EAGAIN) with
          | none => NondetTest.assert False
          | some sDrop =>
            NondetTest.assert ((step sDrop (.flock 0 (.exclusive true)) .unit).isSome)
      match step sF2 (.close 1) .unit with
      | none => NondetTest.assert False
      | some sClosed =>
        NondetTest.assert ((step sClosed (.fstatat (some 1) (ByteArray.mk #[]) { emptyPath := true, eaccess := true }) (.err Errno.EINVAL)).isSome)
        NondetTest.assert ((step sClosed (.fstatat (some 1) (ByteArray.mk #[]) { emptyPath := true, eaccess := false }) (.err Errno.EBADF)).isSome)

/-- Environment-generalization invariants: `umask` and `S_ISGID` inheritance, `getdents64` `dirCursor = 0`, `(st_dev, st_ino)` distinctness, `noXdev` and `noMagiclinks`, cross-mount `renameat2`, `/dev/full`, `.fifo` (`ENXIO`/`EAGAIN`/non-`stripPrivBits`), `.socket` (`ENXIO`), `ETXTBSY`, `EFBIG`, and unlinked `getcwd` (`ENOENT`). -/
def test_files_model_envGeneralizationInvariants {runner : Type → Type} [Core.NondetTest runner]
    (step : FilesState → FilesReq → FilesOutcome → Option FilesState) : runner Unit := do
  let sUmask := FilesState.withSeededTree
    { cwdPath := asciiBytes ['/', 'w'], umask := 0o200, cwdMode := 0o2755, includeHostTree := false }
  let sU1 ← match step sUmask (.openat none (asciiBytes ['u']) { access := .rdwr, creat := true } 0o644) (.opened 0) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sUmask
  let mkSt (k : FileKind) (sz : Nat) (m : Mode) (ino dev : UInt64) (nl : Nat) : StatInfo :=
    { kind := k, size := sz, mode := m, ino := ino, dev := dev, nlink := nl,
      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }
  Core.NondetTest.assert ((step sU1 (.fstat 0) (.statted (mkSt .reg 0 0o444 10 1 1))).isSome)
  Core.NondetTest.assert ((step sU1 (.fstat 0) (.statted (mkSt .reg 0 0o644 10 1 1))).isNone)
  let sU2 ← match step sUmask (.mkdirat none (asciiBytes ['d']) 0o755) .unit with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sUmask
  Core.NondetTest.assert ((step sU2 (.fstatat none (asciiBytes ['d']) {}) (.statted (mkSt .dir 0 0o2555 11 1 2))).isSome)
  Core.NondetTest.assert ((step sU2 (.fstatat none (asciiBytes ['d']) {}) (.statted (mkSt .dir 0 0o0555 11 1 2))).isNone)
  let longName := ByteArray.mk (Array.replicate 255 (115 : UInt8))
  let sDir := FilesState.withSeededTree
    { cwdPath := asciiBytes ['/'], includeHostTree := false
      cwdEntries := [{ name := longName, kind := .reg, mode := 0o644 }] }
  let sD1 ← match step sDir (.openat none (asciiBytes ['.']) { access := .rdonly, directory := true } 0) (.opened 0) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sDir
  Core.NondetTest.assert ((step sD1 (.getdents64 0 24) (.err Errno.EINVAL)).isSome)
  let sDev := FilesState.withSeededTree
    { cwdPath := asciiBytes ['/', 'a'], crossMountPath? := some (asciiBytes ['/', 'b']),
      cwdEntries := [{ name := asciiBytes ['f'], kind := .reg, mode := 0o644,
                       kernelIno? := some 1, kernelDev? := some 28 }] }
  Core.NondetTest.assert ((step sDev (.fstatat none (asciiBytes ['/', 'b']) {}) (.statted (mkSt .dir 0 0o755 1 43 2))).isSome)
  Core.NondetTest.assert ((step sDev (.fstatat none (asciiBytes ['/', 'b']) {}) (.statted (mkSt .dir 0 0o755 1 28 2))).isNone)
  let sHost := FilesState.withSeededTree
    { cwdPath := asciiBytes ['/', 's'], crossMountPath? := some (asciiBytes ['/', 'x']),
      cwdEntries :=
        [ { name := asciiBytes ['f'], kind := .reg, mode := 0o644 },
          { name := asciiBytes ['l'], kind := .symlink, mode := 0o777,
            symlinkTarget := asciiBytes ['/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 's', 't', 'a', 't', 'u', 's'] },
          { name := asciiBytes ['f', 'i', 'f'], kind := .fifo, mode := 0o6755, modeExact := true },
          { name := asciiBytes ['s', 'o', 'k'], kind := .socket, mode := 0o755 } ] }
  Core.NondetTest.assert ((step sHost (.openat2 none (asciiBytes ['l']) { flags := { access := .rdonly }, resolve := { noXdev := true } }) (.err Errno.EXDEV)).isSome)
  Core.NondetTest.assert ((step sHost (.openat2 none (asciiBytes ['/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 'e', 'x', 'e'])
    { flags := { access := .rdonly }, resolve := { noMagiclinks := true } }) (.err Errno.ELOOP)).isSome)
  Core.NondetTest.assert ((step sHost (.openat none (asciiBytes ['/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 'e', 'x', 'e'])
    { access := .wronly } 0) (.err Errno.ETXTBSY)).isSome)
  Core.NondetTest.assert ((step sHost (.renameat2 none (asciiBytes ['f']) none (asciiBytes ['/', 'x', '/', 'g']) {}) (.err Errno.EXDEV)).isSome)
  let sFull ← match step sHost (.openat none (asciiBytes ['/', 'd', 'e', 'v', '/', 'f', 'u', 'l', 'l'])
      { access := .rdwr } 0) (.opened 0) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sHost
  Core.NondetTest.assert ((step sFull (.write 0 (ByteArray.mk #[])) (.err Errno.ENOSPC)).isSome)
  Core.NondetTest.assert ((step sFull (.write 0 (ByteArray.mk #[])) (.u32 0)).isNone)
  Core.NondetTest.assert ((step sHost (.openat none (asciiBytes ['f', 'i', 'f']) { access := .wronly, nonblock := true } 0) (.err Errno.ENXIO)).isSome)
  let sFif1 ← match step sHost (.openat none (asciiBytes ['f', 'i', 'f'])
      { access := .rdwr, nonblock := true, trunc := true } 0) (.opened 0) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sHost
  Core.NondetTest.assert ((step sFif1 (.read 0 16) (.err Errno.EAGAIN)).isSome)
  let sFif2 ← match step sFif1 (.write 0 (asciiBytes ['a', 'b'])) (.u32 2) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sFif1
  Core.NondetTest.assert ((step sFif2 (.fstat 0) (.statted (mkSt .fifo 0 0o6755 99 1 1))).isSome)
  Core.NondetTest.assert ((step sFif2 (.fstat 0) (.statted (mkSt .fifo 0 0o0755 99 1 1))).isNone)
  Core.NondetTest.assert ((step sHost (.openat none (asciiBytes ['s', 'o', 'k']) { access := .rdonly, nonblock := true } 0) (.err Errno.ENXIO)).isSome)
  Core.NondetTest.assert ((step sHost (.openat none (asciiBytes ['s', 'o', 'k']) { access := .rdonly, nonblock := true } 0) (.opened 0)).isNone)
  let sF1 ← match step sHost (.openat none (asciiBytes ['f']) { access := .rdwr } 0) (.opened 0) with
    | some s' => pure s'
    | none => Core.NondetTest.assert False; pure sHost
  Core.NondetTest.assert ((step sF1 (.write 0 (asciiBytes ['x'])) (.err Errno.EFBIG)).isSome)
  let sDeadCwd := { sUmask with
    inodes := assocSet sUmask.inodes sUmask.cwdIno
      { data := .dir { parentIno := 0, lifecycle := .unlinked }, mode := 0o755, nlink := 0 } }
  Core.NondetTest.assert ((step sDeadCwd (.getcwd 256) (.err Errno.ENOENT)).isSome)
  Core.NondetTest.assert ((step sDeadCwd (.getcwd 256) (.bytes (asciiBytes ['/', 'w']))).isNone)

/-- `FilesOpsM` satisfies `O_PATH` (`openat`/`openat2` and `EBADF` operational guards), `lseek` (`SEEK_SET`/`SEEK_CUR`/`SEEK_END`, negative-offset `EINVAL`, and `0o400` directory rewind), `reopenReadOnly` (unlinked file offset `0` reopen and symlink `ELOOP`), and `dupStdio` slot duplication. -/
def test_files_ops_lseekReopenDupStdioAndOpath
    {S fd : Type} {runner} [NondetTest runner]
    (ops : FilesOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let regNm := asciiBytes ['r', 'e', 'g']
  let roNm := asciiBytes ['z', 'e', 'r', 'o']
  let dirNm := asciiBytes ['d', '4', '0', '0']
  let symNm := asciiBytes ['s', 'y', 'm']
  let payload := asciiBytes ['a', 'b', 'c', 'd', 'e']
  let (rMk0, s1) := (ops.openat none roNm { access := .rdwr, creat := true, excl := true } 0o000).run s₀
  NondetTest.assert (∃ h0, rMk0 = .ok h0)
  match rMk0 with
  | .error _ => NondetTest.assert False
  | .ok hMk0 =>
    let (rCh0, s2) := (ops.fchmod hMk0 0o000).run s1
    NondetTest.assert (rCh0 = .ok ())
    let (rCl0, s3) := (ops.close hMk0).run s2
    NondetTest.assert (rCl0 = .ok ())
    let (rOp2Bad, _) := (ops.openat2 none roNm { flags := { path := true, noctty := true } }).run s3
    NondetTest.assert (rOp2Bad = .error Errno.EINVAL)
    let (rPath0, s4) := (ops.openat none roNm { path := true, trunc := true, access := .wronly } 0).run s3
    NondetTest.assert (∃ hp, rPath0 = .ok hp)
    match rPath0 with
    | .error _ => NondetTest.assert False
    | .ok hPath =>
      NondetTest.assert (((ops.read hPath 4).run s4).1 = .error Errno.EBADF)
      NondetTest.assert (((ops.lseek hPath 0 .seekSet).run s4).1 = .error Errno.EBADF)
      NondetTest.assert (((ops.fchmod hPath 0o644).run s4).1 = .error Errno.EBADF)
      NondetTest.assert (((ops.flock hPath (.shared true)).run s4).1 = .error Errno.EBADF)
      NondetTest.assert (((ops.fsync hPath).run s4).1 = .error Errno.EBADF)
      NondetTest.assert (((ops.fcntl hPath .getFl).run s4).1 = .ok 0)
      NondetTest.assert (((ops.reopenReadOnly hPath).run s4).1 = .error Errno.EACCES)
      let (rStatP, _) := (ops.fstat hPath).run s4
      NondetTest.assert (∃ st, rStatP = .ok st ∧ st.kind = .reg)
      let (_, _) := (ops.close hPath).run s4
  let (rReg, s7) := (ops.openat none regNm { access := .rdwr, creat := true, excl := true } 0o644).run s₀
  match rReg with
  | .error _ => NondetTest.assert False
  | .ok hReg =>
    let (rWr, s8) := (ops.write hReg payload).run s7
    NondetTest.assert (rWr = .ok 5)
    let (rNeg, s9) := (ops.lseek hReg (-1) .seekSet).run s8
    NondetTest.assert (rNeg = .error Errno.EINVAL)
    let (rSet2, s10) := (ops.lseek hReg 2 .seekSet).run s9
    NondetTest.assert (rSet2 = .ok 2)
    let (rRdTail, s11) := (ops.read hReg 4).run s10
    NondetTest.assert (rRdTail = .ok (asciiBytes ['c', 'd', 'e']))
    let (rEnd, s12) := (ops.lseek hReg (-1) .seekEnd).run s11
    NondetTest.assert (rEnd = .ok 4)
    let (rCur, s13) := (ops.lseek hReg (-2) .seekCur).run s12
    NondetTest.assert (rCur = .ok 2)
    let (_, _) := (ops.close hReg).run s13
  let (rReg2, s14a) := (ops.openat none (asciiBytes ['r', 'e', 'g', '2']) { access := .rdwr, creat := true, excl := true } 0o644).run s₀
  match rReg2 with
  | .error _ => NondetTest.assert False
  | .ok hReg2 =>
    let (rWr2, s14b) := (ops.write hReg2 payload).run s14a
    NondetTest.assert (rWr2 = .ok 5)
    let (rUnl, s14c) := (ops.unlinkat none (asciiBytes ['r', 'e', 'g', '2']) false).run s14b
    NondetTest.assert (rUnl = .ok ())
    let (rRe, s15) := (ops.reopenReadOnly hReg2).run s14c
    match rRe with
    | .error _ => NondetTest.assert False
    | .ok hRe =>
      let (rRdAll, s16) := (ops.read hRe 8).run s15
      NondetTest.assert (rRdAll = .ok payload)
      let (_, s17) := (ops.close hRe).run s16
      let (_, _) := (ops.close hReg2).run s17
  let (rMkD, s19) := (ops.mkdirat none dirNm 0o400).run s₀
  NondetTest.assert (rMkD = .ok ())
  let (rDir, s20) := (ops.openat none dirNm { access := .rdonly, directory := true } 0).run s19
  match rDir with
  | .error _ => NondetTest.assert False
  | .ok hDir =>
    let (rGd1, s21) := (ops.getdents64 hDir 4096).run s20
    NondetTest.assert (∃ bs, rGd1 = .ok bs ∧ bs.data.size ≥ 24)
    let (rGdEof, s22) := (ops.getdents64 hDir 4096).run s21
    NondetTest.assert (rGdEof = .ok (ByteArray.mk #[]))
    let (rSeek0, s23) := (ops.lseek hDir 0 .seekSet).run s22
    NondetTest.assert (rSeek0 = .ok 0)
    let (rGd2, s24) := (ops.getdents64 hDir 4096).run s23
    NondetTest.assert (∃ bs, rGd2 = .ok bs ∧ bs.data.size ≥ 24)
    let (_, _) := (ops.close hDir).run s24
  let (rSym, s26) := (ops.symlinkat roNm none symNm).run s₀
  NondetTest.assert (rSym = .ok ())
  let (rSymPath, s27) := (ops.openat none symNm { path := true, nofollow := true } 0).run s26
  match rSymPath with
  | .error _ => NondetTest.assert False
  | .ok hSym =>
    let (rReSym, s28) := (ops.reopenReadOnly hSym).run s27
    NondetTest.assert (rReSym = .error Errno.ELOOP)
    let (_, _) := (ops.close hSym).run s28
  let (rStd, s30) := (ops.dupStdio .stdin).run s₀
  match rStd with
  | .error _ => NondetTest.assert False
  | .ok hStd =>
    let (rCloseStd, _) := (ops.close hStd).run s30
    NondetTest.assert (rCloseStd = .ok ())

/-- Encode an optional raw directory handle into a `UInt64` word (`0` for `none`, `d + 1` for `some d`). -/
def recDirWord : Option Nat → UInt64
  | none => 0
  | some d => (d + 1).toUInt64

/-- Encode length and leading 4 bytes of `b` into a `UInt64` word for lossless small-argument recording. -/
def recBytesWord (b : ByteArray) : UInt64 :=
  b.size.toUInt64 |||
    ((byteGetD b 0).toUInt64 <<< 16) |||
    ((byteGetD b 1).toUInt64 <<< 24) |||
    ((byteGetD b 2).toUInt64 <<< 32) |||
    ((byteGetD b 3).toUInt64 <<< 40)

/-- Recording `PosixFilesOpsM` hooks used by `test_files_impl_mkFilesOpsM`. -/
def mkRecRawOps : Internal.PosixFilesOpsM (StateM (List (Nat × UInt64 × UInt64))) Nat :=
  { openat := fun dir path f m => do
      modify fun st => (1, recDirWord dir ||| (recBytesWord path <<< 16), f.toUInt64 ||| (m.toUInt64 <<< 32)) :: st
      pure (.ok 101)
    openat2 := fun dir path f m r => do
      modify fun st => (2, f.toUInt64 ||| (m.toUInt64 <<< 32), r) :: (201, recDirWord dir, recBytesWord path) :: st
      pure (.ok 102)
    close := fun fd => do
      modify fun st => (3, fd.toUInt64, 0) :: st
      pure (.ok ())
    read := fun fd cap => do
      modify fun st => (4, fd.toUInt64, cap.toUInt64) :: st
      pure (.ok (ByteArray.mk #[7]))
    write := fun fd data => do
      modify fun st => (5, fd.toUInt64, recBytesWord data) :: st
      pure (.ok 105)
    fstat := fun fd => do
      modify fun st => (6, fd.toUInt64, 0) :: st
      pure (.ok (1, 9, 0o100755, 2, 3, 4, 5, 6, 7, 8))
    fstatat := fun dir path f => do
      modify fun st => (7, recDirWord dir ||| (recBytesWord path <<< 16), f.toUInt64) :: st
      pure (.ok (2, 11, 0o120777, 12, 13, 14, 15, 16, 17, 18))
    faccessat := fun dir path m f => do
      modify fun st => (8, recDirWord dir ||| (recBytesWord path <<< 16), m.toUInt64 ||| (f.toUInt64 <<< 32)) :: st
      pure (.ok ())
    mkdirat := fun dir path m => do
      modify fun st => (9, recDirWord dir ||| (recBytesWord path <<< 16), m.toUInt64) :: st
      pure (.ok ())
    unlinkat := fun dir path rm => do
      modify fun st => (10, recDirWord dir ||| (recBytesWord path <<< 16), rm.toUInt64) :: st
      pure (.ok ())
    renameat2 := fun od op nd np f => do
      modify fun st => (11, recBytesWord op, recBytesWord np) ::
        (1101, recDirWord od ||| (recDirWord nd <<< 32), f.toUInt64) :: st
      pure (.ok ())
    symlinkat := fun target dir linkPath => do
      modify fun st => (12, recDirWord dir ||| (recBytesWord target <<< 16), recBytesWord linkPath) :: st
      pure (.ok ())
    readlinkat := fun dir path cap => do
      modify fun st => (13, recDirWord dir ||| (recBytesWord path <<< 16), cap.toUInt64) :: st
      pure (.ok (ByteArray.mk #[8]))
    getdents64 := fun fd cap => do
      modify fun st => (14, fd.toUInt64, cap.toUInt64) :: st
      pure (.ok (ByteArray.mk #[9]))
    fchmodat := fun dir path m => do
      modify fun st => (15, recDirWord dir ||| (recBytesWord path <<< 16), m.toUInt64) :: st
      pure (.ok ())
    fchmod := fun fd m => do
      modify fun st => (16, fd.toUInt64, m.toUInt64) :: st
      pure (.ok ())
    flock := fun fd op => do
      modify fun st => (17, fd.toUInt64, op.toUInt64) :: st
      pure (.ok ())
    fcntl := fun fd tag arg => do
      modify fun st => (18, fd.toUInt64, tag.toUInt64 ||| (arg.toUInt64 <<< 32)) :: st
      pure (.ok 118)
    fsync := fun fd => do
      modify fun st => (19, fd.toUInt64, 0) :: st
      pure (.ok ())
    getcwd := fun cap => do
      modify fun st => (20, cap.toUInt64, 0) :: st
      pure (.ok (ByteArray.mk #[10]))
    lseek := fun fd off w => do
      modify fun st => (21, fd.toUInt64 ||| (w.toUInt64 <<< 32), off.toUInt64) :: st
      pure (.ok 121)
    reopenReadOnly := fun fd => do
      modify fun st => (22, fd.toUInt64, 0) :: st
      pure (.ok 122)
    dupStdio := fun slot => do
      modify fun st => (23, slot.toUInt64, 0) :: st
      pure (.ok 123) }

/-- `Internal.mkFilesOpsM` enforces all 12 embedded-NUL path guards and `fstatat` `AT_EACCESS` guard with zero raw calls, forwards all 23 methods (including `dir`, distinct paths, payload bytes, and full 64-bit `lseek` offsets) to their matching `PosixFilesOpsM` hooks, and decodes `StatInfo.ofRawTuple`. -/
def test_files_impl_mkFilesOpsM
    {runner} [NondetTest runner]
    (mkOps : Internal.PosixFilesOpsM (StateM (List (Nat × UInt64 × UInt64))) Nat →
      FilesOpsM (StateM (List (Nat × UInt64 × UInt64))) Nat) :
    runner Unit := do
  let ops := mkOps mkRecRawOps
  let badPath ← nondet ByteArray
  assume (hasEmbeddedNul badPath = true)
  let okPath := asciiBytes ['o', 'k']
  let srcPath := asciiBytes ['s', 'r']
  let dstPath := asciiBytes ['d', 's']
  let dir ← nondet (Option Nat)
  let dir2 ← nondet (Option Nat)
  let o ← nondet OpenFlags
  let r ← nondet ResolveFlags
  let a ← nondet AtFlags
  let m ← nondet AccessModeMask
  let rn ← nondet RenameFlags
  let fl ← nondet FlockOp
  let fc ← nondet FcntlCmd
  let off ← nondet Int64
  let w ← nondet SeekWhence
  let st ← nondet StdioFd
  let rm ← nondet Bool
  NondetTest.assert ((ops.openat dir badPath o 0o644).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.openat2 dir badPath { flags := o, mode := 0, resolve := r }).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.fstatat dir badPath { a with eaccess := false }).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.fstatat dir okPath { a with eaccess := true }).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.faccessat dir badPath m a).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.mkdirat dir badPath 0o755).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.unlinkat dir badPath rm).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.renameat2 dir badPath dir2 dstPath rn).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.renameat2 dir srcPath dir2 badPath rn).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.symlinkat badPath dir dstPath).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.symlinkat srcPath dir badPath).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.readlinkat dir badPath 64).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.fchmodat dir badPath 0o644).run [] = (.error Errno.EINVAL, []))
  NondetTest.assert ((ops.openat dir okPath o 0o644).run [] =
    (.ok 101, [(1, recDirWord dir ||| (recBytesWord okPath <<< 16), o.toBits.toUInt64 ||| ((0o644 : Mode).toUInt64 <<< 32))]))
  NondetTest.assert ((ops.openat2 dir okPath { flags := o, mode := 0o600, resolve := r }).run [] =
    (.ok 102, [(2, o.toBits.toUInt64 ||| ((0o600 : Mode).toUInt64 <<< 32), r.toBits), (201, recDirWord dir, recBytesWord okPath)]))
  NondetTest.assert ((ops.close 11).run [] = (.ok (), [(3, 11, 0)]))
  NondetTest.assert ((ops.read 12 32).run [] = (.ok (ByteArray.mk #[7]), [(4, 12, 32)]))
  NondetTest.assert ((ops.write 13 okPath).run [] = (.ok 105, [(5, 13, recBytesWord okPath)]))
  NondetTest.assert ((ops.fstat 14).run [] = (.ok (StatInfo.ofRawTuple (1, 9, 0o100755, 2, 3, 4, 5, 6, 7, 8)), [(6, 14, 0)]))
  NondetTest.assert ((ops.fstatat dir okPath { a with eaccess := false }).run [] =
    (.ok (StatInfo.ofRawTuple (2, 11, 0o120777, 12, 13, 14, 15, 16, 17, 18)),
     [(7, recDirWord dir ||| (recBytesWord okPath <<< 16), ({ a with eaccess := false } : AtFlags).toBits.toUInt64)]))
  NondetTest.assert ((ops.faccessat dir okPath m a).run [] =
    (.ok (), [(8, recDirWord dir ||| (recBytesWord okPath <<< 16), m.toBits.toUInt64 ||| (a.toBits.toUInt64 <<< 32))]))
  NondetTest.assert ((ops.mkdirat dir okPath 0o755).run [] =
    (.ok (), [(9, recDirWord dir ||| (recBytesWord okPath <<< 16), (0o755 : Mode).toUInt64)]))
  NondetTest.assert ((ops.unlinkat dir okPath rm).run [] =
    (.ok (), [(10, recDirWord dir ||| (recBytesWord okPath <<< 16), (if rm then (1 : UInt8) else 0).toUInt64)]))
  NondetTest.assert ((ops.renameat2 dir srcPath dir2 dstPath rn).run [] =
    (.ok (), [(11, recBytesWord srcPath, recBytesWord dstPath),
              (1101, recDirWord dir ||| (recDirWord dir2 <<< 32), rn.toBits.toUInt64)]))
  NondetTest.assert ((ops.symlinkat srcPath dir dstPath).run [] =
    (.ok (), [(12, recDirWord dir ||| (recBytesWord srcPath <<< 16), recBytesWord dstPath)]))
  NondetTest.assert ((ops.readlinkat dir okPath 64).run [] =
    (.ok (ByteArray.mk #[8]), [(13, recDirWord dir ||| (recBytesWord okPath <<< 16), 64)]))
  NondetTest.assert ((ops.getdents64 15 128).run [] = (.ok (ByteArray.mk #[9]), [(14, 15, 128)]))
  NondetTest.assert ((ops.fchmodat dir okPath 0o700).run [] =
    (.ok (), [(15, recDirWord dir ||| (recBytesWord okPath <<< 16), (0o700 : Mode).toUInt64)]))
  NondetTest.assert ((ops.fchmod 16 0o600).run [] = (.ok (), [(16, 16, (0o600 : Mode).toUInt64)]))
  NondetTest.assert ((ops.flock 17 fl).run [] = (.ok (), [(17, 17, fl.toBits.toUInt64)]))
  NondetTest.assert ((ops.fcntl 18 fc).run [] = ((Except.ok (118 : UInt32) : Except Errno UInt32), [(18, (18 : UInt64), fc.toRaw.1.toUInt64 ||| (fc.toRaw.2.toUInt64 <<< 32))]))
  NondetTest.assert ((ops.fsync 19).run [] = (.ok (), [(19, 19, 0)]))
  NondetTest.assert ((ops.getcwd 256).run [] = (.ok (ByteArray.mk #[10]), [(20, 256, 0)]))
  NondetTest.assert ((ops.lseek 20 off w).run [] = ((Except.ok (121 : UInt64) : Except Errno UInt64), [(21, (20 : UInt64) ||| (w.toRaw.toUInt64 <<< 32), off.toUInt64)]))
  NondetTest.assert ((ops.reopenReadOnly 21).run [] = (.ok 122, [(22, 21, 0)]))
  NondetTest.assert ((ops.dupStdio st).run [] = (.ok 123, [(23, st.toRaw.toUInt64, 0)]))

/-- All 23 top-level `LeanSwe.LinuxSyscall.Files` wrappers and their default arguments delegate directly to `defaultOps`. -/
def test_files_interface_wrappersAndDefaults
    {runner} [NondetTest runner]
    (ops : FilesOps)
    (wOpenat : Option RawFd → ByteArray → OpenFlags → Mode → IO (Except Errno RawFd))
    (wOpenatDef : Option RawFd → ByteArray → OpenFlags → IO (Except Errno RawFd))
    (wOpenat2 : Option RawFd → ByteArray → OpenHow → IO (Except Errno RawFd))
    (wClose : RawFd → IO (Except Errno Unit))
    (wRead : RawFd → UInt32 → IO (Except Errno ByteArray))
    (wWrite : RawFd → ByteArray → IO (Except Errno UInt32))
    (wFstat : RawFd → IO (Except Errno StatInfo))
    (wFstatat : Option RawFd → ByteArray → AtFlags → IO (Except Errno StatInfo))
    (wFstatatDef : Option RawFd → ByteArray → IO (Except Errno StatInfo))
    (wFaccessat : Option RawFd → ByteArray → AccessModeMask → AtFlags → IO (Except Errno Unit))
    (wFaccessatDef : Option RawFd → ByteArray → IO (Except Errno Unit))
    (wMkdirat : Option RawFd → ByteArray → Mode → IO (Except Errno Unit))
    (wMkdiratDef : Option RawFd → ByteArray → IO (Except Errno Unit))
    (wUnlinkat : Option RawFd → ByteArray → Bool → IO (Except Errno Unit))
    (wUnlinkatDef : Option RawFd → ByteArray → IO (Except Errno Unit))
    (wRenameat2 : Option RawFd → ByteArray → Option RawFd → ByteArray → RenameFlags → IO (Except Errno Unit))
    (wRenameat2Def : Option RawFd → ByteArray → Option RawFd → ByteArray → IO (Except Errno Unit))
    (wSymlinkat : ByteArray → Option RawFd → ByteArray → IO (Except Errno Unit))
    (wReadlinkat : Option RawFd → ByteArray → UInt32 → IO (Except Errno ByteArray))
    (wReadlinkatDef : Option RawFd → ByteArray → IO (Except Errno ByteArray))
    (wGetdents64 : RawFd → UInt32 → IO (Except Errno ByteArray))
    (wGetdents64Def : RawFd → IO (Except Errno ByteArray))
    (wFchmodat : Option RawFd → ByteArray → Mode → IO (Except Errno Unit))
    (wFchmod : RawFd → Mode → IO (Except Errno Unit))
    (wFlock : RawFd → FlockOp → IO (Except Errno Unit))
    (wFcntl : RawFd → FcntlCmd → IO (Except Errno UInt32))
    (wFsync : RawFd → IO (Except Errno Unit))
    (wGetcwd : UInt32 → IO (Except Errno ByteArray))
    (wGetcwdDef : IO (Except Errno ByteArray))
    (wLseek : RawFd → Int64 → SeekWhence → IO (Except Errno UInt64))
    (wLseekDef : RawFd → Int64 → IO (Except Errno UInt64))
    (wReopenReadOnly : RawFd → IO (Except Errno RawFd))
    (wDupStdio : StdioFd → IO (Except Errno RawFd)) : runner Unit := do
  let dir ← nondet (Option RawFd)
  let dir2 ← nondet (Option RawFd)
  let path ← nondet ByteArray
  let path2 ← nondet ByteArray
  let fd ← nondet RawFd
  let flags ← nondet OpenFlags
  let how ← nondet OpenHow
  let mode ← nondet Mode
  let atFlags ← nondet AtFlags
  let mask ← nondet AccessModeMask
  let rm ← nondet Bool
  let renFlags ← nondet RenameFlags
  let cap ← nondet UInt32
  let flockOp ← nondet FlockOp
  let cmd ← nondet FcntlCmd
  let off ← nondet Int64
  let whence ← nondet SeekWhence
  let slot ← nondet StdioFd
  NondetTest.assert (wOpenat dir path flags mode = ops.openat dir path flags mode)
  NondetTest.assert (wOpenatDef dir path flags = ops.openat dir path flags 0o644)
  NondetTest.assert (wOpenat2 dir path how = ops.openat2 dir path how)
  NondetTest.assert (wClose fd = ops.close fd)
  NondetTest.assert (wRead fd cap = ops.read fd cap)
  NondetTest.assert (wWrite fd path = ops.write fd path)
  NondetTest.assert (wFstat fd = ops.fstat fd)
  NondetTest.assert (wFstatat dir path atFlags = ops.fstatat dir path atFlags)
  NondetTest.assert (wFstatatDef dir path = ops.fstatat dir path {})
  NondetTest.assert (wFaccessat dir path mask atFlags = ops.faccessat dir path mask atFlags)
  NondetTest.assert (wFaccessatDef dir path = ops.faccessat dir path {} {})
  NondetTest.assert (wMkdirat dir path mode = ops.mkdirat dir path mode)
  NondetTest.assert (wMkdiratDef dir path = ops.mkdirat dir path 0o755)
  NondetTest.assert (wUnlinkat dir path rm = ops.unlinkat dir path rm)
  NondetTest.assert (wUnlinkatDef dir path = ops.unlinkat dir path false)
  NondetTest.assert (wRenameat2 dir path dir2 path2 renFlags = ops.renameat2 dir path dir2 path2 renFlags)
  NondetTest.assert (wRenameat2Def dir path dir2 path2 = ops.renameat2 dir path dir2 path2 {})
  NondetTest.assert (wSymlinkat path dir path2 = ops.symlinkat path dir path2)
  NondetTest.assert (wReadlinkat dir path cap = ops.readlinkat dir path cap)
  NondetTest.assert (wReadlinkatDef dir path = ops.readlinkat dir path 4096)
  NondetTest.assert (wGetdents64 fd cap = ops.getdents64 fd cap)
  NondetTest.assert (wGetdents64Def fd = ops.getdents64 fd 8192)
  NondetTest.assert (wFchmodat dir path mode = ops.fchmodat dir path mode)
  NondetTest.assert (wFchmod fd mode = ops.fchmod fd mode)
  NondetTest.assert (wFlock fd flockOp = ops.flock fd flockOp)
  NondetTest.assert (wFcntl fd cmd = ops.fcntl fd cmd)
  NondetTest.assert (wFsync fd = ops.fsync fd)
  NondetTest.assert (wGetcwd cap = ops.getcwd cap)
  NondetTest.assert (wGetcwdDef = ops.getcwd 4096)
  NondetTest.assert (wLseek fd off whence = ops.lseek fd off whence)
  NondetTest.assert (wLseekDef fd off = ops.lseek fd off .seekSet)
  NondetTest.assert (wReopenReadOnly fd = ops.reopenReadOnly fd)
  NondetTest.assert (wDupStdio slot = ops.dupStdio slot)

/-- Seeded fixture exercising dynamic FIFO `ENXIO` and closed-stdio shared-OFD invariants. -/
def dynamicFifoStdioState : FilesState :=
  { FilesState.withSeededTree {
      cwdPath := asciiBytes ['/', 'w']
      stdoutKind := .other
      cwdEntries := [
        { name := asciiBytes ['d', 'f'], kind := .fifo, mode := 0o644, modeExact := true, dynamicMeta := true },
        { name := asciiBytes ['r', 'a'], kind := .reg, mode := 0o644, modeExact := true, bytes := asciiBytes ['o', 'k'] },
        { name := asciiBytes ['d', 'r'], kind := .reg, mode := 0o644, dynamicMeta := true }
      ]
    } with freeStdioSlots := [.stdin] }

/-- Specification of dynamic FIFO `O_WRONLY | O_NONBLOCK` `ENXIO`, closed-stdio `.reopenExternalStdio` slot binding, and shared-OFD `.readDynamic` offset propagation. -/
def test_files_model_dynamicFifoStdioInvariants
    {runner} [NondetTest runner]
    (step : FilesState → FilesReq → FilesOutcome → Option FilesState := allowedStep)
    (eval : FilesState → FilesReq → FilesOutcome × FilesState := evalModel) : runner Unit := do
  NondetTest.assert ((step dynamicFifoStdioState
    (.openat none (asciiBytes ['d', 'f']) { access := .wronly, nonblock := true } 0)
    (.err Errno.ENXIO)).isSome = true)
  let (rExt, s1) := eval dynamicFifoStdioState
    (.openat none (asciiBytes ['/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 'f', 'd', '/', '1'])
      { path := true, directory := true } 0)
  let (rReg, s2) := eval s1 (.openat none (asciiBytes ['r', 'a']) { access := .rdonly } 0)
  NondetTest.assert (∃ hExt hReg dExt dReg,
    rExt = .opened hExt ∧ rReg = .opened hReg ∧
    assocGet s2.fds hExt = some dExt ∧ assocGet s2.fds hReg = some dReg ∧
    dExt.ofdId? = some 0 ∧ dReg.ofdId? = none)
  let (_, sOut) := eval dynamicFifoStdioState (.dupStdio .stdout)
  let (_, sRe) := eval sOut (.reopenReadOnly 0)
  let (rDup0, _) := eval sRe (.dupStdio .stdin)
  NondetTest.assert (rDup0 = .opened 2)
  let (_, sD1) := eval dynamicFifoStdioState (.openat none (asciiBytes ['d', 'r']) { access := .rdonly } 0)
  let (_, sD2) := eval sD1 (.dupStdio .stdin)
  let sD3? := step sD2 (.read 0 5) (.bytes (asciiBytes ['a', 'b', 'c']))
  NondetTest.assert (∃ sD3 d0 d1,
    sD3? = some sD3 ∧ assocGet sD3.fds 0 = some d0 ∧ assocGet sD3.fds 1 = some d1 ∧
    d0.pos = .byteOffset 3 ∧ d1.pos = .byteOffset 3)

/-- Specification for shared-OFD `getdents64` per-FD `cloexec`/`closeState` preservation, `ambientSeccomp` FIFO `EAGAIN` non-calibration parity, and `!initUserNs` creation `EOVERFLOW` (`75`) allowance. -/
def test_files_model_stateRefinementAndUserns
    {runner} [NondetTest runner]
    (step : FilesState → FilesReq → FilesOutcome → Option FilesState := allowedStep)
    (eval : FilesState → FilesReq → FilesOutcome × FilesState := evalModel) : runner Unit := do
  let sCs0 : FilesState := { FilesState.initial with freeStdioSlots := [.stdin] }
  let (_, sCs1) := eval sCs0 (.openat none (asciiBytes ['.']) { access := .rdonly, directory := true, cloexec := false } 0)
  let (_, sCs2) := eval sCs1 (.dupStdio .stdin)
  let (oGd, sCs3) := eval sCs2 (.getdents64 0 4096)
  let (oFc0, _) := eval sCs3 (.fcntl 0 .getFd)
  let (oFc1, _) := eval sCs3 (.fcntl 1 .getFd)
  NondetTest.assert (oFc0 = .u32 0 ∧ oFc1 = .u32 1 ∧ step sCs2 (.getdents64 0 4096) oGd = some sCs3)
  let fullRing : PipeRing := {
    buf := ByteArray.mk #[1, 2]
    slots := [(4096, 1), (4096, 1)]
    readers := 1
    writers := 1
    capacity := .uncalibrated 2 16
  }
  let sSec0 : FilesState := {
    FilesState.initial with
    ambientSeccomp := true
    inodes := assocSet FilesState.initial.inodes 1 { data := .fifo fullRing, mode := 0o644, modeExact := true, nlink := 1 }
    fds := [(0, { ino := 1, access := .wronly, nonblock := true })]
    nextIno := 2
    nextHid := 1
  }
  let (oFifo, sSec1) := eval sSec0 (.write 0 (asciiBytes ['x']))
  NondetTest.assert (oFifo = .err Errno.EAGAIN ∧ step sSec0 (.write 0 (asciiBytes ['x'])) oFifo = some sSec1)
  let sUnmap : FilesState := { FilesState.initial with cred := { initUserNs := false } }
  NondetTest.assert ((step sUnmap (.openat none (asciiBytes ['f']) { access := .rdwr, creat := true } 0o644) (.err 75)).isSome = true)
  NondetTest.assert ((step sUnmap (.mkdirat none (asciiBytes ['d']) 0o755) (.err 75)).isSome = true)
  NondetTest.assert ((step sUnmap (.symlinkat (asciiBytes ['t']) none (asciiBytes ['s'])) (.err 75)).isSome = true)
  NondetTest.assert (step FilesState.initial (.mkdirat none (asciiBytes ['d']) 0o755) (.err 75) = none)

end LeanSwe.LinuxSyscall.Files
