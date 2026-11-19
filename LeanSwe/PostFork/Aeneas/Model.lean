import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Aeneas.FunsExternal

open _root_.Aeneas _root_.Aeneas.Std Result

namespace LeanSwe.PostFork.Aeneas.Model

open LeanSwe.PostFork
open LeanSwe.PostFork.World

/-- Child flag bit `0`: `FLAG_SET_PGID`. -/
def FLAG_SET_PGID : Std.U32 := 1#u32
/-- Child flag bit `1`: `FLAG_RESET_SIGPIPE`. -/
def FLAG_RESET_SIGPIPE : Std.U32 := 2#u32
/-- Child flag bit `2`: `FLAG_HAS_SYNC_BARRIER`. -/
def FLAG_HAS_SYNC_BARRIER : Std.U32 := 4#u32
/-- Child flag bit `3`: `FLAG_REDIRECT_STDIO`. -/
def FLAG_REDIRECT_STDIO : Std.U32 := 8#u32
/-- Child flag bit `4`: `FLAG_CLOSE_UNKEPT_ABOVE2`. -/
def FLAG_CLOSE_UNKEPT_ABOVE2 : Std.U32 := 16#u32
/-- Child flag bit `5`: `FLAG_CLOSE_STDIO_SOURCES`. -/
def FLAG_CLOSE_STDIO_SOURCES : Std.U32 := 32#u32

/-- Construct a `Slice Std.I32` of length `n` from `xs`. -/
def mkSliceI32 (n : Std.Usize) (xs : List Std.I32) (h : xs.length = n.val := by simp) : Slice Std.I32 :=
  Array.to_slice (Array.make n xs h)

/-- Construct a `Slice Std.U8` of length `n` from `xs`. -/
def mkSliceU8 (n : Std.Usize) (xs : List Std.U8) (h : xs.length = n.val := by simp) : Slice Std.U8 :=
  Array.to_slice (Array.make n xs h)

/-- Require an Aeneas `Result α` computation to terminate with `ok v` satisfying `post v`. -/
def OkPost {α : Type} (r : Result α) (post : α → Prop) : Prop :=
  ∃ v : α, r = ok v ∧ post v

/-- Extract the 4 little-endian `Std.U8` bytes of a 32-bit two's-complement integer `v`. -/
def expectedI32LeBytes (v : Std.I32) : Bytes :=
  [ ⟨v.bv.extractLsb' 0 8⟩
  , ⟨v.bv.extractLsb' 8 8⟩
  , ⟨v.bv.extractLsb' 16 8⟩
  , ⟨v.bv.extractLsb' 24 8⟩ ]

/-- Reference 8-byte failure wire frame `[0x50, 0x01, stage, 0x00, err_le32]`. -/
def expectedFailureWireBytes (stage : Std.U8) (errnum : Std.I32) : Bytes :=
  [80#u8, 1#u8, stage, 0#u8] ++ expectedI32LeBytes errnum

/-- Normalize a possibly zero/negative `errno` to `fallback` (`> 0` preserved). -/
def normalizeErrnoSpec (err fallback : Std.I32) : Std.I32 :=
  if err > 0#i32 then err else fallback

/-- Return `true` iff `fd >= 0` occurs in `fds`. -/
def sliceContainsNonnegSpec (fds : List Std.I32) (fd : Int) : Bool :=
  decide (0 ≤ fd) && fds.any (fun x => x.val == fd)

/-- Return `true` iff `a` and `b` share any non-negative descriptor number. -/
def slicesOverlapNonnegSpec (a b : List Std.I32) : Bool :=
  a.any (fun x => decide (0 ≤ x.val) && sliceContainsNonnegSpec b x.val)

/-- Return `true` iff `fds` contains any stdio descriptor in `0..2`. -/
def sliceHasStdioSlotSpec (fds : List Std.I32) : Bool :=
  fds.any (fun x => decide (0 ≤ x.val) && decide (x.val ≤ 2))

/-- Return `true` iff `fd > 2` is protected by `extraKeep` or `keepFds`. -/
def isKeptAbove2 (extraKeep : Std.I32) (keepFds : List Std.I32) (fd : Int) : Bool :=
  decide (fd > 2) &&
    ((decide (extraKeep.val > 2) && extraKeep.val == fd) ||
      sliceContainsNonnegSpec keepFds fd)

/-- Reference parser for a `/proc/self/fd` `linux_dirent64` `d_name` region `buf[start..stop)`. -/
def expectedDirentParse (buf : Array Std.U8 256#usize) (start stop : Std.Usize) : Std.I32 :=
  if stop.val > 256 || start.val ≥ stop.val then
    (-2)#i32
  else
    let region := (buf.val.take stop.val).drop start.val
    match region.findIdx? (fun b => b == 0#u8) with
    | none => (-2)#i32
    | some 0 => (-2)#i32
    | some nulIdx =>
      if nulIdx ≥ region.length then
        (-2)#i32
      else
        let nm := region.take nulIdx
        if !nm.all (fun b => 48#u8 ≤ b && b ≤ 57#u8) then
          (-1)#i32
        else if nm.length > 1 && nm.head? == some 48#u8 then
          (-1)#i32
        else
          let val := nm.foldl (fun acc b => acc * 10 + (b.val - 48)) 0
          if val > 2147483647 then
            (-1)#i32
          else
            mkI32 (Int.ofNat val)

/-- Concatenate all bytes logged for open-file-description `d` in `log`. -/
def writtenBytesForDesc (log : List (Desc × Bytes)) (d : Desc) : Bytes :=
  (log.filterMap fun (d', bs) => if d' == d then some bs else none).flatten

/-- Newly appended bytes written to `d` between `beforeLog` and `afterLog`. -/
def appendedBytesForDesc (beforeLog afterLog : List (Desc × Bytes)) (d : Desc) : Bytes :=
  writtenBytesForDesc (afterLog.drop beforeLog.length) d

/-- Expected `extraFdFlags` after `F_GETFD` + `F_SETFD` on entry `e` in state `s`. -/
def expectedExtraFlagsAfterSetfd (s : ChildState) (e : FdEntry) : Std.I32 :=
  if s.kernelMasksSetfd then 0#i32 else fdFlagsWord e &&& 2147483646#i32

/-- Fault-free postcondition for `clearCloexec` and `setCloexec` (`targetClo = false` / `true`). -/
def CloexecTogglePost
    (targetClo : Bool)
    (s : ChildState)
    (fd : Std.I32)
    (res : core.result.Result Unit Std.I32)
    (s' : ChildState) : Prop :=
  match s.getFd fd.val with
  | none => res = .Err EBADF ∧ s'.fds = s.fds
  | some e =>
    res = .Ok () ∧
      s'.getFd fd.val =
        some { desc := e.desc, cloexec := targetClo, extraFdFlags := expectedExtraFlagsAfterSetfd s e } ∧
      ∀ k : Int, k ≠ fd.val → s'.getFd k = s.getFd k

/-- Fault-free postcondition for `relocateRepAbove2`. -/
def RelocateRepPost
    (s : ChildState)
    (repW : Std.I32)
    (res : core.result.Result Std.I32 Std.I32)
    (s' : ChildState) : Prop :=
  if repW < 0#i32 then
    res = .Err EBADF ∧ s' = s
  else
    match s.getFd repW.val with
    | none => res = .Err EBADF ∧ s'.fds = s.fds
    | some e =>
      if repW.val ≤ 2 then
        if 3 ≥ s.fdLimit then
          res = .Err EINVAL ∧ s'.fds = s.fds
        else
          match findLowestFreeFd s 3 with
          | none => res = .Err EMFILE ∧ s'.fds = s.fds
          | some dst =>
            res = .Ok (mkI32 dst) ∧
              dst ≥ 3 ∧
              s'.getFd repW.val = none ∧
              s'.getFd dst = some { desc := e.desc, cloexec := true, extraFdFlags := 0#i32 } ∧
              ∀ k : Int, k ≠ repW.val → k ≠ dst → s'.getFd k = s.getFd k
      else
        res = .Ok repW ∧
          s'.getFd repW.val =
            some { desc := e.desc, cloexec := true, extraFdFlags := expectedExtraFlagsAfterSetfd s e } ∧
          ∀ k : Int, k ≠ repW.val → s'.getFd k = s.getFd k

/-- Fault-free postcondition for `setupStdio` routing `(inFd, outFd, errFd)` onto `(0, 1, 2)` without clobbering or leaking scratch descriptors. -/
def SetupStdioPost
    (s : ChildState)
    (inFd outFd errFd : Std.I32)
    (closeAbove2 : Bool)
    (s' : ChildState) : Prop :=
  (∃ e0 f0, s.getFd inFd.val = some e0 ∧ s'.getFd 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
  (∃ e1 f1, s.getFd outFd.val = some e1 ∧ s'.getFd 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
  (∃ e2 f2, s.getFd errFd.val = some e2 ∧ s'.getFd 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false) ∧
  ∀ k : Int, k > 2 →
    s'.getFd k =
      if closeAbove2 && (k == inFd.val || k == outFd.val || k == errFd.val) then
        none
      else
        s.getFd k

/-- Postcondition for `closeFdsAbove2Except`: every unkept 32-bit descriptor `> 2` is closed and `0..2` plus kept descriptors are preserved. -/
def CloseAbove2Post
    (s : ChildState)
    (extraKeep : Std.I32)
    (keepFds : List Std.I32)
    (s' : ChildState) : Prop :=
  (∀ fd : Int, 0 ≤ fd → fd ≤ 2 → s'.getFd fd = s.getFd fd) ∧
  (∀ fd : Int, 3 ≤ fd → fd ≤ 2147483647 →
    if isKeptAbove2 extraKeep keepFds fd then
      s'.getFd fd = s.getFd fd
    else
      s'.getFd fd = none)

/-- Look up descriptor `fd` in an `ExecImage.fds` table. -/
def execImageGetFd (img : ExecImage) (fd : Int) : Option FdEntry :=
  match img.fds.find? (fun p => p.1 == fd) with
  | some (_, e) => some e
  | none => none

/-- Look up signal disposition `g` in an `ExecImage.sig` table (defaulting to `.default`). -/
def execImageGetSig (img : ExecImage) (g : Int) : Disp :=
  match img.sig.find? (fun p => p.1 == g) with
  | some (_, d) => d
  | none => .default

/-- Expected working directory after optional `chdir`. -/
def expectedCwdAfter (origCwd : Bytes) (cwd? : Option Bytes)
    (chdirResolved : List (Bytes × Bytes) := []) : Bytes :=
  match cwd? with
  | none => origCwd
  | some dir =>
    match chdirResolved.find? (fun p => p.1 == dir) with
    | some (_, resolved) => resolved
    | none => chdirTarget origCwd dir

/-- Every non-negative descriptor in `closeFds` is closed via `Req.close` before `newTrace` issues `Req.read1 syncR`. -/
def closedBeforeSyncRead (newTrace : List Event) (closeFds : List Std.I32) (syncR : Std.I32) : Prop :=
  let beforeRead := newTrace.takeWhile (fun ev => ev.req != .read1 syncR)
  ∀ cfd ∈ closeFds, 0#i32 ≤ cfd → ∃ out, Event.mk (.close cfd) out ∈ beforeRead

/-- Return `true` iff any bit of `mask` is set in `flags`. -/
def flagSet (flags mask : Std.U32) : Bool :=
  (flags &&& mask) != 0#u32

/-- Return `true` iff `flags` only enables known `FLAG_*` bits and valid flag combinations. -/
def validFlagsSpec (flags : Std.U32) : Bool :=
  ((flags &&& 4294967232#u32) == 0#u32) &&
  (!(flagSet flags FLAG_CLOSE_STDIO_SOURCES) ||
    (flagSet flags FLAG_REDIRECT_STDIO && !(flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2)))

/-- Return `true` iff enabled `syncR` and stdio source descriptors are non-negative. -/
def validSignsSpec (flags : Std.U32) (syncR inFd outFd errFd : Std.I32) : Bool :=
  (!(flagSet flags FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR)) &&
  (!(flagSet flags FLAG_REDIRECT_STDIO) ||
    (decide (0#i32 ≤ inFd) && decide (0#i32 ≤ outFd) && decide (0#i32 ≤ errFd)))

/-- Return `true` iff `fd` aliases one of `(inFd, outFd, errFd)`. -/
def fdInStdioSpec (fd inFd outFd errFd : Std.I32) : Bool :=
  fd == inFd || fd == outFd || fd == errFd

/-- Return `true` iff any of `(inFd, outFd, errFd)` occurs non-negatively in `fds`. -/
def stdioInSliceSpec (fds : List Std.I32) (inFd outFd errFd : Std.I32) : Bool :=
  sliceContainsNonnegSpec fds inFd.val ||
  sliceContainsNonnegSpec fds outFd.val ||
  sliceContainsNonnegSpec fds errFd.val

/-- Return `true` iff `syncR`, stdio sources, `repW`, `closeFds`, and `keepFds` satisfy all disjointness invariants. -/
def validRunChildNoOverlap
    (flags : Std.U32)
    (syncR inFd outFd errFd repW : Std.I32)
    (closeFds keepFds : List Std.I32) : Bool :=
  !sliceContainsNonnegSpec closeFds repW.val &&
  !sliceContainsNonnegSpec keepFds repW.val &&
  !slicesOverlapNonnegSpec closeFds keepFds &&
  (!(flagSet flags FLAG_HAS_SYNC_BARRIER) ||
    (repW != syncR &&
      !sliceContainsNonnegSpec closeFds syncR.val &&
      !sliceContainsNonnegSpec keepFds syncR.val)) &&
  (!(flagSet flags FLAG_REDIRECT_STDIO) ||
    (!sliceHasStdioSlotSpec keepFds &&
      !fdInStdioSpec repW inFd outFd errFd &&
      !stdioInSliceSpec closeFds inFd outFd errFd &&
      (!(flagSet flags FLAG_HAS_SYNC_BARRIER) || !fdInStdioSpec syncR inFd outFd errFd) &&
      (!(flagSet flags FLAG_CLOSE_STDIO_SOURCES) ||
        ((!(decide (inFd > 2#i32)) || !sliceContainsNonnegSpec keepFds inFd.val) &&
         (!(decide (outFd > 2#i32)) || !sliceContainsNonnegSpec keepFds outFd.val) &&
         (!(decide (errFd > 2#i32)) || !sliceContainsNonnegSpec keepFds errFd.val)))))

/-- Minimum `fdLimit` headroom above `s.fds.length` needed to guarantee scratch descriptor allocation succeeds cleanly. -/
def minRunChildFdSlack (flags : Std.U32) : Int :=
  if flagSet flags FLAG_REDIRECT_STDIO then 6 else 4

/-- Preconditions under which unified `postfork.child.run_child` completes cleanly into `execve`. -/
def ValidRunChildExecPre
    (s : ChildState)
    (flags : Std.U32)
    (syncR inFd outFd errFd repW : Std.I32)
    (closeFds keepFds : List Std.I32)
    (cwd? : Option Bytes)
    (path : Bytes) : Prop :=
  s.status = .running ∧
  s.oracle = [] ∧
  validFlagsSpec flags = true ∧
  0#i32 ≤ repW ∧
  validSignsSpec flags syncR inFd outFd errFd = true ∧
  validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds keepFds = true ∧
  (flagSet flags FLAG_SET_PGID = true → s.pid > 0 ∧ s.pid ≠ s.sid) ∧
  min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length ∧
  (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true →
    s.closeRangeSupported = true ∨ s.procSelfFdAvailable = true) ∧
  s.isOpen repW.val = true ∧
  (flagSet flags FLAG_REDIRECT_STDIO = true →
    s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true) ∧
  (∀ k ∈ keepFds, 0#i32 ≤ k → s.isOpen k.val = true) ∧
  (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
    ∃ es ws bs b rest,
      s.getFd syncR.val = some es ∧
      s.getDesc es.desc = .stream true ws bs (b :: rest)) ∧
  path ≠ [] ∧
  ∀ dir : Bytes, cwd? = some dir → dir ≠ []

/-- Exact postcondition of a successful `postfork.child.run_child` execution across all flag combinations. -/
def RunChildExecPost
    (s : ChildState)
    (flags : Std.U32)
    (syncR inFd outFd errFd repW : Std.I32)
    (closeFds keepFds : List Std.I32)
    (cwd? : Option Bytes)
    (path : Bytes)
    (argv envp : List Bytes)
    (s' : ChildState) : Prop :=
  ∃ img : ExecImage,
    s'.status = .execd img ∧
    s'.writeLog = s.writeLog ∧
    (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
      closedBeforeSyncRead (s'.trace.drop s.trace.length) closeFds syncR) ∧
    img.path = path ∧
    img.argv = effectiveExecArgv argv ∧
    img.envp = envp ∧
    img.pgid = (if flagSet flags FLAG_SET_PGID then s.pid else s.pgid) ∧
    img.cwd = expectedCwdAfter s.cwd cwd? s.chdirResolved ∧
    (flagSet flags FLAG_RESET_SIGPIPE = true →
      execImageGetSig img 13 = .default ∧
      img.blockedSigs = s.blockedSigs.filter (· != 13)) ∧
    (flagSet flags FLAG_RESET_SIGPIPE = false →
      execImageGetSig img 13 = (if s.getSig 13 == .ignore then .ignore else .default) ∧
      img.blockedSigs = s.blockedSigs) ∧
    (∀ g : Int, g ≠ 13 →
      execImageGetSig img g = (if s.getSig g == .ignore then .ignore else .default)) ∧
    ((flagSet flags FLAG_REDIRECT_STDIO = false ∨ 2 < repW.val) →
      execImageGetFd img repW.val = none) ∧
    (flagSet flags FLAG_REDIRECT_STDIO = true →
      (∃ e0 f0, s.getFd inFd.val = some e0 ∧ execImageGetFd img 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
      (∃ e1 f1, s.getFd outFd.val = some e1 ∧ execImageGetFd img 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
      (∃ e2 f2, s.getFd errFd.val = some e2 ∧ execImageGetFd img 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false)) ∧
    (flagSet flags FLAG_REDIRECT_STDIO = false →
      ∀ fd : Int, 0 ≤ fd → fd ≤ 2 →
        if fd == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && fd == syncR.val) ||
            sliceContainsNonnegSpec closeFds fd then
          execImageGetFd img fd = none
        else if sliceContainsNonnegSpec keepFds fd then
          ∃ ek fk, s.getFd fd = some ek ∧ execImageGetFd img fd = some fk ∧ fk.desc = ek.desc ∧ fk.cloexec = false
        else
          match s.getFd fd with
          | some e => execImageGetFd img fd = if e.cloexec then none else some e
          | none => execImageGetFd img fd = none) ∧
    (∀ k ∈ keepFds, 0#i32 ≤ k →
      ∃ ek fk, s.getFd k.val = some ek ∧ execImageGetFd img k.val = some fk ∧ fk.desc = ek.desc ∧ fk.cloexec = false) ∧
    (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true →
      ∀ k : Int, 3 ≤ k → k ≤ 2147483647 →
        sliceContainsNonnegSpec keepFds k = false → execImageGetFd img k = none) ∧
    (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = false →
      ∀ k : Int, k > 2 →
        if k == repW.val || (flagSet flags FLAG_HAS_SYNC_BARRIER && k == syncR.val) ||
            sliceContainsNonnegSpec closeFds k ||
            (flagSet flags FLAG_CLOSE_STDIO_SOURCES &&
              (k == inFd.val || k == outFd.val || k == errFd.val)) then
          execImageGetFd img k = none
        else if sliceContainsNonnegSpec keepFds k then
          ∃ ek fk, s.getFd k = some ek ∧ execImageGetFd img k = some fk ∧ fk.desc = ek.desc ∧ fk.cloexec = false
        else
          match s.getFd k with
          | some e => execImageGetFd img k = if e.cloexec then none else some e
          | none => execImageGetFd img k = none)

/-- Return `true` iff `fault` is a seccomp-bpf `SECCOMP_RET_ERRNO` directive. -/
def isSeccompFault : StepFault → Bool
  | .seccomp _ => true
  | _ => false

/-- Return `true` iff `oracle` contains any seccomp fault directive. -/
def oracleHasSeccomp (oracle : List StepFault) : Bool :=
  oracle.any isSeccompFault

/-- Universal fault-tolerant safety invariant for `postfork.child.run_child` across arbitrary `s.oracle`. -/
def RunChildSafetyPost
    (s : ChildState)
    (flags : Std.U32)
    (syncR inFd outFd errFd repW : Std.I32)
    (closeFds keepFds : List Std.I32)
    (cwd? : Option Bytes)
    (path : Bytes)
    (argv envp : List Bytes)
    (s' : ChildState) : Prop :=
  s'.status = .exited 127#i32 ∨
  (flagSet flags FLAG_HAS_SYNC_BARRIER = true ∧
    s'.status = .exited 125#i32 ∧
    s'.writeLog = s.writeLog ∧
    (oracleHasSeccomp s.oracle = false →
      s'.isOpen syncR.val = false ∧
      (∀ cfd ∈ closeFds, 0#i32 ≤ cfd → s'.isOpen cfd.val = false)) ∧
    closedBeforeSyncRead (s'.trace.drop s.trace.length) closeFds syncR) ∨
  ((oracleHasSeccomp s.oracle = false →
      RunChildExecPost s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp s') ∧
   ∃ img : ExecImage,
     s'.status = .execd img ∧
     s'.writeLog = s.writeLog ∧
     (flagSet flags FLAG_HAS_SYNC_BARRIER = true →
       closedBeforeSyncRead (s'.trace.drop s.trace.length) closeFds syncR) ∧
     img.path = path ∧
     img.argv = effectiveExecArgv argv ∧
     img.envp = envp ∧
     img.cwd = expectedCwdAfter s.cwd cwd? s.chdirResolved ∧
     (flagSet flags FLAG_RESET_SIGPIPE = true →
       execImageGetSig img 13 = .default ∧
       img.blockedSigs.contains 13 = false) ∧
     (∀ g : Int, g ≠ 13 →
       execImageGetSig img g = (if s.getSig g == .ignore then .ignore else .default)) ∧
     (flagSet flags FLAG_REDIRECT_STDIO = true →
       (∃ e0 f0, s.getFd inFd.val = some e0 ∧ execImageGetFd img 0 = some f0 ∧ f0.desc = e0.desc ∧ f0.cloexec = false) ∧
       (∃ e1 f1, s.getFd outFd.val = some e1 ∧ execImageGetFd img 1 = some f1 ∧ f1.desc = e1.desc ∧ f1.cloexec = false) ∧
       (∃ e2 f2, s.getFd errFd.val = some e2 ∧ execImageGetFd img 2 = some f2 ∧ f2.desc = e2.desc ∧ f2.cloexec = false)) ∧
     (∀ k ∈ keepFds, 0#i32 ≤ k →
       ∃ ek fk, s.getFd k.val = some ek ∧ execImageGetFd img k.val = some fk ∧ fk.desc = ek.desc ∧ fk.cloexec = false) ∧
     (flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 = true →
       ∀ k : Int, 3 ≤ k → k ≤ 2147483647 →
         sliceContainsNonnegSpec keepFds k = false → execImageGetFd img k = none))

end LeanSwe.PostFork.Aeneas.Model
