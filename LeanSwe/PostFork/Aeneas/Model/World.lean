import LeanSwe.PostFork.Aeneas.Types

open _root_.Aeneas _root_.Aeneas.Std Result

namespace LeanSwe.PostFork.Aeneas.Internal.World

/-- Linux `EPERM` (`1`). -/
def EPERM : Std.I32 := 1#i32
/-- Linux `ENOENT` (`2`). -/
def ENOENT : Std.I32 := 2#i32
/-- Linux `EINTR` (`4`). -/
def EINTR : Std.I32 := 4#i32
/-- Linux `EIO` (`5`). -/
def EIO : Std.I32 := 5#i32
/-- Linux `EBADF` (`9`). -/
def EBADF : Std.I32 := 9#i32
/-- Linux `EACCES` (`13`). -/
def EACCES : Std.I32 := 13#i32
/-- Linux `ENOTDIR` (`20`). -/
def ENOTDIR : Std.I32 := 20#i32
/-- Linux `EISDIR` (`21`). -/
def EISDIR : Std.I32 := 21#i32
/-- Linux `EINVAL` (`22`). -/
def EINVAL : Std.I32 := 22#i32
/-- Linux `EMFILE` (`24`). -/
def EMFILE : Std.I32 := 24#i32
/-- Linux `EPIPE` (`32`). -/
def EPIPE : Std.I32 := 32#i32
/-- Linux `ENOSYS` (`38`). -/
def ENOSYS : Std.I32 := 38#i32

/-- Clamp an oracle-supplied `errno` into Linux's kernel syscall error range `1..4095`. -/
def sanitizeErrno (e : Std.I32) : Std.I32 :=
  if 1#i32 ≤ e && e ≤ 4095#i32 then e else EIO

/-- Construct a `Std.U8` from `n mod 256`. -/
def mkU8 (n : Nat) : Std.U8 := ⟨BitVec.ofNat 8 n⟩

/-- Construct a `Std.I32` from `v` (2's-complement 32-bit). -/
def mkI32 (v : Int) : Std.I32 := ⟨BitVec.ofInt 32 v⟩

/-- Construct a `Std.Usize` from `n`. -/
def mkUsize (n : Nat) : Std.Usize := ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩

/-- Remove all entries for descriptor `fd` from `fds`. -/
def eraseFdEntries (fds : List (Int × FdEntry)) (fd : Int) : List (Int × FdEntry) :=
  fds.filter (fun p => p.1 != fd)

/-- Deduplicate `fds` preserving the first (active) entry for each descriptor number. -/
def dedupFdEntriesAux (seen : List Int) : List (Int × FdEntry) → List (Int × FdEntry)
  | [] => []
  | (fd, e) :: rest =>
    if seen.contains fd then
      dedupFdEntriesAux seen rest
    else
      (fd, e) :: dedupFdEntriesAux (fd :: seen) rest

/-- Canonicalize `fds` so each open descriptor number appears at most once. -/
def dedupFdEntries (fds : List (Int × FdEntry)) : List (Int × FdEntry) :=
  dedupFdEntriesAux [] fds

/-- Deduplicate `sigs` preserving the first (active) entry for each signal number. -/
def dedupSigEntriesAux (seen : List Int) : List (Int × Disp) → List (Int × Disp)
  | [] => []
  | (g, d) :: rest =>
    if seen.contains g then
      dedupSigEntriesAux seen rest
    else
      (g, d) :: dedupSigEntriesAux (g :: seen) rest

/-- Canonicalize `sigs` so each signal number appears at most once. -/
def dedupSigEntries (sigs : List (Int × Disp)) : List (Int × Disp) :=
  dedupSigEntriesAux [] sigs

/-- Look up descriptor `fd` in `s.fds`. -/
def ChildState.getFd (s : ChildState) (fd : Int) : Option FdEntry :=
  match s.fds.find? (fun p => p.1 == fd) with
  | some (_, e) => some e
  | none => none

/-- Return `true` iff descriptor `fd` is currently open in `s`. -/
def ChildState.isOpen (s : ChildState) (fd : Int) : Bool :=
  (s.getFd fd).isSome

/-- Remove `fd` from `s.fds`. -/
def ChildState.closeSlot (s : ChildState) (fd : Int) : ChildState :=
  { s with fds := eraseFdEntries s.fds fd }

/-- Bind `fd` to `e` in `s.fds`. -/
def ChildState.putSlot (s : ChildState) (fd : Int) (e : FdEntry) : ChildState :=
  { s with fds := (fd, e) :: eraseFdEntries s.fds fd }

/-- Look up open file description `d` in `s.descs`, defaulting to a readable+writable non-broken stream. -/
def ChildState.getDesc (s : ChildState) (d : Desc) : DescState :=
  match s.descs.find? (fun p => p.1 == d) with
  | some (_, st) => st
  | none => .stream true true false []

/-- Update open file description `d` in `s.descs`. -/
def ChildState.putDesc (s : ChildState) (d : Desc) (st : DescState) : ChildState :=
  { s with descs := (d, st) :: s.descs.filter (fun p => p.1 != d) }

/-- Look up disposition of signal `g` in `s.sig`, defaulting to `.default`. -/
def ChildState.getSig (s : ChildState) (g : Int) : Disp :=
  match s.sig.find? (fun p => p.1 == g) with
  | some (_, d) => d
  | none => .default

/-- Return `true` iff signal `g` is currently blocked in `s.blockedSigs`. -/
def ChildState.isSigBlocked (s : ChildState) (g : Int) : Bool :=
  s.blockedSigs.contains g

/-- Set disposition of signal `g` in `s.sig`. -/
def ChildState.putSig (s : ChildState) (g : Int) (d : Disp) : ChildState :=
  { s with sig := (g, d) :: s.sig.filter (fun p => p.1 != g) }

/-- Compute a fresh `Desc` identifier strictly above all existing `Desc`s in `s`. -/
def freshDescId (s : ChildState) : Desc :=
  let m1 := s.fds.foldl (fun acc p => Nat.max acc p.2.desc) 0
  let m2 := s.descs.foldl (fun acc p => Nat.max acc p.1) m1
  m2 + 1

/-- Descriptor flags word returned by `fcntl(fd, F_GETFD)` (`>= 0`, bit `0` = `FD_CLOEXEC`). -/
def fdFlagsWord (e : FdEntry) : Std.I32 :=
  let hi := mkI32 ((e.extraFdFlags.val) - (e.extraFdFlags.val % 2))
  let masked := if hi.val < 0 then 0#i32 else hi
  if e.cloexec then mkI32 (masked.val + 1) else masked

/-- Apply `fcntl(fd, F_SETFD, flags)` to `e` under `kernelMasksSetfd`. -/
def updateFdFlags (kernelMasks : Bool) (flags : Std.I32) (e : FdEntry) : FdEntry :=
  let clo := (flags &&& 1#i32) != 0#i32
  let extra :=
    if kernelMasks then 0#i32
    else
      let raw := flags &&& 2147483646#i32
      raw
  { e with cloexec := clo, extraFdFlags := extra }

/-- Structurally search `[cur, cur + fuel)` for the lowest unused descriptor in `s`. -/
def findLowestFreeFdAux (s : ChildState) (cur : Int) : Nat → Option Int
  | 0 => none
  | fuel + 1 =>
    if s.isOpen cur then
      findLowestFreeFdAux s (cur + 1) fuel
    else
      some cur

/-- Find the lowest unused 32-bit descriptor in `[minFd, min s.fdLimit 2147483648)`. -/
def findLowestFreeFd (s : ChildState) (minFd : Int) : Option Int :=
  let ceil := min s.fdLimit 2147483648
  if minFd < 0 || minFd ≥ ceil then
    none
  else
    findLowestFreeFdAux s minFd (ceil - minFd).toNat

/-- Query the fault schedule at the current `s.trace.length` step. -/
def currentFault (s : ChildState) : StepFault :=
  (s.oracle[s.trace.length]?).getD .normal

/-- Return `true` iff `sig` is rejected with `EINVAL` by glibc userspace `sigaction` before entering `SYS_rt_sigaction`. -/
def isUserspaceInvalidSigactionSig (sig : Std.I32) : Bool :=
  sig.val < 1 || sig.val > 64 || sig.val == 32 || sig.val == 33

/-- Return `true` iff `sig` is rejected with `EINVAL` by the Linux kernel in `SYS_rt_sigaction` (`SIGKILL` = 9, `SIGSTOP` = 19). -/
def isKernelInvalidSigactionSig (sig : Std.I32) : Bool :=
  sig.val == 9 || sig.val == 19

/-- Return `true` iff `sig` is rejected with `EINVAL` by Linux/glibc `sigaction` (`<= 0`, `> 64`, `9`, `19`, `32`, `33`). -/
def isInvalidSigactionSig (sig : Std.I32) : Bool :=
  isUserspaceInvalidSigactionSig sig || isKernelInvalidSigactionSig sig

private def pushPathSeg (acc : List Bytes) (seg : Bytes) : List Bytes :=
  if seg.isEmpty || seg == [46#u8] then acc
  else if seg == [46#u8, 46#u8] then acc.dropLast
  else acc ++ [seg]

private def splitSlashAux : Bytes → Bytes → List Bytes → List Bytes
  | [], cur, acc => acc ++ [cur]
  | b :: rest, cur, acc =>
    if b == 47#u8 then splitSlashAux rest [] (acc ++ [cur])
    else splitSlashAux rest (cur ++ [b]) acc

private def joinPathSegs : List Bytes → Bytes
  | [] => [47#u8]
  | segs => segs.foldl (fun acc seg => acc ++ [47#u8] ++ seg) []

/-- Update `cwd` for `chdir(path)`, lexically canonicalizing `.` / `..` / `//` / trailing `/`. -/
def chdirTarget (cwd path : Bytes) : Bytes :=
  let raw := if path.head? == some 47#u8 then path else cwd ++ [47#u8] ++ path
  joinPathSegs ((splitSlashAux raw [] []).foldl pushPathSeg [])

/-- Resolve `chdir(path)` using `s.chdirResolved` when present, falling back to `chdirTarget s.cwd path`. -/
def resolveChdirTarget (s : ChildState) (path : Bytes) : Bytes :=
  match s.chdirResolved.find? (fun p => p.1 == path) with
  | some (_, resolved) => resolved
  | none => chdirTarget s.cwd path

/-- Filter and canonicalize surviving non-`FD_CLOEXEC` descriptors across `execve`. -/
def afterExecFds (fds : List (Int × FdEntry)) : List (Int × FdEntry) :=
  (dedupFdEntries fds).filter (fun p => !p.2.cloexec)

/-- Linux `7.1` `fs/exec.c` substitutes `[""]` (`argc = 1`, `argv[0] = ""`) when `execve` receives an empty `argv = []`. -/
def effectiveExecArgv (argv : List Bytes) : List Bytes :=
  if argv.isEmpty then [[]] else argv

/-- Reset caught signal handlers (`.handler -> .default`) while preserving `.ignore` across `execve`. -/
def afterExecSigs (sigs : List (Int × Disp)) : List (Int × Disp) :=
  (dedupSigEntries sigs).filterMap fun (g, d) =>
    match d with
    | .ignore => some (g, .ignore)
    | .default | .handler => none

/-- Construct the `ExecImage` produced by a successful `execve`. -/
def imageOf (s : ChildState) (path : Bytes) (argv envp : List Bytes) : ExecImage :=
  { path := path
    argv := effectiveExecArgv argv
    envp := envp
    fds := afterExecFds s.fds
    cwd := s.cwd
    pgid := s.pgid
    sig := afterExecSigs s.sig
    blockedSigs := s.blockedSigs }

/-- Execute a unit-returning syscall (`Result<(), i32>`) with seccomp pre-entry interception before kernel checks. -/
def runUnitSyscall
    (s : ChildState)
    (req : Req)
    (forcedErr? : Option Std.I32)
    (onOk : ChildState → ChildState)
    (onErr : ChildState → ChildState := id) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let e := sanitizeErrno rawE
      ok (.Err e, { s with trace := s.trace ++ [⟨req, .err e⟩] })
    | fault =>
      match forcedErr? with
      | some e =>
        let s' := onErr s
        ok (.Err e, { s' with trace := s'.trace ++ [⟨req, .err e⟩] })
      | none =>
        match fault with
        | .fail rawE =>
          let e := sanitizeErrno rawE
          let s' := onErr s
          ok (.Err e, { s' with trace := s'.trace ++ [⟨req, .err e⟩] })
        | .normal | .seccomp _ | .partialWrite _ | .dentsBatch _ =>
          let s' := onOk s
          ok (.Ok (), { s' with trace := s'.trace ++ [⟨req, .okVal 0⟩] })
  | _ => ok (.Ok (), s)

/-- Execute an `i32`-returning syscall (`Result<i32, i32>`) with seccomp pre-entry interception before kernel checks. -/
def runI32Syscall
    (s : ChildState)
    (req : Req)
    (forcedErr? : Option Std.I32)
    (onOk : ChildState → Std.I32 × ChildState) :
    Result ((core.result.Result Std.I32 Std.I32) × ChildState) :=
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let e := sanitizeErrno rawE
      ok (.Err e, { s with trace := s.trace ++ [⟨req, .err e⟩] })
    | fault =>
      match forcedErr? with
      | some e =>
        ok (.Err e, { s with trace := s.trace ++ [⟨req, .err e⟩] })
      | none =>
        match fault with
        | .fail rawE =>
          let e := sanitizeErrno rawE
          ok (.Err e, { s with trace := s.trace ++ [⟨req, .err e⟩] })
        | .normal | .seccomp _ | .partialWrite _ | .dentsBatch _ =>
          let (v, s') := onOk s
          ok (.Ok v, { s' with trace := s'.trace ++ [⟨req, .okVal v.val⟩] })
  | _ => ok (.Ok 0#i32, s)

/-- Bounded base-10 ASCII formatter helper (`fuel = 12` covers all 32-bit `Nat` values `< 10^12`). -/
def natDigitsFuel : Nat → Nat → Bytes → Bytes
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := mkU8 (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc else natDigitsFuel fuel q (d :: acc)

/-- Render `n` as canonical non-empty ASCII decimal bytes. -/
def natToAsciiBytes (n : Nat) : Bytes :=
  natDigitsFuel 12 n []

/-- Insert `x` into ascending list `xs` without duplicates. -/
def insertSortedInt (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if x < y then x :: y :: ys
    else y :: insertSortedInt x ys

/-- Collect sorted open non-negative 32-bit descriptor numbers in `s.fds`. -/
def sortedOpenFds32 (s : ChildState) : List Int :=
  s.fds.foldl
    (fun acc p =>
      if 0 ≤ p.1 && p.1 ≤ 2147483647 then insertSortedInt p.1 acc else acc)
    []

/-- Encode a 64-bit little-endian unsigned value as 8 `Std.U8` bytes. -/
def encodeU64Le (v : Nat) : Bytes :=
  [ mkU8 (v % 256)
  , mkU8 ((v / 256) % 256)
  , mkU8 ((v / 65536) % 256)
  , mkU8 ((v / 16777216) % 256)
  , mkU8 ((v / 4294967296) % 256)
  , mkU8 ((v / 1099511627776) % 256)
  , mkU8 ((v / 281474976710656) % 256)
  , mkU8 ((v / 72057594037927936) % 256) ]

/-- Encode one 8-byte-aligned Linux `struct linux_dirent64` record (`d_ino`, `d_off`, `d_reclen`, `d_type`, `d_name\0`). -/
def encodeDirent64 (ino : Nat) (nextOff : Nat) (dtype : Std.U8) (nm : Bytes) : Bytes :=
  let rawLen := 20 + nm.length
  let reclen := ((rawLen + 7) / 8) * 8
  let padLen := reclen - 19 - nm.length
  encodeU64Le ino ++
  encodeU64Le nextOff ++
  [mkU8 (reclen % 256), mkU8 ((reclen / 256) % 256), dtype] ++
  nm ++
  List.replicate padLen 0#u8

/-- Enumerate `/proc/self/fd` entries `(cursorKey, nameBytes)` at or after `cursor`. -/
def procSelfFdEntriesFrom (s : ChildState) (cursor : Int) : List (Int × Bytes) :=
  let base : List (Int × Bytes) := [(-2, [46#u8]), (-1, [46#u8, 46#u8])]
  let fdItems : List (Int × Bytes) :=
    (sortedOpenFds32 s).map (fun fd => (fd, natToAsciiBytes fd.toNat))
  (base ++ fdItems).filter (fun p => decide (cursor ≤ p.1))

/-- Maximum non-negative 32-bit open descriptor number in `s.fds` (`0` if none). -/
def ChildState.maxOpenFd32 (s : ChildState) : Int :=
  s.fds.foldl (fun acc p => if 0 ≤ p.1 && p.1 ≤ 2147483647 then max acc p.1 else acc) 0

/-- Terminal `f_pos` cursor emitted at `/proc/self/fd` EOF (`min 2147483648 (max procMaxFds (maxOpenFd32 + 1))`). -/
def procEofCursor (s : ChildState) : Int :=
  min 2147483648 (max (Int.ofNat s.procMaxFds) (s.maxOpenFd32 + 1))

/-- Greedily pack up to `maxEntries` `linux_dirent64` records fitting in `256` bytes, returning the next cursor matching Linux `proc_readfd_common`. -/
def packProcDirents (eofCur : Int) : List (Int × Bytes) → Nat → Bytes → Option Int → Bytes × Option Int
  | [], _, acc, next? => (acc, next?)
  | _, 0, acc, next? => (acc, next?)
  | (key, nm) :: rest, cap + 1, acc, next? =>
    let dtype : Std.U8 := if key < 0 then 4#u8 else 10#u8
    let nextCur : Int := match rest with
      | (nextKey, _) :: _ => nextKey
      | [] => eofCur
    let recBytes := encodeDirent64 (key + 3).toNat (nextCur + 2).toNat dtype nm
    if acc.length + recBytes.length > 256 then
      (acc, next?)
    else
      packProcDirents eofCur rest cap (acc ++ recBytes) (some nextCur)

/-- Greedily pack up to `maxEntries` `.` / `..` records for a generic directory descriptor. -/
def packDirDotEntries : List (Int × Bytes) → Nat → Bytes → Option Int → Bytes × Option Int
  | [], _, acc, next? => (acc, next?)
  | _, 0, acc, next? => (acc, next?)
  | (key, nm) :: rest, cap + 1, acc, _ =>
    let nextCur : Int := key + 1
    let recBytes := encodeDirent64 (key + 1).toNat nextCur.toNat 4#u8 nm
    packDirDotEntries rest cap (acc ++ recBytes) (some nextCur)

/-- Write `payload` (`<= 256` bytes) into the prefix of `orig`, preserving trailing bytes so total length is `256`. -/
def overlayBuf256 (payload : Bytes) (orig : Array Std.U8 256#usize) : Array Std.U8 256#usize :=
  let pfx := payload.take 256
  let merged := pfx ++ orig.val.drop pfx.length
  have hOrig : orig.val.length = (256#usize).val := orig.property
  have hVal256 : (256#usize).val = 256 := by decide
  have hPfxLe : pfx.length ≤ orig.val.length := by
    rw [hOrig, hVal256]
    exact List.length_take_le 256 payload
  have hLen : merged.length = (256#usize).val := by
    simp only [merged, List.length_append, List.length_drop]
    omega
  Array.from merged hLen


end LeanSwe.PostFork.Aeneas.Internal.World
