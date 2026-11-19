import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import LeanSwe.PostFork.Aeneas.Funs
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Interface
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Types

/-!
Differential fuzzer suite `Fuzz.PostFork.suite` comparing `LeanSwe.PostFork.Model`,
Aeneas-generated `postfork.child.run_child` / `postfork.fd_ops.close_fds_above2_except`,
and the public `LeanSwe.PostFork` host API (`spawn`, `spawnWithBarrier`, `releaseBarrier`,
`abortBarrier`, `ArgToken`, `ForkMode`) against live Linux execution of `libpostfork.a`.
-/

namespace Fuzz.PostFork

open Aeneas Aeneas.Std
open Fuzz.Common
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Aeneas.Model

@[extern "leanswe_pf_pipe2"]
private opaque cPipe2 (cloexec : UInt32) : IO (Except UInt32 (Int32 × Int32))

@[extern "leanswe_pf_memfd"]
private opaque cMemfd (cloexec : UInt32) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_dup_from"]
private opaque cDupFrom (oldfd minfd cloexec : UInt32) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_fcntl_getfd"]
private opaque cFcntlGetfd (fd : UInt32) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_fcntl_setfd"]
private opaque cFcntlSetfd (fd fl : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_fstat_dev_ino"]
private opaque cFstatDevIno (fd : UInt32) : IO (Except UInt32 (UInt64 × UInt64))

@[extern "leanswe_pf_close"]
private opaque cClose (fd : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_read_once"]
private opaque cReadOnce (fd : UInt32) (maxBytes : UInt64) : IO (Except UInt32 ByteArray)

@[extern "leanswe_pf_write_once"]
private opaque cWriteOnce (fd : UInt32) (ba : @& ByteArray) (off len : UInt64) : IO (Except UInt32 UInt64)

@[extern "leanswe_pf_rawfd_num"]
private opaque cRawFdNum (h : @& RawFd) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_rawfd_fstat_dev_ino"]
private opaque cRawFdFstatDevIno (h : @& RawFd) : IO (Except UInt32 (UInt64 × UInt64))

@[extern "leanswe_pf_rawfd_setfd"]
private opaque cRawFdSetfd (h : @& RawFd) (fl : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_getpid_sid"]
private opaque cGetPidSid : IO (Int32 × Int32)

@[extern "leanswe_pf_getpgrp"]
private opaque cGetpgrp : IO Int32

@[extern "leanswe_pf_symlink"]
private opaque cSymlink (target linkpath : @& String) : IO UInt32

@[extern "leanswe_pf_chmod"]
private opaque cChmod (path : @& String) (mode : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_mkdir"]
private opaque cMkdir (path : @& String) (mode : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_rmdir_unlink"]
private opaque cRmdirUnlink (path : @& String) (isDir : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_create_file"]
private opaque cCreateFile (path : @& String) (data : @& ByteArray) (mode : UInt32) : IO (Except UInt32 Unit)

@[extern "leanswe_pf_seccomp_const"]
private opaque cSeccompConst (idx : UInt32) : UInt32

@[extern "leanswe_pf_realpath"]
private opaque cRealpath (path : @& String) : IO (Except UInt32 String)

@[extern "leanswe_pf_fork_run"]
private opaque cForkRun
    (cfgBlob closeBlob keepBlob bpfBlob : @& ByteArray)
    (cwd? : @& Option String)
    (path : @& String)
    (argv envp : @& Array String) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_abi_guard_fork"]
private opaque cAbiGuardFork (kind repW flags : UInt32) : IO (Except UInt32 Int32)

@[extern "leanswe_pf_get_rlim_nofile"]
private opaque cGetRlimNofile : IO UInt64

@[extern "leanswe_pf_geteuid"]
private opaque cGeteuid : IO UInt32

@[extern "leanswe_pf_sigpipe_write_fork"]
private opaque cSigpipeWriteFork (pidns sigMode blockSp : UInt32) : IO (Except UInt32 Int32)

@[extern "leanswe_postfork_host_pipe_cloexec"]
private opaque cHostPipeCloexec : BaseIO (Except Errno (RawFd × RawFd))

@[extern "leanswe_postfork_host_close_fd"]
private opaque cHostCloseFd : @& RawFd → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_read_once"]
private opaque cHostReadOnce : @& RawFd → UInt64 → BaseIO (Except Errno ByteArray)

@[extern "leanswe_postfork_host_write_once"]
private opaque cHostWriteOnce : @& RawFd → @& ByteArray → UInt64 → UInt64 → BaseIO (Except Errno UInt64)

@[extern "leanswe_postfork_host_wait_once"]
private opaque cHostWaitOnce : Pid → BaseIO (Except Errno ChildWaitStatus)

@[extern "leanswe_pf_sigpipe_disp"]
private opaque cGetSigpipeDisp : IO Int32

@[extern "leanswe_pf_sigmask_usr1"]
private opaque cSigmaskUsr1 (block : UInt32) : IO (Except UInt32 Unit)

private structure ProbeDump where
  pgid : Int32
  sigPipeDisp : Int32
  sigUsr1Disp : Int32
  sigUsr2Disp : Int32
  sigBlkBits : UInt32
  cwd : String
  argv : Array String
  envp : Array String
  stdinBytes : ByteArray
  openFds : Array (Int32 × UInt32 × UInt64 × UInt64)

private def pushU16Le (ba : ByteArray) (v : UInt16) : ByteArray :=
  ba.push (UInt8.ofNat (v.toNat &&& 0xff)) |>.push (UInt8.ofNat ((v.toNat >>> 8) &&& 0xff))

private def pushU32Le (ba : ByteArray) (v : UInt32) : ByteArray :=
  let n := v.toNat
  ba
    |>.push (UInt8.ofNat (n &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 8) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 16) &&& 0xff))
    |>.push (UInt8.ofNat ((n >>> 24) &&& 0xff))

private def pushI32Le (ba : ByteArray) (v : Int32) : ByteArray :=
  pushU32Le ba v.toUInt32

private def encodeI32ArrayLe (xs : Array Int32) : ByteArray :=
  xs.foldl pushI32Le ByteArray.empty

private def pushInsn (ba : ByteArray) (code : UInt16) (jt jtF : UInt8) (k : UInt32) : ByteArray :=
  pushU16Le ba code |>.push jt |>.push jtF |> fun b => pushU32Le b k

private def buildSeccompRetErrnoBpf (nr : UInt32) (err : UInt32) : ByteArray :=
  let ldArch : UInt16 := 0x20
  let ldNr : UInt16 := 0x20
  let jmpEq : UInt16 := 0x15
  let jmpSet : UInt16 := 0x45
  let ret : UInt16 := 0x06
  let retAllow : UInt32 := 0x7fff0000
  let retErrno : UInt32 := 0x00050000 ||| (err &&& 0xffff)
  let retEnosys : UInt32 := 0x00050000 ||| (38 &&& 0xffff)
  let retKill : UInt32 := 0x00000000
  let auditArch : UInt32 := cSeccompConst 0
  let closeNr : UInt32 := cSeccompConst 3
  let getdents64Nr : UInt32 := cSeccompConst 10
  let openatNr : UInt32 := cSeccompConst 11
  let closeRangeNr : UInt32 := cSeccompConst 12
  let rtSigprocmaskNr : UInt32 := cSeccompConst 16
  let sigUnblockHow : UInt32 := cSeccompConst 17
  let base := ByteArray.empty
    |> fun b => pushInsn b ldArch 0 0 4
    |> fun b => pushInsn b jmpEq 1 0 auditArch
    |> fun b => pushInsn b ret 0 0 retKill
    |> fun b => pushInsn b ldNr 0 0 0
  if nr == openatNr then
    base
      |> fun b => pushInsn b jmpEq 4 0 closeRangeNr
      |> fun b => pushInsn b jmpEq 0 4 nr
      |> fun b => pushInsn b ldNr 0 0 32
      |> fun b => pushInsn b jmpSet 0 2 (cSeccompConst 14)
      |> fun b => pushInsn b ret 0 0 retErrno
      |> fun b => pushInsn b ret 0 0 retEnosys
      |> fun b => pushInsn b ret 0 0 retAllow
  else if nr == getdents64Nr then
    base
      |> fun b => pushInsn b jmpEq 2 0 closeRangeNr
      |> fun b => pushInsn b jmpEq 0 2 nr
      |> fun b => pushInsn b ret 0 0 retErrno
      |> fun b => pushInsn b ret 0 0 retEnosys
      |> fun b => pushInsn b ret 0 0 retAllow
  else if nr == closeNr then
    base
      |> fun b => pushInsn b jmpEq 2 0 closeRangeNr
      |> fun b => pushInsn b jmpEq 0 4 nr
      |> fun b => pushInsn b ret 0 0 retErrno
      |> fun b => pushInsn b ldNr 0 0 16
      |> fun b => pushInsn b jmpEq 1 0 0
      |> fun b => pushInsn b ret 0 0 retEnosys
      |> fun b => pushInsn b ret 0 0 retAllow
  else if nr == rtSigprocmaskNr then
    base
      |> fun b => pushInsn b jmpEq 0 3 nr
      |> fun b => pushInsn b ldNr 0 0 16
      |> fun b => pushInsn b jmpEq 0 1 sigUnblockHow
      |> fun b => pushInsn b ret 0 0 retErrno
      |> fun b => pushInsn b ret 0 0 retAllow
  else
    base
      |> fun b => pushInsn b jmpEq 0 1 nr
      |> fun b => pushInsn b ret 0 0 retErrno
      |> fun b => pushInsn b ret 0 0 retAllow

private def readU32LeAt? (ba : ByteArray) (off : Nat) : Option (UInt32 × Nat) :=
  if off + 4 > ba.size then none
  else
    let b0 := ba.get! off |>.toNat
    let b1 := ba.get! (off + 1) |>.toNat
    let b2 := ba.get! (off + 2) |>.toNat
    let b3 := ba.get! (off + 3) |>.toNat
    let v := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    some (UInt32.ofNat v, off + 4)

private def readU64LeAt? (ba : ByteArray) (off : Nat) : Option (UInt64 × Nat) :=
  if off + 8 > ba.size then none
  else Id.run do
    let mut acc : Nat := 0
    for i in List.range 8 do
      acc := acc ||| ((ba.get! (off + i)).toNat <<< (8 * i))
    return some (UInt64.ofNat acc, off + 8)

private def readStrAt? (ba : ByteArray) (off : Nat) : Option (String × Nat) := do
  let (n, off1) ← readU32LeAt? ba off
  let len := n.toNat
  if off1 + len > ba.size then none
  let slice := ba.extract off1 (off1 + len)
  return (String.fromUTF8! slice, off1 + len)

private def readStrVecAt? (ba : ByteArray) (off : Nat) : Option (Array String × Nat) := do
  let (cnt, cur0) ← readU32LeAt? ba off
  let mut cur := cur0
  let mut out := Array.mkEmpty cnt.toNat
  for _ in List.range cnt.toNat do
    let (s, nextCur) ← readStrAt? ba cur
    out := out.push s
    cur := nextCur
  return (out, cur)

private def parseProbeDump? (ba : ByteArray) : Option ProbeDump := do
  let (magic, off1) ← readU32LeAt? ba 0
  if magic != 0x50465052 then none
  let (pgidU, off2) ← readU32LeAt? ba off1
  let (sp, off3) ← readU32LeAt? ba off2
  let (su1, off4) ← readU32LeAt? ba off3
  let (su2, off5) ← readU32LeAt? ba off4
  let (sigBlk, off5b) ← readU32LeAt? ba off5
  let (cwd, off6) ← readStrAt? ba off5b
  let (argv, off7) ← readStrVecAt? ba off6
  let (envp, off8) ← readStrVecAt? ba off7
  let (stLen, off9) ← readU32LeAt? ba off8
  if off9 + stLen.toNat > ba.size then none
  let stdinBytes := ba.extract off9 (off9 + stLen.toNat)
  let mut cur := off9 + stLen.toNat
  let (fdCnt, cur0) ← readU32LeAt? ba cur
  cur := cur0
  let mut fds := Array.mkEmpty fdCnt.toNat
  for _ in List.range fdCnt.toNat do
    let (fdU, c1) ← readU32LeAt? ba cur
    let (flU, c2) ← readU32LeAt? ba c1
    let (dev, c3) ← readU64LeAt? ba c2
    let (ino, c4) ← readU64LeAt? ba c3
    fds := fds.push (Int32.ofInt (Int.ofNat fdU.toNat), flU, dev, ino)
    cur := c4
  return {
    pgid := Int32.ofInt (Int.ofNat pgidU.toNat)
    sigPipeDisp := Int32.ofInt (Int.ofNat sp.toNat)
    sigUsr1Disp := Int32.ofInt (Int.ofNat su1.toNat)
    sigUsr2Disp := Int32.ofInt (Int.ofNat su2.toNat)
    sigBlkBits := sigBlk
    cwd := cwd
    argv := argv
    envp := envp
    stdinBytes := stdinBytes
    openFds := fds
  }

private def bytesOfString (s : String) : Bytes :=
  s.toUTF8.toList.map (fun b => (⟨BitVec.ofNat 8 b.toNat⟩ : Std.U8))

private def byteArrayOfBytes (bs : Bytes) : ByteArray :=
  ByteArray.mk (bs.map (fun b => UInt8.ofNat b.val)).toArray

private def strOfBytes (bs : Bytes) : String :=
  String.fromUTF8! (byteArrayOfBytes bs)

private def i32ArrToSlice (xs : Array Int32) : Slice Std.I32 :=
  let l := xs.toList.map (fun x => mkI32 x.toInt)
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (Nat.zero_le _)

private def strToCStr (s : String) : sys.CStr :=
  bytesOfString s

private def strArrToCStrArray (xs : Array String) : sys.CStrArray :=
  xs.toList.map strToCStr

private def readAllFd (fd : Int32) : IO ByteArray := do
  let mut acc := ByteArray.empty
  for _ in List.range 4096 do
    match ← cReadOnce fd.toUInt32 4096 with
    | .ok chunk =>
      if chunk.size == 0 then
        return acc
      acc := appendBytes acc chunk
    | .error e =>
      if e != 4 then
        throw (IO.userError s!"readAllFd(fd={fd}) failed: errno={e}")
  throw (IO.userError s!"readAllFd(fd={fd}) exceeded read loop limit")

private def writeAllFd (fd : Int32) (data : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  for _ in List.range 4096 do
    if off ≥ data.size then
      return
    match ← cWriteOnce fd.toUInt32 data off.toUInt64 (data.size - off).toUInt64 with
    | .ok n =>
      if n.toNat == 0 then
        throw (IO.userError s!"writeAllFd(fd={fd}) returned 0 bytes")
      off := off + n.toNat
    | .error e =>
      if e != 4 then
        throw (IO.userError s!"writeAllFd(fd={fd}) failed: errno={e}")
  if off < data.size then
    throw (IO.userError s!"writeAllFd(fd={fd}) exceeded write loop limit")

private def readAllHandle (h : RawFd) : IO ByteArray := do
  let mut acc := ByteArray.empty
  for _ in List.range 4096 do
    match ← cHostReadOnce h 4096 with
    | .ok chunk =>
      if chunk.size == 0 then
        return acc
      acc := appendBytes acc chunk
    | .error e =>
      if e != 4 then
        throw (IO.userError s!"readAllHandle failed: errno={e}")
  throw (IO.userError "readAllHandle exceeded read loop limit")

private def writeAllHandle (h : RawFd) (data : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  for _ in List.range 4096 do
    if off ≥ data.size then
      return
    match ← cHostWriteOnce h data off.toUInt64 (data.size - off).toUInt64 with
    | .ok n =>
      if n.toNat == 0 then
        throw (IO.userError "writeAllHandle returned 0 bytes")
      off := off + n.toNat
    | .error e =>
      if e != 4 then
        throw (IO.userError s!"writeAllHandle failed: errno={e}")
  if off < data.size then
    throw (IO.userError "writeAllHandle exceeded write loop limit")

private def closeIgnore (fd : Int32) : IO Unit := do
  if fd ≥ 0 then
    let _ ← cClose fd.toUInt32

private def closeHandleIgnore (h : RawFd) : IO Unit := do
  let _ ← cHostCloseFd h

private def findProbeBin : IO String := do
  let appDir := (← IO.appPath).parent
  let candidate : String := match appDir with
    | some d => (d / "leanswe-postfork-probe").toString
    | none => ".lake/build/bin/leanswe-postfork-probe"
  let raw := if ← System.FilePath.pathExists ⟨candidate⟩ then candidate else ".lake/build/bin/leanswe-postfork-probe"
  return (← IO.FS.realPath ⟨raw⟩).toString

private structure FuzzScratch where
  initCwd : String
  root : String
  probeBin : String
  validDir : String
  symDir : String
  realParent : String
  realSub : String
  symNested : String
  symNestedDotDot : String
  trailingSlashDir : String
  dotSlashDir : String
  symDirResolved : String
  symNestedDotDotResolved : String
  cwdResolved : List (sys.CStr × sys.CStr)
  probeOut : String
  missingPath : String
  fileNotDir : String
  chmod0Dir : String
  nonExecFile : String
  badExecFile : String
  eloopA : String
  eloopB : String
  longPath : String

private def initScratch (seed : UInt64) : IO FuzzScratch := do
  let initCwd := (← IO.currentDir).toString
  let (pid, _) ← cGetPidSid
  let root := s!"/tmp/leanswe-pf-fuzz-{pid}-{seed}"
  let _ ← cMkdir root 0o755
  let validDir := s!"{root}/cwd_ok"
  let symDir := s!"{root}/cwd_sym"
  let realParent := s!"{root}/real_parent"
  let realSub := s!"{root}/real_parent/sub"
  let symNested := s!"{root}/cwd_nested"
  let symNestedDotDot := s!"{root}/cwd_nested/.."
  let trailingSlashDir := s!"{validDir}/"
  let dotSlashDir := s!"{validDir}//./."
  let chmod0Dir := s!"{root}/cwd_noaccess"
  let fileNotDir := s!"{root}/not_a_dir"
  let nonExecFile := s!"{root}/nonexec"
  let badExecFile := s!"{root}/badexec"
  let eloopA := s!"{root}/eloopA"
  let eloopB := s!"{root}/eloopB"
  let longPath := Id.run do
    let mut acc := s!"{root}/"
    for _ in List.range 4200 do
      acc := acc.push 'a'
    return acc
  let _ ← cMkdir validDir 0o755
  let _ ← cMkdir realParent 0o755
  let _ ← cMkdir realSub 0o755
  let _ ← cSymlink validDir symDir
  let _ ← cSymlink realSub symNested
  let _ ← cMkdir chmod0Dir 0o755
  let _ ← cCreateFile fileNotDir ByteArray.empty 0o644
  let _ ← cCreateFile nonExecFile ("echo hi\n".toUTF8) 0o644
  let _ ← cCreateFile badExecFile (ByteArray.mk #[0x7f, 0x01, 0x02, 0x03, 0x04]) 0o755
  let _ ← cSymlink "eloopB" eloopA
  let _ ← cSymlink "eloopA" eloopB
  let _ ← cChmod chmod0Dir 0o000
  let resolveStr (raw : String) : IO String := do
    match ← cRealpath raw with
    | .ok p => return p
    | .error e => throw (IO.userError s!"realpath({raw}) failed: errno={e}")
  let validDirResolved ← resolveStr validDir
  let symDirResolved ← resolveStr symDir
  let symNestedDotDotResolved ← resolveStr symNestedDotDot
  let trailingResolved ← resolveStr trailingSlashDir
  let dotSlashResolved ← resolveStr dotSlashDir
  let dotResolved ← resolveStr "."
  let dotDotResolved ← resolveStr ".."
  let cwdResolved : List (sys.CStr × sys.CStr) :=
    [ (strToCStr validDir, strToCStr validDirResolved)
    , (strToCStr symDir, strToCStr symDirResolved)
    , (strToCStr symNestedDotDot, strToCStr symNestedDotDotResolved)
    , (strToCStr trailingSlashDir, strToCStr trailingResolved)
    , (strToCStr dotSlashDir, strToCStr dotSlashResolved)
    , (strToCStr ".", strToCStr dotResolved)
    , (strToCStr "..", strToCStr dotDotResolved)
    ]
  let probeBin ← findProbeBin
  return {
    initCwd
    root
    probeBin
    validDir
    symDir
    realParent
    realSub
    symNested
    symNestedDotDot
    trailingSlashDir
    dotSlashDir
    symDirResolved
    symNestedDotDotResolved
    cwdResolved
    probeOut := s!"{root}/probe.bin"
    missingPath := s!"{root}/no_such_entry"
    fileNotDir
    chmod0Dir
    nonExecFile
    badExecFile
    eloopA
    eloopB
    longPath
  }

private def cleanupScratch (sc : FuzzScratch) : IO Unit := do
  let _ ← cChmod sc.chmod0Dir 0o755
  let _ ← cRmdirUnlink sc.probeOut 0
  let _ ← cRmdirUnlink sc.symNested 0
  let _ ← cRmdirUnlink sc.symDir 0
  let _ ← cRmdirUnlink sc.realSub 1
  let _ ← cRmdirUnlink sc.realParent 1
  let _ ← cRmdirUnlink sc.eloopA 0
  let _ ← cRmdirUnlink sc.eloopB 0
  let _ ← cRmdirUnlink sc.nonExecFile 0
  let _ ← cRmdirUnlink sc.badExecFile 0
  let _ ← cRmdirUnlink sc.fileNotDir 0
  let _ ← cRmdirUnlink sc.chmod0Dir 1
  let _ ← cRmdirUnlink sc.validDir 1
  let _ ← cRmdirUnlink sc.root 1

private inductive SeccompTarget
  | none
  | read
  | write
  | close
  | sigaction
  | rtSigprocmask
  | dup2
  | execve
  | fcntl
  | chdir
  | setpgid
  | getdents64
  | openat
  | closeRange
  deriving BEq, Repr, Inhabited

private def allSeccompTargets : Array SeccompTarget := #[
  .read, .write, .close, .sigaction, .rtSigprocmask, .dup2, .execve,
  .fcntl, .chdir, .setpgid, .getdents64, .openat, .closeRange
]

private def seccompTargetNr : SeccompTarget → UInt32
  | .none => 0xffffffff
  | .read => cSeccompConst 1
  | .write => cSeccompConst 2
  | .close => cSeccompConst 3
  | .sigaction => cSeccompConst 4
  | .rtSigprocmask => cSeccompConst 16
  | .dup2 => cSeccompConst 5
  | .execve => cSeccompConst 6
  | .fcntl => cSeccompConst 7
  | .chdir => cSeccompConst 8
  | .setpgid => cSeccompConst 9
  | .getdents64 => cSeccompConst 10
  | .openat => cSeccompConst 11
  | .closeRange => cSeccompConst 12

private def seccompFaultForReq (tgt : SeccompTarget) (secErr : Std.I32) (req : Req) : Option Std.I32 :=
  match tgt, req with
  | .read, .read1 _ => some secErr
  | .write, .write _ _ => some secErr
  | .close, .closeRange .. => some ENOSYS
  | .close, .close _ => some secErr
  | .sigaction, .sigDfl _ | .sigaction, .sigIgn _ => some secErr
  | .rtSigprocmask, .sigUnblock _ => some secErr
  | .dup2, .dup2 oldfd newfd => if cSeccompConst 15 == 0 || oldfd != newfd then some secErr else none
  | .execve, .execve .. => some secErr
  | .fcntl, .fcntlGetfd _ | .fcntl, .fcntlSetfd _ _ | .fcntl, .fcntlDupfdCloexec _ _ => some secErr
  | .fcntl, .dup2 oldfd newfd => if cSeccompConst 15 != 0 && oldfd == newfd then some secErr else none
  | .chdir, .chdir _ => some secErr
  | .setpgid, .setpgidSelf => some secErr
  | .getdents64, .closeRange .. => some ENOSYS
  | .getdents64, .getdents64 _ => some secErr
  | .openat, .closeRange .. => some ENOSYS
  | .openat, .openProcSelfFd => some secErr
  | .closeRange, .closeRange .. => some secErr
  | _, _ => none

private structure DescTrack where
  descId : Desc
  dev : UInt64
  ino : UInt64
  stdinPayload : ByteArray

private def sigDispToModel : Nat → Disp
  | 1 => .ignore
  | 2 => .handler
  | _ => .default

private def modelDispToCode : Disp → Int32
  | .default => 0
  | .ignore => 1
  | .handler => 2

private def runWithSeccompFixedPoint {α : Type}
    (sBase : ChildState) (tgt : SeccompTarget) (errVal : Std.I32)
    (cwdErr? execErr? : Option Std.I32)
    (fn : ChildState → Result α) (extractTrace : α → List Event) :
    Except String α := Id.run do
  if tgt == .none && cwdErr?.isNone && execErr?.isNone then
    match Result.match (fn sBase) with
    | .ok a => return .ok a
    | _ => return .error "Aeneas model returned fail/div with oracle=[]"
  let mut oracle : List StepFault := []
  for _ in List.range 32 do
    let sRun := { sBase with oracle := oracle }
    match Result.match (fn sRun) with
    | .ok a =>
      let tr := extractTrace a
      let mut changed := false
      let mut nextOracle := oracle
      while nextOracle.length < tr.length do
        nextOracle := nextOracle.concat .normal
      for idx in List.range tr.length do
        match tr[idx]? with
        | some ev =>
          let wanted? : Option StepFault :=
            match seccompFaultForReq tgt errVal ev.req with
            | some se => some (StepFault.seccomp se)
            | none =>
              match ev.req, cwdErr?, execErr? with
              | .chdir _, some e, _ => some (StepFault.fail e)
              | .execve .., _, some e => some (StepFault.fail e)
              | _, _, _ => none
          match wanted? with
          | some wanted =>
            if nextOracle[idx]? != some wanted then
              nextOracle := nextOracle.set idx wanted
              changed := true
              break
          | none => pure ()
        | none => pure ()
      if !changed then
        return .ok a
      oracle := nextOracle
    | _ => return .error "Aeneas model returned fail/div under seccomp fixed point"
  return .error "Seccomp fixed-point did not converge"

private def ENAMETOOLONG_I32 : Std.I32 := 36#i32
private def ELOOP_I32 : Std.I32 := 40#i32
private def ENOEXEC_I32 : Std.I32 := 8#i32

private def pickCwdAndErrno (rng : Rng) (sc : FuzzScratch) (isUserNs : Bool) :
    (Option String × Option Std.I32) × Rng :=
  let (tag, r1) := rng.nextNat 14
  match tag with
  | 0 => ((none, none), r1)
  | 1 => ((some sc.validDir, none), r1)
  | 2 => ((some sc.symDir, none), r1)
  | 3 => ((some sc.symNestedDotDot, none), r1)
  | 4 => ((some sc.trailingSlashDir, none), r1)
  | 5 => ((some sc.dotSlashDir, none), r1)
  | 6 => ((some ".", none), r1)
  | 7 => ((some "..", none), r1)
  | 8 => ((some "", some ENOENT), r1)
  | 9 => ((some sc.missingPath, some ENOENT), r1)
  | 10 => ((some sc.fileNotDir, some ENOTDIR), r1)
  | 11 =>
    if isUserNs then ((some sc.missingPath, some ENOENT), r1)
    else ((some sc.chmod0Dir, some EACCES), r1)
  | 12 => ((some sc.eloopA, some ELOOP_I32), r1)
  | _ => ((some sc.longPath, some ENAMETOOLONG_I32), r1)

private def pickPathAndErrno (rng : Rng) (sc : FuzzScratch) (isUserNs : Bool) :
    (String × Option Std.I32) × Rng :=
  let (tag, r1) := rng.nextNat 8
  match tag with
  | 0 | 1 | 2 => ((sc.probeBin, none), r1)
  | 3 => ((sc.missingPath, some ENOENT), r1)
  | 4 =>
    if isUserNs then ((sc.badExecFile, some ENOEXEC_I32), r1)
    else ((sc.nonExecFile, some EACCES), r1)
  | 5 => ((sc.badExecFile, some ENOEXEC_I32), r1)
  | 6 => ((sc.eloopA, some ELOOP_I32), r1)
  | _ => ((sc.longPath, some ENAMETOOLONG_I32), r1)

private def pickArgv (rng : Rng) (probeBin : String) : Array String × Rng :=
  let (tag, r1) := rng.nextNat 4
  match tag with
  | 0 => (#[], r1)
  | 1 => (#[probeBin], r1)
  | 2 => (#[probeBin, "arg1", "arg 2"], r1)
  | _ => (#["custom0", "", "z"], r1)

private def pickEnvp (rng : Rng) (probeOut : String) (includeProbe : Bool) : Array String × Rng :=
  let (tag, r1) := rng.nextNat 3
  let base := match tag with
    | 0 => #[]
    | 1 => #["PF_KEY=val1"]
    | _ => #["PF_A=1", "PF_EMPTY="]
  if includeProbe then (#[s!"_PF_PROBE_OUT={probeOut}"] ++ base, r1)
  else (base, r1)

private def compareExecImage
    (step : Nat) (kind : String)
    (usePidNs expectSigpipeBlocked sigactionBlocked : Bool) (modelPid : Int) (childPid parentPgrp : Int32)
    (img : ExecImage) (sExp : ChildState) (dump : ProbeDump)
    (descMap : List DescTrack) (hasProbeOut : Bool) (expectedArgv : Array String) :
    Except String Unit := do
  if img.path.isEmpty then
    throw s!"step={step} {kind} model ExecImage path is empty"
  if img.blockedSigs.contains 13 != expectSigpipeBlocked then
    throw s!"step={step} {kind} model ExecImage SIGPIPE blocked mismatch: got={img.blockedSigs.contains 13} exp={expectSigpipeBlocked}"
  let gotSpBlocked := ((dump.sigBlkBits >>> 12) &&& 1) != 0
  if gotSpBlocked != expectSigpipeBlocked then
    throw s!"step={step} {kind} child SIGPIPE blocked mismatch: got={gotSpBlocked} exp={expectSigpipeBlocked} mask={dump.sigBlkBits}"
  if (dump.sigBlkBits &&& 0x4a00) != 0 then
    throw s!"step={step} {kind} unexpected child blocked signals mask={dump.sigBlkBits}"
  let expectedEffArgv := if expectedArgv.isEmpty then #[""] else expectedArgv
  let imgArgv := (img.argv.map strOfBytes).toArray
  if imgArgv != expectedEffArgv then
    throw s!"step={step} {kind} model img.argv mismatch: img={repr imgArgv} expected={repr expectedEffArgv}"
  if dump.argv != expectedEffArgv then
    throw s!"step={step} {kind} argv mismatch: got={repr dump.argv} expected={repr expectedEffArgv}"
  let expPgid : Int32 :=
    if usePidNs then Int32.ofInt img.pgid
    else if img.pgid == modelPid then childPid
    else parentPgrp
  if dump.pgid != expPgid then
    throw s!"step={step} {kind} pgid mismatch: got={dump.pgid} exp={expPgid} (img.pgid={img.pgid} pidns={usePidNs})"
  let expPipe := if sigactionBlocked then -1 else modelDispToCode (execImageGetSig img 13)
  let expUsr1 := if sigactionBlocked then -1 else modelDispToCode (execImageGetSig img 10)
  let expUsr2 := if sigactionBlocked then -1 else modelDispToCode (execImageGetSig img 12)
  if dump.sigPipeDisp != expPipe then
    throw s!"step={step} {kind} SIGPIPE disp mismatch: got={dump.sigPipeDisp} exp={expPipe}"
  if dump.sigUsr1Disp != expUsr1 then
    throw s!"step={step} {kind} SIGUSR1 disp mismatch: got={dump.sigUsr1Disp} exp={expUsr1}"
  if dump.sigUsr2Disp != expUsr2 then
    throw s!"step={step} {kind} SIGUSR2 disp mismatch: got={dump.sigUsr2Disp} exp={expUsr2}"
  if hasProbeOut then
    let expEnv := img.envp.map strOfBytes |>.toArray
    if dump.envp != expEnv then
      throw s!"step={step} {kind} envp mismatch: got={repr dump.envp} exp={repr expEnv}"
  let expCwdStr := strOfBytes img.cwd
  if !expCwdStr.isEmpty && dump.cwd != expCwdStr then
    throw s!"step={step} {kind} cwd mismatch: got={dump.cwd} exp={expCwdStr}"
  let gotOpen := dump.openFds.filter (fun x => x.1 < 1024)
  let expOpen := img.fds.filter (fun p => p.1 < 1024)
  if gotOpen.size != expOpen.length then
    let gotFds := gotOpen.map (fun x => x.1)
    let expFds := expOpen.map (fun p => p.1)
    throw s!"step={step} {kind} openFd count mismatch: got={repr gotFds} exp={repr expFds}"
  for (fd, fl, dev, ino) in gotOpen do
    if fl != 0 then
      throw s!"step={step} {kind} post-exec fd {fd} has cloexec flags={fl}"
    match execImageGetFd img fd.toInt with
    | none => throw s!"step={step} {kind} unexpected surviving fd={fd}"
    | some e =>
      match descMap.find? (fun dt => dt.descId == e.desc) with
      | none => throw s!"step={step} {kind} missing desc track for fd={fd} desc={e.desc}"
      | some dt =>
        if dt.dev != dev || dt.ino != ino then
          throw s!"step={step} {kind} fd={fd} identity mismatch: got=({dev},{ino}) exp=({dt.dev},{dt.ino})"
        let expStdin := match sExp.getDesc e.desc with
          | .stream true _ _ bs => byteArrayOfBytes bs
          | _ => dt.stdinPayload
        if fd == 0 && dump.stdinBytes != expStdin then
          throw s!"step={step} {kind} fd=0 stdin bytes mismatch: got={dump.stdinBytes.size} exp={expStdin.size}"

private def applyPreSlotToModel (fds : List (Int × FdEntry)) (dst : Int) (src : Int32) (clo : Bool) :
    List (Int × FdEntry) :=
  if src == -1 then
    fds.filter (fun p => p.1 != dst)
  else if src >= 0 then
    match fds.find? (fun p => p.1 == src.toInt) with
    | some (_, e) => (dst, { desc := e.desc, cloexec := clo, extraFdFlags := 0#i32 }) :: fds.filter (fun p => p.1 != dst)
    | none => fds
  else
    fds

private def waitPidEintr (pid : Pid) : IO (Except Errno ChildWaitStatus) := do
  for _ in List.range 32 do
    match ← cHostWaitOnce pid with
    | .error e =>
      if e == Errno.EINTR then continue
      return .error e
    | .ok st => return .ok st
  return .error Errno.EINTR

private def waitChildPid (pid : Int32) : IO ChildWaitStatus := do
  match ← waitPidEintr pid.toUInt32 with
  | .ok st => return st
  | .error e => throw (IO.userError s!"waitpid({pid}) failed: errno={e}")

private def readCloseBitsBit (buf : ByteArray) (fd : Nat) : Bool :=
  let byteIdx := 4 + (fd >>> 3)
  if byteIdx < buf.size then
    ((buf.get! byteIdx).toNat &&& (1 <<< (fd &&& 7))) != 0
  else
    false

private def probeInheritedFds : IO (List (Int × FdEntry) × List DescTrack) := do
  let mut fds : List (Int × FdEntry) := []
  let mut tracks : List DescTrack := []
  for preFd in List.range 4096 do
    if preFd ≥ 3 then
      match ← cFcntlGetfd (UInt32.ofNat preFd) with
      | .ok fl =>
        fds := (Int.ofNat preFd, { desc := 200 + preFd, cloexec := (fl &&& 1) != 0 }) :: fds
        match ← cFstatDevIno (UInt32.ofNat preFd) with
        | .ok (d, i) =>
          tracks := { descId := 200 + preFd, dev := d, ino := i, stdinPayload := ByteArray.empty } :: tracks
        | .error _ => pure ()
      | .error _ => pure ()
  return (fds, tracks)

private def isStdioSlotPerm (a b c : Int32) : Bool :=
  let inRange := (0 ≤ a && a ≤ 2) && (0 ≤ b && b ≤ 2) && (0 ≤ c && c ≤ 2)
  let distinct := a != b && b != c && a != c
  inRange && distinct && (a != 0 || b != 1 || c != 2)

private def isStdioSelfDup (a b c : Int32) : Bool :=
  a == b || b == c || a == c

private def stageBucketName : FailureStage → String
  | .validate => "err.validate"
  | .processGroup => "err.processGroup"
  | .signalReset => "err.signalReset"
  | .fdSetup => "err.fdSetup"
  | .closeUnkept => "err.closeUnkept"
  | .chdir => "err.chdir"
  | .execve => "err.execve"
  | .wireTruncated => "err.wireTruncated"

private def requiredBuckets : Array CoverageBucket := #[
  bucket "run_child" "ok.execd",
  bucket "run_child" "err.validate",
  bucket "run_child" "err.processGroup",
  bucket "run_child" "err.signalReset",
  bucket "run_child" "err.fdSetup",
  bucket "run_child" "err.closeUnkept",
  bucket "run_child" "err.chdir",
  bucket "run_child" "err.execve",
  bucket "run_child" "sync.abort_125",
  bucket "run_child" "sync.byte_ok",
  bucket "stdio" "stdout_eq_0",
  bucket "stdio" "stderr_eq_1",
  bucket "stdio" "perm_0..2",
  bucket "stdio" "self_dup",
  bucket "close_fds" "close_range_ok",
  bucket "close_fds" "proc_self_fd_fallback",
  bucket "close_fds" "unmounted_proc",
  bucket "close_fds" "rlimit_nofile",
  bucket "close_fds" "standalone_ok",
  bucket "seccomp" "ret_errno_hit",
  bucket "sigpipe" "write_diff",
  bucket "sig" "non_sigpipe_ign_or_handler",
  bucket "argv_env" "empty_argv",
  bucket "argv_env" "multi_argv_envp",
  bucket "interface" "spawn_ok",
  bucket "interface" "spawn_childFailed",
  bucket "interface" "spawn_invalidInput",
  bucket "interface" "spawn_sysError",
  bucket "interface" "barrier_release_ok",
  bucket "interface" "barrier_abort_125",
  bucket "interface" "barrier_failedBefore",
  bucket "interface" "barrier_multi_interleave",
  bucket "interface" "close_sources_and_closed_raw",
  bucket "interface" "argToken_all",
  bucket "interface" "forkMode_immortalThread",
  bucket "interface" "pdeathsig_thread_exit_diff",
  bucket "interface" "wifsignaled"
]

private def recordTracker (ref : IO.Ref CoverageTracker) (op bkt : String) : IO Unit :=
  ref.modify (·.record op bkt)

private def runSigpipeWriteDiff (step : Nat) (rng : Rng) (trackerRef : IO.Ref CoverageTracker) : IO Rng := do
  let (pidnsChoice, r1) := rng.nextNat 2
  let (sigMode, r2) := r1.nextNat 3
  let (blockSp, r3) := r2.nextNat 2
  let sBase : ChildState :=
    { status := .running
      fds := [(1, { desc := 11, cloexec := false })]
      descs := [(11, .stream false true true [])]
      pid := if pidnsChoice == 1 then 1 else 42
      sig := [(13, sigDispToModel sigMode)]
      blockedSigs := if blockSp == 1 then [13] else [] }
  let payload : Slice Std.U8 := mkSliceU8 3#usize [97#u8, 98#u8, 99#u8]
  let sExp ← match Result.match (sys.write sBase 1#i32 payload) with
    | .ok (_, st) => pure st
    | _ => throw (IO.userError s!"step={step} sigpipeWrite model failed")
  let childPid ← match ← cSigpipeWriteFork (UInt32.ofNat pidnsChoice) (UInt32.ofNat sigMode) (UInt32.ofNat blockSp) with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"step={step} sigpipeWrite fork failed: errno={e}")
  let waitSt ← waitChildPid childPid
  let expWait :=
    match sExp.status with
    | .signaled sig => ChildWaitStatus.signaled (UInt32.ofNat sig.bv.toNat)
    | _ => ChildWaitStatus.exited 32
  if waitSt != expWait then
    throw (IO.userError s!"step={step} sigpipeWrite mismatch: got={repr waitSt} exp={repr expWait} (pidns={pidnsChoice} sigMode={sigMode} blockSp={blockSp})")
  recordTracker trackerRef "sigpipe" "write_diff"
  return r3

private def symInR : Int32 := -100
private def symP1w : Int32 := -101
private def symP2w : Int32 := -102
private def symRepW : Int32 := -103
private def symSyncR : Int32 := -104
private def symExtraFd : Int32 := -105
private def symClosedSlot : Int32 := -106
private def symP1r : Int32 := -107
private def symCoW : Int32 := -108

private def resolveSymFd (inR p1w p2w repW syncR extraFd closedSlot p1r coW x : Int32) : Int32 :=
  if x == symInR then inR
  else if x == symP1w then p1w
  else if x == symP2w then p2w
  else if x == symRepW then repW
  else if x == symSyncR then syncR
  else if x == symExtraFd then extraFd
  else if x == symClosedSlot then closedSlot
  else if x == symP1r then p1r
  else if x == symCoW then coW
  else x

private structure FuzzInput where
  isCloseOnly : Bool := false
  pfFlags : UInt32 := 0
  useHighFds : Bool := false
  useSetsid : Bool := false
  usePidNs : Bool := false
  useHideProc : Bool := false
  useBlockSigpipe : Bool := false
  spMode : Nat := 0
  su1Mode : Nat := 0
  su2Mode : Nat := 0
  rlimVal : Int32 := -1
  stdinArg : Int32 := 0
  stdoutArg : Int32 := 1
  stderrArg : Int32 := 2
  repArg : Int32 := -1
  syncArg : Int32 := -1
  extraKeepArg : Int32 := -1
  slot0Src : Int32 := -1
  slot1Src : Int32 := -1
  slot2Src : Int32 := -1
  clo0 : Bool := false
  clo1 : Bool := false
  clo2 : Bool := false
  cs0 : Int32 := -1
  closeArr : Array Int32 := #[]
  keepArr : Array Int32 := #[]
  cwd? : Option String := none
  cwdErr? : Option Std.I32 := none
  pathStr : String := "/bin/true"
  execErr? : Option Std.I32 := none
  argvArr : Array String := #["/bin/true"]
  envArr : Array String := #[]
  secTgt : SeccompTarget := .none
  secErrI32 : Std.I32 := ENOSYS
  brokenRep : Bool := false
  sendSyncByte : Bool := true
  deriving Repr, BEq, Inhabited

private def pfFlagsPopcount (fl : UInt32) : Nat :=
  (List.range 32).foldl
    (fun acc i => if ((fl >>> UInt32.ofNat i) &&& 1) != 0 then acc + 1 else acc) 0

private def envUserCount (inp : FuzzInput) : Nat :=
  (inp.envArr.filter (fun s => !s.startsWith "_PF_PROBE_OUT=")).size

private def fuzzInputWeight (inp : FuzzInput) : Nat :=
  inp.closeArr.size + inp.keepArr.size + inp.argvArr.size + envUserCount inp +
  (if inp.isCloseOnly then 1 else 0) +
  pfFlagsPopcount inp.pfFlags +
  (if inp.useHighFds then 1 else 0) +
  (if inp.useSetsid then 1 else 0) +
  (if inp.usePidNs then 1 else 0) +
  (if inp.useHideProc then 1 else 0) +
  (if inp.useBlockSigpipe then 1 else 0) +
  (if inp.spMode != 0 then 1 else 0) +
  (if inp.su1Mode != 0 then 1 else 0) +
  (if inp.su2Mode != 0 then 1 else 0) +
  (if inp.rlimVal ≥ 0 then 1 else 0) +
  (if inp.stdinArg != 0 then 1 else 0) +
  (if inp.stdoutArg != 1 then 1 else 0) +
  (if inp.stderrArg != 2 then 1 else 0) +
  (if inp.repArg != -1 then 1 else 0) +
  (if inp.syncArg != -1 then 1 else 0) +
  (if inp.extraKeepArg != -1 then 1 else 0) +
  (if inp.slot0Src != -1 then 1 else 0) +
  (if inp.slot1Src != -1 then 1 else 0) +
  (if inp.slot2Src != -1 then 1 else 0) +
  (if inp.clo0 then 1 else 0) +
  (if inp.clo1 then 1 else 0) +
  (if inp.clo2 then 1 else 0) +
  (if inp.cs0 != -1 then 1 else 0) +
  (if inp.cwd?.isSome then 1 else 0) +
  (if inp.pathStr != "/bin/true" then 1 else 0) +
  (if inp.secTgt != .none then 1 else 0) +
  (if inp.secErrI32 != ENOSYS then 1 else 0) +
  (if inp.brokenRep then 1 else 0) +
  (if !inp.sendSyncByte then 1 else 0)

private def shrinkArrayCands {α : Type} (xs : Array α) : List (Array α) := Id.run do
  let n := xs.size
  if n == 0 then
    return []
  let mut out : List (Array α) := [#[]]
  if n > 1 then
    let mid := n / 2
    out := out ++ [xs.extract 0 mid, xs.extract mid n]
  if n > 4 then
    let q := max 1 (n / 4)
    let mut off := 0
    while off < n do
      let hi := min n (off + q)
      out := out ++ [xs.extract 0 off ++ xs.extract hi n]
      off := hi
  for i in List.range (min n 64) do
    out := out ++ [xs.extract 0 i ++ xs.extract (i + 1) n]
  return out

private def shrinkFuzzInputOneStep (inp : FuzzInput) : List FuzzInput := Id.run do
  let mut cands : List FuzzInput := []
  if inp.useHighFds then cands := cands ++ [{ inp with useHighFds := false }]
  if inp.usePidNs then cands := cands ++ [{ inp with usePidNs := false }]
  if inp.useSetsid then cands := cands ++ [{ inp with useSetsid := false }]
  if inp.useHideProc then cands := cands ++ [{ inp with useHideProc := false }]
  if inp.useBlockSigpipe then cands := cands ++ [{ inp with useBlockSigpipe := false }]
  if inp.isCloseOnly then cands := cands ++ [{ inp with isCloseOnly := false }]
  if inp.brokenRep then cands := cands ++ [{ inp with brokenRep := false }]
  if !inp.sendSyncByte then cands := cands ++ [{ inp with sendSyncByte := true }]
  if inp.rlimVal ≥ 0 then cands := cands ++ [{ inp with rlimVal := -1 }]
  if inp.secTgt != .none then cands := cands ++ [{ inp with secTgt := .none }]
  if inp.secErrI32 != ENOSYS then cands := cands ++ [{ inp with secErrI32 := ENOSYS }]
  if inp.spMode != 0 then cands := cands ++ [{ inp with spMode := 0 }]
  if inp.su1Mode != 0 then cands := cands ++ [{ inp with su1Mode := 0 }]
  if inp.su2Mode != 0 then cands := cands ++ [{ inp with su2Mode := 0 }]
  if inp.cwd?.isSome then cands := cands ++ [{ inp with cwd? := none, cwdErr? := none }]
  if inp.pathStr != "/bin/true" then cands := cands ++ [{ inp with pathStr := "/bin/true", execErr? := none }]
  if inp.pfFlags != 0 then
    cands := cands ++ [{ inp with pfFlags := 0 }]
    for b in ([1, 2, 4, 8, 16, 32, 64] : List UInt32) do
      if (inp.pfFlags &&& b) != 0 then
        cands := cands ++ [{ inp with pfFlags := inp.pfFlags &&& (~~~b) }]
  if inp.stdinArg != 0 then cands := cands ++ [{ inp with stdinArg := 0 }]
  if inp.stdoutArg != 1 then cands := cands ++ [{ inp with stdoutArg := 1 }]
  if inp.stderrArg != 2 then cands := cands ++ [{ inp with stderrArg := 2 }]
  if inp.repArg != -1 then cands := cands ++ [{ inp with repArg := -1 }]
  if inp.syncArg != -1 then cands := cands ++ [{ inp with syncArg := -1 }]
  if inp.extraKeepArg != -1 then cands := cands ++ [{ inp with extraKeepArg := -1 }]
  if inp.slot0Src != -1 then cands := cands ++ [{ inp with slot0Src := -1 }]
  if inp.slot1Src != -1 then cands := cands ++ [{ inp with slot1Src := -1 }]
  if inp.slot2Src != -1 then cands := cands ++ [{ inp with slot2Src := -1 }]
  if inp.clo0 then cands := cands ++ [{ inp with clo0 := false }]
  if inp.clo1 then cands := cands ++ [{ inp with clo1 := false }]
  if inp.clo2 then cands := cands ++ [{ inp with clo2 := false }]
  if inp.cs0 != -1 then cands := cands ++ [{ inp with cs0 := -1 }]
  for ca in shrinkArrayCands inp.closeArr do
    cands := cands ++ [{ inp with closeArr := ca }]
  for ka in shrinkArrayCands inp.keepArr do
    cands := cands ++ [{ inp with keepArr := ka }]
  for aa in shrinkArrayCands inp.argvArr do
    cands := cands ++ [{ inp with argvArr := aa }]
  match inp.envArr[0]? with
  | some e0 =>
    if inp.pathStr != "/bin/true" && e0.startsWith "_PF_PROBE_OUT=" then
      for ea in shrinkArrayCands (inp.envArr.extract 1 inp.envArr.size) do
        cands := cands ++ [{ inp with envArr := #[e0] ++ ea }]
    else
      for ea in shrinkArrayCands inp.envArr do
        cands := cands ++ [{ inp with envArr := ea }]
  | none => pure ()
  return cands

private def shrinkFailingInput (inp : FuzzInput) (fails : FuzzInput → IO Bool) : IO FuzzInput := do
  let mut cur := inp
  for _ in List.range 512 do
    let mut progressed := false
    for cand in shrinkFuzzInputOneStep cur do
      if ← fails cand then
        cur := cand
        progressed := true
        break
    if !progressed then
      break
  return cur

private def closeTracked (fdsRef : IO.Ref (Array Int32)) (fd : Int32) : IO Unit := do
  if fd ≥ 0 then
    fdsRef.modify (fun arr => arr.filter (· != fd))
    let _ ← cClose fd.toUInt32

private def recordOpt (trackerRef? : Option (IO.Ref CoverageTracker)) (op bkt : String) : IO Unit := do
  if let some ref := trackerRef? then
    recordTracker ref op bkt

private def evalLowLevelCase
    (inheritedFds : List (Int × FdEntry)) (inheritedTracks : List DescTrack)
    (step : Nat) (sc : FuzzScratch) (inp : FuzzInput)
    (trackerRef? : Option (IO.Ref CoverageTracker)) : IO (Except (String × String) Unit) := do
  let _ ← cRmdirUnlink sc.probeOut 0
  let _ ← cRmdirUnlink "_pf_probe.bin" 0
  let parentRlim ← cGetRlimNofile
  let rlimVal : Int32 :=
    if inp.rlimVal ≥ 0 && UInt64.ofNat inp.rlimVal.toNatClampNeg > parentRlim then
      Int32.ofInt (Int.ofNat (min parentRlim.toNat 2147483647))
    else inp.rlimVal

  let fdsRef ← IO.mkRef (#[] : Array Int32)
  let childPidRef ← IO.mkRef (-1 : Int32)
  try
    let mut descTracks : List DescTrack := inheritedTracks
    let mut modelFds : List (Int × FdEntry) := inheritedFds
    let mut modelDescs : List (Desc × DescState) := []

    let stdinPayload := s!"in-{step}".toUTF8
    let (inR, inW) ← match ← cPipe2 0 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"pipe2 stdin failed: errno={e}")
    fdsRef.modify (·.push inR |>.push inW)
    writeAllFd inW stdinPayload
    closeTracked fdsRef inW
    let (d0, i0) ← match ← cFstatDevIno inR.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat inR failed: errno={e}")
    descTracks := { descId := 10, dev := d0, ino := i0, stdinPayload := stdinPayload } :: descTracks
    modelDescs := (10, .stream true false false (stdinPayload.toList.map (fun b => mkU8 b.toNat))) :: modelDescs
    modelFds := (inR.toInt, { desc := 10, cloexec := false }) :: modelFds

    let (p1r, p1w) ← match ← cPipe2 0 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"pipe2 p1 failed: errno={e}")
    fdsRef.modify (·.push p1r |>.push p1w)
    let (d1, i1) ← match ← cFstatDevIno p1w.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat p1w failed: errno={e}")
    let (d1r, i1r) ← match ← cFstatDevIno p1r.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat p1r failed: errno={e}")
    descTracks := { descId := 17, dev := d1r, ino := i1r, stdinPayload := ByteArray.empty } ::
      { descId := 11, dev := d1, ino := i1, stdinPayload := ByteArray.empty } :: descTracks
    modelDescs := (11, .stream false true false []) :: modelDescs
    modelFds := (p1w.toInt, { desc := 11, cloexec := false }) :: (p1r.toInt, { desc := 17, cloexec := false }) :: modelFds

    let (p2r, p2w) ← match ← cPipe2 0 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"pipe2 p2 failed: errno={e}")
    fdsRef.modify (·.push p2r |>.push p2w)
    let (d2, i2) ← match ← cFstatDevIno p2w.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat p2w failed: errno={e}")
    let (d2r, i2r) ← match ← cFstatDevIno p2r.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat p2r failed: errno={e}")
    descTracks := { descId := 18, dev := d2r, ino := i2r, stdinPayload := ByteArray.empty } ::
      { descId := 12, dev := d2, ino := i2, stdinPayload := ByteArray.empty } :: descTracks
    modelDescs := (12, .stream false true false []) :: modelDescs
    modelFds := (p2w.toInt, { desc := 12, cloexec := false }) :: (p2r.toInt, { desc := 18, cloexec := false }) :: modelFds

    let (repR, repW) ← match ← cPipe2 1 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"pipe2 rep failed: errno={e}")
    fdsRef.modify (·.push repR |>.push repW)
    let (dRep, iRep) ← match ← cFstatDevIno repW.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat repW failed: errno={e}")
    if inp.brokenRep then
      closeTracked fdsRef repR
    else
      let (dRepR, iRepR) ← match ← cFstatDevIno repR.toUInt32 with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"fstat repR failed: errno={e}")
      descTracks := { descId := 19, dev := dRepR, ino := iRepR, stdinPayload := ByteArray.empty } :: descTracks
      modelFds := (repR.toInt, { desc := 19, cloexec := true }) :: modelFds
    descTracks := { descId := 13, dev := dRep, ino := iRep, stdinPayload := ByteArray.empty } :: descTracks
    modelDescs := (13, .stream false true inp.brokenRep []) :: modelDescs
    modelFds := (repW.toInt, { desc := 13, cloexec := true }) :: modelFds

    let (syncR, syncW) ← match ← cPipe2 1 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"pipe2 sync failed: errno={e}")
    fdsRef.modify (·.push syncR |>.push syncW)
    let (dSync, iSync) ← match ← cFstatDevIno syncR.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat syncR failed: errno={e}")
    if inp.sendSyncByte then
      writeAllFd syncW (ByteArray.mk #[0x53])
    closeTracked fdsRef syncW
    descTracks := { descId := 14, dev := dSync, ino := iSync, stdinPayload := ByteArray.empty } :: descTracks
    modelDescs := (14, .stream true false false (if inp.sendSyncByte then [83#u8] else [])) :: modelDescs
    modelFds := (syncR.toInt, { desc := 14, cloexec := true }) :: modelFds

    let extraFd ← match ← cMemfd 1 with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"cMemfd failed: errno={e}")
    fdsRef.modify (·.push extraFd)
    let (dExt, iExt) ← match ← cFstatDevIno extraFd.toUInt32 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"fstat extraFd failed: errno={e}")
    descTracks := { descId := 15, dev := dExt, ino := iExt, stdinPayload := ByteArray.empty } :: descTracks
    modelDescs := (15, .stream true true false []) :: modelDescs
    modelFds := (extraFd.toInt, { desc := 15, cloexec := true }) :: modelFds

    let (coR, coW) ← if inp.isCloseOnly then
      match ← cPipe2 1 with
      | .ok p =>
        fdsRef.modify (·.push p.1 |>.push p.2)
        modelDescs := (16, .stream false true false []) :: modelDescs
        modelFds := (p.2.toInt, { desc := 16, cloexec := true }) :: (p.1.toInt, { desc := 20, cloexec := true }) :: modelFds
        pure p
      | .error e => throw (IO.userError s!"pipe2 close_out failed: errno={e}")
    else
      pure (-1, -1)

    if inp.useHighFds then
      for k in List.range 138 do
        let clo := k % 2 == 0
        match ← cDupFrom extraFd.toUInt32 120 (if clo then 1 else 0) with
        | .ok jf =>
          fdsRef.modify (·.push jf)
          modelFds := (jf.toInt, { desc := 15, cloexec := clo }) :: modelFds
        | .error _ => pure ()

    let closedSlot : Int32 ← match ← cMemfd 1 with
      | .ok f =>
        closeIgnore f
        pure f
      | .error e => throw (IO.userError s!"cMemfd closedSlot failed: errno={e}")

    let resFd := resolveSymFd inR p1w p2w repW syncR extraFd closedSlot p1r coW
    let slot0Src := resFd inp.slot0Src
    let slot1Src := resFd inp.slot1Src
    let slot2Src := resFd inp.slot2Src
    modelFds := applyPreSlotToModel modelFds 0 slot0Src inp.clo0
    modelFds := applyPreSlotToModel modelFds 1 slot1Src inp.clo1
    modelFds := applyPreSlotToModel modelFds 2 slot2Src inp.clo2
    let cs0 := resFd inp.cs0
    if cs0 >= 3 then
      modelFds := modelFds.filter (fun p => p.1 != cs0.toInt)

    let stdinArg := resFd inp.stdinArg
    let stdoutArg := resFd inp.stdoutArg
    let stderrArg := resFd inp.stderrArg
    let repArg := resFd inp.repArg
    let syncArg := resFd inp.syncArg
    let extraKeepArg := resFd inp.extraKeepArg
    let closeArr := inp.closeArr.map resFd
    let keepArr := inp.keepArr.map resFd

    let bpfBlob :=
      if inp.secTgt == .none then ByteArray.empty
      else buildSeccompRetErrnoBpf (seccompTargetNr inp.secTgt) (UInt32.ofNat inp.secErrI32.val.toNat)

    let (parentPid, parentSid) ← cGetPidSid
    let parentPgrp ← cGetpgrp
    let freshChildPid : Int := max parentPid.toInt (max parentSid.toInt parentPgrp.toInt) + 1
    let (modelPid, modelSid, modelPgid) :=
      if inp.usePidNs then
        if inp.useSetsid then ((1 : Int), (1 : Int), (1 : Int))
        else ((1 : Int), (0 : Int), (0 : Int))
      else if inp.useSetsid then (freshChildPid, freshChildPid, freshChildPid)
      else (freshChildPid, parentSid.toInt, parentPgrp.toInt)
    let modelSigs : List (Int × Disp) :=
      [(13, sigDispToModel inp.spMode), (10, sigDispToModel inp.su1Mode), (12, sigDispToModel inp.su2Mode)]
    let modelLimit : Int :=
      if rlimVal >= 0 then rlimVal.toInt
      else min (Int.ofNat parentRlim.toNat) 2147483648
    let sBase : ChildState := {
      status := .running
      fds := modelFds
      descs := modelDescs
      fdLimit := modelLimit
      kernelMasksSetfd := true
      closeRangeSupported := true
      closeRangeErrno := ENOSYS
      procSelfFdAvailable := !inp.useHideProc
      procOpenErrno := ENOENT
      pid := modelPid
      sid := modelSid
      pgid := modelPgid
      cwd := bytesOfString sc.initCwd
      chdirResolved := sc.cwdResolved
      sig := modelSigs
      blockedSigs := if inp.useBlockSigpipe then [13] else []
      oracle := []
    }

    let envFlags : Int32 :=
      (if inp.useSetsid then 1 else 0) ||| (if inp.usePidNs then 2 else 0) |||
      (if inp.useHideProc then 4 else 0) ||| (if inp.useBlockSigpipe then 8 else 0)
    let closeOutArg : Int32 := if inp.isCloseOnly then coW else -1
    let cfgVals : Array Int32 := #[
      if inp.isCloseOnly then 1 else 0,
      Int32.ofInt (Int.ofNat inp.pfFlags.toNat),
      syncArg, stdinArg, stdoutArg, stderrArg, repArg, extraKeepArg, closeOutArg,
      slot0Src, if inp.clo0 then 1 else 0,
      slot1Src, if inp.clo1 then 1 else 0,
      slot2Src, if inp.clo2 then 1 else 0,
      cs0, -1, -1,
      rlimVal, envFlags,
      Int32.ofInt (Int.ofNat inp.spMode),
      Int32.ofInt (Int.ofNat inp.su1Mode),
      Int32.ofInt (Int.ofNat inp.su2Mode)
    ]
    let cfgBlob := encodeI32ArrayLe cfgVals
    let closeBlob := encodeI32ArrayLe closeArr
    let keepBlob := encodeI32ArrayLe keepArr

    let cwdCStrOpt : Option sys.CStr := inp.cwd?.map strToCStr
    let pathCStr := strToCStr inp.pathStr
    let argvCStr := strArrToCStrArray inp.argvArr
    let envpCStr := strArrToCStrArray inp.envArr
    let closeSlice := i32ArrToSlice closeArr
    let keepSlice := i32ArrToSlice keepArr

    let pfFlagsStd : Std.U32 := ⟨BitVec.ofNat 32 inp.pfFlags.toNat⟩
    let modelOutcome : Except String ChildState :=
      if !inp.isCloseOnly then
        runWithSeccompFixedPoint sBase inp.secTgt inp.secErrI32 inp.cwdErr? inp.execErr?
          (fun st => postfork.child.run_child st
            { flags := pfFlagsStd
              sync_r := mkI32 syncArg.toInt
              stdin_fd := mkI32 stdinArg.toInt
              stdout_fd := mkI32 stdoutArg.toInt
              stderr_fd := mkI32 stderrArg.toInt
              rep_w := mkI32 repArg.toInt }
            closeSlice keepSlice cwdCStrOpt pathCStr argvCStr envpCStr)
          (fun st => st.trace)
      else do
        let p ← runWithSeccompFixedPoint sBase inp.secTgt inp.secErrI32 inp.cwdErr? inp.execErr?
          (fun st => postfork.fd_ops.close_fds_above2_except st (mkI32 extraKeepArg.toInt) keepSlice)
          (fun p => p.2.trace)
        let rc : Int32 := match p.1 with
          | core.result.Result.Ok _ => 0
          | core.result.Result.Err e => Int32.ofInt e.val
        return { p.2 with status := .exited (mkI32 (if rc == 0 then 0 else rc.toInt % 256)) }

    let sExp ← match modelOutcome with
      | .ok st => pure st
      | .error msg => return .error ("MODEL_EVAL_FAIL", s!"step={step} model eval failed: {msg}")

    let redirStdio := (inp.pfFlags &&& Model.FLAG_REDIRECT_STDIO) != 0
    let stdioReached :=
      !inp.isCloseOnly && redirStdio &&
      sExp.trace.any (fun ev => match ev.req with
        | .closeRange .. | .chdir _ | .execve .. => true
        | _ => false)
    if stdioReached && stdoutArg == 0 then
      recordOpt trackerRef? "stdio" "stdout_eq_0"
    if stdioReached && stderrArg == 1 then
      recordOpt trackerRef? "stdio" "stderr_eq_1"
    if stdioReached && isStdioSlotPerm stdinArg stdoutArg stderrArg then
      recordOpt trackerRef? "stdio" "perm_0..2"
    if stdioReached && isStdioSelfDup stdinArg stdoutArg stderrArg then
      recordOpt trackerRef? "stdio" "self_dup"
    if inp.secTgt != .none && sExp.trace.any (fun ev => (seccompFaultForReq inp.secTgt inp.secErrI32 ev.req).isSome) then
      recordOpt trackerRef? "seccomp" "ret_errno_hit"
    if rlimVal >= 0 && sExp.trace.any (fun ev => match ev.req with
        | .fcntlDupfdCloexec .. | .openProcSelfFd | .closeRange .. => true
        | _ => false) then
      recordOpt trackerRef? "close_fds" "rlimit_nofile"
    if !inp.isCloseOnly && (sExp.status matches .execd _) && (inp.su1Mode != 0 || inp.su2Mode != 0) then
      recordOpt trackerRef? "sig" "non_sigpipe_ign_or_handler"
    if !inp.isCloseOnly && inp.useHideProc && (inp.pfFlags &&& Model.FLAG_CLOSE_UNKEPT_ABOVE2) != 0 then
      recordOpt trackerRef? "close_fds" "unmounted_proc"
    if sExp.trace.any (fun ev => match ev.req, ev.out with | .closeRange .., .okVal _ => true | _, _ => false) then
      recordOpt trackerRef? "close_fds" "close_range_ok"
    if sExp.trace.any (fun ev => match ev.req, ev.out with | .getdents64 _, .okVal _ => true | _, _ => false) then
      recordOpt trackerRef? "close_fds" "proc_self_fd_fallback"
    if inp.isCloseOnly then
      recordOpt trackerRef? "close_fds" "standalone_ok"

    let childPid ← match ← cForkRun cfgBlob closeBlob keepBlob bpfBlob inp.cwd? inp.pathStr inp.argvArr inp.envArr with
      | .ok p => pure p
      | .error e => return .error ("FORK_FAILED", s!"step={step} fork failed: errno={e}")
    childPidRef.set childPid

    closeTracked fdsRef repW
    closeTracked fdsRef p1w
    closeTracked fdsRef p2w
    closeTracked fdsRef coW
    let repBytes ← if inp.brokenRep then pure ByteArray.empty else readAllFd repR
    let p1Bytes ← readAllFd p1r
    let p2Bytes ← readAllFd p2r
    let closeDump ← if inp.isCloseOnly then readAllFd coR else pure ByteArray.empty
    let waitSt ← waitChildPid childPid
    childPidRef.set (-1)

    let repDesc? := (sBase.getFd repArg.toInt).map (·.desc)
    let trackRepWire :=
      !inp.isCloseOnly && repArg >= 0 &&
      match repDesc? with
      | some 13 => !inp.brokenRep
      | some 11 => inp.pathStr != sc.probeBin || inp.argvArr.size < 2 || inp.argvArr[1]! != "--emit-stdio"
      | some 12 => inp.pathStr != sc.probeBin || inp.argvArr.size < 2 || inp.argvArr[1]! != "--emit-stdio"
      | _ => false
    let checkRepWire : IO (Except (String × String) Unit) := do
      if trackRepWire then
        if let some rd := repDesc? then
          let gotBytes := match rd with
            | 11 => p1Bytes
            | 12 => p2Bytes
            | _ => repBytes
          let expWritten := byteArrayOfBytes (writtenBytesForDesc sExp.writeLog rd)
          if gotBytes != expWritten then
            return .error ("WIRE_MISMATCH", s!"step={step} flags={inp.pfFlags} desc={rd} wire mismatch: got={repr gotBytes.toList} exp={repr expWritten.toList} (secTgt={repr inp.secTgt} secErr={inp.secErrI32.val} cwdErr={repr inp.cwdErr?} execErr={repr inp.execErr?} pidns={inp.usePidNs} setsid={inp.useSetsid} repArg={repArg})")
          if rd == 13 && gotBytes.size == 8 then
            match decodeChildFailure gotBytes with
            | some cf =>
              if cf.stage == .wireTruncated then
                return .error ("WIRE_TRUNCATED", s!"step={step} decoded unexpected wireTruncated from {repr gotBytes.toList}")
              recordOpt trackerRef? "run_child" (stageBucketName cf.stage)
            | none => return .error ("WIRE_DECODE_NONE", s!"step={step} decodeChildFailure returned none on 8-byte wire")
      return .ok ()

    match sExp.status with
    | .exited code =>
      let expWaitCode := UInt32.ofNat (code.bv.toNat % 256)
      if waitSt != .exited expWaitCode then
        return .error ("EXIT_MISMATCH", s!"step={step} flags={inp.pfFlags} closeOnly={inp.isCloseOnly} exit mismatch: got={repr waitSt} exp=exited {expWaitCode} (secTgt={repr inp.secTgt} rlim={rlimVal} pidns={inp.usePidNs} setsid={inp.useSetsid} hideProc={inp.useHideProc} modelFds={modelFds.length} sync={syncArg} in={stdinArg} out={stdoutArg} err={stderrArg} rep={repArg})")
      if let .error e ← checkRepWire then
        return .error e
      if !inp.isCloseOnly && expWaitCode == 125 then
        recordOpt trackerRef? "run_child" "sync.abort_125"
      if inp.isCloseOnly then
        if closeDump.size != 132 then
          return .error ("CLOSE_DUMP_SIZE", s!"step={step} close_fds_above2_except malformed dump size={closeDump.size}")
        let (rcU, _) := (readU32LeAt? closeDump 0).getD (0, 0)
        let rcI := Int32.ofInt (Int.ofNat rcU.toNat)
        if (rcI == 0) != (code == 0#i32) || (if rcI == 0 then (0 : Int) else rcI.toInt % 256) != code.val then
          return .error ("CLOSE_RC_MISMATCH", s!"step={step} close_fds_above2_except rc mismatch: rcI={rcI} code={code.val}")
        for fd in List.range 1024 do
          if Int.ofNat fd != coW.toInt then
            let modelOpen := sExp.isOpen (Int.ofNat fd)
            let realOpen := readCloseBitsBit closeDump fd
            if realOpen != modelOpen then
              return .error ("CLOSE_FD_MISMATCH", s!"step={step} close_fds_above2_except fd={fd} open mismatch: real={realOpen} model={modelOpen} (extra={extraKeepArg} keep={repr keepArr} sec={repr inp.secTgt} rlim={rlimVal} hideProc={inp.useHideProc})")
      return .ok ()
    | .signaled sig =>
      let expSig := UInt32.ofNat sig.bv.toNat
      if waitSt != .signaled expSig then
        return .error ("SIG_MISMATCH", s!"step={step} flags={inp.pfFlags} signal mismatch: got={repr waitSt} exp=signaled {expSig}")
      return .ok ()
    | .execd img =>
      if waitSt != .exited 0 then
        return .error ("EXEC_WAIT_MISMATCH", s!"step={step} flags={inp.pfFlags} execed child wait mismatch: got={repr waitSt} (secTgt={repr inp.secTgt} rlim={rlimVal} pidns={inp.usePidNs} setsid={inp.useSetsid} hideProc={inp.useHideProc} cwd={repr inp.cwd?} path={inp.pathStr} rep={repArg})")
      if let .error e ← checkRepWire then
        return .error e
      recordOpt trackerRef? "run_child" "ok.execd"
      if (inp.pfFlags &&& Model.FLAG_HAS_SYNC_BARRIER) != 0 then
        recordOpt trackerRef? "run_child" "sync.byte_ok"
      if inp.argvArr.isEmpty then
        recordOpt trackerRef? "argv_env" "empty_argv"
      if inp.argvArr.size >= 3 && inp.envArr.size >= 2 then
        recordOpt trackerRef? "argv_env" "multi_argv_envp"
      if inp.pathStr == sc.probeBin then
        let dumpBytes? : Option ByteArray ←
          try some <$> IO.FS.readBinFile sc.probeOut
          catch _ => pure none
        let some dumpBytes := dumpBytes?
          | return .error ("PROBE_DUMP_MISSING", s!"step={step} missing probe dump at {sc.probeOut}")
        let dump ← match parseProbeDump? dumpBytes with
          | some d => pure d
          | none => return .error ("PROBE_DUMP_BAD", s!"step={step} malformed probe dump ({dumpBytes.size} bytes)")
        let expSpBlocked := inp.useBlockSigpipe && (inp.pfFlags &&& Model.FLAG_RESET_SIGPIPE) == 0
        match compareExecImage step s!"flags={inp.pfFlags}" inp.usePidNs expSpBlocked (inp.secTgt == .sigaction) modelPid childPid parentPgrp img sExp dump descTracks true inp.argvArr with
        | .ok () => return .ok ()
        | .error msg => return .error ("EXEC_IMAGE_MISMATCH", s!"{msg} (secTgt={repr inp.secTgt} secErr={inp.secErrI32.val} in={stdinArg} out={stdoutArg} err={stderrArg} rep={repArg})")
      else
        return .ok ()
    | .running =>
      return .error ("MODEL_RUNNING", s!"step={step} model left child in .running state")
  finally
    let pid ← childPidRef.get
    if pid > 0 then
      let _ ← waitPidEintr pid.toUInt32
    (← fdsRef.get).forM closeIgnore
    let _ ← cRmdirUnlink sc.probeOut 0
    let _ ← cRmdirUnlink "_pf_probe.bin" 0

private def fuzzLowLevelEpisode
    (inheritedFds : List (Int × FdEntry)) (inheritedTracks : List DescTrack)
    (step totalSteps : Nat) (isSmoke : Bool) (rng : Rng) (sc : FuzzScratch) (trackerRef : IO.Ref CoverageTracker) : IO Rng := do
  let isRoot := (← cGeteuid) == 0
  let parentRlim ← cGetRlimNofile
  let (isCloseOnlyRaw, r0) := rng.chance 1 6
  let (fPgid, r1a) := r0.chance 1 2
  let (fResetSp, r1b) := r1a.chance 1 2
  let (fSyncBar, r1c) := r1b.chance 1 2
  let (fRedirStdio, r1d) := r1c.chance 2 3
  let (fCloseUnkept, r1e) := r1d.chance 1 2
  let (fCloseSrcRaw, r1f) := r1e.chance 1 2
  let (forceInvalidFlags, r1) := r1f.chance 1 32
  let detMode := isSmoke || totalSteps >= 1000
  let smokeForceExec := detMode && (step < 2 || step == 6)
  let smokeForcePgidErr := detMode && step == 2
  let smokeForceCloseErr := detMode && step == 3
  let smokeForceFallback := detMode && step == 4
  let smokeForceSigResetErr := detMode && step == 5
  let smokeForceRelocChdirErr := detMode && step == 7
  let smokeForceSigDflErr := detMode && step == 8
  let smokeForceValidateErr := detMode && step == 9
  let smokeForceFdSetupRlimErr := detMode && step == 10
  let smokeForceExecveErr := detMode && step == 11
  let smokeForceSyncAbort := detMode && step == 12
  let smokeForceCloseOnly := detMode && step == 13
  let smokeFixed := detMode && step < 14
  let isCloseOnly := if smokeForceCloseOnly then true else if smokeFixed then false else isCloseOnlyRaw
  let pfFlags : UInt32 :=
    if smokeForceExec then
      if step == 0 then Model.FLAG_REDIRECT_STDIO ||| Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_HAS_SYNC_BARRIER
      else if step == 1 then Model.FLAG_REDIRECT_STDIO ||| Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_CLOSE_UNKEPT_ABOVE2
      else Model.FLAG_REDIRECT_STDIO ||| Model.FLAG_RESET_SIGPIPE
    else if smokeForcePgidErr then Model.FLAG_SET_PGID
    else if smokeForceSigResetErr || smokeForceSigDflErr || smokeForceExecveErr then Model.FLAG_RESET_SIGPIPE
    else if smokeForceCloseErr || smokeForceFallback then Model.FLAG_CLOSE_UNKEPT_ABOVE2
    else if smokeForceRelocChdirErr || smokeForceFdSetupRlimErr then Model.FLAG_REDIRECT_STDIO
    else if smokeForceValidateErr then 64
    else if smokeForceSyncAbort then Model.FLAG_HAS_SYNC_BARRIER
    else if smokeForceCloseOnly then 0
    else if forceInvalidFlags then
      (if step % 2 == 0 then 64 else Model.FLAG_CLOSE_STDIO_SOURCES)
    else
      (if fPgid then Model.FLAG_SET_PGID else 0) |||
      (if fResetSp then Model.FLAG_RESET_SIGPIPE else 0) |||
      (if fSyncBar then Model.FLAG_HAS_SYNC_BARRIER else 0) |||
      (if fRedirStdio then Model.FLAG_REDIRECT_STDIO else 0) |||
      (if fCloseUnkept then Model.FLAG_CLOSE_UNKEPT_ABOVE2 else 0) |||
      (if fRedirStdio && !fCloseUnkept && fCloseSrcRaw then Model.FLAG_CLOSE_STDIO_SOURCES else 0)
  let (useHighFdsRaw, r2) := r1.chance 1 16
  let (useSetsidRaw, r3) := r2.chance 1 4
  let (usePidNsRaw, r4) := r3.chance 1 6
  let (useHideProcRaw, r5) := r4.chance 1 8
  let useHighFds := if smokeFixed then false else useHighFdsRaw
  let useSetsid := if smokeForcePgidErr then true else if smokeFixed then false else useSetsidRaw
  let usePidNs := if smokeForceCloseErr then true else if smokeFixed then false else usePidNsRaw
  let useHideProc := if smokeForceCloseErr then true else if smokeFixed then false else useHideProcRaw
  let (useBlockSigpipe, r5') := r5.chance 1 3
  let (spMode, r6) := r5'.nextNat 3
  let (su1ModeRaw, r7) := r6.nextNat 3
  let su1Mode := if smokeForceExec && step == 1 then 1 else su1ModeRaw
  let (su2Mode, r8) := r7.nextNat 3
  let isUserNs := usePidNs || useHideProc
  let (rlimChoice, r9) := r8.nextNat 10
  let cleanExecBias := !isSmoke && !smokeFixed && !forceInvalidFlags && !isCloseOnly && step % 5 == 4
  let rlimRaw : Int32 :=
    if smokeForceFdSetupRlimErr then 3
    else if smokeFixed then -1
    else match rlimChoice with
    | 0 => 3
    | 1 => 4
    | 2 => 5
    | 3 => 6
    | 4 => 7
    | 5 => 8
    | 6 => 16
    | 7 => 32
    | 8 => 64
    | _ => -1
  let rlimVal : Int32 :=
    if rlimRaw ≥ 0 && UInt64.ofNat rlimRaw.toNatClampNeg > parentRlim then
      Int32.ofInt (Int.ofNat (min parentRlim.toNat 2147483647))
    else rlimRaw
  let (brokenRepRaw, r10) := r9.chance 1 8
  let brokenRep := if smokeFixed || cleanExecBias then false else brokenRepRaw
  let (sendSyncByteRaw, r11) := r10.chance 3 4
  let sendSyncByte := if smokeForceSyncAbort then false else if smokeForceExec || cleanExecBias then true else sendSyncByteRaw
  let r12 := r11
  let baseSources : Array Int32 := #[symInR, symP1w, symP2w]
  let (permIdxRaw, r13) := r12.nextNat 8
  let permIdx :=
    if smokeForceExec || smokeForceFdSetupRlimErr then 0
    else if smokeForceRelocChdirErr then 6
    else permIdxRaw
  let (slot0Src, slot1Src, slot2Src) := match permIdx with
    | 0 => (baseSources[0]!, baseSources[1]!, baseSources[2]!)
    | 1 => (baseSources[2]!, baseSources[0]!, baseSources[1]!)
    | 2 => (baseSources[1]!, baseSources[2]!, baseSources[0]!)
    | 3 => (baseSources[0]!, -1, baseSources[2]!)
    | 4 => (-1, baseSources[1]!, -1)
    | 5 => (symRepW, baseSources[1]!, baseSources[2]!)
    | 6 => (baseSources[0]!, symRepW, baseSources[2]!)
    | _ => (baseSources[0]!, baseSources[1]!, symRepW)
  let (clo0, r14) := r13.chance 1 2
  let (clo1, r15) := r14.chance 1 2
  let (clo2, r16) := r15.chance 1 2
  let (closeStage0, r17) := r16.chance 1 3
  let cs0 : Int32 := if smokeFixed then -1 else if closeStage0 then symP1r else -1

  let openPool : Array Int32 := #[0, 1, 2, symInR, symP1w, symP2w, symRepW, symSyncR, symExtraFd]
  let allChoices := openPool ++ #[symClosedSlot, -1, 450]
  let (stdioPatRaw, r17p) := r17.nextNat 8
  let stdioPat := if cleanExecBias then stdioPatRaw % 6 else stdioPatRaw
  let (inMode, r18) := r17p.nextNat 4
  let (inArgIdx, r19) := r18.nextNat allChoices.size
  let (outMode, r20) := r19.nextNat 4
  let (outArgIdx, r21) := r20.nextNat allChoices.size
  let (errMode, r22) := r21.nextNat 4
  let (errArgIdx, r23) := r22.nextNat allChoices.size
  let (repArgChoice, r24) := r23.nextNat 10
  let (syncArgChoice, r25) := r24.nextNat 6
  let (stdinArg, stdoutArg, stderrArg) : Int32 × Int32 × Int32 :=
    if smokeForceExec then
      if step == 0 then (1, 0, 2) else if step == 1 then (2, 1, 1) else (0, 2, 1)
    else if smokeForceRelocChdirErr then (0, symP1w, 2)
    else if smokeForceFdSetupRlimErr then (1, 0, 2)
    else if stdioPat == 0 then (1, 2, 0)
    else if stdioPat == 1 then (2, 0, 1)
    else if stdioPat == 2 then (1, 0, 2)
    else if stdioPat == 3 then (0, 2, 1)
    else if stdioPat == 4 then (2, 1, 0)
    else if stdioPat == 5 then (0, 0, 2)
    else
      let a := match inMode with | 0 => 0 | 1 => 1 | 2 => 2 | _ => allChoices[inArgIdx]!
      let b := match outMode with | 0 => 1 | 1 => 2 | 2 => 0 | _ => allChoices[outArgIdx]!
      let c := match errMode with | 0 => 2 | 1 => 0 | 2 => 1 | _ => allChoices[errArgIdx]!
      (a, b, c)
  let repArg : Int32 :=
    if smokeForceRelocChdirErr then 1
    else if smokeFixed || cleanExecBias then symRepW
    else match repArgChoice with
    | 0 => -1
    | 1 => symClosedSlot
    | 2 => 0
    | 3 => 1
    | 4 => 2
    | 5 => symP1w
    | 6 => symP2w
    | _ => symRepW
  let syncArg : Int32 :=
    if smokeForceExec || smokeForceSyncAbort || cleanExecBias then symSyncR
    else if smokeFixed then -1
    else match syncArgChoice with
    | 0 => -1
    | 1 => symClosedSlot
    | 2 => symP1w
    | _ => symSyncR
  let (useCoInExtra, r26) := r25.chance 1 2
  let (extraNone, r27) := r26.chance 1 3
  let extraKeepArg : Int32 :=
    if smokeForceCloseOnly then symCoW
    else if smokeFixed then -1
    else if isCloseOnly && useCoInExtra then symCoW
    else if extraNone then -1
    else symExtraFd

  let (nClose, r28) := r27.nextNat 3
  let mut closeArr : Array Int32 := #[]
  let mut rCur := r28
  for _ in List.range nClose do
    let (idx, rNext) := rCur.nextNat allChoices.size
    rCur := rNext
    closeArr := closeArr.push allChoices[idx]!
  if smokeFixed || cleanExecBias then closeArr := #[]

  let (nKeep, r24') := rCur.nextNat 3
  let mut keepArr : Array Int32 := if isCloseOnly && !useCoInExtra then #[symCoW] else #[]
  rCur := r24'
  for _ in List.range nKeep do
    let (idx, rNext) := rCur.nextNat allChoices.size
    rCur := rNext
    keepArr := keepArr.push allChoices[idx]!
  if smokeForceCloseOnly then keepArr := #[symExtraFd]
  else if smokeFixed || cleanExecBias then keepArr := #[]

  let ((cwd?Raw, cwdErrRaw?), r25') := pickCwdAndErrno rCur sc (isUserNs || isRoot)
  let ((pathStrRaw, execErrRaw?), r26') := pickPathAndErrno r25' sc (isUserNs || isRoot)
  let (argvArrRaw, r27') := pickArgv r26' (if cleanExecBias then sc.probeBin else pathStrRaw)
  let (envArrRaw, r28') := pickEnvp r27' sc.probeOut (cleanExecBias || pathStrRaw == sc.probeBin)
  let cwd? := if smokeForceRelocChdirErr then some sc.missingPath else if smokeFixed || cleanExecBias then none else cwd?Raw
  let cwdErr? := if smokeForceRelocChdirErr then some ENOENT else if smokeFixed || cleanExecBias then none else cwdErrRaw?
  let pathStr := if smokeForceExecveErr then sc.missingPath else if smokeFixed || cleanExecBias then sc.probeBin else pathStrRaw
  let execErr? := if smokeForceExecveErr then some ENOENT else if smokeFixed || cleanExecBias then none else execErrRaw?
  let argvArr := if smokeForceExec then (if step == 0 then #[] else #[sc.probeBin, "arg1", "arg 2"]) else if smokeFixed then #[sc.probeBin] else argvArrRaw
  let envArr := if smokeFixed then #[s!"_PF_PROBE_OUT={sc.probeOut}", "PF_A=1", "PF_EMPTY="] else envArrRaw

  let (useSeccomp, r29) := r28'.chance 1 4
  let (tgtIdx, r30) := r29.nextNat allSeccompTargets.size
  let secTgt :=
    if smokeForceCloseErr || smokeForceFallback then .closeRange
    else if smokeForceSigResetErr then .rtSigprocmask
    else if smokeForceSigDflErr then .sigaction
    else if !smokeFixed && useSeccomp then allSeccompTargets[tgtIdx]!
    else .none
  let (errChoice, r31) := r30.nextNat 4
  let secErrI32 : Std.I32 :=
    if smokeForceCloseErr || smokeForceFallback then ENOSYS
    else if smokeForceSigResetErr || smokeForceSigDflErr then EPERM
    else match errChoice with
    | 0 => ENOSYS
    | 1 => EPERM
    | 2 => EIO
    | _ => EACCES

  let inp : FuzzInput := {
    isCloseOnly, pfFlags, useHighFds, useSetsid, usePidNs, useHideProc, useBlockSigpipe,
    spMode, su1Mode, su2Mode, rlimVal, stdinArg, stdoutArg, stderrArg, repArg, syncArg,
    extraKeepArg, slot0Src, slot1Src, slot2Src, clo0, clo1, clo2, cs0,
    closeArr, keepArr, cwd?, cwdErr?, pathStr, execErr?, argvArr, envArr,
    secTgt, secErrI32, brokenRep, sendSyncByte
  }
  match ← evalLowLevelCase inheritedFds inheritedTracks step sc inp (some trackerRef) with
  | .ok () => pure ()
  | .error (origCls, origMsg) =>
    let shrunk ← shrinkFailingInput inp fun cand => do
      match ← evalLowLevelCase inheritedFds inheritedTracks step sc cand none with
      | .error (c, _) => pure (c == origCls)
      | .ok () => pure false
    throw (IO.userError s!"{origMsg} (shrunk_weight={fuzzInputWeight inp}->{fuzzInputWeight shrunk}, shrunk={repr shrunk})")

  let rAfterSigpipe ← if step % 12 == 0 then runSigpipeWriteDiff step r31 trackerRef else pure r31
  return rAfterSigpipe

private def parseFirstLineTid (statStr : String) : String :=
  (statStr.splitOn " ").headD ""

private def waitForThreadExit (tid : String) : IO Unit := do
  if tid.isEmpty then
    return
  let path : System.FilePath := ⟨s!"/proc/self/task/{tid}"⟩
  for _ in List.range 1000 do
    if !(← System.FilePath.pathExists path) then
      return
    IO.sleep 1
  throw (IO.userError s!"transient Lean worker thread tid={tid} did not exit within 1000ms")

private def runOnePdeathsigThreadExitCase (mode : ForkMode) : IO (ChildWaitStatus × ByteArray) := do
  let (readyR, readyW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"pdeathsig ready pipe2 failed: errno={e}")
  let (goR, goW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore readyR; closeHandleIgnore readyW
      throw (IO.userError s!"pdeathsig go pipe2 failed: errno={e}")
  let (outR, outW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore readyR; closeHandleIgnore readyW
      closeHandleIgnore goR; closeHandleIgnore goW
      throw (IO.userError s!"pdeathsig out pipe2 failed: errno={e}")
  let (errR, errW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore readyR; closeHandleIgnore readyW
      closeHandleIgnore goR; closeHandleIgnore goW
      closeHandleIgnore outR; closeHandleIgnore outW
      throw (IO.userError s!"pdeathsig err pipe2 failed: errno={e}")
  let pyCode :=
    "import ctypes, os, signal, sys; " ++
    "libc = ctypes.CDLL(None); " ++
    "libc.prctl.argtypes = [ctypes.c_int, ctypes.c_ulong]; " ++
    "libc.prctl.restype = ctypes.c_int; " ++
    "rc = libc.prctl(1, signal.SIGKILL); " ++
    "assert rc == 0; " ++
    "fd = int(sys.argv[1]); " ++
    "os.write(fd, b'R'); os.close(fd); " ++
    "sys.stdin.read(1); " ++
    "os.write(1, b'A')"
  let spec : ChildSpec := {
    path := "/usr/bin/python3"
    argv := #[.ofLiteral "/usr/bin/python3", .ofLiteral "-c", .ofLiteral pyCode, .ofHandle readyW]
    stdio := .redirect (.handle goR) (.handle outW) (.handle errW) true
    fdPolicy := .closeAllAbove2Except #[.handle readyW]
    forkMode := mode
  }
  let mut spawnedChild? : Option SpawnedChild := none
  try
    let task ← IO.asTask (prio := .dedicated) do
      let statStr ← IO.FS.readFile "/proc/thread-self/stat"
      let tid := parseFirstLineTid statStr
      let child ← match ← LeanSwe.PostFork.spawn spec with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"pdeathsig spawn failed: {repr e}")
      closeHandleIgnore readyW
      closeHandleIgnore goR
      closeHandleIgnore outW
      closeHandleIgnore errW
      let readyBytes ← readAllHandle readyR
      closeHandleIgnore readyR
      if readyBytes != "R".toUTF8 then
        throw (IO.userError s!"pdeathsig unexpected ready bytes: {repr readyBytes.toList}")
      return (tid, child)
    let (tid, child) ← IO.ofExcept (← IO.wait task)
    spawnedChild? := some child
    waitForThreadExit tid
    match mode with
    | .direct =>
      let wst ← match ← waitPidEintr child.pid with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"pdeathsig direct waitpid failed: errno={e}")
      spawnedChild? := none
      closeHandleIgnore goW
      let outBytes ← readAllHandle outR
      closeHandleIgnore outR
      return (wst, outBytes)
    | .immortalThread =>
      writeAllHandle goW "G".toUTF8
      closeHandleIgnore goW
      let outBytes ← readAllHandle outR
      closeHandleIgnore outR
      let wst ← match ← waitPidEintr child.pid with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"pdeathsig immortalThread waitpid failed: errno={e}")
      spawnedChild? := none
      return (wst, outBytes)
  finally
    closeHandleIgnore readyR
    closeHandleIgnore readyW
    closeHandleIgnore goR
    closeHandleIgnore goW
    closeHandleIgnore outR
    closeHandleIgnore outW
    closeHandleIgnore errR
    closeHandleIgnore errW
    if let some c := spawnedChild? then
      let _ ← waitPidEintr c.pid

private def runPdeathsigThreadExitDiffTest (trackerRef : IO.Ref CoverageTracker) : IO Unit := do
  let (stDirect, outDirect) ← runOnePdeathsigThreadExitCase .direct
  if stDirect != .signaled 9 || !outDirect.isEmpty then
    throw (IO.userError s!"PDEATHSIG_DIRECT_MISMATCH: expected signaled 9 & empty out, got wait={repr stDirect} out={repr outDirect.toList}")
  let (stImm, outImm) ← runOnePdeathsigThreadExitCase .immortalThread
  if stImm != .exited 0 || outImm != "A".toUTF8 then
    throw (IO.userError s!"PDEATHSIG_IMMORTAL_MISMATCH: expected exited 0 & 'A', got wait={repr stImm} out={repr outImm.toList}")
  recordTracker trackerRef "interface" "forkMode_immortalThread"
  recordTracker trackerRef "interface" "pdeathsig_thread_exit_diff"

private def rawFdNumOrThrow (label : String) (h : RawFd) : IO Int32 := do
  match ← cRawFdNum h with
  | .ok n => pure n
  | .error e => throw (IO.userError s!"{label}: rawfd_num failed errno={e}")

private def rawFdStatOrThrow (label : String) (h : RawFd) : IO (UInt64 × UInt64) := do
  match ← cRawFdFstatDevIno h with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"{label}: rawfd_fstat failed errno={e}")

private def expectInvalidInput {α : Type} (label : String) (res : Except PostForkError α) : IO Unit := do
  match res with
  | .error e =>
    if e.kind != .invalidInput then
      throw (IO.userError s!"{label}: expected invalidInput, got {repr e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invalidInput, got ok")

private def expectSysError {α : Type} (label : String) (expErrno? : Option Errno) (res : Except PostForkError α) : IO Unit := do
  match res with
  | .error e =>
    if e.kind != .sysError then
      throw (IO.userError s!"{label}: expected sysError, got {repr e}")
    if let some exp := expErrno? then
      if e.errno != some exp then
        throw (IO.userError s!"{label}: expected errno={exp}, got {repr e}")
  | .ok _ => throw (IO.userError s!"{label}: expected sysError, got ok")

private def checkSpawnedPgid (step : Nat) (tag : String) (useNewGroup : Bool) (c : SpawnedChild) : IO Unit := do
  let expPgid : Option Pid := if useNewGroup then some c.pid else none
  if c.pgid != expPgid then
    throw (IO.userError s!"step={step} {tag} SpawnedChild.pgid mismatch: got={repr c.pgid} exp={repr expPgid}")

private def checkPendingPgid (step : Nat) (tag : String) (useNewGroup : Bool) (p : PendingChild) : IO Unit := do
  let expPgid : Option Pid := if useNewGroup then some p.pid else none
  if p.pgid != expPgid then
    throw (IO.userError s!"step={step} {tag} PendingChild.pgid mismatch: got={repr p.pgid} exp={repr expPgid}")

private def isZombieStat (statContent : String) : Bool :=
  match statContent.splitOn ") " with
  | [] | [_] => false
  | parts => (parts.getLastD "").startsWith "Z"

private def waitForChildZombie (pid : Pid) : IO Unit := do
  let statPath : System.FilePath := ⟨s!"/proc/{pid}/stat"⟩
  for _ in List.range 200 do
    let s ← try IO.FS.readFile statPath catch _ => pure ""
    if isZombieStat s then
      return
    IO.sleep 1

private def runImmortalSigmaskSmokeTest (sc : FuzzScratch) : IO Unit := do
  for mode in #[ForkMode.direct, ForkMode.immortalThread] do
    let _ ← cRmdirUnlink sc.probeOut 0
    let (inR, inW) ← match ← cHostPipeCloexec with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"immortalSigmask in pipe failed errno={e}")
    let (outR, outW) ← match ← cHostPipeCloexec with
      | .ok p => pure p
      | .error e => closeHandleIgnore inR; closeHandleIgnore inW; throw (IO.userError s!"immortalSigmask out pipe failed errno={e}")
    closeHandleIgnore inW
    try
      let task ← IO.asTask (prio := .dedicated) do
        match ← cSigmaskUsr1 1 with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"immortalSigmask block SIGUSR1 failed errno={e}")
        let mut childPid? : Option Pid := none
        try
          let spec : ChildSpec := {
            path := sc.probeBin
            argv := #[.ofLiteral sc.probeBin]
            env := #[("_PF_PROBE_OUT", sc.probeOut)]
            stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
            fdPolicy := .closeAllAbove2Except #[]
            forkMode := mode
          }
          let child ← match ← LeanSwe.PostFork.spawn spec with
            | .ok c => childPid? := some c.pid; pure c
            | .error e => throw (IO.userError s!"immortalSigmask spawn({repr mode}) failed: {repr e}")
          let wst ← match ← waitPidEintr child.pid with
            | .ok s => pure s
            | .error e => throw (IO.userError s!"immortalSigmask wait({repr mode}) failed errno={e}")
          childPid? := none
          if wst != .exited 0 then
            throw (IO.userError s!"immortalSigmask({repr mode}) unexpected wait={repr wst}")
        finally
          let _ ← cSigmaskUsr1 0
          if let some pid := childPid? then
            let _ ← waitPidEintr pid
      IO.ofExcept (← IO.wait task)
    finally
      closeHandleIgnore inR
      closeHandleIgnore outR
      closeHandleIgnore outW
    let bs ← IO.FS.readBinFile sc.probeOut
    let _ ← cRmdirUnlink sc.probeOut 0
    let dump ← match parseProbeDump? bs with
      | some d => pure d
      | none => throw (IO.userError s!"immortalSigmask({repr mode}) malformed probe dump")
    if (dump.sigBlkBits &&& 0x200) == 0 then
      throw (IO.userError s!"immortalSigmask({repr mode}) failed to inherit blocked SIGUSR1: mask={dump.sigBlkBits}")

private def runInterfaceEpisode
    (step : Nat) (isSmoke : Bool) (rng : Rng) (sc : FuzzScratch) (trackerRef : IO.Ref CoverageTracker) : IO Rng := do
  let _ ← cRmdirUnlink sc.probeOut 0
  let (subRaw, r1) := rng.nextNat 10
  let smokeDet := isSmoke && (step < 3 || step == 10)
  let sub :=
    if isSmoke && step == 10 then 0
    else if isSmoke && step < 10 then step
    else if step < 30 && step % 3 == 0 then step / 3
    else subRaw
  let (useImmortalRaw, r2) := r1.nextBool
  let (useNewGroupRaw, r3) := r2.nextBool
  let (resetSpRaw, r4) := r3.nextBool
  let (closeSrcsRaw, r5) := r4.nextBool
  let (closeAllAbove2Raw, r6) := r5.nextBool
  let useImmortal := if smokeDet then (step == 1 || step == 10) else useImmortalRaw
  let useNewGroup := if smokeDet then (step < 2) else useNewGroupRaw
  let resetSp := if smokeDet then (step == 0 || step == 2) else resetSpRaw
  let closeSrcs := if smokeDet then (step < 2) else closeSrcsRaw
  let closeAllAbove2 := if smokeDet then (step == 0 || step == 10) else closeAllAbove2Raw
  let fMode : ForkMode := if useImmortal then .immortalThread else .direct
  let pgPolicy : ProcessGroupPolicy := if useNewGroup then .newGroup else .inherit
  let spPolicy : SigpipePolicy := if resetSp then .resetDefault else .inherit
  let parentPgrp ← cGetpgrp
  let hostSpDisp ← cGetSigpipeDisp

  let (inR, inW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"step={step} iface in pipe2 failed: errno={e}")
  let (outR, outW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e => closeHandleIgnore inR; closeHandleIgnore inW; throw (IO.userError s!"step={step} iface out pipe2 failed: errno={e}")
  let (errR, errW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e => closeHandleIgnore inR; closeHandleIgnore inW; closeHandleIgnore outR; closeHandleIgnore outW; throw (IO.userError s!"step={step} iface err pipe2 failed: errno={e}")
  let (keepR, keepW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore inR; closeHandleIgnore inW; closeHandleIgnore outR; closeHandleIgnore outW; closeHandleIgnore errR; closeHandleIgnore errW
      throw (IO.userError s!"step={step} iface keep pipe2 failed: errno={e}")
  let (dropR, dropW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore inR; closeHandleIgnore inW; closeHandleIgnore outR; closeHandleIgnore outW; closeHandleIgnore errR; closeHandleIgnore errW; closeHandleIgnore keepR; closeHandleIgnore keepW
      throw (IO.userError s!"step={step} iface drop pipe2 failed: errno={e}")
  let (closedH, closedDummy) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore inR; closeHandleIgnore inW; closeHandleIgnore outR; closeHandleIgnore outW; closeHandleIgnore errR; closeHandleIgnore errW; closeHandleIgnore keepR; closeHandleIgnore keepW; closeHandleIgnore dropR; closeHandleIgnore dropW
      throw (IO.userError s!"step={step} iface closed pipe2 failed: errno={e}")
  let inWNum ← rawFdNumOrThrow "inW" inW
  let keepWNum ← rawFdNumOrThrow "keepW" keepW
  let dropWNum ← rawFdNumOrThrow "dropW" dropW
  let closedNum ← rawFdNumOrThrow "closedH" closedH
  closeHandleIgnore closedH
  closeHandleIgnore closedDummy

  let rawOpenCloseRef ← IO.mkRef (-1 : Int32)
  let unkeptLeakRef ← IO.mkRef (-1 : Int32)
  let childPidRef ← IO.mkRef (none : Option Pid)
  let childBPidRef ← IO.mkRef (none : Option Pid)
  try
    let rawOpenCloseFd ← match ← cMemfd 0 with
      | .ok f => rawOpenCloseRef.set f; pure f
      | .error e => throw (IO.userError s!"step={step} iface rawOpenClose memfd failed: errno={e}")
    let unkeptLeakFd ← match ← cMemfd 0 with
      | .ok f => unkeptLeakRef.set f; pure f
      | .error e => throw (IO.userError s!"step={step} iface unkeptLeak memfd failed: errno={e}")
    let stdinData := s!"iface-{step}".toUTF8
    writeAllHandle inW stdinData
    closeHandleIgnore inW
    closeHandleIgnore keepW
    closeHandleIgnore dropW
    if !closeAllAbove2 then
      let _ ← cRawFdSetfd dropR 0

    let inNum ← rawFdNumOrThrow "inR" inR
    let outNum ← rawFdNumOrThrow "outW" outW
    let errNum ← rawFdNumOrThrow "errW" errW
    let keepNum ← rawFdNumOrThrow "keepR" keepR
    let dropNum ← rawFdNumOrThrow "dropR" dropR
    let (keepDev, keepIno) ← rawFdStatOrThrow "keepR" keepR

    let mkKeepPolicy (keepRef : FdRef RawFd) : FdPolicy RawFd :=
      if closeAllAbove2 then .closeAllAbove2Except #[keepRef] else .inheritNonCloexec #[keepRef]

    let checkProbeCommon (tag : String) (child : SpawnedChild) (expCwd : String)
        (expArgs : Array String) (expEnv : Array String)
        (expectKeepOpen expectDropClosed checkSigpipe checkStdioSrcs expCloseAll : Bool) : IO Unit := do
      let bs ← IO.FS.readBinFile sc.probeOut
      let d ← match parseProbeDump? bs with
        | some x => pure x
        | none => throw (IO.userError s!"step={step} {tag} malformed probe dump")
      if d.stdinBytes != stdinData then
        throw (IO.userError s!"step={step} {tag} stdin mismatch: got={d.stdinBytes.size} exp={stdinData.size}")
      if !expCwd.isEmpty && d.cwd != expCwd then
        throw (IO.userError s!"step={step} {tag} cwd mismatch: got={d.cwd} exp={expCwd}")
      if d.argv != expArgs then
        throw (IO.userError s!"step={step} {tag} argv mismatch: got={repr d.argv} exp={repr expArgs}")
      if d.envp != expEnv then
        throw (IO.userError s!"step={step} {tag} envp mismatch: got={repr d.envp} exp={repr expEnv}")
      let expPgid : Int32 := if useNewGroup then Int32.ofInt (Int.ofNat child.pid.toNat) else parentPgrp
      if d.pgid != expPgid then
        throw (IO.userError s!"step={step} {tag} pgid mismatch: got={d.pgid} exp={expPgid}")
      if checkSigpipe then
        let expSp := if resetSp then (0 : Int32) else hostSpDisp
        if d.sigPipeDisp != expSp then
          throw (IO.userError s!"step={step} {tag} sigpipe disp mismatch: got={d.sigPipeDisp} exp={expSp}")
      if (d.sigBlkBits &&& 0x5a00) != 0 then
        throw (IO.userError s!"step={step} {tag} child blocked signals mask={d.sigBlkBits}")
      if expectKeepOpen then
        match d.openFds.find? (fun x => x.1 == keepNum) with
        | none => throw (IO.userError s!"step={step} {tag} missing keepFd={keepNum}")
        | some (_, fl, dev, ino) =>
          if fl != 0 || dev != keepDev || ino != keepIno then
            throw (IO.userError s!"step={step} {tag} keepFd={keepNum} mismatch: fl={fl} ({dev},{ino}) vs ({keepDev},{keepIno})")
      if expectDropClosed && d.openFds.any (fun x => x.1 == dropNum) then
        throw (IO.userError s!"step={step} {tag} leaked dropFd={dropNum}")
      if expectDropClosed && d.openFds.any (fun x => x.1 == rawOpenCloseFd) then
        throw (IO.userError s!"step={step} {tag} leaked open raw closeFd={rawOpenCloseFd}")
      let leakPresent := d.openFds.any (fun x => x.1 == unkeptLeakFd)
      if expCloseAll && leakPresent then
        throw (IO.userError s!"step={step} {tag} closeAllAbove2Except leaked unkept non-cloexec fd={unkeptLeakFd}")
      if !expCloseAll && !leakPresent then
        throw (IO.userError s!"step={step} {tag} inheritNonCloexec unexpectedly closed unkept non-cloexec fd={unkeptLeakFd}")
      if checkStdioSrcs && !expCloseAll then
        for sfd in #[inNum, outNum, errNum] do
          if sfd >= 3 && sfd != keepNum && sfd != dropNum then
            let present := d.openFds.any (fun x => x.1 == sfd)
            if closeSrcs && present then
              throw (IO.userError s!"step={step} {tag} closeSources=true leaked stdio src fd={sfd}")
            if !closeSrcs && !present then
              throw (IO.userError s!"step={step} {tag} closeSources=false unexpectedly closed non-cloexec stdio src fd={sfd}")

    match sub with
    | 0 | 1 | 2 =>
      let useBarrier := (sub == 1)
      let (cwdOpt, expCwd) := if sub == 0 then (some sc.symDir, sc.symDirResolved) else (some sc.symNestedDotDot, sc.symNestedDotDotResolved)
      if !closeAllAbove2 then
        let _ ← cRawFdSetfd inR 0
        let _ ← cRawFdSetfd outW 0
        let _ ← cRawFdSetfd errW 0
      let argvToks : Array (ArgToken RawFd) := #[
        ArgToken.ofLiteral sc.probeBin,
        ArgToken.ofLiteral "--emit-stdio",
        ArgToken.ofHandle keepR,
        ArgToken.procSelfFd keepR,
        ArgToken.prefixedFd "--fd=" (.handle keepR) ":tail",
        ArgToken.fdDecimal (.raw 1)
      ]
      let expArgv : Array String := #[
        sc.probeBin,
        "--emit-stdio",
        s!"{keepNum}",
        s!"/proc/self/fd/{keepNum}",
        s!"--fd={keepNum}:tail",
        "1"
      ]
      let spec : ChildSpec := {
        path := sc.probeBin
        argv := argvToks
        cwd := cwdOpt
        env := #[("_PF_PROBE_OUT", sc.probeOut), ("PF_IFACE", s!"v{step}")]
        stdio := .redirect (.handle inR) (.handle outW) (.handle errW) closeSrcs
        fdPolicy := mkKeepPolicy (.handle keepR)
        closeFds := #[.handle dropR, .handle closedH, .raw rawOpenCloseFd, .raw inWNum, .raw keepWNum, .raw dropWNum, .raw closedNum]
        processGroup := pgPolicy
        sigpipe := spPolicy
        forkMode := fMode
      }
      if !validateSpec spec then
        throw (IO.userError s!"step={step} validateSpec rejected valid ChildSpec")
      let child ← if useBarrier then
        let pend ← match ← LeanSwe.PostFork.spawnWithBarrier spec with
          | .ok p => pure p
          | .error e => throw (IO.userError s!"step={step} spawnWithBarrier failed: {repr e}")
        checkPendingPgid step "iface_barrier" useNewGroup pend
        if ← System.FilePath.pathExists ⟨sc.probeOut⟩ then
          throw (IO.userError s!"step={step} spawnWithBarrier leaked probeOut before releaseBarrier")
        match ← LeanSwe.PostFork.releaseBarrier pend with
        | .ok c =>
          childPidRef.set (some c.pid)
          checkSpawnedPgid step "iface_release" useNewGroup c
          recordTracker trackerRef "interface" "barrier_release_ok"
          expectSysError "double releaseBarrier" (some Errno.EBADF) (← LeanSwe.PostFork.releaseBarrier pend)
          pure c
        | .error e => throw (IO.userError s!"step={step} releaseBarrier failed: {repr e}")
      else
        match ← LeanSwe.PostFork.spawn spec with
        | .ok c =>
          childPidRef.set (some c.pid)
          checkSpawnedPgid step "iface_spawn" useNewGroup c
          recordTracker trackerRef "interface" "spawn_ok"
          pure c
        | .error e => throw (IO.userError s!"step={step} spawn failed: {repr e}")
      closeHandleIgnore outW
      closeHandleIgnore errW
      let outBs ← readAllHandle outR
      let errBs ← readAllHandle errR
      let wst ← match ← waitPidEintr child.pid with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"step={step} waitOnce failed: errno={e}")
      childPidRef.set none
      if wst != .exited 0 then
        throw (IO.userError s!"step={step} iface child exited with {repr wst}")
      if outBs != "PF-STDOUT\n".toUTF8 || errBs != "PF-STDERR\n".toUTF8 then
        throw (IO.userError s!"step={step} iface stdio mismatch: out={repr outBs.toList} err={repr errBs.toList}")
      checkProbeCommon "iface_ok" child expCwd expArgv #[s!"_PF_PROBE_OUT={sc.probeOut}", s!"PF_IFACE=v{step}"] true true true true closeAllAbove2
      recordTracker trackerRef "interface" "close_sources_and_closed_raw"
      recordTracker trackerRef "interface" "argToken_all"
      if fMode == .immortalThread then
        recordTracker trackerRef "interface" "forkMode_immortalThread"
    | 3 =>
      let spec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin, .ofLiteral "--self-kill"]
        env := #[("_PF_PROBE_OUT", sc.probeOut)]
        processGroup := pgPolicy
        forkMode := fMode
      }
      let child ← match ← LeanSwe.PostFork.spawn spec with
        | .ok c =>
          childPidRef.set (some c.pid)
          checkSpawnedPgid step "self_kill" useNewGroup c
          pure c
        | .error e => throw (IO.userError s!"step={step} self-kill spawn failed: {repr e}")
      let wst ← match ← waitPidEintr child.pid with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"step={step} self-kill wait failed: errno={e}")
      childPidRef.set none
      if wst != .signaled 9 then
        throw (IO.userError s!"step={step} self-kill expected signaled 9, got {repr wst}")
      recordTracker trackerRef "interface" "wifsignaled"
    | 4 =>
      let badStageChdir := (step / 10) % 2 == 0
      let spec : ChildSpec := {
        path := if badStageChdir then sc.probeBin else sc.missingPath
        argv := #[.ofLiteral sc.probeBin]
        cwd := if badStageChdir then some sc.missingPath else none
        forkMode := fMode
      }
      let expStage : FailureStage := if badStageChdir then .chdir else .execve
      match ← LeanSwe.PostFork.spawn spec with
      | .ok _ => throw (IO.userError s!"step={step} expected childFailed for missing path/cwd")
      | .error e =>
        if e.kind != .childFailed || e.errno != some Errno.ENOENT then
          throw (IO.userError s!"step={step} unexpected error for missing path/cwd: {repr e}")
        match e.childFailure with
        | some cf =>
          if cf.stage != expStage || cf.errno != Errno.ENOENT || cf.waitStatus != some (.exited 127) then
            throw (IO.userError s!"step={step} childFailure mismatch: got={repr cf} expStage={repr expStage}")
        | none => throw (IO.userError s!"step={step} missing childFailure on childFailed")
      recordTracker trackerRef "interface" "spawn_childFailed"
    | 5 =>
      let spec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        env := #[("_PF_PROBE_OUT", sc.probeOut)]
        fdPolicy := mkKeepPolicy (.handle keepR)
        processGroup := pgPolicy
        forkMode := fMode
      }
      let pend ← match ← LeanSwe.PostFork.spawnWithBarrier spec with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"step={step} abort spawnWithBarrier failed: {repr e}")
      checkPendingPgid step "abort_barrier" useNewGroup pend
      let out ← match ← LeanSwe.PostFork.abortBarrier pend with
        | .ok o => pure o
        | .error e => throw (IO.userError s!"step={step} abortBarrier failed: {repr e}")
      if out != .aborted (.exited 125) then
        throw (IO.userError s!"step={step} expected aborted 125, got {repr out}")
      if ← System.FilePath.pathExists ⟨sc.probeOut⟩ then
        throw (IO.userError s!"step={step} abortBarrier leaked probeOut")
      expectSysError "double abortBarrier" (some Errno.EBADF) (← LeanSwe.PostFork.abortBarrier pend)
      recordTracker trackerRef "interface" "barrier_abort_125"
    | 6 =>
      let overlapSpec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        fdPolicy := .inheritNonCloexec #[.handle keepR]
        closeFds := #[.handle keepR]
        forkMode := fMode
      }
      let pend ← match ← LeanSwe.PostFork.spawnWithBarrier overlapSpec with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"step={step} overlap spawnWithBarrier failed: {repr e}")
      if (step / 10) % 2 == 0 then
        let out ← match ← LeanSwe.PostFork.abortBarrier pend with
          | .ok o => pure o
          | .error e => throw (IO.userError s!"step={step} overlap abortBarrier failed: {repr e}")
        let expCf : ChildFailure := { stage := .validate, errno := Errno.EINVAL, waitStatus := some (.exited 127) }
        if out != .failedBeforeBarrier expCf (.exited 127) then
          throw (IO.userError s!"step={step} expected failedBeforeBarrier, got {repr out}")
        recordTracker trackerRef "interface" "barrier_failedBefore"
      else
        waitForChildZombie pend.pid
        match ← LeanSwe.PostFork.releaseBarrier pend with
        | .ok _ => throw (IO.userError s!"step={step} overlap releaseBarrier unexpectedly succeeded")
        | .error e =>
          let expCf : ChildFailure := { stage := .validate, errno := Errno.EINVAL, waitStatus := some (.exited 127) }
          if e.kind != .childFailed || e.childFailure != some expCf then
            throw (IO.userError s!"step={step} overlap releaseBarrier mismatch: {repr e}")
        recordTracker trackerRef "interface" "barrier_failedBefore"
    | 7 =>
      let lgRawClose : Array (FdRef RawFd) := Array.ofFn (n := 10) (fun i => .raw (Int32.ofNat (100 + i.val)))
      let lgRawKeepBad : Array (FdRef RawFd) := Array.ofFn (n := 10) (fun i => .raw (Int32.ofNat (if i.val == 9 then 105 else 200 + i.val)))
      let lgRawKeepOk : Array (FdRef RawFd) := Array.ofFn (n := 10) (fun i => .raw (Int32.ofNat (200 + i.val)))
      let badSpecs : Array ChildSpec := #[
        { path := "", argv := #[] },
        { path := "a\x00b", argv := #[] },
        { path := sc.probeBin, argv := #[.lit "x\x00y"] },
        { path := sc.probeBin, argv := #[.fdDecimal (.raw (-1))] },
        { path := sc.probeBin, argv := #[.prefixedFd "p\x00" (.raw 1) "s"] },
        { path := sc.probeBin, argv := #[.prefixedFd "p" (.raw 1) "s\x00"] },
        { path := sc.probeBin, argv := #[.prefixedFd "p" (.raw (-1)) "s"] },
        { path := sc.probeBin, argv := #[], cwd := some "d\x00" },
        { path := sc.probeBin, argv := #[], env := #[("", "1")] },
        { path := sc.probeBin, argv := #[], env := #[("A=B", "1")] },
        { path := sc.probeBin, argv := #[], env := #[("K\x00X", "1")] },
        { path := sc.probeBin, argv := #[], env := #[("K", "V\x00X")] },
        { path := sc.probeBin, argv := #[], closeFds := #[.raw (-1)] },
        { path := sc.probeBin, argv := #[], fdPolicy := .inheritNonCloexec #[.raw (-1)] },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw (-1)) (.raw 1) (.raw 2) true },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw 0) (.raw (-1)) (.raw 2) true },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw 0) (.raw 1) (.raw (-1)) true },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw 0) (.raw 1) (.raw 2) true, fdPolicy := .inheritNonCloexec #[.raw 1] },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw 5) (.raw 1) (.raw 2) true, closeFds := #[.raw 5] },
        { path := sc.probeBin, argv := #[], stdio := .redirect (.raw 5) (.raw 1) (.raw 2) true, fdPolicy := .inheritNonCloexec #[.raw 5] },
        { path := sc.probeBin, argv := #[], closeFds := #[.raw 5], fdPolicy := .closeAllAbove2Except #[.raw 5] },
        { path := sc.probeBin, argv := #[], closeFds := lgRawClose, fdPolicy := .closeAllAbove2Except lgRawKeepBad }
      ]
      for idx in List.range badSpecs.size do
        let bad := badSpecs.getD idx { path := "", argv := #[] }
        if validateSpec bad then
          throw (IO.userError s!"step={step} validateSpec accepted invalid spec idx={idx}")
        expectInvalidInput s!"step={step} spawn invalid idx={idx}" (← LeanSwe.PostFork.spawn bad)
        expectInvalidInput s!"step={step} spawnWithBarrier invalid idx={idx}" (← LeanSwe.PostFork.spawnWithBarrier bad)
      let goodNoCloseSrcs : ChildSpec := {
        path := sc.probeBin, argv := #[], stdio := .redirect (.raw 5) (.raw 1) (.raw 2) false, fdPolicy := .inheritNonCloexec #[.raw 5]
      }
      if !validateSpec goodNoCloseSrcs then
        throw (IO.userError s!"step={step} validateSpec rejected closeSourcesAbove2=false kept stdio source")
      let goodLarge : ChildSpec := {
        path := sc.probeBin, argv := #[], closeFds := lgRawClose, fdPolicy := .closeAllAbove2Except lgRawKeepOk
      }
      if !validateSpec goodLarge then
        throw (IO.userError s!"step={step} validateSpec rejected disjoint >8 spec")
      let lgHandleClose : Array (FdRef Nat) := Array.ofFn (n := 10) (fun i => .handle (10 + i.val))
      let lgHandleKeepBad : Array (FdRef Nat) := Array.ofFn (n := 10) (fun i => .handle (if i.val == 9 then 14 else 50 + i.val))
      let lgHandleKeepOk : Array (FdRef Nat) := Array.ofFn (n := 10) (fun i => .handle (50 + i.val))
      let specHBad : ChildSpecM Nat := { path := sc.probeBin, argv := #[], closeFds := lgHandleClose, fdPolicy := .inheritNonCloexec lgHandleKeepBad }
      let specHOk : ChildSpecM Nat := { path := sc.probeBin, argv := #[], closeFds := lgHandleClose, fdPolicy := .inheritNonCloexec lgHandleKeepOk }
      if validateSpecWith (· == ·) specHBad true then
        throw (IO.userError s!"step={step} validateSpecWith accepted overlapping >8 handle spec")
      if !validateSpecWith (· == ·) specHOk true then
        throw (IO.userError s!"step={step} validateSpecWith rejected disjoint >8 handle spec")
      recordTracker trackerRef "interface" "spawn_invalidInput"
    | 8 =>
      let fModeB : ForkMode :=
        if (step / 10) % 2 == 0 then fMode
        else match fMode with | .direct => .immortalThread | .immortalThread => .direct
      let specA : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        env := #[("_PF_PROBE_OUT", sc.probeOut)]
        stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
        fdPolicy := mkKeepPolicy (.handle keepR)
        closeFds := #[.handle dropR, .handle closedH, .raw rawOpenCloseFd, .raw inWNum, .raw keepWNum, .raw dropWNum, .raw closedNum]
        processGroup := pgPolicy
        sigpipe := spPolicy
        forkMode := fMode
      }
      let specB : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        env := #[("_PF_PROBE_OUT", sc.probeOut)]
        stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
        fdPolicy := .inheritNonCloexec #[.handle keepR]
        closeFds := #[.handle dropR, .raw rawOpenCloseFd]
        processGroup := pgPolicy
        sigpipe := spPolicy
        forkMode := fModeB
      }
      let pendA ← match ← LeanSwe.PostFork.spawnWithBarrier specA with
        | .ok p => childPidRef.set (some p.pid); checkPendingPgid step "multi_A" useNewGroup p; pure p
        | .error e => throw (IO.userError s!"step={step} multi_barrier A spawnWithBarrier failed: {repr e}")
      let pendB ← match ← LeanSwe.PostFork.spawnWithBarrier specB with
        | .ok p => childBPidRef.set (some p.pid); checkPendingPgid step "multi_B" useNewGroup p; pure p
        | .error e =>
          let _ ← LeanSwe.PostFork.abortBarrier pendA
          childPidRef.set none
          throw (IO.userError s!"step={step} multi_barrier B spawnWithBarrier failed: {repr e}")
      if ← System.FilePath.pathExists ⟨sc.probeOut⟩ then
        let _ ← LeanSwe.PostFork.abortBarrier pendA
        let _ ← LeanSwe.PostFork.abortBarrier pendB
        childPidRef.set none; childBPidRef.set none
        throw (IO.userError s!"step={step} multi_barrier leaked probeOut while paused")
      let abortAFirst := (step / 10) % 2 == 0
      let (victim, survivor, isAVictim) :=
        if abortAFirst then (pendA, pendB, true) else (pendB, pendA, false)
      let abortDoneRef ← IO.mkRef false
      let stalledRef ← IO.mkRef false
      let watchdog ← IO.asTask (prio := .default) do
        for _ in List.range 75 do
          if ← abortDoneRef.get then
            return ()
          IO.sleep 10
        stalledRef.set true
        match ← LeanSwe.PostFork.releaseBarrier survivor with
        | .ok _ => pure ()
        | .error _ => pure ()
      let outVRes ← LeanSwe.PostFork.abortBarrier victim
      abortDoneRef.set true
      let _ ← IO.wait watchdog
      if isAVictim then childPidRef.set none else childBPidRef.set none
      if ← stalledRef.get then
        if let some spid ← (if isAVictim then childBPidRef.get else childPidRef.get) then
          let _ ← waitPidEintr spid
          if isAVictim then childBPidRef.set none else childPidRef.set none
        throw (IO.userError s!"step={step} multi_barrier_interleave: abortBarrier stalled while peer paused (pipe FD leak)")
      let outV ← match outVRes with
        | .ok o => pure o
        | .error e =>
          let _ ← LeanSwe.PostFork.abortBarrier survivor
          if isAVictim then childBPidRef.set none else childPidRef.set none
          throw (IO.userError s!"step={step} multi_barrier abortBarrier failed: {repr e}")
      if outV != .aborted (.exited 125) then
        let _ ← LeanSwe.PostFork.abortBarrier survivor
        if isAVictim then childBPidRef.set none else childPidRef.set none
        throw (IO.userError s!"step={step} multi_barrier expected aborted 125, got {repr outV}")
      let childS ← match ← LeanSwe.PostFork.releaseBarrier survivor with
        | .ok c => checkSpawnedPgid step "multi_S" useNewGroup c; pure c
        | .error e =>
          if isAVictim then childBPidRef.set none else childPidRef.set none
          throw (IO.userError s!"step={step} multi_barrier survivor releaseBarrier failed: {repr e}")
      closeHandleIgnore outW
      closeHandleIgnore errW
      let _ ← readAllHandle outR
      let _ ← readAllHandle errR
      let wstS ← match ← waitPidEintr childS.pid with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"step={step} multi_barrier survivor wait failed: errno={e}")
      if isAVictim then childBPidRef.set none else childPidRef.set none
      if wstS != .exited 0 then
        throw (IO.userError s!"step={step} multi_barrier survivor exited with {repr wstS}")
      let survCloseAll := if isAVictim then false else closeAllAbove2
      checkProbeCommon "multi_barrier_ok" childS "" #[sc.probeBin] #[s!"_PF_PROBE_OUT={sc.probeOut}"] true true true false survCloseAll
      recordTracker trackerRef "interface" "barrier_multi_interleave"
    | _ =>
      let closedStdioSpec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        stdio := .redirect (.handle closedH) (.raw 1) (.raw 2) true
      }
      let closedKeepSpec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        fdPolicy := .closeAllAbove2Except #[.handle closedH]
      }
      let closedRawStdioSpec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        stdio := .redirect (.raw 9999) (.raw 1) (.raw 2) true
      }
      let closedRawKeepSpec : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin]
        fdPolicy := .inheritNonCloexec #[.raw 9999]
      }
      expectSysError s!"step={step} spawn closed stdio" (some Errno.EBADF) (← LeanSwe.PostFork.spawn closedStdioSpec)
      expectSysError s!"step={step} spawnWithBarrier closed keep" (some Errno.EBADF) (← LeanSwe.PostFork.spawnWithBarrier closedKeepSpec)
      expectSysError s!"step={step} spawn closed raw stdio" (some Errno.EBADF) (← LeanSwe.PostFork.spawn closedRawStdioSpec)
      expectSysError s!"step={step} spawnWithBarrier closed raw stdio" (some Errno.EBADF) (← LeanSwe.PostFork.spawnWithBarrier closedRawStdioSpec)
      expectSysError s!"step={step} spawn closed raw keep" (some Errno.EBADF) (← LeanSwe.PostFork.spawn closedRawKeepSpec)
      expectSysError s!"step={step} spawnWithBarrier closed raw keep" (some Errno.EBADF) (← LeanSwe.PostFork.spawnWithBarrier closedRawKeepSpec)
      recordTracker trackerRef "interface" "spawn_sysError"
    return r6
  finally
    if let some p ← childPidRef.get then
      let _ ← waitPidEintr p
    if let some pB ← childBPidRef.get then
      let _ ← waitPidEintr pB
    closeIgnore (← rawOpenCloseRef.get)
    closeIgnore (← unkeptLeakRef.get)
    closeHandleIgnore inR
    closeHandleIgnore inW
    closeHandleIgnore outR
    closeHandleIgnore outW
    closeHandleIgnore errR
    closeHandleIgnore errW
    closeHandleIgnore keepR
    closeHandleIgnore keepW
    closeHandleIgnore dropR
    closeHandleIgnore dropW
    let _ ← cRmdirUnlink sc.probeOut 0

private def runProcSelfFdFallbackSmokeTest (trackerRef : IO.Ref CoverageTracker) : IO Unit := do
  let sc ← initScratch 0x504650524f43
  let openedRef ← IO.mkRef (#[] : Array Int32)
  let repRRef ← IO.mkRef (-1 : Int32)
  let repWRef ← IO.mkRef (-1 : Int32)
  let inRRef ← IO.mkRef (-1 : Int32)
  try
    let (r, w) ← match ← cPipe2 1 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"procSelfFd smoke pipe2 failed: errno={e}")
    repRRef.set r
    repWRef.set w
    let (ir, iw) ← match ← cPipe2 1 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"procSelfFd smoke stdin pipe2 failed: errno={e}")
    inRRef.set ir
    closeIgnore iw
    for _ in List.range 32 do
      match ← cMemfd 1 with
      | .ok f => openedRef.modify (·.push f)
      | .error e => throw (IO.userError s!"procSelfFd smoke memfd failed: errno={e}")
    let openedFds ← openedRef.get
    let keepFd := openedFds[openedFds.size / 2]!
    let dropFds := openedFds.filter (· != keepFd)
    let cfgVals : Array Int32 := #[
      0, Int32.ofInt (Int.ofNat Model.FLAG_CLOSE_UNKEPT_ABOVE2.toNat), -1, -1, -1, -1, w, -1, -1,
      ir, 0, -1, 0, -1, 0,
      -1, -1, -1,
      -1, 0, 0, 0, 0
    ]
    let bpfBlob := buildSeccompRetErrnoBpf (cSeccompConst 12) (UInt32.ofNat ENOSYS.val.toNat)
    let childPid ← match ← cForkRun
        (encodeI32ArrayLe cfgVals) (encodeI32ArrayLe #[r]) (encodeI32ArrayLe #[keepFd]) bpfBlob
        none sc.probeBin #[sc.probeBin, "proc-fallback"] #[s!"_PF_PROBE_OUT={sc.probeOut}"] with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"procSelfFd smoke fork failed: errno={e}")
    closeIgnore w
    repWRef.set (-1)
    let repBytes ← readAllFd r
    closeIgnore r
    repRRef.set (-1)
    let waitSt ← waitChildPid childPid
    if waitSt != .exited 0 || !repBytes.isEmpty then
      throw (IO.userError s!"procSelfFd smoke child failed: wait={repr waitSt} rep={repr repBytes.toList}")
    let bs ← IO.FS.readBinFile sc.probeOut
    let dump ← match parseProbeDump? bs with
      | some d => pure d
      | none => throw (IO.userError "procSelfFd smoke malformed probe dump")
    let surviving := dump.openFds.map (·.1)
    if !surviving.contains keepFd then
      throw (IO.userError s!"procSelfFd smoke missing keepFd={keepFd} in {repr surviving}")
    for dfd in dropFds do
      if dfd < 1024 && surviving.contains dfd then
        throw (IO.userError s!"procSelfFd smoke failed to close dropFd={dfd} in {repr surviving}")
    recordTracker trackerRef "close_fds" "proc_self_fd_fallback"
  finally
    closeIgnore (← inRRef.get)
    closeIgnore (← repRRef.get)
    closeIgnore (← repWRef.get)
    (← openedRef.get).forM closeIgnore
    cleanupScratch sc

private def runSeccompCloseEpermSmokeTest (trackerRef : IO.Ref CoverageTracker) : IO Unit := do
  let sc ← initScratch 0x534543434c4f5345
  let repRRef ← IO.mkRef (-1 : Int32)
  let repWRef ← IO.mkRef (-1 : Int32)
  let dropFdRef ← IO.mkRef (-1 : Int32)
  try
    let (r, w) ← match ← cPipe2 1 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"seccomp close EPERM pipe2 failed: errno={e}")
    repRRef.set r
    repWRef.set w
    let dropFd ← match ← cMemfd 1 with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"seccomp close EPERM memfd failed: errno={e}")
    dropFdRef.set dropFd
    let cfgVals : Array Int32 := #[
      0, Int32.ofInt (Int.ofNat Model.FLAG_CLOSE_UNKEPT_ABOVE2.toNat), -1, -1, -1, -1, w, -1, -1,
      -1, 0, -1, 0, -1, 0,
      -1, -1, -1,
      -1, 0, 0, 0, 0
    ]
    let bpfBlob := buildSeccompRetErrnoBpf (cSeccompConst 3) 1
    let childPid ← match ← cForkRun
        (encodeI32ArrayLe cfgVals) (encodeI32ArrayLe #[r]) (encodeI32ArrayLe #[]) bpfBlob
        none sc.probeBin #[sc.probeBin, "seccomp-close"] #[s!"_PF_PROBE_OUT={sc.probeOut}"] with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"seccomp close EPERM fork failed: errno={e}")
    closeIgnore w
    repWRef.set (-1)
    let repBytes ← readAllFd r
    closeIgnore r
    repRRef.set (-1)
    let waitSt ← waitChildPid childPid
    if waitSt != .exited 127 then
      throw (IO.userError s!"seccomp close EPERM expected exit 127 got {repr waitSt}")
    let expWire := encodeFailureReport .closeUnkept Errno.EPERM
    if repBytes != expWire then
      throw (IO.userError s!"seccomp close EPERM report mismatch: got={repr repBytes.toList} exp={repr expWire.toList}")
    if ← System.FilePath.pathExists ⟨sc.probeOut⟩ then
      throw (IO.userError "seccomp close EPERM leaked execution to probeOut")
    recordTracker trackerRef "seccomp" "ret_errno_hit"
    recordTracker trackerRef "run_child" "err.closeUnkept"
  finally
    closeIgnore (← dropFdRef.get)
    closeIgnore (← repRRef.get)
    closeIgnore (← repWRef.get)
    cleanupScratch sc

private def runSigpipeBlockedAndBrokenPipeSmokeTest (trackerRef : IO.Ref CoverageTracker) : IO Unit := do
  let _ ← runSigpipeWriteDiff 0 (Rng.seed 0x53494750) trackerRef
  let cases : Array (UInt32 × UInt32 × UInt32 × ChildWaitStatus) := #[
    (1, 0, 0, .exited 32),
    (0, 0, 1, .exited 32),
    (0, 0, 0, .signaled 13),
    (0, 1, 0, .exited 32)
  ]
  for (pidns, smode, bsp, expSt) in cases do
    let pid ← match ← cSigpipeWriteFork pidns smode bsp with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"sigpipeWriteFork failed errno={e}")
    let st ← waitChildPid pid
    if st != expSt then
      throw (IO.userError s!"sigpipeWrite case=({pidns},{smode},{bsp}) mismatch: got={repr st} exp={repr expSt}")
  let parseHexChar (c : Char) : Option Nat :=
    if '0' ≤ c && c <= '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
    else none
  let parseHex (s : String) : Option Nat :=
    s.trimAscii.toString.toList.foldlM (fun acc c => do
      let d ← parseHexChar c
      return acc * 16 + d) 0
  let flagCombos : Array UInt32 := #[
    Model.FLAG_RESET_SIGPIPE,
    Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_REDIRECT_STDIO,
    Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_HAS_SYNC_BARRIER ||| Model.FLAG_REDIRECT_STDIO ||| Model.FLAG_CLOSE_UNKEPT_ABOVE2,
    Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_CLOSE_UNKEPT_ABOVE2
  ]
  for pfFlags in flagCombos do
    let outRRef ← IO.mkRef (-1 : Int32)
    let outWRef ← IO.mkRef (-1 : Int32)
    let syncRRef ← IO.mkRef (-1 : Int32)
    let syncWRef ← IO.mkRef (-1 : Int32)
    let repRRef ← IO.mkRef (-1 : Int32)
    let repWRef ← IO.mkRef (-1 : Int32)
    let nullFdRef ← IO.mkRef (-1 : Int32)
    try
      let (outR, outW) ← match ← cPipe2 0 with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"sigpipe unblock pipe out failed: errno={e}")
      outRRef.set outR; outWRef.set outW
      let (syncR, syncW) ← match ← cPipe2 1 with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"sigpipe unblock pipe sync failed: errno={e}")
      syncRRef.set syncR; syncWRef.set syncW
      if (pfFlags &&& Model.FLAG_HAS_SYNC_BARRIER) != 0 then
        writeAllFd syncW (ByteArray.mk #[0x53])
      closeIgnore syncW; syncWRef.set (-1)
      let (repR, repW) ← match ← cPipe2 1 with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"sigpipe unblock pipe rep failed: errno={e}")
      repRRef.set repR; repWRef.set repW
      let nullFd ← match ← cMemfd 0 with
        | .ok f => pure f
        | .error e => throw (IO.userError s!"sigpipe unblock memfd failed: errno={e}")
      nullFdRef.set nullFd
      let cfgVals : Array Int32 := #[
        0, Int32.ofInt (Int.ofNat pfFlags.toNat),
        if (pfFlags &&& Model.FLAG_HAS_SYNC_BARRIER) != 0 then syncR else -1,
        nullFd, outW, outW, repW, -1, -1,
        nullFd, 0, outW, 0, outW, 0,
        -1, -1, -1,
        -1, 8, 1, 0, 0
      ]
      let shCmd := "while IFS= read -r l; do case \"$l\" in SigBlk:*|SigIgn:*) printf \"%s \" \"${l#*:}\";; esac; done < /proc/self/status"
      let childPid ← match ← cForkRun
          (encodeI32ArrayLe cfgVals) (encodeI32ArrayLe #[outR, repR]) (encodeI32ArrayLe #[]) ByteArray.empty
          none "/bin/sh" #["/bin/sh", "-c", shCmd] #[] with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"sigpipe unblock fork failed: errno={e}")
      closeIgnore outW; outWRef.set (-1)
      closeIgnore repW; repWRef.set (-1)
      closeIgnore nullFd; nullFdRef.set (-1)
      let repBytes ← readAllFd repR
      let outBytes ← readAllFd outR
      let waitSt ← waitChildPid childPid
      if waitSt != .exited 0 || !repBytes.isEmpty then
        throw (IO.userError s!"sigpipe unblock flags={pfFlags} failed: wait={repr waitSt} rep={repr repBytes.toList}")
      let tokens := (String.fromUTF8! outBytes).trimAscii.toString.splitOn " " |>.filter (fun t => !t.isEmpty)
      match tokens with
      | [blkHex, ignHex] =>
        match parseHex blkHex, parseHex ignHex with
        | some blkMask, some ignMask =>
          if (blkMask &&& (1 <<< 12)) != 0 then
            throw (IO.userError s!"sigpipe unblock flags={pfFlags}: SIGPIPE still blocked SigBlk={blkHex}")
          if (ignMask &&& (1 <<< 12)) != 0 then
            throw (IO.userError s!"sigpipe unblock flags={pfFlags}: SIGPIPE still ignored SigIgn={ignHex}")
        | _, _ => throw (IO.userError s!"sigpipe unblock flags={pfFlags}: bad hex {repr tokens}")
      | _ => throw (IO.userError s!"sigpipe unblock flags={pfFlags}: unexpected status {String.fromUTF8! outBytes}")
    finally
      closeIgnore (← outRRef.get)
      closeIgnore (← outWRef.get)
      closeIgnore (← syncRRef.get)
      closeIgnore (← syncWRef.get)
      closeIgnore (← repRRef.get)
      closeIgnore (← repWRef.get)
      closeIgnore (← nullFdRef.get)

private def runAbiGuardSmokeTest : IO Unit := do
  let expWire := encodeFailureReport .validate Errno.EINVAL
  let expReport (kind : UInt32) (flags : UInt32) : ByteArray :=
    if (flags &&& 1) != 0 || kind != 0 then ByteArray.empty
    else expWire
  let runOne (kind : UInt32) (flags : UInt32) : IO Unit := do
    let rRef ← IO.mkRef (-1 : Int32)
    let wRef ← IO.mkRef (-1 : Int32)
    try
      let (r, w) ← match ← cPipe2 1 with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"abiGuard pipe2 failed: errno={e}")
      rRef.set r
      wRef.set w
      let pid ← match ← cAbiGuardFork kind w.toUInt32 flags with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"abiGuard fork failed: errno={e}")
      closeIgnore w
      wRef.set (-1)
      let rep ← readAllFd r
      closeIgnore r
      rRef.set (-1)
      let st ← waitChildPid pid
      let expSt := if kind != 0 then ChildWaitStatus.exited 0 else ChildWaitStatus.exited 127
      let expRep := expReport kind flags
      if st != expSt || rep != expRep then
        throw (IO.userError s!"abiGuard kind={kind} flags={flags} mismatch: wait={repr st} expWait={repr expSt} rep={repr rep.toList} expRep={repr expRep.toList}")
    finally
      closeIgnore (← rRef.get)
      closeIgnore (← wRef.get)
  let baseFlags : Array UInt32 := #[1, 2, 4, 8, 0x10, 0x20, 0x30, 0x40, 0x80, 0xc0]
  for f in baseFlags do
    runOne 0 f
  for f in (#[0x40, 0x80, 0xc0] : Array UInt32) do
    runOne 1 f

private def safePrintln (msg : String) : IO Unit := do
  try
    let s ← IO.getStdout
    s.putStrLn msg
    s.flush
  catch _ => pure ()

private def runWireDecodeDiffTest : IO Unit := do
  if decodeChildFailure ByteArray.empty != none then
    throw (IO.userError "wireDecodeDiff: empty ByteArray did not return none")
  let stages : Array (FailureStage × UInt8) := #[
    (.validate, 1), (.processGroup, 2), (.signalReset, 3),
    (.fdSetup, 4), (.closeUnkept, 5), (.chdir, 6), (.execve, 7)
  ]
  for (st, tag) in stages do
    for e in (#[1, 2, 5, 9, 13, 22, 38, 4095] : Array UInt32) do
      let u := e.toNat
      let exp := ByteArray.mk #[
        0x50, 0x01, tag, 0x00,
        UInt8.ofNat (u % 256), UInt8.ofNat ((u / 256) % 256),
        UInt8.ofNat ((u / 65536) % 256), UInt8.ofNat ((u / 16777216) % 256)
      ]
      let got := encodeFailureReport st e
      if got != exp then
        throw (IO.userError s!"wireDecodeDiff: encodeFailureReport({repr st}, {e}) mismatch: got={repr got.toList}")
      if decodeChildFailure got != some { stage := st, errno := e, waitStatus := none } then
        throw (IO.userError s!"wireDecodeDiff: roundtrip failed for ({repr st}, {e})")
    for badErr in (#[0, 4096, 0xffffffff] : Array UInt32) do
      let enc := encodeFailureReport st badErr
      if decodeChildFailure enc != some { stage := st, errno := Errno.EIO, waitStatus := none } then
        throw (IO.userError s!"wireDecodeDiff: out-of-range errno {badErr} did not normalize to EIO")
  let expTrunc : Option ChildFailure := some { stage := .wireTruncated, errno := Errno.EIO, waitStatus := none }
  let validBase := ByteArray.mk #[0x50, 0x01, 0x03, 0x00, 0x01, 0x00, 0x00, 0x00]
  for n in ([1, 2, 3, 4, 5, 6, 7] : List Nat) do
    if decodeChildFailure (validBase.extract 0 n) != expTrunc then
      throw (IO.userError s!"wireDecodeDiff: short frame len={n} did not decode to wireTruncated")
  if decodeChildFailure (validBase.push 0x00) != expTrunc then
    throw (IO.userError "wireDecodeDiff: 9-byte frame did not decode to wireTruncated")
  let corruptFrames : Array ByteArray := #[
    ByteArray.mk #[0x51, 0x01, 0x03, 0x00, 0x01, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x02, 0x03, 0x00, 0x01, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x08, 0x00, 0x01, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x03, 0x01, 0x01, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x03, 0x00, 0x00, 0x10, 0x00, 0x00],
    ByteArray.mk #[0x50, 0x01, 0x03, 0x00, 0xff, 0xff, 0xff, 0xff]
  ]
  for cf in corruptFrames do
    if decodeChildFailure cf != expTrunc then
      throw (IO.userError s!"wireDecodeDiff: corrupt frame {repr cf.toList} did not decode to wireTruncated")

private def saveStdioSlot (fd : UInt32) : IO (Int32 × UInt32) := do
  match ← cFcntlGetfd fd with
  | .ok fl =>
    match ← cDupFrom fd 64 1 with
    | .ok dupFd => pure (dupFd, UInt32.ofNat (if (fl &&& 1) != 0 then 1 else 0))
    | .error e => throw (IO.userError s!"closedStdioSmoke: dup slot {fd} failed errno={e}")
  | .error _ => pure (-1, 0)

private def restoreStdioSlot (fd : UInt32) (saved : Int32) (clo : UInt32) : IO Unit := do
  if saved ≥ 0 then
    match ← cDupFrom saved.toUInt32 fd clo with
    | .ok _ => closeIgnore saved
    | .error _ => closeIgnore saved

private def runClosedParentStdioSmokeTest (sc : FuzzScratch) : IO Unit := do
  let _ ← cRmdirUnlink sc.probeOut 0
  let (saved0, clo0) ← saveStdioSlot 0
  let (saved1, clo1) ← saveStdioSlot 1
  let (saved2, clo2) ← saveStdioSlot 2
  let (inR, inW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeIgnore saved0; closeIgnore saved1; closeIgnore saved2
      throw (IO.userError s!"closedStdioSmoke in pipe failed errno={e}")
  let (outR, outW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore inR; closeHandleIgnore inW
      closeIgnore saved0; closeIgnore saved1; closeIgnore saved2
      throw (IO.userError s!"closedStdioSmoke out pipe failed errno={e}")
  let (errR, errW) ← match ← cHostPipeCloexec with
    | .ok p => pure p
    | .error e =>
      closeHandleIgnore inR; closeHandleIgnore inW; closeHandleIgnore outR; closeHandleIgnore outW
      closeIgnore saved0; closeIgnore saved1; closeIgnore saved2
      throw (IO.userError s!"closedStdioSmoke err pipe failed errno={e}")
  let childARef ← IO.mkRef (none : Option Pid)
  let childBRef ← IO.mkRef (none : Option Pid)
  let errRef ← IO.mkRef (none : Option String)
  try
    writeAllHandle inW "closed-stdio-in".toUTF8
    closeHandleIgnore inW
    let _ ← cClose 0
    let _ ← cClose 1
    let _ ← cClose 2
    if (← cFcntlGetfd 0).isOk || (← cFcntlGetfd 1).isOk || (← cFcntlGetfd 2).isOk then
      errRef.set (some "closedStdioSmoke: 0..2 were not closed after cClose")
    else
      let specRedir : ChildSpec := {
        path := sc.probeBin
        argv := #[.ofLiteral sc.probeBin, .ofLiteral "--emit-stdio"]
        env := #[("_PF_PROBE_OUT", sc.probeOut)]
        stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
        fdPolicy := .closeAllAbove2Except #[]
        processGroup := .newGroup
      }
      match ← LeanSwe.PostFork.spawnWithBarrier specRedir with
      | .error e => errRef.set (some s!"closedStdioSmoke spawnWithBarrier(redir) failed: {repr e}")
      | .ok pend =>
        childARef.set (some pend.pid)
        match ← LeanSwe.PostFork.releaseBarrier pend with
        | .error e => errRef.set (some s!"closedStdioSmoke releaseBarrier(redir) failed: {repr e}")
        | .ok childA =>
          closeHandleIgnore outW
          closeHandleIgnore errW
          let outBs ← readAllHandle outR
          let errBs ← readAllHandle errR
          let wstA ← waitPidEintr childA.pid
          childARef.set none
          if wstA != .ok (.exited 0) || outBs != "PF-STDOUT\n".toUTF8 || errBs != "PF-STDERR\n".toUTF8 then
            errRef.set (some s!"closedStdioSmoke redir child mismatch: wait={repr wstA} out={repr outBs.toList} err={repr errBs.toList}")
          else
            let bsA ← IO.FS.readBinFile sc.probeOut
            match parseProbeDump? bsA with
            | none => errRef.set (some "closedStdioSmoke malformed redir probe dump")
            | some dA =>
              if dA.stdinBytes != "closed-stdio-in".toUTF8 || dA.openFds.map (·.1) != #[0, 1, 2] then
                errRef.set (some s!"closedStdioSmoke redir dump mismatch: fds={repr (dA.openFds.map (·.1))}")
      if (← errRef.get).isNone then
        let _ ← cRmdirUnlink sc.probeOut 0
        let specInh : ChildSpec := {
          path := sc.probeBin
          argv := #[.ofLiteral sc.probeBin]
          env := #[("_PF_PROBE_OUT", sc.probeOut)]
          stdio := .inherit
          fdPolicy := .closeAllAbove2Except #[]
        }
        match ← LeanSwe.PostFork.spawn specInh with
        | .error e => errRef.set (some s!"closedStdioSmoke spawn(inherit) failed: {repr e}")
        | .ok childB =>
          childBRef.set (some childB.pid)
          let wstB ← waitPidEintr childB.pid
          childBRef.set none
          if wstB != .ok (.exited 0) then
            errRef.set (some s!"closedStdioSmoke inherit child wait={repr wstB}")
          else
            let bsB ← IO.FS.readBinFile sc.probeOut
            match parseProbeDump? bsB with
            | none => errRef.set (some "closedStdioSmoke malformed inherit probe dump")
            | some dB =>
              if !dB.openFds.isEmpty then
                errRef.set (some s!"closedStdioSmoke inherit leaked openFds={repr (dB.openFds.map (·.1))}")
      if (← errRef.get).isNone then
        let _ ← cRmdirUnlink sc.probeOut 0
        let specAb : ChildSpec := {
          path := sc.probeBin
          argv := #[.ofLiteral sc.probeBin]
          stdio := .inherit
          fdPolicy := .closeAllAbove2Except #[]
        }
        match ← LeanSwe.PostFork.spawnWithBarrier specAb with
        | .error e => errRef.set (some s!"closedStdioSmoke spawnWithBarrier(abort) failed: {repr e}")
        | .ok pendAb =>
          match ← LeanSwe.PostFork.abortBarrier pendAb with
          | .ok (.aborted (.exited 125)) => pure ()
          | other => errRef.set (some s!"closedStdioSmoke abortBarrier unexpected: {repr other}")
  finally
    if let some pA ← childARef.get then
      let _ ← waitPidEintr pA
    if let some pB ← childBRef.get then
      let _ ← waitPidEintr pB
    closeHandleIgnore inR
    closeHandleIgnore inW
    closeHandleIgnore outR
    closeHandleIgnore outW
    closeHandleIgnore errR
    closeHandleIgnore errW
    let _ ← cRmdirUnlink sc.probeOut 0
    let _ ← cClose 0
    let _ ← cClose 1
    let _ ← cClose 2
    restoreStdioSlot 0 saved0 clo0
    restoreStdioSlot 1 saved1 clo1
    restoreStdioSlot 2 saved2 clo2
  if let some msg ← errRef.get then
    throw (IO.userError msg)

private def runPostForkSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let fakeImg : ExecImage := {
    path := [47#u8]
    argv := [bytesOfString "probe"]
    envp := []
    fds := []
    cwd := []
    sig := []
    pgid := 999
  }
  let fakeDump : ProbeDump := {
    pgid := 1
    sigPipeDisp := 0
    sigUsr1Disp := 0
    sigUsr2Disp := 0
    sigBlkBits := 0
    cwd := "/"
    argv := #["probe"]
    envp := #[]
    stdinBytes := ByteArray.empty
    openFds := #[]
  }
  let fakeState : ChildState := { status := .execd fakeImg }
  match compareExecImage 0 "self-test-shrink" true false false 1 1 1 fakeImg fakeState fakeDump [] false #["probe"] with
  | .ok () => throw (IO.userError "POSTFORK_SELF_TEST_FAIL: injected pgid mismatch was not detected")
  | .error _ => pure ()
  let wire := encodeFailureReport .chdir Errno.ENOENT
  if decodeChildFailure wire != some { stage := .chdir, errno := Errno.ENOENT, waitStatus := none } then
    throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: wire roundtrip mismatch for {repr wire.toList}")
  let (inheritedFds, inheritedTracks) ← probeInheritedFds
  let sc ← initScratch seedVal
  try
    let evalRealForkPinProbe (cand : FuzzInput) : IO (Option String) := do
      if cand.closeArr.contains 404 && (cand.pfFlags &&& Model.FLAG_SET_PGID) != 0 &&
          (cand.pfFlags &&& Model.FLAG_CLOSE_UNKEPT_ABOVE2) != 0 &&
          cand.useSetsid && cand.rlimVal == 16 then
        let (repR, repW) ← match ← cPipe2 1 with
          | .ok p => pure p
          | .error e => throw (IO.userError s!"selfTest pipe2 failed: errno={e}")
        try
          let envFlags : Int32 := 1
          let cfgVals : Array Int32 := #[
            0, Int32.ofInt (Int.ofNat cand.pfFlags.toNat),
            -1, 0, 1, 2, repW, -1, -1,
            -1, 0, -1, 0, -1, 0, -1, -1, -1,
            cand.rlimVal, envFlags, 0, 0, 0
          ]
          let pid ← match ← cForkRun (encodeI32ArrayLe cfgVals) (encodeI32ArrayLe cand.closeArr)
              (encodeI32ArrayLe cand.keepArr) ByteArray.empty none "/bin/true" #["/bin/true"] #[] with
            | .ok p => pure p
            | .error e => throw (IO.userError s!"selfTest cForkRun failed: errno={e}")
          closeIgnore repW
          let repBytes ← readAllFd repR
          let wst ← waitChildPid pid
          if wst == .exited 127 then
            if let some cf := decodeChildFailure repBytes then
              if cf.stage == .processGroup then
                return some "PGID_CLOSEABOVE_RLIM"
          return none
        finally
          closeIgnore repR
          closeIgnore repW
      if cand.cwd?.isSome || cand.secTgt == .chdir then
        let (repR, repW) ← match ← cPipe2 1 with
          | .ok p => pure p
          | .error e => throw (IO.userError s!"selfTest decoy pipe2 failed: errno={e}")
        try
          let cfgVals : Array Int32 := #[
            0, 0, -1, 0, 1, 2, repW, -1, -1,
            -1, 0, -1, 0, -1, 0, -1, -1, -1,
            -1, 0, 0, 0, 0
          ]
          let pid ← match ← cForkRun (encodeI32ArrayLe cfgVals) ByteArray.empty ByteArray.empty
              ByteArray.empty (cand.cwd?.orElse fun () => some "/nonexistent_pf_decoy") "/bin/true" #["/bin/true"] #[] with
            | .ok p => pure p
            | .error e => throw (IO.userError s!"selfTest decoy cForkRun failed: errno={e}")
          closeIgnore repW
          let repBytes ← readAllFd repR
          let wst ← waitChildPid pid
          if wst == .exited 127 then
            if let some cf := decodeChildFailure repBytes then
              if cf.stage == .chdir then
                return some "DECOY_CHDIR"
          return none
        finally
          closeIgnore repR
          closeIgnore repW
      return none

    let okInput : FuzzInput := {
      pfFlags := Model.FLAG_RESET_SIGPIPE
      pathStr := sc.probeBin
      argvArr := #[sc.probeBin]
    }
    let bigClose : Array Int32 := Array.ofFn (n := 45) (fun i => Int32.ofNat (400 + i.val))
    let bigKeep : Array Int32 := Array.ofFn (n := 10) (fun i => Int32.ofNat (500 + i.val))
    let bigInput : FuzzInput := {
      pfFlags := Model.FLAG_SET_PGID ||| Model.FLAG_CLOSE_UNKEPT_ABOVE2
      useHighFds := true
      useSetsid := true
      usePidNs := true
      useHideProc := true
      useBlockSigpipe := true
      rlimVal := 16
      repArg := symRepW
      closeArr := bigClose
      keepArr := bigKeep
      cwd? := some "/nonexistent_pf_decoy"
      pathStr := sc.probeBin
      argvArr := #[sc.probeBin, "decoy1", "decoy2"]
      envArr := #["PF_DECOY=1", "PF_DECOY2=2"]
      secTgt := .chdir
      secErrI32 := EPERM
    }
    let decoyOnly : FuzzInput := { bigInput with pfFlags := Model.FLAG_CLOSE_UNKEPT_ABOVE2 }
    if (← evalRealForkPinProbe decoyOnly) != some "DECOY_CHDIR" then
      throw (IO.userError "POSTFORK_SELF_TEST_FAIL: decoy real-fork probe did not return DECOY_CHDIR")
    let mut trace : Array FuzzInput := Array.replicate 200 okInput
    trace := trace.set! 42 decoyOnly
    trace := trace.set! 137 bigInput
    let origClass ← evalRealForkPinProbe bigInput
    if origClass != some "PGID_CLOSEABOVE_RLIM" then
      throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: expected PGID_CLOSEABOVE_RLIM, got {repr origClass}")
    let failsTrace (cand : Array FuzzInput) : IO Bool :=
      cand.anyM fun x => do pure ((← evalRealForkPinProbe x) == origClass)
    let shrunkTrace ← match ← verifyShrinker failsTrace trace 1 with
      | .error msg => throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: trace shrink failed: {msg}")
      | .ok s => pure s
    let shrunkElem ← shrinkElements shrinkFuzzInputOneStep failsTrace shrunkTrace
    let shrunk ← shrinkFailingInput shrunkElem[0]! fun cand => do
      pure ((← evalRealForkPinProbe cand) == origClass)
    if shrunk.closeArr != #[404] || !shrunk.keepArr.isEmpty || shrunk.useHighFds ||
        shrunk.usePidNs || !shrunk.useSetsid || shrunk.useHideProc ||
        shrunk.cwd?.isSome || shrunk.secTgt != .none ||
        fuzzInputWeight shrunk ≥ fuzzInputWeight bigInput then
      throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: real-fork pinned shrink did not minimize (close={repr shrunk.closeArr} keep={repr shrunk.keepArr} weight={fuzzInputWeight shrunk} vs {fuzzInputWeight bigInput})")
    if (← evalRealForkPinProbe shrunk) != origClass then
      throw (IO.userError "POSTFORK_SELF_TEST_FAIL: shrunk element lost pinned mismatch class")

    let execClose : Array Int32 := Array.ofFn (n := 12) (fun i => Int32.ofNat (420 + i.val))
    let bigExecInput : FuzzInput := {
      pfFlags := Model.FLAG_REDIRECT_STDIO ||| Model.FLAG_RESET_SIGPIPE ||| Model.FLAG_SET_PGID ||| Model.FLAG_CLOSE_UNKEPT_ABOVE2
      su1Mode := 1
      stdinArg := 0
      stdoutArg := 2
      stderrArg := 1
      repArg := symRepW
      slot0Src := symInR
      slot1Src := symP1w
      slot2Src := symP2w
      closeArr := execClose
      keepArr := #[symExtraFd, symExtraFd, symExtraFd]
      cwd? := some sc.validDir
      pathStr := sc.probeBin
      argvArr := #[sc.probeBin, "decoy1", "decoy2"]
      envArr := #[s!"_PF_PROBE_OUT={sc.probeOut}", "PF_DECOY=1", "PF_DECOY2=2"]
    }
    let failsPostExec (cand : FuzzInput) : IO Bool := do
      let tRef ← IO.mkRef CoverageTracker.empty
      match ← evalLowLevelCase inheritedFds inheritedTracks 0 sc cand (some tRef) with
      | .ok () =>
        let execHits := (← tRef.get).get "run_child" "ok.execd"
        pure (execHits > 0 && cand.pathStr == sc.probeBin &&
              (cand.pfFlags &&& Model.FLAG_REDIRECT_STDIO) != 0 &&
              cand.stdoutArg == 2 && cand.stderrArg == 1 &&
              cand.slot0Src == symInR && cand.slot1Src == symP1w && cand.slot2Src == symP2w)
      | .error _ => pure false
    if !(← failsPostExec bigExecInput) then
      throw (IO.userError "POSTFORK_SELF_TEST_FAIL: bigExecInput did not trigger post-exec predicate")
    let shrunkExec ← shrinkFailingInput bigExecInput failsPostExec
    if shrunkExec.pfFlags != Model.FLAG_REDIRECT_STDIO ||
        !shrunkExec.closeArr.isEmpty || !shrunkExec.keepArr.isEmpty ||
        !shrunkExec.argvArr.isEmpty || shrunkExec.envArr != #[s!"_PF_PROBE_OUT={sc.probeOut}"] ||
        shrunkExec.cwd?.isSome || shrunkExec.su1Mode != 0 || shrunkExec.repArg != symRepW ||
        fuzzInputWeight shrunkExec ≥ fuzzInputWeight bigExecInput then
      throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: post-exec shrink did not minimize: {repr shrunkExec}")
    match ← evalLowLevelCase inheritedFds inheritedTracks 0 sc { shrunkExec with envArr := #[] } none with
    | .error ("PROBE_DUMP_MISSING", _) => pure ()
    | other => throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: expected PROBE_DUMP_MISSING, got {repr other}")
    if ← System.FilePath.pathExists "_pf_probe.bin" then
      throw (IO.userError "POSTFORK_SELF_TEST_FAIL: evalLowLevelCase leaked _pf_probe.bin into CWD")
    match ← evalLowLevelCase inheritedFds inheritedTracks 0 sc { shrunkExec with cwd? := some sc.validDir, envArr := #[] } none with
    | .error ("PROBE_DUMP_MISSING", _) => pure ()
    | other => throw (IO.userError s!"POSTFORK_SELF_TEST_FAIL: expected PROBE_DUMP_MISSING in validDir, got {repr other}")
    if ← System.FilePath.pathExists ⟨s!"{sc.validDir}/_pf_probe.bin"⟩ then
      let _ ← cRmdirUnlink s!"{sc.validDir}/_pf_probe.bin" 0
      throw (IO.userError "POSTFORK_SELF_TEST_FAIL: evalLowLevelCase leaked _pf_probe.bin into target cwd")
    safePrintln s!"POSTFORK_SHRINK_SELFTEST_OK: trace={trace.size}->{shrunkTrace.size} weight={fuzzInputWeight bigInput}->{fuzzInputWeight shrunk} exec_weight={fuzzInputWeight bigExecInput}->{fuzzInputWeight shrunkExec}"
  finally
    cleanupScratch sc

private def runPostForkSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  let trackerRef ← IO.mkRef CoverageTracker.empty
  runWireDecodeDiffTest
  runAbiGuardSmokeTest
  runProcSelfFdFallbackSmokeTest trackerRef
  runSeccompCloseEpermSmokeTest trackerRef
  runSigpipeBlockedAndBrokenPipeSmokeTest trackerRef
  runPdeathsigThreadExitDiffTest trackerRef
  let sc ← initScratch seedVal
  try
    runImmortalSigmaskSmokeTest sc
    runClosedParentStdioSmokeTest sc
    let (inheritedFds, inheritedTracks) ← probeInheritedFds
    let mut rng := Rng.seed seedVal
    for step in List.range steps do
      rng ← fuzzLowLevelEpisode inheritedFds inheritedTracks step steps isSmoke rng sc trackerRef
      if isSmoke || step % 3 == 0 then
        rng ← runInterfaceEpisode step isSmoke rng sc trackerRef
    let tracker ← trackerRef.get
    if isSmoke || steps >= 1000 then
      assertCoverage "postfork" tracker requiredBuckets
    safePrintln (tracker.formatReport "postfork")
    safePrintln s!"FUZZ_SUMMARY suite=postfork steps={steps} seed={seedVal}"
    cleanupScratch sc
  catch err =>
    cleanupScratch sc
    throw err

/-- Differential fuzzing suite for `LeanSwe.PostFork` (`postfork.child.run_child`, `close_fds_above2_except`, `spawn`, `spawnWithBarrier`, `releaseBarrier`, `abortBarrier`, `ArgToken`, and `ForkMode`). -/
def suite : FuzzSuite := {
  «name» := "postfork"
  description := "Differential fuzzer for PostFork child pipeline, host orchestrator, ArgToken, and ForkMode against Linux"
  runSmoke := fun cfg =>
    runPostForkSuite (min cfg.steps 200) cfg.seed true
  runFuzz := fun cfg =>
    runPostForkSuite cfg.steps cfg.seed false
  selfTestShrink := runPostForkSelfTestShrink
}

end Fuzz.PostFork
