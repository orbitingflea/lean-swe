import LeanSwe.LinuxSyscall.Sandbox.Interface
import LeanSwe.LinuxSyscall.Sandbox.Model
import LeanSwe.LinuxSyscall.Fuzz.Rng
import LeanSwe.LinuxSyscall.Fuzz.SandboxEnv

namespace LeanSwe.LinuxSyscall.Fuzz.SandboxFuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Sandbox
open LeanSwe.LinuxSyscall.Fuzz

private local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray[{b.size}]"

/-- Configuration options for running the `Sandbox` world-model fuzzer. -/
structure FuzzConfig where
  /-- Initial SplitMix64 seed. -/
  seed : UInt64 := 0x517cc1b727220a95
  /-- Total real syscalls to execute across forked episodes. -/
  steps : Nat := 1000000
  /-- Target number of syscalls attempted per forked episode child. -/
  stepsPerEpisode : Nat := 100
  /-- Print per-`(syscall × outcome)` hit matrix summary. -/
  printMatrix : Bool := true
  /-- Run self-test verifying greedy delta-shrinking against an injected oracle fault. -/
  selfTestShrink : Bool := false
  deriving Repr

private inductive HandleChoice where
  | hostDir (idx : Nat)
  | hostFile (idx : Nat)
  | pseudo (idx : Nat)
  | opathMemfd
  | opathRuleset
  | dynamic (idx : Nat)
  | closed (idx : Nat)
  | unmapped
  deriving Repr, DecidableEq, BEq

private inductive FuzzStep where
  | llCreate (attr? : Option LandlockRulesetAttr) (flags : UInt32)
  | llAddPath (rs : HandleChoice) (parent : HandleChoice) (access : UInt64)
  | llAddNet (rs : HandleChoice) (port : UInt64) (access : UInt64)
  | llRestrict (rs : HandleChoice)
  | scGetAvail (action : UInt32) (flags : SeccompFlags)
  | scSetFilter (flags : SeccompFlags) (filterBytes : ByteArray)
  | doPrctl (op : PrctlOp)
  | doSetrlimit (res : RlimitResource) (cur : UInt64) (max : UInt64)
  | doMemfd (name : ByteArray) (flags : MemfdFlags)
  | closeDyn (idx : Nat)
  deriving Repr, DecidableEq, BEq

private structure EpisodePlan where
  useUserns : Bool
  preNnp : Bool
  preOuterLayers : Nat
  preOuterSeccomp : Bool
  spawnMode : Nat
  closeLowFds : Bool
  dirOPaths : Array Bool
  fileOPaths : Array Bool
  pseudoOPaths : Array Bool
  seedOPathSpecials : Bool
  specialSeedIdx : Nat
  steps : Array FuzzStep
  deriving Repr

private structure EpisodeResult where
  executed : Nat
  hits : Array (String × Nat)
  mismatch? : Option (Nat × String)
  deriving Repr

private def encodeFilter (insns : List SockFilterInsn) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    for i in insns do
      out := out.push (UInt8.ofNat (i.code.toNat % 256))
      out := out.push (UInt8.ofNat ((i.code.toNat / 256) % 256))
      out := out.push i.jt
      out := out.push i.jf
      out := out.push (UInt8.ofNat (i.k.toNat % 256))
      out := out.push (UInt8.ofNat ((i.k.toNat / 256) % 256))
      out := out.push (UInt8.ofNat ((i.k.toNat / 65536) % 256))
      out := out.push (UInt8.ofNat ((i.k.toNat / 16777216) % 256))
    return out

private def genHandleChoice (r : Rng) : HandleChoice × Rng :=
  let (kind, r1) := r.nextNat 12
  let (idx, r2) := r1.nextNat 8
  if kind < 3 then (.dynamic idx, r2)
  else if kind < 5 then (.hostDir idx, r2)
  else if kind < 7 then (.hostFile idx, r2)
  else if kind == 7 then (.pseudo idx, r2)
  else if kind == 8 then (.opathMemfd, r2)
  else if kind == 9 then (.opathRuleset, r2)
  else if kind == 10 then (.closed idx, r2)
  else (.unmapped, r2)

private def fsMaskPool : Array UInt64 := #[
  0,
  LANDLOCK_ACCESS_FS_EXECUTE,
  LANDLOCK_ACCESS_FS_WRITE_FILE,
  LANDLOCK_ACCESS_FS_READ_FILE,
  LANDLOCK_ACCESS_FS_READ_DIR,
  (1 : UInt64) <<< 14,
  (1 : UInt64) <<< 15,
  LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR,
  LANDLOCK_ACCESS_FS_EXECUTE ||| LANDLOCK_ACCESS_FS_READ_FILE ||| LANDLOCK_ACCESS_FS_READ_DIR,
  LANDLOCK_ACCESS_FS_V4_ALL,
  LANDLOCK_ACCESS_FS_IOCTL_DEV,
  LANDLOCK_ACCESS_FS_RESOLVE_UNIX,
  (1 : UInt64) <<< 17,
  (1 : UInt64) <<< 20,
  (1 : UInt64) <<< 60
]

private def netMaskPool : Array UInt64 := #[
  0,
  LANDLOCK_ACCESS_NET_BIND_TCP,
  LANDLOCK_ACCESS_NET_CONNECT_TCP,
  LANDLOCK_ACCESS_NET_ALL,
  4,
  (1 : UInt64) <<< 10
]

private def genFsMask (r : Rng) : UInt64 × Rng :=
  let (mode, r1) := r.nextNat 8
  if mode < 6 then
    r1.pickArray fsMaskPool LANDLOCK_ACCESS_FS_EXECUTE
  else
    r1.nextU64

private def genNetMask (r : Rng) : UInt64 × Rng :=
  let (mode, r1) := r.nextNat 8
  if mode < 6 then
    r1.pickArray netMaskPool LANDLOCK_ACCESS_NET_CONNECT_TCP
  else
    r1.nextU64

private def genSeccompFlags (r : Rng) : SeccompFlags × Rng :=
  let (b0, r1) := r.chance 1 3
  let (b1, r2) := r1.chance 1 3
  let (b2, r3) := r2.chance 1 4
  let (b3, r4) := r3.chance 1 3
  ({ tsync := b0, log := b1, specAllow := b2, tsyncEsrch := b3 }, r4)

private def genRandomBytes (r : Rng) (len : Nat) : ByteArray × Rng :=
  Id.run do
    let mut cur := r
    let mut out := ByteArray.empty
    for _ in List.range len do
      let (v, nxt) := cur.nextNat 256
      out := out.push (UInt8.ofNat v)
      cur := nxt
    return (out, cur)

private def seccompErrnoPool : Array UInt32 := #[
  Errno.EPERM,
  Errno.EACCES,
  Errno.E2BIG,
  Errno.EBADF,
  Errno.ENOSYS,
  4095,
  4096,
  5000,
  0xFFFF
]

private def seccompRetPool : Array UInt32 := #[
  SECCOMP_RET_ALLOW,
  SECCOMP_RET_ALLOW ||| 0x42,
  SECCOMP_RET_LOG,
  SECCOMP_RET_LOG ||| 0x17,
  SECCOMP_RET_ERRNO ||| Errno.EPERM,
  SECCOMP_RET_ERRNO ||| Errno.EACCES,
  SECCOMP_RET_ERRNO ||| Errno.E2BIG,
  SECCOMP_RET_ERRNO ||| Errno.EBADF,
  SECCOMP_RET_ERRNO ||| Errno.ENOSYS,
  SECCOMP_RET_ERRNO ||| 4095,
  SECCOMP_RET_ERRNO ||| 4096,
  SECCOMP_RET_ERRNO ||| 5000,
  SECCOMP_RET_ERRNO ||| 0xFFFF,
  SECCOMP_RET_ERRNO,
  SECCOMP_RET_ERRNO ||| Errno.EFAULT,
  SECCOMP_RET_KILL_PROCESS,
  SECCOMP_RET_KILL_THREAD,
  SECCOMP_RET_TRAP,
  SECCOMP_RET_TRACE ||| 5,
  SECCOMP_RET_USER_NOTIF,
  0x12340000
]

private def sandboxSyscallNrs : Array UInt32 := #[
  444, 445, 446, 317, 277, 157, 167, 160, 163, 164, 261, 302, 319, 279
]

private def simpleBpfOps : Array UInt16 := #[
  0x0000, 0x0001, 0x0080, 0x0081, 0x0007, 0x0087,
  0x0004, 0x000c, 0x0014, 0x001c, 0x0024, 0x002c,
  0x0044, 0x004c, 0x0054, 0x005c, 0x006c, 0x007c,
  0x0084, 0x00a4, 0x00ac
]

private def condJmpOps : Array UInt16 := #[
  0x0015, 0x001d, 0x0025, 0x002d, 0x0035, 0x003d, 0x0045, 0x004d
]

private def genFullCbpfDag (r : Rng) (allowSelectErr : Bool) : ByteArray × Rng :=
  Id.run do
    let mut cur := r
    let (longMode, rLenMode) := cur.chance 1 5
    cur := rLenMode
    let (nBody, r1) := if longMode then cur.nextRange 60 159 else cur.nextRange 1 18
    cur := r1
    let (useSelector, r2) := cur.chance 1 3
    cur := r2
    let (retAction, r3) := cur.pickArray #[SECCOMP_RET_ALLOW, SECCOMP_RET_LOG] SECCOMP_RET_ALLOW
    cur := r3
    if useSelector && allowSelectErr then
      let (targetNr, r4) := cur.pickArray sandboxSyscallNrs 446
      let (argMode, r5) := r4.chance 1 2
      let (errVal, r6) := r5.pickArray seccompErrnoPool Errno.EPERM
      let (argCmpVal, r7) := r6.nextNat 4
      cur := r7
      let checkArg : List SockFilterInsn :=
        if argMode then
          [ { code := 0x0020, jt := 0, jf := 0, k := 16 }
          , { code := 0x0015, jt := 0, jf := 1, k := UInt32.ofNat argCmpVal }
          , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| errVal } ]
        else
          [ { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| errVal } ]
      let prog : List SockFilterInsn :=
        [ { code := 0x0020, jt := 0, jf := 0, k := 0 }
        , { code := 0x0015, jt := 0, jf := UInt8.ofNat checkArg.length, k := targetNr } ] ++
        checkArg ++
        [ { code := 0x0006, jt := 0, jf := 0, k := retAction } ]
      return (encodeFilter prog, cur)
    let totalLen := nBody + 1
    let mut pathMasks : Array UInt32 := Array.replicate totalLen (0xFFFF : UInt32)
    let mut curMask : UInt32 := 0
    let mut insns : List SockFilterInsn := []
    for idx in List.range nBody do
      let rem := nBody - 1 - idx
      let effMask := curMask &&& (pathMasks.getD idx 0xFFFF)
      let (cat, nxt) := cur.nextNat 16
      cur := nxt
      if cat < 5 then
        let (op, nxt2) := cur.pickArray simpleBpfOps 0x0000
        let (imm, nxt3) := nxt2.nextNat 128
        cur := nxt3
        insns := insns ++ [{ code := op, jt := 0, jf := 0, k := UInt32.ofNat imm }]
        curMask := effMask
      else if cat < 7 then
        let (offIdx, nxt2) := cur.nextRange 0 15
        cur := nxt2
        insns := insns ++ [{ code := 0x0020, jt := 0, jf := 0, k := UInt32.ofNat (offIdx * 4) }]
        curMask := effMask
      else if cat == 7 then
        let (divVal, nxt2) := cur.nextRange 1 16
        cur := nxt2
        insns := insns ++ [{ code := 0x0034, jt := 0, jf := 0, k := UInt32.ofNat divVal }]
        curMask := effMask
      else if cat == 8 then
        let (shOp, nxt2) := cur.pickArray #[0x0064, 0x0074] 0x0064
        let (shAmt, nxt3) := nxt2.nextNat 32
        cur := nxt3
        insns := insns ++ [{ code := shOp, jt := 0, jf := 0, k := UInt32.ofNat shAmt }]
        curMask := effMask
      else if cat < 11 then
        let (stOp, nxt2) := cur.pickArray #[0x0002, 0x0003] 0x0002
        let (slot, nxt3) := nxt2.nextNat 16
        cur := nxt3
        insns := insns ++ [{ code := stOp, jt := 0, jf := 0, k := UInt32.ofNat slot }]
        curMask := effMask ||| ((1 : UInt32) <<< UInt32.ofNat slot)
      else if cat == 11 && effMask != 0 then
        let (ldOp, nxt2) := cur.pickArray #[0x0060, 0x0061] 0x0060
        let (startSlot, nxt3) := nxt2.nextNat 16
        cur := nxt3
        let mut chosenSlot := 0
        for off in List.range 16 do
          let cand := (startSlot + off) % 16
          if (effMask &&& ((1 : UInt32) <<< UInt32.ofNat cand)) != 0 then
            chosenSlot := cand
            break
        insns := insns ++ [{ code := ldOp, jt := 0, jf := 0, k := UInt32.ofNat chosenSlot }]
        curMask := effMask
      else if cat == 12 && rem > 0 then
        let (kOff, nxt2) := cur.nextNat rem
        cur := nxt2
        let tgt := idx + 1 + kOff
        pathMasks := pathMasks.set! tgt ((pathMasks.getD tgt 0xFFFF) &&& effMask)
        insns := insns ++ [{ code := 0x0005, jt := 0, jf := 0, k := UInt32.ofNat kOff }]
        curMask := 0xFFFF
      else if cat < 15 && rem > 0 then
        let (jmpOp, nxt2) := cur.pickArray condJmpOps 0x0015
        let (jtOff, nxt3) := nxt2.nextNat rem
        let (jfOff, nxt4) := nxt3.nextNat rem
        let (kVal, nxt5) := nxt4.nextNat 16
        cur := nxt5
        let t1 := idx + 1 + jtOff
        let t2 := idx + 1 + jfOff
        pathMasks := pathMasks.set! t1 ((pathMasks.getD t1 0xFFFF) &&& effMask)
        pathMasks := pathMasks.set! t2 ((pathMasks.getD t2 0xFFFF) &&& effMask)
        insns := insns ++ [{ code := jmpOp, jt := UInt8.ofNat jtOff, jf := UInt8.ofNat jfOff, k := UInt32.ofNat kVal }]
        curMask := 0xFFFF
      else
        let (midAct, nxt2) := cur.pickArray #[SECCOMP_RET_ALLOW, SECCOMP_RET_LOG] SECCOMP_RET_ALLOW
        cur := nxt2
        insns := insns ++ [{ code := 0x0006, jt := 0, jf := 0, k := midAct }]
        curMask := effMask
    insns := insns ++ [{ code := 0x0006, jt := 0, jf := 0, k := retAction }]
    return (encodeFilter insns, cur)

private def genAdvSeccompFilter (r : Rng) (allowSelectErr : Bool) : ByteArray × Rng :=
  let (advKind, r1) := r.nextNat 14
  let (retK, r2) := r1.pickArray seccompRetPool SECCOMP_RET_ALLOW
  if advKind == 0 then
    let act := retK &&& SECCOMP_RET_ACTION_FULL
    let isNonBlocking := act == SECCOMP_RET_ERRNO && (retK &&& 0xFFFF) != 0 && (retK &&& 0xFFFF) != Errno.EFAULT
    let isExternalTrap := act == SECCOMP_RET_TRACE || act == SECCOMP_RET_USER_NOTIF
    if isNonBlocking || isExternalTrap then
      if allowSelectErr then
        let (targetNr, r3) := r2.pickArray sandboxSyscallNrs 446
        (encodeFilter
          [ { code := 0x0020, jt := 0, jf := 0, k := 0 }
          , { code := 0x0015, jt := 1, jf := 0, k := targetNr }
          , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }
          , { code := 0x0006, jt := 0, jf := 0, k := retK } ], r3)
      else
        (encodeFilter [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
    else
      (encodeFilter [{ code := 0x0006, jt := 0, jf := 0, k := retK }], r2)
  else if advKind == 1 then
    (encodeFilter [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 2 then
    (encodeFilter [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 3 then
    (encodeFilter [{ code := 0x0000, jt := 0, jf := 0, k := 0 }], r2)
  else if advKind == 4 then
    (encodeFilter [{ code := 0x0020, jt := 0, jf := 0, k := 64 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 5 then
    (encodeFilter [{ code := 0x0020, jt := 0, jf := 0, k := 2 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 6 then
    (encodeFilter [{ code := 0x0060, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 7 then
    (encodeFilter [{ code := 0x0002, jt := 0, jf := 0, k := 16 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 8 then
    (encodeFilter [{ code := 0x0034, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 9 then
    (encodeFilter [{ code := 0x0064, jt := 0, jf := 0, k := 32 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 10 then
    (encodeFilter [{ code := 0x0074, jt := 0, jf := 0, k := 32 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 11 then
    (encodeFilter [{ code := 0x0005, jt := 0, jf := 0, k := 2 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else if advKind == 12 then
    (encodeFilter [{ code := 0x0015, jt := 2, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }], r2)
  else
    let oversized := (List.replicate 160 { code := 0x0000, jt := 0, jf := 0, k := 0 }) ++
      [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]
    (encodeFilter oversized, r2)

private def genFilterBytes (r : Rng) (allowSelectErr : Bool) : ByteArray × Rng :=
  let (kind, r1) := r.nextNat 10
  if kind < 2 then
    let (lenChoice, r2) := r1.nextNat 5
    let (len, r3) :=
      if lenChoice == 0 then (0, r2)
      else if lenChoice == 1 then (7, r2)
      else if lenChoice == 2 then (1288, r2)
      else r2.nextRange 1 80
    genRandomBytes r3 len
  else if kind < 5 then
    genAdvSeccompFilter r1 allowSelectErr
  else
    genFullCbpfDag r1 allowSelectErr

private def rlimitVals : Array UInt64 := #[
  0, 1, 2, 3, 4, 7, 15, 16, 64, 512, 1024, 2048, 4096, 65536, 131072,
  1048576, NOFILE_KERNEL_MAX, NOFILE_KERNEL_MAX + 1, RLIM_INFINITY
]

private def memfdNameLens : Array Nat := #[0, 1, 248, 249, 250, 512]

private def genMemfdName (r : Rng) : ByteArray × Rng :=
  let (kind, r1) := r.nextNat 8
  if kind < 4 then
    let (len, r2) := r1.pickArray memfdNameLens 1
    genRandomBytes r2 len
  else if kind == 4 then
    let (preLen, r2) := r1.nextRange 0 8
    let (pre, r3) := genRandomBytes r2 preLen
    (pre.push 0 |>.push 97, r3)
  else
    let (len, r2) := r1.nextRange 1 24
    Id.run do
      let mut cur := r2
      let mut out := ByteArray.empty
      for _ in List.range len do
        let (c, nxt) := cur.nextRange 97 122
        out := out.push (UInt8.ofNat c)
        cur := nxt
      return (out, cur)

private def netPortPool : Array UInt64 := #[
  0, 1, 80, 443, 65535, 65536, 100000, 0x100000001, UInt64.ofNat 0xFFFFFFFFFFFFFFFF
]

private def genStep (r : Rng) (llBurst : Bool) (allowSelectErr : Bool) : FuzzStep × Rng :=
  let (opRaw, r1) := r.nextNat 12
  let opKind :=
    if llBurst && opRaw >= 6 && opRaw <= 8 then
      if opRaw == 6 then 0 else 3
    else if opRaw >= 10 then
      if opRaw == 10 then 7 else 9
    else
      opRaw
  if opKind == 0 then
    let (useNull, r2) := r1.chance 1 4
    if useNull then
      let (fl, r3) := r2.pickArray #[0, 1, 2, 3, 7] 1
      (.llCreate none fl, r3)
    else
      let (fs, r3) := genFsMask r2
      let (net, r4) := genNetMask r3
      let (fl, r5) := r4.pickArray #[0, 0, 0, 1, 2] 0
      (.llCreate (some { handledAccessFs := fs, handledAccessNet := net }) fl, r5)
  else if opKind == 1 then
    let (rs, r2) := genHandleChoice r1
    let (parent, r3) := genHandleChoice r2
    let (acc, r4) := genFsMask r3
    (.llAddPath rs parent acc, r4)
  else if opKind == 2 then
    let (rs, r2) := genHandleChoice r1
    let (port, r3) := r2.pickArray netPortPool 80
    let (acc, r4) := genNetMask r3
    (.llAddNet rs port acc, r4)
  else if opKind == 3 then
    let (rs, r2) := genHandleChoice r1
    (.llRestrict rs, r2)
  else if opKind == 4 then
    let (sub, r2) := r1.chance 1 3
    let (fl, r3) := genSeccompFlags r2
    if sub then
      let (act, r4) := r3.pickArray seccompRetPool SECCOMP_RET_ALLOW
      (.scGetAvail act fl, r4)
    else
      let (bs, r4) := genFilterBytes r3 allowSelectErr
      (.scSetFilter fl bs, r4)
  else if opKind == 5 then
    let (pk, r2) := r1.nextNat 6
    if pk == 0 then (.doPrctl .getNoNewPrivs, r2)
    else if pk == 1 then (.doPrctl .setNoNewPrivs, r2)
    else if pk == 2 then (.doPrctl (.setChildSubreaper true), r2)
    else if pk == 3 then (.doPrctl (.setChildSubreaper false), r2)
    else
      let (sig, r3) := r2.pickArray #[0, 1, 9, 15, 64, 65, 100] 9
      (.doPrctl (.setPdeathsig sig), r3)
  else if opKind == 6 then
    let (res, r2) := r1.pickArray #[RlimitResource.core, RlimitResource.fsize, RlimitResource.nofile] RlimitResource.fsize
    let (cur, r3) := r2.pickArray rlimitVals 512
    let (maxV, r4) := r3.pickArray rlimitVals 1024
    (.doSetrlimit res cur maxV, r4)
  else if opKind == 7 || opKind == 8 then
    let (name, r2) := genMemfdName r1
    let (b0, r3) := r2.chance 3 4
    let (b1, r4) := r3.chance 1 2
    let (b2, r5) := r4.chance 1 3
    let (b3, r6) := r5.chance 1 4
    (.doMemfd name { cloexec := b0, allowSealing := b1, noexecSeal := b2, exec := b3 }, r6)
  else
    let (idx, r2) := r1.nextNat 8
    (.closeDyn idx, r2)

private def genEpisodePlan (r : Rng) (nSteps : Nat) : EpisodePlan × Rng :=
  Id.run do
    let (useUserns, r1) := r.chance 1 5
    let (preNnp, r2) := r1.chance 1 5
    let (hasOuterLayers, r3) := r2.chance 1 5
    let (outerLayersRaw, r4) := r3.nextRange 1 16
    let preOuterLayers := if hasOuterLayers then outerLayersRaw else 0
    let (preOuterSeccomp, r5) := r4.chance 1 10
    let (spawnRoll, r6) := r5.nextNat 8
    let spawnMode := if spawnRoll == 0 then 1 else if spawnRoll == 1 then 2 else 0
    let (closeLowFds, r7) := r6.chance 1 5
    let (seedOPathSpecials, r8) := r7.chance 1 3
    let (specialSeedIdx, r9) := r8.nextNat 64
    let (llBurst, r10) := r9.chance 1 5
    let (allowLateSeccompErr, r11) := r10.chance 1 4
    let mut cur := r11
    let mut dirOPaths := #[]
    let mut fileOPaths := #[]
    let mut pseudoOPaths := #[]
    for _ in List.range 2 do
      let (b1, c1) := cur.chance 1 2
      let (b2, c2) := c1.chance 1 2
      let (b3, c3) := c2.chance 1 2
      dirOPaths := dirOPaths.push b1
      fileOPaths := fileOPaths.push b2
      pseudoOPaths := pseudoOPaths.push b3
      cur := c3
    let lateThreshold := (nSteps * 3) / 4
    let mut steps := Array.mkEmpty nSteps
    for i in List.range nSteps do
      let allowErrHere := allowLateSeccompErr && i >= lateThreshold
      let (st, nxt) := genStep cur llBurst allowErrHere
      steps := steps.push st
      cur := nxt
    return ({
      useUserns, preNnp, preOuterLayers, preOuterSeccomp, spawnMode,
      closeLowFds, dirOPaths, fileOPaths, pseudoOPaths,
      seedOPathSpecials, specialSeedIdx, steps
    }, cur)

private structure HandleSlot where
  hid : HandleId
  fd : RawFd

private structure ExecState where
  sys : SandboxSysState
  nextHid : HandleId
  hostDirs : Array HandleSlot
  hostFiles : Array HandleSlot
  pseudos : Array HandleSlot
  opathMemfd? : Option HandleSlot
  opathRuleset? : Option HandleSlot
  dynamics : Array HandleSlot
  closedHids : Array HandleSlot
  deadFd : RawFd

private def pickSlot (slots : Array HandleSlot) (idx : Nat) (fallback : RawFd) : HandleId × RawFd :=
  if slots.isEmpty then
    (9999, fallback)
  else
    let s := slots.getD (idx % slots.size) { hid := 9999, fd := fallback }
    (s.hid, s.fd)

private def resolveChoice (st : ExecState) : HandleChoice → HandleId × RawFd
  | .hostDir i => pickSlot st.hostDirs i st.deadFd
  | .hostFile i => pickSlot st.hostFiles i st.deadFd
  | .pseudo i => pickSlot st.pseudos i st.deadFd
  | .opathMemfd =>
    match st.opathMemfd? with
    | some s => (s.hid, s.fd)
    | none => (9999, st.deadFd)
  | .opathRuleset =>
    match st.opathRuleset? with
    | some s => (s.hid, s.fd)
    | none => (9999, st.deadFd)
  | .dynamic i => pickSlot st.dynamics i st.deadFd
  | .closed i => pickSlot st.closedHids i st.deadFd
  | .unmapped => (99999, st.deadFd)

private def outcomeTag : SandboxOutcome → String
  | .landlockVersion _ => "ok.version"
  | .opened _ => "ok.fd"
  | .unit => "ok.unit"
  | .u32 _ => "ok.u32"
  | .err e => s!"err.{e}"

private def reqTag : SandboxReq → String
  | .landlockCreateRuleset _ _ => "landlock_create_ruleset"
  | .landlockAddRule _ (.pathBeneath _ _) => "landlock_add_rule.path"
  | .landlockAddRule _ (.netPort _ _) => "landlock_add_rule.net"
  | .landlockRestrictSelf _ => "landlock_restrict_self"
  | .seccomp (.getActionAvail _) _ _ => "seccomp.avail"
  | .seccomp .setModeFilter _ _ => "seccomp.filter"
  | .prctl _ => "prctl"
  | .setrlimit _ _ _ => "setrlimit"
  | .memfdCreate _ _ => "memfd_create"

private def bumpHit (hits : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  Id.run do
    for i in List.range hits.size do
      let entry := hits.getD i ("", 0)
      if entry.1 == k then
        return hits.set! i (k, entry.2 + 1)
    return hits.push (k, 1)

private def mergeHits (dst src : Array (String × Nat)) : Array (String × Nat) :=
  src.foldl (fun acc (k, n) => Id.run do
    for i in List.range acc.size do
      let e := acc.getD i ("", 0)
      if e.1 == k then
        return acc.set! i (k, e.2 + n)
    return acc.push (k, n)) dst

private def encodeOutcome : SandboxOutcome → String
  | .landlockVersion v => s!"V:{v}"
  | .opened h => s!"O:{h}"
  | .unit => "U"
  | .u32 v => s!"N:{v}"
  | .err e => s!"E:{e}"

private def extraDirPaths : Array String := #[
  "/var/tmp", "/proc", "/sys", "/sys/fs/cgroup"
]

private def extraFilePaths : Array String := #[
  "/proc/self/status", "/dev/null"
]

private def blockMemfdFilter : ByteArray :=
  encodeFilter
    [ { code := 0x0020, jt := 0, jf := 0, k := 0 }
    , { code := 0x0015, jt := 2, jf := 0, k := 319 }
    , { code := 0x0015, jt := 1, jf := 0, k := 279 }
    , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }
    , { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM } ]

private def setupPreEnvironment (plan : EpisodePlan) : IO (Bool × SandboxSysState) := do
  if plan.useUserns then
    let _ ← SandboxEnv.enterUserns
  if plan.preOuterLayers > 0 then
    if !plan.useUserns then
      let _ ← prctl .setNoNewPrivs
    match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
    | .ok (.ruleset outerRs) =>
      for _ in List.range plan.preOuterLayers do
        let _ ← landlockRestrictSelf outerRs
      let _ ← SandboxEnv.closeFd outerRs
    | _ => pure ()
  if plan.preNnp then
    let _ ← prctl .setNoNewPrivs
  let mut sys := SandboxSysState.initial
  if plan.preOuterSeccomp then
    let _ ← prctl .setNoNewPrivs
    match ← seccomp .setModeFilter {} blockMemfdFilter with
    | .ok 0 => sys := sys.withOuterSeccomp
    | _ => pure ()
  let mut spawnActive := false
  if plan.spawnMode == 1 then
    match ← SandboxEnv.spawnSyncThread true with
    | .ok _ => spawnActive := true
    | .error _ => pure ()
  else if plan.spawnMode == 2 then
    match ← SandboxEnv.spawnSyncThread false with
    | .ok _ => spawnActive := true
    | .error _ => pure ()
  return (spawnActive, sys)

private def runPlanInChild
    (dirPath filePath : String)
    (plan : EpisodePlan)
    (stepOracle : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState := allowedStep) :
    IO EpisodeResult := do
  let (st, payload) ← SandboxEnv.runForked do
    let (spawnActive, initSys) ← setupPreEnvironment plan
    let mut sys := initSys
    let mut nextHid : HandleId := 1
    let mut hostDirs : Array HandleSlot := #[]
    let mut hostFiles : Array HandleSlot := #[]
    let mut pseudos : Array HandleSlot := #[]
    let mut opathMemfd? : Option HandleSlot := none
    let mut opathRuleset? : Option HandleSlot := none
    let mut closedHids : Array HandleSlot := #[]
    for i in List.range plan.dirOPaths.size do
      let oPath := plan.dirOPaths.getD i false
      let dPath := if i == 0 then dirPath else extraDirPaths.getD (plan.specialSeedIdx % extraDirPaths.size) "/var/tmp"
      match ← SandboxEnv.openHostFd dPath.toUTF8 (if oPath then 1 else 0) with
      | .ok fd =>
        let hid := nextHid
        nextHid := nextHid + 1
        sys := sys.withHostFd hid true oPath
        hostDirs := hostDirs.push { hid, fd }
      | .error _ => pure ()
    for i in List.range plan.fileOPaths.size do
      let oPath := plan.fileOPaths.getD i false
      let fPath := if i == 0 then filePath else extraFilePaths.getD (plan.specialSeedIdx % extraFilePaths.size) "/dev/null"
      match ← SandboxEnv.openHostFd fPath.toUTF8 (if oPath then 3 else 2) with
      | .ok fd =>
        let hid := nextHid
        nextHid := nextHid + 1
        sys := sys.withHostFd hid false oPath
        hostFiles := hostFiles.push { hid, fd }
      | .error _ => pure ()
    for oPath in plan.pseudoOPaths do
      match ← SandboxEnv.openPipeFd (if oPath then 1 else 0) with
      | .ok fd =>
        let hid := nextHid
        nextHid := nextHid + 1
        sys := sys.withPseudoFd hid oPath
        pseudos := pseudos.push { hid, fd }
      | .error _ => pure ()
    if plan.seedOPathSpecials then
      let pseudoKind := UInt32.ofNat (plan.specialSeedIdx % 3)
      match ← SandboxEnv.openSpecialFd pseudoKind ByteArray.empty with
      | .ok fd =>
        let hid := nextHid
        nextHid := nextHid + 1
        sys := sys.withPseudoFd hid false
        pseudos := pseudos.push { hid, fd }
      | .error _ => pure ()
      let pathKind := UInt32.ofNat (3 + (plan.specialSeedIdx % 5))
      let sPath := s!"{dirPath}/sp_{plan.specialSeedIdx}"
      match ← SandboxEnv.openSpecialFd pathKind sPath.toUTF8 with
      | .ok fd =>
        let hid := nextHid
        nextHid := nextHid + 1
        let isDirSpecial := pathKind == 4
        let isOPathSpecial := pathKind == 5 || pathKind == 6 || pathKind == 7
        sys := sys.withHostFd hid isDirSpecial isOPathSpecial
        if isDirSpecial then
          hostDirs := hostDirs.push { hid, fd }
        else
          hostFiles := hostFiles.push { hid, fd }
      | .error _ => pure ()
      match ← memfdCreate "opm".toUTF8 {} with
      | .ok mfd =>
        match ← SandboxEnv.reopenOPath mfd with
        | .ok opFd =>
          let hid := nextHid
          nextHid := nextHid + 1
          sys := {
            sys with
            fds := assocSet sys.fds hid { kind := .memfd false false, cloexec := true, oPath := true }
            nextHid := Nat.max sys.nextHid (hid + 1)
          }
          opathMemfd? := some { hid, fd := opFd }
        | .error _ => pure ()
        let _ ← SandboxEnv.closeFd mfd
      | .error _ => pure ()
      match ← landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0 with
      | .ok (.ruleset rs) =>
        match ← SandboxEnv.reopenOPath rs with
        | .ok opRs =>
          let hid := nextHid
          nextHid := nextHid + 1
          sys := {
            sys with
            fds := assocSet sys.fds hid { kind := .landlockRuleset LANDLOCK_ACCESS_FS_EXECUTE 0, cloexec := true, oPath := true }
            nextHid := Nat.max sys.nextHid (hid + 1)
            landlockEnabled := true
          }
          opathRuleset? := some { hid, fd := opRs }
        | .error _ => pure ()
        let _ ← SandboxEnv.closeFd rs
      | _ => pure ()
    let deadFd ← match ← memfdCreate "dead".toUTF8 {} with
      | .ok f =>
        let _ ← SandboxEnv.closeFd f
        pure f
      | .error _ =>
        match ← SandboxEnv.openHostFd filePath.toUTF8 3 with
        | .ok f =>
          let _ ← SandboxEnv.closeFd f
          pure f
        | .error e =>
          throw (IO.userError s!"deadFd setup failed: {e}")
    closedHids := closedHids.push { hid := 9999, fd := deadFd }
    if plan.closeLowFds then
      SandboxEnv.closeRaw 0
      SandboxEnv.closeRaw 1
      SandboxEnv.closeRaw 2
    let mut ex : ExecState := {
      sys, nextHid, hostDirs, hostFiles, pseudos, opathMemfd?, opathRuleset?,
      dynamics := #[], closedHids, deadFd
    }
    let mut executed : Nat := 0
    let mut hits : Array (String × Nat) := #[]
    let mut mismatch? : Option (Nat × String) := none
    for stepIdx in List.range plan.steps.size do
      if mismatch?.isSome then
        break
      let fs := plan.steps.getD stepIdx (.doPrctl .getNoNewPrivs)
      match fs with
      | .closeDyn idx =>
        if !ex.dynamics.isEmpty then
          let pos := idx % ex.dynamics.size
          let slot := ex.dynamics.getD pos { hid := 9999, fd := ex.deadFd }
          let _ ← SandboxEnv.closeFd slot.fd
          let sys' := { ex.sys with fds := ex.sys.fds.filter (fun p => p.1 != slot.hid) }
          ex := { ex with
            sys := sys'
            dynamics := ex.dynamics.eraseIdx! pos
            closedHids := ex.closedHids.push slot }
      | .llCreate attr? flags =>
        let req : SandboxReq := .landlockCreateRuleset attr? flags
        let out ← match ← landlockCreateRuleset attr? flags with
          | .error e => pure (SandboxOutcome.err e)
          | .ok (.version v) => pure (SandboxOutcome.landlockVersion v)
          | .ok (.ruleset fd) =>
            let hid := ex.nextHid
            ex := { ex with nextHid := hid + 1, dynamics := ex.dynamics.push { hid, fd } }
            pure (SandboxOutcome.opened hid)
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .llAddPath rsCh pCh acc =>
        let (rHid, rFd) := resolveChoice ex rsCh
        let (pHid, pFd) := resolveChoice ex pCh
        let req : SandboxReq := .landlockAddRule rHid (.pathBeneath pHid acc)
        let out : SandboxOutcome := match ← landlockAddRule rFd (.pathBeneath pFd acc) with
          | .ok () => .unit
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .llAddNet rsCh port acc =>
        let (rHid, rFd) := resolveChoice ex rsCh
        let req : SandboxReq := .landlockAddRule rHid (.netPort port acc)
        let out : SandboxOutcome := match ← landlockAddRule rFd (.netPort port acc) with
          | .ok () => .unit
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .llRestrict rsCh =>
        let (rHid, rFd) := resolveChoice ex rsCh
        let req : SandboxReq := .landlockRestrictSelf rHid
        let out : SandboxOutcome := match ← landlockRestrictSelf rFd with
          | .ok () => .unit
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .scGetAvail act fl =>
        let req : SandboxReq := .seccomp (.getActionAvail act) fl ByteArray.empty
        let out : SandboxOutcome := match ← seccomp (.getActionAvail act) fl ByteArray.empty with
          | .ok v => .u32 v
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .scSetFilter fl bs =>
        let req : SandboxReq := .seccomp .setModeFilter fl bs
        let out : SandboxOutcome := match ← seccomp .setModeFilter fl bs with
          | .ok v => .u32 v
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .doPrctl op =>
        let req : SandboxReq := .prctl op
        let out : SandboxOutcome := match ← prctl op with
          | .ok v => .u32 v
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .doSetrlimit res cur maxV =>
        let req : SandboxReq := .setrlimit res cur maxV
        let out : SandboxOutcome := match ← setrlimit res cur maxV with
          | .ok () => .unit
          | .error e => .err e
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
      | .doMemfd name fl =>
        let req : SandboxReq := .memfdCreate name fl
        let out ← match ← memfdCreate name fl with
          | .error e => pure (SandboxOutcome.err e)
          | .ok fd =>
            let hid := ex.nextHid
            ex := { ex with nextHid := hid + 1, dynamics := ex.dynamics.push { hid, fd } }
            pure (SandboxOutcome.opened hid)
        executed := executed + 1
        hits := bumpHit hits s!"{reqTag req} -> {outcomeTag out}"
        match stepOracle ex.sys req out with
        | some s' =>
          if !s'.wf then
            mismatch? := some (stepIdx, s!"wf violated after {reqTag req} ({encodeOutcome out})")
          ex := { ex with sys := s' }
        | none =>
          mismatch? := some (stepIdx, s!"model mismatch step={stepIdx} req={reqTag req} out={encodeOutcome out} sys={repr ex.sys}")
    if spawnActive then
      let _ ← SandboxEnv.stopSyncThread
    for s in ex.hostDirs do let _ ← SandboxEnv.closeFd s.fd
    for s in ex.hostFiles do let _ ← SandboxEnv.closeFd s.fd
    for s in ex.pseudos do let _ ← SandboxEnv.closeFd s.fd
    if let some s := ex.opathMemfd? then let _ ← SandboxEnv.closeFd s.fd
    if let some s := ex.opathRuleset? then let _ ← SandboxEnv.closeFd s.fd
    for s in ex.dynamics do let _ ← SandboxEnv.closeFd s.fd
    let mut lines := #[toString executed]
    match mismatch? with
    | none => lines := lines.push "OK"
    | some (idx, msg) => lines := lines.push s!"ERR\t{idx}\t{msg}"
    for (k, n) in hits do
      lines := lines.push s!"HIT\t{k}\t{n}"
    return ("\n".intercalate lines.toList).toUTF8
  if (st &&& 0x7F) != 0 || ((st >>> 8) &&& 0xFF) != 0 then
    return { executed := 0, hits := #[], mismatch? := some (0, s!"child crashed/signaled waitStatus={st}") }
  let txt := String.fromUTF8! payload
  let lines := txt.splitOn "\n"
  let executed := (lines.head?.bind String.toNat?).getD 0
  let rest := lines.drop 1
  let mut mismatch? : Option (Nat × String) := none
  let mut hits : Array (String × Nat) := #[]
  for ln in rest do
    if ln.startsWith "ERR\t" then
      let parts := ln.splitOn "\t"
      let idx := (parts.getD 1 "0").toNat?.getD 0
      let msg := "\t".intercalate (parts.drop 2)
      mismatch? := some (idx, msg)
    else if ln.startsWith "HIT\t" then
      let parts := ln.splitOn "\t"
      let k := parts.getD 1 ""
      let n := (parts.getD 2 "0").toNat?.getD 0
      hits := hits.push (k, n)
  return { executed, hits, mismatch? }

private partial def shrinkPlan
    (dirPath filePath : String)
    (plan : EpisodePlan)
    (oracle : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState) :
    IO EpisodePlan := do
  let mut best := plan
  let mut chunk := Nat.max 1 (best.steps.size / 2)
  while chunk >= 1 && best.steps.size > 1 do
    let mut improved := false
    let mut start := 0
    while start < best.steps.size do
      let stop := Nat.min best.steps.size (start + chunk)
      let shrunkSteps := best.steps.extract 0 start ++ best.steps.extract stop best.steps.size
      if !shrunkSteps.isEmpty then
        let candidate := { best with steps := shrunkSteps }
        let res ← runPlanInChild dirPath filePath candidate oracle
        if res.mismatch?.isSome then
          best := candidate
          improved := true
          break
      start := start + chunk
    if !improved then
      if chunk == 1 then
        break
      chunk := chunk / 2
  return best

private def withFuzzDir {α : Type} (f : String → String → IO α) : IO α := do
  let pid ← SandboxEnv.getTid
  let dir := s!"/tmp/leanswe-sbx-fuzz-{pid}"
  let file := s!"{dir}/sample.txt"
  IO.FS.createDirAll dir
  IO.FS.writeFile file "fuzz"
  try
    f dir file
  finally
    for idx in List.range 64 do
      let sp := s!"{dir}/sp_{idx}"
      try IO.FS.removeFile sp catch _ => pure ()
      try IO.FS.removeDir sp catch _ => pure ()
    try IO.FS.removeFile file catch _ => pure ()
    try IO.FS.removeDir dir catch _ => pure ()

/-- Verify greedy delta-shrinking against an injected faulty oracle over a multi-step random trace. -/
def runShrinkSelfTest (seed : UInt64 := 0x123456789abcdef0) : IO Unit := do
  withFuzzDir fun dirPath filePath => do
    let badOracle : SandboxSysState → SandboxReq → SandboxOutcome → Option SandboxSysState :=
      fun s req out =>
        match req, out with
        | .prctl (.setPdeathsig 9), .u32 0 => none
        | _, _ => allowedStep s req out
    let rng := Rng.seed seed
    let (basePlan, _) := genEpisodePlan rng 29
    let prefixSteps := basePlan.steps.extract 0 15
    let suffixSteps := basePlan.steps.extract 15 basePlan.steps.size
    let injected := { basePlan with
      preOuterSeccomp := false
      steps := (prefixSteps.push (.doPrctl (.setPdeathsig 9))) ++ suffixSteps }
    let initialRes ← runPlanInChild dirPath filePath injected badOracle
    match initialRes.mismatch? with
    | none => throw (IO.userError "shrink self-test failed to trigger injected oracle bug")
    | some _ => pure ()
    let minimal ← shrinkPlan dirPath filePath injected badOracle
    if minimal.steps.size > 2 then
      throw (IO.userError s!"shrink self-test expected <= 2 steps, got {minimal.steps.size}")
    IO.println s!"SANDBOX_SHRINK_SELFTEST_OK: {injected.steps.size} -> {minimal.steps.size} step(s)"

/-- Execute `cfg.steps` real sandbox syscalls inside forked child episodes and verify every step against `Model.allowedStep`. -/
def runFuzz (cfg : FuzzConfig := {}) : IO UInt32 := do
  if cfg.selfTestShrink then
    runShrinkSelfTest cfg.seed
  withFuzzDir fun dirPath filePath => do
    let mut rng := Rng.seed cfg.seed
    let mut totalSteps : Nat := 0
    let mut episodes : Nat := 0
    let mut hits : Array (String × Nat) := #[]
    while totalSteps < cfg.steps do
      let remaining := cfg.steps - totalSteps
      let batch := Nat.min cfg.stepsPerEpisode remaining
      let (plan, nxt) := genEpisodePlan rng batch
      rng := nxt
      let res ← runPlanInChild dirPath filePath plan allowedStep
      episodes := episodes + 1
      totalSteps := totalSteps + res.executed
      hits := mergeHits hits res.hits
      match res.mismatch? with
      | some (_, msg) =>
        let minimal ← shrinkPlan dirPath filePath plan allowedStep
        IO.eprintln s!"SANDBOX_FUZZ_MISMATCH after {totalSteps} steps (episode {episodes}): {msg}"
        IO.eprintln s!"SHRUNK_TRACE ({minimal.steps.size} steps): {repr minimal}"
        return 1
      | none => pure ()
    IO.println s!"SANDBOX_FUZZ_OK: syscalls={totalSteps} episodes={episodes} seed={cfg.seed}"
    if cfg.printMatrix then
      IO.println "SANDBOX_FUZZ_MATRIX_BEGIN"
      for (k, n) in hits do
        IO.println s!"  {k}: {n}"
      IO.println "SANDBOX_FUZZ_MATRIX_END"
    return 0

end LeanSwe.LinuxSyscall.Fuzz.SandboxFuzz
