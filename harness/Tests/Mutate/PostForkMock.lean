import Tests.Common
import LeanSwe.PostFork.Interface
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Funs

namespace Tests.Mutate.PostForkMock

open LeanSwe
open Tests.Common

/-- Execute pure `StateM` host-ops fault-injection, wire-codec, and Aeneas `ChildState` checks for `LeanSwe.PostFork`. -/
def runPostForkMockTests : IO Unit := do
  let checkM (lbl : String) (ok : Bool) : IO Unit := do
    if !ok then
      throw (IO.userError s!"PostFork mut extra failed: {lbl}")
  let fakeWrite : Int32 → ByteArray → UInt64 → UInt64 → StateM (Nat × Nat × Nat × List Int32) (Except LinuxSyscall.Errno UInt64) :=
    fun _ _ _ len => do
      let (wCnt, rCnt, tCnt, closed) ← get
      set (wCnt + 1, rCnt, tCnt, closed)
      match wCnt with
      | 0 => pure (.error LinuxSyscall.Errno.EINTR)
      | 1 => pure (.ok 1)
      | _ => pure (.ok (if len > 0 then len else 0))
  let fakeOps (syncEpipe : Bool) (repBytes : ByteArray) :
      PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × Nat × Nat × List Int32)) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := do
        let (wCnt, rCnt, tCnt, closed) ← get
        let base : Int32 := if closed.isEmpty then 10 else 12
        set (wCnt, rCnt, tCnt, closed)
        pure (.ok (base, base + 1))
      closeFd := fun fd => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt, tCnt, fd :: closed)
        pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun fd _ _ len => do
        if syncEpipe && fd == 11 then pure (.error LinuxSyscall.Errno.EPIPE)
        else fakeWrite fd ByteArray.empty 0 len
      readOnce := fun _ _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt + 1, tCnt, closed)
        match rCnt with
        | 0 => pure (.error LinuxSyscall.Errno.EINTR)
        | 1 => pure (.ok (repBytes.extract 0 (min 2 repBytes.size)))
        | 2 => pure (.ok (repBytes.extract (min 2 repBytes.size) repBytes.size))
        | _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt, tCnt + 1, closed)
        if tCnt == 0 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok (.exited 0))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let ops1 := PostFork.Impl.Internal.mkHostOps (fakeOps false (PostFork.Model.encodeFailureReport .chdir LinuxSyscall.Errno.ENOENT)) 4
  let (p1, st1) := (ops1.spawn (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  checkM "spawn eintr+partial wire"
    (match p1 with
     | .error e => e.kind == .childFailed && e.childFailure == some { stage := .chdir, errno := LinuxSyscall.Errno.ENOENT, waitStatus := some (.exited 0) }
     | .ok _ => false)
  checkM "spawn wait count" (st1.2.2.1 == 2)

  let opsBar := PostFork.Impl.Internal.mkHostOps (fakeOps true (PostFork.Model.encodeFailureReport .execve LinuxSyscall.Errno.ENOENT)) 4
  let (bPendRes, bSt) := (opsBar.spawnWithBarrier (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  match bPendRes with
  | .error _ => throw (IO.userError "PostFork mut extra: spawnWithBarrier failed")
  | .ok pend =>
    let (rRel, _) := (opsBar.releaseBarrier pend).run bSt
    checkM "releaseBarrier epipe reports execve"
      (match rRel with
       | .error e => e.kind == .childFailed && e.errno == some LinuxSyscall.Errno.ENOENT
       | .ok _ => false)

  let fakeZero : PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × Nat × Nat × List Int32)) Int32 :=
    { (fakeOps false ByteArray.empty) with writeOnce := fun _ _ _ _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt + 1, rCnt, tCnt, closed)
        pure (.ok 0) }
  let opsZero := PostFork.Impl.Internal.mkHostOps fakeZero 4
  let (bZRes, bZSt) := (opsZero.spawnWithBarrier (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  match bZRes with
  | .error _ => throw (IO.userError "PostFork mut extra: zero spawnWithBarrier failed")
  | .ok pendZ =>
    let (rZ, bZSt2) := (opsZero.releaseBarrier pendZ).run bZSt
    checkM "writeOnce 0 returns error immediately"
      (bZSt2.1 == 1 && (match rZ with | .error e => e.message == "host write returned zero bytes" | .ok _ => false))

  let fakeWriteEintr : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { writeOnce := fun _ _ _ len => do
        let n ← get
        set (n + 1)
        if n == 0 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok len)
      probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun _ => pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      readOnce := fun _ _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => pure (.ok (.exited 0))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let (wrEintr, wrEintrCnt) := (PostFork.Impl.Internal.writeAllRetryEintr fakeWriteEintr 11 (ByteArray.mk #[1, 2, 3]) 0 4).run 0
  checkM "writeAllRetryEintr retries EINTR" (wrEintr.isOk && wrEintrCnt == 2)
  let (wrExactFuel, wrExactCnt) :=
    (PostFork.Impl.Internal.writeAllRetryEintr fakeWriteEintr 11 (ByteArray.mk #[7]) 0 1).run 0
  checkM "writeAllRetryEintr exact fuel finalOff succeeds" (wrExactFuel == .ok () && wrExactCnt == 2)

  let fakeReadAcc : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      readOnce := fun _ _ => do
        let n ← get
        set (n + 1)
        if n == 0 then pure (.ok (ByteArray.mk #[44])) else pure (.ok ByteArray.empty) }
  let (rdAcc, _) := (PostFork.Impl.Internal.readAllRetryEintr fakeReadAcc 10 64 (ByteArray.mk #[42, 43]) 4).run 0
  checkM "readAllRetryEintr keeps non-empty acc" (rdAcc == .ok (ByteArray.mk #[42, 43, 44]))

  let fakeAbortBusy : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EBUSY) }
  let (abBusyRes, abBusyCnt) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortBusy 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier EBUSY fails fast"
    (abBusyCnt == 1 &&
      (match abBusyRes with
       | .error e => e.kind == .sysError && e.errno == some LinuxSyscall.Errno.EBUSY
       | .ok _ => false))

  let fakeAbortCloseEintr : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun fd => do
        modify (· + 1)
        if fd == 13 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok ())
      waitOnce := fun _ => pure (.ok (.exited 125)) }
  let (abEintrRes, _) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortCloseEintr 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier closeFd EINTR still drains and reaps"
    (abEintrRes == .ok (.aborted (.exited 125)))

  let (spFkRes, spFkSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).spawn
      { path := "/bin/true", argv := #[] }).run { failForkErrno := some LinuxSyscall.Errno.EAGAIN }
  checkM "spawn failForkErrno closes errW and errR"
    (spFkRes.isOk == false && spFkSt.closedHandles == [10, 11])

  checkM "ChildSpecM default sigpipe is resetDefault"
    (({ path := "/bin/true", argv := #[] } : PostFork.ChildSpecM Int32).sigpipe == .resetDefault)
  checkM "StdioPlan.redirect default closeSourcesAbove2 is true"
    ((PostFork.StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) : PostFork.StdioPlan Int32) ==
      PostFork.StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) true)
  checkM "Model.ArgToken.ref? extracts refs"
    (PostFork.Model.ArgToken.ref? (.lit "a" : PostFork.ArgToken Int32) == none &&
      PostFork.Model.ArgToken.ref? (.fdDecimal (.raw 5) : PostFork.ArgToken Int32) == some (.raw 5) &&
      PostFork.Model.ArgToken.ref? (.prefixedFd "p" (.handle 7) "s" : PostFork.ArgToken Int32) == some (.handle 7))
  checkM "Model.i32Le signed ordering"
    (PostFork.Model.i32Le (-5) 3 == true &&
      PostFork.Model.i32Le 3 3 == true &&
      PostFork.Model.i32Le 3 (-5) == false &&
      PostFork.Model.i32Le Int32.minValue Int32.maxValue == true &&
      PostFork.Model.i32Le Int32.maxValue Int32.minValue == false)

  let mkRelProbe (wrErr : LinuxSyscall.Errno) (cl13Res : Except LinuxSyscall.Errno Unit) :
      PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × List Int32)) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun fd => do
        modify fun (n, cs) => (n + 1, fd :: cs)
        if fd == 13 then pure cl13Res else pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun _ _ _ _ => do
        modify fun (n, cs) => (n + 1, cs)
        pure (.error wrErr)
      readOnce := fun _ _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => do
        modify fun (n, cs) => (n + 1, cs)
        pure (.ok (.exited 125))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let relPend : PostFork.PendingChildM Int32 := { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }
  let (rWrEbadf, stWrEbadf) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EBADF (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EBADF fails fast" (rWrEbadf.isOk == false && stWrEbadf == (1, []))
  let (rWrEbusy, stWrEbusy) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EBUSY (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EBUSY fails fast" (rWrEbusy.isOk == false && stWrEbusy == (1, []))
  let (rClEbadf, stClEbadf) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EBADF)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EBADF fails fast" (rClEbadf.isOk == false && stClEbadf == (2, [13]))
  let (rClEbusy, stClEbusy) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EBUSY)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EBUSY fails fast" (rClEbusy.isOk == false && stClEbusy == (2, [13]))
  let (rClEintr, stClEintr) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EINTR)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EINTR still closes errRead and reaps" (rClEintr.isOk == false && stClEintr == (4, [10, 13]))
  let (rClOk, stClOk) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EIO closes both and reaps" (rClOk.isOk == false && stClOk == (4, [10, 13]))
  let (rWrEpipe0, stWrEpipe0) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EPIPE (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EPIPE empty errRead reaps and returns wireTruncated"
    (stWrEpipe0 == (4, [10, 13]) &&
      (match rWrEpipe0 with
       | .error e =>
         e.kind == .childFailed &&
           e.childFailure == some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO, waitStatus := some (.exited 125) }
       | .ok _ => false))

  checkM "decodeChildFailure valid"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .chdir, errno := LinuxSyscall.Errno.ENOENT })
  checkM "decodeChildFailure bad magic"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x51, 0x01, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad version"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x02, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad pad3"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 6, 1, 22, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad tag"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 9, 0, 22, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure short len"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 22, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })

  let wrSlice := PostFork.Aeneas.Model.mkSliceU8 1#usize [97#u8] rfl
  let brokenBase : PostFork.World.ChildState :=
    { status := .running
      fds := [(1, { desc := 11, cloexec := false })]
      descs := [(11, .stream false true true [])] }
  let resPid1 := _root_.sys.write { brokenBase with pid := 1, blockedSigs := [] } 1#i32 wrSlice
  checkM "sys.write pid=1 broken pipe survives"
    (match Aeneas.Std.Result.match resPid1 with
     | .ok (.Err _, st) => st.status == .running
     | _ => false)
  let resBlk := _root_.sys.write { brokenBase with pid := 42, blockedSigs := [13] } 1#i32 wrSlice
  checkM "sys.write blocked SIGPIPE survives"
    (match Aeneas.Std.Result.match resBlk with
     | .ok (.Err _, st) => st.status == .running
     | _ => false)
  let resDfl := _root_.sys.write { brokenBase with pid := 42, blockedSigs := [] } 1#i32 wrSlice
  checkM "sys.write unblocked pid!=1 SIGPIPE kills"
    (match Aeneas.Std.Result.match resDfl with
     | .ok (.Err _, st) => st.status == .signaled 13#i32
     | _ => false)

  let zeroBuf : Aeneas.Std.Array Aeneas.Std.U8 256#usize := Aeneas.Std.Array.repeat 256#usize 0#u8
  let dirState : PostFork.World.ChildState :=
    { status := .running
      fds := [(4, { desc := 30, cloexec := true })]
      descs := [(30, .directory 0)] }
  let (dRes1, dSt1, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 dirState 4#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 .directory batch1 failed")
  checkM "sys.getdents64 .directory batch1 > 0"
    (match dRes1 with | .Ok n => n.val > 0 | _ => false)
  let (dRes2, _, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 dSt1 4#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 .directory EOF failed")
  checkM "sys.getdents64 .directory EOF = 0"
    (match dRes2 with | .Ok n => n.val == 0 | _ => false)

  let sparseProcState : PostFork.World.ChildState :=
    { status := .running
      fds := [(3, { desc := 40, cloexec := true }), (10, { desc := 41, cloexec := false }), (200, { desc := 42, cloexec := false })]
      descs := [(40, .procSelfFd (-2)), (41, .stream true true false []), (42, .stream true true false [])]
      oracle := [.dentsBatch 0, .dentsBatch 0] }
  let (pRes1, pSt1, pBuf1) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 sparseProcState 3#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 sparse batch1 failed")
  let hasNonZeroDoff := (List.range 8).any fun i => (pBuf1.val[8 + i]!).val != 0
  checkM "sys.getdents64 procSelfFd batch1 non-zero d_off"
    ((match pRes1 with | .Ok n => n.val >= 20 | _ => false) && hasNonZeroDoff)
  let (pRes2, pSt2, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 pSt1 3#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 sparse batch2 failed")
  checkM "sys.getdents64 procSelfFd batch2 > 0"
    (match pRes2 with | .Ok n => n.val > 0 | _ => false)
  checkM "sys.getdents64 procSelfFd cursor advanced"
    (pSt2.getDesc 40 != sparseProcState.getDesc 40)

  checkM "Impl.pushI32Le all 4 byte lanes"
    (PostFork.Impl.Internal.pushI32Le ByteArray.empty 0x01020304 == ByteArray.mk #[0x04, 0x03, 0x02, 0x01] &&
      PostFork.Impl.Internal.pushI32Le ByteArray.empty (-0x01020304) == ByteArray.mk #[0xFC, 0xFC, 0xFD, 0xFE])
  checkM "Model.packI32Le all 4 byte lanes"
    (PostFork.Model.packI32Le 0x01020304 == ByteArray.mk #[0x04, 0x03, 0x02, 0x01] &&
      PostFork.Model.packI32Le (-0x01020304) == ByteArray.mk #[0xFC, 0xFC, 0xFD, 0xFE])
  checkM "Model.FailureStage.toTag? wireTruncated is none"
    (PostFork.Model.FailureStage.toTag? .wireTruncated == none &&
      PostFork.Model.encodeFailureReport .wireTruncated 0 == ByteArray.mk #[0x50, 0x01, 7, 0, 5, 0, 0, 0])
  checkM "Model.normalizeWireErrno out-of-range normalizes to EIO"
    (PostFork.Model.normalizeWireErrno 0 == LinuxSyscall.Errno.EIO &&
      PostFork.Model.normalizeWireErrno 4096 == LinuxSyscall.Errno.EIO)
  checkM "Types default parameter values"
    ((PostFork.ArgToken.prefixedFd "--fd=" (.raw 5) : PostFork.ArgToken Int32) ==
        PostFork.ArgToken.prefixedFd "--fd=" (.raw 5) "" &&
      (PostFork.FdPolicy.inheritNonCloexec : PostFork.FdPolicy Int32) ==
        PostFork.FdPolicy.inheritNonCloexec #[] &&
      (PostFork.FdPolicy.closeAllAbove2Except : PostFork.FdPolicy Int32) ==
        PostFork.FdPolicy.closeAllAbove2Except #[] &&
      (PostFork.ChildSpecM.ofCommand "/bin/true" : PostFork.ChildSpecM Int32) ==
        { path := "/bin/true", argv := #[.lit "/bin/true"] })

  let alwaysEintrOps : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun _ => pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun _ _ _ _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      readOnce := fun _ _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      waitOnce := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let (wrFuelRes, wrFuelCnt) :=
    (PostFork.Impl.Internal.writeAllRetryEintr alwaysEintrOps 11 (ByteArray.mk #[1]) 0 1).run 0
  checkM "writeAllRetryEintr fuel exhaustion errors"
    (wrFuelCnt == 2 && (match wrFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EIO | .ok () => false))
  let (rdFuelRes, rdFuelCnt) :=
    (PostFork.Impl.Internal.readAllRetryEintr alwaysEintrOps 10 16 ByteArray.empty 1).run 0
  checkM "readAllRetryEintr fuel exhaustion errors"
    (rdFuelCnt == 2 && (match rdFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EIO | .ok _ => false))
  let (wtFuelRes, wtFuelCnt) :=
    (PostFork.Impl.Internal.waitRetryEintr alwaysEintrOps 100 1).run 0
  checkM "waitRetryEintr fuel exhaustion errors"
    (wtFuelCnt == 2 && (match wtFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EINTR | .ok _ => false))

  let (spRdErr, spRdSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).spawn
      { path := "/bin/cat", argv := #[] }).run { failReadErrno := some LinuxSyscall.Errno.ENOMEM }
  checkM "awaitExecOrFailure read error does not call blocking waitOnce"
    (!spRdErr.isOk && spRdSt.closedHandles == [10, 11] && spRdSt.callCount == 5)
  let (relClErr, relClSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).releaseBarrier relPend).run
      { allocSyncWriteFd := 13, closedHandles := [10] }
  checkM "releaseBarrier closed errRead fails fast before syncWrite"
    (!relClErr.isOk && relClSt.syncWritten == ByteArray.empty && relClSt.callCount == 1)
  let (rWrEoverflow, stWrEoverflow) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe 75 (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EOVERFLOW fails fast without closing"
    (!rWrEoverflow.isOk && stWrEoverflow == (1, []))
  let (rClEperm, stClEperm) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EPERM)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EPERM fails fast without reaping"
    (!rClEperm.isOk && stClEperm == (2, [13]))
  let fakeAbortEperm : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EPERM) }
  let (abEpermRes, abEpermCnt) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortEperm 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier EPERM fails fast"
    (abEpermCnt == 1 &&
      (match abEpermRes with
       | .error e => e.kind == .sysError && e.errno == some LinuxSyscall.Errno.EPERM
       | .ok _ => false))

end Tests.Mutate.PostForkMock
