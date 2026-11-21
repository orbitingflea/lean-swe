import Core.NondetTest
import Core.Assumptions
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Impl
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Api
import LeanSwe.PostFork.Aeneas.Bridge

namespace LeanSwe.PostFork

open _root_.Aeneas _root_.Aeneas.Std Result
open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model
open LeanSwe.PostFork.Aeneas.Bridge

/-- `encodeFailureReport` and pure `Model.encodeFailureReport`/`Model.decodeChildFailure` emit uniform 8-byte wire frames `[0x50, 0x01, stage, 0x00, err_le32]`, round-trip every valid `(stage, errno)`, and map malformed/truncated frames to `.wireTruncated` (`EIO`). -/
def test_postfork_wireEncoder_uniformAndRoundTrip
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let stage ← nondet Std.U8
  let errnum ← nondet Std.I32
  let fStage ← nondet FailureStage
  let errU ← nondet UInt32
  NondetTest.assert
    (OkPost (api.encodeFailureReport stage errnum) (fun a => a.val = expectedFailureWireBytes stage errnum))
  NondetTest.assert (LeanSwe.PostFork.Model.decodeChildFailure ByteArray.empty = none)
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 2, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x51, 0x01, 7, 0, 2, 0, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x02, 7, 0, 2, 0, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 1, 2, 0, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 9, 0, 2, 0, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 0, 0, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO })
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 0, 16, 0, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO } ∧
      LeanSwe.PostFork.Model.FailureStage.toTag? .wireTruncated = none ∧
      LeanSwe.PostFork.Model.normalizeWireErrno 0 = Errno.EIO ∧
      LeanSwe.PostFork.Model.normalizeWireErrno 4096 = Errno.EIO ∧
      LeanSwe.PostFork.Model.encodeFailureReport .wireTruncated 0 =
        ByteArray.mk #[0x50, 0x01, 7, 0, 5, 0, 0, 0])
  assume (fStage ≠ .wireTruncated ∧ 1 ≤ errU.toNat ∧ errU.toNat ≤ 4095 ∧ 1 ≤ errnum.val ∧ errnum.val ≤ 4095)
  let wire := LeanSwe.PostFork.Model.encodeFailureReport fStage errU
  NondetTest.assert
    (LeanSwe.PostFork.Model.decodeChildFailure wire = some { stage := fStage, errno := errU })
  NondetTest.assert
    (LeanSwe.PostFork.Model.WIRE_MAGIC.toNat = postfork.child.WIRE_MAGIC.val ∧
      LeanSwe.PostFork.Model.WIRE_VERSION.toNat = postfork.child.WIRE_VERSION.val ∧
      LeanSwe.PostFork.Model.STAGE_VALIDATE.toNat = postfork.child.STAGE_VALIDATE.val ∧
      LeanSwe.PostFork.Model.STAGE_PROCESS_GROUP.toNat = postfork.child.STAGE_PROCESS_GROUP.val ∧
      LeanSwe.PostFork.Model.STAGE_SIGNAL_RESET.toNat = postfork.child.STAGE_SIGNAL_RESET.val ∧
      LeanSwe.PostFork.Model.STAGE_FD_SETUP.toNat = postfork.child.STAGE_FD_SETUP.val ∧
      LeanSwe.PostFork.Model.STAGE_CLOSE_UNKEPT.toNat = postfork.child.STAGE_CLOSE_UNKEPT.val ∧
      LeanSwe.PostFork.Model.STAGE_CHDIR.toNat = postfork.child.STAGE_CHDIR.val ∧
      LeanSwe.PostFork.Model.STAGE_EXECVE.toNat = postfork.child.STAGE_EXECVE.val)
  NondetTest.assert
    (OkPost (api.encodeFailureReport (stageToU8 fStage) errnum) (fun a =>
      bytesToByteArray a.val =
        LeanSwe.PostFork.Model.encodeFailureReport fStage (UInt32.ofNat errnum.toNat) ∧
      LeanSwe.PostFork.Model.decodeChildFailure (bytesToByteArray a.val) =
        some { stage := fStage, errno := UInt32.ofNat errnum.toNat }))

/-- `clearCloexec`, `setCloexec`, and `relocateRepAbove2` are total across all `ChildState`s, preserve non-`FD_CLOEXEC` flag bits via `F_GETFD` + `F_SETFD`, relocate `0..2` error pipes to `>= 3` with `FD_CLOEXEC = true`, and never close `0..2` on `EMFILE`/`EINVAL` failure. -/
def test_postfork_cloexecAndRelocate_preserveFlagsAndBounds
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let fd ← nondet Std.I32
  NondetTest.assert (OkPost (api.clearCloexec s fd) (fun _ => True))
  NondetTest.assert (OkPost (api.setCloexec s fd) (fun _ => True))
  NondetTest.assert (OkPost (api.relocateRepAbove2 s fd) (fun _ => True))
  assume (s.status = .running ∧ s.oracle = [])
  NondetTest.assert (OkPost (api.clearCloexec s fd) (fun p => CloexecTogglePost false s fd p.1 p.2))
  NondetTest.assert (OkPost (api.setCloexec s fd) (fun p => CloexecTogglePost true s fd p.1 p.2))
  NondetTest.assert (OkPost (api.relocateRepAbove2 s fd) (fun p => RelocateRepPost s fd p.1 p.2))

/-- `setupStdio` is total, rejects negative or closed descriptors with `EBADF` before allocating any scratch descriptor, routes arbitrary `(stdin_fd, stdout_fd, stderr_fd)` permutations, swaps, 3-cycles, and shared descriptors onto `(0, 1, 2)` without clobbering, clears `FD_CLOEXEC` on `0..2`, closes internal temporary slots unconditionally, and closes `> 2` caller sources iff `closeAbove2 = true`. -/
def test_postfork_setupStdio_clobberFreePermutationsAndCycles
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let inFd ← nondet Std.I32
  let outFd ← nondet Std.I32
  let errFd ← nondet Std.I32
  let closeAbove2 ← nondet Bool
  if decide (inFd < 0#i32) || decide (outFd < 0#i32) || decide (errFd < 0#i32) then
    NondetTest.assert
      (OkPost (api.setupStdio s inFd outFd errFd closeAbove2) (fun p =>
        p.1 = .Err EBADF ∧ p.2 = s))
  else
    pure ()
  assume (s.status = .running ∧ s.oracle = [])
  assume (0#i32 ≤ inFd ∧ 0#i32 ≤ outFd ∧ 0#i32 ≤ errFd)
  if !s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val then
    NondetTest.assert
      (OkPost (api.setupStdio s inFd outFd errFd closeAbove2) (fun p =>
        p.1 = .Err EBADF ∧ p.2.fds = s.fds))
  else
    pure ()
  assume (s.isOpen inFd.val = true ∧ s.isOpen outFd.val = true ∧ s.isOpen errFd.val = true)
  assume (min s.fdLimit 2147483648 ≥ 5 + Int.ofNat s.fds.length)
  NondetTest.assert
    (OkPost (api.setupStdio s inFd outFd errFd closeAbove2) (fun p =>
      p.1 = .Ok () ∧ SetupStdioPost s inFd outFd errFd closeAbove2 p.2))

/-- `parseDirentName` matches `expectedDirentParse` on all 256-byte buffers and `(start, stop)` bounds, rejecting malformed/unterminated records (`-2`), leading-zero/non-digit/`> INT32_MAX` names (`-1`), and round-tripping every valid `0 <= fd <= INT32_MAX` encoded via `encodeDirent64`. -/
def test_postfork_parseDirentName_canonicalDecimalAndRoundTrip
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let buf ← nondet (Array Std.U8 256#usize)
  let start ← nondet Std.Usize
  let stop ← nondet Std.Usize
  let fdNat ← nondet Nat
  NondetTest.assert (api.parseDirentName buf start stop = ok (expectedDirentParse buf start stop))
  let zeroBuf := Array.repeat 256#usize 0#u8
  let dotRec := encodeDirent64 1 1 4#u8 [46#u8]
  let dotDotRec := encodeDirent64 2 2 4#u8 [46#u8, 46#u8]
  let leadZeroRec := encodeDirent64 3 3 10#u8 [48#u8, 51#u8]
  NondetTest.assert
    (api.parseDirentName (overlayBuf256 dotRec zeroBuf) 19#usize (mkUsize dotRec.length) = ok (-1)#i32)
  NondetTest.assert
    (api.parseDirentName (overlayBuf256 dotDotRec zeroBuf) 19#usize (mkUsize dotDotRec.length) = ok (-1)#i32)
  NondetTest.assert
    (api.parseDirentName (overlayBuf256 leadZeroRec zeroBuf) 19#usize (mkUsize leadZeroRec.length) = ok (-1)#i32)
  assume (fdNat ≤ 2147483647)
  let fdRec := encodeDirent64 10 10 10#u8 (natToAsciiBytes fdNat)
  NondetTest.assert
    (api.parseDirentName (overlayBuf256 fdRec zeroBuf) 19#usize (mkUsize fdRec.length) =
      ok (mkI32 (Int.ofNat fdNat)))

/-- `closeFdsAbove2Except` is total, closes every unkept 32-bit descriptor `> 2` (even above lowered `RLIMIT_NOFILE` or `65536`) while preserving `0..2` and kept descriptors via `close_range` or multi-batch `/proc/self/fd` `getdents64`, and fails closed (`Err`) when both `close_range` and `/proc/self/fd` are unavailable. -/
def test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let extraKeep ← nondet Std.I32
  let keepFds ← nondet (Slice Std.I32)
  NondetTest.assert (OkPost (api.closeFdsAbove2Except s extraKeep keepFds) (fun _ => True))
  let sHighProc : ChildState :=
    { fdLimit := 64
      closeRangeSupported := false
      closeRangeErrno := ENOSYS
      procSelfFdAvailable := true
      fds :=
        [ (0, { desc := 10, cloexec := false })
        , (1, { desc := 11, cloexec := false })
        , (2, { desc := 12, cloexec := false })
        , (7, { desc := 17, cloexec := true })
        , (42, { desc := 42, cloexec := false })
        , (500, { desc := 50, cloexec := false })
        , (70000, { desc := 70, cloexec := false }) ]
      oracle := [.normal, .normal, .fail EINTR, .dentsBatch 0, .dentsBatch 0, .dentsBatch 0] }
  NondetTest.assert
    (OkPost (api.closeFdsAbove2Except sHighProc 7#i32 (mkSliceI32 2#usize [(-1)#i32, 42#i32])) (fun p =>
      p.1 = .Ok () ∧
      p.2.isOpen 0 = true ∧ p.2.isOpen 1 = true ∧ p.2.isOpen 2 = true ∧
      p.2.isOpen 7 = true ∧ p.2.isOpen 42 = true ∧
      p.2.isOpen 500 = false ∧ p.2.isOpen 70000 = false))
  let sNoProc : ChildState :=
    { closeRangeSupported := false
      closeRangeErrno := EPERM
      procSelfFdAvailable := false
      procOpenErrno := ENOENT
      fds := [(0, { desc := 1, cloexec := false }), (500, { desc := 2, cloexec := false })] }
  NondetTest.assert
    (OkPost (api.closeFdsAbove2Except sNoProc (-1)#i32 (mkSliceI32 0#usize [])) (fun p =>
      p.1 = .Err ENOENT))
  assume (s.status = .running ∧ s.oracle = [])
  assume (s.closeRangeSupported = true ∨ (s.procSelfFdAvailable = true ∧ min s.fdLimit 2147483648 ≥ 4 + Int.ofNat s.fds.length))
  NondetTest.assert
    (OkPost (api.closeFdsAbove2Except s extraKeep keepFds) (fun p =>
      p.1 = .Ok () ∧ CloseAbove2Post s extraKeep keepFds.val p.2))

/-- `readSyncByte` is total, retries `EINTR` until a non-`EINTR` outcome, returns `true` iff 1 byte was read, returns `false` on EOF or error, and closes non-negative `syncR` whenever no seccomp fault intercepts it. -/
def test_postfork_readSyncByte_eintrRetryAndClose
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let syncR ← nondet Std.I32
  if decide (syncR < 0#i32) then
    NondetTest.assert (OkPost (api.readSyncByte s syncR) (fun p => p.1 = false ∧ p.2 = s))
  else if s.status == .running then
    if !oracleHasSeccomp s.oracle then
      NondetTest.assert (OkPost (api.readSyncByte s syncR) (fun p => p.2.isOpen syncR.val = false))
    else
      NondetTest.assert (OkPost (api.readSyncByte s syncR) (fun _ => True))
  else
    NondetTest.assert (OkPost (api.readSyncByte s syncR) (fun _ => True))
  let sRetryOk : ChildState :=
    { fds := [(5, { desc := 55, cloexec := true })]
      descs := [(55, .stream true false false [1#u8])]
      oracle := [.fail EINTR, .fail EINTR] }
  NondetTest.assert
    (OkPost (api.readSyncByte sRetryOk 5#i32) (fun p => p.1 = true ∧ p.2.isOpen 5 = false))
  let sRetryEof : ChildState :=
    { fds := [(5, { desc := 55, cloexec := true })]
      descs := [(55, .stream true false false [])]
      oracle := [.fail EINTR] }
  NondetTest.assert
    (OkPost (api.readSyncByte sRetryEof 5#i32) (fun p => p.1 = false ∧ p.2.isOpen 5 = false))
  let sErrEio : ChildState :=
    { fds := [(5, { desc := 55, cloexec := true })]
      descs := [(55, .stream true false false [1#u8])]
      oracle := [.fail EIO] }
  NondetTest.assert
    (OkPost (api.readSyncByte sErrEio 5#i32) (fun p => p.1 = false ∧ p.2.isOpen 5 = false))

/-- `writeAll` is total, rejects negative descriptors with `EBADF`, retries `EINTR`, and reassembles arbitrary `partialWrite` chunks into the exact full byte slice in `writeLog`. -/
def test_postfork_writeAll_eintrPartialWriteAndReassembly
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let fd ← nondet Std.I32
  let payload ← nondet (Slice Std.U8)
  if decide (fd < 0#i32) then
    NondetTest.assert (OkPost (api.writeAll s fd payload) (fun p => p.1 = .Err EBADF ∧ p.2 = s))
  else
    NondetTest.assert (OkPost (api.writeAll s fd payload) (fun _ => True))
  let sChunked : ChildState :=
    { fds := [(4, { desc := 90, cloexec := true })]
      descs := [(90, .stream false true false [])]
      sig := [(13, .ignore)]
      oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] }
  let msg := mkSliceU8 8#usize [10#u8, 20#u8, 30#u8, 40#u8, 50#u8, 60#u8, 70#u8, 80#u8]
  NondetTest.assert
    (OkPost (api.writeAll sChunked 4#i32 msg) (fun p =>
      p.1 = .Ok () ∧ appendedBytesForDesc sChunked.writeLog p.2.writeLog 90 = msg.val))
  assume (s.status = .running ∧ s.oracle = [] ∧ 0#i32 ≤ fd)
  match s.getFd fd.val with
  | some e =>
    assume (s.getDesc e.desc = .stream false true false [])
    NondetTest.assert
      (OkPost (api.writeAll s fd payload) (fun p =>
        p.1 = .Ok () ∧ appendedBytesForDesc s.writeLog p.2.writeLog e.desc = payload.val))
  | none =>
    NondetTest.assert
      (OkPost (api.writeAll s fd payload) (fun p => p.1 = .Err EBADF))

/-- `runChild` is total, satisfies `RunChildSafetyPost` across arbitrary `s.oracle` and flag combinations (`status` is `.exited 127`, `.exited 125` on sync-barrier EOF preserving `closedBeforeSyncRead`, or `.execd img`), and always reaches `RunChildExecPost` when `ValidRunChildExecPre` holds. -/
def test_postfork_runChild_safetyAndExecPost
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let flags ← nondet Std.U32
  let syncR ← nondet Std.I32
  let inFd ← nondet Std.I32
  let outFd ← nondet Std.I32
  let errFd ← nondet Std.I32
  let repW ← nondet Std.I32
  let closeFds ← nondet (Slice Std.I32)
  let keepFds ← nondet (Slice Std.I32)
  let cwd? ← nondet (Option Bytes)
  let path ← nondet Bytes
  let argv ← nondet (List Bytes)
  let envp ← nondet (List Bytes)
  if s.status == .running then
    NondetTest.assert
      (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp)
        (RunChildSafetyPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path argv envp))
  else
    NondetTest.assert
      (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp)
        (fun _ => True))
  assume (ValidRunChildExecPre s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path)
  NondetTest.assert
    (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp)
      (RunChildExecPost s flags syncR inFd outFd errFd repW closeFds.val keepFds.val cwd? path argv envp))

/-- `runChild` universally enforces exact pre-`execve` validation, stage-tagged uniform failure wire bytes (`STAGE_VALIDATE=1`, `STAGE_PROCESS_GROUP=2`, `STAGE_FD_SETUP=4`, `STAGE_CLOSE_UNKEPT=5`, `STAGE_CHDIR=6`, `STAGE_EXECVE=7`), broken-`rep_w` `SIGPIPE`-immunity, sync-barrier EOF `_exit(125)` with `closeFds` closed before `read1`, and `/proc/self/fd`-unavailable fail-closed reporting. -/
def test_postfork_runChild_validationStagesAndBarrier
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let flags ← nondet Std.U32
  let syncR ← nondet Std.I32
  let inFd ← nondet Std.I32
  let outFd ← nondet Std.I32
  let errFd ← nondet Std.I32
  let repW ← nondet Std.I32
  let closeFds ← nondet (Slice Std.I32)
  let keepFds ← nondet (Slice Std.I32)
  let cwd? ← nondet (Option Bytes)
  let path ← nondet Bytes
  let argv ← nondet (List Bytes)
  let envp ← nondet (List Bytes)
  assume (s.status = .running ∧ s.oracle = [])
  if decide (repW < 0#i32) then
    NondetTest.assert
      (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
        s'.status = .exited 127#i32 ∧ s'.writeLog = s.writeLog))
  else
    match s.getFd repW.val with
    | none => pure ()
    | some repEnt =>
      match s.getDesc repEnt.desc with
      | .stream _ true false _ =>
        if !validFlagsSpec flags then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 1#u8 EINVAL))
        else if !validSignsSpec flags syncR inFd outFd errFd then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 1#u8 EBADF))
        else if !validRunChildNoOverlap flags syncR inFd outFd errFd repW closeFds.val keepFds.val then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 1#u8 EINVAL))
        else if flagSet flags FLAG_SET_PGID && decide (s.pid > 0) && decide (s.pid = s.sid) then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 2#u8 EPERM))
        else if (flagSet flags FLAG_HAS_SYNC_BARRIER && !s.isOpen syncR.val) ||
            (flagSet flags FLAG_REDIRECT_STDIO && (!s.isOpen inFd.val || !s.isOpen outFd.val || !s.isOpen errFd.val)) ||
            keepFds.val.any (fun k => decide (0#i32 ≤ k) && !s.isOpen k.val) then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 4#u8 EBADF))
        else if flagSet flags FLAG_HAS_SYNC_BARRIER then
          match s.getFd syncR.val with
          | none => pure ()
          | some syncEnt =>
            match s.getDesc syncEnt.desc with
            | .stream true _ _ [] =>
              NondetTest.assert
                (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
                  s'.status = .exited 125#i32 ∧
                  s'.writeLog = s.writeLog ∧
                  closedBeforeSyncRead (s'.trace.drop s.trace.length) closeFds.val syncR))
            | .stream true _ _ (_ :: _) =>
              if flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
                  !s.closeRangeSupported && !s.procSelfFdAvailable &&
                  decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) then
                NondetTest.assert
                  (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
                    s'.status = .exited 127#i32 ∧
                    appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                      expectedFailureWireBytes 5#u8 (sanitizeErrno s.procOpenErrno)))
              else
                pure ()
            | _ => pure ()
        else if flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 &&
            !s.closeRangeSupported && !s.procSelfFdAvailable &&
            decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc =
                expectedFailureWireBytes 5#u8 (sanitizeErrno s.procOpenErrno)))
        else if (!flagSet flags FLAG_CLOSE_UNKEPT_ABOVE2 ||
              s.closeRangeSupported || s.procSelfFdAvailable) &&
            decide (min s.fdLimit 2147483648 ≥ minRunChildFdSlack flags + Int.ofNat s.fds.length) then do
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds (some []) path argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 6#u8 ENOENT))
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds none [] argv envp) (fun s' =>
              s'.status = .exited 127#i32 ∧
              appendedBytesForDesc s.writeLog s'.writeLog repEnt.desc = expectedFailureWireBytes 7#u8 ENOENT))
        else
          pure ()
      | .stream _ true true _ =>
        if !validFlagsSpec flags then
          NondetTest.assert
            (OkPost (api.runChild s flags syncR inFd outFd errFd repW closeFds keepFds cwd? path argv envp) (fun s' =>
              s'.status = .exited 127#i32))
        else
          pure ()
      | _ => pure ()

/-- `ChildState` syscall transitions universally model Linux `7.1.6` empty `execve` `argv = []` (`[[]]`), `close_range` `!closeRangeSupported` precedence over `EINVAL`, `dup2(fd, fd)` above `RLIMIT_NOFILE`, `F_DUPFD_CLOEXEC` `EBADF` > `EINVAL` precedence, invalid `sigaction` signals (`< 1`, `> 64`, `9`, `19`, `32`, `33`), `CLONE_NEWPID` `sid = 0` `setpgid` vs session-leader `EPERM`, and `brokenPipe` `SIGPIPE` delivery vs `EPIPE` propagation through `api.writeAll`. -/
def test_postfork_worldModel_linuxKernelEdgeInvariants
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let s ← nondet ChildState
  let fd ← nondet Std.I32
  let newFd ← nondet Std.I32
  let minFd ← nondet Std.I32
  let first ← nondet Std.U32
  let last ← nondet Std.U32
  let crFlags ← nondet Std.U32
  let sig ← nondet Std.I32
  let path ← nondet Bytes
  let argHead ← nondet Bytes
  let argTail ← nondet (List Bytes)
  let envp ← nondet (List Bytes)
  let payload ← nondet (Slice Std.U8)
  assume (s.status = .running ∧ s.oracle = [])
  if !path.isEmpty then do
    NondetTest.assert
      (OkPost (sys.execve s path [] envp) (fun p =>
        p.1 = 0#i32 ∧ ∃ img, p.2.status = .execd img ∧ img.argv = [[]]))
    NondetTest.assert
      (OkPost (sys.execve s path (argHead :: argTail) envp) (fun p =>
        p.1 = 0#i32 ∧ ∃ img, p.2.status = .execd img ∧ img.argv = argHead :: argTail))
  else
    pure ()
  if !s.closeRangeSupported then
    NondetTest.assert
      (OkPost (sys.close_range s first last crFlags) (fun p =>
        p.1 = .Err (sanitizeErrno s.closeRangeErrno) ∧ p.2.fds = s.fds))
  else if decide (first.val > last.val) || (crFlags &&& 4294967289#u32) != 0#u32 then
    NondetTest.assert
      (OkPost (sys.close_range s first last crFlags) (fun p =>
        p.1 = .Err EINVAL ∧ p.2.fds = s.fds))
  else
    pure ()
  match s.getFd fd.val with
  | some e =>
    NondetTest.assert
      (OkPost (sys.dup2 s fd fd) (fun p => p.1 = .Ok () ∧ p.2.getFd fd.val = some e))
    if fd != newFd && (decide (newFd.val < 0) || decide (newFd.val ≥ s.fdLimit)) then
      NondetTest.assert
        (OkPost (sys.dup2 s fd newFd) (fun p => p.1 = .Err EBADF ∧ p.2.fds = s.fds))
    else
      pure ()
    if decide (minFd.val < 0) || decide (minFd.val ≥ s.fdLimit) then
      NondetTest.assert
        (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) (fun p => p.1 = .Err EINVAL ∧ p.2.fds = s.fds))
    else
      pure ()
    if decide (0#i32 ≤ fd) && !payload.val.isEmpty then
      match s.getDesc e.desc with
      | .stream _ true true _ =>
        if s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13 then
          NondetTest.assert
            (OkPost (api.writeAll s fd payload) (fun p =>
              p.1 = .Err EPIPE ∧ p.2.status = .signaled 13#i32))
        else
          NondetTest.assert
            (OkPost (api.writeAll s fd payload) (fun p =>
              p.1 = .Err EPIPE ∧ p.2.status = .running))
      | _ => pure ()
    else
      pure ()
  | none =>
    NondetTest.assert
      (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) (fun p => p.1 = .Err EBADF ∧ p.2.fds = s.fds))
  if isInvalidSigactionSig sig then do
    NondetTest.assert (OkPost (sys.sig_dfl s sig) (fun p => p.1 = .Err EINVAL))
    NondetTest.assert (OkPost (sys.sig_ign s sig) (fun p => p.1 = .Err EINVAL))
  else
    pure ()
  if decide (s.pid > 0) && decide (s.pid = s.sid) then
    NondetTest.assert (OkPost (sys.setpgid_self s) (fun p => p.1 = .Err EPERM ∧ p.2.pgid = s.pgid))
  else
    NondetTest.assert (OkPost (sys.setpgid_self s) (fun p => p.1 = .Ok () ∧ p.2.pgid = s.pid))

/-- Caller-agnostic `PostFork.Impl.Internal.mkHostOps` makes zero OS hook calls (`callCount = 0`) on invalid `ChildSpecM`, rejects closed caller handles/descriptors (`EBADF = 9`), closes parent ends safely, resolves `ArgToken` & `ForkMode` without length caps, retries `EINTR` across `writeOnce`/`readOnce`/`waitOnce`, preserves `EPIPE` tolerance on `releaseBarrier`, returns `AbortOutcome.aborted`/`failedBeforeBarrier` cleanly, and decodes uniform 8-byte failure wire frames. -/
def test_postfork_hostOps_validationBarrierEintrAndWire
    {runner} [NondetTest runner]
    (mkOps : LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32) : runner Unit := do
  let spec ← nondet (ChildSpecM Int32)
  let stage ← nondet FailureStage
  let errVal ← nondet UInt32
  let waitSt ← nondet ChildWaitStatus
  let extraArgCount ← nondet Nat
  let tokFd ← nondet Int32
  let fMode ← nondet ForkMode
  let ops := mkOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps
  if !LeanSwe.PostFork.Model.validateSpec spec then do
    let (rSpawn, stSpawn) := (ops.spawn spec).run {}
    NondetTest.assert ((∃ e, rSpawn = .error e ∧ e.kind = .invalidInput) ∧ stSpawn.callCount = 0)
    let (rBar, stBar) := (ops.spawnWithBarrier spec).run {}
    NondetTest.assert ((∃ e, rBar = .error e ∧ e.kind = .invalidInput) ∧ stBar.callCount = 0)
  else
    pure ()
  let largeArgs := #[ArgToken.lit "/bin/echo"] ++ (List.replicate extraArgCount (ArgToken.lit "a")).toArray
  let (rLarge, stLarge) :=
    (ops.spawn { path := "/bin/echo", argv := largeArgs, forkMode := fMode }).run { waitResult := waitSt }
  NondetTest.assert
    (rLarge = .ok { pid := 4242, pgid := none } ∧
      stLarge.spawnedArgv.size = extraArgCount + 1 ∧
      stLarge.spawnedForkMode = fMode)
  let (rTok, stTok) :=
    (ops.spawn
      { path := "/bin/echo"
        argv := #[ArgToken.ofLiteral "/bin/echo", ArgToken.ofHandle tokFd, ArgToken.procSelfFd tokFd, ArgToken.prefixedFd "--fd=" (.raw 5) "x"]
        env := #[("K", "V")]
        processGroup := .newGroup
        forkMode := .immortalThread }).run {}
  NondetTest.assert
    (rTok = .ok { pid := 4242, pgid := some 4242 } ∧
      stTok.setpgidCalls = [(4242, 4242)] ∧
      stTok.spawnedArgv = #["/bin/echo", s!"{tokFd}", s!"/proc/self/fd/{tokFd}", "--fd=5x"] ∧
      stTok.spawnedEnv = #["K=V"] ∧
      stTok.spawnedForkMode = .immortalThread ∧
      stTok.spawnedFlags = LeanSwe.PostFork.Model.flagsOfSpec
        ({ path := "/bin/echo", argv := #[], processGroup := .newGroup } : ChildSpecM Int32) false)
  let closedInit : LeanSwe.PostFork.Model.Internal.HostMockState := { closedCallerFds := [99] }
  let (rClosedStd, _) :=
    (ops.spawn { path := "/bin/true", argv := #[], stdio := .redirect (.raw 99) (.raw 1) (.raw 2) true }).run closedInit
  NondetTest.assert (∃ e, rClosedStd = .error e ∧ e.kind = .sysError ∧ e.errno = some Errno.EBADF)
  let (rClosedKeep, _) :=
    (ops.spawnWithBarrier { path := "/bin/true", argv := #[], fdPolicy := .closeAllAbove2Except #[.handle 99] }).run closedInit
  NondetTest.assert (∃ e, rClosedKeep = .error e ∧ e.kind = .sysError ∧ e.errno = some Errno.EBADF)
  let stBar : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { writeEintrCount := 2
      readEintrCount := 2
      waitEintrCount := 2
      failSetpgidErrno := some Errno.EPERM
      waitResult := waitSt }
  let (rBarOk, stBarMid) :=
    (ops.spawnWithBarrier { path := "/bin/true", argv := #[], processGroup := .newGroup }).run stBar
  match rBarOk with
  | .error _ => NondetTest.assert False
  | .ok pend => do
    NondetTest.assert (stBarMid.syncWritten = ByteArray.empty ∧ stBarMid.hasSpawned = true)
    let (rRelOk, stRelOut) := (ops.releaseBarrier pend).run stBarMid
    NondetTest.assert
      (rRelOk = .ok { pid := 4242, pgid := some 4242 } ∧
        stRelOut.syncWritten = ByteArray.mk #[1] ∧
        stRelOut.closedHandles.contains pend.syncWrite ∧
        stRelOut.closedHandles.contains pend.errRead)
    let stEpipe : LeanSwe.PostFork.Model.Internal.HostMockState :=
      { stBarMid with
        failWriteErrno := some Errno.EPIPE
        repWire := LeanSwe.PostFork.Model.encodeFailureReport .execve Errno.ENOENT
        waitResult := .exited 127 }
    let (rRelEpipe, _) := (ops.releaseBarrier pend).run stEpipe
    let stEpipeEmpty : LeanSwe.PostFork.Model.Internal.HostMockState :=
      { stBarMid with
        failWriteErrno := some Errno.EPIPE
        repWire := ByteArray.empty
        waitResult := waitSt }
    let (rRelEpipeEmpty, stRelEpipeEmptyOut) := (ops.releaseBarrier pend).run stEpipeEmpty
    NondetTest.assert
      ((∃ e cf, rRelEpipe = .error e ∧ e.kind = .childFailed ∧ e.errno = some Errno.ENOENT ∧
          e.childFailure = some cf ∧ cf = { stage := .execve, errno := Errno.ENOENT, waitStatus := some (.exited 127) }) ∧
        (∃ e cf, rRelEpipeEmpty = .error e ∧ e.kind = .childFailed ∧ e.errno = some Errno.EIO ∧
          e.childFailure = some cf ∧ cf = { stage := .wireTruncated, errno := Errno.EIO, waitStatus := some waitSt } ∧
          stRelEpipeEmptyOut.closedHandles.contains pend.syncWrite ∧
          stRelEpipeEmptyOut.closedHandles.contains pend.errRead))
    let (rAbortClean, _) :=
      (ops.abortBarrier pend).run { stBarMid with repWire := ByteArray.empty, waitResult := .exited 125 }
    NondetTest.assert (rAbortClean = .ok (.aborted (.exited 125)))
    let (rAbortFail, _) :=
      (ops.abortBarrier pend).run
        { stBarMid with repWire := LeanSwe.PostFork.Model.encodeFailureReport .fdSetup Errno.EBADF, waitResult := .exited 127 }
    NondetTest.assert
      (rAbortFail = .ok (.failedBeforeBarrier { stage := .fdSetup, errno := Errno.EBADF, waitStatus := some (.exited 127) } (.exited 127)))
  assume (stage ≠ .wireTruncated ∧ 1 ≤ errVal.toNat ∧ errVal.toNat ≤ 4095)
  let (rWireFail, _) :=
    (ops.spawn { path := "/bin/false", argv := #[] }).run
      { readEintrCount := 1
        waitEintrCount := 1
        repWire := LeanSwe.PostFork.Model.encodeFailureReport stage errVal
        waitResult := .exited 127 }
  NondetTest.assert
    (∃ e, rWireFail = .error e ∧ e.kind = .childFailed ∧ e.errno = some errVal ∧
      e.childFailure = some { stage := stage, errno := errVal, waitStatus := some (.exited 127) })
  let (rTrunc, _) :=
    (ops.spawn { path := "/bin/false", argv := #[] }).run
      { repWire := ByteArray.mk #[0x50, 0x01, 7, 0], waitResult := .exited 127 }
  NondetTest.assert
    (∃ e, rTrunc = .error e ∧ e.kind = .childFailed ∧ e.errno = some Errno.EIO ∧
      e.childFailure = some { stage := .wireTruncated, errno := Errno.EIO, waitStatus := some (.exited 127) })

/-- Refinement between pure `PostFork.Model` (`flagsOfSpec` and `validateSpecWith`) and Charon/Aeneas `postfork.child.validate_child_args`: every `FLAG_*` bit matches its exact `ChildSpecM` policy, and `Model.validateSpecWith (· == ·)` is biconditionally equivalent to `api.validateChildArgs = .Ok ()` across all handle-valid specs and fresh internal pipes. -/
def test_postfork_aeneasRefinement_flagsAndValidateChildArgs
    {runner} [NondetTest runner] (api : PostForkAeneasApi) : runner Unit := do
  let spec ← nondet (ChildSpecM Std.I32)
  let withBarrier ← nondet Bool
  let syncR ← nondet Std.I32
  let repW ← nondet Std.I32
  let closeSlice ← nondet (Slice Std.I32)
  let keepSlice ← nondet (Slice Std.I32)
  let fl := specFlagsU32 spec withBarrier
  let hasRedir := match spec.stdio with | .redirect .. => true | .inherit => false
  NondetTest.assert (validFlagsSpec fl = true)
  NondetTest.assert (flagSet fl FLAG_SET_PGID = (spec.processGroup == .newGroup))
  NondetTest.assert (flagSet fl FLAG_RESET_SIGPIPE = (spec.sigpipe == .resetDefault))
  NondetTest.assert (flagSet fl FLAG_HAS_SYNC_BARRIER = withBarrier)
  NondetTest.assert (flagSet fl FLAG_REDIRECT_STDIO = hasRedir)
  NondetTest.assert
    (flagSet fl FLAG_CLOSE_UNKEPT_ABOVE2 =
      (match spec.fdPolicy with | .closeAllAbove2Except _ => true | .inheritNonCloexec _ => false))
  NondetTest.assert
    (flagSet fl FLAG_CLOSE_STDIO_SOURCES =
      (match spec.stdio, spec.fdPolicy with
       | .redirect _ _ _ true, .inheritNonCloexec _ => true
       | _, _ => false))
  let badCloseSrcSpec : ChildSpecM Int32 :=
    { path := "/bin/true"
      argv := #[]
      stdio := .redirect (.raw 5) (.raw 1) (.raw 2) true
      fdPolicy := .inheritNonCloexec #[.raw 5] }
  NondetTest.assert (LeanSwe.PostFork.Model.validateSpec badCloseSrcSpec = false)
  let (inFd, outFd, errFd) := stdioToStdI32Triple spec.stdio
  let keepRefs := LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy
  assume
    (specStringHygieneOk spec = true ∧
      specHandlesValid spec = true ∧
      spec.closeFds.all LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      keepRefs.all LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      closeSlice.val = (spec.closeFds.map fdRefToStdI32).toList ∧
      keepSlice.val = (keepRefs.map fdRefToStdI32).toList ∧
      internalPipesDisjoint withBarrier hasRedir syncR inFd outFd errFd repW closeSlice.val keepSlice.val = true)
  NondetTest.assert
    (OkPost (api.validateChildArgs fl syncR inFd outFd errFd repW closeSlice keepSlice) (fun r =>
      (match r with | .Ok () => true | .Err _ => false) = LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec))

/-- Host marshaling, default-policy invariants, `ArgToken.ref?` & `i32Le` contracts, hygiene rejections, `O(N)` `validateSpec` equivalence, pipe-cleanup, `EBUSY` barrier safety, & closed-`.raw` pipe-collision avoidance: `ChildSpecM` defaults preserve `.resetDefault` `SIGPIPE` and `closeSourcesAbove2 = true`, `ChildSpecM.ofCommand` preserves extra arguments, `forkModeToUInt32` injectively encodes `.direct -> 0` and `.immortalThread -> 1`, `Model.validateSpec` equals `Model.validateSpecWith (fun _ _ => false)` and rejects NUL/sign violations across `path`/`cwd`/`env`/`ArgToken`, `flattenForkArgs` packs 32-bit slots in linear layout while clamping negative `.raw` slots to `-1`, and `mkHostOps` filters closed `.raw` descriptors before `mkPipeCloexec`, cleans up pipes on `pipe2`/`fork`/`read`/`wait` failure, and fails fast without deadlocking when `releaseBarrier` or `abortBarrier` receives `EBUSY`. -/
def test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    {runner} [NondetTest runner]
    (flattenFn :
      Option Int32 → Int32 →
      _root_.Array (FdRef Int32) → _root_.Array (FdRef Int32) → _root_.Array (FdRef Int32) →
      _root_.Array (ArgToken Int32) →
      LeanSwe.PostFork.Model.Internal.FlattenedForkArgsM Int32 :=
      LeanSwe.PostFork.Impl.Internal.flattenForkArgs)
    (modeFn : ForkMode → UInt32 := LeanSwe.PostFork.Impl.Internal.forkModeToUInt32)
    (mkOps :
      LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 :=
      fun raw => LeanSwe.PostFork.Impl.Internal.mkHostOps raw) : runner Unit := do
  let syncRead? ← nondet (Option Int32)
  let errWrite ← nondet Int32
  let stdioRefs ← nondet (_root_.Array (FdRef Int32))
  let closeRefs ← nondet (_root_.Array (FdRef Int32))
  let keepRefs ← nondet (_root_.Array (FdRef Int32))
  let argv ← nondet (_root_.Array (ArgToken Int32))
  let specAny ← nondet (ChildSpecM Int32)
  NondetTest.assert (modeFn .direct = 0 ∧ modeFn .immortalThread = 1)
  NondetTest.assert
    ((ChildSpecM.ofCommand "/bin/echo" #["a", "b"] : ChildSpecM Int32) =
      { path := "/bin/echo", argv := #[.lit "/bin/echo", .lit "a", .lit "b"] } ∧
      (ChildSpecM.ofCommand "/bin/true" : ChildSpecM Int32) =
        { path := "/bin/true", argv := #[.lit "/bin/true"] })
  NondetTest.assert
    (({ path := "/bin/true", argv := #[] } : ChildSpecM Int32).sigpipe = .resetDefault ∧
      ({ path := "/bin/true", argv := #[] } : ChildSpecM Int32).stdio = .inherit ∧
      ({ path := "/bin/true", argv := #[] } : ChildSpecM Int32).processGroup = .inherit ∧
      ({ path := "/bin/true", argv := #[] } : ChildSpecM Int32).forkMode = .direct ∧
      (StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) : StdioPlan Int32) =
        StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) true ∧
      (ArgToken.prefixedFd "--fd=" (.raw 5) : ArgToken Int32) =
        ArgToken.prefixedFd "--fd=" (.raw 5) "" ∧
      (FdPolicy.inheritNonCloexec : FdPolicy Int32) =
        FdPolicy.inheritNonCloexec #[] ∧
      (FdPolicy.closeAllAbove2Except : FdPolicy Int32) =
        FdPolicy.closeAllAbove2Except #[] ∧
      LeanSwe.PostFork.Model.packI32Le 0x01020304 = ByteArray.mk #[0x04, 0x03, 0x02, 0x01] ∧
      LeanSwe.PostFork.Model.packI32Le (-0x01020304) = ByteArray.mk #[0xFC, 0xFC, 0xFD, 0xFE] ∧
      LeanSwe.PostFork.Model.ArgToken.ref? (.lit "a" : ArgToken Int32) = none ∧
      LeanSwe.PostFork.Model.ArgToken.ref? (.fdDecimal (.raw 5) : ArgToken Int32) = some (.raw 5) ∧
      LeanSwe.PostFork.Model.ArgToken.ref? (.prefixedFd "p" (.handle 7) "s" : ArgToken Int32) = some (.handle 7) ∧
      LeanSwe.PostFork.Model.i32Le (-5) 3 = true ∧
      LeanSwe.PostFork.Model.i32Le 3 3 = true ∧
      LeanSwe.PostFork.Model.i32Le 3 (-5) = false ∧
      LeanSwe.PostFork.Model.i32Le Int32.minValue Int32.maxValue = true ∧
      LeanSwe.PostFork.Model.i32Le Int32.maxValue Int32.minValue = false)
  NondetTest.assert
    (LeanSwe.PostFork.Model.validateSpec specAny =
      LeanSwe.PostFork.Model.validateSpecWith (fun _ _ => false) specAny)
  NondetTest.assert
    (LeanSwe.PostFork.Model.validateSpec ({ path := "a\x00b", argv := #[] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], cwd := some "d\x00e" } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("", "1")] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("A=B", "1")] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("K\x00", "1")] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("K", "V\x00")] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.lit "x\x00"] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.fdDecimal (.raw (-1))] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p\x00" (.raw 3) "s"] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p" (.raw 3) "s\x00"] } : ChildSpecM Int32) = false ∧
      LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p" (.raw (-1)) "s"] } : ChildSpecM Int32) = false)
  let flat := flattenFn syncRead? errWrite stdioRefs closeRefs keepRefs argv
  NondetTest.assert
    (flat.metaSlots.size = 20 ∧
      flat.closeSlots.size = 4 * closeRefs.size ∧
      flat.keepSlots.size = 4 * keepRefs.size ∧
      flat.argPrefixes.size = argv.size ∧
      flat.argSuffixes.size = argv.size ∧
      flat.argSlots.size = 4 * argv.size)
  let flatHijack :=
    flattenFn (some 50) 60 #[.raw (-2), .raw Int32.minValue, .handle 70]
      #[.raw (-2)] #[.raw 4] #[.lit "cmd", .fdDecimal (.raw (-2)), .prefixedFd "p=" (.handle 80) ":s"]
  NondetTest.assert
    (flatHijack.handles = #[50, 60, 70, 80] ∧
      flatHijack.metaSlots = LeanSwe.PostFork.Model.packI32LeList [-2, -3, -1, -1, -4] ∧
      flatHijack.closeSlots = LeanSwe.PostFork.Model.packI32LeList [-1] ∧
      flatHijack.keepSlots = LeanSwe.PostFork.Model.packI32LeList [4] ∧
      flatHijack.argPrefixes = #["cmd", "", "p="] ∧
      flatHijack.argSuffixes = #["", "", ":s"] ∧
      flatHijack.argSlots = LeanSwe.PostFork.Model.packI32LeList [-1, -1, -5] ∧
      (flattenFn none 60 #[] #[] #[.raw 0x01020304] #[]).keepSlots =
        ByteArray.mk #[0x04, 0x03, 0x02, 0x01])
  let ops := mkOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps
  NondetTest.assert
    (∃ stCol,
      (ops.spawn
        { path := "/bin/true"
          argv := #[]
          closeFds := #[.raw 10, .raw 11, .raw 5, .handle 7] }).run { closedCallerFds := [10, 11] } =
        (.ok { pid := 4242, pgid := none }, stCol) ∧
      stCol.spawnedCloseRefs = #[.raw 5, .handle 7, .handle 10])
  let busyRaw : LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 :=
    { LeanSwe.PostFork.Model.Internal.mockPosixHostOps with
      closeFd := fun _ => do
        modify fun st => { st with callCount := st.callCount + 1 }
        return .error Errno.EBUSY }
  let epermRaw : LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 :=
    { LeanSwe.PostFork.Model.Internal.mockPosixHostOps with
      closeFd := fun _ => do
        modify fun st => { st with callCount := st.callCount + 1 }
        return .error Errno.EPERM }
  NondetTest.assert
    ((∃ e st,
        (ops.spawn { path := "/bin/true", argv := #[] }).run { failForkErrno := some Errno.EAGAIN } = (.error e, st) ∧
        e.errno = some Errno.EAGAIN ∧ st.closedHandles = [10, 11]) ∧
      (∃ e st,
        (ops.spawnWithBarrier { path := "/bin/true", argv := #[] }).run { failNextPipeAt := some 1 } = (.error e, st) ∧
        e.errno = some Errno.EMFILE ∧ st.closedHandles = [10, 11]) ∧
      (∃ e st,
        (ops.spawnWithBarrier { path := "/bin/true", argv := #[] }).run { failForkErrno := some Errno.EAGAIN } = (.error e, st) ∧
        e.errno = some Errno.EAGAIN ∧ st.closedHandles = [10, 13, 12, 11]) ∧
      (∃ e st,
        (ops.spawn { path := "/bin/true", argv := #[] }).run { failReadErrno := some Errno.EIO } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.closedHandles = [10, 11] ∧ st.callCount = 5) ∧
      (∃ e st,
        (ops.spawn { path := "/bin/false", argv := #[] }).run
          { readEintrCount := 1
            repWire := LeanSwe.PostFork.Model.encodeFailureReport .execve Errno.ENOENT
            failWaitErrno := some Errno.ECHILD } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.ECHILD ∧ st.closedHandles = [10, 11]) ∧
      (∃ e st,
        (ops.releaseBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
          { failWriteErrno := some Errno.EIO, waitResult := .exited 125 } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.closedHandles = [10, 13] ∧ st.callCount = 5) ∧
      (∃ e st,
        ((mkOps busyRaw).releaseBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
          { failWriteErrno := some Errno.EIO } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.callCount = 3 ∧ st.closedHandles = []) ∧
      (∃ e st,
        ((mkOps busyRaw).abortBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EBUSY ∧ st.callCount = 1) ∧
      (∃ e st,
        (ops.releaseBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
          { allocSyncWriteFd := 13, closedHandles := [10] } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EBADF ∧ st.syncWritten = ByteArray.empty ∧ st.callCount = 1) ∧
      (∃ e st,
        (ops.releaseBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
          { failWriteErrno := some 75 } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some 75 ∧ st.callCount = 2 ∧ st.closedHandles = []) ∧
      (∃ e st,
        ((mkOps epermRaw).releaseBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
          { failWriteErrno := some Errno.EIO } = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.callCount = 3 ∧ st.closedHandles = []) ∧
      (∃ e st,
        ((mkOps epermRaw).abortBarrier { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} = (.error e, st) ∧
        e.kind = .sysError ∧ e.errno = some Errno.EPERM ∧ st.callCount = 1))

/-- External trust-boundary assumptions for `LeanSwe.PostFork` (`libpostfork.a` `#![no_std]` Rust FFI + `postfork::sys` 1-syscall wrappers + `postfork_shim.c` 1-syscall host primitives + Linux `7.1` child kernel ABI). -/
def externalAssumptions : List AssumptionObligation :=
  [ { «name» := "LeanSwe.PostFork.assume_postfork_stdioCycleAndCloexec"
      subject := "LeanSwe.PostFork.spawn"
      formalPred? := none }
  , { «name» := "LeanSwe.PostFork.assume_postfork_errPipeWireAndBrokenPipe"
      subject := "LeanSwe.PostFork.spawn"
      formalPred? := none }
  , { «name» := "LeanSwe.PostFork.assume_postfork_syncBarrierReleaseAndAbort"
      subject := "LeanSwe.PostFork.spawnWithBarrier"
      formalPred? := none }
  , { «name» := "LeanSwe.PostFork.assume_postfork_argTokenAndImmortalThread"
      subject := "LeanSwe.PostFork.spawn"
      formalPred? := none }
  , { «name» := "LeanSwe.PostFork.assume_postfork_closeUnkeptProcSelfFdFallback"
      subject := "LeanSwe.PostFork.spawn"
      formalPred? := none } ]

/-- Complete `(request × PostForkErrorKind)` error-coverage matrix across all `4` public host entrypoints (`spawn`, `spawnWithBarrier`, `releaseBarrier`, `abortBarrier`). -/
def errorCoverage : List (ErrorObligation PostForkErrorKind) :=
  [ { request := "LeanSwe.PostFork.spawn"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_spawn_invalidInput" .real }
  , { request := "LeanSwe.PostFork.spawn"
      errorKind := .sysError
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_spawn_sysError" .real }
  , { request := "LeanSwe.PostFork.spawn"
      errorKind := .childFailed
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_spawn_childFailed" .real }
  , { request := "LeanSwe.PostFork.spawnWithBarrier"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_spawnWithBarrier_invalidInput" .real }
  , { request := "LeanSwe.PostFork.spawnWithBarrier"
      errorKind := .sysError
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_spawnWithBarrier_sysError" .real }
  , { request := "LeanSwe.PostFork.spawnWithBarrier"
      errorKind := .childFailed
      justification := .provedImpossible "LeanSwe.PostFork.Proofs.spawnWithBarrier_never_childFailed" }
  , { request := "LeanSwe.PostFork.releaseBarrier"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.PostFork.Proofs.releaseBarrier_never_invalidInput" }
  , { request := "LeanSwe.PostFork.releaseBarrier"
      errorKind := .sysError
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_releaseBarrier_sysError" .real }
  , { request := "LeanSwe.PostFork.releaseBarrier"
      errorKind := .childFailed
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_releaseBarrier_childFailed" .real }
  , { request := "LeanSwe.PostFork.abortBarrier"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.PostFork.Proofs.abortBarrier_never_invalidInput" }
  , { request := "LeanSwe.PostFork.abortBarrier"
      errorKind := .sysError
      justification := .tested "LeanSwe.PostFork.RuntimeTests.err_abortBarrier_sysError" .real }
  , { request := "LeanSwe.PostFork.abortBarrier"
      errorKind := .childFailed
      justification := .provedImpossible "LeanSwe.PostFork.Proofs.abortBarrier_never_childFailed" } ]

end LeanSwe.PostFork
