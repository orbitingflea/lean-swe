import Fuzz.Common.Coverage
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.CmdLine.Gen
import Fuzz.CmdLine.Subproc
import Fuzz.LinuxSyscall.Env
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.Model
import LeanSwe.EnvVars.Raw.Interface

namespace Fuzz.CmdLine

open Fuzz.Common
open LeanSwe
open LeanSwe.CmdLine

@[extern "leanswe_cmdfuzz_save_stdio"]
private opaque saveStdioRaw (unused : UInt32) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_reset_streams"]
private opaque resetStreamsRaw (unused : UInt32) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_restore_stdio"]
private opaque restoreStdioRaw (unused : UInt32) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_close_slot"]
private opaque closeSlotRaw (slot : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_setup_pipe_in"]
private opaque setupPipeInRaw (ba : @& ByteArray) (nonblock closeWriter : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_setup_memfd_in"]
private opaque setupMemfdInRaw (ba : @& ByteArray) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_setup_special"]
private opaque setupSpecialRaw (slot kind : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_setup_capture"]
private opaque setupCaptureRaw (slot nonblock : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_get_pipe_cap"]
private opaque getPipeCapRaw (slot : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_drain_fd"]
private opaque drainFdRaw (fd cap : UInt32) : BaseIO ByteArray

@[extern "leanswe_cmdfuzz_write_fd"]
private opaque writeFdRaw (fd : UInt32) (ba : @& ByteArray) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_close_fd"]
private opaque closeFdRaw (fd : UInt32) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_setup_pty"]
private opaque setupPtyRaw (echoOff : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_set_env_bytes"]
private opaque setEnvBytesRaw (k v : @& ByteArray) (ovw : UInt8) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_unset_env_bytes"]
private opaque unsetEnvBytesRaw (k : @& ByteArray) : BaseIO UInt32

@[extern "leanswe_cmdfuzz_clear_env"]
private opaque clearEnvRaw (unused : UInt32) : BaseIO UInt32

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque armSigalrmRaw (usec : UInt32) (saRestart : UInt8) : BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque disarmSigalrmRaw (unused : UInt32) : BaseIO Unit

@[extern "leanswe_cmdfuzz_run_on_1mib_stack"]
private opaque runOn1MibStackRaw (fn : Unit → IO UInt32) : BaseIO UInt32

@[extern "leanswe_envvars_environ"]
private opaque listEnvironRaw : BaseIO (Array ByteArray)

private structure EpisodeCtx where
  world : Model.StdioWorld := {}
  stdinFeedFd? : Option UInt32 := none
  stdinIsPty : Bool := false
  stdoutCapFd? : Option UInt32 := none
  stderrCapFd? : Option UInt32 := none
  armedSigalrmUsec? : Option UInt32 := none
  lastStdinBytes : ByteArray := ByteArray.empty
  hadPriorReadErr : Bool := false

private def pipeSmallSentinel : UInt32 := 0xfffffffd
private def invalidFdSentinel : UInt32 := 0xfffffffe
private def closedWriterSentinel : UInt32 := 0xffffffff

private def closeOptFd (fd? : Option UInt32) : IO Unit := do
  if let some fd := fd? then
    let _ ← closeFdRaw fd

private def drainAllFd (fd : UInt32) : IO ByteArray := do
  let mut acc := ByteArray.empty
  for _ in List.range 16 do
    let chunk ← drainFdRaw fd 65536
    if chunk.isEmpty then
      break
    acc := acc ++ chunk
  return acc

private def classifyIoError (err : IO.Error) : Option Model.StdioErrClass :=
  match err with
  | .invalidArgument _ 9 _ => some .badFd
  | .inappropriateType _ 21 _ => some .isDirectory
  | .resourceExhausted _ 28 _ => some .noSpace
  | .resourceExhausted _ 27 _ => some .fileTooLarge
  | .otherError 27 _ => some .fileTooLarge
  | .resourceExhausted _ 11 _ => some .wouldBlock
  | .resourceVanished 32 _ => some .brokenPipe
  | .interrupted _ 4 _ => some .interrupted
  | .hardwareFault 5 _ => some .hardwareFault
  | _ => none

private def ioOutcomeMatches {α : Type} [BEq α]
    (expected : Model.IoStepOutcome α) (actual : Except IO.Error α) : Bool :=
  match expected, actual with
  | .returned a, .ok b => a == b
  | .threwIo c, .error e => some c == classifyIoError e
  | _, _ => false

private def byteContains (bs : ByteArray) (b : UInt8) : Bool := Id.run do
  for i in List.range bs.size do
    if bs[i]! == b then
      return true
  return false

private def entryHasKey (entry kBs : ByteArray) : Bool :=
  entry.size > kBs.size &&
  entry.extract 0 kBs.size == kBs &&
  entry[kBs.size]! == '='.toNat.toUInt8

private def envSetInWorld (w : Model.StdioWorld) (kBs vBs : ByteArray) (ovw : Bool) : Model.StdioWorld :=
  if byteContains kBs 0 || byteContains vBs 0 || kBs.isEmpty || byteContains kBs ('='.toNat.toUInt8) then
    w
  else
    let existsAlready := w.rawEnviron.any (fun e => entryHasKey e kBs)
    if existsAlready && !ovw then
      w
    else
      let filtered := w.rawEnviron.filter (fun e => !entryHasKey e kBs)
      let entry := kBs ++ ByteArray.mk #['='.toNat.toUInt8] ++ vBs
      { w with rawEnviron := filtered ++ [entry] }

private def envUnsetInWorld (w : Model.StdioWorld) (kBs : ByteArray) : Model.StdioWorld :=
  if byteContains kBs 0 || kBs.isEmpty || byteContains kBs ('='.toNat.toUInt8) then
    w
  else
    { w with rawEnviron := w.rawEnviron.filter (fun e => !entryHasKey e kBs) }

private def cmdErrorEq (a b : CmdLineError) : Bool :=
  a.kind == b.kind && a.message == b.message && a.target == b.target

private def exceptCmdEq {α : Type} [BEq α] (a b : Except CmdLineError α) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e1, .error e2 => cmdErrorEq e1 e2
  | _, _ => false

private def hasInvalidUtf8ContSkip (bs : ByteArray) : Bool := Id.run do
  let mut i := 0
  while i < bs.size do
    let b := bs[i]!
    if b >= 0x80 then
      match Model.validateUtf8OneWidth bs i with
      | some (_, w) => i := i + w
      | none =>
        let next := Model.skipUtf8ContinuationBytes bs (i + 1)
        if next > i + 1 then
          return true
        i := next
    else
      i := i + 1
  return false

private def classifyReadLineSuccess (before : Model.StdioChannelState) (line : String) : String :=
  match before.backing with
  | .nullDev => "ok.eof_null"
  | .pipe _ _ _ _ _ =>
    if line.isEmpty then "ok.eof_pipe"
    else "ok.some_ascii"
  | .ptySlave segs _ _ =>
    match segs with
    | [] => "ok.eof_pipe"
    | none :: _ => "ok.eof_pty_resume"
    | some _ :: _ => "ok.some_ascii"
  | _ => if line.isEmpty then "ok.eof_null" else "ok.some_ascii"

private def recordReadLineBuckets (before after : Model.StdioChannelState) (hadPriorReadErr : Bool)
    (out : Model.IoStepOutcome (Option String)) (tracker : CoverageTracker) : CoverageTracker :=
  let _ := after
  match out with
  | .threwIo c =>
    let bkt := match before.backing, c with
      | .closedFd, .badFd => "err.ebadf_closed"
      | .wrongMode, .badFd => "err.ebadf_wronly"
      | .dirFd, .isDirectory => "err.eisdir"
      | .pipe pending _ _ _ _, .wouldBlock =>
        if pending.isEmpty then "err.eagain_empty" else "err.eagain_partial_drop"
      | _, .interrupted => "err.eintr"
      | .ptySlave _ _ _, .hardwareFault => "err.pty_eio"
      | .ptyHungup _, .hardwareFault => "err.pty_eio"
      | _, _ => "err.other"
    tracker.record "readLine" bkt
  | .returned none =>
    let bkt := match before.backing with
      | .ptySlave (none :: _) _ _ => "ok.eof_pty_resume"
      | .nullDev | .fullDev => "ok.eof_null"
      | _ => "ok.eof_pipe"
    tracker.record "readLine" bkt
  | .returned (some line) => Id.run do
    let mut t := if hadPriorReadErr then tracker.record "readLine" "ok.recover_after_err" else tracker
    let rawChunk :=
      match before.backing with
      | .pipe pending _ _ _ _ =>
        match Model.splitLineBytes pending with | some (l, _) => l | none => pending
      | .regFile bs pos _ =>
        let tail := bs.extract pos bs.size
        match Model.splitLineBytes tail with | some (l, _) => l | none => tail
      | .ptySlave segs _ _ =>
        match Model.consumePtySegments ByteArray.empty segs with
        | some (chunk, _) => chunk
        | none => ByteArray.empty
      | _ => ByteArray.empty
    if rawChunk.size > 8192 then
      t := t.record "readLine" "ok.some_large_over_8192"
    if byteContains rawChunk 0 then
      t := t.record "readLine" "ok.some_nul_embedded"
    if rawChunk.size >= 2 && rawChunk[rawChunk.size - 1]! == 0x0a && rawChunk[rawChunk.size - 2]! == 0x0d then
      t := t.record "readLine" "ok.some_crlf_and_crcrlf"
    if !rawChunk.isEmpty && rawChunk[rawChunk.size - 1]! != 0x0a then
      t := t.record "readLine" "ok.some_no_trailing_lf"
    if rawChunk == ByteArray.mk #[0x0a] then
      t := t.record "readLine" "ok.some_blank_lf"
    if rawChunk.toList.dropLast.any (· == 0x0d) then
      t := t.record "readLine" "ok.some_internal_cr"
    if (List.range (rawChunk.size - 2)).any (fun i =>
        i + 2 < rawChunk.size && rawChunk[i]! == 0xed && rawChunk[i + 1]! == 0xa0 && rawChunk[i + 2]! == 0x80) then
      t := t.record "readLine" "ok.some_utf8_lossy_surrogate"
    if rawChunk.toList.take 2 == [0xc0, 0xaf] then
      t := t.record "readLine" "ok.some_utf8_lossy_overlong"
    if hasInvalidUtf8ContSkip rawChunk then
      t := t.record "readLine" "ok.some_utf8_lossy_cont_skip"
    if (String.fromUTF8? rawChunk).isSome && rawChunk.toList.any (· >= 0x80) then
      t := t.record "readLine" "ok.some_utf8_valid"
    if rawChunk.toList.all (· < 0x80) && !line.isEmpty then
      t := t.record "readLine" "ok.some_ascii"
    if t.total == tracker.total then
      t := t.record "readLine" (classifyReadLineSuccess before line)
    t

private def recordWriteBuckets (opName : String) (before : Model.StdioChannelState)
    (text : String) (hadPriorErr : Bool) (out : Model.IoStepOutcome Unit) (tracker : CoverageTracker) : CoverageTracker :=
  match out with
  | .returned () =>
    if text.isEmpty then
      match before.backing with
      | .pipe _ _ _ true _ =>
        let t := tracker.record opName "ok.empty_on_broken_pipe"
        if hadPriorErr && opName == "writeOut" then t.record opName "ok.empty_after_prior_err" else t
      | .fullDev =>
        let t := tracker.record opName "ok.empty_on_full_dev"
        if hadPriorErr && opName == "writeOut" then t.record opName "ok.empty_after_prior_err" else t
      | _ =>
        if hadPriorErr && opName == "writeOut" then tracker.record opName "ok.empty_after_prior_err"
        else tracker
    else if text.contains (Char.ofNat 0) && opName == "writeOut" then
      tracker.record opName "ok.nul_embedded"
    else
      tracker.record opName "ok.nonempty"
  | .threwIo c =>
    let bkt := match before.backing, c with
      | _, .brokenPipe => "err.epipe"
      | _, .noSpace => "err.enospc"
      | .closedFd, .badFd => "err.ebadf_closed"
      | .wrongMode, .badFd => "err.ebadf_rdonly"
      | _, .wouldBlock => "err.eagain_full_pipe"
      | _, _ => "err.other"
    tracker.record opName bkt

private def captureHostEnv : IO (List ByteArray) := do
  return (← listEnvironRaw).toList

private def restoreHostEnv (saved : List ByteArray) : IO Unit := do
  let _ ← clearEnvRaw 0
  for entry in saved do
    let bs := entry.toList
    match bs.findIdx? (· == ('='.toNat.toUInt8)) with
    | some idx =>
      let k := ByteArray.mk (bs.take idx).toArray
      let v := ByteArray.mk (bs.drop (idx + 1)).toArray
      let _ ← setEnvBytesRaw k v 1
    | none => pure ()

private def makeEmptyPtySlave : Model.FdBacking := .ptySlave [] true ByteArray.empty

private def canSafelyReadOne (w : Model.StdioWorld) : Bool :=
  match w.stdin.backing with
  | .fullDev => false
  | .pipe pending wc nb _ _ =>
    wc || nb || w.stdin.pendingInterrupt.exhaustsRetries || (Model.splitLineBytes pending).isSome
  | .ptySlave segs openM _ =>
    !openM || w.stdin.pendingInterrupt.exhaustsRetries || (Model.consumePtySegments ByteArray.empty segs).isSome
  | _ => true

private def canSafelyConfirm (w : Model.StdioWorld) (prompt : String) (default : Option Bool) (maxAttempts : Nat) : Bool :=
  match maxAttempts with
  | 0 => true
  | n + 1 =>
    match Model.stepDefaultWriteOut w prompt with
    | (.threwIo .blocked, _) => false
    | (.threwIo _, _) => true
    | (.returned (), w1) =>
      if !canSafelyReadOne w1 then false
      else
        match Model.stepDefaultReadLine w1 with
        | (.threwIo _, _) => true
        | (.returned none, _) => true
        | (.returned (some line), w2) =>
          let norm := Model.asciiLower (Model.trimAscii line)
          if norm.isEmpty then
            if default.isSome || n == 0 then true
            else
              match Model.stepDefaultWriteErr w2 "Please answer yes or no.\n" with
              | (.threwIo .blocked, _) => false
              | (.threwIo _, _) => true
              | (.returned (), w3) => canSafelyConfirm w3 prompt default n
          else if norm == "y" || norm == "yes" || norm == "n" || norm == "no" || n == 0 then true
          else
            match Model.stepDefaultWriteErr w2 "Please answer yes or no.\n" with
            | (.threwIo .blocked, _) => false
            | (.threwIo _, _) => true
            | (.returned (), w3) => canSafelyConfirm w3 prompt default n

private def withArmedSigalrm {α : Type} (usec? : Option UInt32) (act : IO α) : IO α := do
  match usec? with
  | some u =>
    armSigalrmRaw u 0
    try act finally disarmSigalrmRaw 0
  | none =>
    act

private def clearCapPipePending (ch : Model.StdioChannelState) (actualDelta : ByteArray)
    (prevWrittenSize : Nat) : Model.StdioChannelState :=
  let b' := match ch.backing with
    | .pipe _ wc nb rc cap => Model.FdBacking.pipe ByteArray.empty wc nb rc cap
    | other => other
  { ch with backing := b', writtenBytes := ch.writtenBytes.extract 0 prevWrittenSize ++ actualDelta }

private def verifyCaptureDrain (op : String) (capFd? : Option UInt32)
    (chPrev chNext : Model.StdioChannelState) (allowNonblockPartial : Bool) : IO Model.StdioChannelState := do
  let some capFd := capFd? | return chNext
  let drained ← drainAllFd capFd
  let expDelta := chNext.writtenBytes.extract chPrev.writtenBytes.size chNext.writtenBytes.size
  if allowNonblockPartial then
    let okPartial := match chPrev.backing with
      | .pipe pending _ true _ cap =>
        let avail := if cap > pending.size then cap - pending.size else 0
        drained.size <= expDelta.size &&
        drained == expDelta.extract 0 drained.size &&
        Model.isValidNonblockPipeWriteBytes avail expDelta.size drained.size
      | _ => drained == expDelta
    if !okPartial then
      throw (IO.userError s!"FUZZ_MISMATCH|{op}|partial|got={repr drained.data.toList} exp={repr expDelta.data.toList}")
  else
    if drained != expDelta then
      throw (IO.userError s!"FUZZ_MISMATCH|{op}|bytes|got={repr drained.data.toList} exp={repr expDelta.data.toList}")
  return clearCapPipePending chNext drained chPrev.writtenBytes.size

private def runSingleOp (ctx : EpisodeCtx) (tracker : CoverageTracker) (priorOutErr : Bool)
    (op : CmdLineFuzzOp) : IO (EpisodeCtx × CoverageTracker × Bool) := do
  match op with
  | .setupStdin kind =>
    let (fd?, isPty, backing, skip) ← match kind with
      | .pipe bs closed nb _ =>
        let r ← setupPipeInRaw bs (if nb then 1 else 0) (if closed then 1 else 0)
        if r == pipeSmallSentinel then
          pure (none, false, Model.FdBacking.nullDev, true)
        else
          if r == invalidFdSentinel then throw (IO.userError "SETUP_PIPE_IN_FAILED")
          let actualCap ← getPipeCapRaw 0
          pure (if r == closedWriterSentinel then none else some r, false,
            Model.FdBacking.pipe bs closed nb false actualCap.toNat, false)
      | .memfd bs =>
        closeOptFd ctx.stdinFeedFd?
        let r ← setupMemfdInRaw bs
        if r != 0 then throw (IO.userError "SETUP_MEMFD_IN_FAILED")
        pure (none, false, Model.FdBacking.regFile bs 0 none, false)
      | .nullDev =>
        closeOptFd ctx.stdinFeedFd?
        if (← setupSpecialRaw 0 0) != 0 then throw (IO.userError "SETUP_NULL_IN_FAILED")
        pure (none, false, Model.FdBacking.nullDev, false)
      | .fullDev =>
        closeOptFd ctx.stdinFeedFd?
        if (← setupSpecialRaw 0 1) != 0 then throw (IO.userError "SETUP_FULL_IN_FAILED")
        pure (none, false, Model.FdBacking.fullDev, false)
      | .dirFd =>
        closeOptFd ctx.stdinFeedFd?
        if (← setupSpecialRaw 0 2) != 0 then throw (IO.userError "SETUP_DIR_IN_FAILED")
        pure (none, false, Model.FdBacking.dirFd, false)
      | .wrOnly =>
        closeOptFd ctx.stdinFeedFd?
        if (← setupSpecialRaw 0 3) != 0 then throw (IO.userError "SETUP_WRONLY_IN_FAILED")
        pure (none, false, Model.FdBacking.wrongMode, false)
      | .closedFd =>
        closeOptFd ctx.stdinFeedFd?
        let _ ← closeSlotRaw 0
        pure (none, false, Model.FdBacking.closedFd, false)
      | .pty echoOff =>
        closeOptFd ctx.stdinFeedFd?
        let m ← setupPtyRaw (if echoOff then 1 else 0)
        if m == invalidFdSentinel then throw (IO.userError "SETUP_PTY_FAILED")
        pure (some m, true, makeEmptyPtySlave, false)
      | .ptyHungup =>
        closeOptFd ctx.stdinFeedFd?
        if (← setupSpecialRaw 0 6) != 0 then throw (IO.userError "SETUP_PTY_HUNGUP_FAILED")
        pure (none, false, Model.FdBacking.ptyHungup, false)
    if skip then
      return (ctx, tracker, priorOutErr)
    if let .pipe _ _ _ _ := kind then
      closeOptFd ctx.stdinFeedFd?
    let w' := { ctx.world with stdin := { backing := backing } }
    return ({ ctx with world := w', stdinFeedFd? := fd?, stdinIsPty := isPty, armedSigalrmUsec? := none, hadPriorReadErr := false }, tracker, priorOutErr)

  | .setupStdout kind =>
    closeOptFd ctx.stdoutCapFd?
    let (capFd?, backing) ← match kind with
      | .capturePipe nb _ =>
        let r ← setupCaptureRaw 1 (if nb then 1 else 0)
        if r == invalidFdSentinel then throw (IO.userError "SETUP_CAP_OUT_FAILED")
        let actualCap ← getPipeCapRaw 1
        pure (some r, Model.FdBacking.pipe ByteArray.empty false nb false actualCap.toNat)
      | .brokenPipe =>
        if (← setupSpecialRaw 1 5) != 0 then throw (IO.userError "SETUP_BPIPE_OUT_FAILED")
        pure (none, Model.FdBacking.pipe ByteArray.empty false false true 65536)
      | .fullDev =>
        if (← setupSpecialRaw 1 1) != 0 then throw (IO.userError "SETUP_FULL_OUT_FAILED")
        pure (none, Model.FdBacking.fullDev)
      | .nullDev =>
        if (← setupSpecialRaw 1 0) != 0 then throw (IO.userError "SETUP_NULL_OUT_FAILED")
        pure (none, Model.FdBacking.nullDev)
      | .rdOnly =>
        if (← setupSpecialRaw 1 4) != 0 then throw (IO.userError "SETUP_RDONLY_OUT_FAILED")
        pure (none, Model.FdBacking.wrongMode)
      | .closedFd =>
        let _ ← closeSlotRaw 1
        pure (none, Model.FdBacking.closedFd)
      | .ptyHungup =>
        if (← setupSpecialRaw 1 7) != 0 then throw (IO.userError "SETUP_PTY_HUNGUP_OUT_FAILED")
        pure (none, Model.FdBacking.ptySlave [] false ByteArray.empty)
    let w' := { ctx.world with stdout := { backing := backing } }
    return ({ ctx with world := w', stdoutCapFd? := capFd? }, tracker, false)

  | .setupStderr kind =>
    closeOptFd ctx.stderrCapFd?
    let (capFd?, backing) ← match kind with
      | .capturePipe nb _ =>
        let r ← setupCaptureRaw 2 (if nb then 1 else 0)
        if r == invalidFdSentinel then throw (IO.userError "SETUP_CAP_ERR_FAILED")
        let actualCap ← getPipeCapRaw 2
        pure (some r, Model.FdBacking.pipe ByteArray.empty false nb false actualCap.toNat)
      | .brokenPipe =>
        if (← setupSpecialRaw 2 5) != 0 then throw (IO.userError "SETUP_BPIPE_ERR_FAILED")
        pure (none, Model.FdBacking.pipe ByteArray.empty false false true 65536)
      | .fullDev =>
        if (← setupSpecialRaw 2 1) != 0 then throw (IO.userError "SETUP_FULL_ERR_FAILED")
        pure (none, Model.FdBacking.fullDev)
      | .nullDev =>
        if (← setupSpecialRaw 2 0) != 0 then throw (IO.userError "SETUP_NULL_ERR_FAILED")
        pure (none, Model.FdBacking.nullDev)
      | .rdOnly =>
        if (← setupSpecialRaw 2 4) != 0 then throw (IO.userError "SETUP_RDONLY_ERR_FAILED")
        pure (none, Model.FdBacking.wrongMode)
      | .closedFd =>
        let _ ← closeSlotRaw 2
        pure (none, Model.FdBacking.closedFd)
      | .ptyHungup =>
        if (← setupSpecialRaw 2 7) != 0 then throw (IO.userError "SETUP_PTY_HUNGUP_ERR_FAILED")
        pure (none, Model.FdBacking.ptySlave [] false ByteArray.empty)
    let w' := { ctx.world with stderr := { backing := backing } }
    return ({ ctx with world := w', stderrCapFd? := capFd? }, tracker, priorOutErr)

  | .feedPipeOrPty bs =>
    if let some fd := ctx.stdinFeedFd? then
      if !bs.isEmpty then
        let canFeed : Bool ← match ctx.world.stdin.backing with
          | .pipe p _ _ _ _ =>
            let realCap ← getPipeCapRaw 0
            pure (p.size + bs.size <= min realCap.toNat 32768)
          | .ptySlave segs _ pLine =>
            let queued := pLine.size + segs.foldl (fun acc s => match s with | some b => acc + b.size | none => acc) 0
            let hasCtrl := bs.toList.any (fun (b : UInt8) => (b < 0x20 && b != 0x0a && b != 0x0d && b != 0x04) || b == 0x7f)
            pure (queued + bs.size <= 2048 && !hasCtrl)
          | _ => pure false
        if canFeed then
          let wr ← writeFdRaw fd bs
          if wr >= 0x80000000 then
            let err := wr &&& 0x7fffffff
            if err == 11 then
              return (ctx, tracker, priorOutErr)
            throw (IO.userError s!"FEED_FD_FAILED errno={err}")
          let written := wr.toNat
          if written == 0 then
            return (ctx, tracker, priorOutErr)
          let fed := bs.extract 0 written
          let b' := match ctx.world.stdin.backing with
            | .pipe p wc nb rc cap => Model.FdBacking.pipe (p ++ fed) wc nb rc cap
            | .ptySlave segs openM pLine =>
              let (segs', pLine') := Model.ptyFeedBytes segs pLine fed
              Model.FdBacking.ptySlave segs' openM pLine'
            | other => other
          let w' := { ctx.world with stdin := { ctx.world.stdin with backing := b' } }
          return ({ ctx with world := w' }, tracker, priorOutErr)
    return (ctx, tracker, priorOutErr)

  | .sendPtyEof =>
    if ctx.stdinIsPty then
      if let some fd := ctx.stdinFeedFd? then
        let wr ← writeFdRaw fd (ByteArray.mk #[0x04])
        if wr >= 0x80000000 then
          let err := wr &&& 0x7fffffff
          if err == 11 then
            return (ctx, tracker, priorOutErr)
          throw (IO.userError s!"SEND_PTY_EOF_FAILED errno={err}")
        if wr != 1 then
          throw (IO.userError s!"SEND_PTY_EOF_SHORT written={wr}")
        let b' := match ctx.world.stdin.backing with
          | .ptySlave segs openM pLine =>
            let (segs', pLine') := Model.ptyFeedBytes segs pLine (ByteArray.mk #[0x04])
            Model.FdBacking.ptySlave segs' openM pLine'
          | other => other
        let w' := { ctx.world with stdin := { ctx.world.stdin with backing := b' } }
        return ({ ctx with world := w' }, tracker, priorOutErr)
    return (ctx, tracker, priorOutErr)

  | .closeStdinWriter =>
    if let some fd := ctx.stdinFeedFd? then
      let _ ← closeFdRaw fd
      let b' := match ctx.world.stdin.backing with
        | .pipe p _ nb rc cap => Model.FdBacking.pipe p true nb rc cap
        | .ptySlave _ _ _ => Model.FdBacking.ptySlave [] false ByteArray.empty
        | other => other
      let w' := { ctx.world with stdin := { ctx.world.stdin with backing := b' } }
      return ({ ctx with world := w', stdinFeedFd? := none }, tracker, priorOutErr)
    return (ctx, tracker, priorOutErr)

  | .armEintr usec =>
    let armable := match ctx.world.stdin.backing with
      | .pipe _ false false _ _ => true
      | .ptySlave _ true _ => true
      | _ => false
    if armable then
      let w' := { ctx.world with stdin := { ctx.world.stdin with pendingInterrupt := .repeating } }
      return ({ ctx with world := w', armedSigalrmUsec? := some usec }, tracker, priorOutErr)
    else
      let w' := { ctx.world with stdin := { ctx.world.stdin with pendingInterrupt := .none } }
      return ({ ctx with world := w', armedSigalrmUsec? := none }, tracker, priorOutErr)

  | .setEnv k v ovw =>
    let rc ← setEnvBytesRaw k v (if ovw then 1 else 0)
    let w' := envSetInWorld ctx.world k v ovw
    let w'' := if rc != 0 then { w' with lastErrno := rc } else w'
    return ({ ctx with world := w'' }, tracker, priorOutErr)

  | .unsetEnv k =>
    let rc ← unsetEnvBytesRaw k
    let w' := envUnsetInWorld ctx.world k
    let w'' := if rc != 0 then { w' with lastErrno := rc } else w'
    return ({ ctx with world := w'' }, tracker, priorOutErr)

  | .callReadLine =>
    if !canSafelyReadOne ctx.world then
      disarmSigalrmRaw 0
      return (ctx, tracker, priorOutErr)
    let (expOut, wNext) := Model.stepDefaultReadLine ctx.world
    let armForRead := if expOut == .threwIo .interrupted then ctx.armedSigalrmUsec? else none
    let actual : Except IO.Error (Option String) ← try
      let r ← withArmedSigalrm armForRead CmdLine.defaultOps.readLine
      pure (.ok r)
    catch e =>
      pure (.error e)
    if !ioOutcomeMatches expOut actual then
      let _ ← restoreStdioRaw 0
      let actStr := match actual with
        | .ok o => s!"ok ({repr o})"
        | .error e => s!"error ({e})"
      let sub := match expOut with
        | .threwIo c => s!"{repr c}"
        | .returned none => "eof"
        | .returned (some _) => "line"
      throw (IO.userError s!"FUZZ_MISMATCH|READLINE|{sub}|exp={repr expOut} actual={actStr}")
    let t' := recordReadLineBuckets ctx.world.stdin wNext.stdin ctx.hadPriorReadErr expOut tracker
    let nextPriorReadErr := match expOut with | .threwIo _ => true | .returned _ => false
    let nextArm := if wNext.stdin.pendingInterrupt.exhaustsRetries then ctx.armedSigalrmUsec? else none
    return ({ ctx with world := wNext, armedSigalrmUsec? := nextArm, hadPriorReadErr := nextPriorReadErr }, t', priorOutErr)

  | .callWriteOut text =>
    let (expOut, wNext) := Model.stepDefaultWriteOut ctx.world text
    if expOut == .threwIo .blocked then
      return (ctx, tracker, priorOutErr)
    let actual : Except IO.Error Unit ← try
      CmdLine.defaultOps.writeOut text
      pure (.ok ())
    catch e =>
      pure (.error e)
    if !ioOutcomeMatches expOut actual then
      let _ ← restoreStdioRaw 0
      let sub := match expOut with | .threwIo c => s!"{repr c}" | .returned () => "ok"
      throw (IO.userError s!"FUZZ_MISMATCH|WRITEOUT|{sub}|text={repr text} exp={repr expOut}")
    let allowPartial := expOut == .threwIo .wouldBlock
    let outCh' ← try
      verifyCaptureDrain "WRITEOUT_BYTES" ctx.stdoutCapFd? ctx.world.stdout wNext.stdout allowPartial
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let t' := recordWriteBuckets "writeOut" ctx.world.stdout text priorOutErr expOut tracker
    let nextPriorErr := match expOut with | .threwIo _ => true | .returned () => priorOutErr
    return ({ ctx with world := { wNext with stdout := outCh' } }, t', nextPriorErr)

  | .callWriteErr text =>
    let (expOut, wNext) := Model.stepDefaultWriteErr ctx.world text
    if expOut == .threwIo .blocked then
      return (ctx, tracker, priorOutErr)
    let actual : Except IO.Error Unit ← try
      CmdLine.defaultOps.writeErr text
      pure (.ok ())
    catch e =>
      pure (.error e)
    if !ioOutcomeMatches expOut actual then
      let _ ← restoreStdioRaw 0
      let sub := match expOut with | .threwIo c => s!"{repr c}" | .returned () => "ok"
      throw (IO.userError s!"FUZZ_MISMATCH|WRITEERR|{sub}|text={repr text} exp={repr expOut}")
    let allowPartial := expOut == .threwIo .wouldBlock
    let errCh' ← try
      verifyCaptureDrain "WRITEERR_BYTES" ctx.stderrCapFd? ctx.world.stderr wNext.stderr allowPartial
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let t' := recordWriteBuckets "writeErr" ctx.world.stderr text false expOut tracker
    return ({ ctx with world := { wNext with stderr := errCh' } }, t', priorOutErr)

  | .callGetEnv key =>
    let exp := Model.stepDefaultGetEnv ctx.world key
    let actual ← CmdLine.defaultOps.getEnv key
    if !exceptCmdEq actual exp then
      let _ ← restoreStdioRaw 0
      throw (IO.userError s!"FUZZ_MISMATCH|GETENV|mismatch|key={repr key} exp={repr exp} actual={repr actual}")
    let bkt := match exp with
      | .ok none => "ok.none"
      | .ok (some "") => "ok.some_empty"
      | .ok (some _) => "ok.some_valid"
      | .error _ => if !Model.isValidEnvKey key then "err.invalid_key" else "err.invalid_utf8"
    return (ctx, tracker.record "getEnv" bkt, priorOutErr)

  | .callPromptLine prompt default =>
    if (Model.stepDefaultWriteOut ctx.world prompt).1 == .threwIo .blocked || !canSafelyReadOne ctx.world then
      disarmSigalrmRaw 0
      return (ctx, tracker, priorOutErr)
    let (exp, wNext) := Model.stepPromptLine ctx.world prompt default
    if ctx.world.stdin.pendingInterrupt.exhaustsRetries && !wNext.stdin.pendingInterrupt.exhaustsRetries then
      return (ctx, tracker, priorOutErr)
    disarmSigalrmRaw 0
    let actual ← CmdLine.promptLine prompt default
    let outWouldBlock := (Model.stepDefaultWriteOut ctx.world prompt).1 == .threwIo .wouldBlock
    let outCh' ← try
      verifyCaptureDrain "PROMPTLINE_BYTES" ctx.stdoutCapFd? ctx.world.stdout wNext.stdout outWouldBlock
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let okMatch := match exp, actual with
      | .ok a, .ok b => a == b
      | .error ea, .error eb =>
        ea.kind == eb.kind && !eb.message.isEmpty && (if ea.kind == .ioError then eb.target == none else true)
      | _, _ => false
    if !okMatch then
      let _ ← restoreStdioRaw 0
      let sub := match exp with | .ok _ => "ok" | .error e => s!"{repr e.kind}"
      throw (IO.userError s!"FUZZ_MISMATCH|PROMPTLINE|{sub}|exp={repr exp} actual={repr actual}")
    let bkt := match exp with
      | .ok _ =>
        match (Model.stepDefaultReadLine ctx.world).1 with
        | .returned (some line) => if (Model.trimAscii line).isEmpty then "ok.default_on_blank" else "ok.trimmed"
        | _ => "ok.trimmed"
      | .error e =>
        match e.kind with
        | .eof => "err.eof"
        | .ioError =>
          match (Model.stepDefaultWriteOut ctx.world prompt).1 with
          | .threwIo _ => "err.ioError_write"
          | .returned () => "err.ioError_read"
        | _ => "err.other"
    let nextArm := if wNext.stdin.pendingInterrupt.exhaustsRetries then ctx.armedSigalrmUsec? else none
    return ({ ctx with world := { wNext with stdout := outCh' }, armedSigalrmUsec? := nextArm }, tracker.record "promptLine" bkt, priorOutErr)

  | .callConfirm prompt default maxAttempts =>
    if !canSafelyConfirm ctx.world prompt default maxAttempts then
      disarmSigalrmRaw 0
      return (ctx, tracker, priorOutErr)
    let (exp, wNext) := Model.stepConfirm ctx.world prompt default maxAttempts
    if ctx.world.stdin.pendingInterrupt.exhaustsRetries && !wNext.stdin.pendingInterrupt.exhaustsRetries then
      return (ctx, tracker, priorOutErr)
    disarmSigalrmRaw 0
    let actual ← CmdLine.confirm prompt default maxAttempts
    let outWouldBlock := (Model.stepDefaultWriteOut ctx.world prompt).1 == .threwIo .wouldBlock
    let errWouldBlock := !outWouldBlock && wNext.lastErrno == 11 && match ctx.world.stderr.backing with
      | .pipe _ _ true _ _ => true
      | _ => false
    let outCh' ← try
      verifyCaptureDrain "CONFIRM_OUT_BYTES" ctx.stdoutCapFd? ctx.world.stdout wNext.stdout outWouldBlock
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let errCh' ← try
      verifyCaptureDrain "CONFIRM_ERR_BYTES" ctx.stderrCapFd? ctx.world.stderr wNext.stderr errWouldBlock
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let okMatch := match exp, actual with
      | .ok a, .ok b => a == b
      | .error ea, .error eb => ea.kind == eb.kind && !eb.message.isEmpty && eb.target == none
      | _, _ => false
    if !okMatch then
      let _ ← restoreStdioRaw 0
      let sub := match exp with | .ok _ => "ok" | .error e => s!"{repr e.kind}"
      throw (IO.userError s!"FUZZ_MISMATCH|CONFIRM|{sub}|exp={repr exp} actual={repr actual}")
    let bkt := match exp with
      | .ok true =>
        if wNext.stderr.writtenBytes.size > ctx.world.stderr.writtenBytes.size then "ok.retry_then_yes"
        else if default == some true then
          match (Model.stepDefaultReadLine ctx.world).1 with
          | .returned (some l) => if (Model.trimAscii l).isEmpty then "ok.default" else "ok.yes"
          | _ => "ok.yes"
        else "ok.yes"
      | .ok false =>
        if default == some false then
          match (Model.stepDefaultReadLine ctx.world).1 with
          | .returned (some l) => if (Model.trimAscii l).isEmpty then "ok.default" else "ok.no"
          | _ => "ok.no"
        else "ok.no"
      | .error e =>
        match e.kind with
        | .eof => "err.eof"
        | .invalidValue => "err.invalidValue_exhaust"
        | .ioError =>
          match (Model.stepDefaultWriteOut ctx.world prompt).1 with
          | .threwIo _ => "err.ioError_writeOut"
          | .returned () =>
            if wNext.stderr.writtenBytes.size == ctx.world.stderr.writtenBytes.size then
              match (Model.stepDefaultReadLine ctx.world).1 with
              | .threwIo _ => "err.ioError_readLine"
              | _ => "err.ioError_writeErr_reprompt"
            else "err.ioError_writeErr_reprompt"
        | _ => "err.other"
    let nextArm := if wNext.stdin.pendingInterrupt.exhaustsRetries then ctx.armedSigalrmUsec? else none
    return ({ ctx with world := { wNext with stdout := outCh', stderr := errCh' }, armedSigalrmUsec? := nextArm }, tracker.record "confirm" bkt, priorOutErr)

  | .callParseWithEnv spec args =>
    let modelOps : CmdLine.CliOpsM Id := {
      readLine := pure none
      writeOut := fun _ => pure ()
      writeErr := fun _ => pure ()
      getEnv := fun k => Model.stepDefaultGetEnv ctx.world k
    }
    let exp : Except CmdLineError ParsedCmd := CmdLine.Internal.parseWithEnvSpecM modelOps spec args []
    let actual ← CmdLine.parseWithEnv spec args
    if !exceptCmdEq actual exp then
      let _ ← restoreStdioRaw 0
      throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|mismatch|exp={repr exp} actual={repr actual}")
    let valid := Model.isValidSpec spec
    let mut t := tracker
    match actual with
    | .ok parsed =>
      if !valid then
        let _ ← restoreStdioRaw 0
        throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|invalid_spec_ok|spec={spec.name}")
      match Model.findSubcommandPath spec parsed.subcommandPath with
      | .error e =>
        let _ ← restoreStdioRaw 0
        throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|bad_subpath|err={e.message}")
      | .ok (visGlobals, _, curNode) =>
        if !curNode.subcommands.isEmpty then
          let _ ← restoreStdioRaw 0
          throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|nonleaf_ok|cmd={curNode.name}")
        if !exceptCmdEq (Model.resolveArgs curNode.args parsed.rawPositionals) (.ok parsed.args) then
          let _ ← restoreStdioRaw 0
          throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|args_model|raw={repr parsed.rawPositionals}")
        if args.isEmpty then
          let envRes := Model.stepResolveOptionsWithEnv ctx.world (visGlobals ++ curNode.options) []
          if !exceptCmdEq envRes (.ok parsed.options) then
            let _ ← restoreStdioRaw 0
            throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|env_model|exp={repr envRes} act={repr parsed.options}")
      t := t.record "parseWithEnv" "ok"
    | .error e =>
      if !valid && e.kind != .invalidSpec then
        let _ ← restoreStdioRaw 0
        throw (IO.userError s!"FUZZ_MISMATCH|PARSEWITHENV|invalid_spec_kind|kind={repr e.kind}")
      t := t.record "parseWithEnv" s!"err.{repr e.kind}"
    return (ctx, t, priorOutErr)

  | .callRunCli spec args handlerExit =>
    let modelOps : CmdLine.CliOpsM Id := {
      readLine := pure none
      writeOut := fun _ => pure ()
      writeErr := fun _ => pure ()
      getEnv := fun k => Model.stepDefaultGetEnv ctx.world k
    }
    let expParse : Except CmdLineError ParsedCmd := CmdLine.Internal.parseWithEnvSpecM modelOps spec args []
    let (exp, wNext) := Model.stepRunCliWithOutcome ctx.world expParse (fun _ w => (.returned handlerExit, w))
    if exp == .threwIo .blocked then
      return (ctx, tracker, priorOutErr)
    let actual : Except IO.Error UInt32 ← try
      let rc ← CmdLine.runCli spec args (fun _ => pure handlerExit)
      pure (.ok rc)
    catch e =>
      pure (.error e)
    let outWouldBlock := exp == .threwIo .wouldBlock && match ctx.world.stdout.backing with
      | .pipe _ _ true _ _ => true
      | _ => false
    let errWouldBlock := exp == .threwIo .wouldBlock && !outWouldBlock && match ctx.world.stderr.backing with
      | .pipe _ _ true _ _ => true
      | _ => false
    let outCh' ← try
      verifyCaptureDrain "RUNCLI_OUT_BYTES" ctx.stdoutCapFd? ctx.world.stdout wNext.stdout outWouldBlock
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    let errCh' ← try
      verifyCaptureDrain "RUNCLI_ERR_BYTES" ctx.stderrCapFd? ctx.world.stderr wNext.stderr errWouldBlock
    catch e =>
      let _ ← restoreStdioRaw 0
      throw e
    if !ioOutcomeMatches exp actual then
      let _ ← restoreStdioRaw 0
      let actStr := match actual with | .ok rc => s!"ok({rc})" | .error e => s!"err({e})"
      let sub := match exp with | .threwIo c => s!"{repr c}" | .returned rc => s!"ret_{rc}"
      throw (IO.userError s!"FUZZ_MISMATCH|RUNCLI|{sub}|exp={repr exp} actual={actStr}")
    let mut t := tracker
    match exp with
    | .returned 0 =>
      match CmdLine.parse spec args with
      | .error e =>
        if e.kind == .helpRequested then t := t.record "runCli" "ret.0_help"
        else if e.kind == .versionRequested then t := t.record "runCli" "ret.0_version"
      | .ok _ => t := t.record "runCli" "ret.handler_code"
    | .returned 2 =>
      match CmdLine.parse spec args with
      | .error _ => t := t.record "runCli" "ret.2_parse_err"
      | .ok _ => t := t.record "runCli" "ret.2_env_ioError"
    | .returned _ =>
      t := t.record "runCli" "ret.handler_code"
    | .threwIo c =>
      let bkt := match c with
        | .brokenPipe =>
          match CmdLine.parse spec args with
          | .error e => if e.kind == .helpRequested || e.kind == .versionRequested then "threw.epipe_help" else "threw.epipe_err"
          | .ok _ => "threw.epipe_err"
        | .noSpace => "threw.enospc_help"
        | _ => "threw.other"
      t := t.record "runCli" bkt
    return ({ ctx with world := { wNext with stdout := outCh', stderr := errCh' } }, t, priorOutErr)

  | .callPureRoundTrip spec args =>
    let helpRoot := CmdLine.renderHelp spec []
    let valid := Model.isValidSpec spec
    if CmdLine.isValidSpec spec != valid then
      throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|isValidSpec|spec={spec.name}")
    match helpRoot with
    | .ok hTxt =>
      if valid && (hTxt.splitOn spec.name).length <= 1 then
        throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|renderHelp|spec={spec.name}")
    | .error e =>
      if valid || e.kind != .invalidSpec then
        throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|renderHelp_err|spec={spec.name} kind={repr e.kind}")
    let mut t := tracker
    match CmdLine.parse spec args with
    | .ok parsed =>
      if !valid then
        throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|invalid_spec_parsed|spec={spec.name}")
      let impRend := CmdLine.renderArgs spec parsed
      let modRend := Model.renderArgs spec parsed
      if !exceptCmdEq impRend modRend then
        throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|renderArgs_model|args={repr args}")
      match impRend with
      | .error e =>
        t := t.record "pureRoundTrip" s!"err.render.{repr e.kind}"
      | .ok rendered =>
        match CmdLine.parse spec rendered with
        | .error e =>
          throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|reparse_err|kind={repr e.kind} args={repr args} rendered={repr rendered}")
        | .ok reparsed =>
          if reparsed != parsed then
            throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|roundtrip|args={repr args} rendered={repr rendered}")
          t := t.record "pureRoundTrip" "ok.roundtrip"
    | .error e =>
      if !valid && e.kind != .invalidSpec then
        throw (IO.userError s!"FUZZ_MISMATCH|PURE_ROUNDTRIP|invalid_spec_kind|kind={repr e.kind}")
      t := t.record "pureRoundTrip" s!"err.parse.{repr e.kind}"
    return (ctx, t, priorOutErr)

private def runEpisode (ops : Array CmdLineFuzzOp) (tracker : CoverageTracker) : IO CoverageTracker := do
  let _ ← saveStdioRaw 0
  let _ ← resetStreamsRaw 0
  let savedEnv ← captureHostEnv
  let _ ← clearEnvRaw 0
  let _ ← setupSpecialRaw 0 0
  let _ ← setupSpecialRaw 1 0
  let _ ← setupSpecialRaw 2 0
  let ctxRef ← IO.mkRef ({
    world := {
      stdin := { backing := .nullDev }
      stdout := { backing := .nullDev }
      stderr := { backing := .nullDev }
    }
  } : EpisodeCtx)
  try
    Fuzz.LinuxSyscall.Env.withRawStdio do
      let mut t := tracker
      let mut priorOutErr := false
      for op in ops do
        let cur ← ctxRef.get
        let (c', t', p') ← runSingleOp cur t priorOutErr op
        ctxRef.set c'
        t := t'
        priorOutErr := p'
      return t
  finally
    disarmSigalrmRaw 0
    let finalCtx ← ctxRef.get
    closeOptFd finalCtx.stdinFeedFd?
    closeOptFd finalCtx.stdoutCapFd?
    closeOptFd finalCtx.stderrCapFd?
    let _ ← restoreStdioRaw 0
    restoreHostEnv savedEnv

private def boundaryCorpus : Array (Array CmdLineFuzzOp) := #[
  #[.setupStdin (.pipe "hello\nhéllo 🚀\n".toUTF8 true false 65536), .callReadLine, .callReadLine, .callReadLine],
  #[.setupStdin (.pipe (ByteArray.mk #[0xed, 0xa0, 0x80, 0x0a]) true false 65536), .callReadLine],
  #[.setupStdin (.pipe (ByteArray.mk #[0xc0, 0xaf, 0x0a]) true false 65536), .callReadLine],
  #[.setupStdin (.pipe (ByteArray.mk #[0xf4, 0x90, 0x80, 0x80, 0x41, 0x0a]) true false 65536), .callReadLine],
  #[.setupStdin (.pipe (ByteArray.mk #[0x61, 0x00, 0x62, 0x0a]) true false 65536), .callReadLine],
  #[.setupStdin (.pipe "\nfoo\r\nbar\r\r\nmid\rcr\nno_nl".toUTF8 true false 65536), .callReadLine, .callReadLine, .callReadLine, .callReadLine, .callReadLine],
  #[.setupStdin (.memfd ((String.ofList (List.replicate 8200 'x') ++ "\n").toUTF8)), .callReadLine],
  #[.setupStdin .nullDev, .callReadLine],
  #[.setupStdin .closedFd, .callReadLine],
  #[.setupStdin .wrOnly, .callReadLine],
  #[.setupStdin .dirFd, .callReadLine],
  #[.setupStdin (.pipe ByteArray.empty false true 65536), .callReadLine],
  #[.setupStdin (.pipe "part".toUTF8 false true 65536), .callReadLine, .feedPipeOrPty "rest\n".toUTF8, .callReadLine],
  #[.setupStdin (.pipe ByteArray.empty false false 65536), .armEintr 1500, .callReadLine, .feedPipeOrPty "ok\n".toUTF8, .callReadLine],
  #[.setupStdin (.pty true), .feedPipeOrPty "a\n".toUTF8, .callReadLine, .sendPtyEof, .callReadLine, .feedPipeOrPty "after\n".toUTF8, .callReadLine, .closeStdinWriter, .callReadLine],
  #[.setupStdin .ptyHungup, .callReadLine],
  #[.setupStdout (.capturePipe false 65536), .callWriteOut "hi\n", .callWriteOut (String.ofList ['a', Char.ofNat 0, 'b'])],
  #[.setupStdout .brokenPipe, .callWriteOut "fail", .callWriteOut ""],
  #[.setupStdout .fullDev, .callWriteOut "", .callWriteOut "fail"],
  #[.setupStdout .closedFd, .callWriteOut "fail"],
  #[.setupStdout .rdOnly, .callWriteOut "fail"],
  #[.setupStdout (.capturePipe true 4096), .callWriteOut (String.ofList (List.replicate 131072 'z'))],
  #[.setupStderr (.capturePipe false 65536), .callWriteErr "err\n"],
  #[.setupStderr (.capturePipe true 4096), .callWriteErr (String.ofList (List.replicate 131072 'e'))],
  #[.setupStdin (.pipe ByteArray.empty false true 65536), .callReadLine, .feedPipeOrPty "after_err\n".toUTF8,
    .callWriteOut "", .setEnv "STICKY_K".toUTF8 "1".toUTF8 true, .callGetEnv "STICKY_K", .callReadLine],
  #[.setupStderr .brokenPipe, .callWriteErr "", .callWriteErr "fail"],
  #[.setupStderr .fullDev, .callWriteErr "fail"],
  #[.setupStderr .rdOnly, .callWriteErr "fail"],
  #[.unsetEnv "K_NONE".toUTF8, .callGetEnv "K_NONE", .setEnv "K_EMPTY".toUTF8 ByteArray.empty true, .callGetEnv "K_EMPTY",
    .setEnv "K_OK".toUTF8 "v".toUTF8 true, .callGetEnv "K_OK", .callGetEnv "BAD=KEY",
    .setEnv "K_BADU".toUTF8 (ByteArray.mk #[0xed, 0xa0, 0x80]) true, .callGetEnv "K_BADU"],
  #[.setupStdout .nullDev, .setupStdin (.pipe "  val \n\n".toUTF8 true false 65536),
    .callPromptLine "p:" none, .callPromptLine "p:" (some "def"), .callPromptLine "p:" none,
    .setupStdout .brokenPipe, .callPromptLine "p:" none,
    .setupStdout .nullDev, .setupStdin .closedFd, .callPromptLine "p:" none],
  #[.setupStdout .nullDev, .setupStderr (.capturePipe false 65536),
    .setupStdin (.pipe "y\nn\n\nbad\nyes\njunk\n".toUTF8 true false 65536),
    .callConfirm "q1" none 2, .callConfirm "q2" none 2, .callConfirm "q3" (some true) 2,
    .callConfirm "q4" none 3, .callConfirm "q5" none 1, .callConfirm "q6" none 2,
    .setupStdout .brokenPipe, .callConfirm "q7" none 2,
    .setupStdout .nullDev, .setupStderr .brokenPipe, .setupStdin (.pipe "bad\ny\n".toUTF8 true false 65536), .callConfirm "q8" none 2,
    .setupStderr .nullDev, .setupStdin .closedFd, .callConfirm "q9" none 2],
  #[.setupStdout .nullDev, .setupStderr .nullDev,
    .callRunCli { name := "t", version := some "1.0" } ["--help"] 0,
    .callRunCli { name := "t", version := some "1.0" } ["--version"] 0,
    .callRunCli { name := "t" } ["--unknown"] 0,
    .setEnv "GOOD_ENV".toUTF8 (ByteArray.mk #[0xed, 0xa0, 0x80]) true,
    .callRunCli { name := "t", options := [{ name := "x", long := some "x", envVar := some "GOOD_ENV" }] } [] 0,
    .callRunCli { name := "t" } [] 7,
    .setupStdout .brokenPipe, .callRunCli { name := "t", version := some "1.0" } ["--help"] 0,
    .setupStdout .fullDev, .callRunCli { name := "t", version := some "1.0" } ["--help"] 0,
    .setupStdout .nullDev, .setupStderr .brokenPipe, .callRunCli { name := "t" } ["--bad"] 0],
  #[.setupStdin (.pty true),
    .feedPipeOrPty "part".toUTF8, .sendPtyEof, .sendPtyEof, .callReadLine,
    .feedPipeOrPty "x".toUTF8, .sendPtyEof, .feedPipeOrPty "y\n".toUTF8, .callReadLine,
    .feedPipeOrPty "foo\r\n".toUTF8, .callReadLine, .callReadLine,
    .feedPipeOrPty "unread\n".toUTF8, .closeStdinWriter, .callReadLine],
  #[.setupStdin (.pty true),
    .armEintr 1500, .callReadLine,
    .sendPtyEof, .callReadLine,
    .setupStdout .fullDev, .callWriteOut "e",
    .armEintr 1500, .callReadLine,
    .feedPipeOrPty "no_nl".toUTF8, .callReadLine],
  #[.setupStdout .ptyHungup, .callWriteOut "hello_hungup\n",
    .setupStderr .ptyHungup, .callWriteErr "err_hungup\n",
    .setEnv "STRICT_REQ".toUTF8 (ByteArray.mk #[0xed, 0xa0, 0x80]) true,
    .callParseWithEnv { name := "strict_cov", options := [{ name := "req", long := some "req", kind := .int, required := true, envVar := some "STRICT_REQ" }] } []],
  #[.setupStdin (.pipe ("a\n".toUTF8 ++ ByteArray.mk (Array.replicate 60000 0x42)) false false 65536),
    .callReadLine, .feedPipeOrPty "tail\n".toUTF8, .callReadLine],
  #[.setupStdout (.capturePipe false 65536), .setupStderr (.capturePipe false 65536),
    .setupStdin (.pipe "yes\n".toUTF8 true false 65536),
    .callConfirm "ok?" none 2]
]

private def extractMismatchTag (msg : String) : Option String :=
  let pref := "FUZZ_MISMATCH|"
  if !msg.startsWith pref then none
  else
    let rest := (msg.drop pref.length).toString
    match rest.splitOn "|" with
    | cat :: sub :: _ => some s!"{cat}|{sub}"
    | _ => none

private def shrinkByteArrayCandidates (bs : ByteArray) : List ByteArray := Id.run do
  if bs.isEmpty then
    return []
  if bs.size == 1 then
    return [ByteArray.empty]
  let mut cands : List ByteArray := [
    ByteArray.empty,
    bs.extract 0 (bs.size / 2),
    bs.extract (bs.size / 2) bs.size
  ]
  for thresh in [4096, 4097, 8192, 8193] do
    if bs.size > thresh then
      let half := thresh / 2
      cands := cands ++ [
        bs.extract 0 thresh,
        bs.extract (bs.size - thresh) bs.size,
        bs.extract 0 half ++ bs.extract (bs.size - (thresh - half)) bs.size,
        bs.extract 0 1 ++ bs.extract (bs.size - (thresh - 1)) bs.size,
        bs.extract 0 (thresh - 1) ++ bs.extract (bs.size - 1) bs.size
      ]
  let mut d := bs.size / 2
  while d >= 1 do
    cands := cands ++ [bs.extract 0 (bs.size - d), bs.extract d bs.size]
    if bs.size > d + 2 then
      for off in [bs.size / 8, bs.size / 4, bs.size / 2, (3 * bs.size) / 4] do
        if off > 0 && off + d < bs.size then
          cands := cands ++ [bs.extract 0 off ++ bs.extract (off + d) bs.size]
    d := d / 2
  let step := max 1 (bs.size / 8)
  if bs.size > 4 then
    let mut i := 0
    while i < bs.size do
      let stop := min bs.size (i + step)
      cands := cands ++ [bs.extract 0 i ++ bs.extract stop bs.size]
      i := i + step
  if bs.size <= 64 then
    for i in List.range bs.size do
      cands := cands ++ [bs.extract 0 i ++ bs.extract (i + 1) bs.size]
  return cands

private def shrinkStringCandidates (s : String) : List String := Id.run do
  if s.isEmpty then return []
  let mut out : List String := [""]
  for bs in shrinkByteArrayCandidates s.toUTF8 do
    if let some s' := String.fromUTF8? bs then
      if s' != s then out := out ++ [s']
  let cs := s.toList
  if cs.length > 1 then
    let h := cs.length / 2
    out := out ++ [String.ofList (cs.take h), String.ofList (cs.drop h)]
    let mut d := cs.length / 2
    while d >= 1 do
      out := out ++ [String.ofList (cs.take (cs.length - d)), String.ofList (cs.drop d)]
      if cs.length > d + 2 then
        for off in [cs.length / 8, cs.length / 4, cs.length / 2, (3 * cs.length) / 4] do
          if off > 0 && off + d < cs.length then
            out := out ++ [String.ofList (cs.take off ++ cs.drop (off + d))]
      d := d / 2
    let step := max 1 (cs.length / 8)
    let mut i := 0
    while i < cs.length do
      let stop := min cs.length (i + step)
      out := out ++ [String.ofList (cs.take i ++ cs.drop stop)]
      i := i + step
    if cs.length <= 64 then
      for idx in List.range cs.length do
        out := out ++ [String.ofList (cs.take idx ++ cs.drop (idx + 1))]
  return out

private def shrinkOpCandidates : CmdLineFuzzOp → List CmdLineFuzzOp
  | .setupStdin (.pipe bs wc nb cap) =>
    (shrinkByteArrayCandidates bs).map fun bs' => .setupStdin (.pipe bs' wc nb cap)
  | .setupStdin (.memfd bs) =>
    (shrinkByteArrayCandidates bs).map fun bs' => .setupStdin (.memfd bs')
  | .feedPipeOrPty bs =>
    (shrinkByteArrayCandidates bs).map fun bs' => .feedPipeOrPty bs'
  | .callWriteOut s =>
    (shrinkStringCandidates s).map .callWriteOut
  | .callWriteErr s =>
    (shrinkStringCandidates s).map .callWriteErr
  | .callRunCli sp args ex =>
    match args with
    | [] => []
    | _ :: rest => [.callRunCli sp [] ex, .callRunCli sp rest ex]
  | _ => []

private def summarizeOp : CmdLineFuzzOp → String
  | .setupStdin (.pipe bs wc nb _) => s!"setupStdin(pipe len={bs.size} bytes={bs.data.toList} wc={wc} nb={nb})"
  | .setupStdin (.memfd bs) => s!"setupStdin(memfd len={bs.size} bytes={bs.data.toList})"
  | .setupStdin _ => "setupStdin(special)"
  | .setupStdout _ => "setupStdout"
  | .setupStderr _ => "setupStderr"
  | .feedPipeOrPty bs => s!"feedPipeOrPty(len={bs.size} bytes={bs.data.toList})"
  | .sendPtyEof => "sendPtyEof"
  | .closeStdinWriter => "closeStdinWriter"
  | .armEintr u => s!"armEintr({u})"
  | .setEnv k v ovw => s!"setEnv(k={k.data.toList} v={v.data.toList} ovw={ovw})"
  | .unsetEnv k => s!"unsetEnv(k={k.data.toList})"
  | .callReadLine => "callReadLine"
  | .callWriteOut s => s!"callWriteOut({repr s})"
  | .callWriteErr s => s!"callWriteErr({repr s})"
  | .callGetEnv k => s!"callGetEnv({repr k})"
  | .callPromptLine p _ => s!"callPromptLine({repr p})"
  | .callConfirm p _ m => s!"callConfirm({repr p}, max={m})"
  | .callParseWithEnv _ args => s!"callParseWithEnv({repr args})"
  | .callRunCli _ args ex => s!"callRunCli({repr args}, ex={ex})"
  | .callPureRoundTrip _ args => s!"callPureRoundTrip({repr args})"

private def shrinkOnMismatch (runner : Array CmdLineFuzzOp → IO CoverageTracker)
    (ops : Array CmdLineFuzzOp) : IO CoverageTracker := do
  try
    runner ops
  catch e =>
    let msg := e.toString
    match extractMismatchTag msg with
    | none => throw e
    | some tag =>
      let failsPinned (cand : Array CmdLineFuzzOp) : IO Bool := do
        try
          let _ ← runner cand
          return false
        catch ce =>
          return extractMismatchTag ce.toString == some tag
      let shrunkTop ← shrinkTrace failsPinned ops
      let shrunkFull ← shrinkElements shrinkOpCandidates failsPinned shrunkTop
      let traceDesc := String.intercalate "; " (shrunkFull.toList.map summarizeOp)
      throw (IO.userError s!"{msg} [shrunk {ops.size}->{shrunkFull.size} ops tag={tag}: {traceDesc}]")

private def runEpisodeShrunk (ops : Array CmdLineFuzzOp) (tracker : CoverageTracker) : IO CoverageTracker :=
  shrinkOnMismatch (fun c => runEpisode c tracker) ops

private def requiredBuckets : Array CoverageBucket := #[
  bucket "readLine" "ok.some_ascii",
  bucket "readLine" "ok.some_utf8_valid",
  bucket "readLine" "ok.some_utf8_lossy_surrogate",
  bucket "readLine" "ok.some_utf8_lossy_overlong",
  bucket "readLine" "ok.some_utf8_lossy_cont_skip",
  bucket "readLine" "ok.some_nul_embedded",
  bucket "readLine" "ok.some_blank_lf",
  bucket "readLine" "ok.some_crlf_and_crcrlf",
  bucket "readLine" "ok.some_no_trailing_lf",
  bucket "readLine" "ok.some_internal_cr",
  bucket "readLine" "ok.some_large_over_8192",
  bucket "readLine" "ok.eof_pipe",
  bucket "readLine" "ok.eof_null",
  bucket "readLine" "ok.eof_pty_resume",
  bucket "readLine" "err.ebadf_closed",
  bucket "readLine" "err.ebadf_wronly",
  bucket "readLine" "err.eisdir",
  bucket "readLine" "err.eagain_empty",
  bucket "readLine" "err.eagain_partial_drop",
  bucket "readLine" "err.eintr",
  bucket "readLine" "err.pty_eio",
  bucket "readLine" "ok.recover_after_err",
  bucket "writeOut" "ok.nonempty",
  bucket "writeOut" "ok.empty_on_broken_pipe",
  bucket "writeOut" "ok.empty_on_full_dev",
  bucket "writeOut" "ok.empty_after_prior_err",
  bucket "writeOut" "ok.nul_embedded",
  bucket "writeOut" "err.epipe",
  bucket "writeOut" "err.enospc",
  bucket "writeOut" "err.ebadf_closed",
  bucket "writeOut" "err.ebadf_rdonly",
  bucket "writeOut" "err.eagain_full_pipe",
  bucket "writeErr" "ok.nonempty",
  bucket "writeErr" "ok.empty_on_broken_pipe",
  bucket "writeErr" "err.epipe",
  bucket "writeErr" "err.enospc",
  bucket "writeErr" "err.ebadf_rdonly",
  bucket "writeErr" "err.eagain_full_pipe",
  bucket "getEnv" "ok.none",
  bucket "getEnv" "ok.some_empty",
  bucket "getEnv" "ok.some_valid",
  bucket "getEnv" "err.invalid_key",
  bucket "getEnv" "err.invalid_utf8",
  bucket "promptLine" "ok.trimmed",
  bucket "promptLine" "ok.default_on_blank",
  bucket "promptLine" "err.eof",
  bucket "promptLine" "err.ioError_write",
  bucket "promptLine" "err.ioError_read",
  bucket "confirm" "ok.yes",
  bucket "confirm" "ok.no",
  bucket "confirm" "ok.default",
  bucket "confirm" "ok.retry_then_yes",
  bucket "confirm" "err.eof",
  bucket "confirm" "err.invalidValue_exhaust",
  bucket "confirm" "err.ioError_writeOut",
  bucket "confirm" "err.ioError_writeErr_reprompt",
  bucket "confirm" "err.ioError_readLine",
  bucket "runCli" "ret.0_help",
  bucket "runCli" "ret.0_version",
  bucket "runCli" "ret.2_parse_err",
  bucket "runCli" "ret.2_env_ioError",
  bucket "runCli" "ret.handler_code",
  bucket "runCli" "threw.epipe_help",
  bucket "runCli" "threw.enospc_help",
  bucket "runCli" "threw.epipe_err",
  bucket "readLine" "ok.eintr_retry_preserve",
  bucket "parseWithEnv" "err.LeanSwe.CmdLine.CmdLineErrorKind.ioError",
  bucket "subproc" "argv_lossy_utf8",
  bucket "subproc" "sigpipe_dfl_becomes_epipe",
  bucket "subproc" "flush_stdout_before_read",
  bucket "subproc" "flush_stderr_before_read",
  bucket "subproc" "exit_code_mod_256"
]

private def buildDeepSpec (depth : Nat) : CommandSpec := Id.run do
  let mut cur : CommandSpec := {
    name := "leaf"
    options := [{ name := "flag", short := some 'f', long := some "flag", kind := .bool }]
  }
  for i in List.range depth do
    cur := {
      name := if i == depth - 1 then "root" else s!"n{i}"
      options := [{ name := s!"g{i}", long := some s!"g{i}", kind := .nat, global := true }]
      subcommands := [cur]
    }
  return cur

private def buildWideOptsSpec (n : Nat) : CommandSpec × List String := Id.run do
  let mut opts : List OptSpec := []
  let mut args : List String := []
  for i in List.range n do
    opts := { name := s!"o{i}", long := some s!"o{i}", kind := .nat, envVar := some s!"E{i}" } :: opts
    args := s!"--o{i}={i}" :: args
  return ({ name := "wide", options := opts.reverse }, args.reverse)

private def runStackSmokeCheck : IO Unit := do
  let rc ← runOn1MibStackRaw fun () => do
    let deep := buildDeepSpec 20000
    if !CmdLine.isValidSpec deep then return 1
    let mut path : List String := []
    for i in List.range 19999 do
      path := s!"n{19998 - i}" :: path
    let pathFwd := path.reverse ++ ["leaf"]
    let rHelp := CmdLine.renderHelp deep pathFwd
    match rHelp with
    | .error _ => return 2
    | .ok _ => pure ()
    let rDeep ← pure (CmdLine.parse deep (pathFwd ++ ["--flag"]))
    match rDeep with
    | .error _ => return 3
    | .ok pDeep =>
      match CmdLine.renderArgs deep pDeep with
      | .ok _ => pure ()
      | .error _ => return 4
    let natStr := String.ofList (List.replicate 50000 '9')
    let natSpec : CommandSpec := { name := "nat", options := [{ name := "x", long := some "x", kind := .nat }] }
    match CmdLine.parse natSpec [s!"--x={natStr}"] with
    | .error _ => return 5
    | .ok pNat =>
      match CmdLine.renderArgs natSpec pNat with
      | .error _ => return 6
      | .ok toks =>
        if toks != [s!"--x={natStr}"] then return 7
    let (wideSpec, wideArgs) := buildWideOptsSpec 5000
    match CmdLine.parse wideSpec wideArgs with
    | .error _ => return 8
    | .ok pWide =>
      match CmdLine.renderArgs wideSpec pWide with
      | .error _ => return 9
      | .ok _ => pure ()
    let mut envList : List ByteArray := []
    for i in List.range 5000 do
      envList := s!"E{i}={i}".toUTF8 :: envList
    let w : Model.StdioWorld := { rawEnviron := envList }
    match Model.stepResolveOptionsWithEnv w wideSpec.options [] with
    | .error _ => return 10
    | .ok res => if res.length != 5000 then return 11
    return 0
  if rc != 0 then
    throw (IO.userError s!"CMDLINE_1MIB_STACK_FAILED rc={rc}")

private def runTransientEintrProbe : IO Unit := do
  let _ ← saveStdioRaw 0
  let mut feedFd? : Option UInt32 := none
  let mut wrTask? : Option (Task (Except IO.Error UInt32)) := none
  try
    let fd ← setupPipeInRaw "hi".toUTF8 0 0
    if fd == pipeSmallSentinel || fd == invalidFdSentinel || fd == closedWriterSentinel then
      throw (IO.userError s!"TRANSIENT_EINTR_PROBE_SETUP_FAILED fd={fd}")
    feedFd? := some fd
    let t ← IO.asTask (prio := .dedicated) do
      IO.sleep 35
      writeFdRaw fd "!\n".toUTF8
    wrTask? := some t
    let r ← withArmedSigalrm (some 10000) CmdLine.defaultOps.readLine
    let wr ← IO.ofExcept (← IO.wait t)
    wrTask? := none
    if wr != 2 then
      throw (IO.userError s!"TRANSIENT_EINTR_PROBE_WRITE_FAILED wr={wr}")
    if r != some "hi!" then
      throw (IO.userError s!"TRANSIENT_EINTR_PROBE_MISMATCH expected=some \"hi!\" actual={repr r}")
  finally
    disarmSigalrmRaw 0
    if let some t := wrTask? then
      let _ ← IO.wait t
    closeOptFd feedFd?
    let _ ← restoreStdioRaw 0

private def runCmdLineSuite (steps : Nat) (seedVal : UInt64) : IO Unit := do
  runStackSmokeCheck
  let mut tracker := CoverageTracker.empty
  runTransientEintrProbe
  tracker := tracker.record "readLine" "ok.eintr_retry_preserve"
  for ep in boundaryCorpus do
    tracker ← runEpisodeShrunk ep tracker
  let subBuckets ← Subproc.runSubprocChecks
  for b in subBuckets do
    tracker := tracker.record b.op b.bucket
  let mut rng := Rng.seed seedVal
  let mut epOps : Array CmdLineFuzzOp := #[]
  for _ in List.range steps do
    let (op, r1) := genFuzzOp rng
    rng := r1
    epOps := epOps.push op
    if epOps.size >= 24 then
      tracker ← runEpisodeShrunk epOps tracker
      epOps := #[]
  if !epOps.isEmpty then
    tracker ← runEpisodeShrunk epOps tracker
  assertCoverage "cmdline" tracker requiredBuckets
  IO.println (tracker.formatReport "cmdline")
  IO.println s!"FUZZ_SUITE_OK name=cmdline steps={steps} seed={seedVal} total_hits={tracker.total}"

private def runCmdLineSelfTestShrink (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut trace : Array CmdLineFuzzOp := #[]
  for _ in List.range 16 do
    let (op, r1) := genFuzzOp rng
    rng := r1
    let clean := match op with
      | .setupStdin _ | .callReadLine | .armEintr _ | .callPromptLine _ _ | .callConfirm _ _ _ => .callGetEnv "OK"
      | _ => op
    trace := trace.push clean
  let bigPayload := ByteArray.mk (Array.replicate 64 0x41 |>.push 0xed |>.push 0xa0 |>.push 0x80)
  let decoy : Array CmdLineFuzzOp := #[.setupStdin .closedFd, .callReadLine]
  let epBug : Array CmdLineFuzzOp :=
    #[.setupStdin (.pipe bigPayload true false 65536), .callReadLine]
  let combined :=
    decoy ++ trace.extract 0 6 ++ #[epBug[0]!] ++ trace.extract 6 12 ++ #[epBug[1]!] ++ trace.extract 12 trace.size
  let evalRealTag (cand : Array CmdLineFuzzOp) : IO (Option String) := do
    try
      let t ← runEpisode cand CoverageTracker.empty
      if t.get "readLine" "ok.some_utf8_lossy_surrogate" > 0 then
        return some "TARGET_SURROGATE"
      else if t.get "readLine" "err.ebadf_closed" > 0 then
        return some "DECOY_EBADF"
      else
        return none
    catch _ =>
      return none
  let failsTarget (cand : Array CmdLineFuzzOp) : IO Bool := do
    return (← evalRealTag cand) == some "TARGET_SURROGATE"
  unless (← evalRealTag decoy) == some "DECOY_EBADF" do
    throw (IO.userError "CMDLINE_SHRINK_SELFTEST_DECOY: decoy did not trigger DECOY_EBADF")
  let shrunkTop ← match ← verifyShrinker failsTarget combined 2 with
    | .ok st => pure st
    | .error msg => throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_TOP: {msg}")
  let shrunkFull ← shrinkElements shrinkOpCandidates failsTarget shrunkTop
  unless ← failsTarget shrunkFull do
    throw (IO.userError "CMDLINE_SHRINK_SELFTEST_INNER: shrunk trace no longer fails target")
  let innerSize := match shrunkFull[0]? with
    | some (.setupStdin (.pipe bs _ _ _)) => bs.size
    | _ => 999
  if innerSize > 3 then
    throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_INNER: expected <= 3 bytes, got {innerSize}")
  let nulWrite : CmdLineFuzzOp := .callWriteOut (String.ofList (List.replicate 64 'a' ++ [Char.ofNat 0]))
  let shrunkWrite ← shrinkElements shrinkOpCandidates (fun (c : Array CmdLineFuzzOp) =>
    match c[0]? with | some (CmdLineFuzzOp.callWriteOut s) => pure (s.contains (Char.ofNat 0)) | _ => pure false) #[nulWrite]
  let writeLen := match shrunkWrite[0]? with | some (.callWriteOut s) => s.length | _ => 999
  if writeLen != 1 then
    throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_WRITE: expected len=1, got {writeLen}")
  let bigThresh := ByteArray.mk (Array.replicate 8301 0x78)
  let shrunkThresh ← shrinkElements shrinkOpCandidates (fun (c : Array CmdLineFuzzOp) =>
    match c[0]? with | some (CmdLineFuzzOp.setupStdin (.memfd bs)) => pure (bs.size > 8192) | _ => pure false) #[.setupStdin (.memfd bigThresh)]
  let threshSize := match shrunkThresh[0]? with | some (.setupStdin (.memfd bs)) => bs.size | _ => 99999
  if threshSize != 8193 then
    throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_THRESH: expected 8193, got {threshSize}")
  let twoEndBs := ("X" ++ String.ofList (List.replicate 5000 'a') ++ "Y").toUTF8
  let shrunkTwoEnd ← shrinkElements shrinkOpCandidates (fun (c : Array CmdLineFuzzOp) =>
    match c[0]? with
    | some (CmdLineFuzzOp.setupStdin (.memfd bs)) =>
      pure (bs.size > 4096 && bs.size >= 2 && bs[0]! == 0x58 && bs[bs.size - 1]! == 0x59)
    | _ => pure false) #[.setupStdin (.memfd twoEndBs)]
  let twoEndSize := match shrunkTwoEnd[0]? with | some (.setupStdin (.memfd bs)) => bs.size | _ => 99999
  if twoEndSize != 4097 then
    throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_TWOEND_BYTES: expected 4097, got {twoEndSize}")
  let utf8TwoEnd := "🚀" ++ String.ofList (List.replicate 42 'é') ++ "🏁"
  let shrunkUtf8 ← shrinkElements shrinkOpCandidates (fun (c : Array CmdLineFuzzOp) =>
    match c[0]? with
    | some (CmdLineFuzzOp.callWriteOut s) => pure (s.startsWith "🚀" && s.endsWith "🏁" && s.length > 32)
    | _ => pure false) #[.callWriteOut utf8TwoEnd]
  let utf8Len := match shrunkUtf8[0]? with | some (.callWriteOut s) => s.length | _ => 999
  if utf8Len != 33 then
    throw (IO.userError s!"CMDLINE_SHRINK_SELFTEST_UTF8_TWOEND: expected 33, got {utf8Len}")
  let failRunner (cand : Array CmdLineFuzzOp) : IO CoverageTracker := do
    let t ← runEpisode cand CoverageTracker.empty
    if t.get "readLine" "ok.some_utf8_lossy_surrogate" > 0 then
      throw (IO.userError s!"FUZZ_MISMATCH|SELFTEST|surrogate|hits={t.total}")
    if t.get "readLine" "err.ebadf_closed" > 0 then
      throw (IO.userError s!"FUZZ_MISMATCH|DECOY|ebadf|hits={t.total}")
    return t
  let mut gotE2eShrink := false
  try
    let _ ← shrinkOnMismatch failRunner combined
  catch e =>
    let msg := e.toString
    if (msg.splitOn "shrunk 20->2 ops tag=SELFTEST|surrogate").length > 1 then
      gotE2eShrink := true
  unless gotE2eShrink do
    throw (IO.userError "CMDLINE_SHRINK_SELFTEST_E2E: shrinkOnMismatch did not pin and shrink SELFTEST|surrogate to 2 ops")
  IO.println s!"CMDLINE_SHRINK_SELFTEST_OK orig_top={combined.size} shrunk_top={shrunkTop.size} orig_inner={bigPayload.size} shrunk_inner={innerSize}"

/-- Differential fuzzing suite for `LeanSwe.CmdLine` stdio/env/CLI/OS boundaries. -/
def suite : FuzzSuite := {
  name := "cmdline"
  description := "Differential fuzzer for LeanSwe.CmdLine, LinuxSyscall.Files stdio fd semantics, EnvVars, argv UTF-8, and SIGPIPE/flush/exit"
  runSmoke := fun cfg => runCmdLineSuite 200 cfg.seed
  runFuzz := fun cfg => runCmdLineSuite cfg.steps cfg.seed
  selfTestShrink := runCmdLineSelfTestShrink
}

end Fuzz.CmdLine
