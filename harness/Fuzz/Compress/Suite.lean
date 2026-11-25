import Fuzz.Common.Rng
import Fuzz.Common.Coverage
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import Fuzz.Compress.Oracle
import Fuzz.Compress.Gen
import LeanSwe.Compress.Model
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSwe.Process.Interface
import LeanSwe.Fs.Interface

namespace Fuzz.Compress

open Fuzz.Common
open LeanSwe.Compress
open LeanSwe.Process

private def codecTag : Codec → String
  | .zstd => "zstd"
  | .xz => "xz"
  | .gzip => "gzip"

private def errorKindTag : CompressErrorKind → String
  | .toolNotFound => "toolNotFound"
  | .invalidInput => "invalidInput"
  | .corruptData => "corruptData"
  | .outputLimitExceeded => "outputLimitExceeded"
  | .timedOut => "timedOut"
  | .commandFailed => "commandFailed"
  | .ioError => "ioError"

private def randRequiredBuckets : Array CoverageBucket := Id.run do
  let mut req : Array CoverageBucket := #[]
  for c in #[Codec.zstd, Codec.xz, Codec.gzip] do
    let t := codecTag c
    req := req ++ #[
      bucket s!"isToolAvailable.{t}" "true",
      bucket s!"compress.{t}" "ok",
      bucket s!"compressWith.{t}" "ok",
      bucket s!"compressWith.{t}" "err.invalidInput",
      bucket s!"compressWith.{t}" "err.outputLimitExceeded",
      bucket s!"decompress.{t}" "ok",
      bucket s!"decompress.{t}" "ok.multiOrPadded",
      bucket s!"decompress.{t}" "err.corruptData",
      bucket s!"decompress.{t}" "err.corruptData.foreignOrLegacy",
      bucket s!"decompressWith.{t}" "ok",
      bucket s!"decompressWith.{t}" "err.invalidInput",
      bucket s!"decompressWith.{t}" "err.corruptData",
      bucket s!"decompressWith.{t}" "err.outputLimitExceeded",
      bucket s!"decompressWith.{t}" "err.corruptData.tinyLimit"
    ]
  req := req ++ #[
    bucket "decompressWith" "ok",
    bucket "decompressWith" "err.invalidInput",
    bucket "decompressWith" "err.corruptData",
    bucket "decompressWith" "err.outputLimitExceeded",
    bucket "decompressWith" "err.corruptData.tinyLimit"
  ]
  return req

private def osRequiredBuckets : Array CoverageBucket := Id.run do
  let mut req : Array CoverageBucket := #[]
  for c in #[Codec.zstd, Codec.xz, Codec.gzip] do
    let t := codecTag c
    req := req ++ #[
      bucket s!"isToolAvailable.{t}" "false",
      bucket s!"compress.{t}" "err.toolNotFound",
      bucket s!"compress.{t}" "err.invalidInput",
      bucket s!"compress.{t}" "err.outputLimitExceeded",
      bucket s!"compress.{t}" "err.commandFailed",
      bucket s!"compress.{t}" "err.ioError",
      bucket s!"compress.{t}" "err.timedOut",
      bucket s!"compressWith.{t}" "err.toolNotFound",
      bucket s!"compressWith.{t}" "err.invalidInput",
      bucket s!"compressWith.{t}" "err.outputLimitExceeded",
      bucket s!"compressWith.{t}" "err.commandFailed",
      bucket s!"compressWith.{t}" "err.ioError",
      bucket s!"compressWith.{t}" "err.timedOut",
      bucket s!"decompress.{t}" "err.toolNotFound",
      bucket s!"decompress.{t}" "err.invalidInput",
      bucket s!"decompress.{t}" "err.outputLimitExceeded",
      bucket s!"decompress.{t}" "err.commandFailed",
      bucket s!"decompress.{t}" "err.ioError",
      bucket s!"decompress.{t}" "err.timedOut",
      bucket s!"decompressWith.{t}" "err.toolNotFound",
      bucket s!"decompressWith.{t}" "err.invalidInput",
      bucket s!"decompressWith.{t}" "err.outputLimitExceeded",
      bucket s!"decompressWith.{t}" "err.commandFailed",
      bucket s!"decompressWith.{t}" "err.ioError",
      bucket s!"decompressWith.{t}" "err.timedOut"
    ]
  req := req ++ #[
    bucket "compressWith" "err.invalidInput",
    bucket "compressWith" "err.outputLimitExceeded",
    bucket "compressWith" "err.timedOut",
    bucket "compressWith" "err.toolNotFound",
    bucket "compressWith" "err.commandFailed",
    bucket "compressWith" "err.ioError",
    bucket "decompressWith" "err.invalidInput",
    bucket "decompressWith" "err.outputLimitExceeded",
    bucket "decompressWith" "err.timedOut",
    bucket "decompressWith" "err.toolNotFound",
    bucket "decompressWith" "err.commandFailed",
    bucket "decompressWith" "err.ioError"
  ]
  return req

private def mkEnvProc (extraEnv : Array (String × Option String)) (inherit : Bool := true) :
    LeanSwe.Process.ProcessApi :=
  { LeanSwe.Process.defaultApi with
    run := fun req =>
      LeanSwe.Process.defaultApi.run
        { req with env := extraEnv ++ req.env, inheritEnv := inherit } }

private def mkEnvApi (extraEnv : Array (String × Option String)) (inherit : Bool := true) :
    CompressApiM IO :=
  LeanSwe.Compress.Internal.mkApiM (mkEnvProc extraEnv inherit)

private def isMultiOrPaddedTag (tag : String) : Bool :=
  tag == "multi" || tag == "padded" || tag == "padMulti" || tag == "skipOnly" ||
  tag == "skipPre" || tag == "skipPost"

private def isMustAgreeTag (tag : String) : Bool :=
  tag == "storedModel" || tag == "pythonValid" || tag == "cliValid" ||
  tag == "multi" || tag == "skipOnly" || tag == "skipPre" || tag == "skipPost" ||
  tag == "poolReplay" || tag == "poolExactLimit" || tag == "poolTightLimit" ||
  tag == "bombLimit" || tag == "xzX86Bcj" || tag == "xzDelta4" ||
  tag == "xzX86Delta" || tag == "xzDict96MiB" || tag == "pyXzX86Bcj" ||
  tag == "reg.exactLim" || tag == "reg.exactLimMinus1" || tag == "reg.exactReplay" ||
  tag == "reg.xz0x02" || tag.startsWith "reg.comp." || tag.startsWith "reg.dec."

private def checkImplMatchesPy (codec : Codec) (maxOut? : Option Nat) (tag : String) (input : ByteArray)
    (implRes : Except CompressError ByteArray) (oracle : PyOracle) : IO (Option String) := do
  let pyRes ← oracle.decompress codec input
  let mustAgree := isMustAgreeTag tag
  match implRes, pyRes with
  | .ok outBytes, .ok pPlain =>
    if outBytes == pPlain then
      return none
    else
      return some s!"impl/python plain mismatch codec={codecTag codec} implSize={outBytes.size} pySize={pPlain.size}"
  | .ok outBytes, .corrupt =>
    if mustAgree then
      return some s!"impl=ok({outBytes.size}) vs python=corrupt codec={codecTag codec} inSize={input.size}"
    else
      return none
  | .error e, .ok pPlain =>
    match maxOut? with
    | some lim =>
      if e.kind == .outputLimitExceeded then
        if pPlain.size > lim then
          return none
        else
          return some s!"impl=outputLimitExceeded({lim}) vs python=ok({pPlain.size}) codec={codecTag codec}"
      else if mustAgree then
        return some s!"impl={errorKindTag e.kind} vs python=ok({pPlain.size}) codec={codecTag codec} inSize={input.size}"
      else
        return none
    | none =>
      if mustAgree then
        return some s!"impl={errorKindTag e.kind} vs python=ok({pPlain.size}) codec={codecTag codec} inSize={input.size}"
      else
        return none
  | .error e, .corrupt =>
    if mustAgree then
      return some s!"impl={errorKindTag e.kind} and python=corrupt on valid stream codec={codecTag codec} inSize={input.size}"
    else if e.kind == .corruptData || e.kind == .outputLimitExceeded then
      return none
    else
      return some s!"impl={errorKindTag e.kind} vs python=corrupt codec={codecTag codec} inSize={input.size}"

private def isCleanAvailableEnv (env : Model.CompressEnv) (codec : Codec) : Bool :=
  env.toolStatus codec == .available &&
  !env.allowTimeout &&
  !env.allowResourceIoError &&
  !env.allowExternalSignal

private structure EvalResult where
  state : Model.State
  tracker : CoverageTracker
  err? : Option String
  produced? : Option (Codec × ByteArray × ByteArray) := none

private def evalOp (env : Model.CompressEnv) (api : CompressApiM IO) (oracle? : Option PyOracle)
    (st : Model.State) (op : CompressFuzzOp) (tracker : CoverageTracker) :
    IO EvalResult := do
  match op with
  | .isToolAvailable codec =>
    let avail ← api.isToolAvailable codec
    let tr' := tracker.record s!"isToolAvailable.{codecTag codec}" (if avail then "true" else "false")
    if !Model.allowedIsToolAvailable env codec avail then
      return { state := st, tracker := tr', err? := some s!"isToolAvailable mismatch codec={codecTag codec} avail={avail}" }
    return { state := st, tracker := tr', err? := none }
  | .compress codec payload =>
    let res ← api.compress codec payload
    let tr' :=
      match res with
      | .ok _ => tracker.record s!"compress.{codecTag codec}" "ok"
      | .error e => tracker.record s!"compress.{codecTag codec}" s!"err.{errorKindTag e.kind}"
    let st1 := match res with | .ok comp => st.record codec comp payload | .error _ => st
    if !Model.allowedCompressStep env st codec {} payload res st1 then
      let msg :=
        match res with
        | .ok c => s!"compress model reject ok codec={codecTag codec} compSize={c.size} inSize={payload.size}"
        | .error e => s!"compress model reject err codec={codecTag codec} kind={errorKindTag e.kind} msg={e.message}"
      return { state := st1, tracker := tr', err? := some msg }
    match res, oracle? with
    | .ok comp, some oracle =>
      let pyOut ← oracle.decompress codec comp
      if pyOut != .ok payload then
        return { state := st1, tracker := tr', err? := some s!"compress->pyDecompress mismatch codec={codecTag codec} compSize={comp.size} py={repr pyOut}" }
      match ← LeanSwe.Compress.decompress codec comp with
      | .ok outBytes =>
        if outBytes != payload then
          return { state := st1, tracker := tr', err? := some s!"compress->cliDecompress mismatch codec={codecTag codec}" }
      | .error e =>
        return { state := st1, tracker := tr', err? := some s!"compress->cliDecompress error codec={codecTag codec} msg={e.message}" }
    | _, _ => pure ()
    let prod? := match res with | .ok comp => some (codec, comp, payload) | .error _ => none
    return { state := st1, tracker := tr', err? := none, produced? := prod? }
  | .compressWith codec opts payload =>
    let res ← api.compressWith codec opts payload
    let bkt := match res with | .ok _ => "ok" | .error e => s!"err.{errorKindTag e.kind}"
    let tr' := (tracker.record s!"compressWith.{codecTag codec}" bkt).record "compressWith" bkt
    let st1 := match res with | .ok comp => st.record codec comp payload | .error _ => st
    if !Model.allowedCompressStep env st codec opts payload res st1 then
      let msg :=
        match res with
        | .ok c => s!"compressWith model reject ok codec={codecTag codec} compSize={c.size} opts={repr opts}"
        | .error e => s!"compressWith model reject err codec={codecTag codec} kind={errorKindTag e.kind} msg={e.message}"
      return { state := st1, tracker := tr', err? := some msg }
    match res, oracle? with
    | .ok comp, some oracle =>
      let pyOut ← oracle.decompress codec comp
      if pyOut != .ok payload then
        return { state := st1, tracker := tr', err? := some s!"compressWith->pyDecompress mismatch codec={codecTag codec} opts={repr opts}" }
      match ← LeanSwe.Compress.decompress codec comp with
      | .ok outBytes =>
        if outBytes != payload then
          return { state := st1, tracker := tr', err? := some s!"compressWith->cliDecompress mismatch codec={codecTag codec}" }
      | .error e =>
        return { state := st1, tracker := tr', err? := some s!"compressWith->cliDecompress error codec={codecTag codec} msg={e.message}" }
    | _, _ => pure ()
    let prod? := match res with | .ok comp => some (codec, comp, payload) | .error _ => none
    return { state := st1, tracker := tr', err? := none, produced? := prod? }
  | .decompress codec input tag =>
    let res ← api.decompress codec input
    let bkt :=
      match res with
      | .ok _ => if isMultiOrPaddedTag tag then "ok.multiOrPadded" else "ok"
      | .error e =>
        if tag == "foreignOrLegacy" && e.kind == .corruptData then "err.corruptData.foreignOrLegacy"
        else s!"err.{errorKindTag e.kind}"
    let tr1 := tracker.record s!"decompress.{codecTag codec}" bkt
    let tr' := if bkt == "ok.multiOrPadded" then tr1.record s!"decompress.{codecTag codec}" "ok" else tr1
    let st1 := match res with | .ok out => st.record codec input out | .error _ => st
    if !Model.allowedDecompressStep env st codec {} input res st1 then
      let msg :=
        match res with
        | .ok o => s!"decompress model reject ok codec={codecTag codec} tag={tag} outSize={o.size} inSize={input.size}"
        | .error e => s!"decompress model reject err codec={codecTag codec} tag={tag} kind={errorKindTag e.kind} msg={e.message}"
      return { state := st1, tracker := tr', err? := some msg }
    match oracle? with
    | some oracle =>
      if Model.isValidDecompressInput {} input && isCleanAvailableEnv env codec then
        let d0 : DecompressOptions := {}
        if let some errMsg ← checkImplMatchesPy codec (some d0.maxOutputBytes) tag input res oracle then
          return { state := st1, tracker := tr', err? := some s!"decompress(tag={tag}): {errMsg}" }
    | none => pure ()
    let prod? :=
      if isMustAgreeTag tag then
        match res with | .ok out => some (codec, input, out) | .error _ => none
      else
        none
    return { state := st1, tracker := tr', err? := none, produced? := prod? }
  | .decompressWith codec opts input tag =>
    let res ← api.decompressWith codec opts input
    let bkt :=
      match res with
      | .ok _ => "ok"
      | .error e =>
        if e.kind == .corruptData && opts.maxOutputBytes <= 4 then "err.corruptData.tinyLimit"
        else s!"err.{errorKindTag e.kind}"
    let tr' := (tracker.record s!"decompressWith.{codecTag codec}" bkt).record "decompressWith" bkt
    let st1 := match res with | .ok out => st.record codec input out | .error _ => st
    if !Model.allowedDecompressStep env st codec opts input res st1 then
      let msg :=
        match res with
        | .ok o => s!"decompressWith model reject ok codec={codecTag codec} tag={tag} outSize={o.size} opts={repr opts}"
        | .error e => s!"decompressWith model reject err codec={codecTag codec} tag={tag} kind={errorKindTag e.kind} msg={e.message}"
      return { state := st1, tracker := tr', err? := some msg }
    match oracle? with
    | some oracle =>
      if Model.isValidDecompressInput opts input && isCleanAvailableEnv env codec then
        if let some errMsg ← checkImplMatchesPy codec (some opts.maxOutputBytes) tag input res oracle then
          return { state := st1, tracker := tr', err? := some s!"decompressWith(tag={tag}): {errMsg}" }
    | none => pure ()
    let prod? :=
      if isMustAgreeTag tag then
        match res with | .ok out => some (codec, input, out) | .error _ => none
      else
        none
    return { state := st1, tracker := tr', err? := none, produced? := prod? }

private def genValidStreamViaCli (codec : Codec) (r : Rng) : IO (ByteArray × Rng) := do
  let (plain, r1) := genBoundaryPayload r
  match ← LeanSwe.Compress.compressWith codec { level := some (if codec == .xz then 0 else 1) } plain with
  | .ok comp => return (comp, r1)
  | .error _ => return (Model.encodeStored codec plain, r1)

private def genNextOp (oracle : PyOracle) (r : Rng) : IO (CompressFuzzOp × Rng) := do
  let (codec, r1) := genCodec r
  let (probeAvail, r2) := r1.nextNat 20
  if probeAvail == 0 then
    return (.isToolAvailable codec, r2)
  let (fam, r3) := genFamily r2
  match fam with
  | .storedModel =>
    let (plain, r4) := genBoundaryPayload r3
    let (useWith, r5) := r4.nextBool
    let s := Model.encodeStored codec plain
    if useWith then
      let (setExactMax, r6) := r5.nextBool
      let opts : DecompressOptions := if setExactMax then { maxInputBytes := some s.size } else {}
      return (.decompressWith codec opts s "storedModel", r6)
    else
      return (.decompress codec s "storedModel", r5)
  | .cliValid =>
    let (plain, r4) := genBoundaryPayload r3
    let (useWith, r5) := r4.nextBool
    if useWith then
      let (opts0, r6) := genValidCompressOptions codec r5
      let (setExactMax, r7) := r6.nextBool
      let opts1 :=
        if plain.size > 8192 && (opts0.level.getD 0 >= 6) then
          { opts0 with level := some (if codec == .xz then 1 else 3) }
        else opts0
      let opts := if setExactMax then { opts1 with maxInputBytes := some plain.size } else opts1
      return (.compressWith codec opts plain, r7)
    else
      return (.compress codec plain, r5)
  | .pythonValidAndRichHeaders =>
    let (usePy, r4) := r3.nextBool
    if usePy then
      let (plain, r5) := genBoundaryPayload r4
      let s ← oracle.compress codec plain
      let (useWith, r6) := r5.nextBool
      if useWith then
        return (.decompressWith codec {} s "pythonValid", r6)
      else
        return (.decompress codec s "pythonValid", r6)
    else
      let (useEdge, r4b) := r4.nextNat 3
      if useEdge == 0 then
        return genCodecBoundaryEdgeOp codec r4b
      else
        let (s, r5) := genRichHeaderStream codec r4b
        let (useWith, r6) := r5.nextBool
        if useWith then
          return (.decompressWith codec {} s "richHeader", r6)
        else
          return (.decompress codec s "richHeader", r6)
  | .multiFrameAndPadding =>
    let (s1, r4) ← genValidStreamViaCli codec r3
    let (p2, r5) := r4.nextBytesRange 0 32
    let s2 := Model.encodeStored codec p2
    let ((stream, tag), r6) := genMultiOrPadded codec s1 s2 r5
    return (.decompress codec stream tag, r6)
  | .foreignAndLegacyConfusion =>
    let (stream, r4) := genForeignOrLegacyStream codec r3
    return (.decompress codec stream "foreignOrLegacy", r4)
  | .surgicalCorrupt =>
    let (srcKind, r4) := r3.nextNat 3
    let (base, r5) ←
      if srcKind == 0 then
        genValidStreamViaCli codec r4
      else if srcKind == 1 then
        pure (genRichHeaderStream codec r4)
      else
        let (p, r5') := r4.nextBytesRange 0 64
        pure (Model.encodeStored codec p, r5')
    let (corrupt, r6) := corruptStreamSurgically codec base r5
    let (useWith, r7) := r6.nextBool
    if useWith then
      return (.decompressWith codec {} corrupt "surgicalCorrupt", r7)
    else
      return (.decompress codec corrupt "surgicalCorrupt", r7)
  | .truncatedPrefixes =>
    let (s, r4) ← genValidStreamViaCli codec r3
    if s.isEmpty then
      return (.decompress codec s "truncated", r4)
    let (k, r5) := r4.nextNat s.size
    return (.decompress codec (s.extract 0 k) "truncated", r5)
  | .bombsAndOutputLimits =>
    let (subKind, r4) := r3.nextNat 12
    if subKind < 4 then
      let (bomb, r5) := genBombPayload r4
      let (comp, r6) :=
        match ← LeanSwe.Compress.compressWith codec { level := some (if codec == .xz then 0 else 1) } bomb with
        | .ok c => (c, r5)
        | .error _ => (Model.encodeStored codec bomb, r5)
      let (lim, r7) := r6.choose #[1, 2, 10, 32, 33, 37, 40, 255, 1024, bomb.size - 1, bomb.size + 1] 1024
      return (.decompressWith codec { maxOutputBytes := lim } comp "bombLimit", r7)
    else if subKind < 6 then
      let plain := pushReplicateByte ByteArray.empty 0x41 16384
      let corruptTail := Model.encodeStored codec plain ++ ByteArray.mk #[0xFF, 0x00, 0xAB]
      let (lim, r5) := r4.choose #[1, 32, 37, 255, 1024] 32
      return (.decompressWith codec { maxOutputBytes := lim } corruptTail "corruptAfterLimit", r5)
    else if subKind < 9 then
      let (tiny, r5) := r4.choose #[ByteArray.mk #[0xFF, 0x00], "bad".toUTF8] "bad".toUTF8
      let (lim, r6) := r5.choose #[1, 2, 4] 1
      return (.decompressWith codec { maxOutputBytes := lim } tiny "tinyLimit", r6)
    else
      let (p, r5) := r4.nextBytesRange 64 256
      let (lim, r6) := r5.choose #[1, 2, 4, 8] 4
      return (.compressWith codec { maxOutputBytes := lim } p, r6)
  | .invalidOptions =>
    let (invOp, r4) := genInvalidOptionOp codec r3
    return (invOp, r4)
  | .rawRandomBytes =>
    let (bs, r4) := r3.nextBytesRange 0 2048
    return (.decompress codec bs "rawRandom", r4)

private def mkChmod (mode path : String) : IO Unit := do
  match ← LeanSwe.Process.run { program := "chmod", args := #[mode, path], timeoutMs := some 5000 } with
  | .ok res =>
    if res.exitCode != 0 then
      throw (IO.userError s!"chmod {mode} {path} failed exit={res.exitCode}")
  | .error e =>
    throw (IO.userError s!"chmod {mode} {path} process error: {e.message}")

private def readDeviceBytes (devPath : String) (n : Nat) : IO ByteArray := do
  IO.FS.withFile devPath .read fun h => do
    let mut out := ByteArray.emptyWithCapacity n
    while out.size < n do
      let chunk ← h.read (USize.ofNat (n - out.size))
      if chunk.isEmpty then
        throw (IO.userError s!"unexpected EOF reading {devPath}")
      out := out ++ chunk
    return out

private def readUrandom (n : Nat) : IO ByteArray :=
  readDeviceBytes "/dev/urandom" n

private def readZeroBytes (n : Nat) : IO ByteArray :=
  readDeviceBytes "/dev/zero" n

private def runCheckedOsOp (label : String) (env : Model.CompressEnv) (api : CompressApiM IO)
    (op : CompressFuzzOp) (tracker : CoverageTracker) : IO CoverageTracker := do
  let er ← evalOp env api none Model.State.empty op tracker
  if let some msg := er.err? then
    throw (IO.userError s!"OS_SUBPASS_FAIL({label}): {msg}")
  return er.tracker

private def runOsSubPass (oracle : PyOracle) (tracker : CoverageTracker) : IO CoverageTracker := do
  let mut tr := tracker
  let allCodecs := #[Codec.zstd, Codec.xz, Codec.gzip]
  let emptyDir ← IO.FS.createTempDir
  try
    let emptyApi := mkEnvApi #[("PATH", some emptyDir.toString)] false
    let envMissing : Model.CompressEnv := { toolStatus := fun _ => .missingOrNonExec }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"emptyPath.avail.{codecTag c}" envMissing emptyApi (.isToolAvailable c) tr
      tr ← runCheckedOsOp s!"emptyPath.comp.{codecTag c}" envMissing emptyApi (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"emptyPath.compW.{codecTag c}" envMissing emptyApi (.compressWith c {} "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"emptyPath.dec.{codecTag c}" envMissing emptyApi (.decompress c "hi".toUTF8 "osMissing") tr
      tr ← runCheckedOsOp s!"emptyPath.decW.{codecTag c}" envMissing emptyApi (.decompressWith c {} "hi".toUTF8 "osMissing") tr
  finally
    IO.FS.removeDirAll emptyDir

  let nonExecDir ← IO.FS.createTempDir
  try
    for prog in #["zstd", "xz", "gzip"] do
      let p := (nonExecDir / prog).toString
      IO.FS.writeFile p "#!/bin/sh\nexit 0\n"
      mkChmod "0644" p
    let nonExecApi := mkEnvApi #[("PATH", some nonExecDir.toString)] false
    let envMissing : Model.CompressEnv := { toolStatus := fun _ => .missingOrNonExec }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"nonExec.comp.{codecTag c}" envMissing nonExecApi (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"nonExec.decW.{codecTag c}" envMissing nonExecApi (.decompressWith c {} "hi".toUTF8 "osNonExec") tr
  finally
    IO.FS.removeDirAll nonExecDir

  let eloopDir ← IO.FS.createTempDir
  try
    for prog in #["zstd", "xz", "gzip"] do
      match ← LeanSwe.Fs.symlink prog (eloopDir / prog).toString with
      | .ok () => pure ()
      | .error fe => throw (IO.userError s!"symlink failed for {prog}: {fe.message}")
    let eloopApi := mkEnvApi #[("PATH", some eloopDir.toString)] false
    let envEloop : Model.CompressEnv := { toolStatus := fun _ => .pathSymlinkLoop }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"eloop.comp.{codecTag c}" envEloop eloopApi (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"eloop.compW.{codecTag c}" envEloop eloopApi (.compressWith c {} "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"eloop.dec.{codecTag c}" envEloop eloopApi (.decompress c "hi".toUTF8 "osEloop") tr
      tr ← runCheckedOsOp s!"eloop.decW.{codecTag c}" envEloop eloopApi (.decompressWith c {} "hi".toUTF8 "osEloop") tr
  finally
    IO.FS.removeDirAll eloopDir

  let longPath := String.ofList (List.replicate 5000 'a')
  let longApi := mkEnvApi #[("PATH", some longPath)] false
  let compLongPath := "/" ++ String.ofList (List.replicate 300 'a')
  let compLongApi := mkEnvApi #[("PATH", some compLongPath)] false
  let envIo : Model.CompressEnv := { toolStatus := fun _ => .pathOrPipeIoError }
  for c in allCodecs do
    tr ← runCheckedOsOp s!"enametoolong.comp.{codecTag c}" envIo longApi (.compress c "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"enametoolong.compW.{codecTag c}" envIo longApi (.compressWith c {} "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"enametoolong.dec.{codecTag c}" envIo longApi (.decompress c "hi".toUTF8 "osIo") tr
    tr ← runCheckedOsOp s!"enametoolong.decW.{codecTag c}" envIo longApi (.decompressWith c {} "hi".toUTF8 "osIo") tr
    tr ← runCheckedOsOp s!"enametoolong36.comp.{codecTag c}" envIo compLongApi (.compress c "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"enametoolong36.decW.{codecTag c}" envIo compLongApi (.decompressWith c {} "hi".toUTF8 "osIo") tr

  let rsrcErrnos : Array (String × UInt32) := #[
    ("e2big", 7), ("eagain", 11), ("enomem", 12), ("enfile", 23), ("emfile", 24),
    ("enospc", 28), ("emlink", 31), ("enametoolong", 36), ("enolck", 37),
    ("enosr", 63), ("emsgsize", 90), ("enobufs", 105)
  ]
  for (lbl, code) in rsrcErrnos do
    let pe : ProcessError := { kind := .invalidInput, errnoCode := some code, message := "spawn failed" }
    let rsrcApi : CompressApiM IO :=
      LeanSwe.Compress.Internal.mkApiM { LeanSwe.Process.defaultApi with run := fun _ => pure (.error pe) }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"{lbl}.comp.{codecTag c}" envIo rsrcApi (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"{lbl}.decW.{codecTag c}" envIo rsrcApi (.decompressWith c {} "hi".toUTF8 "osIo") tr

  let peNoErrno : ProcessError := { kind := .invalidInput, errnoCode := none, message := "cannot allocate memory" }
  let noErrnoMsgApi : CompressApiM IO :=
    LeanSwe.Compress.Internal.mkApiM { LeanSwe.Process.defaultApi with run := fun _ => pure (.error peNoErrno) }
  let envLoop : Model.CompressEnv := { toolStatus := fun _ => .pathSymlinkLoop }
  tr ← runCheckedOsOp "noErrnoMsg.comp.zstd" envLoop noErrnoMsgApi (.compress .zstd "hi".toUTF8) tr
  tr ← runCheckedOsOp "noErrnoMsg.decW.zstd" envLoop noErrnoMsgApi (.decompressWith .zstd {} "hi".toUTF8 "osPrec") tr

  for (lbl, code) in #[("einvalPrec", (22 : UInt32)), ("eloopPrec", (40 : UInt32))] do
    let pe : ProcessError :=
      { kind := .invalidInput, errnoCode := some code, message := "/tmp/too many open files/zstd: invalid" }
    let precApi : CompressApiM IO :=
      LeanSwe.Compress.Internal.mkApiM { LeanSwe.Process.defaultApi with run := fun _ => pure (.error pe) }
    tr ← runCheckedOsOp s!"{lbl}.comp.zstd" envLoop precApi (.compress .zstd "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"{lbl}.decW.zstd" envLoop precApi (.decompressWith .zstd {} "hi".toUTF8 "osPrec") tr

  let validZstdEmpty := Model.encodeStored .zstd ByteArray.empty
  let childStderrProc : LeanSwe.Process.ProcessApi :=
    { LeanSwe.Process.defaultApi with
      run := fun _ =>
        pure (.ok { exitCode := 1, stdout := ByteArray.empty, stderr := "\ngzip: memory_exhausted\n".toUTF8 }) }
  let childStderrApi := LeanSwe.Compress.Internal.mkApiM childStderrProc
  tr ← runCheckedOsOp "childStderr.comp" { allowExternalSignal := true } childStderrApi (.compress .gzip "hi".toUTF8) tr
  tr ← runCheckedOsOp "childStderr.dec" {} childStderrApi (.decompress .gzip "bad".toUTF8 "osChildStderr") tr

  let ldEnoentProc : LeanSwe.Process.ProcessApi :=
    { LeanSwe.Process.defaultApi with
      run := fun _ =>
        pure (.ok {
          exitCode := 127
          stdout := ByteArray.empty
          stderr := "zstd: error while loading shared libraries: libmissing.so: cannot open shared object file: No such file or directory\n".toUTF8 }) }
  let ldEnoentApi := LeanSwe.Compress.Internal.mkApiM ldEnoentProc
  tr ← runCheckedOsOp "childLdEnoent.comp" { allowExternalSignal := true } ldEnoentApi (.compress .zstd "hi".toUTF8) tr
  tr ← runCheckedOsOp "childLdEnoent.dec" {} ldEnoentApi (.decompress .zstd "bad".toUTF8 "osLdEnoent") tr

  let memLimProc : LeanSwe.Process.ProcessApi :=
    { LeanSwe.Process.defaultApi with
      run := fun _ =>
        pure (.ok { exitCode := 1, stdout := ByteArray.empty, stderr := "xz: (stdin): Memory usage limit reached\n".toUTF8 }) }
  tr ← runCheckedOsOp "xzMemlimitCorrupt" {} (LeanSwe.Compress.Internal.mkApiM memLimProc)
    (.decompress .xz "bad".toUTF8 "osMemlimit") tr

  let timedOutProc : LeanSwe.Process.ProcessApi :=
    { LeanSwe.Process.defaultApi with
      run := fun _ =>
        pure (.error { kind := .timedOut, message := "process timed out" }) }
  let timedOutApi := LeanSwe.Compress.Internal.mkApiM timedOutProc
  let envTimedOut : Model.CompressEnv := { allowTimeout := true }
  for c in allCodecs do
    let validEmpty := Model.encodeStored c ByteArray.empty
    tr ← runCheckedOsOp s!"mockTimeout.comp.{codecTag c}" envTimedOut timedOutApi (.compress c "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"mockTimeout.compW.{codecTag c}" envTimedOut timedOutApi (.compressWith c {} "hi".toUTF8) tr
    tr ← runCheckedOsOp s!"mockTimeout.decValid.{codecTag c}" envTimedOut timedOutApi (.decompress c validEmpty "osTimedOut") tr
    let decFramingEnv : Model.CompressEnv := if c == .gzip then {} else envTimedOut
    tr ← runCheckedOsOp s!"mockTimeout.decFraming.{codecTag c}" decFramingEnv timedOutApi
      (.decompressWith c { maxOutputBytes := 64 } "bad".toUTF8 "osTimedOutFraming") tr

  let normCheckOps (pe : ProcessError) : CompressApiM IO :=
    LeanSwe.Compress.Internal.mkApiM {
      LeanSwe.Process.defaultApi with
      run := fun _ => pure (.error pe) }
  tr ← runCheckedOsOp "normNotFoundStderr" { toolStatus := fun _ => .missingOrNonExec }
    (normCheckOps { kind := .notFound, stderr := some "not found\n".toUTF8, message := "missing" })
    (.compress .zstd "hi".toUTF8) tr
  tr ← runCheckedOsOp "normCmdZeroExit" { allowExternalSignal := true }
    (normCheckOps { kind := .nonZeroExit, exitCode := some 0, stderr := some "sig\n".toUTF8, message := "failed" })
    (.compress .zstd "hi".toUTF8) tr

  let wantSanitizedEnv : Array (String × Option String) := #[
    ("XZ_OPT", none),
    ("XZ_DEFAULTS", none),
    ("ZSTD_CLEVEL", none),
    ("ZSTD_NBTHREADS", none),
    ("GZIP", none),
    ("LC_ALL", some "C")
  ]
  let seenZstdComp ← IO.mkRef 0
  let seenZstdCompOpts ← IO.mkRef 0
  let seenZstdDec ← IO.mkRef 0
  let seenXzCompOpts ← IO.mkRef 0
  let seenXzDec ← IO.mkRef 0
  let seenGzipArgs ← IO.mkRef 0
  let seenGzipCompOpts ← IO.mkRef 0
  let badSanitizedEnv ← IO.mkRef 0
  let inspectArgsProc : LeanSwe.Process.ProcessApi :=
    { LeanSwe.Process.defaultApi with
      run := fun req => do
        if req.env != wantSanitizedEnv || !req.inheritEnv then
          badSanitizedEnv.modify (· + 1)
        if req.program == "zstd" && req.args.contains "--no-progress" && !req.args.contains "--no-asyncio" then
          if req.args.contains "-d" then
            if req.args.contains "--format=zstd" then
              seenZstdDec.modify (· + 1)
          else
            seenZstdComp.modify (· + 1)
            if req.args.contains "-7" && req.args.contains "-T2" && req.maxOutputBytes == some 6144 then
              seenZstdCompOpts.modify (· + 1)
        if req.program == "xz" then
          if req.args == #["-d", "-c", "-q", "-T1", "--format=xz"] then
            seenXzDec.modify (· + 1)
          else if req.args == #["-c", "-q", "-3", "-T2"] && req.maxOutputBytes == some 6144 then
            seenXzCompOpts.modify (· + 1)
        if req.program == "gzip" && req.args.contains "-n" then
          seenGzipArgs.modify (· + 1)
          if req.args.contains "-9" && req.maxOutputBytes == some 6144 then
            seenGzipCompOpts.modify (· + 1)
        LeanSwe.Process.defaultApi.run req }
  let inspectArgsApi := LeanSwe.Compress.Internal.mkApiM inspectArgsProc
  tr ← runCheckedOsOp "zstdNoProgress.comp" {} inspectArgsApi (.compress .zstd "hi".toUTF8) tr
  tr ← runCheckedOsOp "zstdCompOpts" {} inspectArgsApi
    (.compressWith .zstd { level := some 7, threads := some 2, maxOutputBytes := 2048 } "hi".toUTF8) tr
  tr ← runCheckedOsOp "zstdNoProgress.dec" {} inspectArgsApi (.decompress .zstd validZstdEmpty "osNoProgress") tr
  tr ← runCheckedOsOp "xzCompOpts" {} inspectArgsApi
    (.compressWith .xz { level := some 3, threads := some 2, maxOutputBytes := 2048 } "hi".toUTF8) tr
  tr ← runCheckedOsOp "xzDecArgs" {} inspectArgsApi (.decompress .xz (Model.encodeStored .xz ByteArray.empty) "osXzArgs") tr
  tr ← runCheckedOsOp "gzipCompArgs" {} inspectArgsApi (.compress .gzip "hi".toUTF8) tr
  tr ← runCheckedOsOp "gzipCompOpts" {} inspectArgsApi
    (.compressWith .gzip { level := some 9, maxOutputBytes := 2048 } "hi".toUTF8) tr
  tr ← runCheckedOsOp "gzipDecArgs" {} inspectArgsApi (.decompress .gzip (Model.encodeStored .gzip ByteArray.empty) "osGzArgs") tr
  if (← badSanitizedEnv.get) != 0 || (← seenZstdComp.get) != 2 || (← seenZstdCompOpts.get) != 1 ||
     (← seenZstdDec.get) != 1 || (← seenXzCompOpts.get) != 1 || (← seenXzDec.get) != 1 ||
     (← seenGzipArgs.get) != 3 || (← seenGzipCompOpts.get) != 1 then
    throw (IO.userError "OS_SUBPASS_FAIL(inspectArgs): missing required CLI flags, sanitized env, or pipe slack in ExecRequest")

  tr ← runCheckedOsOp "gzipBadLvl10" {} LeanSwe.Compress.defaultApi
    (.compressWith .gzip { level := some 10 } (ByteArray.mk #[0x41])) tr
  tr ← runCheckedOsOp "gzipBadThr0" {} LeanSwe.Compress.defaultApi
    (.compressWith .gzip { threads := some 0 } (ByteArray.mk #[0x41])) tr
  tr ← runCheckedOsOp "xzBadLvl10" {} LeanSwe.Compress.defaultApi
    (.compressWith .xz { level := some 10 } (ByteArray.mk #[0x41])) tr
  tr ← runCheckedOsOp "zstdBadLvl0" {} LeanSwe.Compress.defaultApi
    (.compressWith .zstd { level := some 0 } (ByteArray.mk #[0x41])) tr

  let exit1Dir ← IO.FS.createTempDir
  try
    for prog in #["zstd", "xz", "gzip"] do
      let p := (exit1Dir / prog).toString
      IO.FS.writeFile p "#!/bin/sh\nexit 1\n"
      mkChmod "0755" p
    let exit1Api := mkEnvApi #[("PATH", some exit1Dir.toString)] false
    let envSig : Model.CompressEnv := { allowExternalSignal := true }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"exit1.avail.{codecTag c}" { toolStatus := fun _ => .missingOrNonExec } exit1Api (.isToolAvailable c) tr
      tr ← runCheckedOsOp s!"exit1.comp.{codecTag c}" envSig exit1Api (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"exit1.dec.{codecTag c}" envSig exit1Api (.decompress c "hi".toUTF8 "osExit1") tr
  finally
    IO.FS.removeDirAll exit1Dir

  let sigDir ← IO.FS.createTempDir
  try
    for prog in #["zstd", "xz", "gzip"] do
      let p := (sigDir / prog).toString
      IO.FS.writeFile p "#!/bin/sh\nkill -TERM $$\n"
      mkChmod "0755" p
    let sigApi := mkEnvApi #[("PATH", some sigDir.toString)] false
    let envSig : Model.CompressEnv := { allowExternalSignal := true }
    for c in allCodecs do
      tr ← runCheckedOsOp s!"sigterm.decW.{codecTag c}" envSig sigApi (.decompressWith c {} "hi".toUTF8 "osSigterm") tr
      tr ← runCheckedOsOp s!"sigterm.dec.{codecTag c}" envSig sigApi (.decompress c "hi".toUTF8 "osSigterm") tr
      tr ← runCheckedOsOp s!"sigterm.comp.{codecTag c}" envSig sigApi (.compress c "hi".toUTF8) tr
      tr ← runCheckedOsOp s!"sigterm.compW.{codecTag c}" envSig sigApi (.compressWith c {} "hi".toUTF8) tr
  finally
    IO.FS.removeDirAll sigDir

  let poisonedApi := mkEnvApi #[
    ("XZ_OPT", some "--bad"),
    ("XZ_DEFAULTS", some "--bad"),
    ("ZSTD_CLEVEL", some "19"),
    ("ZSTD_NBTHREADS", some "999"),
    ("GZIP", some "--bad"),
    ("LC_ALL", some "invalid_locale"),
    ("LANG", some "de_AT.utf8"),
    ("LANGUAGE", some "de_AT:de")
  ] true
  let mut stPoison := Model.State.empty
  for c in allCodecs do
    tr ← runCheckedOsOp s!"poisonAvail.{codecTag c}" {} poisonedApi (.isToolAvailable c) tr
    let sample := s!"poisoned-env-check-{codecTag c}\n".toUTF8
    let er1 ← evalOp {} poisonedApi (some oracle) stPoison (.compress c sample) tr
    tr := er1.tracker
    stPoison := er1.state
    if let some msg := er1.err? then
      throw (IO.userError s!"OS_SUBPASS_FAIL(poison.{codecTag c}): {msg}")
    let s := Model.encodeStored c sample
    let er2 ← evalOp {} poisonedApi (some oracle) stPoison (.decompress c s "poison") tr
    tr := er2.tracker
    stPoison := er2.state
    if let some msg := er2.err? then
      throw (IO.userError s!"OS_SUBPASS_FAIL(poisonDec.{codecTag c}): {msg}")
  let detPayload := pushReplicateByte ("zstd-clevel-sanitized-determinism-header\n".toUTF8) 0x42 16384
  match ← LeanSwe.Compress.compress .zstd detPayload, ← poisonedApi.compress .zstd detPayload with
  | .ok cleanBytes, .ok poisonBytes =>
    if cleanBytes != poisonBytes then
      throw (IO.userError "OS_SUBPASS_FAIL(poisonZstdDet): ZSTD_CLEVEL leaked into compressed output")
  | _, _ =>
    throw (IO.userError "OS_SUBPASS_FAIL(poisonZstdDet): unexpected compression error")

  for c in allCodecs do
    tr ← runCheckedOsOp s!"compWLimit.{codecTag c}" {} LeanSwe.Compress.defaultApi
      (.compressWith c { maxOutputBytes := 4 } (ByteArray.mk (Array.replicate 256 0x41))) tr

  return tr

private def runHeavyOsSubPass (tracker : CoverageTracker) : IO CoverageTracker := do
  let mut tr := tracker
  let allCodecs := #[Codec.zstd, Codec.xz, Codec.gzip]
  let envTimeout : Model.CompressEnv := { allowTimeout := true }
  tr ← (do
    let rnd4M ← readUrandom (4 * 1024 * 1024)
    let mut trSub := tr
    trSub ← runCheckedOsOp "timeout.compW.xz" envTimeout LeanSwe.Compress.defaultApi
      (.compressWith .xz { level := some 9, timeoutMs := 1 } rnd4M) trSub
    trSub ← runCheckedOsOp "timeout.compW.zstd" envTimeout LeanSwe.Compress.defaultApi
      (.compressWith .zstd { level := some 19, timeoutMs := 1 } rnd4M) trSub
    trSub ← runCheckedOsOp "timeout.compW.gzip" envTimeout LeanSwe.Compress.defaultApi
      (.compressWith .gzip { level := some 9, timeoutMs := 1 } rnd4M) trSub
    pure trSub)
  tr ← (do
    let rnd12M ← readUrandom (12 * 1024 * 1024)
    let mut trSub := tr
    for c in allCodecs do
      let copts : CompressOptions :=
        { level := some 1
          threads := if c == .xz then some 2 else none
          timeoutMs := 30000 }
      let fastComp ←
        match ← LeanSwe.Compress.compressWith c copts rnd12M with
        | .ok b => pure b
        | .error e => throw (IO.userError s!"OS_SUBPASS_FAIL(prepTimeout.{codecTag c}): {e.message}")
      trSub ← runCheckedOsOp s!"timeout.decW.{codecTag c}" envTimeout LeanSwe.Compress.defaultApi
        (.decompressWith c { timeoutMs := 1 } fastComp "osTimeout") trSub
    pure trSub)
  tr ← (do
    let zerosBomb ← readZeroBytes (64 * 1024 * 1024 + 4096)
    let mut trSub := tr
    for c in allCodecs do
      let copts : CompressOptions :=
        { level := some (if c == .xz then 0 else 1)
          threads := if c == .xz then some 2 else none
          timeoutMs := 30000 }
      let bombComp ←
        match ← LeanSwe.Compress.compressWith c copts zerosBomb with
        | .ok b => pure b
        | .error e => throw (IO.userError s!"OS_SUBPASS_FAIL(prepBomb.{codecTag c}): {e.message}")
      trSub ← runCheckedOsOp s!"decBomb.{codecTag c}" {} LeanSwe.Compress.defaultApi (.decompress c bombComp "defaultBomb") trSub
    pure trSub)
  tr ← (do
    let rnd64M ← readUrandom (64 * 1024 * 1024 + 16384)
    runCheckedOsOp "compLimit.zstd" {} LeanSwe.Compress.defaultApi (.compress .zstd rnd64M) tr)
  let stubDir ← IO.FS.createTempDir
  try
    for prog in #["xz", "gzip"] do
      let p := (stubDir / prog).toString
      IO.FS.writeFile p "#!/bin/sh\nexec /usr/bin/head -c 67113000 /dev/zero\n"
      mkChmod "0755" p
    let stubApi := mkEnvApi #[("PATH", some stubDir.toString)] false
    let zeros64M ← readZeroBytes (64 * 1024 * 1024)
    tr ← runCheckedOsOp "compLimit.xz" {} stubApi (.compress .xz zeros64M) tr
    tr ← runCheckedOsOp "compLimit.gzip" {} stubApi (.compress .gzip zeros64M) tr
  finally
    IO.FS.removeDirAll stubDir

  return tr

private def hexDecode (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  let hv (c : Char) : UInt8 :=
    if '0' <= c && c <= '9' then UInt8.ofNat (c.toNat - '0'.toNat)
    else if 'a' <= c && c <= 'f' then UInt8.ofNat (10 + c.toNat - 'a'.toNat)
    else UInt8.ofNat (10 + c.toNat - 'A'.toNat)
  for i in [0:cs.size / 2] do
    out := out.push ((hv cs[2 * i]! <<< 4) ||| hv cs[2 * i + 1]!)
  return out

private def runRegressionSubPass (oracle : PyOracle) (tracker : CoverageTracker) : IO CoverageTracker := do
  let mut tr := tracker
  let repeatStr (n : Nat) (s : String) : ByteArray :=
    String.ofList (List.flatten (List.replicate n s.toList)) |>.toUTF8
  let mkStride (n : Nat) : ByteArray := Id.run do
    let mut ba := ByteArray.emptyWithCapacity n
    for i in [0:n] do
      ba := ba.push (UInt8.ofNat ((i * 13 + i / 17) % 256))
    return ba
  let jsonRow := "{\"id\":12345,\"name\":\"alice\",\"tags\":[\"a\",\"b\",\"c\"],\"active\":true}\n"
  let cases : List (String × Codec × CompressOptions × ByteArray) := [
    ("xzMatchedLit1", .xz, {}, "aaaaabaaaaac".toUTF8),
    ("xzMatchedLit2", .xz, {}, repeatStr 10 "hello"),
    ("xzMatchedLit3", .xz, {}, "hello_world_1234 hello_world_5678".toUTF8),
    ("zstdJson10L1", .zstd, { level := some 1 }, repeatStr 10 jsonRow),
    ("zstdJson50L19", .zstd, { level := some 19 }, repeatStr 50 jsonRow),
    ("zstdStride4kL1", .zstd, { level := some 1 }, mkStride 4096),
    ("zstdStride2792L3", .zstd, { level := some 3 }, mkStride 2792),
    ("zstdStride2792L19", .zstd, { level := some 19 }, mkStride 2792),
    ("gzipJson10L6", .gzip, { level := some 6 }, repeatStr 10 jsonRow)
  ]
  let mut st := Model.State.empty
  for (label, c, opts, plain) in cases do
    let er1 ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.compressWith c opts plain) tr
    tr := er1.tracker
    st := er1.state
    if let some msg := er1.err? then
      throw (IO.userError s!"REGRESSION_FAIL(comp.{label}): {msg}")
    let comp ←
      match ← LeanSwe.Compress.compressWith c opts plain with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"REGRESSION_FAIL(prep.{label}): {e.message}")
    let er2 ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompress c comp s!"reg.{label}") tr
    tr := er2.tracker
    st := er2.state
    if let some msg := er2.err? then
      throw (IO.userError s!"REGRESSION_FAIL(dec.{label}): {msg}")
  let xzMultiChunk76 := hexDecode
    "fd377a585a0000016922de360200210116000000742fe5a3e0000000055d000000000000020000588000000005000000000000004e0e238d00012c033f8fbe809042990d010000000001595a"
  let er3 ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompress .xz xzMultiChunk76 "reg.xz0x02") tr
  tr := er3.tracker
  st := er3.state
  if let some msg := er3.err? then
    throw (IO.userError s!"REGRESSION_FAIL(xzMultiChunk76): {msg}")
  let zstdWd89 := hexDecode "28b52ffd808905000000290000" ++ "hello".toUTF8
  let zstdBt2Zero1 := hexDecode "28b52ffd0038050000"
  let zstdBt2Zero2 := hexDecode "28b52ffd0038040000010000"
  for (lbl, bs) in #[("wd89Fcs5", zstdWd89), ("bt2ZeroLast", zstdBt2Zero1), ("bt2ZeroMid", zstdBt2Zero2)] do
    let erk ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompress .zstd bs s!"reg.{lbl}") tr
    tr := erk.tracker
    st := erk.state
    if let some msg := erk.err? then
      throw (IO.userError s!"REGRESSION_FAIL({lbl}): {msg}")
  let zstdBigBlock := hexDecode "28b52ffd8089ff010000" ++
    ByteArray.mk #[0x03, 0x00, 0x10, 0x41] ++
    hexDecode "502a4d1800000200" ++ ByteArray.mk (Array.replicate 131072 0xBB)
  let zstdPadFcs :=
    (hexDecode "502a4d1808000200" ++ ByteArray.mk (Array.replicate 131080 0xBB)) ++
    hexDecode "28b52ffd808905000000290000" ++ "hello".toUTF8
  let zstdBt2Skip :=
    (hexDecode "502a4d1808000200" ++ ByteArray.mk (Array.replicate 131080 0xBB)) ++ zstdBt2Zero2
  for (lbl, bs) in #[("zstdBigBlock", zstdBigBlock), ("zstdPadFcs", zstdPadFcs), ("zstdBt2Skip", zstdBt2Skip)] do
    let erk ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompress .zstd bs s!"reg.{lbl}") tr
    tr := erk.tracker
    st := erk.state
    if let some msg := erk.err? then
      throw (IO.userError s!"REGRESSION_FAIL({lbl}): {msg}")
  let gzBombRaw ←
    match ← LeanSwe.Compress.compress .gzip (ByteArray.mk (Array.replicate 65536 0)) with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"REGRESSION_FAIL(prep.gzBomb): {e.message}")
  let gzBombFextra := gzBombRaw.extract 0 3 ++ ByteArray.mk #[0x04] ++ gzBombRaw.extract 4 10 ++
    ByteArray.mk #[0x02, 0x00, 0x1F, 0x9D] ++ gzBombRaw.extract 10 gzBombRaw.size
  let erGz ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st
    (.decompressWith .gzip { maxOutputBytes := 1024 } gzBombFextra "reg.gzipFextraBomb") tr
  tr := erGz.tracker
  st := erGz.state
  if let some msg := erGz.err? then
    throw (IO.userError s!"REGRESSION_FAIL(gzipFextraBomb): {msg}")
  let xzBomb ←
    match ← LeanSwe.Compress.compress .xz (ByteArray.mk (Array.replicate 65536 0)) with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"REGRESSION_FAIL(prep.xzBomb): {e.message}")
  for lim in #[1, 17, 255, 256, 257, 1024] do
    let erXz ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st
      (.decompressWith .xz { maxOutputBytes := lim } xzBomb s!"reg.xzLim{lim}") tr
    tr := erXz.tracker
    st := erXz.state
    if let some msg := erXz.err? then
      throw (IO.userError s!"REGRESSION_FAIL(xzLim{lim}): {msg}")
  let zstdRleBomb := Id.run do
    let mut out := hexDecode "28b52ffd803805000000"
    let rleHdr := ByteArray.mk #[0x02, 0x00, 0x10, 0x41]
    out := out ++ rleHdr ++ rleHdr ++ hexDecode "03001041"
    return out
  let gzInZstd := Model.encodeStored .gzip (ByteArray.mk (Array.replicate 256 0x41))
  let pkZip := ByteArray.mk #[0x50, 0x4B, 0x03, 0x04] ++ ByteArray.mk (Array.replicate 256 0x41)
  let gzSym16Idx0 := hexDecode "1f8b080000000000000305c0050900000000a0f83f5a010000000000000000"
  let gzNoEob := hexDecode "1f8b080000000000000305c0010500000000a06dfd5f150000000000000000000000000000000000000000"
  let xzComp88 := hexDecode
    "fd377a585a000004e6d6b4460200210110000000a8708e86e0063f00175d00309888983bf8bbf1558a0da7d659192c7e81d5111714000000b5a6264c08ebf535000133c00c000000bdf678e2b1c467fb020000000004595a"
  let zstdRing4x1000 := Id.run do
    let mut out := hexDecode "28b52ffd0010"
    for b in #[0x41, 0x42, 0x43, 0x44] do
      out := out ++ ByteArray.mk #[0x42, 0x1f, 0x00, UInt8.ofNat b]
    let seq := hexDecode "000154000b00af0d"
    let bh := (seq.size <<< 3) ||| (2 <<< 1) ||| 1
    out ++ ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF), UInt8.ofNat ((bh >>> 16) &&& 0xFF)] ++ seq
  let zstdRingMulti := Id.run do
    let mut out := hexDecode "28b52ffd0050" ++ ByteArray.mk #[0x43, 0x1f, 0x00, 0x5A] ++ hexDecode "28b52ffd0010"
    for b in #[0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48] do
      out := out ++ ByteArray.mk #[0xe2, 0x15, 0x00, UInt8.ofNat b]
    let seq := hexDecode "000154000b00bb0b"
    let bh := (seq.size <<< 3) ||| (2 <<< 1) ||| 1
    out ++ ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF), UInt8.ofNat ((bh >>> 16) &&& 0xFF)] ++ seq
  for (lbl, c, lim, bs) in #[
      ("zstdRleBomb", Codec.zstd, 100, zstdRleBomb),
      ("gzInZstd", Codec.zstd, 100, gzInZstd),
      ("pkZipInGz", Codec.gzip, 100, pkZip),
      ("gzNoEob", Codec.gzip, 100, gzNoEob),
      ("xzComp88_100", Codec.xz, 100, xzComp88),
      ("xzComp88_1024", Codec.xz, 1024, xzComp88)] do
    let erk ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompressWith c { maxOutputBytes := lim } bs s!"reg.{lbl}") tr
    tr := erk.tracker
    st := erk.state
    if let some msg := erk.err? then
      throw (IO.userError s!"REGRESSION_FAIL({lbl}): {msg}")
  let gzSym16Lzw := gzSym16Idx0 ++ hexDecode "1f9d9000000000000000"
  let skip131050 := hexDecode "502a4d18eaff0100" ++ ByteArray.mk (Array.replicate 131050 0x00)
  let skip131072 := hexDecode "502a4d1800000200" ++ ByteArray.mk (Array.replicate 131072 0x00)
  let zstdCoalLt18 :=
    skip131050 ++ hexDecode "28b52ffd60001400600000" ++ "hello_world!".toUTF8 ++ hexDecode "010000"
  let zstdCoalAf :=
    skip131050 ++ hexDecode "28b52ffd00af280000" ++ "hello".toUTF8
  let zstdSmallFcs := skip131072 ++ hexDecode "28b52ffd6000a40e" ++
    zstdRing4x1000.extract 6 zstdRing4x1000.size
  let zstdSingleSegZero := skip131072 ++ hexDecode "28b52ffd200002000041"
  let zstdEmptyLastOver := hexDecode "28b52ffd6000d006421f0041e22e0041010000"
  let xzCut47 := hexDecode
    "fd377a585a000000ff12d9410200210100000000372797d6e035b6002e5d0028efcdbf297d3e271d47222ec500d93e8bad4e2e27c47eb1497634c526f3ffd40dd35e06f55634c90d2d9f4e183e000000000142b76b000000bcdb05cfa8000afc020000000000595a"
  for (lbl, c, lim, bs) in #[
      ("xzCut47_12500", Codec.xz, 12500, xzCut47),
      ("xzCut47_12288", Codec.xz, 12288, xzCut47)] do
    let erk ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompressWith c { maxOutputBytes := lim } bs s!"reg.{lbl}") tr
    tr := erk.tracker
    st := erk.state
    if let some msg := erk.err? then
      throw (IO.userError s!"REGRESSION_FAIL({lbl}): {msg}")
  let mkZstdRawSplitReg (curInTarget : Nat) : ByteArray := Id.run do
    let pushBlk (f : ByteArray) (btype sz last : Nat) (body : ByteArray) : ByteArray :=
      let bh := (sz <<< 3) ||| (btype <<< 1) ||| last
      (((f.push (UInt8.ofNat (bh &&& 0xFF))).push
        (UInt8.ofNat ((bh >>> 8) &&& 0xFF))).push
        (UInt8.ofNat ((bh >>> 16) &&& 0xFF))) ++ body
    let warmupOut := 524288 + 131073 - 262208
    let mut f := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x48]
    f := pushBlk f 1 131072 0 (ByteArray.mk #[0x58])
    f := pushBlk f 1 131072 0 (ByteArray.mk #[0x58])
    f := pushBlk f 1 (warmupOut - 262144) 0 (ByteArray.mk #[0x58])
    f := pushBlk f 1 131072 0 (ByteArray.mk #[0x41])
    let rawLen := curInTarget - (f.size + 4 + 3)
    let rleB := 262208 - 131072 - rawLen
    f := pushBlk f 1 rleB 0 (ByteArray.mk #[0x42])
    f := pushBlk f 0 rawLen 0 (ByteArray.mk (Array.replicate rawLen 0x42))
    f := pushBlk f 0 100000 0 (ByteArray.mk (Array.replicate 100000 0x5A))
    let blk := ByteArray.mk #[0x00, 0x01, 0x54, 0x00, 18, 0x01, 0xE3, 0x93, 0x04]
    pushBlk f 2 blk.size 1 blk
  let mkStoredPkzipReg (payload : ByteArray) : ByteArray := Id.run do
    let crc := crc32 payload 0 payload.size
    let sz := UInt32.ofNat payload.size
    let fname := "a".toUTF8
    let mut z := ByteArray.mk #[0x50, 0x4B, 0x03, 0x04]
    z := pushU16LE z 10; z := pushU16LE z 0; z := pushU16LE z 0
    z := pushU16LE z 0; z := pushU16LE z 0
    z := pushU32LE z crc; z := pushU32LE z sz; z := pushU32LE z sz
    z := pushU16LE z (UInt16.ofNat fname.size); z := pushU16LE z 0
    z := z ++ fname ++ payload
    let cdOff := z.size
    let mut cd := ByteArray.mk #[0x50, 0x4B, 0x01, 0x02]
    cd := pushU16LE cd 20; cd := pushU16LE cd 10; cd := pushU16LE cd 0; cd := pushU16LE cd 0
    cd := pushU16LE cd 0; cd := pushU16LE cd 0
    cd := pushU32LE cd crc; cd := pushU32LE cd sz; cd := pushU32LE cd sz
    cd := pushU16LE cd (UInt16.ofNat fname.size); cd := pushU16LE cd 0; cd := pushU16LE cd 0
    cd := pushU16LE cd 0; cd := pushU16LE cd 0; cd := pushU32LE cd (UInt32.ofNat cdOff); cd := pushU32LE cd 0
    cd := cd ++ fname
    let mut eocd := ByteArray.mk #[0x50, 0x4B, 0x05, 0x06, 0, 0, 0, 0]
    eocd := pushU16LE eocd 1; eocd := pushU16LE eocd 1
    eocd := pushU32LE eocd (UInt32.ofNat cd.size)
    eocd := pushU32LE eocd (UInt32.ofNat cdOff)
    eocd := pushU16LE eocd 0
    z ++ cd ++ eocd
  let mkGzipPkzipAt262144 (plainAt262144 : ByteArray) (nulPad : Nat) : ByteArray := Id.run do
    let mut hdr := ByteArray.mk #[0x1F, 0x8B, 0x08, 0x0C, 0, 0, 0, 0, 0, 0x03]
    hdr := pushU16LE hdr 65535
    hdr := pushReplicateByte hdr 0x41 65535
    hdr := pushReplicateByte hdr 0x42 196591
    hdr := hdr.push 0x00
    let len16 := UInt16.ofNat plainAt262144.size
    let nlen16 := len16 ^^^ 0xFFFF
    let mut m1 := hdr.push 0x01
    m1 := pushU16LE (pushU16LE m1 len16) nlen16
    m1 := m1 ++ plainAt262144
    m1 := pushU32LE m1 (crc32 plainAt262144 0 plainAt262144.size)
    m1 := pushU32LE m1 (UInt32.ofNat plainAt262144.size)
    pushReplicateByte m1 0x00 nulPad
  let pkFourBody := pushReplicateByte (ByteArray.mk #[0x50, 0x4B, 0x03, 0x04]) 0x43 44
  let gzPkzipReplay2Nul := mkGzipPkzipAt262144 (mkStoredPkzipReg "ZIP_REPLAY_CHECK".toUTF8) 2
  let gzPkzipFour2Nul := mkGzipPkzipAt262144 pkFourBody 2
  let gzPkzipFour1Nul := mkGzipPkzipAt262144 pkFourBody 1
  let xzDictProp29 := Id.run do
    let shdrBody := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]
    let shdr := pushU32LE shdrBody (crc32 shdrBody 6 8)
    let bhdrBody := ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 29, 0x00, 0x00, 0x00]
    let bhdr := pushU32LE bhdrBody (crc32 bhdrBody 0 8)
    let l2Padded := ByteArray.mk #[0x00, 0x00, 0x00, 0x00]
    let chk := pushU64LE ByteArray.empty (crc64Xz ByteArray.empty 0 0)
    let unpadded := bhdr.size + 1 + chk.size
    let buf1 := (ByteArray.empty.push 0x00) ++ Model.encodeXzVli 1 ++
      Model.encodeXzVli unpadded ++ Model.encodeXzVli 0
    let ipad := (4 - buf1.size % 4) % 4
    let buf2 := pushReplicateByte buf1 0x00 ipad
    let idxRaw := pushU32LE buf2 (crc32 buf2 0 buf2.size)
    let bwdSz := UInt32.ofNat (idxRaw.size / 4 - 1)
    let ftrBody := pushU32LE ByteArray.empty bwdSz ++ ByteArray.mk #[0x00, 0x04]
    let ftr := pushU32LE ByteArray.empty (crc32 ftrBody 0 6) ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A]
    return shdr ++ bhdr ++ l2Padded ++ chk ++ idxRaw ++ ftr
  let zstdDid2Zero := hexDecode "28b52ffd2200000109000041"
  let zstdDid2Nz := hexDecode "28b52ffd2200010109000041"
  let zstdDid4Nz := hexDecode "28b52ffd23000000010109000041"
  let zstdFcs8Ok := mkZstdFrameFcs8 ("hello".toUTF8) 5
  let zstdFcs8Unk := mkZstdFrameFcs8 ("hello".toUTF8) 0xFFFFFFFFFFFFFFFF
  let zstdFcs8Bad := mkZstdFrameFcs8 ("hello".toUTF8) 99
  let xzBhSizesOk := mkXzStreamWithBlockSizes 0x04 ("test".toUTF8) (some 8) (some 4)
  let xzBhUncompBad := mkXzStreamWithBlockSizes 0x04 ("test".toUTF8) none (some 5)
  let xzBhCompBad := mkXzStreamWithBlockSizes 0x04 ("test".toUTF8) (some 12) none
  let xzSha256Ok := mkXzStreamWithBlockSizes 0x0A ("sha256-payload".toUTF8) (some 18) (some 14)
  let xzSha256Bad := xzSha256Ok.set! (xzSha256Ok.size - 24) (xzSha256Ok.get! (xzSha256Ok.size - 24) ^^^ 0x01)
  let xzTwoBlkCrc32Ok := mkXzTwoBlockStream 0x01 ("block1".toUTF8) ("block2".toUTF8)
  let xzTwoBlkCrc32Bad := xzTwoBlkCrc32Ok.set! (xzTwoBlkCrc32Ok.size - 24) (xzTwoBlkCrc32Ok.get! (xzTwoBlkCrc32Ok.size - 24) ^^^ 0x01)
  let xzTwoBlkSha256Ok := mkXzTwoBlockStream 0x0A ("alpha".toUTF8) ("omega".toUTF8)
  for (lbl, c, bs) in #[
      ("gzSym16Idx0", Codec.gzip, gzSym16Idx0),
      ("gzSym16Lzw", Codec.gzip, gzSym16Lzw),
      ("gzPkzipReplay2Nul", Codec.gzip, gzPkzipReplay2Nul),
      ("gzPkzipFour2Nul", Codec.gzip, gzPkzipFour2Nul),
      ("gzPkzipFour1Nul", Codec.gzip, gzPkzipFour1Nul),
      ("xzDictProp29", Codec.xz, xzDictProp29),
      ("xzBhSizesOk", Codec.xz, xzBhSizesOk),
      ("xzBhUncompBad", Codec.xz, xzBhUncompBad),
      ("xzBhCompBad", Codec.xz, xzBhCompBad),
      ("xzSha256Ok", Codec.xz, xzSha256Ok),
      ("xzSha256Bad", Codec.xz, xzSha256Bad),
      ("xzTwoBlkCrc32Ok", Codec.xz, xzTwoBlkCrc32Ok),
      ("xzTwoBlkCrc32Bad", Codec.xz, xzTwoBlkCrc32Bad),
      ("xzTwoBlkSha256Ok", Codec.xz, xzTwoBlkSha256Ok),
      ("zstdDid2Zero", Codec.zstd, zstdDid2Zero),
      ("zstdDid2Nz", Codec.zstd, zstdDid2Nz),
      ("zstdDid4Nz", Codec.zstd, zstdDid4Nz),
      ("zstdFcs8Ok", Codec.zstd, zstdFcs8Ok),
      ("zstdFcs8Unk", Codec.zstd, zstdFcs8Unk),
      ("zstdFcs8Bad", Codec.zstd, zstdFcs8Bad),
      ("zstdCoalLt18", Codec.zstd, zstdCoalLt18),
      ("zstdCoalAf", Codec.zstd, zstdCoalAf),
      ("zstdSmallFcs", Codec.zstd, zstdSmallFcs),
      ("zstdSingleSegZero", Codec.zstd, zstdSingleSegZero),
      ("zstdEmptyLastOver", Codec.zstd, zstdEmptyLastOver),
      ("zstdRing4x1000", Codec.zstd, zstdRing4x1000),
      ("zstdRingMulti", Codec.zstd, zstdRingMulti),
      ("zstdRawSplit131070", Codec.zstd, mkZstdRawSplitReg 131070),
      ("zstdRawSplit131071", Codec.zstd, mkZstdRawSplitReg 131071)] do
    let erk ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st (.decompress c bs s!"reg.{lbl}") tr
    tr := erk.tracker
    st := erk.state
    if let some msg := erk.err? then
      throw (IO.userError s!"REGRESSION_FAIL({lbl}): {msg}")
  let exactPlain := "exact-max-output-boundary-regression-payload-xyz".toUTF8
  for c in #[Codec.zstd, Codec.xz, Codec.gzip] do
    let compExact ←
      match ← LeanSwe.Compress.compress c exactPlain with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"REGRESSION_FAIL(prepExact.{codecTag c}): {e.message}")
    for cop in #[
        CompressFuzzOp.compressWith c { maxOutputBytes := compExact.size } exactPlain,
        CompressFuzzOp.compressWith c { maxOutputBytes := compExact.size - 1 } exactPlain,
        CompressFuzzOp.decompressWith c { maxOutputBytes := exactPlain.size } compExact "reg.exactLim",
        CompressFuzzOp.decompressWith c { maxOutputBytes := exactPlain.size - 1 } compExact "reg.exactLimMinus1",
        CompressFuzzOp.decompress c compExact "reg.exactReplay"] do
      let erE ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st cop tr
      tr := erE.tracker
      st := erE.state
      if let some msg := erE.err? then
        throw (IO.userError s!"REGRESSION_FAIL(exactLim.{codecTag c}): {msg}")
  return tr

private def stripBalancedDelim (s key : String) (openCh closeCh : Char) (repl : String := "") : String := Id.run do
  let parts := s.splitOn key
  if parts.length <= 1 then
    return s
  let mut out := parts.headD ""
  for tail in parts.drop 1 do
    let cs := tail.toList
    let mut depth : Nat := 0
    let mut started := false
    let mut skipped : List Char := []
    let mut rest : List Char := cs
    let mut done := false
    while !done do
      match rest with
      | [] => done := true
      | c :: cs' =>
        if !started then
          if c == openCh then
            started := true
            depth := 1
            rest := cs'
          else if c == ' ' then
            out := out ++ key ++ String.ofList (skipped.reverse ++ cs)
            done := true
          else
            skipped := c :: skipped
            rest := cs'
        else
          rest := cs'
          if c == openCh then depth := depth + 1
          else if c == closeCh then
            depth := depth - 1
            if depth == 0 then
              out := out ++ repl ++ String.ofList rest
              done := true
    if !started && skipped.length == cs.length then
      out := out ++ key ++ tail
    else if started && depth > 0 then
      out := out ++ repl
  return out

private def stripTailPrefix (s pfx : String) : String :=
  let parts := s.splitOn pfx
  if parts.length > 1 then parts.headD s else s

private def stripMetricSuffixes (s : String) : String := Id.run do
  let s0 := stripTailPrefix (stripTailPrefix s " msg=") " error="
  let s1 := stripBalancedDelim s0 " opts=" '{' '}' ""
  let s2 := stripBalancedDelim s1 " py=PyOracleOutcome.ok " '(' ')' " py=ok"
  let toks := (s2.splitOn " ").filter (· != "")
  let mut kept : List String := []
  for tok in toks do
    if tok.startsWith "inSize=" || tok.startsWith "outSize=" || tok.startsWith "compSize=" ||
       tok.startsWith "implSize=" || tok.startsWith "pySize=" then
      pure ()
    else if tok.startsWith "impl=ok(" then
      kept := kept ++ ["impl=ok"]
    else if tok.startsWith "impl=outputLimitExceeded(" then
      kept := kept ++ ["impl=outputLimitExceeded"]
    else if tok.startsWith "python=ok(" then
      kept := kept ++ ["python=ok"]
    else
      kept := kept ++ [tok]
  return String.intercalate " " kept

private def normDecodeSide (lhs : String) : String :=
  stripMetricSuffixes lhs

private def compressErrorClass (msg : String) : String :=
  let clean := stripTailPrefix (stripTailPrefix msg " msg=") " error="
  let parts := clean.splitOn " vs "
  if parts.length > 1 then
    let lhsNorm := normDecodeSide (parts.headD clean)
    let rhsNorm := stripMetricSuffixes (String.intercalate " vs " (parts.drop 1))
    if rhsNorm.isEmpty then lhsNorm else s!"{lhsNorm} vs {rhsNorm}"
  else
    stripMetricSuffixes clean

private def traceFails (oracle : PyOracle) (wantClass : String) (trace : Array CompressFuzzOp) : IO Bool := do
  let mut st := Model.State.empty
  for op in trace do
    let er ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st op CoverageTracker.empty
    st := er.state
    if let some msg := er.err? then
      if compressErrorClass msg == wantClass then
        return true
  return false

private def shrinkAndFail (oracle : PyOracle) (trace : Array CompressFuzzOp) (errMsg : String) :
    IO Unit := do
  let wantClass := compressErrorClass errMsg
  let minTrace ← shrinkTrace (traceFails oracle wantClass) trace
  let shrunk ← shrinkElements shrinkOp (traceFails oracle wantClass) minTrace
  let mut shrunkErr := errMsg
  let mut st := Model.State.empty
  for op in shrunk do
    let er ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st op CoverageTracker.empty
    st := er.state
    if let some msg := er.err? then
      if compressErrorClass msg == wantClass then
        shrunkErr := msg
  throw (IO.userError
    s!"COMPRESS_FUZZ_MISMATCH: {errMsg}\n  class={wantClass}\n  original_trace_len={trace.size} shrunk_trace_len={shrunk.size}\n  shrunk_err={shrunkErr}\n  shrunk={repr shrunk}")

private def safeSuitePrintln (s : String) : IO Unit := do
  try
    IO.println s
    (← IO.getStdout).flush
  catch _ => pure ()

private def genStatefulPoolOp (pool : Array (Codec × ByteArray × ByteArray)) (r : Rng) :
    CompressFuzzOp × Rng :=
  let (idx, r1) := r.nextNat pool.size
  let (codec, comp, plain) := pool[idx]!
  let (mode, r2) := r1.nextNat 3
  if mode == 0 then
    (.decompress codec comp "poolReplay", r2)
  else if mode == 1 then
    (.decompressWith codec { maxOutputBytes := plain.size } comp "poolExactLimit", r2)
  else if plain.size > 0 then
    (.decompressWith codec { maxOutputBytes := plain.size - 1 } comp "poolTightLimit", r2)
  else
    (.decompress codec comp "poolReplay", r2)

private def mkXzFilterVectors (oracle : PyOracle) : IO (Array (String × ByteArray)) := do
  let sample :=
    "LeanSwe.Compress multi-filter BCJ+Delta+96MiB dict fuzz payload!\x00\xE8\x00\x00\x00\x00\xC3".toUTF8
  let samplePad := sample ++ ByteArray.mk (Array.replicate 256 0x41)
  let specs : Array (String × Array String) := #[
    ("xzX86Bcj", #["--x86", "--lzma2=dict=64KiB", "-c"]),
    ("xzDelta4", #["--delta=dist=4", "--lzma2=dict=64KiB", "-c"]),
    ("xzX86Delta", #["--x86", "--delta=dist=2", "--lzma2=dict=64KiB", "-c"]),
    ("xzDict96MiB", #["--lzma2=dict=96MiB", "-c"])
  ]
  let mut out : Array (String × ByteArray) := #[]
  for (lbl, args) in specs do
    match ← LeanSwe.Process.run { program := "xz", args := args, stdin := samplePad, timeoutMs := some 10000 } with
    | .ok res =>
      if res.exitCode == 0 && !res.stdout.isEmpty then
        out := out.push (lbl, res.stdout)
    | .error _ => pure ()
  let pyBcj ← oracle.compressXzBcj samplePad
  out := out.push ("pyXzX86Bcj", pyBcj)
  return out

private def runSeededFuzz (cfg : FuzzConfig) (steps : Nat) (smokeMode : Bool) : IO Unit := do
  let oracle ← PyOracle.spawn
  let (osRep, randRep) ←
    try
      let mut rng := Rng.seed cfg.seed
      let mut osTracker := CoverageTracker.empty
      let mut randTracker := CoverageTracker.empty
      osTracker ← runOsSubPass oracle osTracker
      osTracker ← runHeavyOsSubPass osTracker
      osTracker ← runRegressionSubPass oracle osTracker
      assertCoverage "compress-os" osTracker osRequiredBuckets
      let xzVecs ← mkXzFilterVectors oracle
      let mut st := Model.State.empty
      let mut pool : Array (Codec × ByteArray × ByteArray) := #[]
      let mut epochTrace : Array CompressFuzzOp := #[]
      for step in [0:steps] do
        if !smokeMode && step > 0 && step % 10000 == 0 then
          osTracker ← runOsSubPass oracle osTracker
        if step > 0 && step % 32 == 0 then
          st := Model.State.empty
          pool := #[]
          epochTrace := #[]
        let (usePool, rPool) := rng.nextNat 5
        let (useXzVec, rXz) := rPool.nextNat 40
        let (op, rng') ←
          if usePool == 0 && !pool.isEmpty then
            pure (genStatefulPoolOp pool rXz)
          else if useXzVec == 0 && !xzVecs.isEmpty then
            let (idx, r1) := rXz.nextNat xzVecs.size
            let (lbl, vec) := xzVecs[idx]!
            pure (.decompress .xz vec lbl, r1)
          else
            genNextOp oracle rXz
        rng := rng'
        epochTrace := epochTrace.push op
        let er ← evalOp {} LeanSwe.Compress.defaultApi (some oracle) st op randTracker
        st := er.state
        randTracker := er.tracker
        if let some prod := er.produced? then
          if pool.size < 32 then
            pool := pool.push prod
        if let some errMsg := er.err? then
          shrinkAndFail oracle epochTrace errMsg
      assertCoverage "compress" randTracker randRequiredBuckets
      pure (osTracker.formatReport "compress-os", randTracker.formatReport "compress")
    finally
      oracle.close
  safeSuitePrintln osRep
  safeSuitePrintln randRep

private def hasSubseq (hay needle : ByteArray) : Bool := Id.run do
  if needle.isEmpty then
    return true
  if needle.size > hay.size then
    return false
  for i in [0 : hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0 : needle.size] do
      if hay.get! (i + j) != needle.get! j then
        ok := false
        break
    if ok then
      return true
  return false

private def runCompressShrinkSelfTest (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let marker := ByteArray.mk #[0xDE, 0xAD, 0xC0, 0xDE]
  let mut payload := ByteArray.mk (Array.replicate 256 0x41)
  for j in [0:4] do
    payload := payload.set! (100 + j) (marker.get! j)
  let mut ops : Array CompressFuzzOp := #[]
  for i in [0:16] do
    if i == 9 then
      ops := ops.push (.decompress .gzip payload "planted")
    else
      ops := ops.push (.compress .zstd (ByteArray.mk #[UInt8.ofNat i]))
  let syntheticBuggyFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .gzip inp _ => hasSubseq inp marker
      | _ => false
  let minTrace ← shrinkTrace syntheticBuggyFails ops
  let shrunk ← shrinkElements shrinkOp syntheticBuggyFails minTrace
  if shrunk.size != 1 then
    throw (IO.userError s!"COMPRESS_SHRINK_SELFTEST_FAIL: expected trace size 1, got {shrunk.size}")
  match shrunk.toList with
  | .decompress .gzip p _ :: _ =>
    if p != marker then
      throw (IO.userError s!"COMPRESS_SHRINK_SELFTEST_FAIL: expected 4-byte marker, got size={p.size}")
  | other :: _ =>
    throw (IO.userError s!"COMPRESS_SHRINK_SELFTEST_FAIL: unexpected op {repr other}")
  | [] =>
    throw (IO.userError "COMPRESS_SHRINK_SELFTEST_FAIL: empty shrunk trace")
  safeSuitePrintln s!"COMPRESS_SHRINK_SELFTEST_OK: original={ops.size} shrunk={shrunk.size} payload_size=4"
  let big4k := ByteArray.mk (Array.replicate 4096 0x41)
  let evals ← IO.mkRef 0
  let sizeFails : Array CompressFuzzOp → IO Bool := fun tr => do
    evals.modify (· + 1)
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size >= 3100
      | _ => false
  let min4k ← shrinkElements shrinkOp sizeFails #[.decompress .zstd big4k "big4k"]
  let evalCnt ← evals.get
  match min4k.toList with
  | .decompress .zstd p _ :: _ =>
    if p.size != 3100 || evalCnt > 200 then
      throw (IO.userError s!"COMPRESS_SHRINK_4K_FAIL: size={p.size} evals={evalCnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_4K_FAIL: bad op")
  let evals2049 ← IO.mkRef 0
  let size2049Fails : Array CompressFuzzOp → IO Bool := fun tr => do
    evals2049.modify (· + 1)
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size >= 2049
      | _ => false
  let min2049 ← shrinkElements shrinkOp size2049Fails #[.decompress .zstd big4k "big4k2049"]
  let eval2049Cnt ← evals2049.get
  match min2049.toList with
  | .decompress .zstd p _ :: _ =>
    if p.size != 2049 || eval2049Cnt > 200 then
      throw (IO.userError s!"COMPRESS_SHRINK_4K_2049_FAIL: size={p.size} evals={eval2049Cnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_4K_2049_FAIL: bad op")
  let buf32 := ByteArray.mk (Array.replicate 32 0x77)
  let nz32Fails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size == 32 && inp.get! 17 != 0
      | _ => false
  let min32 ← shrinkElements shrinkOp nz32Fails #[.decompress .zstd buf32 "nz32"]
  match min32.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 32 || p.get! 17 == 0 || nzCnt > 1 then
      throw (IO.userError s!"COMPRESS_SHRINK_MIN32_FAIL: size={p.size} nzCnt={nzCnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_MIN32_FAIL: bad op")
  let evals128 ← IO.mkRef 0
  let buf128 := ByteArray.mk (Array.replicate 128 0x77)
  let nz128Fails : Array CompressFuzzOp → IO Bool := fun tr => do
    evals128.modify (· + 1)
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size == 128 && inp.get! 127 != 0
      | _ => false
  let min128 ← shrinkElements shrinkOp nz128Fails #[.decompress .zstd buf128 "nz128"]
  let eval128Cnt ← evals128.get
  match min128.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 128 || p.get! 127 == 0 || nzCnt > 1 || eval128Cnt > 100 then
      throw (IO.userError s!"COMPRESS_SHRINK_MIN128_FAIL: size={p.size} nzCnt={nzCnt} evals={eval128Cnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_MIN128_FAIL: bad op")
  let evals129 ← IO.mkRef 0
  let buf129 := ByteArray.mk (Array.replicate 129 0x77)
  let nz129Fails : Array CompressFuzzOp → IO Bool := fun tr => do
    evals129.modify (· + 1)
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size == 129 && inp.get! 65 != 0
      | _ => false
  let min129 ← shrinkElements shrinkOp nz129Fails #[.decompress .zstd buf129 "nz129"]
  let eval129Cnt ← evals129.get
  match min129.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 129 || p.get! 65 == 0 || nzCnt > 1 || eval129Cnt > 100 then
      throw (IO.userError s!"COMPRESS_SHRINK_MIN129_FAIL: size={p.size} nzCnt={nzCnt} evals={eval129Cnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_MIN129_FAIL: bad op")
  let evals128Ends ← IO.mkRef 0
  let nz128EndsFails : Array CompressFuzzOp → IO Bool := fun tr => do
    evals128Ends.modify (· + 1)
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size == 128 && inp.get! 0 != 0 && inp.get! 127 != 0
      | _ => false
  let min128Ends ← shrinkElements shrinkOp nz128EndsFails #[.decompress .zstd buf128 "nz128Ends"]
  let eval128EndsCnt ← evals128Ends.get
  match min128Ends.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 128 || p.get! 0 == 0 || p.get! 127 == 0 || nzCnt > 2 || eval128EndsCnt > 200 then
      throw (IO.userError s!"COMPRESS_SHRINK_MIN128_ENDS_FAIL: size={p.size} nzCnt={nzCnt} evals={eval128EndsCnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_MIN128_ENDS_FAIL: bad op")
  let buf1024 := ByteArray.mk (Array.replicate 1024 0x77)
  let nz1024EndsFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ => inp.size == 1024 && inp.get! 17 != 0 && inp.get! 999 != 0
      | _ => false
  let min1024Ends ← shrinkElements shrinkOp nz1024EndsFails #[.decompress .zstd buf1024 "nz1024Ends"]
  match min1024Ends.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 1024 || p.get! 17 == 0 || p.get! 999 == 0 || nzCnt != 2 then
      throw (IO.userError s!"COMPRESS_SHRINK_MIN1024_ENDS_FAIL: size={p.size} nzCnt={nzCnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_MIN1024_ENDS_FAIL: bad op")
  let mut buf2048 := ByteArray.mk (Array.replicate 2048 0x77)
  for j in [0:4] do
    buf2048 := buf2048.set! j (UInt8.ofNat (0xA1 + j))
    buf2048 := buf2048.set! (2044 + j) (UInt8.ofNat (0xB1 + j))
  let twoEnd2048Fails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ =>
        inp.size >= 8 &&
        inp.get! 0 == 0xA1 && inp.get! 1 == 0xA2 && inp.get! 2 == 0xA3 && inp.get! 3 == 0xA4 &&
        inp.get! (inp.size - 4) == 0xB1 && inp.get! (inp.size - 3) == 0xB2 &&
        inp.get! (inp.size - 2) == 0xB3 && inp.get! (inp.size - 1) == 0xB4
      | _ => false
  let min2048TwoEnd ← shrinkElements shrinkOp twoEnd2048Fails #[.decompress .zstd buf2048 "twoEnd2048"]
  match min2048TwoEnd.toList with
  | .decompress .zstd p _ :: _ =>
    if p.size != 8 then
      throw (IO.userError s!"COMPRESS_SHRINK_TWOEND2048_FAIL: expected size 8, got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_TWOEND2048_FAIL: bad op")
  let cOk := compressErrorClass "decompress(tag=surgical): impl=ok(50) vs python=corrupt codec=xz inSize=4096"
  let cOk2 := compressErrorClass "decompress(tag=surgical): impl=ok(12) vs python=corrupt codec=xz inSize=99"
  let cSlip1 := compressErrorClass "decompress(tag=surgical): impl=outputLimitExceeded(8) vs python=ok(12) codec=xz inSize=4096"
  let cSlip2 := compressErrorClass "decompress(tag=surgical): impl=outputLimitExceeded(4) vs python=ok(0) codec=xz inSize=0"
  let cOpt1 := compressErrorClass (s!"compressWith model reject ok codec=zstd compSize=50 opts={repr ({ level := some 3, maxInputBytes := some 5000 } : CompressOptions)}")
  let cOpt2 := compressErrorClass (s!"compressWith model reject ok codec=zstd compSize=12 opts={repr ({ level := some 1, maxInputBytes := some 100 } : CompressOptions)}")
  let cPy1 := compressErrorClass s!"compress->pyDecompress mismatch codec=zstd compSize=50 py={repr (PyOracleOutcome.ok (ByteArray.mk #[1, 2, 3]))}"
  let cPy2 := compressErrorClass s!"compress->pyDecompress mismatch codec=zstd compSize=10 py={repr (PyOracleOutcome.ok (ByteArray.mk #[4]))}"
  let cMsg1 := compressErrorClass "compressWith model reject err codec=xz kind=ioError msg=foo bar 123"
  let cMsg2 := compressErrorClass "compressWith model reject err codec=xz kind=ioError msg=baz"
  if cOk != cOk2 || cOk == cSlip1 || cSlip1 != cSlip2 || cOpt1 != cOpt2 || cPy1 != cPy2 || cMsg1 != cMsg2 then
    throw (IO.userError s!"COMPRESS_ERRCLASS_FAIL: cOk={cOk} cSlip1={cSlip1} cSlip2={cSlip2} cOpt1={cOpt1} cOpt2={cOpt2} cPy1={cPy1} cPy2={cPy2} cMsg1={cMsg1} cMsg2={cMsg2}")
  let optFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompressWith .zstd opts _ _ => opts.maxOutputBytes >= 100 && opts.maxOutputBytes <= 20000
      | _ => false
  let minOpt ← shrinkElements shrinkOp optFails #[.decompressWith .zstd { maxOutputBytes := 10000 } (ByteArray.mk #[0x41]) "opt"]
  match minOpt.toList with
  | .decompressWith .zstd opts _ _ :: _ =>
    if opts.maxOutputBytes != 100 then
      throw (IO.userError s!"COMPRESS_SHRINK_OPT_FAIL: expected 100 got {opts.maxOutputBytes}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_OPT_FAIL: bad op")
  let mut buf3Anchor := ByteArray.mk (Array.replicate 2048 0x77)
  let pfx3 := ByteArray.mk #[0xA1, 0xA2, 0xA3, 0xA4]
  let mid3 := ByteArray.mk #[0xC1, 0xC2, 0xC3, 0xC4]
  let sfx3 := ByteArray.mk #[0xB1, 0xB2, 0xB3, 0xB4]
  for j in [0:4] do
    buf3Anchor := buf3Anchor.set! j (pfx3.get! j)
    buf3Anchor := buf3Anchor.set! (1022 + j) (mid3.get! j)
    buf3Anchor := buf3Anchor.set! (2044 + j) (sfx3.get! j)
  let threeAnchorFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ =>
        hasSubseq inp pfx3 && hasSubseq inp mid3 && hasSubseq inp sfx3
      | _ => false
  let min3Anchor ← shrinkElements shrinkOp threeAnchorFails #[.decompress .zstd buf3Anchor "threeAnchor2048"]
  match min3Anchor.toList with
  | .decompress .zstd p _ :: _ =>
    if p.size != 12 then
      throw (IO.userError s!"COMPRESS_SHRINK_3ANCHOR_FAIL: expected size 12, got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_3ANCHOR_FAIL: bad op")
  let buf1024Nz := ByteArray.mk (Array.replicate 1024 0x77)
  let reqIdx33 : Array Nat := Id.run do
    let mut a : Array Nat := #[]
    for k in [0:33] do
      a := a.push (k * 31 + 10)
    return a
  let nz33Fails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun op =>
      match op with
      | .decompress .zstd inp _ =>
        inp.size == 1024 && reqIdx33.all (fun idx => inp.get! idx != 0)
      | _ => false
  let min33Nz ← shrinkElements shrinkOp nz33Fails #[.decompress .zstd buf1024Nz "nz33In1024"]
  match min33Nz.toList with
  | .decompress .zstd p _ :: _ =>
    let nzCnt := Id.run do
      let mut cnt := 0
      for b in p.data do
        if b != 0 then cnt := cnt + 1
      return cnt
    if p.size != 1024 || nzCnt != 33 then
      throw (IO.userError s!"COMPRESS_SHRINK_NZ33_FAIL: size={p.size} nzCnt={nzCnt}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_NZ33_FAIL: bad op")
  let coupled4k := ByteArray.mk (Array.replicate 4096 0x41)
  let coupledCompFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .compressWith .zstd opts p => opts.maxInputBytes == some p.size && p.size >= 1
      | _ => false
  let minCoupledComp ← shrinkElements shrinkOp coupledCompFails
    #[.compressWith .zstd { maxInputBytes := some coupled4k.size } coupled4k]
  match minCoupledComp.toList with
  | .compressWith .zstd opts p :: _ =>
    if p.size != 1 || opts.maxInputBytes != some 1 then
      throw (IO.userError s!"COMPRESS_SHRINK_COUPLED_COMP_FAIL: size={p.size} maxIn={repr opts.maxInputBytes}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_COUPLED_COMP_FAIL: bad op")
  let coupledDecFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompressWith .gzip opts inp _ => opts.maxInputBytes == some inp.size && inp.size >= 1
      | _ => false
  let minCoupledDec ← shrinkElements shrinkOp coupledDecFails
    #[.decompressWith .gzip { maxInputBytes := some coupled4k.size } coupled4k "coupledDec"]
  match minCoupledDec.toList with
  | .decompressWith .gzip opts p _ :: _ =>
    if p.size != 1 || opts.maxInputBytes != some 1 then
      throw (IO.userError s!"COMPRESS_SHRINK_COUPLED_DEC_FAIL: size={p.size} maxIn={repr opts.maxInputBytes}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_COUPLED_DEC_FAIL: bad op")
  let mut bufReal3 := ByteArray.mk (Array.replicate 2048 0x77)
  let hdr18 := ByteArray.mk ((List.range 18).toArray.map fun i => UInt8.ofNat (0x80 + i))
  let mid5 := ByteArray.mk #[0xC1, 0xC2, 0xC3, 0xC4, 0xC5]
  let ftr18 := ByteArray.mk ((List.range 18).toArray.map fun i => UInt8.ofNat (0xA0 + i))
  for j in [0:18] do
    bufReal3 := bufReal3.set! j (hdr18.get! j)
    bufReal3 := bufReal3.set! (2030 + j) (ftr18.get! j)
  for j in [0:5] do
    bufReal3 := bufReal3.set! (1022 + j) (mid5.get! j)
  let real3Fails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompress .gzip inp _ =>
        inp.extract 0 18 == hdr18 &&
        hasSubseq (inp.extract 18 (if inp.size >= 18 then inp.size - 18 else 0)) mid5 &&
        (inp.size >= 36 && inp.extract (inp.size - 18) inp.size == ftr18)
      | _ => false
  let minReal3 ← shrinkElements shrinkOp real3Fails #[.decompress .gzip bufReal3 "realHeader3Anchor"]
  match minReal3.toList with
  | .decompress .gzip p _ :: _ =>
    if p.size != 41 then
      throw (IO.userError s!"COMPRESS_SHRINK_REAL3_FAIL: expected 41, got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_REAL3_FAIL: bad op")
  let mut buf9Anchor := ByteArray.mk (Array.replicate 512 0x77)
  let mut anchors9 : Array ByteArray := #[]
  let positions9 := #[0, 30, 90, 150, 255, 300, 360, 420, 510]
  for idx in [0:positions9.size] do
    let pos := positions9[idx]!
    let anc := ByteArray.mk #[UInt8.ofNat (0xE0 + idx), UInt8.ofNat (0xF0 + idx)]
    anchors9 := anchors9.push anc
    buf9Anchor := buf9Anchor.set! pos (anc.get! 0)
    buf9Anchor := buf9Anchor.set! (pos + 1) (anc.get! 1)
  let nineAnchorFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompress .zstd inp _ => anchors9.all (hasSubseq inp ·)
      | _ => false
  let min9Anchor ← shrinkElements shrinkOp nineAnchorFails #[.decompress .zstd buf9Anchor "nineAnchor512"]
  match min9Anchor.toList with
  | .decompress .zstd p _ :: _ =>
    if p.size != 18 then
      throw (IO.userError s!"COMPRESS_SHRINK_9ANCHOR_FAIL: expected 18, got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_9ANCHOR_FAIL: bad op")
  let big131k := pushReplicateByte ByteArray.empty 0x41 131073
  let big131kFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .compress .zstd p => p.size >= 1 && p.get! 0 == 0x41
      | _ => false
  let min131k ← shrinkElements shrinkOp big131kFails #[.compress .zstd big131k]
  match min131k.toList with
  | .compress .zstd p :: _ =>
    if p.size != 1 then
      throw (IO.userError s!"COMPRESS_SHRINK_131K_FAIL: expected 1, got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_131K_FAIL: bad op")
  let validGz4k := Model.encodeStored .gzip big4k
  let validGzFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompressWith .gzip opts inp _ =>
        match decodeStoredForShrink .gzip inp with
        | some out => out.size > opts.maxOutputBytes && opts.maxOutputBytes >= 1
        | none => false
      | _ => false
  let minValidGz ← shrinkElements shrinkOp validGzFails
    #[.decompressWith .gzip { maxOutputBytes := 10 } validGz4k "bombLimit"]
  match minValidGz.toList with
  | .decompressWith .gzip opts inp _ :: _ =>
    match decodeStoredForShrink .gzip inp with
    | some out =>
      if out.size != 2 || opts.maxOutputBytes != 1 then
        throw (IO.userError s!"COMPRESS_SHRINK_VALID_STREAM_FAIL: plain={out.size} maxOut={opts.maxOutputBytes}")
    | none => throw (IO.userError "COMPRESS_SHRINK_VALID_STREAM_FAIL: shrunk stream failed decode")
  | _ => throw (IO.userError "COMPRESS_SHRINK_VALID_STREAM_FAIL: bad op")
  let gzHdr10 := ByteArray.mk #[0x1F, 0x8B, 0x08, 0x08, 0, 0, 0, 0, 0, 0x03]
  let gzFname16 := "abcdefghijklmno".toUTF8.push 0x00
  let gzBody35 := pushReplicateByte ByteArray.empty 0x43 35
  let gzBlk40 := pushU16LE (pushU16LE (ByteArray.empty.push 0x01) 35) (35 ^^^ 0xFFFF) ++ gzBody35
  let gzTrl8 := pushU32LE (pushU32LE ByteArray.empty (crc32 gzBody35 0 gzBody35.size)) 35
  let gzFnameStream := gzHdr10 ++ gzFname16 ++ gzBlk40 ++ gzTrl8
  let gzFnameFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompress .gzip inp _ =>
        inp.size >= 18 && inp.extract 0 10 == gzHdr10 &&
        (match (List.range (inp.size - 10)).find? (fun k => inp.get! (10 + k) == 0x00) with
         | some k => inp.extract (10 + k + 1) inp.size == gzBlk40 ++ gzTrl8
         | none => false)
      | _ => false
  let minGzFname ← shrinkElements shrinkOp gzFnameFails #[.decompress .gzip gzFnameStream "richHeader"]
  match minGzFname.toList with
  | .decompress .gzip p _ :: _ =>
    if p.size != gzHdr10.size + 1 + gzBlk40.size + gzTrl8.size then
      throw (IO.userError s!"COMPRESS_SHRINK_FNAME_FAIL: got {p.size}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_FNAME_FAIL: bad op")
  let toHiFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .compressWith .xz opts _ => opts.level == some 9 && opts.timeoutMs >= 30000
      | _ => false
  let minToHi ← shrinkElements shrinkOp toHiFails
    #[.compressWith .xz { level := some 9, timeoutMs := 60000 } (ByteArray.mk #[0x41])]
  match minToHi.toList with
  | .compressWith .xz opts _ :: _ =>
    if opts.timeoutMs != 30000 then
      throw (IO.userError s!"COMPRESS_SHRINK_TIMEOUT_HI_FAIL: got {opts.timeoutMs}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_TIMEOUT_HI_FAIL: bad op")
  let toLoFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompressWith .xz opts _ _ => opts.timeoutMs >= 7 && opts.timeoutMs <= 500
      | _ => false
  let minToLo ← shrinkElements shrinkOp toLoFails
    #[.decompressWith .xz { timeoutMs := 500 } (ByteArray.mk #[0x41]) "to"]
  match minToLo.toList with
  | .decompressWith .xz opts _ _ :: _ =>
    if opts.timeoutMs != 7 then
      throw (IO.userError s!"COMPRESS_SHRINK_TIMEOUT_LO_FAIL: got {opts.timeoutMs}")
  | _ => throw (IO.userError "COMPRESS_SHRINK_TIMEOUT_LO_FAIL: bad op")
  let reprSample := reprStr (CompressFuzzOp.decompress .zstd (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]) "t")
  if (reprSample.splitOn "deadbeef").length <= 1 then
    throw (IO.userError s!"COMPRESS_SHRINK_REPR_FAIL: got {reprSample}")
  let cVs1 := compressErrorClass "decompress model reject err codec=zstd tag=t kind=corruptData msg=expected a vs b at 100"
  let cVs2 := compressErrorClass "decompress model reject err codec=zstd tag=t kind=corruptData msg=expected c vs d at 1"
  if cVs1 != cVs2 then
    throw (IO.userError s!"COMPRESS_ERRCLASS_MSG_VS_FAIL: cVs1={cVs1} cVs2={cVs2}")
  let head4 := "HEAD".toUTF8
  let tail4 := "TAIL".toUTF8
  let zstdCompact28 :=
    pushU32LE (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x38]) 4104 ++
    (ByteArray.mk #[0x20, 0x00, 0x00] ++ head4) ++
    ByteArray.mk #[0x02, 0x80, 0x00, 0x41] ++
    (ByteArray.mk #[0x21, 0x00, 0x00] ++ tail4)
  let twoAnchorValidFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompress .zstd inp _ =>
        match decodeStoredForShrink .zstd inp with
        | some out => out.size >= 8 && out.extract 0 4 == head4 && out.extract (out.size - 4) out.size == tail4
        | none => false
      | _ => false
  let minCompact28 ← shrinkElements shrinkOp twoAnchorValidFails #[.decompress .zstd zstdCompact28 "cliValid"]
  match minCompact28.toList with
  | .decompress .zstd p _ :: _ =>
    match decodeStoredForShrink .zstd p with
    | some out =>
      if p.size > zstdCompact28.size || out.size != 8 then
        throw (IO.userError s!"COMPRESS_SHRINK_ANTIBLOAT_FAIL: bytes={p.size} plain={out.size}")
    | none => throw (IO.userError "COMPRESS_SHRINK_ANTIBLOAT_FAIL: decode failed")
  | _ => throw (IO.userError "COMPRESS_SHRINK_ANTIBLOAT_FAIL: bad op")
  let plain512 := head4 ++ pushReplicateByte ByteArray.empty 0x78 504 ++ tail4
  let xzValid512 := Model.encodeStored .xz plain512
  let coupledMaxOutEqFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompressWith .xz opts inp _ =>
        opts.maxOutputBytes >= 1 &&
        match decodeStoredForShrink .xz inp with
        | some out => out.size == opts.maxOutputBytes
        | none => false
      | _ => false
  let minMaxOutEq ← shrinkElements shrinkOp coupledMaxOutEqFails
    #[.decompressWith .xz { maxOutputBytes := 512 } xzValid512 "exactLim"]
  match minMaxOutEq.toList with
  | .decompressWith .xz opts p _ :: _ =>
    match decodeStoredForShrink .xz p with
    | some out =>
      if out.size != 1 || opts.maxOutputBytes != 1 then
        throw (IO.userError s!"COMPRESS_SHRINK_COUPLED_MAXOUT_EQ_FAIL: plain={out.size} lim={opts.maxOutputBytes}")
    | none => throw (IO.userError "COMPRESS_SHRINK_COUPLED_MAXOUT_EQ_FAIL: decode failed")
  | _ => throw (IO.userError "COMPRESS_SHRINK_COUPLED_MAXOUT_EQ_FAIL: bad op")
  let zstBomb4k :=
    pushU32LE (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x38]) 4096 ++
    ByteArray.mk #[0x03, 0x80, 0x00, 0x41]
  let coupledMaxOutPlus1Fails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompressWith .zstd opts inp _ =>
        opts.maxOutputBytes >= 1 &&
        match decodeStoredForShrink .zstd inp with
        | some out => out.size == opts.maxOutputBytes + 1
        | none => false
      | _ => false
  let minMaxOutPlus1 ← shrinkElements shrinkOp coupledMaxOutPlus1Fails
    #[.decompressWith .zstd { maxOutputBytes := 4095 } zstBomb4k "bombLimit"]
  match minMaxOutPlus1.toList with
  | .decompressWith .zstd opts p _ :: _ =>
    match decodeStoredForShrink .zstd p with
    | some out =>
      if out.size != 2 || opts.maxOutputBytes != 1 || p.size > 32 then
        throw (IO.userError s!"COMPRESS_SHRINK_COUPLED_MAXOUT_PLUS1_FAIL: bytes={p.size} plain={out.size} lim={opts.maxOutputBytes}")
    | none => throw (IO.userError "COMPRESS_SHRINK_COUPLED_MAXOUT_PLUS1_FAIL: decode failed")
  | _ => throw (IO.userError "COMPRESS_SHRINK_COUPLED_MAXOUT_PLUS1_FAIL: bad op")
  let rle131k := ByteArray.mk #[0x02, 0x00, 0x10, 0x41]
  let zstOver512k :=
    pushU32LE (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x50]) 655361 ++
    rle131k ++ rle131k ++ rle131k ++ rle131k ++ rle131k ++ ByteArray.mk #[0x0B, 0x00, 0x00, 0x42]
  let over512kFails : Array CompressFuzzOp → IO Bool := fun tr =>
    return tr.any fun
      | .decompress .zstd inp _ =>
        match decodeStoredForShrink .zstd inp with
        | some out => out.size >= 1 && out.get! (out.size - 1) == 0x42
        | none => false
      | _ => false
  let minOver512k ← shrinkElements shrinkOp over512kFails #[.decompress .zstd zstOver512k "zstdCapFcs"]
  match minOver512k.toList with
  | .decompress .zstd p _ :: _ =>
    match decodeStoredForShrink .zstd p with
    | some out =>
      if out.size != 1 then
        throw (IO.userError s!"COMPRESS_SHRINK_OVER512K_FAIL: plain={out.size}")
    | none => throw (IO.userError "COMPRESS_SHRINK_OVER512K_FAIL: decode failed")
  | _ => throw (IO.userError "COMPRESS_SHRINK_OVER512K_FAIL: bad op")
  let twoStepPlain := "rt".toUTF8
  let twoStepComp := Model.encodeStored .zstd twoStepPlain
  let statefulTraceFails : Array CompressFuzzOp → IO Bool := fun tr => do
    let mut st := Model.State.empty
    for op in tr do
      match op with
      | .compress .zstd p =>
        st := st.record .zstd (Model.encodeStored .zstd p) p
      | .decompress .zstd inp _ =>
        if st.lookup .zstd inp == some twoStepPlain then
          return true
      | _ => pure ()
    return false
  let minStatefulTrace ← shrinkTrace statefulTraceFails
    #[.isToolAvailable .gzip, .compress .zstd twoStepPlain, .isToolAvailable .xz, .decompress .zstd twoStepComp "rt"]
  if minStatefulTrace.size != 2 then
    throw (IO.userError s!"COMPRESS_SHRINK_STATEFUL_TRACE_FAIL: len={minStatefulTrace.size}")
  safeSuitePrintln s!"COMPRESS_SHRINK_DETAILS_SELFTEST_OK: eval4k={evalCnt} eval2049={eval2049Cnt} eval128={eval128Cnt} eval129={eval129Cnt} maxOut=100"

/-- Registered differential fuzz suite for `LeanSwe.Compress`. -/
def suite : FuzzSuite :=
  { name := "compress"
    description := "3-way differential fuzzer comparing LeanSwe.Compress IO wrapper, Model specification, and Python reference codecs."
    runSmoke := fun cfg => do
      Fuzz.Common.recordSuiteSteps 1000
      runSeededFuzz cfg 1000 true
    runFuzz := fun cfg => do
      Fuzz.Common.recordSuiteSteps cfg.steps
      runSeededFuzz cfg cfg.steps false
    selfTestShrink := runCompressShrinkSelfTest }

end Fuzz.Compress
