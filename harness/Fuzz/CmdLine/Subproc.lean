import Fuzz.Common.Coverage
import LeanSwe.CmdLine.Interface
import LeanSweProofs.CmdLine.Model

namespace Fuzz.CmdLine.Subproc

open Fuzz.Common
open LeanSwe
open LeanSwe.CmdLine

/-- Raw `execve` subprocess runner with optional `SIGPIPE = SIG_DFL` and broken stdout pipe. -/
@[extern "leanswe_cmdfuzz_exec_raw"]
opaque execRaw (exe a1 a2 a3 : @& ByteArray) (dflSigpipe brokenStdout : UInt8) : BaseIO UInt32

private def isEpipeError (err : IO.Error) : Bool :=
  match err with
  | .resourceVanished 32 _ => true
  | _ => false

private def hexDigit? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeHexBytes? (s : String) : Option ByteArray :=
  let rec go (cs : List Char) (acc : ByteArray) : Option ByteArray :=
    match cs with
    | [] => some acc
    | [_] => none
    | a :: b :: rest => do
      let hi ← hexDigit? a
      let lo ← hexDigit? b
      go rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
  go s.toList ByteArray.empty

/-- Encode a `ByteArray` into lowercase hexadecimal ASCII. -/
def encodeHexBytes (bs : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for i in List.range bs.size do
    let b := bs[i]!.toNat
    out := out.push digits[b / 16]!
    out := out.push digits[b % 16]!
  return out

private def runWorkerArgv (rawVal hexExpected : String) : IO UInt32 := do
  let some expectedBs := decodeHexBytes? hexExpected | return 11
  let expected := (Model.decodeArgvModel [expectedBs]).headD ""
  if rawVal != expected then
    return 12
  let spec : CommandSpec := {
    name := "worker"
    options := [{ name := "val", long := some "val", kind := .string }]
  }
  match CmdLine.parse spec ["--val", rawVal] with
  | .error _ => return 13
  | .ok parsed =>
    if parsed.getString "val" == some expected then return 0 else return 14

private def runWorkerSigpipe : IO UInt32 := do
  try
    CmdLine.defaultOps.writeOut "sigpipe_probe\n"
    return 20
  catch e =>
    if isEpipeError e then return 42 else return 21

private def runWorkerFlushOut : IO UInt32 := do
  match ← CmdLine.promptLine "OUT_PROMPT>" none with
  | .error _ => return 30
  | .ok s => if s == "reply_ok" then return 0 else return 31

private def runWorkerFlushErr : IO UInt32 := do
  match ← CmdLine.confirm "CONF?" none 2 with
  | .error _ => return 40
  | .ok true => return 0
  | .ok false => return 41

private def runWorkerExitMod (codeStr : String) : IO UInt32 := do
  let some n := codeStr.toNat? | return 50
  let spec : CommandSpec := { name := "exitworker" }
  CmdLine.runCli spec [] (fun _ => pure (UInt32.ofNat n))

/-- Subprocess worker entry point dispatched by `Fuzz.Main` on `--cmdline-fuzz-worker`. -/
def workerMain : List String → IO UInt32
  | ["sigpipe", _] => runWorkerSigpipe
  | ["flush-out", _] => runWorkerFlushOut
  | ["flush-err", _] => runWorkerFlushErr
  | ["exit-mod", codeStr] => runWorkerExitMod codeStr
  | [tag, rawVal] =>
    if tag.startsWith "argv:" then
      runWorkerArgv rawVal (tag.drop 5).toString
    else
      return 98
  | _ => return 99

private def readExactBytes (h : IO.FS.Handle) (targetLen : Nat) : IO ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < targetLen do
    let chunk ← h.read (targetLen - acc.size).toUSize
    if chunk.isEmpty then
      break
    acc := acc ++ chunk
  return acc

/-- Run real `execve` / OS pipe subprocess checks and return the 5 hit coverage buckets. -/
def runSubprocChecks : IO (List CoverageBucket) := do
  let exe := (← IO.appPath).toString
  let mut buckets : List CoverageBucket := []
  let rawPayloads : List ByteArray := [
    ByteArray.mk #[0x61, 0xed, 0xa0, 0x80, 0x62],
    ByteArray.mk #[0xc0, 0xaf, 0x7a],
    ByteArray.mk #[0xf4, 0x90, 0x80, 0x80, 0x21],
    ByteArray.mk #[0x61, 0x00, 0x62]
  ]
  for payload in rawPayloads do
    let tag := s!"argv:{encodeHexBytes payload}"
    let rc ← execRaw exe.toUTF8 "--cmdline-fuzz-worker".toUTF8 tag.toUTF8 payload 0 0
    if rc != 0 then
      throw (IO.userError s!"SUBPROC_ARGV_LOSSY_UTF8_FAILED: rc={rc} tag={tag}")
  buckets := bucket "subproc" "argv_lossy_utf8" :: buckets
  let child1 ← IO.Process.spawn {
    cmd := exe
    args := #["--cmdline-fuzz-worker", "flush-out", "_"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let rc1 ← try
    let pOut ← readExactBytes child1.stdout "OUT_PROMPT>".toUTF8.size
    if String.fromUTF8? pOut != some "OUT_PROMPT>" then
      throw (IO.userError s!"SUBPROC_FLUSH_OUT_FAILED: got {repr pOut.data.toList}")
    child1.stdin.putStr "reply_ok\n"
    child1.stdin.flush
    let (stdin1, child1') ← child1.takeStdin
    let _ := stdin1
    child1'.wait
  catch e =>
    try let _ ← child1.kill catch _ => pure ()
    try let _ ← child1.wait catch _ => pure ()
    throw e
  if rc1 != 0 then
    throw (IO.userError s!"SUBPROC_FLUSH_OUT_EXIT: rc={rc1}")
  buckets := bucket "subproc" "flush_stdout_before_read" :: buckets
  let child2 ← IO.Process.spawn {
    cmd := exe
    args := #["--cmdline-fuzz-worker", "flush-err", "_"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let rc2 ← try
    let p1 ← readExactBytes child2.stdout "CONF?".toUTF8.size
    if String.fromUTF8? p1 != some "CONF?" then
      throw (IO.userError s!"SUBPROC_FLUSH_ERR_PROMPT1: got {repr p1.data.toList}")
    child2.stdin.putStr "maybe\n"
    child2.stdin.flush
    let e1 ← readExactBytes child2.stderr "Please answer yes or no.\n".toUTF8.size
    if String.fromUTF8? e1 != some "Please answer yes or no.\n" then
      throw (IO.userError s!"SUBPROC_FLUSH_ERR_MSG: got {repr e1.data.toList}")
    let p2 ← readExactBytes child2.stdout "CONF?".toUTF8.size
    if String.fromUTF8? p2 != some "CONF?" then
      throw (IO.userError s!"SUBPROC_FLUSH_ERR_PROMPT2: got {repr p2.data.toList}")
    child2.stdin.putStr "yes\n"
    child2.stdin.flush
    let (stdin2, child2') ← child2.takeStdin
    let _ := stdin2
    child2'.wait
  catch e =>
    try let _ ← child2.kill catch _ => pure ()
    try let _ ← child2.wait catch _ => pure ()
    throw e
  if rc2 != 0 then
    throw (IO.userError s!"SUBPROC_FLUSH_ERR_EXIT: rc={rc2}")
  buckets := bucket "subproc" "flush_stderr_before_read" :: buckets
  for n in [0, 1, 255, 256, 258, 300] do
    let rc ← execRaw exe.toUTF8 "--cmdline-fuzz-worker".toUTF8 "exit-mod".toUTF8 (toString n).toUTF8 0 0
    let expected := UInt32.ofNat (n % 256)
    if rc != expected then
      throw (IO.userError s!"SUBPROC_EXIT_MOD_MISMATCH: n={n} got={rc} expected={expected}")
  buckets := bucket "subproc" "exit_code_mod_256" :: buckets
  let rcSig ← execRaw exe.toUTF8 "--cmdline-fuzz-worker".toUTF8 "sigpipe".toUTF8 "_".toUTF8 1 1
  if rcSig != 42 then
    throw (IO.userError s!"SUBPROC_SIGPIPE_MISMATCH: expected rc=42 (EPIPE), got rc={rcSig}")
  buckets := bucket "subproc" "sigpipe_dfl_becomes_epipe" :: buckets
  return buckets

end Fuzz.CmdLine.Subproc
