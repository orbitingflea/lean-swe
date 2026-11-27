import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import LeanSwe.CmdLine.Interface
import LeanSweProofs.CmdLine.Model

namespace Fuzz.CmdLine

open Fuzz.Common
open LeanSwe.CmdLine

/-- Stdin channel setup variants generated for differential stdio fuzzing. -/
inductive StdinSetup where
  /-- Pipe backing with bytes, closed writer flag, nonblock flag, and capacity. -/
  | pipe (bytes : ByteArray) (writersClosed : Bool) (nonblock : Bool) (cap : Nat)
  /-- Memfd-backed regular file with initial bytes. -/
  | memfd (bytes : ByteArray)
  /-- Read from `/dev/null`. -/
  | nullDev
  /-- Read from `/dev/full`. -/
  | fullDev
  /-- Directory fd bound to stdin (`EISDIR`). -/
  | dirFd
  /-- Write-only fd bound to stdin (`EBADF`). -/
  | wrOnly
  /-- Closed fd 0 (`EBADF`). -/
  | closedFd
  /-- Pseudoterminal slave bound to stdin. -/
  | pty (echoOff : Bool)
  /-- Hung-up PTY master whose slave fd is closed (`EIO`). -/
  | ptyHungup
  deriving BEq, DecidableEq, Inhabited

/-- Stdout/stderr channel setup variants generated for differential stdio fuzzing. -/
inductive OutSetup where
  /-- Capture pipe with optional `O_NONBLOCK` and capacity. -/
  | capturePipe (nonblock : Bool) (cap : Nat)
  /-- Pipe with closed read end (`EPIPE`). -/
  | brokenPipe
  /-- Write to `/dev/full` (`ENOSPC`). -/
  | fullDev
  /-- Write to `/dev/null`. -/
  | nullDev
  /-- Read-only fd bound to output (`EBADF`). -/
  | rdOnly
  /-- Closed output fd (`EBADF`). -/
  | closedFd
  /-- Hung-up PTY master whose slave fd is closed. -/
  | ptyHungup
  deriving BEq, DecidableEq, Inhabited

/-- Stateful differential fuzzing operation targeting `LeanSwe.CmdLine` and `Model.StdioWorld`. -/
inductive CmdLineFuzzOp where
  /-- Reconfigure stdin fd and backing. -/
  | setupStdin (kind : StdinSetup)
  /-- Reconfigure stdout fd and backing. -/
  | setupStdout (kind : OutSetup)
  /-- Reconfigure stderr fd and backing. -/
  | setupStderr (kind : OutSetup)
  /-- Feed additional bytes to open stdin pipe or PTY master. -/
  | feedPipeOrPty (bytes : ByteArray)
  /-- Send Ctrl-D EOF byte to open PTY master. -/
  | sendPtyEof
  /-- Close open stdin pipe/PTY writer fd. -/
  | closeStdinWriter
  /-- Arm a repeating thread-directed `SIGALRM` interval timer without `SA_RESTART`. -/
  | armEintr (usec : UInt32)
  /-- Set an environment variable using raw bytes. -/
  | setEnv (k v : ByteArray) (ovw : Bool)
  /-- Unset an environment variable using raw bytes. -/
  | unsetEnv (k : ByteArray)
  /-- Invoke `defaultOps.readLine`. -/
  | callReadLine
  /-- Invoke `defaultOps.writeOut`. -/
  | callWriteOut (text : String)
  /-- Invoke `defaultOps.writeErr`. -/
  | callWriteErr (text : String)
  /-- Invoke `defaultOps.getEnv`. -/
  | callGetEnv (key : String)
  /-- Invoke `defaultApi.promptLine`. -/
  | callPromptLine (prompt : String) (default : Option String)
  /-- Invoke `defaultApi.confirm`. -/
  | callConfirm (prompt : String) (default : Option Bool) (maxAttempts : Nat)
  /-- Invoke `defaultApi.parseWithEnv`. -/
  | callParseWithEnv (spec : CommandSpec) (args : List String)
  /-- Invoke `defaultApi.runCli`. -/
  | callRunCli (spec : CommandSpec) (args : List String) (handlerExit : UInt32)
  /-- Check pure `renderHelp` and `renderArgs`/`parse` round-trip. -/
  | callPureRoundTrip (spec : CommandSpec) (args : List String)
  deriving BEq, Inhabited

/-- Convert a `ByteArray` into an array of single bytes for trace shrinking. -/
def byteArrayToChunks (ba : ByteArray) : Array UInt8 := Id.run do
  let mut out := Array.mkEmpty ba.size
  for i in List.range ba.size do
    out := out.push ba[i]!
  return out

/-- Reassemble an array of `UInt8` into a `ByteArray`. -/
def chunksToByteArray (arr : Array UInt8) : ByteArray :=
  arr.foldl (init := ByteArray.empty) fun acc b => acc.push b

/-- Shrink a `ByteArray` while preserving a predicate `fails`. -/
def shrinkByteArray (fails : ByteArray → IO Bool) (ba : ByteArray) : IO ByteArray := do
  let arr ← shrinkTrace (fun c => fails (chunksToByteArray c)) (byteArrayToChunks ba) (allowEmpty := true)
  return chunksToByteArray arr

/-- Generate an arbitrary byte sequence mixing valid UTF-8, invalid UTF-8, NUL, and newline edge cases. -/
def genLineBytes (rng : Rng) : ByteArray × Rng :=
  let (kind, r1) := rng.nextNat 17
  match kind with
  | 0 => ("hello\n".toUTF8, r1)
  | 1 => ("héllo 🚀\n".toUTF8, r1)
  | 2 => (ByteArray.mk #[0xed, 0xa0, 0x80, 0x0a], r1)
  | 3 => (ByteArray.mk #[0xc0, 0xaf, 0x0a], r1)
  | 4 => (ByteArray.mk #[0xf4, 0x90, 0x80, 0x80, 0x41, 0x0a], r1)
  | 5 => (ByteArray.mk #[0x61, 0x00, 0x62, 0x0a], r1)
  | 6 => ("\n".toUTF8, r1)
  | 7 => ("foo\r\nbar\r\r\n".toUTF8, r1)
  | 8 | 15 => ("no_newline".toUTF8, r1)
  | 9 => ("mid\rcr\n".toUTF8, r1)
  | 10 =>
    let big := String.ofList (List.replicate 8200 'x') ++ "\n"
    (big.toUTF8, r1)
  | 11 => ("  yes \n".toUTF8, r1)
  | 12 => ("  NO \n".toUTF8, r1)
  | 13 | 14 => ("bad\ny\n".toUTF8, r1)
  | _ =>
    let (len, r2) := r1.nextRange 0 16
    Id.run do
      let mut cur := r2
      let mut bs := ByteArray.empty
      for _ in List.range len do
        let (b, rN) := cur.nextNat 256
        cur := rN
        bs := bs.push (UInt8.ofNat b)
      let (addNl, rEnd) := cur.nextNat 2
      if addNl == 0 then bs := bs.push 0x0a
      return (bs, rEnd)

/-- Generate a small valid or intentionally weird `CommandSpec` for fuzzing. -/
def genCommandSpec (rng : Rng) : CommandSpec × Rng :=
  let (kind, r1) := rng.nextNat 5
  match kind with
  | 0 =>
    let sp : CommandSpec := {
      name := "fuzztool"
      version := some "1.0.0"
      about := "Fuzz CLI"
      options := [
        { name := "verbose", short := some 'v', long := some "verbose", kind := .bool, global := true },
        { name := "count", short := some 'c', long := some "count", kind := .nat, default := some "3", envVar := some "FUZZ_COUNT" },
        { name := "mode", long := some "mode", kind := .choice ["fast", "safe"], envVar := some "FUZZ_MODE" },
        { name := "tag", short := some 't', long := some "tag", kind := .string, repeatable := true }
      ]
      args := [{ name := "target", kind := .string, required := false }]
    }
    (sp, r1)
  | 1 =>
    let sp : CommandSpec := {
      name := "multi"
      version := some "2.0"
      options := [{ name := "dry", long := some "dry", kind := .bool, global := true }]
      subcommands := [
        { name := "run", options := [{ name := "port", short := some 'p', long := some "port", kind := .nat, envVar := some "MULTI_PORT" }], args := [{ name := "files", kind := .string, variadic := true }] },
        { name := "status" }
      ]
    }
    (sp, r1)
  | 2 =>
    let sp : CommandSpec := {
      name := "strict"
      options := [
        { name := "req", long := some "req", kind := .int, required := true, envVar := some "STRICT_REQ" },
        { name := "quiet", short := some 'q', kind := .bool }
      ]
    }
    (sp, r1)
  | 3 =>
    let sp : CommandSpec := {
      name := "badsug"
      options := [{ name := "flag", long := some "flag", kind := .bool, global := true }]
      subcommands := [{ name := "build", subcommands := [{ name := "push" }] }]
    }
    (sp, r1)
  | _ =>
    let sp : CommandSpec := {
      name := "invalid_non_global"
      options := [{ name := "bad", long := some "bad", kind := .bool, global := false }]
      subcommands := [{ name := "sub" }]
    }
    (sp, r1)

/-- Generate a list of CLI argument strings exercising help, version, options, positionals, and errors. -/
def genCliArgs (rng : Rng) : List String × Rng :=
  let (kind, r1) := rng.nextNat 15
  match kind with
  | 0 => (["--help"], r1)
  | 1 => (["-V"], r1)
  | 2 => (["-vc", "7", "--mode=fast", "pos1"], r1)
  | 3 => (["run", "-p", "8080", "--", "-dashfile"], r1)
  | 4 => (["--unknown-flag"], r1)
  | 5 => (["--tag", "a", "-t", "b", "--no-verbose"], r1)
  | 6 => (["--flag", "build", "push"], r1)
  | 7 => (["biuld"], r1)
  | 8 => (["--mode", "invalid"], r1)
  | 9 => (["--verbos"], r1)
  | 10 => (["-q", "--req", "-12"], r1)
  | 11 => (["--req=9"], r1)
  | 12 | 13 => ([], r1)
  | _ =>
    let (tok, r2) := r1.nextNat 4
    let extra := match tok with | 0 => "-h" | 1 => "--version" | 2 => "--count=-5" | _ => ""
    ([extra], r2)

/-- Generate a `String` for stdout/stderr write operations including empty, NUL-containing, and `> 4096`-byte strings. -/
def genWriteString (rng : Rng) : String × Rng :=
  let (kind, r1) := rng.nextNat 7
  match kind with
  | 0 => ("", r1)
  | 1 => ("ok\n", r1)
  | 2 => (String.ofList ['a', Char.ofNat 0, 'b', '\n'], r1)
  | 3 => ("prompt> ", r1)
  | 4 => ("🚀 unicode\n", r1)
  | 5 => (String.ofList (List.replicate 5000 'w') ++ "\n", r1)
  | _ => (String.ofList (List.replicate 64 'w') ++ "\n", r1)

/-- Generate an environment variable key, value, and overwrite flag. -/
def genEnvBytes (rng : Rng) : (ByteArray × ByteArray × Bool) × Rng :=
  let (kind, r1) := rng.nextNat 11
  let (ovwN, r2) := r1.nextNat 2
  let ovw := ovwN == 0
  match kind with
  | 0 => (("FUZZ_COUNT".toUTF8, "42".toUTF8, ovw), r2)
  | 1 => (("FUZZ_COUNT".toUTF8, "".toUTF8, ovw), r2)
  | 2 | 10 => (("FUZZ_MODE".toUTF8, ByteArray.mk #[0xed, 0xa0, 0x80], true), r2)
  | 3 => (("MULTI_PORT".toUTF8, "9090".toUTF8, ovw), r2)
  | 4 => (("FUZZ_KEY".toUTF8, "val".toUTF8, ovw), r2)
  | 5 => ((ByteArray.mk #[0x42, 0x41, 0x44, 0x00, 0x4b], "val".toUTF8, ovw), r2)
  | 6 => (("FUZZ_NUL".toUTF8, ByteArray.mk #[0x61, 0x00, 0x62], ovw), r2)
  | 7 => (("BAD=KEY".toUTF8, "v".toUTF8, ovw), r2)
  | 8 => (("STRICT_REQ".toUTF8, ByteArray.mk #[0xed, 0xa0, 0x80], true), r2)
  | _ => (("FUZZ_EMPTY".toUTF8, ByteArray.empty, ovw), r2)

/-- Generate a single `CmdLineFuzzOp`. -/
def genFuzzOp (rng : Rng) : CmdLineFuzzOp × Rng :=
  let (kind, r1) := rng.nextNat 19
  match kind with
  | 0 =>
    let (bs, r2) := genLineBytes r1
    let (cl, r3) := r2.nextNat 2
    let (nb, r4) := r3.nextNat 3
    (.setupStdin (.pipe bs (cl == 0) (nb == 0) 65536), r4)
  | 1 =>
    let (bs, r2) := genLineBytes r1
    (.setupStdin (.memfd bs), r2)
  | 2 =>
    let (sk, r2) := r1.nextNat 8
    let setup := match sk with
      | 0 => StdinSetup.nullDev | 1 => .ptyHungup | 2 => .dirFd
      | 3 => .wrOnly | 4 => .closedFd | 5 => .pty true
      | 6 => .pty false | _ => .fullDev
    (.setupStdin setup, r2)
  | 3 =>
    let (ok, r2) := r1.nextNat 8
    let setup := match ok with
      | 0 => OutSetup.capturePipe false 65536 | 1 => .brokenPipe | 2 => .fullDev
      | 3 => .nullDev | 4 => .rdOnly | 5 => .closedFd | 6 => .ptyHungup
      | _ => .capturePipe true 4096
    (.setupStdout setup, r2)
  | 4 =>
    let (ok, r2) := r1.nextNat 8
    let setup := match ok with
      | 0 => OutSetup.capturePipe false 65536 | 1 => .brokenPipe | 2 => .fullDev
      | 3 => .nullDev | 4 => .rdOnly | 5 => .closedFd | 6 => .ptyHungup
      | _ => .capturePipe true 4096
    (.setupStderr setup, r2)
  | 5 =>
    let (bs, r2) := genLineBytes r1
    (.feedPipeOrPty bs, r2)
  | 6 => (.sendPtyEof, r1)
  | 7 => (.closeStdinWriter, r1)
  | 8 =>
    let ((k, v, ovw), r2) := genEnvBytes r1
    (.setEnv k v ovw, r2)
  | 9 =>
    let (which, r2) := r1.nextNat 5
    let k := match which with
      | 0 => "FUZZ_COUNT".toUTF8 | 1 => "FUZZ_MODE".toUTF8
      | 2 => "BAD=KEY".toUTF8 | 3 => ByteArray.mk #[0x42, 0x00, 0x4b]
      | _ => "MULTI_PORT".toUTF8
    (.unsetEnv k, r2)
  | 10 => (.callReadLine, r1)
  | 11 =>
    let (s, r2) := genWriteString r1
    (.callWriteOut s, r2)
  | 12 =>
    let (s, r2) := genWriteString r1
    (.callWriteErr s, r2)
  | 13 =>
    let (which, r2) := r1.nextNat 5
    let k := match which with | 0 => "FUZZ_COUNT" | 1 => "FUZZ_MODE" | 2 => "BAD=KEY" | 3 => "" | _ => "MISSING_KEY"
    (.callGetEnv k, r2)
  | 14 =>
    let (p, r2) := genWriteString r1
    let (df, r3) := r2.nextNat 2
    (.callPromptLine p (if df == 0 then some "def" else none), r3)
  | 15 =>
    let (p, r2) := genWriteString r1
    let (df, r3) := r2.nextNat 3
    let (maIdx, r4) := r3.nextNat 5
    let ma := match maIdx with | 0 => 1 | 1 | 2 => 2 | 3 => 3 | _ => 4
    let d? := match df with | 0 => some true | 1 => some false | _ => none
    (.callConfirm p d? ma, r4)
  | 16 =>
    let (sp, r2) := genCommandSpec r1
    let (args, r3) := genCliArgs r2
    let (ex, r4) := r3.nextRange 0 300
    (.callRunCli sp args (UInt32.ofNat ex), r4)
  | 17 =>
    let (us, r2) := r1.nextRange 800 2500
    (.armEintr (UInt32.ofNat us), r2)
  | _ =>
    let (mode, r2) := r1.nextNat 5
    if mode == 0 || mode == 3 || mode == 4 then
      let (sp, r3) := genCommandSpec r2
      let (args, r4) := genCliArgs r3
      (.callParseWithEnv sp args, r4)
    else if mode == 1 then
      let (p, r3) := genWriteString r2
      (.callConfirm p none 3, r3)
    else
      let (sp, r3) := genCommandSpec r2
      let (args, r4) := genCliArgs r3
      (.callPureRoundTrip sp args, r4)

end Fuzz.CmdLine
