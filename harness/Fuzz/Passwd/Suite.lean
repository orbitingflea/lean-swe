import Std.Data.HashMap
import Fuzz.Common.Suite
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Passwd.Gen
import Fuzz.Passwd.Checks
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Model
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSwe.LinuxSyscall.Sandbox.Interface
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.Passwd

open Fuzz.Common
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

private inductive PyPwdOutcome where
  | found (entry : PasswdEntry)
  | notFound
  | err (errno : Nat)
  deriving DecidableEq, BEq

private instance : Repr PyPwdOutcome where
  reprPrec
    | .found e, _ => s!"PyPwdOutcome.found {repr e}"
    | .notFound, _ => "PyPwdOutcome.notFound"
    | .err n, _ => s!"PyPwdOutcome.err {n}"

private def formatResEntry (r : Except Errno (Option PasswdEntry)) : String :=
  match r with
  | .ok (some e) => s!"ok(some {repr e})"
  | .ok none => "ok(none)"
  | .error e => s!"error({e.name})"

private def isErrnoRes (expected : Errno) (r : Except Errno (Option PasswdEntry)) : Bool :=
  match r with
  | .error e => e == expected
  | .ok _ => false

private structure PyPwdOracle where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }
  uidCache : IO.Ref (Std.HashMap UInt32 PyPwdOutcome)
  nameCache : IO.Ref (Std.HashMap ByteArray PyPwdOutcome)

private def hexNibble (c : Char) : Except String UInt8 :=
  if '0' ≤ c && c ≤ '9' then
    .ok (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then
    .ok (UInt8.ofNat (10 + c.toNat - 'a'.toNat))
  else if 'A' ≤ c && c ≤ 'F' then
    .ok (UInt8.ofNat (10 + c.toNat - 'A'.toNat))
  else
    .error s!"INVALID_HEX_CHAR {repr c}"

private def decodeHexBytes (s : String) : Except String ByteArray := do
  let cs := s.toList
  if cs.length % 2 != 0 then
    throw s!"ODD_HEX_LENGTH len={cs.length}"
  let mut out := ByteArray.emptyWithCapacity (cs.length / 2)
  let mut rest := cs
  while !rest.isEmpty do
    match rest with
    | hi :: lo :: tail =>
      let h ← hexNibble hi
      let l ← hexNibble lo
      out := out.push ((h <<< 4) ||| l)
      rest := tail
    | _ => break
  return out

private def encodeHexBytes (ba : ByteArray) : String := Id.run do
  let mut out := ""
  for b in ba.data do
    let hi := (b >>> 4).toNat
    let lo := (b &&& 0x0F).toNat
    let ch (n : Nat) : Char :=
      if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
    out := out.push (ch hi)
    out := out.push (ch lo)
  return out

private def pyOracleScript : String :=
  "import os, pwd, sys\n" ++
  "def enc(v):\n" ++
  "    return os.fsencode(v or '').hex()\n" ++
  "for line in sys.stdin:\n" ++
  "    s = line.strip()\n" ++
  "    if not s:\n" ++
  "        continue\n" ++
  "    if s == 'QUIT':\n" ++
  "        break\n" ++
  "    try:\n" ++
  "        if s.startswith('U:'):\n" ++
  "            p = pwd.getpwuid(int(s[2:]))\n" ++
  "        elif s.startswith('N:'):\n" ++
  "            p = pwd.getpwnam(os.fsdecode(bytes.fromhex(s[2:])))\n" ++
  "        else:\n" ++
  "            sys.stdout.write('ERR:22\\n')\n" ++
  "            sys.stdout.flush()\n" ++
  "            continue\n" ++
  "        fields = [enc(p.pw_name), str(p.pw_uid & 0xFFFFFFFF), str(p.pw_gid & 0xFFFFFFFF), enc(p.pw_gecos), enc(p.pw_dir), enc(p.pw_shell)]\n" ++
  "        sys.stdout.write('FOUND:' + ':'.join(fields) + '\\n')\n" ++
  "    except KeyError:\n" ++
  "        sys.stdout.write('NONE\\n')\n" ++
  "    except OSError as e:\n" ++
  "        sys.stdout.write(f'ERR:{e.errno}\\n')\n" ++
  "    sys.stdout.flush()\n"

private def startPyPwdOracle : IO PyPwdOracle := do
  let child ← IO.Process.spawn {
    cmd := "/usr/bin/python3"
    args := #["-I", "-u", "-c", pyOracleScript]
    env := #[("HOME", some "/tmp"), ("LC_ALL", some "C.UTF-8"), ("PYTHONUTF8", some "1"), ("PYTHONUNBUFFERED", some "1")]
    stdin := .piped
    stdout := .piped
    stderr := .inherit
  }
  let uidCache ← IO.mkRef {}
  let nameCache ← IO.mkRef {}
  return { child := child, uidCache := uidCache, nameCache := nameCache }

private def stopPyPwdOracle (oracle : PyPwdOracle) : IO Unit := do
  try
    oracle.child.stdin.putStr "QUIT\n"
    oracle.child.stdin.flush
  catch _ =>
    pure ()
  try
    let (_, c) ← oracle.child.takeStdin
    let _ ← c.wait
  catch _ =>
    try
      oracle.child.kill
      let _ ← oracle.child.wait
    catch _ =>
      pure ()

private def parsePyLine (line : String) : Except String PyPwdOutcome :=
  let trimmed := line.trimAscii.toString
  if trimmed == "NONE" then
    .ok .notFound
  else if trimmed.startsWith "FOUND:" then
    let rest := (trimmed.drop 6).toString
    match rest.splitOn ":" with
    | [nameHex, uidStr, gidStr, gecosHex, dirHex, shellHex] => do
      let name ← decodeHexBytes nameHex
      let gecos ← decodeHexBytes gecosHex
      let homeDir ← decodeHexBytes dirHex
      let shell ← decodeHexBytes shellHex
      let some uidNat := uidStr.toNat?
        | .error s!"PYTHON_UID_PARSE line={repr trimmed}"
      let some gidNat := gidStr.toNat?
        | .error s!"PYTHON_GID_PARSE line={repr trimmed}"
      return .found {
        name := name
        uid := UInt32.ofNat uidNat
        gid := UInt32.ofNat gidNat
        gecos := gecos
        homeDir := homeDir
        shell := shell
      }
    | _ => .error s!"PYTHON_FOUND_ARITY line={repr trimmed}"
  else if trimmed.startsWith "ERR:" then
    let errStr := (trimmed.drop 4).toString
    match errStr.toNat? with
    | some n => .ok (.err n)
    | none => .error s!"PYTHON_ERRNO_PARSE line={repr trimmed}"
  else
    .error s!"PYTHON_UNEXPECTED_RESPONSE line={repr trimmed}"

private def queryPyUid (oracle : PyPwdOracle) (uid : UInt32) : IO (Except String PyPwdOutcome) := do
  let map ← oracle.uidCache.get
  match map.get? uid with
  | some cached => return .ok cached
  | none =>
    oracle.child.stdin.putStr s!"U:{uid}\n"
    oracle.child.stdin.flush
    let line ← oracle.child.stdout.getLine
    if line.isEmpty then
      return .error s!"PYTHON_ORACLE_EOF uid={uid}"
    match parsePyLine line with
    | .error err => return .error err
    | .ok res =>
      oracle.uidCache.modify (fun m => m.insert uid res)
      return .ok res

private def queryPyName (oracle : PyPwdOracle) (name : ByteArray) : IO (Except String PyPwdOutcome) := do
  if !validPasswdName name then
    return .ok (.err Errno.EINVAL.toNat)
  if name.size > MAX_PASSWD_NAME_BYTES then
    return .ok (.err Errno.ENAMETOOLONG.toNat)
  let map ← oracle.nameCache.get
  match map.get? name with
  | some cached => return .ok cached
  | none =>
    oracle.child.stdin.putStr s!"N:{encodeHexBytes name}\n"
    oracle.child.stdin.flush
    let line ← oracle.child.stdout.getLine
    if line.isEmpty then
      return .error s!"PYTHON_ORACLE_EOF name_len={name.size}"
    match parsePyLine line with
    | .error err => return .error err
    | .ok res =>
      oracle.nameCache.modify (fun m => m.insert name res)
      return .ok res

private def parseProcUidLine (line : String) : Option UInt32 :=
  if line.startsWith "Uid:" then
    let rest := (line.drop 4).toString
    let parts := rest.splitOn "\t" |>.flatMap (fun s => s.splitOn " ")
    let nonEmpty := parts.filter (fun s => !s.isEmpty)
    match nonEmpty with
    | first :: _ => first.toNat?.map UInt32.ofNat
    | [] => none
  else
    none

private def readCurrentUid : IO UInt32 := do
  let content ← IO.FS.readFile "/proc/self/status"
  for line in content.splitOn "\n" do
    match parseProcUidLine line with
    | some uid => return uid
    | none => pure ()
  throw (IO.userError "PASSWD_FUZZ_PROC_STATUS_MISSING_UID")

private def checkEntryUtf8Accessors (e : PasswdEntry) : Except String Unit := do
  if e.nameUtf8? != String.fromUTF8? e.name then
    throw "PASSWD_UTF8_NAME_MISMATCH"
  if e.gecosUtf8? != String.fromUTF8? e.gecos then
    throw "PASSWD_UTF8_GECOS_MISMATCH"
  if e.homeDirUtf8? != String.fromUTF8? e.homeDir then
    throw "PASSWD_UTF8_HOMEDIR_MISMATCH"
  if e.shellUtf8? != String.fromUTF8? e.shell then
    throw "PASSWD_UTF8_SHELL_MISMATCH"
  if !e.hasNoEmbeddedNul then
    throw "PASSWD_ENTRY_EMBEDDED_NUL"

private instance : BEq PasswdState where
  beq a b :=
    a.byUid.toList == b.byUid.toList &&
    a.byName.toList == b.byName.toList &&
    a.ambientSeccomp == b.ambientSeccomp &&
    a.transientNssUnavail == b.transientNssUnavail

private def checkSingleOp (oracle : PyPwdOracle) (state : PasswdState) (hEnv : HealthyEnv)
    (op : PasswdFuzzOp) :
    IO (Except String (PasswdState × HealthyEnv × List CoverageBucket)) := do
  let stepHealthy (req : PasswdReq) (out : PasswdOutcome) (nxtState : PasswdState) :
      Except String HealthyEnv :=
    if !isCriticalFault out then
      match healthyStep hEnv req out with
      | some hEnv' =>
        if !hEnv'.wf then
          .error s!"PASSWD_HEALTHY_WF_VIOLATED op={repr op}"
        else if hEnv'.state != nxtState then
          .error s!"PASSWD_HEALTHY_STATE_DIVERGENCE op={repr op}"
        else if isEintrOutcome out &&
            (hEnv'.eintrBudget + 1 != hEnv.eintrBudget ||
             (healthyStep { hEnv with eintrBudget := 0 } req out).isSome) then
          .error s!"PASSWD_HEALTHY_EINTR_BUDGET_VIOLATED op={repr op}"
        else
          .ok hEnv'
      | none => .error s!"PASSWD_HEALTHY_STEP_MISMATCH op={repr op} out={repr out}"
    else
      if (healthyStep hEnv req out).isSome then
        .error s!"PASSWD_HEALTHY_CRITICAL_ACCEPTED op={repr op} out={repr out}"
      else
        .ok { hEnv with state := nxtState }
  let mut bkts : List CoverageBucket := []
  match op.kind with
  | .getpwuid =>
    let pyRes ← match ← queryPyUid oracle op.uid with
      | .error err => return .error err
      | .ok v => pure v
    let res ← getpwuid op.uid
    let out := outcomeOfEntryOpt res
    let some nxtState := allowedStep state (.getpwuid op.uid) out
      | return .error s!"PASSWD_MODEL_MISMATCH_UID op={repr op} out={repr out}"
    let nxtHealthy ← match stepHealthy (.getpwuid op.uid) out nxtState with
      | .error err => return .error err
      | .ok h' => pure h'
    match res, pyRes with
    | .ok (some entry), .found pyEntry =>
      if entry != pyEntry then
        return .error s!"PASSWD_UID_ENTRY_MISMATCH uid={op.uid} lean={repr entry} py={repr pyEntry}"
      if let .error msg := checkEntryUtf8Accessors entry then
        return .error s!"{msg} uid={op.uid}"
      bkts := bucket "python_oracle" "ok.matched" :: bucket "utf8_accessors" "ok.matched" :: bucket "getpwuid" "ok.found" :: bkts
    | .ok (some entry), other =>
      return .error s!"PASSWD_UID_PHANTOM uid={op.uid} lean={repr entry} py={repr other}"
    | .ok none, .notFound =>
      bkts := bucket "python_oracle" "ok.matched" :: bucket "getpwuid" "ok.not_found" :: bkts
    | .ok none, .found pyEntry =>
      return .error s!"PASSWD_UID_MISSED uid={op.uid} py={repr pyEntry}"
    | .ok none, .err pyErr =>
      return .error s!"PASSWD_UID_VS_PY_ERR uid={op.uid} pyErr={pyErr}"
    | .error e, _ =>
      if !isAllowedPasswdOsErrno e then
        return .error s!"PASSWD_UID_UNEXPECTED_ERRNO uid={op.uid} err={e.name}"
      bkts := bucket "getpwuid" s!"err.{e.name}" :: bkts
    return .ok (nxtState, nxtHealthy, bkts)
  | .getpwnam =>
    if !validPasswdName op.name then
      let res ← getpwnam op.name
      let out := outcomeOfEntryOpt res
      let some nxtState := allowedStep state (.getpwnam op.name) out
        | return .error s!"PASSWD_MODEL_MISMATCH_NAME op={repr op} out={repr out}"
      let nxtHealthy ← match stepHealthy (.getpwnam op.name) out nxtState with
        | .error err => return .error err
        | .ok h' => pure h'
      match res with
      | .error e =>
        if e != Errno.EINVAL then
          return .error s!"PASSWD_NAME_EXPECTED_EINVAL got={e.name}"
        bkts := bucket "getpwnam" "err.EINVAL" :: bkts
      | other =>
        return .error s!"PASSWD_NAME_EXPECTED_EINVAL got={formatResEntry other}"
      return .ok (nxtState, nxtHealthy, bkts)
    else if op.name.size > MAX_PASSWD_NAME_BYTES then
      let res ← getpwnam op.name
      let out := outcomeOfEntryOpt res
      let some nxtState := allowedStep state (.getpwnam op.name) out
        | return .error s!"PASSWD_MODEL_MISMATCH_NAME op={repr op} out={repr out}"
      let nxtHealthy ← match stepHealthy (.getpwnam op.name) out nxtState with
        | .error err => return .error err
        | .ok h' => pure h'
      match res with
      | .error e =>
        if e != Errno.ENAMETOOLONG then
          return .error s!"PASSWD_NAME_EXPECTED_ENAMETOOLONG got={e.name}"
        bkts := bucket "getpwnam" "err.ENAMETOOLONG" :: bkts
      | other =>
        return .error s!"PASSWD_NAME_EXPECTED_ENAMETOOLONG got={formatResEntry other}"
      return .ok (nxtState, nxtHealthy, bkts)
    else
      let pyRes ← match ← queryPyName oracle op.name with
        | .error err => return .error err
        | .ok v => pure v
      let res ← getpwnam op.name
      let out := outcomeOfEntryOpt res
      let some nxtState := allowedStep state (.getpwnam op.name) out
        | return .error s!"PASSWD_MODEL_MISMATCH_NAME op={repr op} out={repr out}"
      let nxtHealthy ← match stepHealthy (.getpwnam op.name) out nxtState with
        | .error err => return .error err
        | .ok h' => pure h'
      match res, pyRes with
      | .ok (some entry), .found pyEntry =>
        if entry != pyEntry then
          return .error s!"PASSWD_NAME_ENTRY_MISMATCH name={formatPasswdBytes op.name} lean={repr entry} py={repr pyEntry}"
        if let .error msg := checkEntryUtf8Accessors entry then
          return .error s!"{msg} name={formatPasswdBytes op.name}"
        bkts := bucket "python_oracle" "ok.matched" :: bucket "utf8_accessors" "ok.matched" :: bucket "getpwnam" "ok.found" :: bkts
      | .ok (some entry), other =>
        return .error s!"PASSWD_NAME_PHANTOM name={formatPasswdBytes op.name} lean={repr entry} py={repr other}"
      | .ok none, .notFound =>
        bkts := bucket "python_oracle" "ok.matched" :: bucket "getpwnam" "ok.not_found" :: bkts
      | .ok none, .found pyEntry =>
        return .error s!"PASSWD_NAME_MISSED name={formatPasswdBytes op.name} py={repr pyEntry}"
      | .ok none, .err pyErr =>
        return .error s!"PASSWD_NAME_VS_PY_ERR name={formatPasswdBytes op.name} pyErr={pyErr}"
      | .error e, _ =>
        if !isAllowedPasswdOsErrno e then
          return .error s!"PASSWD_NAME_UNEXPECTED_ERRNO err={e.name}"
        bkts := bucket "getpwnam" s!"err.{e.name}" :: bkts
      return .ok (nxtState, nxtHealthy, bkts)

private def checkTrace (oracle : PyPwdOracle) (trace : Array PasswdFuzzOp) :
    IO (Except String (List CoverageBucket)) := do
  let mut state := PasswdState.initial
  let mut hEnv : HealthyEnv := { state := PasswdState.initial, eintrBudget := trace.size }
  let mut bkts : List CoverageBucket := []
  for op in trace do
    match ← checkSingleOp oracle state hEnv op with
    | .error err => return .error err
    | .ok (nxtState, nxtHealthy, stepBkts) =>
      state := nxtState
      hEnv := nxtHealthy
      bkts := stepBkts ++ bkts
  return .ok bkts

private def errorClass (err : String) : String :=
  err.splitOn " " |>.headD err

private def shrinkToFixedPoint (curUid : UInt32) (fails : Array PasswdFuzzOp → IO Bool)
    (trace : Array PasswdFuzzOp) : IO (Array PasswdFuzzOp) := do
  let mut cur ← shrinkTrace fails trace
  for _ in List.range 32 do
    let shrunkEl ← shrinkElements (shrinkPasswdFuzzOp curUid) fails cur
    let nxt ← shrinkTrace fails shrunkEl
    if nxt == cur then
      break
    cur := nxt
  return cur

private def runTraceChecked (curUid : UInt32) (oracle : PyPwdOracle)
    (tracker : CoverageTracker) (trace : Array PasswdFuzzOp) : IO CoverageTracker := do
  match ← checkTrace oracle trace with
  | .ok bkts =>
    let mut tr := tracker
    for b in bkts do
      tr := tr.record b.op b.bucket
    return tr
  | .error err =>
    if err.startsWith "PYTHON_ORACLE_EOF" then
      throw (IO.userError s!"PASSWD_FUZZ_MISMATCH err={err} trace_size={trace.size}")
    let targetClass := errorClass err
    let fails (cand : Array PasswdFuzzOp) : IO Bool := do
      match ← checkTrace oracle cand with
      | .ok _ => return false
      | .error e =>
        if e.startsWith "PYTHON_ORACLE_EOF" then
          throw (IO.userError e)
        return errorClass e == targetClass
    let shrunk ← shrinkToFixedPoint curUid fails trace
    let shrunkErr := match ← checkTrace oracle shrunk with
      | .error e => e
      | .ok _ => err
    throw (IO.userError s!"PASSWD_FUZZ_MISMATCH err={shrunkErr} original_err={err} shrunk={repr shrunk}")

private def bigName65537 : ByteArray :=
  ByteArray.mk (Array.replicate 65537 (UInt8.ofNat 'a'.toNat))

private def overCapName1048577 : ByteArray :=
  ByteArray.mk (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) (UInt8.ofNat 'a'.toNat))

private def runInternalStep (curUid : UInt32) (curName : ByteArray)
    (tracker : CoverageTracker) (rng : Rng) : IO (CoverageTracker × Rng) := do
  let mut tr := tracker
  let (useNameCheck, r1) := rng.nextBool
  if useNameCheck then
    let nulName := ByteArray.mk #[97, 0, 98]
    let resNul ← defaultOps.getpwnam nulName
    let some _ := allowedStep PasswdState.initial (.getpwnam nulName) (outcomeOfEntryOpt resNul)
      | throw (IO.userError s!"DEFAULTOPS_NUL_MODEL_MISMATCH got={formatResEntry resNul}")
    match resNul with
    | .error e =>
      if e != Errno.EINVAL then
        throw (IO.userError s!"DEFAULTOPS_NUL_EXPECTED_EINVAL got={e.name}")
      tr := tr.record "getpwnam" "err.EINVAL"
    | .ok _ =>
      throw (IO.userError "DEFAULTOPS_NUL_SUCCEEDED")
    let resBig ← defaultOps.getpwnam bigName65537
    let some _ := allowedStep PasswdState.initial (.getpwnam bigName65537) (outcomeOfEntryOpt resBig)
      | throw (IO.userError s!"DEFAULTOPS_65537_MODEL_MISMATCH got={formatResEntry resBig}")
    if let .error e := resBig then
      if e == Errno.EINVAL || !isAllowedPasswdOsErrno e then
        throw (IO.userError s!"DEFAULTOPS_65537_BAD_ERRNO got={e.name}")
    let resOver ← defaultOps.getpwnam overCapName1048577
    let some _ := allowedStep PasswdState.initial (.getpwnam overCapName1048577) (outcomeOfEntryOpt resOver)
      | throw (IO.userError s!"DEFAULTOPS_OVERCAP_MODEL_MISMATCH got={formatResEntry resOver}")
    match resOver with
    | .error e =>
      if e != Errno.ENAMETOOLONG then
        throw (IO.userError s!"NAM_OVERCAP_EXPECTED_ENAMETOOLONG got={e.name}")
      tr := tr.record "getpwnam" "err.ENAMETOOLONG"
    | .ok _ =>
      throw (IO.userError "NAM_OVERCAP_SUCCEEDED")
  else
    let resUid ← defaultOps.getpwuid curUid
    let some _ := allowedStep PasswdState.initial (.getpwuid curUid) (outcomeOfEntryOpt resUid)
      | throw (IO.userError s!"DEFAULTOPS_UID_MODEL_MISMATCH got={formatResEntry resUid}")
    let resNam ← defaultOps.getpwnam curName
    let some _ := allowedStep PasswdState.initial (.getpwnam curName) (outcomeOfEntryOpt resNam)
      | throw (IO.userError s!"DEFAULTOPS_NAM_MODEL_MISMATCH got={formatResEntry resNam}")
  let cutoffs : Array UInt32 := #[4096, 8192, 16384, 32768, 65536, 65537]
  let (cutIdx, r2) := r1.nextNat cutoffs.size
  let cutoff := cutoffs.getD cutIdx 8192
  let (corruptKind, r3) := r2.nextNat 5
  let badUtf8 := ByteArray.mk #[0x2F, 0xFF, 0xFE, 0x80]
  let shell := ByteArray.mk #[47, 98, 105, 110, 47, 115, 104]
  let mockOps := Internal.mkPasswdOps {
    getpwuidOnce := fun uid sz => do
      if sz < cutoff then
        return .error Errno.ERANGE
      else if corruptKind == 0 then
        return .ok (some (curName, uid + 1, 100, ByteArray.empty, badUtf8, shell))
      else if corruptKind == 1 then
        return .ok (some (curName, uid, 100, ByteArray.mk #[97, 0, 98], badUtf8, shell))
      else
        return .ok (some (curName, uid, 100, ByteArray.empty, badUtf8, shell))
    getpwnamOnce := fun nm sz => do
      if sz < cutoff then
        return .error Errno.ERANGE
      else if corruptKind == 0 then
        return .ok (some (nm.push 120, 0, 0, ByteArray.empty, badUtf8, shell))
      else if corruptKind == 1 then
        return .ok (some (nm, 0, 0, ByteArray.empty, badUtf8, ByteArray.mk #[47, 0]))
      else
        return .ok (some (nm, 0, 0, ByteArray.empty, badUtf8, shell))
  }
  let (useNamMock, r4) := r3.nextBool
  let req := if useNamMock then PasswdReq.getpwnam (asciiName "mockuser") else PasswdReq.getpwuid curUid
  let res ← if useNamMock then mockOps.getpwnam (asciiName "mockuser") else mockOps.getpwuid curUid
  let mockOut := outcomeOfEntryOpt res
  let some _ := allowedStep PasswdState.initial req mockOut
    | throw (IO.userError s!"INTERNAL_MOCK_MODEL_MISMATCH cutoff={cutoff} corrupt={corruptKind} got={formatResEntry res}")
  let hInit := HealthyEnv.initial 1
  if (corruptKind == 0 || corruptKind == 1) && cutoff <= 65536 then
    if !isCriticalFault mockOut || (healthyStep hInit req mockOut).isSome then
      throw (IO.userError s!"INTERNAL_MOCK_EIO_NOT_REJECTED_BY_HEALTHY got={formatResEntry res}")
  else
    if isCriticalFault mockOut || (healthyStep hInit req mockOut).isNone then
      throw (IO.userError s!"INTERNAL_MOCK_HEALTHY_STEP_REJECTED cutoff={cutoff} corrupt={corruptKind} got={formatResEntry res}")
  if (healthyStep hInit req (.err Errno.EMFILE)).isNone ||
      (healthyStep hInit req (.err Errno.ENOMEM)).isSome ||
      (healthyStep hInit req (.err Errno.ENFILE)).isSome then
    throw (IO.userError "PASSWD_HEALTHY_CRITICAL_SPLIT_BROKEN")
  let (hOut, hEnvAfter) := (execPasswdReq healthyModelOps req).run hInit
  let (mOut, mSt) := (execPasswdReq modelOps req).run hInit.state
  let stEq := hEnvAfter.state.byUid.toList == mSt.byUid.toList &&
    hEnvAfter.state.byName.toList == mSt.byName.toList &&
    hEnvAfter.state.ambientSeccomp == mSt.ambientSeccomp &&
    hEnvAfter.state.transientNssUnavail == mSt.transientNssUnavail
  if hOut != mOut || !stEq || (healthyStep hInit req hOut).isNone ||
      hEnvAfter.eintrBudget != 1 || !hEnvAfter.wf then
    throw (IO.userError "PASSWD_HEALTHY_MODEL_OPS_VIOLATED")
  let badNamReq := PasswdReq.getpwnam (ByteArray.mk #[97, 0, 98])
  let (badHOut, badHEnv) := (execPasswdReq healthyModelOps badNamReq).run hInit
  let (badMOut, _) := (execPasswdReq modelOps badNamReq).run hInit.state
  if badHOut != badMOut || badHOut != .err Errno.EINVAL || !badHEnv.wf || badHEnv.eintrBudget != 1 then
    throw (IO.userError "PASSWD_HEALTHY_MODEL_OPS_INVALID_NAME_VIOLATED")
  match res with
  | .ok (some entry) =>
    if cutoff > 4096 then
      tr := tr.record "erange_retry" "ok.retried"
    if entry.homeDirUtf8?.isNone then
      tr := tr.record "utf8_accessors" "ok.non_utf8_none"
    if let .error msg := checkEntryUtf8Accessors entry then
      throw (IO.userError msg)
  | .ok none =>
    throw (IO.userError "INTERNAL_MOCK_UNEXPECTED_NONE")
  | .error e =>
    if cutoff > 65536 && e == Errno.ERANGE then
      tr := tr.record "erange_retry" "err.ERANGE"
    else if (corruptKind == 0 || corruptKind == 1) && e == Errno.EIO then
      tr := tr.record "postcondition" "err.EIO"
    else
      throw (IO.userError s!"INTERNAL_MOCK_UNEXPECTED_ERR cutoff={cutoff} corrupt={corruptKind} e={e.name}")
  return (tr, r4)

private def runConcurrencyCheck (oracle : PyPwdOracle) (seedVal : UInt64)
    (curUid : UInt32) (curName : ByteArray) : IO Unit := do
  let uids : Array UInt32 := #[curUid, 0, 65534, 0xFFFFFFFE, 0x7FFFFFFF]
  let names : Array ByteArray := #[curName, asciiName "root", asciiName "no_such_user_xyz", ByteArray.mk #[97, 0, 98]]
  let mut expUid : List (UInt32 × PyPwdOutcome) := []
  for u in uids do
    match ← queryPyUid oracle u with
    | .error err => throw (IO.userError s!"PASSWD_CONCURRENCY_UID_ORACLE_ERR uid={u} err={err}")
    | .ok py => expUid := (u, py) :: expUid
  let mut expNam : List (ByteArray × PyPwdOutcome) := []
  for n in names do
    match ← queryPyName oracle n with
    | .error err => throw (IO.userError s!"PASSWD_CONCURRENCY_NAME_ORACLE_ERR err={err}")
    | .ok py => expNam := (n, py) :: expNam
  let uidStep := 1 + (seedVal % 3).toNat
  let namStep := 1 + ((seedVal >>> 8) % 3).toNat
  let worker (workerId : Nat) : IO (Except String Unit) := do
    for iter in List.range 16 do
      let u := uids.getD ((workerId + iter * uidStep + seedVal.toNat) % uids.size) curUid
      let expU := match expUid.find? (fun p => p.1 == u) with
        | some p => p.2
        | none => .notFound
      match ← getpwuid u, expU with
      | .ok (some e), .found pyE =>
        if e != pyE then
          return .error s!"THREAD_UID_MISMATCH w={workerId} u={u}"
      | .ok none, .notFound => pure ()
      | .error e, _ =>
        if !isAllowedPasswdOsErrno e then
          return .error s!"THREAD_UID_ERR w={workerId} u={u} e={e.name}"
      | other, _ =>
        return .error s!"THREAD_UID_OTHER w={workerId} u={u} got={formatResEntry other}"
      let n := names.getD ((workerId + iter * namStep + (seedVal >>> 4).toNat) % names.size) curName
      let resN ← getpwnam n
      if !validPasswdName n then
        if !isErrnoRes Errno.EINVAL resN then
          return .error s!"THREAD_NAME_EINVAL w={workerId} got={formatResEntry resN}"
      else
        let expN := match expNam.find? (fun p => p.1 == n) with
          | some p => p.2
          | none => .notFound
        match resN, expN with
        | .ok (some e), .found pyE =>
          if e != pyE then
            return .error s!"THREAD_NAME_MISMATCH w={workerId}"
        | .ok none, .notFound => pure ()
        | .error e, _ =>
          if !isAllowedPasswdOsErrno e then
            return .error s!"THREAD_NAME_ERR w={workerId} e={e.name}"
        | other, _ =>
          return .error s!"THREAD_NAME_OTHER w={workerId} got={formatResEntry other}"
    return .ok ()
  let mut tasks : Array (Task (Except IO.Error (Except String Unit))) := #[]
  for wid in List.range 8 do
    let t ← IO.asTask (worker wid) (prio := .dedicated)
    tasks := tasks.push t
  for t in tasks do
    match t.get with
    | .error ioErr => throw ioErr
    | .ok (.error msg) => throw (IO.userError s!"PASSWD_CONCURRENCY_FAIL {msg}")
    | .ok (.ok ()) => pure ()

private def hasRegularEtcPasswd : IO Bool := do
  let p : System.FilePath := "/etc/passwd"
  try
    let md ← p.metadata
    if md.type != .file then
      return false
    let raw ← IO.FS.readBinFile p
    let mut lineLen := 0
    for b in raw.data do
      if b == 10 then
        if lineLen >= 65536 then
          return false
        lineLen := 0
      else
        lineLen := lineLen + 1
    return lineLen < 65536
  catch _ =>
    return false

private def requiredPasswdBuckets (hasPasswdFile : Bool) : Array CoverageBucket :=
  let base : Array CoverageBucket := #[
    bucket "getpwnam" "err.EINVAL",
    bucket "getpwnam" "err.ENAMETOOLONG",
    bucket "utf8_accessors" "ok.non_utf8_none",
    bucket "erange_retry" "ok.retried",
    bucket "erange_retry" "err.ERANGE",
    bucket "postcondition" "err.EIO",
    bucket "concurrency" "ok.tsan_tasks"
  ]
  if hasPasswdFile then
    base ++ #[
      bucket "getpwuid" "ok.found",
      bucket "getpwuid" "ok.not_found",
      bucket "getpwnam" "ok.found",
      bucket "getpwnam" "ok.not_found",
      bucket "python_oracle" "ok.matched",
      bucket "utf8_accessors" "ok.matched"
    ]
  else
    base

private def runPasswdOsBoundaryChecks (curUid : UInt32) : IO Unit := do
  for warmNss in [false, true] do
    let (waitSt, payload) ← Fuzz.LinuxSyscall.SandboxEnv.runForked do
      let mut s := PasswdState.initial.withTransientNssUnavail
      let mut h := HealthyEnv.initial 16
      if warmNss then
        for u in ([9999999, 0, 1, curUid] : List UInt32) do
          let o := outcomeOfEntryOpt (← getpwuid u)
          let some s' := allowedStep s (.getpwuid u) o
            | return (s!"warm allowedStep uid={u} failed: {repr o}").toUTF8
          s := s'
          if !isCriticalFault o then
            let some h' := healthyStep h (.getpwuid u) o
              | return (s!"warm healthyStep uid={u} failed: {repr o}").toUTF8
            h := h'
        for nm in [asciiName "root", asciiName "daemon"] do
          let o := outcomeOfEntryOpt (← getpwnam nm)
          let some s' := allowedStep s (.getpwnam nm) o
            | return (s!"warm allowedStep nam failed: {repr o}").toUTF8
          s := s'
          if !isCriticalFault o then
            let some h' := healthyStep h (.getpwnam nm) o
              | return (s!"warm healthyStep nam failed: {repr o}").toUTF8
            h := h'
      let (_, maxNofile) ← match ← Fuzz.LinuxSyscall.SandboxEnv.getRlimit 2 with
        | .ok p => pure p
        | .error e => return (s!"getRlimit failed: {e}").toUTF8
      let safeHigh := if maxNofile > 64 then 64 else maxNofile
      match ← LeanSwe.LinuxSyscall.Sandbox.setrlimit .nofile 0 safeHigh with
      | .ok () => pure ()
      | .error e => return (s!"setrlimit nofile 0 failed: {e}").toUTF8
      for u in ([0, 1, curUid, 9999999] : List UInt32) do
        let o := outcomeOfEntryOpt (← getpwuid u)
        if isCriticalFault o then
          return (s!"RLIMIT_NOFILE=0 uid={u} critical fault: {repr o}").toUTF8
        let some s' := allowedStep s (.getpwuid u) o
          | return (s!"RLIMIT_NOFILE=0 allowedStep uid={u} failed: {repr o}").toUTF8
        let some h' := healthyStep h (.getpwuid u) o
          | return (s!"RLIMIT_NOFILE=0 healthyStep uid={u} failed: {repr o}").toUTF8
        if !h'.wf then
          return (s!"RLIMIT_NOFILE=0 wf violated uid={u}").toUTF8
        s := s'
        h := h'
      for nm in [asciiName "root", asciiName "daemon", ByteArray.mk #[97, 0, 98], overCapName1048577] do
        let o := outcomeOfEntryOpt (← getpwnam nm)
        if isCriticalFault o then
          return (s!"RLIMIT_NOFILE=0 nam sz={nm.size} critical fault: {repr o}").toUTF8
        let some s' := allowedStep s (.getpwnam nm) o
          | return (s!"RLIMIT_NOFILE=0 allowedStep nam sz={nm.size} failed: {repr o}").toUTF8
        let some h' := healthyStep h (.getpwnam nm) o
          | return (s!"RLIMIT_NOFILE=0 healthyStep nam sz={nm.size} failed: {repr o}").toUTF8
        if !h'.wf then
          return (s!"RLIMIT_NOFILE=0 wf violated nam sz={nm.size}").toUTF8
        s := s'
        h := h'
      return "OK".toUTF8
    let msg := (String.fromUTF8? payload).getD "invalid UTF-8"
    if waitSt != 0 || msg != "OK" then
      throw (IO.userError s!"PASSWD_RLIMIT_NOFILE_PARITY_FAILED warm={warmNss} status={waitSt} msg={msg}")

private def runPasswdSuite (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  let regPasswd ← hasRegularEtcPasswd
  let curUid ← readCurrentUid
  runPasswdOsBoundaryChecks curUid
  let curName ← match ← getpwuid curUid with
    | .ok (some e) => pure e.name
    | _ => pure (asciiName "root")
  let oracle ← startPyPwdOracle
  try
    let mut tracker := CoverageTracker.empty
    if isSmoke then
      let corpus := smokeCorpus curUid curName
      let bounded := corpus.extract 0 (min steps corpus.size)
      let epSize := 16
      let mut idx := 0
      while idx < bounded.size do
        let stop := min bounded.size (idx + epSize)
        tracker ← runTraceChecked curUid oracle tracker (bounded.extract idx stop)
        idx := stop
    let mut rng := Rng.seed seedVal
    let mut done := 0
    while done < steps do
      let (epLenRaw, r1) := rng.nextRange 8 24
      rng := r1
      let epLen := min epLenRaw (steps - done)
      let mut trace : Array PasswdFuzzOp := Array.mkEmpty epLen
      for _ in List.range epLen do
        let (op, rN) := genPasswdFuzzOp curUid curName rng
        rng := rN
        trace := trace.push op
      tracker ← runTraceChecked curUid oracle tracker trace
      let (trNext, rInt) ← runInternalStep curUid curName tracker rng
      tracker := trNext
      rng := rInt
      done := done + epLen
    let internalSteps := min steps 120
    for _ in List.range internalSteps do
      let (trNext, rInt) ← runInternalStep curUid curName tracker rng
      tracker := trNext
      rng := rInt
    if steps ≥ 8 then
      runConcurrencyCheck oracle seedVal curUid curName
      tracker := tracker.record "concurrency" "ok.tsan_tasks"
    assertCoverage "passwd" tracker (requiredPasswdBuckets regPasswd)
    IO.println s!"PASSWD_FUZZ_PASS mode={if isSmoke then "smoke" else "fuzz"} steps={steps} seed={seedVal} curUid={curUid} total={tracker.total}"
    IO.println (tracker.formatReport "passwd")
  finally
    stopPyPwdOracle oracle

private def passwdShrinkSelfTest (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let curUid ← readCurrentUid
  let curName := asciiName "root"
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut trace : Array PasswdFuzzOp := Array.mkEmpty 24
  for _ in List.range 24 do
    let (op, r') := genPasswdFuzzOp curUid curName rng
    rng := r'
    trace := trace.push op
  let (badIdx, rA) := rng.nextNat trace.size
  trace := trace.set! badIdx { kind := .getpwnam, uid := 0x12345678, name := ByteArray.mk #[97, 98, 0, 99] }
  let isNulFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op => op.kind == .getpwnam && !validPasswdName op.name)
  match ← verifyShrinker isNulFault trace 1 with
  | .error msg => throw (IO.userError s!"PASSWD_SHRINK_NUL_FAILED: {msg}")
  | .ok shrunk1 =>
    let shrunk ← shrinkToFixedPoint curUid isNulFault shrunk1
    if shrunk.size != 1 then
      throw (IO.userError s!"PASSWD_SHRINK_NUL_SIZE: got {shrunk.size}")
    match shrunk[0]? with
    | some op =>
      if op.kind != .getpwnam || op.name != ByteArray.mk #[0] then
        throw (IO.userError s!"PASSWD_SHRINK_NUL_ITEM: got {repr op}")
    | none =>
      throw (IO.userError "PASSWD_SHRINK_NUL_EMPTY")
  let (uidIdx, rB) := rA.nextNat trace.size
  let uidTrace := trace.set! uidIdx { kind := .getpwuid, uid := 5000, name := ByteArray.empty }
  let isUidFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op => op.kind == .getpwuid && op.uid ≥ 500)
  let shrunkUid ← shrinkToFixedPoint curUid isUidFault uidTrace
  if shrunkUid.size != 1 then
    throw (IO.userError s!"PASSWD_SHRINK_UID_SIZE: got {shrunkUid.size}")
  match shrunkUid[0]? with
  | some op =>
    if op.kind != .getpwuid || op.uid != 500 then
      throw (IO.userError s!"PASSWD_SHRINK_UID_ITEM: expected uid=500 got {repr op}")
  | none =>
    throw (IO.userError "PASSWD_SHRINK_UID_EMPTY")
  let binTrace : Array PasswdFuzzOp :=
    #[{ kind := .getpwuid, uid := 0x80000000, name := ByteArray.empty }]
  let isHighUidFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op => op.kind == .getpwuid && op.uid ≥ 0x40000001)
  let tStartUid ← IO.monoMsNow
  let shrunkBinUid ← shrinkToFixedPoint curUid isHighUidFault binTrace
  let tElapsedUid := (← IO.monoMsNow) - tStartUid
  if tElapsedUid > 500 then
    throw (IO.userError s!"PASSWD_SHRINK_BINUID_SLOW: elapsed_ms={tElapsedUid}")
  if shrunkBinUid.size != 1 then
    throw (IO.userError s!"PASSWD_SHRINK_BINUID_SIZE: got {shrunkBinUid.size}")
  match shrunkBinUid[0]? with
  | some op =>
    if op.kind != .getpwuid || op.uid != 0x40000001 then
      throw (IO.userError s!"PASSWD_SHRINK_BINUID_ITEM: expected 0x40000001 got {repr op}")
  | none =>
    throw (IO.userError "PASSWD_SHRINK_BINUID_EMPTY")
  let hugeBa := (ByteArray.mk (Array.replicate 32768 (UInt8.ofNat 'a'.toNat))).push 0xFF ++
    ByteArray.mk (Array.replicate 32768 (UInt8.ofNat 'a'.toNat))
  let baTrace : Array PasswdFuzzOp :=
    #[{ kind := .getpwnam, uid := curUid, name := hugeBa }]
  let isSentinelFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op => op.kind == .getpwnam && op.name.data.contains 0xFF)
  let tStartBa ← IO.monoMsNow
  let shrunkBa ← shrinkToFixedPoint curUid isSentinelFault baTrace
  let tElapsedBa := (← IO.monoMsNow) - tStartBa
  if tElapsedBa > 500 then
    throw (IO.userError s!"PASSWD_SHRINK_BIGBA_SLOW: elapsed_ms={tElapsedBa}")
  if shrunkBa.size != 1 then
    throw (IO.userError s!"PASSWD_SHRINK_BIGBA_SIZE: got {shrunkBa.size}")
  match shrunkBa[0]? with
  | some op =>
    if op.kind != .getpwnam || op.name != ByteArray.mk #[0xFF] then
      throw (IO.userError s!"PASSWD_SHRINK_BIGBA_ITEM: expected #[0xFF] got {repr op}")
  | none =>
    throw (IO.userError "PASSWD_SHRINK_BIGBA_EMPTY")
  let twoEndBa := (ByteArray.mk #[UInt8.ofNat 'x'.toNat] ++
    ByteArray.mk (Array.replicate 65535 (UInt8.ofNat 'a'.toNat))).push 0xFF
  let twoEndTrace : Array PasswdFuzzOp :=
    #[{ kind := .getpwnam, uid := curUid, name := twoEndBa }]
  let isTwoEndFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op =>
      op.kind == .getpwnam && op.name.size ≥ 2 &&
      op.name[0]! == UInt8.ofNat 'x'.toNat && op.name[op.name.size - 1]! == 0xFF)
  let tStartTwoEnd ← IO.monoMsNow
  let shrunkTwoEnd ← shrinkToFixedPoint curUid isTwoEndFault twoEndTrace
  let tElapsedTwoEnd := (← IO.monoMsNow) - tStartTwoEnd
  if tElapsedTwoEnd > 500 then
    throw (IO.userError s!"PASSWD_SHRINK_TWOEND_SLOW: elapsed_ms={tElapsedTwoEnd}")
  if shrunkTwoEnd.size != 1 then
    throw (IO.userError s!"PASSWD_SHRINK_TWOEND_SIZE: got {shrunkTwoEnd.size}")
  match shrunkTwoEnd[0]? with
  | some op =>
    if op.kind != .getpwnam || op.name != ByteArray.mk #[UInt8.ofNat 'x'.toNat, 0xFF] then
      throw (IO.userError s!"PASSWD_SHRINK_TWOEND_ITEM: expected #[x, 0xFF] got {repr op}")
  | none =>
    throw (IO.userError "PASSWD_SHRINK_TWOEND_EMPTY")
  let (i1, rC) := rB.nextNat 12
  let i2 := 12 + (rC.nextNat 12).1
  let multiTrace := (trace.set! i1 { kind := .getpwuid, uid := 777, name := ByteArray.empty }).set!
    i2 { kind := .getpwnam, uid := curUid, name := asciiName "bad_target" }
  let isMultiFault (xs : Array PasswdFuzzOp) : IO Bool :=
    return xs.any (fun op => op.kind == .getpwuid && op.uid == 777) &&
      xs.any (fun op => op.kind == .getpwnam && !op.name.isEmpty)
  let shrunkMulti ← shrinkToFixedPoint curUid isMultiFault multiTrace
  if shrunkMulti.size != 2 then
    throw (IO.userError s!"PASSWD_SHRINK_MULTI_SIZE: got {shrunkMulti.size}")
  let classifyDual (xs : Array PasswdFuzzOp) : Option String :=
    if xs.any (fun op => op.kind == .getpwnam && op.name.size ≥ 2) then some "CLASS_B"
    else if xs.any (fun op => op.kind == .getpwuid && op.uid == 9999) then some "CLASS_A"
    else none
  let dualTrace := (trace.set! 0 { kind := .getpwuid, uid := 9999, name := ByteArray.empty }).set!
    (trace.size - 1) { kind := .getpwnam, uid := curUid, name := asciiName "abcdef" }
  let isClassB (xs : Array PasswdFuzzOp) : IO Bool :=
    return classifyDual xs == some "CLASS_B"
  let shrunkPinned ← shrinkToFixedPoint curUid isClassB dualTrace
  if shrunkPinned.size != 1 || classifyDual shrunkPinned != some "CLASS_B" then
    throw (IO.userError s!"PASSWD_SHRINK_PINNED_FAIL: got {repr shrunkPinned}")
  match shrunkPinned[0]? with
  | some op =>
    if op.kind != .getpwnam || op.name.size != 2 then
      throw (IO.userError s!"PASSWD_SHRINK_PINNED_ITEM: got {repr op}")
  | none =>
    throw (IO.userError "PASSWD_SHRINK_PINNED_EMPTY")

/-- Differential fuzzing suite for `LeanSwe.LinuxSyscall.Passwd` against `Passwd.Model` and Python `pwd.getpwuid` / `pwd.getpwnam`. -/
def suite : FuzzSuite :=
  { name := "passwd"
    description := "Differential fuzzing of LinuxSyscall.Passwd (getpwuid, getpwnam, PasswdEntry UTF-8 accessors) against stateful NSS model, Python pwd (-I), and multi-threaded task checks"
    runSmoke := fun cfg => do
      Fuzz.Passwd.Checks.runChecks
      let actual := min cfg.steps 200
      Fuzz.Common.recordSuiteSteps actual
      runPasswdSuite actual cfg.seed true
    runFuzz := fun cfg => do
      if ← Fuzz.Common.isCoverageLogActive then
        Fuzz.Passwd.Checks.runChecks
      Fuzz.Common.recordSuiteSteps cfg.steps
      runPasswdSuite cfg.steps cfg.seed false
    selfTestShrink := passwdShrinkSelfTest }

end Fuzz.Passwd
