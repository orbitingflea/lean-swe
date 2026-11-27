import Std.Data.HashMap
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import Fuzz.Dns.Gen
import Fuzz.Dns.Checks
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSweProofs.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Sandbox.Interface
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.Dns

open Fuzz.Common
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

private def pythonOracleScript : String :=
  String.intercalate "\n" [
    "import socket, sys",
    "fam_map = {0: socket.AF_UNSPEC, 1: socket.AF_INET, 2: socket.AF_INET6}",
    "sock_map = {0: 0, 1: socket.SOCK_STREAM, 2: socket.SOCK_DGRAM}",
    "while True:",
    "    raw = sys.stdin.readline()",
    "    if not raw:",
    "        break",
    "    line = raw.strip()",
    "    if line == 'QUIT':",
    "        break",
    "    if not line.startswith('HEX:'):",
    "        continue",
    "    parts = line[4:].split(':', 2)",
    "    if len(parts) != 3:",
    "        print('ERR -2', flush=True)",
    "        continue",
    "    fam_code = fam_map.get(int(parts[0]), socket.AF_UNSPEC)",
    "    sock_code = sock_map.get(int(parts[1]), socket.SOCK_STREAM)",
    "    try:",
    "        host_bytes = bytes.fromhex(parts[2])",
    "    except Exception:",
    "        print('ERR -2', flush=True)",
    "        continue",
    "    if (not host_bytes) or (b'\\x00' in host_bytes):",
    "        print('ERR -2', flush=True)",
    "        continue",
    "    try:",
    "        infos = socket.getaddrinfo(host_bytes, None, fam_code, sock_code)",
    "        out = bytearray()",
    "        for fam, _, _, _, sockaddr in infos:",
    "            if fam == socket.AF_INET:",
    "                out.append(4)",
    "                out.extend(socket.inet_pton(socket.AF_INET, sockaddr[0]))",
    "                out.extend(b'\\x00' * 16)",
    "            elif fam == socket.AF_INET6:",
    "                ip_str = sockaddr[0].split('%', 1)[0]",
    "                sc = sockaddr[3] if len(sockaddr) >= 4 else 0",
    "                out.append(6)",
    "                out.extend(socket.inet_pton(socket.AF_INET6, ip_str))",
    "                out.extend(int(sc).to_bytes(4, 'little'))",
    "        print('OK:' + out.hex(), flush=True)",
    "    except socket.gaierror as e:",
    "        code = e.errno if e.errno is not None else -2",
    "        print(f'ERR {code}', flush=True)",
    "    except (ValueError, UnicodeError):",
    "        print('ERR -2', flush=True)"
  ]

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def bytesToHex (bs : ByteArray) : String := Id.run do
  let mut chars : Array Char := Array.mkEmpty (bs.size * 2)
  for b in bs.data do
    let v := b.toNat
    chars := chars.push (hexChar (v / 16))
    chars := chars.push (hexChar (v % 16))
  return String.ofList chars.toList

private def hexVal (c : Char) : Option UInt8 :=
  if '0' <= c && c <= '9' then
    some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' <= c && c <= 'f' then
    some (UInt8.ofNat (10 + c.toNat - 'a'.toNat))
  else if 'A' <= c && c <= 'F' then
    some (UInt8.ofNat (10 + c.toNat - 'A'.toNat))
  else
    none

private def hexToBytes (s : String) : Except String ByteArray := do
  let chars := s.toList
  if chars.length % 2 != 0 then
    throw s!"odd hex length {chars.length}"
  let mut out := ByteArray.emptyWithCapacity (chars.length / 2)
  let mut rest := chars
  while !rest.isEmpty do
    match rest with
    | hi :: lo :: tail =>
      match hexVal hi, hexVal lo with
      | some hVal, some lVal =>
        out := out.push ((hVal <<< 4) ||| lVal)
        rest := tail
      | _, _ => throw "invalid hex character"
    | _ => throw "odd hex length"
  return out

private inductive PyDnsReply where
  | ok (addrs : List DnsAddr)
  | err (gaiCode : Int32)
  deriving Repr, DecidableEq, BEq, Inhabited

private abbrev OracleChild :=
  IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

private def spawnPythonOracle : IO OracleChild :=
  IO.Process.spawn {
    cmd := "python3"
    args := #["-I", "-B", "-u", "-c", pythonOracleScript]
    stdin := .piped
    stdout := .piped
    stderr := .inherit
  }

private def queryPythonOracle (child : OracleChild) (host : String) (hints : ResolveHints) :
    IO PyDnsReply := do
  let famWire := hints.family.toWire.toNat
  let sockWire := hints.sockType.toWire.toNat
  let hexReq := s!"HEX:{famWire}:{sockWire}:{bytesToHex host.toUTF8}"
  child.stdin.putStrLn hexReq
  child.stdin.flush
  let line ← child.stdout.getLine
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "OK:" then
    let hexPayload := (trimmed.drop 3).toString
    match hexToBytes hexPayload with
    | .error msg => throw (IO.userError s!"PYTHON_ORACLE_HEX_DECODE_FAILED: {msg}")
    | .ok bs =>
      match Internal.decodeRecords bs with
      | .error e => throw (IO.userError s!"PYTHON_ORACLE_RECORD_DECODE_FAILED: {e.message}")
      | .ok addrs => return .ok addrs
  else if trimmed.startsWith "ERR " then
    let codeStr := (trimmed.drop 4).toString
    match codeStr.toInt? with
    | none => throw (IO.userError s!"PYTHON_ORACLE_ERR_PARSE_FAILED: {trimmed}")
    | some codeInt => return .err (Int32.ofInt codeInt)
  else
    throw (IO.userError s!"PYTHON_ORACLE_BAD_REPLY: {trimmed}")

private def closePythonOracle (child : OracleChild) : IO Unit := do
  try
    child.stdin.putStrLn "QUIT"
    child.stdin.flush
  catch _ =>
    pure ()
  let _ ← child.wait

private def addrMultisetEq (a b : List DnsAddr) : Bool :=
  if a.length != b.length then
    false
  else
    let countAddrs (xs : List DnsAddr) : Std.HashMap DnsAddr Nat :=
      xs.foldl (fun acc x => acc.insert x (acc.getD x 0 + 1)) {}
    let ca := countAddrs a
    let cb := countAddrs b
    ca.size == cb.size &&
      ca.fold (fun ok k n => ok && cb.getD k 0 == n) true

private structure DnsMismatch where
  tag : String
  detail : String
  deriving Repr, DecidableEq, BEq

private def evalProbeAgainstOracle (ops : DnsOps) (child : OracleChild) (probe : DnsProbe) :
    IO (Option DnsMismatch) := do
  let pyReply ← queryPythonOracle child probe.host probe.hints
  let leanRes ← ops.getaddrinfo probe.host probe.hints
  if !allowedDnsOutcome probe.host probe.hints leanRes then
    return some {
      tag := "DNS_ALLOWED_OUTCOME_VIOLATED"
      detail := s!"host={repr probe.host} hints={repr probe.hints} res={repr leanRes}"
    }
  let req : DnsReq := { host := probe.host, hints := probe.hints }
  if (allowedStep DnsState.initial req leanRes).isNone then
    return some {
      tag := "DNS_ALLOWED_STEP_VIOLATED"
      detail := s!"host={repr probe.host} hints={repr probe.hints} res={repr leanRes}"
    }
  if isCriticalFault leanRes then
    if (healthyStep (HealthyEnv.initial 1) req leanRes).isSome then
      return some {
        tag := "DNS_HEALTHY_ACCEPTED_CRITICAL"
        detail := s!"host={repr probe.host} hints={repr probe.hints} res={repr leanRes}"
      }
  else if (healthyStep (HealthyEnv.initial 1) req leanRes).isNone then
    return some {
      tag := "DNS_HEALTHY_STEP_VIOLATED"
      detail := s!"host={repr probe.host} hints={repr probe.hints} res={repr leanRes}"
    }
  if !validateHost probe.host then
    match leanRes with
    | .error e =>
      if e.kind != .invalidHost || e.gaiCode != EAI_NONAME || e.errno? != some Errno.EINVAL then
        return some {
          tag := "DNS_INVALID_HOST_MISMATCH"
          detail := s!"host={repr probe.host} err={repr e}"
        }
    | .ok addrs =>
      return some {
        tag := "DNS_INVALID_HOST_ACCEPTED"
        detail := s!"host={repr probe.host} addrs={repr addrs}"
      }
  match pyReply, leanRes with
  | .ok pyAddrs, .ok leanAddrs =>
    if !addrMultisetEq pyAddrs leanAddrs then
      return some {
        tag := "DNS_ADDR_MISMATCH"
        detail := s!"host={repr probe.host} hints={repr probe.hints} py={repr pyAddrs} lean={repr leanAddrs}"
      }
    if probe.host.contains '%' && probe.hints.family != .ipv4 &&
        pyAddrs.any (fun a => a.isIpv6 && !a.isUnscoped) then
      if leanAddrs.isEmpty || !leanAddrs.any (fun a => a.isIpv6 && !a.isUnscoped) then
        return some {
          tag := "DNS_SCOPED_IPV6_LOST"
          detail := s!"host={repr probe.host} lean={repr leanAddrs}"
        }
    return none
  | .err pyCode, .error e =>
    if e.kind == .invalidHost && validateHost probe.host then
      return some {
        tag := "DNS_UNEXPECTED_INVALID_HOST"
        detail := s!"host={repr probe.host} err={repr e}"
      }
    if pyCode != e.gaiCode then
      return some {
        tag := "DNS_GAI_CODE_MISMATCH"
        detail := s!"host={repr probe.host} hints={repr probe.hints} pyCode={pyCode} err={repr e}"
      }
    return none
  | .ok pyAddrs, .error e =>
    return some {
      tag := "DNS_PY_OK_LEAN_ERR"
      detail := s!"host={repr probe.host} hints={repr probe.hints} py={repr pyAddrs} err={repr e}"
    }
  | .err pyCode, .ok leanAddrs =>
    return some {
      tag := "DNS_PY_ERR_LEAN_OK"
      detail := s!"host={repr probe.host} hints={repr probe.hints} pyCode={pyCode} lean={repr leanAddrs}"
    }

private def evalTraceWithTag (ops : DnsOps) (child : OracleChild) (expectedTag : String)
    (trace : Array DnsProbe) : IO Bool := do
  for p in trace do
    if let some mm ← evalProbeAgainstOracle ops child p then
      if mm.tag == expectedTag then
        return true
  return false

private def shrinkAndFail (ops : DnsOps) (child : OracleChild) (trace : Array DnsProbe)
    (mm : DnsMismatch) : IO Unit := do
  let failsPinned := evalTraceWithTag ops child mm.tag
  let minTrace ← shrinkTrace failsPinned trace
  let shrunk ← shrinkElements shrinkProbe failsPinned minTrace
  let shrunkDetail ← match shrunk[0]? with
    | some p =>
      match ← evalProbeAgainstOracle ops child p with
      | some m => pure m.detail
      | none => pure mm.detail
    | none => pure mm.detail
  throw (IO.userError s!"{mm.tag}: shrunk_size={shrunk.size} shrunk={repr shrunk} detail={shrunkDetail}")

private def checkCodecStep (rng : Rng) : IO Rng := do
  let (addrs, r1) := genDnsAddrs rng
  let encoded := Internal.encodeRecords addrs
  if encoded.size != addrs.length * Internal.DNS_RECORD_SIZE then
    throw (IO.userError s!"DNS_CODEC_SIZE_MISMATCH expected={addrs.length * Internal.DNS_RECORD_SIZE} got={encoded.size}")
  match Internal.decodeRecords encoded with
  | .error e =>
    throw (IO.userError s!"DNS_CODEC_ROUNDTRIP_ERR {repr e}")
  | .ok decoded =>
    if decoded != addrs then
      throw (IO.userError s!"DNS_CODEC_ROUNDTRIP_MISMATCH addrs={repr addrs} decoded={repr decoded}")
  let (badBytes, r2) := genCorruptPayload r1
  match Internal.decodeRecords badBytes with
  | .ok addrs' =>
    throw (IO.userError s!"DNS_CORRUPT_DECODE_ACCEPTED bytes={badBytes.size} addrs={repr addrs'}")
  | .error e =>
    if e.kind != .otherGai || e.gaiCode != EAI_OVERFLOW then
      throw (IO.userError s!"DNS_CORRUPT_WRONG_KIND {repr e}")
  return r2

private def exceptDnsEq (a b : Except DnsError (List DnsAddr)) : Bool :=
  match a, b with
  | .ok xs, .ok ys => xs == ys
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def checkModelStep (rng : Rng) : IO Rng := do
  let (probe, r1) := genFastProbe rng
  let (mockAddrs, r2) := genDnsAddrs r1
  let (mode, r3) := r2.nextNat 5
  let (rawCode, r4) := r3.choose #[0, 42, EAI_NONAME, EAI_AGAIN, EAI_FAIL, EAI_SYSTEM, EAI_MEMORY, EAI_ADDRFAMILY, EAI_SERVICE] 0
  let (rawErrno, r5) := r4.choose #[0, Errno.EINVAL, Errno.ENOMEM, Errno.EFAULT] 0
  let (msgStr, r6) := r5.choose #["", "mock oracle failure"] ""
  let oracle : DnsOracle := {
    lookup := fun _ _ =>
      if mode == 0 then
        .ok []
      else if mode == 1 then
        .ok mockAddrs
      else if mode == 2 then
        .ok [.ipv4 127 0 0 1, .ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0]
      else
        .error {
          kind := if rawCode == 0 then .otherGai else .invalidHost
          gaiCode := rawCode
          errno? := if rawErrno == 0 then none else some rawErrno
          message := msgStr
        }
  }
  let resModel := modelResolve oracle probe.host probe.hints
  if !allowedDnsOutcome probe.host probe.hints resModel then
    throw (IO.userError s!"DNS_MODEL_OUTCOME_VIOLATED probe={repr probe} res={repr resModel}")
  let (resOps, _) := (modelOps.getaddrinfo probe.host probe.hints).run oracle
  if !exceptDnsEq resOps resModel then
    throw (IO.userError s!"DNS_MODEL_OPS_DIVERGENCE probe={repr probe} ops={repr resOps} model={repr resModel}")
  let hEnv0 : HealthyEnv := { state := { oracle := oracle, ambientSeccomp := false }, eintrBudget := 1 }
  let (resHealthy, hEnv1) := (healthyModelOps.getaddrinfo probe.host probe.hints).run hEnv0
  let expectExactModel := resModel.isOk ||
    ((parsePureNumericAddr? probe.host).isNone &&
      (parseHybridScopedNumericZone? probe.host).isNone &&
      !isCriticalFault resModel && !isEintrOutcome resModel)
  let stepOk := match healthyStep hEnv0 { host := probe.host, hints := probe.hints } resHealthy with
    | some hNext =>
      hNext.eintrBudget == hEnv1.eintrBudget &&
        hNext.state.ambientSeccomp == hEnv1.state.ambientSeccomp
    | none => false
  if !stepOk || !hEnv1.wf || hEnv1.eintrBudget != hEnv0.eintrBudget ||
      !exceptDnsEq resHealthy (healthyModelResolve oracle probe.host probe.hints) ||
      (expectExactModel && !exceptDnsEq resHealthy resModel) then
    throw (IO.userError s!"DNS_HEALTHY_MODEL_OPS_VIOLATED probe={repr probe} res={repr resHealthy}")
  let checkDefaultOfflineReal (host : String) (allowAgain : Bool) : IO Unit := do
    let mRes := modelResolve defaultOfflineOracle host probe.hints
    if !allowedDnsOutcome host probe.hints mRes then
      throw (IO.userError s!"DNS_OFFLINE_ORACLE_VIOLATED host={repr host} hints={repr probe.hints} res={repr mRes}")
    let realOff ← getaddrinfo host probe.hints
    let isSymbolicScopedCand := match parseScopedNonNumericZone? host with
      | some (baseAddr, zoneCs) => canSymbolicScopedOk probe.hints baseAddr zoneCs
      | none => false
    match mRes, realOff with
    | .ok xs, .ok ys =>
      if (parseHybridScopedNumericZone? host).isSome || isSymbolicScopedCand then
        if !allowedDnsOutcome host probe.hints realOff ||
            (healthyStep (HealthyEnv.initial 1) { host := host, hints := probe.hints } realOff).isNone then
          throw (IO.userError s!"DNS_MODEL_REAL_HYBRID_MISMATCH host={repr host} hints={repr probe.hints} real={repr ys}")
      else if !addrMultisetEq xs ys then
        throw (IO.userError s!"DNS_MODEL_REAL_ADDR_MISMATCH host={repr host} hints={repr probe.hints} model={repr xs} real={repr ys}")
    | .error e1, .error e2 =>
      if !(allowAgain && e2.gaiCode == EAI_AGAIN) then
        if e1.gaiCode != e2.gaiCode || e1.kind != e2.kind then
          throw (IO.userError s!"DNS_MODEL_REAL_ERR_MISMATCH host={repr host} hints={repr probe.hints} model={repr e1} real={repr e2}")
    | .error _, .ok ys =>
      if isSymbolicScopedCand then
        if !allowedDnsOutcome host probe.hints realOff ||
            (healthyStep (HealthyEnv.initial 1) { host := host, hints := probe.hints } realOff).isNone then
          throw (IO.userError s!"DNS_MODEL_REAL_SCOPED_IFACE_MISMATCH host={repr host} hints={repr probe.hints} real={repr ys}")
      else
        throw (IO.userError s!"DNS_MODEL_REAL_STATUS_MISMATCH host={repr host} hints={repr probe.hints} model={repr mRes} real={repr realOff}")
    | _, _ =>
      throw (IO.userError s!"DNS_MODEL_REAL_STATUS_MISMATCH host={repr host} hints={repr probe.hints} model={repr mRes} real={repr realOff}")
  if !probe.slowLookup && probe.kind != .loopbackHost then
    let allowAgain := probe.kind == .malformedLiteral && !probe.host.startsWith "fe80::1%"
    checkDefaultOfflineReal probe.host allowAgain
  let (offHost, r7) := r6.choose #[
    "127.0.0.1", "0.0.0.0", "0x7f.0.0.1", "::1", "::", "::ffff:127.0.0.1",
    "fe80::1%lo", "::1%lo", "2001:db8::1%lo", "ff02::1%lo", "fe80::1%", "fe80::1%a%b",
    "::ffff:127.0.0.1%lo", "fe80::1%305419896", "fe80::1%noiface999",
    "localhost", "LOCALHOST", "localhost.", "nonexistent.invalid.", "", "a\x00b"
  ] "127.0.0.1"
  let offRes := modelResolve defaultOfflineOracle offHost probe.hints
  if !allowedDnsOutcome offHost probe.hints offRes then
    throw (IO.userError s!"DNS_OFFLINE_ORACLE_VIOLATED host={repr offHost} hints={repr probe.hints} res={repr offRes}")
  if offHost != "localhost" && offHost != "LOCALHOST" && offHost != "localhost." &&
      offHost != "nonexistent.invalid." then
    checkDefaultOfflineReal offHost false
  return r7

private def checkFormatRoundtripPair (addr : DnsAddr) (fmt : String) (hints : ResolveHints) : IO Unit := do
  let expected := expandSockType hints [addr]
  let res ← getaddrinfo fmt hints
  match res with
  | .error e =>
    throw (IO.userError s!"DNS_FORMAT_ROUNDTRIP_ERR addr={repr addr} fmt={fmt} hints={repr hints} err={repr e}")
  | .ok addrs =>
    if (parseHybridScopedNumericZone? fmt).isSome then
      if !allowedDnsOutcome fmt hints res ||
          (healthyStep (HealthyEnv.initial 1) { host := fmt, hints := hints } res).isNone then
        throw (IO.userError s!"DNS_FORMAT_ROUNDTRIP_HYBRID_MISMATCH fmt={fmt} got={repr addrs} hints={repr hints}")
    else if !addrMultisetEq expected addrs then
      throw (IO.userError s!"DNS_FORMAT_ROUNDTRIP_MISMATCH expected={repr expected} got={repr addrs} hints={repr hints}")
  let mRes := modelResolve defaultOfflineOracle fmt hints
  match mRes with
  | .error e =>
    throw (IO.userError s!"DNS_FORMAT_MODEL_ROUNDTRIP_ERR addr={repr addr} fmt={fmt} hints={repr hints} err={repr e}")
  | .ok addrs =>
    if !addrMultisetEq expected addrs then
      throw (IO.userError s!"DNS_FORMAT_MODEL_ROUNDTRIP_MISMATCH expected={repr expected} got={repr addrs} hints={repr hints}")

private def checkFormatRoundtripStep (rng : Rng) : IO Rng := do
  let (addr, r1) := genDnsAddr rng
  if let .ipv6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc := addr then
    if sc != 0 then
      let fmtScoped := addr.format
      if !fmtScoped.endsWith s!"%{sc}" then
        throw (IO.userError s!"DNS_FORMAT_SCOPE_SUFFIX_MISSING fmt={fmtScoped} sc={sc}")
      for h in [{ family := .ipv6, sockType := .stream }, { family := .ipv6, sockType := .any }, { family := .any, sockType := .any }] do
        checkFormatRoundtripPair addr fmtScoped h
  let unscopedAddr := match addr with
    | .ipv4 .. => addr
    | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 _ =>
      .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 0
  let fam : AddrFamilyHint := if unscopedAddr.isIpv4 then .ipv4 else .ipv6
  for h in [{ family := fam, sockType := .stream }, { family := fam, sockType := .any }, { family := .any, sockType := .any }] do
    checkFormatRoundtripPair unscopedAddr unscopedAddr.format h
  return r1

private def checkMockedImplStep (rng : Rng) : IO Rng := do
  let (probe, r1) := genFastProbe rng
  let (mode, r2) := r1.nextNat 5
  let (rawCode, r3) := r2.choose #[0, 42, EAI_NONAME, EAI_AGAIN, EAI_FAIL, EAI_SYSTEM, EAI_MEMORY, EAI_ADDRFAMILY, EAI_BADFLAGS, EAI_SERVICE] 0
  let (rawEno, r4) := r3.choose #[0, Errno.EINVAL, Errno.ENOMEM, Errno.EFAULT, 0x7fffffff] 0
  let (msgMode, r5) := r4.nextNat 3
  let msgBytes :=
    if msgMode == 0 then ByteArray.empty
    else if msgMode == 1 then ByteArray.mk #[0xff, 0xfe, 0x80]
    else "mock fail".toUTF8
  let raw : Internal.PosixDnsOps := {
    getaddrinfo := fun _ _ _ => do
      if mode == 0 then
        return .ok ByteArray.empty
      else if mode == 1 then
        let wrongFamAddr : DnsAddr :=
          if probe.hints.family == .ipv4 then .ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
          else .ipv4 127 0 0 1
        return .ok (Internal.encodeRecords [wrongFamAddr])
      else if mode == 2 then
        let matchingAddr : DnsAddr :=
          if probe.hints.family == .ipv6 then .ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
          else .ipv4 127 0 0 1
        let wrongFamAddr : DnsAddr :=
          if probe.hints.family == .ipv4 then .ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
          else .ipv4 127 0 0 1
        return .ok (Internal.encodeRecords [matchingAddr, wrongFamAddr])
      else if mode == 3 then
        return .ok (ByteArray.mk #[7, 1, 2, 3])
      else
        return .error (rawCode, rawEno, msgBytes)
  }
  let res ← (Internal.mkDnsOps raw).getaddrinfo probe.host probe.hints
  if !allowedDnsOutcome probe.host probe.hints res then
    throw (IO.userError s!"DNS_MOCKED_IMPL_VIOLATED probe={repr probe} res={repr res}")
  let req : DnsReq := { host := probe.host, hints := probe.hints }
  if (allowedStep DnsState.initial.withOuterSeccomp req res).isNone then
    throw (IO.userError s!"DNS_MOCKED_SECCOMP_STEP_VIOLATED probe={repr probe} res={repr res}")
  if (healthyStep { state := DnsState.initial.withOuterSeccomp, eintrBudget := 1 } req res).isSome then
    throw (IO.userError s!"DNS_MOCKED_HEALTHY_SECCOMP_ACCEPTED probe={repr probe} res={repr res}")
  if isCriticalFault res && (healthyStep (HealthyEnv.initial 1) req res).isSome then
    throw (IO.userError s!"DNS_MOCKED_HEALTHY_CRITICAL_ACCEPTED probe={repr probe} res={repr res}")
  return r5

private def runConcurrentBatch (child : OracleChild) (rng : Rng) : IO Rng := do
  let (extra1, r1) := genFastProbe rng
  let (extra2, r2) := genFastProbe r1
  let (extra3, r3) := genFastProbe r2
  let probes : Array DnsProbe := #[
    { kind := .ipv4Literal, host := "127.0.0.1", hints := { family := .ipv4, sockType := .stream } },
    { kind := .ipv6Literal, host := "::1", hints := { family := .ipv6, sockType := .dgram } },
    { kind := .ipv4Literal, host := "127.0.0.1", hints := { family := .ipv6, sockType := .stream } },
    { kind := .ipv6Literal, host := "::1", hints := { family := .ipv4, sockType := .dgram } },
    { kind := .scopedIpv6, host := "fe80::1%lo", hints := { family := .ipv6, sockType := .stream } },
    { kind := .emptyHost, host := "", hints := {} },
    { kind := .embeddedNul, host := "a\x00b", hints := {} },
    extra1,
    extra2,
    extra3
  ]
  let mut expected : Array PyDnsReply := Array.mkEmpty probes.size
  for p in probes do
    expected := expected.push (← queryPythonOracle child p.host p.hints)
  let mut tasks : Array (Task (Except IO.Error (Except DnsError (List DnsAddr)))) := Array.mkEmpty probes.size
  for p in probes do
    let t ← IO.asTask (prio := .dedicated) (getaddrinfo p.host p.hints)
    tasks := tasks.push t
  for idx in List.range probes.size do
    let p := probes[idx]!
    let pyReply : PyDnsReply := expected[idx]!
    let leanRes ← IO.ofExcept (← IO.wait tasks[idx]!)
    if !allowedDnsOutcome p.host p.hints leanRes then
      throw (IO.userError s!"DNS_CONCURRENT_OUTCOME_VIOLATED host={repr p.host} hints={repr p.hints} res={repr leanRes}")
    let req : DnsReq := { host := p.host, hints := p.hints }
    if (allowedStep DnsState.initial req leanRes).isNone then
      throw (IO.userError s!"DNS_CONCURRENT_ALLOWED_STEP_VIOLATED host={repr p.host} hints={repr p.hints} res={repr leanRes}")
    if !isCriticalFault leanRes && (healthyStep (HealthyEnv.initial 1) req leanRes).isNone then
      throw (IO.userError s!"DNS_CONCURRENT_HEALTHY_STEP_VIOLATED host={repr p.host} hints={repr p.hints} res={repr leanRes}")
    match pyReply, leanRes with
    | PyDnsReply.ok pyAddrs, Except.ok leanAddrs =>
      if !addrMultisetEq pyAddrs leanAddrs then
        throw (IO.userError s!"DNS_CONCURRENT_ADDR_MISMATCH host={repr p.host} hints={repr p.hints} py={repr pyAddrs} lean={repr leanAddrs}")
      if p.kind == .scopedIpv6 && p.hints.family != .ipv4 &&
          pyAddrs.any (fun a => a.isIpv6 && !a.isUnscoped) then
        if leanAddrs.isEmpty || !leanAddrs.any (fun a => a.isIpv6 && !a.isUnscoped) then
          throw (IO.userError s!"DNS_CONCURRENT_SCOPED_LOST host={repr p.host} lean={repr leanAddrs}")
    | PyDnsReply.err pyCode, Except.error e =>
      if pyCode != e.gaiCode then
        throw (IO.userError s!"DNS_CONCURRENT_GAI_MISMATCH host={repr p.host} hints={repr p.hints} pyCode={pyCode} err={repr e}")
    | _, _ =>
      throw (IO.userError s!"DNS_CONCURRENT_STATUS_MISMATCH host={repr p.host} hints={repr p.hints} py={repr pyReply} lean={repr leanRes}")
  return r3

private def requiredBuckets : Array CoverageBucket := #[
  bucket "dns" "ipv4_literal",
  bucket "dns" "ipv6_literal",
  bucket "dns" "loopback_host",
  bucket "dns" "scoped_ipv6",
  bucket "dns" "empty_host",
  bucket "dns" "embedded_nul",
  bucket "dns" "long_hostname",
  bucket "dns" "malformed_literal",
  bucket "dns" "invalid_domain",
  bucket "hints" "family_any",
  bucket "hints" "family_ipv4",
  bucket "hints" "family_ipv6",
  bucket "hints" "sock_any",
  bucket "hints" "sock_stream",
  bucket "hints" "sock_dgram",
  bucket "hints_cross" "ipv4:stream",
  bucket "hints_cross" "ipv6:dgram",
  bucket "hints_cross" "any:any",
  bucket "codec" "roundtrip_ok",
  bucket "codec" "corrupt_err",
  bucket "model" "oracle_ok",
  bucket "model" "format_ok",
  bucket "model" "mocked_ok",
  bucket "concurrent" "batch_ok"
]

private def recordHintBuckets (tracker : CoverageTracker) (h : ResolveHints) : CoverageTracker :=
  let famStr := match h.family with
    | .any => "any"
    | .ipv4 => "ipv4"
    | .ipv6 => "ipv6"
  let sockStr := match h.sockType with
    | .any => "any"
    | .stream => "stream"
    | .dgram => "dgram"
  tracker
    |>.record "hints" s!"family_{famStr}"
    |>.record "hints" s!"sock_{sockStr}"
    |>.record "hints_cross" s!"{famStr}:{sockStr}"

private def deterministicWarmupProbes : Array DnsProbe := #[
  { kind := .ipv4Literal, host := "127.0.0.1", hints := { family := .ipv4, sockType := .stream } },
  { kind := .ipv6Literal, host := "::1", hints := { family := .ipv6, sockType := .stream } },
  { kind := .ipv4Literal, host := "127.0.0.1", hints := { family := .ipv6, sockType := .stream } },
  { kind := .ipv6Literal, host := "::1", hints := { family := .ipv4, sockType := .dgram } },
  { kind := .ipv4Literal, host := "0.0.0.0", hints := { family := .any, sockType := .any } },
  { kind := .ipv6Literal, host := "::", hints := { family := .ipv6, sockType := .dgram } },
  { kind := .loopbackHost, host := "localhost", hints := { family := .any, sockType := .stream } },
  { kind := .scopedIpv6, host := "fe80::1%lo", hints := { family := .ipv6, sockType := .stream } },
  { kind := .scopedIpv6, host := "fe80::1%00", hints := { family := .ipv6, sockType := .stream } },
  { kind := .scopedIpv6, host := "::1%00", hints := { family := .any, sockType := .stream } },
  { kind := .scopedIpv6, host := "fe80::1%0000000000000001", hints := { family := .ipv6, sockType := .stream } },
  { kind := .scopedIpv6, host := "fe80::1%305419896", hints := { family := .any, sockType := .dgram } },
  { kind := .emptyHost, host := "" },
  { kind := .embeddedNul, host := "a\x00b" },
  { kind := .malformedLiteral, host := "bad host" },
  { kind := .malformedLiteral, host := "999.999.999.999.", slowLookup := true },
  { kind := .invalidDomain, host := "nonexistent.invalid.", slowLookup := true }
]

private def runDnsOsBoundaryChecks (seedVal : UInt64) : IO Unit := do
  let (waitSt, payload) ← Fuzz.LinuxSyscall.SandboxEnv.runForked do
    let (_, curMaxNofile) ← match ← Fuzz.LinuxSyscall.SandboxEnv.getRlimit 2 with
      | .ok p => pure p
      | .error e => return (s!"getRlimit failed: {e}").toUTF8
    let safeHigh := if curMaxNofile > 64 then 64 else curMaxNofile
    match ← LeanSwe.LinuxSyscall.Sandbox.setrlimit .nofile 0 safeHigh with
    | .ok () => pure ()
    | .error _ => return "setrlimit nofile 0 failed".toUTF8
    let mustOk : List (String × ResolveHints) := [
      ("127.0.0.1", {}),
      ("0177.0.0.1", { family := .ipv4, sockType := .any }),
      ("::1", { family := .ipv6, sockType := .stream }),
      ("::ffff:127.0.0.1", { family := .ipv4, sockType := .stream }),
      ("fe80::1%1", { family := .ipv6, sockType := .stream }),
      ("fe80::1%0", { family := .any, sockType := .stream }),
      ("fe80::1%305419896", { family := .any, sockType := .dgram }),
      ("2001:db8::1%305419896", { family := .ipv6, sockType := .stream })
    ]
    for (h, hints) in mustOk do
      let r ← getaddrinfo h hints
      match r with
      | .error e => return (s!"RLIMIT_NOFILE=0 numeric {h} failed: {repr e}").toUTF8
      | .ok _ =>
        if (healthyStep (HealthyEnv.initial 1) { host := h, hints := hints } r).isNone then
          return (s!"RLIMIT_NOFILE=0 numeric {h} rejected by healthyStep").toUTF8
    for h in ["fe80::1%lo", "localhost", "nonexistent.invalid."] do
      let r ← getaddrinfo h {}
      if isCriticalFault r then
        return (s!"RLIMIT_NOFILE=0 {h} triggered critical fault: {repr r}").toUTF8
      if (healthyStep (HealthyEnv.initial 1) { host := h, hints := {} } r).isNone then
        return (s!"RLIMIT_NOFILE=0 {h} rejected by healthyStep: {repr r}").toUTF8
    return "OK".toUTF8
  let msg := (String.fromUTF8? payload).getD "invalid UTF-8"
  if waitSt != 0 || msg != "OK" then
    throw (IO.userError s!"DNS_RLIMIT_NOFILE_PARITY_FAILED status={waitSt} msg={msg}")
  let inSub ← IO.getEnv "LEANSWE_DNS_IN_NETNS_SUBCHECK"
  if inSub != some "1" then
    let probe ← IO.Process.output {
      cmd := "unshare"
      args := #["-r", "-n", "sh", "-c", "ip link add name 305419896 type dummy"]
    }
    if probe.exitCode == 0 then
      let exe ← IO.appPath
      let sub ← IO.Process.output {
        cmd := "unshare"
        args := #[
          "-r", "-n", "sh", "-c",
          "for iface in 305419896 99 0 00 000000305419896 4294967296; do ip link add name \"$iface\" type dummy || exit 1; done && LEANSWE_DNS_IN_NETNS_SUBCHECK=1 exec \"$1\" --suite dns --steps 120 --seed \"$2\"",
          "_", exe.toString, toString seedVal.toNat
        ]
      }
      if sub.exitCode != 0 then
        throw (IO.userError s!"DNS_NETNS_NUMERIC_IFACE_SUBCHECK_FAILED exit={sub.exitCode} stdout={sub.stdout} stderr={sub.stderr}")

private def runDnsDiffFuzz (steps : Nat) (seedVal : UInt64) (slowBudget : Nat) (slowEveryN : Nat) : IO Unit := do
  runDnsOsBoundaryChecks seedVal
  let child ← spawnPythonOracle
  try
    let mut warmupTracker := CoverageTracker.empty
    for p in deterministicWarmupProbes do
      if let some mm ← evalProbeAgainstOracle defaultOps child p then
        shrinkAndFail defaultOps child #[p] mm
      warmupTracker := warmupTracker.record "dns" p.kind.bucketName
      warmupTracker := recordHintBuckets warmupTracker p.hints
    let mut tracker := CoverageTracker.empty
    let mut rng := Rng.seed seedVal
    rng ← runConcurrentBatch child rng
    tracker := tracker.record "concurrent" "batch_ok"
    let mut history : Array DnsProbe := Array.mkEmpty 64
    let mut slowRemaining := slowBudget
    for stepIdx in List.range steps do
      let (pickSlow, r1) := rng.chance 1 slowEveryN
      rng := r1
      let (probe, r2) :=
        if stepIdx < 3 && slowRemaining > 0 then
          genSlowProbeBucket stepIdx rng
        else if (pickSlow || stepIdx < 6) && slowRemaining > 0 then
          genSlowProbe rng
        else
          genFastProbe rng
      rng := r2
      if probe.slowLookup then
        slowRemaining := slowRemaining - 1
      if history.size >= 64 then
        history := history.extract 1 history.size
      history := history.push probe
      if let some mm ← evalProbeAgainstOracle defaultOps child probe then
        shrinkAndFail defaultOps child history mm
      tracker := tracker.record "dns" probe.kind.bucketName
      tracker := recordHintBuckets tracker probe.hints
      rng ← checkCodecStep rng
      tracker := tracker.record "codec" "roundtrip_ok"
      tracker := tracker.record "codec" "corrupt_err"
      rng ← checkModelStep rng
      tracker := tracker.record "model" "oracle_ok"
      rng ← checkFormatRoundtripStep rng
      tracker := tracker.record "model" "format_ok"
      rng ← checkMockedImplStep rng
      tracker := tracker.record "model" "mocked_ok"
      if stepIdx % 2500 == 2499 then
        rng ← runConcurrentBatch child rng
        tracker := tracker.record "concurrent" "batch_ok"
    if steps >= 120 then
      assertCoverage "dns" tracker requiredBuckets
    IO.println (warmupTracker.formatReport "dns_warmup")
    IO.println (tracker.formatReport "dns")
    IO.println s!"FUZZ_SUMMARY suite=dns steps={steps} seed={seedVal}"
  finally
    closePythonOracle child

/-- Verify generic delta-shrinking, real probe-checker shrinking, `shrinkElements shrinkProbe`, mismatch-class pinning, and decoy resistance. -/
def runDnsSelfTestShrink (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let child ← spawnPythonOracle
  try
    let combinedOps : DnsOps := {
      getaddrinfo := fun host hints => do
        match ← getaddrinfo host hints with
        | .ok addrs =>
          return .ok (addrs.map fun
            | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 _ =>
              .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 0
            | other => other)
        | .error e =>
          let swapped := if e.gaiCode == EAI_NONAME && validateHost host then EAI_AGAIN else e.gaiCode
          return .error { e with kind := classifyGaiKind swapped, gaiCode := swapped }
    }
    let mut rng := Rng.seed (seedVal ^^^ 0xa5a5a5a55a5a5a5a)
    let mut trace : Array DnsProbe := Array.mkEmpty 12
    while trace.size < 10 do
      let (p, r') := genFastProbe rng
      rng := r'
      if !p.host.contains '%' then
        if (← evalProbeAgainstOracle combinedOps child p).isNone then
          trace := trace.push p
    let (insertAt, _) := rng.nextRange 0 trace.size
    let prefixArr := trace.extract 0 insertAt
    let suffixArr := trace.extract insertAt trace.size
    let failingProbe : DnsProbe := {
      kind := .scopedIpv6
      host := "fe80::2%lo"
      hints := { family := .ipv6, sockType := .dgram }
    }
    let decoyProbe : DnsProbe := {
      kind := .malformedLiteral
      host := "bad host"
      hints := { family := .any, sockType := .stream }
    }
    let injected := (prefixArr.push failingProbe) ++ #[decoyProbe] ++ suffixArr
    let failsScoped := evalTraceWithTag combinedOps child "DNS_ALLOWED_OUTCOME_VIOLATED"
    if ← evalTraceWithTag combinedOps child "DNS_ALLOWED_OUTCOME_VIOLATED" (trace ++ #[decoyProbe]) then
      throw (IO.userError "DNS_SHRINK_DECOY_MATCHED: unrelated error triggered pinned tag")
    if !(← evalTraceWithTag combinedOps child "DNS_GAI_CODE_MISMATCH" (trace ++ #[decoyProbe])) then
      throw (IO.userError "DNS_SHRINK_DECOY_INACTIVE: combined ops failed to trigger decoy tag")
    let shrunkTrace ← match ← verifyShrinker failsScoped injected 1 with
      | .error msg => throw (IO.userError s!"DNS_SHRINK_FAILED: {msg}")
      | .ok s => pure s
    let shrunkElem ← shrinkElements shrinkProbe failsScoped shrunkTrace
    if !(← failsScoped shrunkElem) then
      throw (IO.userError s!"DNS_SHRINK_LOST_FAILURE: shrunk={repr shrunkElem}")
    match shrunkElem.toList with
    | [p] =>
      if p.kind != .scopedIpv6 || p.hints != {} || p.host != "fe80::1%lo" then
        throw (IO.userError s!"DNS_SHRINK_NOT_MINIMAL: got {repr p}")
      let numProbe : DnsProbe := {
        kind := .scopedIpv6
        host := "fe80::1%305419896"
        hints := { family := .ipv6, sockType := .dgram }
      }
      let failsNumAllowed := evalTraceWithTag combinedOps child "DNS_ALLOWED_OUTCOME_VIOLATED"
      let shrunkNum ← shrinkElements shrinkProbe failsNumAllowed #[numProbe]
      match shrunkNum.toList with
      | [pn] =>
        if pn.hints != {} || pn.host != "fe80::1%1" then
          throw (IO.userError s!"DNS_NUMERIC_SCOPE_SHRINK_NOT_MINIMAL: got {repr pn}")
        let zonePred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] =>
            match q.host.splitOn "%" with
            | [_, z] => match z.toNat? with | some n => n >= 7 | none => false
            | _ => false
          | _ => false
        let z7 ← shrinkElements shrinkProbe zonePred #[{ kind := .scopedIpv6, host := "fe80::2%999" }]
        if z7.toList != [{ kind := .scopedIpv6, host := "fe80::1%7" }] then
          throw (IO.userError s!"DNS_ZONE_BISECT_NOT_MINIMAL: got {repr z7}")
        let z0 ← shrinkElements shrinkProbe (fun arr => pure <| match arr.toList with
          | [q] => q.kind == .scopedIpv6 && (q.host == "fe80::1%0" || q.host == "fe80::1%1" || q.host == "fe80::2%1")
          | _ => false) #[{ kind := .scopedIpv6, host := "fe80::2%1" }]
        if z0.toList != [{ kind := .scopedIpv6, host := "fe80::1%0" }] then
          throw (IO.userError s!"DNS_ZONE_ZERO_SHRINK_NOT_MINIMAL: got {repr z0}")
        let long289 : String :=
          let lbl := String.ofList (List.replicate 60 'a')
          s!"{lbl}.{lbl}.{lbl}.{lbl}.aaaaa.invalid."
        let longPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .longHostname && q.host.length > 255
          | _ => false
        let sLong ← shrinkElements shrinkProbe longPred #[{ kind := .longHostname, host := long289 }]
        match sLong.toList with
        | [ql] =>
          if ql.host.length != 256 then
            throw (IO.userError s!"DNS_LONG_SHRINK_NOT_MINIMAL: len={ql.host.length} host={ql.host}")
        | _ => throw (IO.userError s!"DNS_LONG_SHRINK_BAD_LEN: {repr sLong}")
        let multiPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .invalidDomain && q.host.endsWith ".invalid." && q.host.length >= 10
          | _ => false
        let sMulti ← shrinkElements shrinkProbe multiPred #[{ kind := .invalidDomain, host := "alpha.beta.gamma.delta.invalid." }]
        match sMulti.toList with
        | [qm] =>
          if !qm.host.endsWith ".invalid." || qm.host.length != 10 then
            throw (IO.userError s!"DNS_MULTILABEL_SHRINK_NOT_MINIMAL: got {repr qm}")
        | _ => throw (IO.userError s!"DNS_MULTILABEL_SHRINK_BAD_LEN: got {repr sMulti}")
        let nulPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .embeddedNul && q.host.contains (Char.ofNat 0) && q.host.contains '.'
          | _ => false
        let sNul ← shrinkElements shrinkProbe nulPred #[{ kind := .embeddedNul, host := "127.0.0.1\x00" }]
        if sNul.toList != [{ kind := .embeddedNul, host := ".\x00" }] then
          throw (IO.userError s!"DNS_SUFFIX_NUL_SHRINK_NOT_MINIMAL: got {repr sNul}")
        let zBigPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] =>
            match q.host.splitOn "%" with
            | [_, z] => match z.toNat? with | some n => n >= 4000000000 | none => false
            | _ => false
          | _ => false
        let zBig ← shrinkElements shrinkProbe zBigPred #[{ kind := .scopedIpv6, host := "fe80::2%4294967295" }]
        if zBig.toList != [{ kind := .scopedIpv6, host := "fe80::1%4000000000" }] then
          throw (IO.userError s!"DNS_ZONE_UPPER_QUARTILE_NOT_MINIMAL: got {repr zBig}")
        let midPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .invalidDomain && q.host.startsWith "alpha." && q.host.endsWith ".delta.invalid."
          | _ => false
        let sMid ← shrinkElements shrinkProbe midPred #[{ kind := .invalidDomain, host := "alpha.beta.gamma.delta.invalid." }]
        if sMid.toList != [{ kind := .invalidDomain, host := "alpha.delta.invalid." }] then
          throw (IO.userError s!"DNS_MID_LABEL_SHRINK_NOT_MINIMAL: got {repr sMid}")
        let shortLongPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .longHostname && q.host.endsWith ".invalid." && q.host.length >= 10
          | _ => false
        let sShortLong ← shrinkElements shrinkProbe shortLongPred #[{ kind := .longHostname, host := "a.invalid." }]
        if sShortLong.toList != [{ kind := .longHostname, host := "a.invalid." }] then
          throw (IO.userError s!"DNS_SHORT_LONGHOST_GREW: got {repr sShortLong}")
        let long2EndHost := "a" ++ String.ofList (List.replicate 270 'x') ++ "z.invalid."
        let long2EndPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .longHostname && q.host.startsWith "a" && q.host.endsWith "z.invalid." && q.host.length > 255
          | _ => false
        let sLong2End ← shrinkElements shrinkProbe long2EndPred #[{ kind := .longHostname, host := long2EndHost }]
        match sLong2End.toList with
        | [ql2] =>
          if ql2.host.length != 256 || !ql2.host.startsWith "a" || !ql2.host.endsWith "z.invalid." then
            throw (IO.userError s!"DNS_LONG_TWO_END_SINGLE_LABEL_NOT_MINIMAL: len={ql2.host.length} host={ql2.host}")
        | _ => throw (IO.userError s!"DNS_LONG_TWO_END_SINGLE_LABEL_BAD_LEN: {repr sLong2End}")
        let lbl62 := String.ofList (List.replicate 62 'b')
        let longDottedHost := s!"a.{lbl62}.{lbl62}.{lbl62}.{lbl62}.z.invalid."
        let longDottedPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .longHostname && q.host.startsWith "a." && q.host.endsWith ".z.invalid." && q.host.length > 255
          | _ => false
        let sLongDotted ← shrinkElements shrinkProbe longDottedPred #[{ kind := .longHostname, host := longDottedHost }]
        match sLongDotted.toList with
        | [qld] =>
          if qld.host.length != 256 || !qld.host.startsWith "a." || !qld.host.endsWith ".z.invalid." then
            throw (IO.userError s!"DNS_LONG_TWO_END_DOTTED_NOT_MINIMAL: len={qld.host.length} host={qld.host}")
        | _ => throw (IO.userError s!"DNS_LONG_TWO_END_DOTTED_BAD_LEN: {repr sLongDotted}")
        let inv2EndPred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .invalidDomain && q.host.startsWith "a" && q.host.endsWith "z.invalid."
          | _ => false
        let sInv2End ← shrinkElements shrinkProbe inv2EndPred #[{ kind := .invalidDomain, host := "a0123456789bcdefghijz.invalid." }]
        if sInv2End.toList != [{ kind := .invalidDomain, host := "az.invalid." }] then
          throw (IO.userError s!"DNS_INVALID_TWO_END_SINGLE_LABEL_NOT_MINIMAL: got {repr sInv2End}")
        let nul21Pred := fun (arr : Array DnsProbe) => pure <| match arr.toList with
          | [q] => q.kind == .embeddedNul && q.host.startsWith "a" && q.host.contains 'z' && q.host.contains (Char.ofNat 0)
          | _ => false
        let sNul21 ← shrinkElements shrinkProbe nul21Pred #[{ kind := .embeddedNul, host := "a0123456789abcdefghz\x00" }]
        if sNul21.toList != [{ kind := .embeddedNul, host := "az\x00" }] then
          throw (IO.userError s!"DNS_NUL_21B_MULTI_ANCHOR_NOT_MINIMAL: got {repr sNul21}")
        IO.println s!"DNS_SHRINK_OK: original={injected.size} shrunk_trace={shrunkTrace.size} shrunk_probe={repr p} num_shrunk={repr pn}"
      | _ =>
        throw (IO.userError s!"DNS_NUMERIC_SCOPE_SHRINK_BAD_LEN: got {repr shrunkNum}")
    | _ =>
      throw (IO.userError s!"DNS_SHRINK_BAD_LEN: got {repr shrunkElem}")
  finally
    closePythonOracle child

/-- Differential and concurrency fuzz suite for `LeanSwe.LinuxSyscall.Dns`. -/
def suite : FuzzSuite := {
  name := "dns"
  description := "Differential DNS fuzz suite against Python socket.getaddrinfo, ResolveHints, scoped IPv6 sin6_scope_id, model/impl contracts, codec round-trips, and concurrency"
  runSmoke := fun cfg => do
    Fuzz.Dns.Checks.runChecks
    let smokeSteps := max 120 (min cfg.steps 160)
    Fuzz.Common.recordSuiteSteps smokeSteps
    runDnsDiffFuzz smokeSteps cfg.seed 12 10
  runFuzz := fun cfg => do
    if ← Fuzz.Common.isCoverageLogActive then
      Fuzz.Dns.Checks.runChecks
    let slowBudget := max 24 (cfg.steps / 400)
    Fuzz.Common.recordSuiteSteps cfg.steps
    runDnsDiffFuzz cfg.steps cfg.seed slowBudget 300
  selfTestShrink := runDnsSelfTestShrink
}

end Fuzz.Dns
