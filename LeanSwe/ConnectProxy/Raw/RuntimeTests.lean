import LeanSwe.ConnectProxy.Raw.Interface

namespace LeanSwe.ConnectProxy.Raw.RuntimeTests

open LeanSwe.ConnectProxy.Raw

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ConnectProxy.Raw ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except ProxyError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ConnectProxy.Raw ASSERTION FAILED: {msg} ({repr e})")

private def assertErrKind {α : Type} (res : Except ProxyError α) (expected : ProxyErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ConnectProxy.Raw ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ConnectProxy.Raw ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def runPy (script : String) (args : Array String := #[]) : IO String := do
  let out ← IO.Process.output {
    cmd := "python3"
    args := #["-c", script] ++ args
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 helper failed (exit {out.exitCode}):\nstdout: {out.stdout}\nstderr: {out.stderr}")
  return out.stdout

private def rawEchoServerPy : String :=
  "import socket, sys, threading\n" ++
  "srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)\n" ++
  "srv.bind(('127.0.0.1', 0))\n" ++
  "srv.listen(32)\n" ++
  "port = srv.getsockname()[1]\n" ++
  "sys.stdout.write(f'{port}\\n')\n" ++
  "sys.stdout.flush()\n" ++
  "def handle(c):\n" ++
  "  try:\n" ++
  "    while True:\n" ++
  "      d = c.recv(4096)\n" ++
  "      if not d: break\n" ++
  "      c.sendall(d)\n" ++
  "  finally:\n" ++
  "    c.close()\n" ++
  "def accept_loop():\n" ++
  "  while True:\n" ++
  "    try:\n" ++
  "      c, _ = srv.accept()\n" ++
  "      threading.Thread(target=handle, args=(c,), daemon=True).start()\n" ++
  "    except OSError:\n" ++
  "      break\n" ++
  "t = threading.Thread(target=accept_loop, daemon=True)\n" ++
  "t.start()\n" ++
  "sys.stdin.readline()\n" ++
  "srv.close()\n"

private def checkMapRawErrorAndZeroLimits : IO Unit := do
  let e1 := Raw.mapRawError (.invalidArgument none "")
  assertTrue (e1.kind == .invalidInput && e1.errnoCode == none && e1.message != "") "mapRawError invalidArgument"
  let e2 := Raw.mapRawError (.addressInUse 8080 98 "")
  assertTrue (e2.kind == .addressInUse && e2.errnoCode == some 98 && e2.message != "") "mapRawError addressInUse"
  let e3 := Raw.mapRawError (.permissionDenied 13 "")
  assertTrue (e3.kind == .permissionDenied && e3.errnoCode == some 13 && e3.message != "") "mapRawError permissionDenied"
  let e4 := Raw.mapRawError (.resourceExhausted 12 "")
  assertTrue (e4.kind == .resourceExhausted && e4.errnoCode == some 12 && e4.message != "") "mapRawError resourceExhausted"
  let e5 := Raw.mapRawError (.otherError 5 "")
  assertTrue (e5.kind == .ioError && e5.errnoCode == some 5 && e5.message != "") "mapRawError otherError"
  let e6 := Raw.mapRawError (.userError "")
  assertTrue (e6.kind == .ioError && e6.errnoCode == none && e6.message != "") "mapRawError userError"

  let onHead (_ : ByteArray) : HeadDecision := .deny none none "no"
  let onRes (_ : String) (_ : UInt16) (_ : Array IpAddr) : ResolveDecision := .deny "no"
  let zeroCfgs : Array ProxyLimits := #[
    { maxHeaderBytes := 0 },
    { headerTimeoutMs := 0 },
    { connectTimeoutMs := 0 },
    { maxConcurrentTunnels := 0 }
  ]
  for lim in zeroCfgs do
    assertErrKind (← Raw.startProxy { config := { limits := lim } } onHead onRes)
      .invalidInput "raw startProxy zero limit"
  assertTrue ((← Raw.activeProxyCount) == 0) "activeProxyCount == 0 after zero limits"

private def checkBindEphemeralAddrInUseAndLoopbackOnly : IO Unit := do
  let onHead (_ : ByteArray) : HeadDecision := .deny none none "denied"
  let onRes (_ : String) (_ : UInt16) (_ : Array IpAddr) : ResolveDecision := .deny "denied"
  let p1 ← assertOk (← Raw.startProxy { config := { listenPort := 0 } } onHead onRes) "startProxy ephemeral"
  assertTrue (p1.port != 0) "ephemeral port non-zero"
  assertTrue ((← Raw.activeProxyCount) == 1) "activeProxyCount == 1"

  let dupRes ← Raw.startProxy { config := { listenPort := p1.port } } onHead onRes
  assertErrKind dupRes .addressInUse "startProxy duplicate port EADDRINUSE"
  assertTrue ((← Raw.activeProxyCount) == 1) "activeProxyCount still 1 after EADDRINUSE"

  let _ ← runPy (
    "import socket, sys\n" ++
    "p = int(sys.argv[1])\n" ++
    "s4 = socket.create_connection(('127.0.0.1', p), timeout=2)\n" ++
    "s4.sendall(b'GET / HTTP/1.1\\r\\n\\r\\n')\n" ++
    "resp = b''\n" ++
    "while True:\n" ++
    "  d = s4.recv(4096)\n" ++
    "  if not d: break\n" ++
    "  resp += d\n" ++
    "s4.close()\n" ++
    "assert resp == b'HTTP/1.1 403 Forbidden\\r\\nContent-Length: 0\\r\\n\\r\\n', resp\n" ++
    "if socket.has_ipv6:\n" ++
    "  try:\n" ++
    "    s6 = socket.create_connection(('::1', p), timeout=1)\n" ++
    "    s6.close()\n" ++
    "    raise AssertionError('proxy unexpectedly accepted IPv6 ::1 connection')\n" ++
    "  except OSError:\n" ++
    "    pass\n"
  ) #[toString p1.port]

  let evs ← assertOk (← Raw.stopProxy p1) "stopProxy p1"
  assertTrue (evs.size == 1 && evs[0]!.outcome == .denied) "single denied event from raw probe"
  assertTrue ((← Raw.activeProxyCount) == 0) "activeProxyCount == 0 after stop"
  assertErrKind (← Raw.stopProxy p1) .invalidInput "double stopProxy rejected"
  assertErrKind (← Raw.stopProxy { handleId := 999999, port := 1 }) .invalidInput "unknown handle stopProxy rejected"
  assertTrue ((← Raw.activeProxyCount) == 0) "activeProxyCount remains 0 after invalid stops"

private def checkSaturatedLimitsLargeHeadAndDispatch : IO Unit := do
  let srv ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c", rawEchoServerPy]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  try
    let portLine ← srv.stdout.getLine
    let echoPort := (portLine.trimAscii.toString).toNat!.toUInt16
    let huge : Nat := 100000000000000000000
    let cfg : ValidProxyConfig := {
      config := {
        listenPort := 0
        limits := {
          maxHeaderBytes := huge
          headerTimeoutMs := huge
          connectTimeoutMs := huge
          maxConcurrentTunnels := huge
        }
      }
    }
    let onHead (bs : ByteArray) : HeadDecision :=
      let s := String.fromUTF8! bs
      if s.startsWith "CONNECT lit.test:" then
        .needResolve "127.0.0.1" echoPort (some (.v4 0x7f000001))
      else if s.startsWith "CONNECT failover.test:" then
        .needResolve "failover.test" echoPort none
      else
        .deny none none "raw head denied"
    let onRes (h : String) (_ : UInt16) (ips : Array IpAddr) : ResolveDecision :=
      if h == "127.0.0.1" then
        match ips[0]? with
        | some ip => .dial ip #[]
        | none => .deny "missing"
      else if h == "failover.test" then
        .dial (.v4 0x7f000001) #[.v4 0x7f000001]
      else
        .deny "unexpected host"
    let p ← assertOk (← Raw.startProxy cfg onHead onRes) "startProxy huge saturated limits"
    try
      let _ ← runPy (
        "import socket, sys\n" ++
        "p = int(sys.argv[1])\n" ++
        "s = socket.create_connection(('127.0.0.1', p), timeout=3)\n" ++
        "pad = b'X-Pad: ' + b'a' * 12000 + b'\\r\\n'\n" ++
        "s.sendall(b'CONNECT lit.test:443 HTTP/1.1\\r\\n' + pad + b'\\r\\nping-raw')\n" ++
        "buf = b''\n" ++
        "while b'\\r\\n\\r\\n' not in buf:\n" ++
        "  buf += s.recv(4096)\n" ++
        "assert buf.startswith(b'HTTP/1.1 200 Connection Established\\r\\n\\r\\n'), buf\n" ++
        "rest = buf.split(b'\\r\\n\\r\\n', 1)[1]\n" ++
        "while len(rest) < 8:\n" ++
        "  rest += s.recv(4096)\n" ++
        "assert rest == b'ping-raw', rest\n" ++
        "s.close()\n"
      ) #[toString p.port]
    finally
      let evs ← assertOk (← Raw.stopProxy p) "stopProxy huge saturated limits"
      assertTrue (evs.size == 1 && evs[0]!.outcome == .allowed) "huge head + saturated limits event"
  finally
    try
      srv.stdin.putStrLn "quit"
      srv.stdin.flush
    catch _ =>
      pure ()
    let _ ← srv.wait

private def checkRawFailoverFromDeadIp : IO Unit := do
  let srv ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c",
      "import socket, sys, threading\n" ++
      "mode = 'v4'\n" ++
      "srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)\n" ++
      "try:\n" ++
      "  srv.bind(('127.0.0.2', 0))\n" ++
      "except OSError:\n" ++
      "  srv.close()\n" ++
      "  mode = 'v6'\n" ++
      "  srv = socket.socket(socket.AF_INET6, socket.SOCK_STREAM)\n" ++
      "  srv.bind(('::1', 0))\n" ++
      "srv.listen(8)\n" ++
      "sys.stdout.write(f'{mode} {srv.getsockname()[1]}\\n')\n" ++
      "sys.stdout.flush()\n" ++
      "def accept_once():\n" ++
      "  try:\n" ++
      "    c, _ = srv.accept()\n" ++
      "    d = c.recv(64)\n" ++
      "    c.sendall(b'from-fallback:' + d)\n" ++
      "    c.close()\n" ++
      "  except OSError:\n" ++
      "    pass\n" ++
      "threading.Thread(target=accept_once, daemon=True).start()\n" ++
      "sys.stdin.readline()\n" ++
      "srv.close()\n"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  try
    let portLine ← srv.stdout.getLine
    let parts := (portLine.trimAscii.toString).splitOn " "
    let mode := parts[0]!
    let srvPort := parts[1]!.toNat!.toUInt16
    let fallbackIp : IpAddr := if mode == "v4" then .v4 0x7f000002 else .v6 0 1
    let onHead (_ : ByteArray) : HeadDecision :=
      .needResolve mode srvPort (some (.v4 0x7f000001))
    let onRes (_ : String) (_ : UInt16) (_ : Array IpAddr) : ResolveDecision :=
      .dial (.v4 0x7f000001) #[fallbackIp]
    let p ← assertOk (← Raw.startProxy { config := {} } onHead onRes) "startProxy failover"
    try
      let _ ← runPy (
        "import socket, sys\n" ++
        "p = int(sys.argv[1])\n" ++
        "s = socket.create_connection(('127.0.0.1', p), timeout=3)\n" ++
        "s.sendall(b'CONNECT x:1 HTTP/1.1\\r\\n\\r\\nok')\n" ++
        "buf = b''\n" ++
        "while True:\n" ++
        "  d = s.recv(4096)\n" ++
        "  if not d: break\n" ++
        "  buf += d\n" ++
        "s.close()\n" ++
        "assert buf == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nfrom-fallback:ok', buf\n"
      ) #[toString p.port]
    finally
      let evs ← assertOk (← Raw.stopProxy p) "stopProxy failover"
      assertTrue (evs.size == 1 && evs[0]!.outcome == .allowed) "failover recorded allowed"
  finally
    try
      srv.stdin.putStrLn "quit"
      srv.stdin.flush
    catch _ =>
      pure ()
    let _ ← srv.wait

/-- Execute OS-level runtime verification tests for `LeanSwe.ConnectProxy.Raw`. -/
def runAll : IO Unit := do
  assertTrue ((← Raw.activeProxyCount) == 0) "initial Raw.activeProxyCount == 0"
  checkMapRawErrorAndZeroLimits
  checkBindEphemeralAddrInUseAndLoopbackOnly
  checkSaturatedLimitsLargeHeadAndDispatch
  checkRawFailoverFromDeadIp
  assertTrue ((← Raw.activeProxyCount) == 0) "final Raw.activeProxyCount == 0"
  IO.println "PASS: LeanSwe.ConnectProxy.Raw runtime tests"

end LeanSwe.ConnectProxy.Raw.RuntimeTests
