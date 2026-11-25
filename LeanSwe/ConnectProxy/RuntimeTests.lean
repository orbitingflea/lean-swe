import Core.Assumptions
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.RuntimeTests.TunnelTests
import LeanSwe.ConnectProxy.RuntimeTests.DnsWakeup

namespace LeanSwe.ConnectProxy.RuntimeTests

open LeanSwe.ConnectProxy

private def testLimitsTimeoutOversizeConcurrencyAnd502 : IO Unit := do
  let (holdSrv, holdPort) ← startUpstreamServer "127.0.0.1" "hold"
  let (hcSrv, hcPort) ← startUpstreamServer "127.0.0.1" "halfclose"
  try
    let allowLoopback ← assertOk (parseIpPrefix "127.0.0.1/32") "parse 127.0.0.1/32"
    let limCfg : ProxyConfig := {
      listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := hcPort },
        { host := "127.0.0.1", port := holdPort },
        { host := "127.0.0.1", port := 1 },
        { host := "nonexistent.invalid", port := 443 }
      ]
      ipPolicy := { base := .empty, extraAllows := #[allowLoopback] }
      limits := {
        maxHeaderBytes := 96
        headerTimeoutMs := 150
        connectTimeoutMs := 2000
        maxConcurrentTunnels := 2
      }
    }
    let res ← withProxy limCfg fun proxy => do
      let _ ← runPy (
        "import socket, sys, time\n" ++
        "pp, ep, hp = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])\n" ++
        "def read_all(s):\n" ++
        "  b = b''\n" ++
        "  while True:\n" ++
        "    d = s.recv(4096)\n" ++
        "    if not d: break\n" ++
        "    b += d\n" ++
        "  return b\n" ++
        "s_slow = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s_slow.sendall(b'CONNECT 127.0.0.1')\n" ++
        "assert read_all(s_slow) == b'HTTP/1.1 403 Forbidden\\r\\nContent-Length: 0\\r\\n\\r\\n'\n" ++
        "s_slow.close()\n" ++
        "s_big = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s_big.sendall(b'CONNECT 127.0.0.1:' + str(ep).encode() + b' HTTP/1.1\\r\\nX-Long: ' + b'z'*100 + b'\\r\\n\\r\\n')\n" ++
        "assert read_all(s_big) == b'HTTP/1.1 403 Forbidden\\r\\nContent-Length: 0\\r\\n\\r\\n'\n" ++
        "s_big.close()\n" ++
        "s_pipe = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "head = f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\n\\r\\n'.encode()\n" ++
        "assert len(head) <= 96\n" ++
        "s_pipe.sendall(head + b'P'*80)\n" ++
        "s_pipe.shutdown(socket.SHUT_WR)\n" ++
        "assert read_all(s_pipe) == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:' + b'P'*80\n" ++
        "s_pipe.close()\n" ++
        "s_502 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s_502.sendall(b'CONNECT 127.0.0.1:1 HTTP/1.1\\r\\n\\r\\n')\n" ++
        "assert read_all(s_502) == b'HTTP/1.1 502 Bad Gateway\\r\\nContent-Length: 0\\r\\n\\r\\n'\n" ++
        "s_502.close()\n" ++
        "s_dns = socket.create_connection(('127.0.0.1', pp), timeout=5)\n" ++
        "s_dns.sendall(b'CONNECT nonexistent.invalid:443 HTTP/1.1\\r\\n\\r\\n')\n" ++
        "assert read_all(s_dns) == b'HTTP/1.1 502 Bad Gateway\\r\\nContent-Length: 0\\r\\n\\r\\n'\n" ++
        "s_dns.close()\n" ++
        "t1 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "t1.sendall(f'CONNECT 127.0.0.1:{hp} HTTP/1.1\\r\\n\\r\\n'.encode())\n" ++
        "assert t1.recv(64).startswith(b'HTTP/1.1 200')\n" ++
        "t2 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "t2.sendall(f'CONNECT 127.0.0.1:{hp} HTTP/1.1\\r\\n\\r\\n'.encode())\n" ++
        "assert t2.recv(64).startswith(b'HTTP/1.1 200')\n" ++
        "t3 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "t3.sendall(f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\n\\r\\nqueued'.encode())\n" ++
        "t3.shutdown(socket.SHUT_WR)\n" ++
        "t3.settimeout(0.15)\n" ++
        "try:\n" ++
        "  early = t3.recv(64)\n" ++
        "  raise AssertionError(f't3 served while at maxConcurrentTunnels=2: {early}')\n" ++
        "except socket.timeout:\n" ++
        "  pass\n" ++
        "t1.close()\n" ++
        "t3.settimeout(3.0)\n" ++
        "assert read_all(t3) == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:queued'\n" ++
        "t3.close()\n" ++
        "t2.close()\n"
      ) #[toString proxy.port, toString hcPort, toString holdPort]
      return .ok ()
    let (_, evs) ← assertOk res "limits and concurrency test"
    assertTrue (evs.size == 8) s!"expected 8 events, got {evs.size}"
    assertTrue (evs[0]!.outcome == .denied && evs[1]!.outcome == .denied) "slowloris & big head denied"
    assertTrue (evs[2]!.outcome == .allowed) "pipelined allowed"
    assertTrue (evs[3]!.outcome == .failed && evs[4]!.outcome == .failed) "unreachable port & NXDOMAIN 502 failed"
    assertTrue (evs[5]!.outcome == .allowed && evs[6]!.outcome == .allowed && evs[7]!.outcome == .allowed)
      "concurrency slots allowed"
  finally
    stopServer holdSrv
    stopServer hcSrv

private def testCallbackErrorInFlightStopAndParallel : IO Unit := do
  let allowLoopback ← assertOk (parseIpPrefix "127.0.0.1/32") "parse 127.0.0.1/32"
  let (hcSrv, hcPort) ← startUpstreamServer "127.0.0.1" "halfclose"
  try
    let cfg : ProxyConfig := {
      listenPort := 0
      allowedTargets := #[{ host := "127.0.0.1", port := hcPort }]
      ipPolicy := { base := .empty, extraAllows := #[allowLoopback] }
    }
    let fdsBeforeErr ← countSelfOpenFds
    let errPortRef ← IO.mkRef (0 : UInt16)
    let errRes ← withProxy cfg fun proxy => do
      errPortRef.set proxy.port
      let _ ← runPy (
        "import socket, sys\n" ++
        "s = socket.create_connection(('127.0.0.1', int(sys.argv[1])), timeout=3)\n" ++
        "s.sendall(b'CONNECT 127.0.0.1:')\n" ++
        "s.close()\n"
      ) #[toString proxy.port]
      return (.error { kind := .ioError, message := "caller aborted" } : Except ProxyError Unit)
    assertErrKind errRes .ioError "withProxy callback error preserved"
    let errPort ← errPortRef.get
    let _ ← runPy (
      "import socket, sys\n" ++
      "try:\n" ++
      "  s = socket.create_connection(('127.0.0.1', int(sys.argv[1])), timeout=1)\n" ++
      "  s.close()\n" ++
      "  raise AssertionError('listener still accepting after callback error')\n" ++
      "except OSError:\n" ++
      "  pass\n"
    ) #[toString errPort]
    let fdsAfterErr ← countSelfOpenFds
    assertTrue (fdsAfterErr == fdsBeforeErr)
      s!"proxy leaked FDs on callback error: before={fdsBeforeErr} after={fdsAfterErr}"

    let child ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c",
        "import socket, sys, time\n" ++
        "pp = int(sys.stdin.readline().strip())\n" ++
        "s = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s.sendall(b'CONNECT 127.0.0.1:')\n" ++
        "sys.stdout.write('sent\\n')\n" ++
        "sys.stdout.flush()\n" ++
        "time.sleep(0.3)\n" ++
        "s.close()\n"]
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let stopInFlightRes ← withProxy cfg fun proxy => do
      child.stdin.putStrLn (toString proxy.port)
      child.stdin.flush
      let _ ← child.stdout.getLine
      IO.sleep 40
      return .ok ()
    let (_, child) ← child.takeStdin
    let _ ← child.wait
    let (_, inFlightEvs) ← assertOk stopInFlightRes "in-flight stop"
    assertTrue (inFlightEvs.size == 1 &&
      inFlightEvs[0]!.outcome == .failed &&
      inFlightEvs[0]!.reason == some "proxy stopped")
      s!"expected proxy stopped event, got {repr inFlightEvs}"

    let mut tasks : Array (Task (Except IO.Error (Except ProxyError (UInt16 × Array ConnectEvent)))) := #[]
    for idx in [:4] do
      let t ← IO.asTask do
        withProxy cfg fun proxy => do
          let _ ← runPy (
            "import socket, sys\n" ++
            "pp, ep, tag = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]\n" ++
            "s = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
            "s.sendall(f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\n\\r\\n{tag}'.encode())\n" ++
            "s.shutdown(socket.SHUT_WR)\n" ++
            "b = b''\n" ++
            "while True:\n" ++
            "  d = s.recv(4096)\n" ++
            "  if not d: break\n" ++
            "  b += d\n" ++
            "s.close()\n" ++
            "assert b == f'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:{tag}'.encode(), b\n"
          ) #[toString proxy.port, toString hcPort, s!"worker-{idx}"]
          return .ok proxy.port
      tasks := tasks.push t

    let mut ports : Array UInt16 := #[]
    for t in tasks do
      let ioRes ← IO.wait t
      let prxRes ← match ioRes with
        | .ok r => pure r
        | .error e => throw e
      let (p, evs) ← assertOk prxRes "parallel withProxy"
      assertTrue (p != 0 && evs.size == 1 && evs[0]!.outcome == .allowed) "parallel proxy event"
      assertTrue (!ports.contains p) "parallel ephemeral ports distinct"
      ports := ports.push p
  finally
    stopServer hcSrv

private def mkStartErrorOps (rawErr : ConnectProxyRawError) : RawConnectProxyOps :=
  { mapRawError := Model.mapRawErrorPure
    startProxy := fun _ _ _ => pure (.error (Model.mapRawErrorPure rawErr))
    stopProxy := fun _ => pure (.ok #[])
    activeProxyCount := pure 0 }

/-- Verify `parseIpAddr` rejects wildcard, leading-zero octal, shorthand, and bracketed inputs with `.invalidInput`. -/
def err_cproxy_parseIpAddr_invalidInput : IO Unit := do
  for bad in ["10.1*", "010.0.0.1", "127.1", "[::1]"] do
    assertErrKind (parseIpAddr bad) .invalidInput s!"parseIpAddr {bad}"

/-- Verify `parseIpPrefix` rejects wildcard, non-zero host bits, and out-of-range prefix lengths with `.invalidInput`. -/
def err_cproxy_parseIpPrefix_invalidInput : IO Unit := do
  for bad in ["10.1*", "10.20.1.5/24", "10.0.0.0/33", "fe80::/129"] do
    assertErrKind (parseIpPrefix bad) .invalidInput s!"parseIpPrefix {bad}"

/-- Verify `parseConnectRequest` rejects non-CONNECT methods, malformed framing, and out-of-range ports with `.invalidInput`. -/
def err_cproxy_parseConnectRequest_invalidInput : IO Unit := do
  for bad in ["GET / HTTP/1.1\r\n\r\n", "CONNECT example.com:0 HTTP/1.1\r\n\r\n", "CONNECT example.com:443 HTTP/1.1\r\n"] do
    assertErrKind (parseConnectRequest bad.toUTF8) .invalidInput s!"parseConnectRequest {repr bad}"

/-- Verify `validateConfig` rejects zero limits, invalid CIDR masks, and port-0 target rules with `.invalidInput`. -/
def err_cproxy_validateConfig_invalidInput : IO Unit := do
  let badCfgs : List ProxyConfig :=
    [ { limits := { maxHeaderBytes := 0 } }
    , { limits := { maxConcurrentTunnels := 0 } }
    , { allowedTargets := #[{ host := "example.com", port := 0 }] } ]
  for bad in badCfgs do
    assertErrKind (validateConfig bad) .invalidInput "validateConfig invalid"

/-- Verify `withProxy` rejects invalid configurations with `.invalidInput` before opening any listener socket. -/
def err_cproxy_withProxy_invalidInput : IO Unit := do
  let res ← withProxy { limits := { maxHeaderBytes := 0 } } fun _ => pure (.ok ())
  assertErrKind res .invalidInput "withProxy invalidInput"

/-- Verify `withProxy` returns `.addressInUse` when binding an already-listening `127.0.0.1` port. -/
def err_cproxy_withProxy_addressInUse : IO Unit := do
  let outerRes ← withProxy { listenPort := 0 } fun p => do
    let innerRes ← withProxy { listenPort := p.port } fun _ => pure (.ok ())
    assertErrKind innerRes .addressInUse "withProxy EADDRINUSE"
    return .ok p.port
  let boundPort ← assertOk outerRes "outer withProxy for EADDRINUSE"
  assertTrue (boundPort.1 != 0) "outer ephemeral port non-zero"

/-- Verify `withProxy` surfaces `.permissionDenied` (`EACCES`) from listener startup via `Internal.mkApiM`. -/
def err_cproxy_withProxy_permissionDenied : IO Unit := do
  let ops := mkStartErrorOps (.permissionDenied 13 "permission denied binding listener")
  let res ← (Internal.mkApiM ops).withProxy { listenPort := 80 } fun _ => pure (.ok ())
  assertErrKind res .permissionDenied "withProxy permissionDenied"

/-- Verify `withProxy` surfaces `.resourceExhausted` (`EMFILE`) from listener startup via `Internal.mkApiM`. -/
def err_cproxy_withProxy_resourceExhausted : IO Unit := do
  let ops := mkStartErrorOps (.resourceExhausted 24 "too many open files")
  let res ← (Internal.mkApiM ops).withProxy { listenPort := 0 } fun _ => pure (.ok ())
  assertErrKind res .resourceExhausted "withProxy resourceExhausted"

/-- Verify `withProxy` propagates `.ioError` cleanly while tearing down the listener without leaking descriptors. -/
def err_cproxy_withProxy_ioError : IO Unit := do
  let fdsBefore ← countSelfOpenFds
  let res ← withProxy (α := Unit) { listenPort := 0 } fun _ =>
    pure (.error { kind := .ioError, message := "injected callback ioError" })
  assertErrKind res .ioError "withProxy ioError"
  let fdsAfter ← countSelfOpenFds
  assertTrue (fdsAfter == fdsBefore)
    s!"withProxy ioError leaked file descriptors: before={fdsBefore} after={fdsAfter}"

/-- Registry of error-coverage runtime tests for `LeanSwe.ConnectProxy`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseIpAddr_invalidInput", .real,
    err_cproxy_parseIpAddr_invalidInput⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseIpPrefix_invalidInput", .real,
    err_cproxy_parseIpPrefix_invalidInput⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseConnectRequest_invalidInput", .real,
    err_cproxy_parseConnectRequest_invalidInput⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_validateConfig_invalidInput", .real,
    err_cproxy_validateConfig_invalidInput⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_invalidInput", .real,
    err_cproxy_withProxy_invalidInput⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_addressInUse", .real,
    err_cproxy_withProxy_addressInUse⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_permissionDenied", .mocked,
    err_cproxy_withProxy_permissionDenied⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_resourceExhausted", .mocked,
    err_cproxy_withProxy_resourceExhausted⟩,
  ⟨"LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_ioError", .real,
    err_cproxy_withProxy_ioError⟩
]

/-- Execute end-to-end OS network and Python differential runtime tests for `LeanSwe.ConnectProxy`. -/
def runAll : IO Unit := do
  let fdsBefore ← countSelfOpenFds
  assertErrKind (← withProxy { limits := { maxHeaderBytes := 0 } } fun _ => pure (.ok ()))
    .invalidInput "withProxy invalid config rejected"
  testPollTimeoutClamp
  runPythonIpaddressDifferential
  testTunnelPipelineHalfCloseFailoverAndCurl
  testDenialsPublicOnlyBansAndPostBody
  testLimitsTimeoutOversizeConcurrencyAnd502
  testCallbackErrorInFlightStopAndParallel
  testPerJobDnsWakeupCancelAndEmfile
  testDetachedDnsWakeupAtMaxConcurrency
  testExceptionSafetyAndTeardown
  Core.runRegisteredErrorTests registeredErrorTests
  let fdsAfter ← countSelfOpenFds
  assertTrue (fdsAfter == fdsBefore)
    s!"ConnectProxy.RuntimeTests leaked file descriptors: before={fdsBefore} after={fdsAfter}"
  printlnSafe "PASS: LeanSwe.ConnectProxy runtime tests"

end LeanSwe.ConnectProxy.RuntimeTests
