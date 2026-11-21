import Core.Assumptions
import LeanSwe.ConnectProxy.Interface

namespace LeanSwe.ConnectProxy.RuntimeTests

open LeanSwe.ConnectProxy

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ConnectProxy ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except ProxyError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ConnectProxy ASSERTION FAILED: {msg} ({repr e})")

private def assertErrKind {α : Type} (res : Except ProxyError α) (expected : ProxyErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ConnectProxy ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ConnectProxy ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def countSelfOpenFds : IO Nat := do
  return (← (System.FilePath.mk "/proc/self/fd").readDir).size

private def printlnSafe (msg : String) : IO Unit := do
  try
    IO.println msg
  catch _ =>
    pure ()

private def runPy (script : String) (args : Array String := #[]) : IO String := do
  let out ← IO.Process.output {
    cmd := "python3"
    args := #["-c", script] ++ args
    stdin := .null
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 failed (exit {out.exitCode}):\nstdout: {out.stdout}\nstderr: {out.stderr}")
  return out.stdout

private def runPythonIpaddressDifferential : IO Unit := do
  let mut payload := ByteArray.emptyWithCapacity 65536
  for i in [:65536] do
    let ip : IpAddr := .v6 (UInt64.ofNat i <<< 48) 1
    payload := payload.push (if isGlobalIp ip then 1 else 0)

  let explicitCases : Array (String × IpAddr) := #[
    ("0.0.0.0", .v4 0x00000000),
    ("0.255.255.255", .v4 0x00ffffff),
    ("1.1.1.1", .v4 0x01010101),
    ("8.8.8.8", .v4 0x08080808),
    ("10.0.0.1", .v4 0x0a000001),
    ("100.64.0.1", .v4 0x64400001),
    ("100.127.255.254", .v4 0x647ffffe),
    ("100.128.0.1", .v4 0x64800001),
    ("127.0.0.1", .v4 0x7f000001),
    ("169.254.1.1", .v4 0xa9fe0101),
    ("172.15.255.255", .v4 0xac0fffff),
    ("172.16.0.1", .v4 0xac100001),
    ("172.31.255.255", .v4 0xac1fffff),
    ("172.32.0.1", .v4 0xac200001),
    ("192.0.0.1", .v4 0xc0000001),
    ("192.0.0.9", .v4 0xc0000009),
    ("192.0.0.10", .v4 0xc000000a),
    ("192.0.2.1", .v4 0xc0000201),
    ("192.168.1.1", .v4 0xc0a80101),
    ("198.18.0.1", .v4 0xc6120001),
    ("198.19.255.254", .v4 0xc613fffe),
    ("198.20.0.1", .v4 0xc6140001),
    ("198.51.100.1", .v4 0xc6336401),
    ("203.0.113.1", .v4 0xcb007101),
    ("223.255.255.254", .v4 0xdffffffe),
    ("224.0.0.1", .v4 0xe0000001),
    ("239.255.255.254", .v4 0xeffffffe),
    ("240.0.0.1", .v4 0xf0000001),
    ("255.255.255.255", .v4 0xffffffff),
    ("::", .v6 0 0),
    ("::1", .v6 0 1),
    ("::127.0.0.1", .v6 0 0x7f000001),
    ("::8.8.8.8", .v6 0 0x08080808),
    ("::ffff:127.0.0.1", .v6 0 0x0000ffff7f000001),
    ("::ffff:8.8.8.8", .v6 0 0x0000ffff08080808),
    ("::ffff:0:8.8.8.8", .v6 0 0xffff000008080808),
    ("64:ff9b::8.8.8.8", .v6 0x0064ff9b00000000 0x08080808),
    ("64:ff9b::10.0.0.1", .v6 0x0064ff9b00000000 0x0a000001),
    ("64:ff9b:1::1", .v6 0x0064ff9b00010000 1),
    ("100::1", .v6 0x0100000000000000 1),
    ("2001:0::1", .v6 0x2001000000000000 1),
    ("2001:1::3", .v6 0x2001000100000000 3),
    ("2001:2::1", .v6 0x2001000200000000 1),
    ("2001:db8::1", .v6 0x20010db800000000 1),
    ("2606:4700:4700::1111", .v6 0x2606470047000000 0x1111),
    ("5f00::1", .v6 0x5f00000000000000 1),
    ("fc00::1", .v6 0xfc00000000000000 1),
    ("fe80::1", .v6 0xfe80000000000000 1),
    ("fec0::1", .v6 0xfec0000000000000 1),
    ("ff02::1", .v6 0xff02000000000000 1)
  ]
  let fixedExplicitCases : Array (String × IpAddr × Bool × String) := #[
    ("2001:1::1", .v6 0x2001000100000000 1, true, "RFC 7723 PCP anycast exception is globally reachable"),
    ("2001:1::2", .v6 0x2001000100000000 2, true, "RFC 8155 TURN anycast exception is globally reachable"),
    ("2001:3::1", .v6 0x2001000300000000 1, true, "RFC 7450 AMT exception is globally reachable"),
    ("2001:4:112::1", .v6 0x2001000401120000 1, true, "RFC 7535 AS112-v6 exception is globally reachable"),
    ("2001:20::1", .v6 0x2001002000000000 1, true, "RFC 7343 ORCHIDv2 exception is globally reachable"),
    ("2001:30::1", .v6 0x2001003000000000 1, true, "RFC 9374 Drone Remote ID exception is globally reachable"),
    ("2002:0808:0808::1", .v6 0x2002080808080000 1, false, "RFC 3056 6to4 is not globally reachable"),
    ("3fff::1", .v6 0x3fff000000000000 1, false, "RFC 9637 documentation prefix is not globally reachable")
  ]
  for (s, ip, expectedGlobal, reason) in fixedExplicitCases do
    let got ← assertOk (parseIpAddr s) s!"parseIpAddr {s}"
    assertTrue (got == ip) s!"parseIpAddr mismatch for {s}"
    assertTrue (isGlobalIp ip == expectedGlobal) s!"isGlobalIp mismatch for {s}: {reason}"
  assertTrue (!isGlobalIp (.v6 (UInt64.ofNat 0x2002 <<< 48) 1))
    "2002::1 is not globally reachable (RFC 3056 6to4)"
  assertTrue (!isGlobalIp (.v6 (UInt64.ofNat 0x3fff <<< 48) 1))
    "3fff::1 is not globally reachable (RFC 9637 documentation prefix)"

  let mut scriptCases := ""
  for (s, ip) in explicitCases do
    let got ← assertOk (parseIpAddr s) s!"parseIpAddr {s}"
    assertTrue (got == ip) s!"parseIpAddr mismatch for {s}"
    let b := if isGlobalIp ip then 1 else 0
    scriptCases := scriptCases ++ s!"({repr s}, {b}), "

  let pyScript :=
    "import ipaddress, sys\n" ++
    "data = sys.stdin.buffer.read(65536)\n" ++
    "assert len(data) == 65536, len(data)\n" ++
    "def py_global(ip):\n" ++
    "  if ip.version == 4:\n" ++
    "    return ip.is_global and not ip.is_multicast\n" ++
    "  if ip.ipv4_mapped is not None:\n" ++
    "    v4 = ip.ipv4_mapped\n" ++
    "    return v4.is_global and not v4.is_multicast\n" ++
    "  if int(ip) >> 32 == 0x0064ff9b0000000000000000:\n" ++
    "    v4 = ipaddress.IPv4Address(int(ip) & 0xffffffff)\n" ++
    "    return v4.is_global and not v4.is_multicast\n" ++
    "  return ip.is_global and not ip.is_multicast and not ip.is_site_local and not ip.is_reserved\n" ++
    "for i in range(65536):\n" ++
    "  if i in (0x2002, 0x3fff):\n" ++
    "    continue\n" ++
    "  ip = ipaddress.IPv6Address((i << 112) | 1)\n" ++
    "  exp = 1 if py_global(ip) else 0\n" ++
    "  if data[i] != exp:\n" ++
    "    raise AssertionError(f'/16 mismatch at {hex(i)} ({ip}): lean={data[i]} py={exp}')\n" ++
    "explicit = [" ++ scriptCases ++ "]\n" ++
    "for s, lean_b in explicit:\n" ++
    "  ip = ipaddress.ip_address(s)\n" ++
    "  exp = 1 if py_global(ip) else 0\n" ++
    "  if lean_b != exp:\n" ++
    "    raise AssertionError(f'explicit mismatch for {s}: lean={lean_b} py={exp}')\n"

  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c", pyScript]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.write payload
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  assertTrue (code == 0) s!"ipaddress differential failed (exit {code}): {out} {err}"

private def startUpstreamServer (bindHost : String) (mode : String) :
    IO (IO.Process.Child ⟨.piped, .piped, .piped⟩ × UInt16) := do
  let script :=
    "import socket, sys, threading\n" ++
    "host = sys.argv[1]\n" ++
    "mode = sys.argv[2]\n" ++
    "fam = socket.AF_INET6 if ':' in host else socket.AF_INET\n" ++
    "srv = socket.socket(fam, socket.SOCK_STREAM)\n" ++
    "srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)\n" ++
    "srv.bind((host, 0))\n" ++
    "srv.listen(64)\n" ++
    "sys.stdout.write(f'{srv.getsockname()[1]}\\n')\n" ++
    "sys.stdout.flush()\n" ++
    "def handle(c):\n" ++
    "  try:\n" ++
    "    if mode == 'http':\n" ++
    "      req = b''\n" ++
    "      while b'\\r\\n\\r\\n' not in req:\n" ++
    "        d = c.recv(4096)\n" ++
    "        if not d: break\n" ++
    "        req += d\n" ++
    "      body = b'hello-from-tunnel'\n" ++
    "      c.sendall(b'HTTP/1.1 200 OK\\r\\nContent-Length: 17\\r\\nConnection: close\\r\\n\\r\\n' + body)\n" ++
    "    elif mode == 'halfclose':\n" ++
    "      chunks = []\n" ++
    "      while True:\n" ++
    "        d = c.recv(4096)\n" ++
    "        if not d: break\n" ++
    "        chunks.append(d)\n" ++
    "      c.sendall(b'ECHO:' + b''.join(chunks))\n" ++
    "    elif mode == 'hold':\n" ++
    "      while True:\n" ++
    "        d = c.recv(4096)\n" ++
    "        if not d: break\n" ++
    "  finally:\n" ++
    "    c.close()\n" ++
    "def loop():\n" ++
    "  while True:\n" ++
    "    try:\n" ++
    "      c, _ = srv.accept()\n" ++
    "      threading.Thread(target=handle, args=(c,), daemon=True).start()\n" ++
    "    except OSError:\n" ++
    "      break\n" ++
    "threading.Thread(target=loop, daemon=True).start()\n" ++
    "sys.stdin.readline()\n" ++
    "srv.close()\n"
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c", script, bindHost, mode]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let line ← child.stdout.getLine
  let port := (line.trimAscii.toString).toNat!.toUInt16
  return (child, port)

private def stopServer (srv : IO.Process.Child ⟨.piped, .piped, .piped⟩) : IO Unit := do
  try
    srv.stdin.putStrLn "quit"
    srv.stdin.flush
  catch _ =>
    pure ()
  let _ ← srv.wait

private def testTunnelPipelineHalfCloseFailoverAndCurl : IO Unit := do
  let (httpSrv, httpPort) ← startUpstreamServer "127.0.0.1" "http"
  let (hcSrv, hcPort) ← startUpstreamServer "127.0.0.1" "halfclose"
  let (v6Srv, v6Port) ← startUpstreamServer "::1" "halfclose"
  try
    let allowV4 ← assertOk (parseIpPrefix "127.0.0.1/32") "parse 127.0.0.1/32"
    let allowV6 ← assertOk (parseIpPrefix "::1/128") "parse ::1/128"
    let allowMapped ← assertOk (parseIpPrefix "::ffff:127.0.0.1/128") "parse ::ffff:127.0.0.1/128"
    let cfg : ProxyConfig := {
      listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := httpPort },
        { host := "127.0.0.1", port := hcPort },
        { host := "[::1]", port := v6Port },
        { host := "[::ffff:127.0.0.1]", port := hcPort },
        { host := "LOCALHOST", port := hcPort }
      ]
      ipPolicy := { base := .empty, extraAllows := #[allowV4, allowV6, allowMapped] }
    }
    let res ← withProxy cfg fun proxy => do
      let _ ← runPy (
        "import socket, sys\n" ++
        "pp, hp, ep, v6p = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])\n" ++
        "s1 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s1.sendall(f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\nHost: 127.0.0.1:{ep}\\r\\n\\r\\nfirst-half'.encode())\n" ++
        "resp = b''\n" ++
        "while b'\\r\\n\\r\\n' not in resp:\n" ++
        "  d = s1.recv(4096)\n" ++
        "  assert d, 'premature eof waiting 200'\n" ++
        "  resp += d\n" ++
        "assert resp.startswith(b'HTTP/1.1 200 Connection Established\\r\\n\\r\\n'), resp\n" ++
        "s1.sendall(b'+second-half')\n" ++
        "s1.shutdown(socket.SHUT_WR)\n" ++
        "tail = resp.split(b'\\r\\n\\r\\n', 1)[1]\n" ++
        "while True:\n" ++
        "  d = s1.recv(4096)\n" ++
        "  if not d: break\n" ++
        "  tail += d\n" ++
        "s1.close()\n" ++
        "assert tail == b'ECHO:first-half+second-half', tail\n" ++
        "s2 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s2.sendall(f'CONNECT [::FFFF:127.0.0.1]:{ep} HTTP/1.1\\r\\n\\r\\nv4mapped'.encode())\n" ++
        "s2.shutdown(socket.SHUT_WR)\n" ++
        "all2 = b''\n" ++
        "while True:\n" ++
        "  d = s2.recv(4096)\n" ++
        "  if not d: break\n" ++
        "  all2 += d\n" ++
        "s2.close()\n" ++
        "assert all2 == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:v4mapped', all2\n" ++
        "s3 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s3.sendall(f'CONNECT localhost:{ep} HTTP/1.1\\r\\n\\r\\nfailover-ok'.encode())\n" ++
        "s3.shutdown(socket.SHUT_WR)\n" ++
        "all3 = b''\n" ++
        "while True:\n" ++
        "  d = s3.recv(4096)\n" ++
        "  if not d: break\n" ++
        "  all3 += d\n" ++
        "s3.close()\n" ++
        "assert all3 == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:failover-ok', all3\n" ++
        "s4 = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "s4.sendall(f'CONNECT [0:0::1]:{v6p} HTTP/1.0\\r\\nContent-Length: 0\\r\\n\\r\\nv6direct'.encode())\n" ++
        "s4.shutdown(socket.SHUT_WR)\n" ++
        "all4 = b''\n" ++
        "while True:\n" ++
        "  d = s4.recv(4096)\n" ++
        "  if not d: break\n" ++
        "  all4 += d\n" ++
        "s4.close()\n" ++
        "assert all4 == b'HTTP/1.1 200 Connection Established\\r\\n\\r\\nECHO:v6direct', all4\n"
      ) #[toString proxy.port, toString httpPort, toString hcPort, toString v6Port]

      let curlOut ← IO.Process.output {
        cmd := "curl"
        args := #[
          "-sS", "--noproxy", "", "-p",
          "--proxy", s!"http://127.0.0.1:{proxy.port}",
          "--http1.1",
          s!"http://127.0.0.1:{httpPort}/hello"
        ]
        stdin := .null
      }
      assertTrue (curlOut.exitCode == 0 && curlOut.stdout == "hello-from-tunnel")
        s!"curl tunnel integration failed: exit={curlOut.exitCode} out={curlOut.stdout} err={curlOut.stderr}"
      return .ok "tunneled"
    let (v, evs) ← assertOk res "withProxy tunnel test"
    assertTrue (v == "tunneled" && evs.size == 5) s!"expected 5 allowed events, got {evs.size}"
    for ev in evs do
      assertTrue (ev.outcome == .allowed && ev.reason == none) s!"expected allowed event, got {repr ev}"
  finally
    stopServer httpSrv
    stopServer hcSrv
    stopServer v6Srv

private def testDenialsPublicOnlyBansAndPostBody : IO Unit := do
  let (hcSrv, hcPort) ← startUpstreamServer "127.0.0.1" "halfclose"
  try
    let allowNet ← assertOk (parseIpPrefix "127.0.0.0/8") "parse 127.0.0.0/8"
    let allowAllV6 ← assertOk (parseIpPrefix "::/0") "parse ::/0"
    let banOne ← assertOk (parseIpPrefix "127.0.0.1/32") "parse 127.0.0.1/32"

    let pubCfg : ProxyConfig := {
      listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := hcPort },
        { host := "[::1]", port := hcPort },
        { host := "localhost", port := hcPort }
      ]
      ipPolicy := { base := .publicOnly }
    }
    let pubRes ← withProxy pubCfg fun proxy => do
      let _ ← runPy (
        "import socket, sys\n" ++
        "pp, ep = int(sys.argv[1]), int(sys.argv[2])\n" ++
        "reqs = [\n" ++
        "  f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT [::1]:{ep} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT localhost:{ep} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT evil.example.com:{ep} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT 127.0.0.1:{ep + 1} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT 127.1:{ep} HTTP/1.1\\r\\n\\r\\n'.encode(),\n" ++
        "  f'CONNECT 127.0.0.1:{ep} HTTP/1.1\\r\\nTransfer-Encoding: chunked\\r\\n\\r\\n'.encode(),\n" ++
        "  f'GET http://127.0.0.1:{ep}/ HTTP/1.1\\r\\nHost: 127.0.0.1\\r\\n\\r\\n'.encode(),\n" ++
        "  (f'POST http://127.0.0.1:{ep}/submit HTTP/1.1\\r\\nHost: 127.0.0.1\\r\\nContent-Length: 2048\\r\\n\\r\\n'.encode() + b'B' * 2048),\n" ++
        "]\n" ++
        "for r in reqs:\n" ++
        "  s = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "  s.sendall(r)\n" ++
        "  resp = b''\n" ++
        "  while True:\n" ++
        "    d = s.recv(4096)\n" ++
        "    if not d: break\n" ++
        "    resp += d\n" ++
        "  s.close()\n" ++
        "  assert resp == b'HTTP/1.1 403 Forbidden\\r\\nContent-Length: 0\\r\\n\\r\\n', (r[:40], resp)\n"
      ) #[toString proxy.port, toString hcPort]
      return .ok ()
    let (_, pubEvs) ← assertOk pubRes "publicOnly denials"
    assertTrue (pubEvs.size == 9) s!"expected 9 denied events, got {pubEvs.size}"
    for ev in pubEvs do
      assertTrue (ev.outcome == .denied && ev.reason.isSome) s!"expected denied event, got {repr ev}"

    let banCfg : ProxyConfig := {
      listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := hcPort },
        { host := "[::ffff:127.0.0.1]", port := hcPort },
        { host := "[::127.0.0.1]", port := hcPort },
        { host := "[64:ff9b::127.0.0.1]", port := hcPort }
      ]
      ipPolicy := { base := .empty, extraAllows := #[allowNet, allowAllV6], extraBans := #[banOne] }
    }
    let banRes ← withProxy banCfg fun proxy => do
      let _ ← runPy (
        "import socket, sys\n" ++
        "pp, ep = int(sys.argv[1]), int(sys.argv[2])\n" ++
        "for h in ('127.0.0.1', '[::ffff:127.0.0.1]', '[::127.0.0.1]', '[64:ff9b::127.0.0.1]'):\n" ++
        "  s = socket.create_connection(('127.0.0.1', pp), timeout=3)\n" ++
        "  s.sendall(f'CONNECT {h}:{ep} HTTP/1.1\\r\\n\\r\\n'.encode())\n" ++
        "  resp = b''\n" ++
        "  while True:\n" ++
        "    d = s.recv(4096)\n" ++
        "    if not d: break\n" ++
        "    resp += d\n" ++
        "  s.close()\n" ++
        "  assert resp == b'HTTP/1.1 403 Forbidden\\r\\nContent-Length: 0\\r\\n\\r\\n', (h, resp)\n"
      ) #[toString proxy.port, toString hcPort]
      return .ok ()
    let (_, banEvs) ← assertOk banRes "ban overrides allow"
    assertTrue (banEvs.size == 4) s!"expected 4 ban events, got {banEvs.size}"
    for ev in banEvs do
      assertTrue (ev.outcome == .denied && ev.reason.isSome) s!"expected denied ban event, got {repr ev}"
  finally
    stopServer hcSrv

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

private def rtSendAll (fd : LinuxSyscall.RawFd) (bs : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  let mut steps : Nat := 0
  while off < bs.size && steps < bs.size + 64 do
    steps := steps + 1
    let slice := if off == 0 then bs else bs.extract off bs.size
    match ← LinuxSyscall.Net.sendto fd slice { nosignal := true } with
    | .ok n =>
      if n == 0 then
        throw (IO.userError "rtSendAll unexpected zero write")
      off := off + n.toNat
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"rtSendAll sendto failed errno={e}")

private def rtConnectLoopback (port : UInt16) : IO LinuxSyscall.RawFd := do
  match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
  | .error e => throw (IO.userError s!"rtConnectLoopback socket failed errno={e}")
  | .ok fd =>
    let addr := LinuxSyscall.Net.SockAddr.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK port
    match ← LinuxSyscall.Net.connect fd addr with
    | .ok () => return fd
    | .error e =>
      let _ ← LinuxSyscall.Files.close fd
      throw (IO.userError s!"rtConnectLoopback connect failed errno={e}")

private def rtRecvHead (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) : IO String := do
  let mut acc := ByteArray.empty
  let mut waited : Nat := 0
  while waited < timeoutMs do
    match ← LinuxSyscall.Poll.ppoll #[(fd, { pollin := true })] (some { sec := 0, nsec := 20000000 }) with
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"rtRecvHead ppoll failed errno={e}")
    | .ok revs =>
      let rev : LinuxSyscall.Poll.PollEvents := match revs[0]? with | some r => r | none => {}
      if rev.pollin || rev.pollhup || rev.pollerr then
        match ← LinuxSyscall.Net.recvfrom fd 1024 { dontwait := true } with
        | .ok bs =>
          if bs.size == 0 then
            return String.fromUTF8! acc
          acc := acc ++ bs
          let s := String.fromUTF8! acc
          if (s.splitOn "\r\n\r\n").length > 1 then
            return s
        | .error e =>
          if e != LinuxSyscall.Errno.EINTR && e != LinuxSyscall.Errno.EAGAIN then
            return String.fromUTF8! acc
      else
        waited := waited + 20
  return String.fromUTF8! acc

private def waitFlagTrue (flag : IO.Ref Bool) (maxMs : Nat) (label : String) : IO Unit := do
  let mut waited : Nat := 0
  while !(← flag.get) && waited < maxMs do
    IO.sleep 5
    waited := waited + 5
  assertTrue (← flag.get) s!"timed out waiting for {label}"

private def closeSocketpair (a b : LinuxSyscall.RawFd) : IO Unit := do
  let _ ← LinuxSyscall.Files.close a
  let _ ← LinuxSyscall.Files.close b

private def monoMsNow : IO Nat := do
  match ← LinuxSyscall.TimeRand.clock_gettime .monotonic with
  | .ok ts => return SysBridge.timespecToMs ts
  | .error e => throw (IO.userError s!"clock_gettime failed errno={e}")

private def testPerJobDnsWakeupCancelAndEmfile : IO Unit := do
  let fdsStart ← countSelfOpenFds

  let cancelEntered ← IO.mkRef false
  let cancelRelease ← IO.mkRef false
  let (dummyA, dummyB) ← match ← LinuxSyscall.Net.socketpair .unix .stream { nonblock := true, cloexec := true } with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"dummy socketpair failed errno={e}")
  let mut slotOpt : Option SysBridge.IoDnsJob := none
  try
    let (slot', _) ← SysBridge.startDnsIo {} { phase := .done } #[] dummyA "cancel.invalid" 443
      (dnsResolve := fun _ => do
        cancelEntered.set true
        let mut slept : Nat := 0
        while !(← cancelRelease.get) && slept < 5000 do
          IO.sleep 5
          slept := slept + 5
        return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 127 0 0 1])
    match slot'.phase with
    | .dns _ _ _ job =>
      slotOpt := some job
      waitFlagTrue cancelEntered 2000 "cancelled DNS worker entry"
      SysBridge.cancelDnsJobIo job
      assertTrue ((← job.dnsRRef.get).isNone) "cancelDnsJobIo closed dnsR"
      SysBridge.closeDnsReadFd job
      cancelRelease.set true
      let _ ← IO.wait job.task
      let st ← job.stateRef.get
      assertTrue st.cancelled "IoDnsJobState.cancelled recorded true"
      assertTrue st.result?.isNone "cancelled DNS worker skipped writing result?"
    | _ => throw (IO.userError "startDnsIo did not enter .dns phase")
  finally
    cancelRelease.set true
    if let some job := slotOpt then
      let _ ← IO.wait job.task
    closeSocketpair dummyA dummyB
  let fdsAfterCancel ← countSelfOpenFds
  assertTrue (fdsAfterCancel == fdsStart)
    s!"cancelDnsJobIo leaked FDs: before={fdsStart} after={fdsAfterCancel}"

  let slowEntered ← IO.mkRef false
  let slowRelease ← IO.mkRef false
  let slowDone ← IO.mkRef false
  let tbl ← IO.mkRef ({} : SysBridge.IoProxyTable)
  let gatedResolve (host : String) : IO (Except LinuxSyscall.Dns.DnsError (List LinuxSyscall.Dns.DnsAddr)) := do
    if host == "slow.example.invalid" then
      slowEntered.set true
      let mut waited : Nat := 0
      while !(← slowRelease.get) && waited < 5000 do
        IO.sleep 10
        waited := waited + 10
      slowDone.set true
      return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 93 184 216 34]
    else
      return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 127 0 0 1]
  let ops := SysBridge.mkIoRawOps tbl (dnsResolve := gatedResolve)
  let cfg : ProxyConfig :=
    { allowedTargets := #[
        { host := "slow.example.invalid", port := 443 },
        { host := "fast.example.invalid", port := 443 }
      ]
      ipPolicy := { base := .empty }
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 4 } }
  let vcfg ← assertOk (validateConfig cfg) "validate slow/fast config"
  let proxy ← assertOk (← ops.startProxy vcfg
      (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy))
    "startProxy slow/fast"
  let slowSock ← rtConnectLoopback proxy.port
  let mut slowSockClosed := false
  let mut stopped := false
  try
    rtSendAll slowSock "CONNECT slow.example.invalid:443 HTTP/1.1\r\n\r\n".toUTF8
    waitFlagTrue slowEntered 2000 "slow DNS worker start"
    let fastSock ← rtConnectLoopback proxy.port
    try
      rtSendAll fastSock "CONNECT fast.example.invalid:443 HTTP/1.1\r\n\r\n".toUTF8
      let fastResp ← rtRecvHead fastSock 1500
      assertTrue ((fastResp.splitOn "403 Forbidden").length > 1)
        s!"fast slot did not wake independently while slow DNS blocked: {repr fastResp}"
      assertTrue (!(← slowDone.get)) "slow DNS worker should still be blocked after fast slot finished"
    finally
      let _ ← LinuxSyscall.Files.close fastSock
    let t0 ← monoMsNow
    let evs ← assertOk (← ops.stopProxy proxy) "stopProxy while slow DNS blocked"
    stopped := true
    let t1 ← monoMsNow
    let elapsed := t1 - t0
    assertTrue (elapsed < 500)
      s!"stopProxy blocked waiting on slow DNS worker: elapsed={elapsed}ms"
    assertTrue (!(← slowDone.get)) "slow DNS worker should still be blocked when stopProxy returns"
    assertTrue ((← ops.activeProxyCount) == 0) "activeProxyCount == 0 right after instant stop"
    assertTrue (evs.any fun e => e.host == some "slow.example.invalid" && e.outcome == .failed && e.reason == some "proxy stopped")
      s!"expected proxy stopped event for slow.example.invalid, got {repr evs}"
    let _ ← LinuxSyscall.Files.close slowSock
    slowSockClosed := true

    let canaryA ← match ← LinuxSyscall.Net.socketpair .unix .stream { nonblock := true, cloexec := true } with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"canaryA socketpair failed errno={e}")
    let canaryB ← match ← LinuxSyscall.Net.socketpair .unix .stream { nonblock := true, cloexec := true } with
      | .ok p => pure p
      | .error e =>
        closeSocketpair canaryA.1 canaryA.2
        throw (IO.userError s!"canaryB socketpair failed errno={e}")
    try
      rtSendAll canaryA.2 "CANARY_A".toUTF8
      rtSendAll canaryB.2 "CANARY_B".toUTF8
      slowRelease.set true
      waitFlagTrue slowDone 2000 "slow DNS worker post-stop exit"
      IO.sleep 30
      let gotA ← match ← LinuxSyscall.Net.recvfrom canaryA.1 64 { dontwait := true } with
        | .ok bs => pure (String.fromUTF8! bs)
        | .error e => throw (IO.userError s!"canaryA recv failed after slow DNS exit errno={e}")
      let gotB ← match ← LinuxSyscall.Net.recvfrom canaryB.1 64 { dontwait := true } with
        | .ok bs => pure (String.fromUTF8! bs)
        | .error e => throw (IO.userError s!"canaryB recv failed after slow DNS exit errno={e}")
      assertTrue (gotA == "CANARY_A" && gotB == "CANARY_B")
        s!"fresh FD canary corrupted after post-stop DNS completion: A={repr gotA} B={repr gotB}"
      let pollAfter ← match ← LinuxSyscall.Poll.ppoll #[(canaryA.1, { pollin := true }), (canaryB.1, { pollin := true })] (some { sec := 0, nsec := 0 }) with
        | .ok rs => pure rs
        | .error e => throw (IO.userError s!"canary ppoll failed errno={e}")
      let rA : LinuxSyscall.Poll.PollEvents := match pollAfter[0]? with | some r => r | none => {}
      let rB : LinuxSyscall.Poll.PollEvents := match pollAfter[1]? with | some r => r | none => {}
      assertTrue (!rA.pollin && !rA.pollhup && !rA.pollerr && !rA.pollnval &&
          !rB.pollin && !rB.pollhup && !rB.pollerr && !rB.pollnval)
        s!"unexpected event on reused canary FDs: rA={repr rA} rB={repr rB}"
    finally
      closeSocketpair canaryA.1 canaryA.2
      closeSocketpair canaryB.1 canaryB.2
  finally
    slowRelease.set true
    if !slowSockClosed then
      let _ ← LinuxSyscall.Files.close slowSock
    if !stopped then
      let _ ← ops.stopProxy proxy
  let mut fdMatch := false
  for _ in [:40] do
    let curFds ← countSelfOpenFds
    if curFds == fdsStart then
      fdMatch := true
      break
    IO.sleep 10
  let fdsAfterSlow ← countSelfOpenFds
  assertTrue fdMatch
    s!"slow DNS worker leaked dnsW FD after exit: before={fdsStart} after={fdsAfterSlow}"

  let emTbl ← IO.mkRef ({} : SysBridge.IoProxyTable)
  let emOps := SysBridge.mkIoRawOps emTbl
    (mkWakePair := pure (.error LinuxSyscall.Errno.EMFILE))
  let emCfg : ProxyConfig :=
    { allowedTargets := #[{ host := "emfile.example.invalid", port := 443 }]
      limits := { headerTimeoutMs := 1500, connectTimeoutMs := 1500, maxConcurrentTunnels := 2 } }
  let emVcfg ← assertOk (validateConfig emCfg) "validate emfile config"
  let emPrx ← assertOk (← emOps.startProxy emVcfg
      (Model.decideConnectHead emVcfg.config) (Model.decideResolvedIps emVcfg.config.ipPolicy))
    "startProxy emfile"
  let emSock ← rtConnectLoopback emPrx.port
  let emResp ← try
      rtSendAll emSock "CONNECT emfile.example.invalid:443 HTTP/1.1\r\n\r\n".toUTF8
      rtRecvHead emSock 1500
    finally
      let _ ← LinuxSyscall.Files.close emSock
  let emEvs ← assertOk (← emOps.stopProxy emPrx) "stopProxy emfile"
  assertTrue ((emResp.splitOn "503 Service Unavailable").length > 1)
    s!"expected HTTP 503 on DNS wakeup socketpair EMFILE, got {repr emResp}"
  assertTrue (emEvs.size == 1 && emEvs[0]!.outcome == .failed)
    s!"expected single failed event on socketpair EMFILE, got {repr emEvs}"
  let fdsEnd ← countSelfOpenFds
  assertTrue (fdsEnd == fdsStart)
    s!"socketpair EMFILE path leaked FDs: before={fdsStart} after={fdsEnd}"

private def sendConnectThenResetViaPython
    (port : UInt16) (host : String) (enteredFlag : IO.Ref Bool) : IO Unit := do
  let script :=
    "import select, socket, struct, sys\n" ++
    "s = socket.create_connection(('127.0.0.1', int(sys.argv[1])), timeout=5)\n" ++
    "req = f'CONNECT {sys.argv[2]}:443 HTTP/1.1\\r\\n\\r\\n'.encode('ascii')\n" ++
    "s.sendall(req)\n" ++
    "r, _, _ = select.select([sys.stdin], [], [], 5.0)\n" ++
    "if r:\n" ++
    "  sys.stdin.read(1)\n" ++
    "s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack('ii', 1, 0))\n" ++
    "s.close()\n"
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c", script, toString port, host]
    stdin := .piped
    stdout := .null
    stderr := .null
  }
  let (stdinH, child2) ← child.takeStdin
  try
    waitFlagTrue enteredFlag 2000 s!"DNS worker entry for {host}"
    stdinH.putStr "x"
    stdinH.flush
  finally
    let rc ← child2.wait
    if rc != 0 then
      throw (IO.userError s!"RST client exited with code {rc}")

private def waitForFdCount (target : Nat) (maxMs : Nat) (label : String) : IO Unit := do
  let mut waited : Nat := 0
  let mut cur ← countSelfOpenFds
  while cur != target && waited < maxMs do
    IO.sleep 10
    waited := waited + 10
    cur ← countSelfOpenFds
  assertTrue (cur == target)
    s!"{label}: expected open FDs {target}, got {cur}"

private def testDetachedDnsWakeupAtMaxConcurrency : IO Unit := do
  let fdsStart ← countSelfOpenFds

  let slow1Entered ← IO.mkRef false
  let slow1Release ← IO.mkRef false
  let slow1Done ← IO.mkRef false
  let fastCalled ← IO.mkRef false
  let tbl ← IO.mkRef ({} : SysBridge.IoProxyTable)
  let resolve1 (host : String) : IO (Except LinuxSyscall.Dns.DnsError (List LinuxSyscall.Dns.DnsAddr)) := do
    if host == "detached-slow.example.invalid" then
      slow1Entered.set true
      let mut waited : Nat := 0
      while !(← slow1Release.get) && waited < 5000 do
        IO.sleep 5
        waited := waited + 5
      slow1Done.set true
      return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 93 184 216 34]
    else
      fastCalled.set true
      return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 127 0 0 1]
  let ops := SysBridge.mkIoRawOps tbl (dnsResolve := resolve1)
  let cfg : ProxyConfig :=
    { allowedTargets := #[
        { host := "detached-slow.example.invalid", port := 443 },
        { host := "after-detached.example.invalid", port := 443 }
      ]
      ipPolicy := { base := .empty }
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 1 } }
  let vcfg ← assertOk (validateConfig cfg) "validate detached-dns max=1 config"
  let proxy ← assertOk (← ops.startProxy vcfg
      (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy))
    "startProxy detached-dns max=1"
  let mut stopped := false
  try
    sendConnectThenResetViaPython proxy.port "detached-slow.example.invalid" slow1Entered
    IO.sleep 80
    let c2 ← rtConnectLoopback proxy.port
    let resp2 ← try
        rtSendAll c2 "CONNECT after-detached.example.invalid:443 HTTP/1.1\r\n\r\n".toUTF8
        IO.sleep 40
        assertTrue (!(← fastCalled.get))
          "maxConcurrentTunnels=1 must stay saturated while detached DNS task is active"
        let tWake ← monoMsNow
        slow1Release.set true
        let r ← rtRecvHead c2 1500
        let wakeMs := (← monoMsNow) - tWake
        assertTrue (wakeMs < 1000)
          s!"proxy failed to wake promptly after detached DNS completed: wakeMs={wakeMs} resp={repr r}"
        pure r
      finally
        let _ ← LinuxSyscall.Files.close c2
    assertTrue ((resp2.splitOn "403 Forbidden").length > 1)
      s!"expected client 2 to receive 403 Forbidden after detached DNS wakeup, got {repr resp2}"
    waitFlagTrue slow1Done 2000 "detached slow DNS completion"
    let evs ← assertOk (← ops.stopProxy proxy) "stopProxy detached-dns max=1"
    stopped := true
    assertTrue (evs.any fun e => e.host == some "detached-slow.example.invalid" &&
        e.outcome == .failed && e.reason == some "client disconnected")
      s!"expected client disconnected event for detached slow DNS, got {repr evs}"
    assertTrue (evs.any fun e => e.host == some "after-detached.example.invalid" &&
        e.outcome == .denied)
      s!"expected denied event for after-detached client, got {repr evs}"
  finally
    slow1Release.set true
    if !stopped then
      let _ ← ops.stopProxy proxy
  waitForFdCount fdsStart 1000 "detached DNS wakeup FD cleanup"

  let slow2Entered ← IO.mkRef false
  let slow2Release ← IO.mkRef false
  let slow2Done ← IO.mkRef false
  let tbl2 ← IO.mkRef ({} : SysBridge.IoProxyTable)
  let resolve2 (_host : String) : IO (Except LinuxSyscall.Dns.DnsError (List LinuxSyscall.Dns.DnsAddr)) := do
    slow2Entered.set true
    let mut waited : Nat := 0
    while !(← slow2Release.get) && waited < 5000 do
      IO.sleep 5
      waited := waited + 5
    slow2Done.set true
    return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 93 184 216 34]
  let ops2 := SysBridge.mkIoRawOps tbl2 (dnsResolve := resolve2)
  let cfg2 : ProxyConfig :=
    { allowedTargets := #[{ host := "teardown-detached.example.invalid", port := 443 }]
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 1 } }
  let vcfg2 ← assertOk (validateConfig cfg2) "validate detached teardown config"
  let proxy2 ← assertOk (← ops2.startProxy vcfg2
      (Model.decideConnectHead vcfg2.config) (Model.decideResolvedIps vcfg2.config.ipPolicy))
    "startProxy detached teardown"
  let mut stopped2 := false
  try
    sendConnectThenResetViaPython proxy2.port "teardown-detached.example.invalid" slow2Entered
    IO.sleep 80
    let tStop ← monoMsNow
    let evs2 ← assertOk (← ops2.stopProxy proxy2) "stopProxy with pending detached DNS"
    stopped2 := true
    let stopMs := (← monoMsNow) - tStop
    assertTrue (stopMs < 500)
      s!"stopProxy blocked waiting for detached DNS task: elapsed={stopMs}ms"
    assertTrue (evs2.any fun e => e.host == some "teardown-detached.example.invalid" &&
        e.outcome == .failed && e.reason == some "client disconnected")
      s!"expected client disconnected event before stopProxy teardown, got {repr evs2}"
    let fdsWhileSlow ← countSelfOpenFds
    assertTrue (fdsWhileSlow ≤ fdsStart + 1)
      s!"teardownIoLoopState must close detached dnsR immediately: base={fdsStart} cur={fdsWhileSlow}"
    slow2Release.set true
    waitFlagTrue slow2Done 2000 "detached teardown slow worker completion"
  finally
    slow2Release.set true
    if !stopped2 then
      let _ ← ops2.stopProxy proxy2
  waitForFdCount fdsStart 1000 "detached DNS teardown FD cleanup"

/-- Execute end-to-end OS network and Python differential runtime tests for `LeanSwe.ConnectProxy`. -/
def runAll : IO Unit := do
  let fdsBefore ← countSelfOpenFds
  assertErrKind (← withProxy { limits := { maxHeaderBytes := 0 } } fun _ => pure (.ok ()))
    .invalidInput "withProxy invalid config rejected"
  runPythonIpaddressDifferential
  testTunnelPipelineHalfCloseFailoverAndCurl
  testDenialsPublicOnlyBansAndPostBody
  testLimitsTimeoutOversizeConcurrencyAnd502
  testCallbackErrorInFlightStopAndParallel
  testPerJobDnsWakeupCancelAndEmfile
  testDetachedDnsWakeupAtMaxConcurrency
  Core.runRegisteredErrorTests registeredErrorTests
  let fdsAfter ← countSelfOpenFds
  assertTrue (fdsAfter == fdsBefore)
    s!"ConnectProxy.RuntimeTests leaked file descriptors: before={fdsBefore} after={fdsAfter}"
  printlnSafe "PASS: LeanSwe.ConnectProxy runtime tests"

end LeanSwe.ConnectProxy.RuntimeTests
