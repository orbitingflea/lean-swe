import Tests.Common
import Tests.Mutate.NetRelay
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.RuntimeTests

namespace Tests.Mutate.ConnectProxy

open LeanSwe
open Tests.Common

private def cproxySendAll (fd : LinuxSyscall.RawFd) (bs : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  let mut guard : Nat := 0
  while off < bs.size && guard < bs.size + 64 do
    guard := guard + 1
    let slice := if off == 0 then bs else bs.extract off bs.size
    match ← LinuxSyscall.Net.sendto fd slice { nosignal := true } with
    | .ok n =>
      if n == 0 then
        throw (IO.userError "cproxySendAll unexpected 0-byte send")
      off := off + n.toNat
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"cproxySendAll sendto failed: {e}")

private def cproxyWaitPollin (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) : IO Bool := do
  let ts : LinuxSyscall.Poll.Timespec :=
    { sec := Int64.ofNat (timeoutMs / 1000)
      nsec := UInt32.ofNat ((timeoutMs % 1000) * 1000000) }
  let mut retries : Nat := 8
  while retries > 0 do
    retries := retries - 1
    match ← LinuxSyscall.Poll.ppoll #[(fd, { pollin := true })] (some ts) with
    | .ok rev =>
      let ev := rev[0]?.getD ({} : LinuxSyscall.Poll.PollEvents)
      return (ev.pollin || ev.pollhup || ev.pollerr)
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        return false
  return false

private def cproxyRecvAllUntilEof (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) (maxBytes : Nat := 131072) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut done := false
  let mut steps : Nat := 0
  while !done && steps < 4096 && acc.size < maxBytes do
    steps := steps + 1
    if !(← cproxyWaitPollin fd timeoutMs) then
      throw (IO.userError s!"cproxyRecvAllUntilEof timed out at {acc.size} bytes")
    match ← LinuxSyscall.Net.recvfrom fd 8192 {} with
    | .ok chunk =>
      if chunk.size == 0 then
        done := true
      else
        acc := acc ++ chunk
    | .error e =>
      if e == LinuxSyscall.Errno.ECONNRESET then
        done := true
      else if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"cproxyRecvAllUntilEof recvfrom failed: {e}")
  return acc

private def cproxyRecvUntilHeadEnd (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut steps : Nat := 0
  while steps < 256 do
    steps := steps + 1
    if !(← cproxyWaitPollin fd timeoutMs) then
      throw (IO.userError "cproxyRecvUntilHeadEnd timed out")
    match ← LinuxSyscall.Net.recvfrom fd 1024 {} with
    | .ok chunk =>
      if chunk.size == 0 then
        return acc
      acc := acc ++ chunk
      if (LeanSwe.ConnectProxy.SysBridge.findCrlfCrlf acc 0).isSome then
        return acc
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        return acc
  return acc

private def cproxyBindLoopbackServer : IO (LinuxSyscall.RawFd × UInt16) := do
  let sfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"server socket failed: {e}")
  let _ ← LinuxSyscall.Net.setsockopt sfd .reuseAddr 1
  match ← LinuxSyscall.Net.bind sfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 0) with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"server bind failed: {e}")
  match ← LinuxSyscall.Net.listen sfd 16 with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"server listen failed: {e}")
  match ← LinuxSyscall.Net.getsockname sfd with
  | .ok (.ipv4 _ port) => return (sfd, port)
  | _ =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError "server getsockname unexpected sockaddr")

private def cproxyDialLoopback (port : UInt16) : IO LinuxSyscall.RawFd := do
  let cfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"client socket failed: {e}")
  match ← LinuxSyscall.Net.connect cfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK port) with
  | .ok () => return cfd
  | .error e =>
    let _ ← LinuxSyscall.Files.close cfd
    throw (IO.userError s!"client connect failed: {e}")

private def runConnectProxyUnitTests : IO Unit := do
  checkUnit "cproxy parseIpAddr" (LeanSwe.ConnectProxy.parseIpAddr "127.0.0.1" == .ok (.v4 0x7f000001))
  checkUnit "cproxy parseIpAddr bad" (!(LeanSwe.ConnectProxy.parseIpAddr "10.1*").isOk)
  checkUnit "cproxy parseIpPrefix" (LeanSwe.ConnectProxy.parseIpPrefix "10.1.0.0/16" == .ok (.v4 0x0a010000 16))
  checkUnit "cproxy isGlobalIp" (LeanSwe.ConnectProxy.isGlobalIp (.v4 0x08080808) && !LeanSwe.ConnectProxy.isGlobalIp (.v4 0x7f000001))
  let pol : LeanSwe.ConnectProxy.IpPolicy := { base := .empty, extraAllows := #[.v4 0x0a000000 8], extraBans := #[.v4 0x0a000100 24] }
  checkUnit "cproxy allowsIp" (LeanSwe.ConnectProxy.allowsIp pol (.v4 0x0a000201) && !LeanSwe.ConnectProxy.allowsIp pol (.v4 0x0a000101))
  checkUnit "cproxy parseConnectRequest"
    (LeanSwe.ConnectProxy.parseConnectRequest "CONNECT Example.COM:443 HTTP/1.1\r\n\r\n".toUTF8 ==
      .ok { host := "example.com", port := 443 })
  checkUnit "cproxy validateConfig"
    ((LeanSwe.ConnectProxy.validateConfig { allowedTargets := #[{ host := "Example.COM", port := 443 }] }).isOk &&
     !(LeanSwe.ConnectProxy.validateConfig { limits := { maxHeaderBytes := 0 } }).isOk)
  let mockApi := LeanSwe.ConnectProxy.Internal.mkApiM LeanSwe.ConnectProxy.Model.mockRawProxyOps
  let (mockRes, mockSt) := (mockApi.withProxy { allowedTargets := #[{ host := "example.com", port := 443 }] }
    fun p => pure (.ok p.port)).run { ephemeralPort := 54321 }
  checkUnit "cproxy mkApiM mock" (mockRes == .ok (54321, #[]) && mockSt.activeHandles == [])
  Tests.Mutate.NetRelay.runConnectProxyScriptedTests
  let (rstSrv, rstPort) ← cproxyBindLoopbackServer
  let rstPayload := ByteArray.mk (Array.replicate 4096 0x5a)
  let rstTask ← IO.asTask (prio := .dedicated) do
    if ← cproxyWaitPollin rstSrv 1500 then
      match ← LinuxSyscall.Net.accept4 rstSrv { cloexec := true } with
      | .ok (ufd, _) =>
        cproxySendAll ufd rstPayload
        let _ ← LinuxSyscall.Files.close ufd
      | .error _ => pure ()
    let _ ← LinuxSyscall.Files.close rstSrv
  let liveCfg : LeanSwe.ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := rstPort },
        { host := "allowed.example.com", port := 443 }
      ]
      ipPolicy := { base := .empty, extraAllows := #[.v4 0x7f000000 8] } }
  let liveRes ← LeanSwe.ConnectProxy.withProxy liveCfg fun proxy => do
    let cfdDeny ← cproxyDialLoopback proxy.port
    cproxySendAll cfdDeny "CONNECT blocked.example.com:443 HTTP/1.1\r\nHost: blocked.example.com:443\r\n\r\n".toUTF8
    let denyBytes ← cproxyRecvUntilHeadEnd cfdDeny 800
    let _ ← LinuxSyscall.Files.close cfdDeny
    if ((String.fromUTF8! denyBytes).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "expected 403 on blocked target" }
    let cfdRst ← cproxyDialLoopback proxy.port
    let reqRst := s!"CONNECT 127.0.0.1:{rstPort} HTTP/1.1\r\nHost: 127.0.0.1:{rstPort}\r\n\r\nUNREAD_CLIENT_TAIL".toUTF8
    cproxySendAll cfdRst reqRst
    let allRst ← cproxyRecvAllUntilEof cfdRst 1200 16384
    let _ ← LinuxSyscall.Files.close cfdRst
    if allRst.size != LeanSwe.ConnectProxy.Relay.reply200Bytes.size + rstPayload.size then
      return .error { kind := .ioError, message := s!"TCP RST lost bytes: got {allRst.size}" }
    return .ok proxy.port
  let _ ← IO.wait rstTask
  match liveRes with
  | .ok (boundPort, evs) =>
    checkUnit "cproxy live loopback + RST conservation"
      (boundPort != 0 && evs.size == 2 &&
       evs[0]?.map (·.outcome) == some .denied &&
       evs[1]?.map (·.outcome) == some .allowed)
  | .error e =>
    throw (IO.userError s!"ConnectProxy live loopback failed: {repr e}")

private def countSelfOpenFds : IO Nat := do
  return (← (System.FilePath.mk "/proc/self/fd").readDir).size

private def cproxyReserveUnlisteningLoopback : IO (LinuxSyscall.RawFd × UInt16) := do
  let sfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"reserve socket failed: {e}")
  match ← LinuxSyscall.Net.bind sfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 0) with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"reserve bind failed: {e}")
  match ← LinuxSyscall.Net.getsockname sfd with
  | .ok (.ipv4 _ port) => return (sfd, port)
  | _ =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError "reserve getsockname unexpected sockaddr")

private def runConnectProxyMutateExtra : IO Unit := do
  let fdsBefore ← countSelfOpenFds
  let (echoSrv, echoPort) ← cproxyBindLoopbackServer
  let (deadSock, deadPort) ← cproxyReserveUnlisteningLoopback
  let echoTask ← IO.asTask (prio := .dedicated) do
    for _ in [0 : 2] do
      if ← cproxyWaitPollin echoSrv 2000 then
        match ← LinuxSyscall.Net.accept4 echoSrv { cloexec := true } with
        | .ok (ufd, _) =>
          let rx ← cproxyRecvAllUntilEof ufd 1500 65536
          cproxySendAll ufd ("ACK:".toUTF8 ++ rx)
          let _ ← LinuxSyscall.Net.shutdown ufd .wr
          let _ ← LinuxSyscall.Files.close ufd
        | .error _ => pure ()
    let _ ← LinuxSyscall.Files.close echoSrv
  let cfg : LeanSwe.ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := echoPort },
        { host := "localhost", port := echoPort },
        { host := "127.0.0.1", port := deadPort }
      ]
      ipPolicy := { base := .empty, extraAllows := #[.v4 0x7f000000 8, .v6 0 1 128] }
      limits :=
        { maxHeaderBytes := 128
          headerTimeoutMs := 120
          connectTimeoutMs := 300
          maxConcurrentTunnels := 2 } }
  let streamBody := ByteArray.mk ((List.range 36000).toArray.map fun i => UInt8.ofNat (i % 251))
  let sessRes ← LeanSwe.ConnectProxy.withProxy cfg fun proxy => do
    let cStream ← cproxyDialLoopback proxy.port
    let headWithPipe := s!"CONNECT 127.0.0.1:{echoPort} HTTP/1.1\r\n\r\nPIPE!".toUTF8
    cproxySendAll cStream headWithPipe
    cproxySendAll cStream streamBody
    let _ ← LinuxSyscall.Net.shutdown cStream .wr
    let gotStream ← cproxyRecvAllUntilEof cStream 1500 65536
    let _ ← LinuxSyscall.Files.close cStream
    let expectedStream := LeanSwe.ConnectProxy.Relay.reply200Bytes ++ "ACK:PIPE!".toUTF8 ++ streamBody
    if gotStream != expectedStream then
      return .error { kind := .ioError, message := s!"stream mismatch: got={gotStream.size} expected={expectedStream.size}" }
    let cDns ← cproxyDialLoopback proxy.port
    cproxySendAll cDns s!"CONNECT localhost:{echoPort} HTTP/1.1\r\n\r\nDNSOK".toUTF8
    let _ ← LinuxSyscall.Net.shutdown cDns .wr
    let gotDns ← cproxyRecvAllUntilEof cDns 1500 4096
    let _ ← LinuxSyscall.Files.close cDns
    if gotDns != LeanSwe.ConnectProxy.Relay.reply200Bytes ++ "ACK:DNSOK".toUTF8 then
      return .error { kind := .ioError, message := s!"localhost DNS relay mismatch: {gotDns.size}" }
    let cOver ← cproxyDialLoopback proxy.port
    let overBytes := ByteArray.mk (Array.replicate 132 65)
    cproxySendAll cOver overBytes
    let gotOver ← cproxyRecvUntilHeadEnd cOver 800
    let _ ← LinuxSyscall.Files.close cOver
    if ((String.fromUTF8! gotOver).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "oversized header did not return 403" }
    let cSlow ← cproxyDialLoopback proxy.port
    cproxySendAll cSlow s!"CONNECT 127.0.0.1:{echoPort} HTTP/1.1\r\n".toUTF8
    let gotSlow ← cproxyRecvUntilHeadEnd cSlow 800
    let _ ← LinuxSyscall.Files.close cSlow
    if ((String.fromUTF8! gotSlow).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "slow header timeout did not return 403" }
    let cDead ← cproxyDialLoopback proxy.port
    cproxySendAll cDead s!"CONNECT 127.0.0.1:{deadPort} HTTP/1.1\r\n\r\n".toUTF8
    let gotDead ← cproxyRecvUntilHeadEnd cDead 800
    let _ ← LinuxSyscall.Files.close cDead
    if ((String.fromUTF8! gotDead).splitOn "502").length <= 1 then
      return .error { kind := .ioError, message := "refused upstream did not return 502" }
    return .ok ()
  let _ ← IO.wait echoTask
  let _ ← LinuxSyscall.Files.close deadSock
  match sessRes with
  | .error e => throw (IO.userError s!"runConnectProxyMutateExtra session failed: {repr e}")
  | .ok ((), evs) =>
    checkUnit "cproxy extra events" (evs.size == 5)
  let banCfg : LeanSwe.ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[{ host := "localhost", port := 443 }]
      ipPolicy :=
        { base := .empty
          extraAllows := #[.v4 0x7f000000 8, .v6 0 1 128]
          extraBans := #[.v4 0x7f000000 8, .v6 0 1 128] } }
  let banRes ← LeanSwe.ConnectProxy.withProxy banCfg fun proxy => do
    let cBan ← cproxyDialLoopback proxy.port
    cproxySendAll cBan "CONNECT localhost:443 HTTP/1.1\r\n\r\n".toUTF8
    let gotBan ← cproxyRecvUntilHeadEnd cBan 800
    let _ ← LinuxSyscall.Files.close cBan
    if ((String.fromUTF8! gotBan).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "banned resolved IP did not return 403" }
    return .ok ()
  match banRes with
  | .error e => throw (IO.userError s!"cproxy DNS IP ban failed: {repr e}")
  | .ok ((), banEvs) =>
    checkUnit "cproxy DNS IP ban event"
      (banEvs.size == 1 && banEvs[0]?.map (·.outcome) == some .denied)
  let fdsAfter ← countSelfOpenFds
  checkUnit "cproxy zero FD leaks across sessions" (fdsAfter == fdsBefore)

/-- Mutation test suite for `LeanSwe.ConnectProxy`. -/
def connectProxySuite : MutateSuite :=
  { name := "ConnectProxy"
    runBase := do LeanSwe.ConnectProxy.RuntimeTests.runAll; return none
    runExtra := do runConnectProxyUnitTests; runConnectProxyMutateExtra }

end Tests.Mutate.ConnectProxy
