import Core.ConcOps
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.RuntimeTests.TunnelTests

namespace LeanSwe.ConnectProxy.RuntimeTests

open LeanSwe.ConnectProxy

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
  | .ok ts => return LinuxSyscall.TimeRand.timespecToMs ts
  | .error e => throw (IO.userError s!"clock_gettime failed errno={e}")

private def waitForFdCount (target : Nat) (maxMs : Nat) (label : String) : IO Unit := do
  let mut waited : Nat := 0
  let mut cur ← countSelfOpenFds
  while cur != target && waited < maxMs do
    IO.sleep 10
    waited := waited + 10
    cur ← countSelfOpenFds
  assertTrue (cur == target)
    s!"{label}: expected open FDs {target}, got {cur}"

private def mkCustomIoSys
    (dnsResolve? : Option (String → IO (Except LinuxSyscall.Dns.DnsError (List LinuxSyscall.Dns.DnsAddr))) := none)
    (failSecondSocketpair : Bool := false) : IO (SysBridge.CProxySysOpsM IO LinuxSyscall.RawFd) := do
  let spCalls ← IO.mkRef (0 : Nat)
  let baseNet := LinuxSyscall.Net.defaultOps
  let netOps : LinuxSyscall.Net.NetOpsM IO LinuxSyscall.RawFd :=
    if failSecondSocketpair then
      { baseNet with
        socketpair := fun dom st fl => do
          let n ← spCalls.modifyGet fun k => (k, k + 1)
          if n == 0 then baseNet.socketpair dom st fl
          else pure (.error LinuxSyscall.Errno.EMFILE) }
    else
      baseNet
  let dnsOps : LinuxSyscall.Dns.DnsOpsM IO :=
    match dnsResolve? with
    | some f => { getaddrinfo := fun h _ => f h }
    | none => LinuxSyscall.Dns.defaultOps
  return {
    files := LinuxSyscall.Files.defaultOps
    net := netOps
    poll := LinuxSyscall.Poll.defaultOps
    dns := dnsOps
    timeRand := LinuxSyscall.TimeRand.defaultOps
  }

/-- Exercise `Driver.lean` + `Core.ioConcOps` on per-job `socketpair` DNS wakeup, non-blocking
    shutdown while slow DNS is blocked, FD canary safety, and HTTP `503` on `EMFILE`. -/
def testPerJobDnsWakeupCancelAndEmfile : IO Unit := do
  let fdsStart ← countSelfOpenFds

  let cancelEntered ← IO.mkRef false
  let cancelRelease ← IO.mkRef false
  let (dummyA, dummyB) ← match ← LinuxSyscall.Net.socketpair .unix .stream { nonblock := true, cloexec := true } with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"dummy socketpair failed errno={e}")
  let cancelSys ← mkCustomIoSys (dnsResolve? := some fun _ => do
    cancelEntered.set true
    let mut slept : Nat := 0
    while !(← cancelRelease.get) && slept < 5000 do
      IO.sleep 5
      slept := slept + 5
    return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 127 0 0 1])
  let mut slotOpt : Option (SysBridge.Driver.ConcDnsJob LinuxSyscall.RawFd Core.ioConcOps.Ref Core.ioConcOps.TaskHandle) := none
  try
    let (slot', _) ← SysBridge.Driver.startDnsM cancelSys Core.ioConcOps {} { phase := .done } #[] dummyA "cancel.invalid" 443
    match slot'.phase with
    | .dns _ _ _ dj =>
      slotOpt := some dj
      waitFlagTrue cancelEntered 2000 "cancelled DNS worker entry"
      SysBridge.Driver.cancelAndCloseDnsM cancelSys Core.ioConcOps dj
      cancelRelease.set true
      let _ ← Core.ioConcOps.waitTask dj.task
      let st ← Core.ioConcOps.readRef dj.stateRef
      assertTrue st.cancelled "DnsJobState.cancelled recorded true"
      assertTrue st.result?.isNone "cancelled DNS worker skipped writing result?"
    | _ => throw (IO.userError "startDnsM did not enter .dns phase")
  finally
    cancelRelease.set true
    if let some dj := slotOpt then
      let _ ← Core.ioConcOps.waitTask dj.task
    closeSocketpair dummyA dummyB
  waitForFdCount fdsStart 1000 "cancelAndCloseDnsM FD cleanup"

  let slowEntered ← IO.mkRef false
  let slowRelease ← IO.mkRef false
  let slowDone ← IO.mkRef false
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
  let slowSys ← mkCustomIoSys (dnsResolve? := some gatedResolve)
  let slowApi := Internal.mkFullApiM slowSys Core.ioConcOps
  let cfg : ProxyConfig :=
    { allowedTargets := #[
        { host := "slow.example.invalid", port := 443 },
        { host := "fast.example.invalid", port := 443 }
      ]
      ipPolicy := { base := .empty }
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 4 } }
  let stopStartRef ← IO.mkRef (0 : Nat)
  let slowSockRef ← IO.mkRef (none : Option LinuxSyscall.RawFd)
  try
    let res ← slowApi.withProxy cfg fun proxy => do
      let slowSock ← rtConnectLoopback proxy.port
      slowSockRef.set (some slowSock)
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
      stopStartRef.set (← monoMsNow)
      return .ok ()
    let t1 ← monoMsNow
    let (_, evs) ← assertOk res "withProxy while slow DNS blocked"
    let elapsed := t1 - (← stopStartRef.get)
    assertTrue (elapsed < 500)
      s!"Driver.withProxyM blocked waiting on slow DNS worker: elapsed={elapsed}ms"
    assertTrue (!(← slowDone.get)) "slow DNS worker should still be blocked when withProxy returns"
    assertTrue (evs.any fun e => e.host == some "slow.example.invalid" && e.outcome == .failed && e.reason == some "proxy stopped")
      s!"expected proxy stopped event for slow.example.invalid, got {repr evs}"
    if let some fd ← slowSockRef.modifyGet fun s => (s, none) then
      let _ ← LinuxSyscall.Files.close fd
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
    finally
      closeSocketpair canaryA.1 canaryA.2
      closeSocketpair canaryB.1 canaryB.2
  finally
    slowRelease.set true
    if let some fd ← slowSockRef.modifyGet fun s => (s, none) then
      let _ ← LinuxSyscall.Files.close fd
  waitForFdCount fdsStart 1000 "slow DNS worker FD cleanup"

  let emSys ← mkCustomIoSys (failSecondSocketpair := true)
  let emApi := Internal.mkFullApiM emSys Core.ioConcOps
  let emCfg : ProxyConfig :=
    { allowedTargets := #[{ host := "emfile.example.invalid", port := 443 }]
      limits := { headerTimeoutMs := 1500, connectTimeoutMs := 1500, maxConcurrentTunnels := 2 } }
  let emRes ← emApi.withProxy emCfg fun emPrx => do
    let emSock ← rtConnectLoopback emPrx.port
    try
      rtSendAll emSock "CONNECT emfile.example.invalid:443 HTTP/1.1\r\n\r\n".toUTF8
      let emResp ← rtRecvHead emSock 1500
      return .ok emResp
    finally
      let _ ← LinuxSyscall.Files.close emSock
  let (emResp, emEvs) ← assertOk emRes "withProxy emfile"
  assertTrue ((emResp.splitOn "503 Service Unavailable").length > 1)
    s!"expected HTTP 503 on DNS wakeup socketpair EMFILE, got {repr emResp}"
  assertTrue (emEvs.size == 1 && emEvs[0]!.outcome == .failed)
    s!"expected single failed event on socketpair EMFILE, got {repr emEvs}"
  waitForFdCount fdsStart 1000 "socketpair EMFILE FD cleanup"

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

/-- Exercise `Driver.lean` + `Core.ioConcOps` detached DNS wakeup at `maxConcurrentTunnels = 1`
    and non-blocking teardown with a pending detached DNS job. -/
def testDetachedDnsWakeupAtMaxConcurrency : IO Unit := do
  let fdsStart ← countSelfOpenFds

  let slow1Entered ← IO.mkRef false
  let slow1Release ← IO.mkRef false
  let slow1Done ← IO.mkRef false
  let fastCalled ← IO.mkRef false
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
  let sys1 ← mkCustomIoSys (dnsResolve? := some resolve1)
  let api1 := Internal.mkFullApiM sys1 Core.ioConcOps
  let cfg : ProxyConfig :=
    { allowedTargets := #[
        { host := "detached-slow.example.invalid", port := 443 },
        { host := "after-detached.example.invalid", port := 443 }
      ]
      ipPolicy := { base := .empty }
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 1 } }
  try
    let res1 ← api1.withProxy cfg fun proxy => do
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
      return .ok ()
    let (_, evs) ← assertOk res1 "withProxy detached-dns max=1"
    assertTrue (evs.any fun e => e.host == some "detached-slow.example.invalid" &&
        e.outcome == .failed && e.reason == some "client disconnected")
      s!"expected client disconnected event for detached slow DNS, got {repr evs}"
    assertTrue (evs.any fun e => e.host == some "after-detached.example.invalid" &&
        e.outcome == .denied)
      s!"expected denied event for after-detached client, got {repr evs}"
  finally
    slow1Release.set true
  waitForFdCount fdsStart 1000 "detached DNS wakeup FD cleanup"

  let slow2Entered ← IO.mkRef false
  let slow2Release ← IO.mkRef false
  let slow2Done ← IO.mkRef false
  let resolve2 (_host : String) : IO (Except LinuxSyscall.Dns.DnsError (List LinuxSyscall.Dns.DnsAddr)) := do
    slow2Entered.set true
    let mut waited : Nat := 0
    while !(← slow2Release.get) && waited < 5000 do
      IO.sleep 5
      waited := waited + 5
    slow2Done.set true
    return .ok [LinuxSyscall.Dns.DnsAddr.ipv4 93 184 216 34]
  let sys2 ← mkCustomIoSys (dnsResolve? := some resolve2)
  let api2 := Internal.mkFullApiM sys2 Core.ioConcOps
  let cfg2 : ProxyConfig :=
    { allowedTargets := #[{ host := "teardown-detached.example.invalid", port := 443 }]
      limits := { headerTimeoutMs := 5000, connectTimeoutMs := 5000, maxConcurrentTunnels := 1 } }
  let tStopRef ← IO.mkRef (0 : Nat)
  try
    let res2 ← api2.withProxy cfg2 fun proxy2 => do
      sendConnectThenResetViaPython proxy2.port "teardown-detached.example.invalid" slow2Entered
      IO.sleep 80
      tStopRef.set (← monoMsNow)
      return .ok ()
    let stopMs := (← monoMsNow) - (← tStopRef.get)
    let (_, evs2) ← assertOk res2 "withProxy detached teardown"
    assertTrue (stopMs < 500)
      s!"Driver.withProxyM blocked waiting for detached DNS task: elapsed={stopMs}ms"
    assertTrue (evs2.any fun e => e.host == some "teardown-detached.example.invalid" &&
        e.outcome == .failed && e.reason == some "client disconnected")
      s!"expected client disconnected event before teardown, got {repr evs2}"
    let fdsWhileSlow ← countSelfOpenFds
    assertTrue (fdsWhileSlow ≤ fdsStart + 1)
      s!"teardownLoopM must close detached dnsR immediately: base={fdsStart} cur={fdsWhileSlow}"
    slow2Release.set true
    waitFlagTrue slow2Done 2000 "detached teardown slow worker completion"
  finally
    slow2Release.set true
  waitForFdCount fdsStart 1000 "detached DNS teardown FD cleanup"

/-- Verify 64-bit Linux `ppoll` relative timeout clamping via `Poll.msToPollTimespec` and `buildPollBatchSync`. -/
def testPollTimeoutClamp : IO Unit := do
  assertTrue (LinuxSyscall.Poll.msToPollTimespec 0 == { sec := 0, nsec := 0 })
    "Poll.msToPollTimespec 0"
  assertTrue (LinuxSyscall.Poll.msToPollTimespec 1250 == { sec := 1, nsec := 250000000 })
    "Poll.msToPollTimespec 1250"
  assertTrue (LinuxSyscall.Poll.msToPollTimespec (2147483648 * 1000 + 750) ==
      { sec := 2147483648, nsec := 750000000 })
    "Poll.msToPollTimespec above 2^31-1 seconds preserves full 64-bit sec and nsec"
  assertTrue (LinuxSyscall.Poll.msToPollTimespec (10000000000000000000 * 1000 + 500) ==
      { sec := 9223372036854775807, nsec := 500000000 })
    "Poll.msToPollTimespec above Int64 max clamps sec to Int64.max with valid nsec"
  let overInt32Slot : SysBridge.ClientSlot Nat Unit :=
    { phase := .handshake 7 ByteArray.empty (1000 + 2147483648 * 1000 + 750) }
  let (_, _, to32?) := SysBridge.buildPollBatchSync 3 4 4 1000 #[overInt32Slot]
  assertTrue (to32? == some { sec := 2147483648, nsec := 750000000 })
    s!"buildPollBatchSync >2^31-1s deadline expected 2147483648s/750000000ns, got {repr to32?}"
  let hugeSlot : SysBridge.ClientSlot Nat Unit :=
    { phase := .handshake 7 ByteArray.empty (1000 + 10000000000000000000 * 1000 + 500) }
  let (_, _, toMax?) := SysBridge.buildPollBatchSync 3 4 4 1000 #[hugeSlot]
  assertTrue (toMax? == some { sec := 9223372036854775807, nsec := 500000000 })
    s!"buildPollBatchSync huge deadline expected Int64.max/500000000ns, got {repr toMax?}"
  let efd ← match ← LinuxSyscall.Poll.eventfd2 1 { nonblock := true, cloexec := true } with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"eventfd2 failed: errno {e}")
  try
    let revs ← match ← LinuxSyscall.retryEintr
        (LinuxSyscall.Poll.ppoll #[(efd, { pollin := true })] toMax?) SysBridge.MAX_EINTR_RETRIES with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"ppoll with Int64.max timeout failed: errno {e}")
    let rev : LinuxSyscall.Poll.PollEvents := match revs[0]? with | some r => r | none => {}
    assertTrue rev.pollin
      s!"ppoll with Int64.max timeout expected POLLIN on ready eventfd, got {repr revs}"
  finally
    let _ ← LinuxSyscall.Files.close efd

/-- Verify `Driver.withProxyM` catches host exceptions in `createListener`, inside `runProxyLoopM`
    (closing tracked active client sockets and listener/wakeup FDs via `teardownTrackedM`), and
    inside the finalizer, converting every failure to `.error` (`.ioError`) with zero FD leaks. -/
def testExceptionSafetyAndTeardown : IO Unit := do
  let fdsStart ← countSelfOpenFds
  let baseSys ← mkCustomIoSys
  let throwListenerSys : Internal.SysBridge.CProxySysOpsM IO LinuxSyscall.RawFd :=
    { baseSys with
      net := { baseSys.net with
        socket := fun _ _ _ _ => throw (IO.userError "injected listener socket throw") } }
  let res1 ← (Internal.mkFullApiM throwListenerSys Core.ioConcOps).withProxy {} fun _ => pure (.ok ())
  assertErrKind res1 .ioError "createListener host throw converts to ioError"
  waitForFdCount fdsStart 1000 "createListener throw zero FD leak"

  let acceptedOnce ← IO.mkRef false
  let threwInLoop ← IO.mkRef false
  let throwLoopSys : Internal.SysBridge.CProxySysOpsM IO LinuxSyscall.RawFd :=
    { baseSys with
      net := { baseSys.net with
        accept4 := fun fd fl => do
          let r ← baseSys.net.accept4 fd fl
          if let .ok _ := r then acceptedOnce.set true
          return r }
      poll := { baseSys.poll with
        ppoll := fun fds to? => do
          if (← acceptedOnce.get) && !(← threwInLoop.get) then
            threwInLoop.set true
            throw (IO.userError "injected mid-loop ppoll throw")
          baseSys.poll.ppoll fds to? } }
  let res2 ← (Internal.mkFullApiM throwLoopSys Core.ioConcOps).withProxy {} fun proxy => do
    let cfd ← rtConnectLoopback proxy.port
    try
      waitFlagTrue threwInLoop 2000 "mid-loop throw fired with active client slot"
      let gotEof ← do
        let mut ok := false
        let mut waited : Nat := 0
        while !ok && waited < 2000 do
          match ← LinuxSyscall.Net.recvfrom cfd 16 { dontwait := true } with
          | .ok bs => if bs.size == 0 then ok := true
          | .error e => if e == LinuxSyscall.Errno.ECONNRESET then ok := true
          if !ok then
            IO.sleep 10
            waited := waited + 10
        pure ok
      assertTrue gotEof "teardownTrackedM closed active client socket on loop throw"
      return .ok ()
    finally
      let _ ← LinuxSyscall.Files.close cfd
  assertErrKind res2 .ioError "mid-loop host throw converts to ioError"
  waitForFdCount fdsStart 1000 "mid-loop throw teardown zero FD leak"

  let throwFinSys : Internal.SysBridge.CProxySysOpsM IO LinuxSyscall.RawFd :=
    { baseSys with
      net := { baseSys.net with
        sendto := fun _ _ _ => throw (IO.userError "injected finalizer sendto throw") } }
  let res3 ← (Internal.mkFullApiM throwFinSys Core.ioConcOps).withProxy {} fun _ => pure (.ok ())
  assertErrKind res3 .ioError "finalizer host throw converts to ioError"
  waitForFdCount fdsStart 1000 "finalizer throw zero FD leak"

end LeanSwe.ConnectProxy.RuntimeTests
