import Tests.Common
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Interface

namespace Tests.Mutate.NetRelay

open LeanSwe
open Tests.Common

private structure ScriptedCProxyState where
  rxQueue : List (Except LinuxSyscall.Errno ByteArray) := []
  txQueue : List (Except LinuxSyscall.Errno UInt32) := []
  accQueue : List (Except LinuxSyscall.Errno (Nat × LinuxSyscall.Net.SockAddr)) := []
  pollQueue : List (Except LinuxSyscall.Errno (Array LinuxSyscall.Poll.PollEvents)) := []
  soErrQueue : List (Except LinuxSyscall.Errno UInt32) := []
  connQueue : List (Except LinuxSyscall.Errno Unit) := []
  sentLog : ByteArray := ByteArray.empty
  closedFds : Array Nat := #[]
  dialed : Array LinuxSyscall.Net.SockAddr := #[]
  nextSock : Nat := 50

private def scriptedCProxySys : ConnectProxy.SysBridge.CProxySysOpsM (StateM ScriptedCProxyState) Nat :=
  let popRx : StateM ScriptedCProxyState (Except LinuxSyscall.Errno ByteArray) := do
    let s ← get
    match s.rxQueue with
    | hd :: tl => set { s with rxQueue := tl }; return hd
    | [] => return .error LinuxSyscall.Errno.EAGAIN
  let popTx (bs : ByteArray) : StateM ScriptedCProxyState (Except LinuxSyscall.Errno UInt32) := do
    let s ← get
    match s.txQueue with
    | hd :: tl =>
      let sent' := match hd with
        | .ok n => s.sentLog ++ bs.extract 0 (Nat.min n.toNat bs.size)
        | .error _ => s.sentLog
      set { s with txQueue := tl, sentLog := sent' }
      return hd
    | [] => return .error LinuxSyscall.Errno.EAGAIN
  { files :=
      { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        close := fun fd => do modify (fun s => { s with closedFds := s.closedFds.push fd }); return .ok ()
        read := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        write := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fstat := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        flock := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fcntl := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fsync := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        getcwd := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        dupStdio := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    net :=
      { socket := fun _ _ _ _ => do
          let s ← get
          set { s with nextSock := s.nextSock + 1 }
          return .ok s.nextSock
        socketpair := fun _ _ _ => pure (.ok (60, 61))
        bind := fun _ _ => pure (.ok ())
        listen := fun _ _ => pure (.ok ())
        accept4 := fun _ _ => do
          let s ← get
          match s.accQueue with
          | hd :: tl => set { s with accQueue := tl }; return hd
          | [] => return .error LinuxSyscall.Errno.EAGAIN
        connect := fun _ sa => do
          let s ← get
          set { s with dialed := s.dialed.push sa }
          match s.connQueue with
          | hd :: tl => modify (fun st => { st with connQueue := tl }); return hd
          | [] => return .error LinuxSyscall.Errno.EINPROGRESS
        getsockopt := fun _ _ => do
          let s ← get
          match s.soErrQueue with
          | hd :: tl => set { s with soErrQueue := tl }; return hd
          | [] => return .ok 0
        setsockopt := fun _ _ _ => pure (.ok ())
        getsockname := fun _ => pure (.ok (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 18080))
        recvfrom := fun _ _ _ => popRx
        sendto := fun _ bs _ => popTx bs
        shutdown := fun _ _ => pure (.ok ())
        sendmsg := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        recvmsg := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        ioctl := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    poll :=
      { ppoll := fun _ _ => do
          let s ← get
          match s.pollQueue with
          | hd :: tl => set { s with pollQueue := tl }; return hd
          | [] => return .ok #[]
        eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    dns :=
      { getaddrinfo := fun _ _ => pure (.ok []) }
    timeRand :=
      { clock_gettime := fun _ => pure (.ok { sec := 1, nsec := 0 })
        clock_nanosleep := fun _ _ _ => pure (.ok ())
        getrandom := fun _ _ => pure (.ok ByteArray.empty) } }

private def runNetRelayUnitTests : IO Unit := do
  let rb0 : LeanSwe.NetRelay.RingBuf := { cap := 3 }
  let rb1 := rb0.push (ByteArray.mk #[10, 20, 30, 40])
  checkUnit "netRelay push clamp and cap preserved"
    (rb1.cap == 3 && rb1.len == 3 && rb1.writeAvail == 0 && rb1.toList == [10, 20, 30] &&
      rb1.frontSlice.data.toList == [10, 20, 30])
  let rb2 := rb1.consume 2
  checkUnit "netRelay consume preserves cap and unread suffix"
    (rb2.cap == 3 && rb2.len == 1 && rb2.writeAvail == 2 && rb2.toList == [30])
  let rb3 := rb2.consume 5
  checkUnit "netRelay consume full drain resets buf and keeps cap"
    (rb3.cap == 3 && rb3.isEmpty && rb3.toList == [])
  let rxInit : ScriptedCProxyState :=
    { rxQueue := [.error LinuxSyscall.Errno.EINTR, .ok (ByteArray.mk #[1, 2]),
                  .ok (ByteArray.mk #[3, 4])] }
  let (rxRes, _) := (LeanSwe.NetRelay.recvIntoRing scriptedCProxySys.net 7 8 { cap := 3 }).run rxInit
  checkUnit "netRelay recvIntoRing custom cap EINTR"
    (match rxRes with
     | some (rb', eof) => !eof && rb'.cap == 3 && rb'.toList == [1, 2, 3]
     | none => false)
  let (fbRes, fbSt) := (LeanSwe.NetRelay.flushBytesNonblock scriptedCProxySys.net 7 ("WXYZ".toUTF8) 8 1).run
    { txQueue := [.error LinuxSyscall.Errno.EINTR, .ok 2, .error LinuxSyscall.Errno.EAGAIN] }
  checkUnit "netRelay flushBytesNonblock EINTR short write"
    (fbRes == some 3 && fbSt.sentLog == "XY".toUTF8)
  let (shOk, _) := (LeanSwe.NetRelay.shutdownWrClean scriptedCProxySys.net 7 4).run {}
  checkUnit "netRelay shutdownWrClean ok" shOk
  let (drOk, _) := (LeanSwe.NetRelay.drainDeadPeerRx scriptedCProxySys.net 7 4).run
    { rxQueue := [.error LinuxSyscall.Errno.EINTR, .ok ByteArray.empty] }
  checkUnit "netRelay drainDeadPeerRx EINTR + EOF" drOk

/-- Execute scripted `StateM` unit checks for `ConnectProxy.SysBridge` and `ConnectProxy.Relay`. -/
def runConnectProxyScriptedTests : IO Unit := do
  checkUnit "cproxy listenPollEvents cap"
    ((ConnectProxy.SysBridge.listenPollEvents 0 2).pollin == true &&
     (ConnectProxy.SysBridge.listenPollEvents 1 2).pollin == true &&
     (ConnectProxy.SysBridge.listenPollEvents 2 2).pollin == false &&
     (ConnectProxy.SysBridge.listenPollEvents 3 2).pollin == false)
  let rxInit : ScriptedCProxyState :=
    { rxQueue := [.ok (ByteArray.mk #[65]), .error LinuxSyscall.Errno.EINTR,
                  .ok (ByteArray.mk #[66, 67]), .error LinuxSyscall.Errno.ECONNRESET] }
  let (rxOut, _) := (LeanSwe.NetRelay.recvIntoRing scriptedCProxySys.net 7 8 {}).run rxInit
  match rxOut with
  | some (rb', eof) =>
    checkUnit "cproxy recvIntoRing EINTR + ECONNRESET preserves bytes"
      (eof == true && rb'.toList == [65, 66, 67])
  | none =>
    throw (IO.userError "recvIntoRing unexpectedly dropped bytes on EINTR/ECONNRESET")
  let txInit : ScriptedCProxyState :=
    { txQueue := [.error LinuxSyscall.Errno.EINTR, .ok 2, .error LinuxSyscall.Errno.EINTR, .ok 2] }
  let rb0 := ({} : LeanSwe.NetRelay.RingBuf).push ("ABCD".toUTF8)
  let (txOut, txSt) := (LeanSwe.NetRelay.flushRingNonblock scriptedCProxySys.net 7 8 rb0).run txInit
  checkUnit "cproxy flushRingNonblock EINTR + short writes"
    (txOut.map (·.isEmpty) == some true && txSt.sentLog == "ABCD".toUTF8)
  let pipeInit : ScriptedCProxyState :=
    { txQueue := [.error LinuxSyscall.Errno.EINTR, .ok 2, .ok 3] }
  let st0 := ConnectProxy.Relay.RelayState.init 10 11 ("HELLO".toUTF8)
  let (stPipe, stPipeW) :=
    (ConnectProxy.Relay.stepBidirectionalRelay scriptedCProxySys.net scriptedCProxySys.closeFd
      st0 {} { pollout := true }).run pipeInit
  checkUnit "cproxy relay pipelined prefix flush + 200 preserved"
    (stPipe.prefixFlushed == true && stPipeW.sentLog == "HELLO".toUTF8 &&
     stPipe.u2c.toList == ConnectProxy.Relay.reply200Bytes.data.toList)
  let accInit : ScriptedCProxyState :=
    { accQueue := [
        .error LinuxSyscall.Errno.EINTR,
        .ok (21, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40001),
        .error LinuxSyscall.Errno.EINTR,
        .ok (22, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40002),
        .ok (23, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40003)
      ] }
  let lim2 : ConnectProxy.ProxyLimits := { maxConcurrentTunnels := 2 }
  let (accSlots, _) :=
    (ConnectProxy.SysBridge.acceptNewClients (dnsJob := Unit) scriptedCProxySys lim2 3 100 #[]).run accInit
  checkUnit "cproxy acceptNewClients EINTR + maxConcurrentTunnels"
    (accSlots.size == 2)
  let hsCapInit : ScriptedCProxyState := { rxQueue := [.ok ("0123456789ABCDEF".toUTF8)] }
  let lim16 : ConnectProxy.ProxyLimits := { maxHeaderBytes := 16 }
  let hsSlot0 : ConnectProxy.SysBridge.ClientSlot Nat Unit := { phase := .handshake 40 ByteArray.empty 5000 }
  let ((hsSlot1, hsEvs1), _) :=
    (ConnectProxy.SysBridge.stepHandshakeReadAux scriptedCProxySys lim16
      (ConnectProxy.Model.decideConnectHead { limits := lim16 })
      (ConnectProxy.Model.decideResolvedIps {})
      (ConnectProxy.SysBridge.startDnsSync scriptedCProxySys lim16 (ConnectProxy.Model.decideResolvedIps {}))
      hsSlot0 #[] 40 5000 1 ByteArray.empty).run hsCapInit
  checkUnit "cproxy stepHandshakeReadAux fuel-1 maxHeaderBytes cap"
    (hsEvs1.size == 1 && !(match hsSlot1.phase with | .handshake .. => true | _ => false))
  let fbCands : Array ConnectProxy.IpAddr := #[.v4 0x7f000001, .v4 0x7f000002]
  let connInit : ScriptedCProxyState :=
    { soErrQueue := [.error LinuxSyscall.Errno.EINTR, .ok LinuxSyscall.Errno.ECONNREFUSED]
      connQueue := [.ok ()] }
  let connSlot0 : ConnectProxy.SysBridge.ClientSlot Nat Unit :=
    { phase := .connecting 30 31 "up.local" 8443 fbCands 1 none 5000
      pipelined := "TAIL".toUTF8
      target? := some ("up.local", 8443) }
  let ((connSlot1, connEvs1), connSt1) :=
    (ConnectProxy.SysBridge.stepConnecting scriptedCProxySys {} connSlot0 #[]
      30 31 "up.local" 8443 fbCands 1 none 5000 {} { pollout := true } 1000).run connInit
  let connRelayOk := match connSlot1.phase with
    | .relay rst => rst.pendingPrefix == "TAIL".toUTF8 && rst.u2c.toList == ConnectProxy.Relay.reply200Bytes.data.toList
    | _ => false
  checkUnit "cproxy stepConnecting SO_ERROR fallback dial + pipelined handoff"
    (connRelayOk && connEvs1.size == 1 && connSt1.closedFds == #[31] &&
     connSt1.dialed == #[.ipv4 0x7f000002 8443])
  let tickInit : ScriptedCProxyState :=
    { pollQueue := [.error LinuxSyscall.Errno.EINTR] }
  let (tickOut, _) :=
    (ConnectProxy.SysBridge.pollAndStepTickSync scriptedCProxySys {}
      (ConnectProxy.Model.decideConnectHead {})
      (ConnectProxy.Model.decideResolvedIps {})
      false 4 3 #[] #[]).run tickInit
  let isRetry := match tickOut with | .retryEintr => true | _ => false
  checkUnit "cproxy pollAndStepTickSync retries ppoll EINTR" isRetry

/-- Mutation test suite for `LeanSwe.NetRelay`. -/
def netRelaySuite : MutateSuite :=
  { name := "NetRelay", runBase := do runNetRelayUnitTests; return none }

end Tests.Mutate.NetRelay
