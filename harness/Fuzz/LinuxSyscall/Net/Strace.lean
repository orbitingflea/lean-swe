import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Net.Impl
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.LinuxSyscall.Net.Strace

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open Fuzz.LinuxSyscall

private def logNetErrHit {α : Type} (op : String) (mode : String) (r : Except Errno α) : IO (Except Errno α) := do
  if let .error e := r then
    Fuzz.Common.logErrHit s!"LeanSwe.LinuxSyscall.Net.{op}"
      (reprStr (NetErrorKind.ofErrno e)).trimAscii.toString mode
  return r

private def trackNetOps (mode : String) (ops : NetOps) : NetOps :=
  { socket := fun a b c d => do logNetErrHit "socket" mode (← ops.socket a b c d)
    socketpair := fun a b c => do logNetErrHit "socketpair" mode (← ops.socketpair a b c)
    bind := fun a b => do logNetErrHit "bind" mode (← ops.bind a b)
    listen := fun a b => do logNetErrHit "listen" mode (← ops.listen a b)
    accept4 := fun a b => do logNetErrHit "accept4" mode (← ops.accept4 a b)
    connect := fun a b => do logNetErrHit "connect" mode (← ops.connect a b)
    getsockopt := fun a b => do logNetErrHit "getsockopt" mode (← ops.getsockopt a b)
    setsockopt := fun a b c => do logNetErrHit "setsockopt" mode (← ops.setsockopt a b c)
    getsockname := fun a => do logNetErrHit "getsockname" mode (← ops.getsockname a)
    recvfrom := fun a b c => do logNetErrHit "recvfrom" mode (← ops.recvfrom a b c)
    sendto := fun a b c => do logNetErrHit "sendto" mode (← ops.sendto a b c)
    shutdown := fun a b => do logNetErrHit "shutdown" mode (← ops.shutdown a b)
    sendmsg := fun a b => do logNetErrHit "sendmsg" mode (← ops.sendmsg a b)
    recvmsg := fun a b => do logNetErrHit "recvmsg" mode (← ops.recvmsg a b)
    ioctl := fun a b c => do logNetErrHit "ioctl" mode (← ops.ioctl a b c) }

private def defaultOps : NetOps := trackNetOps "real" LeanSwe.LinuxSyscall.Net.defaultOps

@[extern "leanswe_net_close_fd"]
private opaque rawNetClose : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_net_open_nonsock"]
private opaque rawOpenNonsock : IO (Except Errno RawFd)

@[extern "leanswe_net_get_fd_flags"]
private opaque rawNetGetFdFlags : @& RawFd → IO (Except Errno UInt32)

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque rawRtArmSigalrm : UInt32 → UInt8 → BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque rawRtDisarmSigalrm : UInt32 → BaseIO Unit

@[extern "leanswe_net_reset_sigpipe_dfl"]
private opaque rawRtResetSigpipeDfl : BaseIO Unit

private def assertTrue (msg : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"assertion failed: {msg}")

private def assertEqErrno (msg : String) (actual expected : Errno) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{msg}: expected errno {expected}, got {actual}")

private def assertErr {α : Type} (msg : String) (r : Except Errno α) (expected : Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error {expected}, got ok")
  | .error e => assertEqErrno msg e expected

private def assertErrOneOf {α : Type} (msg : String) (r : Except Errno α) (allowed : List Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error in {allowed}, got ok")
  | .error e =>
    if !allowed.contains e then
      throw (IO.userError s!"{msg}: expected error in {allowed}, got {e}")

private def assertOk {α : Type} (msg : String) (r : Except Errno α) : IO α := do
  match r with
  | .ok v => return v
  | .error e => throw (IO.userError s!"{msg}: unexpected error {e}")

private def safeClose (fd : RawFd) : IO Unit := do
  let _ ← rawNetClose fd

private def safeCloseAll (fds : Array RawFd) : IO Unit := do
  for fd in fds do
    safeClose fd

private def withTempSockDir (tag : String) (k : ByteArray → IO Unit) : IO Unit := do
  let nanos ← IO.monoNanosNow
  let dir : System.FilePath := s!"/dev/shm/leanswe-net-rt-{tag}-{nanos}"
  IO.FS.createDirAll dir
  try
    k (dir.toString ++ "/s.sock").toUTF8
  finally
    if ← dir.pathExists then
      IO.FS.removeDirAll dir

private def closedSockFd : IO RawFd := do
  let fd ← assertOk "socket for close" (← defaultOps.socket .inet .dgram { cloexec := true } 0)
  assertOk "close socket" (← rawNetClose fd)
  return fd

private def mkMockNetOps (err : Errno) : NetOps :=
  trackNetOps "mocked" <| Internal.mkNetOps
    { socket := fun _ _ _ _ => pure (.error err)
      socketpair := fun _ _ _ => pure (.error err)
      bind := fun _ _ => pure (.error err)
      listen := fun _ _ => pure (.error err)
      accept4 := fun _ _ => pure (.error err)
      connect := fun _ _ => pure (.error err)
      getsockopt := fun _ _ => pure (.error err)
      setsockopt := fun _ _ _ => pure (.error err)
      getsockname := fun _ => pure (.error err)
      recvfrom := fun _ _ _ => pure (.error err)
      sendto := fun _ _ _ => pure (.error err)
      shutdown := fun _ _ => pure (.error err)
      sendmsg := fun _ _ => pure (.error err)
      recvmsg := fun _ _ => pure (.error err)
      ioctl := fun _ _ _ _ => pure (.error err) }

private def runMockNetError (label : String) (forced : Errno) (expectedKind : NetErrorKind)
    (act : RawFd → NetOps → IO (Except Errno Unit)) : IO Unit := do
  let dummyFd ← closedSockFd
  let res ← act dummyFd (mkMockNetOps forced)
  match res with
  | .ok _ => throw (IO.userError s!"mock {label}: expected {forced}, got ok")
  | .error e =>
    assertEqErrno s!"mock {label}" e forced
    if NetErrorKind.ofErrno e != expectedKind then
      throw (IO.userError s!"mock {label}: wrong NetErrorKind")

private def nbFlags : SockFlags := { nonblock := true, cloexec := true }

private def setupLoopbackListener (ops : NetOps) : IO (RawFd × UInt16) := do
  let lfd ← assertOk "listener socket" (← ops.socket .inet .stream nbFlags 0)
  let _ ← ops.setsockopt lfd .reuseAddr 1
  assertOk "listener bind" (← ops.bind lfd (.ipv4 INADDR_LOOPBACK 0))
  assertOk "listener listen" (← ops.listen lfd 16)
  match ← assertOk "listener getsockname" (← ops.getsockname lfd) with
  | .ipv4 _ p => return (lfd, p)
  | _ =>
    safeClose lfd
    throw (IO.userError "listener getsockname did not return ipv4")

private def drainConnect (ops : NetOps) (lfd cfd : RawFd) (addr : SockAddr) : IO RawFd := do
  match ← ops.connect cfd addr with
  | .ok () => pure ()
  | .error e =>
    if e != Errno.EINPROGRESS then
      throw (IO.userError s!"connect unexpected error {e}")
  let mut accepted? : Option RawFd := none
  for _ in [0 : 100] do
    match ← ops.accept4 lfd nbFlags with
    | .ok (sfd, _) =>
      accepted? := some sfd
      break
    | .error e =>
      if e != Errno.EAGAIN then
        throw (IO.userError s!"accept4 unexpected error {e}")
      IO.sleep 1
  match accepted? with
  | some sfd => return sfd
  | none => throw (IO.userError "timed out waiting for loopback accept4")

/-- Verify `socket(2)` domain/type/flags/protocol ABI (`AF_INET`, `AF_INET6`, `AF_UNIX`, and curated TCP/UDP rejection boundaries). -/
private def assume_net_socket_domainTypeFlagsAbi : IO Unit := do
  let ops := defaultOps
  assertErr "socket proto>=MAX" (← ops.socket .inet .stream {} IPPROTO_MAX) Errno.EINVAL
  assertErr "socket inet6 dgram proto>=MAX" (← ops.socket .inet6 .dgram {} 263) Errno.EINVAL
  assertErr "socket inet seqpacket" (← ops.socket .inet .seqpacket {} 0) Errno.ESOCKTNOSUPPORT
  assertErr "socket inet6 seqpacket" (← ops.socket .inet6 .seqpacket {} 0) Errno.ESOCKTNOSUPPORT
  assertErr "socket inet bad proto" (← ops.socket .inet .stream {} IPPROTO_UDP) Errno.EPROTONOSUPPORT
  assertErr "socket inet mptcp rejected" (← ops.socket .inet .stream nbFlags 262) Errno.EPROTONOSUPPORT
  assertErr "socket inet6 sctp rejected" (← ops.socket .inet6 .stream nbFlags 132) Errno.EPROTONOSUPPORT
  assertErr "socket inet icmp rejected" (← ops.socket .inet .dgram nbFlags 1) Errno.EPROTONOSUPPORT
  assertErr "socket inet6 icmpv6 rejected" (← ops.socket .inet6 .dgram nbFlags 58) Errno.EPROTONOSUPPORT
  assertErr "socket inet l2tp rejected" (← ops.socket .inet .dgram nbFlags 115) Errno.EPROTONOSUPPORT
  assertErr "socket inet dgram tcp rejected" (← ops.socket .inet .dgram nbFlags IPPROTO_TCP) Errno.EPROTONOSUPPORT
  assertErr "socket inet6 dgram tcp rejected" (← ops.socket .inet6 .dgram nbFlags IPPROTO_TCP) Errno.EPROTONOSUPPORT
  assertErr "socket unix stream proto=2 rejected" (← ops.socket .unix .stream {} 2) Errno.EPROTONOSUPPORT
  assertErr "socket unix dgram proto=2 rejected" (← ops.socket .unix .dgram {} 2) Errno.EPROTONOSUPPORT
  assertErr "socket unix seqpacket proto=2 rejected" (← ops.socket .unix .seqpacket {} 2) Errno.EPROTONOSUPPORT
  assertErr "socket unix dgram nonzero proto" (← ops.socket .unix .dgram {} IPPROTO_UDP) Errno.EPROTONOSUPPORT
  let s4 ← assertOk "socket inet4" (← ops.socket .inet .stream nbFlags 0)
  let s6 ← assertOk "socket inet6" (← ops.socket .inet6 .dgram { nonblock := false, cloexec := true } IPPROTO_UDP)
  let su ← assertOk "socket unix" (← ops.socket .unix .seqpacket { nonblock := true, cloexec := false } 0)
  let suPfS ← assertOk "socket unix stream PF_UNIX" (← ops.socket .unix .stream {} PF_UNIX)
  let suPfD ← assertOk "socket unix dgram PF_UNIX" (← ops.socket .unix .dgram nbFlags PF_UNIX)
  let suPfQ ← assertOk "socket unix seqpacket PF_UNIX" (← ops.socket .unix .seqpacket { nonblock := true, cloexec := false } PF_UNIX)
  let s0 ← assertOk "socket plain" (← ops.socket .inet .stream { nonblock := false, cloexec := false } 0)
  try
    assertTrue "s4 cloexec+nonblock" ((← assertOk "s4 flags" (← rawNetGetFdFlags s4)) == 3)
    assertTrue "s6 cloexec only" ((← assertOk "s6 flags" (← rawNetGetFdFlags s6)) == 1)
    assertTrue "su nonblock only" ((← assertOk "su flags" (← rawNetGetFdFlags su)) == 2)
    assertTrue "suPfS cloexec only" ((← assertOk "suPfS flags" (← rawNetGetFdFlags suPfS)) == 1)
    assertTrue "suPfD cloexec+nonblock" ((← assertOk "suPfD flags" (← rawNetGetFdFlags suPfD)) == 3)
    assertTrue "suPfQ nonblock only" ((← assertOk "suPfQ flags" (← rawNetGetFdFlags suPfQ)) == 2)
    assertTrue "s0 no flags" ((← assertOk "s0 flags" (← rawNetGetFdFlags s0)) == 0)
  finally
    safeClose s4
    safeClose s6
    safeClose su
    safeClose suPfS
    safeClose suPfD
    safeClose suPfQ
    safeClose s0

/-- Verify `socketpair(2)` `AF_UNIX` stream/dgram/seqpacket creation and non-Unix rejection. -/
private def assume_net_socketpair_unixPairAbi : IO Unit := do
  let ops := defaultOps
  assertErr "socketpair inet EOPNOTSUPP" (← ops.socketpair .inet .stream {}) Errno.EOPNOTSUPP
  assertErr "socketpair inet6 stream EOPNOTSUPP" (← ops.socketpair .inet6 .stream {}) Errno.EOPNOTSUPP
  assertErr "socketpair inet dgram EOPNOTSUPP" (← ops.socketpair .inet .dgram {}) Errno.EOPNOTSUPP
  assertErr "socketpair inet6 dgram EOPNOTSUPP" (← ops.socketpair .inet6 .dgram {}) Errno.EOPNOTSUPP
  assertErr "socketpair inet seqpacket ESOCKTNOSUPPORT" (← ops.socketpair .inet .seqpacket {}) Errno.ESOCKTNOSUPPORT
  assertErr "socketpair inet6 seqpacket ESOCKTNOSUPPORT" (← ops.socketpair .inet6 .seqpacket {}) Errno.ESOCKTNOSUPPORT
  let (a, b) ← assertOk "socketpair unix seqpacket" (← ops.socketpair .unix .seqpacket nbFlags)
  try
    assertTrue "sp a flags" ((← assertOk "sp a fl" (← rawNetGetFdFlags a)) == 3)
    assertTrue "sp b flags" ((← assertOk "sp b fl" (← rawNetGetFdFlags b)) == 3)
  finally
    safeClose a
    safeClose b

/-- Verify `bind(2)` sockaddr translation across IPv4/IPv6/Unix and NUL/length guards. -/
private def assume_net_bind_sockaddrTranslationAndNulGuard : IO Unit := withTempSockDir "a-bind" fun path => do
  let ops := defaultOps
  let s4 ← assertOk "socket4" (← ops.socket .inet .stream nbFlags 0)
  try
    assertErr "bind empty unix path" (← ops.bind s4 (.unix ByteArray.empty)) Errno.EINVAL
    assertErr "bind unix path NUL" (← ops.bind s4 (.unix (ByteArray.mk #[47, 0, 97]))) Errno.EINVAL
    assertErr "bind unix on inet4" (← ops.bind s4 (.unix path)) Errno.EAFNOSUPPORT
    assertOk "bind ipv4" (← ops.bind s4 (.ipv4 INADDR_LOOPBACK 0))
  finally
    safeClose s4
  let su ← assertOk "socket unix" (← ops.socket .unix .stream nbFlags 0)
  try
    assertOk "bind unix" (← ops.bind su (.unix path))
  finally
    safeClose su

/-- Verify `listen(2)` backlog handling on bound `AF_INET` and `AF_UNIX` listeners. -/
private def assume_net_listen_backlogAbi : IO Unit := do
  let ops := defaultOps
  let lfd ← assertOk "socket" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "bind" (← ops.bind lfd (.ipv4 INADDR_LOOPBACK 0))
    assertOk "listen 0" (← ops.listen lfd 0)
    assertOk "listen 128" (← ops.listen lfd 128)
  finally
    safeClose lfd

private def loIfname : ByteArray := "lo".toUTF8

private def isLoopbackUp (ops : NetOps) : IO Bool := do
  let fd ← assertOk "lo check socket" (← ops.socket .inet .dgram nbFlags 0)
  try
    let flags ← assertOk "lo check ioctl" (← ops.ioctl fd .getIfFlags loIfname)
    return (flags &&& IFF_UP) != 0
  finally
    safeClose fd

/-- Verify `accept4(2)` peer address decoding and `SOCK_NONBLOCK`/`SOCK_CLOEXEC` flags. -/
private def assume_net_accept4_flagsAndPeerAddrDecode : IO Unit := do
  let ops := defaultOps
  if ← isLoopbackUp ops then
    let (lfd, port) ← setupLoopbackListener ops
    let cfd ← assertOk "client socket" (← ops.socket .inet .stream nbFlags 0)
    try
      let sfd ← drainConnect ops lfd cfd (.ipv4 INADDR_LOOPBACK port)
      try
        assertTrue "accepted cloexec+nonblock" ((← assertOk "acc flags" (← rawNetGetFdFlags sfd)) == 3)
        assertErr "accepted nonblocking empty recv" (← ops.recvfrom sfd 8 {}) Errno.EAGAIN
      finally
        safeClose sfd
      let cfd2 ← assertOk "client socket 2" (← ops.socket .inet .stream nbFlags 0)
      try
        let _ ← ops.connect cfd2 (.ipv4 INADDR_LOOPBACK port)
        let mut accepted? : Option RawFd := none
        for _ in [:20] do
          match ← ops.accept4 lfd { nonblock := false, cloexec := true } with
          | .ok (sfd2, _) =>
            accepted? := some sfd2
            break
          | .error e =>
            if e == Errno.EAGAIN then IO.sleep 2
            else throw (IO.userError s!"accept4 blk+cloexec failed: {e}")
        match accepted? with
        | none => throw (IO.userError "accept4 blk+cloexec timed out")
        | some sfd2 =>
          try
            assertTrue "accepted cloexec only" ((← assertOk "acc blk flags" (← rawNetGetFdFlags sfd2)) == 1)
          finally
            safeClose sfd2
      finally
        safeClose cfd2
    finally
      safeClose cfd
      safeClose lfd
  else
    let (lfd, port) ← setupLoopbackListener ops
    let c4 ← assertOk "client4 socket" (← ops.socket .inet .stream nbFlags 0)
    try
      assertErr "lo down inet connect ENETUNREACH" (← ops.connect c4 (.ipv4 INADDR_LOOPBACK port)) Errno.ENETUNREACH
    finally
      safeClose c4
      safeClose lfd
    withTempSockDir "a-acc4-nodn" fun path => do
      let ul ← assertOk "unix lis" (← ops.socket .unix .stream nbFlags 0)
      let uc ← assertOk "unix cli" (← ops.socket .unix .stream nbFlags 0)
      try
        assertOk "unix bind" (← ops.bind ul (.unix path))
        assertOk "unix listen" (← ops.listen ul 4)
        assertOk "unix connect" (← ops.connect uc (.unix path))
        let (sfd, _) ← assertOk "unix accept4" (← ops.accept4 ul nbFlags)
        try
          assertTrue "accepted cloexec+nonblock" ((← assertOk "acc flags" (← rawNetGetFdFlags sfd)) == 3)
          assertErr "accepted nonblocking empty recv" (← ops.recvfrom sfd 8 {}) Errno.EAGAIN
        finally
          safeClose sfd
      finally
        safeClose uc
        safeClose ul

/-- Verify `connect(2)` non-blocking `EINPROGRESS`, `AF_INET6` `::ffff:127.0.0.1` dual-stack, and TCP self-connect. -/
private def assume_net_connect_nonblockAndSockaddrAbi : IO Unit := do
  let ops := defaultOps
  let l6 ← assertOk "socket6" (← ops.socket .inet6 .stream nbFlags 0)
  assertOk "setsockopt reuse" (← ops.setsockopt l6 .reuseAddr 1)
  assertOk "bind6" (← ops.bind l6 (.ipv6 0 0 0))
  assertOk "listen6" (← ops.listen l6 8)
  let port6 ← match ← assertOk "getsockname6" (← ops.getsockname l6) with
    | .ipv6 _ _ p _ _ => pure p
    | _ => safeClose l6; throw (IO.userError "expected ipv6 addr")
  let c6 ← assertOk "client6" (← ops.socket .inet6 .stream nbFlags 0)
  try
    if ← isLoopbackUp ops then
      let sfd ← drainConnect ops l6 c6 (.ipv6 0 0x0000ffff7f000001 port6)
      safeClose sfd
    else
      assertErr "lo down v4mapped connect ENETUNREACH"
        (← ops.connect c6 (.ipv6 0 0x0000ffff7f000001 port6)) Errno.ENETUNREACH
  finally
    safeClose c6
    safeClose l6

/-- Verify `getsockopt(2)` `SO_ERROR` clear-on-read and `SO_REUSEADDR` ABI. -/
private def assume_net_getsockopt_soErrorAndReuseAddrAbi : IO Unit := do
  let ops := defaultOps
  let (lfd, port) ← setupLoopbackListener ops
  let cfd ← assertOk "client" (← ops.socket .inet .stream nbFlags 0)
  try
    if ← isLoopbackUp ops then
      let sfd ← drainConnect ops lfd cfd (.ipv4 INADDR_LOOPBACK port)
      safeClose sfd
    else
      assertErr "lo down gso connect ENETUNREACH" (← ops.connect cfd (.ipv4 INADDR_LOOPBACK port)) Errno.ENETUNREACH
    let reuse ← assertOk "getsockopt reuseAddr" (← ops.getsockopt lfd .reuseAddr)
    assertTrue "reuseAddr == 1" (reuse == 1)
    let err0 ← assertOk "getsockopt error" (← ops.getsockopt cfd .error)
    assertTrue "SO_ERROR == 0" (err0 == 0)
  finally
    safeClose cfd
    safeClose lfd

/-- Verify `setsockopt(2)` `SO_REUSEADDR` enable/disable ABI. -/
private def assume_net_setsockopt_reuseAddrAbi : IO Unit := do
  let ops := defaultOps
  let fd ← assertOk "socket" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "setsockopt 1" (← ops.setsockopt fd .reuseAddr 1)
    assertTrue "getsockopt == 1" ((← assertOk "get 1" (← ops.getsockopt fd .reuseAddr)) == 1)
    assertOk "setsockopt 0" (← ops.setsockopt fd .reuseAddr 0)
    assertTrue "getsockopt == 0" ((← assertOk "get 0" (← ops.getsockopt fd .reuseAddr)) == 0)
    assertOk "setsockopt 0x100" (← ops.setsockopt fd .reuseAddr 0x100)
    assertTrue "getsockopt 0x100 == 1" ((← assertOk "get 0x100" (← ops.getsockopt fd .reuseAddr)) == 1)
    assertOk "setsockopt 0x80000000" (← ops.setsockopt fd .reuseAddr 0x80000000)
    assertTrue "getsockopt 0x80000000 == 1" ((← assertOk "get 0x80000000" (← ops.getsockopt fd .reuseAddr)) == 1)
  finally
    safeClose fd

/-- Verify `getsockname(2)` local address decoding across IPv4, IPv6, and Unix endpoints. -/
private def assume_net_getsockname_sockaddrDecode : IO Unit := withTempSockDir "a-gsn" fun path => do
  let ops := defaultOps
  let s4 ← assertOk "socket4" (← ops.socket .inet .dgram nbFlags 0)
  let s6 ← assertOk "socket6" (← ops.socket .inet6 .dgram nbFlags 0)
  let su ← assertOk "socketu" (← ops.socket .unix .dgram nbFlags 0)
  try
    assertOk "bind4" (← ops.bind s4 (.ipv4 INADDR_LOOPBACK 0))
    let loUp ← isLoopbackUp ops
    if loUp then
      assertOk "bind6" (← ops.bind s6 (.ipv6 0 1 0))
    else
      assertErr "bind6 lo down EADDRNOTAVAIL" (← ops.bind s6 (.ipv6 0 1 0)) Errno.EADDRNOTAVAIL
      assertOk "bind6 any" (← ops.bind s6 (.ipv6 0 0 0))
    assertOk "bindu" (← ops.bind su (.unix path))
    match ← assertOk "gsn4" (← ops.getsockname s4) with
    | .ipv4 a p => assertTrue "ipv4 loopback nonzero port" (a == INADDR_LOOPBACK && p != 0)
    | _ => throw (IO.userError "gsn4 expected ipv4")
    match ← assertOk "gsn6" (← ops.getsockname s6) with
    | .ipv6 hi lo p _ _ =>
      if loUp then
        assertTrue "ipv6 ::1 nonzero port" (hi == 0 && lo == 1 && p != 0)
      else
        assertTrue "ipv6 :: nonzero port" (hi == 0 && lo == 0 && p != 0)
    | _ => throw (IO.userError "gsn6 expected ipv6")
    match ← assertOk "gsnu" (← ops.getsockname su) with
    | .unix gotPath => assertTrue "unix path matches" (gotPath.data == path.data)
    | _ => throw (IO.userError "gsnu expected unix")
    let sm6 ← assertOk "socket6 scope" (← ops.socket .inet6 .dgram nbFlags 0)
    try
      assertOk "bind6 mcast scope=1" (← ops.bind sm6 (.ipv6 0xff02000000000000 1 0 0 1))
      match ← assertOk "gsn6 scope" (← ops.getsockname sm6) with
      | .ipv6 hi lo p _ sc =>
        assertTrue "ipv6 scopeId preserved" (hi == 0xff02000000000000 && lo == 1 && p != 0 && sc == 1)
      | _ => throw (IO.userError "gsn6 scope expected ipv6")
    finally
      safeClose sm6
  finally
    safeClose s4
    safeClose s6
    safeClose su

/-- Verify `recvfrom(2)` `MAX_READ_BYTES` clamping, `MSG_PEEK`, and partial reads. -/
private def assume_net_recvfrom_clamped16MiBAndMsgFlags : IO Unit := do
  let ops := defaultOps
  let (a, b) ← assertOk "socketpair" (← ops.socketpair .unix .stream nbFlags)
  try
    let sent ← assertOk "sendto" (← ops.sendto a (asciiBytes ['h', 'e', 'l', 'l', 'o']) { nosignal := true })
    assertTrue "sent 5" (sent == 5)
    let peeked ← assertOk "recvfrom peek" (← ops.recvfrom b 2 { peek := true })
    assertTrue "peek he" (peeked.data == (asciiBytes ['h', 'e']).data)
    let clamped ← assertOk "recvfrom > 16MiB" (← ops.recvfrom b 0x7fffffff { dontwait := true })
    assertTrue "clamped got hello" (clamped.data == (asciiBytes ['h', 'e', 'l', 'l', 'o']).data)
    let stTxt ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
    if (stTxt.splitOn "TracerPid:\t0").length > 1 then
      let exe ← IO.appPath
      let tr ← IO.Process.output {
        cmd := "strace"
        args := #["-f", "-qq", "-e", "trace=recvfrom", exe.toString, "--net-strace-worker", "__recvfrom_cap__", "0"]
      }
      if tr.exitCode != 0 then
        throw (IO.userError s!"recvfrom 16MiB strace probe failed (exit={tr.exitCode}): {tr.stderr}")
      assertTrue "recvfrom clamped 0xffffffff and 0x7fffffff to 16777216"
        ((tr.stderr.splitOn ", 16777216,").length >= 4 && (tr.stderr.splitOn ", 16777215,").length >= 2)
  finally
    safeClose a
    safeClose b

/-- Verify `sendto(2)` `MSG_NOSIGNAL` / `MSG_DONTWAIT` flag encoding and partial send counts. -/
private def assume_net_sendto_msgFlagsAndPartialCount : IO Unit := do
  let ops := defaultOps
  let (a, b) ← assertOk "socketpair" (← ops.socketpair .unix .stream nbFlags)
  try
    safeClose b
    assertErr "sendto broken pipe EPIPE" (← ops.sendto a (asciiBytes ['x']) { nosignal := true }) Errno.EPIPE
  finally
    safeClose a

/-- Verify `shutdown(2)` `SHUT_RD` / `SHUT_WR` / `SHUT_RDWR` ABI tags and half-close semantics. -/
private def assume_net_shutdown_shutHowAbi : IO Unit := do
  let ops := defaultOps
  let (a, b) ← assertOk "socketpair" (← ops.socketpair .unix .stream nbFlags)
  try
    assertOk "shutdown wr" (← ops.shutdown a .wr)
    assertErr "sendto after SHUT_WR" (← ops.sendto a (asciiBytes ['z']) { nosignal := true }) Errno.EPIPE
    let eof ← assertOk "peer recv EOF" (← ops.recvfrom b 8 {})
    assertTrue "eof empty" (eof.size == 0)
    assertOk "shutdown rdwr" (← ops.shutdown b .rdwr)
    let rd0 ← assertOk "local SHUT_RD EOF" (← ops.recvfrom b 8 {})
    assertTrue "rd0 empty" (rd0.size == 0)
  finally
    safeClose a
    safeClose b

/-- Verify `sendmsg(2)` `SCM_RIGHTS` batch encoding and bounds (`1..32`). -/
private def assume_net_sendmsg_scmRightsBatchAbi : IO Unit := do
  let ops := defaultOps
  let (a, b) ← assertOk "socketpair" (← ops.socketpair .unix .seqpacket nbFlags)
  let dummy ← assertOk "dummy sock" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertErr "sendmsg empty" (← ops.sendmsg a #[]) Errno.EINVAL
    assertOk "sendmsg 1 fd" (← ops.sendmsg a #[dummy])
    let recvd ← assertOk "recvmsg 1 fd" (← ops.recvmsg b 4)
    safeCloseAll recvd
    assertTrue "received 1 fd" (recvd.size == 1)
    assertOk "sendmsg 32 fds" (← ops.sendmsg a (Array.replicate 32 dummy))
    let recvd32 ← assertOk "recvmsg 32 fds" (← ops.recvmsg b 32)
    try
      assertTrue "received 32 fds" (recvd32.size == 32)
      for rfd in recvd32 do
        let fl ← assertOk "recvmsg 32 cloexec" (← rawNetGetFdFlags rfd)
        assertTrue "recvmsg 32 fd has FD_CLOEXEC" ((fl &&& 1) != 0)
    finally
      safeCloseAll recvd32
  finally
    safeClose dummy
    safeClose a
    safeClose b

/-- Verify `recvmsg(2)` `CMSG_LEN(maxFds * sizeof(int))` cap and excess-FD closing on 64-bit Linux. -/
private def assume_net_recvmsg_scmRightsCloexecAndCapAbi : IO Unit := do
  let ops := defaultOps
  let (a, b) ← assertOk "socketpair" (← ops.socketpair .unix .seqpacket nbFlags)
  let f1 ← assertOk "f1" (← ops.socket .inet .dgram nbFlags 0)
  let f2 ← assertOk "f2" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "bind f1" (← ops.bind f1 (.ipv4 INADDR_LOOPBACK 0))
    let f1Port ← match ← assertOk "gsn f1" (← ops.getsockname f1) with
      | .ipv4 _ p => pure p
      | _ => throw (IO.userError "gsn f1 expected ipv4")
    assertTrue "f1Port != 0" (f1Port != 0)
    assertOk "sendmsg 2 fds" (← ops.sendmsg a #[f1, f2])
    assertErr "recvmsg odd cap 1 EPROTO" (← ops.recvmsg b 1) Errno.EPROTO
    assertOk "sendmsg 2 fds retry" (← ops.sendmsg a #[f1, f2])
    let got2 ← assertOk "recvmsg cap 2" (← ops.recvmsg b 2)
    try
      assertTrue "cap 2 keeps 2 fds" (got2.size == 2)
      for rfd in got2 do
        let fl ← assertOk "recvmsg cloexec flag" (← rawNetGetFdFlags rfd)
        assertTrue "recvmsg fd has FD_CLOEXEC" ((fl &&& 1) != 0)
      match got2[0]?, got2[1]? with
      | some g0, some g1 =>
        match ← assertOk "gsn got2[0]" (← ops.getsockname g0),
              ← assertOk "gsn got2[1]" (← ops.getsockname g1) with
        | .ipv4 _ pA, .ipv4 _ pB =>
          assertTrue "recvmsg preserves distinct SCM_RIGHTS fds" (pA == f1Port && pB == 0)
        | _, _ => throw (IO.userError "got2 getsockname expected ipv4")
      | _, _ => throw (IO.userError "expected 2 elements in got2")
    finally
      safeCloseAll got2

    let _ ← assertOk "sendto plain" (← ops.sendto a (asciiBytes ['Q']) { nosignal := true })
    let plain ← assertOk "recvmsg plain" (← ops.recvmsg b 4)
    safeCloseAll plain
    assertTrue "plain message gives 0 fds" (plain.size == 0)
  finally
    safeClose f1
    safeClose f2
    safeClose a
    safeClose b

/-- Verify `ioctl(2)` `SIOCGIFFLAGS`/`SIOCSIFFLAGS` and `IFNAMSIZ` / NUL validation. -/
private def assume_net_ioctl_ifreqFlagsAndIfnameBounds : IO Unit := do
  let ops := defaultOps
  let fd ← assertOk "dgram sock" (← ops.socket .inet .dgram nbFlags 0)
  try
    let fl ← assertOk "ioctl lo" (← ops.ioctl fd .getIfFlags loIfname)
    assertTrue "lo has IFF_LOOPBACK" ((fl &&& IFF_LOOPBACK) != 0)
    assertErr "ioctl missing ifname" (← ops.ioctl fd .getIfFlags (asciiBytes ['n', 'o', 'p', 'e', '0'])) Errno.ENODEV
    assertErr "ioctl NUL ifname" (← ops.ioctl fd .getIfFlags (ByteArray.mk #[108, 0])) Errno.EINVAL
    let nonsock ← assertOk "open nonsock" (← rawOpenNonsock)
    try
      assertErr "ioctl nonsock ENOTTY" (← ops.ioctl nonsock .getIfFlags loIfname) Errno.ENOTTY
    finally
      safeClose nonsock
    let nsProbe ← IO.Process.output { cmd := "unshare", args := #["-Urn", "--", "true"] }
    if nsProbe.exitCode == 0 then
      let exe ← IO.appPath
      let sub ← IO.Process.output {
        cmd := "unshare"
        args := #["-Urn", "--", exe.toString, "--net-strace-worker", "__ioctl_signext__", "0"]
      }
      if sub.exitCode != 0 then
        throw (IO.userError s!"ioctl 0x8049 sign-ext check failed (exit={sub.exitCode}): {sub.stderr}")
  finally
    safeClose fd

/-- Real `socket` `.invalidArg` test (`EINVAL` and `ESOCKTNOSUPPORT`). -/
private def err_socket_invalidArg : IO Unit := do
  assertErr "socket high proto" (← defaultOps.socket .inet .stream {} IPPROTO_MAX) Errno.EINVAL
  assertErr "socket bad proto" (← defaultOps.socket .inet .stream {} IPPROTO_UDP) Errno.EPROTONOSUPPORT

/-- Mocked `socket` non-transient error paths. -/
private def err_socket_mocked : IO Unit := do
  runMockNetError "socket badFd" Errno.EBADF .badFd (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "socket addr" Errno.EADDRNOTAVAIL .addressError (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "socket wb" Errno.EAGAIN .wouldBlockOrInProgress (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "socket cs" Errno.ENETDOWN .connectionState (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "socket perm" Errno.EACCES .permissionDenied (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `socket` `.transientOrResource` test (`ENOBUFS`). -/
private def err_socket_transient : IO Unit :=
  runMockNetError "socket transient" Errno.ENOBUFS .transientOrResource (fun _ ops => ops.socket .inet .stream {} 0 >>= fun r => pure (r.map fun _ => ()))

/-- Real `socketpair` `.invalidArg` test (`EOPNOTSUPP`). -/
private def err_socketpair_invalidArg : IO Unit := do
  assertErr "socketpair inet" (← defaultOps.socketpair .inet .stream {}) Errno.EOPNOTSUPP

/-- Mocked `socketpair` non-transient error paths. -/
private def err_socketpair_mocked : IO Unit := do
  runMockNetError "sp badFd" Errno.EBADF .badFd (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "sp addr" Errno.ENOENT .addressError (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "sp wb" Errno.EAGAIN .wouldBlockOrInProgress (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "sp cs" Errno.ECONNABORTED .connectionState (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "sp perm" Errno.EPERM .permissionDenied (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `socketpair` `.transientOrResource` test (`EMFILE`). -/
private def err_socketpair_transient : IO Unit :=
  runMockNetError "sp transient" Errno.EMFILE .transientOrResource (fun _ ops => ops.socketpair .unix .stream {} >>= fun r => pure (r.map fun _ => ()))

/-- Real `bind` `.badFd` test (`EBADF` and `ENOTSOCK`). -/
private def err_bind_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "bind closed" (← defaultOps.bind cfd (.ipv4 INADDR_LOOPBACK 0)) Errno.EBADF
  let ns ← assertOk "open nonsock" (← rawOpenNonsock)
  try
    assertErr "bind nonsock" (← defaultOps.bind ns (.ipv4 INADDR_LOOPBACK 0)) Errno.ENOTSOCK
  finally
    safeClose ns

/-- Real `bind` `.invalidArg` test (`EINVAL` on link-local scope 0 and `EAFNOSUPPORT`). -/
private def err_bind_invalidArg : IO Unit := do
  let s6 ← assertOk "socket6" (← defaultOps.socket .inet6 .dgram nbFlags 0)
  try
    assertErr "bind fe80 scope 0" (← defaultOps.bind s6 (.ipv6 0xfe80000000000000 1 8080 0 0)) Errno.EINVAL
    assertErr "bind unix on inet6" (← defaultOps.bind s6 (.unix (ByteArray.mk (Array.replicate 30 97)))) Errno.EAFNOSUPPORT
  finally
    safeClose s6

/-- Real `bind` `.addressError` test (`EADDRINUSE` and `ENOENT`). -/
private def err_bind_addressError : IO Unit := do
  let (lfd, port) ← setupLoopbackListener defaultOps
  let s2 ← assertOk "socket2" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "bind addr in use" (← defaultOps.bind s2 (.ipv4 INADDR_LOOPBACK port)) Errno.EADDRINUSE
  finally
    safeClose s2
    safeClose lfd

/-- Real `bind` `.permissionDenied` test (`EACCES` on unprivileged low-port bind; mocked fallback when `CAP_NET_BIND_SERVICE` is held). -/
private def err_bind_permissionDenied : IO Unit := do
  let fd ← assertOk "socket4" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    match ← defaultOps.bind fd (.ipv4 INADDR_LOOPBACK 81) with
    | .error e =>
      if ![Errno.EACCES, Errno.EPERM, Errno.EADDRINUSE].contains e then
        throw (IO.userError s!"bind privileged port 81: unexpected error {e}")
    | .ok _ =>
      runMockNetError "bind eacces cap fallback" Errno.EACCES .permissionDenied
        (fun mfd ops => ops.bind mfd (.ipv4 INADDR_LOOPBACK 81))
  finally
    safeClose fd

/-- Mocked `bind` non-transient error paths. -/
private def err_bind_mocked : IO Unit := do
  runMockNetError "bind wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.bind fd (.ipv4 INADDR_LOOPBACK 0))
  runMockNetError "bind cs" Errno.EISCONN .connectionState (fun fd ops => ops.bind fd (.ipv4 INADDR_LOOPBACK 0))

/-- Mocked `bind` `.transientOrResource` test (`ENOMEM`). -/
private def err_bind_transient : IO Unit :=
  runMockNetError "bind transient" Errno.ENOMEM .transientOrResource (fun fd ops => ops.bind fd (.ipv4 INADDR_LOOPBACK 0))

/-- Real `listen` `.badFd` test (`EBADF`). -/
private def err_listen_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "listen closed" (← defaultOps.listen cfd 8) Errno.EBADF

/-- Real `listen` `.invalidArg` test (`EOPNOTSUPP` on dgram and `EINVAL` on unbound unix). -/
private def err_listen_invalidArg : IO Unit := do
  let dg ← assertOk "dgram" (← defaultOps.socket .inet .dgram nbFlags 0)
  let us ← assertOk "unix stream" (← defaultOps.socket .unix .stream nbFlags 0)
  try
    assertErr "listen dgram" (← defaultOps.listen dg 4) Errno.EOPNOTSUPP
    assertErr "listen unbound unix" (← defaultOps.listen us 4) Errno.EINVAL
  finally
    safeClose dg
    safeClose us

/-- Real `listen` `.addressError` test (`EADDRINUSE` across `SO_REUSEADDR` listeners). -/
private def err_listen_addressError : IO Unit := do
  let l1 ← assertOk "socket l1" (← defaultOps.socket .inet .stream nbFlags 0)
  let l2 ← assertOk "socket l2" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertOk "reuse l1" (← defaultOps.setsockopt l1 .reuseAddr 1)
    assertOk "bind l1" (← defaultOps.bind l1 (.ipv4 INADDR_LOOPBACK 0))
    let port ← match ← assertOk "gsn l1" (← defaultOps.getsockname l1) with
      | .ipv4 _ p => pure p
      | _ => throw (IO.userError "listen test l1 non-ipv4")
    assertOk "reuse l2" (← defaultOps.setsockopt l2 .reuseAddr 1)
    assertOk "bind l2" (← defaultOps.bind l2 (.ipv4 INADDR_LOOPBACK port))
    assertOk "listen l1" (← defaultOps.listen l1 8)
    assertErr "listen l2 EADDRINUSE" (← defaultOps.listen l2 8) Errno.EADDRINUSE
  finally
    safeClose l2
    safeClose l1

/-- Mocked `listen` non-transient error paths. -/
private def err_listen_mocked : IO Unit := do
  runMockNetError "listen wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.listen fd 8)
  runMockNetError "listen cs" Errno.EISCONN .connectionState (fun fd ops => ops.listen fd 8)
  runMockNetError "listen perm" Errno.EPERM .permissionDenied (fun fd ops => ops.listen fd 8)

/-- Mocked `listen` `.transientOrResource` test (`ENOBUFS`). -/
private def err_listen_transient : IO Unit :=
  runMockNetError "listen transient" Errno.ENOBUFS .transientOrResource (fun fd ops => ops.listen fd 8)

/-- Real `accept4` `.badFd` test (`EBADF`). -/
private def err_accept4_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "accept4 closed" (← defaultOps.accept4 cfd nbFlags) Errno.EBADF

/-- Real `accept4` `.invalidArg` test (`EINVAL` on non-listening socket). -/
private def err_accept4_invalidArg : IO Unit := do
  let s ← assertOk "socket" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "accept4 non-listening" (← defaultOps.accept4 s nbFlags) Errno.EINVAL
  finally
    safeClose s

/-- Real `accept4` `.wouldBlockOrInProgress` test (`EAGAIN` on empty non-blocking listener). -/
private def err_accept4_wouldBlock : IO Unit := do
  let (lfd, _) ← setupLoopbackListener defaultOps
  try
    assertErr "accept4 EAGAIN" (← defaultOps.accept4 lfd nbFlags) Errno.EAGAIN
  finally
    safeClose lfd

/-- Mocked `accept4` non-transient error paths. -/
private def err_accept4_mocked : IO Unit := do
  runMockNetError "accept4 addr" Errno.EADDRNOTAVAIL .addressError (fun fd ops => ops.accept4 fd nbFlags >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "accept4 cs" Errno.ECONNABORTED .connectionState (fun fd ops => ops.accept4 fd nbFlags >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "accept4 perm" Errno.EPERM .permissionDenied (fun fd ops => ops.accept4 fd nbFlags >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `accept4` `.transientOrResource` test (`EMFILE`). -/
private def err_accept4_transient : IO Unit :=
  runMockNetError "accept4 transient" Errno.EMFILE .transientOrResource (fun fd ops => ops.accept4 fd nbFlags >>= fun r => pure (r.map fun _ => ()))

/-- Real `connect` `.badFd` test (`EBADF`). -/
private def err_connect_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "connect closed" (← defaultOps.connect cfd (.ipv4 INADDR_LOOPBACK 1)) Errno.EBADF

/-- Real `connect` `.invalidArg` test (`EINVAL` on bad Unix path and `EAFNOSUPPORT`). -/
private def err_connect_invalidArg : IO Unit := do
  let s ← assertOk "socket" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "connect unix empty" (← defaultOps.connect s (.unix ByteArray.empty)) Errno.EINVAL
    assertErr "connect unix NUL" (← defaultOps.connect s (.unix (ByteArray.mk #[47, 0, 97]))) Errno.EINVAL
    assertErr "connect ipv6 on ipv4" (← defaultOps.connect s (.ipv6 0 1 80)) Errno.EAFNOSUPPORT
  finally
    safeClose s

/-- Real `connect` `.addressError` test (`ENOENT` on missing `AF_UNIX` path). -/
private def err_connect_addressError : IO Unit := withTempSockDir "econn-enoent" fun miss => do
  let u ← assertOk "unix socket" (← defaultOps.socket .unix .stream nbFlags 0)
  try
    assertErr "connect missing unix" (← defaultOps.connect u (.unix miss)) Errno.ENOENT
  finally
    safeClose u

/-- Real `connect` `.wouldBlockOrInProgress` test (`EINPROGRESS` on non-blocking loopback, or `ENETUNREACH` if `lo` is down). -/
private def err_connect_inProgress : IO Unit := do
  let (lfd, port) ← setupLoopbackListener defaultOps
  let cfd ← assertOk "client" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    if ← isLoopbackUp defaultOps then
      match ← defaultOps.connect cfd (.ipv4 INADDR_LOOPBACK port) with
      | .error e => assertEqErrno "connect EINPROGRESS" e Errno.EINPROGRESS
      | .ok _ => pure ()
    else
      assertErr "lo down connect ENETUNREACH" (← defaultOps.connect cfd (.ipv4 INADDR_LOOPBACK port)) Errno.ENETUNREACH
  finally
    safeClose cfd
    safeClose lfd

/-- Real `connect` `.connectionState` test (`EISCONN` and `ECONNREFUSED`). -/
private def err_connect_connectionState : IO Unit := withTempSockDir "econn-cs" fun path => do
  let srv ← assertOk "srv" (← defaultOps.socket .unix .stream nbFlags 0)
  let cli ← assertOk "cli" (← defaultOps.socket .unix .stream nbFlags 0)
  try
    assertOk "bind srv" (← defaultOps.bind srv (.unix path))
    assertErr "connect unbound listening -> ECONNREFUSED" (← defaultOps.connect cli (.unix path)) Errno.ECONNREFUSED
    assertOk "listen srv" (← defaultOps.listen srv 4)
    let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
    try
      assertErr "connect already connected -> EISCONN" (← defaultOps.connect a (.unix path)) Errno.EISCONN
    finally
      safeClose a
      safeClose b
  finally
    safeClose cli
    safeClose srv

/-- Mocked `connect` `.permissionDenied` test (`EACCES`). -/
private def err_connect_mocked : IO Unit :=
  runMockNetError "connect perm" Errno.EACCES .permissionDenied (fun fd ops => ops.connect fd (.ipv4 INADDR_LOOPBACK 1))

/-- Mocked `connect` `.transientOrResource` test (`EINTR`). -/
private def err_connect_transient : IO Unit :=
  runMockNetError "connect transient" Errno.EINTR .transientOrResource (fun fd ops => ops.connect fd (.ipv4 INADDR_LOOPBACK 1))

/-- Real `getsockopt` `.badFd` test (`EBADF`). -/
private def err_getsockopt_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "getsockopt closed" (← defaultOps.getsockopt cfd .error) Errno.EBADF

/-- Mocked `getsockopt` non-transient error paths. -/
private def err_getsockopt_mocked : IO Unit := do
  runMockNetError "gso inv" Errno.ENOPROTOOPT .invalidArg (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gso addr" Errno.ENOENT .addressError (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gso wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gso cs" Errno.ENOTCONN .connectionState (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gso perm" Errno.EPERM .permissionDenied (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `getsockopt` `.transientOrResource` test (`ENOMEM`). -/
private def err_getsockopt_transient : IO Unit :=
  runMockNetError "gso transient" Errno.ENOMEM .transientOrResource (fun fd ops => ops.getsockopt fd .error >>= fun r => pure (r.map fun _ => ()))

/-- Real `setsockopt` `.badFd` test (`EBADF`). -/
private def err_setsockopt_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "setsockopt closed" (← defaultOps.setsockopt cfd .reuseAddr 1) Errno.EBADF

/-- Mocked `setsockopt` non-transient error paths. -/
private def err_setsockopt_mocked : IO Unit := do
  runMockNetError "sso inv" Errno.EINVAL .invalidArg (fun fd ops => ops.setsockopt fd .reuseAddr 1)
  runMockNetError "sso addr" Errno.ENOENT .addressError (fun fd ops => ops.setsockopt fd .reuseAddr 1)
  runMockNetError "sso wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.setsockopt fd .reuseAddr 1)
  runMockNetError "sso cs" Errno.ENOTCONN .connectionState (fun fd ops => ops.setsockopt fd .reuseAddr 1)
  runMockNetError "sso perm" Errno.EPERM .permissionDenied (fun fd ops => ops.setsockopt fd .reuseAddr 1)

/-- Mocked `setsockopt` `.transientOrResource` test (`ENOMEM`). -/
private def err_setsockopt_transient : IO Unit :=
  runMockNetError "sso transient" Errno.ENOMEM .transientOrResource (fun fd ops => ops.setsockopt fd .reuseAddr 1)

/-- Real `getsockname` `.badFd` test (`EBADF` and `ENOTSOCK`). -/
private def err_getsockname_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "gsn closed" (← defaultOps.getsockname cfd) Errno.EBADF
  let ns ← assertOk "nonsock" (← rawOpenNonsock)
  try
    assertErr "gsn nonsock" (← defaultOps.getsockname ns) Errno.ENOTSOCK
  finally
    safeClose ns

/-- Mocked `getsockname` non-transient error paths. -/
private def err_getsockname_mocked : IO Unit := do
  runMockNetError "gsn inv" Errno.EINVAL .invalidArg (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gsn addr" Errno.ENOENT .addressError (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gsn wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gsn cs" Errno.ENOTCONN .connectionState (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "gsn perm" Errno.EPERM .permissionDenied (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `getsockname` `.transientOrResource` test (`ENOBUFS`). -/
private def err_getsockname_transient : IO Unit :=
  runMockNetError "gsn transient" Errno.ENOBUFS .transientOrResource (fun fd ops => ops.getsockname fd >>= fun r => pure (r.map fun _ => ()))

/-- Real `recvfrom` `.badFd` test (`EBADF`). -/
private def err_recvfrom_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "recvfrom closed" (← defaultOps.recvfrom cfd 8 {}) Errno.EBADF

/-- Real `recvfrom` `.invalidArg` test (`EINVAL` on unconnected `AF_UNIX` stream). -/
private def err_recvfrom_invalidArg : IO Unit := do
  let u ← assertOk "unix stream" (← defaultOps.socket .unix .stream nbFlags 0)
  try
    assertErr "recvfrom unconnected unix stream" (← defaultOps.recvfrom u 8 {}) Errno.EINVAL
  finally
    safeClose u

/-- Real `recvfrom` `.wouldBlockOrInProgress` test (`EAGAIN` on empty non-blocking pair). -/
private def err_recvfrom_wouldBlock : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
  try
    assertErr "recvfrom empty EAGAIN" (← defaultOps.recvfrom a 8 {}) Errno.EAGAIN
  finally
    safeClose a
    safeClose b

/-- Real `recvfrom` `.connectionState` test (`ENOTCONN` on unconnected TCP socket). -/
private def err_recvfrom_connectionState : IO Unit := do
  let s ← assertOk "tcp sock" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "recvfrom unconnected tcp ENOTCONN" (← defaultOps.recvfrom s 8 {}) Errno.ENOTCONN
  finally
    safeClose s

/-- Mocked `recvfrom` non-transient error paths. -/
private def err_recvfrom_mocked : IO Unit := do
  runMockNetError "recv addr" Errno.ENOENT .addressError (fun fd ops => ops.recvfrom fd 8 {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "recv perm" Errno.EACCES .permissionDenied (fun fd ops => ops.recvfrom fd 8 {} >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `recvfrom` `.transientOrResource` test (`EINTR`). -/
private def err_recvfrom_transient : IO Unit :=
  runMockNetError "recv transient" Errno.EINTR .transientOrResource (fun fd ops => ops.recvfrom fd 8 {} >>= fun r => pure (r.map fun _ => ()))

/-- Real `sendto` `.badFd` test (`EBADF`). -/
private def err_sendto_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "sendto closed" (← defaultOps.sendto cfd (asciiBytes ['a']) { nosignal := true }) Errno.EBADF

/-- Real `sendto` `.invalidArg` test (`EDESTADDRREQ` on unconnected UDP socket). -/
private def err_sendto_invalidArg : IO Unit := do
  let u4 ← assertOk "udp sock" (← defaultOps.socket .inet .dgram nbFlags 0)
  try
    assertErr "sendto unconnected udp EDESTADDRREQ" (← defaultOps.sendto u4 (asciiBytes ['a']) { nosignal := true }) Errno.EDESTADDRREQ
  finally
    safeClose u4

/-- Real `sendto` `.wouldBlockOrInProgress` test (`EAGAIN` when send buffer fills). -/
private def err_sendto_wouldBlock : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
  try
    let big := ByteArray.mk (Array.replicate 65536 65)
    let mut hitAgain := false
    for _ in [0 : 256] do
      match ← defaultOps.sendto a big { nosignal := true, dontwait := true } with
      | .ok _ => pure ()
      | .error e =>
        if e == Errno.EAGAIN then
          hitAgain := true
          break
        else
          throw (IO.userError s!"sendto fill unexpected error {e}")
    assertTrue "hit EAGAIN filling buffer" hitAgain
  finally
    safeClose a
    safeClose b

/-- Real `sendto` `.connectionState` test (`EPIPE` on `SHUT_WR` stream socket). -/
private def err_sendto_connectionState : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
  try
    assertOk "shutdown wr" (← defaultOps.shutdown a .wr)
    assertErr "sendto after SHUT_WR EPIPE" (← defaultOps.sendto a (asciiBytes ['a']) { nosignal := true }) Errno.EPIPE
  finally
    safeClose a
    safeClose b

/-- Mocked `sendto` non-transient error paths. -/
private def err_sendto_mocked : IO Unit := do
  runMockNetError "send addr" Errno.ENOENT .addressError (fun fd ops => ops.sendto fd (asciiBytes ['a']) {} >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "send perm" Errno.EACCES .permissionDenied (fun fd ops => ops.sendto fd (asciiBytes ['a']) {} >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `sendto` `.transientOrResource` test (`ENOBUFS`). -/
private def err_sendto_transient : IO Unit :=
  runMockNetError "send transient" Errno.ENOBUFS .transientOrResource (fun fd ops => ops.sendto fd (asciiBytes ['a']) {} >>= fun r => pure (r.map fun _ => ()))

/-- Real `shutdown` `.badFd` test (`EBADF`). -/
private def err_shutdown_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "shutdown closed" (← defaultOps.shutdown cfd .rdwr) Errno.EBADF

/-- Real `shutdown` `.connectionState` test (`ENOTCONN` on unconnected socket). -/
private def err_shutdown_connectionState : IO Unit := do
  let s ← assertOk "socket" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "shutdown unconnected ENOTCONN" (← defaultOps.shutdown s .rdwr) Errno.ENOTCONN
  finally
    safeClose s

/-- Mocked `shutdown` non-transient error paths. -/
private def err_shutdown_mocked : IO Unit := do
  runMockNetError "shut inv" Errno.EINVAL .invalidArg (fun fd ops => ops.shutdown fd .rd)
  runMockNetError "shut addr" Errno.ENOENT .addressError (fun fd ops => ops.shutdown fd .rd)
  runMockNetError "shut wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.shutdown fd .rd)
  runMockNetError "shut perm" Errno.EPERM .permissionDenied (fun fd ops => ops.shutdown fd .rd)

/-- Mocked `shutdown` `.transientOrResource` test (`EINTR`). -/
private def err_shutdown_transient : IO Unit :=
  runMockNetError "shut transient" Errno.EINTR .transientOrResource (fun fd ops => ops.shutdown fd .rd)

/-- Real `sendmsg` `.badFd` test (`EBADF` on closed socket and closed SCM payload FD). -/
private def err_sendmsg_badFd : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .seqpacket nbFlags)
  let cfd ← closedSockFd
  try
    assertErr "sendmsg closed payload EBADF" (← defaultOps.sendmsg a #[cfd]) Errno.EBADF
    assertErr "sendmsg closed socket EBADF" (← defaultOps.sendmsg cfd #[b]) Errno.EBADF
  finally
    safeClose a
    safeClose b

/-- Real `sendmsg` `.invalidArg` test (`EINVAL` on empty and oversized SCM batch). -/
private def err_sendmsg_invalidArg : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .seqpacket nbFlags)
  try
    assertErr "sendmsg empty" (← defaultOps.sendmsg a #[]) Errno.EINVAL
    assertErr "sendmsg > 32" (← defaultOps.sendmsg a (Array.replicate 33 b)) Errno.EINVAL
    let v4 ← assertOk "inet4 dgram" (← defaultOps.socket .inet .dgram nbFlags 0)
    try
      assertErr "sendmsg non-unix EOPNOTSUPP" (← defaultOps.sendmsg v4 #[b]) Errno.EOPNOTSUPP
    finally
      safeClose v4
  finally
    safeClose a
    safeClose b

/-- Real `sendmsg` `.connectionState` test (`ENOTCONN` on unconnected Unix and `EPIPE` on broken stream). -/
private def err_sendmsg_connectionState : IO Unit := do
  let u ← assertOk "unix" (← defaultOps.socket .unix .dgram nbFlags 0)
  try
    assertErr "sendmsg unconnected ENOTCONN" (← defaultOps.sendmsg u #[u]) Errno.ENOTCONN
  finally
    safeClose u

/-- Mocked `sendmsg` non-transient error paths. -/
private def err_sendmsg_mocked : IO Unit := do
  runMockNetError "sm addr" Errno.ENOENT .addressError (fun fd ops => ops.sendmsg fd #[fd])
  runMockNetError "sm wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.sendmsg fd #[fd])
  runMockNetError "sm perm" Errno.EPERM .permissionDenied (fun fd ops => ops.sendmsg fd #[fd])

/-- Mocked `sendmsg` `.transientOrResource` test (`ENOMEM`). -/
private def err_sendmsg_transient : IO Unit :=
  runMockNetError "sm transient" Errno.ENOMEM .transientOrResource (fun fd ops => ops.sendmsg fd #[fd])

/-- Real `recvmsg` `.badFd` test (`EBADF`). -/
private def err_recvmsg_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "recvmsg closed" (← defaultOps.recvmsg cfd 1) Errno.EBADF

/-- Real `recvmsg` `.invalidArg` test (`EINVAL` on `maxFds = 0`, `> 32`, and unconnected Unix stream). -/
private def err_recvmsg_invalidArg : IO Unit := do
  let u ← assertOk "unix stream" (← defaultOps.socket .unix .stream nbFlags 0)
  try
    assertErr "recvmsg maxFds 0" (← defaultOps.recvmsg u 0) Errno.EINVAL
    assertErr "recvmsg maxFds 33" (← defaultOps.recvmsg u 33) Errno.EINVAL
    assertErr "recvmsg unconnected unix stream" (← defaultOps.recvmsg u 1) Errno.EINVAL
  finally
    safeClose u

/-- Real `recvmsg` `.wouldBlockOrInProgress` test (`EAGAIN`). -/
private def err_recvmsg_wouldBlock : IO Unit := do
  let (a, b) ← assertOk "socketpair" (← defaultOps.socketpair .unix .seqpacket nbFlags)
  try
    assertErr "recvmsg EAGAIN" (← defaultOps.recvmsg a 1) Errno.EAGAIN
  finally
    safeClose a
    safeClose b

/-- Real `recvmsg` `.connectionState` test (`ENOTCONN` on unconnected TCP socket). -/
private def err_recvmsg_connectionState : IO Unit := do
  let s ← assertOk "tcp" (← defaultOps.socket .inet .stream nbFlags 0)
  try
    assertErr "recvmsg unconnected tcp ENOTCONN" (← defaultOps.recvmsg s 1) Errno.ENOTCONN
  finally
    safeClose s

/-- Mocked `recvmsg` non-transient error paths. -/
private def err_recvmsg_mocked : IO Unit := do
  runMockNetError "rm addr" Errno.ENOENT .addressError (fun fd ops => ops.recvmsg fd 1 >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "rm perm" Errno.EACCES .permissionDenied (fun fd ops => ops.recvmsg fd 1 >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `recvmsg` `.transientOrResource` test (`EMFILE`). -/
private def err_recvmsg_transient : IO Unit :=
  runMockNetError "rm transient" Errno.EMFILE .transientOrResource (fun fd ops => ops.recvmsg fd 1 >>= fun r => pure (r.map fun _ => ()))

/-- Real `ioctl` `.badFd` test (`EBADF` and non-socket `ENOTTY`). -/
private def err_ioctl_badFd : IO Unit := do
  let cfd ← closedSockFd
  assertErr "ioctl closed" (← defaultOps.ioctl cfd .getIfFlags loIfname) Errno.EBADF
  let ns ← assertOk "nonsock" (← rawOpenNonsock)
  try
    assertErr "ioctl nonsock ENOTTY" (← defaultOps.ioctl ns .getIfFlags loIfname) Errno.ENOTTY
  finally
    safeClose ns

/-- Real `ioctl` `.invalidArg` test (`EINVAL` on embedded-NUL and `>= IFNAMSIZ` interface names). -/
private def err_ioctl_invalidArg : IO Unit := do
  let fd ← assertOk "sock" (← defaultOps.socket .inet .dgram nbFlags 0)
  try
    assertErr "ioctl NUL" (← defaultOps.ioctl fd .getIfFlags (ByteArray.mk #[108, 0])) Errno.EINVAL
    assertErr "ioctl >= IFNAMSIZ" (← defaultOps.ioctl fd .getIfFlags (ByteArray.mk (Array.replicate 16 97))) Errno.EINVAL
  finally
    safeClose fd

/-- Real `ioctl` `.addressError` test (`ENODEV` on missing or empty interface name). -/
private def err_ioctl_addressError : IO Unit := do
  let fd ← assertOk "sock" (← defaultOps.socket .inet .dgram nbFlags 0)
  try
    assertErr "ioctl empty ENODEV" (← defaultOps.ioctl fd .getIfFlags ByteArray.empty) Errno.ENODEV
    assertErr "ioctl missing ENODEV" (← defaultOps.ioctl fd .getIfFlags (asciiBytes ['n', 'o', 'p', 'e', '0'])) Errno.ENODEV
  finally
    safeClose fd

/-- Real `ioctl` `.permissionDenied` test (`EPERM`/`EACCES` on unprivileged `SIOCSIFFLAGS`; mocked fallback when `CAP_NET_ADMIN` is held). -/
private def err_ioctl_permissionDenied : IO Unit := do
  let fd ← assertOk "sock" (← defaultOps.socket .inet .dgram nbFlags 0)
  try
    let curFlags ← assertOk "ioctl get flags" (← defaultOps.ioctl fd .getIfFlags loIfname)
    match ← defaultOps.ioctl fd (.setIfFlags curFlags) loIfname with
    | .error e =>
      if ![Errno.EPERM, Errno.EACCES].contains e then
        throw (IO.userError s!"ioctl SIOCSIFFLAGS unpriv: unexpected error {e}")
    | .ok _ =>
      runMockNetError "ioctl eperm cap fallback" Errno.EPERM .permissionDenied
        (fun mfd ops => ops.ioctl mfd (.setIfFlags 0) loIfname >>= fun r => pure (r.map fun _ => ()))
  finally
    safeClose fd

/-- Mocked `ioctl` non-transient error paths. -/
private def err_ioctl_mocked : IO Unit := do
  runMockNetError "ioctl wb" Errno.EAGAIN .wouldBlockOrInProgress (fun fd ops => ops.ioctl fd .getIfFlags loIfname >>= fun r => pure (r.map fun _ => ()))
  runMockNetError "ioctl cs" Errno.ENETDOWN .connectionState (fun fd ops => ops.ioctl fd .getIfFlags loIfname >>= fun r => pure (r.map fun _ => ()))

/-- Mocked `ioctl` `.transientOrResource` test (`ENOMEM`). -/
private def err_ioctl_transient : IO Unit :=
  runMockNetError "ioctl transient" Errno.ENOMEM .transientOrResource (fun fd ops => ops.ioctl fd .getIfFlags loIfname >>= fun r => pure (r.map fun _ => ()))

/-- Run live Linux regression checks covering abstract `AF_UNIX`, `SCM_RIGHTS`, and TCP connect-reset edge cases. -/
private def runUnixScmAndConnectResetPart1 : IO Unit := do
  let ops := defaultOps
  let lfd ← assertOk "ux unix reuse listen" (← ops.socket .unix .stream nbFlags 0)
  let cfd ← assertOk "ux unix reuse cli" (← ops.socket .unix .stream { nonblock := false, cloexec := true } 0)
  let nanos ← IO.monoNanosNow
  let absPath := ByteArray.mk (#[0] ++ s!"leanswe-ux-abs-{nanos}".toUTF8.data)
  try
    assertOk "ux reuse set" (← ops.setsockopt lfd .reuseAddr 1)
    assertOk "ux bind abs" (← ops.bind lfd (.unix absPath))
    let gsnAbs ← assertOk "ux gsn abs" (← ops.getsockname lfd)
    assertTrue "ux abs roundtrip" (gsnAbs == .unix absPath)
    assertOk "ux listen" (← ops.listen lfd 4)
    assertOk "ux connect abs" (← ops.connect cfd (.unix absPath))
    let (afd, _) ← assertOk "ux accept4" (← ops.accept4 lfd nbFlags)
    try
      assertTrue "ux accept4 AF_UNIX reuseAddr=0" ((← assertOk "get reuse" (← ops.getsockopt afd .reuseAddr)) == 0)
      let payload ← assertOk "ux dummy fd" (← ops.socket .inet .dgram nbFlags 0)
      try
        assertOk "ux sendmsg scm" (← ops.sendmsg cfd #[payload])
      finally
        safeClose payload
      let _ ← assertOk "ux unread send" (← ops.sendto afd (asciiBytes ['z']) { nosignal := true })
      safeClose cfd
      assertTrue "ux unix stream unread ECONNRESET" ((← assertOk "soerr" (← ops.getsockopt afd .error)) == Errno.ECONNRESET.toNat.toUInt32)
      let recvd ← assertOk "ux deferred scm" (← ops.recvmsg afd 4)
      safeCloseAll recvd
      assertTrue "ux received deferred fd" (recvd.size == 1)
    finally
      safeClose afd
  finally
    safeClose lfd
    safeClose cfd
  let path108 := ByteArray.mk (#[0] ++ Array.replicate 107 98)
  let path109 := ByteArray.mk (#[0] ++ Array.replicate 108 98)
  let s108 ← assertOk "ux s108" (← ops.socket .unix .dgram nbFlags 0)
  try
    assertOk "ux bind 108" (← ops.bind s108 (.unix path108))
    assertErr "ux bind 109 EINVAL" (← ops.bind s108 (.unix path109)) Errno.EINVAL
    let g108 ← assertOk "ux gsn 108" (← ops.getsockname s108)
    assertTrue "ux 108 matches" (g108 == .unix path108)
  finally
    safeClose s108
  let s64 ← assertOk "ux s64" (← ops.socket .inet6 .dgram nbFlags 0)
  try
    let v4mappedAny : UInt64 := 0x0000ffff00000000
    assertOk "ux bind ::ffff:0.0.0.0" (← ops.bind s64 (.ipv6 0 v4mappedAny 0))
    match ← assertOk "ux gsn v4mapped" (← ops.getsockname s64) with
    | .ipv6 hi lo p _ _ => assertTrue "ux v4mapped any" (hi == 0 && lo == v4mappedAny && p != 0)
    | _ => throw (IO.userError "ux gsn v4mapped unexpected")
  finally
    safeClose s64
  let dead ← assertOk "ux dead l" (← ops.socket .inet .stream nbFlags 0)
  assertOk "ux dead bind" (← ops.bind dead (.ipv4 INADDR_LOOPBACK 0))
  let deadPort ← match ← assertOk "ux dead gsn" (← ops.getsockname dead) with
    | .ipv4 _ p => pure p
    | _ => pure 0
  safeClose dead
  let blk ← assertOk "ux blk tcp" (← ops.socket .inet .stream { nonblock := false, cloexec := true } 0)
  try
    assertErr "ux blk connect refused" (← ops.connect blk (.ipv4 INADDR_LOOPBACK deadPort)) Errno.ECONNREFUSED
    assertErr "ux shutdown after failed connect" (← ops.shutdown blk .rdwr) Errno.ENOTCONN
    match ← assertOk "ux blk gsn after fail" (← ops.getsockname blk) with
    | .ipv4 a p => assertTrue "ux reset to 0.0.0.0:port" (a == 0 && p != 0)
    | _ => throw (IO.userError "ux blk gsn unexpected")
    assertOk "ux blk re-bind" (← ops.bind blk (.ipv4 INADDR_LOOPBACK 0))
    assertOk "ux blk listen" (← ops.listen blk 2)
  finally
    safeClose blk
  let (pa, pb) ← assertOk "ux pair stream" (← ops.socketpair .unix .stream nbFlags)
  let scmFd ← assertOk "ux scm fd" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ux sendmsg stream" (← ops.sendmsg pa #[scmFd])
    let r0 ← assertOk "ux recvfrom 0 strips scm" (← ops.recvfrom pb 0 {})
    assertTrue "ux r0 empty" (r0.size == 0)
    let rmStripped ← assertOk "ux recvmsg gets stripped byte" (← ops.recvmsg pb 4)
    assertTrue "ux stripped 0 fds" rmStripped.isEmpty
    assertErr "ux recvmsg empty EAGAIN" (← ops.recvmsg pb 4) Errno.EAGAIN
  finally
    safeClose scmFd
    safeClose pa
    safeClose pb
  let (sa, sb) ← assertOk "ux pair seqpacket" (← ops.socketpair .unix .seqpacket nbFlags)
  try
    let _ ← assertOk "ux seq send" (← ops.sendto sa (asciiBytes ['q']) { nosignal := true })
    let _ ← assertOk "ux seq unread to sa" (← ops.sendto sb (asciiBytes ['x']) { nosignal := true })
    safeClose sa
    assertErr "ux seq unread ECONNRESET first" (← ops.recvfrom sb 8 {}) Errno.ECONNRESET
    let q ← assertOk "ux seq drained q" (← ops.recvfrom sb 8 {})
    assertTrue "ux seq got q" (q.data == (asciiBytes ['q']).data)
  finally
    safeClose sb

private def runUnixScmAndConnectResetPart2 : IO Unit := do
  let ops := defaultOps
  let nanos ← IO.monoNanosNow
  let ua ← assertOk "ux udp a" (← ops.socket .inet .dgram { nonblock := false, cloexec := true } 0)
  let ub ← assertOk "ux udp b" (← ops.socket .inet .dgram nbFlags 0)
  let uc ← assertOk "ux udp c" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ux ua bind" (← ops.bind ua (.ipv4 INADDR_LOOPBACK 0))
    assertOk "ux ub bind" (← ops.bind ub (.ipv4 INADDR_LOOPBACK 0))
    assertOk "ux uc bind" (← ops.bind uc (.ipv4 INADDR_LOOPBACK 0))
    let paPort ← match ← assertOk "ux ua gsn" (← ops.getsockname ua) with | .ipv4 _ p => pure p | _ => pure 0
    let pbPort ← match ← assertOk "ux ub gsn" (← ops.getsockname ub) with | .ipv4 _ p => pure p | _ => pure 0
    let pcPort ← match ← assertOk "ux uc gsn" (← ops.getsockname uc) with | .ipv4 _ p => pure p | _ => pure 0
    assertOk "ux ub connect ua" (← ops.connect ub (.ipv4 INADDR_LOOPBACK paPort))
    assertOk "ux uc connect ub" (← ops.connect uc (.ipv4 INADDR_LOOPBACK pbPort))
    let _ ← assertOk "ux uc->ub" (← ops.sendto uc (asciiBytes ['m']) {})
    assertErr "ux ub drops uc EAGAIN" (← ops.recvfrom ub 8 {}) Errno.EAGAIN
    assertOk "ux uc connect ua" (← ops.connect uc (.ipv4 INADDR_LOOPBACK paPort))
    assertErr "ux uc gets ECONNREFUSED from ub mismatch" (← ops.sendto uc (asciiBytes ['k']) {}) Errno.ECONNREFUSED
    assertErr "ux unconnected ua shutRd ENOTCONN" (← ops.shutdown ua .rd) Errno.ENOTCONN
    assertOk "ux ua connect uc" (← ops.connect ua (.ipv4 INADDR_LOOPBACK pcPort))
    let _ ← assertOk "ux uc->ua" (← ops.sendto uc (asciiBytes ['k']) {})
    assertErr "ux connected udp sendmsg EOPNOTSUPP" (← ops.sendmsg uc #[ub]) Errno.EOPNOTSUPP
    assertOk "ux ua shutRd" (← ops.shutdown ua .rd)
    let gotK ← assertOk "ux ua drain k" (← ops.recvfrom ua 8 {})
    assertTrue "ux got k" (gotK.data == (asciiBytes ['k']).data)
    let eof ← assertOk "ux ua shutRd eof" (← ops.recvfrom ua 8 {})
    assertTrue "ux ua eof" (eof.size == 0)
  finally
    safeClose ua
    safeClose ub
    safeClose uc
  let ud1 ← assertOk "ux ud1" (← ops.socket .unix .dgram nbFlags 0)
  let ud2 ← assertOk "ux ud2" (← ops.socket .unix .dgram nbFlags 0)
  let ud3 ← assertOk "ux ud3" (← ops.socket .unix .dgram nbFlags 0)
  try
    let p1 := ByteArray.mk (#[0] ++ s!"leanswe-ux-ud1-{nanos}".toUTF8.data)
    let p2 := ByteArray.mk (#[0] ++ s!"leanswe-ux-ud2-{nanos}".toUTF8.data)
    let p3 := ByteArray.mk (#[0] ++ s!"leanswe-ux-ud3-{nanos}".toUTF8.data)
    assertOk "ux ud1 bind" (← ops.bind ud1 (.unix p1))
    assertOk "ux ud2 bind" (← ops.bind ud2 (.unix p2))
    assertOk "ux ud3 bind" (← ops.bind ud3 (.unix p3))
    assertOk "ux ud2 shutRd" (← ops.shutdown ud2 .rd)
    assertOk "ux ud1 connect ud2" (← ops.connect ud1 (.unix p2))
    assertErr "ux ud1 send after peer shutRd EPIPE" (← ops.sendto ud1 (asciiBytes ['x']) { nosignal := true }) Errno.EPIPE
    assertOk "ux ud2 connect ud3" (← ops.connect ud2 (.unix p3))
    assertErr "ux ud1 send to connected ud2 EPERM" (← ops.sendto ud1 (asciiBytes ['y']) {}) Errno.EPERM
    let p4 := ByteArray.mk (#[0] ++ s!"leanswe-ux-ud4-{nanos}".toUTF8.data)
    let ud4 ← assertOk "ux ud4" (← ops.socket .unix .dgram nbFlags 0)
    try
      assertOk "ux ud4 bind" (← ops.bind ud4 (.unix p4))
      assertOk "ux ud1 connect ud4" (← ops.connect ud1 (.unix p4))
      assertOk "ux ud4 self connect" (← ops.connect ud4 (.unix p4))
      assertOk "ux ud4 shut rdwr" (← ops.shutdown ud4 .rdwr)
      assertErr "ux ud1 send to self-connected shutRdwr ud4 EPERM" (← ops.sendto ud1 (asciiBytes ['z']) { nosignal := true }) Errno.EPERM
    finally
      safeClose ud4
  finally
    safeClose ud1
    safeClose ud2
    safeClose ud3
  let uxSeq ← assertOk "ux ux seq" (← ops.socket .unix .seqpacket nbFlags 0)
  try
    let pSeq := ByteArray.mk (#[0] ++ s!"leanswe-ux-seq-{nanos}".toUTF8.data)
    assertOk "ux ux seq bind" (← ops.bind uxSeq (.unix pSeq))
    assertOk "ux ux seq pre-listen shutdown" (← ops.shutdown uxSeq .wr)
    assertOk "ux ux seq listen" (← ops.listen uxSeq 4)
    assertErrOneOf "ux ux seq listen self-connect" (← ops.connect uxSeq (.unix pSeq))
      [Errno.EISCONN, Errno.EINVAL, Errno.EOPNOTSUPP]
  finally
    safeClose uxSeq
  let d6 ← assertOk "ux dgram6" (← ops.socket .inet6 .dgram nbFlags 0)
  try
    assertOk "ux d6 connect v4" (← ops.connect d6 (.ipv4 INADDR_LOOPBACK 9))
    assertErr "ux d6 connect ::1 EAFNOSUPPORT" (← ops.connect d6 (.ipv6 0 1 9)) Errno.EAFNOSUPPORT
  finally
    safeClose d6
  let sc ← assertOk "ux tcp self" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ux sc bind" (← ops.bind sc (.ipv4 INADDR_LOOPBACK 0))
    let scAddr ← assertOk "ux sc gsn" (← ops.getsockname sc)
    let scPort := match scAddr with | .ipv4 _ p => p | _ => 0
    let _ ← ops.connect sc scAddr
    assertOk "ux sc self shutWr" (← ops.shutdown sc .wr)
    assertErr "ux sc rebind same port EADDRINUSE" (← ops.bind sc scAddr) Errno.EADDRINUSE
    match ← assertOk "ux sc gsn zeroed ip" (← ops.getsockname sc) with
    | .ipv4 a p => assertTrue "ux sc 0.0.0.0:port" (a == 0 && p == scPort)
    | _ => throw (IO.userError "ux sc gsn unexpected")
    assertOk "ux sc rebind port 0" (← ops.bind sc (.ipv4 INADDR_LOOPBACK 0))
  finally
    safeClose sc
  let rstL ← assertOk "ux rst l" (← ops.socket .inet .stream nbFlags 0)
  let rstC ← assertOk "ux rst c" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ux rst l bind" (← ops.bind rstL (.ipv4 INADDR_LOOPBACK 0))
    let rstAddr ← assertOk "ux rst l gsn" (← ops.getsockname rstL)
    assertOk "ux rst l listen" (← ops.listen rstL 4)
    let _ ← ops.connect rstC rstAddr
    let _ ← assertOk "ux rst c send" (← ops.sendto rstC (asciiBytes ['r']) { nosignal := true })
    let (rstA, _) ← assertOk "ux rst accept4" (← ops.accept4 rstL nbFlags)
    safeClose rstA
    assertOk "ux rst c rebind after peer rst" (← ops.bind rstC (.ipv4 INADDR_LOOPBACK 0))
  finally
    safeClose rstL
    safeClose rstC

private def runUnixScmAndConnectResetPart3 : IO Unit := do
  let ops := defaultOps
  let shutLis ← assertOk "ux shutlis sock" (← ops.socket .inet .stream { nonblock := false, cloexec := true } 0)
  let shutCli ← assertOk "ux shutcli sock" (← ops.socket .inet .stream { nonblock := false, cloexec := false } IPPROTO_TCP)
  try
    assertErr "ux shutlis rdwr ENOTCONN" (← ops.shutdown shutLis .rdwr) Errno.ENOTCONN
    assertOk "ux shutlis listen" (← ops.listen shutLis 16)
    let slAddr ← assertOk "ux shutlis gsn" (← ops.getsockname shutLis)
    let slPort := match slAddr with | .ipv4 _ p => p | _ => 0
    assertOk "ux shutcli connect" (← ops.connect shutCli (.ipv4 0x7f000002 slPort))
    let _ ← assertOk "ux shutcli sendto" (← ops.sendto shutCli (ByteArray.mk #[1, 2, 3]) { nosignal := true, dontwait := true })
    let (shutAcc, _) ← assertOk "ux shutlis accept4" (← ops.accept4 shutLis nbFlags)
    try
      assertErr "ux shutacc sendto ECONNRESET" (← ops.sendto shutAcc (ByteArray.mk #[4, 5]) { nosignal := true }) Errno.ECONNRESET
      assertErr "ux shutacc sendto2 EPIPE" (← ops.sendto shutAcc (ByteArray.mk #[4, 5]) { nosignal := true }) Errno.EPIPE
    finally
      safeClose shutAcc
  finally
    safeClose shutCli
    safeClose shutLis
  let shutConn ← assertOk "ux shutconn sock" (← ops.socket .inet .stream { nonblock := false, cloexec := true } IPPROTO_TCP)
  try
    assertOk "ux shutconn listen" (← ops.listen shutConn 4)
    let scAddr ← assertOk "ux shutconn gsn" (← ops.getsockname shutConn)
    assertOk "ux shutconn shut1" (← ops.shutdown shutConn .rdwr)
    assertErr "ux shutconn shut2 ENOTCONN" (← ops.shutdown shutConn .rdwr) Errno.ENOTCONN
    assertErr "ux shutconn connect ECONNREFUSED" (← ops.connect shutConn scAddr) Errno.ECONNREFUSED
    assertErr "ux shutconn recv ENOTCONN" (← ops.recvfrom shutConn 64 {}) Errno.ENOTCONN
  finally
    safeClose shutConn

private def runUnixScmAndConnectResetPart4 : IO Unit := do
  let ops := defaultOps
  let v4mLis ← assertOk "ux v4m lis" (← ops.socket .inet6 .stream nbFlags 0)
  let v4mCli ← assertOk "ux v4m cli" (← ops.socket .inet6 .stream { nonblock := false, cloexec := true } 0)
  let v4mClosed ← assertOk "ux v4m closed port" (← ops.socket .inet6 .stream nbFlags 0)
  let v4mNbCli ← assertOk "ux v4m nb cli" (← ops.socket .inet6 .stream nbFlags IPPROTO_TCP)
  try
    assertOk "ux v4m lis listen" (← ops.listen v4mLis 8)
    let v4mLisAddr ← assertOk "ux v4m lis gsn" (← ops.getsockname v4mLis)
    let v4mClosedAddr ← assertOk "ux v4m closed gsn" (← ops.getsockname v4mClosed)
    safeClose v4mClosed
    match v4mClosedAddr, v4mLisAddr with
    | .ipv6 _ _ cp _ _, .ipv6 _ _ lp _ _ =>
      assertErr "ux v4m first connect ECONNREFUSED"
        (← ops.connect v4mCli (SockAddr.ipv6 0 0xffff7f000001 cp 0 0)) Errno.ECONNREFUSED
      assertOk "ux v4m reconnect to v4m succeeds"
        (← ops.connect v4mCli (SockAddr.ipv6 0 0xffff7f000001 lp 0 0))
      let _ ← ops.connect v4mNbCli (SockAddr.ipv6 0 0xffff7f000001 cp 0 0)
      let _ ← ops.getsockopt v4mNbCli .error
      let _ ← ops.connect v4mNbCli (SockAddr.ipv6 0 1 lp 0 0)
    | _, _ => pure ()
  finally
    safeClose v4mNbCli
    safeClose v4mCli
    safeClose v4mLis
  let (gcA, gcB) ← assertOk "ux unix gc sp" (← ops.socketpair .unix .seqpacket nbFlags)
  try
    assertOk "ux unix gc sendmsg self" (← ops.sendmsg gcB #[gcA])
    safeClose gcA
    let gcTmp ← assertOk "ux unix gc trigger" (← ops.socket .unix .dgram nbFlags 0)
    safeClose gcTmp
    let _ ← ops.sendmsg gcB #[gcB]
  finally
    safeClose gcB
  let tcpResetGsn ← assertOk "ux tcp reset gsn sock" (← ops.socket .inet .stream nbFlags 0)
  try
    assertErr "ux tcp reset gsn c1 EINPROGRESS"
      (← ops.connect tcpResetGsn (.ipv4 0x7f000001 1)) Errno.EINPROGRESS
    let _ ← assertOk "ux tcp reset gsn 1" (← ops.getsockname tcpResetGsn)
    let _ ← ops.connect tcpResetGsn (.ipv4 0x7f000001 1)
    let _ ← assertOk "ux tcp reset gsn 2" (← ops.getsockname tcpResetGsn)
  finally
    safeClose tcpResetGsn

private def runUnixScmAndConnectResetPart5 : IO Unit := do
  let ops := defaultOps
  let v4mTaintRecv ← assertOk "ux v4m tainted recv sock" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertErr "ux v4m tainted c1 EINPROGRESS"
      (← ops.connect v4mTaintRecv (.ipv6 0 0x0000ffff7f000001 1 0 0)) Errno.EINPROGRESS
    assertErr "ux v4m tainted c2 ECONNREFUSED"
      (← ops.connect v4mTaintRecv (.unix (ByteArray.mk #[47, 116, 109, 112, 47, 110, 111, 110, 101]))) Errno.ECONNREFUSED
    let gsn ← assertOk "ux v4m tainted gsn" (← ops.getsockname v4mTaintRecv)
    let port := match gsn with | .ipv6 _ _ p _ _ => p | _ => 0
    assertErr "ux v4m tainted native self EINPROGRESS"
      (← ops.connect v4mTaintRecv (.ipv6 0 1 port 0 0)) Errno.EINPROGRESS
    assertErr "ux v4m tainted native recv EAGAIN"
      (← ops.recvfrom v4mTaintRecv 64 {}) Errno.EAGAIN
  finally
    safeClose v4mTaintRecv
  let (dgramA, dgramB) ← assertOk "ux unix dgram reconnect sp" (← ops.socketpair .unix .dgram nbFlags)
  let dgramTarget ← assertOk "ux unix dgram target" (← ops.socket .unix .dgram nbFlags 0)
  try
    let absPath := ByteArray.mk #[0, 117, 120, 95, 100, 103, 114, 97, 109, 95, 114, 101, 99, 111, 110, 110]
    assertOk "ux unix dgram target bind" (← ops.bind dgramTarget (.unix absPath))
    let _ ← assertOk "ux unix dgram sp send" (← ops.sendto dgramA (ByteArray.mk #[1, 2, 3]) {})
    assertOk "ux unix dgram reconnect" (← ops.connect dgramB (.unix absPath))
    let soErr ← assertOk "ux unix dgram old peer soError" (← ops.getsockopt dgramA .error)
    assertTrue "ux unix dgram old peer ECONNRESET" (soErr == Errno.ECONNRESET)
  finally
    safeClose dgramTarget
    safeClose dgramB
    safeClose dgramA
  let selfSeg ← assertOk "ux tcp self seg sock" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ux tcp self seg bind" (← ops.bind selfSeg (.ipv4 0x7f000002 0))
    let selfSa ← assertOk "ux tcp self seg gsn" (← ops.getsockname selfSeg)
    assertErr "ux tcp self seg connect EINPROGRESS" (← ops.connect selfSeg selfSa) Errno.EINPROGRESS
    let _ ← assertOk "ux tcp self seg send1" (← ops.sendto selfSeg (ByteArray.mk #[1, 2, 3, 4]) { nosignal := true })
    let _ ← assertOk "ux tcp self seg send2" (← ops.sendto selfSeg (ByteArray.mk #[5, 6, 7]) { nosignal := true, dontwait := true })
    let _ ← assertOk "ux tcp self seg send3" (← ops.sendto selfSeg (ByteArray.mk #[8, 9, 10, 11]) { nosignal := true })
    let r1 ← assertOk "ux tcp self seg recv1" (← ops.recvfrom selfSeg 64 {})
    assertTrue "ux tcp self seg recv1 non-empty" (r1.data.size >= 1)
    let _ ← ops.recvfrom selfSeg 1 { dontwait := true }
  finally
    safeClose selfSeg
  let resetSock ← assertOk "ux listen shutdown reset sock" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertOk "ux listen shutdown reset listen" (← ops.listen resetSock 0)
    let lsa ← assertOk "ux listen shutdown reset gsn1" (← ops.getsockname resetSock)
    let p1 := match lsa with | .ipv6 _ _ p _ _ => p | _ => 0
    assertTrue "ux listen shutdown reset port1 nonzero" (p1 != 0)
    assertOk "ux listen shutdown reset shut" (← ops.shutdown resetSock .rdwr)
    assertErr "ux listen shutdown reset c1 EINPROGRESS"
      (← ops.connect resetSock (.ipv6 0 1 p1 0 0)) Errno.EINPROGRESS
    let csa ← assertOk "ux listen shutdown reset gsn2" (← ops.getsockname resetSock)
    assertErr "ux listen shutdown reset c2 ECONNREFUSED" (← ops.connect resetSock csa) Errno.ECONNREFUSED
    let rgsn ← assertOk "ux listen shutdown reset gsn3" (← ops.getsockname resetSock)
    match csa, rgsn with
    | .ipv6 _ _ p2 _ _, .ipv6 hi lo p3 _ _ =>
      assertTrue "ux listen shutdown reset wildcard IP" (hi == 0 && lo == 0 && p3 == p2)
    | _, _ => throw (IO.userError "expected ipv6 getsockname after reset")
  finally
    safeClose resetSock
  let uShutCli ← assertOk "ux unix shut before connect cli" (← ops.socket .unix .seqpacket nbFlags 0)
  let uShutLis ← assertOk "ux unix shut before connect lis" (← ops.socket .unix .seqpacket nbFlags 0)
  let mut uShutAccOpt := none
  try
    assertOk "ux unix shut before connect shut" (← ops.shutdown uShutCli .rdwr)
    let uShutPath := ByteArray.mk #[0, 117, 120, 95, 117, 115, 104, 117, 116, 95, 98, 101, 102, 111, 114, 101]
    assertOk "ux unix shut before connect bind" (← ops.bind uShutLis (.unix uShutPath))
    assertOk "ux unix shut before connect listen" (← ops.listen uShutLis 4)
    assertOk "ux unix shut before connect conn" (← ops.connect uShutCli (.unix uShutPath))
    let (accFd, _) ← assertOk "ux unix shut before connect accept" (← ops.accept4 uShutLis nbFlags)
    uShutAccOpt := some accFd
    assertErr "ux unix shut before connect peer EPIPE"
      (← ops.sendto accFd (ByteArray.mk #[1, 2, 3, 4]) { nosignal := true, dontwait := true }) Errno.EPIPE
  finally
    if let some accFd := uShutAccOpt then
      safeClose accFd
    safeClose uShutLis
    safeClose uShutCli
  let lisWrCli ← assertOk "ux lis shut_wr cli" (← ops.socket .inet .stream nbFlags 0)
  let lisWrSrv ← assertOk "ux lis shut_wr lis" (← ops.socket .inet .stream nbFlags 6)
  let mut lisWrAccOpt := none
  let mut lisWrCliClosed := false
  try
    assertOk "ux lis shut_wr listen" (← ops.listen lisWrSrv 4)
    let lsa ← assertOk "ux lis shut_wr gsn" (← ops.getsockname lisWrSrv)
    let lport := match lsa with | .ipv4 _ p => p | _ => 0
    assertOk "ux lis shut_wr shutdown wr" (← ops.shutdown lisWrSrv .wr)
    assertErr "ux lis shut_wr connect EINPROGRESS"
      (← ops.connect lisWrCli (.ipv4 0x7f000002 lport)) Errno.EINPROGRESS
    let (accFd, _) ← assertOk "ux lis shut_wr accept4" (← ops.accept4 lisWrSrv nbFlags)
    lisWrAccOpt := some accFd
    let _ ← assertOk "ux lis shut_wr close cli" (← rawNetClose lisWrCli)
    lisWrCliClosed := true
    assertErr "ux lis shut_wr acc bind EINVAL" (← ops.bind accFd (.ipv4 0x7f000002 0)) Errno.EINVAL
  finally
    if let some accFd := lisWrAccOpt then
      safeClose accFd
    safeClose lisWrSrv
    if !lisWrCliClosed then
      safeClose lisWrCli

private def runUnixScmAndConnectResetPart6 : IO Unit := do
  let ops := defaultOps
  let rstLis ← assertOk "ux shutmask rst lis" (← ops.socket .inet .stream { nonblock := false, cloexec := true } IPPROTO_TCP)
  let rstCli ← assertOk "ux shutmask rst cli" (← ops.socket .inet .stream nbFlags 0)
  let mut rstAcc? : Option _ := none
  try
    assertErr "ux shutmask pre-listen shut" (← ops.shutdown rstLis .rdwr) Errno.ENOTCONN
    assertOk "ux shutmask listen" (← ops.listen rstLis 4294967295)
    let rlsa ← assertOk "ux shutmask gsn" (← ops.getsockname rstLis)
    assertErr "ux shutmask connect" (← ops.connect rstCli rlsa) Errno.EINPROGRESS
    let sent ← assertOk "ux shutmask send" (← ops.sendto rstCli (ByteArray.mk #[88, 1, 2]) {})
    if sent == 0 then throw (IO.userError "ux shutmask send returned 0")
    let (accFd, _) ← assertOk "ux shutmask accept4" (← ops.accept4 rstLis nbFlags)
    rstAcc? := some accFd
    assertOk "ux shutmask accept rebind" (← ops.bind accFd (.ipv4 0 0))
    assertOk "ux shutmask cli rebind" (← ops.bind rstCli (.ipv4 0x7f000001 0))
    let cliSa ← assertOk "ux shutmask cli gsn" (← ops.getsockname rstCli)
    assertErr "ux shutmask cli reset v6" (← ops.connect rstCli (.ipv6 0 1 0 0 0)) Errno.EPIPE
    assertErr "ux shutmask cli self connect" (← ops.connect rstCli cliSa) Errno.EINPROGRESS
    let selfSent ← assertOk "ux shutmask cli self send" (← ops.sendto rstCli (ByteArray.mk #[1, 2, 3, 4]) { nosignal := true })
    if selfSent != 4 then throw (IO.userError s!"ux shutmask cli self send returned {selfSent}")
  finally
    if let some afd := rstAcc? then safeClose afd
    safeClose rstCli
    safeClose rstLis
  let cwLis ← assertOk "ux cw rst lis" (← ops.socket .inet6 .stream nbFlags 0)
  let cwCli ← assertOk "ux cw rst cli" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertErr "ux cw rst shut wr" (← ops.shutdown cwLis .wr) Errno.ENOTCONN
    assertOk "ux cw rst bind" (← ops.bind cwLis (.ipv6 0 0xffff7f000001 0 0 0))
    let cwSa ← assertOk "ux cw rst gsn" (← ops.getsockname cwLis)
    assertOk "ux cw rst listen" (← ops.listen cwLis 4294967295)
    assertErr "ux cw rst connect" (← ops.connect cwCli cwSa) Errno.EINPROGRESS
    safeClose cwLis
    let cwSelf ← assertOk "ux cw rst cli gsn" (← ops.getsockname cwCli)
    assertErr "ux cw rst reconnect EPIPE" (← ops.connect cwCli cwSelf) Errno.EPIPE
  finally
    safeClose cwCli
    safeClose cwLis
  let v4mCli ← assertOk "ux v4m taint cli" (← ops.socket .inet6 .stream nbFlags 0)
  let v4mSink ← assertOk "ux v4m taint sink" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ux v4m taint sink bind" (← ops.bind v4mSink (.ipv4 0x7f000001 0))
    let sinkSa ← assertOk "ux v4m taint sink gsn" (← ops.getsockname v4mSink)
    let sinkPort := match sinkSa with | .ipv4 _ p => p | _ => 0
    let v4mAddr : SockAddr := .ipv6 0 (0x0000ffff00000000 ||| 0x7f000001) sinkPort 0 0
    assertErr "ux v4m taint c1" (← ops.connect v4mCli v4mAddr) Errno.EINPROGRESS
    let selfV4m ← assertOk "ux v4m taint gsn" (← ops.getsockname v4mCli)
    assertErr "ux v4m taint c2" (← ops.connect v4mCli selfV4m) Errno.ECONNREFUSED
    assertErr "ux v4m taint c3 ::1" (← ops.connect v4mCli (.ipv6 0 1 80 0 0)) Errno.EINPROGRESS
  finally
    safeClose v4mSink
    safeClose v4mCli
  let udpSrv ← assertOk "ux udp self srv" (← ops.socket .inet .dgram nbFlags 0)
  let udpCli ← assertOk "ux udp self cli" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ux udp self srv bind" (← ops.bind udpSrv (.ipv4 0x7f000001 0))
    let usa ← assertOk "ux udp self srv gsn" (← ops.getsockname udpSrv)
    assertOk "ux udp self srv conn" (← ops.connect udpSrv usa)
    assertOk "ux udp self cli conn" (← ops.connect udpCli usa)
    let sent ← assertOk "ux udp self cli send" (← ops.sendto udpCli (ByteArray.mk #[1, 2, 3, 4]) { nosignal := true })
    if sent != 4 then throw (IO.userError s!"ux udp self cli send returned {sent}")
    assertErr "ux udp self cli recv ECONNREFUSED" (← ops.recvfrom udpCli 64 { peek := true }) Errno.ECONNREFUSED
  finally
    safeClose udpCli
    safeClose udpSrv
  let synShutCli ← assertOk "ux syn shut cli" (← ops.socket .inet6 .stream nbFlags 0)
  let synShutSink ← assertOk "ux syn shut sink" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ux syn shut sink bind" (← ops.bind synShutSink (.ipv4 0x7f000001 0))
    let sinkSa ← assertOk "ux syn shut sink gsn" (← ops.getsockname synShutSink)
    let sinkPort := match sinkSa with | .ipv4 _ p => p | _ => 0
    let v4mAddr : SockAddr := .ipv6 0 (0x0000ffff00000000 ||| 0x7f000001) sinkPort 0 0
    assertErr "ux syn shut c1" (← ops.connect synShutCli v4mAddr) Errno.EINPROGRESS
    assertErrOneOf "ux syn shut c2" (← ops.connect synShutCli sinkSa) [Errno.EAFNOSUPPORT, Errno.ECONNREFUSED]
    let cSa ← assertOk "ux syn shut cli gsn" (← ops.getsockname synShutCli)
    assertErr "ux syn shut c3 self" (← ops.connect synShutCli cSa) Errno.EINPROGRESS
    assertOk "ux syn shut rd" (← ops.shutdown synShutCli .rd)
    assertErr "ux syn shut post connect EINPROGRESS" (← ops.connect synShutCli (.ipv6 0 1 80 0 0)) Errno.EINPROGRESS
  finally
    safeClose synShutSink
    safeClose synShutCli

private def runUnixScmAndConnectResetPart7 : IO Unit := do
  let ops := defaultOps
  let udDst ← assertOk "ux unix dgram dst" (← ops.socket .unix .dgram nbFlags 0)
  let (udA, udB) ← assertOk "ux unix dgram pair" (← ops.socketpair .unix .dgram nbFlags)
  try
    let absPath := ByteArray.mk #[0, 117, 120, 95, 117, 100, 95, 114, 101, 99]
    assertOk "ux unix dgram dst bind" (← ops.bind udDst (.unix absPath))
    assertOk "ux unix dgram B shut rd" (← ops.shutdown udB .rd)
    assertOk "ux unix dgram A reconnect" (← ops.connect udA (.unix absPath))
    let sent ← assertOk "ux unix dgram A sendto" (← ops.sendto udA (ByteArray.mk #[238]) { nosignal := true, dontwait := true })
    if sent != 1 then throw (IO.userError s!"ux unix dgram A sendto returned {sent}")
  finally
    safeClose udB
    safeClose udA
    safeClose udDst
  let uhSrv ← assertOk "ux unhashed listen srv" (← ops.socket .inet .stream nbFlags IPPROTO_TCP)
  let uhCli ← assertOk "ux unhashed listen cli" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertErr "ux unhashed listen c1" (← ops.connect uhSrv (.ipv4 INADDR_LOOPBACK 1)) Errno.EINPROGRESS
    IO.sleep 10
    let oldSa ← assertOk "ux unhashed listen gsn1" (← ops.getsockname uhSrv)
    let oldP := match oldSa with | .ipv4 _ p => p | _ => 0
    assertErr "ux unhashed listen c2" (← ops.connect uhSrv (.ipv4 INADDR_LOOPBACK oldP)) Errno.ECONNREFUSED
    assertOk "ux unhashed listen" (← ops.listen uhSrv 4)
    let newSa ← assertOk "ux unhashed listen gsn2" (← ops.getsockname uhSrv)
    let newP := match newSa with | .ipv4 _ p => p | _ => 0
    if newP == oldP || newP == 0 then
      throw (IO.userError s!"ux unhashed listen expected new ephemeral port != {oldP}, got {newP}")
    let mappedOld : SockAddr := .ipv6 0 (0xffff00000000 + INADDR_LOOPBACK.toNat.toUInt64) oldP 0 0
    assertErr "ux unhashed listen cli conn" (← ops.connect uhCli mappedOld) Errno.EINPROGRESS
    IO.sleep 10
    assertErr "ux unhashed listen cli recv" (← ops.recvfrom uhCli 64 { dontwait := true }) Errno.ECONNREFUSED
  finally
    safeClose uhCli
    safeClose uhSrv
  let uFullSrv ← assertOk "ux unix full srv" (← ops.socket .unix .seqpacket nbFlags 0)
  let uFullCli ← assertOk "ux unix full cli" (← ops.socket .unix .seqpacket nbFlags 0)
  try
    let absFull := ByteArray.mk #[0, 117, 120, 95, 117, 95, 102, 117, 108, 108]
    assertOk "ux unix full bind" (← ops.bind uFullSrv (.unix absFull))
    assertOk "ux unix full listen" (← ops.listen uFullSrv 0)
    assertOk "ux unix full cli conn" (← ops.connect uFullCli (.unix absFull))
    assertErr "ux unix full self conn" (← ops.connect uFullSrv (.unix absFull)) Errno.EAGAIN
  finally
    safeClose uFullCli
    safeClose uFullSrv
  let udSrv2 ← assertOk "ux ud2 srv" (← ops.socket .unix .dgram nbFlags 0)
  let (ud2A, ud2B) ← assertOk "ux ud2 pair" (← ops.socketpair .unix .dgram nbFlags)
  try
    let absUd2 := ByteArray.mk #[0, 117, 120, 95, 117, 100, 50, 95, 115, 114, 118]
    assertOk "ux ud2 bind" (← ops.bind udSrv2 (.unix absUd2))
    assertOk "ux ud2 B connect" (← ops.connect ud2B (.unix absUd2))
    assertOk "ux ud2 A shut rd" (← ops.shutdown ud2A .rd)
    let sent2 ← assertOk "ux ud2 B sendto" (← ops.sendto ud2B (ByteArray.mk #[1, 2, 3, 4, 5]) { nosignal := true })
    if sent2 != 5 then throw (IO.userError s!"ux ud2 B sendto expected 5, got {sent2}")
  finally
    safeClose ud2B
    safeClose ud2A
    safeClose udSrv2
  let ff02Addr : SockAddr := .ipv6 0xff02000000000000 1 8080 0 0
  let tcpMcast ← assertOk "ux tcp mcast sock" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertErr "ux tcp mcast bind EINVAL" (← ops.bind tcpMcast ff02Addr) Errno.EINVAL
  finally
    safeClose tcpMcast

/-- Run live Linux regression checks covering abstract `AF_UNIX`, `SCM_RIGHTS`, UDP peer-filtering, and TCP connect-reset edge cases. -/
def runUnixScmAndConnectResetTests : IO Unit := do
  runUnixScmAndConnectResetPart1
  runUnixScmAndConnectResetPart2
  runUnixScmAndConnectResetPart3
  runUnixScmAndConnectResetPart4
  runUnixScmAndConnectResetPart5
  runUnixScmAndConnectResetPart6
  runUnixScmAndConnectResetPart7

private def runDualStackShutdownAndUnixFsPart1 : IO Unit := do
  let ops := defaultOps
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let absGc := SockAddr.unix (ByteArray.mk #[0, 117, 120, 95, 117, 95, 103, 99])
  let s0 := NetState.initial false
  let s1 := match allowedStep s0 (.socket .unix .stream nbFlags 0) (.opened 0) with
    | some st => st | none => s0
  let s2 := match allowedStep s1 (.bind 0 absGc) .unit with | some st => st | none => s1
  let s3 := match allowedStep s2 (.listen 0 8) .unit with | some st => st | none => s2
  let s4 := match allowedStep s3 (.socket .unix .stream nbFlags 0) (.opened 1) with
    | some st => st | none => s3
  let s5 := match allowedStep s4 (.connect 1 absGc) .unit with | some st => st | none => s4
  let s6 := match allowedStep s5 (.sendmsg 1 #[1, 0]) .unit with | some st => st | none => s5
  let s7 := match s6.closeHandle 0 with | .ok st => st | .error _ => s6
  let s8 := match allowedStep s7 (.shutdown 1 .rdwr) .unit with | some st => st | none => s7
  assertTrue "ux unix gc listener ECONNRESET"
    (allowedStep s8 (.recvfrom 1 64 { dontwait := true }) (.err Errno.ECONNRESET)).isSome
  let blkFlags : SockFlags := { nonblock := false, cloexec := true }
  let selfSock ← assertOk "ds self-shut socket" (← ops.socket .inet .stream blkFlags 0)
  try
    assertOk "ds self-shut bind" (← ops.bind selfSock (.ipv4 0 0))
    let gsn ← assertOk "ds self-shut gsn" (← ops.getsockname selfSock)
    let sport := match gsn with | .ipv4 _ p => p | _ => 0
    assertErr "ds self-shut rd" (← ops.shutdown selfSock .rd) Errno.ENOTCONN
    assertErr "ds self-shut wr" (← ops.shutdown selfSock .wr) Errno.ENOTCONN
    assertErr "ds self-shut connect" (← ops.connect selfSock (.ipv4 INADDR_LOOPBACK sport)) Errno.ECONNABORTED
    assertErr "ds self-shut recv" (← ops.recvfrom selfSock 64 {}) Errno.ENOTCONN
  finally
    safeClose selfSock
  let rstCli ← assertOk "ds shutwr rst cli" (← ops.socket .inet6 .stream blkFlags 0)
  let rstLis ← assertOk "ds shutwr rst lis" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ds shutwr rst listen" (← ops.listen rstLis 4)
    let rlsa ← assertOk "ds shutwr rst gsn" (← ops.getsockname rstLis)
    let rlport := match rlsa with | .ipv4 _ p => p | _ => 0
    assertErr "ds shutwr rst shut0" (← ops.shutdown rstCli .wr) Errno.ENOTCONN
    assertOk "ds shutwr rst conn" (← ops.connect rstCli (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) rlport 0 0))
    assertOk "ds shutwr rst shut1" (← ops.shutdown rstLis .rd)
    assertErr "ds shutwr rst send1" (← ops.sendto rstCli (ByteArray.mk #[1, 2, 3]) { dontwait := true }) Errno.ECONNRESET
    assertErr "ds shutwr rst send2" (← ops.sendto rstCli (ByteArray.mk #[1, 2, 3]) { dontwait := true }) Errno.EPIPE
  finally
    safeClose rstCli
    safeClose rstLis

private def runDualStackShutdownAndUnixFsPart2 : IO Unit := do
  let ops := defaultOps
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let mcastStream ← assertOk "ds mcast stream sock" (← ops.socket .inet .stream {} 0)
  try
    assertOk "ds mcast stream bind" (← ops.bind mcastStream (.ipv4 0xe0000001 0))
    let saPre ← assertOk "ds mcast stream gsn pre" (← ops.getsockname mcastStream)
    let mcastPort := match saPre with | .ipv4 _ p => p | _ => 0
    assertTrue "ds mcast stream pre ip" (saPre == .ipv4 0xe0000001 mcastPort && mcastPort != 0)
    assertErr "ds mcast stream conn" (← ops.connect mcastStream (.ipv4 0x7f000002 1)) Errno.ECONNREFUSED
    let saPost ← assertOk "ds mcast stream gsn post" (← ops.getsockname mcastStream)
    assertTrue "ds mcast stream post ip" (saPost == .ipv4 INADDR_LOOPBACK mcastPort)
  finally
    safeClose mcastStream
  let mcastDgram ← assertOk "ds mcast dgram sock" (← ops.socket .inet .dgram {} 0)
  try
    assertOk "ds mcast dgram bind" (← ops.bind mcastDgram (.ipv4 0xe0000001 0))
    let saPre ← assertOk "ds mcast dgram gsn pre" (← ops.getsockname mcastDgram)
    let mcastPort := match saPre with | .ipv4 _ p => p | _ => 0
    assertOk "ds mcast dgram conn" (← ops.connect mcastDgram (.ipv4 0x7f000002 1))
    let saPost ← assertOk "ds mcast dgram gsn post" (← ops.getsockname mcastDgram)
    assertTrue "ds mcast dgram post ip" (saPost == .ipv4 0xe0000001 mcastPort)
  finally
    safeClose mcastDgram
  let preShutLis ← assertOk "ds pre shut lis sock" (← ops.socket .inet6 .stream nbFlags IPPROTO_TCP)
  let preShutCli ← assertOk "ds pre shut cli sock" (← ops.socket .inet .stream {} 0)
  try
    assertErr "ds pre shut rdwr" (← ops.shutdown preShutLis .rdwr) Errno.ENOTCONN
    assertOk "ds pre shut listen" (← ops.listen preShutLis 16)
    let lsa ← assertOk "ds pre shut gsn" (← ops.getsockname preShutLis)
    let lport := match lsa with | .ipv6 _ _ p _ _ => p | _ => 0
    assertOk "ds pre shut connect" (← ops.connect preShutCli (.ipv4 INADDR_LOOPBACK lport))
    assertOk "ds pre shut lis rd" (← ops.shutdown preShutLis .rd)
    let gotFds ← assertOk "ds pre shut cli recvmsg" (← ops.recvmsg preShutCli 4)
    assertTrue "ds pre shut cli eof" (gotFds.size == 0)
    let soe ← assertOk "ds pre shut cli so_error" (← ops.getsockopt preShutCli .error)
    assertTrue "ds pre shut cli epipe" (soe == Errno.EPIPE)
  finally
    safeClose preShutCli
    safeClose preShutLis
  let (us0, us1) ← assertOk "ds unix pair s" (← ops.socketpair .unix .stream nbFlags)
  let (up0, up1) ← assertOk "ds unix pair p" (← ops.socketpair .unix .stream nbFlags)
  try
    let nSent ← assertOk "ds unix sendto abc" (← ops.sendto us1 (ByteArray.mk #[97, 98, 99]) {})
    assertTrue "ds unix sendto 3" (nSent == 3)
    assertOk "ds unix sendmsg p0" (← ops.sendmsg us1 #[up0])
    let zGot ← assertOk "ds unix recvfrom 0" (← ops.recvfrom us0 0 {})
    assertTrue "ds unix recvfrom 0 empty" (zGot.data.size == 0)
    safeClose up0
    assertErr "ds unix p1 still open" (← ops.recvfrom up1 4 { dontwait := true }) Errno.EAGAIN
    let abc ← assertOk "ds unix recvfrom 3" (← ops.recvfrom us0 3 {})
    assertTrue "ds unix got abc" (abc == ByteArray.mk #[97, 98, 99])
    let rcvFds ← assertOk "ds unix recvmsg p0" (← ops.recvmsg us0 2)
    assertTrue "ds unix got 1 fd" (rcvFds.size == 1)
    for rfd in rcvFds do
      safeClose rfd
  finally
    safeClose us0
    safeClose us1
    safeClose up1

private def runDualStackShutdownAndUnixFsPart3 : IO Unit := do
  let ops := defaultOps
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let raLis ← assertOk "ds reuse snap lis" (← ops.socket .inet6 .stream nbFlags 0)
  let raCli ← assertOk "ds reuse snap cli" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertOk "ds reuse snap listen" (← ops.listen raLis 4)
    let rlsa ← assertOk "ds reuse snap gsn" (← ops.getsockname raLis)
    let rlport := match rlsa with | .ipv6 _ _ p _ _ => p | _ => 0
    assertErr "ds reuse snap conn" (← ops.connect raCli (.ipv6 0 1 rlport 0 0)) Errno.EINPROGRESS
    assertOk "ds reuse snap set" (← ops.setsockopt raLis .reuseAddr 1)
    let (raAcc, _) ← assertOk "ds reuse snap accept" (← ops.accept4 raLis nbFlags)
    try
      let raVal ← assertOk "ds reuse snap get" (← ops.getsockopt raAcc .reuseAddr)
      assertTrue "ds reuse snap 0" (raVal == 0)
    finally
      safeClose raAcc
  finally
    safeClose raCli
    safeClose raLis
  let snFd ← assertOk "ds shutrd nagle sock" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertErr "ds shutrd nagle shut" (← ops.shutdown snFd .rd) Errno.ENOTCONN
    assertOk "ds shutrd nagle bind" (← ops.bind snFd (.ipv6 0 1 0 0 0))
    let snSa ← assertOk "ds shutrd nagle gsn" (← ops.getsockname snFd)
    assertErr "ds shutrd nagle conn" (← ops.connect snFd snSa) Errno.EINPROGRESS
    let _ ← assertOk "ds shutrd nagle tx1" (← ops.sendto snFd (ByteArray.mk #[1, 2, 3, 4, 5, 6]) {})
    let rx1 ← assertOk "ds shutrd nagle rx1" (← ops.recvfrom snFd 16 { dontwait := true })
    assertTrue "ds shutrd nagle rx1 len" (rx1.data.size >= 1)
    let _ ← assertOk "ds shutrd nagle tx2" (← ops.sendto snFd (ByteArray.mk #[32]) {})
    let _ ← assertOk "ds shutrd nagle tx3" (← ops.sendto snFd (ByteArray.mk (Array.replicate 16 (9 : UInt8))) { dontwait := true })
    let fds ← assertOk "ds shutrd nagle recvmsg" (← ops.recvmsg snFd 2)
    assertTrue "ds shutrd nagle recvmsg fds" (fds.size == 0)
    let rx2 ← assertOk "ds shutrd nagle rx2" (← ops.recvfrom snFd 1 {})
    assertTrue "ds shutrd nagle rx2 eof or byte" (rx2.data.size == 0 || rx2.data.size == 1)
  finally
    safeClose snFd
  let mut ms := NetState.initial false
  let snH : HandleId := ms.nextHid
  ms := match allowedStep ms (.socket .inet6 .stream nbFlags 0) (.opened snH) with | some s' => s' | none => ms
  ms := match allowedStep ms (.shutdown snH .rd) (.err Errno.ENOTCONN) with | some s' => s' | none => ms
  ms := match allowedStep ms (.bind snH (.ipv6 0 1 12345 0 0)) .unit with | some s' => s' | none => ms
  ms := match allowedStep ms (.connect snH (.ipv6 0 1 12345 0 0)) (.err Errno.EINPROGRESS) with | some s' => s' | none => ms
  let some msTx := allowedStep ms (.sendto snH (ByteArray.mk (Array.replicate 16 (9 : UInt8))) {}) (.u32 16)
    | throw (IO.userError "ds shutrd nagle model sendto failed")
  assertTrue "ds shutrd nagle model eof"
    (allowedStep msTx (.recvfrom snH 1 {}) (.bytes (ByteArray.mk #[]))).isSome
  let qLis ← assertOk "ds backlog0 lis" (← ops.socket .inet .stream nbFlags 0)
  let qC0 ← assertOk "ds backlog0 c0" (← ops.socket .inet6 .stream nbFlags 0)
  let qC2 ← assertOk "ds backlog0 c2" (← ops.socket .inet6 .stream nbFlags 6)
  try
    assertOk "ds backlog0 listen" (← ops.listen qLis 0)
    let qSa ← assertOk "ds backlog0 gsn" (← ops.getsockname qLis)
    let qPort := match qSa with | .ipv4 _ p => p | _ => 0
    let mappedTarget := SockAddr.ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) qPort 0 0
    assertErr "ds backlog0 conn0" (← ops.connect qC0 mappedTarget) Errno.EINPROGRESS
    assertErr "ds backlog0 conn2" (← ops.connect qC2 mappedTarget) Errno.EINPROGRESS
    let (qA0, _) ← assertOk "ds backlog0 accept0" (← ops.accept4 qLis nbFlags)
    safeClose qA0
    let qSoErr ← assertOk "ds backlog0 soerr" (← ops.getsockopt qC2 .error)
    assertTrue "ds backlog0 soerr 0" (qSoErr == 0)
    assertErr "ds backlog0 recv" (← ops.recvfrom qC2 16 { dontwait := true }) Errno.EAGAIN
    assertErr "ds backlog0 accept1" (← ops.accept4 qLis nbFlags) Errno.EAGAIN
  finally
    safeClose qC2
    safeClose qC0
    safeClose qLis
  let preLis ← assertOk "ds finsent lis" (← ops.socket .inet6 .stream nbFlags 6)
  let preCli ← assertOk "ds finsent cli" (← ops.socket .inet6 .stream nbFlags 0)
  try
    assertOk "ds finsent listen" (← ops.listen preLis 0)
    let pSa ← assertOk "ds finsent gsn" (← ops.getsockname preLis)
    let pPort := match pSa with | .ipv6 _ _ p _ _ => p | _ => 0
    assertErr "ds finsent pre shut" (← ops.shutdown preCli .wr) Errno.ENOTCONN
    assertErr "ds finsent conn" (← ops.connect preCli (.ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) pPort 0 0)) Errno.EINPROGRESS
    let (preAcc, _) ← assertOk "ds finsent accept" (← ops.accept4 preLis nbFlags)
    try
      assertOk "ds finsent acc shut" (← ops.shutdown preAcc .rdwr)
      assertErr "ds finsent bind einval" (← ops.bind preCli (.ipv6 0 1 0 0 0)) Errno.EINVAL
    finally
      safeClose preAcc
  finally
    safeClose preCli
    safeClose preLis

private def runDualStackShutdownAndUnixFsPart4 : IO Unit := do
  let ops := defaultOps
  let bcastUdp ← assertOk "ds bcast udp" (← ops.socket .inet .dgram nbFlags 0)
  try
    assertOk "ds bcast bind" (← ops.bind bcastUdp (.ipv4 0xffffffff 0))
    let bSa ← assertOk "ds bcast gsn" (← ops.getsockname bcastUdp)
    match bSa with
    | .ipv4 ip port =>
      assertTrue "ds bcast gsn ip" (ip == 0xffffffff)
      assertTrue "ds bcast gsn port" (port != 0)
    | _ => throw (IO.userError "ds bcast gsn not ipv4")
  finally
    safeClose bcastUdp
  let nonlocalTcp ← assertOk "ds nonlocal tcp" (← ops.socket .inet .stream nbFlags 0)
  try
    assertErr "ds nonlocal bind" (← ops.bind nonlocalTcp (.ipv4 0xc0000201 0)) Errno.EADDRNOTAVAIL
  finally
    safeClose nonlocalTcp
  let ds6 ← assertOk "ds ds6 sock" (← ops.socket .inet6 .stream nbFlags 0)
  let ds4 ← assertOk "ds ds4 sock" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ds ds6 bind" (← ops.bind ds6 (.ipv6 0 0 0 0 0))
    let ds6Sa ← assertOk "ds ds6 gsn" (← ops.getsockname ds6)
    let ds6Port := match ds6Sa with | .ipv6 _ _ p _ _ => p | _ => 0
    assertErr "ds ds4 conflict" (← ops.bind ds4 (.ipv4 INADDR_LOOPBACK ds6Port)) Errno.EADDRINUSE
  finally
    safeClose ds4
    safeClose ds6

private def runDualStackShutdownAndUnixFsPart5 : IO Unit := do
  let ops := defaultOps
  let preShutLis ← assertOk "ds preshut lis" (← ops.socket .inet .stream nbFlags 0)
  let preShutCli ← assertOk "ds preshut cli" (← ops.socket .inet .stream nbFlags 0)
  try
    assertOk "ds preshut bind" (← ops.bind preShutLis (.ipv4 INADDR_LOOPBACK 0))
    let pSa ← assertOk "ds preshut gsn" (← ops.getsockname preShutLis)
    let pPort := match pSa with | .ipv4 _ p => p | _ => 0
    assertOk "ds preshut listen" (← ops.listen preShutLis 4)
    assertErr "ds preshut conn" (← ops.connect preShutCli (.ipv4 INADDR_LOOPBACK pPort)) Errno.EINPROGRESS
    let (acc, _) ← assertOk "ds preshut accept" (← ops.accept4 preShutLis nbFlags)
    try
      assertOk "ds preshut acc shut rd" (← ops.shutdown acc .rd)
      let rx ← assertOk "ds preshut acc recv" (← ops.recvfrom acc 16 { dontwait := true })
      assertTrue "ds preshut acc rx empty" (rx.data.size == 0)
      assertOk "ds preshut lis shut rd" (← ops.shutdown preShutLis .rd)
      assertErr "ds preshut lis accept einval" (← ops.accept4 preShutLis nbFlags) Errno.EINVAL
    finally
      safeClose acc
  finally
    safeClose preShutCli
    safeClose preShutLis
  withTempSockDir "uxfs" fun basePath => do
    let d1 ← assertOk "ds ud1" (← ops.socket .unix .dgram nbFlags 0)
    let d2 ← assertOk "ds ud2" (← ops.socket .unix .dgram nbFlags 0)
    let d3 ← assertOk "ds ud3" (← ops.socket .unix .dgram nbFlags 0)
    try
      let p1 := basePath ++ ".1".toUTF8
      let p2 := basePath ++ ".2".toUTF8
      let pMissing := basePath ++ ".missing".toUTF8
      assertOk "ds ud1 bind" (← ops.bind d1 (.unix p1))
      assertOk "ds ud2 bind" (← ops.bind d2 (.unix p2))
      assertErr "ds ud1 enoent" (← ops.connect d1 (.unix pMissing)) Errno.ENOENT
      assertOk "ds ud1 conn d2" (← ops.connect d1 (.unix p2))
      assertOk "ds ud2 conn d1" (← ops.connect d2 (.unix p1))
      assertErr "ds ud3 eperm" (← ops.connect d3 (.unix p1)) Errno.EPERM
    finally
      safeClose d3
      safeClose d2
      safeClose d1

private def runDualStackShutdownAndUnixFsTests : IO Unit := do
  runDualStackShutdownAndUnixFsPart1
  runDualStackShutdownAndUnixFsPart2
  runDualStackShutdownAndUnixFsPart3
  runDualStackShutdownAndUnixFsPart4
  runDualStackShutdownAndUnixFsPart5

private def runDefaultWrapperFlagsTests : IO Unit := do
  let sDef ← assertOk "def default socket" (← Net.socket .inet .stream)
  try
    let fl ← assertOk "def default socket fd flags" (← rawNetGetFdFlags sDef)
    assertTrue "def Net.socket default FD_CLOEXEC" ((fl &&& 1) == 1)
  finally
    safeClose sDef
  let (sp0, sp1) ← assertOk "def default socketpair" (← Net.socketpair .unix .stream)
  try
    let fl0 ← assertOk "def sp0 fd flags" (← rawNetGetFdFlags sp0)
    let fl1 ← assertOk "def sp1 fd flags" (← rawNetGetFdFlags sp1)
    assertTrue "def Net.socketpair default FD_CLOEXEC" ((fl0 &&& 1) == 1 && (fl1 &&& 1) == 1)
    assertOk "def close sp1" (← rawNetClose sp1)
    assertErr "def Net.sendto default MSG_NOSIGNAL EPIPE" (← Net.sendto sp0 (asciiBytes ['x'])) Errno.EPIPE
  finally
    safeClose sp0
    safeClose sp1

private def runStickyScopeMappedWildcardAndUntaintTests : IO Unit := do
  let ops := defaultOps
  let v4mPort : UInt16 := 5555
  let v4mLo : SockAddr := .ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) v4mPort 0 0
  let v4mBcast : SockAddr := .ipv6 0 (0x0000ffff00000000 ||| 0x7fffffff) v4mPort 0 0
  let v6Lo : SockAddr := .ipv6 0 1 v4mPort 0 0
  let must (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"sticky-scope model rejected {lbl}: req={repr req} out={repr out}")
  let mut ms1 ← must "untaint sock" (NetState.initial true) (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ms1 ← must "untaint c1 v4mLo" ms1 (.connect 0 v4mLo) (.err Errno.EINPROGRESS)
  ms1 ← must "untaint rst ECONNREFUSED" ms1 (.connect 0 v4mLo) (.err Errno.ECONNREFUSED)
  ms1 ← must "untaint v4mBcast ENETUNREACH" ms1 (.connect 0 v4mBcast) (.err Errno.ENETUNREACH)
  let ms1Conn ← must "untaint ::1 EINPROGRESS" ms1 (.connect 0 v6Lo) (.err Errno.EINPROGRESS)
  assertTrue "untaint model untaint cleared"
    (match lookupFileSocket ms1Conn 0 with
     | .ok sd => match sd.proto with | .tcp .v6 _ _ _ false => true | _ => false
     | .error _ => false)
  let _ ← must "untaint post-untaint send ECONNREFUSED"
    ms1Conn (.sendto 0 (ByteArray.mk #[1]) { dontwait := true, nosignal := true }) (.err Errno.ECONNREFUSED)
  let mut ms2 ← must "netns sock0" (NetState.initialNetns true) (.socket .inet .stream nbFlags 0) (.opened 0)
  ms2 ← must "netns sock1" ms2 (.socket .inet .stream nbFlags 0) (.opened 1)
  ms2 ← must "netns lo-down bind" ms2 (.bind 0 (.ipv4 0x7fffffff 0)) .unit
  ms2 ← must "netns ioctl lo UP" ms2 (.ioctl 1 (.setIfFlags (IFF_UP ||| IFF_LOOPBACK ||| IFF_RUNNING)) loIfname) (.u32 0)
  let _ ← must "netns connect after lo UP" ms2 (.connect 0 (.ipv4 INADDR_LOOPBACK 1)) (.err Errno.EINPROGRESS)
  if ← isLoopbackUp ops then
    let sink ← assertOk "untaint sink" (← ops.socket .inet .dgram nbFlags 0)
    let cli ← assertOk "untaint cli" (← ops.socket .inet6 .stream nbFlags 0)
    try
      assertOk "untaint sink bind" (← ops.bind sink (.ipv4 INADDR_LOOPBACK 0))
      let sinkSa ← assertOk "untaint sink gsn" (← ops.getsockname sink)
      let sinkPort := match sinkSa with | .ipv4 _ p => p | _ => 0
      let v4mAddr : SockAddr := .ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) sinkPort 0 0
      assertErr "untaint taint" (← ops.connect cli v4mAddr) Errno.EINPROGRESS
      IO.sleep 10
      assertErr "untaint rst clear" (← ops.connect cli v4mAddr) Errno.ECONNREFUSED
      assertErr "untaint untaint ENETUNREACH" (← ops.connect cli v4mBcast) Errno.ENETUNREACH
      assertErr "untaint ::1 EINPROGRESS" (← ops.connect cli (.ipv6 0 1 sinkPort 0 0)) Errno.EINPROGRESS
      IO.sleep 10
      assertErr "untaint ::1 ECONNREFUSED" (← ops.sendto cli (ByteArray.mk #[1]) { dontwait := true, nosignal := true }) Errno.ECONNREFUSED
    finally
      safeClose cli
      safeClose sink
    let scTcp ← assertOk "sc scope tcp" (← ops.socket .inet6 .stream nbFlags 0)
    try
      assertErrOneOf "sc ll%999 connect" (← ops.connect scTcp (.ipv6 0xfe80000000000000 1 8080 0 999))
        [Errno.ENETUNREACH, Errno.ENODEV, Errno.EINVAL]
      assertErr "sc bind [::1]:0 after ll%999 ENODEV" (← ops.bind scTcp (.ipv6 0 1 0 0 0)) Errno.ENODEV
      assertErr "sc override ll%1 EADDRNOTAVAIL" (← ops.bind scTcp (.ipv6 0xfe80000000000000 1 0 0 1)) Errno.EADDRNOTAVAIL
      assertOk "sc bind [::1]:0 after ll%1 override" (← ops.bind scTcp (.ipv6 0 1 0 0 0))
    finally
      safeClose scTcp
    let scUdpMc ← assertOk "sc scope udp" (← ops.socket .inet6 .dgram nbFlags 0)
    try
      assertErr "sc udp bind ff02::1%999 ENODEV" (← ops.bind scUdpMc (.ipv6 0xff02000000000000 1 0 0 999)) Errno.ENODEV
      assertErrOneOf "sc udp connect [::1] after ff02%999" (← ops.connect scUdpMc (.ipv6 0 1 5555 0 0))
        [Errno.ENETUNREACH, Errno.ENODEV]
    finally
      safeClose scUdpMc
    let lis6 ← assertOk "sc v6 lis" (← ops.socket .inet6 .stream nbFlags 0)
    let mapCli ← assertOk "sc map cli" (← ops.socket .inet6 .stream { nonblock := false, cloexec := true } 0)
    try
      assertOk "sc v6 lis bind" (← ops.bind lis6 (.ipv6 0 0 0 0 0))
      let lSa ← assertOk "sc v6 lis gsn" (← ops.getsockname lis6)
      let lp := match lSa with | .ipv6 _ _ p _ _ => p | _ => 0
      assertOk "sc v6 lis listen" (← ops.listen lis6 4)
      assertOk "sc map cli bind" (← ops.bind mapCli (.ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) 0 0 0))
      assertOk "sc map cli connect [::]:lp" (← ops.connect mapCli (.ipv6 0 0 lp 0 0))
      let (accFd, _) ← assertOk "sc v6 lis accept4" (← ops.accept4 lis6 nbFlags)
      safeClose accFd
    finally
      safeClose mapCli
      safeClose lis6
    let autoD6 ← assertOk "sc auto d6" (← ops.socket .inet6 .dgram nbFlags 0)
    let rxU4 ← assertOk "sc rx u4" (← ops.socket .inet .dgram nbFlags 0)
    try
      assertOk "sc d6 connect [::1]:9" (← ops.connect autoD6 (.ipv6 0 1 9 0 0))
      let d6Sa ← assertOk "sc d6 gsn" (← ops.getsockname autoD6)
      let d6Port := match d6Sa with | .ipv6 _ _ p _ _ => p | _ => 0
      assertOk "sc u4 bind" (← ops.bind rxU4 (.ipv4 INADDR_LOOPBACK 0))
      let u4Sa ← assertOk "sc u4 gsn" (← ops.getsockname rxU4)
      let u4Port := match u4Sa with | .ipv4 _ p => p | _ => 0
      assertOk "sc u4 connect d6Port" (← ops.connect rxU4 (.ipv4 INADDR_LOOPBACK d6Port))
      assertOk "sc d6 reconnect v4map" (← ops.connect autoD6 (.ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) u4Port 0 0))
      let nSent ← assertOk "sc d6 sendto" (← ops.sendto autoD6 (asciiBytes ['w']) { nosignal := true })
      assertTrue "sc d6 sent 1" (nSent == 1)
      let rxGot ← assertOk "sc u4 recvfrom" (← ops.recvfrom rxU4 8 { dontwait := true })
      assertTrue "sc u4 got w" (rxGot == asciiBytes ['w'])
      assertOk "sc d6 connect v4map port 0" (← ops.connect autoD6 (.ipv6 0 (0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64) 0 0 0))
      assertErr "sc d6 sendto v4map port 0 EINVAL" (← ops.sendto autoD6 (asciiBytes ['x']) { nosignal := true }) Errno.EINVAL
    finally
      safeClose rxU4
      safeClose autoD6

private def findExtIfIndex (ops : NetOps) : IO (Option UInt32) := do
  for idx in [2, 3, 4, 5, 6, 7, 8] do
    let sc := UInt32.ofNat idx
    if let .ok u ← ops.socket .inet6 .dgram nbFlags 0 then
      let okBind ← try
        pure ((← ops.bind u (.ipv6 0xff02000000000000 1 0 0 sc)).isOk)
      finally
        safeClose u
      if okBind then
        return some sc
  return none

private def runMcastScopeAndSynResetTests : IO Unit := do
  let ops := defaultOps
  let must (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"model rejected {lbl}: req={repr req} out={repr out}")
  let unitOut (r : Except Errno Unit) : NetOutcome :=
    match r with | .ok () => .unit | .error e => .err e
  let addrOut (r : Except Errno SockAddr) : NetOutcome :=
    match r with | .ok sa => .addr sa | .error e => .err e
  let u32Out (r : Except Errno UInt32) : NetOutcome :=
    match r with | .ok n => .u32 n | .error e => .err e
  let bytesOut (r : Except Errno ByteArray) : NetOutcome :=
    match r with | .ok b => .bytes b | .error e => .err e
  let v4mLo : UInt64 := 0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64
  if ← isLoopbackUp ops then
    let uTx ← assertOk "mcast uTx" (← ops.socket .inet .dgram nbFlags 0)
    let uRx ← assertOk "mcast uRx" (← ops.socket .inet .dgram nbFlags 0)
    try
      assertOk "mcast uTx bind 224.0.0.1" (← ops.bind uTx (.ipv4 0xe0000001 0))
      let .ipv4 _ txP ← assertOk "mcast uTx gsn" (← ops.getsockname uTx) | throw (IO.userError "mcast txP")
      assertOk "mcast uRx bind lo" (← ops.bind uRx (.ipv4 INADDR_LOOPBACK 0))
      let .ipv4 _ rxP ← assertOk "mcast uRx gsn" (← ops.getsockname uRx) | throw (IO.userError "mcast rxP")
      assertOk "mcast uRx conn" (← ops.connect uRx (.ipv4 INADDR_LOOPBACK txP))
      assertOk "mcast uTx conn" (← ops.connect uTx (.ipv4 INADDR_LOOPBACK rxP))
      let rSend ← ops.sendto uTx (asciiBytes ['m']) { nosignal := true }
      let rRecv ← ops.recvfrom uRx 8 { dontwait := true }
      assertTrue "mcast src delivered" (bytesOut rRecv == .bytes (asciiBytes ['m']))
      let mut ms ← must "mcast.uTx" (NetState.initial false) (.socket .inet .dgram nbFlags 0) (.opened 0)
      ms ← must "mcast.uRx" ms (.socket .inet .dgram nbFlags 0) (.opened 1)
      ms ← must "mcast.bindTx" ms (.bind 0 (.ipv4 0xe0000001 txP)) .unit
      ms ← must "mcast.bindRx" ms (.bind 1 (.ipv4 INADDR_LOOPBACK rxP)) .unit
      ms ← must "mcast.connRx" ms (.connect 1 (.ipv4 INADDR_LOOPBACK txP)) .unit
      ms ← must "mcast.connTx" ms (.connect 0 (.ipv4 INADDR_LOOPBACK rxP)) .unit
      ms ← must "mcast.send" ms (.sendto 0 (asciiBytes ['m']) { nosignal := true }) (u32Out rSend)
      let _ ← must "mcast.recv" ms (.recvfrom 1 8 { dontwait := true }) (bytesOut rRecv)
    finally
      safeClose uRx
      safeClose uTx
    let u6Map ← assertOk "mapped u6Map" (← ops.socket .inet6 .dgram nbFlags 0)
    try
      assertOk "mapped u6Map bind" (← ops.bind u6Map (.ipv6 0 v4mLo 0 0 0))
      let rMc ← ops.connect u6Map (.ipv6 0xff05000000000000 1 8080 0 0)
      assertErr "mapped u6Map ff05 EAFNOSUPPORT" rMc Errno.EAFNOSUPPORT
      let mut ms2 ← must "mapped.u6Map" (NetState.initial false) (.socket .inet6 .dgram nbFlags 0) (.opened 0)
      ms2 ← must "mapped.bind" ms2 (.bind 0 (.ipv6 0 v4mLo 0 0 0)) .unit
      let _ ← must "mapped.conn_ff05" ms2 (.connect 0 (.ipv6 0xff05000000000000 1 8080 0 0)) (unitOut rMc)
    finally
      safeClose u6Map
    let lis6 ← assertOk "untaint lis6" (← ops.socket .inet6 .stream nbFlags 0)
    let c6 ← assertOk "untaint c6" (← ops.socket .inet6 .stream { nonblock := false, cloexec := true } 0)
    try
      assertOk "untaint lis6 bind" (← ops.bind lis6 (.ipv6 0 1 0 0 0))
      let .ipv6 _ _ lp6 _ _ ← assertOk "untaint lis6 gsn" (← ops.getsockname lis6) | throw (IO.userError "untaint lp6")
      assertOk "untaint lis6 listen" (← ops.listen lis6 4)
      let r1 ← ops.connect c6 (.ipv6 0xfe80000000000000 1 8080 0 999)
      let r2 ← ops.connect c6 (.ipv6 0 v4mLo lp6 0 0)
      let r3 ← ops.bind c6 (.ipv6 0xfe80000000000000 1 0 0 1)
      let r4 ← ops.connect c6 (.ipv6 0 1 lp6 0 0)
      assertOk "untaint c6 conn v6lo after enodev" r4
      let (acc, _) ← assertOk "untaint lis6 accept" (← ops.accept4 lis6 nbFlags)
      safeClose acc
      let mut ms3 ← must "untaint.lis6" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
      ms3 ← must "untaint.lis6_bind" ms3 (.bind 0 (.ipv6 0 1 lp6 0 0)) .unit
      ms3 ← must "untaint.lis6_listen" ms3 (.listen 0 4) .unit
      ms3 ← must "untaint.c6" ms3 (.socket .inet6 .stream { nonblock := false, cloexec := true } 0) (.opened 1)
      ms3 ← must "untaint.ll999" ms3 (.connect 1 (.ipv6 0xfe80000000000000 1 8080 0 999)) (unitOut r1)
      ms3 ← must "untaint.v4m_enodev" ms3 (.connect 1 (.ipv6 0 v4mLo lp6 0 0)) (unitOut r2)
      ms3 ← must "untaint.bind_ll1" ms3 (.bind 1 (.ipv6 0xfe80000000000000 1 0 0 1)) (unitOut r3)
      let _ ← must "untaint.conn_v6lo" ms3 (.connect 1 (.ipv6 0 1 lp6 0 0)) (unitOut r4)
    finally
      safeClose c6
      safeClose lis6
  if let some extIdx ← findExtIfIndex ops then
    let uExt ← assertOk "ext uExt" (← ops.socket .inet6 .dgram nbFlags 0)
    let tExt ← assertOk "ext tExt" (← ops.socket .inet6 .stream nbFlags 0)
    try
      let rUc ← ops.connect uExt (.ipv6 0xfe80000000000000 1 8080 0 extIdx)
      let rUgsn ← ops.getsockname uExt
      let rUsend ← ops.sendto uExt (asciiBytes ['h', 'i']) { nosignal := true }
      let mut ms4 ← must "ext.uExt" (NetState.initial false) (.socket .inet6 .dgram nbFlags 0) (.opened 0)
      ms4 ← must "ext.conn" ms4 (.connect 0 (.ipv6 0xfe80000000000000 1 8080 0 extIdx)) (unitOut rUc)
      ms4 ← must "ext.gsn" ms4 (.getsockname 0) (addrOut rUgsn)
      let _ ← must "ext.send" ms4 (.sendto 0 (asciiBytes ['h', 'i']) { nosignal := true }) (u32Out rUsend)
      let rTc ← ops.connect tExt (.ipv6 0xfe80000000000000 1 80 0 extIdx)
      let rTg1 ← ops.getsockname tExt
      let rTsh ← ops.shutdown tExt .rdwr
      let rTg2 ← ops.getsockname tExt
      let mut ms5 ← must "ext.tExt" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
      ms5 ← must "ext.tconn" ms5 (.connect 0 (.ipv6 0xfe80000000000000 1 80 0 extIdx)) (unitOut rTc)
      ms5 ← must "ext.tgsn1" ms5 (.getsockname 0) (addrOut rTg1)
      ms5 ← must "ext.tshut" ms5 (.shutdown 0 .rdwr) (unitOut rTsh)
      let _ ← must "ext.tgsn2" ms5 (.getsockname 0) (addrOut rTg2)
    finally
      safeClose tExt
      safeClose uExt
  let t4 ← assertOk "synrst t4" (← ops.socket .inet .stream nbFlags 0)
  try
    let rc4 ← ops.connect t4 (.ipv4 0xc0000201 80)
    if unitOut rc4 == .err Errno.EINPROGRESS then
      let rg1 ← ops.getsockname t4
      let rsh ← ops.shutdown t4 .rdwr
      let rg2 ← ops.getsockname t4
      let rse1 ← ops.getsockopt t4 .error
      let rse2 ← ops.getsockopt t4 .error
      let mut msR ← must "synrst.t4" (NetState.initial false) (.socket .inet .stream nbFlags 0) (.opened 0)
      msR ← must "synrst.conn" msR (.connect 0 (.ipv4 0xc0000201 80)) (unitOut rc4)
      msR ← must "synrst.gsn1" msR (.getsockname 0) (addrOut rg1)
      msR ← must "synrst.shut" msR (.shutdown 0 .rdwr) (unitOut rsh)
      msR ← must "synrst.gsn2" msR (.getsockname 0) (addrOut rg2)
      msR ← must "synrst.soerr1" msR (.getsockopt 0 .error) (u32Out rse1)
      let _ ← must "synrst.soerr2" msR (.getsockopt 0 .error) (u32Out rse2)
  finally
    safeClose t4

private def findExtSelfLinkLocal (ops : NetOps) : IO (Option (UInt32 × UInt64 × UInt64)) := do
  for idx in [2, 3, 4, 5, 6, 7, 8] do
    let sc := UInt32.ofNat idx
    if let .ok u ← ops.socket .inet6 .dgram nbFlags 0 then
      let res? ← try
        if (← ops.connect u (.ipv6 0xfe80000000000000 1 8080 0 sc)).isOk then
          match ← ops.getsockname u with
          | .ok (.ipv6 hi lo _ _ _) =>
            if (hi &&& 0xffc0000000000000) == 0xfe80000000000000 then pure (some (sc, hi, lo))
            else pure none
          | _ => pure none
        else pure none
      finally
        safeClose u
      if res?.isSome then
        return res?
  return none

private def runTaintedAbortLastAckAndMcastRoutedTests : IO Unit := do
  let ops := defaultOps
  let must (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"model rejected {lbl}: req={repr req} out={repr out}")
  let unitOut (r : Except Errno Unit) : NetOutcome :=
    match r with | .ok () => .unit | .error e => .err e
  let addrOut (r : Except Errno SockAddr) : NetOutcome :=
    match r with | .ok sa => .addr sa | .error e => .err e
  let u32Out (r : Except Errno UInt32) : NetOutcome :=
    match r with | .ok n => .u32 n | .error e => .err e
  let bytesOut (r : Except Errno ByteArray) : NetOutcome :=
    match r with | .ok b => .bytes b | .error e => .err e
  let v4mLo : UInt64 := 0x0000ffff00000000 ||| INADDR_LOOPBACK.toUInt64
  if ← isLoopbackUp ops then
    let dead4 ← assertOk "taint dead4" (← ops.socket .inet .stream nbFlags 0)
    assertOk "taint dead4 bind" (← ops.bind dead4 (.ipv4 INADDR_LOOPBACK 0))
    let .ipv4 _ deadP4 ← assertOk "taint dead4 gsn" (← ops.getsockname dead4) | throw (IO.userError "deadP4")
    safeClose dead4

    let l6a ← assertOk "taint l6a" (← ops.socket .inet6 .stream nbFlags 0)
    let c6a ← assertOk "taint c6a" (← ops.socket .inet6 .stream nbFlags 0)
    try
      let rt1 ← ops.connect l6a (.ipv6 0 v4mLo deadP4 0 0)
      let rt2 ← ops.connect l6a (.ipv6 0 v4mLo deadP4 0 0)
      assertOk "taint l6a listen" (← ops.listen l6a 4)
      let .ipv6 _ _ lpa _ _ ← assertOk "taint l6a gsn" (← ops.getsockname l6a) | throw (IO.userError "lpa")
      let rc1 ← ops.connect c6a (.ipv6 0 1 lpa 0 0)
      assertOk "taint close l6a" (← rawNetClose l6a)
      let rErr ← ops.getsockopt c6a .error
      let rConn2 ← ops.connect c6a (.ipv6 0 1 lpa 0 0)
      let rSend1 ← ops.sendto c6a (asciiBytes ['h', 'i']) { nosignal := true }
      let rSend2 ← ops.sendto c6a (asciiBytes ['h', 'i']) { nosignal := true }
      let mut msA ← must "taintA.l6" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
      msA ← must "taintA.t1" msA (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt1)
      msA ← must "taintA.t2" msA (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt2)
      msA ← must "taintA.lis" msA (.listen 0 4) .unit
      msA ← must "taintA.gsn" msA (.getsockname 0) (.addr (.ipv6 0 0 lpa 0 0))
      msA ← must "taintA.c6" msA (.socket .inet6 .stream nbFlags 0) (.opened 1)
      msA ← must "taintA.c1" msA (.connect 1 (.ipv6 0 1 lpa 0 0)) (unitOut rc1)
      let msCl ← assertOk "taintA.close_l6" (NetState.closeHandle msA 0)
      msA ← must "taintA.err0" msCl (.getsockopt 1 .error) (u32Out rErr)
      msA ← must "taintA.c2" msA (.connect 1 (.ipv6 0 1 lpa 0 0)) (unitOut rConn2)
      msA ← must "taintA.tx1" msA (.sendto 1 (asciiBytes ['h', 'i']) { nosignal := true }) (u32Out rSend1)
      let _ ← must "taintA.tx2_rst" msA (.sendto 1 (asciiBytes ['h', 'i']) { nosignal := true }) (u32Out rSend2)
    finally
      safeClose c6a
      safeClose l6a

    let l6b ← assertOk "taint l6b" (← ops.socket .inet6 .stream nbFlags 0)
    let c6b ← assertOk "taint c6b" (← ops.socket .inet6 .stream nbFlags 0)
    let c6c ← assertOk "taint c6c" (← ops.socket .inet6 .stream nbFlags 0)
    try
      let rt1 ← ops.connect l6b (.ipv6 0 v4mLo deadP4 0 0)
      let rt2 ← ops.connect l6b (.ipv6 0 v4mLo deadP4 0 0)
      assertOk "taint l6b listen" (← ops.listen l6b 4)
      let .ipv6 _ _ lpb _ _ ← assertOk "taint l6b gsn" (← ops.getsockname l6b) | throw (IO.userError "lpb")
      let rcB ← ops.connect c6b (.ipv6 0 1 lpb 0 0)
      let cSaB ← assertOk "taint c6b gsn" (← ops.getsockname c6b)
      let _ ← ops.sendto c6b (asciiBytes ['a', 'b']) { nosignal := true }
      assertOk "taint close c6b" (← rawNetClose c6b)
      let (s6b, peerB) ← assertOk "taint s6b acc" (← ops.accept4 l6b nbFlags)
      try
        let rRx1 ← ops.recvfrom s6b 16 {}
        let rRx2 ← ops.recvfrom s6b 16 {}
        let rTx1 ← ops.sendto s6b (asciiBytes ['r']) { nosignal := true }
        let rSerr ← ops.getsockopt s6b .error
        let rTx2 ← ops.sendto s6b (asciiBytes ['q']) { nosignal := true }
        let rSwr ← ops.shutdown s6b .wr
        let rSrd ← ops.shutdown s6b .rd
        let rSbind ← ops.bind s6b (.ipv6 0 1 0 0 0)
        let mut msB ← must "taintB.l6" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
        msB ← must "taintB.t1" msB (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt1)
        msB ← must "taintB.t2" msB (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt2)
        msB ← must "taintB.lis" msB (.listen 0 4) .unit
        msB ← must "taintB.gsn" msB (.getsockname 0) (.addr (.ipv6 0 0 lpb 0 0))
        msB ← must "taintB.c6" msB (.socket .inet6 .stream nbFlags 0) (.opened 1)
        msB ← must "taintB.conn" msB (.connect 1 (.ipv6 0 1 lpb 0 0)) (unitOut rcB)
        msB ← must "taintB.cgsn" msB (.getsockname 1) (.addr cSaB)
        msB ← must "taintB.csend" msB (.sendto 1 (asciiBytes ['a', 'b']) { nosignal := true }) (.u32 2)
        let msCcl ← assertOk "taintB.close_c6" (NetState.closeHandle msB 1)
        msB ← must "taintB.acc" msCcl (.accept4 0 nbFlags) (.accepted 2 peerB)
        msB ← must "taintB.rx1" msB (.recvfrom 2 16 {}) (bytesOut rRx1)
        msB ← must "taintB.rx2" msB (.recvfrom 2 16 {}) (bytesOut rRx2)
        msB ← must "taintB.tx1" msB (.sendto 2 (asciiBytes ['r']) { nosignal := true }) (u32Out rTx1)
        msB ← must "taintB.err0" msB (.getsockopt 2 .error) (u32Out rSerr)
        msB ← must "taintB.tx2" msB (.sendto 2 (asciiBytes ['q']) { nosignal := true }) (u32Out rTx2)
        msB ← must "taintB.shut_wr" msB (.shutdown 2 .wr) (unitOut rSwr)
        msB ← must "taintB.shut_rd" msB (.shutdown 2 .rd) (unitOut rSrd)
        let _ ← must "taintB.bind_einval" msB (.bind 2 (.ipv6 0 1 0 0 0)) (unitOut rSbind)
      finally
        safeClose s6b

      let rcC ← ops.connect c6c (.ipv6 0 1 lpb 0 0)
      let (s6c, peerC) ← assertOk "taint s6c acc" (← ops.accept4 l6b nbFlags)
      try
        let _ ← ops.connect c6c (.ipv6 0 1 lpb 0 0)
        let rSrdwr ← ops.shutdown s6c .rdwr
        let rCwr ← ops.shutdown c6c .wr
        let rCerr ← ops.getsockopt c6c .error
        let rSrd2 ← ops.shutdown s6c .rd
        let mut msC ← must "taintC.l6" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
        msC ← must "taintC.t1" msC (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt1)
        msC ← must "taintC.t2" msC (.connect 0 (.ipv6 0 v4mLo deadP4 0 0)) (unitOut rt2)
        msC ← must "taintC.lis" msC (.listen 0 4) .unit
        msC ← must "taintC.gsn" msC (.getsockname 0) (.addr (.ipv6 0 0 lpb 0 0))
        msC ← must "taintC.c6" msC (.socket .inet6 .stream nbFlags 0) (.opened 1)
        msC ← must "taintC.conn1" msC (.connect 1 (.ipv6 0 1 lpb 0 0)) (unitOut rcC)
        msC ← must "taintC.acc" msC (.accept4 0 nbFlags) (.accepted 2 peerC)
        msC ← must "taintC.conn2" msC (.connect 1 (.ipv6 0 1 lpb 0 0)) .unit
        msC ← must "taintC.s6_rdwr" msC (.shutdown 2 .rdwr) (unitOut rSrdwr)
        msC ← must "taintC.c6_wr" msC (.shutdown 1 .wr) (unitOut rCwr)
        msC ← must "taintC.c6_err0" msC (.getsockopt 1 .error) (u32Out rCerr)
        let _ ← must "taintC.s6_rd" msC (.shutdown 2 .rd) (unitOut rSrd2)
      finally
        safeClose s6c
    finally
      safeClose c6c
      safeClose c6b
      safeClose l6b

    if let some (extIdx, selfHi, selfLo) ← findExtSelfLinkLocal ops then
      let dead6 ← assertOk "ext dead6" (← ops.socket .inet6 .stream nbFlags 0)
      assertOk "ext dead6 bind" (← ops.bind dead6 (.ipv6 0 1 0 0 0))
      let .ipv6 _ _ deadP6 _ _ ← assertOk "ext dead6 gsn" (← ops.getsockname dead6) | throw (IO.userError "deadP6")
      safeClose dead6
      let cLl ← assertOk "ext cLl" (← ops.socket .inet6 .stream nbFlags 0)
      try
        let rCe ← ops.connect cLl (.ipv6 selfHi selfLo deadP6 0 extIdx)
        let rBe ← ops.bind cLl (.ipv6 selfHi selfLo 0 0 extIdx)
        let mut msLl ← must "extLl.sock" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
        msLl ← must "extLl.conn" msLl (.connect 0 (.ipv6 selfHi selfLo deadP6 0 extIdx)) (unitOut rCe)
        let _ ← must "extLl.bind" msLl (.bind 0 (.ipv6 selfHi selfLo 0 0 extIdx)) (unitOut rBe)
      finally
        safeClose cLl

    let l4 ← assertOk "mcrt l4" (← ops.socket .inet .stream nbFlags 0)
    let m4 ← assertOk "mcrt m4" (← ops.socket .inet .stream nbFlags 0)
    try
      assertOk "mcrt l4 bind" (← ops.bind l4 (.ipv4 INADDR_LOOPBACK 0))
      let .ipv4 _ lp4 ← assertOk "mcrt l4 gsn" (← ops.getsockname l4) | throw (IO.userError "lp4")
      assertOk "mcrt l4 listen" (← ops.listen l4 4)
      assertOk "mcrt m4 bind" (← ops.bind m4 (.ipv4 0xe0000001 0))
      let rg0 ← ops.getsockname m4
      let rcExt ← ops.connect m4 (.ipv4 0xc0000201 80)
      if unitOut rcExt == .err Errno.EINPROGRESS then
        let rSh ← ops.shutdown m4 .rdwr
        let rcLo ← ops.connect m4 (.ipv4 INADDR_LOOPBACK lp4)
        let (acc4, gotPeer4) ← assertOk "mcrt l4 acc" (← ops.accept4 l4 nbFlags)
        safeClose acc4
        let rg3 ← ops.getsockname m4
        let mut msM ← must "mcrt.l4" (NetState.initial false) (.socket .inet .stream nbFlags 0) (.opened 0)
        msM ← must "mcrt.bind_l4" msM (.bind 0 (.ipv4 INADDR_LOOPBACK lp4)) .unit
        msM ← must "mcrt.lis_l4" msM (.listen 0 4) .unit
        msM ← must "mcrt.m4" msM (.socket .inet .stream nbFlags 0) (.opened 1)
        msM ← must "mcrt.bind_m4" msM (.bind 1 (.ipv4 0xe0000001 0)) .unit
        msM ← must "mcrt.gsn0" msM (.getsockname 1) (addrOut rg0)
        msM ← must "mcrt.conn_ext" msM (.connect 1 (.ipv4 0xc0000201 80)) (unitOut rcExt)
        msM ← must "mcrt.shut" msM (.shutdown 1 .rdwr) (unitOut rSh)
        msM ← must "mcrt.conn_lo" msM (.connect 1 (.ipv4 INADDR_LOOPBACK lp4)) (unitOut rcLo)
        msM ← must "mcrt.acc" msM (.accept4 0 nbFlags) (.accepted 2 gotPeer4)
        let _ ← must "mcrt.gsn3" msM (.getsockname 1) (addrOut rg3)
    finally
      safeClose m4
      safeClose l4

    let blkFlags : SockFlags := { nonblock := false, cloexec := true }
    let v4m0 (p : UInt16) : SockAddr := .ipv6 0 0x0000ffff00000000 p 0 0
    let v4mLo (p : UInt16) : SockAddr := .ipv6 0 0x0000ffff7f000001 p 0 0
    let v4mExt (p : UInt16) : SockAddr := .ipv6 0 0x0000ffffc0000201 p 0 0
    let sBlk6 ← assertOk "v4m0 blk6" (← ops.socket .inet6 .stream blkFlags 0)
    try
      assertOk "v4m0 blk6 bind" (← ops.bind sBlk6 (v4m0 0))
      let gBlk0 ← ops.getsockname sBlk6
      let rcBlk ← ops.connect sBlk6 (v4mLo 1)
      let gBlk1 ← ops.getsockname sBlk6
      let mut msBlk ← must "v4m0Blk.sock" (NetState.initial false) (.socket .inet6 .stream blkFlags 0) (.opened 0)
      msBlk ← must "v4m0Blk.bind" msBlk (.bind 0 (v4m0 0)) .unit
      msBlk ← must "v4m0Blk.gsn0" msBlk (.getsockname 0) (addrOut gBlk0)
      msBlk ← must "v4m0Blk.conn" msBlk (.connect 0 (v4mLo 1)) (unitOut rcBlk)
      let _ ← must "v4m0Blk.gsn1" msBlk (.getsockname 0) (addrOut gBlk1)
    finally
      safeClose sBlk6

    let u6 ← assertOk "v4m0 u6" (← ops.socket .inet6 .dgram nbFlags 0)
    let l6 ← assertOk "v4m0 l6" (← ops.socket .inet6 .stream nbFlags 0)
    let t6 ← assertOk "v4m0 t6" (← ops.socket .inet6 .stream nbFlags 0)
    try
      assertOk "v4m0 u6 bind" (← ops.bind u6 (v4m0 0))
      let gu0 ← ops.getsockname u6
      let rcuExt ← ops.connect u6 (v4mExt 9)
      if unitOut rcuExt == .unit then
        let gu1 ← ops.getsockname u6
        let mut msU6 ← must "v4m0U6.sock" (NetState.initial false) (.socket .inet6 .dgram nbFlags 0) (.opened 0)
        msU6 ← must "v4m0U6.bind" msU6 (.bind 0 (v4m0 0)) .unit
        msU6 ← must "v4m0U6.gsn0" msU6 (.getsockname 0) (addrOut gu0)
        msU6 ← must "v4m0U6.conn" msU6 (.connect 0 (v4mExt 9)) .unit
        let _ ← must "v4m0U6.gsn1" msU6 (.getsockname 0) (addrOut gu1)
      assertOk "v4m0 l6 bind" (← ops.bind l6 (.ipv6 0 0 0 0 0))
      let .ipv6 _ _ lp6 _ _ ← assertOk "v4m0 l6 gsn" (← ops.getsockname l6) | throw (IO.userError "lp6")
      assertOk "v4m0 l6 listen" (← ops.listen l6 4)
      assertOk "v4m0 t6 bind" (← ops.bind t6 (v4m0 0))
      let rctExt ← ops.connect t6 (v4mExt 80)
      if unitOut rctExt == .err Errno.EINPROGRESS then
        let rSh6 ← ops.shutdown t6 .rdwr
        let rctLo ← ops.connect t6 (v4mLo lp6)
        IO.sleep 3
        let (acc6, gotPeer6) ← assertOk "v4m0 l6 acc" (← ops.accept4 l6 nbFlags)
        safeClose acc6
        let gt3 ← ops.getsockname t6
        let mut msT6 ← must "v4m0T6.l6" (NetState.initial false) (.socket .inet6 .stream nbFlags 0) (.opened 0)
        msT6 ← must "v4m0T6.bind_l6" msT6 (.bind 0 (.ipv6 0 0 lp6 0 0)) .unit
        msT6 ← must "v4m0T6.lis_l6" msT6 (.listen 0 4) .unit
        msT6 ← must "v4m0T6.t6" msT6 (.socket .inet6 .stream nbFlags 0) (.opened 1)
        msT6 ← must "v4m0T6.bind_t6" msT6 (.bind 1 (v4m0 0)) .unit
        msT6 ← must "v4m0T6.conn_ext" msT6 (.connect 1 (v4mExt 80)) (unitOut rctExt)
        msT6 ← must "v4m0T6.shut" msT6 (.shutdown 1 .rdwr) (unitOut rSh6)
        msT6 ← must "v4m0T6.conn_lo" msT6 (.connect 1 (v4mLo lp6)) (unitOut rctLo)
        msT6 ← must "v4m0T6.acc" msT6 (.accept4 0 nbFlags) (.accepted 2 gotPeer6)
        let _ ← must "v4m0T6.gsn3" msT6 (.getsockname 1) (addrOut gt3)
    finally
      safeClose t6
      safeClose l6
      safeClose u6

    let (stNs, _) ← SandboxEnv.runForked do
      if (← SandboxEnv.enterUserns).isOk && (← SandboxEnv.unshareExtra 2).isOk then
        let ctl ← assertOk "ns ctl" (← ops.socket .inet .dgram nbFlags 0)
        let cNs ← assertOk "ns c" (← ops.socket .inet .stream nbFlags 0)
        let uTxNs ← assertOk "ns uTx" (← ops.socket .inet .dgram nbFlags 0)
        try
          assertOk "ns c bind" (← ops.bind cNs (.ipv4 0x7f000002 0))
          let gc0 ← ops.getsockname cNs
          assertOk "ns uTx bind" (← ops.bind uTxNs (.ipv4 0x7f000002 0))
          let guTx ← assertOk "ns uTx gsn" (← ops.getsockname uTxNs)
          let .ipv4 _ uTxPort := guTx | throw (IO.userError "uTxPort")
          let _ ← assertOk "ns lo up" (← ops.ioctl ctl (.setIfFlags defaultLoFlags) loIfname)
          let lNs ← assertOk "ns l" (← ops.socket .inet .stream nbFlags 0)
          let uRxNs ← assertOk "ns uRx" (← ops.socket .inet .dgram nbFlags 0)
          try
            assertOk "ns l bind" (← ops.bind lNs (.ipv4 0 0))
            assertOk "ns l listen" (← ops.listen lNs 4)
            let .ipv4 _ lpNs ← assertOk "ns l gsn" (← ops.getsockname lNs) | throw (IO.userError "lpNs")
            let rcNs ← ops.connect cNs (.ipv4 INADDR_LOOPBACK lpNs)
            IO.sleep 2
            let gc1 ← ops.getsockname cNs
            let (accNs, peerNs) ← assertOk "ns acc" (← ops.accept4 lNs nbFlags)
            safeClose accNs
            assertOk "ns uRx bind" (← ops.bind uRxNs (.ipv4 INADDR_LOOPBACK 0))
            let .ipv4 _ uRxPort ← assertOk "ns uRx gsn" (← ops.getsockname uRxNs) | throw (IO.userError "uRxPort")
            assertOk "ns uRx conn" (← ops.connect uRxNs (.ipv4 INADDR_LOOPBACK uTxPort))
            assertOk "ns uTx conn" (← ops.connect uTxNs (.ipv4 INADDR_LOOPBACK uRxPort))
            let rSentNs ← ops.sendto uTxNs (asciiBytes ['z']) {}
            IO.sleep 1
            let rRecvNs ← ops.recvfrom uRxNs 8 {}
            let mut msNs ← must "ns.ctl" (NetState.initialNetns true) (.socket .inet .dgram nbFlags 0) (.opened 0)
            msNs ← must "ns.c" msNs (.socket .inet .stream nbFlags 0) (.opened 1)
            msNs ← must "ns.c_bind" msNs (.bind 1 (.ipv4 0x7f000002 0)) .unit
            msNs ← must "ns.c_gsn0" msNs (.getsockname 1) (addrOut gc0)
            msNs ← must "ns.uTx" msNs (.socket .inet .dgram nbFlags 0) (.opened 2)
            msNs ← must "ns.uTx_bind" msNs (.bind 2 (.ipv4 0x7f000002 0)) .unit
            msNs ← must "ns.uTx_gsn" msNs (.getsockname 2) (.addr guTx)
            msNs ← must "ns.lo_up" msNs (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
            msNs ← must "ns.l" msNs (.socket .inet .stream nbFlags 0) (.opened 3)
            msNs ← must "ns.l_bind" msNs (.bind 3 (.ipv4 0 0)) .unit
            msNs ← must "ns.l_lis" msNs (.listen 3 4) .unit
            msNs ← must "ns.l_gsn" msNs (.getsockname 3) (.addr (.ipv4 0 lpNs))
            msNs ← must "ns.c_conn" msNs (.connect 1 (.ipv4 INADDR_LOOPBACK lpNs)) (unitOut rcNs)
            msNs ← must "ns.c_gsn1" msNs (.getsockname 1) (addrOut gc1)
            msNs ← must "ns.acc" msNs (.accept4 3 nbFlags) (.accepted 4 peerNs)
            msNs ← must "ns.uRx" msNs (.socket .inet .dgram nbFlags 0) (.opened 5)
            msNs ← must "ns.uRx_bind" msNs (.bind 5 (.ipv4 INADDR_LOOPBACK 0)) .unit
            msNs ← must "ns.uRx_gsn" msNs (.getsockname 5) (.addr (.ipv4 INADDR_LOOPBACK uRxPort))
            msNs ← must "ns.uRx_conn" msNs (.connect 5 (.ipv4 INADDR_LOOPBACK uTxPort)) .unit
            msNs ← must "ns.uTx_conn" msNs (.connect 2 (.ipv4 INADDR_LOOPBACK uRxPort)) .unit
            msNs ← must "ns.uTx_send" msNs (.sendto 2 (asciiBytes ['z']) {}) (u32Out rSentNs)
            let _ ← must "ns.uRx_recv" msNs (.recvfrom 5 8 {}) (bytesOut rRecvNs)
          finally
            safeClose uRxNs
            safeClose lNs
        finally
          safeClose uTxNs
          safeClose cNs
          safeClose ctl
      return ByteArray.empty
    assertTrue "forked netns parity child status" (stNs == 0)

    let mut unboxed64m := ByteArray.mk #[65, 66, 67, 68]
    for _ in [:24] do
      unboxed64m := unboxed64m ++ unboxed64m
    let mut msUnbox ← must "unbox.dgram" (NetState.initial false) (.socket .inet .dgram nbFlags 0) (.opened 0)
    msUnbox ← must "unbox.sendto64m" msUnbox (.sendto 0 unboxed64m {}) (.err Errno.EMSGSIZE)
    assertTrue "unbox.unixGsn64m rejected without boxing"
      ((Net.allowedStep msUnbox (.getsockname 0) (.addr (.unix unboxed64m))).isNone)

@[noinline] private def allocStreamReadDroppingWrite : IO RawFd := do
  let (s0, _s1) ← assertOk "finalizer socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
  return s0

private def checkNetErrorKindTable : IO Unit := do
  let pairs : Array (Errno × NetErrorKind) :=
    #[ (Errno.EBADF, .badFd), (Errno.ENOTSOCK, .badFd), (Errno.ENOTTY, .badFd)
     , (Errno.EINVAL, .invalidArg), (Errno.EAFNOSUPPORT, .invalidArg)
     , (Errno.EPROTONOSUPPORT, .invalidArg), (Errno.ESOCKTNOSUPPORT, .invalidArg)
     , (Errno.EOPNOTSUPP, .invalidArg), (Errno.EPFNOSUPPORT, .invalidArg)
     , (Errno.ENOPROTOOPT, .invalidArg), (Errno.EPROTOTYPE, .invalidArg)
     , (Errno.EDESTADDRREQ, .invalidArg), (Errno.EMSGSIZE, .invalidArg), (Errno.ENOSYS, .invalidArg)
     , (Errno.EADDRINUSE, .addressError), (Errno.EADDRNOTAVAIL, .addressError)
     , (Errno.ENOENT, .addressError), (Errno.ENODEV, .addressError)
     , (Errno.EAGAIN, .wouldBlockOrInProgress), (Errno.EINPROGRESS, .wouldBlockOrInProgress)
     , (Errno.EALREADY, .wouldBlockOrInProgress)
     , (Errno.EISCONN, .connectionState), (Errno.ENOTCONN, .connectionState)
     , (Errno.EPIPE, .connectionState), (Errno.ECONNRESET, .connectionState)
     , (Errno.ECONNREFUSED, .connectionState), (Errno.ECONNABORTED, .connectionState)
     , (Errno.ESHUTDOWN, .connectionState), (Errno.ETIMEDOUT, .connectionState)
     , (Errno.ENETDOWN, .connectionState), (Errno.ENETUNREACH, .connectionState)
     , (Errno.EHOSTUNREACH, .connectionState), (Errno.EPROTO, .connectionState)
     , (Errno.EACCES, .permissionDenied), (Errno.EPERM, .permissionDenied)
     , (Errno.ENOMEM, .transientOrResource), (Errno.ENFILE, .transientOrResource)
     , (Errno.EMFILE, .transientOrResource), (Errno.EBUSY, .transientOrResource) ]
  for (code, wantKind) in pairs do
    assertTrue s!"NetErrorKind.ofErrno {code}" (NetErrorKind.ofErrno code == wantKind)

@[noinline] private def allocStreamReadDroppingWriteFd0 : IO RawFd := do
  let (s0, s1) ← assertOk "finalizer fd0 socketpair" (← defaultOps.socketpair .unix .stream nbFlags)
  let rawS0 ← SandboxEnv.peekRawFd s0
  assertTrue "finalizer socketpair write end landed on raw fd 0" (rawS0 == 0)
  return s1

private def runShimAndFdBoxEdgeTests : IO Unit := do
  let ops := defaultOps
  checkNetErrorKindTable

  let finRx ← allocStreamReadDroppingWrite
  try
    let eofBs ← assertOk "finalizer stream eof" (← ops.recvfrom finRx 8 { dontwait := true })
    assertTrue "finalizer closed peer fd" (eofBs.size == 0)
  finally
    safeClose finRx

  let mut sawBusy := false
  for _ in [0 : 8] do
    if !sawBusy then
      let (busy0, busy1) ← assertOk "busy socketpair"
        (← ops.socketpair .unix .stream { nonblock := false, cloexec := true })
      let entered ← IO.mkRef false
      let reader ← IO.asTask (prio := .dedicated) do
        entered.set true
        ops.recvfrom busy0 8 {}
      while !(← entered.get) do
        IO.sleep 1
      IO.sleep 5
      match ← rawNetClose busy0 with
      | .error e =>
        if e == Errno.EBUSY then
          sawBusy := true
      | .ok () => pure ()
      let _ ← ops.sendto busy1 (ByteArray.mk #[0x55]) { nosignal := true }
      let _ ← IO.wait reader
      safeClose busy0
      safeClose busy1
  assertTrue "concurrent rawNetClose observed EBUSY" sawBusy

  let abaOld ← assertOk "aba old socket" (← ops.socket .inet .dgram nbFlags 0)
  assertOk "close aba old" (← rawNetClose abaOld)
  assertErr "double close aba old EBADF" (← rawNetClose abaOld) Errno.EBADF
  let abaNew ← assertOk "aba new socket" (← ops.socket .inet .dgram nbFlags 0)
  let (uxScm0, uxScm1) ← assertOk "scm unpin ux pair" (← ops.socketpair .unix .stream nbFlags)
  try
    assertErr "getsockname on closed abaOld after fd reuse EBADF" (← ops.getsockname abaOld) Errno.EBADF
    assertErr "sendmsg tcp with closed scm fd EBADF" (← ops.sendmsg abaNew #[abaOld]) Errno.EBADF
    assertErr "sendmsg unix partial scm pin EBADF" (← ops.sendmsg uxScm0 #[uxScm1, abaOld]) Errno.EBADF
    assertErr "sendmsg udp nonunix domain EOPNOTSUPP" (← ops.sendmsg abaNew #[uxScm1]) Errno.EOPNOTSUPP
  catch e =>
    safeClose uxScm1
    safeClose uxScm0
    safeClose abaNew
    throw e
  assertOk "close uxScm0 after bad scm sendmsg" (← rawNetClose uxScm0)
  assertOk "close abaNew after nonunix sendmsg" (← rawNetClose abaNew)
  assertOk "close uxScm1 after partial and nonunix sendmsg" (← rawNetClose uxScm1)

  let (ct0, ct1) ← assertOk "ctrunc carrier sp" (← ops.socketpair .unix .stream nbFlags)
  let (pr0, pr1) ← assertOk "ctrunc probe sp" (← ops.socketpair .unix .stream nbFlags)
  try
    let zSent ← assertOk "sendto empty payload" (← ops.sendto ct0 ByteArray.empty { nosignal := true })
    assertTrue "sendto empty payload returns 0" (zSent == 0)
    assertOk "ctrunc sendmsg 2 fds" (← ops.sendmsg ct0 #[pr1, ct0])
    assertOk "close sender pr1" (← rawNetClose pr1)
    assertErr "ctrunc recvmsg maxFds=1 EPROTO" (← ops.recvmsg ct1 1) Errno.EPROTO
    let probeEof ← assertOk "ctrunc leaked fd check" (← ops.recvfrom pr0 8 { dontwait := true })
    assertTrue "ctrunc closed truncated scm fds" (probeEof.size == 0)
  finally
    safeClose pr1
    safeClose pr0
    safeClose ct1
    safeClose ct0

  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"selfShut model rejected {lbl}: req={repr req} out={repr out}")
  let v4Map0 : SockAddr := .ipv6 0 0x0000ffff00000000 0 74565 7
  let v4MapP : SockAddr := .ipv6 0 0x0000ffff00000000 35979 0 0
  let mut ms ← mustStep "selfShut sock" (NetState.initial false) (.socket .inet6 .stream {} 0) (.opened 0)
  ms ← mustStep "selfShut bind" ms (.bind 0 v4Map0) .unit
  ms ← mustStep "selfShut gsn" ms (.getsockname 0) (.addr v4MapP)
  ms ← mustStep "selfShut conn" ms (.connect 0 v4MapP) .unit
  ms ← mustStep "selfShut send" ms (.sendto 0 (ByteArray.mk #[142]) { dontwait := true }) (.u32 1)
  ms ← mustStep "selfShut wr" ms (.shutdown 0 .wr) .unit
  let msRdUnit ← mustStep "selfShut rd unit" ms (.shutdown 0 .rd) .unit
  let _ ← mustStep "selfShut rst soError" msRdUnit (.getsockopt 0 .error) (.u32 Errno.ECONNRESET)

  let mut msSyn ← mustStep "synRst sock" (NetState.initial false) (.socket .inet .stream {} 0) (.opened 0)
  msSyn ← mustStep "synRst eintr" msSyn (.connect 0 (.ipv4 0xc0000201 80)) (.err Errno.EINTR)
  msSyn ← mustStep "synRst blkZero" msSyn (.recvfrom 0 0 {}) (.bytes ByteArray.empty)
  msSyn ← mustStep "synRst shut" msSyn (.shutdown 0 .rdwr) .unit
  let msSynRead ← mustStep "synRst soerr" msSyn (.getsockopt 0 .error) (.u32 Errno.ECONNRESET)
  let _ ← mustStep "synRst soerr0" msSynRead (.getsockopt 0 .error) (.u32 0)
  let msPostRef ← mustStep "synRst postRefused" msSyn (.connect 0 (.ipv4 INADDR_LOOPBACK 1)) (.err Errno.ECONNREFUSED)
  let _ ← mustStep "synRst postRefused soerr0" msPostRef (.getsockopt 0 .error) (.u32 0)

  let nanosZero ← IO.monoNanosNow
  let u108Pfx := s!"/tmp/lsnet108_{nanosZero}_"
  let u108Str := u108Pfx ++ String.ofList (List.replicate (UNIX_PATH_MAX - u108Pfx.utf8ByteSize) 'x')
  let u108Addr := SockAddr.unix u108Str.toUTF8
  assertTrue "u108 exact byte length" (u108Str.utf8ByteSize == UNIX_PATH_MAX)
  try IO.FS.removeFile u108Str catch _ => pure ()
  let u108Lis ← assertOk "u108 lis" (← ops.socket .unix .stream nbFlags 0)
  let u108Cli ← assertOk "u108 cli" (← ops.socket .unix .stream nbFlags 0)
  try
    assertOk "u108 bind" (← ops.bind u108Lis u108Addr)
    let gsn108 ← assertOk "u108 gsn" (← ops.getsockname u108Lis)
    assertTrue "u108 getsockname roundtrip" (gsn108 == u108Addr)
    assertOk "u108 listen" (← ops.listen u108Lis 4)
    assertOk "u108 connect" (← ops.connect u108Cli u108Addr)
    let (u108Acc, u108Peer) ← assertOk "u108 accept4" (← ops.accept4 u108Lis nbFlags)
    safeClose u108Acc
    let mut ms108 ← mustStep "u108.lis" (NetState.initial false) (.socket .unix .stream nbFlags 0) (.opened 0)
    ms108 ← mustStep "u108.cli" ms108 (.socket .unix .stream nbFlags 0) (.opened 1)
    ms108 ← mustStep "u108.bind" ms108 (.bind 0 u108Addr) .unit
    ms108 ← mustStep "u108.gsn" ms108 (.getsockname 0) (.addr gsn108)
    ms108 ← mustStep "u108.listen" ms108 (.listen 0 4) .unit
    ms108 ← mustStep "u108.conn" ms108 (.connect 1 u108Addr) .unit
    let _ ← mustStep "u108.acc" ms108 (.accept4 0 nbFlags) (.accepted 2 u108Peer)
  finally
    safeClose u108Cli
    safeClose u108Lis
    try IO.FS.removeFile u108Str catch _ => pure ()

  let (stZero, _) ← SandboxEnv.runForked do
    SandboxEnv.closeRaw 0
    let sZero ← assertOk "socket raw fd 0" (← ops.socket .unix .stream nbFlags 0)
    let rawSock0 ← SandboxEnv.peekRawFd sZero
    assertTrue "socket landed on raw fd 0" (rawSock0 == 0)
    let _ ← assertOk "getsockname on raw fd 0" (← ops.getsockname sZero)
    let zPath := ByteArray.mk (#[0] ++ s!"leanswe-net-zfd-{nanosZero}".toUTF8.data)
    let zLis ← assertOk "zfd unix lis" (← ops.socket .unix .stream nbFlags 0)
    let zCli ← assertOk "zfd unix cli" (← ops.socket .unix .stream nbFlags 0)
    assertOk "zfd bind" (← ops.bind zLis (.unix zPath))
    assertOk "zfd listen" (← ops.listen zLis 4)
    assertOk "zfd connect" (← ops.connect zCli (.unix zPath))
    assertOk "close placeholder raw fd 0" (← rawNetClose sZero)
    let (accZero, _) ← assertOk "accept4 raw fd 0" (← ops.accept4 zLis nbFlags)
    let rawAcc0 ← SandboxEnv.peekRawFd accZero
    assertTrue "accept4 landed on raw fd 0" (rawAcc0 == 0)
    assertOk "close accepted raw fd 0" (← rawNetClose accZero)
    assertOk "close zCli" (← rawNetClose zCli)
    assertOk "close zLis" (← rawNetClose zLis)

    let (spZ0, spZ1) ← assertOk "socketpair raw fd 0" (← ops.socketpair .unix .stream nbFlags)
    let rawSp0 ← SandboxEnv.peekRawFd spZ0
    assertTrue "socketpair first end landed on raw fd 0" (rawSp0 == 0)
    let sentZ ← assertOk "sendto raw fd 0" (← ops.sendto spZ0 (ByteArray.mk #[0x42]) { nosignal := true })
    assertTrue "sendto raw fd 0 byte count" (sentZ == 1)
    let gotZ ← assertOk "recvfrom peer of raw fd 0" (← ops.recvfrom spZ1 4 { dontwait := true })
    assertTrue "recvfrom peer payload" (gotZ == ByteArray.mk #[0x42])
    assertOk "close spZ0 raw fd 0" (← rawNetClose spZ0)
    assertOk "close spZ1" (← rawNetClose spZ1)

    let finRx0 ← allocStreamReadDroppingWriteFd0
    let eofZ ← assertOk "finalizer raw fd 0 eof" (← ops.recvfrom finRx0 8 { dontwait := true })
    assertTrue "finalizer closed raw fd 0 peer" (eofZ.size == 0)
    assertOk "close finRx0" (← rawNetClose finRx0)

    let ph0 ← assertOk "ctrunc placeholder fd 0" (← ops.socket .unix .stream nbFlags 0)
    let (ctZ0, ctZ1) ← assertOk "ctrunc fd0 carrier" (← ops.socketpair .unix .stream nbFlags)
    let (prZ0, prZ1) ← assertOk "ctrunc fd0 probe" (← ops.socketpair .unix .stream nbFlags)
    assertOk "ctrunc fd0 sendmsg 2 fds" (← ops.sendmsg ctZ0 #[prZ1, ctZ0])
    assertOk "close prZ1" (← rawNetClose prZ1)
    assertOk "close placeholder freeing fd 0" (← rawNetClose ph0)
    assertErr "ctrunc fd0 recvmsg EPROTO" (← ops.recvmsg ctZ1 1) Errno.EPROTO
    let eofCt0 ← assertOk "ctrunc fd0 leaked check" (← ops.recvfrom prZ0 8 { dontwait := true })
    assertTrue "ctrunc closed truncated raw fd 0" (eofCt0.size == 0)
    assertOk "close prZ0" (← rawNetClose prZ0)
    assertOk "close ctZ1" (← rawNetClose ctZ1)
    assertOk "close ctZ0" (← rawNetClose ctZ0)

    let (dw0, dw1) ← assertOk "blocking dontwait sp"
      (← ops.socketpair .unix .stream { nonblock := false, cloexec := true })
    rawRtArmSigalrm 10000 0
    let rDw ← ops.recvfrom dw0 8 { dontwait := true }
    rawRtDisarmSigalrm 0
    assertErr "blocking socket recvfrom MSG_DONTWAIT EAGAIN" rDw Errno.EAGAIN
    rawRtResetSigpipeDfl
    assertOk "close dw1 for sigpipe check" (← rawNetClose dw1)
    assertErr "sendto MSG_NOSIGNAL under SIG_DFL EPIPE"
      (← ops.sendto dw0 (ByteArray.mk #[0x7f]) { nosignal := true }) Errno.EPIPE
    assertOk "close dw0" (← rawNetClose dw0)
    return ByteArray.empty
  assertTrue "forked net raw fd 0 child status" (stZero == 0)

  let uxBlPath := ByteArray.mk (#[0] ++ s!"leanswe-net-somax-{nanosZero}".toUTF8.data)
  let uxBlLis ← assertOk "somax ux lis" (← ops.socket .unix .stream nbFlags 0)
  try
    assertOk "somax ux bind" (← ops.bind uxBlLis (.unix uxBlPath))
    assertOk "somax ux listen max" (← ops.listen uxBlLis 0xffffffff)
    let mut msBl ← mustStep "somax.lis" (NetState.initial false) (.socket .unix .stream nbFlags 0) (.opened 0)
    msBl ← mustStep "somax.bind" msBl (.bind 0 (.unix uxBlPath)) .unit
    msBl ← mustStep "somax.listen" msBl (.listen 0 0xffffffff) .unit
    for _ in [0 : 4097] do
      let cTmp ← assertOk "somax ux cli" (← ops.socket .unix .stream nbFlags 0)
      assertOk "somax ux conn" (← ops.connect cTmp (.unix uxBlPath))
      safeClose cTmp
      msBl ← mustStep "somax.copen" msBl (.socket .unix .stream nbFlags 0) (.opened 1)
      msBl ← mustStep "somax.cconn" msBl (.connect 1 (.unix uxBlPath)) .unit
      match NetState.closeHandle msBl 1 with
      | .ok nextSt => msBl := nextSt
      | .error e => throw (IO.userError s!"somax closeHandle failed: {e}")
    let cOvf ← assertOk "somax ux ovf" (← ops.socket .unix .stream nbFlags 0)
    try
      assertErr "somax ux 4098th EAGAIN" (← ops.connect cOvf (.unix uxBlPath)) Errno.EAGAIN
      msBl ← mustStep "somax.ovfOpen" msBl (.socket .unix .stream nbFlags 0) (.opened 1)
      let _ ← mustStep "somax.ovfEagain" msBl (.connect 1 (.unix uxBlPath)) (.err Errno.EAGAIN)
    finally
      safeClose cOvf
  finally
    safeClose uxBlLis

  if ← isLoopbackUp ops then
    let tcpBlLis ← assertOk "somax tcp lis" (← ops.socket .inet .stream nbFlags 0)
    try
      assertOk "somax tcp bind" (← ops.bind tcpBlLis (.ipv4 INADDR_LOOPBACK 0))
      let .ipv4 _ tcpBlPort ← assertOk "somax tcp gsn" (← ops.getsockname tcpBlLis)
        | throw (IO.userError "somax tcpBlPort")
      assertOk "somax tcp listen max" (← ops.listen tcpBlLis 0xffffffff)
      let mut msTcpBl ← mustStep "somaxTcp.lis" (NetState.initial false) (.socket .inet .stream nbFlags 0) (.opened 0)
      msTcpBl ← mustStep "somaxTcp.bind" msTcpBl (.bind 0 (.ipv4 INADDR_LOOPBACK tcpBlPort)) .unit
      msTcpBl ← mustStep "somaxTcp.listen" msTcpBl (.listen 0 0xffffffff) .unit
      for i in [0 : 4097] do
        let hid := i + 1
        let cTmp ← assertOk "somax tcp cli" (← ops.socket .inet .stream { nonblock := false, cloexec := true } 0)
        assertOk "somax tcp conn" (← ops.connect cTmp (.ipv4 INADDR_LOOPBACK tcpBlPort))
        safeClose cTmp
        msTcpBl ← mustStep "somaxTcp.copen" msTcpBl (.socket .inet .stream { nonblock := false, cloexec := true } 0) (.opened hid)
        msTcpBl ← mustStep "somaxTcp.cconn" msTcpBl (.connect hid (.ipv4 INADDR_LOOPBACK tcpBlPort)) .unit
        match NetState.closeHandle msTcpBl hid with
        | .ok nextSt => msTcpBl := nextSt
        | .error e => throw (IO.userError s!"somaxTcp closeHandle failed: {e}")
      let cTcpOvf ← assertOk "somax tcp ovf" (← ops.socket .inet .stream nbFlags 0)
      try
        let rOvfConn ← ops.connect cTcpOvf (.ipv4 INADDR_LOOPBACK tcpBlPort)
        let outOvfConn : NetOutcome := match rOvfConn with | .ok () => .unit | .error e => .err e
        assertOk "somax tcp ovf shut" (← ops.shutdown cTcpOvf .rdwr)
        let seTcpOvf ← assertOk "somax tcp ovf soerr" (← ops.getsockopt cTcpOvf .error)
        assertTrue "somax tcp 4098th dropped SYN ECONNRESET" (seTcpOvf == Errno.ECONNRESET.toNat.toUInt32)
        msTcpBl ← mustStep "somaxTcp.ovfOpen" msTcpBl (.socket .inet .stream nbFlags 0) (.opened 4098)
        msTcpBl ← mustStep "somaxTcp.ovfConn" msTcpBl (.connect 4098 (.ipv4 INADDR_LOOPBACK tcpBlPort)) outOvfConn
        msTcpBl ← mustStep "somaxTcp.ovfShut" msTcpBl (.shutdown 4098 .rdwr) .unit
        let _ ← mustStep "somaxTcp.ovfSoerr" msTcpBl (.getsockopt 4098 .error) (.u32 seTcpOvf)
      finally
        safeClose cTcpOvf
    finally
      safeClose tcpBlLis
    let (stAlrm, _) ← SandboxEnv.runForked do
      let lisOvf ← assertOk "alrm lis" (← ops.socket .inet .stream nbFlags 0)
      let cFill ← assertOk "alrm cfill" (← ops.socket .inet .stream nbFlags 0)
      let cBlk ← assertOk "alrm cblk" (← ops.socket .inet .stream { nonblock := false, cloexec := true } 0)
      let cEst ← assertOk "alrm cest" (← ops.socket .inet .stream { nonblock := false, cloexec := true } 0)
      try
        assertOk "alrm lis bind" (← ops.bind lisOvf (.ipv4 INADDR_LOOPBACK 0))
        let .ipv4 _ lpOvf ← assertOk "alrm lis gsn" (← ops.getsockname lisOvf)
          | throw (IO.userError "alrm lpOvf")
        assertOk "alrm lis listen 0" (← ops.listen lisOvf 0)
        let rFill ← ops.connect cFill (.ipv4 INADDR_LOOPBACK lpOvf)
        let outFill : NetOutcome := match rFill with | .ok () => .unit | .error e => .err e
        rawRtArmSigalrm 10000 0
        let rConn ← ops.connect cBlk (.ipv4 INADDR_LOOPBACK lpOvf)
        rawRtDisarmSigalrm 0
        assertErr "alrm blk connect EINTR" rConn Errno.EINTR
        let gBlk ← assertOk "alrm cblk gsn" (← ops.getsockname cBlk)
        assertErr "alrm cblk listen EINVAL" (← ops.listen cBlk 4) Errno.EINVAL
        rawRtArmSigalrm 10000 0
        let rZeroSyn ← ops.recvfrom cBlk 0 {}
        rawRtDisarmSigalrm 0
        let bZeroSyn ← assertOk "alrm syn recv0" rZeroSyn
        assertTrue "alrm syn recv0 empty" (bZeroSyn.size == 0)
        assertOk "alrm cblk shut" (← ops.shutdown cBlk .rdwr)
        let seBlk ← assertOk "alrm cblk soerr" (← ops.getsockopt cBlk .error)
        assertTrue "alrm cblk soerr ECONNRESET" (seBlk == Errno.ECONNRESET.toNat.toUInt32)
        let mut msA ← mustStep "alrm.lis" (NetState.initial false) (.socket .inet .stream nbFlags 0) (.opened 0)
        msA ← mustStep "alrm.bind" msA (.bind 0 (.ipv4 INADDR_LOOPBACK lpOvf)) .unit
        msA ← mustStep "alrm.listen" msA (.listen 0 0) .unit
        msA ← mustStep "alrm.cfill" msA (.socket .inet .stream nbFlags 0) (.opened 1)
        msA ← mustStep "alrm.cfillConn" msA (.connect 1 (.ipv4 INADDR_LOOPBACK lpOvf)) outFill
        msA ← mustStep "alrm.cblk" msA (.socket .inet .stream { nonblock := false, cloexec := true } 0) (.opened 2)
        msA ← mustStep "alrm.eintr" msA (.connect 2 (.ipv4 INADDR_LOOPBACK lpOvf)) (.err Errno.EINTR)
        msA ← mustStep "alrm.gsn" msA (.getsockname 2) (.addr gBlk)
        msA ← mustStep "alrm.lisEinval" msA (.listen 2 4) (.err Errno.EINVAL)
        msA ← mustStep "alrm.synRecv0" msA (.recvfrom 2 0 {}) (.bytes bZeroSyn)
        msA ← mustStep "alrm.shut" msA (.shutdown 2 .rdwr) .unit
        let _ ← mustStep "alrm.soerr" msA (.getsockopt 2 .error) (.u32 seBlk)
        assertOk "alrm lis widen" (← ops.listen lisOvf 4)
        assertOk "alrm cest conn" (← ops.connect cEst (.ipv4 INADDR_LOOPBACK lpOvf))
        rawRtArmSigalrm 10000 0
        let rZeroEst ← ops.recvfrom cEst 0 {}
        rawRtDisarmSigalrm 0
        let bZeroEst ← assertOk "alrm est recv0" rZeroEst
        assertTrue "alrm est recv0 empty" (bZeroEst.size == 0)
        msA ← mustStep "alrm.widen" msA (.listen 0 4) .unit
        msA ← mustStep "alrm.cest" msA (.socket .inet .stream { nonblock := false, cloexec := true } 0) (.opened 3)
        msA ← mustStep "alrm.cestConn" msA (.connect 3 (.ipv4 INADDR_LOOPBACK lpOvf)) .unit
        let _ ← mustStep "alrm.estRecv0" msA (.recvfrom 3 0 {}) (.bytes bZeroEst)
      finally
        rawRtDisarmSigalrm 0
        safeClose cEst
        safeClose cBlk
        safeClose cFill
        safeClose lisOvf
      return ByteArray.empty
    assertTrue "forked net sigalrm child status" (stAlrm == 0)

private def runMulticastAndV6SelfShutTests : IO Unit := do
  let ops := defaultOps
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match Net.allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"multicast/self-shut parity: model rejected {lbl}: req={repr req} out={repr out}")
  let s0 := NetState.initial true
  let tx ← assertOk "mcast224 tx" (← ops.socket .inet .dgram nbFlags 0)
  let rxMcast ← assertOk "mcast224 rxMcast" (← ops.socket .inet .dgram nbFlags 0)
  let rxAny ← assertOk "mcast224 rxAny" (← ops.socket .inet .dgram nbFlags 0)
  let rxV6 ← assertOk "mcast224 rxV6" (← ops.socket .inet6 .dgram nbFlags 0)
  try
    assertOk "mcast224 tx bind" (← ops.bind tx (.ipv4 0x7f000002 0))
    assertOk "mcast224 rxMcast reuse" (← ops.setsockopt rxMcast .reuseAddr 1)
    assertOk "mcast224 rxAny reuse" (← ops.setsockopt rxAny .reuseAddr 1)
    assertOk "mcast224 rxV6 reuse" (← ops.setsockopt rxV6 .reuseAddr 1)
    assertOk "mcast224 rxMcast bind" (← ops.bind rxMcast (.ipv4 INADDR_ALLHOSTS_GROUP 0))
    let .ipv4 _ mPort ← assertOk "mcast224 rxMcast gsn" (← ops.getsockname rxMcast)
      | throw (IO.userError "mcast224 expected ipv4 gsn")
    assertOk "mcast224 rxAny bind" (← ops.bind rxAny (.ipv4 INADDR_ANY mPort))
    assertOk "mcast224 rxV6 bind" (← ops.bind rxV6 (.ipv6 0 0 mPort 0 0))
    assertOk "mcast224 tx connect" (← ops.connect tx (.ipv4 INADDR_ALLHOSTS_GROUP mPort))
    let payload := ByteArray.mk #[11, 22, 33]
    let n1 ← assertOk "mcast224 send1" (← ops.sendto tx payload {})
    assertTrue "mcast224 send1 len" (n1 == 3)
    IO.sleep 2
    let bMcast ← assertOk "mcast224 recv mcast" (← ops.recvfrom rxMcast 16 { dontwait := true })
    let bAny ← assertOk "mcast224 recv any" (← ops.recvfrom rxAny 16 { dontwait := true })
    assertTrue "mcast224 recv mcast eq" (bMcast == payload)
    assertTrue "mcast224 recv any eq" (bAny == payload)
    assertErr "mcast224 recv v6 eagain" (← ops.recvfrom rxV6 16 { dontwait := true }) Errno.EAGAIN
    let n0 ← assertOk "mcast224 send0" (← ops.sendto tx ByteArray.empty {})
    assertTrue "mcast224 send0 len" (n0 == 0)
    IO.sleep 2
    let bZero ← assertOk "mcast224 recv0" (← ops.recvfrom rxMcast 0 {})
    assertTrue "mcast224 recv0 empty" (bZero.size == 0)
    let mut ms ← mustStep "m.tx" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
    ms ← mustStep "m.rxM" ms (.socket .inet .dgram nbFlags 0) (.opened 1)
    ms ← mustStep "m.rxA" ms (.socket .inet .dgram nbFlags 0) (.opened 2)
    ms ← mustStep "m.rx6" ms (.socket .inet6 .dgram nbFlags 0) (.opened 3)
    ms ← mustStep "m.txB" ms (.bind 0 (.ipv4 0x7f000002 0)) .unit
    ms ← mustStep "m.rxMR" ms (.setsockopt 1 .reuseAddr 1) .unit
    ms ← mustStep "m.rxAR" ms (.setsockopt 2 .reuseAddr 1) .unit
    ms ← mustStep "m.rx6R" ms (.setsockopt 3 .reuseAddr 1) .unit
    ms ← mustStep "m.rxMB" ms (.bind 1 (.ipv4 INADDR_ALLHOSTS_GROUP 0)) .unit
    ms ← mustStep "m.rxMG" ms (.getsockname 1) (.addr (.ipv4 INADDR_ALLHOSTS_GROUP mPort))
    ms ← mustStep "m.rxAB" ms (.bind 2 (.ipv4 INADDR_ANY mPort)) .unit
    ms ← mustStep "m.rx6B" ms (.bind 3 (.ipv6 0 0 mPort 0 0)) .unit
    ms ← mustStep "m.txC" ms (.connect 0 (.ipv4 INADDR_ALLHOSTS_GROUP mPort)) .unit
    ms ← mustStep "m.txS1" ms (.sendto 0 payload {}) (.u32 3)
    ms ← mustStep "m.rxM1" ms (.recvfrom 1 16 { dontwait := true }) (.bytes bMcast)
    ms ← mustStep "m.rxA1" ms (.recvfrom 2 16 { dontwait := true }) (.bytes bAny)
    ms ← mustStep "m.rx6E" ms (.recvfrom 3 16 { dontwait := true }) (.err Errno.EAGAIN)
    ms ← mustStep "m.txS0" ms (.sendto 0 ByteArray.empty {}) (.u32 0)
    let _ ← mustStep "m.rxM0" ms (.recvfrom 1 0 {}) (.bytes bZero)
  finally
    safeClose rxV6
    safeClose rxAny
    safeClose rxMcast
    safeClose tx
  let mut ms6 ← mustStep "v6s.sock" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ms6 ← mustStep "v6s.bind" ms6 (.bind 0 (.ipv6 0 1 0 0 0)) .unit
  ms6 ← mustStep "v6s.gsn" ms6 (.getsockname 0) (.addr (.ipv6 0 1 55101 0 0))
  ms6 ← mustStep "v6s.conn" ms6 (.connect 0 (.ipv6 0 1 55101 0 0)) (.err Errno.EINPROGRESS)
  let ms6Down ← mustStep "v6s.loDown" ms6 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  let ms6Shut ← mustStep "v6s.shutWr" ms6Down (.shutdown 0 .wr) .unit
  let ms6Err1 ← mustStep "v6s.soErr1" ms6Shut (.getsockopt 0 .error) (.u32 Errno.ENETUNREACH)
  assertTrue "v6s.soErr2 rejects ENETUNREACH" ((Net.allowedStep ms6Err1 (.getsockopt 0 .error) (.u32 Errno.ENETUNREACH)).isNone)
  let _ ← mustStep "v6s.soErr2 zero" ms6Err1 (.getsockopt 0 .error) (.u32 0)
  let ms6Tx ← mustStep "v6s.tx" ms6 (.sendto 0 (ByteArray.mk #[42, 43]) {}) (.u32 2)
  let ms6RxDown ← mustStep "v6s.rxLoDown" ms6Tx (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  let ms6Rdwr ← mustStep "v6s.shutRdwr" ms6RxDown (.shutdown 0 .rdwr) .unit
  let ms6RdwrE1 ← mustStep "v6s.rdwrSoErr1" ms6Rdwr (.getsockopt 0 .error) (.u32 Errno.ENETUNREACH)
  assertTrue "v6s.rdwrSoErr2 rejects ENETUNREACH" ((Net.allowedStep ms6RdwrE1 (.getsockopt 0 .error) (.u32 Errno.ENETUNREACH)).isNone)
  let _ ← mustStep "v6s.rdwrSoErr2 zero" ms6RdwrE1 (.getsockopt 0 .error) (.u32 0)
  let mut ms4 ← mustStep "v4s.sock" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
  ms4 ← mustStep "v4s.bind" ms4 (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) .unit
  ms4 ← mustStep "v4s.gsn" ms4 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 55102))
  ms4 ← mustStep "v4s.conn" ms4 (.connect 0 (.ipv4 INADDR_LOOPBACK 55102)) (.err Errno.EINPROGRESS)
  ms4 ← mustStep "v4s.loDown" ms4 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  ms4 ← mustStep "v4s.shutWr" ms4 (.shutdown 0 .wr) .unit
  assertTrue "v4s.soErr rejects ENETUNREACH" ((Net.allowedStep ms4 (.getsockopt 0 .error) (.u32 Errno.ENETUNREACH)).isNone)

private def runPreShutCloseWaitLoFlapTests : IO Unit := do
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match Net.allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"pre-shut closeWait lo-flap parity: model rejected {lbl}: req={repr req} out={repr out}")
  let mustClose (lbl : String) (s : NetState) (hid : HandleId) : IO NetState := do
    match s.closeHandle hid with
    | .ok s' => return s'
    | .error e => throw (IO.userError s!"pre-shut closeWait lo-flap closeHandle {lbl} failed: {e}")
  let nbNoClo : SockFlags := { nonblock := true, cloexec := false }
  let blkFlags : SockFlags := { nonblock := false, cloexec := true }
  let s0 := NetState.initial true
  let mut c ← mustStep "ci.s0" s0 (.socket .inet6 .stream nbNoClo 6) (.opened 0)
  c ← mustStep "ci.sh0" c (.shutdown 0 .rdwr) (.err Errno.ENOTCONN)
  c ← mustStep "ci.lis0" c (.listen 0 0) .unit
  c ← mustStep "ci.gsn0" c (.getsockname 0) (.addr (.ipv6 0 0 55201 0 0))
  c ← mustStep "ci.s1" c (.socket .inet .stream nbNoClo 0) (.opened 1)
  c ← mustStep "ci.sh1pre" c (.shutdown 1 .rdwr) (.err Errno.ENOTCONN)
  c ← mustStep "ci.conn1" c (.connect 1 (.ipv4 INADDR_LOOPBACK 55201)) (.err Errno.EINPROGRESS)
  c ← mustStep "ci.acc" c (.accept4 0 nbFlags) (.accepted 2 (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 49153 0 0))
  let cNoFlap1 ← mustStep "ci.noFlap.sh1" c (.shutdown 1 .rdwr) .unit
  assertTrue "ci.noFlap.sh1.wr rejects unit" ((Net.allowedStep cNoFlap1 (.shutdown 1 .wr) .unit).isNone)
  let cNoFlap2 ← mustStep "ci.noFlap.sh1.wr" cNoFlap1 (.shutdown 1 .wr) (.err Errno.ENOTCONN)
  assertTrue "ci.noFlap.sh2.rd rejects unit" ((Net.allowedStep cNoFlap2 (.shutdown 2 .rd) .unit).isNone)
  let _ ← mustStep "ci.noFlap.sh2.rd" cNoFlap2 (.shutdown 2 .rd) (.err Errno.ENOTCONN)
  let cDown ← mustStep "ci.loDown" c (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  let cDownSh ← mustStep "ci.sh1Down" cDown (.shutdown 1 .rdwr) .unit
  assertTrue "ci.sh1Down queues single shutFin" (cDownSh.loPendingTcp.length == 1)
  let cDownShDup ← mustStep "ci.sh1DownDup" cDownSh (.shutdown 1 .wr) .unit
  assertTrue "ci.sh1DownDup does not duplicate shutFin" (cDownShDup.loPendingTcp.length == 1)
  let cUp ← mustStep "ci.loUp" cDownSh (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let c12Unit ← mustStep "ci.sh1Up.unit" cUp (.shutdown 1 .wr) .unit
  let _ ← mustStep "ci.sh2Up.rd.unit" c12Unit (.shutdown 2 .rd) .unit
  let _ ← mustStep "ci.sh2Up.wr.unit" c12Unit (.shutdown 2 .wr) .unit
  let _ ← mustStep "ci.sh2Up.rdwr.unit" c12Unit (.shutdown 2 .rdwr) .unit
  let c12Err ← mustStep "ci.sh1Up.enotconn" cUp (.shutdown 1 .wr) (.err Errno.ENOTCONN)
  let _ ← mustStep "ci.sh2Up.enotconn" c12Err (.shutdown 2 .rd) (.err Errno.ENOTCONN)
  let mut v4 ← mustStep "v4.s0" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
  v4 ← mustStep "v4.sh0" v4 (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  v4 ← mustStep "v4.lis0" v4 (.listen 0 4) .unit
  v4 ← mustStep "v4.gsn0" v4 (.getsockname 0) (.addr (.ipv4 INADDR_ANY 55202))
  v4 ← mustStep "v4.s1" v4 (.socket .inet .stream nbFlags 0) (.opened 1)
  v4 ← mustStep "v4.sh1pre" v4 (.shutdown 1 .wr) (.err Errno.ENOTCONN)
  v4 ← mustStep "v4.conn1" v4 (.connect 1 (.ipv4 INADDR_LOOPBACK 55202)) (.err Errno.EINPROGRESS)
  v4 ← mustStep "v4.acc" v4 (.accept4 0 nbFlags) (.accepted 2 (.ipv4 INADDR_LOOPBACK 49154))
  v4 ← mustStep "v4.loDown" v4 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  v4 ← mustStep "v4.sh1Down" v4 (.shutdown 1 .wr) .unit
  v4 ← mustStep "v4.loUp" v4 (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let _ ← mustStep "v4.sh2.unit" v4 (.shutdown 2 .rd) .unit
  let _ ← mustStep "v4.rx2.eagain" v4 (.recvfrom 2 8 { dontwait := true }) (.err Errno.EAGAIN)
  let _ ← mustStep "v4.rx2.eof" v4 (.recvfrom 2 8 { dontwait := true }) (.bytes ByteArray.empty)
  let _ ← mustStep "v4.gso1.zero" v4 (.getsockopt 1 .error) (.u32 0)
  assertTrue "v4.gso1 rejects ENETUNREACH" ((Net.allowedStep v4 (.getsockopt 1 .error) (.u32 Errno.ENETUNREACH)).isNone)
  let mut v6 ← mustStep "v6.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  v6 ← mustStep "v6.sh0" v6 (.shutdown 0 .rdwr) (.err Errno.ENOTCONN)
  v6 ← mustStep "v6.lis0" v6 (.listen 0 4) .unit
  v6 ← mustStep "v6.gsn0" v6 (.getsockname 0) (.addr (.ipv6 0 0 55203 0 0))
  v6 ← mustStep "v6.s1" v6 (.socket .inet6 .stream nbFlags 0) (.opened 1)
  v6 ← mustStep "v6.sh1pre" v6 (.shutdown 1 .rdwr) (.err Errno.ENOTCONN)
  v6 ← mustStep "v6.conn1" v6 (.connect 1 (.ipv6 0 1 55203 0 0)) (.err Errno.EINPROGRESS)
  v6 ← mustStep "v6.acc" v6 (.accept4 0 nbFlags) (.accepted 2 (.ipv6 0 1 49155 0 0))
  v6 ← mustStep "v6.loDown" v6 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  v6 ← mustStep "v6.sh1Down" v6 (.shutdown 1 .rdwr) .unit
  let v6Err ← mustStep "v6.gso1.unreach" v6 (.getsockopt 1 .error) (.u32 Errno.ENETUNREACH)
  let v6Up ← mustStep "v6.loUp" v6Err (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let _ ← mustStep "v6.sh1.unit" v6Up (.shutdown 1 .wr) .unit
  let _ ← mustStep "v6.sh2.unit" v6Up (.shutdown 2 .rd) .unit
  let _ ← mustStep "v6.sh2.enotconn" v6Up (.shutdown 2 .rd) (.err Errno.ENOTCONN)
  let _ ← mustStep "v6.bind1.einval" v6Up (.bind 1 (.ipv6 0 1 0 0 0)) (.err Errno.EINVAL)
  let _ ← mustStep "v6.bind1.unit" v6Up (.bind 1 (.ipv6 0 1 0 0 0)) .unit
  let mut mv ← mustStep "mv.s0" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
  mv ← mustStep "mv.sh0" mv (.shutdown 0 .rdwr) (.err Errno.ENOTCONN)
  mv ← mustStep "mv.lis0" mv (.listen 0 4) .unit
  mv ← mustStep "mv.gsn0" mv (.getsockname 0) (.addr (.ipv4 INADDR_ANY 55204))
  mv ← mustStep "mv.s1" mv (.socket .inet6 .stream nbFlags 0) (.opened 1)
  mv ← mustStep "mv.sh1pre" mv (.shutdown 1 .rdwr) (.err Errno.ENOTCONN)
  mv ← mustStep "mv.conn1" mv (.connect 1 (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 55204 0 0)) (.err Errno.EINPROGRESS)
  mv ← mustStep "mv.acc" mv (.accept4 0 nbFlags) (.accepted 2 (.ipv4 INADDR_LOOPBACK 49156))
  mv ← mustStep "mv.loDown" mv (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  mv ← mustStep "mv.sh1Down" mv (.shutdown 1 .rdwr) .unit
  mv ← mustStep "mv.loUp" mv (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let _ ← mustStep "mv.sh2.rdwr.unit" mv (.shutdown 2 .rdwr) .unit
  let mut orp ← mustStep "orp.s0" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
  orp ← mustStep "orp.lis0" orp (.listen 0 4) .unit
  orp ← mustStep "orp.gsn0" orp (.getsockname 0) (.addr (.ipv4 INADDR_ANY 55205))
  orp ← mustStep "orp.s1" orp (.socket .inet .stream nbFlags 0) (.opened 1)
  orp ← mustStep "orp.sh1pre" orp (.shutdown 1 .rdwr) (.err Errno.ENOTCONN)
  orp ← mustStep "orp.conn1" orp (.connect 1 (.ipv4 INADDR_LOOPBACK 55205)) (.err Errno.EINPROGRESS)
  orp ← mustStep "orp.acc" orp (.accept4 0 nbFlags) (.accepted 2 (.ipv4 INADDR_LOOPBACK 49157))
  orp ← mustClose "orp.close2" orp 2
  let orpDown ← mustStep "orp.loDown" orp (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  let orpFlap ← mustStep "orp.loUp" orpDown (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let _ ← mustStep "orp.noShut.conn2.unit" orpFlap (.connect 1 (.ipv4 INADDR_LOOPBACK 55205)) .unit
  let _ ← mustStep "orp.noShut.sh1.rd.unit" orpFlap (.shutdown 1 .rd) .unit
  assertTrue "orp.noShut.conn2 modelOps returns unit" ((stepNetCore orpFlap (.connect 1 (.ipv4 INADDR_LOOPBACK 55205)) none).map Prod.fst == some .unit)
  assertTrue "orp.noShut.sh1.rd modelOps returns unit" ((stepNetCore orpFlap (.shutdown 1 .rd) none).map Prod.fst == some .unit)
  let _ ← mustStep "orp.noShut.bind1.einval" orpFlap (.bind 1 (.ipv4 INADDR_LOOPBACK 0)) (.err Errno.EINVAL)
  let orpShutDown ← mustStep "orp.shut.wrDown" orpDown (.shutdown 1 .wr) .unit
  let orpShutUp ← mustStep "orp.shut.loUp" orpShutDown (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  assertTrue "orp.shut.sh1 modelOps returns ENOTCONN" ((stepNetCore orpShutUp (.shutdown 1 .rd) none).map Prod.fst == some (.err Errno.ENOTCONN))
  let _ ← mustStep "orp.shut.sh1.unit" orpShutUp (.shutdown 1 .rd) .unit
  let _ ← mustStep "orp.shut.sh1.enotconn" orpShutUp (.shutdown 1 .rd) (.err Errno.ENOTCONN)
  let mut t6 ← mustStep "t6.s0" s0 (.socket .inet6 .stream blkFlags 0) (.opened 0)
  t6 ← mustStep "t6.taint" t6 (.connect 0 (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 1 0 0)) (.err Errno.ECONNREFUSED)
  t6 ← mustStep "t6.sh0" t6 (.shutdown 0 .rdwr) (.err Errno.ENOTCONN)
  t6 ← mustStep "t6.lis0" t6 (.listen 0 4) .unit
  t6 ← mustStep "t6.gsn0" t6 (.getsockname 0) (.addr (.ipv6 0 0 55206 0 0))
  t6 ← mustStep "t6.s1" t6 (.socket .inet6 .stream nbFlags 0) (.opened 1)
  t6 ← mustStep "t6.conn1" t6 (.connect 1 (.ipv6 0 1 55206 0 0)) (.err Errno.EINPROGRESS)
  t6 ← mustStep "t6.acc" t6 (.accept4 0 nbFlags) (.accepted 2 (.ipv6 0 1 49158 0 0))
  let _ ← mustStep "t6.rx1.eagain" t6 (.recvfrom 1 8 { dontwait := true }) (.err Errno.EAGAIN)
  t6 ← mustStep "t6.loDown" t6 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  t6 ← mustStep "t6.sh1.wr" t6 (.shutdown 1 .wr) .unit
  t6 ← mustStep "t6.loUp" t6 (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let _ ← mustStep "t6.sh1.rd.unit" t6 (.shutdown 1 .rd) .unit
  let _ ← mustStep "t6.sh2.rd.unit" t6 (.shutdown 2 .rd) .unit
  let mut t6v4 ← mustStep "t6v4.s0" s0 (.socket .inet6 .stream blkFlags 0) (.opened 0)
  t6v4 ← mustStep "t6v4.taint" t6v4 (.connect 0 (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 1 0 0)) (.err Errno.ECONNREFUSED)
  t6v4 ← mustStep "t6v4.sh0" t6v4 (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  t6v4 ← mustStep "t6v4.lis0" t6v4 (.listen 0 4) .unit
  t6v4 ← mustStep "t6v4.gsn0" t6v4 (.getsockname 0) (.addr (.ipv6 0 0 55207 0 0))
  t6v4 ← mustStep "t6v4.s1" t6v4 (.socket .inet .stream nbFlags 0) (.opened 1)
  t6v4 ← mustStep "t6v4.conn1" t6v4 (.connect 1 (.ipv4 INADDR_LOOPBACK 55207)) (.err Errno.EINPROGRESS)
  let _ ← mustStep "t6v4.rx1.eof" t6v4 (.recvfrom 1 8 { dontwait := true }) (.bytes ByteArray.empty)

private def runV6SelfShutBindLoDownTests : IO Unit := do
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match Net.allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"v6 self-shut lo-down bind parity: model rejected {lbl}: req={repr req} out={repr out}")
  let mustReject (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO Unit :=
    assertTrue s!"v6 self-shut lo-down bind parity: {lbl} should reject" ((Net.allowedStep s req out).isNone)
  let s0 := NetState.initial true
  let ep : UInt16 := 50715
  let lo6Ep : SockAddr := .ipv6 0 1 ep 0 0
  let lo6Zero : SockAddr := .ipv6 0 1 0 0 0
  let any6Ep : SockAddr := .ipv6 0 0 ep 0 0
  let any6Zero : SockAddr := .ipv6 0 0 0 0 0
  let mut ci ← mustStep "ci.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ci ← mustStep "ci.bind0" ci (.bind 0 (.ipv6 0 1 0 74565 7)) .unit
  ci ← mustStep "ci.gsn0" ci (.getsockname 0) (.addr lo6Ep)
  ci ← mustStep "ci.shutWr" ci (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  ci ← mustStep "ci.connSelf" ci (.connect 0 lo6Ep) (.err Errno.EINPROGRESS)
  mustReject "loUp bind ::1:ep rejects EADDRNOTAVAIL" ci (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  mustReject "loUp bind ::1:0 rejects EADDRNOTAVAIL" ci (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "loUp bind ::1:ep EADDRINUSE" ci (.bind 0 lo6Ep) (.err Errno.EADDRINUSE)
  let _ ← mustStep "loUp bind ::1:0 unit" ci (.bind 0 lo6Zero) .unit
  let ciDown ← mustStep "ci.loDown" ci (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  let ciAfter ← mustStep "ci.bind7 EADDRNOTAVAIL" ciDown (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  mustReject "ci loDown bind ::1:ep rejects unit" ciDown (.bind 0 lo6Ep) .unit
  mustReject "ci loDown bind ::1:0 rejects unit" ciDown (.bind 0 lo6Zero) .unit
  let _ ← mustStep "ci loDown bind ::1:0 EADDRNOTAVAIL" ciDown (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let ciGsn ← mustStep "ci after EADDRNOTAVAIL gsn" ciAfter (.getsockname 0) (.addr lo6Ep)
  let _ ← mustStep "ci after EADDRNOTAVAIL soErr" ciGsn (.getsockopt 0 .error) (.u32 0)
  let _ ← mustStep "ci after EADDRNOTAVAIL conn" ciGsn (.connect 0 lo6Ep) (.err Errno.ECONNABORTED)
  let _ ← mustStep "ci after EADDRNOTAVAIL shutRd" ciGsn (.shutdown 0 .rd) (.err Errno.ENOTCONN)
  mustReject "ci loDown bind [::]:0 rejects EADDRNOTAVAIL" ciAfter (.bind 0 any6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "ci loDown bind [::]:0 unit" ciAfter (.bind 0 any6Zero) .unit
  let ciInUse ← mustStep "ci loDown bind [::]:ep EADDRINUSE" ciAfter (.bind 0 any6Ep) (.err Errno.EADDRINUSE)
  let _ ← mustStep "ci after EADDRINUSE gsn cleared to ::" ciInUse (.getsockname 0) (.addr any6Ep)
  let ciConnUnit ← mustStep "ciUnit.connSelf" (← mustStep "ciUnit.shutWr" (← mustStep "ciUnit.gsn" (← mustStep "ciUnit.bind" (← mustStep "ciUnit.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)) (.bind 0 lo6Zero) .unit) (.getsockname 0) (.addr lo6Ep)) (.shutdown 0 .wr) (.err Errno.ENOTCONN)) (.connect 0 lo6Ep) .unit
  let ciUnitDown ← mustStep "ciUnit.loDown" ciConnUnit (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  mustReject "ciUnit loDown bind ::1:0 rejects unit" ciUnitDown (.bind 0 lo6Zero) .unit
  let _ ← mustStep "ciUnit loDown bind ::1:0 EADDRNOTAVAIL" ciUnitDown (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let mut bnd ← mustStep "bnd.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  bnd ← mustStep "bnd.bind" bnd (.bind 0 lo6Zero) .unit
  bnd ← mustStep "bnd.gsn" bnd (.getsockname 0) (.addr lo6Ep)
  let bndDown ← mustStep "bnd.loDown" bnd (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "already-bound loDown ::1:ep rejects EADDRNOTAVAIL" bndDown (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  mustReject "already-bound loDown ::1:0 rejects EADDRNOTAVAIL" bndDown (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "already-bound loDown ::1:ep EINVAL" bndDown (.bind 0 lo6Ep) (.err Errno.EINVAL)
  let mut locked ← mustStep "locked.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  locked ← mustStep "locked.bind" locked (.bind 0 (.ipv6 0 1 41234 0 0)) .unit
  locked ← mustStep "locked.shut" locked (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  locked ← mustStep "locked.conn" locked (.connect 0 (.ipv6 0 1 41234 0 0)) (.err Errno.EINPROGRESS)
  let lockedDown ← mustStep "locked.loDown" locked (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "port-locked loDown ::1:41234 rejects EADDRNOTAVAIL" lockedDown (.bind 0 (.ipv6 0 1 41234 0 0)) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "port-locked loDown EINVAL" lockedDown (.bind 0 (.ipv6 0 1 41234 0 0)) (.err Errno.EINVAL)
  let mut est ← mustStep "est.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  est ← mustStep "est.bind" est (.bind 0 lo6Zero) .unit
  est ← mustStep "est.gsn" est (.getsockname 0) (.addr lo6Ep)
  est ← mustStep "est.conn" est (.connect 0 lo6Ep) (.err Errno.EINPROGRESS)
  let estDown ← mustStep "est.loDown" est (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "established loDown ::1:ep rejects EADDRNOTAVAIL" estDown (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "established loDown EINVAL" estDown (.bind 0 lo6Ep) (.err Errno.EINVAL)
  let mut lis ← mustStep "lis.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  lis ← mustStep "lis.listen" lis (.listen 0 4) .unit
  let lisDown ← mustStep "lis.loDown" lis (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "listener loDown ::1:0 rejects EADDRNOTAVAIL" lisDown (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let mut udp6 ← mustStep "udp6.s0" s0 (.socket .inet6 .dgram nbFlags 0) (.opened 0)
  udp6 ← mustStep "udp6.bind" udp6 (.bind 0 lo6Zero) .unit
  let udp6Down ← mustStep "udp6.loDown" udp6 (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "udp6 bound loDown ::1:0 rejects EADDRNOTAVAIL" udp6Down (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let mut ref ← mustStep "ref.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ref ← mustStep "ref.conn" ref (.connect 0 (.ipv6 0 1 49999 0 0)) (.err Errno.EINPROGRESS)
  mustReject "refused loUp bind ::1:49999 rejects EADDRNOTAVAIL" ref (.bind 0 (.ipv6 0 1 49999 0 0)) (.err Errno.EADDRNOTAVAIL)
  let refDown ← mustStep "ref.loDown" ref (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "refused loDown bind ::1:49999 rejects unit" refDown (.bind 0 (.ipv6 0 1 49999 0 0)) .unit
  let _ ← mustStep "refused loDown bind ::1:49999 EADDRNOTAVAIL" refDown (.bind 0 (.ipv6 0 1 49999 0 0)) (.err Errno.EADDRNOTAVAIL)
  let mut cw ← mustStep "cw.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  cw ← mustStep "cw.bind" cw (.bind 0 lo6Zero) .unit
  cw ← mustStep "cw.gsn" cw (.getsockname 0) (.addr (.ipv6 0 1 55290 0 0))
  cw ← mustStep "cw.lis" cw (.listen 0 4) .unit
  cw ← mustStep "cw.s1" cw (.socket .inet6 .stream nbFlags 0) (.opened 1)
  cw ← mustStep "cw.conn" cw (.connect 1 (.ipv6 0 1 55290 0 0)) (.err Errno.EINPROGRESS)
  cw ← mustStep "cw.acc" cw (.accept4 0 nbFlags) (.accepted 2 (.ipv6 0 1 49290 0 0))
  cw ← mustStep "cw.send" cw (.sendto 2 (ByteArray.mk #[65, 66]) {}) (.u32 2)
  cw ← mustStep "cw.shut1" cw (.shutdown 1 .rdwr) .unit
  mustReject "finWait loUp bind ::1:0 rejects EADDRNOTAVAIL" cw (.bind 1 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  mustReject "closeWait loUp bind ::1:0 rejects EADDRNOTAVAIL" cw (.bind 2 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let cwDown ← mustStep "cw.loDown" cw (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "finWait loDown bind ::1:0 rejects unit" cwDown (.bind 1 lo6Zero) .unit
  let _ ← mustStep "finWait loDown bind ::1:0 EADDRNOTAVAIL" cwDown (.bind 1 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  mustReject "closeWait loDown bind ::1:0 rejects unit" cwDown (.bind 2 lo6Zero) .unit
  let _ ← mustStep "closeWait loDown bind ::1:0 EADDRNOTAVAIL" cwDown (.bind 2 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let cwInUse ← mustStep "closeWait bind [::]:55290 EADDRINUSE" cwDown (.bind 2 (.ipv6 0 0 55290 0 0)) (.err Errno.EADDRINUSE)
  let _ ← mustStep "closeWait after EADDRINUSE gsn cleared to ::" cwInUse (.getsockname 2) (.addr (.ipv6 0 0 55290 0 0))
  let mut v4 ← mustStep "v4.s0" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
  v4 ← mustStep "v4.bind" v4 (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) .unit
  v4 ← mustStep "v4.gsn" v4 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 50716))
  v4 ← mustStep "v4.shut" v4 (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  v4 ← mustStep "v4.conn" v4 (.connect 0 (.ipv4 INADDR_LOOPBACK 50716)) (.err Errno.EINPROGRESS)
  let v4Down ← mustStep "v4.loDown" v4 (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "v4 loDown 127.0.0.1:ep rejects EADDRNOTAVAIL" v4Down (.bind 0 (.ipv4 INADDR_LOOPBACK 50716)) (.err Errno.EADDRNOTAVAIL)
  mustReject "v4 loDown 127.0.0.1:0 rejects EADDRNOTAVAIL" v4Down (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "v4 loDown 127.0.0.1:ep EADDRINUSE" v4Down (.bind 0 (.ipv4 INADDR_LOOPBACK 50716)) (.err Errno.EADDRINUSE)
  let _ ← mustStep "v4 loDown 127.0.0.1:0 unit" v4Down (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) .unit
  let mappedLoZero : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0
  let mappedLoEp : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) ep 0 0
  mustReject "ci loDown(wasUp) mapped ::ffff:127.0.0.1:0 rejects EADDRNOTAVAIL" ciDown (.bind 0 mappedLoZero) (.err Errno.EADDRNOTAVAIL)
  mustReject "ci loDown(wasUp) mapped ::ffff:127.0.0.1:ep rejects EADDRNOTAVAIL" ciDown (.bind 0 mappedLoEp) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "ci loDown(wasUp) mapped ::ffff:127.0.0.1:0 unit" ciDown (.bind 0 mappedLoZero) .unit
  let _ ← mustStep "ci loDown(wasUp) mapped ::ffff:127.0.0.1:0 EINVAL" ciDown (.bind 0 mappedLoZero) (.err Errno.EINVAL)
  let _ ← mustStep "ci loDown(wasUp) mapped ::ffff:127.0.0.1:ep EADDRINUSE" ciDown (.bind 0 mappedLoEp) (.err Errno.EADDRINUSE)
  let _ ← mustStep "ci loDown(wasUp) mapped ::ffff:127.0.0.1:ep EINVAL" ciDown (.bind 0 mappedLoEp) (.err Errno.EINVAL)
  let mut ciMapped ← mustStep "ciMapped.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ciMapped ← mustStep "ciMapped.bind" ciMapped (.bind 0 mappedLoZero) .unit
  ciMapped ← mustStep "ciMapped.gsn" ciMapped (.getsockname 0) (.addr mappedLoEp)
  ciMapped ← mustStep "ciMapped.shut" ciMapped (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  ciMapped ← mustStep "ciMapped.conn" ciMapped (.connect 0 mappedLoEp) (.err Errno.EINPROGRESS)
  let ciMappedDown ← mustStep "ciMapped.loDown" ciMapped (.ioctl 0 (.setIfFlags 8) loIfname) (.u32 0)
  mustReject "mapped loDown(wasUp) ::ffff:127.0.0.1:0 rejects EADDRNOTAVAIL" ciMappedDown (.bind 0 mappedLoZero) (.err Errno.EADDRNOTAVAIL)
  mustReject "mapped loDown(wasUp) ::ffff:127.0.0.1:ep rejects EADDRNOTAVAIL" ciMappedDown (.bind 0 mappedLoEp) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "mapped loDown(wasUp) ::ffff:127.0.0.1:0 unit" ciMappedDown (.bind 0 mappedLoZero) .unit
  let ciMappedInUse ← mustStep "mapped loDown(wasUp) ::ffff:127.0.0.1:ep EADDRINUSE" ciMappedDown (.bind 0 mappedLoEp) (.err Errno.EADDRINUSE)
  let _ ← mustStep "mapped loDown(wasUp) after EADDRINUSE gsn cleared to ::" ciMappedInUse (.getsockname 0) (.addr any6Ep)
  mustReject "mapped loDown(wasUp) ::1:0 rejects unit" ciMappedDown (.bind 0 lo6Zero) .unit
  let _ ← mustStep "mapped loDown(wasUp) ::1:0 EADDRNOTAVAIL" ciMappedDown (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "mapped loDown(wasUp) ::1:ep EADDRNOTAVAIL" ciMappedDown (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  let sNeverUp := NetState.initialNetns
  let mut refNeverUp ← mustStep "neverUp.s0" sNeverUp (.socket .inet6 .stream nbFlags 0) (.opened 0)
  refNeverUp ← mustStep "neverUp.conn" refNeverUp (.connect 0 (.ipv6 0 (ipv4ToMappedV6Lo 0x0a000002) 49999 0 0)) (.err Errno.EINPROGRESS)
  mustReject "neverUp ::1:0 rejects unit" refNeverUp (.bind 0 lo6Zero) .unit
  let _ ← mustStep "neverUp ::1:0 EADDRNOTAVAIL" refNeverUp (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "neverUp ::1:ep EADDRNOTAVAIL" refNeverUp (.bind 0 lo6Ep) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "neverUp mapped ::ffff:127.0.0.1:0 unit" refNeverUp (.bind 0 mappedLoZero) .unit
  let _ ← mustStep "neverUp mapped ::ffff:127.0.0.1:0 EADDRNOTAVAIL" refNeverUp (.bind 0 mappedLoZero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "neverUp mapped ::ffff:127.0.0.1:ep EADDRNOTAVAIL" refNeverUp (.bind 0 mappedLoEp) (.err Errno.EADDRNOTAVAIL)
  let refUp ← mustStep "neverUp.loUp" refNeverUp (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  let refWasUp ← mustStep "neverUp.loDown" refUp (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  mustReject "wasUp mapped ::ffff:127.0.0.1:0 rejects EADDRNOTAVAIL" refWasUp (.bind 0 mappedLoZero) (.err Errno.EADDRNOTAVAIL)
  mustReject "wasUp mapped ::ffff:127.0.0.1:ep rejects EADDRNOTAVAIL" refWasUp (.bind 0 mappedLoEp) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "wasUp mapped ::ffff:127.0.0.1:0 unit" refWasUp (.bind 0 mappedLoZero) .unit
  mustReject "wasUp ::1:0 rejects unit" refWasUp (.bind 0 lo6Zero) .unit
  let _ ← mustStep "wasUp ::1:0 EADDRNOTAVAIL" refWasUp (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let mut ext ← mustStep "ext.s0" s0 (.socket .inet6 .stream nbFlags 0) (.opened 0)
  ext ← mustStep "ext.conn" ext (.connect 0 (.ipv6 0xfe80000000000000 1 49998 0 2)) (.err Errno.EINPROGRESS)
  mustReject "ext mcast ff02::1 rejects EADDRNOTAVAIL" ext (.bind 0 (.ipv6 0xff02000000000000 1 0 0 2)) (.err Errno.EADDRNOTAVAIL)
  mustReject "ext lo6 rejects unit" ext (.bind 0 lo6Zero) .unit
  let _ ← mustStep "ext lo6 EADDRNOTAVAIL" ext (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let sUnpin := NetState.initialUnpinned false
  let mut unp ← mustStep "unp.s0" sUnpin (.socket .inet6 .stream nbFlags 0) (.opened 0)
  unp ← mustStep "unp.bind" unp (.bind 0 lo6Zero) .unit
  unp ← mustStep "unp.gsn" unp (.getsockname 0) (.addr lo6Ep)
  unp ← mustStep "unp.shut" unp (.shutdown 0 .wr) (.err Errno.ENOTCONN)
  unp ← mustStep "unp.conn" unp (.connect 0 lo6Ep) (.err Errno.EINPROGRESS)
  let _ ← mustStep "unp lo6:0 unit" unp (.bind 0 lo6Zero) .unit
  let _ ← mustStep "unp lo6:0 EADDRNOTAVAIL" unp (.bind 0 lo6Zero) (.err Errno.EADDRNOTAVAIL)
  let _ ← mustStep "unp mapped ::ffff:127.0.0.1:0 unit" unp (.bind 0 mappedLoZero) .unit
  let _ ← mustStep "unp mapped ::ffff:127.0.0.1:0 EADDRNOTAVAIL" unp (.bind 0 mappedLoZero) (.err Errno.EADDRNOTAVAIL)

private def runTcpDisconnectRxPurgeTests : IO Unit := do
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match Net.allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"tcp disconnect rx purge: model rejected {lbl}: req={repr req} out={repr out}")
  let mustReject (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO Unit :=
    assertTrue s!"tcp disconnect rx purge: {lbl} should reject" ((Net.allowedStep s req out).isNone)
  let s0 := NetState.initial true
  let blkFlags : SockFlags := { nonblock := false, cloexec := true }
  let p0 : UInt16 := 44100
  let p1 : UInt16 := 51234
  let p1b : UInt16 := 51235
  let lisAddr6 : SockAddr := .ipv6 0 0 p0 0 0
  let dstV4 : SockAddr := .ipv4 INADDR_LOOPBACK p0
  let cliV4 : SockAddr := .ipv4 INADDR_LOOPBACK p1
  let peerV6Mapped : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p1 0 0
  let peerV6Mapped2 : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p1b 0 0
  let b206 : ByteArray := ByteArray.mk #[206]
  let b170 : ByteArray := ByteArray.mk #[170]
  let b99 : ByteArray := ByteArray.mk #[99]
  let mkPostRst (nbClient completeEarly : Bool) : IO NetState := do
    let mut st ← mustStep "s0" s0 (.socket .inet6 .stream blkFlags 0) (.opened 0)
    st ← mustStep "s1" st (.socket .inet .stream { nonblock := nbClient, cloexec := true } 0) (.opened 1)
    st ← mustStep "lis" st (.listen 0 0) .unit
    st ← mustStep "gsn0" st (.getsockname 0) (.addr lisAddr6)
    st ← mustStep "conn1" st (.connect 1 dstV4) (if nbClient then .err Errno.EINPROGRESS else .unit)
    st ← mustStep "gsn1" st (.getsockname 1) (.addr cliV4)
    st ← mustStep "acc" st (.accept4 0 nbFlags) (.accepted 2 peerV6Mapped)
    if completeEarly then
      st ← mustStep "conn1.early" st (.connect 1 dstV4) .unit
    st ← mustStep "send2" st (.sendto 2 b206 {}) (.u32 1)
    st ← assertOk "close2" (NetState.closeHandle st 2)
    mustStep "send1" st (.sendto 1 b170 {}) (.u32 1)
  let st1 ← mkPostRst true false
  mustReject "pre-conn rx(0) rejects ENOTCONN" st1 (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  mustReject "pre-conn rx(1024) rejects ENOTCONN" st1 (.recvfrom 1 1024 { dontwait := true }) (.err Errno.ENOTCONN)
  let _ ← mustStep "pre-conn rx(0) empty" st1 (.recvfrom 1 0 {}) (.bytes ByteArray.empty)
  let _ ← mustStep "pre-conn rx(1024) 206" st1 (.recvfrom 1 1024 { dontwait := true }) (.bytes b206)
  let stDisc ← mustStep "conn1.self EPIPE" st1 (.connect 1 cliV4) (.err Errno.EPIPE)
  let _ ← mustStep "post-disc rx(0) ENOTCONN" stDisc (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-disc rx(1024,dw) ENOTCONN" stDisc (.recvfrom 1 1024 { dontwait := true }) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-disc rx(1024,blk) ENOTCONN" stDisc (.recvfrom 1 1024 {}) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-disc recvmsg ENOTCONN" stDisc (.recvmsg 1 1) (.err Errno.ENOTCONN)
  mustReject "post-disc rx(0) rejects empty" stDisc (.recvfrom 1 0 {}) (.bytes ByteArray.empty)
  mustReject "post-disc rx(1024) rejects stale 206" stDisc (.recvfrom 1 1024 { dontwait := true }) (.bytes b206)
  mustReject "post-disc rx(1024) rejects empty" stDisc (.recvfrom 1 1024 { dontwait := true }) (.bytes ByteArray.empty)
  mustReject "post-disc rx(1024) rejects EAGAIN" stDisc (.recvfrom 1 1024 { dontwait := true }) (.err Errno.EAGAIN)
  mustReject "post-disc recvmsg rejects empty fds" stDisc (.recvmsg 1 1) (.fds #[])
  let mut stRec ← mustStep "reconn" stDisc (.connect 1 dstV4) (.err Errno.EINPROGRESS)
  stRec ← mustStep "reconn.acc" stRec (.accept4 0 nbFlags) (.accepted 3 peerV6Mapped2)
  mustReject "reconn pre-send rx rejects stale 206" stRec (.recvfrom 1 16 { dontwait := true }) (.bytes b206)
  let _ ← mustStep "reconn pre-send rx EAGAIN" stRec (.recvfrom 1 16 { dontwait := true }) (.err Errno.EAGAIN)
  stRec ← mustStep "reconn send3 99" stRec (.sendto 3 b99 {}) (.u32 1)
  mustReject "reconn post-send rx rejects stale 206" stRec (.recvfrom 1 16 { dontwait := true }) (.bytes b206)
  let _ ← mustStep "reconn post-send rx 99" stRec (.recvfrom 1 16 { dontwait := true }) (.bytes b99)
  let stSo ← mustStep "soErr EPIPE" st1 (.getsockopt 1 .error) (.u32 Errno.EPIPE)
  mustReject "post-soErr pre-conn rx(0) rejects ENOTCONN" stSo (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  mustReject "post-soErr pre-conn rx(16) rejects ENOTCONN" stSo (.recvfrom 1 16 { dontwait := true }) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-soErr pre-conn rx(0) empty" stSo (.recvfrom 1 0 {}) (.bytes ByteArray.empty)
  let _ ← mustStep "post-soErr pre-conn rx(16,peek) 206" stSo (.recvfrom 1 16 { dontwait := true, peek := true }) (.bytes b206)
  let stAb ← mustStep "post-soErr conn ECONNABORTED" stSo (.connect 1 cliV4) (.err Errno.ECONNABORTED)
  let _ ← mustStep "post-abort rx(0) ENOTCONN" stAb (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-abort rx(16) ENOTCONN" stAb (.recvfrom 1 16 { dontwait := true }) (.err Errno.ENOTCONN)
  mustReject "post-abort rx(16) rejects stale 206" stAb (.recvfrom 1 16 { dontwait := true }) (.bytes b206)
  mustReject "post-abort rx(0) rejects empty" stAb (.recvfrom 1 0 {}) (.bytes ByteArray.empty)
  let mut stUnr ← mustStep "unr.s0" s0 (.socket .inet6 .stream blkFlags 0) (.opened 0)
  stUnr ← mustStep "unr.s1" stUnr (.socket .inet .stream nbFlags 0) (.opened 1)
  stUnr ← mustStep "unr.lis" stUnr (.listen 0 0) .unit
  stUnr ← mustStep "unr.gsn0" stUnr (.getsockname 0) (.addr lisAddr6)
  stUnr ← mustStep "unr.conn1" stUnr (.connect 1 dstV4) (.err Errno.EINPROGRESS)
  stUnr ← mustStep "unr.gsn1" stUnr (.getsockname 1) (.addr cliV4)
  stUnr ← mustStep "unr.acc" stUnr (.accept4 0 nbFlags) (.accepted 2 peerV6Mapped)
  stUnr ← mustStep "unr.send2" stUnr (.sendto 2 b206 {}) (.u32 1)
  stUnr ← mustStep "unr.send1" stUnr (.sendto 1 b170 {}) (.u32 1)
  stUnr ← assertOk "unr.close2" (NetState.closeHandle stUnr 2)
  let stUnrDisc ← mustStep "unr.conn ECONNRESET" stUnr (.connect 1 dstV4) (.err Errno.ECONNRESET)
  let _ ← mustStep "unr post-disc rx(0) ENOTCONN" stUnrDisc (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  let _ ← mustStep "unr post-disc rx(16) ENOTCONN" stUnrDisc (.recvfrom 1 16 { dontwait := true }) (.err Errno.ENOTCONN)
  mustReject "unr post-disc rx(16) rejects stale 206" stUnrDisc (.recvfrom 1 16 { dontwait := true }) (.bytes b206)
  mustReject "unr post-disc rx(0) rejects empty" stUnrDisc (.recvfrom 1 0 {}) (.bytes ByteArray.empty)
  let dstV6 : SockAddr := .ipv6 0 1 44101 0 0
  let peerV6 : SockAddr := .ipv6 0 1 51236 0 0
  let mut stV6 ← mustStep "v6.s0" s0 (.socket .inet6 .stream blkFlags 0) (.opened 0)
  stV6 ← mustStep "v6.bind" stV6 (.bind 0 (.ipv6 0 1 0 0 0)) .unit
  stV6 ← mustStep "v6.gsn0" stV6 (.getsockname 0) (.addr dstV6)
  stV6 ← mustStep "v6.lis" stV6 (.listen 0 4) .unit
  stV6 ← mustStep "v6.s1" stV6 (.socket .inet6 .stream nbFlags 0) (.opened 1)
  stV6 ← mustStep "v6.conn1" stV6 (.connect 1 dstV6) (.err Errno.EINPROGRESS)
  stV6 ← mustStep "v6.acc" stV6 (.accept4 0 nbFlags) (.accepted 2 peerV6)
  stV6 ← mustStep "v6.send2" stV6 (.sendto 2 b206 {}) (.u32 1)
  stV6 ← mustStep "v6.loDown" stV6 (.ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 0)
  stV6 ← mustStep "v6.send1.down" stV6 (.sendto 1 b170 {}) (.u32 1)
  stV6 ← mustStep "v6.loUp" stV6 (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  stV6 ← assertOk "v6.close2" (NetState.closeHandle stV6 2)
  let stV6Disc ← mustStep "v6.conn ECONNRESET" stV6 (.connect 1 dstV6) (.err Errno.ECONNRESET)
  mustReject "v6 post-disc soErr rejects stale ENETUNREACH" stV6Disc (.getsockopt 1 .error) (.u32 Errno.ENETUNREACH)
  let _ ← mustStep "v6 post-disc soErr 0" stV6Disc (.getsockopt 1 .error) (.u32 0)
  let _ ← mustStep "v6 post-disc rx(16) ENOTCONN" stV6Disc (.recvfrom 1 16 { dontwait := true }) (.err Errno.ENOTCONN)
  mustReject "v6 post-disc rx(16) rejects stale 206" stV6Disc (.recvfrom 1 16 { dontwait := true }) (.bytes b206)
  mustReject "v6 post-disc rx(16) rejects EAGAIN" stV6Disc (.recvfrom 1 16 { dontwait := true }) (.err Errno.EAGAIN)
  let stBlk ← mkPostRst false false
  mustReject "blk conn rejects EPIPE" stBlk (.connect 1 cliV4) (.err Errno.EPIPE)
  let stBlkC ← mustStep "blk conn EISCONN" stBlk (.connect 1 cliV4) (.err Errno.EISCONN)
  mustReject "blk post-EISCONN rx(1024) rejects ENOTCONN" stBlkC (.recvfrom 1 1024 { dontwait := true }) (.err Errno.ENOTCONN)
  mustReject "blk post-EISCONN rx(0) rejects ENOTCONN" stBlkC (.recvfrom 1 0 {}) (.err Errno.ENOTCONN)
  let _ ← mustStep "blk post-EISCONN rx(1024) 206" stBlkC (.recvfrom 1 1024 { dontwait := true }) (.bytes b206)
  let stDone ← mkPostRst true true
  let stDoneC ← mustStep "early-done conn EISCONN" stDone (.connect 1 cliV4) (.err Errno.EISCONN)
  mustReject "early-done post-EISCONN rx(1024) rejects ENOTCONN" stDoneC (.recvfrom 1 1024 { dontwait := true }) (.err Errno.ENOTCONN)
  let _ ← mustStep "early-done post-EISCONN rx(1024) 206" stDoneC (.recvfrom 1 1024 { dontwait := true }) (.bytes b206)
  let stSh ← mustStep "shutRd ENOTCONN" st1 (.shutdown 1 .rd) (.err Errno.ENOTCONN)
  let stShC ← mustStep "post-shutRd conn EINVAL" stSh (.connect 1 cliV4) (.err Errno.EINVAL)
  mustReject "post-shutRd EINVAL rx(1024) rejects ENOTCONN" stShC (.recvfrom 1 1024 { dontwait := true }) (.err Errno.ENOTCONN)
  let _ ← mustStep "post-shutRd EINVAL rx(1024) 206" stShC (.recvfrom 1 1024 { dontwait := true }) (.bytes b206)

private def runUdpWildcardPeerResolveTests : IO Unit := do
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match Net.allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"udp wildcard peer resolve: model rejected {lbl}: req={repr req} out={repr out}")
  let mustReject (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO Unit :=
    assertTrue s!"udp wildcard peer resolve: {lbl} should reject" ((Net.allowedStep s req out).isNone)
  let s0 := NetState.initial true
  let blkFlags : SockFlags := { nonblock := false, cloexec := true }
  let p0 : UInt16 := 44200
  let p1 : UInt16 := 44201
  let v4m0 (p : UInt16) (sc : UInt32 := 0) : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_ANY) p 0 sc
  let v4m1 (p : UInt16) : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p 0 0
  let v4m2 (p : UInt16) : SockAddr := .ipv6 0 (ipv4ToMappedV6Lo 0x7f000002) p 0 0
  let mut st ← mustStep "249.s0" s0 (.socket .inet6 .dgram blkFlags 0) (.opened 0)
  st ← mustStep "249.bind0" st (.bind 0 (v4m0 0 7)) .unit
  st ← mustStep "249.gsn0" st (.getsockname 0) (.addr (v4m0 p0))
  st ← mustStep "249.s1" st (.socket .inet .dgram nbFlags 0) (.opened 1)
  st ← mustStep "249.bind1" st (.bind 1 (.ipv4 0x7f000002 0)) .unit
  st ← mustStep "249.gsn1" st (.getsockname 1) (.addr (.ipv4 0x7f000002 p1))
  st ← mustStep "249.conn1" st (.connect 1 (.ipv4 INADDR_ANY p0)) .unit
  let stUnconnSend ← mustStep "249.unconn.send1" st (.sendto 1 (asciiBytes ['u']) {}) (.u32 1)
  let _ ← mustStep "249.unconn.recv0" stUnconnSend (.recvfrom 0 8 { dontwait := true }) (.bytes (asciiBytes ['u']))
  mustReject "249.unconn.send1 rejects ECONNREFUSED" stUnconnSend (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  st ← mustStep "249.conn0" st (.connect 0 (v4m2 p1)) .unit
  st ← mustStep "249.gsn0.post" st (.getsockname 0) (.addr (v4m1 p0))
  let stTx1 ← mustStep "249.send1.1" st (.sendto 1 ByteArray.empty {}) (.u32 0)
  let _ ← mustStep "249.send1.2 ECONNREFUSED" stTx1 (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  mustReject "249.recv0 rejects empty delivery" stTx1 (.recvfrom 0 8 { dontwait := true }) (.bytes ByteArray.empty)
  let _ ← mustStep "249.recv0 EAGAIN" stTx1 (.recvfrom 0 8 { dontwait := true }) (.err Errno.EAGAIN)
  let stTx0 ← mustStep "249.send0.1" st (.sendto 0 (asciiBytes ['x']) { dontwait := true }) (.u32 1)
  let _ ← mustStep "249.send0.2 ECONNREFUSED" stTx0 (.sendto 0 (asciiBytes ['x']) { dontwait := true }) (.err Errno.ECONNREFUSED)
  mustReject "249.recv1 rejects x" stTx0 (.recvfrom 1 8 { dontwait := true }) (.bytes (asciiBytes ['x']))
  let stMatch ← mustStep "249.reconn1.127.0.0.1" st (.connect 1 (.ipv4 INADDR_LOOPBACK p0)) .unit
  let stMatch1 ← mustStep "249.match.send1" stMatch (.sendto 1 (asciiBytes ['a']) {}) (.u32 1)
  mustReject "249.match.send1 rejects ECONNREFUSED" stMatch1 (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  let stMatch2 ← mustStep "249.match.recv0" stMatch1 (.recvfrom 0 8 { dontwait := true }) (.bytes (asciiBytes ['a']))
  let stMatch3 ← mustStep "249.match.send0" stMatch2 (.sendto 0 (asciiBytes ['b']) { dontwait := true }) (.u32 1)
  let _ ← mustStep "249.match.recv1" stMatch3 (.recvfrom 1 8 { dontwait := true }) (.bytes (asciiBytes ['b']))
  let mut sv4 ← mustStep "v4.s0" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
  sv4 ← mustStep "v4.bind0" sv4 (.bind 0 (.ipv4 INADDR_LOOPBACK p0)) .unit
  sv4 ← mustStep "v4.s1" sv4 (.socket .inet .dgram nbFlags 0) (.opened 1)
  sv4 ← mustStep "v4.bind1" sv4 (.bind 1 (.ipv4 0x7f000002 p1)) .unit
  sv4 ← mustStep "v4.conn1" sv4 (.connect 1 (.ipv4 INADDR_ANY p0)) .unit
  let sv4Tx ← mustStep "v4.miss.send1" sv4 (.sendto 1 (asciiBytes ['m']) {}) (.u32 1)
  let _ ← mustStep "v4.miss.send2 ECONNREFUSED" sv4Tx (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  mustReject "v4.miss.recv0 rejects m" sv4Tx (.recvfrom 0 8 { dontwait := true }) (.bytes (asciiBytes ['m']))
  let mut sv6 ← mustStep "v6.s0" s0 (.socket .inet6 .dgram nbFlags 0) (.opened 0)
  sv6 ← mustStep "v6.bind0" sv6 (.bind 0 (v4m1 p0)) .unit
  sv6 ← mustStep "v6.s1" sv6 (.socket .inet6 .dgram nbFlags 0) (.opened 1)
  sv6 ← mustStep "v6.bind1" sv6 (.bind 1 (v4m2 p1)) .unit
  let sv6Miss ← mustStep "v6.conn.v4m0" sv6 (.connect 1 (v4m0 p0)) .unit
  let sv6MissTx ← mustStep "v6.miss.send1" sv6Miss (.sendto 1 (asciiBytes ['k']) {}) (.u32 1)
  let _ ← mustStep "v6.miss.send2 ECONNREFUSED" sv6MissTx (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  mustReject "v6.miss.recv0 rejects k" sv6MissTx (.recvfrom 0 8 { dontwait := true }) (.bytes (asciiBytes ['k']))
  let sv6Any ← mustStep "v6.conn.any6" sv6 (.connect 1 (.ipv6 0 0 p0 0 0)) .unit
  let sv6AnyTx ← mustStep "v6.any6.send1" sv6Any (.sendto 1 (asciiBytes ['k']) {}) (.u32 1)
  let _ ← mustStep "v6.any6.recv0" sv6AnyTx (.recvfrom 0 8 { dontwait := true }) (.bytes (asciiBytes ['k']))
  mustReject "v6.any6.send2 rejects ECONNREFUSED" sv6AnyTx (.sendto 1 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  let mut sNs ← mustStep "ns.s0" (NetState.initialNetns true) (.socket .inet .dgram nbFlags 0) (.opened 0)
  sNs ← mustStep "ns.bind0.down" sNs (.bind 0 (.ipv4 0x7f000002 p1)) .unit
  sNs ← mustStep "ns.loUp" sNs (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
  sNs ← mustStep "ns.s1" sNs (.socket .inet .dgram nbFlags 0) (.opened 1)
  sNs ← mustStep "ns.bind1" sNs (.bind 1 (.ipv4 INADDR_LOOPBACK p0)) .unit
  sNs ← mustStep "ns.conn0" sNs (.connect 0 (.ipv4 INADDR_ANY p0)) .unit
  let sNsTx ← mustStep "ns.send0" sNs (.sendto 0 (asciiBytes ['n']) {}) (.u32 1)
  let _ ← mustStep "ns.recv1" sNsTx (.recvfrom 1 8 { dontwait := true }) (.bytes (asciiBytes ['n']))
  mustReject "ns.send0 rejects ECONNREFUSED" sNsTx (.sendto 0 ByteArray.empty {}) (.err Errno.ECONNREFUSED)
  let mut sMc ← mustStep "mc.s0" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
  sMc ← mustStep "mc.bind0" sMc (.bind 0 (.ipv4 INADDR_ALLHOSTS_GROUP p1)) .unit
  sMc ← mustStep "mc.s1" sMc (.socket .inet .dgram nbFlags 0) (.opened 1)
  sMc ← mustStep "mc.bind1" sMc (.bind 1 (.ipv4 INADDR_LOOPBACK p0)) .unit
  sMc ← mustStep "mc.conn0" sMc (.connect 0 (.ipv4 INADDR_ANY p0)) .unit
  let sMcTx ← mustStep "mc.send0" sMc (.sendto 0 (asciiBytes ['c']) {}) (.u32 1)
  let _ ← mustStep "mc.recv1" sMcTx (.recvfrom 1 8 { dontwait := true }) (.bytes (asciiBytes ['c']))
  mustReject "mc.send0 rejects ECONNREFUSED" sMcTx (.sendto 0 ByteArray.empty {}) (.err Errno.ECONNREFUSED)

/-- Run all `Net` real and mocked regression and error-path checks (dispatched by `leanswe-fuzz --smoke`). -/
def runChecks : IO Unit := do
  assume_net_socket_domainTypeFlagsAbi
  assume_net_socketpair_unixPairAbi
  assume_net_bind_sockaddrTranslationAndNulGuard
  assume_net_listen_backlogAbi
  assume_net_accept4_flagsAndPeerAddrDecode
  assume_net_connect_nonblockAndSockaddrAbi
  assume_net_getsockopt_soErrorAndReuseAddrAbi
  assume_net_setsockopt_reuseAddrAbi
  assume_net_getsockname_sockaddrDecode
  assume_net_recvfrom_clamped16MiBAndMsgFlags
  assume_net_sendto_msgFlagsAndPartialCount
  assume_net_shutdown_shutHowAbi
  assume_net_sendmsg_scmRightsBatchAbi
  assume_net_recvmsg_scmRightsCloexecAndCapAbi
  assume_net_ioctl_ifreqFlagsAndIfnameBounds
  err_socket_invalidArg
  err_socket_mocked
  err_socket_transient
  err_socketpair_invalidArg
  err_socketpair_mocked
  err_socketpair_transient
  err_bind_badFd
  err_bind_invalidArg
  err_bind_addressError
  err_bind_permissionDenied
  err_bind_mocked
  err_bind_transient
  err_listen_badFd
  err_listen_invalidArg
  err_listen_addressError
  err_listen_mocked
  err_listen_transient
  err_accept4_badFd
  err_accept4_invalidArg
  err_accept4_wouldBlock
  err_accept4_mocked
  err_accept4_transient
  err_connect_badFd
  err_connect_invalidArg
  err_connect_addressError
  err_connect_inProgress
  err_connect_connectionState
  err_connect_mocked
  err_connect_transient
  err_getsockopt_badFd
  err_getsockopt_mocked
  err_getsockopt_transient
  err_setsockopt_badFd
  err_setsockopt_mocked
  err_setsockopt_transient
  err_getsockname_badFd
  err_getsockname_mocked
  err_getsockname_transient
  err_recvfrom_badFd
  err_recvfrom_invalidArg
  err_recvfrom_wouldBlock
  err_recvfrom_connectionState
  err_recvfrom_mocked
  err_recvfrom_transient
  err_sendto_badFd
  err_sendto_invalidArg
  err_sendto_wouldBlock
  err_sendto_connectionState
  err_sendto_mocked
  err_sendto_transient
  err_shutdown_badFd
  err_shutdown_connectionState
  err_shutdown_mocked
  err_shutdown_transient
  err_sendmsg_badFd
  err_sendmsg_invalidArg
  err_sendmsg_connectionState
  err_sendmsg_mocked
  err_sendmsg_transient
  err_recvmsg_badFd
  err_recvmsg_invalidArg
  err_recvmsg_wouldBlock
  err_recvmsg_connectionState
  err_recvmsg_mocked
  err_recvmsg_transient
  err_ioctl_badFd
  err_ioctl_invalidArg
  err_ioctl_addressError
  err_ioctl_permissionDenied
  err_ioctl_mocked
  err_ioctl_transient
  if ← isLoopbackUp defaultOps then
    runUnixScmAndConnectResetTests
    runDualStackShutdownAndUnixFsTests
    runMulticastAndV6SelfShutTests
  runPreShutCloseWaitLoFlapTests
  runV6SelfShutBindLoDownTests
  runTcpDisconnectRxPurgeTests
  runUdpWildcardPeerResolveTests
  runDefaultWrapperFlagsTests
  runStickyScopeMappedWildcardAndUntaintTests
  runMcastScopeAndSynResetTests
  runTaintedAbortLastAckAndMcastRoutedTests
  runShimAndFdBoxEdgeTests

private def parseInjectedErrno (s : String) : Errno :=
  match s with
  | "EINTR" => Errno.EINTR
  | "ENOMEM" => Errno.ENOMEM
  | "EIO" => Errno.EIO
  | "ENFILE" => Errno.ENFILE
  | "EAGAIN" => Errno.EAGAIN
  | _ => 0

private def expectStraceClose (label : String) (fd : RawFd) : IO Unit := do
  match ← rawNetClose fd with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{label}: post-error close failed (unpin leak?): {e}")

private def modelStepOrThrow (label : String) (s : NetState) (req : NetReq) (out : NetOutcome) :
    IO NetState := do
  match Net.allowedStep s req out with
  | some s' => return s'
  | none => throw (IO.userError s!"{label}: model setup step failed")

private def runStraceAction (syscallName : String) : IO (NetState × NetReq × Except Errno Unit) := do
  let ops := defaultOps
  let s0 := NetState.initial false
  match syscallName with
  | "socket" =>
    let req := NetReq.socket .inet .stream nbFlags 0
    match ← ops.socket .inet .stream nbFlags 0 with
    | .ok fd => expectStraceClose "strace socket" fd; return (s0, req, .ok ())
    | .error e => return (s0, req, .error e)
  | "socketpair" =>
    let req := NetReq.socketpair .unix .stream nbFlags
    match ← ops.socketpair .unix .stream nbFlags with
    | .ok (a, b) =>
      expectStraceClose "strace sp a" a
      expectStraceClose "strace sp b" b
      return (s0, req, .ok ())
    | .error e => return (s0, req, .error e)
  | "bind" =>
    let fd ← assertOk "strace bind sock" (← ops.socket .inet .dgram nbFlags 0)
    let s1 ← modelStepOrThrow "strace bind" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
    let req := NetReq.bind 0 (.ipv4 INADDR_LOOPBACK 0)
    let res ← try
      match ← ops.bind fd (.ipv4 INADDR_LOOPBACK 0) with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace bind" fd
    return (s1, req, res)
  | "listen" =>
    let fd ← assertOk "strace listen sock" (← ops.socket .inet .stream nbFlags 0)
    let s1 ← modelStepOrThrow "strace listen" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
    let req := NetReq.listen 0 4
    let res ← try
      match ← ops.listen fd 4 with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace listen" fd
    return (s1, req, res)
  | "accept4" =>
    let fd ← assertOk "strace accept4 sock" (← ops.socket .inet .stream nbFlags 0)
    let s1 ← modelStepOrThrow "strace accept4 sock" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
    let req := NetReq.accept4 0 nbFlags
    let (s2, res) ← try
      assertOk "strace accept4 listen" (← ops.listen fd 4)
      let s2 ← modelStepOrThrow "strace accept4 listen" s1 (.listen 0 4) .unit
      match ← ops.accept4 fd nbFlags with
      | .ok (c, _) => expectStraceClose "strace accept4 cli" c; pure (s2, .ok ())
      | .error e => pure (s2, .error e)
    finally
      expectStraceClose "strace accept4 lis" fd
    return (s2, req, res)
  | "connect" =>
    let fd ← assertOk "strace connect sock" (← ops.socket .inet .dgram nbFlags 0)
    let s1 ← modelStepOrThrow "strace connect" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
    let req := NetReq.connect 0 (.ipv4 INADDR_LOOPBACK 1)
    let res ← try
      match ← ops.connect fd (.ipv4 INADDR_LOOPBACK 1) with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace connect" fd
    return (s1, req, res)
  | "getsockopt" =>
    let fd ← assertOk "strace gso sock" (← ops.socket .inet .stream nbFlags 0)
    let s1 ← modelStepOrThrow "strace gso" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
    let req := NetReq.getsockopt 0 .error
    let res ← try
      match ← ops.getsockopt fd .error with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace gso" fd
    return (s1, req, res)
  | "setsockopt" =>
    let fd ← assertOk "strace sso sock" (← ops.socket .inet .stream nbFlags 0)
    let s1 ← modelStepOrThrow "strace sso" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
    let req := NetReq.setsockopt 0 .reuseAddr 1
    let res ← try
      match ← ops.setsockopt fd .reuseAddr 1 with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace sso" fd
    return (s1, req, res)
  | "getsockname" =>
    let fd ← assertOk "strace gsn sock" (← ops.socket .inet .stream nbFlags 0)
    let s1 ← modelStepOrThrow "strace gsn" s0 (.socket .inet .stream nbFlags 0) (.opened 0)
    let req := NetReq.getsockname 0
    let res ← try
      match ← ops.getsockname fd with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace gsn" fd
    return (s1, req, res)
  | "recvfrom" =>
    let (a, b) ← assertOk "strace rx pair" (← ops.socketpair .unix .stream nbFlags)
    let s1 ← modelStepOrThrow "strace rx" s0 (.socketpair .unix .stream nbFlags) (.pair 0 1)
    let req := NetReq.recvfrom 0 16 { dontwait := true }
    let res ← try
      match ← ops.recvfrom a 16 { dontwait := true } with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace rx b" b
      expectStraceClose "strace rx a" a
    return (s1, req, res)
  | "sendto" =>
    let (a, b) ← assertOk "strace tx pair" (← ops.socketpair .unix .stream nbFlags)
    let s1 ← modelStepOrThrow "strace tx" s0 (.socketpair .unix .stream nbFlags) (.pair 0 1)
    let req := NetReq.sendto 0 (ByteArray.mk #[1]) { dontwait := true, nosignal := true }
    let res ← try
      match ← ops.sendto a (ByteArray.mk #[1]) { dontwait := true, nosignal := true } with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace tx b" b
      expectStraceClose "strace tx a" a
    return (s1, req, res)
  | "shutdown" =>
    let (a, b) ← assertOk "strace shut pair" (← ops.socketpair .unix .stream nbFlags)
    let s1 ← modelStepOrThrow "strace shut" s0 (.socketpair .unix .stream nbFlags) (.pair 0 1)
    let req := NetReq.shutdown 0 .rd
    let res ← try
      match ← ops.shutdown a .rd with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace shut b" b
      expectStraceClose "strace shut a" a
    return (s1, req, res)
  | "sendmsg" =>
    let (a, b) ← assertOk "strace sendmsg pair" (← ops.socketpair .unix .stream nbFlags)
    let s1 ← modelStepOrThrow "strace sendmsg" s0 (.socketpair .unix .stream nbFlags) (.pair 0 1)
    let req := NetReq.sendmsg 0 #[1]
    let res ← try
      match ← ops.sendmsg a #[b] with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace sendmsg b" b
      expectStraceClose "strace sendmsg a" a
    return (s1, req, res)
  | "recvmsg" =>
    let (a, b) ← assertOk "strace recvmsg pair" (← ops.socketpair .unix .stream nbFlags)
    let s1 ← modelStepOrThrow "strace recvmsg" s0 (.socketpair .unix .stream nbFlags) (.pair 0 1)
    let req := NetReq.recvmsg 0 1
    let res ← try
      match ← ops.recvmsg a 1 with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace recvmsg b" b
      expectStraceClose "strace recvmsg a" a
    return (s1, req, res)
  | "ioctl" =>
    let fd ← assertOk "strace ioctl sock" (← ops.socket .inet .dgram nbFlags 0)
    let s1 ← modelStepOrThrow "strace ioctl" s0 (.socket .inet .dgram nbFlags 0) (.opened 0)
    let req := NetReq.ioctl 0 .getIfFlags "lo".toUTF8
    let res ← try
      match ← ops.ioctl fd .getIfFlags "lo".toUTF8 with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
    finally
      expectStraceClose "strace ioctl" fd
    return (s1, req, res)
  | _ => throw (IO.userError s!"unknown strace syscall: {syscallName}")

private def straceWorker (syscallName errName : String) : IO UInt32 := do
  let expected := parseInjectedErrno errName
  let (st, req, res) ← runStraceAction syscallName
  match res with
  | .error e =>
    if e != expected then
      IO.eprintln s!"net strace-worker ({syscallName}): expected {expected} ({errName}), got {e}"
      return 2
    let stepOk := (Net.allowedStep st req (.err e)).isSome
    if errName == "EAGAIN" then
      let allowEagain := ["accept4", "recvfrom", "sendto", "sendmsg", "recvmsg"].contains syscallName
      if stepOk != allowEagain then
        IO.eprintln s!"net strace-worker ({syscallName}): EAGAIN model stepOk={stepOk} expected={allowEagain}"
        return 7
      return 0
    if !stepOk then
      IO.eprintln s!"net strace-worker ({syscallName}): allowedStep rejected {errName}"
      return 8
    return 0
  | .ok () =>
    IO.eprintln s!"net strace-worker ({syscallName}): expected {errName}, got ok"
    return 3

private def straceNetSyscalls : List String :=
  ["socket", "socketpair", "bind", "listen", "accept4", "connect",
   "getsockopt", "setsockopt", "getsockname", "recvfrom", "sendto",
   "shutdown", "sendmsg", "recvmsg", "ioctl"]

/-- Run live `strace -f` fault-injection checks (`EINTR`, `ENOMEM`, `EIO`, `ENFILE`, `EAGAIN`) against all 15 `Net` syscalls. -/
def runStraceFaultCheck : IO Unit := do
  let exe ← IO.appPath
  for syscallName in straceNetSyscalls do
    for errName in ["EINTR", "ENOMEM", "EIO", "ENFILE", "EAGAIN"] do
      let out ← IO.Process.output {
        cmd := "strace"
        args := #["-f", "-qq", "-o", "/dev/null", "-e", s!"inject={syscallName}:error={errName}",
          exe.toString, "--net-strace-worker", syscallName, errName]
      }
      if out.exitCode != 0 then
        throw (IO.userError s!"net strace {syscallName} {errName} failed (exit={out.exitCode}): {out.stderr}")

/-- Handle `--net-strace-fault-check` and `--net-strace-worker` subcommands dispatched by `leanswe-fuzz` (`Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker`). -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    runStraceFaultCheck
    IO.println "NET_STRACE_FAULT_CHECK: ok (15 syscalls x EINTR, ENOMEM, EIO, ENFILE, EAGAIN)"
    return 0
  | ["--worker", "__recvfrom_cap__", _] =>
    let ops := defaultOps
    let (a, b) ← assertOk "cap worker sp" (← ops.socketpair .unix .stream nbFlags)
    try
      let _ ← ops.recvfrom a 0xffffffff { dontwait := true }
      let _ ← ops.recvfrom a 0x7fffffff { dontwait := true }
      let _ ← ops.recvfrom a MAX_READ_BYTES.toNat.toUInt32 { dontwait := true }
      let _ ← ops.recvfrom a (MAX_READ_BYTES.toNat.toUInt32 - 1) { dontwait := true }
      return 0
    finally
      safeClose a
      safeClose b
  | ["--worker", "__ioctl_signext__", _] =>
    let ops := defaultOps
    let fd ← assertOk "signext sock" (← ops.socket .inet .dgram nbFlags 0)
    try
      let _ ← assertOk "signext set 0x8049" (← ops.ioctl fd (.setIfFlags 0x8049) loIfname)
      let got ← assertOk "signext get" (← ops.ioctl fd .getIfFlags loIfname)
      if got != 0x8049 then
        IO.eprintln s!"ioctl sign-extension bug: expected 0x8049, got {got}"
        return 2
      return 0
    finally
      safeClose fd
  | ["--worker", syscallName, errName] => straceWorker syscallName errName
  | ["--worker", errName] => straceWorker "socket" errName
  | _ =>
    IO.eprintln s!"unknown net strace args: {args}"
    return 1

end Fuzz.LinuxSyscall.Net.Strace
