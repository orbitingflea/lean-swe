import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Model

namespace LeanSwe.LinuxSyscall.Net

open Core (NondetTest ErrorObligation ErrorJustification ErrorTestMode AssumptionObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `isTransientNetErrno` excludes `EFAULT` and extends `Errno.isTransientOsErrno` with `ENOBUFS`, while `NetErrorKind.ofErrno` classifies all Linux socket errnos into their exact 7 semantic categories. -/
def test_net_errno_classification
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := isTransientNetErrno)
    (classify : Errno → NetErrorKind := NetErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e = (Errno.isTransientOsErrno e || e == Errno.ENOBUFS))
  NondetTest.assert (classify e =
    (if e == Errno.EBADF || e == Errno.ENOTSOCK || e == Errno.ENOTTY then .badFd
     else if e == Errno.EINVAL || e == Errno.EAFNOSUPPORT || e == Errno.EPROTONOSUPPORT ||
             e == Errno.ESOCKTNOSUPPORT || e == Errno.EOPNOTSUPP || e == Errno.EPFNOSUPPORT ||
             e == Errno.ENOPROTOOPT || e == Errno.EPROTOTYPE || e == Errno.EDESTADDRREQ ||
             e == Errno.EMSGSIZE || e == Errno.ENOSYS then .invalidArg
     else if e == Errno.EADDRINUSE || e == Errno.EADDRNOTAVAIL ||
             e == Errno.ENOENT || e == Errno.ENODEV then .addressError
     else if e == Errno.EAGAIN || e == Errno.EINPROGRESS || e == Errno.EALREADY then .wouldBlockOrInProgress
     else if e == Errno.EISCONN || e == Errno.ENOTCONN || e == Errno.EPIPE ||
             e == Errno.ECONNRESET || e == Errno.ECONNREFUSED || e == Errno.ECONNABORTED ||
             e == Errno.ESHUTDOWN || e == Errno.ETIMEDOUT || e == Errno.ENETDOWN ||
             e == Errno.ENETUNREACH || e == Errno.EHOSTUNREACH || e == Errno.EPROTO then .connectionState
     else if e == Errno.EACCES || e == Errno.EPERM then .permissionDenied
     else .transientOrResource))
  NondetTest.assert (classify Errno.EBADF = .badFd ∧ classify Errno.ENOTSOCK = .badFd ∧ classify Errno.ENOTTY = .badFd)
  NondetTest.assert (classify Errno.EINVAL = .invalidArg ∧ classify Errno.EAFNOSUPPORT = .invalidArg ∧
    classify Errno.EPROTONOSUPPORT = .invalidArg ∧ classify Errno.ESOCKTNOSUPPORT = .invalidArg ∧
    classify Errno.EOPNOTSUPP = .invalidArg ∧ classify Errno.EDESTADDRREQ = .invalidArg ∧
    classify Errno.EMSGSIZE = .invalidArg)
  NondetTest.assert (classify Errno.EADDRINUSE = .addressError ∧ classify Errno.EADDRNOTAVAIL = .addressError ∧
    classify Errno.ENOENT = .addressError ∧ classify Errno.ENODEV = .addressError)
  NondetTest.assert (classify Errno.EAGAIN = .wouldBlockOrInProgress ∧
    classify Errno.EINPROGRESS = .wouldBlockOrInProgress ∧ classify Errno.EALREADY = .wouldBlockOrInProgress)
  NondetTest.assert (classify Errno.EISCONN = .connectionState ∧ classify Errno.ENOTCONN = .connectionState ∧
    classify Errno.EPIPE = .connectionState ∧ classify Errno.ECONNRESET = .connectionState ∧
    classify Errno.ECONNREFUSED = .connectionState ∧ classify Errno.ECONNABORTED = .connectionState ∧
    classify Errno.ESHUTDOWN = .connectionState ∧ classify Errno.ETIMEDOUT = .connectionState ∧
    classify Errno.EPROTO = .connectionState)
  NondetTest.assert (classify Errno.EACCES = .permissionDenied ∧ classify Errno.EPERM = .permissionDenied)
  NondetTest.assert (classify Errno.EINTR = .transientOrResource ∧ classify Errno.ENOMEM = .transientOrResource ∧
    classify Errno.ENOBUFS = .transientOrResource ∧ classify Errno.EMFILE = .transientOrResource)

/-- Portable symbolic `Net` encoders are injective, default `SockFlags` enables `cloexec`, `SockAddr.toRawTuple`/`ofRawTuple` round-trips across exact 8-lane IPv4/IPv6/Unix layouts, and `SockAddr.isValidTarget` enforces non-empty `<= 108`-byte `AF_UNIX` paths (allowing abstract `\0...` sockets while rejecting embedded NULs in pathname sockets). -/
def test_net_flags_and_sockaddr_codecs
    {runner} [NondetTest runner]
    (encDom : SockDomain → UInt32 := SockDomain.toTag)
    (encTyp : SockType → UInt32 := SockType.toTag)
    (encSf : SockFlags → UInt32 := SockFlags.toBits)
    (encOpt : SockOpt → UInt32 := SockOpt.toTag)
    (encSetOpt : SetSockOpt → UInt32 := SetSockOpt.toTag)
    (encMsg : MsgFlags → UInt32 := MsgFlags.toBits)
    (encShut : ShutHow → UInt32 := ShutHow.toTag)
    (encIoctl : NetIoctlOp → UInt32 × UInt32 := NetIoctlOp.toRaw)
    (encAddr : SockAddr → RawSockAddrTuple := SockAddr.toRawTuple)
    (decAddr : RawSockAddrTuple → SockAddr := SockAddr.ofRawTuple)
    (validTarget : SockAddr → Bool := SockAddr.isValidTarget)
    (defSf : SockFlags := {})
    (defMsg : MsgFlags := {}) : runner Unit := do
  let d1 ← nondet SockDomain
  let d2 ← nondet SockDomain
  NondetTest.assert ((encDom d1 == encDom d2) = (d1 == d2))
  let t1 ← nondet SockType
  let t2 ← nondet SockType
  NondetTest.assert ((encTyp t1 == encTyp t2) = (t1 == t2))
  let sf1 ← nondet SockFlags
  let sf2 ← nondet SockFlags
  NondetTest.assert ((encSf sf1 == encSf sf2) = (sf1 == sf2))
  let o1 ← nondet SockOpt
  let o2 ← nondet SockOpt
  NondetTest.assert ((encOpt o1 == encOpt o2) = (o1 == o2))
  let so1 ← nondet SetSockOpt
  let so2 ← nondet SetSockOpt
  NondetTest.assert ((encSetOpt so1 == encSetOpt so2) = (so1 == so2))
  let mf1 ← nondet MsgFlags
  let mf2 ← nondet MsgFlags
  NondetTest.assert ((encMsg mf1 == encMsg mf2) = (mf1 == mf2))
  let sh1 ← nondet ShutHow
  let sh2 ← nondet ShutHow
  NondetTest.assert ((encShut sh1 == encShut sh2) = (sh1 == sh2))
  let io1 ← nondet NetIoctlOp
  let io2 ← nondet NetIoctlOp
  NondetTest.assert ((encIoctl io1 == encIoctl io2) = (io1 == io2))
  let sa ← nondet SockAddr
  NondetTest.assert (decAddr (encAddr sa) = sa)
  NondetTest.assert (encDom .inet = 0 ∧ encDom .inet6 = 1 ∧ encDom .unix = 2)
  NondetTest.assert (encTyp .stream = 0 ∧ encTyp .dgram = 1 ∧ encTyp .seqpacket = 2)
  NondetTest.assert (encSf { nonblock := true, cloexec := false } = 1 ∧ encSf { cloexec := true } = 2)
  NondetTest.assert (encOpt .error = 0 ∧ encOpt .reuseAddr = 1 ∧ encSetOpt .reuseAddr = 0)
  NondetTest.assert (encMsg { nosignal := true } = 1 ∧ encMsg { dontwait := true } = 2 ∧ encMsg { peek := true } = 4)
  NondetTest.assert (encShut .rd = 0 ∧ encShut .wr = 1 ∧ encShut .rdwr = 2 ∧
    encIoctl .getIfFlags = (0, 0) ∧ encIoctl (.setIfFlags 0x49) = (1, 0x49))
  NondetTest.assert (validTarget (.ipv4 INADDR_LOOPBACK 8080) = true)
  NondetTest.assert (validTarget (.ipv6 0 1 443) = true)
  NondetTest.assert (validTarget (.unix (asciiBytes ['/', 't', 'm', 'p', '/', 's'])) = true)
  NondetTest.assert (validTarget (.unix (ByteArray.mk #[0, 97, 0, 98])) = true)
  NondetTest.assert (validTarget (.unix (ByteArray.mk (List.replicate 108 97).toArray)) = true)
  NondetTest.assert (validTarget (.unix (ByteArray.mk #[])) = false)
  NondetTest.assert (validTarget (.unix (ByteArray.mk #[47, 0, 97])) = false)
  NondetTest.assert (validTarget (.unix (ByteArray.mk (List.replicate 109 97).toArray)) = false)
  NondetTest.assert (defSf = { nonblock := false, cloexec := true } ∧
    defMsg = { nosignal := false, dontwait := false, peek := false })
  NondetTest.assert (encAddr (.ipv4 0x7f000001 8080) = (0, 0x7f000001, 0, 0, 8080, 0, 0, ByteArray.mk #[]) ∧
    encAddr (.ipv6 1 2 443 3 4) = (1, 0, 1, 2, 443, 3, 4, ByteArray.mk #[]) ∧
    encAddr (.unix (ByteArray.mk #[0, 97])) = (2, 0, 0, 0, 0, 0, 0, ByteArray.mk #[0, 97]))
  NondetTest.assert (IPPROTO_TCP = 6 ∧ IPPROTO_UDP = 17 ∧ IPPROTO_MAX = 263 ∧
    UNIX_PATH_MAX = 108 ∧ IFNAMSIZ = 16 ∧ MAX_SCM_FDS = 32 ∧ MAX_READ_BYTES = 16777216 ∧
    PF_UNIX = 1)

/-- `bind`/`connect` reject invalid `AF_UNIX` paths, `sendmsg`/`recvmsg` reject `0` or `> 32` `SCM_RIGHTS` FD counts, and `ioctl` rejects embedded-NUL or `>= IFNAMSIZ` (`16`) interface names with `Errno.EINVAL` without mutating state. -/
def test_net_ops_boundaryValidation_einval
    {S fd : Type} {runner} [NondetTest runner]
    (ops : NetOpsM (StateM S) fd) : runner Unit := do
  let s₀ ← nondet S
  let h ← nondet fd
  let op ← nondet NetIoctlOp
  let nulBytes ← nondet ByteArray
  assume (nulBytes.data[0]? != some 0 ∧ hasEmbeddedNul nulBytes = true)
  let longUnix ← nondet ByteArray
  assume (longUnix.data.size > UNIX_PATH_MAX)
  let longIf ← nondet ByteArray
  assume (longIf.data.size ≥ IFNAMSIZ)
  let overFds ← nondet (Array fd)
  assume (overFds.size > MAX_SCM_FDS)
  let overMaxFds ← nondet UInt32
  assume (overMaxFds.toNat > MAX_SCM_FDS)
  NondetTest.assert ((ops.bind h (.unix (ByteArray.mk #[]))).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.bind h (.unix nulBytes)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.bind h (.unix longUnix)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.connect h (.unix (ByteArray.mk #[]))).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.connect h (.unix nulBytes)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.connect h (.unix longUnix)).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.sendmsg h #[]).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.sendmsg h overFds).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.recvmsg h 0).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.recvmsg h overMaxFds).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.ioctl h op nulBytes).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.ioctl h op longIf).run s₀ = (.error Errno.EINVAL, s₀))

/-- `socket` and `socketpair` enforce curated `Net` domain/type/protocol rules (`EINVAL` for `proto >= 263`, `ESOCKTNOSUPPORT` on `AF_INET`/`AF_INET6` `SOCK_SEQPACKET`, `PF_UNIX` (`1`) accepted alongside `0` on `AF_UNIX`, `EPROTONOSUPPORT` on unsupported/mismatched protocols including `2` on `AF_UNIX` and `262`/`132`/`1`/`58`/`115`, `EOPNOTSUPP`/`ESOCKTNOSUPPORT` on non-`AF_UNIX` `socketpair`). -/
def test_net_ops_socketAndSocketpairMatrix
    {S fd : Type} {runner} [NondetTest runner]
    (ops : NetOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let (rHighProto, sHp) := (ops.socket .inet .stream {} IPPROTO_MAX).run s₀
  NondetTest.assert (rHighProto = .error Errno.EINVAL ∧ sHp = s₀)
  let (rSeq4, s₁) := (ops.socket .inet .seqpacket {} 0).run s₀
  NondetTest.assert (rSeq4 = .error Errno.ESOCKTNOSUPPORT ∧ s₁ = s₀)
  let (rSeq6, s₂) := (ops.socket .inet6 .seqpacket {} 0).run s₀
  NondetTest.assert (rSeq6 = .error Errno.ESOCKTNOSUPPORT ∧ s₂ = s₀)
  let (rBadProto4, s₃) := (ops.socket .inet .stream {} IPPROTO_UDP).run s₀
  NondetTest.assert (rBadProto4 = .error Errno.EPROTONOSUPPORT ∧ s₃ = s₀)
  let (rBadProtoU, s₄) := (ops.socket .unix .stream {} IPPROTO_TCP).run s₀
  NondetTest.assert (rBadProtoU = .error Errno.EPROTONOSUPPORT ∧ s₄ = s₀)
  let (rMptcp, sM) := (ops.socket .inet .stream {} 262).run s₀
  let (rSctp, sSc) := (ops.socket .inet .stream {} 132).run s₀
  let (rIcmp, sIc) := (ops.socket .inet .dgram {} 1).run s₀
  let (rIcmp6, sI6) := (ops.socket .inet6 .dgram {} 58).run s₀
  let (rL2tp, sL2) := (ops.socket .inet .dgram {} 115).run s₀
  NondetTest.assert (rMptcp = .error Errno.EPROTONOSUPPORT ∧ sM = s₀ ∧
    rSctp = .error Errno.EPROTONOSUPPORT ∧ sSc = s₀ ∧
    rIcmp = .error Errno.EPROTONOSUPPORT ∧ sIc = s₀ ∧
    rIcmp6 = .error Errno.EPROTONOSUPPORT ∧ sI6 = s₀ ∧
    rL2tp = .error Errno.EPROTONOSUPPORT ∧ sL2 = s₀)
  let (rSp4, s₅) := (ops.socketpair .inet .stream {}).run s₀
  NondetTest.assert (rSp4 = .error Errno.EOPNOTSUPP ∧ s₅ = s₀)
  let (rSpSeq, s₆) := (ops.socketpair .inet6 .seqpacket {}).run s₀
  NondetTest.assert (rSpSeq = .error Errno.ESOCKTNOSUPPORT ∧ s₆ = s₀)
  let (rOkTcp, s₇) := (ops.socket .inet .stream { nonblock := true, cloexec := true } IPPROTO_TCP).run s₀
  let (rOk6, s₈) := (ops.socket .inet6 .dgram { cloexec := true } IPPROTO_UDP).run s₇
  let (rOkSp, _) := (ops.socketpair .unix .seqpacket { nonblock := true, cloexec := true }).run s₈
  NondetTest.assert ((∃ h, rOkTcp = .ok h) ∧ (∃ h, rOk6 = .ok h) ∧ (∃ p, rOkSp = .ok p))
  NondetTest.assert (
    (ops.socket .inet6 .dgram {} IPPROTO_MAX).run s₀ = (.error Errno.EINVAL, s₀) ∧
    (ops.socket .inet .dgram {} IPPROTO_TCP).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀) ∧
    (ops.socket .inet6 .dgram {} IPPROTO_TCP).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀) ∧
    (ops.socket .unix .dgram {} IPPROTO_UDP).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀) ∧
    (ops.socketpair .inet .seqpacket {}).run s₀ = (.error Errno.ESOCKTNOSUPPORT, s₀) ∧
    (ops.socketpair .inet6 .stream {}).run s₀ = (.error Errno.EOPNOTSUPP, s₀) ∧
    (ops.socketpair .inet .dgram {}).run s₀ = (.error Errno.EOPNOTSUPP, s₀) ∧
    (ops.socketpair .inet6 .dgram {}).run s₀ = (.error Errno.EOPNOTSUPP, s₀))
  let (rOkUxS, _) := (ops.socket .unix .stream {} PF_UNIX).run s₀
  let (rOkUxD, _) := (ops.socket .unix .dgram {} PF_UNIX).run s₀
  let (rOkUxQ, _) := (ops.socket .unix .seqpacket {} PF_UNIX).run s₀
  NondetTest.assert (
    (∃ h, rOkUxS = .ok h) ∧ (∃ h, rOkUxD = .ok h) ∧ (∃ h, rOkUxQ = .ok h) ∧
    (ops.socket .unix .stream {} 2).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀) ∧
    (ops.socket .unix .dgram {} 2).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀) ∧
    (ops.socket .unix .seqpacket {} 2).run s₀ = (.error Errno.EPROTONOSUPPORT, s₀))

/-- IPv4 loopback `socket` -> `setsockopt(SO_REUSEADDR)` -> ephemeral `bind(port=0)` -> `getsockname` -> `listen` -> empty `accept4` (`EAGAIN`) -> duplicate listener `bind` (`EADDRINUSE`) -> non-blocking `connect` (`EINPROGRESS` -> `getsockopt SO_ERROR` -> `connect` completion -> `EISCONN`) -> `accept4` inherits `SO_REUSEADDR`. -/
def test_net_ops_loopbackBindListenAndConnectLifecycle
    {S fd : Type} {runner} [NondetTest runner]
    (ops : NetOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let (rL, s₁) := (ops.socket .inet .stream nbFlags 0).run s₀
  match rL with
  | .error _ => NondetTest.assert False
  | .ok lfd =>
    let (rUnbSa, _) := (ops.getsockname lfd).run s₁
    NondetTest.assert (rUnbSa = .ok (.ipv4 0 0))
    let (rAccPre, _) := (ops.accept4 lfd nbFlags).run s₁
    NondetTest.assert (rAccPre = .error Errno.EINVAL)
    let (rShutPre, _) := (ops.shutdown lfd .rdwr).run s₁
    NondetTest.assert (rShutPre = .error Errno.ENOTCONN)
    let (rFamMis, _) := (ops.bind lfd (.ipv6 0 1 0)).run s₁
    NondetTest.assert (rFamMis = .error Errno.EAFNOSUPPORT)
    let (rReuseSet, s₂) := (ops.setsockopt lfd .reuseAddr 1).run s₁
    let (rReuseGet, _) := (ops.getsockopt lfd .reuseAddr).run s₂
    NondetTest.assert (rReuseSet = .ok () ∧ rReuseGet = .ok 1)
    let (rBind, s₃) := (ops.bind lfd (.ipv4 INADDR_LOOPBACK 0)).run s₂
    NondetTest.assert (rBind = .ok ())
    let (rDupBind, sDb) := (ops.bind lfd (.ipv4 INADDR_LOOPBACK 0)).run s₃
    NondetTest.assert (rDupBind = .error Errno.EINVAL ∧ sDb = s₃)
    let (rSa, s₄) := (ops.getsockname lfd).run s₃
    match rSa with
    | .ok (.ipv4 boundIp boundPort) =>
      NondetTest.assert (boundIp = INADDR_LOOPBACK ∧ boundPort ≠ 0)
      let (rLis, s₅) := (ops.listen lfd 128).run s₄
      NondetTest.assert (rLis = .ok ())
      let (rEmptyAcc, sEa) := (ops.accept4 lfd nbFlags).run s₅
      NondetTest.assert (rEmptyAcc = .error Errno.EAGAIN ∧ sEa = s₅)
      let (rDupS, s₆) := (ops.socket .inet .stream nbFlags 0).run s₅
      match rDupS with
      | .error _ => NondetTest.assert False
      | .ok dupFd =>
        let (_, s₇) := (ops.setsockopt dupFd .reuseAddr 1).run s₆
        let (rInUse, _) := (ops.bind dupFd (.ipv4 INADDR_LOOPBACK boundPort)).run s₇
        NondetTest.assert (rInUse = .error Errno.EADDRINUSE)
        let (rC, s₈) := (ops.socket .inet .stream nbFlags 0).run s₇
        match rC with
        | .error _ => NondetTest.assert False
        | .ok cfd =>
          let (rConn1, s₉) := (ops.connect cfd (.ipv4 INADDR_LOOPBACK boundPort)).run s₈
          NondetTest.assert (rConn1 = .error Errno.EINPROGRESS ∨ rConn1 = .ok ())
          let (rSoErr, s₁₀) := (ops.getsockopt cfd .error).run s₉
          NondetTest.assert (rSoErr = .ok 0)
          let (rConn2, s₁₁) := (ops.connect cfd (.ipv4 INADDR_LOOPBACK boundPort)).run s₁₀
          NondetTest.assert (rConn2 = .ok () ∨ rConn2 = .error Errno.EISCONN)
          let (rConn3, _) := (ops.connect cfd (.ipv4 INADDR_LOOPBACK boundPort)).run s₁₁
          NondetTest.assert (rConn3 = .error Errno.EISCONN)
          let (rAcc, s₁₂) := (ops.accept4 lfd nbFlags).run s₁₁
          match rAcc with
          | .error _ => NondetTest.assert False
          | .ok (sfd, peerSa) =>
            let (rSrvReuse, _) := (ops.getsockopt sfd .reuseAddr).run s₁₂
            NondetTest.assert (peerSa.domain = .inet ∧ rSrvReuse = .ok 1)
    | _ => NondetTest.assert False

/-- Connected `SOCK_STREAM` endpoints enforce `MSG_PEEK`, partial `recvfrom`, `SHUT_WR` half-close preserving reverse-direction `sendto`/`recvfrom`, unread-RX drainage before local `SHUT_RD` EOF, and `AF_UNIX` peer `SHUT_RD` `EPIPE`. -/
def test_net_ops_streamTransferPeekAndShutdown
    {S fd : Type} {runner} [NondetTest runner]
    (ops : NetOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let (rPair, s₁) := (ops.socketpair .unix .stream nbFlags).run s₀
  match rPair with
  | .error _ => NondetTest.assert False
  | .ok (cfd, sfd) =>
    let msg := asciiBytes ['h', 'e', 'l', 'l', 'o']
    let (rSend, s₂) := (ops.sendto cfd msg { nosignal := true }).run s₁
    NondetTest.assert (rSend = .ok 5)
    let (rPeek, s₃) := (ops.recvfrom sfd 2 { peek := true }).run s₂
    NondetTest.assert (rPeek = .ok (asciiBytes ['h', 'e']) ∧ s₃ = s₂)
    let (rPart1, s₄) := (ops.recvfrom sfd 2 {}).run s₃
    let (rPart2, s₅) := (ops.recvfrom sfd 8 {}).run s₄
    NondetTest.assert (rPart1 = .ok (asciiBytes ['h', 'e']) ∧ rPart2 = .ok (asciiBytes ['l', 'l', 'o']))
    let (rEmptyRx, _) := (ops.recvfrom sfd 8 {}).run s₅
    NondetTest.assert (rEmptyRx = .error Errno.EAGAIN)
    let (rShutWr, s₆) := (ops.shutdown cfd .wr).run s₅
    NondetTest.assert (rShutWr = .ok ())
    let (rSendAfterShut, _) := (ops.sendto cfd (asciiBytes ['x']) { nosignal := true }).run s₆
    NondetTest.assert (rSendAfterShut = .error Errno.EPIPE)
    let (rPeerEof, s₇) := (ops.recvfrom sfd 8 {}).run s₆
    NondetTest.assert (rPeerEof = .ok (ByteArray.mk #[]))
    let (rRevSend, s₈) := (ops.sendto sfd (asciiBytes ['b', 'a', 'c', 'k']) { nosignal := true }).run s₇
    NondetTest.assert (rRevSend = .ok 4)
    let (rShutRd, s₉) := (ops.shutdown cfd .rd).run s₈
    let (rDrainBeforeEof, s₁₀) := (ops.recvfrom cfd 8 {}).run s₉
    let (rLocalRdEof, s₁₁) := (ops.recvfrom cfd 8 {}).run s₁₀
    let (rUnixPeerRdPipe, _) := (ops.sendto sfd (asciiBytes ['z']) { nosignal := true }).run s₁₁
    NondetTest.assert (rShutRd = .ok () ∧ rDrainBeforeEof = .ok (asciiBytes ['b', 'a', 'c', 'k']) ∧
      rLocalRdEof = .ok (ByteArray.mk #[]) ∧ rUnixPeerRdPipe = .error Errno.EPIPE)

/-- `AF_UNIX` and non-blocking TCP enforce `socketpair` `bind`, `backlog = 0` `EAGAIN`, refused `EINPROGRESS` `recvfrom`/`sendto` consuming `ECONNREFUSED` into `SS_DISCONNECTING` (`ECONNABORTED` on re-`connect`), and coupled `SCM_RIGHTS` `sendmsg`/`recvmsg` vs `sendto`/`recvfrom` queue semantics. -/
def test_net_ops_unixSeqpacketScmRightsAndSoErrorClear
    {S fd : Type} {runner} [NondetTest runner]
    (ops : NetOpsM (StateM S) fd) (s₀ : S) : runner Unit := do
  let nbFlags : SockFlags := { nonblock := true, cloexec := true }
  let (rU, s₁) := (ops.socket .unix .seqpacket nbFlags 0).run s₀
  match rU with
  | .error _ => NondetTest.assert False
  | .ok ufd =>
    let (rUnbLis, _) := (ops.listen ufd 0).run s₁
    NondetTest.assert (rUnbLis = .error Errno.EINVAL)
    let missPath := asciiBytes ['/', 't', 'm', 'p', '/', 'm', 'i', 's', 's', '.', 's', 'o', 'c', 'k']
    let (rMissConn, _) := (ops.connect ufd (.unix missPath)).run s₁
    NondetTest.assert (rMissConn = .error Errno.ENOENT)
    let boundPath := asciiBytes ['/', 't', 'm', 'p', '/', 'b', 'o', 'u', 'n', 'd', '.', 's', 'o', 'c', 'k']
    let (rBindU, s₂) := (ops.bind ufd (.unix boundPath)).run s₁
    NondetTest.assert (rBindU = .ok ())
    let (rU2, s₃) := (ops.socket .unix .seqpacket nbFlags 0).run s₂
    match rU2 with
    | .error _ => NondetTest.assert False
    | .ok ufd2 =>
      let (rRefU, _) := (ops.connect ufd2 (.unix boundPath)).run s₃
      NondetTest.assert (rRefU = .error Errno.ECONNREFUSED)
      let (_, s₃L) := (ops.listen ufd 0).run s₃
      let (rConnOkU, s₃C) := (ops.connect ufd2 (.unix boundPath)).run s₃L
      let (rU3, s₃D) := (ops.socket .unix .seqpacket nbFlags 0).run s₃C
      match rU3 with
      | .error _ => NondetTest.assert False
      | .ok ufd3 =>
        let (rBacklogFull, _) := (ops.connect ufd3 (.unix boundPath)).run s₃D
        NondetTest.assert (rConnOkU = .ok () ∧ rBacklogFull = .error Errno.EAGAIN)
        let (rC4, s₄) := (ops.socket .inet .stream nbFlags 0).run s₃D
        match rC4 with
        | .error _ => NondetTest.assert False
        | .ok cRef =>
          let (rRef4, s₅) := (ops.connect cRef (.ipv4 INADDR_LOOPBACK 65001)).run s₄
          NondetTest.assert (rRef4 = .error Errno.EINPROGRESS ∨ rRef4 = .error Errno.ECONNREFUSED)
          let (rRecvRef, s₆) := (ops.recvfrom cRef 8 {}).run s₅
          let (rErrAfter, s₇) := (ops.getsockopt cRef .error).run s₆
          let (rReconnAbort, _) := (ops.connect cRef (.ipv4 INADDR_LOOPBACK 65001)).run s₇
          NondetTest.assert ((rRef4 = .error Errno.EINPROGRESS → rRecvRef = .error Errno.ECONNREFUSED) ∧
            rErrAfter = .ok 0 ∧ rReconnAbort = .error Errno.ECONNABORTED)
          let (rSp, s₈) := (ops.socketpair .unix .seqpacket nbFlags).run s₇
          match rSp with
          | .error _ => NondetTest.assert False
          | .ok (sp0, sp1) =>
            let spBindPath := asciiBytes ['/', 't', 'm', 'p', '/', 's', 'p', '.', 's', 'o', 'c', 'k']
            let (rSpBind, s₈B) := (ops.bind sp0 (.unix spBindPath)).run s₈
            NondetTest.assert (rSpBind = .ok ())
            let (_, s₉) := (ops.sendto sp0 (asciiBytes ['A']) { nosignal := true }).run s₈B
            let (rPlainRecvmsg, s₁₀) := (ops.recvmsg sp1 4).run s₉
            NondetTest.assert (rPlainRecvmsg = .ok #[])
            let (rScmDropSend, s₁₁) := (ops.sendmsg sp0 #[ufd]).run s₁₀
            let (rDropByRecvfrom, s₁₂) := (ops.recvfrom sp1 8 {}).run s₁₁
            let (rAfterDrop, s₁₃) := (ops.recvmsg sp1 4).run s₁₂
            NondetTest.assert (rScmDropSend = .ok () ∧ (∃ b, rDropByRecvfrom = .ok b ∧ b.size = 1) ∧
              rAfterDrop = .error Errno.EAGAIN)
            let (rScmSend, s₁₄) := (ops.sendmsg sp0 #[ufd, ufd2]).run s₁₃
            let (rScmRecv, _) := (ops.recvmsg sp1 4).run s₁₄
            NondetTest.assert (rScmSend = .ok () ∧ (∃ got, rScmRecv = .ok got ∧ got.size = 2))

/-- `NetState` models `ioctl` (`SIOCGIFFLAGS` on `"lo"` vs `ENODEV` on missing/empty names, `SIOCSIFFLAGS` `EPERM` vs `CAP_NET_ADMIN` flag update) and non-socket `ENOTSOCK`/`ENOTTY` rejection. -/
def test_net_state_ioctlAndNonSocket
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let sUnpriv := NetState.initial false
  let (rS, s₁) := (ops.socket .inet .dgram {} 0).run sUnpriv
  match rS with
  | .error _ => NondetTest.assert False
  | .ok dgramFd =>
    let (rLo, _) := (ops.ioctl dgramFd .getIfFlags loIfname).run s₁
    NondetTest.assert (rLo = .ok defaultLoFlags)
    let (rEmptyIf, _) := (ops.ioctl dgramFd .getIfFlags (ByteArray.mk #[])).run s₁
    NondetTest.assert (rEmptyIf = .error Errno.ENODEV)
    let (rMissIf, _) := (ops.ioctl dgramFd .getIfFlags (asciiBytes ['n', 'o', 'p', 'e', '0'])).run s₁
    NondetTest.assert (rMissIf = .error Errno.ENODEV)
    let (rEperm, _) := (ops.ioctl dgramFd (.setIfFlags 0) loIfname).run s₁
    let (rEpermMiss, _) := (ops.ioctl dgramFd (.setIfFlags 0) (asciiBytes ['n', 'o', 'p', 'e', '0'])).run s₁
    let (rEpermEmpty, _) := (ops.ioctl dgramFd (.setIfFlags 0) (ByteArray.mk #[])).run s₁
    NondetTest.assert (rEperm = .error Errno.EPERM ∧ rEpermMiss = .error Errno.EPERM ∧ rEpermEmpty = .error Errno.EPERM)
    let (nonSockHid, sNs) := NetState.registerNonSocket s₁
    let (rNotSock, _) := (ops.getsockname nonSockHid).run sNs
    let (rNotTy, _) := (ops.ioctl nonSockHid .getIfFlags loIfname).run sNs
    NondetTest.assert (rNotSock = .error Errno.ENOTSOCK ∧ rNotTy = .error Errno.ENOTTY)
    let sPriv := NetState.initial true
    let (rSp, sPriv1) := (ops.socket .inet .dgram {} 0).run sPriv
    match rSp with
    | .error _ => NondetTest.assert False
    | .ok privFd =>
      let (rPrivMiss, _) := (ops.ioctl privFd (.setIfFlags 0) (asciiBytes ['n', 'o', 'p', 'e', '0'])).run sPriv1
      let (rDown, sPriv2) := (ops.ioctl privFd (.setIfFlags 0) loIfname).run sPriv1
      let (rFlagsDown, _) := (ops.ioctl privFd .getIfFlags loIfname).run sPriv2
      let (rUp, sPriv3) := (ops.ioctl privFd (.setIfFlags IFF_UP) loIfname).run sPriv2
      let (rFlagsUp, _) := (ops.ioctl privFd .getIfFlags loIfname).run sPriv3
      NondetTest.assert (rPrivMiss = .error Errno.ENODEV ∧ rDown = .ok 0 ∧
        rFlagsDown = .ok IFF_LOOPBACK ∧ rUp = .ok 0 ∧ rFlagsUp = .ok defaultLoFlags)

/-- `NetState.closeHandle` drains unread RX before reporting `ECONNRESET` once and `0` EOF thereafter, allows 1st `sendto` after clean TCP peer close before `EPIPE` on 2nd `sendto`, preserves pre-`accept4` closed-client TX bytes, and resets unaccepted clients on listener close. -/
def test_net_state_closeAndPeerReset
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rL, st1) := (ops.socket .inet .stream nb 0).run (NetState.initial false)
  match rL with
  | .error _ => NondetTest.assert False
  | .ok lfd =>
    let (_, st2) := (ops.bind lfd (.ipv4 INADDR_LOOPBACK 55100)).run st1
    let (_, st3) := (ops.listen lfd 8).run st2
    let (rC, st4) := (ops.socket .inet .stream {} 0).run st3
    match rC with
    | .error _ => NondetTest.assert False
    | .ok cfd =>
      let (_, st5) := (ops.connect cfd (.ipv4 INADDR_LOOPBACK 55100)).run st4
      let (rA, st6) := (ops.accept4 lfd nb).run st5
      match rA with
      | .error _ => NondetTest.assert False
      | .ok (sfd, _) =>
        let (_, st7) := (ops.sendto cfd (asciiBytes ['h', 'i']) { nosignal := true }).run st6
        let (_, st8) := (ops.sendto sfd (asciiBytes ['u', 'n', 'r']) { nosignal := true }).run st7
        match NetState.closeHandle st8 cfd with
        | .error _ => NondetTest.assert False
        | .ok st9 =>
          let (rClosedUse, _) := (ops.getsockname cfd).run st9
          let (rDrainHi, st10) := (ops.recvfrom sfd 16 {}).run st9
          let (rRstOnce, st11) := (ops.recvfrom sfd 16 {}).run st10
          let (rEofAfterRst, _) := (ops.recvfrom sfd 16 {}).run st11
          let (rRstSend, _) := (ops.sendto sfd (asciiBytes ['x']) { nosignal := true }).run st11
          NondetTest.assert (rClosedUse = .error Errno.EBADF ∧ rDrainHi = .ok (asciiBytes ['h', 'i']) ∧
            rRstOnce = .error Errno.ECONNRESET ∧ rEofAfterRst = .ok (ByteArray.mk #[]) ∧
            rRstSend = .error Errno.EPIPE)

/-- `NetState` models clean TCP close (1st `sendto` succeeds triggering `RST`, 2nd `sendto` returns `EPIPE`), pre-`accept4` client `sendto` + `closeHandle` delivering buffered bytes before EOF, and listener `closeHandle` resetting queued unaccepted clients. -/
def test_net_state_cleanClosePreAcceptAndListenerReset
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rL, s1) := (ops.socket .inet .stream nb 0).run (NetState.initial false)
  match rL with
  | .error _ => NondetTest.assert False
  | .ok lfd =>
    let (_, s2) := (ops.bind lfd (.ipv4 INADDR_ANY 55200)).run s1
    let (_, s3) := (ops.listen lfd 8).run s2
    let (rC1, s4) := (ops.socket .inet .stream {} 0).run s3
    match rC1 with
    | .error _ => NondetTest.assert False
    | .ok c1 =>
      let (_, s5) := (ops.connect c1 (.ipv4 INADDR_LOOPBACK 55200)).run s4
      let (_, s6) := (ops.sendto c1 (asciiBytes ['a', 'b', 'c']) { nosignal := true }).run s5
      match NetState.closeHandle s6 c1 with
      | .error _ => NondetTest.assert False
      | .ok s7 =>
        let (rAcc1, s8) := (ops.accept4 lfd nb).run s7
        match rAcc1 with
        | .error _ => NondetTest.assert False
        | .ok (srv1, _) =>
          let (rSrvLocal, _) := (ops.getsockname srv1).run s8
          let (rPreBytes, s9) := (ops.recvfrom srv1 8 {}).run s8
          let (rPreEof, s10) := (ops.recvfrom srv1 8 {}).run s9
          let (rFirstSend, s11) := (ops.sendto srv1 (asciiBytes ['p']) { nosignal := true }).run s10
          let (rSecondSend, s12) := (ops.sendto srv1 (asciiBytes ['q']) { nosignal := true }).run s11
          NondetTest.assert (rSrvLocal = .ok (.ipv4 INADDR_LOOPBACK 55200) ∧
            rPreBytes = .ok (asciiBytes ['a', 'b', 'c']) ∧ rPreEof = .ok (ByteArray.mk #[]) ∧
            rFirstSend = .ok 1 ∧ rSecondSend = .error Errno.EPIPE)
          let (rC2, s13) := (ops.socket .inet .stream nb 0).run s12
          match rC2 with
          | .error _ => NondetTest.assert False
          | .ok c2 =>
            let (_, s14) := (ops.connect c2 (.ipv4 INADDR_LOOPBACK 55200)).run s13
            match NetState.closeHandle s14 lfd with
            | .error _ => NondetTest.assert False
            | .ok s15 =>
              let (rQueuedRst, _) := (ops.recvfrom c2 8 {}).run s15
              NondetTest.assert (rQueuedRst = .error Errno.ECONNRESET)

/-- `NetState` models dual-stack IPv4 `127.0.0.2` -> IPv6 `[::]` `connect`/`accept4` (`::ffff:127.0.0.2`), unbound UDP `connect` ephemeral auto-bind + unused-port `sendto` `ECONNREFUSED` + `SHUT_RD` `EAGAIN`, and `AF_UNIX` `SOCK_DGRAM` missing-path `ENOENT`. -/
def test_net_state_dualStackAndDgramConnect
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rL6, s1) := (ops.socket .inet6 .stream nb 0).run (NetState.initial false)
  match rL6 with
  | .error _ => NondetTest.assert False
  | .ok l6 =>
    let (_, s2) := (ops.bind l6 (.ipv6 0 0 55300)).run s1
    let (_, s3) := (ops.listen l6 4).run s2
    let (rC4, s4) := (ops.socket .inet .stream {} 0).run s3
    match rC4 with
    | .error _ => NondetTest.assert False
    | .ok c4 =>
      let (rDsConn, s5) := (ops.connect c4 (.ipv4 0x7f000002 55300)).run s4
      let (rDsAcc, s6) := (ops.accept4 l6 nb).run s5
      match rDsAcc with
      | .error _ => NondetTest.assert False
      | .ok (srv6, peer6) =>
        let (rSrv6Sa, _) := (ops.getsockname srv6).run s6
        NondetTest.assert (rDsConn = .ok () ∧ peer6.domain = .inet6 ∧
          rSrv6Sa = .ok (.ipv6 0 0x0000ffff7f000002 55300 0 0))
        let (rUdp, s7) := (ops.socket .inet .dgram nb 0).run s6
        let (rUnixDg, s8) := (ops.socket .unix .dgram nb 0).run s7
        match rUdp, rUnixDg with
        | .ok u4, .ok udg =>
          let (rUdgMiss, _) := (ops.connect udg (.unix (asciiBytes ['/', 't', 'm', 'p', '/', 'n', 'o']))).run s8
          let (rU4Conn, s9) := (ops.connect u4 (.ipv4 INADDR_LOOPBACK 55399)).run s8
          let (rU4Sa, _) := (ops.getsockname u4).run s9
          let (rU4Send, s10) := (ops.sendto u4 (asciiBytes ['p']) {}).run s9
          let (rU4IcmpErr, s11) := (ops.recvfrom u4 8 {}).run s10
          let (_, s12) := (ops.shutdown u4 .rd).run s11
          let (rU4AfterShutRd, _) := (ops.recvfrom u4 8 {}).run s12
          NondetTest.assert (rUdgMiss = .error Errno.ENOENT ∧ rU4Conn = .ok () ∧
            (∃ p, rU4Sa = .ok (.ipv4 INADDR_LOOPBACK p) ∧ p ≠ 0) ∧
            rU4Send = .ok 1 ∧ rU4IcmpErr = .error Errno.ECONNREFUSED ∧
            rU4AfterShutRd = .error Errno.EAGAIN)
        | _, _ => NondetTest.assert False

/-- `NetState` models unconnected `AF_UNIX` `SOCK_DGRAM` `ENOTCONN` (vs UDP `EDESTADDRREQ`), closed `AF_UNIX` `SOCK_DGRAM` peer `ECONNREFUSED` -> `ENOTCONN` on both `socketpair` and `bind`+`connect`, and TCP simultaneous self-connect (`EINPROGRESS` -> `SO_ERROR = 0` -> self `sendto`/`recvfrom`). -/
def test_net_state_unixDgramDisconnectAndTcpSelfConnect
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rUd0, s1) := (ops.socket .unix .dgram nb 0).run (NetState.initial false)
  let (rV40, s2) := (ops.socket .inet .dgram nb 0).run s1
  let (rSpDg, s3) := (ops.socketpair .unix .dgram nb).run s2
  match rUd0, rV40, rSpDg with
  | .ok udUnconn, .ok v4Unconn, .ok (sp0, sp1) =>
    let (rUnconnUnix, _) := (ops.sendto udUnconn (asciiBytes ['a']) { nosignal := true }).run s3
    let (rUnconnUdp, _) := (ops.sendto v4Unconn (asciiBytes ['a']) { nosignal := true }).run s3
    NondetTest.assert (rUnconnUnix = .error Errno.ENOTCONN ∧ rUnconnUdp = .error Errno.EDESTADDRREQ)
    match NetState.closeHandle s3 sp1 with
    | .error _ => NondetTest.assert False
    | .ok s4 =>
      let (rSpSend1, s5) := (ops.sendto sp0 (asciiBytes ['a']) { nosignal := true }).run s4
      let (rSpSend2, s6) := (ops.sendto sp0 (asciiBytes ['a']) { nosignal := true }).run s5
      let (rSpRecv, _) := (ops.recvfrom sp0 8 {}).run s6
      NondetTest.assert (rSpSend1 = .error Errno.ECONNREFUSED ∧ rSpSend2 = .error Errno.ENOTCONN ∧
        rSpRecv = .error Errno.EAGAIN)
      let dgPath := asciiBytes ['/', 't', 'm', 'p', '/', 'd', 'g', '.', 's', 'o', 'c', 'k']
      let (rSrvDg, s7) := (ops.socket .unix .dgram nb 0).run s6
      match rSrvDg with
      | .error _ => NondetTest.assert False
      | .ok srvDg =>
        let (_, s8) := (ops.bind srvDg (.unix dgPath)).run s7
        let (rDgConn, s9) := (ops.connect udUnconn (.unix dgPath)).run s8
        match NetState.closeHandle s9 srvDg with
        | .error _ => NondetTest.assert False
        | .ok s10 =>
          let (rBcSm1, s11) := (ops.sendmsg udUnconn #[v4Unconn]).run s10
          let (rBcSm2, s12) := (ops.sendmsg udUnconn #[v4Unconn]).run s11
          NondetTest.assert (rDgConn = .ok () ∧ rBcSm1 = .error Errno.ECONNREFUSED ∧ rBcSm2 = .error Errno.ENOTCONN)
          let (rSc, s13) := (ops.socket .inet .stream nb 0).run s12
          match rSc with
          | .error _ => NondetTest.assert False
          | .ok sc =>
            let selfAddr := SockAddr.ipv4 INADDR_LOOPBACK 55400
            let (rScBind, s14) := (ops.bind sc selfAddr).run s13
            let (rScConn, s15) := (ops.connect sc selfAddr).run s14
            let (rScErr, s16) := (ops.getsockopt sc .error).run s15
            let (rScSend, s17) := (ops.sendto sc (asciiBytes ['s', 'e', 'l', 'f']) { nosignal := true }).run s16
            let (rScRecv, _) := (ops.recvfrom sc 16 {}).run s17
            NondetTest.assert (rScBind = .ok () ∧ rScConn = .error Errno.EINPROGRESS ∧ rScErr = .ok 0 ∧
              rScSend = .ok 4 ∧ rScRecv = .ok (asciiBytes ['s', 'e', 'l', 'f']))
  | _, _, _ => NondetTest.assert False

/-- `NetState` models unconfigured `"lo"` (`!IFF_UP` returning `ENETUNREACH` on TCP/UDP loopback `connect` without queuing onto listeners), `fe80::/10` (`scopeId = 0`) and `ff00::/8` `EINVAL`, and bidirectional `::ffff:127.x.y.z` dual-stack `bind`/`connect`/`accept4`. -/
def test_net_state_loDownLinkLocalAndMappedIpv6
    {runner} [NondetTest runner]
    (ops : NetOpsM (StateM NetState) HandleId := modelOps) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial true
  let (rCtl, s1) := (ops.socket .inet6 .dgram nb 0).run s0
  let (rL4, s2) := (ops.socket .inet .stream nb 0).run s1
  let (rC4, s3) := (ops.socket .inet .stream {} 0).run s2
  let (rU4, s4) := (ops.socket .inet .dgram nb 0).run s3
  match rCtl, rL4, rC4, rU4 with
  | .ok ctl6, .ok l4, .ok c4, .ok u4 =>
    let llNoScope := SockAddr.ipv6 0xfe80000000000000 1 8080 0 0
    let mcastAddr := SockAddr.ipv6 0xff02000000000000 1 8080 0 0
    let (rLlBind, _) := (ops.bind ctl6 llNoScope).run s4
    let (rLlConn, _) := (ops.connect ctl6 llNoScope).run s4
    let (rMcBind, _) := (ops.bind ctl6 mcastAddr).run s4
    NondetTest.assert (rLlBind = .error Errno.EINVAL ∧ rLlConn = .error Errno.EINVAL ∧
      rMcBind = .error Errno.EINVAL)
    let (_, s5) := (ops.ioctl ctl6 (.setIfFlags 0) loIfname).run s4
    let (rBind4, s6) := (ops.bind l4 (.ipv4 INADDR_LOOPBACK 55500)).run s5
    let (rLis4, s7) := (ops.listen l4 4).run s6
    let (rLoDownTcp, s8) := (ops.connect c4 (.ipv4 INADDR_LOOPBACK 55500)).run s7
    let (rLoDownUdp, s9) := (ops.connect u4 (.ipv4 INADDR_LOOPBACK 55500)).run s8
    let (rAccEmpty, s10) := (ops.accept4 l4 nb).run s9
    NondetTest.assert (rBind4 = .ok () ∧ rLis4 = .ok () ∧
      rLoDownTcp = .error Errno.ENETUNREACH ∧ rLoDownUdp = .error Errno.ENETUNREACH ∧
      rAccEmpty = .error Errno.EAGAIN)
    let (_, s11) := (ops.ioctl ctl6 (.setIfFlags IFF_UP) loIfname).run s10
    let (rM6, s12) := (ops.socket .inet6 .stream nb 0).run s11
    let (rC6, s13) := (ops.socket .inet6 .stream {} 0).run s12
    match rM6, rC6 with
    | .ok m6, .ok c6 =>
      let mapped501 := SockAddr.ipv6 0 0x0000ffff7f000001 55501 0 0
      let (rBindM6, s14) := (ops.bind m6 mapped501).run s13
      let (_, s15) := (ops.listen m6 4).run s14
      let (rV4ToM6, s16) := (ops.connect c4 (.ipv4 INADDR_LOOPBACK 55501)).run s15
      let (rAccM6, s17) := (ops.accept4 m6 nb).run s16
      let mapped500 := SockAddr.ipv6 0 0x0000ffff7f000001 55500 0 0
      let (rC6ToV4, s18) := (ops.connect c6 mapped500).run s17
      let (rC6Sa, _) := (ops.getsockname c6).run s18
      let (rAccV4, _) := (ops.accept4 l4 nb).run s18
      NondetTest.assert (rBindM6 = .ok () ∧ rV4ToM6 = .ok () ∧
        (∃ srv6 p6, rAccM6 = .ok (srv6, p6) ∧ p6.domain = .inet6) ∧
        rC6ToV4 = .ok () ∧
        (∃ ep, rC6Sa = .ok (.ipv6 0 0x0000ffff7f000001 ep 0 0) ∧
          (∃ srv4, rAccV4 = .ok (srv4, .ipv4 INADDR_LOOPBACK ep))))
    | _, _ => NondetTest.assert False
  | _, _, _, _ => NondetTest.assert False

/-- `Model.allowedStep` supports lazy OS ephemeral port binding (`bind(port=0)` -> `getsockname`), partial `SOCK_STREAM` `sendto`/`recvfrom` prefix checks, and rejects corrupted stream bytes, duplicate handle allocation, and closed-FD `sendmsg`. -/
def test_net_model_allowedStep_ephemeralAndPartialIoInvariants
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let s0 := NetState.initial false
  NondetTest.assert ((step s0 (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) .unit).isNone)
  NondetTest.assert ((step s0 (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) (.err Errno.EBADF)).isSome)
  match step s0 (.socket .inet .stream { nonblock := true, cloexec := true } 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.socket .inet .stream {} 0) (.opened 0)).isNone)
    match step s1 (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) .unit with
    | none => NondetTest.assert False
    | some s2 =>
      NondetTest.assert ((step s2 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 0))).isNone)
      match step s2 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 34205)) with
      | none => NondetTest.assert False
      | some s3 =>
        NondetTest.assert ((step s3 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 39999))).isNone)
        NondetTest.assert ((step s3 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 34205))).isSome)
        match step s3 (.socketpair .unix .stream { nonblock := true, cloexec := true }) (.pair 1 2) with
        | none => NondetTest.assert False
        | some s4 =>
          NondetTest.assert ((step s4 (.sendmsg 1 #[99]) .unit).isNone)
          NondetTest.assert ((step s4 (.sendmsg 1 #[99]) (.err Errno.EBADF)).isSome)
          match step s4 (.sendto 1 (asciiBytes ['a', 'b', 'c', 'd']) { nosignal := true }) (.u32 3) with
          | none => NondetTest.assert False
          | some s5 =>
            NondetTest.assert ((step s5 (.recvfrom 2 4 {}) (.bytes (asciiBytes ['a', 'x']))).isNone)
            NondetTest.assert ((step s5 (.recvfrom 2 4 {}) (.bytes (ByteArray.mk #[]))).isNone)
            match step s5 (.recvfrom 2 4 {}) (.bytes (asciiBytes ['a', 'b'])) with
            | none => NondetTest.assert False
            | some s6 =>
              match step s6 (.recvfrom 2 4 {}) (.bytes (asciiBytes ['c'])) with
              | none => NondetTest.assert False
              | some s6c =>
                match step s6c (.socket .inet .stream { nonblock := true, cloexec := true } 0) (.opened 3) with
                | none => NondetTest.assert False
                | some s7 =>
                  match step s7 (.connect 3 (.ipv4 0xc0000201 80)) (.err Errno.EINPROGRESS) with
                  | none => NondetTest.assert False
                  | some s8 =>
                    match step s8 (.getsockopt 3 .error) (.u32 0) with
                    | none => NondetTest.assert False
                    | some s9 =>
                      match step s9 (.getsockopt 3 .error) (.u32 Errno.ETIMEDOUT) with
                      | none => NondetTest.assert False
                      | some s10 =>
                        NondetTest.assert ((step s10 (.connect 3 (.ipv4 0xc0000201 80)) (.err Errno.ECONNABORTED)).isSome)
                        match step s10 (.sendmsg 1 #[0, 3]) .unit with
                        | none => NondetTest.assert False
                        | some s11 =>
                          NondetTest.assert ((step s11 (.recvmsg 2 2) (.fds #[4, 5, 6])).isNone)
                          NondetTest.assert ((step s11 (.recvmsg 2 2) (.fds #[4])).isNone)
                          NondetTest.assert ((step s11 (.recvmsg 2 2) (.fds #[4, 5])).isSome)
                          NondetTest.assert ((step s11 (.recvmsg 2 1) (.err Errno.EPROTO)).isSome)

/-- `NetState.ambientSeccomp = true` permits safe seccomp errnos (`1..4095 \ {EFAULT}`) iff `reachesKernelSyscall` holds, rejecting `EFAULT`, `0`, `4096`, invalid wrapper args (`preCheckNet`), and closed FDs (`EBADF`). -/
def test_net_model_ambientSeccomp
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let sSec := NetState.initial false true
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err Errno.EPERM)).isSome)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err Errno.EACCES)).isSome)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err Errno.ENOSYS)).isSome)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err 4095)).isSome)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err Errno.EFAULT)).isNone)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err 0)).isNone)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 0) (.err 4096)).isNone)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 262) (.err Errno.EPERM)).isNone)
  NondetTest.assert ((step sSec (.socket .inet .stream {} 262) (.err Errno.EPROTONOSUPPORT)).isSome)
  NondetTest.assert ((step sSec (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) (.err Errno.EPERM)).isNone)
  NondetTest.assert ((step sSec (.bind 0 (.ipv4 INADDR_LOOPBACK 0)) (.err Errno.EBADF)).isSome)
  match step sSec (.socket .inet .stream { nonblock := true, cloexec := true } 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.listen 0 4) (.err Errno.EPERM)).isSome)
    NondetTest.assert ((step s1 (.bind 0 (.unix (ByteArray.mk #[]))) (.err Errno.EPERM)).isNone)
    NondetTest.assert ((step s1 (.sendmsg 0 #[0, 99]) (.err Errno.EPERM)).isNone)

/-- Kernel socket semantics for multicast/broadcast `bind` (`.unit`) vs non-local unicast (`EADDRNOTAVAIL`), dual-stack `::` vs `0.0.0.0` & `127.0.0.1` vs `::ffff:127.0.0.1` `EADDRINUSE`, pre-listen `SHUT_RD` allowing `listen`/`accept4`, `ssConnecting` `shutdown`, listener `shutdown(SHUT_RD)` returning `.unit`, 4-way FIN close preserving unread RX, and `AF_UNIX` bind filesystem errnos. -/
def test_net_model_bindDualStackShutdownAndFinInvariants
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let s0 := NetState.initial false
  match step s0 (.socket .inet .dgram {} 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.bind 0 (.ipv4 0xe0000001 8080)) .unit).isSome)
    NondetTest.assert ((step s1 (.bind 0 (.ipv4 0xffffffff 8080)) .unit).isSome)
    NondetTest.assert ((step s1 (.bind 0 (.ipv4 0xc0000201 8080)) (.err Errno.EADDRNOTAVAIL)).isSome)
    NondetTest.assert ((step s1 (.bind 0 (.ipv4 0xc0000201 8080)) .unit).isNone)
    match step s1 (.socket .inet6 .stream { nonblock := true, cloexec := true } 0) (.opened 1) with
    | none => NondetTest.assert False
    | some s2 =>
      match step s2 (.socket .inet .stream { nonblock := true, cloexec := true } 0) (.opened 2) with
      | none => NondetTest.assert False
      | some s3 =>
        match step s3 (.bind 1 (.ipv6 0 0 56100 0 0)) .unit with
        | none => NondetTest.assert False
        | some s4 =>
          NondetTest.assert ((step s4 (.bind 2 (.ipv4 INADDR_ANY 56100)) (.err Errno.EADDRINUSE)).isSome)
          NondetTest.assert ((step s4 (.bind 2 (.ipv4 INADDR_ANY 56100)) .unit).isNone)
          match step s4 (.shutdown 2 .rd) (.err Errno.ENOTCONN) with
          | none => NondetTest.assert False
          | some s5 =>
            match step s5 (.bind 2 (.ipv4 INADDR_LOOPBACK 56101)) .unit with
            | none => NondetTest.assert False
            | some s6 =>
              match step s6 (.listen 2 4) .unit with
              | none => NondetTest.assert False
              | some s7 =>
                match step s7 (.socket .inet .stream { nonblock := true, cloexec := true } 0) (.opened 3) with
                | none => NondetTest.assert False
                | some s8 =>
                  match step s8 (.connect 3 (.ipv4 INADDR_LOOPBACK 56101)) .unit with
                  | none => NondetTest.assert False
                  | some s9 =>
                    NondetTest.assert ((step s9 (.accept4 2 {}) (.opened 4)).isNone)
                    match step s9 (.accept4 2 {}) (.accepted 4 (.ipv4 INADDR_LOOPBACK 49152)) with
                    | none => NondetTest.assert False
                    | some s10 =>
                      match step s10 (.sendto 4 (asciiBytes ['h', 'i']) {}) (.u32 2) with
                      | none => NondetTest.assert False
                      | some s11 =>
                        match step s11 (.shutdown 4 .wr) .unit with
                        | none => NondetTest.assert False
                        | some s12 =>
                          NondetTest.assert ((step s12 (.recvfrom 3 4 {}) (.bytes (asciiBytes ['h', 'i']))).isSome)
                          NondetTest.assert ((step s7 (.shutdown 2 .rd) .unit).isSome)
                          match step s7 (.socket .unix .dgram {} 0) (.opened 5) with
                          | none => NondetTest.assert False
                          | some s13 =>
                            let uPath := SockAddr.unix (asciiBytes ['/', 't', 'm', 'p', '/', 'u', 'x'])
                            NondetTest.assert ((step s13 (.bind 5 uPath) (.err Errno.ENOENT)).isSome)
                            NondetTest.assert ((step s13 (.bind 5 uPath) (.err Errno.EACCES)).isSome)

/-- Deterministic `stepNetCore s req none` output is universally accepted by `allowedStep` (`modelOps` soundness). -/
def test_net_model_stepCoreSound
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let s ← nondet NetState
  let req ← nondet NetReq
  let out ← nondet NetOutcome
  let s' ← nondet NetState
  assume (stepNetCore s req none = some (out, s'))
  NondetTest.assert (step s req out = some s')

/-- `Internal.mkNetOpsM` enforces `validateSocketArgs` and `validateSocketpairArgs` and faithfully encodes/decodes all tags, flags, `RawSockAddrTuple` lanes, `SCM_RIGHTS` bounds, and `ioctl` tuples across all 15 `NetOpsM` methods. -/
def test_net_mkNetOps_encodesAndDelegates
    {runner} [NondetTest runner]
    (mkOps : PosixNetOpsM Id Nat → NetOpsM Id Nat) : runner Unit := do
  let raw ← nondet (PosixNetOpsM Id Nat)
  let dom ← nondet SockDomain
  let typ ← nondet SockType
  let sf ← nondet SockFlags
  let proto ← nondet UInt32
  let fd ← nondet Nat
  let validAddr ← nondet SockAddr
  assume (validAddr.isValidTarget = true)
  let backlog ← nondet UInt32
  let opt ← nondet SockOpt
  let setOpt ← nondet SetSockOpt
  let optVal ← nondet UInt32
  let maxBytes ← nondet UInt32
  let mf ← nondet MsgFlags
  let payload ← nondet ByteArray
  let how ← nondet ShutHow
  let validFds ← nondet (Array Nat)
  assume (isValidScmCount validFds.size = true)
  let validMaxFds ← nondet UInt32
  assume (isValidScmCount validMaxFds.toNat = true)
  let ioOp ← nondet NetIoctlOp
  let validIf ← nondet ByteArray
  assume (isValidIfname validIf = true)
  let ops := mkOps raw
  let expSock : Except Errno Nat :=
    match validateSocketArgs dom typ proto with
    | some e => .error e
    | none => raw.socket dom.toTag typ.toTag sf.toBits proto
  let expPair : Except Errno (Nat × Nat) :=
    match validateSocketpairArgs dom typ with
    | some e => .error e
    | none => raw.socketpair dom.toTag typ.toTag sf.toBits
  let expAcc : Except Errno (Nat × SockAddr) :=
    match raw.accept4 fd sf.toBits with
    | .ok (cfd, rawSa) => .ok (cfd, SockAddr.ofRawTuple rawSa)
    | .error e => .error e
  let expGsn : Except Errno SockAddr :=
    match raw.getsockname fd with
    | .ok rawSa => .ok (SockAddr.ofRawTuple rawSa)
    | .error e => .error e
  NondetTest.assert (ops.socket dom typ sf proto = expSock)
  NondetTest.assert (ops.socketpair dom typ sf = expPair)
  NondetTest.assert (ops.bind fd validAddr = raw.bind fd validAddr.toRawTuple)
  NondetTest.assert (ops.listen fd backlog = raw.listen fd backlog)
  NondetTest.assert (ops.accept4 fd sf = expAcc)
  NondetTest.assert (ops.connect fd validAddr = raw.connect fd validAddr.toRawTuple)
  NondetTest.assert (ops.getsockopt fd opt = raw.getsockopt fd opt.toTag)
  NondetTest.assert (ops.setsockopt fd setOpt optVal = raw.setsockopt fd setOpt.toTag optVal)
  NondetTest.assert (ops.getsockname fd = expGsn)
  NondetTest.assert (ops.recvfrom fd maxBytes mf = raw.recvfrom fd maxBytes mf.toBits)
  NondetTest.assert (ops.sendto fd payload mf = raw.sendto fd payload mf.toBits)
  NondetTest.assert (ops.shutdown fd how = raw.shutdown fd how.toTag)
  NondetTest.assert (ops.sendmsg fd validFds = raw.sendmsg fd validFds)
  NondetTest.assert (ops.recvmsg fd validMaxFds = raw.recvmsg fd validMaxFds)
  NondetTest.assert (ops.ioctl fd ioOp validIf = raw.ioctl fd (ioOp.toRaw).1 (ioOp.toRaw).2 validIf)

/-- `Net.defaultOps` is constructed via `Internal.mkNetOps`, and all 15 top-level `Net` functions delegate directly to `defaultOps` with exact `SOCK_CLOEXEC` and `MSG_NOSIGNAL` defaults. -/
def test_net_interface_defaultOpsWiring
    {m : Type → Type} {fd : Type} {runner} [NondetTest runner]
    (mkOps : PosixNetOpsM m fd → NetOpsM m fd)
    (ops : NetOpsM m fd)
    (socketFn : SockDomain → SockType → SockFlags → UInt32 → m (Except Errno fd))
    (socketDefault : SockDomain → SockType → m (Except Errno fd))
    (socketpairFn : SockDomain → SockType → SockFlags → m (Except Errno (fd × fd)))
    (socketpairDefault : SockDomain → SockType → m (Except Errno (fd × fd)))
    (bindFn : fd → SockAddr → m (Except Errno Unit))
    (listenFn : fd → UInt32 → m (Except Errno Unit))
    (listenDefault : fd → m (Except Errno Unit))
    (accept4Fn : fd → SockFlags → m (Except Errno (fd × SockAddr)))
    (accept4Default : fd → m (Except Errno (fd × SockAddr)))
    (connectFn : fd → SockAddr → m (Except Errno Unit))
    (getsockoptFn : fd → SockOpt → m (Except Errno UInt32))
    (setsockoptFn : fd → SetSockOpt → UInt32 → m (Except Errno Unit))
    (getsocknameFn : fd → m (Except Errno SockAddr))
    (recvfromFn : fd → UInt32 → MsgFlags → m (Except Errno ByteArray))
    (recvfromDefault : fd → UInt32 → m (Except Errno ByteArray))
    (sendtoFn : fd → ByteArray → MsgFlags → m (Except Errno UInt32))
    (sendtoDefault : fd → ByteArray → m (Except Errno UInt32))
    (shutdownFn : fd → ShutHow → m (Except Errno Unit))
    (sendmsgFn : fd → Array fd → m (Except Errno Unit))
    (recvmsgFn : fd → UInt32 → m (Except Errno (Array fd)))
    (ioctlFn : fd → NetIoctlOp → ByteArray → m (Except Errno UInt32)) : runner Unit := do
  let dom ← nondet SockDomain
  let typ ← nondet SockType
  let sf ← nondet SockFlags
  let proto ← nondet UInt32
  let h ← nondet fd
  let sa ← nondet SockAddr
  let bl ← nondet UInt32
  let opt ← nondet SockOpt
  let setOpt ← nondet SetSockOpt
  let val ← nondet UInt32
  let maxB ← nondet UInt32
  let mf ← nondet MsgFlags
  let data ← nondet ByteArray
  let how ← nondet ShutHow
  let fds ← nondet (Array fd)
  let maxF ← nondet UInt32
  let ioOp ← nondet NetIoctlOp
  let ifn ← nondet ByteArray
  NondetTest.assert (∃ raw : PosixNetOpsM m fd, ops = mkOps raw)
  NondetTest.assert (socketFn dom typ sf proto = ops.socket dom typ sf proto)
  NondetTest.assert (socketDefault dom typ = ops.socket dom typ { nonblock := false, cloexec := true } 0)
  NondetTest.assert (socketpairFn dom typ sf = ops.socketpair dom typ sf)
  NondetTest.assert (socketpairDefault dom typ = ops.socketpair dom typ { nonblock := false, cloexec := true })
  NondetTest.assert (bindFn h sa = ops.bind h sa)
  NondetTest.assert (listenFn h bl = ops.listen h bl)
  NondetTest.assert (listenDefault h = ops.listen h 128)
  NondetTest.assert (accept4Fn h sf = ops.accept4 h sf)
  NondetTest.assert (accept4Default h = ops.accept4 h { nonblock := false, cloexec := true })
  NondetTest.assert (connectFn h sa = ops.connect h sa)
  NondetTest.assert (getsockoptFn h opt = ops.getsockopt h opt)
  NondetTest.assert (setsockoptFn h setOpt val = ops.setsockopt h setOpt val)
  NondetTest.assert (getsocknameFn h = ops.getsockname h)
  NondetTest.assert (recvfromFn h maxB mf = ops.recvfrom h maxB mf)
  NondetTest.assert (recvfromDefault h maxB = ops.recvfrom h maxB { nosignal := false, dontwait := false, peek := false })
  NondetTest.assert (sendtoFn h data mf = ops.sendto h data mf)
  NondetTest.assert (sendtoDefault h data = ops.sendto h data { nosignal := true, dontwait := false, peek := false })
  NondetTest.assert (shutdownFn h how = ops.shutdown h how)
  NondetTest.assert (sendmsgFn h fds = ops.sendmsg h fds)
  NondetTest.assert (recvmsgFn h maxF = ops.recvmsg h maxF)
  NondetTest.assert (ioctlFn h ioOp ifn = ops.ioctl h ioOp ifn)

/-- `Model.allowedStep` matches Linux kernel `sk->sk_bound_dev_if` link-local `sin6_scope_id` sticky binding, `ff02::/16` (`scopeId = 0`) TCP `ENETUNREACH`, `v4MappedTainted` listener child `RST` drop on native `[::1]` peers, and `lo`-was-up broadcast/multicast local-address rewrite. -/
def test_net_model_boundScopeTaintedRstAndBcastRewrite
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial false
  match step s0 (.socket .inet6 .stream nb 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    NondetTest.assert ((step s1 (.connect 0 (.ipv6 0xff02000000000000 1 8080 0 0)) (.err Errno.ENETUNREACH)).isSome)
    match step s1 (.connect 0 (.ipv6 0xfe80000000000000 1 8080 0 999)) (.err Errno.ENETUNREACH) with
    | none => NondetTest.assert False
    | some sSc =>
      NondetTest.assert ((step sSc (.connect 0 (.ipv6 0 0x0000ffff7f000001 8080 0 0)) (.err Errno.ENODEV)).isSome)
      NondetTest.assert ((step sSc (.connect 0 (.ipv6 0 1 8080 0 0)) (.err Errno.ENETUNREACH)).isSome)
      match step sSc (.listen 0 1) .unit with
      | none => NondetTest.assert False
      | some sLis =>
        match step sLis (.getsockname 0) (.addr (.ipv6 0 0 55600 0 0)) with
        | none => NondetTest.assert False
        | some sGsn =>
          match step sGsn (.socket .inet6 .stream nb 0) (.opened 1) with
          | none => NondetTest.assert False
          | some sCli0 =>
            match step sCli0 (.connect 1 (.ipv6 0 1 55600 0 0)) (.err Errno.EINPROGRESS) with
            | none => NondetTest.assert False
            | some sCli1 =>
              NondetTest.assert ((step sCli1 (.recvfrom 1 0 {}) (.err Errno.ECONNREFUSED)).isSome)
              match step s1 (.connect 0 (.ipv6 0 0x0000ffff7f000001 1 0 0)) (.err Errno.ECONNREFUSED) with
              | none => NondetTest.assert False
              | some sTaint =>
                match step sTaint (.listen 0 1) .unit with
                | none => NondetTest.assert False
                | some sTLis =>
                  match step sTLis (.getsockname 0) (.addr (.ipv6 0 0 55601 0 0)) with
                  | none => NondetTest.assert False
                  | some sTGsn =>
                    match step sTGsn (.socket .inet6 .stream nb 0) (.opened 1) with
                    | none => NondetTest.assert False
                    | some sTC0 =>
                      match step sTC0 (.connect 1 (.ipv6 0 1 55601 0 0)) (.err Errno.EINPROGRESS) with
                      | none => NondetTest.assert False
                      | some sTC1 =>
                        match step sTC1 (.accept4 0 nb) (.accepted 2 (.ipv6 0 1 55602 0 0)) with
                        | none => NondetTest.assert False
                        | some sTA =>
                          match step sTA (.sendto 1 (asciiBytes ['A']) { nosignal := true }) (.u32 1) with
                          | none => NondetTest.assert False
                          | some sTS =>
                            match NetState.closeHandle sTS 2 with
                            | .error _ => NondetTest.assert False
                            | .ok sTClosed =>
                              NondetTest.assert ((step sTClosed (.getsockopt 1 .error) (.u32 0)).isSome)
                              let sLoWasUp : NetState := { NetState.initial true with loState := .down IFF_LOOPBACK true }
                              match step sLoWasUp (.socket .inet .stream nb 0) (.opened 0) with
                              | none => NondetTest.assert False
                              | some sB0 =>
                                match step sB0 (.bind 0 (.ipv4 0xffffffff 0)) .unit with
                                | none => NondetTest.assert False
                                | some sB1 =>
                                  match step sB1 (.getsockname 0) (.addr (.ipv4 0xffffffff 37505)) with
                                  | none => NondetTest.assert False
                                  | some sB2 =>
                                    match step sB2 (.connect 0 (.ipv4 INADDR_LOOPBACK 55603)) (.err Errno.EINPROGRESS) with
                                    | none => NondetTest.assert False
                                    | some sB3 =>
                                      NondetTest.assert ((step sB3 (.getsockname 0) (.addr (.ipv4 INADDR_LOOPBACK 37505))).isSome)

/-- `Model.allowedStep` matches Linux `7.1.6` kernel socket invariants: sticky `sk_bound_dev_if` across `bind` and UDP (`fe80::/10`, `ff02::/16`, `[::]:0` wildcard bypass, scope override), IPv4-mapped `AF_INET6` `connect` to `[::]:port`, auto-bound `[::1]:ep` UDP reconnect to `::ffff:127.0.0.1` wire source matching, synchronous `tcp_v4_connect` untainting (`ENETUNREACH`), and `AF_INET6` `::ffff:*:0` UDP `sendto` `EINVAL`. -/
def test_net_model_stickyScopeMappedWildcardAndUntaint
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial true
  match step s0 (.socket .inet6 .stream nb 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    match step s1 (.connect 0 (.ipv6 0xfe80000000000000 1 8080 0 999)) (.err Errno.ENETUNREACH) with
    | none => NondetTest.assert False
    | some sSc999 =>
      NondetTest.assert ((step sSc999 (.bind 0 (.ipv6 0 1 0 0 0)) (.err Errno.ENODEV)).isSome)
      NondetTest.assert ((step sSc999 (.bind 0 (.ipv6 0 0 0 0 0)) .unit).isSome)
      match step sSc999 (.bind 0 (.ipv6 0xfe80000000000000 1 0 0 1)) (.err Errno.EADDRNOTAVAIL) with
      | none => NondetTest.assert False
      | some sSc1 =>
        NondetTest.assert ((step sSc1 (.bind 0 (.ipv6 0 1 0 0 0)) .unit).isSome)
        match step s1 (.socket .inet6 .dgram nb 0) (.opened 1) with
        | none => NondetTest.assert False
        | some sU0 =>
          match step sU0 (.bind 1 (.ipv6 0xff02000000000000 1 0 0 999)) (.err Errno.ENODEV) with
          | none => NondetTest.assert False
          | some sUMc =>
            NondetTest.assert ((step sUMc (.connect 1 (.ipv6 0 1 5555 0 0)) (.err Errno.ENETUNREACH)).isSome)
            match step s0 (.socket .inet6 .stream nb 0) (.opened 0) with
            | none => NondetTest.assert False
            | some sL0 =>
              match step sL0 (.bind 0 (.ipv6 0 0 55700 0 0)) .unit with
              | none => NondetTest.assert False
              | some sL1 =>
                match step sL1 (.listen 0 4) .unit with
                | none => NondetTest.assert False
                | some sL2 =>
                  match step sL2 (.socket .inet6 .stream {} 0) (.opened 1) with
                  | none => NondetTest.assert False
                  | some sM0 =>
                    match step sM0 (.bind 1 (.ipv6 0 0x0000ffff7f000001 0 0 0)) .unit with
                    | none => NondetTest.assert False
                    | some sM1 =>
                      NondetTest.assert ((step sM1 (.connect 1 (.ipv6 0 0 55700 0 0)) .unit).isSome)
                      match step s0 (.socket .inet6 .dgram nb 0) (.opened 0) with
                      | none => NondetTest.assert False
                      | some sD0 =>
                        match step sD0 (.connect 0 (.ipv6 0 1 9 0 0)) .unit with
                        | none => NondetTest.assert False
                        | some sD1 =>
                          match step sD1 (.getsockname 0) (.addr (.ipv6 0 1 42424 0 0)) with
                          | none => NondetTest.assert False
                          | some sD2 =>
                            match step sD2 (.socket .inet .dgram nb 0) (.opened 1) with
                            | none => NondetTest.assert False
                            | some sD3 =>
                              match step sD3 (.bind 1 (.ipv4 INADDR_LOOPBACK 55701)) .unit with
                              | none => NondetTest.assert False
                              | some sD4 =>
                                match step sD4 (.connect 1 (.ipv4 INADDR_LOOPBACK 42424)) .unit with
                                | none => NondetTest.assert False
                                | some sD5 =>
                                  match step sD5 (.connect 0 (.ipv6 0 0x0000ffff7f000001 55701 0 0)) .unit with
                                  | none => NondetTest.assert False
                                  | some sD6 =>
                                    match step sD6 (.sendto 0 (asciiBytes ['z']) { nosignal := true }) (.u32 1) with
                                    | none => NondetTest.assert False
                                    | some sD7 =>
                                      NondetTest.assert ((step sD7 (.recvfrom 1 8 {}) (.bytes (asciiBytes ['z']))).isSome)
                                      match step sD7 (.connect 0 (.ipv6 0 0x0000ffff7f000001 0 0 0)) .unit with
                                      | none => NondetTest.assert False
                                      | some sDP0 =>
                                        NondetTest.assert ((step sDP0 (.sendto 0 (asciiBytes ['x']) { nosignal := true }) (.err Errno.EINVAL)).isSome)
                                        match step s1 (.connect 0 (.ipv6 0 0x0000ffff7f000001 1 0 0)) (.err Errno.EINPROGRESS) with
                                        | none => NondetTest.assert False
                                        | some sT1 =>
                                          match step sT1 (.connect 0 (.ipv6 0 0x0000ffff7f000001 1 0 0)) (.err Errno.ECONNREFUSED) with
                                          | none => NondetTest.assert False
                                          | some sT2 =>
                                            match step sT2 (.connect 0 (.ipv6 0 0x0000ffffc0000201 80 0 0)) (.err Errno.ENETUNREACH) with
                                            | none => NondetTest.assert False
                                            | some sT3 =>
                                              match step sT3 (.connect 0 (.ipv6 0 1 1 0 0)) (.err Errno.EINPROGRESS) with
                                              | none => NondetTest.assert False
                                              | some sT4 =>
                                                NondetTest.assert ((step sT4 (.sendto 0 (asciiBytes ['q']) { dontwait := true, nosignal := true }) (.err Errno.ECONNREFUSED)).isSome)

/-- `Model.allowedStep` matches Linux `7.1.6` kernel socket invariants for multicast/broadcast-bound UDP loopback wire-source matching (`224.0.0.1` -> `127.0.0.1`, `ff02::1%1` -> `::1`), IPv4-mapped `AF_INET6` `connect` to non-`[::1]` native IPv6 (`ff05::1`) returning `EAFNOSUPPORT`, `boundDevIf > 1` synchronous `tcp_v6_connect(::ffff:*)` untainting via `late_failure:`, non-`lo` `ifindex > 1` (`2`) `bind`/UDP `connect`/`sendto`/`getsockname` scope resolution, and `.synSent` `shutdown` resetting unlocked routed IPv4/IPv6 local addresses to `0.0.0.0` / `[::%0]`. -/
def test_net_model_mcastMappedScopeAndSynReset
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial false
  match step s0 (.socket .inet .dgram nb 0) (.opened 0) with
  | none => NondetTest.assert False
  | some sM1 =>
    match step sM1 (.socket .inet .dgram nb 0) (.opened 1) with
    | none => NondetTest.assert False
    | some sM2 =>
      match step sM2 (.bind 0 (.ipv4 0xe0000001 44100)) .unit with
      | none => NondetTest.assert False
      | some sM3 =>
        match step sM3 (.bind 1 (.ipv4 INADDR_LOOPBACK 44101)) .unit with
        | none => NondetTest.assert False
        | some sM4 =>
          match step sM4 (.connect 1 (.ipv4 INADDR_LOOPBACK 44100)) .unit with
          | none => NondetTest.assert False
          | some sM5 =>
            match step sM5 (.connect 0 (.ipv4 INADDR_LOOPBACK 44101)) .unit with
            | none => NondetTest.assert False
            | some sM6 =>
              match step sM6 (.sendto 0 (asciiBytes ['m']) { nosignal := true }) (.u32 1) with
              | none => NondetTest.assert False
              | some sM7 =>
                NondetTest.assert ((step sM7 (.recvfrom 1 8 { dontwait := true }) (.bytes (asciiBytes ['m']))).isSome)
                match step s0 (.socket .inet6 .dgram nb 0) (.opened 0) with
                | none => NondetTest.assert False
                | some sA1 =>
                  match step sA1 (.bind 0 (.ipv6 0 0x0000ffff7f000001 44102 0 0)) .unit with
                  | none => NondetTest.assert False
                  | some sA2 =>
                    NondetTest.assert ((step sA2 (.connect 0 (.ipv6 0xff05000000000000 1 8080 0 0)) (.err Errno.EAFNOSUPPORT)).isSome)
                    NondetTest.assert ((step sA2 (.connect 0 (.ipv6 0xff05000000000000 1 8080 0 0)) .unit).isNone)
                    match step s0 (.socket .inet6 .stream nb 0) (.opened 0) with
                    | none => NondetTest.assert False
                    | some sL1 =>
                      match step sL1 (.bind 0 (.ipv6 0 1 55800 0 0)) .unit with
                      | none => NondetTest.assert False
                      | some sL2 =>
                        match step sL2 (.listen 0 4) .unit with
                        | none => NondetTest.assert False
                        | some sL3 =>
                          match step sL3 (.socket .inet6 .stream {} 0) (.opened 1) with
                          | none => NondetTest.assert False
                          | some sU1 =>
                            match step sU1 (.connect 1 (.ipv6 0xfe80000000000000 1 8080 0 999)) (.err Errno.ENETUNREACH) with
                            | none => NondetTest.assert False
                            | some sU2 =>
                              match step sU2 (.connect 1 (.ipv6 0 0x0000ffff7f000001 55800 0 0)) (.err Errno.ENODEV) with
                              | none => NondetTest.assert False
                              | some sU3 =>
                                match step sU3 (.bind 1 (.ipv6 0xfe80000000000000 1 0 0 1)) (.err Errno.EADDRNOTAVAIL) with
                                | none => NondetTest.assert False
                                | some sU4 =>
                                  NondetTest.assert ((step sU4 (.connect 1 (.ipv6 0 1 55800 0 0)) .unit).isSome)
                                  match step s0 (.socket .inet6 .dgram nb 0) (.opened 0) with
                                  | none => NondetTest.assert False
                                  | some sE1 =>
                                    NondetTest.assert ((step sE1 (.bind 0 (.ipv6 0xff02000000000000 1 0 0 2)) .unit).isSome)
                                    match step sE1 (.connect 0 (.ipv6 0xfe80000000000000 1 8080 0 2)) .unit with
                                    | none => NondetTest.assert False
                                    | some sE2 =>
                                      match step sE2 (.getsockname 0) (.addr (.ipv6 0xfe80000000000000 9 41234 0 2)) with
                                      | none => NondetTest.assert False
                                      | some sE3 =>
                                        NondetTest.assert ((step sE3 (.sendto 0 (asciiBytes ['h', 'i']) { nosignal := true }) (.u32 2)).isSome)
                                        match step s0 (.socket .inet .stream nb 0) (.opened 0) with
                                        | none => NondetTest.assert False
                                        | some sR1 =>
                                          match step sR1 (.connect 0 (.ipv4 0xc0000201 80)) (.err Errno.EINPROGRESS) with
                                          | none => NondetTest.assert False
                                          | some sR2 =>
                                            match step sR2 (.getsockname 0) (.addr (.ipv4 0xac100005 51234)) with
                                            | none => NondetTest.assert False
                                            | some sR3 =>
                                              match step sR3 (.shutdown 0 .rdwr) .unit with
                                              | none => NondetTest.assert False
                                              | some sR4 =>
                                                NondetTest.assert ((step sR4 (.getsockname 0) (.addr (.ipv4 0 51234))).isSome)

/-- `Model.allowedStep` matches Linux `7.1.6` kernel socket invariants for `v4MappedTainted` listener teardown `RST` drop on unaccepted native `[::1]` clients, tainted `CLOSE_WAIT` `ip_queue_xmit` TX drop and unacked-data `FIN` delay, `TCP_LAST_ACK` / `TCP_CLOSING` hashed-port retention without spurious `FIN` `ECONNRESET`, `boundDevIf > 1` / `fe80::/10` `bind` after async refused `connect`, and multicast/broadcast-bound IPv4 TCP host-routed `inet_saddr` persistence across `shutdown` and loopback reconnect. -/
def test_net_model_taintedAbortLastAckAndMcastRouted
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial true
  match step s0 (.socket .inet6 .stream {} 0) (.opened 0) with
  | none => NondetTest.assert False
  | some sT0 =>
    match step sT0 (.connect 0 (.ipv6 0 0x0000ffff7f000001 1 0 0)) (.err Errno.ECONNREFUSED) with
    | none => NondetTest.assert False
    | some sT1 =>
      match step sT1 (.listen 0 4) .unit with
      | none => NondetTest.assert False
      | some sT2 =>
        match step sT2 (.getsockname 0) (.addr (.ipv6 0 0 55900 0 0)) with
        | none => NondetTest.assert False
        | some sT3 =>
          match step sT3 (.socket .inet6 .stream nb 0) (.opened 1) with
          | none => NondetTest.assert False
          | some sT4 =>
            match step sT4 (.connect 1 (.ipv6 0 1 55900 0 0)) (.err Errno.EINPROGRESS) with
            | none => NondetTest.assert False
            | some sQueued =>
              match NetState.closeHandle sQueued 0 with
              | .error _ => NondetTest.assert False
              | .ok sLisClosed =>
                NondetTest.assert ((step sLisClosed (.connect 1 (.ipv6 0 1 55900 0 0)) .unit).isSome)
                match step sQueued (.accept4 0 nb) (.accepted 2 (.ipv6 0 1 49153 0 0)) with
                | none => NondetTest.assert False
                | some sAcc =>
                  match step sAcc (.sendto 1 (asciiBytes ['a']) { nosignal := true }) (.u32 1) with
                  | none => NondetTest.assert False
                  | some sData =>
                    match NetState.closeHandle sData 1 with
                    | .error _ => NondetTest.assert False
                    | .ok sCw0 =>
                      match step sCw0 (.recvfrom 2 8 {}) (.bytes (asciiBytes ['a'])) with
                      | none => NondetTest.assert False
                      | some sCw1 =>
                        NondetTest.assert ((step sCw1 (.recvfrom 2 8 {}) (.err Errno.EAGAIN)).isSome)
                        match step sCw1 (.sendto 2 (asciiBytes ['r']) { nosignal := true }) (.u32 1) with
                        | none => NondetTest.assert False
                        | some sCwTx =>
                          NondetTest.assert ((step sCwTx (.getsockopt 2 .error) (.u32 0)).isSome)
                          match step sCwTx (.shutdown 2 .wr) .unit with
                          | none => NondetTest.assert False
                          | some sLastAck =>
                            NondetTest.assert ((step sLastAck (.shutdown 2 .rd) .unit).isSome)
                            match step sAcc (.connect 1 (.ipv6 0 1 55900 0 0)) .unit with
                            | none => NondetTest.assert False
                            | some sEst =>
                              match step sEst (.shutdown 2 .rdwr) .unit with
                              | none => NondetTest.assert False
                              | some sFw =>
                                match step sFw (.shutdown 1 .wr) .unit with
                                | none => NondetTest.assert False
                                | some sClosing =>
                                  NondetTest.assert ((step sClosing (.getsockopt 1 .error) (.u32 0)).isSome ∧
                                    (step sClosing (.shutdown 2 .rd) .unit).isSome)
                                  match step s0 (.socket .inet6 .stream nb 0) (.opened 0) with
                                  | none => NondetTest.assert False
                                  | some sB0 =>
                                    match step sB0 (.connect 0 (.ipv6 0xfe80000000000000 1 55901 0 2)) (.err Errno.EINPROGRESS) with
                                    | none => NondetTest.assert False
                                    | some sB1 =>
                                      NondetTest.assert ((step sB1 (.bind 0 (.ipv6 0xfe80000000000000 9 0 0 2)) .unit).isSome)
                                      match step s0 (.socket .inet .stream nb 0) (.opened 0) with
                                      | none => NondetTest.assert False
                                      | some sM0 =>
                                        match step sM0 (.bind 0 (.ipv4 INADDR_LOOPBACK 55902)) .unit with
                                        | none => NondetTest.assert False
                                        | some sM1 =>
                                          match step sM1 (.listen 0 4) .unit with
                                          | none => NondetTest.assert False
                                          | some sM2 =>
                                            match step sM2 (.socket .inet .stream nb 0) (.opened 1) with
                                            | none => NondetTest.assert False
                                            | some sM3 =>
                                              match step sM3 (.bind 1 (.ipv4 0xe0000001 44200)) .unit with
                                              | none => NondetTest.assert False
                                              | some sM4 =>
                                                match step sM4 (.connect 1 (.ipv4 0xc0000201 80)) (.err Errno.EINPROGRESS) with
                                                | none => NondetTest.assert False
                                                | some sM5 =>
                                                  NondetTest.assert ((step sM5 (.getsockname 1) (.addr (.ipv4 0xac100005 44200))).isSome)
                                                  match step sM5 (.shutdown 1 .rdwr) .unit with
                                                  | none => NondetTest.assert False
                                                  | some sM6 =>
                                                    match step sM6 (.connect 1 (.ipv4 INADDR_LOOPBACK 55902)) (.err Errno.EINPROGRESS) with
                                                    | none => NondetTest.assert False
                                                    | some sM7 =>
                                                      NondetTest.assert ((step sM7 (.accept4 0 nb) (.accepted 2 (.ipv4 0xac100005 44200))).isSome)
                                                      let blk : SockFlags := { nonblock := false, cloexec := true }
                                                      let v4m0 (p : UInt16) : SockAddr := .ipv6 0 0x0000ffff00000000 p 0 0
                                                      let v4mLo (p : UInt16) : SockAddr := .ipv6 0 0x0000ffff7f000001 p 0 0
                                                      let v4mExt (p : UInt16) : SockAddr := .ipv6 0 0x0000ffffc0000201 p 0 0
                                                      let v4mHost (p : UInt16) : SockAddr := .ipv6 0 0x0000ffffac10e795 p 0 0
                                                      let chkV4mBlk : Option NetState := do
                                                        let q1 ← step s0 (.socket .inet6 .stream blk 0) (.opened 0)
                                                        let q2 ← step q1 (.bind 0 (v4m0 0)) .unit
                                                        let q3 ← step q2 (.connect 0 (v4mLo 1)) (.err Errno.ECONNREFUSED)
                                                        step q3 (.getsockname 0) (.addr (v4mLo 49152))
                                                      NondetTest.assert chkV4mBlk.isSome
                                                      let chkV4mRouted : Option NetState := do
                                                        let u1 ← step s0 (.socket .inet6 .dgram nb 0) (.opened 0)
                                                        let u2 ← step u1 (.bind 0 (v4m0 45000)) .unit
                                                        let u3 ← step u2 (.connect 0 (v4mExt 9)) .unit
                                                        let _ ← step u3 (.getsockname 0) (.addr (v4mHost 45000))
                                                        let t1 ← step s0 (.socket .inet6 .stream nb 0) (.opened 0)
                                                        let t2 ← step t1 (.bind 0 (.ipv6 0 0 46000 0 0)) .unit
                                                        let t3 ← step t2 (.listen 0 4) .unit
                                                        let t4 ← step t3 (.socket .inet6 .stream nb 0) (.opened 1)
                                                        let t5 ← step t4 (.bind 1 (v4m0 0)) .unit
                                                        let t6 ← step t5 (.connect 1 (v4mExt 80)) (.err Errno.EINPROGRESS)
                                                        let t7 ← step t6 (.shutdown 1 .rdwr) .unit
                                                        let t8 ← step t7 (.connect 1 (v4mLo 46000)) (.err Errno.EINPROGRESS)
                                                        step t8 (.accept4 0 nb) (.accepted 2 (v4mHost 50001))
                                                      NondetTest.assert chkV4mRouted.isSome
                                                      let chkFreshNetns : Option NetState := do
                                                        let n0 := NetState.initialNetns true
                                                        let n1 ← step n0 (.socket .inet .dgram nb 0) (.opened 0)
                                                        let n2 ← step n1 (.socket .inet .stream nb 0) (.opened 1)
                                                        let n3 ← step n2 (.bind 1 (.ipv4 0x7f000002 0)) .unit
                                                        let n4 ← step n3 (.getsockname 1) (.addr (.ipv4 0x7f000002 49152))
                                                        let n5 ← step n4 (.socket .inet .dgram nb 0) (.opened 2)
                                                        let n6 ← step n5 (.bind 2 (.ipv4 0x7f000002 45100)) .unit
                                                        let n7 ← step n6 (.ioctl 0 (.setIfFlags defaultLoFlags) loIfname) (.u32 0)
                                                        let n8 ← step n7 (.socket .inet .stream nb 0) (.opened 3)
                                                        let n9 ← step n8 (.bind 3 (.ipv4 0 46100)) .unit
                                                        let n10 ← step n9 (.listen 3 4) .unit
                                                        let n11 ← step n10 (.connect 1 (.ipv4 INADDR_LOOPBACK 46100)) (.err Errno.EINPROGRESS)
                                                        let n12 ← step n11 (.getsockname 1) (.addr (.ipv4 INADDR_LOOPBACK 49152))
                                                        let n13 ← step n12 (.accept4 3 nb) (.accepted 4 (.ipv4 INADDR_LOOPBACK 49152))
                                                        let n14 ← step n13 (.socket .inet .dgram nb 0) (.opened 5)
                                                        let n15 ← step n14 (.bind 5 (.ipv4 INADDR_LOOPBACK 45101)) .unit
                                                        let n16 ← step n15 (.connect 5 (.ipv4 INADDR_LOOPBACK 45100)) .unit
                                                        let n17 ← step n16 (.connect 2 (.ipv4 INADDR_LOOPBACK 45101)) .unit
                                                        let n18 ← step n17 (.sendto 2 (asciiBytes ['z']) {}) (.u32 1)
                                                        step n18 (.recvfrom 5 8 {}) (.bytes (asciiBytes ['z']))
                                                      NondetTest.assert chkFreshNetns.isSome

/-- External trust-boundary assumptions for all 15 `LeanSwe.LinuxSyscall.Net` C wrappers (`net_shim.c` + `fd_box.h`) and Linux kernel socket ABI (`x86_64` + `aarch64`), including `recvmsg` `MSG_CTRUNC -> EPROTO` and `sendmsg` non-`AF_UNIX` `EOPNOTSUPP`, verified 1-to-1 by `RuntimeTests.lean`, `leanswe-world-fuzz`, and `strace` fault injection. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.LinuxSyscall.Net.assume_net_socket_domainTypeFlagsAbi"
      subject := "LeanSwe.LinuxSyscall.Net.socket"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_socketpair_unixPairAbi"
      subject := "LeanSwe.LinuxSyscall.Net.socketpair"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_bind_sockaddrTranslationAndNulGuard"
      subject := "LeanSwe.LinuxSyscall.Net.bind"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_listen_backlogAbi"
      subject := "LeanSwe.LinuxSyscall.Net.listen"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_accept4_flagsAndPeerAddrDecode"
      subject := "LeanSwe.LinuxSyscall.Net.accept4"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_connect_nonblockAndSockaddrAbi"
      subject := "LeanSwe.LinuxSyscall.Net.connect"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_getsockopt_soErrorAndReuseAddrAbi"
      subject := "LeanSwe.LinuxSyscall.Net.getsockopt"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_setsockopt_reuseAddrAbi"
      subject := "LeanSwe.LinuxSyscall.Net.setsockopt"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_getsockname_sockaddrDecode"
      subject := "LeanSwe.LinuxSyscall.Net.getsockname"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_recvfrom_clamped16MiBAndMsgFlags"
      subject := "LeanSwe.LinuxSyscall.Net.recvfrom"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_sendto_msgFlagsAndPartialCount"
      subject := "LeanSwe.LinuxSyscall.Net.sendto"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_shutdown_shutHowAbi"
      subject := "LeanSwe.LinuxSyscall.Net.shutdown"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_sendmsg_scmRightsBatchAbi"
      subject := "LeanSwe.LinuxSyscall.Net.sendmsg"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_recvmsg_scmRightsCloexecAndCapAbi"
      subject := "LeanSwe.LinuxSyscall.Net.recvmsg"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Net.assume_net_ioctl_ifreqFlagsAndIfnameBounds"
      subject := "LeanSwe.LinuxSyscall.Net.ioctl"
      formalPred? := none } ]

/-- Complete `(request × NetErrorKind)` error-coverage matrix for all 15 curated `Net` syscalls (`105` obligations), linked to real Linux tests and `strace`/mocked fault-injection tests in `RuntimeTests.lean`. -/
def errorCoverage : List (ErrorObligation NetErrorKind) :=
  [ { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socket", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socket_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.socketpair", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_socketpair_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_addressError" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.bind", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_bind_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_addressError" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.listen", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_listen_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_wouldBlock" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.accept4", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_accept4_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_addressError" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_inProgress" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.connect", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_connect_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockopt", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockopt_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.setsockopt", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_setsockopt_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.getsockname", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_getsockname_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_wouldBlock" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.recvfrom", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvfrom_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_wouldBlock" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.sendto", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendto_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.shutdown", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_shutdown_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.sendmsg", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_sendmsg_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_wouldBlock" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_connectionState" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.recvmsg", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_recvmsg_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .badFd, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_badFd" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .addressError, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_addressError" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .wouldBlockOrInProgress, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .connectionState, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_permissionDenied" .real }
  , { request := "LeanSwe.LinuxSyscall.Net.ioctl", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.Net.RuntimeTests.err_ioctl_transient" .mocked } ]

/-- `Model.allowedStep` matches Linux `7.1.6` 2-socket loopback TCP Nagle `SHUT_RDWR` and `lo`-down RTO `SHUT_RDWR` parity: when a socket with queued RX reaches `SHUT_RDWR` and the peer flushes a Nagle-buffered segment (`close`, `shutdown(SHUT_WR)`, or ATO timer), `ECONNRESET` is observable at most once on `sendto`/`recvfrom`/`recvmsg`/`getsockopt(SO_ERROR)` (dropping any Nagle-discarded RX tail on `recvfrom`/`recvmsg`), while the peer in `CLOSE_WAIT` accepts 0-byte `sendto -> EPIPE` and `shutdown(SHUT_WR) -> LAST_ACK` `ECONNRESET` after `recvfrom -> EOF`; and when `SHUT_RDWR` occurs while `lo` is down, `sendto` after `lo` comes back up accepts `getsockopt(SO_ERROR) -> ECONNRESET` while the deferred `FIN` RTO is still pending. -/
def test_net_model_tcpNagleShutRdwrParity
    {runner} [NondetTest runner]
    (step : NetState → NetReq → NetOutcome → Option NetState := allowedStep) : runner Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let s0 := NetState.initial true
  match step s0 (.socket .inet .stream nb 0) (.opened 0) with
  | none => NondetTest.assert False
  | some s1 =>
    match step s1 (.socket .inet .stream nb 0) (.opened 1) with
    | none => NondetTest.assert False
    | some s2 =>
      match step s2 (.bind 1 (.ipv4 INADDR_LOOPBACK 55900)) .unit with
      | none => NondetTest.assert False
      | some s3 =>
        match step s3 (.listen 1 8) .unit with
        | none => NondetTest.assert False
        | some s4 =>
          match step s4 (.connect 0 (.ipv4 INADDR_LOOPBACK 55900)) (.err Errno.EINPROGRESS) with
          | none => NondetTest.assert False
          | some s5 =>
            match step s5 (.accept4 1 nb) (.accepted 2 (.ipv4 INADDR_LOOPBACK 51000)) with
            | none => NondetTest.assert False
            | some s6 =>
              match step s6 (.sendto 0 (ByteArray.mk #[112]) {}) (.u32 1) with
              | none => NondetTest.assert False
              | some s7 =>
                match step s7 (.sendto 2 (ByteArray.mk #[124]) {}) (.u32 1) with
                | none => NondetTest.assert False
                | some s8 =>
                  match step s8 (.shutdown 2 .wr) .unit with
                  | none => NondetTest.assert False
                  | some s9 =>
                    match step s9 (.sendto 0 (ByteArray.mk #[191]) {}) (.u32 1) with
                    | none => NondetTest.assert False
                    | some s10 =>
                      match step s10 (.recvfrom 0 1 {}) (.bytes (ByteArray.mk #[124])) with
                      | none => NondetTest.assert False
                      | some s11 =>
                        match step s11 (.sendto 0 (ByteArray.mk #[240]) {}) (.u32 1) with
                        | none => NondetTest.assert False
                        | some s12 =>
                          match step s12 (.shutdown 2 .rd) .unit with
                          | none => NondetTest.assert False
                          | some s13 =>
                            NondetTest.assert ((step s13 (.sendto 0 ByteArray.empty {}) (.err Errno.EPIPE)).isSome)
                            match step s13 (.shutdown 0 .wr) .unit with
                            | none => NondetTest.assert False
                            | some sCwShut =>
                              match step sCwShut (.recvfrom 0 8 {}) (.bytes ByteArray.empty) with
                              | none => NondetTest.assert False
                              | some sCwEof =>
                                NondetTest.assert ((step sCwEof (.getsockopt 0 .error) (.u32 Errno.ECONNRESET)).isSome)
                                match s13.closeHandle 0 with
                                | .error _ => NondetTest.assert False
                                | .ok sClosed =>
                                  match step sClosed (.sendto 2 ByteArray.empty {}) (.err Errno.ECONNRESET) with
                                  | none => NondetTest.assert False
                                  | some sSendClr =>
                                    NondetTest.assert ((step sSendClr (.sendto 2 ByteArray.empty {}) (.err Errno.ECONNRESET)).isNone)
                                    NondetTest.assert ((step sSendClr (.sendto 2 ByteArray.empty {}) (.err Errno.EPIPE)).isSome)
                                    match step sClosed (.recvfrom 2 2 {}) (.bytes (ByteArray.mk #[112, 191])) with
                                    | none => NondetTest.assert False
                                    | some sRxPre =>
                                      match step sRxPre (.recvfrom 2 8 {}) (.err Errno.ECONNRESET) with
                                      | none => NondetTest.assert False
                                      | some sRxRst =>
                                        NondetTest.assert ((step sRxRst (.recvfrom 2 8 {}) (.bytes ByteArray.empty)).isSome)
                                        NondetTest.assert ((step sRxRst (.getsockopt 2 .error) (.u32 0)).isSome)
                                        NondetTest.assert ((step sRxRst (.getsockopt 2 .error) (.u32 Errno.ECONNRESET)).isNone)
                                        match step s6 (.ioctl 0 (.setIfFlags 0) loIfname) (.u32 0) with
                                        | none => NondetTest.assert False
                                        | some sLoDn =>
                                          match step sLoDn (.shutdown 2 .rdwr) .unit with
                                          | none => NondetTest.assert False
                                          | some sLoShut =>
                                            match step sLoShut (.ioctl 0 (.setIfFlags (IFF_UP ||| IFF_LOOPBACK)) loIfname) (.u32 0) with
                                            | none => NondetTest.assert False
                                            | some sLoUp =>
                                              match step sLoUp (.sendto 0 (ByteArray.mk #[65]) { nosignal := true }) (.u32 1) with
                                              | none => NondetTest.assert False
                                              | some sLoSent =>
                                                NondetTest.assert ((step sLoSent (.getsockopt 0 .error) (.u32 Errno.ECONNRESET)).isSome)

end LeanSwe.LinuxSyscall.Net
