import LeanSwe.LinuxSyscall.Net.SpecTests
import LeanSwe.LinuxSyscall.Net.Impl

namespace LeanSwe.LinuxSyscall.Net

open Core (AllPass)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `modelOps` satisfies the full `socket` and `socketpair` domain/type/protocol validation matrix. -/
theorem net_ops_socketAndSocketpairMatrix_allPass :
    AllPass (test_net_ops_socketAndSocketpairMatrix modelOps (NetState.initial false)) := by
  dsimp only [AllPass, test_net_ops_socketAndSocketpairMatrix, Bind.bind, assert, pure]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩, trivial⟩

/-- `Internal.mkNetOpsM raw` satisfies the full `socket` and `socketpair` domain/type/protocol validation matrix whenever valid underlying `socket`/`socketpair` calls succeed. -/
theorem net_ops_socketAndSocketpairMatrix_mkNetOpsM_allPass
    {S fd : Type} (raw : Internal.PosixNetOpsM (StateM S) fd) (s₀ : S)
    (hSock : ∀ dom st fl proto s, ∃ h s', (raw.socket dom st fl proto).run s = (.ok h, s'))
    (hPair : ∀ dom st fl s, ∃ p s', (raw.socketpair dom st fl).run s = (.ok p, s')) :
    AllPass (test_net_ops_socketAndSocketpairMatrix (Internal.mkNetOpsM raw) s₀) := by
  rcases hSock SockDomain.inet.toTag SockType.stream.toTag
    ({ nonblock := true, cloexec := true } : SockFlags).toBits IPPROTO_TCP s₀ with ⟨h1, s1, e1⟩
  rcases hSock SockDomain.inet6.toTag SockType.dgram.toTag
    ({ cloexec := true } : SockFlags).toBits IPPROTO_UDP s1 with ⟨h2, s2, e2⟩
  rcases hPair SockDomain.unix.toTag SockType.seqpacket.toTag
    ({ nonblock := true, cloexec := true } : SockFlags).toBits s2 with ⟨p3, s3, e3⟩
  rcases hSock SockDomain.unix.toTag SockType.stream.toTag
    ({} : SockFlags).toBits PF_UNIX s₀ with ⟨hu1, su1, eu1⟩
  rcases hSock SockDomain.unix.toTag SockType.dgram.toTag
    ({} : SockFlags).toBits PF_UNIX s₀ with ⟨hu2, su2, eu2⟩
  rcases hSock SockDomain.unix.toTag SockType.seqpacket.toTag
    ({} : SockFlags).toBits PF_UNIX s₀ with ⟨hu3, su3, eu3⟩
  have ok1 : ((Internal.mkNetOpsM raw).socket .inet .stream { nonblock := true, cloexec := true } IPPROTO_TCP).run s₀ = (.ok h1, s1) := by
    have hv : validateSocketArgs .inet .stream IPPROTO_TCP = none := by decide
    dsimp only [Internal.mkNetOpsM]
    rw [hv]
    exact e1
  have ok2 : ((Internal.mkNetOpsM raw).socket .inet6 .dgram { cloexec := true } IPPROTO_UDP).run s1 = (.ok h2, s2) := by
    have hv : validateSocketArgs .inet6 .dgram IPPROTO_UDP = none := by decide
    dsimp only [Internal.mkNetOpsM]
    rw [hv]
    exact e2
  have ok3 : ((Internal.mkNetOpsM raw).socketpair .unix .seqpacket { nonblock := true, cloexec := true }).run s2 = (.ok p3, s3) := by
    dsimp only [Internal.mkNetOpsM, validateSocketpairArgs]
    exact e3
  have okUxS : ((Internal.mkNetOpsM raw).socket .unix .stream {} PF_UNIX).run s₀ = (.ok hu1, su1) := by
    have hv : validateSocketArgs .unix .stream PF_UNIX = none := by decide
    dsimp only [Internal.mkNetOpsM]
    rw [hv]
    exact eu1
  have okUxD : ((Internal.mkNetOpsM raw).socket .unix .dgram {} PF_UNIX).run s₀ = (.ok hu2, su2) := by
    have hv : validateSocketArgs .unix .dgram PF_UNIX = none := by decide
    dsimp only [Internal.mkNetOpsM]
    rw [hv]
    exact eu2
  have okUxQ : ((Internal.mkNetOpsM raw).socket .unix .seqpacket {} PF_UNIX).run s₀ = (.ok hu3, su3) := by
    have hv : validateSocketArgs .unix .seqpacket PF_UNIX = none := by decide
    dsimp only [Internal.mkNetOpsM]
    rw [hv]
    exact eu3
  have mkErr (dom : SockDomain) (st : SockType) (fl : SockFlags) (p : UInt32) (e : Errno)
      (hv : validateSocketArgs dom st p = some e := by decide) :
      ((Internal.mkNetOpsM raw).socket dom st fl p).run s₀ = (.error e, s₀) := by
    dsimp only [Internal.mkNetOpsM, StateT.run, Pure.pure, StateT.pure]
    rw [hv]
    rfl
  unfold test_net_ops_socketAndSocketpairMatrix
  rw [mkErr .inet .stream {} IPPROTO_MAX Errno.EINVAL]
  rw [mkErr .inet .seqpacket {} 0 Errno.ESOCKTNOSUPPORT]
  rw [mkErr .inet6 .seqpacket {} 0 Errno.ESOCKTNOSUPPORT]
  rw [mkErr .inet .stream {} IPPROTO_UDP Errno.EPROTONOSUPPORT]
  rw [mkErr .unix .stream {} IPPROTO_TCP Errno.EPROTONOSUPPORT]
  rw [mkErr .inet .stream {} 262 Errno.EPROTONOSUPPORT]
  rw [mkErr .inet .stream {} 132 Errno.EPROTONOSUPPORT]
  rw [mkErr .inet .dgram {} 1 Errno.EPROTONOSUPPORT]
  rw [mkErr .inet6 .dgram {} 58 Errno.EPROTONOSUPPORT]
  rw [mkErr .inet .dgram {} 115 Errno.EPROTONOSUPPORT]
  rw [mkErr .inet6 .dgram {} IPPROTO_MAX Errno.EINVAL]
  rw [mkErr .inet .dgram {} IPPROTO_TCP Errno.EPROTONOSUPPORT]
  rw [mkErr .inet6 .dgram {} IPPROTO_TCP Errno.EPROTONOSUPPORT]
  rw [mkErr .unix .dgram {} IPPROTO_UDP Errno.EPROTONOSUPPORT]
  rw [mkErr .unix .stream {} 2 Errno.EPROTONOSUPPORT]
  rw [mkErr .unix .dgram {} 2 Errno.EPROTONOSUPPORT]
  rw [mkErr .unix .seqpacket {} 2 Errno.EPROTONOSUPPORT]
  rw [ok1]
  dsimp only
  rw [ok2]
  dsimp only
  rw [ok3]
  rw [okUxS, okUxD, okUxQ]
  dsimp only [AllPass, Internal.mkNetOpsM, validateSocketpairArgs,
    StateT.run, Pure.pure, StateT.pure, Bind.bind, assert, pure]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨⟨h1, rfl⟩, ⟨h2, rfl⟩, ⟨p3, rfl⟩⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨⟨hu1, rfl⟩, ⟨hu2, rfl⟩, ⟨hu3, rfl⟩, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies the IPv4 loopback `socket`/`setsockopt`/`bind`/`listen`/`connect`/`accept4` lifecycle checks. -/
theorem net_ops_loopbackBindListenAndConnectLifecycle_allPass :
    AllPass (test_net_ops_loopbackBindListenAndConnectLifecycle modelOps (NetState.initial false)) := by
  dsimp only [AllPass, test_net_ops_loopbackBindListenAndConnectLifecycle, Bind.bind, assert, pure]
  refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, by decide⟩,
    rfl, ⟨rfl, rfl⟩, rfl, ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, ⟨rfl, rfl⟩, trivial⟩⟩

/-- `modelOps` satisfies `MSG_PEEK`, partial `recvfrom`, `SHUT_WR` half-close, `SHUT_RD` drain-before-EOF, and `AF_UNIX` `EPIPE` invariants. -/
theorem net_ops_streamTransferPeekAndShutdown_allPass :
    AllPass (test_net_ops_streamTransferPeekAndShutdown modelOps (NetState.initial false)) := by
  dsimp only [AllPass, test_net_ops_streamTransferPeekAndShutdown, Bind.bind, assert, pure]
  refine ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `AF_UNIX` `SOCK_SEQPACKET` `listen`/`connect`, `SO_ERROR` clear, `ECONNABORTED`, and `SCM_RIGHTS` queue invariants. -/
theorem net_ops_unixSeqpacketScmRightsAndSoErrorClear_allPass :
    AllPass (test_net_ops_unixSeqpacketScmRightsAndSoErrorClear modelOps (NetState.initial false)) := by
  dsimp only [AllPass, test_net_ops_unixSeqpacketScmRightsAndSoErrorClear, Bind.bind, assert, pure]
  refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, Or.inl rfl,
    ⟨fun _ => rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, ⟨_, rfl, rfl⟩, rfl⟩, ⟨rfl, ⟨_, rfl, rfl⟩⟩, trivial⟩

end LeanSwe.LinuxSyscall.Net
