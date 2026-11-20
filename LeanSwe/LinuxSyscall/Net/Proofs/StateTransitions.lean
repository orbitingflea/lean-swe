import LeanSwe.LinuxSyscall.Net.SpecTests

namespace LeanSwe.LinuxSyscall.Net

open Core (AllPass)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `modelOps` and `NetState` satisfy `ioctl` (`SIOCGIFFLAGS`, `SIOCSIFFLAGS`, `EPERM`, `CAP_NET_ADMIN`) and non-socket `ENOTSOCK`/`ENOTTY` checks. -/
theorem net_state_ioctlAndNonSocket_allPass :
    AllPass (test_net_state_ioctlAndNonSocket modelOps) := by
  dsimp only [AllPass, test_net_state_ioctlAndNonSocket, Bind.bind, assert, pure]
  refine ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` and `NetState.closeHandle` satisfy unread-RX drain before `ECONNRESET` and subsequent `0` EOF / `EPIPE` checks. -/
theorem net_state_closeAndPeerReset_allPass :
    AllPass (test_net_state_closeAndPeerReset modelOps) := by
  dsimp only [AllPass, test_net_state_closeAndPeerReset, Bind.bind, assert, pure]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies clean TCP peer close (`RST` on 1st `sendto`, `EPIPE` on 2nd), pre-`accept4` buffered delivery, and listener-close client reset checks. -/
theorem net_state_cleanClosePreAcceptAndListenerReset_allPass :
    AllPass (test_net_state_cleanClosePreAcceptAndListenerReset modelOps) := by
  dsimp only [AllPass, test_net_state_cleanClosePreAcceptAndListenerReset, Bind.bind, assert, pure]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, trivial⟩

/-- `modelOps` satisfies IPv4-mapped IPv6 dual-stack `connect`/`accept4`, UDP ephemeral auto-bind + `ECONNREFUSED`, and `AF_UNIX` `SOCK_DGRAM` `ENOENT` checks. -/
theorem net_state_dualStackAndDgramConnect_allPass :
    AllPass (test_net_state_dualStackAndDgramConnect modelOps) := by
  dsimp only [AllPass, test_net_state_dualStackAndDgramConnect, Bind.bind, assert, pure]
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, ⟨_, rfl, by decide⟩, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies unconnected/closed `AF_UNIX` `SOCK_DGRAM` error checks and TCP simultaneous self-connect checks. -/
theorem net_state_unixDgramDisconnectAndTcpSelfConnect_allPass :
    AllPass (test_net_state_unixDgramDisconnectAndTcpSelfConnect modelOps) := by
  dsimp only [AllPass, test_net_state_unixDgramDisconnectAndTcpSelfConnect, Bind.bind, assert, pure]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `lo`-down `ENETUNREACH`, IPv6 `fe80::/10`/`ff00::/8` `EINVAL`, and `::ffff:127.0.0.1` dual-stack checks. -/
theorem net_state_loDownLinkLocalAndMappedIpv6_allPass :
    AllPass (test_net_state_loDownLinkLocalAndMappedIpv6 modelOps) := by
  dsimp only [AllPass, test_net_state_loDownLinkLocalAndMappedIpv6, Bind.bind, assert, pure]
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, ⟨_, _, rfl, rfl⟩, rfl, ⟨_, rfl, ⟨_, rfl⟩⟩⟩, trivial⟩

/-- `Model.allowedStep` satisfies lazy ephemeral port pinning, partial stream TX/RX prefix checks, `SO_ERROR` transitions, and `SCM_RIGHTS` cap invariants. -/
theorem net_model_allowedStep_ephemeralAndPartialIoInvariants_allPass :
    AllPass (test_net_model_allowedStep_ephemeralAndPartialIoInvariants allowedStep) := by
  dsimp only [AllPass, test_net_model_allowedStep_ephemeralAndPartialIoInvariants, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies Linux kernel parity invariants (`sk_bound_dev_if` sticky scope, `ff02::/16` `ENETUNREACH`, `v4MappedTainted` child `RST` drop, and `lo`-was-up broadcast local rewrite). -/
theorem net_model_boundScopeTaintedRstAndBcastRewrite_allPass :
    AllPass (test_net_model_boundScopeTaintedRstAndBcastRewrite allowedStep) := by
  dsimp only [AllPass, test_net_model_boundScopeTaintedRstAndBcastRewrite, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies Linux `7.1.6` kernel parity invariants (`sk_bound_dev_if` `bind`/UDP scope & override, `::ffff:* -> [::]:port` resolution, auto-bound `[::1]` UDP wire-source matching, synchronous `tcp_v4_connect` untainting, and `::ffff:*:0` UDP `sendto` `EINVAL`). -/
theorem net_model_stickyScopeMappedWildcardAndUntaint_allPass :
    AllPass (test_net_model_stickyScopeMappedWildcardAndUntaint allowedStep) := by
  dsimp only [AllPass, test_net_model_stickyScopeMappedWildcardAndUntaint, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies Linux `7.1.6` kernel parity invariants for multicast/broadcast-bound UDP loopback wire-source matching, `::ffff:* -> ff05::1` `EAFNOSUPPORT`, `boundDevIf > 1` `tcp_v6_connect` `late_failure` untainting, `ifindex > 1` `bind`/UDP `connect`/`sendto`/`getsockname`, and `.synSent` `shutdown` unlocked wildcard reset. -/
theorem net_model_mcastMappedScopeAndSynReset_allPass :
    AllPass (test_net_model_mcastMappedScopeAndSynReset allowedStep) := by
  dsimp only [AllPass, test_net_model_mcastMappedScopeAndSynReset, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies Linux `7.1.6` kernel parity invariants for tainted unaccepted-child `RST` drop, tainted `CLOSE_WAIT` TX drop & delayed `FIN`, `TCP_LAST_ACK` / `TCP_CLOSING` port retention, `boundDevIf > 1` async-reset `bind`, and multicast-bound TCP host-routed `inet_saddr` persistence. -/
theorem net_model_taintedAbortLastAckAndMcastRouted_allPass :
    AllPass (test_net_model_taintedAbortLastAckAndMcastRouted allowedStep) := by
  dsimp only [AllPass, test_net_model_taintedAbortLastAckAndMcastRouted, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies Linux `7.1.6` 2-socket loopback TCP Nagle `SHUT_RDWR` and `lo`-down RTO `SHUT_RDWR` parity invariants. -/
theorem net_model_tcpNagleShutRdwrParity_allPass :
    AllPass (test_net_model_tcpNagleShutRdwrParity allowedStep) := by
  dsimp only [AllPass, test_net_model_tcpNagleShutRdwrParity, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

end LeanSwe.LinuxSyscall.Net
