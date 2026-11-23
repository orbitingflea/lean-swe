import LeanSwe.LinuxSyscall.Net.SpecTests
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Net.Interface

namespace LeanSwe.LinuxSyscall.Net

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def stubNetOps : NetOpsM (StateM Unit) Nat :=
  { socket := fun _ _ _ _ => pure (Except.ok 0)
    socketpair := fun _ _ _ => pure (Except.ok (0, 1))
    bind := fun _ _ => pure (Except.ok ())
    listen := fun _ _ => pure (Except.ok ())
    accept4 := fun _ _ => pure (Except.ok (1, .ipv4 INADDR_LOOPBACK 50000))
    connect := fun _ _ => pure (Except.ok ())
    getsockopt := fun _ _ => pure (Except.ok 0)
    setsockopt := fun _ _ _ => pure (Except.ok ())
    getsockname := fun _ => pure (Except.ok (.ipv4 INADDR_LOOPBACK 8080))
    recvfrom := fun _ _ _ => pure (Except.ok (ByteArray.mk #[]))
    sendto := fun _ data _ => pure (Except.ok (UInt32.ofNat data.data.size))
    shutdown := fun _ _ => pure (Except.ok ())
    sendmsg := fun _ _ => pure (Except.ok ())
    recvmsg := fun _ _ => pure (Except.ok #[])
    ioctl := fun _ _ _ => pure (Except.ok 0) }

private def stubStateNetOps : NetOpsM (StateM NetState) HandleId :=
  { socket := fun _ _ _ _ => pure (Except.ok 0)
    socketpair := fun _ _ _ => pure (Except.ok (0, 1))
    bind := fun _ _ => pure (Except.ok ())
    listen := fun _ _ => pure (Except.ok ())
    accept4 := fun _ _ => pure (Except.ok (1, .ipv4 INADDR_LOOPBACK 50000))
    connect := fun _ _ => pure (Except.ok ())
    getsockopt := fun _ _ => pure (Except.ok 0)
    setsockopt := fun _ _ _ => pure (Except.ok ())
    getsockname := fun _ => pure (Except.ok (.ipv4 0 0))
    recvfrom := fun _ _ _ => pure (Except.ok (ByteArray.mk #[]))
    sendto := fun _ data _ => pure (Except.ok (UInt32.ofNat data.data.size))
    shutdown := fun _ _ => pure (Except.ok ())
    sendmsg := fun _ _ => pure (Except.ok ())
    recvmsg := fun _ _ => pure (Except.ok #[])
    ioctl := fun _ _ _ => pure (Except.ok defaultLoFlags) }

/-- Mutant treating `EFAULT` as a transient networking errno is rejected by `test_net_errno_classification`. -/
theorem mutant_net_efault_transient : ¬ Core.AllPass (test_net_errno_classification
    (fun e => e == Errno.EFAULT || isTransientNetErrno e)
    NetErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_net_errno_classification
    isTransientNetErrno
    (fun e => if e == Errno.ECONNABORTED then .invalidArg else NetErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ECONNABORTED
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (encSf := fun f => ({ nonblock := f.cloexec, cloexec := f.nonblock } : SockFlags).toBits)) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := (h2 {} {}).2
  have h4 := (h3 .error .error).2
  have h5 := (h4 .reuseAddr .reuseAddr).2
  have h6 := (h5 {} {}).2
  have h7 := (h6 .rd .rd).2
  have h8 := (h7 .getIfFlags .getIfFlags).2
  have h9 := h8 (.ipv4 INADDR_LOOPBACK 8080)
  exact absurd h9.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (encSf := fun f => { f with nonblock := false }.toBits)) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := h2 { nonblock := false } { nonblock := true }
  exact absurd h3.1 (by decide)

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (encMsg := fun f => { f with nosignal := false }.toBits)) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := (h2 {} {}).2
  have h4 := (h3 .error .error).2
  have h5 := (h4 .reuseAddr .reuseAddr).2
  have h6 := h5 { nosignal := false } { nosignal := true }
  exact absurd h6.1 (by decide)

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (decAddr := fun t =>
      let (tag, v4, hi, lo, _, flow, scope, path) := t
      SockAddr.ofRawTuple (tag, v4, hi, lo, 0, flow, scope, path))) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := (h2 {} {}).2
  have h4 := (h3 .error .error).2
  have h5 := (h4 .reuseAddr .reuseAddr).2
  have h6 := (h5 {} {}).2
  have h7 := (h6 .rd .rd).2
  have h8 := (h7 .getIfFlags .getIfFlags).2
  have h9 := h8 (.ipv4 INADDR_LOOPBACK 8080)
  exact absurd h9.1 (by decide)

private def witnessLongBytes (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (97 : UInt8)).toArray

private theorem witnessLongBytes_size (n : Nat) :
    (witnessLongBytes n).data.size = n := by
  unfold witnessLongBytes
  rw [List.size_toArray, List.length_replicate]

example : ¬ Core.AllPass (test_net_ops_boundaryValidation_einval stubNetOps) := by
  intro h
  have hUnix : (witnessLongBytes 109).data.size > UNIX_PATH_MAX := by
    rw [witnessLongBytes_size]
    decide
  have hIf : (witnessLongBytes 16).data.size ≥ IFNAMSIZ := by
    rw [witnessLongBytes_size]
    decide
  have hFds : ((List.replicate 33 (0 : Nat)).toArray).size > MAX_SCM_FDS := by
    rw [List.size_toArray, List.length_replicate]
    decide
  have h0 := h () 0 .getIfFlags (ByteArray.mk #[97, 0, 98]) (by decide)
    (witnessLongBytes 109) hUnix (witnessLongBytes 16) hIf
    ((List.replicate 33 (0 : Nat)).toArray) hFds 33 (by decide)
  dsimp only [stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_net_ops_boundaryValidation_einval
    { stubNetOps with
      bind := fun _ _ => pure (Except.error Errno.EINVAL)
      connect := fun _ _ => pure (Except.error Errno.EINVAL)
      sendmsg := fun _ _ => pure (Except.error Errno.EINVAL)
      recvmsg := fun _ _ => pure (Except.error Errno.EINVAL)
      ioctl := fun _ _ ifname =>
        if hasEmbeddedNul ifname then pure (Except.error Errno.EINVAL)
        else pure (Except.ok 0) }) := by
  intro h
  have hUnix : (witnessLongBytes 109).data.size > UNIX_PATH_MAX := by
    rw [witnessLongBytes_size]
    decide
  have hIf : (witnessLongBytes 16).data.size ≥ IFNAMSIZ := by
    rw [witnessLongBytes_size]
    decide
  have hFds : ((List.replicate 33 (0 : Nat)).toArray).size > MAX_SCM_FDS := by
    rw [List.size_toArray, List.length_replicate]
    decide
  have h0 := h () 0 .getIfFlags (ByteArray.mk #[97, 0, 98]) (by decide)
    (witnessLongBytes 109) hUnix (witnessLongBytes 16) hIf
    ((List.replicate 33 (0 : Nat)).toArray) hFds 33 (by decide)
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [stubNetOps, Bind.bind, StateT.run, pure, StateT.pure] at hBad
  have hNul : hasEmbeddedNul (witnessLongBytes 16) = false := by decide
  rw [hNul] at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_ops_socketAndSocketpairMatrix stubNetOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_socketAndSocketpairMatrix,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_net_ops_socketAndSocketpairMatrix
    { stubNetOps with
      socket := fun dom typ _ proto =>
        if proto == 262 then pure (Except.ok 0)
        else
          match validateSocketArgs dom typ proto with
          | some e => pure (Except.error e)
          | none => pure (Except.ok 0)
      socketpair := fun dom _ _ =>
        if dom != .unix then pure (Except.error Errno.EOPNOTSUPP)
        else pure (Except.ok (0, 1)) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_socketAndSocketpairMatrix,
    stubNetOps, validateSocketArgs, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.2.2.1.1

example : ¬ Core.AllPass (test_net_ops_loopbackBindListenAndConnectLifecycle stubNetOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_loopbackBindListenAndConnectLifecycle,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  injection h.1 with hSa
  exact absurd hSa (by decide)

example : ¬ Core.AllPass (test_net_ops_loopbackBindListenAndConnectLifecycle
    { stubNetOps with
      getsockname := fun _ => pure (Except.ok (.ipv4 0 0))
      accept4 := fun _ _ => pure (Except.error Errno.EINVAL)
      shutdown := fun _ _ => pure (Except.ok ()) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_loopbackBindListenAndConnectLifecycle,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.1

example : ¬ Core.AllPass (test_net_ops_streamTransferPeekAndShutdown stubNetOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_streamTransferPeekAndShutdown,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  injection h.2.1.1 with hBytes
  exact absurd hBytes (by decide)

example : ¬ Core.AllPass (test_net_ops_streamTransferPeekAndShutdown
    { stubNetOps with
      recvfrom := fun _ maxBytes _ =>
        if maxBytes == 2 then pure (Except.ok (asciiBytes ['h', 'e']))
        else pure (Except.ok (asciiBytes ['l', 'l', 'o'])) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_streamTransferPeekAndShutdown,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.1

example : ¬ Core.AllPass (test_net_ops_unixSeqpacketScmRightsAndSoErrorClear stubNetOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_unixSeqpacketScmRightsAndSoErrorClear,
    stubNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1

example : ¬ Core.AllPass (test_net_ops_unixSeqpacketScmRightsAndSoErrorClear
    { stubNetOps with
      listen := fun _ _ => pure (Except.error Errno.EINVAL)
      connect := fun _ sa =>
        match sa with
        | .unix p =>
          if bytesEq p (asciiBytes ['/', 't', 'm', 'p', '/', 'm', 'i', 's', 's', '.', 's', 'o', 'c', 'k']) then
            pure (Except.error Errno.ENOENT)
          else pure (Except.error Errno.ECONNREFUSED)
        | _ => pure (Except.error Errno.EINPROGRESS) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_unixSeqpacketScmRightsAndSoErrorClear,
    stubNetOps, bytesEq, asciiBytes, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.2.1.1

example : ¬ Core.AllPass (test_net_state_ioctlAndNonSocket stubStateNetOps) := by
  intro h
  dsimp only [Core.AllPass, test_net_state_ioctlAndNonSocket,
    stubStateNetOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1

example : ¬ Core.AllPass (test_net_state_ioctlAndNonSocket
    { stubStateNetOps with
      ioctl := fun hid op ifname =>
        if hid != 0 then pure (Except.error Errno.ENOTTY)
        else if !bytesEq ifname loIfname then pure (Except.error Errno.ENODEV)
        else
          match op with
          | .getIfFlags => pure (Except.ok defaultLoFlags)
          | .setIfFlags _ => do
            let s ← get
            if !s.hasNetAdmin then return Except.error Errno.EPERM
            else return Except.ok 0
      getsockname := fun _ => pure (Except.error Errno.ENOTSOCK) }) := by
  intro h
  have hBad := h.2.2.2.1.2.1
  change (Except.error Errno.ENODEV : Except Errno UInt32) = Except.error Errno.EPERM at hBad
  injection hBad with hErr
  exact absurd hErr (by decide)

example : ¬ Core.AllPass (test_net_state_ioctlAndNonSocket
    { stubStateNetOps with
      ioctl := fun hid op ifname =>
        if hid != 0 then pure (Except.error Errno.ENOTTY)
        else
          match op with
          | .getIfFlags =>
            if bytesEq ifname loIfname then pure (Except.ok defaultLoFlags)
            else pure (Except.error Errno.ENODEV)
          | .setIfFlags _ => do
            let s ← get
            if !s.hasNetAdmin then return Except.error Errno.EPERM
            else if !bytesEq ifname loIfname then return Except.error Errno.ENODEV
            else return Except.ok 0
      getsockname := fun _ => pure (Except.error Errno.ENOTSOCK) }) := by
  intro h
  have hBad := h.2.2.2.2.2.1.2.2.1
  change (Except.ok defaultLoFlags : Except Errno UInt32) = Except.ok IFF_LOOPBACK at hBad
  injection hBad with hFl
  exact absurd hFl (by decide)

example : ¬ Core.AllPass (test_net_state_closeAndPeerReset stubStateNetOps) := by
  intro h
  exact h.1

private def mkStubConnectedDesc (dom : SockDomain) (typ : SockType) : SockDesc :=
  let proto :=
    match dom, typ with
    | .inet, .stream => .tcp .v4 .unbound .connected (.established none (.ipv4 INADDR_LOOPBACK 50000)) false
    | .inet6, .stream => .tcp .v6 .unbound .connected (.established none (.ipv6 0 1 50000 0 0)) false
    | .inet, .dgram => .udp .v4 .unbound (some (.ipv4 INADDR_LOOPBACK 50000))
    | .inet6, .dgram => .udp .v6 .unbound (some (.ipv6 0 1 50000 0 0))
    | .unix, .dgram => .unixDgram none none
    | .unix, .stream => .unixStream false none (.connected none false false false false)
    | .unix, .seqpacket => .unixStream true none (.connected none false false false false)
    | _, .seqpacket => (SockDesc.mkDefault dom typ).proto
  { proto := proto }

private def allocStubConnected (dom : SockDomain) (typ : SockType) : StateM NetState HandleId := do
  let s ← get
  let hid := freshHidBase s
  let fid := s.nextFileId
  set ({ s with
    handles := assocSet s.handles hid (.open fid true)
    files := assocSet s.files fid (.socket (mkStubConnectedDesc dom typ))
    nextFileId := fid + 1 } : NetState)
  return hid

example : ¬ Core.AllPass (test_net_state_closeAndPeerReset
    { stubStateNetOps with
      socket := fun dom typ _ _ => return Except.ok (← allocStubConnected dom typ)
      getsockname := fun _ => pure (Except.error Errno.EBADF)
      recvfrom := fun _ _ _ => pure (Except.error Errno.ECONNRESET) }) := by
  intro h
  have hBad := h.1.2.1
  change (Except.error Errno.ECONNRESET : Except Errno ByteArray) = Except.ok (asciiBytes ['h', 'i']) at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_state_cleanClosePreAcceptAndListenerReset stubStateNetOps) := by
  intro h
  exact h.1

example : ¬ Core.AllPass (test_net_state_cleanClosePreAcceptAndListenerReset
    { stubStateNetOps with
      socket := fun dom typ _ _ => return Except.ok (← allocStubConnected dom typ) }) := by
  intro h
  have hBad := h.1.1
  change (Except.ok (SockAddr.ipv4 0 0) : Except Errno SockAddr) = Except.ok (SockAddr.ipv4 INADDR_LOOPBACK 55200) at hBad
  injection hBad with hSa
  exact absurd hSa (by decide)

example : ¬ Core.AllPass (test_net_state_dualStackAndDgramConnect stubStateNetOps) := by
  intro h
  have hBad := h.1.2.1
  change SockDomain.inet = SockDomain.inet6 at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_state_dualStackAndDgramConnect
    { stubStateNetOps with
      accept4 := fun _ _ => pure (Except.ok (1, .ipv6 0 0x0000ffff7f000001 49152 0 0))
      getsockname := fun _ => pure (Except.ok (.ipv6 0 0x0000ffff7f000002 55300 0 0)) }) := by
  intro h
  have hBad := h.2.1.1
  change (Except.ok () : Except Errno Unit) = Except.error Errno.ENOENT at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_state_unixDgramDisconnectAndTcpSelfConnect
    { stubStateNetOps with
      sendto := fun _ _ _ => pure (Except.error Errno.EDESTADDRREQ) }) := by
  intro h
  have hBad := h.1.1
  change (Except.error Errno.EDESTADDRREQ : Except Errno UInt32) = Except.error Errno.ENOTCONN at hBad
  injection hBad with hErr
  exact absurd hErr (by decide)

example : ¬ Core.AllPass (test_net_state_unixDgramDisconnectAndTcpSelfConnect
    { stubStateNetOps with
      socketpair := fun dom typ _ => do
        let h0 ← allocStubConnected dom typ
        let h1 ← allocStubConnected dom typ
        return Except.ok (h0, h1)
      sendto := fun hid _ _ =>
        if hid == 0 then pure (Except.error Errno.ENOTCONN)
        else pure (Except.error Errno.EDESTADDRREQ) }) := by
  intro h
  have hBad := h.2.1.1
  change (Except.error Errno.ENOTCONN : Except Errno UInt32) = Except.error Errno.ECONNREFUSED at hBad
  injection hBad with hErr
  exact absurd hErr (by decide)

example : ¬ Core.AllPass (test_net_model_allowedStep_ephemeralAndPartialIoInvariants
    (fun s req out =>
      match req, out with
      | .getsockopt _ .error, .u32 v =>
        if v == Errno.ETIMEDOUT then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_net_state_loDownLinkLocalAndMappedIpv6 stubStateNetOps) := by
  intro h
  have hBad := h.1.1
  change (Except.ok () : Except Errno Unit) = Except.error Errno.EINVAL at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_state_loDownLinkLocalAndMappedIpv6
    { stubStateNetOps with
      bind := fun _ sa =>
        if isIpv6LinkLocalNoScope sa || isIpv6Multicast sa then pure (Except.error Errno.EINVAL)
        else pure (Except.ok ())
      connect := fun _ sa =>
        if isIpv6LinkLocalNoScope sa then pure (Except.error Errno.EINVAL)
        else pure (Except.ok ()) }) := by
  intro h
  have hBad := h.2.1.2.2.1
  change (Except.ok () : Except Errno Unit) = Except.error Errno.ENETUNREACH at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_model_allowedStep_ephemeralAndPartialIoInvariants
    (fun s req out =>
      match req, out with
      | .recvmsg _ _, .fds got =>
        if got.size == 2 then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_allowedStep_ephemeralAndPartialIoInvariants
    (fun s req out =>
      match req, out with
      | .getsockname _, .addr _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_allowedStep_ephemeralAndPartialIoInvariants
    (fun s req out =>
      match req, out with
      | .recvfrom _ _ _, .bytes _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_ambientSeccomp
    (fun s req out =>
      match out with
      | .err e => if e == Errno.EFAULT then some s else allowedStep s req out
      | _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_bindDualStackShutdownAndFinInvariants
    (fun s req out =>
      match req, out with
      | .bind _ (.ipv4 0xc0000201 _), .unit => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_stepCoreSound (fun _ _ _ => none)) := by
  intro h
  let s0 := NetState.initial false
  let req : NetReq := .socket .inet .stream {} 0
  have hs : ∃ out s', stepNetCore s0 req none = some (out, s') :=
    ⟨.opened 0, _, rfl⟩
  rcases hs with ⟨out, s', hstep⟩
  have h1 := h s0 req out s' hstep
  cases h1.1

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (defSf := { nonblock := false, cloexec := false })) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := (h2 {} {}).2
  have h4 := (h3 .error .error).2
  have h5 := (h4 .reuseAddr .reuseAddr).2
  have h6 := (h5 {} {}).2
  have h7 := (h6 .rd .rd).2
  have h8 := (h7 .getIfFlags .getIfFlags).2
  have h9 := h8 (.ipv4 INADDR_LOOPBACK 8080)
  have hDef := h9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  exact absurd hDef (by decide)

example : ¬ Core.AllPass (test_net_flags_and_sockaddr_codecs
    (encAddr := fun sa =>
      match sa with
      | .ipv6 hi lo port flow scope => (1, 0, lo, hi, port, scope, flow, ByteArray.mk #[])
      | other => other.toRawTuple)
    (decAddr := fun t =>
      let (tag, _, a, b, port, c, d, _) := t
      if tag == 1 then .ipv6 b a port d c else SockAddr.ofRawTuple t)) := by
  intro h
  have h1 := (h .inet .inet).2
  have h2 := (h1 .stream .stream).2
  have h3 := (h2 {} {}).2
  have h4 := (h3 .error .error).2
  have h5 := (h4 .reuseAddr .reuseAddr).2
  have h6 := (h5 {} {}).2
  have h7 := (h6 .rd .rd).2
  have h8 := (h7 .getIfFlags .getIfFlags).2
  have h9 := h8 (.ipv6 1 2 443 3 4)
  have hWire := h9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hHi : (2 : UInt64) = 1 := congrArg (fun t => t.2.2.1) hWire
  exact absurd hHi (by decide)

private def mutIdRawNetOps : PosixNetOpsM Id Nat :=
  { socket := fun _ _ _ p => .ok p.toNat
    socketpair := fun _ _ _ => .ok (0, 1)
    bind := fun _ _ => .ok ()
    listen := fun _ _ => .ok ()
    accept4 := fun _ _ => .ok (1, (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[]))
    connect := fun _ _ => .ok ()
    getsockopt := fun _ _ => .ok 0
    setsockopt := fun _ _ _ => .ok ()
    getsockname := fun _ => .ok (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[])
    recvfrom := fun _ _ _ => .ok (ByteArray.mk #[])
    sendto := fun _ _ bits => .ok bits
    shutdown := fun _ _ => .ok ()
    sendmsg := fun _ _ => .ok ()
    recvmsg := fun _ _ => .ok #[]
    ioctl := fun _ _ _ _ => .ok 0 }

example : ¬ Core.AllPass (test_net_mkNetOps_encodesAndDelegates
    (fun raw =>
      let base := @Internal.mkNetOpsM Id Nat _ raw
      { base with socket := fun dom typ sf proto => raw.socket dom.toTag typ.toTag sf.toBits proto })) := by
  intro h
  have h0 := h mutIdRawNetOps .inet .seqpacket {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) rfl
    128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[0] (by decide) 1 (by decide) .getIfFlags loIfname (by decide)
  have hBad := h0.1
  change (Except.ok 0 : Except Errno Nat) = Except.error Errno.ESOCKTNOSUPPORT at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_mkNetOps_encodesAndDelegates
    (fun raw =>
      let base := @Internal.mkNetOpsM Id Nat _ raw
      { base with sendto := fun fd data _ => raw.sendto fd data 0 })) := by
  intro h
  have h0 := h mutIdRawNetOps .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) rfl
    128 .error .reuseAddr 1 16 { nosignal := true } (ByteArray.mk #[]) .rdwr #[0] (by decide) 1 (by decide) .getIfFlags loIfname (by decide)
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.1
  change (Except.ok 0 : Except Errno UInt32) = Except.ok 1 at hBad
  injection hBad with hEq
  exact absurd hEq (by decide)

private def distingNetOps : NetOpsM Id Nat :=
  { socket := fun _ _ sf _ => .ok sf.toBits.toNat
    socketpair := fun _ _ _ => .ok (0, 1)
    bind := fun _ _ => .ok ()
    listen := fun _ _ => .ok ()
    accept4 := fun _ _ => .ok (1, .ipv4 INADDR_LOOPBACK 8080)
    connect := fun _ _ => .ok ()
    getsockopt := fun _ _ => .ok 0
    setsockopt := fun _ _ _ => .ok ()
    getsockname := fun _ => .ok (.ipv4 INADDR_LOOPBACK 8080)
    recvfrom := fun _ _ _ => .ok (ByteArray.mk #[])
    sendto := fun _ _ mf => .ok mf.toBits
    shutdown := fun _ _ => .ok ()
    sendmsg := fun _ _ => .ok ()
    recvmsg := fun _ _ => .ok #[]
    ioctl := fun _ _ _ => .ok 0 }

example : ¬ Core.AllPass (test_net_interface_defaultOpsWiring
    (fun _ => distingNetOps) distingNetOps
    distingNetOps.socket (fun d t => distingNetOps.socket d t { nonblock := false, cloexec := false } 0)
    distingNetOps.socketpair (fun d t => distingNetOps.socketpair d t { nonblock := false, cloexec := true })
    distingNetOps.bind distingNetOps.listen (fun h => distingNetOps.listen h 128)
    distingNetOps.accept4 (fun h => distingNetOps.accept4 h { nonblock := false, cloexec := true })
    distingNetOps.connect distingNetOps.getsockopt distingNetOps.setsockopt distingNetOps.getsockname
    distingNetOps.recvfrom (fun h m => distingNetOps.recvfrom h m {})
    distingNetOps.sendto (fun h d => distingNetOps.sendto h d { nosignal := true })
    distingNetOps.shutdown distingNetOps.sendmsg distingNetOps.recvmsg distingNetOps.ioctl) := by
  intro h
  have h0 := h .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) 128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[] 1 .getIfFlags loIfname
  have hBad := h0.2.2.1
  change (Except.ok 0 : Except Errno Nat) = Except.ok 2 at hBad
  injection hBad with hEq
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_net_interface_defaultOpsWiring
    (fun _ => distingNetOps) distingNetOps
    distingNetOps.socket (fun d t => distingNetOps.socket d t { nonblock := false, cloexec := true } 0)
    distingNetOps.socketpair (fun d t => distingNetOps.socketpair d t { nonblock := false, cloexec := true })
    distingNetOps.bind distingNetOps.listen (fun h => distingNetOps.listen h 128)
    distingNetOps.accept4 (fun h => distingNetOps.accept4 h { nonblock := false, cloexec := true })
    distingNetOps.connect distingNetOps.getsockopt distingNetOps.setsockopt distingNetOps.getsockname
    distingNetOps.recvfrom (fun h m => distingNetOps.recvfrom h m {})
    distingNetOps.sendto (fun h d => distingNetOps.sendto h d { nosignal := false })
    distingNetOps.shutdown distingNetOps.sendmsg distingNetOps.recvmsg distingNetOps.ioctl) := by
  intro h
  have h0 := h .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) 128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[] 1 .getIfFlags loIfname
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  change (Except.ok 0 : Except Errno UInt32) = Except.ok 1 at hBad
  injection hBad with hEq
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_net_model_boundScopeTaintedRstAndBcastRewrite
    (fun s req out =>
      match req, out with
      | .connect _ (.ipv6 0xff02000000000000 1 8080 0 0), .err e =>
        if e == Errno.ENETUNREACH then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_net_model_boundScopeTaintedRstAndBcastRewrite
    (fun s req out =>
      match req, out with
      | .connect _ (.ipv6 0 0x0000ffff7f000001 8080 0 0), .err e =>
        if e == Errno.ENODEV then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_stickyScopeMappedWildcardAndUntaint
    (fun s req out =>
      match req, out with
      | .bind _ (.ipv6 0 1 0 0 0), .err e =>
        if e == Errno.ENODEV then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_net_model_stickyScopeMappedWildcardAndUntaint
    (fun s req out =>
      match req, out with
      | .connect _ (.ipv6 0 0 55700 0 0), .unit => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_stickyScopeMappedWildcardAndUntaint
    (fun s req out =>
      match req, out with
      | .sendto _ _ _, .err e =>
        if e == Errno.EINVAL then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_mcastMappedScopeAndSynReset
    (fun s req out =>
      match req, out with
      | .recvfrom _ _ _, .bytes _ => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_net_model_mcastMappedScopeAndSynReset
    (fun s req out =>
      match req, out with
      | .connect _ (.ipv6 0xff05000000000000 1 8080 0 0), .err e =>
        if e == Errno.EAFNOSUPPORT then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_mcastMappedScopeAndSynReset
    (fun s req out =>
      match req, out with
      | .getsockname _, .addr (.ipv4 0 51234) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .connect 1 (.ipv6 0 1 55900 0 0), .unit => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .getsockopt 2 .error, .u32 0 => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .shutdown 2 .rd, .unit => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .bind 0 (.ipv6 0xfe80000000000000 9 0 0 2), .unit => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .getsockname 1, .addr (.ipv4 0xac100005 44200) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_tcpNagleShutRdwrParity
    (fun s req out =>
      match req, out with
      | .sendto 2 _ _, .err e =>
        if e == Errno.ECONNRESET then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_net_model_tcpNagleShutRdwrParity, Bind.bind, assert, pure] at h
  exact h.2.2.1

example : ¬ Core.AllPass (test_net_model_tcpNagleShutRdwrParity
    (fun s req out =>
      match req, out with
      | .sendto 0 _ _, .err e =>
        if e == Errno.EPIPE then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_net_model_tcpNagleShutRdwrParity
    (fun s req out =>
      match s.loState, req, out with
      | .up _, .getsockopt 0 .error, .u32 v =>
        if v == Errno.ECONNRESET then none else allowedStep s req out
      | _, _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_ops_socketAndSocketpairMatrix
    { stubNetOps with
      socket := fun dom typ _ proto =>
        if typ == .dgram && proto == IPPROTO_TCP then pure (Except.ok 0)
        else
          match validateSocketArgs dom typ proto with
          | some e => pure (Except.error e)
          | none => pure (Except.ok 0)
      socketpair := fun dom typ _ =>
        match validateSocketpairArgs dom typ with
        | some e => pure (Except.error e)
        | none => pure (Except.ok (0, 1)) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_socketAndSocketpairMatrix,
    stubNetOps, validateSocketArgs, validateSocketpairArgs, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  have hBad := h.2.2.2.2.2.2.2.2.2.1.2.1
  have hEq : (SockType.dgram == SockType.dgram && IPPROTO_TCP == IPPROTO_TCP) = true := by decide
  rw [hEq] at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_ops_socketAndSocketpairMatrix
    { stubNetOps with
      socket := fun dom typ _ proto =>
        match validateSocketArgs dom typ proto with
        | some e => pure (Except.error e)
        | none => pure (Except.ok 0)
      socketpair := fun dom _ _ =>
        match dom with
        | .unix => pure (Except.ok (0, 1))
        | .inet | .inet6 => pure (Except.error Errno.EOPNOTSUPP) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_socketAndSocketpairMatrix,
    stubNetOps, validateSocketArgs, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  injection h.2.2.2.2.2.2.2.1.1 with hErr
  exact absurd hErr (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .getsockname 0, .addr (.ipv6 0 0x0000ffff7f000001 49152 0 0) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .getsockname 0, .addr (.ipv6 0 0x0000ffffac10e795 45000 0 0) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_model_taintedAbortLastAckAndMcastRouted
    (fun s req out =>
      match req, out with
      | .accept4 3 _, .accepted 4 (.ipv4 0x7f000001 49152) => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_net_ops_socketAndSocketpairMatrix
    { stubNetOps with
      socket := fun dom typ _ proto =>
        if dom == .unix && proto == PF_UNIX then pure (Except.error Errno.EPROTONOSUPPORT)
        else
          match validateSocketArgs dom typ proto with
          | some e => pure (Except.error e)
          | none => pure (Except.ok 0)
      socketpair := fun dom typ _ =>
        match validateSocketpairArgs dom typ with
        | some e => pure (Except.error e)
        | none => pure (Except.ok (0, 1)) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_net_ops_socketAndSocketpairMatrix,
    stubNetOps, validateSocketArgs, validateSocketpairArgs, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  rcases h.2.2.2.2.2.2.2.2.2.2.1.1 with ⟨_, hBad⟩
  cases hBad

end LeanSwe.LinuxSyscall.Net
