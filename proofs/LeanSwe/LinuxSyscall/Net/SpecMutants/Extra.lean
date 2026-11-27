import LeanSwe.LinuxSyscall.Net.SpecTests

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

private def refMkNetOpsM {m : Type → Type} {fd : Type} [Monad m]
    (raw : PosixNetOpsM m fd) : NetOpsM m fd :=
  { socket := fun domain sockType flags proto =>
      match validateSocketArgs domain sockType proto with
      | some e => pure (.error e)
      | none => raw.socket domain.toTag sockType.toTag flags.toBits proto
    socketpair := fun domain sockType flags =>
      match validateSocketpairArgs domain sockType with
      | some e => pure (.error e)
      | none => raw.socketpair domain.toTag sockType.toTag flags.toBits
    bind := fun fd addr =>
      if !addr.isValidTarget then pure (.error Errno.EINVAL)
      else raw.bind fd addr.toRawTuple
    listen := raw.listen
    accept4 := fun fd flags => do
      match ← raw.accept4 fd flags.toBits with
      | .ok (cfd, rawSa) => return .ok (cfd, SockAddr.ofRawTuple rawSa)
      | .error e => return .error e
    connect := fun fd addr =>
      if !addr.isValidTarget then pure (.error Errno.EINVAL)
      else raw.connect fd addr.toRawTuple
    getsockopt := fun fd opt => raw.getsockopt fd opt.toTag
    setsockopt := fun fd opt val => raw.setsockopt fd opt.toTag val
    getsockname := fun fd => do
      match ← raw.getsockname fd with
      | .ok rawSa => return .ok (SockAddr.ofRawTuple rawSa)
      | .error e => return .error e
    recvfrom := fun fd maxBytes flags => raw.recvfrom fd maxBytes flags.toBits
    sendto := fun fd data flags => raw.sendto fd data flags.toBits
    shutdown := fun fd how => raw.shutdown fd how.toTag
    sendmsg := fun fd fds =>
      if !isValidScmCount fds.size then pure (.error Errno.EINVAL)
      else raw.sendmsg fd fds
    recvmsg := fun fd maxFds =>
      if !isValidScmCount maxFds.toNat then pure (.error Errno.EINVAL)
      else raw.recvmsg fd maxFds
    ioctl := fun fd op ifname =>
      if !isValidIfname ifname then pure (.error Errno.EINVAL)
      else
        let (tag, arg) := op.toRaw
        raw.ioctl fd tag arg ifname }

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
      { refMkNetOpsM raw with socket := fun dom typ sf proto => raw.socket dom.toTag typ.toTag sf.toBits proto })) := by
  intro h
  have h0 := h mutIdRawNetOps .inet .seqpacket {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) rfl
    128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[0] (by decide) 1 (by decide) .getIfFlags loIfname (by decide)
  have hBad := h0.1
  change (Except.ok 0 : Except Errno Nat) = Except.error Errno.ESOCKTNOSUPPORT at hBad
  cases hBad

example : ¬ Core.AllPass (test_net_mkNetOps_encodesAndDelegates
    (fun raw =>
      { refMkNetOpsM raw with sendto := fun fd data _ => raw.sendto fd data 0 })) := by
  intro h
  have h0 := h mutIdRawNetOps .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) rfl
    128 .error .reuseAddr 1 16 { nosignal := true } (ByteArray.mk #[]) .rdwr #[0] (by decide) 1 (by decide) .getIfFlags loIfname (by decide)
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.1
  change (Except.ok 0 : Except Errno UInt32) = Except.ok 1 at hBad
  injection hBad with hEq
  exact absurd hEq (by decide)

private def rawWiringNetOps : PosixNetOpsM Id Nat :=
  { socket := fun _ _ sfBits _ => .ok sfBits.toNat
    socketpair := fun _ _ _ => .ok (0, 1)
    bind := fun _ _ => .ok ()
    listen := fun _ _ => .ok ()
    accept4 := fun _ _ => .ok (1, (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[]))
    connect := fun _ _ => .ok ()
    getsockopt := fun _ _ => .ok 0
    setsockopt := fun _ _ _ => .ok ()
    getsockname := fun _ => .ok (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[])
    recvfrom := fun _ _ _ => .ok (ByteArray.mk #[])
    sendto := fun _ _ mfBits => .ok mfBits
    shutdown := fun _ _ => .ok ()
    sendmsg := fun _ _ => .ok ()
    recvmsg := fun _ _ => .ok #[]
    ioctl := fun _ _ _ _ => .ok 0 }

private def refIdNetOps : NetOpsM Id Nat :=
  refMkNetOpsM rawWiringNetOps

example : ¬ Core.AllPass (test_net_interface_defaultOpsWiring
    (refMkNetOpsM (m := Id)) refIdNetOps
    refIdNetOps.socket (fun d t => refIdNetOps.socket d t { nonblock := false, cloexec := false } 0)
    refIdNetOps.socketpair (fun d t => refIdNetOps.socketpair d t { nonblock := false, cloexec := true })
    refIdNetOps.bind refIdNetOps.listen (fun h => refIdNetOps.listen h 128)
    refIdNetOps.accept4 (fun h => refIdNetOps.accept4 h { nonblock := false, cloexec := true })
    refIdNetOps.connect refIdNetOps.getsockopt refIdNetOps.setsockopt refIdNetOps.getsockname
    refIdNetOps.recvfrom (fun h m => refIdNetOps.recvfrom h m {})
    refIdNetOps.sendto (fun h d => refIdNetOps.sendto h d { nosignal := true })
    refIdNetOps.shutdown refIdNetOps.sendmsg refIdNetOps.recvmsg refIdNetOps.ioctl) := by
  intro h
  have h0 := h .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) 128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[] 1 .getIfFlags loIfname
  have hBad := h0.2.2.1
  change (Except.ok 0 : Except Errno Nat) = Except.ok 2 at hBad
  injection hBad with hEq
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_net_interface_defaultOpsWiring
    (refMkNetOpsM (m := Id)) refIdNetOps
    refIdNetOps.socket (fun d t => refIdNetOps.socket d t { nonblock := false, cloexec := true } 0)
    refIdNetOps.socketpair (fun d t => refIdNetOps.socketpair d t { nonblock := false, cloexec := true })
    refIdNetOps.bind refIdNetOps.listen (fun h => refIdNetOps.listen h 128)
    refIdNetOps.accept4 (fun h => refIdNetOps.accept4 h { nonblock := false, cloexec := true })
    refIdNetOps.connect refIdNetOps.getsockopt refIdNetOps.setsockopt refIdNetOps.getsockname
    refIdNetOps.recvfrom (fun h m => refIdNetOps.recvfrom h m {})
    refIdNetOps.sendto (fun h d => refIdNetOps.sendto h d { nosignal := false })
    refIdNetOps.shutdown refIdNetOps.sendmsg refIdNetOps.recvmsg refIdNetOps.ioctl) := by
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
