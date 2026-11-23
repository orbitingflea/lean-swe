import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Sandbox.Interface
import Fuzz.LinuxSyscall.Rng
import Fuzz.LinuxSyscall.SandboxEnv
import Std.Data.HashMap

namespace Fuzz.LinuxSyscall.NetFuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

@[extern "leanswe_net_close_fd"]
private opaque rawNetClose : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_net_open_nonsock"]
private opaque rawOpenNonsock : IO (Except Errno RawFd)

@[extern "leanswe_poll_rlimit_nofile"]
private opaque rawRlimitNofile : UInt8 → UInt64 → IO (Except Errno UInt64)

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque rawArmSigalrm : UInt32 → UInt8 → BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque rawDisarmSigalrm : UInt32 → BaseIO Unit

@[extern "leanswe_net_get_fd_flags"]
private opaque rawNetGetFdFlags : @& RawFd → IO (Except Errno UInt32)

@[extern "leanswe_net_reset_sigpipe_dfl"]
private opaque rawResetSigpipeDfl : BaseIO Unit

private def checkNetFdFlags (ctx : String) (rfd : RawFd) (flags : SockFlags) : IO (Except String Unit) := do
  let expected : UInt32 := (if flags.cloexec then 1 else 0) ||| (if flags.nonblock then 2 else 0)
  match ← rawNetGetFdFlags rfd with
  | .error e => return .error s!"{ctx} fd flag check failed: {e}"
  | .ok got =>
    if got != expected then
      return .error s!"{ctx} fd flags mismatch: flags={repr flags} expected={expected} got={got}"
    return .ok ()

private def sameNetOutcomeShape (a b : String) : Bool :=
  if a == b then true
  else
    let norm := fun (s : String) => s.replace "LeanSwe.LinuxSyscall.Net." ""
    let na := norm a
    let nb := norm b
    let hasStem := fun (s p : String) => s == p || s.startsWith (p ++ " ")
    let stems :=
      #[ "NetOutcome.opened"
       , "NetOutcome.pair"
       , "NetOutcome.accepted"
       , "NetOutcome.fds"
       , "NetOutcome.addr"
       , "NetOutcome.u32"
       , "NetOutcome.bytes" ]
    stems.any fun p => hasStem na p && hasStem nb p

private def extractNetOut? (s : String) : Option String :=
  match s.splitOn " out=" with
  | [_, rest] =>
    let flat := " ".intercalate ((rest.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))
    some flat
  | _ => none

private def matchesNetMismatch (wantPrefix : String) (wantOut? : Option String) (mm : String) : Bool :=
  mm.startsWith wantPrefix &&
    match wantOut?, extractNetOut? mm with
    | none, _ => true
    | some w, some g => sameNetOutcomeShape w g
    | some _, none => false

local instance : Repr ByteArray where
  reprPrec b _ :=
    if b.size > 64 then f!"ByteArray(len={b.size})"
    else f!"ByteArray.mk {repr b.data}"

/-- Symbolic handle identifier used inside shrinkable `Net` fuzz traces. -/
abbrev SymFd := Nat

/-- Symbolic socket address allowing replay and shrinking across ephemeral OS ports and temp directories. -/
inductive SymAddr where
  /-- Fixed literal `SockAddr`. -/
  | fixed (sa : SockAddr)
  /-- Relative `AF_UNIX` filename placed inside the episode's private directory. -/
  | unixRel (relName : String)
  /-- Concrete local `SockAddr` observed via `getsockname` on `target`, optionally overriding IPv4 host. -/
  | sameLocalOf (target : SymFd) (ipOverride? : Option UInt32 := none)
  /-- Cross-family loopback address targeting `target` (`AF_INET` <-> `::ffff:127.x.y.z`). -/
  | crossFamilyTo (target : SymFd)
  /-- TCP simultaneous self-connect targeting `target`'s own concrete local `SockAddr`. -/
  | tcpSelfConnect (target : SymFd)
  deriving Repr

/-- Symbolic `Net` syscall or descriptor-lifecycle request using `SymFd` and `SymAddr`. -/
inductive SymReq where
  /-- `socket(domain, sockType, flags, proto)`. -/
  | socket (domain : SockDomain) (sockType : SockType) (flags : SockFlags) (proto : UInt32)
  /-- `socketpair(domain, sockType, flags)`. -/
  | socketpair (domain : SockDomain) (sockType : SockType) (flags : SockFlags)
  /-- Open a non-socket handle via `leanswe_net_open_nonsock`. -/
  | openNonsock
  /-- Close a handle via `leanswe_net_close_fd`. -/
  | close (fd : SymFd)
  /-- `bind(fd, addr)`. -/
  | bind (fd : SymFd) (addr : SymAddr)
  /-- `listen(fd, backlog)`. -/
  | listen (fd : SymFd) (backlog : UInt32)
  /-- `accept4(fd, flags)`. -/
  | accept4 (fd : SymFd) (flags : SockFlags)
  /-- `connect(fd, addr)`. -/
  | connect (fd : SymFd) (addr : SymAddr)
  /-- `getsockopt(fd, opt)`. -/
  | getsockopt (fd : SymFd) (opt : SockOpt)
  /-- `setsockopt(fd, opt, val)`. -/
  | setsockopt (fd : SymFd) (opt : SetSockOpt) (val : UInt32)
  /-- `getsockname(fd)`. -/
  | getsockname (fd : SymFd)
  /-- `recvfrom(fd, maxBytes, flags)`. -/
  | recvfrom (fd : SymFd) (maxBytes : UInt32) (flags : MsgFlags)
  /-- `sendto(fd, data, flags)`. -/
  | sendto (fd : SymFd) (data : ByteArray) (flags : MsgFlags)
  /-- `shutdown(fd, how)`. -/
  | shutdown (fd : SymFd) (how : ShutHow)
  /-- `sendmsg(fd, fds)`. -/
  | sendmsg (fd : SymFd) (fds : Array SymFd)
  /-- `recvmsg(fd, maxFds)`. -/
  | recvmsg (fd : SymFd) (maxFds : UInt32)
  /-- `ioctl(fd, op, ifname)`. -/
  | ioctl (fd : SymFd) (op : NetIoctlOp) (ifname : ByteArray)
  /-- Adjust process soft `RLIMIT_NOFILE` limit (`0` restores saved baseline). -/
  | setSoftNofile (limit : UInt64)
  deriving Repr

/-- Recorded step in a `Net` fuzzing episode with pre-allocated symbolic handle slots. -/
structure SymStep where
  /-- Symbolic handle slots reserved for any descriptors produced by this step. -/
  allocIds : Array SymFd
  /-- Syscall or helper request executed at this step. -/
  req : SymReq
  /-- Arm a short `SIGALRM` (`ITIMER_REAL`) around this syscall to exercise `EINTR`. -/
  armAlrm : Bool := false
  deriving Repr

/-- Per-(syscall, outcome) hit counter table accumulated across `Net` fuzzing episodes. -/
structure HitStats where
  /-- Counts keyed by `"<syscall>:<ok|err(errno)>"`. -/
  counts : Std.HashMap String Nat := {}
  /-- Total `Net` model syscalls executed. -/
  totalSteps : Nat := 0
  /-- Total fuzz episodes executed. -/
  totalEpisodes : Nat := 0

/-- Names of all 15 `Net` syscalls verified for coverage. -/
def allSyscallNames : Array String :=
  #[ "socket", "socketpair", "bind", "listen", "accept4", "connect"
   , "getsockopt", "setsockopt", "getsockname", "recvfrom", "sendto"
   , "shutdown", "sendmsg", "recvmsg", "ioctl" ]

/-- Record one `Net` syscall outcome into `HitStats`. -/
def HitStats.record (st : HitStats) (syscallName : String) (out : NetOutcome) : HitStats :=
  let bucket := match out with
    | .err e => s!"{syscallName}:err({e})"
    | _ => s!"{syscallName}:ok"
  let prev := st.counts.getD bucket 0
  { counts := st.counts.insert bucket (prev + 1)
    totalSteps := st.totalSteps + 1
    totalEpisodes := st.totalEpisodes }

private structure SymMeta where
  domain : Option SockDomain
  sockType : SockType
  nonblock : Bool
  isSocket : Bool

private structure GenEnv where
  allMeta : Std.HashMap SymFd SymMeta := {}
  openSocks : Array SymFd := #[]
  openNonsocks : Array SymFd := #[]
  allOpen : Array SymFd := #[]
  closedFds : Array SymFd := #[]
  listeners : Array (SymFd × SockDomain × SockType) := #[]
  boundTargets : Array (SymFd × SockDomain × SockType) := #[]
  needGetsockname : Array SymFd := #[]
  knownLiveAddrs : Std.HashMap SymFd SockAddr := {}
  unixSeq : Nat := 0
  absSeq : Nat := 0
  absTag : String := "0"
  allowBareAbs : Bool := false

private def symReqName : SymReq → Option String
  | .socket .. => some "socket"
  | .socketpair .. => some "socketpair"
  | .openNonsock => none
  | .close _ => none
  | .bind .. => some "bind"
  | .listen .. => some "listen"
  | .accept4 .. => some "accept4"
  | .connect .. => some "connect"
  | .getsockopt .. => some "getsockopt"
  | .setsockopt .. => some "setsockopt"
  | .getsockname .. => some "getsockname"
  | .recvfrom .. => some "recvfrom"
  | .sendto .. => some "sendto"
  | .shutdown .. => some "shutdown"
  | .sendmsg .. => some "sendmsg"
  | .recvmsg .. => some "recvmsg"
  | .ioctl .. => some "ioctl"
  | .setSoftNofile _ => none

private def allocSlotsForReq : SymReq → Nat
  | .socket .. => 1
  | .socketpair .. => 2
  | .openNonsock => 1
  | .accept4 .. => 1
  | .recvmsg _ maxFds => min MAX_SCM_FDS (max 1 maxFds.toNat)
  | _ => 0

private def resolveSymAddr (epDir : System.FilePath) (liveAddrs : Std.HashMap SymFd SockAddr)
    (sa : SymAddr) : Option SockAddr :=
  match sa with
  | .fixed a => some a
  | .unixRel name => some (.unix (epDir.toString ++ "/" ++ name).toUTF8)
  | .sameLocalOf target ipOv? =>
    match liveAddrs.get? target with
    | some (.ipv4 ip p) => some (.ipv4 (ipOv?.getD ip) p)
    | some (.ipv6 hi lo p fl sc) =>
      if hi == 0 && lo == 0 then some (.ipv6 0 1 p fl sc) else some (.ipv6 hi lo p fl sc)
    | some (.unix path) => some (.unix path)
    | none => none
  | .crossFamilyTo target =>
    match liveAddrs.get? target with
    | some (.ipv4 ip p) =>
      let effIp := if ip == INADDR_ANY then INADDR_LOOPBACK else ip
      some (.ipv6 0 (ipv4ToMappedV6Lo effIp) p 0 0)
    | some (.ipv6 hi lo p _ _) =>
      if hi == 0 && lo == 0 then some (.ipv4 INADDR_LOOPBACK p)
      else
        match mappedLoopbackV4? hi lo with
        | some mip => some (.ipv4 mip p)
        | none => some (.ipv4 INADDR_LOOPBACK p)
    | _ => none
  | .tcpSelfConnect target =>
    match liveAddrs.get? target with
    | some (.ipv4 ip p) =>
      some (.ipv4 (if ip == INADDR_ANY then INADDR_LOOPBACK else ip) p)
    | some (.ipv6 hi lo p fl sc) =>
      if hi == 0 && lo == 0 then some (.ipv6 0 1 p fl sc) else some (.ipv6 hi lo p fl sc)
    | some other => some other
    | none => none

private def genDomain (r : Rng) : SockDomain × Rng :=
  let (k, r1) := r.nextNat 3
  match k with
  | 0 => (.inet, r1)
  | 1 => (.inet6, r1)
  | _ => (.unix, r1)

private def genSockType (r : Rng) : SockType × Rng :=
  let (k, r1) := r.nextNat 10
  if k < 4 then (.stream, r1)
  else if k < 7 then (.dgram, r1)
  else (.seqpacket, r1)

private def genFlags (r : Rng) : SockFlags × Rng :=
  let (nb, r1) := r.chance 3 4
  let (ce, r2) := r1.chance 1 2
  ({ nonblock := nb, cloexec := ce }, r2)

private def genProto (r : Rng) (dom : SockDomain) (st : SockType) : UInt32 × Rng :=
  let (k, r1) := r.nextNat 12
  if k < 5 then (0, r1)
  else if k == 5 then
    if dom != .unix && st == .dgram then (IPPROTO_UDP, r1)
    else if dom != .unix && st == .stream then (IPPROTO_TCP, r1)
    else if dom == .unix then (PF_UNIX, r1)
    else (0, r1)
  else
    r1.pickArray
      #[0, PF_UNIX, 2, IPPROTO_TCP, IPPROTO_UDP, 58, 115, 132, 262, IPPROTO_MAX, 999] 0

private def largePayload65508 : ByteArray := ByteArray.mk (Array.replicate 65508 0x41)
private def largePayload65528 : ByteArray := ByteArray.mk (Array.replicate 65528 0x42)
private def largePayload70000 : ByteArray := ByteArray.mk (Array.replicate 70000 0x43)
private def largePayload250000 : ByteArray := ByteArray.mk (Array.replicate 250000 0x44)
private def largePayload500000 : ByteArray := ByteArray.mk (Array.replicate 500000 0x45)

private def largePayloads : Array ByteArray :=
  #[largePayload65508, largePayload65528, largePayload70000, largePayload250000, largePayload500000]

private def genBytes (r : Rng) (maxLen : Nat) : ByteArray × Rng :=
  let (len, r1) := r.nextRange 0 maxLen
  let rec go (k : Nat) (rng : Rng) (acc : Array UInt8) : ByteArray × Rng :=
    match k with
    | 0 => (ByteArray.mk acc, rng)
    | k' + 1 =>
      let (b, rng') := rng.nextNat 256
      go k' rng' (acc.push (UInt8.ofNat b))
  go len r1 #[]

private def genIfname (r : Rng) : ByteArray × Rng :=
  let (k, r1) := r.nextNat 7
  if k < 3 then (loIfname, r1)
  else if k == 3 then (asciiBytes ['n', 'o', 'p', 'e', '0'], r1)
  else if k == 4 then (ByteArray.mk #[108, 0], r1)
  else if k == 5 then (ByteArray.empty, r1)
  else (ByteArray.mk (Array.replicate 16 97), r1)

private def genAbsPath (absTag : String) (seq : Nat) (exact108 : Bool) : ByteArray :=
  if exact108 then
    let tag := s!"ls-{absTag}-{seq}-".toUTF8.data
    let padLen := UNIX_PATH_MAX - 1 - tag.size
    ByteArray.mk (#[0] ++ tag ++ Array.replicate padLen 97)
  else
    let tag := s!"leanswe-abs-{absTag}-{seq}".toUTF8.data
    ByteArray.mk (#[0] ++ tag ++ #[0, 120])

private def pickTargetFd (r : Rng) (env : GenEnv) : SymFd × Rng :=
  let (useClosed, r1) := r.chance 1 12
  if useClosed && !env.closedFds.isEmpty then
    r1.pickArray env.closedFds 0
  else
    let (useNs, r2) := r1.chance 1 12
    if useNs && !env.openNonsocks.isEmpty then
      r2.pickArray env.openNonsocks 0
    else if !env.openSocks.isEmpty then
      r2.pickArray env.openSocks 0
    else
      r2.pickArray env.allOpen 0

private def pickTargetOrBad? (r : Rng) (env : GenEnv) (cands : Array SymFd) : Option (SymFd × Rng) :=
  let (useBad, r1) := r.chance 1 10
  let bads := env.closedFds ++ env.openNonsocks
  if useBad && !bads.isEmpty then some (r1.pickArray bads 0)
  else if !cands.isEmpty then some (r1.pickArray cands 0)
  else if !bads.isEmpty then some (r1.pickArray bads 0)
  else none

private def isSocketNonblock (env : GenEnv) (sid : SymFd) : Bool :=
  match env.allMeta.get? sid with
  | some m => m.isSocket && m.nonblock
  | none => false

private def lookupSocket (s : NetState) (hid : HandleId) : Except Errno SockDesc :=
  match lookupHandleFileId s hid with
  | some fid => lookupFileSocket s fid
  | none => .error Errno.EBADF

private def isTcpUnhashedAfterConn (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid with
  | none => false
  | some hid =>
    match lookupSocket s hid with
    | .ok d =>
      match d.proto with
      | .tcp _ (.unhashed ..) .connected (.closedAfterConn ..) _ => true
      | _ => false
    | .error _ => false

private def safeBlockingAccept4 (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid with
  | none => true
  | some hid =>
    match lookupSocket s hid with
    | .error _ => true
    | .ok d => !d.proto.isListening || !(d.proto.acceptQueue?.getD []).isEmpty

private def safeBlockingRecv (s : NetState) (symMap : Std.HashMap SymFd HandleId)
    (sid : SymFd) (_isRecvmsg : Bool) : Bool :=
  match symMap.get? sid with
  | none => true
  | some hid =>
    match lookupSocket s hid with
    | .error _ => true
    | .ok d =>
      let tcpLoUncertain := d.domain != .unix && d.sockType == .stream &&
        (d.tcpLoFinPending || !(match s.loState with | .up _ => true | _ => false))
      let guaranteedSoError := !tcpLoUncertain && d.soError != 0 &&
        !(d.domain != .unix && d.sockType == .dgram && d.soError == Errno.ECONNREFUSED)
      let rxReady := !d.rxQueue.isEmpty && !tcpLoUncertain
      if guaranteedSoError || d.shut.rd || rxReady then true
      else
        match d.proto with
        | .tcp _ _ _ (.idle) _ | .tcp _ _ _ (.listen _ _) _ => true
        | .tcp _ _ _ (.closeWait _ _ _) _ | .tcp _ _ _ (.closedAfterConn _ _) _ => !tcpLoUncertain
        | .unixStream _ _ .idle | .unixStream _ _ (.listen _ _) => true
        | .unixStream _ _ (.connected _ peerShutWr _ peerReset _) => peerShutWr || peerReset
        | _ => false

private def hasNonEmptyRx (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
  | some d =>
    !d.rxQueue.isEmpty &&
    match d.proto with
    | .tcp _ _ ss (.established _ _) _ => ss == .connected
    | .tcp _ _ _ _ _ => false
    | _ => true
  | none => false

private def isUnackedCleanFinTcp (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd)
    (dontwait : Bool := false) : Bool :=
  match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
  | some d =>
    (d.nonblock || dontwait) && d.domain != .unix && d.rxQueue.isEmpty && !d.shut.rd && !d.tcpLoFinPending &&
    (d.proto matches .tcp _ _ _ (.closedAfterConn _ .cleanFin) _)
  | none => false

private def listenerQueueFull (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid with
  | none => false
  | some hid =>
    match lookupSocket s hid with
    | .ok d =>
      match d.proto with
      | .tcp _ _ _ (.listen bl aq) _ | .unixStream _ _ (.listen bl aq) => aq.length ≥ bl.toNat
      | _ => false
    | .error _ => false

private def safeBlockingConnect (s : NetState) (symMap : Std.HashMap SymFd HandleId)
    (liveAddrs : Std.HashMap SymFd SockAddr) (epDir : System.FilePath) (sid : SymFd) (sa : SymAddr) : Bool :=
  match symMap.get? sid with
  | none => true
  | some hid =>
    match lookupSocket s hid with
    | .error _ => true
    | .ok d =>
      if d.nonblock || d.sockType == .dgram then true
      else
        match resolveSymAddr epDir liveAddrs sa with
        | none => true
        | some addr =>
          let isV6TaintedNative := match d.proto with
            | .tcp .v6 _ _ _ true => addr.domain == .inet6 && !isIpv4MappedV6Addr addr
            | _ => false
          let addrSafe := !isV6TaintedNative && match addr with
            | .unix _ => true
            | _ => (s.loState matches .up _) && isLoopbackTargetAddr addr
          if !addrSafe then false
          else
            let targetFull := match sa with
              | .sameLocalOf t _ | .crossFamilyTo t | .tcpSelfConnect t => listenerQueueFull s symMap t
              | .fixed _ | .unixRel _ => false
            let anyAddrFull := s.files.any (fun (_, fdObj) =>
              match fdObj with
              | .socket ld =>
                match ld.proto with
                | .tcp _ _ _ (.listen bl aq) _ | .unixStream _ _ (.listen bl aq) =>
                  ld.localAddr? == some addr && aq.length ≥ bl.toNat
                | _ => false
              | _ => false)
            !targetFull && !anyAddrFull

private def genUnixFsCornerPath (epDir : System.FilePath) (seq : Nat) (targetLen : Nat) : String :=
  let prefixLen := epDir.toString.length + 1
  let base := s!"p{seq}-"
  let padLen := if targetLen > prefixLen + base.length + 5 then targetLen - prefixLen - base.length - 5 else 4
  base ++ String.ofList (List.replicate padLen 'a') ++ ".sock"

private def genBindAddr (r : Rng) (env : GenEnv) (epDir : System.FilePath) (sid : SymFd)
    (loNeverUp : Bool := false) : SymAddr × Rng :=
  let dom := match env.allMeta.get? sid with
    | some m => m.domain.getD .inet
    | none => .inet
  let (bad, r1) := r.chance 1 7
  if bad then
    let (pick, r2) := r1.nextNat 12
    match pick with
    | 0 => (.fixed (.ipv6 0xfe80000000000000 1 8080 0 0), r2)
    | 1 => (.fixed (.ipv6 0xff02000000000000 1 8080 0 0), r2)
    | 2 => (.fixed (.unix ByteArray.empty), r2)
    | 3 => (.fixed (.unix (ByteArray.mk #[47, 0, 97])), r2)
    | 4 => (.fixed (.unix (ByteArray.mk (Array.replicate 109 97))), r2)
    | 5 => (.fixed (.ipv4 0xe0000001 8080), r2)
    | 6 => (.fixed (.ipv4 0xffffffff 0), r2)
    | 7 => if loNeverUp then (.fixed (.unix ByteArray.empty), r2) else (.fixed (.ipv4 0xc0000201 0), r2)
    | 8 => if loNeverUp then (.fixed (.unix (ByteArray.mk #[47, 0, 97])), r2) else (.fixed (.ipv4 0x08080808 0), r2)
    | 9 => if loNeverUp then (.unixRel "missing/sub.sock", r2) else (.fixed (.ipv6 0x20010db800000000 1 0 0 0), r2)
    | 10 => (.unixRel "missing/sub.sock", r2)
    | _ => (.fixed (.ipv4 INADDR_LOOPBACK 81), r2)
  else
    let validTargets :=
      if !loNeverUp then env.boundTargets
      else env.boundTargets.filter fun (tid, d, _) =>
        match env.knownLiveAddrs.get? tid with
        | some (.ipv6 hi lo _ _ _) => (mappedV4Addr? hi lo).isSome
        | some _ => true
        | none => d != .inet6
    let (reuseConflict, r2) := r1.chance 1 4
    if reuseConflict && !validTargets.isEmpty then
      let ((tid, _, _), r3) := r2.pickArray validTargets (0, .inet, .stream)
      let (ipOvPick, r4) := r3.nextNat 5
      let ipOv :=
        if ipOvPick == 0 then none
        else if ipOvPick == 1 then some INADDR_ANY
        else if ipOvPick == 2 then some INADDR_LOOPBACK
        else if ipOvPick == 3 && !loNeverUp then some 0x7f000002
        else none
      (.sameLocalOf tid ipOv, r4)
    else
      match dom with
      | .inet =>
        let (ipPick, r3) := r2.nextNat 6
        let ip :=
          if ipPick == 0 then INADDR_LOOPBACK
          else if ipPick == 1 then INADDR_ANY
          else if loNeverUp then (if ipPick % 2 == 0 then INADDR_LOOPBACK else INADDR_ANY)
          else if ipPick == 2 then 0x7f000002
          else if ipPick == 3 then 0xffffffff
          else if ipPick == 4 then 0x7fffffff
          else 0xe0000001
        (.fixed (.ipv4 ip 0), r3)
      | .inet6 =>
        let (ipPick, r3) := r2.nextNat 9
        let (fl, r4) := r3.nextNat 4
        let (sc, r5) := r4.nextNat 2
        let flow := if fl == 0 then 0 else 0x12345
        let scope := if sc == 0 then 0 else 7
        if loNeverUp then
          if ipPick % 2 == 0 then (.fixed (.ipv6 0 0 0 flow scope), r5)
          else (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 flow scope), r5)
        else if ipPick == 0 then (.fixed (.ipv6 0 1 0 flow scope), r5)
        else if ipPick == 1 then (.fixed (.ipv6 0 0 0 flow scope), r5)
        else if ipPick == 2 then (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 flow scope), r5)
        else if ipPick == 3 then (.fixed (.ipv6 0 (ipv4ToMappedV6Lo 0x7f000002) 0 flow scope), r5)
        else if ipPick == 4 then (.fixed (.ipv6 0 0x0000ffff00000000 0 flow scope), r5)
        else if ipPick == 5 then (.fixed (.ipv6 0xff0e000000000000 1 0 flow scope), r5)
        else if ipPick == 6 then (.fixed (.ipv6 0xff02000000000000 1 0 flow 1), r5)
        else if ipPick == 7 then (.fixed (.ipv6 0 (ipv4ToMappedV6Lo 0x7fffffff) 0 flow scope), r5)
        else (.fixed (.ipv6 0 1 0 0 0), r5)
      | .unix =>
        let (uPick, r3) := r2.nextNat 7
        if uPick == 0 then (.fixed (.unix (genAbsPath env.absTag env.absSeq false)), r3)
        else if uPick == 1 then (.fixed (.unix (genAbsPath env.absTag env.absSeq true)), r3)
        else if uPick == 2 then
          let p := if env.allowBareAbs then ByteArray.mk #[0] else ByteArray.mk (#[0] ++ s!"s{env.absTag}".toUTF8.data)
          (.fixed (.unix p), r3)
        else if uPick == 3 && epDir.toString.length < 95 then
          (.unixRel (genUnixFsCornerPath epDir env.unixSeq 107), r3)
        else if uPick == 4 && env.unixSeq > 0 then
          (.unixRel s!"u{env.unixSeq - 1}.sock/sub.sock", r3)
        else (.unixRel s!"u{env.unixSeq}.sock", r3)

private def isNativeMcastBoundV6 (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid with
  | none => false
  | some hid =>
    match lookupSocket s hid with
    | .ok d =>
      match d.localAddr? with
      | some (.ipv6 hi _ _ _ _) => (hi >>> 56) == 0xff
      | _ => false
    | .error _ => false

private def genConnectAddr (r : Rng) (env : GenEnv) (s : NetState)
    (symMap : Std.HashMap SymFd HandleId) (epDir : System.FilePath) (sid : SymFd) : SymAddr × Rng :=
  let isNb := isSocketNonblock env sid
  let isDgram := match env.allMeta.get? sid with | some m => m.sockType == .dgram | none => false
  let (cand, rOut) : SymAddr × Rng :=
    let (bad, r1) := r.chance 1 7
    if bad then
      let (pick, r2) := r1.nextNat 14
      match pick with
      | 0 => (.fixed (.ipv6 0xfe80000000000000 1 8080 0 0), r2)
      | 1 => (.fixed (.unix ByteArray.empty), r2)
      | 2 => (.fixed (.unix (ByteArray.mk #[47, 0, 120])), r2)
      | 3 => (.fixed (.unix (ByteArray.mk (Array.replicate 109 98))), r2)
      | 4 => (.unixRel "missing-sock.sock", r2)
      | 5 => (.fixed (.unix (ByteArray.mk #[0, 109, 105, 115, 115])), r2)
      | 6 => (.fixed (.ipv6 0 0x0000ffff00000000 1 0 0), r2)
      | 7 => (.unixRel "missing/sub.sock", r2)
      | 8 =>
        if env.unixSeq > 0 then (.unixRel s!"u{env.unixSeq - 1}.sock/sub.sock", r2)
        else
          let p := if env.allowBareAbs then ByteArray.mk #[0] else ByteArray.mk (#[0] ++ s!"s{env.absTag}".toUTF8.data)
          (.fixed (.unix p), r2)
      | 9 =>
        if isNb || isDgram then (.fixed (.ipv4 0x08080808 80), r2)
        else (.fixed (.ipv4 INADDR_LOOPBACK 1), r2)
      | 10 =>
        if isNb || isDgram then (.fixed (.ipv4 0xc0000201 80), r2)
        else (.fixed (.ipv4 INADDR_LOOPBACK 1), r2)
      | 11 =>
        if isNb || isDgram then (.fixed (.ipv6 0x20010db800000000 1 80 0 0), r2)
        else (.fixed (.ipv6 0 1 80 0 0), r2)
      | 12 =>
        if isNb || isDgram then (.fixed (.ipv4 0xffffffff 80), r2)
        else (.fixed (.ipv4 0xe0000001 80), r2)
      | _ => (.fixed (.ipv6 0 1 80 0 0), r2)
    else
      let blockingNonDgram := !isNb && !isDgram
      let okBlockingTarget := fun (tid : SymFd) =>
        !blockingNonDgram || !listenerQueueFull s symMap tid
      let myDom := (env.allMeta.get? sid).bind (·.domain) |>.getD .inet
      let mySt := (env.allMeta.get? sid).map (·.sockType) |>.getD .stream
      let domCompat := fun (tgtSid : SymFd) (tgtDom : SockDomain) =>
        if tgtDom == myDom then true
        else if myDom == .inet6 && tgtDom == .inet then true
        else if myDom == .inet && tgtDom == .inet6 then
          match env.knownLiveAddrs.get? tgtSid with
          | some (.ipv6 0 0 _ _ _) => true
          | some a => isIpv4MappedV6Addr a
          | none => false
        else false
      let (selfPick, r2) := r1.chance 1 8
      if selfPick && env.knownLiveAddrs.contains sid && myDom != .unix then
        (.tcpSelfConnect sid, r2)
      else
        let (specialPick, rSp) := r2.nextNat 14
        if specialPick == 0 && (isNb || isDgram) && myDom != .unix then
          let (mPick, rM) := rSp.nextNat 6
          if myDom == .inet then
            let addr :=
              if mPick < 2 then (.ipv4 0x7fffffff 5555)
              else if mPick < 4 then (.ipv4 0xffffffff 5555)
              else (.ipv4 0xe0000001 5555)
            (.fixed addr, rM)
          else
            let addr :=
              if mPick == 0 then
                if isDgram then (.ipv6 0xff0e000000000000 1 5555 0 0)
                else (.ipv6 0xfe80000000000000 1 5555 0 0)
              else if mPick == 1 then
                if isDgram then (.ipv6 0xff02000000000000 1 5555 0 1)
                else (.ipv6 0x20010db800000000 1 5555 0 0)
              else if mPick == 2 then (.ipv6 0 (ipv4ToMappedV6Lo 0x7fffffff) 5555 0 0)
              else if mPick == 3 then (.ipv6 0 (ipv4ToMappedV6Lo 0xffffffff) 5555 0 0)
              else if mPick == 4 then (.ipv6 0x20010db800000000 1 5555 0 0)
              else (.ipv6 0 (ipv4ToMappedV6Lo 0xe0000001) 5555 0 0)
            (.fixed addr, rM)
        else
          let liveListeners := env.listeners.filter (fun p =>
            env.knownLiveAddrs.contains p.1 && okBlockingTarget p.1)
          let compatListeners := liveListeners.filter (fun p =>
            p.2.2 == mySt && domCompat p.1 p.2.1)
          let liveBound := env.boundTargets.filter (fun p =>
            env.knownLiveAddrs.contains p.1 && okBlockingTarget p.1)
          let compatBound := liveBound.filter (fun p =>
            p.2.2 == mySt && domCompat p.1 p.2.1)
          let (useListener, r3) := rSp.chance 4 5
          if useListener && !compatListeners.isEmpty then
            let ((lsid, ldom, _), r4) := r3.pickArray compatListeners (0, .inet, .stream)
            if ldom != myDom then
              (.crossFamilyTo lsid, r4)
            else
              let (useAltLoop, r5) := r4.chance 1 4
              (.sameLocalOf lsid (if useAltLoop then some 0x7f000002 else none), r5)
          else if !compatBound.isEmpty then
            let ((bsid, bdom, _), r4) := r3.pickArray compatBound (0, .inet, .stream)
            if bdom != myDom then
              (.crossFamilyTo bsid, r4)
            else
              let (useAltLoop, r5) := r4.chance 1 4
              (.sameLocalOf bsid (if useAltLoop then some 0x7f000002 else none), r5)
          else if !liveListeners.isEmpty then
            let ((lsid, _, _), r4) := r3.pickArray liveListeners (0, .inet, .stream)
            (.sameLocalOf lsid none, r4)
          else if !liveBound.isEmpty then
            let ((bsid, _, _), r4) := r3.pickArray liveBound (0, .inet, .stream)
            (.sameLocalOf bsid none, r4)
          else
            match myDom with
            | .inet => (.fixed (.ipv4 INADDR_LOOPBACK 1), r3)
            | .inet6 => (.fixed (.ipv6 0 1 1 0 0), r3)
            | .unix => (.unixRel "unconnected.sock", r3)
  let udpReconnectUnsafe :=
    match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
    | some d =>
      if d.domain == .unix then false
      else
        match d.proto with
        | .udp _ ubind (some _) =>
          match resolveSymAddr epDir env.knownLiveAddrs cand with
          | none => false
          | some rawAddr =>
            let addr := normalizeUdpTarget d.domain rawAddr
            if addr.domain != d.domain then false
            else
              let loUp := s.loState matches .up _
              !loUp || !isLoopbackTargetAddr addr || isBcastTargetAddr addr ||
                isInvalidV6LinkOrMulticast .dgram addr ||
                (v6MappedNativeMismatchErrno? ubind.addr? addr ubind.isAddrLocked).isSome
        | _ => false
    | none => false
  let udpWildcardLoopbackMismatch :=
    match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
    | some d =>
      match d.proto with
      | .udp _ ubind _ =>
        if ubind.addr?.isSome && !ubind.isAddrLocked then
          match resolveSymAddr epDir env.knownLiveAddrs cand with
          | some rawAddr =>
            let addr := normalizeUdpTarget d.domain rawAddr
            match addr with
            | .ipv4 ip _ => isIpv4Loopback ip && ip != INADDR_LOOPBACK
            | .ipv6 _ lo _ _ _ =>
              isIpv4MappedV6Addr addr &&
              let ip := lo.toUInt32
              isIpv4Loopback ip && ip != INADDR_LOOPBACK
            | _ => false
          | none => false
        else false
      | _ => false
    | none => false
  if !udpReconnectUnsafe && !udpWildcardLoopbackMismatch &&
      safeBlockingConnect s symMap env.knownLiveAddrs epDir sid cand then
    (cand, rOut)
  else (.fixed (.unix ByteArray.empty), rOut)

private def listenerHasPending (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid with
  | none => false
  | some hid =>
    match lookupSocket s hid with
    | .ok d => !(d.proto.acceptQueue?.getD []).isEmpty
    | .error _ => false

private def tcpPeerHasLargeUnread (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
  | some d =>
    match d.proto with
    | .tcp _ _ _ (.established (some peerFid) _) _
    | .tcp _ _ _ (.finWait (some peerFid) _) _
    | .tcp _ _ _ (.closeWait (some peerFid) _ _) _ =>
      match lookupFileSocket s peerFid with
      | .ok pd => pd.rxQueue.foldl (fun acc u => acc + u.bytes.data.size) 0 >= 4096
      | .error _ => false
    | _ => false
  | none => false

private def isTcpV6Tainted (s : NetState) (symMap : Std.HashMap SymFd HandleId) (sid : SymFd) : Bool :=
  match symMap.get? sid >>= (fun hid => (lookupSocket s hid).toOption) with
  | some d =>
    match d.proto with
    | .tcp .v6 _ _ _ true => true
    | _ => false
  | none => false

private def genSymReq (r : Rng) (env : GenEnv) (s : NetState) (symMap : Std.HashMap SymFd HandleId)
    (epDir : System.FilePath) (origNofile curNofile : UInt64) :
    SymReq × Bool × Rng :=
  if curNofile != origNofile then
    let (restore, r1) := r.chance 1 4
    if restore then (.setSoftNofile 0, false, r1)
    else
      let (emPick, r2) := r1.nextNat 6
      if emPick < 2 then
        let (dom, r3) := genDomain r2
        let (st, r4) := genSockType r3
        let (fl, r5) := genFlags r4
        let (proto, r6) := genProto r5 dom st
        (.socket dom st fl proto, false, r6)
      else if emPick < 4 then
        let (st, r3) := genSockType r2
        let (fl, r4) := genFlags r3
        (.socketpair .unix st fl, false, r4)
      else if emPick == 4 then
        let safeListeners := env.listeners.filter (fun p =>
          isSocketNonblock env p.1 || safeBlockingAccept4 s symMap p.1)
        if !safeListeners.isEmpty then
          let ((ls, _, _), r3) := r2.pickArray safeListeners (0, .inet, .stream)
          let (fl, r4) := genFlags r3
          (.accept4 ls fl, false, r4)
        else
          (.setSoftNofile 0, false, r2)
      else
        let safeUnix := env.allOpen.filter (fun sid =>
          (isSocketNonblock env sid || safeBlockingRecv s symMap sid true) &&
          (env.allMeta.get? sid).bind (·.domain) == some .unix)
        if !safeUnix.isEmpty then
          let (fd, r3) := r2.pickArray safeUnix 0
          (.recvmsg fd 2, false, r3)
        else
          (.setSoftNofile 0, false, r2)
  else
    let (doGsn, r0) := r.chance 3 4
    if doGsn && !env.needGetsockname.isEmpty then
      (.getsockname (env.needGetsockname.getD 0 0), false, r0)
    else if env.openSocks.size < 3 then
      let (useSp, r1) := r0.chance 1 4
      if useSp then
        let (st, r2) := genSockType r1
        let (fl, r3) := genFlags r2
        (.socketpair .unix st fl, false, r3)
      else
        let (dom, r2) := genDomain r1
        let (st, r3) := genSockType r2
        let (fl, r4) := genFlags r3
        let (proto, r5) := genProto r4 dom st
        (.socket dom st fl proto, false, r5)
    else
      let readyListenersNow := env.listeners.filter (fun p =>
        (isSocketNonblock env p.1 || safeBlockingAccept4 s symMap p.1) && listenerHasPending s symMap p.1)
      let (boostAccept, rBoost) :=
        if !readyListenersNow.isEmpty then r0.chance 1 8 else (false, r0)
      if boostAccept then
        let ((ls, _, _), rb) := rBoost.pickArray readyListenersNow (0, .inet, .stream)
        let (fl, r3) := genFlags rb
        (.accept4 ls fl, false, r3)
      else
      let (opPick, r1) := rBoost.nextNat 100
      if opPick == 99 then
        (.setSoftNofile (UInt64.ofNat (env.allOpen.size + 4)), false, r1)
      else if opPick < 8 && env.allOpen.size < 20 then
        let (kindPick, r2) := r1.nextNat 10
        if kindPick == 0 && env.openNonsocks.size < 2 then
          (.openNonsock, false, r2)
        else if kindPick < 4 then
          let (dom, r3) := genDomain r2
          let (st, r4) := genSockType r3
          let (fl, r5) := genFlags r4
          (.socketpair dom st fl, false, r5)
        else
          let (dom, r3) := genDomain r2
          let (st, r4) := genSockType r3
          let (fl, r5) := genFlags r4
          let (proto, r6) := genProto r5 dom st
          (.socket dom st fl proto, false, r6)
      else if opPick < 18 then
        let loNeverUp := match s.loState with | .down _ false => true | _ => false
        let bindCands := env.openSocks.filter (fun sid => !isTcpUnhashedAfterConn s symMap sid)
        match pickTargetOrBad? r1 env bindCands with
        | some (fd, r2) =>
          let (addr, r3) := genBindAddr r2 env epDir fd loNeverUp
          (.bind fd addr, false, r3)
        | none => (.openNonsock, false, r1)
      else if opPick < 25 then
        let listenCands := env.openSocks.filter (fun sid => !isTcpV6Tainted s symMap sid)
        match pickTargetOrBad? r1 env listenCands with
        | some (fd, r2) =>
          let (bl, r3) := r2.pickArray #[0, 1, 2, 8, 16, 0xffffffff] 8
          (.listen fd bl, false, r3)
        | none => (.openNonsock, false, r1)
      else if opPick < 33 then
        let blkEmptyListeners := env.listeners.filter (fun p =>
          !isSocketNonblock env p.1 && !listenerHasPending s symMap p.1)
        let (tryAlrm, ra) := r1.chance 1 16
        if tryAlrm && !blkEmptyListeners.isEmpty then
          let ((ls, _, _), r2) := ra.pickArray blkEmptyListeners (0, .inet, .stream)
          let (fl, r3) := genFlags r2
          (.accept4 ls fl, true, r3)
        else
          let safeListeners := env.listeners.filter (fun p =>
            isSocketNonblock env p.1 || safeBlockingAccept4 s symMap p.1)
          let readyListeners := safeListeners.filter (fun p => listenerHasPending s symMap p.1)
          let (preferReady, rr) := ra.chance 3 4
          let fdOpt :=
            if preferReady && !readyListeners.isEmpty then
              let ((ls, _, _), rb) := rr.pickArray readyListeners (0, .inet, .stream)
              some (ls, rb)
            else if !safeListeners.isEmpty then
              let ((ls, _, _), rb) := rr.pickArray safeListeners (0, .inet, .stream)
              some (ls, rb)
            else
              let safeSocks := env.openSocks.filter (fun sid =>
                isSocketNonblock env sid || safeBlockingAccept4 s symMap sid)
              pickTargetOrBad? rr env safeSocks
          match fdOpt with
          | some (fd, r2) =>
            let (fl, r3) := genFlags r2
            (.accept4 fd fl, false, r3)
          | none => (.openNonsock, false, rr)
      else if opPick < 45 then
        let nonListeners := env.openSocks.filter (fun sid => !env.listeners.any (·.1 == sid))
        let (preferNonLis, rC) := r1.chance 5 6
        let cands := if preferNonLis && !nonListeners.isEmpty then nonListeners else env.openSocks
        match pickTargetOrBad? rC env cands with
        | some (fd, r2) =>
          let (addr, r3) := genConnectAddr r2 env s symMap epDir fd
          let safeConn := isSocketNonblock env fd || safeBlockingConnect s symMap env.knownLiveAddrs epDir fd addr
          let (armC, r4) := if safeConn then (false, r3) else r3.chance 1 8
          if safeConn || armC then (.connect fd addr, armC, r4)
          else (.getsockname fd, false, r4)
        | none => (.openNonsock, false, rC)
      else if opPick < 50 then
        let (fd, r2) := pickTargetFd r1 env
        let (useErr, r3) := r2.chance 1 2
        (.getsockopt fd (if useErr then .error else .reuseAddr), false, r3)
      else if opPick < 56 then
        let (fd, r2) := pickTargetFd r1 env
        let (v, r3) := r2.pickArray #[0, 1, 2, 0x100, 0x10000, 0x80000000, 0xffffffff] 1
        (.setsockopt fd .reuseAddr v, false, r3)
      else if opPick < 62 then
        let (fd, r2) := pickTargetFd r1 env
        (.getsockname fd, false, r2)
      else if opPick < 71 then
        let (fd, r2) := pickTargetFd r1 env
        let (pk, r3) := r2.chance 1 5
        let isNb := isSocketNonblock env fd
        let safeBlk := isNb || safeBlockingRecv s symMap fd false
        let (tryAlrm, rA) := if !isNb && !safeBlk then r3.chance 1 6 else (false, r3)
        let (dw, r4) :=
          if tryAlrm then (false, rA)
          else if safeBlk then rA.chance 1 2
          else (true, rA)
        let szPool :=
          if !tryAlrm && hasNonEmptyRx s symMap fd then
            #[0, 1, 16, 64, 1024, MAX_READ_BYTES.toNat.toUInt32, 0x7fffffff, 0xffffffff]
          else
            #[1, 16, 64, 1024, MAX_READ_BYTES.toNat.toUInt32, 0x7fffffff, 0xffffffff]
        let (sz, r5) := r4.pickArray szPool 64
        if isUnackedCleanFinTcp s symMap fd dw then (.getsockname fd, false, r5)
        else (.recvfrom fd sz { peek := pk, dontwait := dw }, tryAlrm, r5)
      else if opPick < 80 then
        let (fd, r2) := pickTargetFd r1 env
        let (useLarge, rL) := r2.chance 1 6
        let avoidZeroSend := match symMap.get? fd >>= (fun hid => (lookupSocket s hid).toOption) with
          | some d =>
            match d.proto with
            | .unixStream _ _ (.connected pf? _ pwb _ _) => pf?.isNone || pwb
            | _ => false
          | none => false
        let (bs0, r3) :=
          if useLarge then rL.pickArray largePayloads largePayload65508
          else genBytes rL 24
        let bs := if avoidZeroSend && bs0.isEmpty then ByteArray.mk #[1] else bs0
        let (ns, r4) := r3.chance 1 2
        let isNb := isSocketNonblock env fd
        let (tryAlrm, rA) := if !isNb then r4.chance 1 16 else (false, r4)
        let (dw, r5) :=
          if tryAlrm then (false, rA)
          else if isNb then rA.chance 1 2
          else (true, rA)
        (.sendto fd bs { nosignal := ns, dontwait := dw }, tryAlrm, r5)
      else if opPick < 85 then
        let (fd, r2) := pickTargetFd r1 env
        let (k, r3) := r2.nextNat 3
        let rawHow : ShutHow := if k == 0 then .rd else if k == 1 then .wr else .rdwr
        if tcpPeerHasLargeUnread s symMap fd then (.getsockname fd, false, r3)
        else (.shutdown fd rawHow, false, r3)
      else if opPick < 90 then
        let unixSocks := env.openSocks.filter (fun sid =>
          (env.allMeta.get? sid).bind (·.domain) == some .unix)
        let (biasUnix, r2) := r1.chance 1 2
        let (fd, r3) :=
          if biasUnix && !unixSocks.isEmpty then r2.pickArray unixSocks 0
          else pickTargetFd r2 env
        let (cnt, r4) := r3.pickArray #[0, 1, 2, 3, 4, 5, 8, 16, 31, 32, 33] 1
        let rec pickPayloads (k : Nat) (rng : Rng) (acc : Array SymFd) : Array SymFd × Rng :=
          match k with
          | 0 => (acc, rng)
          | k' + 1 =>
            let (pfd, rng') := pickTargetFd rng env
            pickPayloads k' rng' (acc.push pfd)
        let (pfds, r5) := pickPayloads (min cnt 4) r4 #[]
        let finalPfds :=
          if cnt > 4 && !pfds.isEmpty then
            let padCnt := min cnt 33
            pfds ++ Array.replicate (padCnt - pfds.size) (pfds.getD 0 fd)
          else pfds
        let armSendmsg := !isSocketNonblock env fd && !finalPfds.isEmpty && finalPfds.size <= 32
        (.sendmsg fd finalPfds, armSendmsg, r5)
      else if opPick < 94 then
        let (tryAlrm, rA) := r1.chance 1 16
        let blkRecv := env.allOpen.filter (fun sid =>
          !isUnackedCleanFinTcp s symMap sid && !isSocketNonblock env sid && !safeBlockingRecv s symMap sid true)
        if tryAlrm && !blkRecv.isEmpty then
          let (fd, r3) := rA.pickArray blkRecv 0
          let (cap, r4) := r3.pickArray #[0, 1, 2, 4, 5, 16, 31, 32, 33] 1
          (.recvmsg fd cap, true, r4)
        else
          let safeRecvmsg := env.allOpen.filter (fun sid =>
            !isUnackedCleanFinTcp s symMap sid &&
            (isSocketNonblock env sid || safeBlockingRecv s symMap sid true))
          let safeUnix := safeRecvmsg.filter (fun sid =>
            (env.allMeta.get? sid).bind (·.domain) == some .unix)
          let (biasUnix, r2) := rA.chance 2 3
          let fdOpt :=
            if biasUnix && !safeUnix.isEmpty then some (r2.pickArray safeUnix 0)
            else pickTargetOrBad? r2 env safeRecvmsg
          match fdOpt with
          | some (fd, r3) =>
            let (cap, r4) := r3.pickArray #[0, 1, 2, 4, 5, 16, 31, 32, 33] 1
            (.recvmsg fd cap, false, r4)
          | none => (.openNonsock, false, rA)
      else if opPick < 97 then
        let (fd, r2) := pickTargetFd r1 env
        let (ifn, r3) := genIfname r2
        let (setOp, r4) := r3.chance 1 3
        let (op2, r5) :=
          if !setOp then (.getIfFlags, r4)
          else
            let (u, ra) := r4.nextU64
            (.setIfFlags u.toUInt32, ra)
        (.ioctl fd op2 ifn, false, r5)
      else
        let (useClosed, r2) := r1.chance 1 6
        if useClosed && !env.closedFds.isEmpty then
          let (fd, r3) := r2.pickArray env.closedFds 0
          (.close fd, false, r3)
        else
          let closeCands := env.allOpen.filter (fun sid => !tcpPeerHasLargeUnread s symMap sid)
          if !closeCands.isEmpty then
            let (fd, r3) := r2.pickArray closeCands 0
            (.close fd, false, r3)
          else
            (.openNonsock, false, r2)

private def closeOpenFds (openMap : Std.HashMap HandleId RawFd) : IO Unit := do
  for (_, rfd) in openMap.toList do
    let _ ← rawNetClose rfd

private def bindFreshSocket (symMap : Std.HashMap SymFd HandleId) (rawMap openMap : Std.HashMap HandleId RawFd)
    (hid : HandleId) (rfd : RawFd) (slot? : Option SymFd) :
    Std.HashMap SymFd HandleId × Std.HashMap HandleId RawFd × Std.HashMap HandleId RawFd :=
  let sm := match slot? with | some sid => symMap.insert sid hid | none => symMap
  (sm, rawMap.insert hid rfd, openMap.insert hid rfd)

private def applyModelAndTrack (modelState : NetState) (req : NetReq) (out : NetOutcome)
    (stepModel : NetState → NetReq → NetOutcome → Option NetState)
    (label : String) : IO (Except String NetState) := do
  match stepModel modelState req out with
  | some s' => return .ok s'
  | none => return .error s!"mismatch on {label}: req={repr req} out={repr out}"

private def execOneStep (ops : NetOps) (epDir : System.FilePath)
    (origNofile : UInt64) (curNofile : UInt64)
    (symMap : Std.HashMap SymFd HandleId)
    (rawMap : Std.HashMap HandleId RawFd)
    (openMap : Std.HashMap HandleId RawFd)
    (liveAddrs : Std.HashMap SymFd SockAddr)
    (modelState : NetState)
    (step : SymStep)
    (stepModel : NetState → NetReq → NetOutcome → Option NetState := allowedStep) :
    IO (Except String (Std.HashMap SymFd HandleId × Std.HashMap HandleId RawFd ×
      Std.HashMap HandleId RawFd × Std.HashMap SymFd SockAddr × UInt64 × NetState ×
      Option (String × NetOutcome))) := do
  let lookupRaw := fun (sid : SymFd) => symMap.get? sid >>= fun h => rawMap.get? h |>.map (fun r => (h, r))
  match step.req with
  | .socket domain sockType flags proto =>
    let req : NetReq := .socket domain sockType flags proto
    match ← ops.socket domain sockType flags proto with
    | .ok rfd =>
      match ← checkNetFdFlags "socket" rfd flags with
      | .error m =>
        let _ ← rawNetClose rfd
        return .error m
      | .ok () => pure ()
      let hid := modelState.nextHid
      let out : NetOutcome := .opened hid
      match ← applyModelAndTrack modelState req out stepModel "socket" with
      | .error e =>
        let _ ← rawNetClose rfd
        return .error e
      | .ok s' =>
        let (sm, rm, om) := bindFreshSocket symMap rawMap openMap hid rfd (step.allocIds[0]?)
        return .ok (sm, rm, om, liveAddrs, curNofile, s', some ("socket", out))
    | .error e =>
      let out : NetOutcome := .err e
      match ← applyModelAndTrack modelState req out stepModel "socket" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("socket", out))
  | .socketpair domain sockType flags =>
    let req : NetReq := .socketpair domain sockType flags
    match ← ops.socketpair domain sockType flags with
    | .ok (r0, r1) =>
      match ← checkNetFdFlags "socketpair[0]" r0 flags, ← checkNetFdFlags "socketpair[1]" r1 flags with
      | .error m, _ | _, .error m =>
        let _ ← rawNetClose r0
        let _ ← rawNetClose r1
        return .error m
      | .ok (), .ok () => pure ()
      let h0 := modelState.nextHid
      let h1 := h0 + 1
      let out : NetOutcome := .pair h0 h1
      match ← applyModelAndTrack modelState req out stepModel "socketpair" with
      | .error e =>
        let _ ← rawNetClose r0
        let _ ← rawNetClose r1
        return .error e
      | .ok s' =>
        let (sm1, rm1, om1) := bindFreshSocket symMap rawMap openMap h0 r0 (step.allocIds[0]?)
        let (sm2, rm2, om2) := bindFreshSocket sm1 rm1 om1 h1 r1 (step.allocIds[1]?)
        return .ok (sm2, rm2, om2, liveAddrs, curNofile, s', some ("socketpair", out))
    | .error e =>
      let out : NetOutcome := .err e
      match ← applyModelAndTrack modelState req out stepModel "socketpair" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("socketpair", out))
  | .openNonsock =>
    match ← rawOpenNonsock with
    | .error _ => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | .ok rfd =>
      let (hid, s') := modelState.registerNonSocket true
      let (sm, rm, om) := bindFreshSocket symMap rawMap openMap hid rfd (step.allocIds[0]?)
      return .ok (sm, rm, om, liveAddrs, curNofile, s', none)
  | .setSoftNofile lim =>
    let target := if lim == 0 then origNofile else lim
    match ← rawRlimitNofile 1 target with
    | .ok actual => return .ok (symMap, rawMap, openMap, liveAddrs, actual, modelState, none)
    | .error _ => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
  | .close sid =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let _ ← rawNetClose rfd
      let s' := match modelState.closeHandle hid with | .ok nx => nx | .error _ => modelState
      return .ok (symMap, rawMap, openMap.erase hid, liveAddrs.erase sid, curNofile, s', none)
  | .bind sid saddr =>
    match lookupRaw sid, resolveSymAddr epDir liveAddrs saddr with
    | some (hid, rfd), some sa =>
      let req : NetReq := .bind hid sa
      let out ← match ← ops.bind rfd sa with | .ok () => pure .unit | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "bind" with
      | .error m => return .error m
      | .ok s' =>
        let la :=
          match out with
          | .unit =>
            match sa with
            | .ipv4 _ 0 | .ipv6 _ _ 0 _ _ => liveAddrs
            | _ => liveAddrs.insert sid sa
          | _ => liveAddrs
        return .ok (symMap, rawMap, openMap, la, curNofile, s', some ("bind", out))
    | _, _ => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
  | .listen sid backlog =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .listen hid backlog
      let out ← match ← ops.listen rfd backlog with | .ok () => pure .unit | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "listen" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("listen", out))
  | .accept4 sid flags =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .accept4 hid flags
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.accept4 rfd flags
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      match res with
      | .ok (cfd, peerAddr) =>
        match ← checkNetFdFlags "accept4" cfd flags with
        | .error m =>
          let _ ← rawNetClose cfd
          return .error m
        | .ok () => pure ()
        let cHid := modelState.nextHid
        let out : NetOutcome := .accepted cHid peerAddr
        match ← applyModelAndTrack modelState req out stepModel "accept4" with
        | .error m =>
          let _ ← rawNetClose cfd
          return .error m
        | .ok s' =>
          let (sm, rm, om) := bindFreshSocket symMap rawMap openMap cHid cfd (step.allocIds[0]?)
          return .ok (sm, rm, om, liveAddrs, curNofile, s', some ("accept4", out))
      | .error e =>
        let out : NetOutcome := .err e
        match ← applyModelAndTrack modelState req out stepModel "accept4" with
        | .error m => return .error m
        | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("accept4", out))
  | .connect sid saddr =>
    match lookupRaw sid, resolveSymAddr epDir liveAddrs saddr with
    | some (hid, rfd), some sa =>
      let req : NetReq := .connect hid sa
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.connect rfd sa
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      let out := match res with | .ok () => .unit | .error e => .err e
      match ← applyModelAndTrack modelState req out stepModel "connect" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("connect", out))
    | _, _ => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
  | .getsockopt sid opt =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .getsockopt hid opt
      let out ← match ← ops.getsockopt rfd opt with | .ok v => pure (.u32 v) | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "getsockopt" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("getsockopt", out))
  | .setsockopt sid opt val =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .setsockopt hid opt val
      let out ← match ← ops.setsockopt rfd opt val with | .ok () => pure .unit | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "setsockopt" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("setsockopt", out))
  | .getsockname sid =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .getsockname hid
      let out ← match ← ops.getsockname rfd with | .ok sa => pure (.addr sa) | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "getsockname" with
      | .error m => return .error m
      | .ok s' =>
        let la := match out with
          | .addr (.ipv4 _ 0) | .addr (.ipv6 _ _ 0 _ _) => liveAddrs
          | .addr (.unix path) => if path.data.isEmpty then liveAddrs else liveAddrs.insert sid (.unix path)
          | .addr sa => liveAddrs.insert sid sa
          | _ => liveAddrs
        return .ok (symMap, rawMap, openMap, la, curNofile, s', some ("getsockname", out))
  | .recvfrom sid maxBytes flags =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .recvfrom hid maxBytes flags
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.recvfrom rfd maxBytes flags
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      let out := match res with | .ok bs => .bytes bs | .error e => .err e
      match ← applyModelAndTrack modelState req out stepModel "recvfrom" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("recvfrom", out))
  | .sendto sid data flags =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .sendto hid data flags
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.sendto rfd data flags
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      let out := match res with | .ok n => .u32 n | .error e => .err e
      match ← applyModelAndTrack modelState req out stepModel "sendto" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("sendto", out))
  | .shutdown sid how =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .shutdown hid how
      let out ← match ← ops.shutdown rfd how with | .ok () => pure .unit | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "shutdown" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("shutdown", out))
  | .sendmsg sid fds =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let mut hids : Array HandleId := #[]
      let mut rfds : Array RawFd := #[]
      let mut okAll := true
      for psid in fds do
        match lookupRaw psid with
        | some (phid, prfd) =>
          hids := hids.push phid
          rfds := rfds.push prfd
        | none => okAll := false
      if !okAll then return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
      let req : NetReq := .sendmsg hid hids
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.sendmsg rfd rfds
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      let out := match res with | .ok () => .unit | .error e => .err e
      match ← applyModelAndTrack modelState req out stepModel "sendmsg" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("sendmsg", out))
  | .recvmsg sid maxFds =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .recvmsg hid maxFds
      let res ← try
        if step.armAlrm then rawArmSigalrm 2000 0
        ops.recvmsg rfd maxFds
      finally
        if step.armAlrm then rawDisarmSigalrm 0
      match res with
      | .ok gotRfds =>
        for gfd in gotRfds do
          match ← rawNetGetFdFlags gfd with
          | .error fe =>
            for cfd in gotRfds do let _ ← rawNetClose cfd
            return .error s!"recvmsg fd flag check failed: {fe}"
          | .ok fl =>
            if (fl &&& 1) == 0 then
              for cfd in gotRfds do let _ ← rawNetClose cfd
              return .error s!"recvmsg fd flags missing FD_CLOEXEC: got={fl}"
        let mut gotHids : Array HandleId := #[]
        let baseHid := modelState.nextHid
        for i in [:gotRfds.size] do
          gotHids := gotHids.push (baseHid + i)
        let out : NetOutcome := .fds gotHids
        match ← applyModelAndTrack modelState req out stepModel "recvmsg" with
        | .error m =>
          for gfd in gotRfds do
            let _ ← rawNetClose gfd
          return .error m
        | .ok s' =>
          let mut sm := symMap
          let mut rm := rawMap
          let mut om := openMap
          for h : i in [:gotRfds.size] do
            let rcvFd := gotRfds[i]
            let rcvHid := baseHid + i
            let (sm', rm', om') := bindFreshSocket sm rm om rcvHid rcvFd (step.allocIds[i]?)
            sm := sm'
            rm := rm'
            om := om'
          return .ok (sm, rm, om, liveAddrs, curNofile, s', some ("recvmsg", out))
      | .error e =>
        let out : NetOutcome := .err e
        match ← applyModelAndTrack modelState req out stepModel "recvmsg" with
        | .error m => return .error m
        | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("recvmsg", out))
  | .ioctl sid op ifname =>
    match lookupRaw sid with
    | none => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, modelState, none)
    | some (hid, rfd) =>
      let req : NetReq := .ioctl hid op ifname
      let out ← match ← ops.ioctl rfd op ifname with | .ok v => pure (.u32 v) | .error e => pure (.err e)
      match ← applyModelAndTrack modelState req out stepModel "ioctl" with
      | .error m => return .error m
      | .ok s' => return .ok (symMap, rawMap, openMap, liveAddrs, curNofile, s', some ("ioctl", out))

/-- Result of replaying a symbolic `Net` trace. -/
structure ReplayResult where
  /-- Step index where `allowedStep` returned `none`, if any. -/
  mismatchIdx : Option Nat
  /-- Human-readable mismatch message, if any. -/
  mismatchMsg : Option String

/-- Replay a deterministic `Array SymStep` trace inside `epDir` against `defaultOps` and `stepModel`. -/
def replayTrace (epDir : System.FilePath) (trace : Array SymStep)
    (hasNetAdmin : Bool := false)
    (stepModel : NetState → NetReq → NetOutcome → Option NetState := allowedStep)
    (initialLoDown : Bool := false)
    (loWasEverUp : Bool := false) :
    IO ReplayResult := do
  if ← epDir.pathExists then
    IO.FS.removeDirAll epDir
  IO.FS.createDirAll epDir
  let ops := defaultOps
  if initialLoDown then
    match ← ops.socket .inet .dgram { nonblock := true, cloexec := true } 0 with
    | .ok tmpFd =>
      let _ ← ops.ioctl tmpFd (.setIfFlags IFF_LOOPBACK) loIfname
      let _ ← rawNetClose tmpFd
    | .error _ => pure ()
  else if hasNetAdmin then
    match ← ops.socket .inet .dgram { nonblock := true, cloexec := true } 0 with
    | .ok tmpFd =>
      let _ ← ops.ioctl tmpFd (.setIfFlags defaultLoFlags) loIfname
      let _ ← rawNetClose tmpFd
    | .error _ => pure ()
  let origNofile ← match ← rawRlimitNofile 0 0 with
    | .ok v => pure v
    | .error _ => pure 1024
  let mut curNofile := origNofile
  let mut symMap : Std.HashMap SymFd HandleId := {}
  let mut rawMap : Std.HashMap HandleId RawFd := {}
  let mut openMap : Std.HashMap HandleId RawFd := {}
  let mut liveAddrs : Std.HashMap SymFd SockAddr := {}
  let mut modelState :=
    if initialLoDown then
      if loWasEverUp then { NetState.initial hasNetAdmin with loState := .down IFF_LOOPBACK true }
      else NetState.initialNetns
    else NetState.initial hasNetAdmin
  try
    for h : idx in [:trace.size] do
      let step := trace[idx]
      let isNonblock := fun (sid : SymFd) =>
        match symMap.get? sid with
        | some hid =>
          match lookupSocket modelState hid with
          | .ok d => d.nonblock
          | .error _ => true
        | none => true
      let safeStep :=
        match step.req with
        | .accept4 sid _ => step.armAlrm || isNonblock sid || safeBlockingAccept4 modelState symMap sid
        | .connect sid sa => step.armAlrm || isNonblock sid || safeBlockingConnect modelState symMap liveAddrs epDir sid sa
        | .recvfrom sid _ fl => step.armAlrm || fl.dontwait || isNonblock sid || safeBlockingRecv modelState symMap sid false
        | .sendto sid _ fl => step.armAlrm || fl.dontwait || isNonblock sid
        | .sendmsg sid fds => step.armAlrm || isNonblock sid || fds.isEmpty || fds.size > 32
        | .recvmsg sid _ => step.armAlrm || isNonblock sid || safeBlockingRecv modelState symMap sid true
        | _ => true
      if !safeStep then
        return { mismatchIdx := none, mismatchMsg := none }
      match ← execOneStep ops epDir origNofile curNofile symMap rawMap openMap liveAddrs modelState step stepModel with
      | .error msg =>
        return { mismatchIdx := some idx, mismatchMsg := some msg }
      | .ok (sm, rm, om, la, cn, s', _) =>
        symMap := sm
        rawMap := rm
        openMap := om
        liveAddrs := la
        curNofile := cn
        modelState := s'
    return { mismatchIdx := none, mismatchMsg := none }
  finally
    let _ ← rawRlimitNofile 1 origNofile
    closeOpenFds openMap
    if ← epDir.pathExists then
      IO.FS.removeDirAll epDir

private def remapSymAddr (m : Std.HashMap SymFd SymFd) : SymAddr → Option SymAddr
  | .fixed a => some (.fixed a)
  | .unixRel name => some (.unixRel name)
  | .sameLocalOf t ipOv => (m.get? t).map (fun nt => .sameLocalOf nt ipOv)
  | .crossFamilyTo t => (m.get? t).map .crossFamilyTo
  | .tcpSelfConnect t => (m.get? t).map .tcpSelfConnect

private def normalizeTrace (raw : Array SymStep) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  let mut remap : Std.HashMap SymFd SymFd := {}
  let mut nextId : SymFd := 0
  let allocNew := fun (slots : Array SymFd) (rm : Std.HashMap SymFd SymFd) (nid : SymFd) => Id.run do
    let mut r := rm
    let mut n := nid
    let mut news : Array SymFd := #[]
    for old in slots do
      r := r.insert old n
      news := news.push n
      n := n + 1
    return (news, r, n)
  for step in raw do
    match step.req with
    | .socket d t fl p =>
      let (news, rm, nid) := allocNew step.allocIds remap nextId
      remap := rm
      nextId := nid
      out := out.push { allocIds := news, req := .socket d t fl p }
    | .socketpair d t fl =>
      let (news, rm, nid) := allocNew step.allocIds remap nextId
      remap := rm
      nextId := nid
      out := out.push { allocIds := news, req := .socketpair d t fl }
    | .openNonsock =>
      let (news, rm, nid) := allocNew step.allocIds remap nextId
      remap := rm
      nextId := nid
      out := out.push { allocIds := news, req := .openNonsock }
    | .accept4 sid fl =>
      if let some ns := remap.get? sid then
        let (news, rm, nid) := allocNew step.allocIds remap nextId
        remap := rm
        nextId := nid
        out := out.push { allocIds := news, req := .accept4 ns fl, armAlrm := step.armAlrm }
    | .recvmsg sid maxFds =>
      if let some ns := remap.get? sid then
        let trimmed :=
          if maxFds == 0 || maxFds.toNat > MAX_SCM_FDS then #[]
          else step.allocIds.take (allocSlotsForReq (.recvmsg ns maxFds))
        let (news, rm, nid) := allocNew trimmed remap nextId
        remap := rm
        nextId := nid
        out := out.push { allocIds := news, req := .recvmsg ns maxFds, armAlrm := step.armAlrm }
    | .close sid =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .close ns }
    | .bind sid sa =>
      if let (some ns, some nsa) := (remap.get? sid, remapSymAddr remap sa) then
        out := out.push { allocIds := #[], req := .bind ns nsa }
    | .listen sid bl =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .listen ns bl }
    | .connect sid sa =>
      if let (some ns, some nsa) := (remap.get? sid, remapSymAddr remap sa) then
        out := out.push { allocIds := #[], req := .connect ns nsa, armAlrm := step.armAlrm }
    | .getsockopt sid opt =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .getsockopt ns opt }
    | .setsockopt sid opt v =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .setsockopt ns opt v }
    | .getsockname sid =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .getsockname ns }
    | .recvfrom sid mb fl =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .recvfrom ns mb fl, armAlrm := step.armAlrm }
    | .sendto sid bs fl =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .sendto ns bs fl, armAlrm := step.armAlrm }
    | .shutdown sid how =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .shutdown ns how }
    | .sendmsg sid pfds =>
      if let (some ns, some npfds) := (remap.get? sid, pfds.mapM remap.get?) then
        out := out.push { allocIds := #[], req := .sendmsg ns npfds, armAlrm := step.armAlrm }
    | .ioctl sid op ifn =>
      if let some ns := remap.get? sid then
        out := out.push { allocIds := #[], req := .ioctl ns op ifn }
    | .setSoftNofile lim =>
      out := out.push { allocIds := #[], req := .setSoftNofile lim }
  return out

private def dropRange (xs : Array SymStep) (lo hi : Nat) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  for h : i in [:xs.size] do
    if i < lo || i >= hi then
      out := out.push xs[i]
  return normalizeTrace out

private def dropTwo (xs : Array SymStep) (idxA idxB : Nat) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  for h : i in [:xs.size] do
    if i != idxA && i != idxB then
      out := out.push xs[i]
  return normalizeTrace out

private def shrinkMsgFlagsCands (fl : MsgFlags) : Array MsgFlags := Id.run do
  let mut out : Array MsgFlags := #[]
  let pushIfNew := fun (arr : Array MsgFlags) (f : MsgFlags) =>
    if f != fl && !arr.contains f then arr.push f else arr
  out := pushIfNew out {}
  if fl.nosignal then out := pushIfNew out { fl with nosignal := false }
  if fl.dontwait then out := pushIfNew out { fl with dontwait := false }
  if fl.peek then out := pushIfNew out { fl with peek := false }
  return out

private def shrinkParamCands (st : SymStep) : Array SymReq := Id.run do
  match st.req with
  | .sendto sid bs fl =>
    let mut cands : Array SymReq := #[]
    if bs.size > 1 then
      cands := cands.push (.sendto sid ByteArray.empty fl)
      cands := cands.push (.sendto sid (ByteArray.mk #[bs.data[0]!]) fl)
      if bs.size > 4097 then
        cands := cands.push (.sendto sid (bs.extract 0 4097) fl)
      if bs.size > 65508 then
        cands := cands.push (.sendto sid (bs.extract 0 65508) fl)
      if bs.size > 2 then
        cands := cands.push (.sendto sid (bs.extract 0 (bs.size / 2)) fl)
    else if bs.size == 1 then
      cands := cands.push (.sendto sid ByteArray.empty fl)
    for fl' in shrinkMsgFlagsCands fl do
      cands := cands.push (.sendto sid bs fl')
    return cands
  | .recvfrom sid mb fl =>
    let mut cands : Array SymReq := #[]
    if mb > 1 then
      cands := cands.push (.recvfrom sid 0 fl)
      cands := cands.push (.recvfrom sid 1 fl)
      if mb > 4097 then
        cands := cands.push (.recvfrom sid 4097 fl)
      if mb > MAX_READ_BYTES.toNat.toUInt32 then
        cands := cands.push (.recvfrom sid MAX_READ_BYTES.toNat.toUInt32 fl)
      if mb > 2 then
        cands := cands.push (.recvfrom sid (mb / 2) fl)
    else if mb == 1 then
      cands := cands.push (.recvfrom sid 0 fl)
    for fl' in shrinkMsgFlagsCands fl do
      cands := cands.push (.recvfrom sid mb fl')
    return cands
  | .sendmsg sid pfds =>
    if pfds.size > 1 then Id.run do
      let mut out : Array SymReq := #[.sendmsg sid #[], .sendmsg sid #[pfds[0]!]]
      if pfds.size > 2 then
        let mid := pfds.size / 2
        out := out.push (.sendmsg sid (pfds.take mid))
        out := out.push (.sendmsg sid (pfds.extract mid pfds.size))
      for i in [:pfds.size] do
        out := out.push (.sendmsg sid (pfds.eraseIdxIfInBounds i))
      return out
    else if pfds.size == 1 then return #[.sendmsg sid #[]]
    else return #[]
  | .recvmsg sid maxFds =>
    if maxFds > 2 then
      return #[.recvmsg sid 0, .recvmsg sid 1, .recvmsg sid 2, .recvmsg sid (maxFds / 2)]
    else if maxFds == 2 then return #[.recvmsg sid 0, .recvmsg sid 1]
    else if maxFds == 1 then return #[.recvmsg sid 0]
    else return #[]
  | .setsockopt sid opt val =>
    if val > 1 then return #[.setsockopt sid opt 0, .setsockopt sid opt 1, .setsockopt sid opt (val / 2)]
    else if val == 1 then return #[.setsockopt sid opt 0]
    else return #[]
  | .listen sid bl =>
    if bl > 1 then return #[.listen sid 0, .listen sid 1, .listen sid (bl / 2)]
    else if bl == 1 then return #[.listen sid 0]
    else return #[]
  | .ioctl sid op ifn =>
    if sid > 2 then return #[.ioctl 0 op ifn, .ioctl 1 op ifn, .ioctl 2 op ifn]
    else if sid > 0 then return #[.ioctl 0 op ifn]
    else return #[]
  | _ => return #[]

private def substSymAddr (oldSym newSym : SymFd) : SymAddr → SymAddr
  | .sameLocalOf t ipOv => .sameLocalOf (if t == oldSym then newSym else t) ipOv
  | .crossFamilyTo t => .crossFamilyTo (if t == oldSym then newSym else t)
  | .tcpSelfConnect t => .tcpSelfConnect (if t == oldSym then newSym else t)
  | other => other

private def substSymReq (oldSym newSym : SymFd) : SymReq → SymReq
  | .accept4 sid fl => .accept4 (if sid == oldSym then newSym else sid) fl
  | .recvmsg sid mf => .recvmsg (if sid == oldSym then newSym else sid) mf
  | .close sid => .close (if sid == oldSym then newSym else sid)
  | .bind sid sa => .bind (if sid == oldSym then newSym else sid) (substSymAddr oldSym newSym sa)
  | .listen sid bl => .listen (if sid == oldSym then newSym else sid) bl
  | .connect sid sa => .connect (if sid == oldSym then newSym else sid) (substSymAddr oldSym newSym sa)
  | .getsockopt sid opt => .getsockopt (if sid == oldSym then newSym else sid) opt
  | .setsockopt sid opt v => .setsockopt (if sid == oldSym then newSym else sid) opt v
  | .getsockname sid => .getsockname (if sid == oldSym then newSym else sid)
  | .recvfrom sid mb fl => .recvfrom (if sid == oldSym then newSym else sid) mb fl
  | .sendto sid bs fl => .sendto (if sid == oldSym then newSym else sid) bs fl
  | .shutdown sid how => .shutdown (if sid == oldSym then newSym else sid) how
  | .sendmsg sid pfds =>
    .sendmsg (if sid == oldSym then newSym else sid) (pfds.map fun s => if s == oldSym then newSym else s)
  | .ioctl sid op ifn => .ioctl (if sid == oldSym then newSym else sid) op ifn
  | other => other

private def reqUsesSym (target : SymFd) : SymReq → Bool
  | .accept4 sid _ | .recvmsg sid _ | .close sid | .listen sid _
  | .getsockopt sid _ | .setsockopt sid _ _ | .getsockname sid
  | .recvfrom sid _ _ | .sendto sid _ _ | .shutdown sid _ | .ioctl sid _ _ => sid == target
  | .bind sid sa | .connect sid sa =>
    sid == target || match sa with
      | .sameLocalOf t _ | .crossFamilyTo t | .tcpSelfConnect t => t == target
      | _ => false
  | .sendmsg sid pfds => sid == target || pfds.contains target
  | _ => false

private def substSymAfterIdx (xs : Array SymStep) (afterIdx : Nat) (oldSym newSym : SymFd) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  for h : i in [:xs.size] do
    let st := xs[i]
    if i > afterIdx then
      out := out.push { st with req := substSymReq oldSym newSym st.req }
    else
      out := out.push st
  return normalizeTrace out

private def shrinkPairedScmCands (xs : Array SymStep) : Array (Array SymStep) := Id.run do
  let mut out : Array (Array SymStep) := #[]
  for h1 : i in [:xs.size] do
    match xs[i].req with
    | .sendmsg sid pfds =>
      if pfds.size > 0 then
        for j in [i + 1 : xs.size] do
          if let some rSt := xs[j]? then
            match rSt.req with
            | .recvmsg rsid maxFds =>
              if rSt.allocIds.size > 0 then
                for k in [:min pfds.size rSt.allocIds.size] do
                  let oldSym := rSt.allocIds[k]!
                  let srcSym := pfds[k]!
                  let usedLater := (xs.extract (j + 1) xs.size).any (fun st => reqUsesSym oldSym st.req)
                  if usedLater then
                    out := out.push (substSymAfterIdx xs j oldSym srcSym)
                if pfds.size > 1 && rSt.allocIds.size >= pfds.size then
                  let mid := pfds.size / 2
                  if mid > 0 then
                    let sTake := { xs[i] with req := .sendmsg sid (pfds.take mid) }
                    let rTake := { rSt with allocIds := rSt.allocIds.take mid, req := .recvmsg rsid (UInt32.ofNat mid) }
                    out := out.push (normalizeTrace ((xs.set! i sTake).set! j rTake))
                    let rem := pfds.size - mid
                    let sDrop := { xs[i] with req := .sendmsg sid (pfds.extract mid pfds.size) }
                    let rDrop := { rSt with allocIds := rSt.allocIds.extract mid pfds.size, req := .recvmsg rsid (UInt32.ofNat rem) }
                    out := out.push (normalizeTrace ((xs.set! i sDrop).set! j rDrop))
                  for k in [:pfds.size] do
                    let newP := pfds.eraseIdxIfInBounds k
                    let newA := rSt.allocIds.eraseIdxIfInBounds k
                    let newCap := UInt32.ofNat (max 1 (min maxFds.toNat newP.size))
                    let sEr := { xs[i] with req := .sendmsg sid newP }
                    let rEr := { rSt with allocIds := newA, req := .recvmsg rsid newCap }
                    out := out.push (normalizeTrace ((xs.set! i sEr).set! j rEr))
            | _ => pure ()
    | _ => pure ()
  return out

/-- Greedy delta-minimization shrinker with non-adjacent pair deletion, `SCM_RIGHTS` substitution/lockstep shrinking, parameter shrinking, and handle-ID compaction. -/
def shrinkTrace (trace : Array SymStep) (reproduces : Array SymStep → IO Bool) :
    IO (Array SymStep) := do
  let mut cur ← deltaShrink (normalizeTrace trace) Array.size dropRange reproduces
  let mut scmChanged := true
  while scmChanged do
    scmChanged := false
    for cand in shrinkPairedScmCands cur do
      if ← reproduces cand then
        cur ← deltaShrink cand Array.size dropRange reproduces
        scmChanged := true
        break
  let mut changed := true
  while changed && cur.size <= 128 do
    changed := false
    let n := cur.size
    let mut i := 0
    while !changed && i < n do
      let mut j := i + 1
      while !changed && j < n do
        let cand := dropTwo cur i j
        if cand.size < cur.size then
          if ← reproduces cand then
            cur ← deltaShrink cand Array.size dropRange reproduces
            changed := true
        j := j + 1
      i := i + 1
  let mut paramChanged := true
  while paramChanged do
    paramChanged := false
    for cand in shrinkPairedScmCands cur do
      if ← reproduces cand then
        cur ← deltaShrink cand Array.size dropRange reproduces
        paramChanged := true
        break
    if !paramChanged then
      for idx in [:cur.size] do
        if let some st := cur[idx]? then
          if st.armAlrm then
            let cand := normalizeTrace (cur.set! idx { st with armAlrm := false })
            if ← reproduces cand then
              cur ← deltaShrink cand Array.size dropRange reproduces
              paramChanged := true
              break
          for candReq in shrinkParamCands st do
            let cand := normalizeTrace (cur.set! idx { st with req := candReq })
            if ← reproduces cand then
              cur ← deltaShrink cand Array.size dropRange reproduces
              paramChanged := true
              break
          if paramChanged then
            break
  return cur

/-- Summary report produced by `runNetFuzz`. -/
structure FuzzReport where
  /-- Executed `Net` syscalls. -/
  totalSteps : Nat
  /-- Executed stateful episodes. -/
  totalEpisodes : Nat
  /-- Wall-clock milliseconds elapsed. -/
  elapsedMs : Nat
  /-- Throughput in syscalls/sec. -/
  syscallsPerSec : Nat
  /-- Hit counts keyed by `"<syscall>:<outcome>"`. -/
  stats : HitStats
  /-- Self-test shrinker diagnostic if `--self-test-shrink` was enabled. -/
  shrinkSelfTestDetail : String := ""
  /-- Optional diagnostic from an isolated `CLONE_NEWUSER | CLONE_NEWNET` `lo`-down probe. -/
  usernsDetail : String := ""

/-- Verify greedy delta-minimization and handle-ID compaction on a generated trace with a synthetic fault. -/
def runShrinkSelfTest (rootDir : System.FilePath) : IO String := do
  let mut rng := Rng.seed 0x4e4554534852494b
  let mut rawTrace : Array SymStep := #[]
  let mut nextId : SymFd := 0
  let nb : SockFlags := { nonblock := true, cloexec := true }
  for i in [:12] do
    if i == 4 || i == 9 then
      let sid := nextId
      nextId := nextId + 1
      let (p, r1) := rng.nextRange 1 3
      rng := r1
      rawTrace := rawTrace.push { allocIds := #[sid], req := .socket .inet .dgram nb 0 }
      rawTrace := rawTrace.push { allocIds := #[], req := .setsockopt sid .reuseAddr (UInt32.ofNat p) }
    else
      let sid := nextId
      nextId := nextId + 1
      rawTrace := rawTrace.push { allocIds := #[sid], req := .socket .inet .stream nb 0 }
      rawTrace := rawTrace.push { allocIds := #[], req := .close sid }
  let faultModel : NetState → NetReq → NetOutcome → Option NetState := fun st req out =>
    match req, out with
    | .setsockopt _ .reuseAddr v, .unit =>
      if v != 0 then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let epDir := rootDir / "shrink-self-test"
  let reproduces : Array SymStep → IO Bool := fun cand => do
    let r ← replayTrace epDir cand false faultModel
    return r.mismatchIdx.isSome
  if !(← reproduces rawTrace) then
    throw (IO.userError "net shrink self-test: baseline fault did not trigger")
  let shrunk ← shrinkTrace rawTrace reproduces
  if shrunk.size != 2 then
    throw (IO.userError s!"net shrink self-test: expected minimal size 2, got {shrunk.size} ({repr shrunk})")
  let firstAlloc := (shrunk.getD 0 { allocIds := #[], req := .openNonsock }).allocIds
  if firstAlloc != #[0] then
    throw (IO.userError s!"net shrink self-test: expected renumbered handle #[0], got {repr firstAlloc}")
  let mut pairRaw : Array SymStep := #[]
  pairRaw := pairRaw.push { allocIds := #[0], req := .socket .inet .stream nb 0 }
  pairRaw := pairRaw.push { allocIds := #[1, 2], req := .socketpair .unix .stream nb }
  pairRaw := pairRaw.push { allocIds := #[3], req := .socket .inet .dgram nb 0 }
  pairRaw := pairRaw.push { allocIds := #[], req := .close 0 }
  pairRaw := pairRaw.push { allocIds := #[], req := .sendto 1 (ByteArray.mk #[1, 2, 3, 4]) { nosignal := true, dontwait := true }, armAlrm := true }
  pairRaw := pairRaw.push { allocIds := #[], req := .close 3 }
  let pairFault : NetState → NetReq → NetOutcome → Option NetState := fun st req out =>
    match req, out with
    | .sendto _ bs _, .u32 _ =>
      if !bs.isEmpty then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let pairDir := rootDir / "shrink-pair-self-test"
  let pairInit ← replayTrace pairDir pairRaw false pairFault
  let pairMsg ← match pairInit.mismatchMsg with
    | some m => pure m
    | none => throw (IO.userError "net pair shrink self-test: baseline fault did not trigger")
  let pairWantOut? := extractNetOut? pairMsg
  let reproducesPair : Array SymStep → IO Bool := fun cand => do
    let r ← replayTrace pairDir cand false pairFault
    return (r.mismatchMsg.map (matchesNetMismatch "mismatch on sendto:" pairWantOut?)).getD false
  let pairShrunk ← shrinkTrace pairRaw reproducesPair
  if pairShrunk.size != 2 then
    throw (IO.userError s!"net pair shrink self-test: expected minimal size 2, got {pairShrunk.size} ({repr pairShrunk})")
  let pairStep1 := pairShrunk.getD 1 { allocIds := #[], req := .openNonsock }
  if pairStep1.armAlrm then
    throw (IO.userError "net pair shrink self-test: expected armAlrm to shrink to false")
  match pairStep1.req with
  | .sendto _ bs fl =>
    if bs.size != 1 || fl != {} then
      throw (IO.userError s!"net param shrink self-test: expected 1B payload and empty flags, got size={bs.size} flags={repr fl}")
  | other =>
    throw (IO.userError s!"net pair shrink self-test: expected sendto at step 1, got {repr other}")
  let wrapRaw : Array SymStep :=
    #[ { allocIds := #[0, 1], req := .socketpair .unix .stream nb }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk (Array.replicate 40 0x41)) { nosignal := true } }
     , { allocIds := #[], req := .recvfrom 1 64 { dontwait := true } }
     ]
  let wrapFault : NetState → NetReq → NetOutcome → Option NetState := fun st req out =>
    match req, out with
    | .recvfrom _ _ _, .bytes b =>
      if !b.isEmpty then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let wrapDir := rootDir / "shrink-wrap-self-test"
  let wrapInit ← replayTrace wrapDir wrapRaw false wrapFault
  let wrapMsg ← match wrapInit.mismatchMsg with
    | some m => pure m
    | none => throw (IO.userError "net wrap shrink self-test: baseline fault did not trigger")
  let wrapWantOut? := extractNetOut? wrapMsg
  let wrapShrunk ← shrinkTrace wrapRaw fun cand => do
    let r ← replayTrace wrapDir cand false wrapFault
    return (r.mismatchMsg.map (matchesNetMismatch "mismatch on recvfrom:" wrapWantOut?)).getD false
  match (wrapShrunk.getD 1 { allocIds := #[], req := .openNonsock }).req with
  | .sendto _ bs _ =>
    if bs.size != 1 then
      throw (IO.userError s!"net wrap shrink self-test: expected 1B payload after wrapped Repr, got {bs.size}")
  | other =>
    throw (IO.userError s!"net wrap shrink self-test: expected sendto at step 1, got {repr other}")
  let mut rmsgSlots : Array SymFd := #[]
  for k in [:16] do
    rmsgSlots := rmsgSlots.push (2 + k)
  let rmsgRaw : Array SymStep :=
    #[ { allocIds := #[0, 1], req := .socketpair .unix .stream nb }
     , { allocIds := #[], req := .sendmsg 0 #[0] }
     , { allocIds := rmsgSlots, req := .recvmsg 1 16 }
     , { allocIds := #[18], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .close 18 }
     ]
  let rmsgFault : NetState → NetReq → NetOutcome → Option NetState := fun st req out =>
    match req, out with
    | .recvmsg _ _, .fds fs =>
      if !fs.isEmpty then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let rmsgDir := rootDir / "shrink-rmsg-self-test"
  let rmsgInit ← replayTrace rmsgDir rmsgRaw false rmsgFault
  let rmsgMsg ← match rmsgInit.mismatchMsg with
    | some m => pure m
    | none => throw (IO.userError "net recvmsg shrink self-test: baseline fault did not trigger")
  let rmsgWantOut? := extractNetOut? rmsgMsg
  let rmsgShrunk ← shrinkTrace rmsgRaw fun cand => do
    let r ← replayTrace rmsgDir cand false rmsgFault
    return (r.mismatchMsg.map (matchesNetMismatch "mismatch on recvmsg:" rmsgWantOut?)).getD false
  if rmsgShrunk.size != 3 then
    throw (IO.userError s!"net recvmsg shrink self-test: expected size 3, got {rmsgShrunk.size} ({repr rmsgShrunk})")
  let rmsgStep2 := rmsgShrunk.getD 2 { allocIds := #[], req := .openNonsock }
  if rmsgStep2.allocIds != #[2] then
    throw (IO.userError s!"net recvmsg shrink self-test: expected compacted allocIds #[2], got {repr rmsgStep2.allocIds}")
  let mut scmAliasSlots : Array SymFd := #[]
  for k in [:16] do
    scmAliasSlots := scmAliasSlots.push (4 + k)
  let mut scmSendBatch : Array SymFd := #[]
  for k in [:16] do
    scmSendBatch := scmSendBatch.push (if k == 11 then 2 else 3)
  let scmAliasRaw : Array SymStep :=
    #[ { allocIds := #[0, 1], req := .socketpair .unix .stream nb }
     , { allocIds := #[2], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[3], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .sendmsg 0 scmSendBatch }
     , { allocIds := scmAliasSlots, req := .recvmsg 1 16 }
     , { allocIds := #[], req := .setsockopt 15 .reuseAddr 1 }
     ]
  let scmAliasDir := rootDir / "shrink-scm-alias-self-test"
  let scmAliasShrunk ← shrinkTrace scmAliasRaw fun cand => do
    let r ← replayTrace scmAliasDir cand false faultModel
    return r.mismatchIdx.isSome
  if scmAliasShrunk.size != 2 then
    throw (IO.userError s!"net scm alias shrink self-test: expected size 2, got {scmAliasShrunk.size} ({repr scmAliasShrunk})")
  let scmLockFault : NetState → NetReq → NetOutcome → Option NetState := fun st req out =>
    match req, out with
    | .setsockopt hid .reuseAddr 1, .unit =>
      if hid >= 3 then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let scmLockRaw : Array SymStep :=
    #[ { allocIds := #[0, 1], req := .socketpair .unix .stream nb }
     , { allocIds := #[2], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[3], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .sendmsg 0 scmSendBatch }
     , { allocIds := scmAliasSlots, req := .recvmsg 1 16 }
     , { allocIds := #[], req := .setsockopt 15 .reuseAddr 1 }
     ]
  let scmLockDir := rootDir / "shrink-scm-lock-self-test"
  let scmLockShrunk ← shrinkTrace scmLockRaw fun cand => do
    let r ← replayTrace scmLockDir cand false scmLockFault
    return r.mismatchIdx.isSome
  let shrunkSendLen? := scmLockShrunk.findSome? fun st =>
    match st.req with
    | .sendmsg _ pfds => some pfds.size
    | _ => none
  if shrunkSendLen? != some 1 || scmLockShrunk.size != 5 then
    throw (IO.userError s!"net scm lockstep shrink self-test: expected 1-fd sendmsg in 5 steps, got len={repr shrunkSendLen?} ({repr scmLockShrunk})")
  return s!"shrunk {rawTrace.size}->{shrunk.size} + {pairRaw.size}->{pairShrunk.size} + wrap + recvmsg + scm verified"

private def updateEnvAfterStep (env : GenEnv) (step : SymStep) (symMap : Std.HashMap SymFd HandleId)
    (liveAddrs : Std.HashMap SymFd SockAddr) (s : NetState)
    (out? : Option (String × NetOutcome)) : GenEnv :=
  match step.req with
  | .socket dom st fl _ =>
    match step.allocIds[0]?, out? with
    | some sid, some (_, .opened _) =>
      let metaEntry : SymMeta := { domain := some dom, sockType := st, nonblock := fl.nonblock, isSocket := true }
      { env with
        allMeta := env.allMeta.insert sid metaEntry
        openSocks := env.openSocks.push sid
        allOpen := env.allOpen.push sid }
    | _, _ => env
  | .socketpair dom st fl =>
    match step.allocIds[0]?, step.allocIds[1]?, out? with
    | some s0, some s1, some (_, .pair _ _) =>
      let metaEntry : SymMeta := { domain := some dom, sockType := st, nonblock := fl.nonblock, isSocket := true }
      { env with
        allMeta := (env.allMeta.insert s0 metaEntry).insert s1 metaEntry
        openSocks := (env.openSocks.push s0).push s1
        allOpen := (env.allOpen.push s0).push s1 }
    | _, _, _ => env
  | .openNonsock =>
    match step.allocIds[0]? with
    | some sid =>
      if symMap.contains sid then
        let metaEntry : SymMeta := { domain := none, sockType := .stream, nonblock := true, isSocket := false }
        { env with
          allMeta := env.allMeta.insert sid metaEntry
          openNonsocks := env.openNonsocks.push sid
          allOpen := env.allOpen.push sid }
      else env
    | none => env
  | .accept4 lsid fl =>
    match step.allocIds[0]?, out? with
    | some csid, some (_, .accepted _ _) =>
      let parentMeta := env.allMeta.getD lsid { domain := some .inet, sockType := .stream, nonblock := true, isSocket := true }
      let childMeta : SymMeta := { parentMeta with nonblock := fl.nonblock }
      { env with
        allMeta := env.allMeta.insert csid childMeta
        openSocks := env.openSocks.push csid
        allOpen := env.allOpen.push csid }
    | _, _ => env
  | .recvmsg _ _ =>
    match out? with
    | some (_, .fds hids) => Id.run do
      let mut e := env
      for i in [:hids.size] do
        if let some rsid := step.allocIds[i]? then
          if let some rhid := symMap.get? rsid then
            match lookupHandleFileId s rhid with
            | some fid =>
              match assocGet s.files fid with
              | some (.socket rd) =>
                let m : SymMeta :=
                  { domain := some rd.domain, sockType := rd.sockType, nonblock := rd.nonblock, isSocket := true }
                e := { e with
                  allMeta := e.allMeta.insert rsid m
                  openSocks := e.openSocks.push rsid
                  allOpen := e.allOpen.push rsid }
              | some .nonSocket =>
                let m : SymMeta := { domain := none, sockType := .stream, nonblock := true, isSocket := false }
                e := { e with
                  allMeta := e.allMeta.insert rsid m
                  openNonsocks := e.openNonsocks.push rsid
                  allOpen := e.allOpen.push rsid }
              | none => pure ()
            | none => pure ()
      return e
    | _ => env
  | .close sid =>
    { env with
      openSocks := env.openSocks.filter (· != sid)
      openNonsocks := env.openNonsocks.filter (· != sid)
      allOpen := env.allOpen.filter (· != sid)
      listeners := env.listeners.filter (fun p => p.1 != sid)
      boundTargets := env.boundTargets.filter (fun p => p.1 != sid)
      needGetsockname := env.needGetsockname.filter (· != sid)
      closedFds := if env.closedFds.contains sid then env.closedFds else env.closedFds.push sid
      knownLiveAddrs := liveAddrs }
  | .bind sid saddr =>
    match out? with
    | some (_, .unit) =>
      let dom := (env.allMeta.get? sid).bind (·.domain) |>.getD .inet
      let st := (env.allMeta.get? sid).map (·.sockType) |>.getD .stream
      let (uSeq, aSeq) := match saddr with
        | .unixRel _ => (env.unixSeq + 1, env.absSeq)
        | .fixed (.unix p) => if p.data[0]? == some 0 then (env.unixSeq, env.absSeq + 1) else (env.unixSeq, env.absSeq)
        | _ => (env.unixSeq, env.absSeq)
      let needGsn := if liveAddrs.contains sid then env.needGetsockname else env.needGetsockname.push sid
      { env with
        boundTargets := env.boundTargets.push (sid, dom, st)
        needGetsockname := needGsn
        unixSeq := uSeq
        absSeq := aSeq
        knownLiveAddrs := liveAddrs }
    | _ => env
  | .listen sid _ =>
    match out? with
    | some (_, .unit) =>
      let dom := (env.allMeta.get? sid).bind (·.domain) |>.getD .inet
      let st := (env.allMeta.get? sid).map (·.sockType) |>.getD .stream
      let needGsn := if liveAddrs.contains sid then env.needGetsockname else env.needGetsockname.push sid
      let nextListeners :=
        if env.listeners.any (·.1 == sid) then env.listeners
        else env.listeners.push (sid, dom, st)
      { env with
        listeners := nextListeners
        needGetsockname := needGsn
        knownLiveAddrs := liveAddrs }
    | _ => env
  | .getsockname sid =>
    { env with
      needGetsockname := env.needGetsockname.filter (· != sid)
      knownLiveAddrs := liveAddrs }
  | _ => env

/-- Bring `lo` up (`IFF_UP | IFF_LOOPBACK | IFF_RUNNING`) inside a newly created network namespace. -/
def bringLoopbackUp : IO Unit := do
  let ops := defaultOps
  match ← ops.socket .inet .dgram { nonblock := true, cloexec := true } 0 with
  | .error e => throw (IO.userError s!"bringLoopbackUp socket failed: {e}")
  | .ok fd =>
    try
      match ← ops.ioctl fd (.setIfFlags defaultLoFlags) loIfname with
      | .error e => throw (IO.userError s!"bringLoopbackUp ioctl(SIOCSIFFLAGS, lo) failed: {e}")
      | .ok _ => pure ()
    finally
      let _ ← rawNetClose fd

private def encodeHitLines (st : HitStats) : ByteArray :=
  let lines := st.counts.toList.map fun (k, v) => s!"{k}={v}"
  ("\n".intercalate lines).toUTF8

private def runUsernsLoParityProbe (baseDir : System.FilePath) : IO Unit := do
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let blk : SockFlags := { nonblock := false, cloexec := true }
  let tcpPairSetup : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     ]
  let trClosingShut : Array SymStep :=
    tcpPairSetup ++
    #[ { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 2 .wr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 2 .rdwr }
     ]
  let trTaintedV6LoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 12345 0 0)) }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0x20010db800000000 1 80 0 0)) }
     ]
  let trCloseWaitRstEpipe : Array SymStep :=
    tcpPairSetup ++
    #[ { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[247]) { dontwait := true } }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .close 1 }
     , { allocIds := #[], req := .sendto 2 largePayload65508 { dontwait := true } }
     , { allocIds := #[], req := .getsockopt 2 .error }
     ]
  let trSelfShutFlushRx : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .connect 0 (.tcpSelfConnect 0) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk #[75]) { dontwait := true } }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .recvfrom 0 0 { dontwait := true } }
     ]
  let trMappedDirBcastGsn : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .unix .dgram nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo 0x7fffffff) 0 0 0)) }
     , { allocIds := #[2], req := .socket .inet .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 2 (.fixed (.ipv4 INADDR_ANY 0)) }
     , { allocIds := #[], req := .getsockname 2 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 2) }
     , { allocIds := #[], req := .getsockname 1 }
     ]
  let trUdpAllHostsMcastLoopback : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 0x7f000002 0)) }
     , { allocIds := #[1], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv4 INADDR_ALLHOSTS_GROUP 0)) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 1 none) }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk #[1, 2, 3]) {} }
     , { allocIds := #[], req := .recvfrom 1 16 { dontwait := true } }
     , { allocIds := #[], req := .sendto 0 ByteArray.empty {} }
     , { allocIds := #[], req := .recvfrom 1 0 {} }
     ]
  let trV6SelfConnectLoDownShutSoError : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .getsockopt 0 .error }
     , { allocIds := #[], req := .getsockopt 0 .error }
     ]
  let trV6SelfConnectLoDownShutRdwrRxSoError : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk #[42, 43]) {} }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .getsockopt 0 .error }
     , { allocIds := #[], req := .getsockopt 0 .error }
     ]
  let nbNoClo : SockFlags := { nonblock := true, cloexec := false }
  let trPreShutCrossV6LoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nbNoClo 6 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .listen 0 0 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream nbNoClo 0 }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 2 .rd }
     ]
  let trPreShutV4LoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 2 .rd }
     , { allocIds := #[], req := .recvfrom 2 8 { dontwait := true } }
     ]
  let trPreShutV6NativeLoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .getsockopt 1 .error }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 2 .rd }
     ]
  let trPreShutV6MappedToV4LoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .shutdown 2 .rdwr }
     ]
  let trPreShutOrphanCloseLoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .close 2 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .shutdown 1 .rd }
     ]
  let trPreShutOrphanShutLoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .close 2 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .getsockopt 1 .error }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .rd }
     ]
  let trTaintedV6PreShutLisLoFlap : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 1 0 0)) }
     , { allocIds := #[], req := .shutdown 0 .rdwr }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .recvfrom 1 8 { dontwait := true } }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .shutdown 1 .wr }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .shutdown 1 .rd }
     , { allocIds := #[], req := .shutdown 2 .rd }
     ]
  let trV6SelfShutBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 74565 7)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags 8) loIfname }
     , { allocIds := #[], req := .bind 0 (.sameLocalOf 0 (some 2130706434)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .getsockopt 0 .error }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     ]
  let trV6SelfShutBindPort0LoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 0 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     ]
  let trV6RefusedSynSentBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 1 49999 0 0)) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 49999 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockopt 0 .error }
     ]
  let trV4SelfShutBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     ]
  let trV6MappedAndNativeLoNeverUp : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 41234 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .bind 1 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 41235 0 0)) }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 49999 0 0)) }
     , { allocIds := #[2], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .connect 2 (.fixed (.ipv6 0 1 49999 0 0)) }
     ]
  let trV6MappedSelfShutBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     ]
  let trV6MappedSelfShutBindPort0LoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     ]
  let trV6SelfShutBindMappedLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 41236 0 0)) }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     ]
  let trV6RefusedSynSentBindMappedLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 1 49999 0 0)) }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .connect 1 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 49999 0 0)) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) 49999 0 0)) }
     , { allocIds := #[], req := .getsockname 1 }
     ]
  let trV6PortLockedSelfShutBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 41234 0 0)) }
     , { allocIds := #[], req := .shutdown 0 .wr }
     , { allocIds := #[], req := .connect 0 (.fixed (.ipv6 0 1 41234 0 0)) }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 41234 0 0)) }
     ]
  let trV6ShutRdwrPeerRstBindLoDown : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[1], req := .socket .inet6 .stream nb 0 }
     , { allocIds := #[], req := .connect 1 (.sameLocalOf 0 none) }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .shutdown 1 .rdwr }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[104, 105]) {} }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags IFF_LOOPBACK) loIfname }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .bind 2 (.fixed (.ipv6 0 1 0 0 0)) }
     , { allocIds := #[], req := .bind 2 (.sameLocalOf 0 none) }
     , { allocIds := #[], req := .getsockname 2 }
     ]
  let trConnectResetPurgesRx : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[1], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .listen 0 0 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[206]) {} }
     , { allocIds := #[], req := .close 2 }
     , { allocIds := #[], req := .sendto 1 (ByteArray.mk #[170]) {} }
     , { allocIds := #[], req := .connect 1 (.tcpSelfConnect 1) }
     , { allocIds := #[], req := .recvfrom 1 0 {} }
     , { allocIds := #[], req := .recvfrom 1 1024 { dontwait := true } }
     , { allocIds := #[], req := .recvmsg 1 1 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[3], req := .accept4 0 nb }
     , { allocIds := #[], req := .recvfrom 1 16 { dontwait := true } }
     , { allocIds := #[], req := .sendto 3 (ByteArray.mk #[99]) {} }
     , { allocIds := #[], req := .recvfrom 1 16 { dontwait := true } }
     ]
  let trConnectResetSoErrorAndUnreadRst : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[206]) {} }
     , { allocIds := #[], req := .close 2 }
     , { allocIds := #[], req := .sendto 1 (ByteArray.mk #[170]) {} }
     , { allocIds := #[], req := .getsockopt 1 .error }
     , { allocIds := #[], req := .recvfrom 1 16 { dontwait := true, peek := true } }
     , { allocIds := #[], req := .connect 1 (.tcpSelfConnect 1) }
     , { allocIds := #[], req := .recvfrom 1 0 {} }
     , { allocIds := #[], req := .recvfrom 1 1024 { dontwait := true } }
     , { allocIds := #[3], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .connect 3 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .getsockname 3 }
     , { allocIds := #[4], req := .accept4 0 nb }
     , { allocIds := #[], req := .sendto 4 (ByteArray.mk #[206]) {} }
     , { allocIds := #[], req := .sendto 3 (ByteArray.mk #[170]) {} }
     , { allocIds := #[], req := .close 4 }
     , { allocIds := #[], req := .connect 3 (.tcpSelfConnect 3) }
     , { allocIds := #[], req := .recvfrom 3 0 {} }
     , { allocIds := #[], req := .recvfrom 3 16 { dontwait := true } }
     ]
  let trConnectResetNegControls : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .stream blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .listen 0 4 }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .stream blk 0 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[2], req := .accept4 0 nb }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[206]) {} }
     , { allocIds := #[], req := .close 2 }
     , { allocIds := #[], req := .sendto 1 (ByteArray.mk #[170]) {} }
     , { allocIds := #[], req := .connect 1 (.tcpSelfConnect 1) }
     , { allocIds := #[], req := .recvfrom 1 1024 { dontwait := true } }
     , { allocIds := #[3], req := .socket .inet .stream nb 0 }
     , { allocIds := #[], req := .connect 3 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .getsockname 3 }
     , { allocIds := #[4], req := .accept4 0 nb }
     , { allocIds := #[], req := .sendto 4 (ByteArray.mk #[206]) {} }
     , { allocIds := #[], req := .close 4 }
     , { allocIds := #[], req := .sendto 3 (ByteArray.mk #[170]) {} }
     , { allocIds := #[], req := .shutdown 3 .rd }
     , { allocIds := #[], req := .connect 3 (.tcpSelfConnect 3) }
     , { allocIds := #[], req := .recvfrom 3 1024 { dontwait := true } }
     ]
  let trUdpFreshNetnsZeroSaddr : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 0x7f000002 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[1], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[], req := .connect 0 (.sameLocalOf 1 (some INADDR_ANY)) }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk #[110]) {} }
     , { allocIds := #[], req := .recvfrom 1 8 { dontwait := true } }
     , { allocIds := #[], req := .sendto 0 ByteArray.empty {} }
     ]
  let trCrossFamV4m0UdpRefused : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet6 .dgram blk 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv6 0 0x0000ffff00000000 0 0 7)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv4 0x7f000002 0)) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .connect 0 (.crossFamilyTo 1) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[], req := .sendto 1 ByteArray.empty {} }
     , { allocIds := #[], req := .sendto 1 ByteArray.empty {} }
     , { allocIds := #[], req := .recvfrom 0 16 { dontwait := true } }
     , { allocIds := #[], req := .sendto 0 ByteArray.empty { dontwait := true } }
     , { allocIds := #[], req := .sendto 0 ByteArray.empty { dontwait := true } }
     , { allocIds := #[], req := .connect 1 (.crossFamilyTo 0) }
     , { allocIds := #[], req := .sendto 1 (ByteArray.mk #[65]) {} }
     , { allocIds := #[], req := .recvfrom 0 16 { dontwait := true } }
     , { allocIds := #[], req := .sendto 0 (ByteArray.mk #[66]) { dontwait := true } }
     , { allocIds := #[], req := .recvfrom 1 16 { dontwait := true } }
     ]
  let trUdpWildcardSourceRouteVariants : Array SymStep :=
    #[ { allocIds := #[0], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .ioctl 0 (.setIfFlags defaultLoFlags) loIfname }
     , { allocIds := #[], req := .bind 0 (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
     , { allocIds := #[], req := .getsockname 0 }
     , { allocIds := #[1], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 1 (.fixed (.ipv4 0x7f000002 0)) }
     , { allocIds := #[], req := .getsockname 1 }
     , { allocIds := #[2], req := .socket .inet .dgram nb 0 }
     , { allocIds := #[], req := .bind 2 (.fixed (.ipv4 0x7f000002 0)) }
     , { allocIds := #[], req := .getsockname 2 }
     , { allocIds := #[], req := .connect 2 (.sameLocalOf 1 (some INADDR_ANY)) }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[98]) {} }
     , { allocIds := #[], req := .recvfrom 1 8 { dontwait := true } }
     , { allocIds := #[], req := .connect 2 (.sameLocalOf 0 (some INADDR_ANY)) }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[99]) {} }
     , { allocIds := #[], req := .sendto 2 (ByteArray.mk #[99]) {} }
     , { allocIds := #[], req := .recvfrom 0 8 { dontwait := true } }
     , { allocIds := #[3], req := .socket .inet6 .dgram nb 0 }
     , { allocIds := #[], req := .bind 3 (.fixed (.ipv6 0 0x0000ffff00000000 0 0 0)) }
     , { allocIds := #[], req := .getsockname 3 }
     , { allocIds := #[4], req := .socket .inet6 .dgram nb 0 }
     , { allocIds := #[], req := .bind 4 (.fixed (.ipv6 0 (ipv4ToMappedV6Lo 0x7f000002) 0 0 0)) }
     , { allocIds := #[], req := .getsockname 4 }
     , { allocIds := #[], req := .connect 4 (.sameLocalOf 3 none) }
     , { allocIds := #[], req := .connect 3 (.sameLocalOf 4 none) }
     , { allocIds := #[], req := .getsockname 3 }
     , { allocIds := #[], req := .sendto 4 ByteArray.empty {} }
     , { allocIds := #[], req := .sendto 4 ByteArray.empty {} }
     , { allocIds := #[], req := .connect 4 (.sameLocalOf 3 none) }
     , { allocIds := #[], req := .sendto 4 (ByteArray.mk #[100]) {} }
     , { allocIds := #[], req := .recvfrom 3 8 { dontwait := true } }
     ]
  let (rc, payload) ← SandboxEnv.runForked do
    match ← SandboxEnv.unshareExtra 2 with
    | .error e => return s!"UNSHARE_ERR:{e}".toUTF8
    | .ok () => pure ()
    let traces := #[trV6MappedAndNativeLoNeverUp, trUdpFreshNetnsZeroSaddr, trClosingShut, trTaintedV6LoDown, trCloseWaitRstEpipe, trSelfShutFlushRx, trMappedDirBcastGsn, trUdpAllHostsMcastLoopback, trV6SelfConnectLoDownShutSoError, trV6SelfConnectLoDownShutRdwrRxSoError, trPreShutCrossV6LoFlap, trPreShutV4LoFlap, trPreShutV6NativeLoFlap, trPreShutV6MappedToV4LoFlap, trPreShutOrphanCloseLoFlap, trPreShutOrphanShutLoFlap, trTaintedV6PreShutLisLoFlap, trV6SelfShutBindLoDown, trV6SelfShutBindPort0LoDown, trV6RefusedSynSentBindLoDown, trV4SelfShutBindLoDown, trV6MappedSelfShutBindLoDown, trV6MappedSelfShutBindPort0LoDown, trV6SelfShutBindMappedLoDown, trV6RefusedSynSentBindMappedLoDown, trV6PortLockedSelfShutBindLoDown, trV6ShutRdwrPeerRstBindLoDown, trConnectResetPurgesRx, trConnectResetSoErrorAndUnreadRst, trConnectResetNegControls, trCrossFamV4m0UdpRefused, trUdpWildcardSourceRouteVariants]
    for h : idx in [:traces.size] do
      let pDir := baseDir / s!"parity-{idx}"
      let r ← replayTrace pDir traces[idx] true allowedStep true false
      if let some mm := r.mismatchMsg then
        return s!"TRACE_{idx}:{mm}".toUTF8
      match ← defaultOps.socket .inet .dgram nb 0 with
      | .ok tmp =>
        let _ ← defaultOps.ioctl tmp (.setIfFlags IFF_LOOPBACK) loIfname
        let _ ← rawNetClose tmp
      | .error _ => pure ()
    let ops := defaultOps
    let mut st := NetState.initialNetns
    let mut openFds : Array RawFd := #[]
    let must (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
      match allowedStep s req out with
      | some s' => return s'
      | none => throw (IO.userError s!"RTO_ORPHAN_{lbl}: req={repr req} out={repr out}")
    try
      let lfd ← match ← ops.socket .inet .stream nb 0 with
        | .ok fd => openFds := openFds.push fd; pure fd
        | .error e => return s!"RTO_SOCK:{e}".toUTF8
      let lH := st.nextHid
      st ← must "l_sock" st (.socket .inet .stream nb 0) (.opened lH)
      match ← ops.ioctl lfd (.setIfFlags defaultLoFlags) loIfname with
      | .ok v => st ← must "lo_up1" st (.ioctl lH (.setIfFlags defaultLoFlags) loIfname) (.u32 v)
      | .error e => return s!"RTO_UP1:{e}".toUTF8
      match ← ops.bind lfd (.ipv4 INADDR_LOOPBACK 0) with
      | .ok () => st ← must "bind" st (.bind lH (.ipv4 INADDR_LOOPBACK 0)) .unit
      | .error e => return s!"RTO_BIND:{e}".toUTF8
      match ← ops.listen lfd 4 with
      | .ok () => st ← must "listen" st (.listen lH 4) .unit
      | .error e => return s!"RTO_LISTEN:{e}".toUTF8
      let laddr ← match ← ops.getsockname lfd with
        | .ok sa => st ← must "gsn" st (.getsockname lH) (.addr sa); pure sa
        | .error e => return s!"RTO_GSN:{e}".toUTF8
      let cfd ← match ← ops.socket .inet .stream nb 0 with
        | .ok fd => pure fd
        | .error e => return s!"RTO_CSOCK:{e}".toUTF8
      let cH := st.nextHid
      st ← must "c_sock" st (.socket .inet .stream nb 0) (.opened cH)
      match ← ops.connect cfd laddr with
      | .ok () => st ← must "conn" st (.connect cH laddr) .unit
      | .error e => st ← must "conn_e" st (.connect cH laddr) (.err e)
      let (sfd, psa) ← match ← ops.accept4 lfd nb with
        | .ok (fd, a) => openFds := openFds.push fd; pure (fd, a)
        | .error e => let _ ← rawNetClose cfd; return s!"RTO_ACC:{e}".toUTF8
      let sH := st.nextHid
      st ← must "acc" st (.accept4 lH nb) (.accepted sH psa)
      match ← ops.ioctl lfd (.setIfFlags IFF_LOOPBACK) loIfname with
      | .ok v => st ← must "lo_down" st (.ioctl lH (.setIfFlags IFF_LOOPBACK) loIfname) (.u32 v)
      | .error e => let _ ← rawNetClose cfd; return s!"RTO_DOWN:{e}".toUTF8
      let _ ← rawNetClose cfd
      st ← match st.closeHandle cH with
        | .ok s' => pure s'
        | .error e => return s!"RTO_CLOSE:{e}".toUTF8
      let payload4097 := ByteArray.mk (Array.replicate 4097 65)
      match ← ops.sendto sfd payload4097 { dontwait := true } with
      | .ok n => st ← must "tx4097" st (.sendto sH payload4097 { dontwait := true }) (.u32 n)
      | .error e => st ← must "tx4097_e" st (.sendto sH payload4097 { dontwait := true }) (.err e)
      match ← ops.shutdown sfd .rdwr with
      | .ok () => st ← must "shut" st (.shutdown sH .rdwr) .unit
      | .error e => st ← must "shut_e" st (.shutdown sH .rdwr) (.err e)
      match ← ops.ioctl lfd (.setIfFlags defaultLoFlags) loIfname with
      | .ok v => st ← must "lo_up2" st (.ioctl lH (.setIfFlags defaultLoFlags) loIfname) (.u32 v)
      | .error e => return s!"RTO_UP2:{e}".toUTF8
      IO.sleep 260
      let postOut ← match ← ops.sendto sfd ByteArray.empty { dontwait := true } with
        | .ok n => pure (.u32 n)
        | .error e => pure (.err e)
      let _ ← must "post_rto_send" st (.sendto sH ByteArray.empty { dontwait := true }) postOut
      return "OK".toUTF8
    finally
      for fd in openFds do
        let _ ← rawNetClose fd
  let txt := String.fromUTF8! payload
  if rc != 0 || txt != "OK" then
    throw (IO.userError s!"userns lo parity probe failed (rc={rc}): {txt}")

/-- Run a dedicated `CLONE_NEWUSER | CLONE_NEWNET` `lo`-down -> `ENETUNREACH` -> `SIOCSIFFLAGS IFF_UP` -> loopback check and multi-episode fuzz steps inside an already-entered user+net namespace. -/
def runUsernsLoDownProbe (steps : Nat) (seed : UInt64) : IO Unit := do
  let ops := defaultOps
  let origNofile ← match ← rawRlimitNofile 0 0 with
    | .ok v => pure v
    | .error _ => pure 1024
  let loInitiallyDown ← match ← ops.socket .inet .dgram { nonblock := true, cloexec := true } 0 with
    | .ok probeFd =>
      let res ← ops.ioctl probeFd .getIfFlags loIfname
      let _ ← rawNetClose probeFd
      match res with
      | .ok fl => pure ((fl &&& IFF_UP) == 0)
      | .error _ => pure false
    | .error _ => pure false
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let nanos ← IO.monoNanosNow
  let baseDir : System.FilePath := s!"/dev/shm/leanswe-net-userns-{nanos}"
  IO.FS.createDirAll baseDir
  let execAndRecord := fun (epStartLoDown epWasEverUp : Bool) (step : SymStep)
      (ep : System.FilePath) (cn : UInt64)
      (sm : Std.HashMap SymFd HandleId) (rm om : Std.HashMap HandleId RawFd)
      (la : Std.HashMap SymFd SockAddr) (ms : NetState) (ev : GenEnv)
      (st : HitStats) (tr : Array SymStep) => do
    match ← execOneStep ops ep origNofile cn sm rm om la ms step with
    | .error msg =>
      let _ ← rawRlimitNofile 1 origNofile
      closeOpenFds om
      let shrinkDir := baseDir / "shrink"
      let wantPrefix := ((msg.splitOn ":").headD msg).trimAscii.toString
      let wantOut? := extractNetOut? msg
      let runFastInprocReplay := fun (cand : Array SymStep) => do
        let r ← replayTrace shrinkDir cand loInitiallyDown allowedStep epStartLoDown (epWasEverUp || !epStartLoDown)
        match r.mismatchMsg with
        | some mm =>
          if matchesNetMismatch wantPrefix wantOut? mm then return some mm else return none
        | none => return none
      let runForkedNetnsReplay := fun (cand : Array SymStep) => do
        let (_, payload) ← SandboxEnv.runForked do
          if loInitiallyDown then
            match ← SandboxEnv.unshareExtra 2 with
            | .error e => return s!"UNSHARE_ERR:{e}".toUTF8
            | .ok () => pure ()
          let r ← replayTrace shrinkDir cand loInitiallyDown allowedStep epStartLoDown epWasEverUp
          match r.mismatchMsg with
          | some mm => return s!"MISMATCH:{mm}".toUTF8
          | none => return ByteArray.empty
        let txt := String.fromUTF8! payload
        if txt.startsWith "MISMATCH:" then
          let mm := (txt.drop 9).toString
          if matchesNetMismatch wantPrefix wantOut? mm then
            return some mm
          else return none
        else return none
      let canShrinkInproc ← (·.isSome) <$> runFastInprocReplay tr
      let runIsolatedReplay := if canShrinkInproc then runFastInprocReplay else runForkedNetnsReplay
      let shrunk ← shrinkTrace tr fun cand => do
        return (← runIsolatedReplay cand).isSome
      let shrunkMsg := (← runIsolatedReplay shrunk).getD "(none)"
      throw (IO.userError s!"userns mismatch at step={tr.size}: {msg}\nshrunk_msg={shrunkMsg}\nminimal trace ({shrunk.size} steps): {repr shrunk}")
    | .ok (sm', rm', om', la', cn', ms', out?) =>
      let ev' := updateEnvAfterStep ev step sm' la' ms' out?
      let st' := match out? with
        | some (sname, out) => st.record sname out
        | none => st
      return (sm', rm', om', la', cn', ms', ev', st', out?.isSome)
  try
    if loInitiallyDown then
      runUsernsLoParityProbe baseDir
    let mut rng := Rng.seed seed
    let mut stats : HitStats := {}
    let mut done := 0
    let mut epIdx := 0
    let mut hostLoEverUp := !loInitiallyDown
    while done < steps do
      let epTarget := min (steps - done) 120
      let epDir := baseDir / s!"ep-{epIdx}"
      if ← epDir.pathExists then
        IO.FS.removeDirAll epDir
      IO.FS.createDirAll epDir
      let epStartLoDown :=
        if !loInitiallyDown then false
        else if epIdx == 0 then true
        else epIdx % 2 == 0
      let epWasEverUp := hostLoEverUp
      if loInitiallyDown && epIdx > 0 then
        match ← ops.socket .inet .dgram nb 0 with
        | .ok ctlFd =>
          let fl := if epStartLoDown then IFF_LOOPBACK else defaultLoFlags
          let _ ← ops.ioctl ctlFd (.setIfFlags fl) loIfname
          if !epStartLoDown then hostLoEverUp := true
          let _ ← rawNetClose ctlFd
        | .error _ => pure ()
      let mut curNofile := origNofile
      let mut modelState :=
        if epStartLoDown then
          if epWasEverUp then { NetState.initial loInitiallyDown with loState := .down IFF_LOOPBACK true }
          else NetState.initialNetns
        else NetState.initial loInitiallyDown
      let mut symMap : Std.HashMap SymFd HandleId := {}
      let mut rawMap : Std.HashMap HandleId RawFd := {}
      let mut openMap : Std.HashMap HandleId RawFd := {}
      let mut liveAddrs : Std.HashMap SymFd SockAddr := {}
      let mut env : GenEnv := { absTag := s!"u-{nanos % 1000000}-{epIdx}" }
      let mut nextSym : SymFd := 0
      let mut uTrace : Array SymStep := #[]
      try
        if loInitiallyDown && epIdx == 0 then
          let loDownScript : Array SymReq :=
            #[ .socket .inet .stream nb 0
             , .ioctl 0 .getIfFlags loIfname
             , .ioctl 0 (.setIfFlags 0x8008) loIfname
             , .ioctl 0 .getIfFlags loIfname
             , .connect 0 (.fixed (.ipv4 INADDR_LOOPBACK 12345))
             ]
          for sreq in loDownScript do
            let nAlloc := allocSlotsForReq sreq
            let mut allocIds : Array SymFd := #[]
            for _ in [:nAlloc] do
              allocIds := allocIds.push nextSym
              nextSym := nextSym + 1
            let step : SymStep := { allocIds, req := sreq }
            uTrace := uTrace.push step
            let (sm', rm', om', la', cn', ms', ev', st', _) ←
              execAndRecord epStartLoDown epWasEverUp step epDir curNofile symMap rawMap openMap liveAddrs modelState env stats uTrace
            symMap := sm'; rawMap := rm'; openMap := om'; liveAddrs := la'
            curNofile := cn'; modelState := ms'; env := ev'; stats := st'
        let mut epDone := 0
        let togglePoint1 := max 1 (epTarget / 3)
        let togglePoint2 := max 2 ((epTarget * 2) / 3)
        let mut didToggle1 := false
        let mut didToggle2 := false
        while epDone < epTarget && done < steps do
          if loInitiallyDown && !didToggle1 && epDone >= togglePoint1 then
            didToggle1 := true
            let sCtl := nextSym
            nextSym := nextSym + 1
            let targetFl := if epStartLoDown then defaultLoFlags else IFF_LOOPBACK
            let ctlSteps : Array SymStep ←
              if epIdx == 0 then do
                let sB := nextSym
                nextSym := nextSym + 1
                pure #[ { allocIds := #[sCtl], req := .socket .inet .stream nb 0 }
                      , { allocIds := #[], req := .ioctl sCtl (.setIfFlags defaultLoFlags) loIfname }
                      , { allocIds := #[sB], req := .socket .inet .stream nb 0 }
                      , { allocIds := #[], req := .bind sB (.fixed (.ipv4 INADDR_LOOPBACK 0)) }
                      , { allocIds := #[], req := .listen sB 8 }
                      , { allocIds := #[], req := .getsockname sB }
                      , { allocIds := #[], req := .connect sCtl (.sameLocalOf sB none) }
                      ]
              else
                pure #[ { allocIds := #[sCtl], req := .socket .inet .dgram nb 0 }
                      , { allocIds := #[], req := .ioctl sCtl (.setIfFlags targetFl) loIfname }
                      , { allocIds := #[], req := .close sCtl }
                      ]
            for cStep in ctlSteps do
              uTrace := uTrace.push cStep
              let (sm', rm', om', la', cn', ms', ev', st', _) ←
                execAndRecord epStartLoDown epWasEverUp cStep epDir curNofile symMap rawMap openMap liveAddrs modelState env stats uTrace
              symMap := sm'; rawMap := rm'; openMap := om'; liveAddrs := la'
              curNofile := cn'; modelState := ms'; env := ev'; stats := st'
              if (match ms'.loState with | .up _ => true | .down _ true => true | _ => false) then
                hostLoEverUp := true
          if loInitiallyDown && !epStartLoDown && !didToggle2 && epDone >= togglePoint2 then
            didToggle2 := true
            let sCtl := nextSym
            nextSym := nextSym + 1
            for cStep in #[
              ({ allocIds := #[sCtl], req := .socket .inet .dgram nb 0 } : SymStep),
              { allocIds := #[], req := .ioctl sCtl (.setIfFlags defaultLoFlags) loIfname },
              { allocIds := #[], req := .close sCtl }
            ] do
              uTrace := uTrace.push cStep
              let (sm', rm', om', la', cn', ms', ev', st', _) ←
                execAndRecord epStartLoDown epWasEverUp cStep epDir curNofile symMap rawMap openMap liveAddrs modelState env stats uTrace
              symMap := sm'; rawMap := rm'; openMap := om'; liveAddrs := la'
              curNofile := cn'; modelState := ms'; env := ev'; stats := st'
              hostLoEverUp := true
          let (sreq, armAlrm, rNext) := genSymReq rng env modelState symMap epDir origNofile curNofile
          rng := rNext
          let nAlloc := allocSlotsForReq sreq
          let mut allocIds : Array SymFd := #[]
          for _ in [:nAlloc] do
            allocIds := allocIds.push nextSym
            nextSym := nextSym + 1
          let step : SymStep := { allocIds, req := sreq, armAlrm }
          uTrace := uTrace.push step
          let (sm', rm', om', la', cn', ms', ev', st', counted) ←
            execAndRecord epStartLoDown epWasEverUp step epDir curNofile symMap rawMap openMap liveAddrs modelState env stats uTrace
          symMap := sm'; rawMap := rm'; openMap := om'; liveAddrs := la'
          curNofile := cn'; modelState := ms'; env := ev'; stats := st'
          if (match ms'.loState with | .up _ => true | .down _ true => true | _ => false) then
            hostLoEverUp := true
          if counted then
            epDone := epDone + 1
            done := done + 1
      finally
        let _ ← rawRlimitNofile 1 origNofile
        closeOpenFds openMap
        if ← epDir.pathExists then
          IO.FS.removeDirAll epDir
      epIdx := epIdx + 1
    for (k, v) in stats.counts.toList do
      IO.println s!"USERNS_HITS {k}={v}"
  finally
    let _ ← rawRlimitNofile 1 origNofile
    if ← baseDir.pathExists then
      IO.FS.removeDirAll baseDir

/-- Verify `SIGALRM` without `SA_RESTART` interrupts blocking `accept4`, `recvfrom`, `recvmsg`, and `connect` matching `allowedStep`. -/
def runSigalrmEintrProbe : IO Unit := do
  let ops := defaultOps
  let blk : SockFlags := { nonblock := false, cloexec := true }
  let mut st := NetState.initial false
  let mut openFds : Array RawFd := #[]
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"net sigalrm model rejected {lbl}: req={repr req} out={repr out}")
  try
    let lisFd ← match ← ops.socket .inet .stream blk 0 with
      | .ok fd => openFds := openFds.push fd; pure fd
      | .error e => throw (IO.userError s!"net sigalrm lis socket failed: {e}")
    let lHid := st.nextHid
    st ← mustStep "lis socket" st (.socket .inet .stream blk 0) (.opened lHid)
    match ← ops.bind lisFd (.ipv4 INADDR_LOOPBACK 0) with
    | .error e => throw (IO.userError s!"net sigalrm bind failed: {e}")
    | .ok () => st ← mustStep "lis bind" st (.bind lHid (.ipv4 INADDR_LOOPBACK 0)) .unit
    match ← ops.listen lisFd 4 with
    | .error e => throw (IO.userError s!"net sigalrm listen failed: {e}")
    | .ok () => st ← mustStep "lis listen" st (.listen lHid 4) .unit
    rawArmSigalrm 5000 0
    let accRes ← ops.accept4 lisFd { nonblock := true, cloexec := true }
    rawDisarmSigalrm 0
    match accRes with
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"net sigalrm accept4 expected EINTR, got {e}")
      st ← mustStep "accept4 eintr" st (.accept4 lHid { nonblock := true, cloexec := true }) (.err e)
    | .ok (cfd, _) =>
      let _ ← rawNetClose cfd
      throw (IO.userError "net sigalrm accept4 unexpectedly succeeded")
    let (sp0, sp1) ← match ← ops.socketpair .unix .stream blk with
      | .ok (a, b) => openFds := (openFds.push a).push b; pure (a, b)
      | .error e => throw (IO.userError s!"net sigalrm socketpair failed: {e}")
    let pHid0 := st.nextHid
    st ← mustStep "socketpair" st (.socketpair .unix .stream blk) (.pair pHid0 (pHid0 + 1))
    let _ := sp1
    rawArmSigalrm 5000 0
    let rxRes ← ops.recvfrom sp0 16 {}
    rawDisarmSigalrm 0
    match rxRes with
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"net sigalrm recvfrom expected EINTR, got {e}")
      st ← mustStep "recvfrom eintr" st (.recvfrom pHid0 16 {}) (.err e)
    | .ok _ => throw (IO.userError "net sigalrm recvfrom unexpectedly succeeded")
    rawArmSigalrm 5000 0
    let rmsgRes ← ops.recvmsg sp0 2
    rawDisarmSigalrm 0
    match rmsgRes with
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"net sigalrm recvmsg expected EINTR, got {e}")
      st ← mustStep "recvmsg eintr" st (.recvmsg pHid0 2) (.err e)
    | .ok got =>
      for fd in got do let _ ← rawNetClose fd
      throw (IO.userError "net sigalrm recvmsg unexpectedly succeeded")
    let connFd ← match ← ops.socket .inet .stream blk 0 with
      | .ok fd => openFds := openFds.push fd; pure fd
      | .error e => throw (IO.userError s!"net sigalrm conn socket failed: {e}")
    let cHid := st.nextHid
    st ← mustStep "conn socket" st (.socket .inet .stream blk 0) (.opened cHid)
    rawArmSigalrm 5000 0
    let connRes ← ops.connect connFd (.ipv4 0xc0000201 80)
    rawDisarmSigalrm 0
    match connRes with
    | .error e =>
      if e != Errno.EINTR && e != Errno.ENETUNREACH then
        throw (IO.userError s!"net sigalrm connect expected EINTR or ENETUNREACH, got {e}")
      if (allowedStep st (.connect cHid (.ipv4 0xc0000201 80)) (.err e)).isNone then
        throw (IO.userError s!"net sigalrm model rejected connect err {e}")
    | .ok () => pure ()
  finally
    rawDisarmSigalrm 0
    for fd in openFds do
      let _ ← rawNetClose fd

private def runSigpipeNosignalProbe : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rc, payload) ← SandboxEnv.runForked do
    rawResetSigpipeDfl
    let mut st := NetState.initial false
    let (tx, rx) ← match ← ops.socketpair .unix .stream nb with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"net sigpipe probe socketpair failed: {e}")
    let txH := st.nextHid
    let rxH := txH + 1
    st ← match allowedStep st (.socketpair .unix .stream nb) (.pair txH rxH) with
      | some s' => pure s'
      | none =>
        let _ ← rawNetClose tx
        let _ ← rawNetClose rx
        throw (IO.userError "net sigpipe probe model rejected socketpair")
    let _ ← rawNetClose rx
    st ← match st.closeHandle rxH with
      | .ok s' => pure s'
      | .error e =>
        let _ ← rawNetClose tx
        throw (IO.userError s!"net sigpipe probe closeHandle failed: {e}")
    let sres ← ops.sendto tx (ByteArray.mk #[1]) { nosignal := true, dontwait := true }
    match sres with
    | .error e =>
      if e != Errno.EPIPE then
        let _ ← rawNetClose tx
        throw (IO.userError s!"net sigpipe probe sendto expected EPIPE, got {e}")
      if (allowedStep st (.sendto txH (ByteArray.mk #[1]) { nosignal := true, dontwait := true }) (.err e)).isNone then
        let _ ← rawNetClose tx
        throw (IO.userError s!"net sigpipe probe model rejected sendto err={e}")
    | .ok n =>
      let _ ← rawNetClose tx
      throw (IO.userError s!"net sigpipe probe sendto unexpectedly succeeded: {n}")
    let mres ← ops.sendmsg tx #[tx]
    match mres with
    | .error e =>
      if e != Errno.EPIPE then
        let _ ← rawNetClose tx
        throw (IO.userError s!"net sigpipe probe sendmsg expected EPIPE, got {e}")
      if (allowedStep st (.sendmsg txH #[txH]) (.err e)).isNone then
        let _ ← rawNetClose tx
        throw (IO.userError s!"net sigpipe probe model rejected sendmsg err={e}")
    | .ok () =>
      let _ ← rawNetClose tx
      throw (IO.userError "net sigpipe probe sendmsg unexpectedly succeeded")
    let _ ← rawNetClose tx
    return "OK".toUTF8
  if rc != 0 || String.fromUTF8! payload != "OK" then
    throw (IO.userError s!"net sigpipe MSG_NOSIGNAL probe failed (wait_status={rc}, msg={String.fromUTF8! payload})")

private def runListenBacklogProbe (rootDir : System.FilePath) : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let sockPath := rootDir / "bl-probe.sock"
  if ← sockPath.pathExists then
    IO.FS.removeFile sockPath
  let addr : SockAddr := .unix sockPath.toString.toUTF8
  let mut st := NetState.initial false
  let mut openFds : Array RawFd := #[]
  let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
    match allowedStep s req out with
    | some s' => return s'
    | none => throw (IO.userError s!"net listen backlog model rejected {lbl}: req={repr req} out={repr out}")
  try
    let lisFd ← match ← ops.socket .unix .stream nb 0 with
      | .ok fd => openFds := openFds.push fd; pure fd
      | .error e => throw (IO.userError s!"net listen backlog socket failed: {e}")
    let lH := st.nextHid
    st ← mustStep "lis socket" st (.socket .unix .stream nb 0) (.opened lH)
    match ← ops.bind lisFd addr with
    | .ok () => st ← mustStep "lis bind" st (.bind lH addr) .unit
    | .error e => throw (IO.userError s!"net listen backlog bind failed: {e}")
    match ← ops.listen lisFd 2 with
    | .ok () => st ← mustStep "lis listen" st (.listen lH 2) .unit
    | .error e => throw (IO.userError s!"net listen backlog listen(2) failed: {e}")
    for i in [:3] do
      let cliFd ← match ← ops.socket .unix .stream nb 0 with
        | .ok fd => openFds := openFds.push fd; pure fd
        | .error e => throw (IO.userError s!"net listen backlog cli{i} socket failed: {e}")
      let cH := st.nextHid
      st ← mustStep s!"cli{i} socket" st (.socket .unix .stream nb 0) (.opened cH)
      match ← ops.connect cliFd addr with
      | .ok () => st ← mustStep s!"cli{i} connect" st (.connect cH addr) .unit
      | .error e => throw (IO.userError s!"net listen backlog cli{i} connect expected ok under backlog=2, got {e}")
    let extraFd ← match ← ops.socket .unix .stream nb 0 with
      | .ok fd => openFds := openFds.push fd; pure fd
      | .error e => throw (IO.userError s!"net listen backlog extra cli socket failed: {e}")
    let eH := st.nextHid
    st ← mustStep "extra cli socket" st (.socket .unix .stream nb 0) (.opened eH)
    match ← ops.connect extraFd addr with
    | .error e =>
      if e != Errno.EAGAIN then
        throw (IO.userError s!"net listen backlog overflow expected EAGAIN, got {e}")
      st ← mustStep "extra cli overflow" st (.connect eH addr) (.err e)
    | .ok () => throw (IO.userError "net listen backlog=2 unexpectedly accepted 4th queued connect without EAGAIN")
    for i in [:3] do
      match ← ops.accept4 lisFd nb with
      | .ok (afd, peer) =>
        openFds := openFds.push afd
        let aH := st.nextHid
        st ← mustStep s!"accept{i}" st (.accept4 lH nb) (.accepted aH peer)
      | .error e => throw (IO.userError s!"net listen backlog accept{i} failed: {e}")
    match ← ops.accept4 lisFd nb with
    | .error e =>
      if e != Errno.EAGAIN then
        throw (IO.userError s!"net listen backlog empty accept expected EAGAIN, got {e}")
      let _ ← mustStep "empty accept" st (.accept4 lH nb) (.err e)
    | .ok (afd, _) =>
      openFds := openFds.push afd
      throw (IO.userError "net listen backlog unexpected 4th accepted connection")
  finally
    for fd in openFds do
      let _ ← rawNetClose fd
    if ← sockPath.pathExists then
      IO.FS.removeFile sockPath

private def netSeccompX86Nrs : Array UInt32 :=
  #[41, 53, 49, 50, 288, 42, 55, 54, 51, 45, 44, 48, 46, 47, 16]

private def netSeccompArmNrs : Array UInt32 :=
  #[198, 199, 200, 201, 242, 203, 209, 208, 204, 207, 206, 210, 211, 212, 29]

private def runSeccompChild (expected : Errno) : IO ByteArray := do
  let ops := defaultOps
  let mut st := NetState.initial (ambientSeccomp := true)
  let fl : SockFlags := { nonblock := true, cloexec := true }
  let mut openFds : Array RawFd := #[]
  let mut hits : HitStats := {}
  try
    let liveFd ← match ← ops.socket .inet .stream fl 0 with
      | .ok fd => openFds := openFds.push fd; pure fd
      | .error e => throw (IO.userError s!"net seccomp prep socket failed: {e}")
    let liveHid := st.nextHid
    match allowedStep st (.socket .inet .stream fl 0) (.opened liveHid) with
    | some st' => st := st'
    | none => throw (IO.userError "net seccomp prep model rejected socket")
    let (u0, u1) ← match ← ops.socketpair .unix .stream fl with
      | .ok (a, b) => openFds := (openFds.push a).push b; pure (a, b)
      | .error e => throw (IO.userError s!"net seccomp prep socketpair failed: {e}")
    let u0Hid := st.nextHid
    let _ := u1
    match allowedStep st (.socketpair .unix .stream fl) (.pair u0Hid (u0Hid + 1)) with
    | some st' => st := st'
    | none => throw (IO.userError "net seccomp prep model rejected socketpair")
    let closedFd ← match ← ops.socket .inet .stream fl 0 with
      | .ok fd => pure fd
      | .error e => throw (IO.userError s!"net seccomp prep closed socket failed: {e}")
    let closedHid := st.nextHid
    match allowedStep st (.socket .inet .stream fl 0) (.opened closedHid) with
    | some st' => st := st'
    | none => throw (IO.userError "net seccomp prep model rejected closed socket")
    let _ ← rawNetClose closedFd
    match st.closeHandle closedHid with
    | .ok st' => st := st'
    | .error e => throw (IO.userError s!"net seccomp prep closeHandle failed: {e}")
    let sops := LeanSwe.LinuxSyscall.Sandbox.defaultOps
    match ← sops.prctl .setNoNewPrivs with
    | .error e => throw (IO.userError s!"net seccomp prctl(PR_SET_NO_NEW_PRIVS) failed: {e}")
    | .ok _ => pure ()
    let bpf := SandboxEnv.encodeSeccompErrnoBpf netSeccompX86Nrs netSeccompArmNrs expected
    match ← SandboxEnv.installRawSeccomp bpf with
    | .error e => throw (IO.userError s!"net seccomp installRawSeccomp failed: {e}")
    | .ok () => pure ()
    let stRef ← IO.mkRef st
    let hitsRef ← IO.mkRef hits
    let checkErr {α : Type} (sname : String) (req : NetReq) (wantErr : Errno) (act : IO (Except Errno α)) : IO Unit := do
      match ← act with
      | .error e =>
        if e != wantErr then
          throw (IO.userError s!"net seccomp {sname} expected {wantErr}, got {e}")
        let curSt ← stRef.get
        match allowedStep curSt req (.err e) with
        | some st' =>
          stRef.set st'
          hitsRef.modify (fun h => h.record sname (.err e))
        | none => throw (IO.userError s!"net seccomp model rejected {sname} err={e}")
      | .ok _ =>
        throw (IO.userError s!"net seccomp {sname} unexpectedly succeeded")
    checkErr "socket" (.socket .inet .stream fl 0) expected (ops.socket .inet .stream fl 0)
    checkErr "socketpair" (.socketpair .unix .stream fl) expected (ops.socketpair .unix .stream fl)
    checkErr "bind" (.bind liveHid (.ipv4 INADDR_LOOPBACK 0)) expected (ops.bind liveFd (.ipv4 INADDR_LOOPBACK 0))
    checkErr "listen" (.listen liveHid 4) expected (ops.listen liveFd 4)
    checkErr "accept4" (.accept4 liveHid fl) expected (ops.accept4 liveFd fl)
    checkErr "connect" (.connect liveHid (.ipv4 INADDR_LOOPBACK 1)) expected (ops.connect liveFd (.ipv4 INADDR_LOOPBACK 1))
    checkErr "getsockopt" (.getsockopt liveHid .reuseAddr) expected (ops.getsockopt liveFd .reuseAddr)
    checkErr "setsockopt" (.setsockopt liveHid .reuseAddr 1) expected (ops.setsockopt liveFd .reuseAddr 1)
    checkErr "getsockname" (.getsockname liveHid) expected (ops.getsockname liveFd)
    checkErr "recvfrom" (.recvfrom liveHid 16 { dontwait := true }) expected (ops.recvfrom liveFd 16 { dontwait := true })
    checkErr "sendto" (.sendto liveHid (ByteArray.mk #[1]) { dontwait := true }) expected (ops.sendto liveFd (ByteArray.mk #[1]) { dontwait := true })
    checkErr "shutdown" (.shutdown liveHid .rd) expected (ops.shutdown liveFd .rd)
    checkErr "sendmsg" (.sendmsg u0Hid #[liveHid]) expected (ops.sendmsg u0 #[liveFd])
    checkErr "recvmsg" (.recvmsg u0Hid 1) expected (ops.recvmsg u0 1)
    checkErr "ioctl" (.ioctl liveHid .getIfFlags loIfname) expected (ops.ioctl liveFd .getIfFlags loIfname)
    checkErr "bind" (.bind closedHid (.ipv4 INADDR_LOOPBACK 0)) Errno.EBADF (ops.bind closedFd (.ipv4 INADDR_LOOPBACK 0))
    checkErr "recvfrom" (.recvfrom closedHid 16 {}) Errno.EBADF (ops.recvfrom closedFd 16 {})
    checkErr "sendmsg" (.sendmsg u0Hid #[closedHid]) Errno.EBADF (ops.sendmsg u0 #[closedFd])
    checkErr "socket" (.socket .inet .seqpacket fl 0) Errno.ESOCKTNOSUPPORT (ops.socket .inet .seqpacket fl 0)
    checkErr "bind" (.bind liveHid (.unix ByteArray.empty)) Errno.EINVAL (ops.bind liveFd (.unix ByteArray.empty))
    checkErr "recvmsg" (.recvmsg u0Hid 33) Errno.EINVAL (ops.recvmsg u0 33)
    checkErr "sendmsg" (.sendmsg u0Hid (Array.replicate 33 liveHid)) Errno.EINVAL (ops.sendmsg u0 (Array.replicate 33 liveFd))
    let finalHits ← hitsRef.get
    return encodeHitLines finalHits
  finally
    for fd in openFds do
      let _ ← rawNetClose fd

/-- Verify `Net.allowedStep` under a self-installed `SECCOMP_RET_ERRNO` filter returning `expected`. -/
def runSeccompWorker (expected : Errno) : IO Unit := do
  let _ ← runSeccompChild expected

private def runNetSeccompSubEpisodes : IO Unit := do
  for err in #[Errno.EPERM, Errno.EACCES] do
    let (rc, _) ← SandboxEnv.runForked (runSeccompChild err)
    if rc != 0 then
      throw (IO.userError s!"net seccomp sub-episode failed (errno={err}, exit={rc})")

private def maybeRunUsernsChild (totalSteps : Nat) (seed : UInt64) (requireNs : Bool := false) : IO String := do
  let probe ← IO.Process.output { cmd := "unshare", args := #["-Urn", "--", "true"] }
  if probe.exitCode != 0 then
    if requireNs then
      throw (IO.userError s!"net userns probe unavailable under --require-ns (exit={probe.exitCode}): {probe.stderr.trimAscii.toString}")
    return "skipped (unprivileged user+net namespace unavailable)"
  let usernsSteps := max 2000 (min 4000 (totalSteps / 6))
  let exe ← IO.appPath
  let child ← IO.Process.output {
    cmd := "unshare"
    args := #["-Urn", "--", exe.toString, "--suite", "net", "--net-userns-worker", "--steps", toString usernsSteps, "--seed", toString seed]
  }
  if child.exitCode != 0 then
    throw (IO.userError s!"net userns child failed (exit={child.exitCode}): {child.stderr}")
  return s!"CLONE_NEWUSER|CLONE_NEWNET lo-down ENETUNREACH + SIOCSIFFLAGS IFF_UP + {usernsSteps} steps ok"

private def pushU16LELocal (b : ByteArray) (v : UInt16) : ByteArray :=
  (b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8

private def pushU32LELocal (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8).push
    ((v >>> 16) &&& 0xff).toUInt8).push ((v >>> 24) &&& 0xff).toUInt8

private def pushBpfLocal (b : ByteArray) (code : UInt16) (jt jf : UInt8) (k : UInt32) : ByteArray :=
  pushU32LELocal (((pushU16LELocal b code).push jt).push jf) k

private def encodeRecvfromMaxBytesSeccompBpf : ByteArray := Id.run do
  let mut b := ByteArray.empty
  b := pushBpfLocal b 0x0020 0 0 4
  b := pushBpfLocal b 0x0015 1 0 0xc000003e
  b := pushBpfLocal b 0x0015 2 8 0xc00000b7
  b := pushBpfLocal b 0x0020 0 0 0
  b := pushBpfLocal b 0x0015 2 6 45
  b := pushBpfLocal b 0x0020 0 0 0
  b := pushBpfLocal b 0x0015 0 4 207
  b := pushBpfLocal b 0x0020 0 0 36
  b := pushBpfLocal b 0x0015 0 3 0
  b := pushBpfLocal b 0x0020 0 0 32
  b := pushBpfLocal b 0x0015 0 1 MAX_READ_BYTES.toNat.toUInt32
  b := pushBpfLocal b 0x0006 0 0 0x7fff0000
  b := pushBpfLocal b 0x0006 0 0 (0x00050000 ||| (Errno.EPERM &&& 0xffff))
  return b

private def runRecvfromMaxBytesSeccompProbe : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let (rc, payload) ← SandboxEnv.runForked do
    let (a, b) ← match ← ops.socketpair .unix .stream nb with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"net recvfrom cap socketpair failed: {e}")
    try
      let sops := LeanSwe.LinuxSyscall.Sandbox.defaultOps
      match ← sops.prctl .setNoNewPrivs with
      | .error e => throw (IO.userError s!"net recvfrom cap setNoNewPrivs failed: {e}")
      | .ok _ => pure ()
      match ← SandboxEnv.installRawSeccomp encodeRecvfromMaxBytesSeccompBpf with
      | .error e => throw (IO.userError s!"net recvfrom cap installRawSeccomp failed: {e}")
      | .ok () => pure ()
      for reqLen in #[MAX_READ_BYTES.toNat.toUInt32, 0x7fffffff, 0xffffffff] do
        match ← ops.recvfrom a reqLen { dontwait := true } with
        | .error e =>
          if e != Errno.EAGAIN then
            throw (IO.userError s!"net recvfrom cap len={reqLen} expected EAGAIN (clamped to 16MiB), got {e}")
        | .ok bs => throw (IO.userError s!"net recvfrom cap len={reqLen} unexpectedly got {bs.size}B")
      for subLen in #[MAX_READ_BYTES.toNat.toUInt32 - 1, 1048576] do
        match ← ops.recvfrom a subLen { dontwait := true } with
        | .error e =>
          if e != Errno.EPERM then
            throw (IO.userError s!"net recvfrom cap subLen={subLen} expected seccomp EPERM, got {e}")
        | .ok bs => throw (IO.userError s!"net recvfrom cap subLen={subLen} unexpectedly got {bs.size}B")
      return "OK".toUTF8
    finally
      let _ ← rawNetClose a
      let _ ← rawNetClose b
  if rc != 0 || String.fromUTF8! payload != "OK" then
    throw (IO.userError s!"net recvfrom 16MiB cap probe failed (rc={rc}, msg={String.fromUTF8! payload})")

@[noinline] private def allocFuzzStreamReadDroppingWriteFd0 (nb : SockFlags) : IO RawFd := do
  match ← defaultOps.socketpair .unix .stream nb with
  | .ok (s0, s1) =>
    let r0 ← SandboxEnv.peekRawFd s0
    if r0 != 0 then
      let _ ← rawNetClose s0
      let _ ← rawNetClose s1
      throw (IO.userError s!"net fd0 finalizer sp expected raw 0, got {r0}")
    return s1
  | .error e => throw (IO.userError s!"net fd0 finalizer sp failed: {e}")

private def runFdZeroAndPath108Probe (nanos : Nat) : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let pfx := s!"/tmp/lsnfz108_{nanos}_"
  let p108 := pfx ++ String.ofList (List.replicate (UNIX_PATH_MAX - pfx.utf8ByteSize) 'z')
  let addr108 := SockAddr.unix p108.toUTF8
  try IO.FS.removeFile p108 catch _ => pure ()
  let l108 ← match ← ops.socket .unix .stream nb 0 with
    | .ok f => pure f | .error e => throw (IO.userError s!"net u108 lis failed: {e}")
  let c108 ← match ← ops.socket .unix .stream nb 0 with
    | .ok f => pure f
    | .error e => let _ ← rawNetClose l108; throw (IO.userError s!"net u108 cli failed: {e}")
  try
    match ← ops.bind l108 addr108 with
    | .ok () => pure () | .error e => throw (IO.userError s!"net u108 bind failed: {e}")
    match ← ops.getsockname l108 with
    | .ok g =>
      if g != addr108 then
        throw (IO.userError s!"net u108 getsockname mismatch: {repr g}")
    | .error e => throw (IO.userError s!"net u108 gsn failed: {e}")
    match ← ops.listen l108 4 with
    | .ok () => pure () | .error e => throw (IO.userError s!"net u108 listen failed: {e}")
    match ← ops.connect c108 addr108 with
    | .ok () => pure () | .error e => throw (IO.userError s!"net u108 connect failed: {e}")
    match ← ops.accept4 l108 nb with
    | .ok (afd, _) => let _ ← rawNetClose afd
    | .error e => throw (IO.userError s!"net u108 accept4 failed: {e}")
  finally
    let _ ← rawNetClose c108
    let _ ← rawNetClose l108
    try IO.FS.removeFile p108 catch _ => pure ()

  let (st, payload) ← SandboxEnv.runForked do
    SandboxEnv.closeRaw 0
    let (sp0, sp1) ← match ← ops.socketpair .unix .stream nb with
      | .ok p => pure p | .error e => throw (IO.userError s!"net fd0 sp failed: {e}")
    let rSp0 ← SandboxEnv.peekRawFd sp0
    if rSp0 != 0 then
      let _ ← rawNetClose sp0; let _ ← rawNetClose sp1
      throw (IO.userError s!"net fd0 sp0 expected raw 0, got {rSp0}")
    match ← ops.getsockname sp0 with
    | .ok _ => pure ()
    | .error e =>
      let _ ← rawNetClose sp0; let _ ← rawNetClose sp1
      throw (IO.userError s!"net fd0 getsockname failed: {e}")
    match ← rawNetClose sp0 with
    | .ok () => pure ()
    | .error e =>
      let _ ← rawNetClose sp1
      throw (IO.userError s!"net fd0 close sp0 failed: {e}")
    let _ ← rawNetClose sp1

    let finRx ← allocFuzzStreamReadDroppingWriteFd0 nb
    match ← ops.recvfrom finRx 8 { dontwait := true } with
    | .ok bs =>
      let _ ← rawNetClose finRx
      if !bs.isEmpty then throw (IO.userError s!"net fd0 finalizer expected EOF, got {bs.size}B")
    | .error e =>
      let _ ← rawNetClose finRx
      throw (IO.userError s!"net fd0 finalizer recvfrom failed: {e}")

    let ph0 ← match ← ops.socket .unix .stream nb 0 with
      | .ok f => pure f | .error e => throw (IO.userError s!"net fd0 ph0 failed: {e}")
    let (ct0, ct1) ← match ← ops.socketpair .unix .stream nb with
      | .ok p => pure p | .error e => throw (IO.userError s!"net fd0 ct sp failed: {e}")
    let (pr0, pr1) ← match ← ops.socketpair .unix .stream nb with
      | .ok p => pure p | .error e => throw (IO.userError s!"net fd0 pr sp failed: {e}")
    match ← ops.sendmsg ct0 #[pr1, ct0] with
    | .ok () => pure () | .error e => throw (IO.userError s!"net fd0 ctrunc sendmsg failed: {e}")
    let _ ← rawNetClose pr1
    let _ ← rawNetClose ph0
    match ← ops.recvmsg ct1 1 with
    | .error e =>
      if e != Errno.EPROTO then throw (IO.userError s!"net fd0 ctrunc expected EPROTO, got {e}")
    | .ok got =>
      for x in got do let _ ← rawNetClose x
      throw (IO.userError "net fd0 ctrunc unexpectedly succeeded")
    match ← ops.recvfrom pr0 8 { dontwait := true } with
    | .ok eof =>
      if !eof.isEmpty then throw (IO.userError s!"net fd0 ctrunc expected EOF, got {eof.size}B")
    | .error e => throw (IO.userError s!"net fd0 ctrunc leaked raw fd 0: {e}")
    let _ ← rawNetClose pr0
    let _ ← rawNetClose ct1
    let _ ← rawNetClose ct0
    return "OK".toUTF8
  if st != 0 || String.fromUTF8! payload != "OK" then
    throw (IO.userError s!"net fd0 probe failed (status={st}, payload={String.fromUTF8! payload})")

private def runScmTruncFdLeakProbe : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  for nSend in #[2, 3] do
    let mut st := NetState.initial false
    let mut openFds : Array RawFd := #[]
    let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
      match allowedStep s req out with
      | some s' => return s'
      | none => throw (IO.userError s!"net scm trunc model rejected {lbl}: req={repr req} out={repr out}")
    try
      let (c0, c1) ← match ← ops.socketpair .unix .seqpacket nb with
        | .ok (a, b) => openFds := (openFds.push a).push b; pure (a, b)
        | .error e => throw (IO.userError s!"net scm trunc carrier sp failed: {e}")
      let c0H := st.nextHid
      let c1H := c0H + 1
      st ← mustStep "carrier sp" st (.socketpair .unix .seqpacket nb) (.pair c0H c1H)
      let (p0, p1) ← match ← ops.socketpair .unix .stream nb with
        | .ok (a, b) => openFds := openFds.push a; pure (a, b)
        | .error e => throw (IO.userError s!"net scm trunc probe sp failed: {e}")
      let p0H := st.nextHid
      let p1H := p0H + 1
      st ← mustStep "probe sp" st (.socketpair .unix .stream nb) (.pair p0H p1H)
      let rawBatch := if nSend == 2 then #[p1, c0] else #[p1, c0, c1]
      let hidBatch := if nSend == 2 then #[p1H, c0H] else #[p1H, c0H, c1H]
      match ← ops.sendmsg c0 rawBatch with
      | .ok () => st ← mustStep "sendmsg" st (.sendmsg c0H hidBatch) .unit
      | .error e =>
        let _ ← rawNetClose p1
        throw (IO.userError s!"net scm trunc sendmsg({nSend}) failed: {e}")
      let _ ← rawNetClose p1
      st ← match st.closeHandle p1H with
        | .ok s' => pure s'
        | .error e => throw (IO.userError s!"net scm trunc closeHandle failed: {e}")
      match ← ops.recvmsg c1 1 with
      | .error e =>
        if e != Errno.EPROTO then
          throw (IO.userError s!"net scm trunc recvmsg({nSend}->1) expected EPROTO, got {e}")
        st ← mustStep "recvmsg trunc" st (.recvmsg c1H 1) (.err e)
      | .ok got =>
        for fd in got do let _ ← rawNetClose fd
        throw (IO.userError s!"net scm trunc recvmsg({nSend}->1) unexpectedly succeeded")
      match ← ops.recvfrom p0 8 { dontwait := true } with
      | .ok eof =>
        if !eof.isEmpty then
          throw (IO.userError s!"net scm trunc expected 0B EOF, got {eof.size}B")
        let _ ← mustStep "probe eof" st (.recvfrom p0H 8 { dontwait := true }) (.bytes eof)
      | .error e =>
        throw (IO.userError s!"net scm trunc leaked kernel FD on nSend={nSend} (recvfrom got {e}, expected EOF)")
    finally
      for fd in openFds do
        let _ ← rawNetClose fd

private def runTcpNagleShutRdwrProbe : IO Unit := do
  let ops := defaultOps
  let nb : SockFlags := { nonblock := true, cloexec := true }
  let checkLo ← match ← ops.socket .inet .dgram nb 0 with
    | .ok fd =>
      let r ← ops.ioctl fd .getIfFlags loIfname
      let _ ← rawNetClose fd
      match r with | .ok fl => pure ((fl &&& IFF_UP) != 0) | .error _ => pure false
    | .error _ => pure false
  if !checkLo then
    return ()
  for mode in #[0, 1] do
    let mut st := NetState.initial false
    let mut openFds : Array RawFd := #[]
    let mustStep (lbl : String) (s : NetState) (req : NetReq) (out : NetOutcome) : IO NetState := do
      match allowedStep s req out with
      | some s' => return s'
      | none => throw (IO.userError s!"net nagle shut_rdwr probe({mode}) model rejected {lbl}: req={repr req} out={repr out}")
    try
      let cfd ← match ← ops.socket .inet .stream nb 0 with
        | .ok fd => pure fd
        | .error e => throw (IO.userError s!"nagle probe cli socket failed: {e}")
      let cH := st.nextHid
      st ← mustStep "cli sock" st (.socket .inet .stream nb 0) (.opened cH)
      let lfd ← match ← ops.socket .inet .stream nb 0 with
        | .ok fd => openFds := openFds.push fd; pure fd
        | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe lis socket failed: {e}")
      let lH := st.nextHid
      st ← mustStep "lis sock" st (.socket .inet .stream nb 0) (.opened lH)
      match ← ops.bind lfd (.ipv4 INADDR_LOOPBACK 0) with
      | .ok () => st ← mustStep "lis bind" st (.bind lH (.ipv4 INADDR_LOOPBACK 0)) .unit
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe bind failed: {e}")
      match ← ops.listen lfd 8 with
      | .ok () => st ← mustStep "lis listen" st (.listen lH 8) .unit
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe listen failed: {e}")
      let laddr ← match ← ops.getsockname lfd with
        | .ok sa => st ← mustStep "lis gsn" st (.getsockname lH) (.addr sa); pure sa
        | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe gsn failed: {e}")
      match ← ops.connect cfd laddr with
      | .ok () => st ← mustStep "cli conn ok" st (.connect cH laddr) .unit
      | .error e => st ← mustStep "cli conn err" st (.connect cH laddr) (.err e)
      let mut sfdOpt : Option (RawFd × SockAddr) := none
      for _ in [:20] do
        match ← ops.accept4 lfd nb with
        | .ok p => sfdOpt := some p; break
        | .error e => if e == Errno.EAGAIN then IO.sleep 1 else break
      let (sfd, peerSa) ← match sfdOpt with
        | some (fd, psa) => openFds := openFds.push fd; pure (fd, psa)
        | none => let _ ← rawNetClose cfd; throw (IO.userError "nagle probe accept4 timed out")
      let sH := st.nextHid
      st ← mustStep "accept4" st (.accept4 lH nb) (.accepted sH peerSa)
      match ← ops.sendto cfd (ByteArray.mk #[112]) {} with
      | .ok n => st ← mustStep "c send1" st (.sendto cH (ByteArray.mk #[112]) {}) (.u32 n)
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe c send1 failed: {e}")
      match ← ops.sendto sfd (ByteArray.mk #[124]) {} with
      | .ok n => st ← mustStep "s send1" st (.sendto sH (ByteArray.mk #[124]) {}) (.u32 n)
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe s send1 failed: {e}")
      match ← ops.shutdown sfd .wr with
      | .ok () => st ← mustStep "s shut wr" st (.shutdown sH .wr) .unit
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe s shut wr failed: {e}")
      match ← ops.sendto cfd (ByteArray.mk #[191]) {} with
      | .ok n => st ← mustStep "c send2" st (.sendto cH (ByteArray.mk #[191]) {}) (.u32 n)
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe c send2 failed: {e}")
      match ← ops.recvfrom cfd 1 {} with
      | .ok bs => st ← mustStep "c recv1" st (.recvfrom cH 1 {}) (.bytes bs)
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe c recv1 failed: {e}")
      match ← ops.sendto cfd (ByteArray.mk #[240]) {} with
      | .ok n => st ← mustStep "c send3" st (.sendto cH (ByteArray.mk #[240]) {}) (.u32 n)
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe c send3 failed: {e}")
      match ← ops.shutdown sfd .rd with
      | .ok () => st ← mustStep "s shut rd" st (.shutdown sH .rd) .unit
      | .error e => let _ ← rawNetClose cfd; throw (IO.userError s!"nagle probe s shut rd failed: {e}")
      if mode == 0 then
        let _ ← rawNetClose cfd
        st ← match st.closeHandle cH with
          | .ok s' => pure s'
          | .error e => throw (IO.userError s!"nagle probe closeHandle failed: {e}")
        IO.sleep 2
        let sOut ← match ← ops.sendto sfd ByteArray.empty {} with
          | .ok n => pure (.u32 n)
          | .error e => pure (.err e)
        st ← mustStep "s send0 after close" st (.sendto sH ByteArray.empty {}) sOut
        let sOut2 ← match ← ops.sendto sfd (ByteArray.mk #[1]) { nosignal := true } with
          | .ok n => pure (.u32 n)
          | .error e => pure (.err e)
        st ← mustStep "s send1 after close" st (.sendto sH (ByteArray.mk #[1]) { nosignal := true }) sOut2
      else
        openFds := openFds.push cfd
        let cShutOut ← match ← ops.shutdown cfd .wr with
          | .ok () => pure .unit
          | .error e => pure (.err e)
        st ← mustStep "c shut wr" st (.shutdown cH .wr) cShutOut
        IO.sleep 2
        let cRxOut ← match ← ops.recvfrom cfd 8 {} with
          | .ok bs => pure (.bytes bs)
          | .error e => pure (.err e)
        st ← mustStep "c recv eof" st (.recvfrom cH 8 {}) cRxOut
        let cSoOut ← match ← ops.getsockopt cfd .error with
          | .ok v => pure (.u32 v)
          | .error e => pure (.err e)
        st ← mustStep "c soError" st (.getsockopt cH .error) cSoOut
        let r1Out ← match ← ops.recvfrom sfd 8 {} with
          | .ok bs => pure (.bytes bs)
          | .error e => pure (.err e)
        st ← mustStep "s recv1" st (.recvfrom sH 8 {}) r1Out
        let r2Out ← match ← ops.recvfrom sfd 8 {} with
          | .ok bs => pure (.bytes bs)
          | .error e => pure (.err e)
        let _ ← mustStep "s recv2" st (.recvfrom sH 8 {}) r2Out
    finally
      for fd in openFds do
        let _ ← rawNetClose fd

/-- Execute stateful `Net` world fuzzing across `totalSteps` real syscalls over all 15 `Net` operations. -/
def runNetFuzz (totalSteps : Nat) (seed : UInt64 := 0x4e455446555a5a31)
    (selfTestShrink : Bool := false) (requireNs : Bool := false) : IO FuzzReport := do
  let nanos ← IO.monoNanosNow
  let rootDir : System.FilePath := s!"/dev/shm/leanswe-net-fuzz-{nanos}"
  IO.FS.createDirAll rootDir
  try
    let shrinkDetail ← if selfTestShrink then runShrinkSelfTest rootDir else pure ""
    let usernsDetail ←
      if totalSteps >= 1000 then maybeRunUsernsChild totalSteps seed requireNs
      else pure ""
    if totalSteps >= 1000 then
      runNetSeccompSubEpisodes
      runRecvfromMaxBytesSeccompProbe
      runScmTruncFdLeakProbe
      runTcpNagleShutRdwrProbe
      runSigalrmEintrProbe
      runSigpipeNosignalProbe
      runListenBacklogProbe rootDir
      runFdZeroAndPath108Probe nanos
    let mut stats : HitStats := {}
    let origNofile ← match ← rawRlimitNofile 0 0 with
      | .ok v => pure v
      | .error _ => pure 1024
    let startNs ← IO.monoNanosNow
    let ops := defaultOps
    let mut rng := Rng.seed seed
    let mut epIdx : Nat := 0
    let mut mainSteps : Nat := 0
    while mainSteps < totalSteps do
      let remaining := totalSteps - mainSteps
      let (epLenRaw, rLen) := rng.nextNat 91
      rng := rLen
      let epLen := min (max remaining 1) (50 + epLenRaw)
      let epDir := rootDir / s!"ep-{epIdx}"
      if ← epDir.pathExists then
        IO.FS.removeDirAll epDir
      IO.FS.createDirAll epDir
      let mut curNofile := origNofile
      let mut modelState := NetState.initial false
      let mut env : GenEnv := { absTag := s!"{nanos % 1000000}-{epIdx}", allowBareAbs := epIdx == 0 }
      let mut symMap : Std.HashMap SymFd HandleId := {}
      let mut rawMap : Std.HashMap HandleId RawFd := {}
      let mut openMap : Std.HashMap HandleId RawFd := {}
      let mut liveAddrs : Std.HashMap SymFd SockAddr := {}
      let mut trace : Array SymStep := #[]
      let mut nextSym : SymFd := 0
      try
        let mut epSyscalls := 0
        for stepIdx in [:epLen * 3] do
          if epSyscalls >= epLen || mainSteps >= totalSteps then
            break
          let (sreq, armAlrm, rNext) := genSymReq rng env modelState symMap epDir origNofile curNofile
          rng := rNext
          let nAlloc := allocSlotsForReq sreq
          let mut allocIds : Array SymFd := #[]
          for _ in [:nAlloc] do
            allocIds := allocIds.push nextSym
            nextSym := nextSym + 1
          let step : SymStep := { allocIds, req := sreq, armAlrm }
          trace := trace.push step
          match ← execOneStep ops epDir origNofile curNofile symMap rawMap openMap liveAddrs modelState step with
          | .error msg =>
            let _ ← rawRlimitNofile 1 origNofile
            closeOpenFds openMap
            openMap := {}
            let shrinkDir := rootDir / "shrink"
            let wantPrefix := ((msg.splitOn ":").headD msg).trimAscii.toString
            let wantOut? := extractNetOut? msg
            let shrunk ← shrinkTrace trace fun cand => do
              let r ← replayTrace shrinkDir cand false
              return (r.mismatchMsg.map (matchesNetMismatch wantPrefix wantOut?)).getD false
            throw (IO.userError s!"net model/kernel mismatch at ep={epIdx} step={stepIdx} (global={stats.totalSteps}): {msg}\nminimal trace ({shrunk.size} steps): {repr shrunk}\nraw trace ({trace.size} steps): {repr trace}")
          | .ok (sm, rm, om, la, cn, s', out?) =>
            symMap := sm
            rawMap := rm
            openMap := om
            liveAddrs := la
            curNofile := cn
            modelState := s'
            env := updateEnvAfterStep env step symMap liveAddrs modelState out?
            match out? with
            | some (sname, out) =>
              stats := stats.record sname out
              epSyscalls := epSyscalls + 1
              mainSteps := mainSteps + 1
            | none => pure ()
      finally
        let _ ← rawRlimitNofile 1 origNofile
        closeOpenFds openMap
        if ← epDir.pathExists then
          IO.FS.removeDirAll epDir
      stats := { stats with totalEpisodes := stats.totalEpisodes + 1 }
      epIdx := epIdx + 1
    let endNs ← IO.monoNanosNow
    let elapsedMs := (endNs - startNs) / 1000000
    let sps := (stats.totalSteps * 1000) / max 1 elapsedMs
    return {
      totalSteps := stats.totalSteps
      totalEpisodes := stats.totalEpisodes
      elapsedMs
      syscallsPerSec := sps
      stats
      shrinkSelfTestDetail := shrinkDetail
      usernsDetail
    }
  finally
    if ← rootDir.pathExists then
      IO.FS.removeDirAll rootDir

end Fuzz.LinuxSyscall.NetFuzz
