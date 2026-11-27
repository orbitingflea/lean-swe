import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSweProofs.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Poll.Interface
import Fuzz.LinuxSyscall.Rng
import Fuzz.LinuxSyscall.SandboxEnv
import Std.Data.HashMap

namespace Fuzz.LinuxSyscall.PollFuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Poll

@[extern "leanswe_poll_close_fd"]
private opaque rawPollClose : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_poll_efd_write"]
private opaque rawEfdWrite : @& RawFd → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_poll_efd_read"]
private opaque rawEfdRead : @& RawFd → IO (Except Errno UInt64)

@[extern "leanswe_poll_open_pipe"]
private opaque rawOpenPipe : IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_poll_open_kind"]
private opaque rawOpenKind : UInt32 → IO (Except Errno RawFd)

@[extern "leanswe_poll_open_sockpair"]
private opaque rawOpenSockpair : IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_poll_pipe_write1"]
private opaque rawPipeWrite1 : @& RawFd → IO (Except Errno UInt8)

@[extern "leanswe_poll_pipe_read1"]
private opaque rawPipeRead1 : @& RawFd → IO (Except Errno UInt8)

@[extern "leanswe_poll_rlimit_nofile"]
private opaque rawRlimitNofile : UInt8 → UInt64 → IO (Except Errno UInt64)

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque rawArmSigalrm : UInt32 → UInt8 → BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque rawDisarmSigalrm : UInt32 → BaseIO Unit

@[extern "leanswe_poll_get_fd_flags"]
private opaque rawPollGetFdFlags : @& RawFd → IO (Except Errno UInt32)

@[extern "leanswe_poll_open_seqpair"]
private opaque rawOpenSeqpair : IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_poll_open_tcp_listener"]
private opaque rawOpenTcpListener : IO (Except Errno (RawFd × UInt32))

@[extern "leanswe_poll_tcp_connect_loopback"]
private opaque rawTcpConnectLoopback : UInt32 → IO (Except Errno RawFd)

@[extern "leanswe_poll_accept4"]
private opaque rawAccept4 : @& RawFd → IO (Except Errno RawFd)

@[extern "leanswe_poll_open_udp_socket"]
private opaque rawOpenUdpSocket : IO (Except Errno RawFd)

@[extern "leanswe_poll_open_udp_pair"]
private opaque rawOpenUdpPair : IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_poll_sendto_dontwait"]
private opaque rawSendtoDontwait : @& RawFd → @& ByteArray → IO (Except Errno UInt32)

@[extern "leanswe_poll_recv_dontwait"]
private opaque rawRecvDontwait : @& RawFd → UInt32 → UInt8 → IO (Except Errno UInt32)

/-- Symbolic descriptor slot used in shrinkable `Poll` fuzz traces. -/
abbrev SymFd := Nat

/-- Kind of symbolic descriptor tracked during `Poll` trace generation and shrinking. -/
inductive SymKind where
  /-- Linux `eventfd` handle. -/
  | eventfd
  /-- Read end of a non-blocking pipe paired with write `SymFd`. -/
  | pipeRead (peerWrite : SymFd)
  /-- Write end of a non-blocking pipe paired with read `SymFd`. -/
  | pipeWrite (peerRead : SymFd)
  /-- Endpoint of a non-blocking `AF_UNIX` `SOCK_STREAM` `socketpair` paired with peer `SymFd`. -/
  | sockEnd (peer : SymFd)
  /-- Endpoint of a non-blocking `AF_UNIX` `SOCK_SEQPACKET` `socketpair` paired with peer `SymFd`. -/
  | seqEnd (peer : SymFd)
  /-- Endpoint of a connected non-blocking loopback `AF_INET` TCP pair paired with peer `SymFd`. -/
  | tcpEnd (peer : SymFd)
  /-- Endpoint of a connected non-blocking loopback `AF_INET` UDP pair paired with peer `SymFd`. -/
  | udpEnd (peer : SymFd)
  /-- Always-ready endpoint (`/dev/null`, directory, or regular file). -/
  | alwaysReady
  /-- Open `O_PATH` descriptor reporting `POLLNVAL` in `revents`. -/
  | opathInvalid
  /-- Non-blocking IPv4 TCP listening socket (initially non-readable and non-writable). -/
  | tcpListener
  /-- Non-blocking IPv4 UDP datagram socket (initially writable). -/
  | udpSocket
  deriving Repr, DecidableEq, BEq

/-- Symbolic `Poll` fuzz request using `SymFd` handles. -/
inductive SymReq where
  /-- Create a new `eventfd2` descriptor. -/
  | eventfd2 (initval : UInt32) (flags : EventFdFlags)
  /-- Open a non-blocking pipe pair `(readEnd, writeEnd)`. -/
  | openPipe
  /-- Open a non-blocking `AF_UNIX` `SOCK_STREAM` socket pair. -/
  | openSockpair
  /-- Open a non-blocking `AF_UNIX` `SOCK_SEQPACKET` socket pair. -/
  | openSeqpair
  /-- Open a connected non-blocking loopback `AF_INET` TCP socket pair. -/
  | openTcpPair
  /-- Open a connected non-blocking loopback `AF_INET` UDP socket pair. -/
  | openUdpPair
  /-- Open a bound/listening non-blocking IPv4 TCP socket. -/
  | openTcpListener
  /-- Open a non-blocking IPv4 UDP socket. -/
  | openUdpSocket
  /-- Open a static descriptor kind (`0`: `/dev/null`, `1`: dir, `2`: `O_PATH`, `3`: regfile). -/
  | openKind (kind : UInt32)
  /-- Add `delta` to an `eventfd` counter. -/
  | efdWrite (fd : SymFd) (delta : UInt64)
  /-- Consume an `eventfd` counter. -/
  | efdRead (fd : SymFd)
  /-- Write 1 byte to a pipe write end or socketpair end. -/
  | streamWrite1 (fd : SymFd)
  /-- Read 1 byte from a pipe read end or socketpair end. -/
  | streamRead1 (fd : SymFd)
  /-- Saturate send buffer of a stream socket until `EAGAIN` (`writable := false`). -/
  | streamSaturate (fd : SymFd)
  /-- Drain receive buffer of a saturated stream socket peer until `EAGAIN` (`writable := true`). -/
  | streamDrain (fd : SymFd)
  /-- Adjust process soft `RLIMIT_NOFILE` limit (`0` restores saved baseline). -/
  | setSoftNofile (limit : UInt64)
  /-- Execute `ppoll` over symbolic descriptor entries and timeout (optionally arming `SIGALRM`). -/
  | ppoll (entries : Array (SymFd × PollEvents)) (timeout : Option Timespec) (armAlrm : Bool := false)
  /-- Execute `ppoll` over `MAX_POLL_NFDS + 1` copies of `fd` without storing the large entry array in the trace. -/
  | ppollOverMaxCap (fd : SymFd) (timeout : Option Timespec)
  /-- Close an open or already-closed descriptor. -/
  | close (fd : SymFd)
  deriving Repr

/-- Recorded symbolic step in a `Poll` fuzzing episode. -/
structure SymStep where
  /-- Symbolic handle IDs allocated by this step (`[]`, `[s]`, or `[s0, s1]`). -/
  allocIds : Array SymFd
  /-- Syscall or helper request executed at this step. -/
  req : SymReq
  deriving Repr

/-- Per-(syscall, outcome) hit counter table for `Poll` fuzzing. -/
structure HitStats where
  /-- Counts keyed by `"<syscall>:<ok|err(errno)>"`. -/
  counts : Std.HashMap String Nat := {}
  /-- Total `eventfd2` + `ppoll` syscalls executed. -/
  totalSteps : Nat := 0
  /-- Total fuzz episodes executed. -/
  totalEpisodes : Nat := 0

/-- All model syscall names covered by `PollFuzz`. -/
def allSyscallNames : Array String := #["eventfd2", "ppoll"]

/-- Record one `Poll` syscall outcome into `HitStats`. -/
def HitStats.record (st : HitStats) (syscallName : String) (out : PollOutcome) : HitStats :=
  let bucket := match out with
    | .err e => s!"{syscallName}:err({e})"
    | .opened _ => s!"{syscallName}:ok"
    | .polled _ => s!"{syscallName}:ok"
  let prev := st.counts.getD bucket 0
  { counts := st.counts.insert bucket (prev + 1)
    totalSteps := st.totalSteps + 1
    totalEpisodes := st.totalEpisodes }

private structure GenEnv where
  allFds : Array (SymFd × HandleId × SymKind) := #[]
  efds : Array SymFd := #[]
  streamWriters : Array SymFd := #[]
  streamReaders : Array SymFd := #[]
  saturatableWriters : Array SymFd := #[]
  saturatedWriters : Array SymFd := #[]
  saturatedReaders : Array SymFd := #[]
  allOpen : Array SymFd := #[]
  closedFds : Array SymFd := #[]

private def findHid (allFds : Array (SymFd × HandleId × SymKind)) (sid : SymFd) : Option HandleId :=
  (allFds.find? (fun p => p.1 == sid)).map (fun p => p.2.1)

private def genPollEvents (r : Rng) : PollEvents × Rng :=
  let (b1, r1) := r.chance 1 2
  let (b2, r2) := r1.chance 1 2
  let (b3, r3) := r2.chance 1 4
  let (b4, r4) := r3.chance 1 4
  let (b5, r5) := r4.chance 1 4
  ({ pollin := b1, pollout := b2, pollerr := b3, pollhup := b4, pollnval := b5 }, r5)

private def genTimespec (r : Rng) (allowLongOrNone : Bool) : Option Timespec × Rng :=
  let (pick, r1) := r.nextNat 14
  if allowLongOrNone && pick < 3 then (none, r1)
  else if pick == 3 then (some { sec := -1, nsec := 0 }, r1)
  else if pick == 4 then (some { sec := -100, nsec := -1 }, r1)
  else if pick == 5 then (some { sec := 0, nsec := NANOS_PER_SEC }, r1)
  else if pick == 6 then (some { sec := 0, nsec := -1 }, r1)
  else if pick == 7 then (some { sec := 0, nsec := 0x7fffffff }, r1)
  else if allowLongOrNone && pick == 8 then (some { sec := 0x7fffffffffffffff, nsec := 999999999 }, r1)
  else if allowLongOrNone && pick == 9 then
    let (s, r2) := r1.nextRange 1 1000
    let (ns, r3) := r2.nextRange 0 (NANOS_PER_SEC.toNat - 1)
    (some { sec := Int64.ofInt (Int.ofNat s), nsec := UInt32.ofNat ns }, r3)
  else
    let (ns, r2) := r1.nextRange 0 10000
    (some { sec := 0, nsec := UInt32.ofNat ns }, r2)

private def genEventfdInit (r : Rng) : UInt32 × EventFdFlags × Rng :=
  let (corner, r1) := r.chance 1 2
  let (initval, r2) :=
    if corner then r1.pickArray #[0, 1, 2, 7, 1000, 0x7fffffff, EFD_MAX_COUNT.toNat.toUInt32, 0xffffffff] 0
    else
      let (u, r') := r1.nextU64
      (u.toUInt32, r')
  let (nb, r3) := r2.chance 1 2
  let (ce, r4) := r3.chance 1 2
  let (sem, r5) := r4.chance 1 2
  (initval, { nonblock := nb, cloexec := ce, semaphore := sem }, r5)

private def canNonblockingEfdOp (s : PollState) (hid : HandleId) (isWrite : Bool) (delta : UInt64) : Bool :=
  match assocGet s.fds hid with
  | some desc =>
    match desc.kind with
    | .eventfd counter flags =>
      if flags.nonblock then true
      else if isWrite then delta != 0xffffffffffffffff && delta.toNat + counter.toNat ≤ EFD_MAX_COUNT.toNat
      else counter > 0
    | _ => false
  | none => false

private def efdDeltaChoices : Array UInt64 :=
  #[0, 1, 2, 5, 100, 0xfffffffffffffffe, 0xffffffffffffffff]

private def collectValidEfdWrites (s : PollState) (env : GenEnv) : Array (SymFd × UInt64) := Id.run do
  let mut out : Array (SymFd × UInt64) := #[]
  for sid in env.efds do
    if let some hid := findHid env.allFds sid then
      for d in efdDeltaChoices do
        if canNonblockingEfdOp s hid true d then
          out := out.push (sid, d)
  return out

private def collectValidEfdReads (s : PollState) (env : GenEnv) : Array SymFd :=
  env.efds.filter fun sid =>
    match findHid env.allFds sid with
    | some hid => canNonblockingEfdOp s hid false 0
    | none => false

private def genOpenExtra (r : Rng) : SymReq × Rng :=
  let (kPick, r1) := r.nextNat 18
  if kPick < 2 then (.openPipe, r1)
  else if kPick < 4 then (.openSockpair, r1)
  else if kPick == 4 then (.openSeqpair, r1)
  else if kPick < 7 then (.openTcpPair, r1)
  else if kPick == 7 then (.openUdpPair, r1)
  else if kPick == 8 then (.openTcpListener, r1)
  else if kPick == 9 then (.openUdpSocket, r1)
  else if kPick < 12 then
    let (kind, r2) := r1.nextNat 4
    (.openKind (UInt32.ofNat kind), r2)
  else
    let (iv, fl, r2) := genEventfdInit r1
    (.eventfd2 iv fl, r2)

private def genSymReq (r : Rng) (env : GenEnv) (s : PollState) (origNofile curNofile : UInt64) :
    SymReq × Rng :=
  if env.allOpen.size < 2 then
    genOpenExtra r
  else
    let (opPick, r1) := r.nextNat 100
    let validWrites := if opPick < 30 && opPick >= 18 then collectValidEfdWrites s env else #[]
    let validReads := if opPick < 40 && opPick >= 30 then collectValidEfdReads s env else #[]
    let availWriters := env.streamWriters.filter (fun sid => !env.saturatedWriters.contains sid)
    let availReaders := env.streamReaders.filter (fun sid => !env.saturatedReaders.contains sid)
    let availSatWriters := env.saturatableWriters.filter (fun sid => !env.saturatedWriters.contains sid)
    if curNofile != origNofile && opPick < 30 then
      let (iv, fl, r2) := genEventfdInit r1
      (.eventfd2 iv fl, r2)
    else if opPick < 18 && env.allOpen.size < 20 then
      genOpenExtra r1
    else if !validWrites.isEmpty then
      let ((sid, d), r2) := r1.pickArray validWrites (0, 0)
      (.efdWrite sid d, r2)
    else if !validReads.isEmpty then
      let (sid, r2) := r1.pickArray validReads 0
      (.efdRead sid, r2)
    else if opPick < 45 && !availWriters.isEmpty then
      let (sid, r2) := r1.pickArray availWriters 0
      (.streamWrite1 sid, r2)
    else if opPick < 50 && !availReaders.isEmpty then
      let (sid, r2) := r1.pickArray availReaders 0
      (.streamRead1 sid, r2)
    else if opPick < 53 && !availSatWriters.isEmpty then
      let (sid, r2) := r1.pickArray availSatWriters 0
      (.streamSaturate sid, r2)
    else if opPick < 56 && !env.saturatedReaders.isEmpty then
      let (sid, r2) := r1.pickArray env.saturatedReaders 0
      (.streamDrain sid, r2)
    else if opPick < 62 && env.allOpen.size > 2 then
      let (closeClosed, r2) := r1.chance 1 8
      if closeClosed && !env.closedFds.isEmpty then
        let (sid, r3) := r2.pickArray env.closedFds 0
        (.close sid, r3)
      else
        let (sid, r3) := r2.pickArray env.allOpen 0
        (.close sid, r3)
    else if opPick >= 62 && opPick < 66 then
      if curNofile == origNofile then
        (.setSoftNofile (UInt64.ofNat (env.allOpen.size + 3)), r1)
      else
        (.setSoftNofile 0, r1)
    else
      let (overCap, r2) := r1.chance 1 2000
      if overCap then
        let (sid, r3) := r2.pickArray env.allOpen 0
        let (tsOpt, r4) := genTimespec r3 true
        (.ppollOverMaxCap sid tsOpt, r4)
      else
        let (bigN, r3) := r2.chance 1 20
        let (nEntries, r4) := if bigN then r3.nextRange 20 80 else r3.nextRange 0 12
        let rec buildEntries (k : Nat) (rng : Rng) (acc : Array (SymFd × PollEvents)) :
            Array (SymFd × PollEvents) × Rng :=
          match k with
          | 0 => (acc, rng)
          | k' + 1 =>
            let (useClosed, ra) := rng.chance 1 12
            let (sid, rb) :=
              if useClosed && !env.closedFds.isEmpty then ra.pickArray env.closedFds 0
              else ra.pickArray env.allOpen 0
            let (ev, rc) := genPollEvents rb
            buildEntries k' rc (acc.push (sid, ev))
        let (entries, r5) := buildEntries nEntries r4 #[]
        let resolved? := entries.mapM fun (sid, ev) =>
          (findHid env.allFds sid).map (fun hid => (hid, ev))
        let anyReady :=
          if entries.size.toUInt64 > curNofile then true
          else
            match resolved? with
            | none => true
            | some pairs =>
              match evalPollList s pairs.toList with
              | .error _ => true
              | .ok revs => revs.any (fun ev => !ev.isEmpty)
        let (doAlrm, r6) := if !anyReady && !entries.isEmpty then r5.chance 1 8 else (false, r5)
        if doAlrm then
          (.ppoll entries (some { sec := 0, nsec := 250000000 }) true, r6)
        else
          let (tsOpt, r7) := genTimespec r6 anyReady
          (.ppoll entries tsOpt false, r7)

private def isAllocReq : SymReq → Nat
  | .eventfd2 .. => 1
  | .openKind _ => 1
  | .openTcpListener => 1
  | .openUdpSocket => 1
  | .openPipe => 2
  | .openSockpair => 2
  | .openSeqpair => 2
  | .openTcpPair => 2
  | .openUdpPair => 2
  | _ => 0

private def closeOpenFds (openMap : Std.HashMap HandleId RawFd) : IO Unit := do
  for (_, rfd) in openMap.toList do
    let _ ← rawPollClose rfd

private def endpointWithBuf (bufCount : Nat) (isSock : Bool) (isReadEnd : Bool)
    (hup err : Bool) (writable : Bool := true) (fin : Bool := false) : PollDesc :=
  if isSock then
    if hup then { kind := .endpoint true writable err true }
    else { kind := .endpoint (bufCount > 0 || fin) writable err false }
  else if isReadEnd then
    { kind := .endpoint (bufCount > 0) false err hup }
  else
    { kind := .endpoint false writable err hup }

private def applyStreamCloseSideEffects (s : PollState) (symKindMap : Std.HashMap SymFd SymKind)
    (hidMap : Std.HashMap SymFd HandleId) (bufMap : Std.HashMap SymFd Nat)
    (hupMap errMap finMap wrFullMap : Std.HashMap SymFd Bool)
    (closedSid : SymFd) :
    PollState × Std.HashMap SymFd Bool × Std.HashMap SymFd Bool × Std.HashMap SymFd Bool × Std.HashMap SymFd Bool :=
  match symKindMap.get? closedSid with
  | some (.pipeWrite rSid) =>
    let hm := hupMap.insert rSid true
    match hidMap.get? rSid with
    | some rHid =>
      match assocGet s.fds rHid with
      | some _ =>
        let cnt := bufMap.getD rSid 0
        let err := errMap.getD rSid false
        ({ s with fds := assocSet s.fds rHid (endpointWithBuf cnt false true true err) }, hm, errMap, finMap, wrFullMap)
      | none => (s, hm, errMap, finMap, wrFullMap)
    | none => (s, hm, errMap, finMap, wrFullMap)
  | some (.pipeRead wSid) =>
    let em := errMap.insert wSid true
    match hidMap.get? wSid with
    | some wHid =>
      match assocGet s.fds wHid with
      | some _ =>
        let hup := hupMap.getD wSid false
        ({ s with fds := assocSet s.fds wHid (endpointWithBuf 0 false false hup true) }, hupMap, em, finMap, wrFullMap)
      | none => (s, hupMap, em, finMap, wrFullMap)
    | none => (s, hupMap, em, finMap, wrFullMap)
  | some (.sockEnd peerSid) | some (.seqEnd peerSid) =>
    let hm := hupMap.insert peerSid true
    let em := if bufMap.getD closedSid 0 > 0 then errMap.insert peerSid true else errMap
    let wm := wrFullMap.insert peerSid false
    match hidMap.get? peerSid with
    | some pHid =>
      match assocGet s.fds pHid with
      | some _ =>
        let cnt := bufMap.getD peerSid 0
        let err := em.getD peerSid false
        ({ s with fds := assocSet s.fds pHid (endpointWithBuf cnt true true true err true) }, hm, em, finMap, wm)
      | none => (s, hm, em, finMap, wm)
    | none => (s, hm, em, finMap, wm)
  | some (.tcpEnd peerSid) =>
    let hasUnread := bufMap.getD closedSid 0 > 0
    let hm := if hasUnread then hupMap.insert peerSid true else hupMap
    let em := if hasUnread then errMap.insert peerSid true else errMap
    let fm := finMap.insert peerSid true
    let wm := if hasUnread then wrFullMap.insert peerSid false else wrFullMap
    match hidMap.get? peerSid with
    | some pHid =>
      match assocGet s.fds pHid with
      | some _ =>
        let cnt := bufMap.getD peerSid 0
        let hup := hm.getD peerSid false
        let err := em.getD peerSid false
        let wr := if hasUnread then true else !(wrFullMap.getD peerSid false)
        ({ s with fds := assocSet s.fds pHid (endpointWithBuf cnt true true hup err wr true) }, hm, em, fm, wm)
      | none => (s, hm, em, fm, wm)
    | none => (s, hm, em, fm, wm)
  | _ => (s, hupMap, errMap, finMap, wrFullMap)

private def streamPeerInfo (symKindMap : Std.HashMap SymFd SymKind) (sid : SymFd) : Option (SymFd × Bool) :=
  match symKindMap.get? sid with
  | some (.pipeWrite rSid) => some (rSid, false)
  | some (.sockEnd pSid) | some (.seqEnd pSid) | some (.tcpEnd pSid) | some (.udpEnd pSid) => some (pSid, true)
  | _ => none

private def streamSelfKind (symKindMap : Std.HashMap SymFd SymKind) (sid : SymFd) : Option Bool :=
  match symKindMap.get? sid with
  | some (.pipeRead _) => some false
  | some (.sockEnd _) | some (.seqEnd _) | some (.tcpEnd _) | some (.udpEnd _) => some true
  | _ => none

private def openTcpPairRaw : IO (Except Errno (RawFd × RawFd)) := do
  let pollOps := defaultOps
  match ← rawOpenTcpListener with
  | .error e => return .error e
  | .ok (lfd, port) =>
    match ← rawTcpConnectLoopback port with
    | .error e => let _ ← rawPollClose lfd; return .error e
    | .ok cfd =>
      let mut res : Except Errno (RawFd × RawFd) := .error Errno.EAGAIN
      for _ in [:8] do
        match ← rawAccept4 lfd with
        | .ok sfd =>
          let _ ← rawPollClose lfd
          return .ok (cfd, sfd)
        | .error e =>
          res := .error e
          if e == Errno.EAGAIN then
            let _ ← pollOps.ppoll #[(lfd, { pollin := true })] (some { sec := 0, nsec := 10000000 })
          else
            break
      let _ ← rawPollClose cfd
      let _ ← rawPollClose lfd
      return res

private def openUdpPairRaw : IO (Except Errno (RawFd × RawFd)) :=
  rawOpenUdpPair

private def bigSatChunk : ByteArray := ByteArray.mk (Array.replicate 65536 0x41)

private def execOneStep (ops : PollOps)
    (origNofile : UInt64)
    (symMap : Std.HashMap SymFd HandleId)
    (symKindMap : Std.HashMap SymFd SymKind)
    (rawMap : Std.HashMap HandleId RawFd)
    (openMap : Std.HashMap HandleId RawFd)
    (bufMap : Std.HashMap SymFd Nat)
    (hupMap : Std.HashMap SymFd Bool)
    (errMap : Std.HashMap SymFd Bool)
    (finMap : Std.HashMap SymFd Bool)
    (wrFullMap : Std.HashMap SymFd Bool)
    (curNofile : UInt64)
    (modelState : PollState)
    (step : SymStep)
    (stepModel : PollState → PollReq → PollOutcome → Option PollState := allowedStep)
    (guardHang : Bool := false) :
    IO (Except String (Std.HashMap SymFd HandleId × Std.HashMap SymFd SymKind ×
      Std.HashMap HandleId RawFd × Std.HashMap HandleId RawFd ×
      Std.HashMap SymFd Nat × Std.HashMap SymFd Bool × Std.HashMap SymFd Bool ×
      Std.HashMap SymFd Bool × Std.HashMap SymFd Bool ×
      UInt64 × PollState × Option (String × PollOutcome))) := do
  let stay := (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, modelState, none)
  match step.req with
  | .eventfd2 initval flags =>
    match step.allocIds[0]? with
    | none => return .error "missing allocId for eventfd2"
    | some sid =>
      let req : PollReq := .eventfd2 initval flags
      match ← ops.eventfd2 initval flags with
      | .ok rfd =>
        let expectedFlags : UInt32 :=
          (if flags.cloexec then 1 else 0) ||| (if flags.nonblock then 2 else 0)
        match ← rawPollGetFdFlags rfd with
        | .error fe =>
          let _ ← rawPollClose rfd
          return .error s!"eventfd2 fd flag check failed: {fe}"
        | .ok gotFlags =>
          if gotFlags != expectedFlags then
            let _ ← rawPollClose rfd
            return .error s!"eventfd2 fd flags mismatch: flags={repr flags} expected={expectedFlags} got={gotFlags}"
        let hid := modelState.nextHid
        let out : PollOutcome := .opened hid
        match stepModel modelState req out with
        | none =>
          let _ ← rawPollClose rfd
          return .error s!"mismatch on eventfd2: req={repr req} out={repr out}"
        | some s' =>
          return .ok (symMap.insert sid hid, symKindMap.insert sid .eventfd,
            rawMap.insert hid rfd, openMap.insert hid rfd, bufMap, hupMap, errMap, finMap, wrFullMap,
            curNofile, s', some ("eventfd2", out))
      | .error e =>
        let out : PollOutcome := .err e
        match stepModel modelState req out with
        | none => return .error s!"mismatch on eventfd2 err: req={repr req} out={repr out}"
        | some s' =>
          return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap,
            curNofile, s', some ("eventfd2", out))
  | .openPipe =>
    match step.allocIds[0]?, step.allocIds[1]? with
    | some rSid, some wSid =>
      match ← rawOpenPipe with
      | .error _ => return .ok stay
      | .ok (rRaw, wRaw) =>
        let (rHid, s1) := modelState.registerDesc { kind := .endpoint false false false false }
        let (wHid, s2) := s1.registerDesc { kind := .endpoint false true false false }
        let sm := (symMap.insert rSid rHid).insert wSid wHid
        let sk := (symKindMap.insert rSid (.pipeRead wSid)).insert wSid (.pipeWrite rSid)
        let rm := (rawMap.insert rHid rRaw).insert wHid wRaw
        let om := (openMap.insert rHid rRaw).insert wHid wRaw
        return .ok (sm, sk, rm, om, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s2, none)
    | _, _ => return .error "missing allocIds for openPipe"
  | .openSockpair =>
    match step.allocIds[0]?, step.allocIds[1]? with
    | some s0, some s1 =>
      match ← rawOpenSockpair with
      | .error _ => return .ok stay
      | .ok (r0, r1) =>
        let (h0, st1) := modelState.registerDesc { kind := .endpoint false true false false }
        let (h1, st2) := st1.registerDesc { kind := .endpoint false true false false }
        let sm := (symMap.insert s0 h0).insert s1 h1
        let sk := (symKindMap.insert s0 (.sockEnd s1)).insert s1 (.sockEnd s0)
        let rm := (rawMap.insert h0 r0).insert h1 r1
        let om := (openMap.insert h0 r0).insert h1 r1
        return .ok (sm, sk, rm, om, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, st2, none)
    | _, _ => return .error "missing allocIds for openSockpair"
  | .openSeqpair =>
    match step.allocIds[0]?, step.allocIds[1]? with
    | some s0, some s1 =>
      match ← rawOpenSeqpair with
      | .error _ => return .ok stay
      | .ok (r0, r1) =>
        let (h0, st1) := modelState.registerDesc { kind := .endpoint false true false false }
        let (h1, st2) := st1.registerDesc { kind := .endpoint false true false false }
        let sm := (symMap.insert s0 h0).insert s1 h1
        let sk := (symKindMap.insert s0 (.seqEnd s1)).insert s1 (.seqEnd s0)
        let rm := (rawMap.insert h0 r0).insert h1 r1
        let om := (openMap.insert h0 r0).insert h1 r1
        return .ok (sm, sk, rm, om, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, st2, none)
    | _, _ => return .error "missing allocIds for openSeqpair"
  | .openTcpPair =>
    match step.allocIds[0]?, step.allocIds[1]? with
    | some s0, some s1 =>
      match ← openTcpPairRaw with
      | .error _ => return .ok stay
      | .ok (r0, r1) =>
        let (h0, st1) := modelState.registerDesc { kind := .endpoint false true false false }
        let (h1, st2) := st1.registerDesc { kind := .endpoint false true false false }
        let sm := (symMap.insert s0 h0).insert s1 h1
        let sk := (symKindMap.insert s0 (.tcpEnd s1)).insert s1 (.tcpEnd s0)
        let rm := (rawMap.insert h0 r0).insert h1 r1
        let om := (openMap.insert h0 r0).insert h1 r1
        return .ok (sm, sk, rm, om, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, st2, none)
    | _, _ => return .error "missing allocIds for openTcpPair"
  | .openUdpPair =>
    match step.allocIds[0]?, step.allocIds[1]? with
    | some s0, some s1 =>
      match ← openUdpPairRaw with
      | .error _ => return .ok stay
      | .ok (r0, r1) =>
        let (h0, st1) := modelState.registerDesc { kind := .endpoint false true false false }
        let (h1, st2) := st1.registerDesc { kind := .endpoint false true false false }
        let sm := (symMap.insert s0 h0).insert s1 h1
        let sk := (symKindMap.insert s0 (.udpEnd s1)).insert s1 (.udpEnd s0)
        let rm := (rawMap.insert h0 r0).insert h1 r1
        let om := (openMap.insert h0 r0).insert h1 r1
        return .ok (sm, sk, rm, om, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, st2, none)
    | _, _ => return .error "missing allocIds for openUdpPair"
  | .openTcpListener =>
    match step.allocIds[0]? with
    | none => return .error "missing allocId for openTcpListener"
    | some sid =>
      match ← rawOpenTcpListener with
      | .error _ => return .ok stay
      | .ok (rfd, _) =>
        let (hid, s') := modelState.registerDesc { kind := .endpoint false false false false }
        return .ok (symMap.insert sid hid, symKindMap.insert sid .tcpListener,
          rawMap.insert hid rfd, openMap.insert hid rfd, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
  | .openUdpSocket =>
    match step.allocIds[0]? with
    | none => return .error "missing allocId for openUdpSocket"
    | some sid =>
      match ← rawOpenUdpSocket with
      | .error _ => return .ok stay
      | .ok rfd =>
        let (hid, s') := modelState.registerDesc { kind := .endpoint false true false false }
        return .ok (symMap.insert sid hid, symKindMap.insert sid .udpSocket,
          rawMap.insert hid rfd, openMap.insert hid rfd, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
  | .openKind kind =>
    match step.allocIds[0]? with
    | none => return .error "missing allocId for openKind"
    | some sid =>
      match ← rawOpenKind kind with
      | .error _ => return .ok stay
      | .ok rfd =>
        let desc : PollDesc :=
          if kind == 2 then { kind := .invalidOsFd }
          else { kind := .endpoint true true false false }
        let skind : SymKind := if kind == 2 then .opathInvalid else .alwaysReady
        let (hid, s') := modelState.registerDesc desc
        return .ok (symMap.insert sid hid, symKindMap.insert sid skind,
          rawMap.insert hid rfd, openMap.insert hid rfd, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
  | .efdWrite sid delta =>
    match symMap.get? sid with
    | none => return .ok stay
    | some hid =>
      if !canNonblockingEfdOp modelState hid true delta then
        return .ok stay
      match rawMap.get? hid with
      | none => return .ok stay
      | some rfd =>
        match ← rawEfdWrite rfd delta, modelState.eventfdAdd hid delta with
        | .ok (), .ok s' =>
          return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
        | .error e, .error expE =>
          if e == expE || Errno.isTransientOsErrno e then return .ok stay
          return .error s!"mismatch on efdWrite: sid={sid} delta={delta} expectedErr={expE} gotErr={e}"
        | .error e, .ok _ =>
          if Errno.isTransientOsErrno e then return .ok stay
          return .error s!"mismatch on efdWrite: sid={sid} delta={delta} expected=ok gotErr={e}"
        | .ok (), .error expE =>
          return .error s!"mismatch on efdWrite: sid={sid} delta={delta} expectedErr={expE} got=ok"
  | .efdRead sid =>
    match symMap.get? sid with
    | none => return .ok stay
    | some hid =>
      if !canNonblockingEfdOp modelState hid false 0 then
        return .ok stay
      match rawMap.get? hid with
      | none => return .ok stay
      | some rfd =>
        match ← rawEfdRead rfd, modelState.eventfdConsume hid with
        | .ok gotVal, .ok (expVal, s') =>
          if gotVal != expVal then
            return .error s!"mismatch on efdRead: sid={sid} expected={expVal} got={gotVal}"
          return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
        | .error e, .error expE =>
          if e == expE || Errno.isTransientOsErrno e then return .ok stay
          return .error s!"mismatch on efdRead: sid={sid} expectedErr={expE} gotErr={e}"
        | .error e, .ok (expVal, _) =>
          if Errno.isTransientOsErrno e then return .ok stay
          return .error s!"mismatch on efdRead: sid={sid} expected={expVal} gotErr={e}"
        | .ok gotVal, .error expE =>
          return .error s!"mismatch on efdRead: sid={sid} expectedErr={expE} got={gotVal}"
  | .streamWrite1 sid =>
    match symMap.get? sid, streamPeerInfo symKindMap sid with
    | some hid, some (peerSid, isSock) =>
      let isUdp := match symKindMap.get? sid with | some (.udpEnd _) => true | _ => false
      let isTcp := match symKindMap.get? sid with | some (.tcpEnd _) => true | _ => false
      let peerOpen := match symMap.get? peerSid with | some ph => openMap.contains ph | none => false
      if (isUdp && !peerOpen) || (isTcp && (bufMap.getD peerSid 0 > 0 || wrFullMap.getD sid false)) then
        return .ok stay
      else
      match rawMap.get? hid with
      | some rfd =>
        match ← rawPipeWrite1 rfd with
        | .ok 1 =>
          if isTcp && !peerOpen then
            let mut gotHup := hupMap.getD sid false
            let mut gotErr := errMap.getD sid false
            let mut clearedErr := false
            if !gotHup then
              for _ in [:25] do
                IO.sleep 2
                match ← rawPipeWrite1 rfd with
                | .error e =>
                  if e == Errno.EPIPE || e == Errno.ECONNRESET then
                    gotHup := true
                    clearedErr := true
                    break
                | .ok _ => pure ()
            if clearedErr then
              gotErr := false
            let hm := hupMap.insert sid gotHup
            let em := errMap.insert sid gotErr
            let fm := finMap.insert sid true
            let wm := if gotHup then wrFullMap.insert sid false else wrFullMap
            let cnt := bufMap.getD sid 0
            let wr := !(wm.getD sid false)
            let s' := match assocGet modelState.fds hid with
              | some _ => { modelState with fds := assocSet modelState.fds hid (endpointWithBuf cnt true true gotHup gotErr wr true) }
              | none => modelState
            return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hm, em, fm, wm, curNofile, s', none)
          else
            if isTcp && peerOpen then
              match symMap.get? peerSid >>= rawMap.get? with
              | some peerRfd =>
                let _ ← ops.ppoll #[(peerRfd, { pollin := true })] (some { sec := 0, nsec := 50000000 })
              | none => pure ()
            let cnt := bufMap.getD peerSid 0 + 1
            let bm := bufMap.insert peerSid cnt
            match symMap.get? peerSid with
            | some pHid =>
              match assocGet modelState.fds pHid with
              | some _ =>
                let hup := hupMap.getD peerSid false
                let err := errMap.getD peerSid false
                let wr := !(wrFullMap.getD peerSid false)
                let fin := finMap.getD peerSid false
                let s' := { modelState with fds := assocSet modelState.fds pHid (endpointWithBuf cnt isSock true hup err wr fin) }
                return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
              | none => return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wrFullMap, curNofile, modelState, none)
            | none => return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wrFullMap, curNofile, modelState, none)
        | .ok _ => return .ok stay
        | .error e =>
          if (isSock && e == Errno.ECONNRESET) || (isTcp && e == Errno.EPIPE) then
            let em := errMap.insert sid false
            let hm := if isTcp then hupMap.insert sid true else hupMap
            let fm := if isTcp then finMap.insert sid true else finMap
            let wm := if isTcp then wrFullMap.insert sid false else wrFullMap
            match assocGet modelState.fds hid with
            | some _ =>
              let cnt := bufMap.getD sid 0
              let hup := hm.getD sid false
              let wr := !(wm.getD sid false)
              let fin := fm.getD sid false
              let s' := { modelState with fds := assocSet modelState.fds hid (endpointWithBuf cnt true true hup false wr fin) }
              return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hm, em, fm, wm, curNofile, s', none)
            | none => return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hm, em, fm, wm, curNofile, modelState, none)
          else
            return .ok stay
      | none => return .ok stay
    | _, _ => return .ok stay
  | .streamRead1 sid =>
    match symMap.get? sid, streamSelfKind symKindMap sid with
    | some hid, some isSock =>
      match rawMap.get? hid with
      | some rfd =>
        match ← rawPipeRead1 rfd with
        | .ok 1 =>
          let prev := bufMap.getD sid 0
          let cnt := if prev > 0 then prev - 1 else 0
          let bm := bufMap.insert sid cnt
          match assocGet modelState.fds hid with
          | some _ =>
            let hup := hupMap.getD sid false
            let err := errMap.getD sid false
            let wr := !(wrFullMap.getD sid false)
            let fin := finMap.getD sid false
            let s' := { modelState with fds := assocSet modelState.fds hid (endpointWithBuf cnt isSock true hup err wr fin) }
            return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wrFullMap, curNofile, s', none)
          | none => return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wrFullMap, curNofile, modelState, none)
        | .ok _ =>
          return .ok stay
        | .error e =>
          if isSock && e == Errno.ECONNRESET then
            let isTcp := match symKindMap.get? sid with | some (.tcpEnd _) => true | _ => false
            let em := errMap.insert sid false
            let hm := if isTcp then hupMap.insert sid true else hupMap
            let fm := if isTcp then finMap.insert sid true else finMap
            match assocGet modelState.fds hid with
            | some _ =>
              let cnt := bufMap.getD sid 0
              let hup := hm.getD sid false
              let wr := !(wrFullMap.getD sid false)
              let fin := fm.getD sid false
              let s' := { modelState with fds := assocSet modelState.fds hid (endpointWithBuf cnt true true hup false wr fin) }
              return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hm, em, fm, wrFullMap, curNofile, s', none)
            | none => return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hm, em, fm, wrFullMap, curNofile, modelState, none)
          else
            return .ok stay
      | none => return .ok stay
    | _, _ => return .ok stay
  | .streamSaturate sid =>
    match symMap.get? sid, streamPeerInfo symKindMap sid with
    | some hid, some (peerSid, true) =>
      let peerOpen := match symMap.get? peerSid with | some ph => openMap.contains ph | none => false
      if !peerOpen then return .ok stay
      match rawMap.get? hid with
      | none => return .ok stay
      | some rfd =>
        let isSeq := match symKindMap.get? sid with | some (.seqEnd _) => true | _ => false
        let mut added : Nat := 0
        let mut hitEagain := false
        for _ in [:128] do
          match ← rawSendtoDontwait rfd bigSatChunk with
          | .ok n => added := added + (if isSeq then 1 else n.toNat)
          | .error e =>
            if e == Errno.EAGAIN then hitEagain := true
            break
        if !hitEagain && added == 0 then return .ok stay
        let isTcp := match symKindMap.get? sid with | some (.tcpEnd _) => true | _ => false
        if isTcp && added > 0 then
          match symMap.get? peerSid >>= rawMap.get? with
          | some peerRfd =>
            for _ in [:25] do
              match ← rawRecvDontwait peerRfd 1 1 with
              | .ok n => if n > 0 then break
              | .error _ => pure ()
              IO.sleep 2
          | none => pure ()
        let wm := if hitEagain then wrFullMap.insert sid true else wrFullMap
        let cnt := bufMap.getD peerSid 0 + added
        let bm := bufMap.insert peerSid cnt
        let s1 :=
          match assocGet modelState.fds hid with
          | some _ =>
            let sc := bufMap.getD sid 0
            let sh := hupMap.getD sid false
            let se := errMap.getD sid false
            let sw := !(wm.getD sid false)
            let sf := finMap.getD sid false
            { modelState with fds := assocSet modelState.fds hid (endpointWithBuf sc true true sh se sw sf) }
          | none => modelState
        let s2 :=
          match symMap.get? peerSid with
          | some pHid =>
            match assocGet s1.fds pHid with
            | some _ =>
              let ph := hupMap.getD peerSid false
              let pe := errMap.getD peerSid false
              let pw := !(wm.getD peerSid false)
              let pf := finMap.getD peerSid false
              { s1 with fds := assocSet s1.fds pHid (endpointWithBuf cnt true true ph pe pw pf) }
            | none => s1
          | none => s1
        return .ok (symMap, symKindMap, rawMap, openMap, bm, hupMap, errMap, finMap, wm, curNofile, s2, none)
    | _, _ => return .ok stay
  | .streamDrain sid =>
    match symMap.get? sid, streamPeerInfo symKindMap sid with
    | some hid, some (peerSid, true) =>
      match rawMap.get? hid with
      | none => return .ok stay
      | some rfd =>
        let isTcp := match symKindMap.get? sid with | some (.tcpEnd _) => true | _ => false
        let isSeq := match symKindMap.get? sid with | some (.seqEnd _) => true | _ => false
        let mut hitEagain := false
        let mut sawDrainEnd := false
        let mut drained : Nat := 0
        let mut errCleared := errMap.getD sid false
        let mut sawReset := false
        for _ in [:512] do
          match ← rawRecvDontwait rfd 65536 0 with
          | .ok n =>
            if n == 0 then
              sawDrainEnd := true
              break
            drained := drained + (if isSeq then 1 else n.toNat)
          | .error e =>
            if e == Errno.EAGAIN then
              hitEagain := true
              sawDrainEnd := true
            else if e == Errno.ECONNRESET then
              errCleared := false
              sawReset := true
              sawDrainEnd := true
            break
        if isTcp && hitEagain then
          match symMap.get? peerSid with
          | some pHid =>
            if openMap.contains pHid then
              match rawMap.get? pHid with
              | some peerRfd =>
                let _ ← ops.ppoll #[(peerRfd, { pollout := true })] (some { sec := 0, nsec := 50000000 })
              | none => pure ()
          | none => pure ()
        let prevCnt := bufMap.getD sid 0
        let newCnt := if sawDrainEnd then 0 else prevCnt - min prevCnt drained
        let bm := bufMap.insert sid newCnt
        let em := errMap.insert sid errCleared
        let hm := if isTcp && sawReset then hupMap.insert sid true else hupMap
        let fm := if isTcp && sawReset then finMap.insert sid true else finMap
        let wm := if hitEagain then wrFullMap.insert peerSid false else wrFullMap
        let s1 :=
          match assocGet modelState.fds hid with
          | some _ =>
            let sh := hm.getD sid false
            let sw := !(wm.getD sid false)
            let sf := fm.getD sid false
            { modelState with fds := assocSet modelState.fds hid (endpointWithBuf newCnt true true sh errCleared sw sf) }
          | none => modelState
        let s2 :=
          if !hitEagain then s1
          else
            match symMap.get? peerSid with
            | some pHid =>
              match assocGet s1.fds pHid with
              | some _ =>
                let pc := bm.getD peerSid 0
                let ph := hm.getD peerSid false
                let pe := em.getD peerSid false
                let pf := fm.getD peerSid false
                { s1 with fds := assocSet s1.fds pHid (endpointWithBuf pc true true ph pe true pf) }
              | none => s1
            | none => s1
        return .ok (symMap, symKindMap, rawMap, openMap, bm, hm, em, fm, wm, curNofile, s2, none)
    | _, _ => return .ok stay
  | .setSoftNofile lim =>
    let target := if lim == 0 then origNofile else lim
    match ← rawRlimitNofile 1 target with
    | .ok actual =>
      let s' := { modelState with softNofile? := some actual.toNat }
      return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, actual, s', none)
    | .error _ => return .ok stay
  | .close sid =>
    match symMap.get? sid with
    | none => return .ok stay
    | some hid =>
      match rawMap.get? hid with
      | none => return .ok stay
      | some rfd =>
        let _ ← rawPollClose rfd
        match modelState.closeHandle hid with
        | .ok s1 =>
          let (s2, hm2, em2, fm2, wm2) := applyStreamCloseSideEffects s1 symKindMap symMap bufMap hupMap errMap finMap wrFullMap sid
          return .ok (symMap, symKindMap, rawMap, openMap.erase hid, bufMap, hm2, em2, fm2, wm2, curNofile, s2, none)
        | .error _ =>
          return .ok (symMap, symKindMap, rawMap, openMap.erase hid, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, modelState, none)
  | .ppoll entries timeout armAlrm =>
    let mut modelPairs : Array (HandleId × PollEvents) := #[]
    let mut realPairs : Array (RawFd × PollEvents) := #[]
    let mut missing := false
    for (sid, ev) in entries do
      match symMap.get? sid with
      | none => missing := true
      | some hid =>
        match rawMap.get? hid with
        | none => missing := true
        | some rfd =>
          modelPairs := modelPairs.push (hid, ev)
          realPairs := realPairs.push (rfd, ev)
    if missing then
      return .ok stay
    let isLongTimeout := match timeout with
      | none => true
      | some ts => ts.isValid && (ts.sec > 0 || ts.nsec > 50000000)
    if guardHang && !armAlrm && isLongTimeout && entries.size.toUInt64 <= curNofile && !modelState.ambientSeccomp then
      let wouldBlock :=
        match evalPollList modelState modelPairs.toList with
        | .error _ => false
        | .ok revs => !(revs.any (fun ev => !ev.isEmpty))
      if wouldBlock then
        return .ok stay
    let req : PollReq := .ppoll modelPairs timeout
    if armAlrm then rawArmSigalrm 1500 0
    let res ← ops.ppoll realPairs timeout
    if armAlrm then rawDisarmSigalrm 0
    let out :=
      match res with
      | .ok revs => .polled revs
      | .error e => .err e
    match stepModel modelState req out with
    | none =>
      let reqStr := match req with
        | .ppoll es to => if es.size > 32 then s!"ppoll(entries={es.size}, to={repr to})" else s!"{repr req}"
        | _ => s!"{repr req}"
      return .error s!"mismatch on ppoll: req={reqStr} out={repr out}"
    | some s' => return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', some ("ppoll", out))
  | .ppollOverMaxCap sid timeout =>
    match symMap.get? sid >>= rawMap.get?, symMap.get? sid with
    | some rfd, some hid =>
      let cap := MAX_POLL_NFDS + 1
      let realPairs := Array.replicate cap (rfd, { pollin := true })
      let modelPairs := Array.replicate cap (hid, { pollin := true })
      let req : PollReq := .ppoll modelPairs timeout
      let res ← ops.ppoll realPairs timeout
      let out :=
        match res with
        | .ok revs => .polled revs
        | .error e => .err e
      match stepModel modelState req out with
      | none =>
        return .error s!"mismatch on ppollOverMaxCap: entries={cap} out={repr out}"
      | some s' =>
        return .ok (symMap, symKindMap, rawMap, openMap, bufMap, hupMap, errMap, finMap, wrFullMap, curNofile, s', some ("ppoll", out))
    | _, _ => return .ok stay

/-- Result of replaying a symbolic `Poll` trace. -/
structure ReplayResult where
  /-- Step index of the first oracle mismatch, if any. -/
  mismatchIdx : Option Nat
  /-- Human-readable mismatch message, if any. -/
  mismatchMsg : Option String

/-- Replay a deterministic `Array SymStep` trace against real `defaultOps` and `stepModel`. -/
def replayTrace (trace : Array SymStep)
    (stepModel : PollState → PollReq → PollOutcome → Option PollState := allowedStep)
    (guardHang : Bool := true) :
    IO ReplayResult := do
  let ops := defaultOps
  let origNofile ← match ← rawRlimitNofile 0 0 with
    | .ok v => pure v
    | .error _ => pure 1024
  let mut curNofile := origNofile
  let mut symMap : Std.HashMap SymFd HandleId := {}
  let mut symKindMap : Std.HashMap SymFd SymKind := {}
  let mut rawMap : Std.HashMap HandleId RawFd := {}
  let mut openMap : Std.HashMap HandleId RawFd := {}
  let mut bufMap : Std.HashMap SymFd Nat := {}
  let mut hupMap : Std.HashMap SymFd Bool := {}
  let mut errMap : Std.HashMap SymFd Bool := {}
  let mut finMap : Std.HashMap SymFd Bool := {}
  let mut wrFullMap : Std.HashMap SymFd Bool := {}
  let mut modelState := { PollState.initial with softNofile? := some origNofile.toNat }
  try
    for h : idx in [:trace.size] do
      let step := trace[idx]
      match ← execOneStep ops origNofile symMap symKindMap rawMap openMap bufMap hupMap errMap finMap wrFullMap curNofile modelState step stepModel guardHang with
      | .error msg =>
        return { mismatchIdx := some idx, mismatchMsg := some msg }
      | .ok (sm, sk, rm, om, bm, hm, em, fm, wm, cn, s', _) =>
        symMap := sm
        symKindMap := sk
        rawMap := rm
        openMap := om
        bufMap := bm
        hupMap := hm
        errMap := em
        finMap := fm
        wrFullMap := wm
        curNofile := cn
        modelState := s'
    return { mismatchIdx := none, mismatchMsg := none }
  finally
    let _ ← rawRlimitNofile 1 origNofile
    closeOpenFds openMap

private def remapSym (m : Std.HashMap SymFd SymFd) (s : SymFd) : Option SymFd :=
  m.get? s

private def normalizeTrace (raw : Array SymStep) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  let mut remap : Std.HashMap SymFd SymFd := {}
  let mut nextId : SymFd := 0
  for step in raw do
    match step.req with
    | .eventfd2 initval flags =>
      match step.allocIds[0]? with
      | none => pure ()
      | some oldId =>
        let newId := nextId
        nextId := nextId + 1
        remap := remap.insert oldId newId
        out := out.push { allocIds := #[newId], req := .eventfd2 initval flags }
    | .openKind kind =>
      match step.allocIds[0]? with
      | none => pure ()
      | some oldId =>
        let newId := nextId
        nextId := nextId + 1
        remap := remap.insert oldId newId
        out := out.push { allocIds := #[newId], req := .openKind kind }
    | .openPipe =>
      match step.allocIds[0]?, step.allocIds[1]? with
      | some oldR, some oldW =>
        let newR := nextId
        let newW := nextId + 1
        nextId := nextId + 2
        remap := (remap.insert oldR newR).insert oldW newW
        out := out.push { allocIds := #[newR, newW], req := .openPipe }
      | _, _ => pure ()
    | .openSockpair =>
      match step.allocIds[0]?, step.allocIds[1]? with
      | some old0, some old1 =>
        let new0 := nextId
        let new1 := nextId + 1
        nextId := nextId + 2
        remap := (remap.insert old0 new0).insert old1 new1
        out := out.push { allocIds := #[new0, new1], req := .openSockpair }
      | _, _ => pure ()
    | .openSeqpair =>
      match step.allocIds[0]?, step.allocIds[1]? with
      | some old0, some old1 =>
        let new0 := nextId
        let new1 := nextId + 1
        nextId := nextId + 2
        remap := (remap.insert old0 new0).insert old1 new1
        out := out.push { allocIds := #[new0, new1], req := .openSeqpair }
      | _, _ => pure ()
    | .openTcpPair =>
      match step.allocIds[0]?, step.allocIds[1]? with
      | some old0, some old1 =>
        let new0 := nextId
        let new1 := nextId + 1
        nextId := nextId + 2
        remap := (remap.insert old0 new0).insert old1 new1
        out := out.push { allocIds := #[new0, new1], req := .openTcpPair }
      | _, _ => pure ()
    | .openUdpPair =>
      match step.allocIds[0]?, step.allocIds[1]? with
      | some old0, some old1 =>
        let new0 := nextId
        let new1 := nextId + 1
        nextId := nextId + 2
        remap := (remap.insert old0 new0).insert old1 new1
        out := out.push { allocIds := #[new0, new1], req := .openUdpPair }
      | _, _ => pure ()
    | .openTcpListener =>
      match step.allocIds[0]? with
      | none => pure ()
      | some oldId =>
        let newId := nextId
        nextId := nextId + 1
        remap := remap.insert oldId newId
        out := out.push { allocIds := #[newId], req := .openTcpListener }
    | .openUdpSocket =>
      match step.allocIds[0]? with
      | none => pure ()
      | some oldId =>
        let newId := nextId
        nextId := nextId + 1
        remap := remap.insert oldId newId
        out := out.push { allocIds := #[newId], req := .openUdpSocket }
    | .efdWrite sid delta =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .efdWrite ns delta }
    | .efdRead sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .efdRead ns }
    | .streamWrite1 sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .streamWrite1 ns }
    | .streamRead1 sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .streamRead1 ns }
    | .streamSaturate sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .streamSaturate ns }
    | .streamDrain sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .streamDrain ns }
    | .setSoftNofile lim =>
      out := out.push { allocIds := #[], req := .setSoftNofile lim }
    | .close sid =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .close ns }
    | .ppoll entries ts armAlrm =>
      let mapped? := entries.mapM fun (sid, ev) => (remapSym remap sid).map (fun ns => (ns, ev))
      if let some mapped := mapped? then
        out := out.push { allocIds := #[], req := .ppoll mapped ts armAlrm }
    | .ppollOverMaxCap sid ts =>
      if let some ns := remapSym remap sid then
        out := out.push { allocIds := #[], req := .ppollOverMaxCap ns ts }
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

private def shrinkPollEventsCands (ev : PollEvents) : Array PollEvents := Id.run do
  let mut cands : Array PollEvents := #[]
  let pushIfNew := fun (arr : Array PollEvents) (e : PollEvents) =>
    if e != ev && !arr.contains e then arr.push e else arr
  cands := pushIfNew cands {}
  if ev.pollin then cands := pushIfNew cands { pollin := true }
  if ev.pollout then cands := pushIfNew cands { pollout := true }
  if ev.pollerr then cands := pushIfNew cands { pollerr := true }
  if ev.pollhup then cands := pushIfNew cands { pollhup := true }
  if ev.pollnval then cands := pushIfNew cands { pollnval := true }
  return cands

private def shrinkParamCands (st : SymStep) : Array SymReq := Id.run do
  let mut cands : Array SymReq := #[]
  match st.req with
  | .ppoll entries to armAlrm =>
    if armAlrm then
      cands := cands.push (.ppoll entries to false)
    if let some ts := to then
      cands := cands.push (.ppoll entries none armAlrm)
      if ts.sec != 0 || ts.nsec != 0 then
        cands := cands.push (.ppoll entries (some { sec := 0, nsec := 0 }) armAlrm)
    if !entries.isEmpty then
      cands := cands.push (.ppoll #[] to armAlrm)
      if entries.size > 1 then
        let mid := entries.size / 2
        cands := cands.push (.ppoll (entries.take mid) to armAlrm)
        cands := cands.push (.ppoll (entries.extract mid entries.size) to armAlrm)
        for i in [:entries.size] do
          cands := cands.push (.ppoll (entries.eraseIdxIfInBounds i) to armAlrm)
      for h : i in [:entries.size] do
        let (sid, ev) := entries[i]
        for ev' in shrinkPollEventsCands ev do
          cands := cands.push (.ppoll (entries.set i (sid, ev')) to armAlrm)
  | .efdWrite sid delta =>
    if delta > 1 then
      cands := cands.push (.efdWrite sid 1)
      cands := cands.push (.efdWrite sid (delta / 2))
  | .eventfd2 initval flags =>
    if initval > 1 then
      cands := cands.push (.eventfd2 0 flags)
      cands := cands.push (.eventfd2 1 flags)
      if initval > 2 then
        cands := cands.push (.eventfd2 (initval / 2) flags)
    else if initval == 1 then
      cands := cands.push (.eventfd2 0 flags)
    if flags.semaphore then
      cands := cands.push (.eventfd2 initval { flags with semaphore := false })
  | .ppollOverMaxCap sid (some ts) =>
    cands := cands.push (.ppollOverMaxCap sid none)
    if ts.sec != 0 || ts.nsec != 0 then
      cands := cands.push (.ppollOverMaxCap sid (some { sec := 0, nsec := 0 }))
  | _ => pure ()
  return cands

/-- Greedy delta-minimization + parameter shrinker with handle-ID compaction for `Poll` fuzz traces. -/
def shrinkTrace (trace : Array SymStep) (reproduces : Array SymStep → IO Bool) :
    IO (Array SymStep) := do
  let mut cur ← deltaShrink (normalizeTrace trace) Array.size dropRange reproduces
  let mut pairChanged := true
  while pairChanged && cur.size <= 128 do
    pairChanged := false
    let n := cur.size
    let mut i := 0
    while !pairChanged && i < n do
      let mut j := i + 1
      while !pairChanged && j < n do
        let cand := dropTwo cur i j
        if cand.size < cur.size then
          if ← reproduces cand then
            cur ← deltaShrink cand Array.size dropRange reproduces
            pairChanged := true
        j := j + 1
      i := i + 1
  let mut changed := true
  while changed do
    changed := false
    for idx in [:cur.size] do
      if let some st := cur[idx]? then
        for req' in shrinkParamCands st do
          let cand := normalizeTrace (cur.set! idx { st with req := req' })
          if ← reproduces cand then
            cur ← deltaShrink cand Array.size dropRange reproduces
            changed := true
            break
      if changed then
        break
  return cur

private def extractPollOut? (s : String) : Option String :=
  match s.splitOn " out=" with
  | [_, rest] =>
    let flat := " ".intercalate ((rest.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))
    some flat
  | _ => none

private def samePollOut (a b : String) : Bool :=
  if a == b then true
  else
    let norm := fun (s : String) => s.replace "LeanSwe.LinuxSyscall.Poll." ""
    let na := norm a
    let nb := norm b
    let hasStem := fun (s stem : String) => s == stem || s.startsWith (stem ++ " ")
    (hasStem na "PollOutcome.opened" && hasStem nb "PollOutcome.opened") ||
      (hasStem na "PollOutcome.polled" && hasStem nb "PollOutcome.polled")

private def matchesPollMismatch (wantPrefix : String) (wantOut? : Option String) (mm : String) : Bool :=
  mm.startsWith wantPrefix &&
    match wantOut?, extractPollOut? mm with
    | none, _ => true
    | some w, some g => samePollOut w g
    | some _, none => false

/-- Summary report produced by `runPollFuzz`. -/
structure FuzzReport where
  /-- Executed `eventfd2` + `ppoll` syscalls. -/
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

/-- Verify greedy delta-minimization and handle-ID compaction on a generated trace with a synthetic fault. -/
def runShrinkSelfTest : IO String := do
  let mut rng := Rng.seed 0x504f4c4c5348524b
  let mut rawTrace : Array SymStep := #[]
  let mut nextId : SymFd := 0
  for i in [:12] do
    if i == 3 || i == 7 then
      let sid := nextId
      nextId := nextId + 1
      let (iv, r1) := rng.nextRange 1 9
      rng := r1
      rawTrace := rawTrace.push { allocIds := #[sid], req := .eventfd2 (UInt32.ofNat iv) { nonblock := true, cloexec := true } }
      rawTrace := rawTrace.push { allocIds := #[], req := .ppoll #[(sid, { pollin := true })] (some { sec := 0, nsec := 0 }) }
    else
      let sid := nextId
      nextId := nextId + 1
      rawTrace := rawTrace.push { allocIds := #[sid], req := .eventfd2 0 { nonblock := true, cloexec := true } }
      rawTrace := rawTrace.push { allocIds := #[], req := .close sid }
  let faultModel : PollState → PollReq → PollOutcome → Option PollState := fun st req out =>
    match req, out with
    | .ppoll entries _, .polled revs =>
      if entries.size == 1 && revs == #[{ pollin := true }] then
        match st.fds.reverse.head? with
        | some (_, d) =>
          match d.kind with
          | .eventfd cnt _ => if cnt > 0 then none else allowedStep st req out
          | _ => allowedStep st req out
        | none => allowedStep st req out
      else allowedStep st req out
    | _, _ => allowedStep st req out
  let reproduces : Array SymStep → IO Bool := fun cand => do
    let r ← replayTrace cand faultModel
    return r.mismatchIdx.isSome
  if !(← reproduces rawTrace) then
    throw (IO.userError "poll shrink self-test: baseline fault did not trigger")
  let shrunk ← shrinkTrace rawTrace reproduces
  if shrunk.size != 2 then
    throw (IO.userError s!"poll shrink self-test: expected minimal size 2, got {shrunk.size} ({repr shrunk})")
  let firstAlloc := (shrunk.getD 0 { allocIds := #[], req := .openPipe }).allocIds
  if firstAlloc != #[0] then
    throw (IO.userError s!"poll shrink self-test: expected renumbered handle #[0], got {repr firstAlloc}")
  let mut noneRaw : Array SymStep := #[]
  for j in [:6] do
    let sid := j
    noneRaw := noneRaw.push { allocIds := #[sid], req := .eventfd2 0 { nonblock := true, cloexec := true } }
    if j == 2 then
      noneRaw := noneRaw.push { allocIds := #[], req := .efdWrite sid 3 }
      noneRaw := noneRaw.push { allocIds := #[], req := .ppoll #[(sid, { pollin := true })] none }
    else
      noneRaw := noneRaw.push { allocIds := #[], req := .close sid }
  let noneShrunk ← shrinkTrace noneRaw fun cand => do
    let r ← replayTrace cand faultModel
    return r.mismatchIdx.isSome
  if noneShrunk.size != 3 then
    throw (IO.userError s!"poll shrink timeout=none self-test: expected size 3, got {noneShrunk.size} ({repr noneShrunk})")
  let mut longRaw : Array SymStep := #[]
  for j in [:4] do
    let sid := j
    longRaw := longRaw.push { allocIds := #[sid], req := .eventfd2 0 { nonblock := true, cloexec := true } }
    if j == 2 then
      longRaw := longRaw.push { allocIds := #[], req := .efdWrite sid 1 }
      longRaw := longRaw.push { allocIds := #[], req := .ppoll #[(sid, { pollin := true })] (some { sec := 0x7fffffffffffffff, nsec := 999999999 }) }
    else
      longRaw := longRaw.push { allocIds := #[], req := .close sid }
  let longShrunk ← shrinkTrace longRaw fun cand => do
    let r ← replayTrace cand faultModel
    return r.mismatchIdx.isSome
  if longShrunk.size != 3 then
    throw (IO.userError s!"poll shrink long-timeout self-test: expected size 3, got {longShrunk.size} ({repr longShrunk})")
  let multiRaw : Array SymStep :=
    #[ { allocIds := #[0, 1], req := .openPipe }
     , { allocIds := #[2], req := .eventfd2 1 { nonblock := true, cloexec := true } }
     , { allocIds := #[], req := .ppoll #[(0, { pollin := true, pollout := true }), (2, { pollin := true, pollout := true })] (some { sec := 0, nsec := 0 }) true }
     ]
  let multiFault : PollState → PollReq → PollOutcome → Option PollState := fun st req out =>
    match req, out with
    | .ppoll entries _, .polled revs =>
      if entries.size >= 1 && revs.any (·.pollin) then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let multiInit ← replayTrace multiRaw multiFault
  let multiMsg ← match multiInit.mismatchMsg with
    | some m => pure m
    | none => throw (IO.userError "poll shrink multi-entry self-test: baseline fault did not trigger")
  let multiPrefix := ((multiMsg.splitOn ":").headD multiMsg).trimAscii.toString
  let multiWantOut? := extractPollOut? multiMsg
  let multiShrunk ← shrinkTrace multiRaw fun cand => do
    let r ← replayTrace cand multiFault
    return (r.mismatchMsg.map (matchesPollMismatch multiPrefix multiWantOut?)).getD false
  if multiShrunk.size != 2 then
    throw (IO.userError s!"poll shrink multi-entry self-test: expected size 2, got {multiShrunk.size} ({repr multiShrunk})")
  match (multiShrunk.getD 1 { allocIds := #[], req := .openPipe }).req with
  | .ppoll #[(0, { pollin := true, pollout := false, pollerr := false, pollhup := false, pollnval := false })] none false => pure ()
  | other => throw (IO.userError s!"poll shrink multi-entry self-test: expected single pollin entry without timeout/alarm, got {repr other}")
  let wrapRaw : Array SymStep :=
    #[ { allocIds := #[0], req := .eventfd2 0xffffffff { nonblock := true, cloexec := true, semaphore := true } }
     , { allocIds := #[1], req := .eventfd2 7 { nonblock := true, cloexec := true } }
     , { allocIds := #[], req := .ppoll #[(0, { pollin := true, pollout := true }), (1, { pollin := true, pollout := true })] (some { sec := 0, nsec := 0 }) false }
     ]
  let wrapFault : PollState → PollReq → PollOutcome → Option PollState := fun st req out =>
    match req, out with
    | .ppoll _ (some _), .polled _ => none
    | _, _ => allowedStep st req out
  let wrapInit ← replayTrace wrapRaw wrapFault
  let wrapMsg ← match wrapInit.mismatchMsg with
    | some m => pure m
    | none => throw (IO.userError "poll shrink wrap self-test: baseline fault did not trigger")
  let wrapPrefix := ((wrapMsg.splitOn ":").headD wrapMsg).trimAscii.toString
  let wrapWantOut? := extractPollOut? wrapMsg
  let wrapShrunk ← shrinkTrace wrapRaw fun cand => do
    let r ← replayTrace cand wrapFault
    return (r.mismatchMsg.map (matchesPollMismatch wrapPrefix wrapWantOut?)).getD false
  if wrapShrunk.size != 1 then
    throw (IO.userError s!"poll shrink wrap->empty self-test: expected size 1, got {wrapShrunk.size} ({repr wrapShrunk})")
  let overCapRaw : Array SymStep :=
    #[ { allocIds := #[0], req := .eventfd2 0 { nonblock := true, cloexec := true } }
     , { allocIds := #[], req := .ppollOverMaxCap 0 (some { sec := 5, nsec := 123 }) }
     ]
  let overCapFault : PollState → PollReq → PollOutcome → Option PollState := fun st req out =>
    match req, out with
    | .ppoll entries _, _ =>
      if entries.size > MAX_POLL_NFDS then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let overCapShrunk ← shrinkTrace overCapRaw fun cand => do
    let r ← replayTrace cand overCapFault
    return r.mismatchIdx.isSome
  match (overCapShrunk.getD 1 { allocIds := #[], req := .openPipe }).req with
  | .ppollOverMaxCap 0 none => pure ()
  | other => throw (IO.userError s!"poll shrink overCap timeout self-test: expected timeout=none, got {repr other}")
  return s!"shrunk {rawTrace.size}->{shrunk.size} steps (+ timeout=none {noneRaw.size}->{noneShrunk.size}, timeout=max {longRaw.size}->{longShrunk.size}, multi={multiRaw.size}->{multiShrunk.size}, wrap={wrapRaw.size}->{wrapShrunk.size}, overCap) verified"

private def runEventfdInitvalProbe : IO Unit := do
  let ops := defaultOps
  for iv in #[0, 1, 101, 0x7fffffff, 0x80000000, 0xffffffff] do
    let fl : EventFdFlags := { nonblock := true, cloexec := true, semaphore := false }
    let rfd ← match ← ops.eventfd2 iv fl with
      | .ok fd => pure fd
      | .error e => throw (IO.userError s!"poll eventfd2 initval={iv} probe failed: {e}")
    try
      let st0 := PollState.initial
      let some (.opened hid, st1) := stepPollCore st0 (.eventfd2 iv fl) none
        | throw (IO.userError "poll eventfd2 initval model step failed")
      match ← rawEfdRead rfd, st1.eventfdConsume hid with
      | .ok gotV, .ok (expV, _) =>
        if gotV != expV then
          throw (IO.userError s!"poll eventfd2 initval={iv} readback mismatch: expected={expV} got={gotV}")
      | .error gotE, .error expE =>
        if gotE != expE then
          throw (IO.userError s!"poll eventfd2 initval={iv} err mismatch: expected={expE} got={gotE}")
      | got, exp =>
        throw (IO.userError s!"poll eventfd2 initval={iv} outcome mismatch: expected={repr exp} got={repr got}")
    finally
      let _ ← rawPollClose rfd

/-- Verify `SIGALRM` without `SA_RESTART` interrupts blocking `ppoll` with `Errno.EINTR` matching `allowedStep` (including 64-bit `tv_sec >= 2^32`). -/
def runSigalrmEintrProbe : IO Unit := do
  let ops := defaultOps
  let efd ← match ← ops.eventfd2 0 { nonblock := true, cloexec := true } with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"poll sigalrm probe eventfd2 failed: {e}")
  let (hid, st) := PollState.initial.registerDesc { kind := .eventfd 0 { nonblock := true, cloexec := true } }
  try
    for ts in #[none, some { sec := 2, nsec := 0 }, some { sec := 0x100000000, nsec := 0 }] do
      rawArmSigalrm 5000 0
      let res ← ops.ppoll #[(efd, { pollin := true })] ts
      rawDisarmSigalrm 0
      match res with
      | .error e =>
        if e != Errno.EINTR then
          throw (IO.userError s!"poll sigalrm probe expected EINTR, got {e}")
        let req : PollReq := .ppoll #[(hid, { pollin := true })] ts
        if (allowedStep st req (.err e)).isNone then
          throw (IO.userError s!"poll sigalrm probe model rejected EINTR on {repr ts}")
      | .ok revs =>
        throw (IO.userError s!"poll sigalrm probe expected EINTR, got {repr revs}")
  finally
    rawDisarmSigalrm 0
    let _ ← rawPollClose efd

private def installPollSeccompFilter (expected : Errno) : IO Unit := do
  match ← SandboxEnv.setNoNewPrivs with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"poll seccomp PR_SET_NO_NEW_PRIVS failed: {e}")
  let bpf := SandboxEnv.encodeSeccompErrnoBpf #[271, 290] #[73, 19] expected
  match ← SandboxEnv.installRawSeccomp bpf with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"poll seccomp installRawSeccomp failed: {e}")

private def execPollSeccompChecks (expected : Errno) (nSteps : Nat) (seed : UInt64) : IO HitStats := do
  let ops := defaultOps
  let closedBox ← match ← ops.eventfd2 0 { nonblock := true, cloexec := true } with
    | .ok fd =>
      let _ ← rawPollClose fd
      pure fd
    | .error e => throw (IO.userError s!"poll seccomp pre-open eventfd2 failed: {e}")
  installPollSeccompFilter expected
  let st : PollState := { PollState.initial with ambientSeccomp := true }
  let (stWithClosed, closedHid) :=
    let (h, s1) := st.registerDesc { kind := .eventfd 0 { nonblock := true, cloexec := true } }
    match s1.closeHandle h with
    | .ok s2 => (s2, h)
    | .error _ => (s1, h)
  let mut stats : HitStats := {}
  let mut rng := Rng.seed seed
  for i in [:nSteps] do
    let (pick, r1) := rng.nextNat 4
    rng := r1
    if pick == 0 then
      let (iv, fl, r2) := genEventfdInit rng
      rng := r2
      let req : PollReq := .eventfd2 iv fl
      match ← ops.eventfd2 iv fl with
      | .error e =>
        if e != expected then
          throw (IO.userError s!"poll seccomp eventfd2 expected {expected}, got {e}")
        if (allowedStep st req (.err e)).isNone then
          throw (IO.userError s!"poll seccomp model rejected eventfd2 err={e}")
        stats := stats.record "eventfd2" (.err e)
      | .ok fd =>
        let _ ← rawPollClose fd
        throw (IO.userError "poll seccomp eventfd2 unexpectedly succeeded")
    else if pick == 1 then
      let ts : Option Timespec := some { sec := -1, nsec := 0 }
      let req : PollReq := .ppoll #[] ts
      match ← ops.ppoll #[] ts with
      | .error e =>
        if e != Errno.EINVAL then
          throw (IO.userError s!"poll seccomp invalid timespec expected EINVAL, got {e}")
        if (allowedStep st req (.err e)).isNone then
          throw (IO.userError "poll seccomp model rejected preCheck EINVAL")
        stats := stats.record "ppoll" (.err e)
      | .ok _ => throw (IO.userError "poll seccomp invalid timespec unexpectedly succeeded")
    else if pick == 2 then
      let ts : Option Timespec := some { sec := 0, nsec := 0 }
      let req : PollReq := .ppoll #[(closedHid, { pollin := true })] ts
      match ← ops.ppoll #[(closedBox, { pollin := true })] ts with
      | .error e =>
        if e != Errno.EBADF then
          throw (IO.userError s!"poll seccomp closed fd expected EBADF, got {e}")
        if (allowedStep stWithClosed req (.err e)).isNone then
          throw (IO.userError "poll seccomp model rejected closed LeanFdBox EBADF")
        stats := stats.record "ppoll" (.err e)
      | .ok _ => throw (IO.userError "poll seccomp closed fd unexpectedly succeeded")
    else
      let ts : Option Timespec := if i % 2 == 0 then none else some { sec := 0, nsec := 1000 }
      let req : PollReq := .ppoll #[] ts
      match ← ops.ppoll #[] ts with
      | .error e =>
        if e != expected then
          throw (IO.userError s!"poll seccomp ppoll expected {expected}, got {e}")
        if (allowedStep st req (.err e)).isNone then
          throw (IO.userError s!"poll seccomp model rejected ppoll err={e}")
        stats := stats.record "ppoll" (.err e)
      | .ok revs =>
        throw (IO.userError s!"poll seccomp ppoll unexpectedly succeeded: {repr revs}")
  return stats

/-- Verify `Poll.allowedStep` under an outer `SECCOMP_RET_ERRNO` filter returning `expected`. -/
def runSeccompWorker (expected : Errno) : IO Unit := do
  let _ ← execPollSeccompChecks expected 12 0x504f4c4c53454343

private def runPollSeccompSubEpisodes (seed : UInt64) : IO (List (String × Nat)) := do
  let mut merged : List (String × Nat) := []
  for (expected, idx) in #[(Errno.EPERM, 0), (Errno.EACCES, 1)] do
    let (st, payload) ← SandboxEnv.runForked do
      let s ← execPollSeccompChecks expected 32 (seed ^^^ UInt64.ofNat (idx + 1))
      let mut out := ""
      for (k, v) in s.counts.toList do
        out := out ++ s!"{k}={v}\n"
      return out.toUTF8
    if st != 0 then
      throw (IO.userError s!"poll seccomp forked sub-episode failed with wait status {st}")
    merged := merged ++ SandboxEnv.decodeHitCounts payload
  return merged

@[noinline] private def allocFuzzPipeWriteDroppingReadFd0 : IO RawFd := do
  match ← rawOpenPipe with
  | .ok (pr, pw) =>
    let rawPr ← SandboxEnv.peekRawFd pr
    if rawPr != 0 then
      let _ ← rawPollClose pr
      let _ ← rawPollClose pw
      throw (IO.userError s!"poll fd0 pipe read expected 0, got {rawPr}")
    return pw
  | .error e => throw (IO.userError s!"poll fd0 rawOpenPipe failed: {e}")

private def runPollFdZeroProbe : IO Unit := do
  let (st, payload) ← SandboxEnv.runForked do
    SandboxEnv.closeRaw 0
    let ops := defaultOps
    let zfd ← match ← ops.eventfd2 5 { nonblock := true, cloexec := true } with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"poll fd0 eventfd2 failed: {e}")
    let rawZ ← SandboxEnv.peekRawFd zfd
    if rawZ != 0 then
      let _ ← rawPollClose zfd
      throw (IO.userError s!"poll fd0 expected raw 0, got {rawZ}")
    match ← ops.ppoll #[(zfd, { pollin := true, pollout := true })] (some { sec := 0, nsec := 0 }) with
    | .ok rev =>
      if rev != #[{ pollin := true, pollout := true }] then
        let _ ← rawPollClose zfd
        throw (IO.userError s!"poll fd0 revents mismatch: {repr rev}")
    | .error e =>
      let _ ← rawPollClose zfd
      throw (IO.userError s!"poll fd0 ppoll failed: {e}")
    match ← rawPollClose zfd with
    | .ok () => pure ()
    | .error e => throw (IO.userError s!"poll fd0 close failed: {e}")
    let pwFin ← allocFuzzPipeWriteDroppingReadFd0
    match ← ops.ppoll #[(pwFin, { pollout := true })] (some { sec := 0, nsec := 0 }) with
    | .ok rev =>
      let _ ← rawPollClose pwFin
      if rev != #[{ pollout := true, pollerr := true }] then
        throw (IO.userError s!"poll fd0 finalizer expected POLLOUT+POLLERR, got {repr rev}")
    | .error e =>
      let _ ← rawPollClose pwFin
      throw (IO.userError s!"poll fd0 finalizer ppoll failed: {e}")
    return "OK".toUTF8
  if st != 0 || String.fromUTF8! payload != "OK" then
    throw (IO.userError s!"poll fd0 probe failed (status={st}, payload={String.fromUTF8! payload})")

/-- Execute stateful `Poll` world fuzzing across `totalSteps` real `eventfd2` and `ppoll` syscalls. -/
def runPollFuzz (totalSteps : Nat) (seed : UInt64 := 0x504f4c4c46555a5a)
    (selfTestShrink : Bool := false) : IO FuzzReport := do
  let shrinkDetail ← if selfTestShrink then runShrinkSelfTest else pure ""
  if totalSteps >= 100 then
    runEventfdInitvalProbe
    runSigalrmEintrProbe
    runPollFdZeroProbe
  let startNs ← IO.monoNanosNow
  let ops := defaultOps
  let origNofile ← match ← rawRlimitNofile 0 0 with
    | .ok v => pure v
    | .error _ => pure 1024
  let mut rng := Rng.seed seed
  let mut stats : HitStats := {}
  if totalSteps >= 500 then
    let _ ← runPollSeccompSubEpisodes seed
  let mut epIdx : Nat := 0
  while stats.totalSteps < totalSteps do
    let remaining := totalSteps - stats.totalSteps
    let (epLenRaw, rLen) := rng.nextNat 101
    rng := rLen
    let epLen := min (max remaining 1) (40 + epLenRaw)
    let mut modelState := { PollState.initial with softNofile? := some origNofile.toNat }
    let mut env : GenEnv := {}
    let mut symMap : Std.HashMap SymFd HandleId := {}
    let mut symKindMap : Std.HashMap SymFd SymKind := {}
    let mut rawMap : Std.HashMap HandleId RawFd := {}
    let mut openMap : Std.HashMap HandleId RawFd := {}
    let mut bufMap : Std.HashMap SymFd Nat := {}
    let mut hupMap : Std.HashMap SymFd Bool := {}
    let mut errMap : Std.HashMap SymFd Bool := {}
    let mut finMap : Std.HashMap SymFd Bool := {}
    let mut wrFullMap : Std.HashMap SymFd Bool := {}
    let mut curNofile := origNofile
    let mut trace : Array SymStep := #[]
    let mut nextSym : SymFd := 0
    try
      let mut epSyscalls := 0
      for stepIdx in [:epLen * 3] do
        if epSyscalls >= epLen || stats.totalSteps >= totalSteps then
          break
        let (sreq, rNext) := genSymReq rng env modelState origNofile curNofile
        rng := rNext
        let nAlloc := isAllocReq sreq
        let mut allocIds : Array SymFd := #[]
        for _ in [:nAlloc] do
          allocIds := allocIds.push nextSym
          nextSym := nextSym + 1
        let step : SymStep := { allocIds, req := sreq }
        trace := trace.push step
        match ← execOneStep ops origNofile symMap symKindMap rawMap openMap bufMap hupMap errMap finMap wrFullMap curNofile modelState step with
        | .error msg =>
          let _ ← rawRlimitNofile 1 origNofile
          closeOpenFds openMap
          openMap := {}
          let wantPrefix := ((msg.splitOn ":").headD msg).trimAscii.toString
          let wantOut? := extractPollOut? msg
          let shrunk ← shrinkTrace trace fun cand => do
            let r ← replayTrace cand
            return (r.mismatchMsg.map (matchesPollMismatch wantPrefix wantOut?)).getD false
          let shrunkRes ← replayTrace shrunk
          let fmtStep (st : SymStep) : String :=
            let rStr := match st.req with
              | .ppoll es to alrm =>
                if es.size > 32 then s!"ppoll(entries={es.size}, to={repr to}, alrm={alrm})"
                else s!"{repr st.req}"
              | _ => s!"{repr st.req}"
            s!"(alloc={repr st.allocIds}, {rStr})"
          let traceStr := String.intercalate "\n  " (shrunk.toList.map fmtStep)
          throw (IO.userError s!"poll model/kernel mismatch at ep={epIdx} step={stepIdx}: {msg}\nshrunk mismatch: {shrunkRes.mismatchMsg.getD "<flaky>"}\nminimal trace ({shrunk.size} steps):\n  {traceStr}")
        | .ok (sm, sk, rm, om, bm, hm, em, fm, wm, cn, s', recorded?) =>
          symMap := sm
          symKindMap := sk
          rawMap := rm
          openMap := om
          bufMap := bm
          hupMap := hm
          errMap := em
          finMap := fm
          wrFullMap := wm
          curNofile := cn
          modelState := s'
          match recorded? with
          | some (sname, out) =>
            stats := stats.record sname out
            epSyscalls := epSyscalls + 1
          | none => pure ()
          match sreq with
          | .eventfd2 _ _ =>
            if let some sid := allocIds[0]? then
              if let some hid := symMap.get? sid then
                env := { env with
                  allFds := env.allFds.push (sid, hid, .eventfd)
                  efds := env.efds.push sid
                  allOpen := env.allOpen.push sid }
          | .openKind kind =>
            if let some sid := allocIds[0]? then
              if let some hid := symMap.get? sid then
                let sk : SymKind := if kind == 2 then .opathInvalid else .alwaysReady
                env := { env with
                  allFds := env.allFds.push (sid, hid, sk)
                  allOpen := env.allOpen.push sid }
          | .openPipe =>
            match allocIds[0]?, allocIds[1]? with
            | some rSid, some wSid =>
              if let (some rHid, some wHid) := (symMap.get? rSid, symMap.get? wSid) then
                env := { env with
                  allFds := (env.allFds.push (rSid, rHid, .pipeRead wSid)).push (wSid, wHid, .pipeWrite rSid)
                  streamReaders := env.streamReaders.push rSid
                  streamWriters := env.streamWriters.push wSid
                  allOpen := (env.allOpen.push rSid).push wSid }
            | _, _ => pure ()
          | .openSockpair =>
            match allocIds[0]?, allocIds[1]? with
            | some s0, some s1 =>
              if let (some h0, some h1) := (symMap.get? s0, symMap.get? s1) then
                env := { env with
                  allFds := (env.allFds.push (s0, h0, .sockEnd s1)).push (s1, h1, .sockEnd s0)
                  streamReaders := (env.streamReaders.push s0).push s1
                  streamWriters := (env.streamWriters.push s0).push s1
                  saturatableWriters := (env.saturatableWriters.push s0).push s1
                  allOpen := (env.allOpen.push s0).push s1 }
            | _, _ => pure ()
          | .openSeqpair =>
            match allocIds[0]?, allocIds[1]? with
            | some s0, some s1 =>
              if let (some h0, some h1) := (symMap.get? s0, symMap.get? s1) then
                env := { env with
                  allFds := (env.allFds.push (s0, h0, .seqEnd s1)).push (s1, h1, .seqEnd s0)
                  streamReaders := (env.streamReaders.push s0).push s1
                  streamWriters := (env.streamWriters.push s0).push s1
                  saturatableWriters := (env.saturatableWriters.push s0).push s1
                  allOpen := (env.allOpen.push s0).push s1 }
            | _, _ => pure ()
          | .openTcpPair =>
            match allocIds[0]?, allocIds[1]? with
            | some s0, some s1 =>
              if let (some h0, some h1) := (symMap.get? s0, symMap.get? s1) then
                env := { env with
                  allFds := (env.allFds.push (s0, h0, .tcpEnd s1)).push (s1, h1, .tcpEnd s0)
                  streamReaders := (env.streamReaders.push s0).push s1
                  streamWriters := (env.streamWriters.push s0).push s1
                  allOpen := (env.allOpen.push s0).push s1 }
            | _, _ => pure ()
          | .openUdpPair =>
            match allocIds[0]?, allocIds[1]? with
            | some s0, some s1 =>
              if let (some h0, some h1) := (symMap.get? s0, symMap.get? s1) then
                env := { env with
                  allFds := (env.allFds.push (s0, h0, .udpEnd s1)).push (s1, h1, .udpEnd s0)
                  streamReaders := (env.streamReaders.push s0).push s1
                  streamWriters := (env.streamWriters.push s0).push s1
                  allOpen := (env.allOpen.push s0).push s1 }
            | _, _ => pure ()
          | .openTcpListener =>
            if let some sid := allocIds[0]? then
              if let some hid := symMap.get? sid then
                env := { env with
                  allFds := env.allFds.push (sid, hid, .tcpListener)
                  allOpen := env.allOpen.push sid }
          | .openUdpSocket =>
            if let some sid := allocIds[0]? then
              if let some hid := symMap.get? sid then
                env := { env with
                  allFds := env.allFds.push (sid, hid, .udpSocket)
                  allOpen := env.allOpen.push sid }
          | .streamSaturate sid =>
            if wrFullMap.getD sid false then
              if let some (peerSid, _) := streamPeerInfo symKindMap sid then
                env := { env with
                  saturatedWriters := if env.saturatedWriters.contains sid then env.saturatedWriters else env.saturatedWriters.push sid
                  saturatedReaders := if env.saturatedReaders.contains peerSid then env.saturatedReaders else env.saturatedReaders.push peerSid }
          | .streamDrain sid =>
            if let some (peerSid, _) := streamPeerInfo symKindMap sid then
              if !(wrFullMap.getD peerSid false) then
                env := { env with
                  saturatedWriters := env.saturatedWriters.filter (· != peerSid)
                  saturatedReaders := env.saturatedReaders.filter (· != sid) }
          | .close sid =>
            env := { env with
              efds := env.efds.filter (· != sid)
              streamReaders := env.streamReaders.filter (· != sid)
              streamWriters := env.streamWriters.filter (· != sid)
              saturatableWriters := env.saturatableWriters.filter (· != sid)
              saturatedWriters := env.saturatedWriters.filter (· != sid)
              saturatedReaders := env.saturatedReaders.filter (· != sid)
              allOpen := env.allOpen.filter (· != sid)
              closedFds := if env.closedFds.contains sid then env.closedFds else env.closedFds.push sid }
          | _ => pure ()
    finally
      let _ ← rawRlimitNofile 1 origNofile
      closeOpenFds openMap
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
  }

end Fuzz.LinuxSyscall.PollFuzz
