import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Interface

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

/-- Kernel open-file table identifier (`struct file *`). -/
abbrev FileId := Nat

/-- One queued receive buffer item (`bytes` payload plus any attached `SCM_RIGHTS` `FileId`s). -/
structure RxUnit where
  /-- Payload bytes queued for `recv*`. -/
  bytes : ByteArray
  /-- `SCM_RIGHTS` open file references attached to this SKB. -/
  scm : List FileId := []
  /-- `true` when the single byte is a dummy carrier byte inserted by `sendmsg` (`SCM_RIGHTS`). -/
  isScmDummy : Bool := false
  deriving DecidableEq, BEq

/-- Shutdown bitmask (`SHUT_RD` / `SHUT_WR` / `SHUT_RDWR`). -/
structure ShutMask where
  /-- Read direction shut down (`RCV_SHUTDOWN`). -/
  rd : Bool := false
  /-- Write direction shut down (`SEND_SHUTDOWN`). -/
  wr : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Apply a `ShutHow` transition monotonically to `m`. -/
def ShutMask.apply (m : ShutMask) : ShutHow → ShutMask
  | .rd => { m with rd := true }
  | .wr => { m with wr := true }
  | .rdwr => { rd := true, wr := true }

/-- Returns `true` iff both read and write directions are shut down (`SHUTDOWN_MASK`). -/
def ShutMask.isBoth (m : ShutMask) : Bool := m.rd && m.wr

/-- IP address family of a TCP/UDP socket. -/
inductive InetFamily where
  /-- IPv4 (`AF_INET`). -/
  | v4
  /-- IPv6 (`AF_INET6`, dual-stack by default). -/
  | v6
  deriving Repr, DecidableEq, BEq

/-- Local address binding state in the inet port hash table. -/
inductive InetBind where
  /-- Socket has not bound or auto-bound any port/address yet. -/
  | unbound
  /-- Socket holds a port-hash entry (`addr`, pending ephemeral resolution, explicit port lock, explicit IP lock). -/
  | hashed (addr : SockAddr) (ephemeral : Bool) (portLocked : Bool) (addrLocked : Bool)
  /-- Socket port was unhashed (`inet_put_port`) while retaining `lastAddr` until re-bound or closed. -/
  | unhashed (lastAddr : SockAddr) (ephemeral : Bool) (addrLocked : Bool)
  deriving DecidableEq, BEq

/-- Extract the local `SockAddr` if the socket was ever bound or auto-bound. -/
def InetBind.addr? : InetBind → Option SockAddr
  | .unbound => none
  | .hashed addr _ _ _ => some addr
  | .unhashed addr _ _ => some addr

/-- Returns `true` iff the bound port is still a placeholder pending `getsockname` observation. -/
def InetBind.isEphemeral : InetBind → Bool
  | .hashed _ ep _ _ => ep
  | .unhashed _ ep _ => ep
  | .unbound => false

/-- Returns `true` iff an explicit non-zero port was locked via `bind()`. -/
def InetBind.isPortLocked : InetBind → Bool
  | .hashed _ _ pl _ => pl
  | _ => false

/-- Returns `true` iff a non-wildcard local IP was locked via `bind()`. -/
def InetBind.isAddrLocked : InetBind → Bool
  | .hashed _ _ _ al => al
  | .unhashed _ _ al => al
  | .unbound => false

/-- Unhash an unlocked inet port when transitioning to `TCP_CLOSE` (`inet_put_port`). -/
def InetBind.unhashUnlocked : InetBind → InetBind
  | .hashed addr ep false al => .unhashed addr ep al
  | other => other

/-- Cross-family vs same-family listener match mode for loopback and dual-stack `connect` / `accept4`. -/
inductive LoopbackMatchKind where
  /-- Client and listener share the same `SockDomain`. -/
  | sameFamily
  /-- `AF_INET` client connecting to an `AF_INET6` dual-stack listener (`::ffff:...`). -/
  | v4ToV6
  /-- `AF_INET6` `::ffff:...` client connecting to an `AF_INET` listener. -/
  | v6MappedToV4
  deriving Repr, DecidableEq, BEq

/-- Linux POSIX `socket->state` (`SS_UNCONNECTED` .. `SS_DISCONNECTING`). -/
inductive PosixSockState where
  /-- `SS_UNCONNECTED`. -/
  | unconnected
  /-- `SS_CONNECTING` (`crossFamily` records dual-stack listener queueing pending potential `IPV6_V6ONLY` abort). -/
  | connecting (crossFamily : Bool := false)
  /-- `SS_CONNECTED`. -/
  | connected
  /-- `SS_DISCONNECTING` (after async `soError` consumption on failed connect). -/
  | disconnecting
  deriving Repr, DecidableEq, BEq

/-- Completed child socket queued on a listener's `acceptQueue`. -/
structure AcceptEntry where
  /-- Server-side accepted socket `FileId` created at handshake time. -/
  childFid : FileId
  /-- Frozen client peer address visible to `accept4` on this listener. -/
  peerAddr : SockAddr
  /-- `true` iff the client port was already explicitly bound or observed via `getsockname`. -/
  peerPortPinned : Bool
  /-- Same-family vs dual-stack loopback endpoint mapping. -/
  matchKind : LoopbackMatchKind
  /-- `true` iff client and listener crossed IPv4/IPv6 domains. -/
  crossFamily : Bool := false
  /-- `true` iff the client holds an unpinned host-routed IPv4 `inet_saddr` from a multicast/broadcast-bound non-loopback connect. -/
  peerRoutedV4 : Bool := false
  deriving DecidableEq, BEq

/-- Reason a previously connected TCP socket entered `TCP_CLOSE`. -/
inductive TcpCloseReason where
  /-- Clean 4-way FIN exchange completed. -/
  | cleanFin
  /-- Connection aborted by TCP `RST`. -/
  | reset
  /-- Self-connected socket shut down `SHUT_RDWR` with buffered RX (`Nagle` segment may hit `SHUTDOWN_MASK` and emit `ECONNRESET`). -/
  | selfShutRstPossible
  deriving Repr, DecidableEq, BEq

/-- Linux TCP `sk->sk_state` for standard stream TCP sockets. -/
inductive TcpState where
  /-- `TCP_CLOSE` before any connection attempt. -/
  | idle
  /-- `TCP_LISTEN`. -/
  | listen (backlog : UInt32) (acceptQueue : List AcceptEntry)
  /-- `TCP_SYN_SENT` (`lo` down `wasEverUp = true` non-blocking attempt, or refused/stalled connect). -/
  | synSent (target : SockAddr)
  /-- `TCP_ESTABLISHED`. -/
  | established (peerFid? : Option FileId) (peerAddr : SockAddr)
  /-- `TCP_FIN_WAIT1`/`TCP_FIN_WAIT2` after local `SHUT_WR`. -/
  | finWait (peerFid? : Option FileId) (peerAddr : SockAddr)
  /-- `TCP_CLOSE_WAIT` after peer `FIN` or clean close (`peerClosedClean` iff remote socket has no live FD). -/
  | closeWait (peerFid? : Option FileId) (peerAddr : SockAddr) (peerClosedClean : Bool)
  /-- `TCP_CLOSE` entered after connection establishment. -/
  | closedAfterConn (peerAddr : SockAddr) (reason : TcpCloseReason)
  deriving DecidableEq, BEq

/-- Connection state of an `AF_UNIX` `SOCK_STREAM` or `SOCK_SEQPACKET` socket. -/
inductive UnixConnState where
  /-- Unconnected/idle `AF_UNIX` stream or seqpacket socket. -/
  | idle
  /-- Listening `AF_UNIX` socket with pending child queue. -/
  | listen (backlog : UInt32) (acceptQueue : List AcceptEntry)
  /-- Connected `AF_UNIX` stream/seqpacket socket (`peerResetFromGc` marks optional `unix_gc` reset). -/
  | connected (peerFid? : Option FileId) (peerShutWr : Bool) (peerWriteBroken : Bool)
      (peerReset : Bool) (peerResetFromGc : Bool)
  deriving DecidableEq, BEq

/-- Protocol-discriminated socket state. -/
inductive SockProtoState where
  /-- Standard IPv4/IPv6 TCP stream socket. -/
  | tcp (family : InetFamily) (bind : InetBind := .unbound)
      (sockState : PosixSockState := .unconnected)
      (tcpState : TcpState := .idle) (v4MappedTainted : Bool := false)
  /-- Standard IPv4/IPv6 UDP datagram socket. -/
  | udp (family : InetFamily) (bind : InetBind := .unbound)
      (connectedPeer? : Option SockAddr := none)
  /-- `AF_UNIX` `SOCK_STREAM` (`isSeqpacket = false`) or `SOCK_SEQPACKET` (`isSeqpacket = true`). -/
  | unixStream (isSeqpacket : Bool) (boundPath? : Option ByteArray := none)
      (conn : UnixConnState := .idle)
  /-- `AF_UNIX` `SOCK_DGRAM` socket. -/
  | unixDgram (boundPath? : Option ByteArray := none)
      (peer? : Option (FileId × SockAddr) := none)
  deriving DecidableEq, BEq

/-- Construct the initial `SockProtoState` for a validated `(domain, sockType)`. -/
def SockProtoState.ofDomainType (domain : SockDomain) (sockType : SockType) : SockProtoState :=
  match domain, sockType with
  | .inet, .stream => .tcp .v4
  | .inet6, .stream => .tcp .v6
  | .inet, .dgram => .udp .v4
  | .inet6, .dgram => .udp .v6
  | .unix, .stream => .unixStream false
  | .unix, .seqpacket => .unixStream true
  | .unix, .dgram => .unixDgram
  | .inet, .seqpacket => .tcp .v4
  | .inet6, .seqpacket => .tcp .v6

/-- Extract the `SockDomain` of `p`. -/
def SockProtoState.domain : SockProtoState → SockDomain
  | .tcp .v4 .. | .udp .v4 .. => .inet
  | .tcp .v6 .. | .udp .v6 .. => .inet6
  | .unixStream .. | .unixDgram .. => .unix

/-- Extract the `SockType` of `p`. -/
def SockProtoState.sockType : SockProtoState → SockType
  | .tcp .. => .stream
  | .udp .. | .unixDgram .. => .dgram
  | .unixStream false .. => .stream
  | .unixStream true .. => .seqpacket

/-- Returns `true` iff `p` is currently a listening TCP or Unix stream/seqpacket socket. -/
def SockProtoState.isListening : SockProtoState → Bool
  | .tcp _ _ _ (.listen _ _) _ => true
  | .unixStream _ _ (.listen _ _) => true
  | _ => false

/-- Extract `acceptQueue` when `p` is a listening socket. -/
def SockProtoState.acceptQueue? : SockProtoState → Option (List AcceptEntry)
  | .tcp _ _ _ (.listen _ aq) _ => some aq
  | .unixStream _ _ (.listen _ aq) => some aq
  | _ => none

/-- Extract the bound/auto-bound `SockAddr` of `p` if present. -/
def SockProtoState.localAddr? : SockProtoState → Option SockAddr
  | .tcp _ bind .. | .udp _ bind _ => bind.addr?
  | .unixStream _ (some path) _ | .unixDgram (some path) _ => some (.unix path)
  | .unixStream _ none _ | .unixDgram none _ => none

/-- Clean 6-field abstract socket descriptor. -/
structure SockDesc where
  /-- Protocol-discriminated socket state. -/
  proto : SockProtoState
  /-- `O_NONBLOCK` file-status flag. -/
  nonblock : Bool := false
  /-- `SO_REUSEADDR` boolean option. -/
  reuseAddr : Bool := false
  /-- Sticky `SHUT_RD` / `SHUT_WR` shutdown bitmask. -/
  shut : ShutMask := {}
  /-- Pending asynchronous `SO_ERROR` value (`0` when clear). -/
  soError : Errno := 0
  /-- Buffered incoming data/datagrams/`SCM_RIGHTS` units. -/
  rxQueue : List RxUnit := []
  /-- `true` when `AF_UNIX` `boundPath?` was inherited on `accept` rather than bound in the bind table. -/
  unixAddrInherited : Bool := false
  /-- `true` after a TCP send started while `lo` was down, leaving unacked data in retransmit backoff. -/
  tcpLoStalledTx : Bool := false
  /-- Monotonic bind-order sequence number assigned on UDP `bind`/autobind (`udp4_lib_lookup2` tie-break). -/
  udpBindSeq : Nat := 0
  /-- `true` once a deferred loopback FIN/close flushed on `lo`-up and nonblocking reads may observe `EAGAIN` before RTO. -/
  tcpLoFinPending : Bool := false
  /-- `true` when `shutdown(WR)` closed a nonblocking self-connect that may still have been in `TCP_SYN_SENT`. -/
  tcpSelfSynPending : Bool := false
  /-- `true` when an `AF_INET6` TCP socket transmitted while `lo` was down, leaving `sk_err_soft = ENETUNREACH` observable via `SO_ERROR`. -/
  tcpLoSoftUnreach : Bool := false
  /-- `true` once the peer called `SHUT_RDWR`, so in-flight TX hitting `RCV_SHUTDOWN` may trigger `CLOSE_WAIT` `RST` (`EPIPE`). -/
  tcpCloseWaitRst : Bool := false
  /-- `true` when `SHUT_RDWR` completed while `rxQueue` was non-empty, so a Nagle-buffered peer segment may hit `SHUTDOWN_MASK` (`ECONNRESET`). -/
  tcpShutRdwrRst : Bool := false
  /-- Sticky `sk->sk_bound_dev_if` interface index bound by IPv6 link-local `connect` (`0` = unbound, `1` = `"lo"`). -/
  boundDevIf : UInt32 := 0
  /-- `true` when an IPv4 multicast/broadcast or `::ffff:0.0.0.0`-bound socket connected to a non-loopback target, assigning an unpinned host-routed `inet_saddr`. -/
  tcpMcastRoutedIp : Bool := false
  /-- `true` when an `AF_INET` socket bound a non-wildcard IPv4 address before `"lo"` was ever brought up (`inet_saddr = 0`). -/
  inetSaddrZero : Bool := false
  /-- `true` when a `SOCK_DGRAM` socket with locked `inet_saddr = 0` connected to a non-loopback IPv4 destination, locking a non-loopback wire source IP. -/
  udpExtRoutedIp : Bool := false
  /-- `true` when a socket bound `127.255.255.255` or `::ffff:127.255.255.255` while `lo` was down (`RTN_LOCAL` source retained). -/
  tcpLoDownDirectedBcast : Bool := false
  /-- `true` once `shutdown(SHUT_WR/RDWR)` sent a `FIN` from `TCP_CLOSE_WAIT` that stays in `TCP_LAST_ACK` (`lo` down or tainted IPv6). -/
  tcpLastAck : Bool := false
  deriving DecidableEq, BEq

/-- Construct a fresh `SockDesc` for `(domain, sockType)`. -/
def SockDesc.mkDefault (domain : SockDomain) (sockType : SockType) (nonblock : Bool := false) : SockDesc :=
  { proto := SockProtoState.ofDomainType domain sockType, nonblock }

/-- Socket domain helper. -/
def SockDesc.domain (d : SockDesc) : SockDomain := d.proto.domain

/-- Socket type helper. -/
def SockDesc.sockType (d : SockDesc) : SockType := d.proto.sockType

/-- Local address helper. -/
def SockDesc.localAddr? (d : SockDesc) : Option SockAddr := d.proto.localAddr?

/-- Open-file entry in `NetState.files`. -/
inductive OpenFileEntry where
  /-- Live socket descriptor. -/
  | socket (desc : SockDesc)
  /-- Non-socket open file descriptor (for `ENOTSOCK`/`ENOTTY`/`SCM_RIGHTS`). -/
  | nonSocket
  deriving DecidableEq, BEq

/-- Descriptor-table entry in `NetState.handles`. -/
inductive NetHandleEntry where
  /-- Open descriptor pointing to `fileId` with `FD_CLOEXEC` bit. -/
  | open (fileId : FileId) (cloexec : Bool := true)
  /-- Closed descriptor slot. -/
  | closed
  deriving Repr, DecidableEq, BEq

/-- Loopback interface lifecycle (`IFF_UP` and whether `lo` was ever brought up). -/
inductive LoState where
  /-- Initial `"lo"` flags have not been pinned via `ioctl` (`defaultFlags` used by `modelOps`). -/
  | unpinned (defaultFlags : UInt32 := 0x49)
  /-- `"lo"` has `IFF_UP` enabled. -/
  | up (flags : UInt32)
  /-- `"lo"` has `IFF_UP` cleared (`wasEverUp` tracks cached loopback routes in Linux `CLONE_NEWNET`). -/
  | down (flags : UInt32) (wasEverUp : Bool)
  deriving Repr, DecidableEq, BEq

/-- Loopback interface name `"lo"`. -/
def loIfname : ByteArray := asciiBytes ['l', 'o']

/-- Standard Linux `IFF_UP | IFF_LOOPBACK | IFF_RUNNING` flags on `"lo"`. -/
def defaultLoFlags : UInt32 := IFF_UP ||| IFF_LOOPBACK ||| IFF_RUNNING

/-- Deferred loopback TCP packet event queued while `"lo"` is down (`!IFF_UP`). -/
inductive LoPendingTcpEvent where
  /-- Deferred TCP data send from `srcFid` to `peerFid`. -/
  | tx (srcFid peerFid : FileId) (unit : RxUnit)
  /-- Deferred TCP write-side FIN (`shutdown(SHUT_WR)`) from `srcFid` to `peerFid`. -/
  | shutFin (srcFid peerFid : FileId)
  /-- Deferred TCP FIN/RST from closed `srcFid` to `peerFid`. -/
  | close (srcFid peerFid : FileId) (hasUnread selfEstab selfFinWait selfCloseWait : Bool)
  deriving DecidableEq, BEq

/-- Pure model state tracking open FDs, open sockets/files, bound Unix paths, and network interface flags. -/
structure NetState where
  /-- Descriptor handle table mapping `HandleId` to open file references or closed slots. -/
  handles : List (HandleId × NetHandleEntry)
  /-- Kernel open-file table mapping `FileId` to active sockets or non-socket files. -/
  files : List (FileId × OpenFileEntry) := []
  /-- Persistent bound filesystem `AF_UNIX` socket paths (survive `closeHandle`). -/
  boundUnixPaths : List ByteArray := []
  /-- Loopback `"lo"` interface state. -/
  loState : LoState := .up defaultLoFlags
  /-- Flags observed/configured for non-loopback interfaces. -/
  otherIfaces : List (ByteArray × UInt32) := []
  /-- Whether the process has `CAP_NET_ADMIN`. -/
  hasNetAdmin : Bool := false
  /-- Whether an inherited outer safe `seccomp(SECCOMP_RET_ERRNO)` filter is active. -/
  ambientSeccomp : Bool := false
  /-- Hint for next fresh `HandleId`. -/
  nextHid : HandleId := 0
  /-- Next fresh `FileId`. -/
  nextFileId : FileId := 0
  /-- Ephemeral port allocation cursor (`[49152, 65535]`). -/
  nextPort : UInt16 := 49152
  /-- Monotonic counter for UDP bind ordering. -/
  nextBindSeq : Nat := 1
  /-- Deferred TCP loopback events queued while `"lo"` is down. -/
  loPendingTcp : List LoPendingTcpEvent := []
  deriving DecidableEq, BEq

/-- Standard initial state with `"lo"` up (`IFF_UP | IFF_LOOPBACK | IFF_RUNNING`). -/
def NetState.initial (hasNetAdmin : Bool := false) (ambientSeccomp : Bool := false) : NetState :=
  { handles := [], files := [], loState := .up defaultLoFlags, hasNetAdmin, ambientSeccomp }

/-- Initial state for a fresh `CLONE_NEWNET` namespace where `"lo"` starts down (`wasEverUp = false`). -/
def NetState.initialNetns (hasNetAdmin : Bool := true) (ambientSeccomp : Bool := false) : NetState :=
  { handles := [], files := [], loState := .down IFF_LOOPBACK false, hasNetAdmin, ambientSeccomp }

/-- Initial state with `"lo"` unpinned for harnesses that discover initial flags dynamically. -/
def NetState.initialUnpinned (hasNetAdmin : Bool := false) (ambientSeccomp : Bool := false) : NetState :=
  { handles := [], files := [], loState := .unpinned defaultLoFlags, hasNetAdmin, ambientSeccomp }

/-- Returns `true` iff `e` is a transient networking OS errno (`Errno.isTransientOsErrno` or `ENOBUFS`). -/
def isTransientNetErrno (e : Errno) : Bool :=
  e.isTransientOsErrno || e == Errno.ENOBUFS

/-- Structural tail-recursive byte-by-byte equality helper for `bytesEq`. -/
def bytesEqAux (a b : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | rem + 1, i =>
    if a.get! i != b.get! i then false
    else bytesEqAux a b rem (i + 1)

/-- Returns `true` iff `a` and `b` have identical byte contents. -/
def bytesEq (a b : ByteArray) : Bool :=
  a.size == b.size && bytesEqAux a b a.size 0

/-- Slice `[start, start + len)` bytes out of `b`. -/
def sliceBytes (b : ByteArray) (start len : Nat) : ByteArray :=
  if start == 0 && len >= b.size then b
  else if len == 0 then ByteArray.empty
  else b.extract start (start + len)

/-- Association-list lookup by `BEq` key. -/
def assocGet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  match xs with
  | [] => none
  | (x, v) :: rest => if x == k then some v else assocGet rest k

/-- Tail-recursive helper for `assocSet`. -/
def assocSetAux {α β : Type} [BEq α] :
    List (α × β) → α → β → List (α × β) → List (α × β)
  | [], k, v, acc => acc.reverseAux [(k, v)]
  | (x, oldV) :: rest, k, v, acc =>
    if x == k then acc.reverseAux ((k, v) :: rest)
    else assocSetAux rest k v ((x, oldV) :: acc)

/-- Functional association-list update by `BEq` key (tail-recursive). -/
def assocSet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) (v : β) : List (α × β) :=
  assocSetAux xs k v []

/-- Tail-recursive helper for `assocErase`. -/
def assocEraseAux {α β : Type} [BEq α] :
    List (α × β) → α → List (α × β) → List (α × β)
  | [], _, acc => acc.reverse
  | (x, v) :: rest, k, acc =>
    if x == k then assocEraseAux rest k acc
    else assocEraseAux rest k ((x, v) :: acc)

/-- Erase key `k` from association list `xs` (tail-recursive). -/
def assocErase {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : List (α × β) :=
  assocEraseAux xs k []

/-- Byte-keyed association-list lookup. -/
def bytesAssocGet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) : Option β :=
  match xs with
  | [] => none
  | (x, v) :: rest => if bytesEq x k then some v else bytesAssocGet rest k

/-- Tail-recursive helper for `bytesAssocSet`. -/
def bytesAssocSetAux {β : Type} :
    List (ByteArray × β) → ByteArray → β → List (ByteArray × β) → List (ByteArray × β)
  | [], k, v, acc => acc.reverseAux [(k, v)]
  | (x, oldV) :: rest, k, v, acc =>
    if bytesEq x k then acc.reverseAux ((k, v) :: rest)
    else bytesAssocSetAux rest k v ((x, oldV) :: acc)

/-- Byte-keyed association-list update (tail-recursive). -/
def bytesAssocSet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) (v : β) : List (ByteArray × β) :=
  bytesAssocSetAux xs k v []

/-- Returns `true` iff `b` is byte-equal to an element of `xs`. -/
def bytesListContains (xs : List ByteArray) (b : ByteArray) : Bool :=
  xs.any (bytesEq · b)

/-- Resolve `hid` to its open `FileId`, returning `none` if `hid` is missing or closed. -/
def lookupHandleFileId (s : NetState) (hid : HandleId) : Option FileId :=
  match assocGet s.handles hid with
  | some (.open fid _) => some fid
  | _ => none

/-- Resolve `fid` in `s.files` to a live socket, returning `EBADF` if absent or `ENOTSOCK` if non-socket. -/
def lookupFileSocket (s : NetState) (fid : FileId) : Except Errno SockDesc :=
  match assocGet s.files fid with
  | some (.socket d) => .ok d
  | some .nonSocket => .error Errno.ENOTSOCK
  | none => .error Errno.EBADF

/-- Returns `true` iff `hid` is currently open in `s`. -/
def isLiveHandle (s : NetState) (hid : HandleId) : Bool :=
  (lookupHandleFileId s hid).isSome

/-- Returns `true` iff `hid` is not currently open in `s.handles`. -/
def isFreshHid (s : NetState) (hid : HandleId) : Bool :=
  match assocGet s.handles hid with
  | some (.open _ _) => false
  | _ => true

/-- Compute a guaranteed-fresh handle ID (`>= s.nextHid` and `>= 1 + max open hid`). -/
def freshHidBase (s : NetState) : HandleId :=
  s.handles.foldl
    (fun acc (h, e) => match e with | .open _ _ => max acc (h + 1) | .closed => acc)
    s.nextHid

/-- Update `fid`'s socket entry in `s.files`. -/
def setFileSocket (s : NetState) (fid : FileId) (d : SockDesc) : NetState :=
  { s with files := assocSet s.files fid (.socket d) }

/-- Store `d` at `hid`, allocating a new `FileId` if `hid` is not yet mapped. -/
def setSocket (s : NetState) (hid : HandleId) (d : SockDesc) : NetState :=
  match lookupHandleFileId s hid with
  | some fid => setFileSocket s fid d
  | none =>
    let fid := s.nextFileId
    { s with
      handles := assocSet s.handles hid (.open fid true)
      files := assocSet s.files fid (.socket d)
      nextFileId := fid + 1 }

/-- Register an open non-socket handle at `freshHidBase s`. -/
def NetState.registerNonSocket (s : NetState) (cloexec : Bool := true) : HandleId × NetState :=
  let hid := freshHidBase s
  let fid := s.nextFileId
  (hid,
    { s with
      handles := assocSet s.handles hid (.open fid cloexec)
      files := assocSet s.files fid .nonSocket
      nextHid := max s.nextHid (hid + 1)
      nextFileId := fid + 1 })

/-- Allocate the next non-zero dynamic port number in `[49152, 65535]`. -/
def allocNextPort (s : NetState) : UInt16 × UInt16 :=
  let p := if s.nextPort == 0 then (49152 : UInt16) else s.nextPort
  let next := if p == 65535 then (49152 : UInt16) else p + 1
  (p, next)

/-- Return all `FileId`s directly referenced by `d`'s receive queue or accept queue. -/
def directChildRefs (d : SockDesc) : List FileId :=
  let scmRefs := d.rxQueue.foldl (fun acc u => acc ++ u.scm) []
  let accRefs :=
    match d.proto.acceptQueue? with
    | some aq => aq.map (·.childFid)
    | none => []
  scmRefs ++ accRefs

/-- Returns `true` iff `fid` is still referenced by any open handle, live `rxQueue` `SCM_RIGHTS`, or live listener `acceptQueue`. -/
def isFileReferenced (s : NetState) (fid : FileId) : Bool :=
  let inHandles := s.handles.any fun (_, e) => match e with | .open f _ => f == fid | .closed => false
  let inFiles := s.files.any fun (_, entry) =>
    match entry with
    | .socket d => (directChildRefs d).contains fid
    | .nonSocket => false
  inHandles || inFiles

/-- Returns `true` iff `sa` is a native (non-`::ffff:*`) IPv6 socket address. -/
def isNativeV6PeerAddr : SockAddr → Bool
  | .ipv6 hi lo _ _ _ => !(hi == 0 && (lo &&& 0xffffffff00000000) == 0x0000ffff00000000)
  | _ => false

/-- Propagate TCP peer close (`FIN` or `RST`) onto `peerFid` upon connection teardown. -/
def resetTcpPeerOnClose (s : NetState) (peerFid : FileId) (hasUnread : Bool)
    (selfWasEstablished selfWasFinWait selfWasCloseWait : Bool) : NetState :=
  match lookupFileSocket s peerFid with
  | .ok pd =>
    match pd.proto with
    | .tcp pfam pbind psock ptcp ptaint =>
      if hasUnread then
        let resetErr := match ptcp with | .closeWait _ _ _ => Errno.EPIPE | _ => Errno.ECONNRESET
        let pd' :=
          { pd with
            soError := if pd.soError == 0 then resetErr else pd.soError
            tcpShutRdwrRst := false
            tcpLastAck :=
              match ptcp with
              | .established .. | .finWait .. | .closeWait .. => false
              | _ => pd.tcpLastAck
            proto :=
              match ptcp with
              | .established _ pa | .finWait _ pa | .closeWait _ pa _ =>
                .tcp pfam pbind.unhashUnlocked psock (.closedAfterConn pa .reset) ptaint
              | _ => .tcp pfam pbind.unhashUnlocked psock ptcp ptaint }
        setFileSocket s peerFid pd'
      else
        let (nextPbind, nextPtcp) :=
          if selfWasCloseWait then
            match ptcp with
            | .finWait _ pa => (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | .established _ pa => (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | .closeWait _ pa _ => (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | other => (pbind, other)
          else if selfWasFinWait then
            match ptcp with
            | .closeWait _ pa _ => (pbind, TcpState.closeWait none pa true)
            | .finWait _ pa =>
              if pfam == .v6 && ptaint && isNativeV6PeerAddr pa then
                (pbind, TcpState.closeWait none pa true)
              else
                (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | other => (pbind, other)
          else if selfWasEstablished then
            match ptcp with
            | .established _ pa => (pbind, TcpState.closeWait none pa true)
            | .finWait _ pa =>
              if pfam == .v6 && ptaint && isNativeV6PeerAddr pa then
                (pbind, TcpState.closeWait none pa true)
              else
                (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | .closeWait _ pa _ => (pbind.unhashUnlocked, TcpState.closedAfterConn pa .cleanFin)
            | other => (pbind, other)
          else (pbind, ptcp)
        let delayFin :=
          !pd.rxQueue.isEmpty && pfam == .v6 && ptaint &&
            match nextPtcp with
            | .closeWait _ pa _ | .closedAfterConn pa _ => isNativeV6PeerAddr pa
            | _ => false
        let nextLastAck := match nextPtcp with | .closeWait .. => pd.tcpLastAck | _ => false
        setFileSocket s peerFid
          { pd with
            tcpLoFinPending := pd.tcpLoFinPending || delayFin
            tcpLastAck := nextLastAck
            proto := .tcp pfam nextPbind psock nextPtcp ptaint }
    | _ => s
  | .error _ => s

private def abortUnacceptedTcpChild (s : NetState) (q : AcceptEntry) : NetState × List FileId :=
  match assocGet s.files q.childFid with
  | some (.socket cd) =>
    let s0 := { s with files := assocErase s.files q.childFid }
    let loUp := match s0.loState with | .up _ => true | _ => false
    let s1 :=
      match cd.proto with
      | .tcp fam _ _ (.established (some cliFid) pa) tainted
      | .tcp fam _ _ (.finWait (some cliFid) pa) tainted
      | .tcp fam _ _ (.closeWait (some cliFid) pa _) tainted =>
        if fam == .v6 && tainted && isNativeV6PeerAddr pa then
          s0
        else if !loUp then
          { s0 with loPendingTcp := s0.loPendingTcp ++ [.close q.childFid cliFid true false false false] }
        else
          resetTcpPeerOnClose s0 cliFid true false false false
      | _ => s0
    (s1, cd.rxQueue.foldl (fun acc u => acc ++ u.scm) [])
  | _ => (s, [])

private def abortUnacceptedUnixChild (s : NetState) (q : AcceptEntry) (fromGc : Bool) : NetState × List FileId :=
  match assocGet s.files q.childFid with
  | some (.socket cd) =>
    let s0 := { s with files := assocErase s.files q.childFid }
    let s1 :=
      match cd.proto with
      | .unixStream _ _ (.connected (some cliFid) _ _ _ _) =>
        match lookupFileSocket s0 cliFid with
        | .ok cpd =>
          match cpd.proto with
          | .unixStream cseq cbp (.connected _ _ _ _ _) =>
            setFileSocket s0 cliFid
              { cpd with proto := .unixStream cseq cbp (.connected none true true true fromGc) }
          | _ => s0
        | .error _ => s0
      | _ => s0
    (s1, cd.rxQueue.foldl (fun acc u => acc ++ u.scm) [])
  | _ => (s, [])

private def releaseOneFile (s : NetState) (fid : FileId) (fromGc : Bool := false) : NetState × List FileId :=
  match assocGet s.files fid with
  | none => (s, [])
  | some entry =>
    let s0 : NetState := { s with files := assocErase s.files fid }
    match entry with
    | .nonSocket => (s0, [])
    | .socket d =>
      let rxScm := d.rxQueue.foldl (fun acc u => acc ++ u.scm) []
      let hasUnread := !d.rxQueue.isEmpty
      let hasUnreadBytes := d.rxQueue.any (fun u => u.bytes.size > 0) || d.rxQueue.length >= 2
      match d.proto with
      | .tcp fam _ _ tcpState tainted =>
        let isNativeV6Peer : SockAddr → Bool
          | .ipv6 hi lo _ _ _ => !(hi == 0 && (lo &&& 0xffffffff00000000) == 0x0000ffff00000000)
          | _ => false
        match tcpState with
        | .listen _ aq =>
          aq.foldl
            (fun (accS, accRefs) q =>
              let (nextS, moreRefs) := abortUnacceptedTcpChild accS q
              (nextS, accRefs ++ moreRefs))
            (s0, rxScm)
        | .established (some peerFid) pa =>
          let loUp := match s0.loState with | .up _ => true | _ => false
          let s1 :=
            if peerFid == fid || (fam == .v6 && tainted && isNativeV6Peer pa) then s0
            else if !loUp then { s0 with loPendingTcp := s0.loPendingTcp ++ [.close fid peerFid hasUnread true false false] }
            else resetTcpPeerOnClose s0 peerFid hasUnread true false false
          (s1, rxScm)
        | .finWait (some peerFid) pa =>
          let loUp := match s0.loState with | .up _ => true | _ => false
          let s1 :=
            if peerFid == fid || (fam == .v6 && tainted && isNativeV6Peer pa) then s0
            else if !loUp then { s0 with loPendingTcp := s0.loPendingTcp ++ [.close fid peerFid hasUnread false true false] }
            else resetTcpPeerOnClose s0 peerFid hasUnread false true false
          (s1, rxScm)
        | .closeWait (some peerFid) pa _ =>
          let loUp := match s0.loState with | .up _ => true | _ => false
          let s1 :=
            if peerFid == fid || (fam == .v6 && tainted && isNativeV6Peer pa) then s0
            else if !loUp then { s0 with loPendingTcp := s0.loPendingTcp ++ [.close fid peerFid hasUnread false false true] }
            else resetTcpPeerOnClose s0 peerFid hasUnread false false true
          (s1, rxScm)
        | _ => (s0, rxScm)
      | .unixStream _ _ conn =>
        match conn with
        | .listen _ aq =>
          aq.foldl
            (fun (accS, accRefs) q =>
              let (nextS, moreRefs) := abortUnacceptedUnixChild accS q fromGc
              (nextS, accRefs ++ moreRefs))
            (s0, rxScm)
        | .connected (some peerFid) _ _ _ _ =>
          if peerFid == fid then (s0, rxScm)
          else
            let s1 :=
              match lookupFileSocket s0 peerFid with
              | .ok pd =>
                match pd.proto with
                | .unixStream pseq pbp (.connected _ _ _ prevRst prevRstGc) =>
                  let nextRst := prevRst || hasUnreadBytes || fromGc
                  let nextRstGc := if !prevRst && fromGc then true else prevRstGc
                  setFileSocket s0 peerFid
                    { pd with proto := .unixStream pseq pbp (.connected none true true nextRst nextRstGc) }
                | _ => s0
              | .error _ => s0
            (s1, rxScm)
        | .connected none .. | .idle => (s0, rxScm)
      | .udp .. | .unixDgram .. => (s0, rxScm)

private def releaseUnusedWork : Nat → NetState → List FileId → Bool → NetState
  | 0, s, _, _ => s
  | _, s, [], _ => s
  | fuel + 1, s, fid :: rest, fromGc =>
    if (assocGet s.files fid).isNone || rest.contains fid || isFileReferenced s fid then
      releaseUnusedWork fuel s rest fromGc
    else
      let (s1, more) := releaseOneFile s fid fromGc
      let freshMore := more.filter (fun c => (assocGet s1.files c).isSome && !rest.contains c)
      releaseUnusedWork fuel s1 (freshMore ++ rest) fromGc

/-- Recursively free any `FileId`s in `candidates` whose reference count has reached zero. -/
def releaseUnusedFiles (s : NetState) (candidates : List FileId) : NetState :=
  let uniqueCands := candidates.foldl (fun acc x => if acc.contains x then acc else x :: acc) [] |>.reverse
  releaseUnusedWork ((s.files.length + 1) * (s.files.length + 1) + uniqueCands.length + 1) s uniqueCands false

/-- Erase `fid` immediately and recursively drop any orphaned `SCM_RIGHTS` handles it held. -/
def releaseFile (s : NetState) (fid : FileId) : NetState :=
  let (s1, more) := releaseOneFile s fid false
  releaseUnusedFiles s1 more

/-- Unreachable `FileId` candidates eligible for asynchronous `unix_gc` / `delayed_fput` release. -/
def collectUnixGcCandidates (s : NetState) : List FileId :=
  let rawSeeds : List FileId :=
    s.handles.filterMap fun (_, e) => match e with | .open fid _ => some fid | .closed => none
  let seeds : List FileId :=
    rawSeeds.foldl (fun acc x => if acc.contains x then acc else x :: acc) [] |>.reverse
  let rec bfs : Nat → List FileId → List FileId → List FileId
    | 0, _, seen => seen
    | _, [], seen => seen
    | fuel + 1, fid :: work, seen =>
      if seen.contains fid then bfs fuel work seen
      else
        let seen' := fid :: seen
        let children :=
          match assocGet s.files fid with
          | some (.socket d) => directChildRefs d
          | _ => []
        let freshChildren := children.filter (fun c => !seen'.contains c && !work.contains c)
        bfs fuel (freshChildren ++ work) seen'
  let reachable := bfs (s.files.length * 2 + seeds.length + 1) seeds []
  s.files.filterMap fun (fid, _) => if reachable.contains fid then none else some fid

/-- Release a single unreachable `FileId` (`unix_gc` / `delayed_fput` partial teardown). -/
def releaseUnixGcFile (s : NetState) (fid : FileId) : NetState :=
  (releaseOneFile s fid true).1

/-- Collect cyclic unreferenced `SCM_RIGHTS` files (`unix_gc`), returning `none` if none exist. -/
def collectUnixGc (s : NetState) : Option NetState :=
  let garbage := collectUnixGcCandidates s
  if garbage.isEmpty then none
  else
    let s1 := garbage.foldl (fun acc fid => (releaseOneFile acc fid true).1) s
    some s1

/-- Close descriptor handle `hid`, recursively freeing the underlying file when its refcount reaches zero. -/
def NetState.closeHandle (s : NetState) (hid : HandleId) : Except Errno NetState :=
  match assocGet s.handles hid with
  | some (.open fid _) =>
    let s1 := { s with handles := assocSet s.handles hid .closed }
    .ok (releaseUnusedFiles s1 [fid])
  | _ => .error Errno.EBADF

/-- Reset an accepted listener's pending `acceptQueue` when `shutdown(SHUT_RD)` / `shutdown(SHUT_RDWR)` closes a TCP listener. -/
def resetListenerAcceptQueue (s : NetState) (aq : List AcceptEntry) : NetState :=
  let (s1, refs) := aq.foldl
    (fun (accS, accRefs) q =>
      let (nextS, moreRefs) := abortUnacceptedTcpChild accS q
      (nextS, accRefs ++ moreRefs))
    (s, [])
  releaseUnusedFiles s1 refs

end LeanSwe.LinuxSyscall.Net
