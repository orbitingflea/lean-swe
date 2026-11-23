import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Maximum number of file descriptors sent or received in one `SCM_RIGHTS` `sendmsg` / `recvmsg` call (`32`). -/
def MAX_SCM_FDS : Nat := 32

/-- Linux `struct ifreq.ifr_name` buffer capacity (`IFNAMSIZ = 16`; valid NUL-terminated names have `< 16` bytes). -/
def IFNAMSIZ : Nat := 16

/-- Linux `struct sockaddr_un.sun_path` buffer capacity (`108`; valid filesystem paths have `1..108` bytes when non-NUL-terminated or `1..107` when NUL-terminated). -/
def UNIX_PATH_MAX : Nat := 108

/-- Network interface is administratively up (`IFF_UP`, `0x1`). -/
def IFF_UP : UInt32 := 0x1

/-- Network interface is a loopback device (`IFF_LOOPBACK`, `0x8`). -/
def IFF_LOOPBACK : UInt32 := 0x8

/-- Network interface resources are allocated and operational (`IFF_RUNNING`, `0x40`). -/
def IFF_RUNNING : UInt32 := 0x40

/-- IPv4 wildcard bind address `0.0.0.0` (`INADDR_ANY`). -/
def INADDR_ANY : UInt32 := 0x00000000

/-- IPv4 loopback address `127.0.0.1` (`INADDR_LOOPBACK`, `0x7f000001`). -/
def INADDR_LOOPBACK : UInt32 := 0x7f000001

/-- Default / automatic socket protocol selector (`0`). -/
def IPPROTO_IP : UInt32 := 0

/-- Unix-domain socket protocol selector (`PF_UNIX`, `1`), accepted alongside `0` by Linux `unix_create` for `socket(AF_UNIX, type, proto)`. -/
def PF_UNIX : UInt32 := 1

/-- Transmission Control Protocol number (`IPPROTO_TCP`, `6`). -/
def IPPROTO_TCP : UInt32 := 6

/-- User Datagram Protocol number (`IPPROTO_UDP`, `17`). -/
def IPPROTO_UDP : UInt32 := 17

/-- Exclusive upper bound on valid `AF_INET`/`AF_INET6` protocol numbers (`IPPROTO_MAX = 263`; `>= 263` fails with `EINVAL`). -/
def IPPROTO_MAX : UInt32 := 263

/-- Portable socket communication domain translated via `<sys/socket.h>`. -/
inductive SockDomain where
  /-- IPv4 Internet protocols (`AF_INET`). -/
  | inet
  /-- IPv6 Internet protocols (`AF_INET6`). -/
  | inet6
  /-- Local Unix-domain IPC (`AF_UNIX`). -/
  | unix
  deriving Repr, DecidableEq, BEq

/-- Encode `SockDomain` into a portable C-ABI tag (`0..2`). -/
def SockDomain.toTag : SockDomain → UInt32
  | .inet => 0
  | .inet6 => 1
  | .unix => 2

/-- Portable socket communication semantics translated via `<sys/socket.h>`. -/
inductive SockType where
  /-- Sequenced, reliable, connection-based byte streams (`SOCK_STREAM`). -/
  | stream
  /-- Connectionless datagrams (`SOCK_DGRAM`, also used for `SIOCGIFFLAGS`/`SIOCSIFFLAGS` `ioctl`). -/
  | dgram
  /-- Sequenced, reliable, connection-based record-boundary packets (`SOCK_SEQPACKET`). -/
  | seqpacket
  deriving Repr, DecidableEq, BEq

/-- Encode `SockType` into a portable C-ABI tag (`0..2`). -/
def SockType.toTag : SockType → UInt32
  | .stream => 0
  | .dgram => 1
  | .seqpacket => 2

/-- Portable atomic descriptor creation flags for `socket`, `socketpair`, and `accept4`. -/
structure SockFlags where
  /-- Set `O_NONBLOCK` (`SOCK_NONBLOCK`) on the new open file description. -/
  nonblock : Bool := false
  /-- Set `FD_CLOEXEC` (`SOCK_CLOEXEC`) on the new file descriptor. -/
  cloexec : Bool := true
  deriving Repr, DecidableEq, BEq

/-- Encode `SockFlags` into a 2-bit portable bitmask (`0..3`) decoded by `net_shim.c`. -/
def SockFlags.toBits (f : SockFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.nonblock 0 ||| bit f.cloexec 1

/-- Architecture-independent socket address (`AF_INET`, `AF_INET6`, `AF_UNIX`). -/
inductive SockAddr where
  /-- IPv4 address (`addr` in big-endian host `UInt32`, e.g. `0x7f000001` = `127.0.0.1`, and `port` in host `UInt16`). -/
  | ipv4 (addr : UInt32) (port : UInt16)
  /-- IPv6 address (`hi`/`lo` 64-bit big-endian words, e.g. `(0, 1)` = `::1`, `port`, `flowinfo`, `scopeId`). -/
  | ipv6 (hi : UInt64) (lo : UInt64) (port : UInt16) (flowinfo : UInt32 := 0) (scopeId : UInt32 := 0)
  /-- Unix-domain filesystem path (`ByteArray.empty` represents an unnamed `AF_UNIX` endpoint from `getsockname`/`accept4`). -/
  | unix (path : ByteArray)
  deriving Repr

private def unixBytesEqAux (a b : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | rem + 1, i =>
    if a.get! i != b.get! i then false
    else unixBytesEqAux a b rem (i + 1)

private def unixBytesEq (a b : ByteArray) : Bool :=
  a.size == b.size && unixBytesEqAux a b a.size 0

/-- Kernel-reducible boolean equality on `SockAddr`. -/
def SockAddr.beq : SockAddr → SockAddr → Bool
  | .ipv4 a1 p1, .ipv4 a2 p2 => a1 == a2 && p1 == p2
  | .ipv6 hi1 lo1 p1 fl1 sc1, .ipv6 hi2 lo2 p2 fl2 sc2 =>
    hi1 == hi2 && lo1 == lo2 && p1 == p2 && fl1 == fl2 && sc1 == sc2
  | .unix b1, .unix b2 => unixBytesEq b1 b2
  | _, _ => false

instance : BEq SockAddr := ⟨SockAddr.beq⟩

instance : DecidableEq SockAddr := fun x y =>
  match x, y with
  | .ipv4 a1 p1, .ipv4 a2 p2 =>
    if h : a1 = a2 ∧ p1 = p2 then isTrue (by rcases h with ⟨rfl, rfl⟩; rfl)
    else isFalse (fun heq => by cases heq; exact h ⟨rfl, rfl⟩)
  | .ipv6 hi1 lo1 p1 fl1 sc1, .ipv6 hi2 lo2 p2 fl2 sc2 =>
    if h : hi1 = hi2 ∧ lo1 = lo2 ∧ p1 = p2 ∧ fl1 = fl2 ∧ sc1 = sc2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else
      isFalse (fun heq => by cases heq; exact h ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | .unix b1, .unix b2 =>
    if h : b1.data = b2.data then
      isTrue (by cases b1; cases b2; cases h; rfl)
    else
      isFalse (fun heq => by cases heq; exact h rfl)
  | .ipv4 _ _, .ipv6 _ _ _ _ _ => isFalse (fun h => by cases h)
  | .ipv4 _ _, .unix _ => isFalse (fun h => by cases h)
  | .ipv6 _ _ _ _ _, .ipv4 _ _ => isFalse (fun h => by cases h)
  | .ipv6 _ _ _ _ _, .unix _ => isFalse (fun h => by cases h)
  | .unix _, .ipv4 _ _ => isFalse (fun h => by cases h)
  | .unix _, .ipv6 _ _ _ _ _ => isFalse (fun h => by cases h)

/-- Returns the `SockDomain` corresponding to `sa`. -/
def SockAddr.domain : SockAddr → SockDomain
  | .ipv4 _ _ => .inet
  | .ipv6 _ _ _ _ _ => .inet6
  | .unix _ => .unix

/-- Returns `true` iff `sa` is valid as a `bind` or `connect` target (rejecting empty, `> 108`-byte, or non-abstract NUL-containing `AF_UNIX` paths). -/
def SockAddr.isValidTarget : SockAddr → Bool
  | .ipv4 _ _ => true
  | .ipv6 _ _ _ _ _ => true
  | .unix path =>
    path.size > 0 && path.size ≤ UNIX_PATH_MAX &&
      (path.data[0]? == some 0 || !hasEmbeddedNul path)

/-- Validate `(domain, sockType, proto)` for curated `Net.socket` scope (`TCP`, `UDP`, and `AF_UNIX` accepting `0` or `PF_UNIX`), returning exact Linux errno before C shim / kernel entry. -/
def validateSocketArgs (domain : SockDomain) (sockType : SockType) (proto : UInt32) : Option Errno :=
  match domain with
  | .unix =>
    if proto == 0 || proto == PF_UNIX then none
    else some Errno.EPROTONOSUPPORT
  | .inet | .inet6 =>
    if proto >= IPPROTO_MAX then some Errno.EINVAL
    else
      match sockType with
      | .seqpacket => some Errno.ESOCKTNOSUPPORT
      | .stream =>
        if proto == 0 || proto == IPPROTO_TCP then none
        else some Errno.EPROTONOSUPPORT
      | .dgram =>
        if proto == 0 || proto == IPPROTO_UDP then none
        else some Errno.EPROTONOSUPPORT

/-- Validate `(domain, sockType)` for `Net.socketpair` (`AF_UNIX` only), returning exact Linux errno before C shim / kernel entry. -/
def validateSocketpairArgs (domain : SockDomain) (sockType : SockType) : Option Errno :=
  match domain with
  | .unix => none
  | .inet | .inet6 =>
    some (if sockType == .seqpacket then Errno.ESOCKTNOSUPPORT else Errno.EOPNOTSUPP)

/-- Returns `true` iff `count` is a valid `SCM_RIGHTS` descriptor batch count (`1..MAX_SCM_FDS`). -/
def isValidScmCount (count : Nat) : Bool :=
  count > 0 && count ≤ MAX_SCM_FDS

/-- Returns `true` iff `ifname` is a valid C string for `struct ifreq.ifr_name` (no embedded NUL and `< IFNAMSIZ`). -/
def isValidIfname (ifname : ByteArray) : Bool :=
  ifname.size < IFNAMSIZ && !hasEmbeddedNul ifname

/-- Raw C-ABI tuple `(familyTag, ipv4Addr, ipv6Hi, ipv6Lo, port, flowinfo, scopeId, unixPath)` exchanged with `net_shim.c`. -/
abbrev RawSockAddrTuple :=
  UInt8 × UInt32 × UInt64 × UInt64 × UInt16 × UInt32 × UInt32 × ByteArray

/-- Encode `SockAddr` into `RawSockAddrTuple` for C-ABI transport. -/
def SockAddr.toRawTuple : SockAddr → RawSockAddrTuple
  | .ipv4 addr port => (0, addr, 0, 0, port, 0, 0, ByteArray.mk #[])
  | .ipv6 hi lo port flow scope => (1, 0, hi, lo, port, flow, scope, ByteArray.mk #[])
  | .unix path => (2, 0, 0, 0, 0, 0, 0, path)

/-- Decode `RawSockAddrTuple` returned by `net_shim.c` (`accept4`, `getsockname`) into `SockAddr`. -/
def SockAddr.ofRawTuple (t : RawSockAddrTuple) : SockAddr :=
  let (tag, v4, hi, lo, port, flow, scope, path) := t
  match tag.toNat with
  | 0 => .ipv4 v4 port
  | 1 => .ipv6 hi lo port flow scope
  | _ => .unix path

/-- Curated socket options readable via `getsockopt(2)` (`SOL_SOCKET`). -/
inductive SockOpt where
  /-- Query and clear pending asynchronous socket error (`SO_ERROR`). -/
  | error
  /-- Query local address reuse flag (`SO_REUSEADDR`, `0` or `1`). -/
  | reuseAddr
  deriving Repr, DecidableEq, BEq

/-- Encode `SockOpt` into a portable C-ABI tag (`0..1`). -/
def SockOpt.toTag : SockOpt → UInt32
  | .error => 0
  | .reuseAddr => 1

/-- Curated socket options writable via `setsockopt(2)` (`SOL_SOCKET`). -/
inductive SetSockOpt where
  /-- Enable (`val != 0`) or disable (`val == 0`) local address reuse (`SO_REUSEADDR`). -/
  | reuseAddr
  deriving Repr, DecidableEq, BEq

/-- Encode `SetSockOpt` into a portable C-ABI tag. -/
def SetSockOpt.toTag : SetSockOpt → UInt32
  | .reuseAddr => 0

/-- Portable per-call message flags for `recvfrom(2)` and `sendto(2)`. -/
structure MsgFlags where
  /-- Suppress `SIGPIPE` generation on broken stream peers (`MSG_NOSIGNAL`). -/
  nosignal : Bool := false
  /-- Enable non-blocking operation for this call (`MSG_DONTWAIT`). -/
  dontwait : Bool := false
  /-- Peek at incoming receive queue without consuming data (`MSG_PEEK`). -/
  peek : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `MsgFlags` into a 3-bit portable bitmask (`0..7`) decoded by `net_shim.c`. -/
def MsgFlags.toBits (f : MsgFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.nosignal 0 ||| bit f.dontwait 1 ||| bit f.peek 2

/-- Portable direction selector for `shutdown(2)`. -/
inductive ShutHow where
  /-- Disallow further receptions (`SHUT_RD`, `0`). -/
  | rd
  /-- Disallow further transmissions (`SHUT_WR`, `1`). -/
  | wr
  /-- Disallow further receptions and transmissions (`SHUT_RDWR`, `2`). -/
  | rdwr
  deriving Repr, DecidableEq, BEq

/-- Encode `ShutHow` into a portable C-ABI tag (`0..2`). -/
def ShutHow.toTag : ShutHow → UInt32
  | .rd => 0
  | .wr => 1
  | .rdwr => 2

/-- Curated network interface `ioctl(2)` commands (`SIOCGIFFLAGS`, `SIOCSIFFLAGS`). -/
inductive NetIoctlOp where
  /-- Query 16-bit `ifr_flags` for a named network interface (`SIOCGIFFLAGS`). -/
  | getIfFlags
  /-- Set `ifr_flags` (lower 16 bits of `flags`) for a named network interface (`SIOCSIFFLAGS`, returning `0`). -/
  | setIfFlags (flags : UInt32)
  deriving Repr, DecidableEq, BEq

/-- Encode `NetIoctlOp` into `(cmdTag, arg)` for `leanswe_sys_net_ioctl`. -/
def NetIoctlOp.toRaw : NetIoctlOp → UInt32 × UInt32
  | .getIfFlags => (0, 0)
  | .setIfFlags flags => (1, flags)

/-- Semantic classification of Linux `Net` syscall `Errno` outcomes for error-coverage auditing. -/
inductive NetErrorKind where
  /-- Closed/invalid descriptor or non-socket descriptor (`EBADF`, `ENOTSOCK`, `ENOTTY`). -/
  | badFd
  /-- Invalid argument, unsupported socket/protocol/family combination, or malformed path/ifname (`EINVAL`, `EAFNOSUPPORT`, `EPROTONOSUPPORT`, `ESOCKTNOSUPPORT`, `EOPNOTSUPP`, `EPFNOSUPPORT`, `ENOPROTOOPT`, `EPROTOTYPE`, `EDESTADDRREQ`, `EMSGSIZE`, `ENOSYS`). -/
  | invalidArg
  /-- Address/path collision, unavailable bind address, missing `AF_UNIX` path, or missing interface (`EADDRINUSE`, `EADDRNOTAVAIL`, `ENOENT`, `ENODEV`). -/
  | addressError
  /-- Non-blocking operation would block or asynchronous connect in progress (`EAGAIN`, `EINPROGRESS`, `EALREADY`). -/
  | wouldBlockOrInProgress
  /-- Connection lifecycle or transport error (`EISCONN`, `ENOTCONN`, `EPIPE`, `ECONNRESET`, `ECONNREFUSED`, `ECONNABORTED`, `ESHUTDOWN`, `ETIMEDOUT`, `ENETDOWN`, `ENETUNREACH`, `EHOSTUNREACH`, `EPROTO`). -/
  | connectionState
  /-- Insufficient privilege or permission (`EACCES`, `EPERM`). -/
  | permissionDenied
  /-- Transient signal, I/O, or kernel resource exhaustion (`EINTR`, `EIO`, `ENOMEM`, `ENOBUFS`, `ENFILE`, `EMFILE`, `ENOSPC`, `EBUSY`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq

/-- Classify any Linux `Errno` into a `NetErrorKind`. -/
def NetErrorKind.ofErrno (e : Errno) : NetErrorKind :=
  if e == Errno.EBADF || e == Errno.ENOTSOCK || e == Errno.ENOTTY then .badFd
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
  else .transientOrResource

/-- Monad-parameterized capability bundle for all 15 curated Linux `Net` syscalls. -/
structure NetOpsM (m : Type → Type) (fd : Type) where
  /-- Create an unbound socket endpoint via `socket(2)`. -/
  socket : SockDomain → SockType → SockFlags → UInt32 → m (Except Errno fd)
  /-- Create a connected pair of anonymous local sockets via `socketpair(2)`. -/
  socketpair : SockDomain → SockType → SockFlags → m (Except Errno (fd × fd))
  /-- Bind a socket to a local `SockAddr` via `bind(2)`. -/
  bind : fd → SockAddr → m (Except Errno Unit)
  /-- Mark a stream or seqpacket socket as passive listener with `backlog` via `listen(2)`. -/
  listen : fd → UInt32 → m (Except Errno Unit)
  /-- Accept a pending connection atomically with `SockFlags` via `accept4(2)`. -/
  accept4 : fd → SockFlags → m (Except Errno (fd × SockAddr))
  /-- Initiate a connection to peer `SockAddr` via `connect(2)`. -/
  connect : fd → SockAddr → m (Except Errno Unit)
  /-- Read a curated `SOL_SOCKET` option (`SO_ERROR`, `SO_REUSEADDR`) via `getsockopt(2)`. -/
  getsockopt : fd → SockOpt → m (Except Errno UInt32)
  /-- Set a curated `SOL_SOCKET` option (`SO_REUSEADDR`) via `setsockopt(2)`. -/
  setsockopt : fd → SetSockOpt → UInt32 → m (Except Errno Unit)
  /-- Query the local `SockAddr` currently bound to `fd` via `getsockname(2)`. -/
  getsockname : fd → m (Except Errno SockAddr)
  /-- Receive up to `min maxBytes MAX_READ_BYTES` bytes from `fd` via `recvfrom(2)`. -/
  recvfrom : fd → UInt32 → MsgFlags → m (Except Errno ByteArray)
  /-- Send bytes on `fd` with `MsgFlags` (`MSG_NOSIGNAL`) via `sendto(2)`. -/
  sendto : fd → ByteArray → MsgFlags → m (Except Errno UInt32)
  /-- Shut down part or all of a full-duplex connection via `shutdown(2)`. -/
  shutdown : fd → ShutHow → m (Except Errno Unit)
  /-- Pass `1..32` open file descriptors over an `AF_UNIX` socket via `SCM_RIGHTS` `sendmsg(2)` (rejects non-`AF_UNIX` sockets with `EOPNOTSUPP`). -/
  sendmsg : fd → Array fd → m (Except Errno Unit)
  /-- Receive up to `maxFds` (`1..32`) file descriptors with `MSG_CMSG_CLOEXEC` via `SCM_RIGHTS` `recvmsg(2)`. `net_shim.c` reads through a 1-byte dummy `iovec`, so each completed call consumes and discards 1 byte of stream payload (`SOCK_STREAM`, or `0` bytes at EOF) or truncates and discards one entire datagram/seqpacket message (`SOCK_DGRAM`/`SOCK_SEQPACKET`), matching `popRecvmsgUnit` in the model (`#[]` when no `SCM_RIGHTS` ancillary data is present). Sets `msg_controllen = CMSG_LEN(maxFds * sizeof(int))`, and on `MSG_CTRUNC` (or `> maxFds` received descriptors) closes all received FDs and returns `EPROTO`. -/
  recvmsg : fd → UInt32 → m (Except Errno (Array fd))
  /-- Execute a curated network interface `ioctl(2)` (`SIOCGIFFLAGS`, `SIOCSIFFLAGS`). -/
  ioctl : fd → NetIoctlOp → ByteArray → m (Except Errno UInt32)

/-- Real-world `IO` specialization of `NetOpsM` using ABA-safe `RawFd` handles. -/
abbrev NetOps := NetOpsM IO RawFd

/-- Monad-parameterized low-level C-ABI syscall hooks for all 15 `Net` syscalls. -/
structure PosixNetOpsM (m : Type → Type) (fd : Type) where
  /-- Raw `socket(2)` hook accepting `(domainTag, typeTag, sockFlagBits, proto)`. -/
  socket : UInt32 → UInt32 → UInt32 → UInt32 → m (Except Errno fd)
  /-- Raw `socketpair(2)` hook accepting `(domainTag, typeTag, sockFlagBits)`. -/
  socketpair : UInt32 → UInt32 → UInt32 → m (Except Errno (fd × fd))
  /-- Raw `bind(2)` hook accepting `RawSockAddrTuple`. -/
  bind : fd → RawSockAddrTuple → m (Except Errno Unit)
  /-- Raw `listen(2)` hook accepting `(fd, backlog)`. -/
  listen : fd → UInt32 → m (Except Errno Unit)
  /-- Raw `accept4(2)` hook accepting `(fd, sockFlagBits)` and returning `(clientFd, RawSockAddrTuple)`. -/
  accept4 : fd → UInt32 → m (Except Errno (fd × RawSockAddrTuple))
  /-- Raw `connect(2)` hook accepting `RawSockAddrTuple`. -/
  connect : fd → RawSockAddrTuple → m (Except Errno Unit)
  /-- Raw `getsockopt(2)` hook accepting `(fd, sockOptTag)`. -/
  getsockopt : fd → UInt32 → m (Except Errno UInt32)
  /-- Raw `setsockopt(2)` hook accepting `(fd, setSockOptTag, val)`. -/
  setsockopt : fd → UInt32 → UInt32 → m (Except Errno Unit)
  /-- Raw `getsockname(2)` hook returning `RawSockAddrTuple`. -/
  getsockname : fd → m (Except Errno RawSockAddrTuple)
  /-- Raw `recvfrom(2)` hook accepting `(fd, maxBytes, msgFlagBits)`. -/
  recvfrom : fd → UInt32 → UInt32 → m (Except Errno ByteArray)
  /-- Raw `sendto(2)` hook accepting `(fd, data, msgFlagBits)`. -/
  sendto : fd → ByteArray → UInt32 → m (Except Errno UInt32)
  /-- Raw `shutdown(2)` hook accepting `(fd, shutHowTag)`. -/
  shutdown : fd → UInt32 → m (Except Errno Unit)
  /-- Raw `SCM_RIGHTS` `sendmsg(2)` hook accepting `(fd, fds)`. -/
  sendmsg : fd → Array fd → m (Except Errno Unit)
  /-- Raw `SCM_RIGHTS` `recvmsg(2)` hook accepting `(fd, maxFds)`. -/
  recvmsg : fd → UInt32 → m (Except Errno (Array fd))
  /-- Raw `ioctl(2)` hook accepting `(fd, opTag, flagsArg, ifname)`. -/
  ioctl : fd → UInt32 → UInt32 → ByteArray → m (Except Errno UInt32)

/-- Concrete `IO` specialization of `PosixNetOpsM` supplied by `Interface.lean` and backed by `net_shim.c`. -/
abbrev PosixNetOps := PosixNetOpsM IO RawFd

/-- Logical handle identifier used by the relational `Net` world model and fuzzer traces. -/
abbrev HandleId := Nat

/-- One syscall request in a `Net` world-model trace (covers all 15 curated syscalls). -/
inductive NetReq where
  /-- `socket(domain, sockType, flags, proto)`. -/
  | socket (domain : SockDomain) (sockType : SockType) (flags : SockFlags) (proto : UInt32)
  /-- `socketpair(domain, sockType, flags)`. -/
  | socketpair (domain : SockDomain) (sockType : SockType) (flags : SockFlags)
  /-- `bind(hid, addr)`. -/
  | bind (hid : HandleId) (addr : SockAddr)
  /-- `listen(hid, backlog)`. -/
  | listen (hid : HandleId) (backlog : UInt32)
  /-- `accept4(hid, flags)`. -/
  | accept4 (hid : HandleId) (flags : SockFlags)
  /-- `connect(hid, addr)`. -/
  | connect (hid : HandleId) (addr : SockAddr)
  /-- `getsockopt(hid, opt)`. -/
  | getsockopt (hid : HandleId) (opt : SockOpt)
  /-- `setsockopt(hid, opt, val)`. -/
  | setsockopt (hid : HandleId) (opt : SetSockOpt) (val : UInt32)
  /-- `getsockname(hid)`. -/
  | getsockname (hid : HandleId)
  /-- `recvfrom(hid, maxBytes, flags)`. -/
  | recvfrom (hid : HandleId) (maxBytes : UInt32) (flags : MsgFlags)
  /-- `sendto(hid, data, flags)`. -/
  | sendto (hid : HandleId) (data : ByteArray) (flags : MsgFlags)
  /-- `shutdown(hid, how)`. -/
  | shutdown (hid : HandleId) (how : ShutHow)
  /-- `sendmsg(hid, fds)`. -/
  | sendmsg (hid : HandleId) (fds : Array HandleId)
  /-- `recvmsg(hid, maxFds)`. -/
  | recvmsg (hid : HandleId) (maxFds : UInt32)
  /-- `ioctl(hid, op, ifname)`. -/
  | ioctl (hid : HandleId) (op : NetIoctlOp) (ifname : ByteArray)
  deriving Repr, DecidableEq, BEq

/-- Raw kernel outcome observed for one `NetReq`. -/
inductive NetOutcome where
  /-- `socket` succeeded and allocated `hid`. -/
  | opened (hid : HandleId)
  /-- `socketpair` succeeded and allocated `(hid0, hid1)`. -/
  | pair (hid0 hid1 : HandleId)
  /-- `accept4` succeeded and returned `(hid, peerAddr)`. -/
  | accepted (hid : HandleId) (peerAddr : SockAddr)
  /-- `getsockname` succeeded and returned `sa`. -/
  | addr (sa : SockAddr)
  /-- `recvfrom` succeeded and returned `data`. -/
  | bytes (data : ByteArray)
  /-- `getsockopt`, `sendto`, or `ioctl` succeeded and returned `val`. -/
  | u32 (val : UInt32)
  /-- `recvmsg` succeeded and returned `handles`. -/
  | fds (handles : Array HandleId)
  /-- Unit-returning syscall succeeded (`bind`, `listen`, `connect`, `setsockopt`, `shutdown`, `sendmsg`). -/
  | unit
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, DecidableEq, BEq

end LeanSwe.LinuxSyscall.Net
