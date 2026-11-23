import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Impl

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_socket"]
private opaque rawSocket :
    UInt32 → UInt32 → UInt32 → UInt32 → IO (Except Errno RawFd)

@[extern "leanswe_sys_socketpair"]
private opaque rawSocketpair :
    UInt32 → UInt32 → UInt32 → IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_sys_bind"]
private opaque rawBind :
    @& RawFd → @& RawSockAddrTuple → IO (Except Errno Unit)

@[extern "leanswe_sys_listen"]
private opaque rawListen :
    @& RawFd → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_accept4"]
private opaque rawAccept4 :
    @& RawFd → UInt32 → IO (Except Errno (RawFd × RawSockAddrTuple))

@[extern "leanswe_sys_connect"]
private opaque rawConnect :
    @& RawFd → @& RawSockAddrTuple → IO (Except Errno Unit)

@[extern "leanswe_sys_getsockopt"]
private opaque rawGetsockopt :
    @& RawFd → UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_setsockopt"]
private opaque rawSetsockopt :
    @& RawFd → UInt32 → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_getsockname"]
private opaque rawGetsockname :
    @& RawFd → IO (Except Errno RawSockAddrTuple)

@[extern "leanswe_sys_recvfrom"]
private opaque rawRecvfrom :
    @& RawFd → UInt32 → UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_sendto"]
private opaque rawSendto :
    @& RawFd → @& ByteArray → UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_shutdown"]
private opaque rawShutdown :
    @& RawFd → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_sendmsg_scm"]
private opaque rawSendmsg :
    @& RawFd → @& Array RawFd → IO (Except Errno Unit)

@[extern "leanswe_sys_recvmsg_scm"]
private opaque rawRecvmsg :
    @& RawFd → UInt32 → IO (Except Errno (Array RawFd))

@[extern "leanswe_sys_net_ioctl"]
private opaque rawNetIoctl :
    @& RawFd → UInt32 → UInt32 → @& ByteArray → IO (Except Errno UInt32)

private def posixNetOps : Internal.PosixNetOps :=
  { socket := rawSocket
    socketpair := rawSocketpair
    bind := rawBind
    listen := rawListen
    accept4 := rawAccept4
    connect := rawConnect
    getsockopt := rawGetsockopt
    setsockopt := rawSetsockopt
    getsockname := rawGetsockname
    recvfrom := rawRecvfrom
    sendto := rawSendto
    shutdown := rawShutdown
    sendmsg := rawSendmsg
    recvmsg := rawRecvmsg
    ioctl := rawNetIoctl }

/-- Default Linux `Net` syscall bundle backed by `LeanSwe/LinuxSyscall/c/net_shim.c`. -/
def defaultOps : NetOps :=
  Internal.mkNetOps posixNetOps

/-- Create a socket endpoint via Linux `socket(2)`. -/
@[inline] def socket (domain : SockDomain) (sockType : SockType) (flags : SockFlags := {})
    (proto : UInt32 := 0) : IO (Except Errno RawFd) :=
  defaultOps.socket domain sockType flags proto

/-- Create a connected pair of anonymous local sockets via Linux `socketpair(2)`. -/
@[inline] def socketpair (domain : SockDomain) (sockType : SockType) (flags : SockFlags := {}) :
    IO (Except Errno (RawFd × RawFd)) :=
  defaultOps.socketpair domain sockType flags

/-- Bind socket `fd` to local address `addr` via Linux `bind(2)`. -/
@[inline] def bind (fd : RawFd) (addr : SockAddr) : IO (Except Errno Unit) :=
  defaultOps.bind fd addr

/-- Mark stream or seqpacket socket `fd` as a passive listener via Linux `listen(2)`. -/
@[inline] def listen (fd : RawFd) (backlog : UInt32 := 128) : IO (Except Errno Unit) :=
  defaultOps.listen fd backlog

/-- Accept a pending connection on listener `fd` atomically with `flags` via Linux `accept4(2)`. -/
@[inline] def accept4 (fd : RawFd) (flags : SockFlags := {}) : IO (Except Errno (RawFd × SockAddr)) :=
  defaultOps.accept4 fd flags

/-- Initiate a connection on `fd` to peer `addr` via Linux `connect(2)`. -/
@[inline] def connect (fd : RawFd) (addr : SockAddr) : IO (Except Errno Unit) :=
  defaultOps.connect fd addr

/-- Read a curated `SOL_SOCKET` option (`SO_ERROR`, `SO_REUSEADDR`) via Linux `getsockopt(2)`. -/
@[inline] def getsockopt (fd : RawFd) (opt : SockOpt) : IO (Except Errno UInt32) :=
  defaultOps.getsockopt fd opt

/-- Set a curated `SOL_SOCKET` option (`SO_REUSEADDR`) via Linux `setsockopt(2)`. -/
@[inline] def setsockopt (fd : RawFd) (opt : SetSockOpt) (val : UInt32) : IO (Except Errno Unit) :=
  defaultOps.setsockopt fd opt val

/-- Query the current local `SockAddr` of `fd` via Linux `getsockname(2)`. -/
@[inline] def getsockname (fd : RawFd) : IO (Except Errno SockAddr) :=
  defaultOps.getsockname fd

/-- Receive up to `min maxBytes MAX_READ_BYTES` bytes from `fd` via Linux `recvfrom(2)`. -/
@[inline] def recvfrom (fd : RawFd) (maxBytes : UInt32) (flags : MsgFlags := {}) :
    IO (Except Errno ByteArray) :=
  defaultOps.recvfrom fd maxBytes flags

/-- Send `data` over `fd` with `flags` (`MSG_NOSIGNAL`) via Linux `sendto(2)`. -/
@[inline] def sendto (fd : RawFd) (data : ByteArray) (flags : MsgFlags := { nosignal := true }) :
    IO (Except Errno UInt32) :=
  defaultOps.sendto fd data flags

/-- Shut down part or all of full-duplex connection `fd` via Linux `shutdown(2)`. -/
@[inline] def shutdown (fd : RawFd) (how : ShutHow) : IO (Except Errno Unit) :=
  defaultOps.shutdown fd how

/-- Send `1..32` open `RawFd` handles over `AF_UNIX` socket `fd` via `SCM_RIGHTS` `sendmsg(2)` (rejects non-`AF_UNIX` sockets with `EOPNOTSUPP`). -/
@[inline] def sendmsg (fd : RawFd) (fds : Array RawFd) : IO (Except Errno Unit) :=
  defaultOps.sendmsg fd fds

/-- Receive up to `maxFds` (`1..32`) `RawFd` handles with `MSG_CMSG_CLOEXEC` via `SCM_RIGHTS` `recvmsg(2)`. `net_shim.c` reads through a 1-byte dummy `iovec`, so each completed call consumes and discards 1 byte of stream payload (`SOCK_STREAM`, or `0` bytes at EOF) or truncates and discards one entire datagram/seqpacket message (`SOCK_DGRAM`/`SOCK_SEQPACKET`), matching `popRecvmsgUnit` in the model (`#[]` when no `SCM_RIGHTS` ancillary data is present). Sets `msg_controllen = CMSG_LEN(maxFds * sizeof(int))`, and on `MSG_CTRUNC` (or `> maxFds` received descriptors) closes all received FDs and returns `EPROTO`. -/
@[inline] def recvmsg (fd : RawFd) (maxFds : UInt32) : IO (Except Errno (Array RawFd)) :=
  defaultOps.recvmsg fd maxFds

/-- Execute a curated network interface `ioctl(2)` (`SIOCGIFFLAGS`, `SIOCSIFFLAGS`) on `fd`. -/
@[inline] def ioctl (fd : RawFd) (op : NetIoctlOp) (ifname : ByteArray) :
    IO (Except Errno UInt32) :=
  defaultOps.ioctl fd op ifname

end LeanSwe.LinuxSyscall.Net
