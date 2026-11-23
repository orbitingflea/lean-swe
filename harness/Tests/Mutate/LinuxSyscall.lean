import Tests.Common
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Process.Interface
import Fuzz.Passwd.Suite
import Fuzz.Passwd.Checks
import Fuzz.Dns.Suite
import Fuzz.LinuxSyscall.Sandbox.Strace
import Fuzz.LinuxSyscall.TimeRand.Strace
import Fuzz.LinuxSyscall.Files.Strace
import Fuzz.LinuxSyscall.Poll.Strace
import Fuzz.LinuxSyscall.Net.Strace
import Fuzz.LinuxSyscall.ProcessEnv
import Fuzz.LinuxSyscall.Process.Fuzz
import Fuzz.LinuxSyscall.Process.Strace

namespace Tests.Mutate.LinuxSyscall

open LeanSwe
open Tests.Common

private def runFilesMkOpsUnitTests : IO Unit := do
  let sentinelErr := LeanSwe.LinuxSyscall.Errno.ENOSYS
  let raw : LeanSwe.LinuxSyscall.Files.Internal.PosixFilesOps :=
    { openat := fun _ _ _ _ => pure (.error sentinelErr)
      openat2 := fun _ _ _ _ _ => pure (.error sentinelErr)
      close := fun _ => pure (.error sentinelErr)
      read := fun _ _ => pure (.error sentinelErr)
      write := fun _ _ => pure (.error sentinelErr)
      fstat := fun _ => pure (.error sentinelErr)
      fstatat := fun _ _ _ => pure (.error sentinelErr)
      faccessat := fun _ _ _ _ => pure (.error sentinelErr)
      mkdirat := fun _ _ _ => pure (.error sentinelErr)
      unlinkat := fun _ _ _ => pure (.error sentinelErr)
      renameat2 := fun _ _ _ _ _ => pure (.error sentinelErr)
      symlinkat := fun _ _ _ => pure (.error sentinelErr)
      readlinkat := fun _ _ _ => pure (.error sentinelErr)
      getdents64 := fun _ _ => pure (.error sentinelErr)
      fchmodat := fun _ _ _ => pure (.error sentinelErr)
      fchmod := fun _ _ => pure (.error sentinelErr)
      flock := fun _ _ => pure (.error sentinelErr)
      fcntl := fun _ _ _ => pure (.error sentinelErr)
      fsync := fun _ => pure (.error sentinelErr)
      getcwd := fun _ => pure (.error sentinelErr)
      lseek := fun _ _ _ => pure (.error sentinelErr)
      reopenReadOnly := fun _ => pure (.error sentinelErr)
      dupStdio := fun _ => pure (.error sentinelErr) }
  let ops := LeanSwe.LinuxSyscall.Files.Internal.mkFilesOps raw
  let nul := ByteArray.mk #[97, 0, 98]
  let okP := "ok".toUTF8
  let expectEinval {α : Type} (label : String) (act : IO (Except LeanSwe.LinuxSyscall.Errno α)) : IO Unit := do
    match ← act with
    | .error e =>
      if e != LeanSwe.LinuxSyscall.Errno.EINVAL then
        throw (IO.userError s!"mkFilesOps {label}: expected EINVAL, got {e}")
    | .ok _ => throw (IO.userError s!"mkFilesOps {label}: expected EINVAL, got ok")
  let expectEnosys {α : Type} (label : String) (act : IO (Except LeanSwe.LinuxSyscall.Errno α)) : IO Unit := do
    match ← act with
    | .error e =>
      if e != sentinelErr then
        throw (IO.userError s!"mkFilesOps {label}: expected ENOSYS, got {e}")
    | .ok _ => throw (IO.userError s!"mkFilesOps {label}: expected ENOSYS, got ok")
  expectEinval "openat" (ops.openat none nul {} 0)
  expectEnosys "openat pass" (ops.openat none okP {} 0)
  expectEinval "openat2" (ops.openat2 none nul {})
  expectEnosys "openat2 pass" (ops.openat2 none okP {})
  expectEinval "fstatat" (ops.fstatat none nul {})
  expectEinval "fstatat eaccess" (ops.fstatat none okP { eaccess := true })
  expectEnosys "fstatat pass" (ops.fstatat none okP {})
  expectEinval "faccessat" (ops.faccessat none nul {} {})
  expectEnosys "faccessat pass" (ops.faccessat none okP {} {})
  expectEinval "mkdirat" (ops.mkdirat none nul 0o755)
  expectEnosys "mkdirat pass" (ops.mkdirat none okP 0o755)
  expectEinval "unlinkat" (ops.unlinkat none nul false)
  expectEnosys "unlinkat pass" (ops.unlinkat none okP false)
  expectEinval "renameat2 old" (ops.renameat2 none nul none okP {})
  expectEinval "renameat2 new" (ops.renameat2 none okP none nul {})
  expectEnosys "renameat2 pass" (ops.renameat2 none okP none okP {})
  expectEinval "symlinkat target" (ops.symlinkat nul none okP)
  expectEinval "symlinkat link" (ops.symlinkat okP none nul)
  expectEnosys "symlinkat pass" (ops.symlinkat okP none okP)
  expectEinval "readlinkat" (ops.readlinkat none nul 64)
  expectEnosys "readlinkat pass" (ops.readlinkat none okP 64)
  expectEinval "fchmodat" (ops.fchmodat none nul 0o644)
  expectEnosys "fchmodat pass" (ops.fchmodat none okP 0o644)

private def runDnsUnitTests : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"{label} failed")
  match ← LeanSwe.LinuxSyscall.Dns.getaddrinfo "" with
  | .error e =>
    checkB "dns empty invalidHost" (e.kind == .invalidHost && e.gaiCode == LeanSwe.LinuxSyscall.Dns.EAI_NONAME)
  | .ok _ => throw (IO.userError "dns empty unexpectedly succeeded")
  match ← LeanSwe.LinuxSyscall.Dns.getaddrinfo "a\x00b" with
  | .error e =>
    checkB "dns nul invalidHost" (e.kind == .invalidHost && e.gaiCode == LeanSwe.LinuxSyscall.Dns.EAI_NONAME)
  | .ok _ => throw (IO.userError "dns nul unexpectedly succeeded")
  checkB "dns 127.0.0.1" ((← LeanSwe.LinuxSyscall.Dns.getaddrinfo "127.0.0.1") == .ok [.ipv4 127 0 0 1])
  checkB "dns ::1" ((← LeanSwe.LinuxSyscall.Dns.getaddrinfo "::1") == .ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0])
  checkB "dns ::ffff:127.0.0.1 any"
    ((← LeanSwe.LinuxSyscall.Dns.getaddrinfo "::ffff:127.0.0.1" { family := .ipv4, sockType := .any }) ==
      .ok [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])
  match ← LeanSwe.LinuxSyscall.Dns.getaddrinfo "fe80::1%lo" with
  | .ok addrs => checkB "dns scoped fe80::1%lo" (!addrs.isEmpty && addrs.all fun a => a.isIpv6 && !a.isUnscoped)
  | .error e => throw (IO.userError s!"dns fe80::1%lo failed: {repr e}")
  match ← LeanSwe.LinuxSyscall.Dns.getaddrinfo "bad host" with
  | .error e => checkB "dns bad host" (e.kind == .nameNotFound)
  | .ok _ => throw (IO.userError "dns bad host unexpectedly succeeded")
  let addrs : List LeanSwe.LinuxSyscall.Dns.DnsAddr :=
    [.ipv4 10 0 0 1, .ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7]
  checkB "dns codec roundtrip"
    (LeanSwe.LinuxSyscall.Dns.Internal.decodeRecords (LeanSwe.LinuxSyscall.Dns.Internal.encodeRecords addrs) == .ok addrs)
  let mockSys := LeanSwe.LinuxSyscall.Dns.Internal.mkDnsOps
    { getaddrinfo := fun _ _ _ => pure (.error (LeanSwe.LinuxSyscall.Dns.EAI_SYSTEM, LeanSwe.LinuxSyscall.Errno.ENOENT, "mock sys".toUTF8)) }
  match ← mockSys.getaddrinfo "example.invalid" {} with
  | .error e =>
    checkB "dns mock EAI_SYSTEM" (e.kind == .systemError && e.errno? == some LeanSwe.LinuxSyscall.Errno.ENOENT && e.message == "mock sys")
  | .ok _ => throw (IO.userError "dns mock EAI_SYSTEM unexpectedly succeeded")
  let mockBadUtf8 := LeanSwe.LinuxSyscall.Dns.Internal.mkDnsOps
    { getaddrinfo := fun _ _ _ => pure (.error (LeanSwe.LinuxSyscall.Dns.EAI_FAIL, 0, ByteArray.mk #[0xff, 0xfe])) }
  match ← mockBadUtf8.getaddrinfo "example.invalid" {} with
  | .error e => checkB "dns mock non-utf8" (e.kind == .nameNotFound && e.gaiCode == LeanSwe.LinuxSyscall.Dns.EAI_FAIL && e.message == "<non-utf8:2B>")
  | .ok _ => throw (IO.userError "dns mock non-utf8 unexpectedly succeeded")

private def runPollOpsUnitTests : IO Unit := do
  let mkMock (revBytes : ByteArray) (failPpoll? : Option LeanSwe.LinuxSyscall.Errno := none) :
      LeanSwe.LinuxSyscall.Poll.PosixPollOpsM (StateM Nat) Nat :=
    { ppoll := fun _ _ _ _ _ => do
        modify (· + 1)
        return match failPpoll? with
          | some e => .error e
          | none => .ok revBytes
      eventfd2 := fun _ _ => do
        modify (· + 1)
        return .ok 7 }
  let opsOk := LeanSwe.LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock (ByteArray.mk #[0x1f]))
  let opsShort := LeanSwe.LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock ByteArray.empty)
  let opsErr := LeanSwe.LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock ByteArray.empty (some LeanSwe.LinuxSyscall.Errno.ENOSYS))
  let (rNeg, cNeg) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := -1, nsec := 0 })).run 0
  checkUnit "mkPollOpsM neg sec" (rNeg == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cNeg == 0)
  let (rNsec, cNsec) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := 0, nsec := 1000000000 })).run 0
  checkUnit "mkPollOpsM big nsec" (rNsec == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cNsec == 0)
  let bigEntries := Array.replicate (LeanSwe.LinuxSyscall.Poll.MAX_POLL_NFDS + 1) (1, { pollin := true })
  let (rBig, cBig) := (opsOk.ppoll bigEntries none).run 0
  checkUnit "mkPollOpsM max nfds" (rBig == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cBig == 0)
  let (rMismatch, cMismatch) := (opsShort.ppoll #[(1, { pollin := true })] none).run 0
  checkUnit "mkPollOpsM revBytes len mismatch" (rMismatch == .error LeanSwe.LinuxSyscall.Errno.EIO && cMismatch == 1)
  let (rRawErr, cRawErr) := (opsErr.ppoll #[(1, { pollin := true })] (some { sec := 1, nsec := 5 })).run 0
  checkUnit "mkPollOpsM raw err prop" (rRawErr == .error LeanSwe.LinuxSyscall.Errno.ENOSYS && cRawErr == 1)
  let (rOk, cOk) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := 0, nsec := 0 })).run 0
  checkUnit "mkPollOpsM ok" (rOk == .ok #[{ pollin := true, pollout := true, pollerr := true, pollhup := true, pollnval := true }] && cOk == 1)
  let (rEfd, cEfd) := (opsOk.eventfd2 3 { nonblock := true, cloexec := true, semaphore := false }).run 0
  checkUnit "mkPollOpsM eventfd2" (rEfd == .ok 7 && cEfd == 1)

private def runNetOpsUnitTests : IO Unit := do
  let sentinel := LeanSwe.LinuxSyscall.Errno.ENOSYS
  let mockRaw : LeanSwe.LinuxSyscall.Net.PosixNetOpsM (StateM Nat) Nat :=
    { socket := fun _ _ _ _ => modify (· + 1) *> pure (.error sentinel)
      socketpair := fun _ _ _ => modify (· + 1) *> pure (.error sentinel)
      bind := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      listen := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      accept4 := fun _ _ => modify (· + 1) *> pure (.ok (9, (0, LeanSwe.LinuxSyscall.Net.INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.empty)))
      connect := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      getsockopt := fun _ _ => modify (· + 1) *> pure (.ok 1)
      setsockopt := fun _ _ _ => modify (· + 1) *> pure (.ok ())
      getsockname := fun _ => modify (· + 1) *> pure (.ok (2, 0, 0, 0, 0, 0, 0, "u".toUTF8))
      recvfrom := fun _ _ _ => modify (· + 1) *> pure (.ok "hi".toUTF8)
      sendto := fun _ _ _ => modify (· + 1) *> pure (.ok 2)
      shutdown := fun _ _ => modify (· + 1) *> pure (.ok ())
      sendmsg := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      recvmsg := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      ioctl := fun _ _ _ _ => modify (· + 1) *> pure (.error sentinel) }
  let ops := LeanSwe.LinuxSyscall.Net.Internal.mkNetOpsM mockRaw
  let (rSock1, cSock1) := (ops.socket .unix .stream {} 6).run 0
  checkUnit "mkNetOpsM socket unix proto" (rSock1 == .error LeanSwe.LinuxSyscall.Errno.EPROTONOSUPPORT && cSock1 == 0)
  let (rSock2, cSock2) := (ops.socket .inet .stream {} 263).run 0
  checkUnit "mkNetOpsM socket inet proto>=263" (rSock2 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cSock2 == 0)
  let (rSock3, cSock3) := (ops.socket .inet .stream {} 6).run 0
  checkUnit "mkNetOpsM socket valid passthrough" (rSock3 == .error sentinel && cSock3 == 1)
  let (rPair1, cPair1) := (ops.socketpair .inet .stream {}).run 0
  checkUnit "mkNetOpsM socketpair inet" (rPair1 == .error LeanSwe.LinuxSyscall.Errno.EOPNOTSUPP && cPair1 == 0)
  let (rPair2, cPair2) := (ops.socketpair .unix .dgram {}).run 0
  checkUnit "mkNetOpsM socketpair unix passthrough" (rPair2 == .error sentinel && cPair2 == 1)
  let badUnix1 := LeanSwe.LinuxSyscall.Net.SockAddr.unix ByteArray.empty
  let badUnix2 := LeanSwe.LinuxSyscall.Net.SockAddr.unix (ByteArray.mk #[65, 0, 66])
  let badUnix3 := LeanSwe.LinuxSyscall.Net.SockAddr.unix (ByteArray.mk (Array.replicate (LeanSwe.LinuxSyscall.Net.UNIX_PATH_MAX + 1) 97))
  let goodAddr := LeanSwe.LinuxSyscall.Net.SockAddr.ipv4 LeanSwe.LinuxSyscall.Net.INADDR_LOOPBACK 8080
  let (rBind1, cBind1) := (ops.bind 1 badUnix1).run 0
  let (rBind2, cBind2) := (ops.bind 1 badUnix2).run 0
  let (rBind3, cBind3) := (ops.bind 1 badUnix3).run 0
  let (rBindOk, cBindOk) := (ops.bind 1 goodAddr).run 0
  checkUnit "mkNetOpsM bind guards" (rBind1 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cBind1 == 0 &&
    rBind2 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cBind2 == 0 &&
    rBind3 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cBind3 == 0 &&
    rBindOk == .error sentinel && cBindOk == 1)
  let (rConn1, cConn1) := (ops.connect 1 badUnix1).run 0
  let (rConn2, cConn2) := (ops.connect 1 badUnix2).run 0
  let (rConnOk, cConnOk) := (ops.connect 1 goodAddr).run 0
  checkUnit "mkNetOpsM connect guards" (rConn1 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cConn1 == 0 &&
    rConn2 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cConn2 == 0 &&
    rConnOk == .error sentinel && cConnOk == 1)
  let (rSend0, cSend0) := (ops.sendmsg 1 #[]).run 0
  let (rSend33, cSend33) := (ops.sendmsg 1 (Array.replicate (LeanSwe.LinuxSyscall.Net.MAX_SCM_FDS + 1) 2)).run 0
  let (rSendOk, cSendOk) := (ops.sendmsg 1 #[2]).run 0
  checkUnit "mkNetOpsM sendmsg guards" (rSend0 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cSend0 == 0 &&
    rSend33 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cSend33 == 0 &&
    rSendOk == .error sentinel && cSendOk == 1)
  let (rRecv0, cRecv0) := (ops.recvmsg 1 0).run 0
  let (rRecv33, cRecv33) := (ops.recvmsg 1 (UInt32.ofNat (LeanSwe.LinuxSyscall.Net.MAX_SCM_FDS + 1))).run 0
  let (rRecvOk, cRecvOk) := (ops.recvmsg 1 4).run 0
  checkUnit "mkNetOpsM recvmsg guards" (rRecv0 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cRecv0 == 0 &&
    rRecv33 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cRecv33 == 0 &&
    rRecvOk == .error sentinel && cRecvOk == 1)
  let badIf1 := ByteArray.mk (Array.replicate LeanSwe.LinuxSyscall.Net.IFNAMSIZ 97)
  let badIf2 := ByteArray.mk #[108, 0, 111]
  let (rIoctl1, cIoctl1) := (ops.ioctl 1 .getIfFlags badIf1).run 0
  let (rIoctl2, cIoctl2) := (ops.ioctl 1 .getIfFlags badIf2).run 0
  let (rIoctlOk, cIoctlOk) := (ops.ioctl 1 (.setIfFlags LeanSwe.LinuxSyscall.Net.IFF_UP) "lo".toUTF8).run 0
  checkUnit "mkNetOpsM ioctl guards" (rIoctl1 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cIoctl1 == 0 &&
    rIoctl2 == .error LeanSwe.LinuxSyscall.Errno.EINVAL && cIoctl2 == 0 &&
    rIoctlOk == .error sentinel && cIoctlOk == 1)
  let (rAcc, cAcc) := (ops.accept4 1 {}).run 0
  let (rGsn, cGsn) := (ops.getsockname 1).run 0
  checkUnit "mkNetOpsM accept4/getsockname" (rAcc == .ok (9, goodAddr) && cAcc == 1 &&
    rGsn == .ok (LeanSwe.LinuxSyscall.Net.SockAddr.unix "u".toUTF8) && cGsn == 1)

private def runProcessMutExtra : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then
      throw (IO.userError s!"process mutate-driver check failed: {msg}")
  let pf0 : LeanSwe.LinuxSyscall.Process.PipeFlags := { cloexec := false, nonblock := true, direct := true, notificationPipe := true }
  checkB "PipeFlags.isValid valid" pf0.isValid
  checkB "PipeFlags.toBits valid" (pf0.toBits == 0xe)
  let pfBad : LeanSwe.LinuxSyscall.Process.PipeFlags := { extraBits := 1 }
  checkB "PipeFlags.isValid extraBits" (!pfBad.isValid)
  checkB "PipeFlags.toBits extraBits" (pfBad.toBits == 0x11)
  let wf0 : LeanSwe.LinuxSyscall.Process.WaitFlags := { nohang := true, untraced := true, continued := true, wall := true, wclone := true, wnothread := true }
  checkB "WaitFlags.isValid valid" wf0.isValid
  checkB "WaitFlags.toBits valid" (wf0.toBits == 0x3f)
  let wfBad : LeanSwe.LinuxSyscall.Process.WaitFlags := { extraBits := 2 }
  checkB "WaitFlags.isValid extraBits" (!wfBad.isValid)
  checkB "WaitFlags.toBits extraBits" (wfBad.toBits == 0x80)
  let pof0 : LeanSwe.LinuxSyscall.Process.PidfdOpenFlags := { nonblock := true, thread := true }
  checkB "PidfdOpenFlags.isValid valid" pof0.isValid
  checkB "PidfdOpenFlags.toBits valid" (pof0.toBits == 0x3)
  let pofBad : LeanSwe.LinuxSyscall.Process.PidfdOpenFlags := { extraBits := 1 }
  checkB "PidfdOpenFlags.isValid extraBits" (!pofBad.isValid)
  checkB "PidfdOpenFlags.toBits extraBits" (pofBad.toBits == 0x4)
  let psf0 : LeanSwe.LinuxSyscall.Process.PidfdSignalFlags := { processGroup := true }
  checkB "PidfdSignalFlags.isValid valid" psf0.isValid
  checkB "PidfdSignalFlags.toBits valid" (psf0.toBits == 0x4)
  checkB "PidfdSignalFlags.isValid exclusive" (!(LeanSwe.LinuxSyscall.Process.PidfdSignalFlags.mk true true false 0).isValid)
  let psfBad : LeanSwe.LinuxSyscall.Process.PidfdSignalFlags := { extraBits := 1 }
  checkB "PidfdSignalFlags.isValid extraBits" (!psfBad.isValid)
  checkB "PidfdSignalFlags.toBits extraBits" (psfBad.toBits == 0x8)
  checkB "Signal.sigkill toRaw" (LeanSwe.LinuxSyscall.Process.Signal.sigkill.toRaw == (3, 0))
  checkB "Signal.sigkill toLinuxNum" (LeanSwe.LinuxSyscall.Process.Signal.sigkill.toLinuxNum == 9)
  checkB "Signal.sigzero valid" (LeanSwe.LinuxSyscall.Process.Signal.sigzero.isValid)
  checkB "Signal.raw 32 nptl" (LeanSwe.LinuxSyscall.Process.Signal.raw 32 |>.isNptlReserved)
  checkB "Signal.raw 33 nptl" (LeanSwe.LinuxSyscall.Process.Signal.raw 33 |>.isNptlReserved)
  checkB "Signal.raw -1 invalid" (!(LeanSwe.LinuxSyscall.Process.Signal.raw (-1)).isValid)
  checkB "Signal.raw 65 invalid" (!(LeanSwe.LinuxSyscall.Process.Signal.raw 65).isValid)
  checkB "WaitResult.stillRunning" (LeanSwe.LinuxSyscall.Process.WaitResult.ofRawWait4 (0, 0) == .stillRunning)
  checkB "WaitResult.exited" (LeanSwe.LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x0700) == .exited 42 7)
  checkB "WaitResult.signaled core" (LeanSwe.LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x8b) == .signaled 42 11 true)
  checkB "WaitResult.stopped" (LeanSwe.LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x137f) == .stopped 42 19)
  checkB "WaitResult.continued" (LeanSwe.LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0xffff) == .continued 42)
  checkB "pipe2 invalid extraBits EINVAL"
    (match ← LeanSwe.LinuxSyscall.Process.pipe2 pfBad with | .error e => e == LeanSwe.LinuxSyscall.Errno.EINVAL | .ok _ => false)
  checkB "pipe2 high extraBits EINVAL"
    (match ← LeanSwe.LinuxSyscall.Process.pipe2 { extraBits := 0x80000000 } with | .error e => e == LeanSwe.LinuxSyscall.Errno.EINVAL | .ok _ => false)
  if !(← Fuzz.LinuxSyscall.ProcessEnv.probeKernelWatchQueue) then
    let notifOk ←
      match ← LeanSwe.LinuxSyscall.Process.pipe2 { notificationPipe := true } with
      | .error e => pure (e == LeanSwe.LinuxSyscall.Process.errnoENOPKG)
      | .ok (r, w) =>
        let _ ← Fuzz.LinuxSyscall.ProcessEnv.closeFd r
        let _ ← Fuzz.LinuxSyscall.ProcessEnv.closeFd w
        pure false
    checkB "pipe2 notificationPipe ENOPKG" notifOk
  checkB "waitpid invalid extraBits EINVAL" ((← LeanSwe.LinuxSyscall.Process.waitpid 0 wfBad) == .error LeanSwe.LinuxSyscall.Errno.EINVAL)
  checkB "waitpid high extraBits EINVAL" ((← LeanSwe.LinuxSyscall.Process.waitpid 0 { extraBits := 0x80000000 }) == .error LeanSwe.LinuxSyscall.Errno.EINVAL)
  match ← LeanSwe.LinuxSyscall.Process.getpid with
  | .ok selfPid =>
    checkB "pidfd_open invalid extraBits EINVAL"
      (match ← LeanSwe.LinuxSyscall.Process.pidfd_open selfPid pofBad with | .error e => e == LeanSwe.LinuxSyscall.Errno.EINVAL | .ok _ => false)
    checkB "pidfd_open high extraBits EINVAL"
      (match ← LeanSwe.LinuxSyscall.Process.pidfd_open selfPid { extraBits := 0x80000000 } with | .error e => e == LeanSwe.LinuxSyscall.Errno.EINVAL | .ok _ => false)
    match ← LeanSwe.LinuxSyscall.Process.pidfd_open selfPid {} with
    | .ok pfd =>
      checkB "pidfd_send_signal invalid extraBits EINVAL" ((← LeanSwe.LinuxSyscall.Process.pidfd_send_signal pfd .sigzero psfBad) == .error LeanSwe.LinuxSyscall.Errno.EINVAL)
      checkB "pidfd_send_signal high extraBits EINVAL" ((← LeanSwe.LinuxSyscall.Process.pidfd_send_signal pfd .sigzero { extraBits := 0x80000000 }) == .error LeanSwe.LinuxSyscall.Errno.EINVAL)
      checkB "pidfd_send_signal valid sigzero ok" ((← LeanSwe.LinuxSyscall.Process.pidfd_send_signal pfd .sigzero {}) == .ok ())
      checkB "pidfd_open self close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd pfd) == .ok ())
      checkB "pidfd_open double close EBADF" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd pfd) == .error LeanSwe.LinuxSyscall.Errno.EBADF)
      checkB "pidfd_send_signal closed EBADF" ((← LeanSwe.LinuxSyscall.Process.pidfd_send_signal pfd .sigzero {}) == .error LeanSwe.LinuxSyscall.Errno.EBADF)
    | .error e => throw (IO.userError s!"pidfd_open self in MutateDriver failed: {e}")
  | .error e => throw (IO.userError s!"getpid in MutateDriver failed: {e}")
  match ← LeanSwe.LinuxSyscall.Process.pipe2 { cloexec := true } with
  | .ok (rd, wr) =>
    match ← Fuzz.LinuxSyscall.ProcessEnv.getFdFlags rd, ← Fuzz.LinuxSyscall.ProcessEnv.getFdFlags wr with
    | .ok (_, flR), .ok (_, flW) =>
      checkB "pipe2 rd O_RDONLY" ((flR &&& 3) == 0)
      checkB "pipe2 wr O_WRONLY" ((flW &&& 3) == 1)
    | _, _ => throw (IO.userError "getFdFlags failed on pipe2 in MutateDriver")
    checkB "pipe2 rd close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd rd) == .ok ())
    checkB "pipe2 wr close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd wr) == .ok ())
  | .error e => throw (IO.userError s!"pipe2 in MutateDriver failed: {e}")
  match ← Fuzz.LinuxSyscall.ProcessEnv.spawnControlled (-1) false with
  | .ok (cPid, _) =>
    try
      checkB "waitpid live child stillRunning" ((← LeanSwe.LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true }) == .ok .stillRunning)
      checkB "waitpid __WCLONE ECHILD on SIGCHLD child" ((← LeanSwe.LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true, wclone := true }) == .error LeanSwe.LinuxSyscall.Errno.ECHILD)
    finally
      Fuzz.LinuxSyscall.ProcessEnv.cleanupChild cPid
  | .error e => throw (IO.userError s!"spawnControlled in MutateDriver failed: {e}")
  for secErr in #[(1 : UInt32), 4, 5, 7, 9, 12, 28, 104, 116, 122, 4095] do
    match ← Fuzz.LinuxSyscall.ProcessEnv.checkFdCloseSeccomp secErr with
    | .ok true => pure ()
    | other => throw (IO.userError s!"checkFdCloseSeccomp {secErr} failed in MutateDriver: {repr other}")
  match ← Fuzz.LinuxSyscall.ProcessEnv.checkSeccompEfaultAbort with
  | .ok true => pure ()
  | other => throw (IO.userError s!"checkSeccompEfaultAbort failed in MutateDriver: {repr other}")

/-- Ordered `LinuxSyscall.*` mutation test suites. -/
def suites : Array MutateSuite := #[
  { name := "LinuxSyscall.Sandbox", runBase := do Fuzz.LinuxSyscall.Sandbox.Strace.runChecks; return none, runExtra := Fuzz.LinuxSyscall.Sandbox.Strace.runStraceFaultCheck },
  { name := "LinuxSyscall.TimeRand", runBase := do Fuzz.LinuxSyscall.TimeRand.Strace.runChecks; return none, runExtra := Fuzz.LinuxSyscall.TimeRand.Strace.runStraceFaultCheck },
  { name := "LinuxSyscall.Passwd", runBase := do Fuzz.Passwd.suite.runSmoke { smoke := true }; return none },
  { name := "LinuxSyscall.Dns", runBase := do Fuzz.Dns.suite.runSmoke { smoke := true }; return none, runExtra := runDnsUnitTests },
  { name := "LinuxSyscall.Poll", runBase := do Fuzz.LinuxSyscall.Poll.Strace.runChecks; return none, runExtra := do Fuzz.LinuxSyscall.Poll.Strace.runStraceFaultCheck; runPollOpsUnitTests },
  { name := "LinuxSyscall.Net", runBase := do Fuzz.LinuxSyscall.Net.Strace.runChecks; return none, runExtra := do Fuzz.LinuxSyscall.Net.Strace.runStraceFaultCheck; runNetOpsUnitTests },
  { name := "LinuxSyscall.Process", runBase := do Fuzz.LinuxSyscall.Process.Strace.runChecks; return none, runExtra := runProcessMutExtra },
  { name := "LinuxSyscall.Files", runBase := do Fuzz.LinuxSyscall.Files.Strace.runChecks; return none, runExtra := runFilesMkOpsUnitTests }
]

/-- Match `LinuxSyscall` strace, namespace, passwd, and dns subprocess worker CLI flags. -/
def findEarlyWorker? : List String → Option (IO UInt32)
  | "--passwd-probe" :: rest => some (Fuzz.Passwd.Checks.probeMain rest)
  | "--sandbox-strace-worker" :: mode :: [] =>
    some (do Fuzz.LinuxSyscall.Sandbox.Strace.runStraceWorker mode; return 0)
  | "--sandbox-strace-fault-check" :: [] =>
    some (do Fuzz.LinuxSyscall.Sandbox.Strace.runStraceFaultCheck; IO.println "SANDBOX_STRACE_FAULT_CHECK_OK"; return 0)
  | "--timerand-strace-fault-check" :: rest => some (Fuzz.LinuxSyscall.TimeRand.Strace.probeMain rest)
  | "--poll-strace-fault-check" :: rest => some (Fuzz.LinuxSyscall.Poll.Strace.probeMain rest)
  | "--poll-strace-worker" :: rest => some (Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--worker" :: rest))
  | "--poll-strace-efd-worker" :: rest => some (Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--efd-worker" :: rest))
  | "--net-strace-fault-check" :: rest => some (Fuzz.LinuxSyscall.Net.Strace.probeMain rest)
  | "--net-strace-worker" :: rest => some (Fuzz.LinuxSyscall.Net.Strace.probeMain ("--worker" :: rest))
  | "--suite" :: "process" :: "--ns-worker" :: mode :: arg :: rest =>
    some (do Fuzz.LinuxSyscall.ProcessEnv.ensureStdio; Fuzz.LinuxSyscall.ProcessFuzz.nsWorkerMain mode arg rest)
  | "--ns-worker" :: mode :: arg :: rest =>
    some (do Fuzz.LinuxSyscall.ProcessEnv.ensureStdio; Fuzz.LinuxSyscall.ProcessFuzz.nsWorkerMain mode arg rest)
  | "--process-strace-worker" :: opName :: errName :: _ =>
    some (Fuzz.LinuxSyscall.Process.Strace.probeMain ["--worker", opName, errName])
  | "--files-strace-worker" :: rest => some (Fuzz.LinuxSyscall.Files.Strace.probeMain ("--worker" :: rest))
  | ["--suite", "dns", "--steps", stepsStr, "--seed", seedStr] =>
    some do
      match stepsStr.toNat?, seedStr.toNat? with
      | some n, some s =>
        Fuzz.Dns.suite.runFuzz { steps := n, seed := UInt64.ofNat s }
        return 0
      | _, _ =>
        IO.eprintln s!"invalid dns subcheck args: {stepsStr} {seedStr}"
        return 2
  | _ => none

end Tests.Mutate.LinuxSyscall
