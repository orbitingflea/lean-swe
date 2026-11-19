import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.Dns.Impl

namespace LeanSwe.LinuxSyscall.Dns

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_getaddrinfo"]
private opaque rawGetaddrinfo :
  @& String → UInt8 → UInt8 → BaseIO (Except (Int32 × UInt32 × ByteArray) ByteArray)

private def posixDnsOpsBase : Internal.PosixDnsOpsM BaseIO :=
  { getaddrinfo := rawGetaddrinfo }

/-- Default standalone `BaseIO` Linux `Dns` capability bundle backed by `LeanSwe/LinuxSyscall/c/dns_shim.c`. -/
def defaultOpsBase : DnsOpsM BaseIO :=
  Internal.mkDnsOpsM posixDnsOpsBase

/-- Default standalone `IO` Linux `Dns` capability bundle backed by `LeanSwe/LinuxSyscall/c/dns_shim.c`. -/
def defaultOps : DnsOps :=
  { getaddrinfo := fun host hints => liftM (defaultOpsBase.getaddrinfo host hints) }

/-- Resolve `host` under `hints` to a list of IPv4/IPv6 `DnsAddr` records via `getaddrinfo(3)`. -/
@[inline] def getaddrinfo (host : String) (hints : ResolveHints := {}) :
    IO (Except DnsError (List DnsAddr)) :=
  defaultOps.getaddrinfo host hints

end LeanSwe.LinuxSyscall.Dns
