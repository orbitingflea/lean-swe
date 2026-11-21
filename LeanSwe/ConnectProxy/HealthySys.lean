import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge

namespace LeanSwe.ConnectProxy.HealthySys

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.SysBridge

/-- Curated catastrophic OS/hardware fault codes excluded from `healthyStep` (`ENOMEM`, `EIO`, `ENFILE`). -/
abbrev isCriticalOsErrno : Errno → Bool := Errno.isCriticalOsErrno

/-- Everyday per-process/filesystem resource limit errnos (`EMFILE`, `ENOSPC`) included inside `healthyStep`. -/
abbrev isResourceLimitErrno : Errno → Bool := Errno.isResourceLimitErrno

/-- Convert `Except Errno Unit` into `Files.FilesOutcome`. -/
def filesOutcomeUnit : Except Errno Unit → Files.FilesOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno Files.HandleId` into `Files.FilesOutcome`. -/
def filesOutcomeOpened : Except Errno Files.HandleId → Files.FilesOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Convert `Except Errno ByteArray` into `Files.FilesOutcome`. -/
def filesOutcomeBytes : Except Errno ByteArray → Files.FilesOutcome
  | .ok b => .bytes b
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `Files.FilesOutcome`. -/
def filesOutcomeU32 : Except Errno UInt32 → Files.FilesOutcome
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert `Except Errno UInt64` into `Files.FilesOutcome`. -/
def filesOutcomeU64 : Except Errno UInt64 → Files.FilesOutcome
  | .ok v => .u64 v
  | .error e => .err e

/-- Convert `Except Errno Files.StatInfo` into `Files.FilesOutcome`. -/
def filesOutcomeStatted : Except Errno Files.StatInfo → Files.FilesOutcome
  | .ok st => .statted st
  | .error e => .err e

/-- Return `true` iff `FilesOutcome` is a curated critical OS fault. -/
def isFilesCriticalFault : Files.FilesOutcome → Bool
  | .err e => isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `FilesOutcome` is `EINTR`. -/
def isFilesEintrOutcome : Files.FilesOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy host environment wrapping `Files.FilesState` and bounded `eintrBudget`. -/
structure FilesHealthyEnv where
  /-- Underlying `Files` world state. -/
  state : Files.FilesState := Files.FilesState.initial
  /-- Remaining `EINTR` budget (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving BEq, Inhabited

/-- Construct an initial `FilesHealthyEnv` with optional `eintrBudget`. -/
def FilesHealthyEnv.initial (eintrBudget : Nat := 0) : FilesHealthyEnv :=
  { state := Files.FilesState.initial, eintrBudget := eintrBudget }

/-- Well-formedness predicate (`ambientSeccomp = false`). -/
def FilesHealthyEnv.wf (env : FilesHealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Return `true` iff `req` is `.close` and `out` is `.err Errno.EBUSY`. -/
def isFilesCloseEbusy (req : Files.FilesReq) (out : Files.FilesOutcome) : Bool :=
  match req, out with
  | .close _, .err e => e == Errno.EBUSY
  | _, _ => false

/-- Relational `healthyStep` for `LinuxSyscall.Files` excluding critical OS faults and bounding `EINTR` (and excluding `EBUSY` on unpinned single-thread `close`). -/
def healthyFilesStep (env : FilesHealthyEnv) (req : Files.FilesReq) (out : Files.FilesOutcome) :
    Option FilesHealthyEnv :=
  if !env.wf || isFilesCriticalFault out || isFilesCloseEbusy req out then
    none
  else
    match Files.allowedStep env.state req out with
    | none => none
    | some s' =>
      if isFilesEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Execute one `FilesReq` against `ops : Files.FilesOpsM m Files.HandleId`. -/
def execFilesReq {m : Type → Type} [Monad m]
    (ops : Files.FilesOpsM m Files.HandleId) : Files.FilesReq → m Files.FilesOutcome
  | .openat d p fl md => filesOutcomeOpened <$> ops.openat d p fl md
  | .openat2 d p how => filesOutcomeOpened <$> ops.openat2 d p how
  | .close h => filesOutcomeUnit <$> ops.close h
  | .read h n => filesOutcomeBytes <$> ops.read h n
  | .write h bs => filesOutcomeU32 <$> ops.write h bs
  | .fstat h => filesOutcomeStatted <$> ops.fstat h
  | .fstatat d p fl => filesOutcomeStatted <$> ops.fstatat d p fl
  | .faccessat d p mk fl => filesOutcomeUnit <$> ops.faccessat d p mk fl
  | .mkdirat d p md => filesOutcomeUnit <$> ops.mkdirat d p md
  | .unlinkat d p rd => filesOutcomeUnit <$> ops.unlinkat d p rd
  | .renameat2 od op nd np fl => filesOutcomeUnit <$> ops.renameat2 od op nd np fl
  | .symlinkat t d lp => filesOutcomeUnit <$> ops.symlinkat t d lp
  | .readlinkat d p c => filesOutcomeBytes <$> ops.readlinkat d p c
  | .getdents64 h c => filesOutcomeBytes <$> ops.getdents64 h c
  | .fchmodat d p md => filesOutcomeUnit <$> ops.fchmodat d p md
  | .fchmod h md => filesOutcomeUnit <$> ops.fchmod h md
  | .flock h op => filesOutcomeUnit <$> ops.flock h op
  | .fcntl h cmd => filesOutcomeU32 <$> ops.fcntl h cmd
  | .fsync h => filesOutcomeUnit <$> ops.fsync h
  | .getcwd c => filesOutcomeBytes <$> ops.getcwd c
  | .lseek h off wh => filesOutcomeU64 <$> ops.lseek h off wh
  | .reopenReadOnly h => filesOutcomeOpened <$> ops.reopenReadOnly h
  | .dupStdio sl => filesOutcomeOpened <$> ops.dupStdio sl

/-- Universal lens-form healthy refinement for `FilesOpsM (StateM W) HandleId`. -/
def RefinesHealthyFilesAt {W : Type} (proj : W → FilesHealthyEnv)
    (ops : Files.FilesOpsM (StateM W) Files.HandleId) : Prop :=
  ∀ (w : W) (req : Files.FilesReq),
    (proj w).wf = true →
    let (out, w') := (execFilesReq ops req).run w
    healthyFilesStep (proj w) req out = some (proj w')

/-- Direct `StateM FilesHealthyEnv` healthy refinement abbreviation. -/
abbrev RefinesHealthyFiles (ops : Files.FilesOpsM (StateM FilesHealthyEnv) Files.HandleId) : Prop :=
  RefinesHealthyFilesAt id ops

/-- Convert `Except Errno Net.HandleId` into `Net.NetOutcome`. -/
def netOutcomeOpened : Except Errno Net.HandleId → Net.NetOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Convert `Except Errno (Net.HandleId × Net.HandleId)` into `Net.NetOutcome`. -/
def netOutcomePair : Except Errno (Net.HandleId × Net.HandleId) → Net.NetOutcome
  | .ok (h0, h1) => .pair h0 h1
  | .error e => .err e

/-- Convert `Except Errno (Net.HandleId × Net.SockAddr)` into `Net.NetOutcome`. -/
def netOutcomeAccepted : Except Errno (Net.HandleId × Net.SockAddr) → Net.NetOutcome
  | .ok (h, sa) => .accepted h sa
  | .error e => .err e

/-- Convert `Except Errno Net.SockAddr` into `Net.NetOutcome`. -/
def netOutcomeAddr : Except Errno Net.SockAddr → Net.NetOutcome
  | .ok sa => .addr sa
  | .error e => .err e

/-- Convert `Except Errno ByteArray` into `Net.NetOutcome`. -/
def netOutcomeBytes : Except Errno ByteArray → Net.NetOutcome
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `Net.NetOutcome`. -/
def netOutcomeU32 : Except Errno UInt32 → Net.NetOutcome
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert `Except Errno Unit` into `Net.NetOutcome`. -/
def netOutcomeUnit : Except Errno Unit → Net.NetOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno (Array Net.HandleId)` into `Net.NetOutcome`. -/
def netOutcomeFds : Except Errno (Array Net.HandleId) → Net.NetOutcome
  | .ok fds => .fds fds
  | .error e => .err e

/-- Return `true` iff `NetOutcome` is a curated critical OS fault. -/
def isNetCriticalFault : Net.NetOutcome → Bool
  | .err e => isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `NetOutcome` is `EINTR`. -/
def isNetEintrOutcome : Net.NetOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy host environment wrapping `Net.NetState` and bounded `eintrBudget`. -/
structure NetHealthyEnv where
  /-- Underlying `Net` world state. -/
  state : Net.NetState := Net.NetState.initial
  /-- Remaining `EINTR` budget (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving BEq, Inhabited

/-- Construct an initial `NetHealthyEnv` with optional `eintrBudget`. -/
def NetHealthyEnv.initial (eintrBudget : Nat := 0) : NetHealthyEnv :=
  { state := Net.NetState.initial, eintrBudget := eintrBudget }

/-- Well-formedness predicate (`ambientSeccomp = false`). -/
def NetHealthyEnv.wf (env : NetHealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational `healthyStep` for `LinuxSyscall.Net` excluding critical OS faults and bounding `EINTR`. -/
def healthyNetStep (env : NetHealthyEnv) (req : Net.NetReq) (out : Net.NetOutcome) :
    Option NetHealthyEnv :=
  if !env.wf || isNetCriticalFault out then
    none
  else
    match Net.allowedStep env.state req out with
    | none => none
    | some s' =>
      if isNetEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Execute one `NetReq` against `ops : Net.NetOpsM m Net.HandleId`. -/
def execNetReq {m : Type → Type} [Monad m]
    (ops : Net.NetOpsM m Net.HandleId) : Net.NetReq → m Net.NetOutcome
  | .socket dom st fl p => netOutcomeOpened <$> ops.socket dom st fl p
  | .socketpair dom st fl => netOutcomePair <$> ops.socketpair dom st fl
  | .bind h sa => netOutcomeUnit <$> ops.bind h sa
  | .listen h bl => netOutcomeUnit <$> ops.listen h bl
  | .accept4 h fl => netOutcomeAccepted <$> ops.accept4 h fl
  | .connect h sa => netOutcomeUnit <$> ops.connect h sa
  | .getsockopt h opt => netOutcomeU32 <$> ops.getsockopt h opt
  | .setsockopt h opt val => netOutcomeUnit <$> ops.setsockopt h opt val
  | .getsockname h => netOutcomeAddr <$> ops.getsockname h
  | .recvfrom h n fl => netOutcomeBytes <$> ops.recvfrom h n fl
  | .sendto h bs fl => netOutcomeU32 <$> ops.sendto h bs fl
  | .shutdown h how => netOutcomeUnit <$> ops.shutdown h how
  | .sendmsg h fds => netOutcomeUnit <$> ops.sendmsg h fds
  | .recvmsg h maxFds => netOutcomeFds <$> ops.recvmsg h maxFds
  | .ioctl h op ifn => netOutcomeU32 <$> ops.ioctl h op ifn

/-- Universal lens-form healthy refinement for `NetOpsM (StateM W) HandleId`. -/
def RefinesHealthyNetAt {W : Type} (proj : W → NetHealthyEnv)
    (ops : Net.NetOpsM (StateM W) Net.HandleId) : Prop :=
  ∀ (w : W) (req : Net.NetReq),
    (proj w).wf = true →
    let (out, w') := (execNetReq ops req).run w
    healthyNetStep (proj w) req out = some (proj w')

/-- Direct `StateM NetHealthyEnv` healthy refinement abbreviation. -/
abbrev RefinesHealthyNet (ops : Net.NetOpsM (StateM NetHealthyEnv) Net.HandleId) : Prop :=
  RefinesHealthyNetAt id ops

/-- Convert `Except Errno (Array Poll.PollEvents)` into `Poll.PollOutcome`. -/
def pollOutcomePolled : Except Errno (Array Poll.PollEvents) → Poll.PollOutcome
  | .ok rev => .polled rev
  | .error e => .err e

/-- Convert `Except Errno Poll.HandleId` into `Poll.PollOutcome`. -/
def pollOutcomeOpened : Except Errno Poll.HandleId → Poll.PollOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Return `true` iff `PollOutcome` is a curated critical OS fault. -/
def isPollCriticalFault : Poll.PollOutcome → Bool
  | .err e => isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `PollOutcome` is `EINTR`. -/
def isPollEintrOutcome : Poll.PollOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy host environment wrapping `Poll.PollState` and bounded `eintrBudget`. -/
structure PollHealthyEnv where
  /-- Underlying `Poll` world state. -/
  state : Poll.PollState := Poll.PollState.initial
  /-- Remaining `EINTR` budget (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving BEq, Inhabited

/-- Construct an initial `PollHealthyEnv` with optional `eintrBudget`. -/
def PollHealthyEnv.initial (eintrBudget : Nat := 0) : PollHealthyEnv :=
  { state := Poll.PollState.initial, eintrBudget := eintrBudget }

/-- Well-formedness predicate (`ambientSeccomp = false`). -/
def PollHealthyEnv.wf (env : PollHealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational `healthyStep` for `LinuxSyscall.Poll` excluding critical OS faults and bounding `EINTR`. -/
def healthyPollStep (env : PollHealthyEnv) (req : Poll.PollReq) (out : Poll.PollOutcome) :
    Option PollHealthyEnv :=
  if !env.wf || isPollCriticalFault out then
    none
  else
    match Poll.allowedStep env.state req out with
    | none => none
    | some s' =>
      if isPollEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Execute one `PollReq` against `ops : Poll.PollOpsM m Poll.HandleId`. -/
def execPollReq {m : Type → Type} [Monad m]
    (ops : Poll.PollOpsM m Poll.HandleId) : Poll.PollReq → m Poll.PollOutcome
  | .ppoll fds to? => pollOutcomePolled <$> ops.ppoll fds to?
  | .eventfd2 iv fl => pollOutcomeOpened <$> ops.eventfd2 iv fl

/-- Universal lens-form healthy refinement for `PollOpsM (StateM W) HandleId`. -/
def RefinesHealthyPollAt {W : Type} (proj : W → PollHealthyEnv)
    (ops : Poll.PollOpsM (StateM W) Poll.HandleId) : Prop :=
  ∀ (w : W) (req : Poll.PollReq),
    (proj w).wf = true →
    let (out, w') := (execPollReq ops req).run w
    healthyPollStep (proj w) req out = some (proj w')

/-- Direct `StateM PollHealthyEnv` healthy refinement abbreviation. -/
abbrev RefinesHealthyPoll (ops : Poll.PollOpsM (StateM PollHealthyEnv) Poll.HandleId) : Prop :=
  RefinesHealthyPollAt id ops

/-- Re-export of canonical `LinuxSyscall.Dns.DnsReq`. -/
abbrev DnsReq := Dns.DnsReq

/-- Re-export of canonical `LinuxSyscall.Dns.DnsOutcome`. -/
abbrev DnsOutcome := Dns.DnsOutcome

/-- Re-export of canonical `LinuxSyscall.Dns.isCriticalFault`. -/
abbrev isDnsCriticalFault : DnsOutcome → Bool := Dns.isCriticalFault

/-- Re-export of canonical `LinuxSyscall.Dns.isEintrOutcome`. -/
abbrev isDnsEintrOutcome : DnsOutcome → Bool := Dns.isEintrOutcome

/-- Re-export of canonical `LinuxSyscall.Dns.HealthyEnv`. -/
abbrev DnsHealthyEnv := Dns.HealthyEnv

/-- Re-export of canonical `LinuxSyscall.Dns.healthyStep`. -/
abbrev healthyDnsStep := Dns.healthyStep

/-- Re-export of canonical `LinuxSyscall.Dns.execDnsReq`. -/
abbrev execDnsReq {m : Type → Type} [Monad m] := @Dns.execDnsReq m _

/-- Re-export of canonical `LinuxSyscall.Dns.RefinesHealthyDnsAt`. -/
abbrev RefinesHealthyDnsAt {W : Type} := @Dns.RefinesHealthyDnsAt W

/-- Re-export of canonical `LinuxSyscall.Dns.RefinesHealthyDns`. -/
abbrev RefinesHealthyDns := Dns.RefinesHealthyDns

/-- Re-export of canonical `LinuxSyscall.TimeRand.isCriticalFault`. -/
abbrev isTimeRandCriticalFault : TimeRand.TimeRandOutcome → Bool := TimeRand.isCriticalFault

/-- Re-export of canonical `LinuxSyscall.TimeRand.isEintrOutcome`. -/
abbrev isTimeRandEintrOutcome : TimeRand.TimeRandOutcome → Bool := TimeRand.isEintrOutcome

/-- Re-export of canonical `LinuxSyscall.TimeRand.HealthyEnv`. -/
abbrev TimeRandHealthyEnv := TimeRand.HealthyEnv

/-- Re-export of canonical `LinuxSyscall.TimeRand.healthyStep`. -/
abbrev healthyTimeRandStep := TimeRand.healthyStep

/-- Re-export of canonical `LinuxSyscall.TimeRand.execTimeRandReq`. -/
abbrev execTimeRandReq {m : Type → Type} [Monad m] := @TimeRand.execTimeRandReq m _

/-- Re-export of canonical `LinuxSyscall.TimeRand.RefinesHealthyTimeRandAt`. -/
abbrev RefinesHealthyTimeRandAt {W : Type} := @TimeRand.RefinesHealthyTimeRandAt W

/-- Re-export of canonical `LinuxSyscall.TimeRand.RefinesHealthyTimeRand`. -/
abbrev RefinesHealthyTimeRand := TimeRand.RefinesHealthyTimeRand

/-- Combined healthy OS world state for `ConnectProxy` relational specs (`Files` + `Net` + `Poll` + `Dns` + `TimeRand` + `SyncProxyTable` + unconstrained nondeterministic `auxTag`). -/
structure HealthySysWorld where
  /-- `Files` healthy environment. -/
  filesEnv : FilesHealthyEnv := FilesHealthyEnv.initial
  /-- `Net` healthy environment. -/
  netEnv : NetHealthyEnv := NetHealthyEnv.initial
  /-- `Poll` healthy environment. -/
  pollEnv : PollHealthyEnv := PollHealthyEnv.initial
  /-- `Dns` healthy environment (shared `LinuxSyscall.Dns.HealthyEnv`). -/
  dnsEnv : DnsHealthyEnv := Dns.HealthyEnv.initial
  /-- `TimeRand` healthy environment (shared `LinuxSyscall.TimeRand.HealthyEnv`). -/
  timeEnv : TimeRandHealthyEnv := TimeRand.HealthyEnv.initial 0 0 true
  /-- Unconstrained auxiliary state allowing arbitrary healthy adversarial/nondeterministic schedules. -/
  auxTag : Nat := 0
  /-- Active synchronous proxy table owned by `mkSyncRawOps`. -/
  proxyTable : SyncProxyTable Nat := {}
  deriving Inhabited

/-- Combined well-formedness check across all 5 subsystem environments. -/
def HealthySysWorld.wf (w : HealthySysWorld) : Bool :=
  w.filesEnv.wf && w.netEnv.wf && w.pollEnv.wf && w.dnsEnv.wf && w.timeEnv.wf

/-- Universal relational healthy refinement for `CProxySysOpsM (StateM W) Nat` over arbitrary world `W`. -/
def RefinesHealthyCProxySysAt {W : Type}
    (projFiles : W → FilesHealthyEnv)
    (projNet : W → NetHealthyEnv)
    (projPoll : W → PollHealthyEnv)
    (projDns : W → DnsHealthyEnv)
    (projTime : W → TimeRandHealthyEnv)
    (getTable : W → SyncProxyTable Nat)
    (setTable : W → SyncProxyTable Nat → W)
    (sys : CProxySysOpsM (StateM W) Nat) : Prop :=
  let worldWf (w : W) : Prop :=
    (projFiles w).wf = true ∧ (projNet w).wf = true ∧ (projPoll w).wf = true ∧
    (projDns w).wf = true ∧ (projTime w).wf = true
  let fdsNodup (w : W) : Prop := ((projFiles w).state.fds.map Prod.fst).Nodup
  (∀ w h, worldWf w →
    let (r, w') := (sys.files.close h).run w
    healthyFilesStep (projFiles w) (.close h) (filesOutcomeUnit r) = some (projFiles w') ∧
    worldWf w' ∧ getTable w' = getTable w) ∧
  (∀ w req, worldWf w →
    let (out, w') := (execNetReq sys.net req).run w
    healthyNetStep (projNet w) req out = some (projNet w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (execPollReq sys.poll req).run w
    healthyPollStep (projPoll w) req out = some (projPoll w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (execDnsReq sys.dns req).run w
    healthyDnsStep (projDns w) req out = some (projDns w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (execTimeRandReq sys.timeRand req).run w
    healthyTimeRandStep (projTime w) req out = some (projTime w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w t, getTable (setTable w t) = t) ∧
  (∀ w t, (worldWf w → worldWf (setTable w t)) ∧ (fdsNodup w → fdsNodup (setTable w t)))

/-- Relational healthy OS world refinement instantiated at `HealthySysWorld`. -/
def RefinesHealthyCProxySys (sys : CProxySysOpsM (StateM HealthySysWorld) Nat) : Prop :=
  RefinesHealthyCProxySysAt
    (·.filesEnv) (·.netEnv) (·.pollEnv) (·.dnsEnv) (·.timeEnv)
    (·.proxyTable) (fun w t => { w with proxyTable := t })
    sys

/-- Return all open descriptors currently owned by `slot`. -/
def slotOpenFds {fd dnsJob : Type} (slot : ClientSlot fd dnsJob) : List fd :=
  match slot.phase with
  | .handshake cfd _ _ => [cfd]
  | .dns cfd _ _ _ => [cfd]
  | .connecting cfd ufd .. => [ufd, cfd]
  | .relay st =>
    (match st.clientFd? with | some c => [c] | none => []) ++
    (match st.upstreamFd? with | some u => [u] | none => [])
  | .closingReply cfd? .. =>
    match cfd? with | some c => [c] | none => []
  | .done => []

/-- Entrypoint bundle tested by `ConnectProxy`'s `RefinesHealthy*` `SpecTests` and `SpecMutants`. -/
structure SysBridgeTarget where
  /-- Create `127.0.0.1` loopback listener + wakeup socketpair. -/
  createListener :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ValidProxyConfig →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Except ProxyError (Nat × Nat × Nat × UInt16))
  /-- Stage-1 complete-head gate + Stage-2 DNS/dial pipeline. -/
  handleCompleteHeadSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Nat →
    ByteArray →
    ByteArray →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Concurrency-bounded `accept4` admission loop. -/
  acceptNewClients :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    Nat →
    Nat →
    Array (ClientSlot Nat Unit) →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Array (ClientSlot Nat Unit))
  /-- Listener `POLLIN` interest gate (`slots.size < maxConcurrentTunnels`). -/
  listenPollinEnabled : Nat → Nat → Bool
  /-- Synchronous `ppoll` batch builder (`wakeR`, `listenFd`, per-slot poll requests, and relative timeout). -/
  buildPollBatchSync :
    Nat → Nat → Nat → Nat → Array (ClientSlot Nat Unit) →
    Array (Nat × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Poll.Timespec
  /-- Non-blocking handshake reader (`maxHeaderBytes` cap). -/
  stepHandshakeSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Nat → ByteArray → Nat → Poll.PollEvents → Nat →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Non-blocking `recvfrom` loop into `RingBuf`. -/
  recvIntoRing :
    Net.NetOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Nat → Nat → Relay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option (Relay.RingBuf × Bool))
  /-- Non-blocking `sendto` loop draining `RingBuf`. -/
  flushRingNonblock :
    Net.NetOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Nat → Nat → Relay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option Relay.RingBuf)
  /-- One non-blocking bidirectional tunnel relay tick (`pendingPrefix`, `c2u`, `u2c`, half-close, peer reset drain). -/
  stepBidirectionalRelay :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Relay.RelayState Nat → Poll.PollEvents → Poll.PollEvents →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Relay.RelayState Nat)
  /-- Synchronous single-slot transition (`stepSlotM` instantiated over `StateM`). -/
  stepSlotSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Poll.PollEvents → Poll.PollEvents → Nat →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Synchronous server loop tick (`pollAndStepTickM` instantiated over `StateM`). -/
  pollAndStepTickSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    Bool →
    Nat → Nat →
    Array (ClientSlot Nat Unit) →
    Array ConnectEvent →
    StateM (HealthySysWorld × SysAuditTrace Nat) (SysBridge.PollTickOutcome Nat Unit)
  /-- Synchronous single-threaded `RawConnectProxyOpsM` stand-in builder (`SysBridge.mkSyncRawOps`) over instrumented `HealthySysWorld`.
      Formal FD-conservation proofs target this stand-in; the concurrent `IO` task/socketpair driver (`mkIoRawOps` / `runIoProxyLoop` / `teardownIoLoopState`) is verified by runtime, mutation, and stress tests. -/
  mkRawOps :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    RawConnectProxyOpsM (StateM (HealthySysWorld × SysAuditTrace Nat))

/-- Canonical `SysBridgeTarget` wired directly to `SysBridge` and `Relay`.
    Note: `mkRawOps` binds the synchronous single-threaded stand-in `SysBridge.mkSyncRawOps` for formal FD-conservation and `healthyStep` proofs; concurrent `IO` DNS-task/socketpair orchestration (`mkIoRawOps` / `runIoProxyLoop` / `teardownIoLoopState`) is verified separately via runtime, mutation, and stress tests. -/
def realBridgeTarget : SysBridgeTarget :=
  { createListener := fun sys vcfg => SysBridge.createListener sys vcfg
    handleCompleteHeadSync := fun sys limits onHead onResolved slot evs cfd head pipe =>
      SysBridge.handleCompleteHead sys limits onHead onResolved
        (SysBridge.startDnsSync sys limits onResolved) slot evs cfd head pipe
    acceptNewClients := fun sys limits lfd now slots =>
      SysBridge.acceptNewClients sys limits lfd now slots
    listenPollinEnabled := fun cur maxT => (SysBridge.listenPollEvents cur maxT).pollin
    buildPollBatchSync := fun wakeR lfd maxT nowMs slots =>
      SysBridge.buildPollBatchSync wakeR lfd maxT nowMs slots
    stepHandshakeSync := fun sys limits onHead onResolved slot evs cfd hb dl rev now =>
      SysBridge.stepHandshake sys limits onHead onResolved
        (SysBridge.startDnsSync sys limits onResolved) slot evs cfd hb dl rev now
    recvIntoRing := fun net fd fuel rb => Relay.recvIntoRing net fd fuel rb
    flushRingNonblock := fun net fd fuel rb => Relay.flushRingNonblock net fd fuel rb
    stepBidirectionalRelay := fun sys st cRev uRev =>
      Relay.stepBidirectionalRelay sys.net sys.closeFd st cRev uRev
    stepSlotSync := fun sys limits onHead onResolved slot evs cRev uRev nowMs =>
      SysBridge.stepSyncSlot sys limits onHead onResolved slot evs cRev uRev nowMs
    pollAndStepTickSync := fun sys limits onHead onResolved stopFlag wakeR lfd slots evs =>
      SysBridge.pollAndStepTickSync sys limits onHead onResolved stopFlag wakeR lfd slots evs
    mkRawOps := fun sys =>
      SysBridge.mkSyncRawOps sys (fun wt => wt.1.proxyTable)
        (fun (w, tr) tbl => ({ w with proxyTable := tbl }, tr)) }

end LeanSwe.ConnectProxy.HealthySys
