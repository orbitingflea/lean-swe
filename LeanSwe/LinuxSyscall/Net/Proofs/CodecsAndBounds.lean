import LeanSwe.LinuxSyscall.Net.SpecTests
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Net.Interface

namespace LeanSwe.LinuxSyscall.Net

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem bool_beq_eq_of_inj {α β : Type} [BEq α] [DecidableEq α] [BEq β] [DecidableEq β]
    (hBeq : ∀ x y : α, (x == y) = decide (x = y))
    (hBeqB : ∀ u v : β, (u == v) = decide (u = v))
    (enc : α → β) (hInj : ∀ x y : α, enc x = enc y → x = y) :
    ∀ x y : α, (enc x == enc y) = (x == y) := by
  intro x y
  rw [hBeq x y, hBeqB (enc x) (enc y)]
  by_cases h : x = y
  · subst h; simp
  · have hne : enc x ≠ enc y := fun heq => h (hInj x y heq)
    simp [h, hne]

private theorem ui32_beq_eq_decide (u v : UInt32) : (u == v) = decide (u = v) := by
  by_cases h : u = v
  · subst h; simp
  · simp [h, beq_false_of_ne h]

private theorem ui32_pair_beq_eq_decide (u v : UInt32 × UInt32) : (u == v) = decide (u = v) := by
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  by_cases h : (u1, u2) = (v1, v2)
  · cases h; simp
  · simp [h, beq_false_of_ne h]

private theorem sockDomain_beq_eq_decide (x y : SockDomain) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem sockType_beq_eq_decide (x y : SockType) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem sockFlags_beq_eq_decide (x y : SockFlags) : (x == y) = decide (x = y) := by
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> rfl

private theorem sockOpt_beq_eq_decide (x y : SockOpt) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem setSockOpt_beq_eq_decide (x y : SetSockOpt) : (x == y) = decide (x = y) := by
  cases x; cases y; rfl

private theorem msgFlags_beq_eq_decide (x y : MsgFlags) : (x == y) = decide (x = y) := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;> rfl

private theorem shutHow_beq_eq_decide (x y : ShutHow) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem netIoctlOp_beq_eq_decide (x y : NetIoctlOp) : (x == y) = decide (x = y) := by
  cases x with
  | getIfFlags =>
    cases y with
    | getIfFlags => rfl
    | setIfFlags _ => rfl
  | setIfFlags a =>
    cases y with
    | getIfFlags => rfl
    | setIfFlags b =>
      change (a == b) = decide (NetIoctlOp.setIfFlags a = NetIoctlOp.setIfFlags b)
      by_cases h : a = b
      · subst h; simp
      · simp [h]

private theorem sockDomain_toTag_inj (x y : SockDomain) (h : x.toTag = y.toTag) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem sockType_toTag_inj (x y : SockType) (h : x.toTag = y.toTag) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem sockFlags_toBits_inj (x y : SockFlags) (h : x.toBits = y.toBits) : x = y := by
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> first | rfl | exact absurd h (by decide)

private theorem sockOpt_toTag_inj (x y : SockOpt) (h : x.toTag = y.toTag) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem setSockOpt_toTag_inj (x y : SetSockOpt) (_ : x.toTag = y.toTag) : x = y := by
  cases x; cases y; rfl

private theorem msgFlags_toBits_inj (x y : MsgFlags) (h : x.toBits = y.toBits) : x = y := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    first | rfl | exact absurd h (by decide)

private theorem shutHow_toTag_inj (x y : ShutHow) (h : x.toTag = y.toTag) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem netIoctlOp_toRaw_inj (x y : NetIoctlOp) (h : x.toRaw = y.toRaw) : x = y := by
  cases x with
  | getIfFlags =>
    cases y with
    | getIfFlags => rfl
    | setIfFlags _ => simp [NetIoctlOp.toRaw] at h
  | setIfFlags a =>
    cases y with
    | getIfFlags => simp [NetIoctlOp.toRaw] at h
    | setIfFlags b =>
      simp [NetIoctlOp.toRaw] at h
      subst h
      rfl

private theorem sockAddr_roundtrip (sa : SockAddr) : SockAddr.ofRawTuple sa.toRawTuple = sa := by
  cases sa <;> rfl

/-- `isTransientNetErrno` and `NetErrorKind.ofErrno` satisfy their complete classification specification across all `Errno` values. -/
theorem net_errno_classification_allPass :
    AllPass (test_net_errno_classification isTransientNetErrno NetErrorKind.ofErrno) := by
  intro e
  dsimp only [Bind.bind, assert, pure]
  refine ⟨by decide, rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals decide

/-- All symbolic `Net` encoders are injective, default `SockFlags` enables `cloexec`, `SockAddr.ofRawTuple`/`toRawTuple` round-trips across exact 8-lane wire layouts, and `SockAddr.isValidTarget` validates `AF_UNIX` path bounds. -/
theorem net_flags_and_sockaddr_codecs_allPass :
    AllPass (test_net_flags_and_sockaddr_codecs
      SockDomain.toTag SockType.toTag SockFlags.toBits SockOpt.toTag SetSockOpt.toTag
      MsgFlags.toBits ShutHow.toTag NetIoctlOp.toRaw SockAddr.toRawTuple SockAddr.ofRawTuple
      SockAddr.isValidTarget {} {}) := by
  intro d1 d2
  refine ⟨bool_beq_eq_of_inj sockDomain_beq_eq_decide ui32_beq_eq_decide SockDomain.toTag sockDomain_toTag_inj d1 d2, ?_⟩
  intro t1 t2
  refine ⟨bool_beq_eq_of_inj sockType_beq_eq_decide ui32_beq_eq_decide SockType.toTag sockType_toTag_inj t1 t2, ?_⟩
  intro sf1 sf2
  refine ⟨bool_beq_eq_of_inj sockFlags_beq_eq_decide ui32_beq_eq_decide SockFlags.toBits sockFlags_toBits_inj sf1 sf2, ?_⟩
  intro o1 o2
  refine ⟨bool_beq_eq_of_inj sockOpt_beq_eq_decide ui32_beq_eq_decide SockOpt.toTag sockOpt_toTag_inj o1 o2, ?_⟩
  intro so1 so2
  refine ⟨bool_beq_eq_of_inj setSockOpt_beq_eq_decide ui32_beq_eq_decide SetSockOpt.toTag setSockOpt_toTag_inj so1 so2, ?_⟩
  intro mf1 mf2
  refine ⟨bool_beq_eq_of_inj msgFlags_beq_eq_decide ui32_beq_eq_decide MsgFlags.toBits msgFlags_toBits_inj mf1 mf2, ?_⟩
  intro sh1 sh2
  refine ⟨bool_beq_eq_of_inj shutHow_beq_eq_decide ui32_beq_eq_decide ShutHow.toTag shutHow_toTag_inj sh1 sh2, ?_⟩
  intro io1 io2
  refine ⟨bool_beq_eq_of_inj netIoctlOp_beq_eq_decide ui32_pair_beq_eq_decide NetIoctlOp.toRaw netIoctlOp_toRaw_inj io1 io2, ?_⟩
  intro sa
  refine ⟨sockAddr_roundtrip sa, ?_⟩
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
    by unfold SockAddr.isValidTarget; simp [hasEmbeddedNul_eq_toList_any]; decide,
    rfl, rfl, rfl,
    ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem isValidTarget_unix_empty :
    SockAddr.isValidTarget (.unix (ByteArray.mk #[])) = false := by
  decide

private theorem isValidTarget_unix_nul {p : ByteArray}
    (h : p.data[0]? != some 0 ∧ hasEmbeddedNul p = true) :
    SockAddr.isValidTarget (.unix p) = false := by
  unfold SockAddr.isValidTarget
  have h0 : (p.data[0]? == some 0) = false := by simpa using h.1
  simp [h0, h.2]

private theorem isValidTarget_unix_long {p : ByteArray} (h : p.data.size > UNIX_PATH_MAX) :
    SockAddr.isValidTarget (.unix p) = false := by
  unfold SockAddr.isValidTarget
  have h' : p.size > UNIX_PATH_MAX := h
  have hNotLe : ¬ (p.size ≤ UNIX_PATH_MAX) := Nat.not_le_of_lt h'
  simp [hNotLe]

/-- `Internal.mkNetOpsM raw` rejects every invalid `AF_UNIX` path, invalid `SCM_RIGHTS` batch bound, and invalid `ioctl` interface name with `Errno.EINVAL` before calling raw hooks. -/
theorem net_ops_boundaryValidation_einval_mkNetOpsM_allPass
    {S fd : Type} (raw : Internal.PosixNetOpsM (StateM S) fd) :
    AllPass (test_net_ops_boundaryValidation_einval (Internal.mkNetOpsM raw)) := by
  intro s₀ h _ nulBytes hNul longUnix hLongUnix longIf hLongIf overFds hOverFds overMaxFds hOverMaxFds
  dsimp only [Bind.bind, assert, pure, Internal.mkNetOpsM, StateT.run, Pure.pure, StateT.pure,
    isValidScmCount, isValidIfname]
  have hOverFdsNotLe : ¬ (overFds.size ≤ MAX_SCM_FDS) := Nat.not_le_of_lt hOverFds
  have hOverMaxNotLe : ¬ (overMaxFds.toNat ≤ MAX_SCM_FDS) := Nat.not_le_of_lt hOverMaxFds
  have hLongIfNotLt : ¬ (longIf.size < IFNAMSIZ) := Nat.not_lt_of_ge hLongIf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [isValidTarget_unix_empty]; rfl
  · simp [isValidTarget_unix_nul hNul]; rfl
  · simp [isValidTarget_unix_long hLongUnix]; rfl
  · simp [isValidTarget_unix_empty]; rfl
  · simp [isValidTarget_unix_nul hNul]; rfl
  · simp [isValidTarget_unix_long hLongUnix]; rfl
  · rfl
  · simp [hOverFdsNotLe]; rfl
  · rfl
  · simp [hOverMaxNotLe]; rfl
  · simp [hNul.2]; rfl
  · simp [hLongIfNotLt]; rfl

/-- Concrete witness demonstrating reachability of `test_net_ops_boundaryValidation_einval` on `Internal.mkNetOpsM`. -/
theorem net_ops_boundaryValidation_einval_mkNetOpsM_canReach :
    CanReach (test_net_ops_boundaryValidation_einval (Internal.mkNetOpsM
      ({ socket := fun _ _ _ _ => pure (.error Errno.ENOSYS)
         socketpair := fun _ _ _ => pure (.error Errno.ENOSYS)
         bind := fun _ _ => pure (.error Errno.ENOSYS)
         listen := fun _ _ => pure (.error Errno.ENOSYS)
         accept4 := fun _ _ => pure (.error Errno.ENOSYS)
         connect := fun _ _ => pure (.error Errno.ENOSYS)
         getsockopt := fun _ _ => pure (.error Errno.ENOSYS)
         setsockopt := fun _ _ _ => pure (.error Errno.ENOSYS)
         getsockname := fun _ => pure (.error Errno.ENOSYS)
         recvfrom := fun _ _ _ => pure (.error Errno.ENOSYS)
         sendto := fun _ _ _ => pure (.error Errno.ENOSYS)
         shutdown := fun _ _ => pure (.error Errno.ENOSYS)
         sendmsg := fun _ _ => pure (.error Errno.ENOSYS)
         recvmsg := fun _ _ => pure (.error Errno.ENOSYS)
         ioctl := fun _ _ _ _ => pure (.error Errno.ENOSYS) } :
        Internal.PosixNetOpsM (StateM NetState) HandleId))) := by
  have hNul : (ByteArray.mk #[97, 0, 98]).data[0]? != some 0 ∧ hasEmbeddedNul (ByteArray.mk #[97, 0, 98]) = true := by decide
  have hLongUnix : (ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97)).data.size > UNIX_PATH_MAX := by
    rw [Array.size_replicate]; decide
  have hLongIf : (ByteArray.mk (Array.replicate IFNAMSIZ 97)).data.size ≥ IFNAMSIZ := by
    rw [Array.size_replicate]; exact Nat.le_refl _
  have hOverFds : (Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId)).size > MAX_SCM_FDS := by
    rw [Array.size_replicate]; exact Nat.lt_succ_self _
  have hOverMax : ((MAX_SCM_FDS + 1 : Nat).toUInt32).toNat > MAX_SCM_FDS := by decide
  refine ⟨NetState.initial false, 0, .getIfFlags, ByteArray.mk #[97, 0, 98], hNul,
    ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97), hLongUnix,
    ByteArray.mk (Array.replicate IFNAMSIZ 97), hLongIf,
    Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId), hOverFds,
    (MAX_SCM_FDS + 1 : Nat).toUInt32, hOverMax, ?_⟩
  exact net_ops_boundaryValidation_einval_mkNetOpsM_allPass _
    (NetState.initial false) 0 .getIfFlags (ByteArray.mk #[97, 0, 98]) hNul
    (ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97)) hLongUnix
    (ByteArray.mk (Array.replicate IFNAMSIZ 97)) hLongIf
    (Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId)) hOverFds
    (MAX_SCM_FDS + 1 : Nat).toUInt32 hOverMax

/-- `modelOps` rejects every invalid `AF_UNIX` path, invalid `SCM_RIGHTS` batch bound, and invalid `ioctl` interface name with `Errno.EINVAL` without mutating state. -/
theorem net_ops_boundaryValidation_einval_model_allPass :
    AllPass (test_net_ops_boundaryValidation_einval modelOps) := by
  intro s₀ h _ nulBytes hNul longUnix hLongUnix longIf hLongIf overFds hOverFds overMaxFds hOverMaxFds
  dsimp only [Bind.bind, assert, pure, modelOps, runModelStep, stepNetCore, preCheckNet, emitErr,
    StateT.run, StateT.bind, get, getThe, MonadState.get, MonadStateOf.get, StateT.get,
    set, MonadState.set, MonadStateOf.set, StateT.set, Pure.pure, StateT.pure,
    isValidScmCount, isValidIfname]
  have hOverFdsNotLe : ¬ (overFds.size ≤ MAX_SCM_FDS) := Nat.not_le_of_lt hOverFds
  have hOverMaxNotLe : ¬ (overMaxFds.toNat ≤ MAX_SCM_FDS) := Nat.not_le_of_lt hOverMaxFds
  have hLongIfNotLt : ¬ (longIf.size < IFNAMSIZ) := Nat.not_lt_of_ge hLongIf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [isValidTarget_unix_empty]; rfl
  · simp [isValidTarget_unix_nul hNul]; rfl
  · simp [isValidTarget_unix_long hLongUnix]; rfl
  · simp [isValidTarget_unix_empty]; rfl
  · simp [isValidTarget_unix_nul hNul]; rfl
  · simp [isValidTarget_unix_long hLongUnix]; rfl
  · rfl
  · simp [hOverFdsNotLe]; rfl
  · rfl
  · simp [hOverMaxNotLe]; rfl
  · simp [hNul.2]; rfl
  · simp [hLongIfNotLt]; rfl

/-- Concrete witness demonstrating reachability of `test_net_ops_boundaryValidation_einval` on `modelOps`. -/
theorem net_ops_boundaryValidation_einval_model_canReach :
    CanReach (test_net_ops_boundaryValidation_einval modelOps) := by
  have hNul : (ByteArray.mk #[97, 0, 98]).data[0]? != some 0 ∧ hasEmbeddedNul (ByteArray.mk #[97, 0, 98]) = true := by decide
  have hLongUnix : (ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97)).data.size > UNIX_PATH_MAX := by
    rw [Array.size_replicate]; decide
  have hLongIf : (ByteArray.mk (Array.replicate IFNAMSIZ 97)).data.size ≥ IFNAMSIZ := by
    rw [Array.size_replicate]; exact Nat.le_refl _
  have hOverFds : (Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId)).size > MAX_SCM_FDS := by
    rw [Array.size_replicate]; exact Nat.lt_succ_self _
  have hOverMax : ((MAX_SCM_FDS + 1 : Nat).toUInt32).toNat > MAX_SCM_FDS := by decide
  refine ⟨NetState.initial false, 0, .getIfFlags, ByteArray.mk #[97, 0, 98], hNul,
    ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97), hLongUnix,
    ByteArray.mk (Array.replicate IFNAMSIZ 97), hLongIf,
    Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId), hOverFds,
    (MAX_SCM_FDS + 1 : Nat).toUInt32, hOverMax, ?_⟩
  exact net_ops_boundaryValidation_einval_model_allPass
    (NetState.initial false) 0 .getIfFlags (ByteArray.mk #[97, 0, 98]) hNul
    (ByteArray.mk (Array.replicate (UNIX_PATH_MAX + 1) 97)) hLongUnix
    (ByteArray.mk (Array.replicate IFNAMSIZ 97)) hLongIf
    (Array.replicate (MAX_SCM_FDS + 1) (0 : HandleId)) hOverFds
    (MAX_SCM_FDS + 1 : Nat).toUInt32 hOverMax

/-- `Internal.mkNetOpsM` satisfies its complete 15-syscall protocol validation, flag/tag/address encoding, and raw delegation promise. -/
theorem net_mkNetOps_encodesAndDelegates_allPass :
    AllPass (test_net_mkNetOps_encodesAndDelegates (@Internal.mkNetOpsM Id Nat _)) := by
  intro raw dom typ sf proto fd validAddr hValidAddr backlog opt setOpt optVal maxBytes mf payload how
    validFds hValidFds validMaxFds hValidMax ioOp validIf hValidIf
  have hNotBadAddr : (!validAddr.isValidTarget) = false := by simp [hValidAddr]
  have hNotBadFds : (!isValidScmCount validFds.size) = false := by simp [hValidFds]
  have hNotBadMax : (!isValidScmCount validMaxFds.toNat) = false := by simp [hValidMax]
  have hNotBadIf : (!isValidIfname validIf) = false := by simp [hValidIf]
  dsimp only [test_net_mkNetOps_encodesAndDelegates, Internal.mkNetOpsM, Bind.bind, assert, pure, Id.instMonad]
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, trivial⟩
  · cases validateSocketArgs dom typ proto <;> rfl
  · cases validateSocketpairArgs dom typ <;> rfl
  · simp only [hNotBadAddr, Bool.false_eq_true, ↓reduceIte]
  · cases raw.accept4 fd sf.toBits with
    | error _ => rfl
    | ok p => cases p; rfl
  · simp only [hNotBadAddr, Bool.false_eq_true, ↓reduceIte]
  · cases raw.getsockname fd <;> rfl
  · simp only [hNotBadFds, Bool.false_eq_true, ↓reduceIte]
  · simp only [hNotBadMax, Bool.false_eq_true, ↓reduceIte]
  · simp only [hNotBadIf, Bool.false_eq_true, ↓reduceIte]

private def dummyIdRawNetOps : PosixNetOpsM Id Nat :=
  { socket := fun _ _ _ _ => .ok 0
    socketpair := fun _ _ _ => .ok (0, 1)
    bind := fun _ _ => .ok ()
    listen := fun _ _ => .ok ()
    accept4 := fun _ _ => .ok (1, (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[]))
    connect := fun _ _ => .ok ()
    getsockopt := fun _ _ => .ok 0
    setsockopt := fun _ _ _ => .ok ()
    getsockname := fun _ => .ok (0, INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.mk #[])
    recvfrom := fun _ _ _ => .ok (ByteArray.mk #[])
    sendto := fun _ _ _ => .ok 0
    shutdown := fun _ _ => .ok ()
    sendmsg := fun _ _ => .ok ()
    recvmsg := fun _ _ => .ok #[]
    ioctl := fun _ _ _ _ => .ok 0 }

/-- Concrete witness demonstrating reachability of `test_net_mkNetOps_encodesAndDelegates`. -/
theorem net_mkNetOps_encodesAndDelegates_canReach :
    CanReach (test_net_mkNetOps_encodesAndDelegates (@Internal.mkNetOpsM Id Nat _)) := by
  have hAddr : (SockAddr.ipv4 INADDR_LOOPBACK 8080).isValidTarget = true := rfl
  have hFds : isValidScmCount (#[0] : Array Nat).size = true := by decide
  have hMax : isValidScmCount ((1 : UInt32).toNat) = true := by decide
  have hIf : isValidIfname loIfname = true := by decide
  refine ⟨dummyIdRawNetOps, .inet, .stream, {}, 0, 0, .ipv4 INADDR_LOOPBACK 8080, hAddr,
    128, .error, .reuseAddr, 1, 16, {}, ByteArray.mk #[], .rdwr, #[0], hFds, 1, hMax, .getIfFlags, loIfname, hIf, ?_⟩
  exact net_mkNetOps_encodesAndDelegates_allPass dummyIdRawNetOps
    .inet .stream {} 0 0 (.ipv4 INADDR_LOOPBACK 8080) hAddr
    128 .error .reuseAddr 1 16 {} (ByteArray.mk #[]) .rdwr #[0] hFds 1 hMax .getIfFlags loIfname hIf

/-- `Net.defaultOps` and all 15 top-level `Net` functions satisfy their `Interface` wiring and `SOCK_CLOEXEC` / `MSG_NOSIGNAL` default-argument specification. -/
theorem net_interface_defaultOpsWiring_allPass :
    AllPass (test_net_interface_defaultOpsWiring
      Internal.mkNetOps defaultOps
      (fun d t sf p => socket d t sf p) (fun d t => socket d t)
      (fun d t sf => socketpair d t sf) (fun d t => socketpair d t)
      bind
      (fun h bl => listen h bl) (fun h => listen h)
      (fun h sf => accept4 h sf) (fun h => accept4 h)
      connect getsockopt setsockopt getsockname
      (fun h m mf => recvfrom h m mf) (fun h m => recvfrom h m)
      (fun h d mf => sendto h d mf) (fun h d => sendto h d)
      shutdown sendmsg recvmsg ioctl) := by
  intro dom typ sf proto h sa bl opt setOpt val maxB mf data how fds maxF ioOp ifn
  dsimp only [test_net_interface_defaultOpsWiring, Bind.bind, assert, pure]
  exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

end LeanSwe.LinuxSyscall.Net
