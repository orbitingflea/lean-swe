import LeanSwe.ProcessSandbox.Host.Forwarder
import LeanSwe.ProcessSandbox.Host.StreamIo
import LeanSwe.ProcessSandbox.Proofs.HostBwrapProofs

namespace LeanSwe.ProcessSandbox.Proofs.HostForwarderStream

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Host.Bwrap
open LeanSwe.ProcessSandbox.Host.Forwarder
open LeanSwe.ProcessSandbox.Host.StreamIo

/-- `boxPollEvents` is empty once box inbound EOF has arrived and `h2b` is empty. -/
theorem boxPollEvents_empty_when_drained {fd : Type} (c : ForwardRelayConn fd)
    (heof : c.boxEofIn = true) (hempty : c.h2b.isEmpty = true) :
    c.boxPollEvents.isEmpty = true := by
  simp [ForwardRelayConn.boxPollEvents, Poll.PollEvents.isEmpty, heof, hempty]

/-- `hostPollEvents` watches strictly `POLLOUT` while non-blocking `connect(2)` is in progress. -/
theorem hostPollEvents_when_connecting {fd : Type} (c : ForwardRelayConn fd)
    (hconn : c.hostConnecting = true) :
    c.hostPollEvents = { pollout := true } := by
  simp [ForwardRelayConn.hostPollEvents, hconn]

/-- `buildForwarderPollPlan` suppresses all listener `POLLIN` registrations once active relays reach `MAX_RELAY_SLOTS` (`128`), preventing host `EMFILE`. -/
theorem buildForwarderPollPlan_suppresses_listeners_at_cap {fd : Type}
    (wakeR : fd) (listeners : Array (fd × UInt16)) (relays : Array (ForwardRelayConn fd))
    (hcap : MAX_RELAY_SLOTS ≤ relays.size) :
    (buildForwarderPollPlan wakeR listeners relays).listenerIndices = #[] := by
  have hnot : ¬ (relays.size < MAX_RELAY_SLOTS) := Nat.not_lt.mpr hcap
  unfold buildForwarderPollPlan
  simp [hnot]

private theorem array_push_preserves_elem0 {α : Type} (a : Array α) (x y : α)
    (h0 : a[0]? = some y) : (a.push x)[0]? = some y := by
  have hpos : 0 < a.size := by
    cases hsz : a.size with
    | zero =>
      have : a[0]? = none := Array.getElem?_eq_none (by omega)
      rw [this] at h0; cases h0
    | succ _ => omega
  rw [Array.getElem?_push_lt hpos]
  rw [Array.getElem?_eq_getElem hpos] at h0
  exact h0

/-- `buildForwarderPollPlan` always keeps `wakeR` at poll entry index `0` watching `POLLIN` for arbitrary listeners and relays. -/
theorem buildForwarderPollPlan_wake_entry0 {fd : Type}
    (wakeR : fd) (listeners : Array (fd × UInt16)) (relays : Array (ForwardRelayConn fd)) :
    (buildForwarderPollPlan wakeR listeners relays).entries[0]? =
      some (wakeR, { pollin := true }) := by
  unfold buildForwarderPollPlan
  have hL : ∀ (ls : List (fd × UInt16)) (es : Array (fd × Poll.PollEvents)) (lis : Array (Nat × fd × UInt16)),
      es[0]? = some (wakeR, { pollin := true }) →
      (ls.foldl (fun (acc : Array (fd × Poll.PollEvents) × Array (Nat × fd × UInt16)) (lp : fd × UInt16) =>
        (acc.1.push (lp.1, { pollin := true }), acc.2.push (acc.1.size, lp.1, lp.2))) (es, lis)).1[0]? =
        some (wakeR, { pollin := true }) := by
    intro ls
    induction ls with
    | nil => intro es lis he; exact he
    | cons lp rest ih =>
      intro es lis he
      simp only [List.foldl_cons]
      exact ih _ _ (array_push_preserves_elem0 es _ _ he)
  have hR : ∀ (rs : List (ForwardRelayConn fd)) (es : Array (fd × Poll.PollEvents)) (ris : Array (Option Nat × Option Nat)),
      es[0]? = some (wakeR, { pollin := true }) →
      (rs.foldl (fun (acc : Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat)) (c : ForwardRelayConn fd) =>
        let (es0, r0) := acc
        let bev := c.boxPollEvents
        let (es1, bIdx?) := if !bev.isEmpty then (es0.push (c.boxFd, bev), some es0.size) else (es0, none)
        let hev := c.hostPollEvents
        let (es2, hIdx?) := if !hev.isEmpty then (es1.push (c.hostFd, hev), some es1.size) else (es1, none)
        (es2, r0.push (bIdx?, hIdx?))) (es, ris)).1[0]? =
        some (wakeR, { pollin := true }) := by
    intro rs
    induction rs with
    | nil => intro es ris he; exact he
    | cons c rest ih =>
      intro es ris he
      simp only [List.foldl_cons]
      apply ih
      have h1 : (if !c.boxPollEvents.isEmpty then (es.push (c.boxFd, c.boxPollEvents), some es.size) else (es, none)).1[0]? =
          some (wakeR, { pollin := true }) := by
        split
        · exact array_push_preserves_elem0 es _ _ he
        · exact he
      split
      · exact array_push_preserves_elem0 _ _ _ h1
      · exact h1
  have hbase :
      (if relays.size < MAX_RELAY_SLOTS then
        listeners.foldl
          (fun (acc : Array (fd × Poll.PollEvents) × Array (Nat × fd × UInt16)) (lp : fd × UInt16) =>
            (acc.1.push (lp.1, { pollin := true }), acc.2.push (acc.1.size, lp.1, lp.2)))
          (#[(wakeR, { pollin := true })], #[])
      else (#[(wakeR, { pollin := true })], #[])).1[0]? = some (wakeR, { pollin := true }) := by
    split
    · rw [← Array.foldl_toList]
      exact hL listeners.toList #[(wakeR, { pollin := true })] #[] rfl
    · rfl
  let p1 :=
    if relays.size < MAX_RELAY_SLOTS then
      listeners.foldl
        (fun (acc : Array (fd × Poll.PollEvents) × Array (Nat × fd × UInt16)) (lp : fd × UInt16) =>
          (acc.1.push (lp.1, { pollin := true }), acc.2.push (acc.1.size, lp.1, lp.2)))
        (#[(wakeR, { pollin := true })], #[])
    else (#[(wakeR, { pollin := true })], #[])
  have hres := hR relays.toList p1.1 (Array.emptyWithCapacity relays.size) hbase
  simpa [p1, Array.foldl_toList] using hres

/-- Exact 8-byte wire round-trip theorem: `decodeInitStatusMsg (encodeInitStatusMsg m) = some m` for every `InitStatusMsg`. -/
theorem decodeInitStatusMsg_encodeInitStatusMsg (m : InitStatusMsg) :
    decodeInitStatusMsg (encodeInitStatusMsg m) = some m := by
  cases m with
  | mk kind flag value =>
    unfold decodeInitStatusMsg encodeInitStatusMsg
    have hsz : (ByteArray.mk #[kind, flag, 0, 0,
      UInt8.ofNat (value.toUInt32.toNat % 256),
      UInt8.ofNat ((value.toUInt32.toNat / 256) % 256),
      UInt8.ofNat ((value.toUInt32.toNat / 65536) % 256),
      UInt8.ofNat ((value.toUInt32.toNat / 16777216) % 256)]).size = 8 := rfl
    simp only [hsz, ↓reduceDIte]
    congr 1
    have hv : value.toUInt32.toNat < 4294967296 := value.toUInt32.toBitVec.isLt
    have hmod : ∀ n : Nat, (UInt8.ofNat (n % 256)).toNat = n % 256 := fun n => by
      simp
    have hrecon :
        (UInt8.ofNat (value.toUInt32.toNat % 256)).toNat +
        256 * (UInt8.ofNat ((value.toUInt32.toNat / 256) % 256)).toNat +
        65536 * (UInt8.ofNat ((value.toUInt32.toNat / 65536) % 256)).toNat +
        16777216 * (UInt8.ofNat ((value.toUInt32.toNat / 16777216) % 256)).toNat =
        value.toUInt32.toNat := by
      rw [hmod, hmod, hmod, hmod]
      omega
    have heqU :
        UInt32.ofNat (
          (UInt8.ofNat (value.toUInt32.toNat % 256)).toNat +
          256 * (UInt8.ofNat ((value.toUInt32.toNat / 256) % 256)).toNat +
          65536 * (UInt8.ofNat ((value.toUInt32.toNat / 65536) % 256)).toNat +
          16777216 * (UInt8.ofNat ((value.toUInt32.toNat / 16777216) % 256)).toNat) =
        value.toUInt32 := by
      rw [hrecon]
      exact UInt32.ofNat_toNat
    have heqI : (UInt32.ofNat (
          (UInt8.ofNat (value.toUInt32.toNat % 256)).toNat +
          256 * (UInt8.ofNat ((value.toUInt32.toNat / 256) % 256)).toNat +
          65536 * (UInt8.ofNat ((value.toUInt32.toNat / 65536) % 256)).toNat +
          16777216 * (UInt8.ofNat ((value.toUInt32.toNat / 16777216) % 256)).toNat)).toInt32 = value := by
      rw [heqU]
      cases value; rfl
    exact congrArg (InitStatusMsg.mk kind flag) heqI

/-- `decodeInitStatusMsg` rejects any byte slice whose length is not exactly `8`. -/
theorem decodeInitStatusMsg_wrong_size (bs : ByteArray) (h : bs.size ≠ 8) :
    decodeInitStatusMsg bs = none := by
  unfold decodeInitStatusMsg
  simp [h]

/-- `classifyBoxStreamResult` attributes `PS_STATUS_EXEC_ERR` to `cwd` when `flag ≠ 0` and to `program` when `flag = 0`. -/
theorem classifyBoxStreamResult_execErr (program cwd : String) (to lim : Bool)
    (flag : UInt8) (code : Int32) (out err : ByteArray) :
    ∃ se, classifyBoxStreamResult program cwd to lim
      (some { kind := PS_STATUS_EXEC_ERR, flag := flag, value := code }) out err = .error se ∧
      se.path = some (if flag != 0 then cwd else program) ∧
      se.message ≠ "" := by
  unfold classifyBoxStreamResult
  simp only [PS_STATUS_EXEC_ERR, beq_self_eq_true, ↓reduceIte]
  let errCode : Errno := if code == 0 then Errno.EIO else code.toUInt32
  let targetPath := if flag != 0 then cwd else program
  let ctx := if flag != 0 then "chdir" else "execvp"
  have hcls := HostBwrap.mapPathErrnoToSandboxError_classification targetPath ctx errCode
  exact ⟨mapPathErrnoToSandboxError targetPath ctx errCode, rfl, hcls.1, hcls.2.2.1⟩

/-- `classifyBoxStreamResult` maps `PS_STATUS_INIT_ERR` (when not timed out or limit-exceeded) to `.unavailable`. -/
theorem classifyBoxStreamResult_initErr (program cwd : String) (code : Int32) (out err : ByteArray) :
    ∃ se, classifyBoxStreamResult program cwd false false
      (some { kind := PS_STATUS_INIT_ERR, flag := 0, value := code }) out err = .error se ∧
      se.kind = .unavailable ∧ se.message ≠ "" := by
  have hnonEmpty : ∀ s : String, Internal.nonEmptyMsg "sandbox unavailable" s ≠ "" := by
    intro s
    unfold Internal.nonEmptyMsg
    split
    · decide
    · next h => exact String.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr h)
  unfold classifyBoxStreamResult
  simp only [PS_STATUS_INIT_ERR, PS_STATUS_EXEC_ERR, Bool.not_false, Bool.and_self]
  have hne : ((2 : UInt8) == 3) = false := by decide
  have heq : ((2 : UInt8) == 2) = true := rfl
  simp only [hne, heq, Bool.false_eq_true, ↓reduceIte, Internal.mapRawError]
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only
  exact hnonEmpty _

/-- `classifyBoxStreamResult` maps `timedOut`, `limitExceeded`, `PS_STATUS_EXITED`, `PS_STATUS_SIGNALED`, and silent-EOF (`none` -> `.signaled 9`) deterministically. -/
theorem classifyBoxStreamResult_outcomes (program cwd : String) (out err : ByteArray) :
    classifyBoxStreamResult program cwd true false none out err =
      .ok { outcome := .timedOut, stdout := out, stderr := err } ∧
    classifyBoxStreamResult program cwd false true none out err =
      .ok { outcome := .outputLimitExceeded, stdout := out, stderr := err } ∧
    classifyBoxStreamResult program cwd false false none out err =
      .ok { outcome := .signaled 9, stdout := out, stderr := err } ∧
    classifyBoxStreamResult program cwd false false
      (some { kind := PS_STATUS_EXITED, flag := 0, value := 42 }) out err =
      .ok { outcome := .exited 42, stdout := out, stderr := err } ∧
    classifyBoxStreamResult program cwd false false
      (some { kind := PS_STATUS_SIGNALED, flag := 0, value := 15 }) out err =
      .ok { outcome := .signaled 15, stdout := out, stderr := err } := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;>
    (simp [classifyBoxStreamResult, PS_STATUS_EXEC_ERR, PS_STATUS_INIT_ERR,
      PS_STATUS_EXITED, PS_STATUS_SIGNALED]; decide)

/-- `buildBoxPollEntries` size equals the number of currently open descriptors among `(inFd?, outFd?, errFd?, statusFd?)`. -/
theorem buildBoxPollEntries_size {fd : Type} (st : BoxStreamState fd) :
    (buildBoxPollEntries st).size =
      (if st.inFd?.isSome then 1 else 0) +
      (if st.outFd?.isSome then 1 else 0) +
      (if st.errFd?.isSome then 1 else 0) +
      (if st.statusFd?.isSome then 1 else 0) := by
  unfold buildBoxPollEntries
  cases st.inFd? <;> cases st.outFd? <;> cases st.errFd? <;> cases st.statusFd? <;> simp

end LeanSwe.ProcessSandbox.Proofs.HostForwarderStream
