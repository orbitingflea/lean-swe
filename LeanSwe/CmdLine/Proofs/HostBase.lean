import Core.Obeys
import LeanSwe.CmdLine.Interface

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.LinuxSyscall

/-- Evaluate `pure` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_pure {W α : Type} (a : α) (w : W) :
    ((pure a : ExceptT IO.Error (StateM W) α).run.run w) = (.ok a, w) := rfl

/-- Evaluate `throwThe IO.Error` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_throw {W α : Type} (err : IO.Error) (w : W) :
    ((throwThe IO.Error err : ExceptT IO.Error (StateM W) α).run.run w) = (.error err, w) := rfl

/-- Evaluate `<$>` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_map {W α β : Type} (f : α → β)
    (x : ExceptT IO.Error (StateM W) α) (w : W) :
    ((f <$> x).run.run w) = ((x.run.run w).1.map f, (x.run.run w).2) := by
  change ExceptT.map f x w = _
  unfold ExceptT.map
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk]
  cases hx : x w with
  | mk v w1 => cases v <;> rfl

/-- Evaluate `*>` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_seqRight {W α β : Type}
    (x : ExceptT IO.Error (StateM W) α) (y : ExceptT IO.Error (StateM W) β) (w : W) :
    ((x *> y).run.run w) =
      match x.run.run w with
      | (.error e, w1) => (.error e, w1)
      | (.ok _, w1) => y.run.run w1 := by
  change ExceptT.bind x (fun _ => y) w = _
  unfold ExceptT.bind ExceptT.bindCont
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk]
  cases hx : x w with
  | mk v w1 => cases v <;> rfl

/-- Evaluate `>>=` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_bind {W α β : Type}
    (x : ExceptT IO.Error (StateM W) α)
    (f : α → ExceptT IO.Error (StateM W) β) (w : W) :
    ((x >>= f).run.run w) =
      match x.run.run w with
      | (.error e, w1) => (.error e, w1)
      | (.ok a, w1) => (f a).run.run w1 := by
  change ExceptT.bind x f w = _
  unfold ExceptT.bind ExceptT.bindCont
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk]
  cases hx : x w with
  | mk v w1 => cases v <;> rfl

/-- Evaluate `tryCatch` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_tryCatch {W α : Type}
    (x : ExceptT IO.Error (StateM W) α)
    (h : IO.Error → ExceptT IO.Error (StateM W) α) (w : W) :
    ((tryCatch x h).run.run w) =
      match x.run.run w with
      | (.ok a, w1) => (.ok a, w1)
      | (.error e, w1) => (h e).run.run w1 := by
  change ExceptT.tryCatch x h w = _
  unfold ExceptT.tryCatch
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk]
  cases hx : x w with
  | mk v w1 => cases v <;> rfl

/-- Evaluate `tryFinally'` in `ExceptT IO.Error (StateM W)`. -/
theorem exceptT_run_tryFinally {W α β : Type}
    (x : ExceptT IO.Error (StateM W) α)
    (fin : Option α → ExceptT IO.Error (StateM W) β) (w : W) :
    ((tryFinally' x fin).run.run w) =
      match x.run.run w with
      | (.ok a, w1) =>
        match (fin (some a)).run.run w1 with
        | (.ok b, w2) => (.ok (a, b), w2)
        | (.error e, w2) => (.error e, w2)
      | (.error e, w1) =>
        match (fin none).run.run w1 with
        | (.ok _, w2) => (.error e, w2)
        | (.error e2, w2) => (.error e2, w2) := by
  change (ExceptT.finally.tryFinally' x fin) w = _
  unfold ExceptT.finally MonadFinally.tryFinally' StateT.tryFinally Id.finally
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk, Id.instMonad]
  cases hx : x w with
  | mk v w1 =>
    cases v with
    | ok a =>
      dsimp only
      cases hf : fin (some a) w1 with
      | mk fv w2 => cases fv <;> rfl
    | error e =>
      dsimp only
      cases hf : fin none w1 with
      | mk fv w2 => cases fv <;> rfl

theorem byteArray_extract_toList (data : ByteArray) (b e : Nat) :
    (data.extract b e).data.toList = (data.data.toList.drop b).take (e - b) := by
  have h1 : (data.extract b e).data = data.data.extract b (b + (e - b)) := by
    simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.data_empty, ByteArray.size_data,
      Array.extract_zero, Array.empty_append, Array.extract_empty, Array.append_empty]
  rw [h1, Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]

theorem byteArray_extract_self_empty (data : ByteArray) (k : Nat) :
    data.extract k k = ByteArray.empty := by
  apply ByteArray.ext; apply Array.ext'
  rw [byteArray_extract_toList]; simp

theorem byteArray_extract_zero_size (data : ByteArray) :
    data.extract 0 data.size = data := by
  apply ByteArray.ext; apply Array.ext'
  rw [byteArray_extract_toList]
  have hSz : data.size = data.data.toList.length := rfl
  rw [hSz, List.drop_zero, Nat.sub_zero, List.take_length]

theorem byteArray_extract_append (data : ByteArray) {off mid stop : Nat}
    (h1 : off ≤ mid) (h2 : mid ≤ stop) :
    data.extract off mid ++ data.extract mid stop = data.extract off stop := by
  apply ByteArray.ext; apply Array.ext'
  have hApp : (data.extract off mid ++ data.extract mid stop).data.toList =
      (data.extract off mid).data.toList ++ (data.extract mid stop).data.toList := by
    simp only [ByteArray.data_append, Array.toList_append]
  rw [hApp, byteArray_extract_toList, byteArray_extract_toList, byteArray_extract_toList]
  have hDrop : data.data.toList.drop mid = (data.data.toList.drop off).drop (mid - off) := by
    rw [List.drop_drop]; congr 1; omega
  have hTake : (data.data.toList.drop off).take (mid - off) ++
      ((data.data.toList.drop off).drop (mid - off)).take (stop - mid) =
      (data.data.toList.drop off).take ((mid - off) + (stop - mid)) :=
    (List.take_add (l := data.data.toList.drop off) (i := mid - off) (j := stop - mid)).symm
  rw [hDrop, hTake]; congr 1; omega

theorem byteArray_extract_size (data : ByteArray) {off stop : Nat}
    (h1 : off ≤ stop) (h2 : stop ≤ data.size) :
    (data.extract off stop).size = stop - off := by
  have hL := congrArg List.length (byteArray_extract_toList data off stop)
  have hSz : (data.extract off stop).size = (data.extract off stop).data.toList.length := rfl
  have hDataSz : data.size = data.data.toList.length := rfl
  rw [← hSz, List.length_take, List.length_drop, ← hDataSz] at hL
  omega

theorem byteArray_append_assoc (a b c : ByteArray) : (a ++ b) ++ c = a ++ (b ++ c) := by
  apply ByteArray.ext; apply Array.ext'; simp [ByteArray.data_append]

theorem byteArray_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext; apply Array.ext'; simp

theorem string_nonEmpty_utf8_pos {s : String} (h : s.isEmpty = false) :
    0 < s.toUTF8.size := by
  change (s.toUTF8.size == 0) = false at h
  simp only [beq_eq_false_iff_ne] at h
  omega

theorem caps_envGet_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (key : String) (w : W) :
    ((caps.env.getEnv key).run.run w).1 = .ok (LeanSwe.EnvVars.Model.getEnvModel (proj w).env key) ∧
      proj ((caps.env.getEnv key).run.run w).2 = proj w := by
  have h := hCaps w (.envGet key) rfl
  dsimp only [Model.execCapsStep] at h
  rw [exceptT_run_map] at h
  dsimp only [Model.allowedHostCapsStep] at h
  cases hr : (caps.env.getEnv key).run.run w with
  | mk res w1 =>
    rw [hr] at h
    cases res with
    | error _ => simp [Except.map] at h
    | ok _ =>
      simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.envVal.injEq] at h
      exact ⟨congrArg Except.ok h.1, h.2⟩

theorem caps_dupStdio_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (slot : Files.StdioFd) (w : W) :
    match (proj w).fault with
    | .dupErrno code =>
      ((caps.files.dupStdio slot).run.run w).1 = .ok (.error code) ∧
        proj ((caps.files.dupStdio slot).run.run w).2 = proj w
    | .none | .ioErrno _ | .ioThrow _ =>
      ∃ fd : RawFd,
        ((caps.files.dupStdio slot).run.run w).1 = .ok (.ok fd) ∧
          proj ((caps.files.dupStdio slot).run.run w).2 =
            { proj w with openDups := slot :: (proj w).openDups } := by
  have h := hCaps w (.dupStdio slot) rfl
  dsimp only [Model.execCapsStep] at h
  rw [exceptT_run_map] at h
  dsimp only [Model.allowedHostCapsStep] at h
  cases hr : (caps.files.dupStdio slot).run.run w with
  | mk res w1 =>
    rw [hr] at h
    cases hf : (proj w).fault <;> simp only [hf] at h ⊢
    · rcases h with ⟨fd, hOut, hSt⟩
      cases res with
      | error _ => simp [Except.map] at hOut
      | ok _ =>
        simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.opened.injEq] at hOut
        exact ⟨fd, congrArg Except.ok hOut, hSt⟩
    · cases res with
      | error _ => simp [Except.map] at h
      | ok _ =>
        simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.opened.injEq] at h
        exact ⟨congrArg Except.ok h.1, h.2⟩
    · rcases h with ⟨fd, hOut, hSt⟩
      cases res with
      | error _ => simp [Except.map] at hOut
      | ok _ =>
        simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.opened.injEq] at hOut
        exact ⟨fd, congrArg Except.ok hOut, hSt⟩
    · rcases h with ⟨fd, hOut, hSt⟩
      cases res with
      | error _ => simp [Except.map] at hOut
      | ok _ =>
        simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.opened.injEq] at hOut
        exact ⟨fd, congrArg Except.ok hOut, hSt⟩

theorem caps_close_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (fd : RawFd) (slot : Files.StdioFd) (rest : List Files.StdioFd) (w : W)
    (hOpen : (proj w).openDups = slot :: rest) :
    ((caps.files.close fd).run.run w).1 = .ok (.ok ()) ∧
      proj ((caps.files.close fd).run.run w).2 = { proj w with openDups := rest } := by
  have h := hCaps w (.close fd) rfl
  dsimp only [Model.execCapsStep] at h
  rw [exceptT_run_map] at h
  dsimp only [Model.allowedHostCapsStep] at h
  rw [hOpen] at h
  cases hr : (caps.files.close fd).run.run w with
  | mk res w1 =>
    rw [hr] at h
    cases res with
    | error _ => simp [Except.map] at h
    | ok _ =>
      simp only [Except.map, Except.ok.injEq, Model.CmdLineCapsOut.closed.injEq] at h
      exact ⟨congrArg Except.ok h.1, h.2⟩

theorem caps_read1_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (fd : RawFd) (restDups : List Files.StdioFd) (w : W)
    (hOpen : (proj w).openDups = .stdin :: restDups) :
    match (proj w).fault with
    | .ioThrow msg =>
      ((caps.files.read fd 1).run.run w).1 = .error (IO.userError msg) ∧
        proj ((caps.files.read fd 1).run.run w).2 = proj w
    | .ioErrno code =>
      ((caps.files.read fd 1).run.run w).1 = .ok (.error code) ∧
        proj ((caps.files.read fd 1).run.run w).2 = proj w
    | .none | .dupErrno _ =>
      if (proj w).eintrCount > 0 then
        ((caps.files.read fd 1).run.run w).1 = .ok (.error Errno.EINTR) ∧
          proj ((caps.files.read fd 1).run.run w).2 = { proj w with eintrCount := (proj w).eintrCount - 1 }
      else
        match (proj w).stdinBytes with
        | [] =>
          ((caps.files.read fd 1).run.run w).1 = .ok (.ok ByteArray.empty) ∧
            proj ((caps.files.read fd 1).run.run w).2 = proj w
        | b :: rest =>
          ((caps.files.read fd 1).run.run w).1 = .ok (.ok (ByteArray.mk #[b])) ∧
            proj ((caps.files.read fd 1).run.run w).2 = { proj w with stdinBytes := rest } := by
  have h := hCaps w (.read fd 1) rfl
  dsimp only [Model.execCapsStep] at h
  rw [exceptT_run_map] at h
  dsimp only [Model.allowedHostCapsStep] at h
  rw [hOpen] at h
  have h10 : ((1 : UInt32) == 0) = false := rfl
  cases hr : (caps.files.read fd 1).run.run w with
  | mk res w1 =>
    rw [hr] at h
    cases hf : (proj w).fault <;> simp only [hf] at h ⊢
    · by_cases he : (proj w).eintrCount > 0
      · simp only [he, ↓reduceIte] at h ⊢; cases res <;> simp_all [Except.map]
      · simp only [he, ↓reduceIte, h10, Bool.false_eq_true] at h ⊢
        cases hb : (proj w).stdinBytes <;> simp only [hb] at h ⊢ <;> (cases res <;> simp_all [Except.map])
    · by_cases he : (proj w).eintrCount > 0
      · simp only [he, ↓reduceIte] at h ⊢; cases res <;> simp_all [Except.map]
      · simp only [he, ↓reduceIte, h10, Bool.false_eq_true] at h ⊢
        cases hb : (proj w).stdinBytes <;> simp only [hb] at h ⊢ <;> (cases res <;> simp_all [Except.map])
    · cases res <;> simp_all [Except.map]
    · cases res <;> simp_all [Except.map]

theorem caps_write_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (isStdout : Bool) (fd : RawFd) (slice : ByteArray) (restDups : List Files.StdioFd) (w : W)
    (hOpen : (proj w).openDups = (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: restDups) :
    match (proj w).fault with
    | .ioThrow msg =>
      ((caps.files.write fd slice).run.run w).1 = .error (IO.userError msg) ∧
        proj ((caps.files.write fd slice).run.run w).2 = proj w
    | .ioErrno code =>
      ((caps.files.write fd slice).run.run w).1 = .ok (.error code) ∧
        proj ((caps.files.write fd slice).run.run w).2 = proj w
    | .none | .dupErrno _ =>
      if (proj w).eintrCount > 0 then
        ((caps.files.write fd slice).run.run w).1 = .ok (.error Errno.EINTR) ∧
          proj ((caps.files.write fd slice).run.run w).2 = { proj w with eintrCount := (proj w).eintrCount - 1 }
      else
        let k := min slice.size 1048576
        ((caps.files.write fd slice).run.run w).1 = .ok (.ok (UInt32.ofNat k)) ∧
          proj ((caps.files.write fd slice).run.run w).2 =
            if isStdout then { proj w with stdoutBytes := (proj w).stdoutBytes ++ slice.extract 0 k }
            else { proj w with stderrBytes := (proj w).stderrBytes ++ slice.extract 0 k } := by
  have h := hCaps w (.write fd slice) rfl
  dsimp only [Model.execCapsStep] at h
  rw [exceptT_run_map] at h
  dsimp only [Model.allowedHostCapsStep] at h
  rw [hOpen] at h
  cases hr : (caps.files.write fd slice).run.run w with
  | mk res w1 =>
    rw [hr] at h
    cases isStdout <;> dsimp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
      (cases hf : (proj w).fault <;> simp only [hf] at h ⊢ <;>
        first
        | (cases res <;> simp_all [Except.map])
        | (by_cases he : (proj w).eintrCount > 0 <;>
            simp only [he, ↓reduceIte] at h ⊢ <;>
            (cases res <;> simp_all [Except.map])))

theorem retryEintr_const_errno {W α : Type} (proj : W → Model.CmdLineHostState)
    (act : ExceptT IO.Error (StateM W) (Except Errno α))
    (code : Errno) (s0 : Model.CmdLineHostState)
    (hAct : ∀ w, proj w = s0 → (act.run.run w).1 = .ok (.error code) ∧ proj (act.run.run w).2 = s0) :
    ∀ (fuel : Nat) (w : W), proj w = s0 →
      ((retryEintr act fuel).run.run w).1 = .ok (.error code) ∧ proj ((retryEintr act fuel).run.run w).2 = s0
  | 0, w, hw => hAct w hw
  | fuel + 1, w, hw => by
    unfold retryEintr
    rw [exceptT_run_bind]
    have h1 := hAct w hw
    cases hr : act.run.run w with
    | mk res w1 =>
      rw [hr] at h1
      rcases h1 with ⟨rfl, hw1⟩
      dsimp only
      by_cases he : (code == Errno.EINTR) = true
      · simp only [he, ↓reduceIte]
        exact retryEintr_const_errno proj act code s0 hAct fuel w1 hw1
      · simp only [he, Bool.false_eq_true, ↓reduceIte, exceptT_run_pure]
        exact ⟨trivial, hw1⟩

theorem retryEintr_countdown {W α : Type} (proj : W → Model.CmdLineHostState)
    (act : ExceptT IO.Error (StateM W) (Except Errno α))
    (base : Model.CmdLineHostState) (hBase0 : base.eintrCount = 0)
    (zeroVal : α) (sNext : Model.CmdLineHostState)
    (hPos : ∀ w k, proj w = { base with eintrCount := k + 1 } →
      (act.run.run w).1 = .ok (.error Errno.EINTR) ∧ proj (act.run.run w).2 = { base with eintrCount := k })
    (hZero : ∀ w, proj w = base →
      (act.run.run w).1 = .ok (.ok zeroVal) ∧ proj (act.run.run w).2 = sNext) :
    ∀ (fuel k : Nat) (w : W), proj w = { base with eintrCount := k } →
      (((retryEintr act fuel).run.run w).1, proj ((retryEintr act fuel).run.run w).2) =
        if k > fuel then (.ok (.error Errno.EINTR), { base with eintrCount := k - (fuel + 1) })
        else (.ok (.ok zeroVal), sNext)
  | 0, 0, w, hw => by
    have hb : { base with eintrCount := 0 } = base := by
      cases base; simp only at hBase0; subst hBase0; rfl
    rw [hb] at hw
    have h0 := hZero w hw
    have hgt : ¬(0 > 0) := by omega
    simp only [retryEintr, hgt, ↓reduceIte]
    exact Prod.ext h0.1 h0.2
  | 0, k + 1, w, hw => by
    have h1 := hPos w k hw
    have hgt : k + 1 > 0 := by omega
    simp only [retryEintr, hgt, ↓reduceIte, Nat.zero_add, Nat.add_sub_cancel]
    exact Prod.ext h1.1 h1.2
  | fuel + 1, 0, w, hw => by
    have hb : { base with eintrCount := 0 } = base := by
      cases base; simp only at hBase0; subst hBase0; rfl
    rw [hb] at hw
    unfold retryEintr
    rw [exceptT_run_bind]
    have h0 := hZero w hw
    cases hr : act.run.run w with
    | mk res w1 =>
      rw [hr] at h0
      rcases h0 with ⟨rfl, hw1⟩
      have hgt : ¬(0 > fuel + 1) := by omega
      simp only [hgt, ↓reduceIte, exceptT_run_pure]
      exact Prod.ext rfl hw1
  | fuel + 1, k + 1, w, hw => by
    unfold retryEintr
    rw [exceptT_run_bind]
    have h1 := hPos w k hw
    cases hr : act.run.run w with
    | mk res w1 =>
      rw [hr] at h1
      rcases h1 with ⟨rfl, hw1⟩
      have heq : (Errno.EINTR == Errno.EINTR) = true := rfl
      simp only [heq, ↓reduceIte]
      have ih := retryEintr_countdown proj act base hBase0 zeroVal sNext hPos hZero fuel k w1 hw1
      rw [ih]
      by_cases hk : k > fuel
      · have hk1 : k + 1 > fuel + 1 := by omega
        have hsub : k + 1 - (fuel + 1 + 1) = k - (fuel + 1) := by omega
        simp [hk, hk1, hsub]
      · have hk1 : ¬(k + 1 > fuel + 1) := by omega
        simp [hk, hk1]

theorem readStdioLineFdLoop_zero_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (fd : RawFd) (restDups : List Files.StdioFd) :
    ∀ (fuel : Nat) (acc : ByteArray) (w : W),
      (proj w).openDups = .stdin :: restDups →
      (proj w).fault = .none →
      (proj w).eintrCount = 0 →
      ((SysBridge.readStdioLineFdLoop caps.files fd acc fuel).run.run w).1 =
          .ok (Model.stepHostReadLoop acc fuel (proj w).stdinBytes).1 ∧
        proj ((SysBridge.readStdioLineFdLoop caps.files fd acc fuel).run.run w).2 =
          { proj w with stdinBytes := (Model.stepHostReadLoop acc fuel (proj w).stdinBytes).2 }
  | 0, acc, w, _, _, _ => by
    unfold SysBridge.readStdioLineFdLoop Model.stepHostReadLoop
    rw [exceptT_run_pure]
    exact ⟨rfl, by cases proj w; rfl⟩
  | fuel + 1, acc, w, hOpen, hFault, hE0 => by
    unfold SysBridge.readStdioLineFdLoop
    rw [exceptT_run_bind]
    cases hBytes : (proj w).stdinBytes with
    | nil =>
      have hRe := retryEintr_countdown proj (caps.files.read fd 1) (proj w) hE0 ByteArray.empty (proj w)
        (fun w0 k hw0 => by
          have hr := caps_read1_spec proj caps hCaps fd restDups w0 (by rw [hw0]; exact hOpen)
          rw [hw0] at hr; simp only [hFault, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hr
          exact ⟨hr.1, hr.2.trans (by cases hp : proj w; simp_all)⟩)
        (fun w0 hw0 => by
          have hr := caps_read1_spec proj caps hCaps fd restDups w0 (by rw [hw0]; exact hOpen)
          rw [hw0] at hr
          have hNotPos : ¬(0 > 0) := by omega
          simp only [hFault, hE0, hNotPos, ↓reduceIte, hBytes] at hr
          exact ⟨hr.1, hr.2.trans (by cases hp : proj w; simp_all)⟩)
        SysBridge.stdioEintrFuel 0 w (by cases hp : proj w; simp_all)
      cases hAct : (retryEintr (caps.files.read fd 1) SysBridge.stdioEintrFuel).run.run w with
      | mk res w1 =>
        rw [hAct] at hRe
        have hgt : ¬(0 > SysBridge.stdioEintrFuel) := by omega
        simp only [hgt, ↓reduceIte, Prod.mk.injEq] at hRe
        rcases hRe with ⟨rfl, hw1⟩
        have hSz : ¬(0 < ByteArray.empty.size) := by decide
        unfold Model.stepHostReadLoop
        simp only [hSz, ↓reduceDIte, exceptT_run_pure]
        exact ⟨trivial, by rw [hw1]; cases hp : proj w; simp_all⟩
    | cons b rest =>
      have hRe := retryEintr_countdown proj (caps.files.read fd 1) (proj w) hE0
        (ByteArray.mk #[b]) { proj w with stdinBytes := rest }
        (fun w0 k hw0 => by
          have hr := caps_read1_spec proj caps hCaps fd restDups w0 (by rw [hw0]; exact hOpen)
          rw [hw0] at hr; simp only [hFault, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hr
          exact ⟨hr.1, hr.2.trans (by cases hp : proj w; simp_all)⟩)
        (fun w0 hw0 => by
          have hr := caps_read1_spec proj caps hCaps fd restDups w0 (by rw [hw0]; exact hOpen)
          rw [hw0] at hr
          have hNotPos : ¬(0 > 0) := by omega
          simp only [hFault, hE0, hNotPos, ↓reduceIte, hBytes] at hr
          exact ⟨hr.1, hr.2.trans (by cases hp : proj w; simp_all)⟩)
        SysBridge.stdioEintrFuel 0 w (by cases hp : proj w; simp_all)
      cases hAct : (retryEintr (caps.files.read fd 1) SysBridge.stdioEintrFuel).run.run w with
      | mk res w1 =>
        rw [hAct] at hRe
        have hgt : ¬(0 > SysBridge.stdioEintrFuel) := by omega
        simp only [hgt, ↓reduceIte, Prod.mk.injEq] at hRe
        rcases hRe with ⟨rfl, hw1⟩
        have hSz : 0 < (ByteArray.mk #[b]).size := by show 0 < #[b].size; simp
        have hGet : (ByteArray.mk #[b])[0]'hSz = b := rfl
        unfold Model.stepHostReadLoop
        simp only [hSz, ↓reduceDIte, hGet]
        by_cases hb : (b == (0x0A : UInt8)) = true
        · simp only [hb, ↓reduceIte, exceptT_run_pure]
          exact ⟨trivial, hw1⟩
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          have ih := readStdioLineFdLoop_zero_spec proj caps hCaps fd restDups fuel (acc.push b) w1
            (by rw [hw1]; exact hOpen) (by rw [hw1]; exact hFault) (by rw [hw1]; exact hE0)
          rw [show (proj w1).stdinBytes = rest from by rw [hw1]] at ih
          exact ⟨ih.1, ih.2.trans (by rw [hw1])⟩

theorem writeStdioSlicesLoop_zero_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (isStdout : Bool) (fd : RawFd) (bs : ByteArray) (restDups : List Files.StdioFd) :
    ∀ (fuel off : Nat) (w : W),
      off ≤ bs.size →
      bs.size - off ≤ fuel →
      (proj w).openDups = (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: restDups →
      (proj w).fault = .none →
      (proj w).eintrCount = 0 →
      ((SysBridge.writeStdioSlicesLoop caps.files fd bs off fuel).run.run w).1 = .ok (.ok ()) ∧
        proj ((SysBridge.writeStdioSlicesLoop caps.files fd bs off fuel).run.run w).2 =
          if isStdout then { proj w with stdoutBytes := (proj w).stdoutBytes ++ bs.extract off bs.size }
          else { proj w with stderrBytes := (proj w).stderrBytes ++ bs.extract off bs.size }
  | 0, off, w, hLe, hRem, _, _, _ => by
    have hEq : off = bs.size := by omega
    subst hEq
    unfold SysBridge.writeStdioSlicesLoop
    have hGe : bs.size ≥ bs.size := Nat.le_refl _
    simp only [hGe, ↓reduceIte, exceptT_run_pure, byteArray_extract_self_empty, byteArray_append_empty]
    cases isStdout <;> exact ⟨trivial, by cases proj w; rfl⟩
  | fuel + 1, off, w, hLe, hRem, hOpen, hFault, hE0 => by
    unfold SysBridge.writeStdioSlicesLoop
    by_cases hGe : off ≥ bs.size
    · have hEq : off = bs.size := by omega
      subst hEq
      have hRefl : bs.size ≥ bs.size := Nat.le_refl _
      simp only [hRefl, ↓reduceIte, exceptT_run_pure, byteArray_extract_self_empty, byteArray_append_empty]
      cases isStdout <;> exact ⟨trivial, by cases proj w; rfl⟩
    · simp only [hGe, ↓reduceIte]
      have hEndLe : min bs.size (off + 1048576) ≤ bs.size := Nat.min_le_left _ _
      have hOffLeEnd : off ≤ min bs.size (off + 1048576) := by omega
      have hSliceEq :
          (if off == 0 && min bs.size (off + 1048576) == bs.size then bs
           else bs.extract off (min bs.size (off + 1048576))) =
            bs.extract off (min bs.size (off + 1048576)) := by
        by_cases hc : (off == 0 && min bs.size (off + 1048576) == bs.size) = true
        · simp only [hc, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rw [hc.2, hc.1, byteArray_extract_zero_size]
        · simp [hc]
      rw [hSliceEq, exceptT_run_bind]
      have hSliceSz : (bs.extract off (min bs.size (off + 1048576))).size = min bs.size (off + 1048576) - off :=
        byteArray_extract_size bs hOffLeEnd hEndLe
      have hSlicePos : 0 < (bs.extract off (min bs.size (off + 1048576))).size := by rw [hSliceSz]; omega
      have hSliceCap : (bs.extract off (min bs.size (off + 1048576))).size ≤ 1048576 := by rw [hSliceSz]; omega
      have hMinSlice : min (bs.extract off (min bs.size (off + 1048576))).size 1048576 =
          (bs.extract off (min bs.size (off + 1048576))).size := Nat.min_eq_left hSliceCap
      have hSliceExt :
          (bs.extract off (min bs.size (off + 1048576))).extract 0
            (min (bs.extract off (min bs.size (off + 1048576))).size 1048576) =
            bs.extract off (min bs.size (off + 1048576)) := by
        rw [hMinSlice, byteArray_extract_zero_size]
      have hRe := retryEintr_countdown proj
        (caps.files.write fd (bs.extract off (min bs.size (off + 1048576))))
        (proj w) hE0
        (UInt32.ofNat (bs.extract off (min bs.size (off + 1048576))).size)
        (if isStdout then { proj w with stdoutBytes := (proj w).stdoutBytes ++ bs.extract off (min bs.size (off + 1048576)) }
         else { proj w with stderrBytes := (proj w).stderrBytes ++ bs.extract off (min bs.size (off + 1048576)) })
        (fun w0 k hw0 => by
          have hw := caps_write_spec proj caps hCaps isStdout fd (bs.extract off (min bs.size (off + 1048576))) restDups w0
            (by rw [hw0]; exact hOpen)
          rw [hw0] at hw; simp only [hFault, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hw
          exact ⟨hw.1, hw.2.trans (by cases hp : proj w; simp_all)⟩)
        (fun w0 hw0 => by
          have hw := caps_write_spec proj caps hCaps isStdout fd (bs.extract off (min bs.size (off + 1048576))) restDups w0
            (by rw [hw0]; exact hOpen)
          rw [hw0] at hw
          have hNotPos : ¬(0 > 0) := by omega
          simp only [hFault, hE0, hNotPos, ↓reduceIte] at hw
          rw [hSliceExt, hMinSlice] at hw
          refine ⟨hw.1, hw.2.trans ?_⟩
          cases isStdout <;> (cases hp : proj w; simp_all))
        SysBridge.stdioEintrFuel 0 w (by cases hp : proj w; simp_all)
      cases hAct : (retryEintr (caps.files.write fd (bs.extract off (min bs.size (off + 1048576)))) SysBridge.stdioEintrFuel).run.run w with
      | mk res w1 =>
        rw [hAct] at hRe
        have hgt : ¬(0 > SysBridge.stdioEintrFuel) := by omega
        simp only [hgt, ↓reduceIte, Prod.mk.injEq] at hRe
        rcases hRe with ⟨rfl, hw1⟩
        have hMod : (bs.extract off (min bs.size (off + 1048576))).size < UInt32.size := by
          have : UInt32.size = 4294967296 := rfl
          omega
        have hToNat : (UInt32.ofNat (bs.extract off (min bs.size (off + 1048576))).size).toNat =
            (bs.extract off (min bs.size (off + 1048576))).size := UInt32.toNat_ofNat_of_lt hMod
        have hNe0 : (UInt32.ofNat (bs.extract off (min bs.size (off + 1048576))).size == 0) = false := by
          apply beq_false_of_ne
          intro hEq
          have hc := congrArg UInt32.toNat hEq
          rw [hToNat] at hc
          change (bs.extract off (min bs.size (off + 1048576))).size = 0 at hc
          omega
        dsimp only
        simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hToNat]
        have hNextOff : off + (bs.extract off (min bs.size (off + 1048576))).size = min bs.size (off + 1048576) := by
          rw [hSliceSz]; omega
        rw [hNextOff]
        have hRem' : bs.size - min bs.size (off + 1048576) ≤ fuel := by omega
        have ih := writeStdioSlicesLoop_zero_spec proj caps hCaps isStdout fd bs restDups
          fuel (min bs.size (off + 1048576)) w1 hEndLe hRem'
          (by rw [hw1]; cases isStdout <;> exact hOpen)
          (by rw [hw1]; cases isStdout <;> exact hFault)
          (by rw [hw1]; cases isStdout <;> exact hE0)
        refine ⟨ih.1, ih.2.trans ?_⟩
        rw [hw1]
        cases isStdout <;>
          simp only [↓reduceIte, Bool.false_eq_true, byteArray_append_assoc,
            byteArray_extract_append bs hOffLeEnd hEndLe]

end LeanSwe.CmdLine.Proofs
