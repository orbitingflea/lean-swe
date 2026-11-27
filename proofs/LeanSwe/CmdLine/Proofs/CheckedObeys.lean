import Core.Obeys
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.Proofs.HostBase

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.LinuxSyscall

private theorem hostState_ext {a b : Model.CmdLineHostState}
    (h1 : a.env = b.env) (h2 : a.stdinBytes = b.stdinBytes)
    (h3 : a.stdoutBytes = b.stdoutBytes) (h4 : a.stderrBytes = b.stderrBytes)
    (h5 : a.openDups = b.openDups) (h6 : a.eintrCount = b.eintrCount)
    (h7 : a.fault = b.fault) : a = b := by
  cases a; cases b
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- Exact single-step specification of `(Internal.mkCliOpsFromCapsM caps).readLine` over `ExceptT IO.Error (StateM W)`. -/
theorem mkCliOps_readLine_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (w : W) :
    (((Internal.mkCliOpsFromCapsM caps).readLine).run.run w).1 = (Model.stepHostReadLine (proj w)).1 ∧
      proj (((Internal.mkCliOpsFromCapsM caps).readLine).run.run w).2 = (Model.stepHostReadLine (proj w)).2 := by
  unfold Internal.mkCliOpsFromCapsM SysBridge.mkFilesCliOpsM SysBridge.readStdioLineM Model.stepHostReadLine
  dsimp only
  rw [exceptT_run_bind, exceptT_run_bind]
  have hDup := caps_dupStdio_spec proj caps hCaps .stdin w
  cases hd : (caps.files.dupStdio .stdin).run.run w with
  | mk dupRes w1 =>
    rw [hd] at hDup
    cases hf : (proj w).fault with
    | none =>
      simp only [hf] at hDup ⊢
      rcases hDup with ⟨fd, rfl, hw1⟩
      dsimp only at hw1 ⊢
      rw [exceptT_run_bind, exceptT_run_tryFinally]
      unfold SysBridge.readStdioLineFdLoop
      rw [exceptT_run_bind]
      have hBase0 : ({ proj w with openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 } : Model.CmdLineHostState).eintrCount = 0 := rfl
      have hW1Eq : proj w1 = { ({ proj w with openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 } : Model.CmdLineHostState) with eintrCount := (proj w).eintrCount } := by
        rw [hw1]; apply hostState_ext <;> first | rfl | exact hf.symm
      cases hBytes : (proj w).stdinBytes with
      | nil =>
        have hRe := retryEintr_countdown proj (caps.files.read fd 1)
          { proj w with openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 } hBase0
          ByteArray.empty { proj w with openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 }
          (fun w0 k hw0 => by
            have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hr; simp only [hf, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hr
            exact ⟨hr.1, hr.2.trans (by apply hostState_ext <;> first | rfl | exact hf.symm)⟩)
          (fun w0 hw0 => by
            have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hr
            have hNotPos : ¬(0 > 0) := by omega
            simp only [hf, hNotPos, ↓reduceIte, hBytes] at hr
            exact ⟨hr.1, hr.2.trans (by apply hostState_ext <;> first | rfl | exact hf.symm | exact hBytes.symm)⟩)
          SysBridge.stdioEintrFuel (proj w).eintrCount w1 hW1Eq
        rw [show SysBridge.stdioEintrFuel = Model.stdioEintrRetryLimit from rfl] at hRe ⊢
        cases hAct : (retryEintr (caps.files.read fd 1) Model.stdioEintrRetryLimit).run.run w1 with
        | mk res w2 =>
          rw [hAct] at hRe
          by_cases hGt : (proj w).eintrCount > Model.stdioEintrRetryLimit
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            dsimp only [exceptT_run_pure]
            have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2])
            cases hc : (caps.files.close fd).run.run w2 with
            | mk clRes w3 =>
              rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
              dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
              refine ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm | exact hBytes | exact hBytes.symm⟩
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            have hSz : ¬(0 < ByteArray.empty.size) := by decide
            simp only [hSz, ↓reduceDIte, exceptT_run_pure]
            have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2])
            cases hc : (caps.files.close fd).run.run w2 with
            | mk clRes w3 =>
              rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩; dsimp only at hw3
              have hEmp : ByteArray.empty.isEmpty = true := rfl
              unfold Model.stepHostReadLoop; simp only [hEmp, ↓reduceIte]; dsimp only [exceptT_run_pure]
              refine ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm | exact hBytes | exact hBytes.symm⟩
      | cons b rest =>
        have hRe := retryEintr_countdown proj (caps.files.read fd 1)
          { proj w with openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 } hBase0
          (ByteArray.mk #[b])
          { proj w with stdinBytes := rest, openDups := Files.StdioFd.stdin :: (proj w).openDups, eintrCount := 0 }
          (fun w0 k hw0 => by
            have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hr; simp only [hf, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hr
            exact ⟨hr.1, hr.2.trans (by apply hostState_ext <;> first | rfl | exact hf.symm)⟩)
          (fun w0 hw0 => by
            have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hr
            have hNotPos : ¬(0 > 0) := by omega
            simp only [hf, hNotPos, ↓reduceIte, hBytes] at hr
            exact ⟨hr.1, hr.2.trans (by apply hostState_ext <;> first | rfl | exact hf.symm)⟩)
          SysBridge.stdioEintrFuel (proj w).eintrCount w1 hW1Eq
        rw [show SysBridge.stdioEintrFuel = Model.stdioEintrRetryLimit from rfl] at hRe ⊢
        cases hAct : (retryEintr (caps.files.read fd 1) Model.stdioEintrRetryLimit).run.run w1 with
        | mk res w2 =>
          rw [hAct] at hRe
          by_cases hGt : (proj w).eintrCount > Model.stdioEintrRetryLimit
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            dsimp only [exceptT_run_pure]
            have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2])
            cases hc : (caps.files.close fd).run.run w2 with
            | mk clRes w3 =>
              rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
              dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
              refine ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm | exact hBytes | exact hBytes.symm⟩
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            have hSz : 0 < (ByteArray.mk #[b]).size := by show 0 < #[b].size; simp
            have hGet : (ByteArray.mk #[b])[0]'hSz = b := rfl
            unfold Model.stepHostReadLoop
            simp only [hSz, ↓reduceDIte, hGet]
            by_cases hb : (b == (0x0A : UInt8)) = true
            · simp only [hb, ↓reduceIte, exceptT_run_pure]
              have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2])
              cases hc : (caps.files.close fd).run.run w2 with
              | mk clRes w3 =>
                rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩; dsimp only at hw3 ⊢
                cases (ByteArray.empty.push b).isEmpty
                · simp only [Bool.false_eq_true, ↓reduceIte, sysBridge_decodeUtf8LossyLean_eq]; dsimp only [exceptT_run_pure]
                  exact ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
                · simp only [↓reduceIte]; dsimp only [exceptT_run_pure]
                  exact ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
            · simp only [hb, Bool.false_eq_true, ↓reduceIte]
              have hLoop := readStdioLineFdLoop_zero_spec proj caps hCaps fd (proj w).openDups
                67108863 (ByteArray.empty.push b) w2
                (by rw [hw2]) (by rw [hw2]; exact hf) (by rw [hw2])
              rw [show (proj w2).stdinBytes = rest from by rw [hw2]] at hLoop
              cases hStep : Model.stepHostReadLoop (ByteArray.empty.push b) 67108863 rest with
              | mk stepRes rem =>
                rw [hStep] at hLoop
                cases hRun : (SysBridge.readStdioLineFdLoop caps.files fd (ByteArray.empty.push b) 67108863).run.run w2 with
                | mk loopOut w3 =>
                  rw [hRun] at hLoop; rcases hLoop with ⟨rfl, hw3⟩; dsimp only at hw3 ⊢
                  have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w3 (by rw [hw3, hw2])
                  cases hc : (caps.files.close fd).run.run w3 with
                  | mk clRes w4 =>
                    rw [hc] at hCl; rcases hCl with ⟨rfl, hw4⟩; dsimp only at hw4 ⊢
                    cases stepRes with
                    | error e =>
                      dsimp only [exceptT_run_pure, exceptT_run_throw]
                      exact ⟨rfl, by rw [hw4, hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
                    | ok lineBs =>
                      dsimp only
                      cases lineBs.isEmpty
                      · simp only [Bool.false_eq_true, ↓reduceIte, sysBridge_decodeUtf8LossyLean_eq]; dsimp only [exceptT_run_pure]
                        exact ⟨rfl, by rw [hw4, hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
                      · simp only [↓reduceIte]; dsimp only [exceptT_run_pure]
                        exact ⟨rfl, by rw [hw4, hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
    | dupErrno code =>
      simp only [hf] at hDup ⊢
      rcases hDup with ⟨rfl, hw1⟩
      dsimp only [exceptT_run_pure, exceptT_run_throw] at hw1 ⊢
      exact ⟨rfl, hw1⟩
    | ioErrno code =>
      simp only [hf] at hDup ⊢
      rcases hDup with ⟨fd, rfl, hw1⟩
      dsimp only at hw1 ⊢
      rw [exceptT_run_bind, exceptT_run_tryFinally]
      unfold SysBridge.readStdioLineFdLoop
      rw [exceptT_run_bind]
      have hRe := retryEintr_const_errno proj (caps.files.read fd 1) code (proj w1)
        (fun w0 hw0 => by
          have hf0 : (proj w0).fault = .ioErrno code := by rw [hw0, hw1]
          have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w0 (by rw [hw0, hw1])
          rw [hf0] at hr; dsimp only at hr
          exact ⟨hr.1, hr.2.trans hw0⟩)
        SysBridge.stdioEintrFuel w1 rfl
      cases hAct : (retryEintr (caps.files.read fd 1) SysBridge.stdioEintrFuel).run.run w1 with
      | mk res w2 =>
        rw [hAct] at hRe; rcases hRe with ⟨rfl, hw2⟩
        dsimp only [exceptT_run_pure] at hw2 ⊢
        have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2, hw1])
        cases hc : (caps.files.close fd).run.run w2 with
        | mk clRes w3 =>
          rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
          dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
          exact ⟨rfl, by rw [hw3, hw2, hw1]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
    | ioThrow msg =>
      simp only [hf] at hDup ⊢
      rcases hDup with ⟨fd, rfl, hw1⟩
      dsimp only at hw1 ⊢
      rw [exceptT_run_bind, exceptT_run_tryFinally]
      unfold SysBridge.readStdioLineFdLoop SysBridge.stdioEintrFuel retryEintr
      rw [exceptT_run_bind, exceptT_run_bind]
      have hr := caps_read1_spec proj caps hCaps fd (proj w).openDups w1 (by rw [hw1])
      rw [hw1] at hr; dsimp only at hr
      cases hRd : (caps.files.read fd 1).run.run w1 with
      | mk rdRes w2 =>
        rw [hRd] at hr; rcases hr with ⟨rfl, hw2⟩; dsimp only at hw2 ⊢
        have hCl := caps_close_spec proj caps hCaps fd .stdin (proj w).openDups w2 (by rw [hw2])
        cases hc : (caps.files.close fd).run.run w2 with
        | mk clRes w3 =>
          rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
          dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
          exact ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩

/-- Exact single-step specification of `writeOut` (`isStdout = true`) and `writeErr` (`false`) over `ExceptT IO.Error (StateM W)`. -/
theorem mkCliOps_writeSlot_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (isStdout : Bool) (text : String) (w : W) :
    ((if isStdout then (Internal.mkCliOpsFromCapsM caps).writeOut text
      else (Internal.mkCliOpsFromCapsM caps).writeErr text).run.run w).1 =
        (Model.stepHostWriteSlot isStdout (proj w) text).1 ∧
      proj ((if isStdout then (Internal.mkCliOpsFromCapsM caps).writeOut text
             else (Internal.mkCliOpsFromCapsM caps).writeErr text).run.run w).2 =
        (Model.stepHostWriteSlot isStdout (proj w) text).2 := by
  have hUnify :
      (if isStdout then (Internal.mkCliOpsFromCapsM caps).writeOut text
       else (Internal.mkCliOpsFromCapsM caps).writeErr text) =
      (do
        match ← SysBridge.writeStdioSlotM caps.files (if isStdout then .stdout else .stderr) text with
        | .error e => throwThe IO.Error (SysBridge.errnoToIoError e)
        | .ok () => return ()) := by
    cases isStdout <;> rfl
  rw [hUnify]
  unfold SysBridge.writeStdioSlotM Model.stepHostWriteSlot
  by_cases hEmp : text.isEmpty = true
  · simp only [hEmp, ↓reduceIte, exceptT_run_bind, exceptT_run_pure]
    exact ⟨trivial, trivial⟩
  · simp only [hEmp, Bool.false_eq_true, ↓reduceIte]
    have hEmpF : text.isEmpty = false := Bool.eq_false_iff.mpr hEmp
    have hPos : 0 < text.toUTF8.size := string_nonEmpty_utf8_pos hEmpF
    rw [exceptT_run_bind, exceptT_run_bind]
    have hDup := caps_dupStdio_spec proj caps hCaps (if isStdout then .stdout else .stderr) w
    cases hd : (caps.files.dupStdio (if isStdout then .stdout else .stderr)).run.run w with
    | mk dupRes w1 =>
      rw [hd] at hDup
      cases hf : (proj w).fault with
      | none =>
        simp only [hf] at hDup ⊢
        rcases hDup with ⟨fd, rfl, hw1⟩
        dsimp only at hw1 ⊢
        rw [exceptT_run_bind, exceptT_run_tryFinally]
        have hBsFuel : text.toUTF8.size = (text.toUTF8.size - 1) + 1 := by omega
        have hLoopUnfold :
            SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 text.toUTF8.size =
              SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 ((text.toUTF8.size - 1) + 1) := by
          rw [← hBsFuel]
        rw [hLoopUnfold]
        unfold SysBridge.writeStdioSlicesLoop
        have hNotGe : ¬(0 ≥ text.toUTF8.size) := by omega
        simp only [hNotGe, ↓reduceIte]
        have hEndLe : min text.toUTF8.size (0 + 1048576) ≤ text.toUTF8.size := Nat.min_le_left _ _
        have hSliceEq :
            (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8
             else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))) =
              text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)) := by
          by_cases hc : ((0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size) = true
          · simp only [hc, ↓reduceIte]; simp only [Bool.and_eq_true, beq_iff_eq] at hc
            rw [hc.2, byteArray_extract_zero_size]
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rw [hSliceEq, exceptT_run_bind]
        have hSliceSz : (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size =
            min text.toUTF8.size (0 + 1048576) := by
          have hs := byteArray_extract_size text.toUTF8 (Nat.zero_le _) hEndLe; omega
        have hSlicePos : 0 < (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size := by
          rw [hSliceSz]; omega
        have hSliceCap : (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size ≤ 1048576 := by
          rw [hSliceSz]; omega
        have hMinSlice : min (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size 1048576 =
            (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size := Nat.min_eq_left hSliceCap
        have hSliceExt :
            (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).extract 0
              (min (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size 1048576) =
              text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)) := by
          rw [hMinSlice, byteArray_extract_zero_size]
        have hBase0 :
            ({ proj w with openDups := (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: (proj w).openDups, eintrCount := 0 } :
              Model.CmdLineHostState).eintrCount = 0 := rfl
        have hW1Eq :
            proj w1 =
              { ({ proj w with openDups := (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: (proj w).openDups, eintrCount := 0 } :
                  Model.CmdLineHostState) with eintrCount := (proj w).eintrCount } := by
          rw [hw1]; apply hostState_ext <;> first | rfl | exact hf.symm
        have hRe := retryEintr_countdown proj
          (caps.files.write fd (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))))
          { proj w with openDups := (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: (proj w).openDups, eintrCount := 0 }
          hBase0
          (UInt32.ofNat (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size)
          (if isStdout then
            { proj w with
              stdoutBytes := (proj w).stdoutBytes ++ text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)),
              openDups := (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: (proj w).openDups,
              eintrCount := 0 }
           else
            { proj w with
              stderrBytes := (proj w).stderrBytes ++ text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)),
              openDups := (if isStdout then Files.StdioFd.stdout else Files.StdioFd.stderr) :: (proj w).openDups,
              eintrCount := 0 })
          (fun w0 k hw0 => by
            have hw := caps_write_spec proj caps hCaps isStdout fd
              (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))) (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hw; simp only [hf, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at hw
            exact ⟨hw.1, hw.2.trans (by apply hostState_ext <;> first | rfl | exact hf.symm)⟩)
          (fun w0 hw0 => by
            have hw := caps_write_spec proj caps hCaps isStdout fd
              (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))) (proj w).openDups w0 (by rw [hw0])
            rw [hw0] at hw
            have hNotPos : ¬(0 > 0) := by omega
            simp only [hf, hNotPos, ↓reduceIte] at hw
            rw [hSliceExt, hMinSlice] at hw
            refine ⟨hw.1, hw.2.trans ?_⟩
            cases isStdout
            · simp only [Bool.false_eq_true, ↓reduceIte]; apply hostState_ext <;> first | rfl | exact hf.symm
            · simp only [↓reduceIte]; apply hostState_ext <;> first | rfl | exact hf.symm)
          SysBridge.stdioEintrFuel (proj w).eintrCount w1 hW1Eq
        rw [show SysBridge.stdioEintrFuel = Model.stdioEintrRetryLimit from rfl] at hRe ⊢
        cases hAct : (retryEintr (caps.files.write fd (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)))) Model.stdioEintrRetryLimit).run.run w1 with
        | mk res w2 =>
          rw [hAct] at hRe
          by_cases hGt : (proj w).eintrCount > Model.stdioEintrRetryLimit
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            dsimp only [exceptT_run_pure]
            have hCl := caps_close_spec proj caps hCaps fd (if isStdout then .stdout else .stderr) (proj w).openDups w2
              (by rw [hw2])
            cases hc : (caps.files.close fd).run.run w2 with
            | mk clRes w3 =>
              rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
              dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
              exact ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
          · simp only [hGt, ↓reduceIte, Prod.mk.injEq] at hRe ⊢
            rcases hRe with ⟨rfl, hw2⟩
            have hMod : (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size < UInt32.size := by
              have : UInt32.size = 4294967296 := rfl; omega
            have hToNat : (UInt32.ofNat (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size).toNat =
                (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size := UInt32.toNat_ofNat_of_lt hMod
            have hNe0 : (UInt32.ofNat (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size == 0) = false := by
              apply beq_false_of_ne; intro hEq
              have hc := congrArg UInt32.toNat hEq; rw [hToNat] at hc
              change (text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))).size = 0 at hc; omega
            dsimp only
            simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hToNat, Nat.zero_add]
            rw [hSliceSz]
            have hRem' : text.toUTF8.size - min text.toUTF8.size (0 + 1048576) ≤ text.toUTF8.size - 1 := by omega
            have hLoop := writeStdioSlicesLoop_zero_spec proj caps hCaps isStdout fd text.toUTF8 (proj w).openDups
              (text.toUTF8.size - 1) (min text.toUTF8.size (0 + 1048576)) w2 hEndLe hRem'
              (by rw [hw2]; cases isStdout <;> rfl)
              (by rw [hw2]; cases isStdout <;> exact hf)
              (by rw [hw2]; cases isStdout <;> rfl)
            cases hRun : (SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 (min text.toUTF8.size (0 + 1048576)) (text.toUTF8.size - 1)).run.run w2 with
            | mk loopOut w3 =>
              rw [hRun] at hLoop; rcases hLoop with ⟨rfl, hw3⟩; dsimp only at hw3 ⊢
              have hCl := caps_close_spec proj caps hCaps fd (if isStdout then .stdout else .stderr) (proj w).openDups w3
                (by rw [hw3, hw2]; cases isStdout <;> rfl)
              cases hc : (caps.files.close fd).run.run w3 with
              | mk clRes w4 =>
                rw [hc] at hCl; rcases hCl with ⟨rfl, hw4⟩
                dsimp only [exceptT_run_pure] at hw4 ⊢
                refine ⟨rfl, ?_⟩
                rw [hw4, hw3, hw2]
                cases isStdout
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  apply hostState_ext <;> first | rfl | exact hf | exact hf.symm |
                    (dsimp only; rw [byteArray_append_assoc, byteArray_extract_append text.toUTF8 (Nat.zero_le _) hEndLe, byteArray_extract_zero_size])
                · simp only [↓reduceIte]
                  apply hostState_ext <;> first | rfl | exact hf | exact hf.symm |
                    (dsimp only; rw [byteArray_append_assoc, byteArray_extract_append text.toUTF8 (Nat.zero_le _) hEndLe, byteArray_extract_zero_size])
      | dupErrno code =>
        simp only [hf] at hDup ⊢
        rcases hDup with ⟨rfl, hw1⟩
        dsimp only [exceptT_run_pure, exceptT_run_throw] at hw1 ⊢
        exact ⟨rfl, hw1⟩
      | ioErrno code =>
        simp only [hf] at hDup ⊢
        rcases hDup with ⟨fd, rfl, hw1⟩
        dsimp only at hw1 ⊢
        rw [exceptT_run_bind, exceptT_run_tryFinally]
        have hBsFuel : text.toUTF8.size = (text.toUTF8.size - 1) + 1 := by omega
        have hLoopUnfold :
            SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 text.toUTF8.size =
              SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 ((text.toUTF8.size - 1) + 1) := by
          rw [← hBsFuel]
        rw [hLoopUnfold]
        unfold SysBridge.writeStdioSlicesLoop
        have hNotGe : ¬(0 ≥ text.toUTF8.size) := by omega
        simp only [hNotGe, ↓reduceIte]
        rw [exceptT_run_bind]
        have hRe := retryEintr_const_errno proj
          (caps.files.write fd (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8 else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576))))
          code (proj w1)
          (fun w0 hw0 => by
            have hf0 : (proj w0).fault = .ioErrno code := by rw [hw0, hw1]
            have hw := caps_write_spec proj caps hCaps isStdout fd
              (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8 else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)))
              (proj w).openDups w0 (by rw [hw0, hw1])
            rw [hf0] at hw; dsimp only at hw
            exact ⟨hw.1, hw.2.trans hw0⟩)
          SysBridge.stdioEintrFuel w1 rfl
        cases hAct : (retryEintr (caps.files.write fd (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8 else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)))) SysBridge.stdioEintrFuel).run.run w1 with
        | mk res w2 =>
          rw [hAct] at hRe; rcases hRe with ⟨rfl, hw2⟩
          dsimp only [exceptT_run_pure] at hw2 ⊢
          have hCl := caps_close_spec proj caps hCaps fd (if isStdout then .stdout else .stderr) (proj w).openDups w2
            (by rw [hw2, hw1])
          cases hc : (caps.files.close fd).run.run w2 with
          | mk clRes w3 =>
            rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
            dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
            exact ⟨rfl, by rw [hw3, hw2, hw1]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩
      | ioThrow msg =>
        simp only [hf] at hDup ⊢
        rcases hDup with ⟨fd, rfl, hw1⟩
        dsimp only at hw1 ⊢
        rw [exceptT_run_bind, exceptT_run_tryFinally]
        have hBsFuel : text.toUTF8.size = (text.toUTF8.size - 1) + 1 := by omega
        have hLoopUnfold :
            SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 text.toUTF8.size =
              SysBridge.writeStdioSlicesLoop caps.files fd text.toUTF8 0 ((text.toUTF8.size - 1) + 1) := by
          rw [← hBsFuel]
        rw [hLoopUnfold]
        unfold SysBridge.writeStdioSlicesLoop
        have hNotGe : ¬(0 ≥ text.toUTF8.size) := by omega
        simp only [hNotGe, ↓reduceIte]
        unfold SysBridge.stdioEintrFuel retryEintr
        rw [exceptT_run_bind, exceptT_run_bind]
        have hw := caps_write_spec proj caps hCaps isStdout fd
          (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8 else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)))
          (proj w).openDups w1 (by rw [hw1])
        rw [hw1] at hw; dsimp only at hw
        cases hWr : (caps.files.write fd (if (0 : Nat) == 0 && min text.toUTF8.size (0 + 1048576) == text.toUTF8.size then text.toUTF8 else text.toUTF8.extract 0 (min text.toUTF8.size (0 + 1048576)))).run.run w1 with
        | mk wrRes w2 =>
          rw [hWr] at hw; rcases hw with ⟨rfl, hw2⟩; dsimp only at hw2 ⊢
          have hCl := caps_close_spec proj caps hCaps fd (if isStdout then .stdout else .stderr) (proj w).openDups w2
            (by rw [hw2])
          cases hc : (caps.files.close fd).run.run w2 with
          | mk clRes w3 =>
            rw [hc] at hCl; rcases hCl with ⟨rfl, hw3⟩
            dsimp only [exceptT_run_pure, exceptT_run_throw] at hw3 ⊢
            exact ⟨rfl, by rw [hw3, hw2]; apply hostState_ext <;> first | rfl | exact hf | exact hf.symm⟩

/-- Exact single-step specification of `writeOut` over `ExceptT IO.Error (StateM W)`. -/
theorem mkCliOps_writeOut_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (text : String) (w : W) :
    (((Internal.mkCliOpsFromCapsM caps).writeOut text).run.run w).1 = (Model.stepHostWriteSlot true (proj w) text).1 ∧
      proj (((Internal.mkCliOpsFromCapsM caps).writeOut text).run.run w).2 = (Model.stepHostWriteSlot true (proj w) text).2 := by
  simpa using mkCliOps_writeSlot_spec proj caps hCaps true text w

/-- Exact single-step specification of `writeErr` over `ExceptT IO.Error (StateM W)`. -/
theorem mkCliOps_writeErr_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (text : String) (w : W) :
    (((Internal.mkCliOpsFromCapsM caps).writeErr text).run.run w).1 = (Model.stepHostWriteSlot false (proj w) text).1 ∧
      proj (((Internal.mkCliOpsFromCapsM caps).writeErr text).run.run w).2 = (Model.stepHostWriteSlot false (proj w) text).2 := by
  simpa using mkCliOps_writeSlot_spec proj caps hCaps false text w

/-- Exact single-step specification of `(Internal.mkCliOpsFromCapsM caps).getEnv` over `ExceptT IO.Error (StateM W)`. -/
theorem mkCliOps_getEnv_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (key : String) (w : W) :
    (((Internal.mkCliOpsFromCapsM caps).getEnv key).run.run w).1 = .ok (Model.lookupHostEnv (proj w).env key) ∧
      proj (((Internal.mkCliOpsFromCapsM caps).getEnv key).run.run w).2 = proj w := by
  unfold Internal.mkCliOpsFromCapsM SysBridge.mkFilesCliOpsM SysBridge.mapEnvVarsGet Model.lookupHostEnv
  dsimp only
  rw [exceptT_run_bind]
  have hg := caps_envGet_spec proj caps hCaps key w
  cases hr : (caps.env.getEnv key).run.run w with
  | mk res w1 =>
    rw [hr] at hg; rcases hg with ⟨rfl, hw1⟩; dsimp only at hw1 ⊢
    cases LeanSwe.EnvVars.Model.getEnvModel (proj w).env key <;> exact ⟨rfl, hw1⟩

/-- Compositional `Core.ObeysStepFromExcept` proof for `Internal.mkCliOpsFromCapsM`. -/
theorem obeysStepFromExcept_mkCliOpsFromCapsM :
    Core.ObeysStepFromExcept id Model.hostStepWf Model.execCapsStep Model.allowedHostCapsStep
      Model.hostStepWf Internal.mkCliOpsFromCapsM Model.execCliExceptStep Model.allowedHostCliStep := by
  intro W proj caps hCaps w req _
  cases req with
  | readLine =>
    dsimp only [Function.comp, id, Model.execCliExceptStep, Model.allowedHostCliStep]
    rw [exceptT_run_map]
    have h := mkCliOps_readLine_spec proj caps hCaps w
    cases hr : ((Internal.mkCliOpsFromCapsM caps).readLine).run.run w with
    | mk res w1 =>
      rw [hr] at h
      cases hs : Model.stepHostReadLine (proj w) with
      | mk mRes st =>
        rw [hs] at h; dsimp only at h ⊢
        exact Prod.ext (congrArg (Except.map Model.RawStepOut.line) h.1) h.2
  | writeOut text =>
    dsimp only [Function.comp, id, Model.execCliExceptStep, Model.allowedHostCliStep]
    rw [exceptT_run_seqRight]
    have h := mkCliOps_writeOut_spec proj caps hCaps text w
    cases hr : ((Internal.mkCliOpsFromCapsM caps).writeOut text).run.run w with
    | mk res w1 =>
      rw [hr] at h
      cases hs : Model.stepHostWriteSlot true (proj w) text with
      | mk mRes st =>
        rw [hs] at h; dsimp only at h ⊢; rcases h with ⟨rfl, hw1⟩
        cases res <;> (dsimp only [exceptT_run_pure]; exact Prod.ext rfl hw1)
  | writeErr text =>
    dsimp only [Function.comp, id, Model.execCliExceptStep, Model.allowedHostCliStep]
    rw [exceptT_run_seqRight]
    have h := mkCliOps_writeErr_spec proj caps hCaps text w
    cases hr : ((Internal.mkCliOpsFromCapsM caps).writeErr text).run.run w with
    | mk res w1 =>
      rw [hr] at h
      cases hs : Model.stepHostWriteSlot false (proj w) text with
      | mk mRes st =>
        rw [hs] at h; dsimp only at h ⊢; rcases h with ⟨rfl, hw1⟩
        cases res <;> (dsimp only [exceptT_run_pure]; exact Prod.ext rfl hw1)
  | getEnv key =>
    dsimp only [Function.comp, id, Model.execCliExceptStep, Model.allowedHostCliStep]
    rw [exceptT_run_map]
    have h := mkCliOps_getEnv_spec proj caps hCaps key w
    cases hr : ((Internal.mkCliOpsFromCapsM caps).getEnv key).run.run w with
    | mk res w1 =>
      rw [hr] at h
      rcases h with ⟨rfl, hw1⟩
      exact ⟨rfl, hw1⟩

end LeanSwe.CmdLine.Proofs
