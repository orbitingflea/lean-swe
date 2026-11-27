import LeanSwe.PostFork.Proofs.ObeysHelpers

/-!
Canonical `Core.ObeysStepFrom` capability-refinement proofs (`obeysStepFrom_postfork`,
`modelRawOps_obeys_allowedRawStep`) for `LeanSwe.PostFork`.
-/

namespace LeanSwe.PostFork.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Impl.Internal

/-- Canonical `Core.ObeysStepFrom` refinement lifting `PosixHostOpsM` to `PostForkOpsM`. -/
theorem obeysStepFrom_postfork :
    Core.ObeysStepFrom id rawStepWf execRawStep allowedRawStep
      rawStepWf mkHostOpsM execPkgStep allowedPkgStep := by
  intro W proj raw hRaw w req hwf
  try dsimp only [Function.comp_apply, id] at hwf ⊢
  cases req with
  | spawn spec =>
    try dsimp only [allowedPkgStep, execPkgStep, Functor.map, StateT.map, mkHostOpsM, mkHostOps,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    rw [show validateSpecImpl spec = validateSpec spec from rfl]
    cases hVal : validateSpec spec with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      simp [hVal, validInvalidErrProp, mkInvalidErr, hwf]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      have hStd := probeStdioPlan_sound hRaw spec.stdio w hwf
      try dsimp only [StateT.run] at hStd
      cases hS : probeStdioPlan raw spec.stdio w with
      | mk stdRes w₁ =>
        rw [hS] at hStd
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStd ⊢
        cases stdRes with
        | error err =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hwf, hStd.1.1, hStd.1.2, Or.inl (hStd.2 err rfl)⟩
        | ok u =>
          cases u
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          have hKeep := probeRefList_sound hRaw (FdPolicy.keepFds spec.fdPolicy).toList w₁ hStd.1.1
          try dsimp only [StateT.run] at hKeep
          rw [show keepFdsImpl spec.fdPolicy = FdPolicy.keepFds spec.fdPolicy from rfl]
          cases hK : probeRefList raw (FdPolicy.keepFds spec.fdPolicy).toList w₁ with
          | mk keepRes w₂ =>
            rw [hK] at hKeep
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hKeep ⊢
            have hInv₂ := hostInv_trans hStd.1 hKeep.1
            cases keepRes with
            | error err =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ⟨hwf, hInv₂.1, hInv₂.2, Or.inl (hKeep.2 err rfl)⟩
            | ok u =>
              cases u
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              have hFilt := filterOpenCloseList_inv hRaw spec.closeFds.toList #[] w₂ hInv₂.1
              try dsimp only [StateT.run] at hFilt
              cases hF : filterOpenCloseList raw spec.closeFds.toList #[] w₂ with
              | mk openCloseFds w₃ =>
                rw [hF] at hFilt
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hFilt ⊢
                have hInv₃ := hostInv_trans hInv₂ hFilt
                have hPipe := hRaw w₃ .mkPipeCloexec hInv₃.1
                try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
                  Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe
                cases hP : raw.mkPipeCloexec w₃ with
                | mk pRes w₄ =>
                  rw [hP] at hPipe
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe ⊢
                  rcases hPipe with ⟨_, hwf₄, hLe₄, hPayP⟩
                  have hInv₄ := hostInv_trans hInv₃ ⟨hwf₄, hLe₄⟩
                  cases pRes with
                  | error e =>
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayP ⊢
                    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨hwf, hInv₄.1, hInv₄.2,
                      Or.inl (mkSysErr_valid e "pipe2 error-pipe failed" hPayP rfl)⟩
                  | ok pair =>
                    rcases pair with ⟨errR, errW⟩
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                    have hFk := performFork_sound hRaw spec none errW openCloseFds
                      #[FdRef.handle errR] false w₄ hInv₄.1
                    try dsimp only [StateT.run] at hFk
                    cases hFkRun : performFork raw spec none errW openCloseFds
                        #[FdRef.handle errR] false w₄ with
                    | mk fkRes w₅ =>
                      rw [hFkRun] at hFk
                      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hFk ⊢
                      have hInv₅ := hostInv_trans hInv₄ hFk.1
                      have hClW := (closeFd_inv hRaw errW w₅ hInv₅.1).1
                      try dsimp only [StateT.run] at hClW
                      cases hCw : raw.closeFd errW w₅ with
                      | mk _ w₆ =>
                        rw [hCw] at hClW
                        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hClW ⊢
                        have hInv₆ := hostInv_trans hInv₅ hClW
                        cases fkRes with
                        | error err =>
                          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                          have hClR := (closeFd_inv hRaw errR w₆ hInv₆.1).1
                          try dsimp only [StateT.run] at hClR
                          cases hCr : raw.closeFd errR w₆ with
                          | mk _ w₇ =>
                            rw [hCr] at hClR
                            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hClR ⊢
                            have hInv₇ := hostInv_trans hInv₆ hClR
                            simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                            exact ⟨hwf, hInv₇.1, hInv₇.2, Or.inl (hFk.2.2 err rfl)⟩
                        | ok pid =>
                          rcases hFk.2.1 pid rfl with ⟨hGe1, hLeMax⟩
                          cases hPg : spec.processGroup with
                          | inherit =>
                            try dsimp only [expectedPgid, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                            have hAw := awaitExecOrFailure_sound hRaw pid none errR 18 false w₆ hInv₆.1
                            try dsimp only [StateT.run] at hAw
                            cases hAwRun : awaitExecOrFailure raw pid none errR 18 false w₆ with
                            | mk awRes w₇ =>
                              rw [hAwRun] at hAw
                              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hAw ⊢
                              have hInv₇ := hostInv_trans hInv₆ hAw.1
                              simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                              cases awRes with
                              | error err => exact ⟨hwf, hInv₇.1, hInv₇.2, hAw.2.2 err rfl⟩
                              | ok ch =>
                                dsimp only
                                rcases hAw.2.1 ch rfl with ⟨hPidEq, hPgEq⟩
                                rw [hPg, hPidEq, hPgEq]
                                exact ⟨hwf, hInv₇.1, hInv₇.2, hGe1, hLeMax, rfl⟩
                          | newGroup =>
                            try dsimp only [expectedPgid, Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                            have hAw := awaitExecOrFailure_sound hRaw pid (some pid) errR 18 false w₆ hInv₆.1
                            try dsimp only [StateT.run] at hAw
                            cases hAwRun : awaitExecOrFailure raw pid (some pid) errR 18 false w₆ with
                            | mk awRes w₇ =>
                              rw [hAwRun] at hAw
                              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hAw ⊢
                              have hInv₇ := hostInv_trans hInv₆ hAw.1
                              simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                              cases awRes with
                              | error err => exact ⟨hwf, hInv₇.1, hInv₇.2, hAw.2.2 err rfl⟩
                              | ok ch =>
                                dsimp only
                                rcases hAw.2.1 ch rfl with ⟨hPidEq, hPgEq⟩
                                rw [hPg, hPidEq, hPgEq]
                                exact ⟨hwf, hInv₇.1, hInv₇.2, hGe1, hLeMax, rfl⟩
  | spawnWithBarrier spec =>
    try dsimp only [allowedPkgStep, execPkgStep, Functor.map, StateT.map, mkHostOpsM, mkHostOps,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    rw [show validateSpecImpl spec = validateSpec spec from rfl]
    cases hVal : validateSpec spec with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      simp [hVal, validInvalidErrProp, mkInvalidErr, hwf]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      have hStd := probeStdioPlan_sound hRaw spec.stdio w hwf
      try dsimp only [StateT.run] at hStd
      cases hS : probeStdioPlan raw spec.stdio w with
      | mk stdRes w₁ =>
        rw [hS] at hStd
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStd ⊢
        cases stdRes with
        | error err =>
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hwf, hStd.1.1, hStd.1.2, hStd.2 err rfl⟩
        | ok u =>
          cases u
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          have hKeep := probeRefList_sound hRaw (FdPolicy.keepFds spec.fdPolicy).toList w₁ hStd.1.1
          try dsimp only [StateT.run] at hKeep
          rw [show keepFdsImpl spec.fdPolicy = FdPolicy.keepFds spec.fdPolicy from rfl]
          cases hK : probeRefList raw (FdPolicy.keepFds spec.fdPolicy).toList w₁ with
          | mk keepRes w₂ =>
            rw [hK] at hKeep
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hKeep ⊢
            have hInv₂ := hostInv_trans hStd.1 hKeep.1
            cases keepRes with
            | error err =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ⟨hwf, hInv₂.1, hInv₂.2, hKeep.2 err rfl⟩
            | ok u =>
              cases u
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              have hFilt := filterOpenCloseList_inv hRaw spec.closeFds.toList #[] w₂ hInv₂.1
              try dsimp only [StateT.run] at hFilt
              cases hF : filterOpenCloseList raw spec.closeFds.toList #[] w₂ with
              | mk openCloseFds w₃ =>
                rw [hF] at hFilt
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hFilt ⊢
                have hInv₃ := hostInv_trans hInv₂ hFilt
                have hPipe1 := hRaw w₃ .mkPipeCloexec hInv₃.1
                try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
                  Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe1
                cases hP1 : raw.mkPipeCloexec w₃ with
                | mk pRes1 w₄ =>
                  rw [hP1] at hPipe1
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe1 ⊢
                  rcases hPipe1 with ⟨_, hwf₄, hLe₄, hPayP1⟩
                  have hInv₄ := hostInv_trans hInv₃ ⟨hwf₄, hLe₄⟩
                  cases pRes1 with
                  | error e =>
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayP1 ⊢
                    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨hwf, hInv₄.1, hInv₄.2, mkSysErr_valid e "pipe2 error-pipe failed" hPayP1 rfl⟩
                  | ok pair1 =>
                    rcases pair1 with ⟨errR, errW⟩
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayP1 ⊢
                    have hPipe2 := hRaw w₄ .mkPipeCloexec hwf₄
                    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
                      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe2
                    cases hP2 : raw.mkPipeCloexec w₄ with
                    | mk pRes2 w₅ =>
                      rw [hP2] at hPipe2
                      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPipe2 ⊢
                      rcases hPipe2 with ⟨_, hwf₅, hLe₅, hPayP2⟩
                      have hInv₅ := hostInv_trans hInv₄ ⟨hwf₅, hLe₅⟩
                      cases pRes2 with
                      | error e =>
                        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayP2 ⊢
                        have hCl := closeListQuiet_inv hRaw [errW, errR] w₅ hwf₅
                        try dsimp only [StateT.run] at hCl
                        cases hClRun : closeListQuiet raw [errW, errR] w₅ with
                        | mk _ w₆ =>
                          rw [hClRun] at hCl
                          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl ⊢
                          have hInv₆ := hostInv_trans hInv₅ hCl
                          simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                          exact ⟨hwf, hInv₆.1, hInv₆.2, mkSysErr_valid e "pipe2 sync-barrier failed" hPayP2 rfl⟩
                      | ok pair2 =>
                        rcases pair2 with ⟨syncR, syncW⟩
                        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayP2 ⊢
                        have hFk := performFork_sound hRaw spec (some syncR) errW openCloseFds
                          #[FdRef.handle errR, FdRef.handle syncW] true w₅ hwf₅
                        try dsimp only [StateT.run] at hFk
                        cases hFkRun : performFork raw spec (some syncR) errW openCloseFds
                            #[FdRef.handle errR, FdRef.handle syncW] true w₅ with
                        | mk fkRes w₆ =>
                          rw [hFkRun] at hFk
                          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hFk ⊢
                          have hInv₆ := hostInv_trans hInv₅ hFk.1
                          have hCl1 := closeListQuiet_inv hRaw [errW, syncR] w₆ hInv₆.1
                          try dsimp only [StateT.run] at hCl1
                          cases hCl1Run : closeListQuiet raw [errW, syncR] w₆ with
                          | mk _ w₇ =>
                            rw [hCl1Run] at hCl1
                            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl1 ⊢
                            have hInv₇ := hostInv_trans hInv₆ hCl1
                            cases fkRes with
                            | error err =>
                              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                              have hCl2 := closeListQuiet_inv hRaw [syncW, errR] w₇ hInv₇.1
                              try dsimp only [StateT.run] at hCl2
                              cases hCl2Run : closeListQuiet raw [syncW, errR] w₇ with
                              | mk _ w₈ =>
                                rw [hCl2Run] at hCl2
                                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl2 ⊢
                                have hInv₈ := hostInv_trans hInv₇ hCl2
                                simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                                exact ⟨hwf, hInv₈.1, hInv₈.2, hFk.2.2 err rfl⟩
                            | ok pid =>
                              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                              simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                              rcases hFk.2.1 pid rfl with ⟨hGe1, hLeMax⟩
                              have hErrRGe : (proj w).nextHandle ≤ errR :=
                                Nat.le_trans hInv₃.2 hPayP1.2.1
                              have hErrRLtSyncW : errR < syncW :=
                                Nat.lt_of_lt_of_le hPayP1.2.2.2.1 hPayP2.2.2.1
                              have hSyncWLt : syncW < (proj w₇).nextHandle :=
                                Nat.lt_of_lt_of_le hPayP2.2.2.2.2 (Nat.le_trans hFk.1.2 hCl1.2)
                              cases spec.processGroup <;>
                                exact ⟨hwf, hInv₇.1, hInv₇.2, hGe1, hLeMax, rfl,
                                  Nat.ne_of_gt hErrRLtSyncW, hErrRGe, hSyncWLt⟩
  | releaseBarrier pending =>
    try dsimp only [allowedPkgStep, execPkgStep, Functor.map, StateT.map, mkHostOpsM, mkHostOps,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    have hPr := hRaw w (.probeHandleOpen pending.errRead) hwf
    try dsimp only [allowedRawStep, execRawStep, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPr
    cases hPrRun : raw.probeHandleOpen pending.errRead w with
    | mk prRes w₁ =>
      rw [hPrRun] at hPr
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPr ⊢
      rcases hPr with ⟨_, hwf₁, hLe₁, hPayPr⟩
      cases prRes with
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hPayPr ⊢
        exact ⟨hwf, hwf₁, hLe₁, Or.inl (mkSysErr_valid e _ hPayPr (by decide))⟩
      | ok u =>
        cases u
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hWr := writeAllRetryEintr_sound hRaw pending.syncWrite (ByteArray.mk #[1]) 0 18 w₁ hwf₁
        try dsimp only [StateT.run] at hWr
        cases hWrRun : writeAllRetryEintr raw pending.syncWrite (ByteArray.mk #[1]) 0 18 w₁ with
        | mk wrRes w₂ =>
          rw [hWrRun] at hWr
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWr ⊢
          have hInv₂ := hostInv_trans ⟨hwf₁, hLe₁⟩ hWr.1
          cases wrRes with
          | ok u =>
            cases u
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            have hCl := (closeFd_inv hRaw pending.syncWrite w₂ hInv₂.1).1
            try dsimp only [StateT.run] at hCl
            cases hClRun : raw.closeFd pending.syncWrite w₂ with
            | mk _ w₃ =>
              rw [hClRun] at hCl
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl ⊢
              have hInv₃ := hostInv_trans hInv₂ hCl
              have hAw := awaitExecOrFailure_sound hRaw pending.pid pending.pgid
                pending.errRead 18 false w₃ hInv₃.1
              try dsimp only [StateT.run] at hAw
              cases hAwRun : awaitExecOrFailure raw pending.pid pending.pgid
                  pending.errRead 18 false w₃ with
              | mk awRes w₄ =>
                rw [hAwRun] at hAw
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hAw ⊢
                have hInv₄ := hostInv_trans hInv₃ hAw.1
                cases awRes with
                | ok ch => exact ⟨hwf, hInv₄.1, hInv₄.2, hAw.2.1 ch rfl⟩
                | error err => exact ⟨hwf, hInv₄.1, hInv₄.2, hAw.2.2 err rfl⟩
          | error err =>
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
            have hErrSys : validSysErrProp err := hWr.2 err rfl
            by_cases hEpipe : (err.errno == some Errno.EPIPE) = true
            · simp only [hEpipe, ↓reduceIte]
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              have hCl := (closeFd_inv hRaw pending.syncWrite w₂ hInv₂.1).1
              try dsimp only [StateT.run] at hCl
              cases hClRun : raw.closeFd pending.syncWrite w₂ with
              | mk _ w₃ =>
                rw [hClRun] at hCl
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl ⊢
                have hInv₃ := hostInv_trans hInv₂ hCl
                have hAw := awaitExecOrFailure_sound hRaw pending.pid pending.pgid
                  pending.errRead 18 true w₃ hInv₃.1
                try dsimp only [StateT.run] at hAw
                cases hAwRun : awaitExecOrFailure raw pending.pid pending.pgid
                    pending.errRead 18 true w₃ with
                | mk awRes w₄ =>
                  rw [hAwRun] at hAw
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hAw ⊢
                  have hInv₄ := hostInv_trans hInv₃ hAw.1
                  cases awRes with
                  | ok ch => exact ⟨hwf, hInv₄.1, hInv₄.2, hAw.2.1 ch rfl⟩
                  | error err₂ => exact ⟨hwf, hInv₄.1, hInv₄.2, hAw.2.2 err₂ rfl⟩
            · simp only [hEpipe, Bool.false_eq_true, ↓reduceIte]
              by_cases hFast : isFastFailSyncWriteErr err.errno = true
              · simp only [hFast, ↓reduceIte]
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                exact ⟨hwf, hInv₂.1, hInv₂.2, Or.inl hErrSys⟩
              · simp only [hFast, Bool.false_eq_true, ↓reduceIte]
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                have hCl1 := (closeFd_inv hRaw pending.syncWrite w₂ hInv₂.1).1
                try dsimp only [StateT.run] at hCl1
                cases hCl1Run : raw.closeFd pending.syncWrite w₂ with
                | mk cl1Res w₃ =>
                  rw [hCl1Run] at hCl1
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl1 ⊢
                  have hInv₃ := hostInv_trans hInv₂ hCl1
                  cases cl1Res with
                  | error e =>
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                    by_cases hDet : (!isKernelCloseDetachNonBadf e) = true
                    · simp only [hDet, ↓reduceIte]
                      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                      exact ⟨hwf, hInv₃.1, hInv₃.2, Or.inl hErrSys⟩
                    · simp only [hDet, Bool.false_eq_true, ↓reduceIte]
                      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                      have hCl2 := (closeFd_inv hRaw pending.errRead w₃ hInv₃.1).1
                      try dsimp only [StateT.run] at hCl2
                      cases hCl2Run : raw.closeFd pending.errRead w₃ with
                      | mk _ w₄ =>
                        rw [hCl2Run] at hCl2
                        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl2 ⊢
                        have hInv₄ := hostInv_trans hInv₃ hCl2
                        have hWt := (waitRetryEintr_sound hRaw pending.pid 18 w₄ hInv₄.1).1
                        try dsimp only [StateT.run] at hWt
                        cases hWtRun : waitRetryEintr raw pending.pid 18 w₄ with
                        | mk _ w₅ =>
                          rw [hWtRun] at hWt
                          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWt ⊢
                          have hInv₅ := hostInv_trans hInv₄ hWt
                          exact ⟨hwf, hInv₅.1, hInv₅.2, Or.inl hErrSys⟩
                  | ok u =>
                    cases u
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                    have hCl2 := (closeFd_inv hRaw pending.errRead w₃ hInv₃.1).1
                    try dsimp only [StateT.run] at hCl2
                    cases hCl2Run : raw.closeFd pending.errRead w₃ with
                    | mk _ w₄ =>
                      rw [hCl2Run] at hCl2
                      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl2 ⊢
                      have hInv₄ := hostInv_trans hInv₃ hCl2
                      have hWt := (waitRetryEintr_sound hRaw pending.pid 18 w₄ hInv₄.1).1
                      try dsimp only [StateT.run] at hWt
                      cases hWtRun : waitRetryEintr raw pending.pid 18 w₄ with
                      | mk _ w₅ =>
                        rw [hWtRun] at hWt
                        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWt ⊢
                        have hInv₅ := hostInv_trans hInv₄ hWt
                        exact ⟨hwf, hInv₅.1, hInv₅.2, Or.inl hErrSys⟩
  | abortBarrier pending =>
    try dsimp only [allowedPkgStep, execPkgStep, Functor.map, StateT.map, mkHostOpsM, mkHostOps,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    have hCl1 := closeFd_inv hRaw pending.syncWrite w hwf
    try dsimp only [StateT.run] at hCl1
    cases hCl1Run : raw.closeFd pending.syncWrite w with
    | mk cl1Res w₁ =>
      rw [hCl1Run] at hCl1
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl1 ⊢
      have hCont : ∀ (wA : W), HostInv proj w wA →
          let r := ((do
            let repRes ← readAllRetryEintr raw pending.errRead 16 ByteArray.empty 18
            let _ ← raw.closeFd pending.errRead
            match repRes with
            | .error err =>
              let _ ← waitRetryEintr raw pending.pid 18
              return Except.error err
            | .ok repBytes =>
              let wst ← match ← waitRetryEintr raw pending.pid 18 with
                | .ok s => pure s
                | .error err => return Except.error err
              match decodeChildFailure repBytes with
              | none => return Except.ok (AbortOutcome.aborted wst)
              | some cf =>
                return Except.ok
                  (AbortOutcome.failedBeforeBarrier { cf with waitStatus := some wst } wst) :
              StateM W (Except PostForkError AbortOutcome))).run wA
          rawStepWf (proj w) = true ∧ rawStepWf (proj r.2) = true ∧
            (proj w).nextHandle ≤ (proj r.2).nextHandle ∧
            match r.1 with
            | .ok (.aborted wst) => validWaitStatusProp wst
            | .ok (.failedBeforeBarrier cf wst) =>
              validWaitStatusProp wst ∧ cf.waitStatus = some wst ∧ validHostErrnoProp cf.errno
            | .error err => validSysErrProp err := by
        intro wA hInvA
        have hRd := readAllRetryEintr_sound hRaw pending.errRead 16 ByteArray.empty 18 wA hInvA.1
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRd ⊢
        cases hRdRun : readAllRetryEintr raw pending.errRead 16 ByteArray.empty 18 wA with
        | mk repRes wB =>
          rw [hRdRun] at hRd
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRd ⊢
          have hInvB := hostInv_trans hInvA hRd.1
          have hCl2 := (closeFd_inv hRaw pending.errRead wB hInvB.1).1
          try dsimp only [StateT.run] at hCl2
          cases hCl2Run : raw.closeFd pending.errRead wB with
          | mk _ wC =>
            rw [hCl2Run] at hCl2
            try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hCl2 ⊢
            have hInvC := hostInv_trans hInvB hCl2
            cases repRes with
            | error err =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              have hWt := (waitRetryEintr_sound hRaw pending.pid 18 wC hInvC.1).1
              try dsimp only [StateT.run] at hWt
              cases hWtRun : waitRetryEintr raw pending.pid 18 wC with
              | mk _ wD =>
                rw [hWtRun] at hWt
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWt ⊢
                have hInvD := hostInv_trans hInvC hWt
                exact ⟨hwf, hInvD.1, hInvD.2, hRd.2 err rfl⟩
            | ok repBytes =>
              try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
              have hWt := waitRetryEintr_sound hRaw pending.pid 18 wC hInvC.1
              try dsimp only [StateT.run] at hWt
              cases hWtRun : waitRetryEintr raw pending.pid 18 wC with
              | mk wtRes wD =>
                rw [hWtRun] at hWt
                try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hWt ⊢
                have hInvD := hostInv_trans hInvC hWt.1
                cases wtRes with
                | error err =>
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                  exact ⟨hwf, hInvD.1, hInvD.2, hWt.2.2 err rfl⟩
                | ok wst =>
                  try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                  have hWst := hWt.2.1 wst rfl
                  cases hDec : decodeChildFailure repBytes with
                  | none =>
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                    exact ⟨hwf, hInvD.1, hInvD.2, hWst⟩
                  | some cf =>
                    try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
                    exact ⟨hwf, hInvD.1, hInvD.2, hWst, rfl, decodeChildFailure_errno_valid hDec⟩
      cases cl1Res with
      | ok u =>
        cases u
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hRes := hCont w₁ hCl1.1
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRes ⊢
        exact hRes
      | error e =>
        try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        by_cases hDet : (!isKernelCloseDetachNonBadf e) = true
        · simp only [hDet, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          exact ⟨hwf, hCl1.1.1, hCl1.1.2, mkSysErr_valid e _ (hCl1.2 e rfl) (by decide)⟩
        · simp only [hDet, Bool.false_eq_true, ↓reduceIte]
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
          have hRes := hCont w₁ hCl1.1
          try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hRes ⊢
          exact hRes

/-- Reference `Model.modelRawOps` satisfies `Core.ObeysStep` against `Model.allowedRawStep`. -/
theorem modelRawOps_obeys_allowedRawStep :
    Core.ObeysStep id rawStepWf (execRawStep modelRawOps) allowedRawStep := by
  intro s req hwf
  try dsimp only [id] at hwf ⊢
  have hParts : s.healthyHost = true ∧ 3 ≤ s.nextHandle ∧ 1 ≤ s.lastPid ∧ s.lastPid ≤ maxLinuxPid := by
    unfold rawStepWf at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2⟩
  cases req with
  | probeFdOpen fd =>
    try dsimp only [allowedRawStep, execRawStep, modelRawOps, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    by_cases h0 : decide (0 ≤ fd.toInt) = true
    · simp [h0, pure, StateT.pure, hwf]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      try dsimp only [Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      exact ⟨hwf, hwf, Nat.le_refl _, ⟨by decide, by decide⟩⟩
  | probeHandleOpen _ =>
    exact ⟨hwf, hwf, Nat.le_refl _, trivial⟩
  | mkPipeCloexec =>
    try dsimp only [allowedRawStep, execRawStep, modelRawOps, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set]
    have hwf' : rawStepWf { s with nextHandle := s.nextHandle + 2 } = true := by
      unfold rawStepWf
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hParts.1, by omega, hParts.2.2.1, hParts.2.2.2⟩
    exact ⟨hwf, hwf', by omega, by omega, Nat.le_refl _, by omega, by omega, by omega⟩
  | closeFd _ =>
    exact ⟨hwf, hwf, Nat.le_refl _, trivial⟩
  | setpgidOnce _ _ =>
    exact ⟨hwf, hwf, Nat.le_refl _, trivial⟩
  | writeOnce _ _ _ _ =>
    exact ⟨hwf, hwf, Nat.le_refl _, Nat.le_refl _⟩
  | readOnce _ _ =>
    exact ⟨hwf, hwf, Nat.le_refl _, Nat.zero_le _⟩
  | waitOnce _ =>
    try dsimp only [allowedRawStep, execRawStep, modelRawOps, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    exact ⟨hwf, hwf, Nat.le_refl _, by unfold validWaitStatusProp; decide⟩
  | forkRun _ _ _ _ _ _ _ _ _ _ _ =>
    try dsimp only [allowedRawStep, execRawStep, modelRawOps, Functor.map, StateT.map,
      Bind.bind, pure, Pure.pure, StateT.run, StateT.bind, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set]
    have hwf' : rawStepWf { s with lastPid := 100 } = true := by
      unfold rawStepWf
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hParts.1, hParts.2.1, by decide, by decide⟩
    exact ⟨hwf, hwf', Nat.le_refl _, by decide, by decide, rfl⟩

end LeanSwe.PostFork.Proofs
