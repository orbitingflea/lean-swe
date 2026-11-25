import Core.Obeys
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model
import LeanSwe.Fs.Model.HealthyStep

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- The initial `FsWorld` satisfies `fsWorldWf`. -/
theorem fsWorldWf_initial : Model.fsWorldWf {} = true := rfl

/-- Single verified `healthyStep` forms a 1-step `HealthyFilesSteps` trace. -/
theorem healthyFilesSteps_single {e1 e2 : HealthyEnv} {req : FilesReq} {out : FilesOutcome}
    (h : healthyStep e1 req out = some e2) :
    HealthyFilesSteps e1 [(req, out)] e2 :=
  HealthyFilesSteps.cons req out [] h (HealthyFilesSteps.nil e2)

/-- Append two `HealthyFilesSteps` traces. -/
theorem healthyFilesSteps_append {e1 e2 e3 : HealthyEnv} {tr1 tr2 : List KernelStep}
    (h1 : HealthyFilesSteps e1 tr1 e2) (h2 : HealthyFilesSteps e2 tr2 e3) :
    HealthyFilesSteps e1 (tr1 ++ tr2) e3 := by
  induction h1 with
  | nil _ => exact h2
  | cons req out rest hs _ ih => exact HealthyFilesSteps.cons req out _ hs (ih h2)

private theorem list_erase_append_left {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} {x : α} (hx : x ∈ xs) :
    (xs ++ ys).erase x = xs.erase x ++ ys := by
  induction xs with
  | nil => cases hx
  | cons a tl ih =>
    simp only [List.cons_append, List.erase_cons]
    cases hEq : (a == x) with
    | true => rfl
    | false =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | htl
      · simp at hEq
      · simp [ih htl]

/-- Append two `TraceFds` derivations. -/
theorem traceFds_append {h1 h2 h3 : List HandleId} {tr1 tr2 : List KernelStep}
    (t1 : TraceFds h1 tr1 h2) (t2 : TraceFds h2 tr2 h3) :
    TraceFds h1 (tr1 ++ tr2) h3 := by
  induction t1 with
  | nil _ => exact t2
  | step hOne _ ih => exact TraceFds.step hOne (ih t2)

/-- Frame `TraceFds` on the right with an arbitrary extra list of held descriptors. -/
theorem traceFds_frame {h1 h2 extra : List HandleId} {tr : List KernelStep}
    (t : TraceFds h1 tr h2) :
    TraceFds (h1 ++ extra) tr (h2 ++ extra) := by
  induction t with
  | nil _ => exact TraceFds.nil _
  | @step held held' held'' s rest hOne _ ih =>
    refine TraceFds.step ?_ ih
    cases hO : stepOpenedFd s <;> cases hC : stepClosedFd s
    · rw [hO, hC] at hOne; dsimp only at hOne; subst hOne; rfl
    · rw [hO, hC] at hOne; dsimp only at hOne
      obtain ⟨hMem, hEq⟩ := hOne
      exact ⟨List.mem_append_left extra hMem, by rw [hEq, list_erase_append_left hMem]⟩
    · rw [hO, hC] at hOne; dsimp only at hOne; subst hOne; rfl
    · rw [hO, hC] at hOne; exact False.elim hOne

/-- Frame a balanced `TraceFds [] tr []` onto any outer held descriptor list. -/
theorem traceFds_frame_empty {held : List HandleId} {tr : List KernelStep}
    (t : TraceFds [] tr []) : TraceFds held tr held := by
  simpa using traceFds_frame (extra := held) t

/-- Single non-open, non-close step preserves `held`. -/
theorem traceFds_nonFd_step {held : List HandleId} {s : KernelStep}
    (hO : stepOpenedFd s = none) (hC : stepClosedFd s = none) :
    TraceFds held [s] held :=
  TraceFds.step (by simp [hO, hC]) (TraceFds.nil held)

/-- Single descriptor-opening step pushes `h` onto `held`. -/
theorem traceFds_open_step {held : List HandleId} {s : KernelStep} {h : HandleId}
    (hO : stepOpenedFd s = some h) (hC : stepClosedFd s = none) :
    TraceFds held [s] (h :: held) :=
  TraceFds.step (by simp [hO, hC]) (TraceFds.nil (h :: held))

/-- Single descriptor-closing step pops head `h` from `h :: held`. -/
theorem traceFds_close_head {held : List HandleId} {s : KernelStep} {h : HandleId}
    (hO : stepOpenedFd s = none) (hC : stepClosedFd s = some h) :
    TraceFds (h :: held) [s] held :=
  TraceFds.step (by simp [hO, hC]) (TraceFds.nil held)

/-- Empty `FsWorldTrace` reflexivity. -/
theorem fsWorldTrace_nil {w : FsWorld} (hWf : fsWorldWf w = true) :
    FsWorldTrace w [] w :=
  ⟨hWf, HealthyFilesSteps.nil w.env, TraceFds.nil [], Nat.le_refl _⟩

/-- Append two `FsWorldTrace` transitions. -/
theorem fsWorldTrace_append {w1 w2 w3 : FsWorld} {tr1 tr2 : List KernelStep}
    (h1 : FsWorldTrace w1 tr1 w2) (h2 : FsWorldTrace w2 tr2 w3) :
    FsWorldTrace w1 (tr1 ++ tr2) w3 :=
  ⟨h2.1, healthyFilesSteps_append h1.2.1 h2.2.1,
   traceFds_append h1.2.2.1 h2.2.2.1, Nat.le_trans h1.2.2.2 h2.2.2.2⟩

/-- Reflexivity of `Subtrace`. -/
theorem subtrace_refl (tr : List KernelStep) : Subtrace tr tr :=
  ⟨[], [], by simp⟩

/-- Left weakening of `Subtrace`. -/
theorem subtrace_append_left {sub tr1 : List KernelStep} (tr2 : List KernelStep)
    (h : Subtrace sub tr1) : Subtrace sub (tr1 ++ tr2) := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨pre, post ++ tr2, by simp [List.append_assoc]⟩

/-- Right weakening of `Subtrace`. -/
theorem subtrace_append_right {sub tr2 : List KernelStep} (tr1 : List KernelStep)
    (h : Subtrace sub tr2) : Subtrace sub (tr1 ++ tr2) := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨tr1 ++ pre, post, by simp [List.append_assoc]⟩

/-- Transitivity of `Subtrace`. -/
theorem subtrace_trans {a b c : List KernelStep}
    (h1 : Subtrace a b) (h2 : Subtrace b c) : Subtrace a c := by
  obtain ⟨p1, q1, rfl⟩ := h1
  obtain ⟨p2, q2, rfl⟩ := h2
  exact ⟨p2 ++ p1, q1 ++ q2, by simp [List.append_assoc]⟩

/-- Associativity of `ByteArray` append. -/
theorem byteArray_append_assoc (a b c : ByteArray) : (a ++ b) ++ c = a ++ (b ++ c) := by
  apply ByteArray.ext
  simp [Array.append_assoc]

/-- Left identity of `ByteArray.empty`. -/
theorem byteArray_empty_append (a : ByteArray) : ByteArray.empty ++ a = a := by
  apply ByteArray.ext
  simp

/-- Right identity of `ByteArray.empty`. -/
theorem byteArray_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext
  simp

/-- `ByteArray.emptyWithCapacity n` equals `ByteArray.empty`. -/
theorem byteArray_emptyWithCapacity_eq (n : Nat) :
    ByteArray.emptyWithCapacity n = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext'
  simp [ByteArray.emptyWithCapacity, ByteArray.empty]

/-- `concatChunks chunks cap` equals folding `(· ++ ·)` over `chunks.toList` from `ByteArray.empty`. -/
theorem concatChunks_eq_foldl (chunks : Array ByteArray) (cap : Nat) :
    concatChunks chunks cap = chunks.toList.foldl (· ++ ·) ByteArray.empty := by
  unfold concatChunks
  rw [byteArray_emptyWithCapacity_eq]

/-- Folding `(· ++ ·)` from an initial accumulator `init` pulls `init` to the left. -/
theorem foldl_byteArray_append_init (xs : List ByteArray) (init : ByteArray) :
    xs.foldl (· ++ ·) init = init ++ xs.foldl (· ++ ·) ByteArray.empty := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, byteArray_empty_append]
    rw [ih (init ++ x), ih x, byteArray_append_assoc]

private theorem byteArray_extract_toList (data : ByteArray) (b e : Nat) :
    (data.extract b e).data.toList = (data.data.toList.drop b).take (e - b) := by
  have h1 : (data.extract b e).data = data.data.extract b (b + (e - b)) := by
    simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.data_empty, ByteArray.size_data,
      Array.extract_zero, Array.empty_append, Array.extract_empty, Array.append_empty]
  rw [h1, Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]

/-- Extracting `[0, data.size)` returns `data`. -/
theorem byteArray_extract_zero_size (data : ByteArray) :
    data.extract 0 data.size = data := by
  apply ByteArray.ext
  apply Array.ext'
  rw [byteArray_extract_toList]
  have hSz : data.size = data.data.toList.length := rfl
  rw [hSz, List.drop_zero, Nat.sub_zero, List.take_length]

/-- Adjacent `ByteArray.extract` slices concatenate seamlessly. -/
theorem byteArray_extract_append (data : ByteArray) {off mid stop : Nat}
    (h1 : off ≤ mid) (h2 : mid ≤ stop) :
    data.extract off mid ++ data.extract mid stop = data.extract off stop := by
  apply ByteArray.ext
  apply Array.ext'
  have hApp : (data.extract off mid ++ data.extract mid stop).data.toList =
      (data.extract off mid).data.toList ++ (data.extract mid stop).data.toList := by
    simp only [ByteArray.data_append, Array.toList_append]
  rw [hApp, byteArray_extract_toList, byteArray_extract_toList, byteArray_extract_toList]
  have hDrop : data.data.toList.drop mid = (data.data.toList.drop off).drop (mid - off) := by
    rw [List.drop_drop]
    congr 1; omega
  have hTake : (data.data.toList.drop off).take (mid - off) ++
      ((data.data.toList.drop off).drop (mid - off)).take (stop - mid) =
      (data.data.toList.drop off).take ((mid - off) + (stop - mid)) :=
    (List.take_add (l := data.data.toList.drop off) (i := mid - off) (j := stop - mid)).symm
  rw [hDrop, hTake]
  congr 1; omega

/-- Prefix extraction of an extracted `ByteArray` slice collapses into a single `extract`. -/
theorem byteArray_extract_extract_zero (data : ByteArray) {off stop n : Nat}
    (hLe : off + n ≤ stop) :
    (data.extract off stop).extract 0 n = data.extract off (off + n) := by
  apply ByteArray.ext
  apply Array.ext'
  rw [byteArray_extract_toList, byteArray_extract_toList, byteArray_extract_toList]
  simp only [List.drop_zero, Nat.sub_zero, List.take_take]
  congr 1; omega

private theorem foldl_step_byteArray_init (f : KernelStep → ByteArray)
    (tr : List KernelStep) (init : ByteArray) :
    tr.foldl (fun acc s => acc ++ f s) init =
    init ++ tr.foldl (fun acc s => acc ++ f s) ByteArray.empty := by
  induction tr generalizing init with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons, byteArray_empty_append]
    rw [ih (init ++ f s), ih (f s), byteArray_append_assoc]

private def stepWrittenSlice (h : HandleId) : KernelStep → ByteArray
  | (.write hid chunk, .u32 n) => if hid == h then chunk.extract 0 n.toNat else ByteArray.empty
  | _ => ByteArray.empty

private theorem writtenBytesOn_eq_foldl (h : HandleId) (tr : List KernelStep) :
    writtenBytesOn h tr = tr.foldl (fun acc s => acc ++ stepWrittenSlice h s) ByteArray.empty := by
  have hStep : ∀ (acc : ByteArray) (s : KernelStep),
      (match s with
       | (.write hid chunk, .u32 n) => if hid == h then acc ++ chunk.extract 0 n.toNat else acc
       | _ => acc) = acc ++ stepWrittenSlice h s := by
    intro acc s
    rcases s with ⟨req, out⟩
    cases req <;> cases out <;> try (simp [stepWrittenSlice])
    rename_i hid chunk n
    split <;> simp
  unfold writtenBytesOn
  congr 1
  funext acc s
  exact hStep acc s

/-- `writtenBytesOn` distributes over trace append. -/
theorem writtenBytesOn_append (h : HandleId) (tr1 tr2 : List KernelStep) :
    writtenBytesOn h (tr1 ++ tr2) = writtenBytesOn h tr1 ++ writtenBytesOn h tr2 := by
  rw [writtenBytesOn_eq_foldl, writtenBytesOn_eq_foldl, writtenBytesOn_eq_foldl, List.foldl_append]
  exact foldl_step_byteArray_init (stepWrittenSlice h) tr2 _

/-- `writtenBytesOn` on a single `.write h chunk` returning `.u32 n`. -/
theorem writtenBytesOn_write_hit (h : HandleId) (chunk : ByteArray) (n : UInt32) :
    writtenBytesOn h [(.write h chunk, .u32 n)] = chunk.extract 0 n.toNat := by
  simp [writtenBytesOn]

/-- `writtenBytesOn` on any non-matching single step is empty. -/
theorem writtenBytesOn_step_miss (h : HandleId) (s : KernelStep)
    (hMiss : ∀ chunk n, s ≠ (.write h chunk, .u32 n)) :
    writtenBytesOn h [s] = ByteArray.empty := by
  rw [writtenBytesOn_eq_foldl]
  simp only [List.foldl_cons, List.foldl_nil, byteArray_empty_append]
  rcases s with ⟨req, out⟩
  cases req <;> cases out <;> try rfl
  rename_i hid chunk n
  by_cases hEq : (hid == h) = true
  · have : hid = h := beq_iff_eq.mp hEq
    subst this
    exact False.elim (hMiss chunk n rfl)
  · simp [stepWrittenSlice, hEq]

private def stepReadSlice (h : HandleId) : KernelStep → ByteArray
  | (.read hid _, .bytes chunk) => if hid == h then chunk else ByteArray.empty
  | _ => ByteArray.empty

private theorem readBytesOn_eq_foldl (h : HandleId) (tr : List KernelStep) :
    readBytesOn h tr = tr.foldl (fun acc s => acc ++ stepReadSlice h s) ByteArray.empty := by
  have hStep : ∀ (acc : ByteArray) (s : KernelStep),
      (match s with
       | (.read hid _, .bytes chunk) => if hid == h then acc ++ chunk else acc
       | _ => acc) = acc ++ stepReadSlice h s := by
    intro acc s
    rcases s with ⟨req, out⟩
    cases req <;> cases out <;> try (simp [stepReadSlice])
    rename_i hid cap chunk
    split <;> simp
  unfold readBytesOn
  congr 1
  funext acc s
  exact hStep acc s

/-- `readBytesOn` distributes over trace append. -/
theorem readBytesOn_append (h : HandleId) (tr1 tr2 : List KernelStep) :
    readBytesOn h (tr1 ++ tr2) = readBytesOn h tr1 ++ readBytesOn h tr2 := by
  rw [readBytesOn_eq_foldl, readBytesOn_eq_foldl, readBytesOn_eq_foldl, List.foldl_append]
  exact foldl_step_byteArray_init (stepReadSlice h) tr2 _

/-- `readBytesOn` on a single `.read h cap` returning `.bytes chunk`. -/
theorem readBytesOn_read_hit (h : HandleId) (cap : UInt32) (chunk : ByteArray) :
    readBytesOn h [(.read h cap, .bytes chunk)] = chunk := by
  simp [readBytesOn]

/-- `readBytesOn` on any non-matching single step is empty. -/
theorem readBytesOn_step_miss (h : HandleId) (s : KernelStep)
    (hMiss : ∀ cap chunk, s ≠ (.read h cap, .bytes chunk)) :
    readBytesOn h [s] = ByteArray.empty := by
  rw [readBytesOn_eq_foldl]
  simp only [List.foldl_cons, List.foldl_nil, byteArray_empty_append]
  rcases s with ⟨req, out⟩
  cases req <;> cases out <;> try rfl
  rename_i hid cap chunk
  by_cases hEq : (hid == h) = true
  · have : hid = h := beq_iff_eq.mp hEq
    subst this
    exact False.elim (hMiss cap chunk rfl)
  · simp [stepReadSlice, hEq]

private theorem verifyStep_nondet_u32 {s s1 : FilesState} {act : NondetAction} {extra : List Errno}
    {n : UInt32} (hV : verifyStep s (.nondet act extra) (.u32 n) = some s1) :
    verifyNondet s act (.u32 n) = some s1 := by
  cases hN : verifyNondet s act (.u32 n) with
  | none => simp [verifyStep, hN] at hV
  | some s2 => simp [verifyStep, hN] at hV; subst hV; rfl

private theorem verifyStep_writeDiscard_le {s s1 : FilesState} {len : Nat}
    {ex ex2 : List Errno} {nb : Bool} {n : UInt32}
    (hV : verifyStep s (.nondet (.writeDiscard len ex nb) ex2) (.u32 n) = some s1) :
    n.toNat ≤ len := by
  have hN := verifyStep_nondet_u32 hV
  unfold verifyNondet at hN; dsimp only at hN
  by_cases h0 : (len == 0) = true
  · simp only [h0, ↓reduceIte] at hN
    by_cases hn : (n.toNat == 0) = true
    · have := beq_iff_eq.mp hn; omega
    · simp [hn] at hN
  · simp only [h0] at hN
    by_cases hc : (decide (n.toNat ≥ 1) && decide (n.toNat ≤ len)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.2
    · simp [hc] at hN

private theorem verifyStep_writeReg_le {s s1 : FilesState} {hid : HandleId} {desc : OpenDesc}
    {ino : InodeId} {chunk : ByteArray} {sp ov ro cu : Bool} {ex : List Errno} {n : UInt32}
    (hV : verifyStep s (.nondet (.writeReg hid desc ino chunk sp ov ro cu) ex) (.u32 n) = some s1) :
    n.toNat ≤ chunk.size := by
  have hN := verifyStep_nondet_u32 hV
  unfold verifyNondet at hN; dsimp only at hN
  by_cases h0 : (chunk.size == 0) = true
  · simp only [h0, ↓reduceIte] at hN
    by_cases hn : (n.toNat == 0) = true
    · have := beq_iff_eq.mp hn; omega
    · simp [hn] at hN
  · simp only [h0] at hN
    cases hI : assocGet s.inodes ino with
    | none => rw [hI] at hN; simp at hN
    | some vn =>
      rw [hI] at hN; dsimp only at hN
      simp at hN
      have hLe := hN.1.2
      split at hLe
      all_goals
        split at hLe
        · exact hLe
        · exact Nat.le_trans hLe (Nat.min_le_left _ _)

private theorem healthyStep_write_to_verifyStep {env env' : HealthyEnv} {hid : HandleId}
    {chunk : ByteArray} {n : UInt32}
    (h : healthyStep env (.write hid chunk) (.u32 n) = some env') :
    ∃ s1, verifyStep env.state (evalReq env.state (.write hid chunk)) (.u32 n) = some s1 := by
  unfold healthyStep at h
  by_cases hWf : env.wf = true
  · have hSec : env.state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf; exact Bool.eq_false_iff.mpr (by simpa using hWf)
    have hVws : ∀ s1, verifyWithSeccomp env.state (.write hid chunk) (.u32 n) = some s1 →
        verifyStep env.state (evalReq env.state (.write hid chunk)) (.u32 n) = some s1 := by
      intro s1 hVw
      cases hVs : verifyStep env.state (evalReq env.state (.write hid chunk)) (.u32 n) with
      | none => simp [verifyWithSeccomp, hSec, hVs] at hVw
      | some s2 => simp [verifyWithSeccomp, hVs] at hVw; subst hVw; rfl
    simp only [hWf, Bool.not_true] at h
    cases hA : allowedStep env.state (.write hid chunk) (.u32 n) with
    | none => rw [hA] at h; cases h
    | some s2 =>
      unfold allowedStep at hA
      simp only [directHid?] at hA
      cases hG : assocGet env.state.fds hid with
      | none => rw [hG] at hA; dsimp only at hA; exact ⟨s2, hVws s2 hA⟩
      | some desc =>
        rw [hG] at hA; dsimp only at hA
        by_cases hUnc : (desc.closeState == FdCloseState.closeUncertain) = true
        · simp only [hUnc, ↓reduceIte, isOutcomeErr, Bool.false_eq_true] at hA
          cases hVw : verifyWithSeccomp env.state (.write hid chunk) (.u32 n) with
          | none => rw [hVw] at hA; cases hA
          | some s1 => exact ⟨s1, hVws s1 hVw⟩
        · simp only [hUnc, Bool.false_eq_true, ↓reduceIte] at hA
          exact ⟨s2, hVws s2 hA⟩
  · simp [hWf] at h

/-- Every healthy `.write hid chunk` returning `.u32 n` writes at most `chunk.size` bytes. -/
theorem healthyStep_write_le {env env' : HealthyEnv} {hid : HandleId} {chunk : ByteArray}
    {n : UInt32} (h : healthyStep env (.write hid chunk) (.u32 n) = some env') :
    n.toNat ≤ chunk.size := by
  obtain ⟨s1, hV⟩ := healthyStep_write_to_verifyStep h
  unfold evalReq at hV
  split at hV
  · simp [verifyStep, isOutcomeErr] at hV
  · dsimp only at hV
    unfold evalWrite at hV
    cases hG : assocGet env.state.fds hid with
    | none => rw [hG] at hV; simp [verifyStep, isOutcomeErr] at hV
    | some desc =>
      rw [hG] at hV; dsimp only at hV
      split at hV
      · simp [verifyStep] at hV
      · split at hV
        · exact verifyStep_writeDiscard_le hV
        · cases hI : assocGet env.state.inodes desc.ino with
          | none => rw [hI] at hV; simp [verifyStep] at hV
          | some vn =>
            rw [hI] at hV; dsimp only at hV
            cases hD : vn.data with
            | dir _ => rw [hD] at hV; simp [verifyStep] at hV
            | charDev dk =>
              rw [hD] at hV; dsimp only at hV
              split at hV
              · exact verifyStep_writeDiscard_le hV
              · cases dk with
                | fullDev => simp [verifyStep] at hV
                | nullDev | zeroDev => exact verifyStep_writeDiscard_le hV
                | whiteout | generic =>
                  dsimp only at hV
                  split at hV
                  · exact verifyStep_writeDiscard_le hV
                  · simp [verifyStep] at hV
            | fifo ring =>
              rw [hD] at hV; dsimp only at hV
              split at hV
              · split at hV
                · simp [verifyStep, outcomeEq] at hV
                  rw [hV.1]; exact Nat.zero_le _
                · simp [verifyStep] at hV
              · split at hV
                · simp [verifyStep, outcomeEq] at hV
                  rw [hV.1]; exact Nat.zero_le _
                · split at hV
                  · simp [verifyStep] at hV
                  · have hN := verifyStep_nondet_u32 hV
                    unfold verifyNondet at hN; dsimp only at hN
                    simp only [Option.ite_none_right_eq_some, Bool.and_eq_true, decide_eq_true_eq] at hN
                    have hLe := hN.1.2
                    split at hLe
                    · exact hLe
                    · exact Nat.le_trans hLe (Nat.min_le_left _ _)
            | reg d =>
              rw [hD] at hV; dsimp only at hV
              cases hPs : vn.isPseudo
              · simp only [hPs, Bool.false_eq_true, ↓reduceIte] at hV
                cases hSl : d.seals <;> rw [hSl] at hV <;> dsimp only at hV
                all_goals
                  cases hApp : desc.append <;> simp only [hApp, Bool.false_eq_true, ↓reduceIte] at hV
                  all_goals
                    split at hV
                    · simp [verifyStep] at hV
                    · split at hV
                      · simp [verifyStep] at hV
                      · exact verifyStep_writeReg_le hV
              · simp only [hPs, ↓reduceIte] at hV
                exact verifyStep_writeDiscard_le hV
            | symlink _ | socket | blockDev | other =>
              rw [hD] at hV; dsimp only at hV
              cases hPs : vn.isPseudo
              · simp only [hPs, Bool.false_eq_true, ↓reduceIte] at hV
                cases hApp : desc.append <;> simp only [hApp, Bool.false_eq_true, ↓reduceIte] at hV
                all_goals
                  split at hV
                  · simp [verifyStep] at hV
                  · split at hV
                    · simp [verifyStep] at hV
                    · exact verifyStep_writeReg_le hV
              · simp only [hPs, ↓reduceIte] at hV
                exact verifyStep_writeDiscard_le hV

/-- Extract a single verified `FilesReq` transition from `Core.ObeysStep` over `HealthyFilesCapM`. -/
theorem cap_fileReq_raw {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (req : FilesReq) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (execFilesReq cap.files req).run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env req p.1 = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq := by
  have h := hCap s (.fileReq req) hWf
  have hRun : ((execFilesCapStep cap (.fileReq req)).run s) =
      (FilesCapStepOut.fileOut (execFilesReq cap.files req |>.run s).1,
       (execFilesReq cap.files req |>.run s).2) := by
    simp [execFilesCapStep, Functor.map, StateT.map, StateT.run]
  rw [hRun] at h
  dsimp only [allowedFilesCapStep] at h
  exact ⟨h.2.2.2, h.2.1, h.2.2.1⟩

/-- Extract a single verified `nextTempSeq` transition from `Core.ObeysStep` over `HealthyFilesCapM`. -/
theorem cap_nextTempSeq {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := cap.nextTempSeq.run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).env = (proj s).env ∧
    p.1 = (proj s).tempSeq ∧
    (proj p.2).tempSeq = (proj s).tempSeq + 1 := by
  have h := hCap s .nextTempSeq hWf
  have hRun : ((execFilesCapStep cap .nextTempSeq).run s) =
      (FilesCapStepOut.tempSeq (cap.nextTempSeq.run s).1, (cap.nextTempSeq.run s).2) := by
    simp [execFilesCapStep, Functor.map, StateT.map, StateT.run]
  rw [hRun] at h
  dsimp only [allowedFilesCapStep] at h
  have hWf' : fsWorldWf (proj (cap.nextTempSeq.run s).2) = true := by
    unfold fsWorldWf; rw [h.2.1]; exact hWf
  exact ⟨hWf', h.2.1, h.2.2.1, h.2.2.2⟩

/-- Generic `retryEintr` trace lifting lemma for any single-attempt `FilesReq` wrapper. -/
theorem retryEintr_single_req {W α : Type} {proj : W → FsWorld}
    (act : StateM W (Except Errno α)) (req : FilesReq) (toOut : Except Errno α → FilesOutcome)
    (hAct : ∀ s, fsWorldWf (proj s) = true →
      let p := act.run s
      fsWorldWf (proj p.2) = true ∧
      healthyStep (proj s).env req (toOut p.1) = some (proj p.2).env ∧
      (proj p.2).tempSeq = (proj s).tempSeq)
    (hErr : ∀ e, toOut (.error e) = .err e)
    (fuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (retryEintr act fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trRetries : List KernelStep,
      HealthyFilesSteps (proj s).env (trRetries ++ [(req, toOut p.1)]) (proj p.2).env ∧
      (∀ step ∈ trRetries, step = (req, .err Errno.EINTR)) := by
  induction fuel generalizing s with
  | zero =>
    unfold retryEintr
    have h0 := hAct s hWf
    refine ⟨h0.1, h0.2.2, [], ?_, fun _ hm => by cases hm⟩
    simpa using healthyFilesSteps_single h0.2.1
  | succ f ih =>
    unfold retryEintr
    have h0 := hAct s hWf
    cases hR : (act s) with
    | mk res s1 =>
      change (act s) = (res, s1) at hR
      have h0' : fsWorldWf (proj s1) = true ∧
          healthyStep (proj s).env req (toOut res) = some (proj s1).env ∧
          (proj s1).tempSeq = (proj s).tempSeq := by
        simpa [StateT.run, hR] using h0
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases res with
      | ok v =>
        simp only [Pure.pure, StateT.pure]
        refine ⟨h0'.1, h0'.2.2, [], ?_, fun _ hm => by cases hm⟩
        simpa using healthyFilesSteps_single h0'.2.1
      | error e =>
        by_cases hEin : (e == Errno.EINTR) = true
        · have hEq : e = Errno.EINTR := beq_iff_eq.mp hEin
          subst hEq
          simp only [hEin, ↓reduceIte]
          obtain ⟨hWf2, hTmp2, trR, hSteps2, hAll2⟩ := ih h0'.1
          refine ⟨hWf2, hTmp2.trans h0'.2.2, (req, .err Errno.EINTR) :: trR, ?_, ?_⟩
          · have hStep0 : healthyStep (proj s).env req (.err Errno.EINTR) = some (proj s1).env := by
              rw [← hErr Errno.EINTR]; exact h0'.2.1
            exact HealthyFilesSteps.cons req (.err Errno.EINTR) _ hStep0 hSteps2
          · intro step hm
            simp only [List.mem_cons] at hm
            rcases hm with rfl | htl
            · rfl
            · exact hAll2 step htl
        · simp only [hEin, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
          refine ⟨h0'.1, h0'.2.2, [], ?_, fun _ hm => by cases hm⟩
          simpa using healthyFilesSteps_single h0'.2.1

/-- Every `TraceFds` step over a list of identical `EINTR` error steps preserves `held`. -/
theorem traceFds_eintr_retries {held : List HandleId} {req : FilesReq}
    (hNotClose : ∀ h, req ≠ .close h) {tr : List KernelStep}
    (hAll : ∀ step ∈ tr, step = (req, .err Errno.EINTR)) :
    TraceFds held tr held := by
  induction tr with
  | nil => exact TraceFds.nil held
  | cons s rest ih =>
    have hs : s = (req, .err Errno.EINTR) := hAll s (by simp)
    subst hs
    have hO : stepOpenedFd (req, .err Errno.EINTR) = none := by
      cases req <;> rfl
    have hC : stepClosedFd (req, .err Errno.EINTR) = none := by
      cases req with
      | close h => exact False.elim (hNotClose h rfl)
      | _ => rfl
    exact TraceFds.step (by simp [hO, hC]) (ih fun x hx => hAll x (by simp [hx]))

end LeanSwe.Fs.Proofs
