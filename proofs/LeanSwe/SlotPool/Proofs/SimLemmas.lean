import LeanSwe.SlotPool.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.SpecTests

namespace LeanSwe.SlotPool.Proofs

open Core Core.NondetTest LeanSwe.SlotPool.Model
open LeanSwe.Fs (FsApiM FsError FsErrorKind LockMode)
open LeanSwe.Time (TimeOpsM)

local notation "lpJoin" => slotLockPath simFs.join

/-- Unfold `StateM` bind evaluation into a two-step `let` binding. -/
theorem stateM_bind_run {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) : (x >>= f).run s = let (a, s') := x.run s; (f a).run s' := rfl
/-- Unfold `ExceptT` bind evaluation over `StateM`. -/
theorem exceptT_bind_run {E S α β : Type} (x : ExceptT E (StateM S) α) (f : α → ExceptT E (StateM S) β) (st : S) :
    (ExceptT.run (x >>= f)).run st = match (ExceptT.run x).run st with | (.error err, st') => (.error err, st') | (.ok a, st') => (ExceptT.run (f a)).run st' := by
  show ((ExceptT.run x) >>= ExceptT.bindCont f).run st = _; rw [stateM_bind_run]; cases (ExceptT.run x).run st with | mk r _ => cases r <;> rfl
/-- Unfold `NondetTest.assert` followed by a continuation in `AllPassRun`. -/
theorem allPass_assert {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) : (assert p >>= k) post = (p ∧ k () post) := rfl
/-- Unfold a trailing `NondetTest.assert` in `AllPassRun Unit`. -/
theorem allPass_assert_end (p : Prop) : (assert p : AllPassRun Unit) (fun _ => True) = (p ∧ True) := rfl
/-- Exact round-trip `(UInt32.ofNat c).toNat = c` for `c ≤ maxSleepChunkMs`. -/
theorem uint32_ofNat_toNat_of_le (c : Nat) (hc : c ≤ maxSleepChunkMs) : (UInt32.ofNat c).toNat = c := Nat.mod_eq_of_lt (by dsimp [maxSleepChunkMs, UInt32.size] at *; omega)
/-- Shift the initial accumulator out of `List.foldl (fun acc c => acc + c.toNat)`. -/
theorem foldl_add_shift : ∀ (cs : List UInt32) (init : Nat), cs.foldl (fun acc c => acc + c.toNat) init = init + cs.foldl (fun acc c => acc + c.toNat) 0
  | [], _ => by simp
  | _ :: cs, _ => by have := foldl_add_shift cs; grind
/-- Every chunk produced by `sleepChunksAux` is positive and the chunks sum to `ms`. -/
theorem sleepChunksAux_spec : ∀ (fuel ms : Nat), ms ≤ fuel * maxSleepChunkMs → (sleepChunksAux fuel ms).all (fun c => decide (0 < c.toNat)) = true ∧ (sleepChunksAux fuel ms).foldl (fun acc c => acc + c.toNat) 0 = ms
  | 0, 0, _ | _ + 1, 0, _ => by simp [sleepChunksAux]
  | 0, _ + 1, h => by omega
  | f + 1, m + 1, h => by
    simp only [sleepChunksAux, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.foldl_cons, Nat.zero_add]; let c := (m + 1).min maxSleepChunkMs
    have hTo := uint32_ofNat_toNat_of_le c (Nat.min_le_right _ _); have hLe : c ≤ m + 1 := Nat.min_le_left _ _
    have ⟨hAll, hSum⟩ := sleepChunksAux_spec f (m + 1 - c) (by dsimp only [c, maxSleepChunkMs] at h ⊢; change m + 1 - min (m + 1) 4294967295 ≤ _; omega)
    rw [foldl_add_shift, hSum, hTo]; exact ⟨⟨Nat.lt_min.mpr ⟨Nat.zero_lt_succ m, by decide⟩, hAll⟩, by omega⟩
/-- Every chunk produced by `sleepChunks ms` is positive and the chunks sum to `ms`. -/
theorem sleepChunks_spec (ms : Nat) : (sleepChunks ms).all (fun c => decide (0 < c.toNat)) = true ∧ (sleepChunks ms).foldl (fun acc c => acc + c.toNat) 0 = ms := sleepChunksAux_spec _ ms (by dsimp [maxSleepChunkMs]; omega)
/-- Running `runSleepChunks (liftTimeFirst time) cs` leaves `aux` unchanged. -/
theorem runSleepChunks_liftTimeFirst {S Aux : Type} (time : TimeOpsM (StateM S)) : ∀ (cs : List UInt32) (st : S) (aux : Aux), (runSleepChunks (liftTimeFirst time) cs).run (st, aux) = let ((), st') := (runSleepChunks time cs).run st; ((), (st', aux))
  | [], _, _ => rfl
  | c :: cs, st, aux => by unfold runSleepChunks; rw [stateM_bind_run, stateM_bind_run]; cases hs : (time.sleep c).run st with | mk _ st1 => rw [show ((liftTimeFirst (Aux := Aux) time).sleep c).run (st, aux) = ((), (st1, aux)) by change (let (a, s') := (time.sleep c).run st; (a, (s', aux))) = _; rw [hs]]; exact runSleepChunks_liftTimeFirst time cs st1 aux
/-- Executing `runSleepChunks simTime cs` advances `monoNanos` by the chunk sum and appends `cs` to `sleepLog`. -/
theorem runSleepChunks_simTime : ∀ (cs : List UInt32) (s : PoolSimState), (runSleepChunks simTime cs).run s = ((), { s with monoNanos := s.monoNanos + (cs.foldl (fun acc c => acc + c.toNat) 0) * nanosecondsPerMs, sleepLog := s.sleepLog ++ cs.toArray })
  | [], _ => by simp [runSleepChunks]; rfl
  | c :: rest, s => by
    unfold runSleepChunks; rw [stateM_bind_run]; change (runSleepChunks simTime rest).run { s with monoNanos := s.monoNanos + c.toNat * nanosecondsPerMs, sleepLog := s.sleepLog.push c } = _
    rw [runSleepChunks_simTime rest]; simp only [List.foldl_cons, Nat.zero_add, foldl_add_shift rest c.toNat]; congr 2; · rw [Nat.add_mul, Nat.add_assoc]
    · exact Array.ext' (by simp)
/-- Executing `runSleepChunks simTime (sleepChunks ms)` advances `monoNanos` by `ms * nanosecondsPerMs`. -/
theorem runSleepChunks_simTime_sleepChunks (ms : Nat) (s : PoolSimState) : (runSleepChunks simTime (sleepChunks ms)).run s = ((), { s with monoNanos := s.monoNanos + ms * nanosecondsPerMs, sleepLog := s.sleepLog ++ (sleepChunks ms).toArray }) := by rw [runSleepChunks_simTime, (sleepChunks_spec ms).2]
/-- Invalid `PoolConfig` values fail `validatePoolConfig` with `.invalidInput`, `path = some cfg.poolDir`, and a non-empty message. -/
theorem validatePoolConfig_of_false (cfg : PoolConfig) (h : validPoolConfig cfg = false) : ∃ e, validatePoolConfig cfg = .error e ∧ e.kind = .invalidInput ∧ e.path = some cfg.poolDir ∧ e.message ≠ "" := by
  unfold validPoolConfig at h; unfold validatePoolConfig; cases hD : validPoolDir cfg.poolDir <;> simp only [hD] at h ⊢; simp; cases hS : cfg.totalSlots <;> cases hP : cfg.pollIntervalMs <;> simp_all
/-- Valid `PoolConfig` values pass `validatePoolConfig` and satisfy all positive numeric bounds. -/
theorem validatePoolConfig_of_true (cfg : PoolConfig) (h : validPoolConfig cfg = true) : validatePoolConfig cfg = .ok cfg ∧ validPoolDir cfg.poolDir = true ∧ 1 ≤ cfg.totalSlots ∧ 1 ≤ cfg.pollIntervalMs := by
  simp only [validPoolConfig, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨by unfold validatePoolConfig; simp [h.1.1, show cfg.totalSlots ≠ 0 by omega, show cfg.pollIntervalMs ≠ 0 by omega], h.1.1, h.1.2, h.2⟩
/-- `mapFsError fe` always yields a non-empty diagnostic message. -/
theorem mapFsError_nonEmpty (fe : FsError) : (mapFsError fe).message ≠ "" := by unfold mapFsError; dsimp only; split; decide; next h => intro e; exact h (by simp [e])

private def parseDecAcc (acc : Nat) : List Char → Nat | [] => acc | c :: cs => parseDecAcc (acc * 10 + (c.toNat - 48)) cs
private theorem decDigitChar_val {k : Nat} (hk : k < 10) : (decDigitChar k).toNat - 48 = k ∧ decDigitChar k ≠ '/' ∧ decDigitChar k ≠ Char.ofNat 0 := (show ∀ x : Fin 10, (decDigitChar x.1).toNat - 48 = x.1 ∧ decDigitChar x.1 ≠ '/' ∧ decDigitChar x.1 ≠ Char.ofNat 0 by decide) ⟨k, hk⟩
private theorem parseDecAcc_natDecCharsAux : ∀ (fuel n : Nat) (ds : List Char), n < fuel → parseDecAcc 0 (natDecCharsAux fuel n ds) = parseDecAcc n ds
  | 0, _, _, _ => by omega
  | f + 1, n, ds, hf => by unfold natDecCharsAux; dsimp only; have hd := (decDigitChar_val (k := n % 10) (by omega)).1; split <;> (next hq => simp only [beq_iff_eq] at hq; first | (change parseDecAcc (0 * 10 + ((decDigitChar (n % 10)).toNat - 48)) ds = _; rw [Nat.zero_mul, Nat.zero_add, hd, show n % 10 = n by omega]) | (rw [parseDecAcc_natDecCharsAux f (n / 10) _ (by omega)]; change parseDecAcc (n / 10 * 10 + ((decDigitChar (n % 10)).toNat - 48)) ds = _; rw [hd, show n / 10 * 10 + n % 10 = n by omega]))
private theorem natDecCharsAux_good : ∀ (fuel n : Nat) (ds : List Char), (∀ c ∈ ds, c ≠ '/' ∧ c ≠ Char.ofNat 0) → ∀ c ∈ natDecCharsAux fuel n ds, c ≠ '/' ∧ c ≠ Char.ofNat 0
  | 0, _, _, hds => hds
  | f + 1, n, ds, hds => by simp only [natDecCharsAux]; have hds' : ∀ c ∈ decDigitChar (n % 10) :: ds, c ≠ '/' ∧ c ≠ Char.ofNat 0 := fun c hc => (List.mem_cons.mp hc).elim (· ▸ (decDigitChar_val (by omega)).2) (hds c); split; exact hds'; exact natDecCharsAux_good f (n / 10) _ hds'
private theorem slotFileName_toList (i : Nat) : (slotFileName i).toList = ['s', 'l', 'o', 't', '-'] ++ natDecCharsAux (i + 1) i [] ++ ['.', 'l', 'o', 'c', 'k'] := by unfold slotFileName natDecString; simp [String.toList_append, String.toList_ofList]
/-- `slotFileName` is injective on slot indices. -/
theorem slotFileName_inj {i j : Nat} (h : slotFileName i = slotFileName j) : i = j := by
  have hL := congrArg String.toList h; rw [slotFileName_toList, slotFileName_toList, List.append_assoc, List.append_assoc] at hL; have ha := parseDecAcc_natDecCharsAux (i + 1) i [] (Nat.lt_succ_self i); rw [List.append_cancel_right (List.append_cancel_left hL)] at ha; exact ha.symm.trans (parseDecAcc_natDecCharsAux (j + 1) j [] (Nat.lt_succ_self j))
private theorem str_ext_toList {s1 s2 : String} (h : s1.toList = s2.toList) : s1 = s2 := (@String.ofList_toList s1).symm.trans ((congrArg String.ofList h).trans (@String.ofList_toList s2))
private theorem hasNulChar_false_iff : ∀ (cs : List Char), hasNulChar cs = false ↔ ∀ c ∈ cs, c ≠ Char.ofNat 0
  | [] => by simp [hasNulChar]
  | _ :: cs => by simp [hasNulChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne, hasNulChar_false_iff cs]
private theorem trimTrailingSlashesRev_props (cs : List Char) : (cs ≠ [] → trimTrailingSlashesRev cs ≠ []) ∧ (trimTrailingSlashesRev cs).length ≤ cs.length ∧ (∀ c ∈ trimTrailingSlashesRev cs, c ∈ cs) ∧ (trimTrailingSlashesRev cs = ['/'] ∨ ∀ rest, trimTrailingSlashesRev cs ≠ '/' :: rest) := by
  induction cs with | nil => simp [trimTrailingSlashesRev] | cons c rest ih => unfold trimTrailingSlashesRev; cases rest <;> grind
/-- `normSimPath` is idempotent on all path strings. -/
theorem normSimPath_idempotent (p : String) : normSimPath (normSimPath p) = normSimPath p := by
  unfold normSimPath; rw [String.toList_ofList, List.reverse_reverse]; rcases (trimTrailingSlashesRev_props p.toList.reverse).2.2.2 with hRoot | hNo; · rw [hRoot]; rfl
  · cases hRev : trimTrailingSlashesRev p.toList.reverse with | nil => rfl | cons x xs => have hx : x ≠ '/' := fun h => hNo xs (h ▸ hRev); simp only [trimTrailingSlashesRev, beq_false_of_ne hx, Bool.false_eq_true, ↓reduceIte]
private theorem dropUntilSlashRev_noSlash : ∀ (xs pre : List Char), (∀ c ∈ xs, c ≠ '/') → dropUntilSlashRev (xs ++ '/' :: pre) = some pre
  | [], _, _ => rfl
  | c :: xs, pre, hNo => by simp only [List.cons_append, dropUntilSlashRev, beq_false_of_ne (hNo c (.head _)), Bool.false_eq_true, ↓reduceIte]; exact dropUntilSlashRev_noSlash xs pre fun x hx => hNo x (.tail _ hx)
private theorem dropUntilSlashRev_lt_len (xs res : List Char) (h : dropUntilSlashRev xs = some res) : res.length < xs.length := by induction xs with | nil => cases h | cons c rest ih => unfold dropUntilSlashRev at h; grind
/-- Any parent path returned by `parentSimPath p` is normalized and strictly shorter than `normSimPath p`. -/
theorem parentSimPath_props {p par : String} (h : parentSimPath p = some par) : normSimPath par = par ∧ par.toList.length < (normSimPath p).toList.length := by
  unfold parentSimPath at h; dsimp only at h; by_cases h0 : ((normSimPath p).isEmpty || normSimPath p == "/") = true; · simp [h0] at h
  · simp only [h0] at h; cases hd : dropUntilSlashRev (normSimPath p).toList.reverse with | none => simp [hd] at h | some revPar =>
    simp only [hd] at h; have hLt := dropUntilSlashRev_lt_len _ _ hd; rw [List.length_reverse] at hLt; cases revPar with
    | nil => injection h with hPar; subst hPar; refine ⟨rfl, ?_⟩; change 1 < (normSimPath p).toList.length; match hL : (normSimPath p).toList with | [] | ['/'] => exact absurd (by rw [← String.ofList_toList (s := normSimPath p), hL]; rfl) h0 | [a] => rw [hL] at hd; have ha : a ≠ '/' := fun e => h0 (by rw [← String.ofList_toList (s := normSimPath p), hL, e]; rfl); simp [dropUntilSlashRev, beq_false_of_ne ha] at hd | _ :: _ :: _ => simp
    | cons r0 rtail => injection h with hPar; subst hPar; refine ⟨normSimPath_idempotent _, ?_⟩; unfold normSimPath; rw [String.toList_ofList, List.length_reverse, String.toList_ofList, List.reverse_reverse]; exact Nat.lt_of_le_of_lt (trimTrailingSlashesRev_props (r0 :: rtail)).2.1 hLt
private theorem normSimPath_of_last_k {s : String} {xs : List Char} (h : s.toList.reverse = 'k' :: xs) : normSimPath s = s ∧ s.isEmpty = false ∧ (s == "/") = false ∧ s ≠ "ran-other" ∧ s ≠ "ran-expired" :=
  ⟨(by unfold normSimPath; rw [h]; simp only [trimTrailingSlashesRev, show ('k' == '/') = false by decide, Bool.false_eq_true, ↓reduceIte]; rw [← h, List.reverse_reverse, String.ofList_toList]), (by cases hb : s.isEmpty with | false => rfl | true => rw [String.isEmpty_iff.mp hb] at h; cases h), beq_false_of_ne (fun e => by rw [e] at h; cases h), (fun e => by rw [e] at h; cases h), (fun e => by rw [e] at h; cases h)⟩
private theorem slotLockPath_expand {p : String} (hV : validPoolDir p = true) (i : Nat) : (normSimPath p).toList ≠ [] ∧ ∃ pre, (lpJoin p i).toList = pre ++ '/' :: (slotFileName i).toList ∧ (normSimPath p = "/" ∧ pre = [] ∨ normSimPath p ≠ "/" ∧ pre = (normSimPath p).toList) := by
  simp only [validPoolDir, Bool.and_eq_true, Bool.not_eq_true'] at hV; have hDirNe : p.toList ≠ [] := fun hem => by have : p = "" := str_ext_toList hem; subst this; cases hV.1
  have hNbNe : (normSimPath p).toList ≠ [] := by unfold normSimPath; rw [String.toList_ofList]; exact fun hem => (trimTrailingSlashesRev_props p.toList.reverse).1 (by simp [hDirNe]) (List.reverse_eq_iff.mp hem)
  have hNbEmptyF : (normSimPath p).isEmpty = false := by cases hb : (normSimPath p).isEmpty; rfl; exact absurd (congrArg String.toList (String.isEmpty_iff.mp hb)) hNbNe
  have hNormF : normSimPath (slotFileName i) = slotFileName i := (normSimPath_of_last_k (show ∃ xs, (slotFileName i).toList.reverse = 'k' :: xs by rw [slotFileName_toList, List.reverse_append, List.reverse_cons]; exact ⟨_, rfl⟩).choose_spec).1
  have hHeadF : ((slotFileName i).toList.head? == some '/') = false := by rw [slotFileName_toList]; rfl
  have hEq : lpJoin p i = if normSimPath p == "/" then "/" ++ slotFileName i else normSimPath p ++ "/" ++ slotFileName i := by have hJ : simFs.join = simJoin := rfl; unfold slotLockPath; rw [hJ]; unfold simJoin; simp only [hNormF, hHeadF, hNbEmptyF, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hNbNe, ?_⟩; rw [hEq]; by_cases hS : normSimPath p = "/"; · exact ⟨[], by simp [hS, String.toList_append], Or.inl ⟨hS, rfl⟩⟩
  · exact ⟨(normSimPath p).toList, by simp [beq_false_of_ne hS, String.toList_append], Or.inr ⟨hS, rfl⟩⟩
/-- Structural invariants of `slotLockPath simFs.join poolDir i` for any valid `poolDir`. -/
theorem slotLockPath_props {poolDir : String} (hValid : validPoolDir poolDir = true) (i : Nat) : let lp := slotLockPath simFs.join poolDir i; let nb := normSimPath poolDir; normSimPath lp = lp ∧ validPoolDir lp = true ∧ parentSimPath lp = some nb ∧ nb.toList.length < lp.toList.length ∧ lp ≠ "ran-other" ∧ lp ≠ "ran-expired" := by
  dsimp only; obtain ⟨hNbNe, pre, hLpList, hPre⟩ := slotLockPath_expand hValid i
  have hSubAll : ∀ c ∈ (slotFileName i).toList, c ≠ '/' ∧ c ≠ Char.ofNat 0 := fun c hc => by rw [slotFileName_toList] at hc; simp only [List.mem_append] at hc; rcases hc with (hP | hM) | hS; exact (show ∀ x ∈ ['s', 'l', 'o', 't', '-'], x ≠ '/' ∧ x ≠ Char.ofNat 0 by decide) c hP; exact natDecCharsAux_good (i + 1) i [] (fun _ h => nomatch h) c hM; exact (show ∀ x ∈ ['.', 'l', 'o', 'c', 'k'], x ≠ '/' ∧ x ≠ Char.ofNat 0 by decide) c hS
  obtain ⟨hNormLp, hLpEmpty, hNotRoot, hNe1, hNe2⟩ := normSimPath_of_last_k (show ∃ xs, (lpJoin poolDir i).toList.reverse = 'k' :: xs by rw [hLpList, slotFileName_toList, List.reverse_append, List.reverse_cons, List.reverse_append, List.reverse_append]; exact ⟨_, rfl⟩).choose_spec
  have hLpNoNul : hasNulChar (lpJoin poolDir i).toList = false := by
    rw [hasNulChar_false_iff, hLpList]; intro c hc; rcases List.mem_append.mp hc with h1 | h2
    · rcases hPre with ⟨_, rfl⟩ | ⟨_, rfl⟩; cases h1; unfold normSimPath at h1; rw [String.toList_ofList] at h1; exact (hasNulChar_false_iff _).mp (by simp only [validPoolDir, Bool.and_eq_true, Bool.not_eq_true'] at hValid; exact hValid.2) c (List.mem_reverse.mp ((trimTrailingSlashesRev_props _).2.2.1 c (List.mem_reverse.mp h1)))
    · rcases List.mem_cons.mp h2 with rfl | hSub; decide; exact (hSubAll c hSub).2
  have hParent : parentSimPath (lpJoin poolDir i) = some (normSimPath poolDir) := by
    unfold parentSimPath; rw [hNormLp]; simp only [hLpEmpty, hNotRoot, Bool.or_self, Bool.false_eq_true, ↓reduceIte]; rw [show (lpJoin poolDir i).toList.reverse = (slotFileName i).toList.reverse ++ '/' :: pre.reverse by rw [hLpList, List.reverse_append, List.reverse_cons, List.append_assoc]; rfl, dropUntilSlashRev_noSlash _ _ (fun c hc => (hSubAll c (List.mem_reverse.mp hc)).1)]
    rcases hPre with ⟨hS, rfl⟩ | ⟨_, rfl⟩; exact congrArg some hS.symm; cases hR : (normSimPath poolDir).toList.reverse with | nil => exact absurd (List.reverse_eq_nil_iff.mp hR) hNbNe | cons _ _ => dsimp only; rw [← hR, List.reverse_reverse, String.ofList_toList]; exact congrArg some (normSimPath_idempotent poolDir)
  refine ⟨hNormLp, by simp [validPoolDir, hLpEmpty, hLpNoNul], hParent, ?_, hNe1, hNe2⟩; rw [hLpList, slotFileName_toList]; rcases hPre with ⟨hS, rfl⟩ | ⟨_, rfl⟩; simp [show (normSimPath poolDir).toList.length = 1 by rw [hS]; rfl]; simp
/-- `slotLockPath simFs.join poolDir` is injective on slot indices when `validPoolDir poolDir = true`. -/
theorem slotLockPath_inj {poolDir : String} (hValid : validPoolDir poolDir = true) {i j : Nat} (h : slotLockPath simFs.join poolDir i = slotLockPath simFs.join poolDir j) : i = j := by
  obtain ⟨_, p1, h1, hp1⟩ := slotLockPath_expand hValid i; obtain ⟨_, p2, h2, hp2⟩ := slotLockPath_expand hValid j; have hEq : p1 = p2 := by grind
  have hL := congrArg String.toList h; rw [h1, h2, hEq] at hL; exact slotFileName_inj (str_ext_toList (List.cons.inj (List.append_cancel_left hL)).2)

private theorem ensureSimDirChain_clean (maxLen : Nat) : ∀ (fuel : Nat) (s : PoolSimState) (np : String), s.files = [] → s.symlinks = [] → normSimPath np = np → np.toList.length < fuel → np.toList.length ≤ maxLen → (∀ d ∈ s.dirs, d.toList.length ≤ maxLen) → ∃ dirs', ensureSimDirChain fuel s np = .ok { s with dirs := dirs' } ∧ np ∈ dirs' ∧ ∀ d ∈ dirs', d.toList.length ≤ maxLen
  | 0, _, _, _, _, _, _, _, _ => by omega
  | fuel + 1, s, np, hF, hSy, hNorm, hLt, hMax, hD => by
    unfold ensureSimDirChain; simp only [show (hasSimFile s np || decide (np ∈ s.symlinks)) = false by simp [hasSimFile, hF, hSy], Bool.false_eq_true, ↓reduceIte]
    by_cases hIn : np ∈ s.dirs; exact ⟨s.dirs, by simp [hIn], hIn, hD⟩; simp only [hIn, ↓reduceIte]; cases hPar : parentSimPath np with
    | none => exact ⟨np :: s.dirs, rfl, .head _, fun d hd => (List.mem_cons.mp hd).elim (· ▸ hMax) (hD d)⟩
    | some par => obtain ⟨hPN, hPL⟩ := parentSimPath_props hPar; rw [hNorm] at hPL; obtain ⟨d1, hRec, _, hD1⟩ := ensureSimDirChain_clean maxLen fuel s par hF hSy hPN (by omega) (by omega) hD; dsimp only; rw [hRec]; dsimp only; by_cases hIn1 : np ∈ d1; exact ⟨d1, by simp [hIn1], hIn1, hD1⟩; exact ⟨np :: d1, by simp [hIn1], .head _, fun d hd => (List.mem_cons.mp hd).elim (· ▸ hMax) (hD1 d)⟩
/-- Exact evaluation equation for `simFs.mkdir`. -/
theorem simFs_mkdir_run (s : PoolSimState) (p : String) (parents existOk : Bool) : (simFs.mkdir p parents existOk).run s = match simMkdirPure s p parents existOk with | .error e => (.error e, s) | .ok s' => (.ok (), s') := by dsimp only [simFs]; rw [stateM_bind_run, show (get : StateM PoolSimState PoolSimState).run s = (s, s) from rfl]; dsimp only; cases simMkdirPure s p parents existOk <;> rfl
/-- Exact evaluation equation for `simFs.tryWithFileLock`. -/
theorem simFs_tryWithFileLock_run {α : Type} (s : PoolSimState) (p : String) (mode : LockMode) (createIfMissing : Bool) (action : StateM PoolSimState (Except FsError α)) :
    (simFs.tryWithFileLock p mode createIfMissing action).run s = match simTryAcquirePure s p mode createIfMissing with | .error e => (.error e, s) | .ok none => (.ok none, s) | .ok (some sLocked) => let np := normSimPath p; let (r, s') := action.run sLocked; (r.map some, { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }) := by
  dsimp only [simFs]; rw [stateM_bind_run, show (get : StateM PoolSimState PoolSimState).run s = (s, s) from rfl]; dsimp only; cases simTryAcquirePure s p mode createIfMissing with | error _ => rfl | ok opt => cases opt with | none => rfl | some sL => dsimp only; rw [stateM_bind_run, show (set sL : StateM PoolSimState Unit).run s = ((), sL) from rfl]; dsimp only; rw [stateM_bind_run]; cases action.run sL with | mk _ _ => rfl
/-- Exact evaluation equation for `simFsEx.mkdir`. -/
theorem simFsEx_mkdir_run (s : PoolSimState) (p : String) (parents existOk : Bool) : (ExceptT.run (simFsEx.mkdir p parents existOk)).run s = match (simFs.mkdir p parents existOk).run s with | (res, s') => (.ok res, s') := rfl
/-- Exact evaluation equation for `simFsEx.tryWithFileLock`. -/
theorem simFsEx_tryWithFileLock_run {α : Type} (s : PoolSimState) (p : String) (mode : LockMode) (createIfMissing : Bool) (action : ExceptT String (StateM PoolSimState) (Except FsError α)) :
    (ExceptT.run (simFsEx.tryWithFileLock p mode createIfMissing action)).run s = match simTryAcquirePure s p mode createIfMissing with
      | .error e => (.ok (.error e), s) | .ok none => (.ok (.ok none), s)
      | .ok (some sLocked) => let np := normSimPath p; match (ExceptT.run action).run sLocked with | (.error ex, sAfter) => (.error ex, { sAfter with heldLocks := removeFirstSimLock np mode sAfter.heldLocks }) | (.ok r, sAfter) => (.ok (r.map some), { sAfter with heldLocks := removeFirstSimLock np mode sAfter.heldLocks }) := by
  dsimp only [simFsEx]; rw [exceptT_bind_run, show (ExceptT.run (get : ExceptT String (StateM PoolSimState) PoolSimState)).run s = (.ok s, s) from rfl]; dsimp only
  cases simTryAcquirePure s p mode createIfMissing with | error _ => rfl | ok opt => cases opt with | none => rfl | some sL => dsimp only; rw [exceptT_bind_run, show (ExceptT.run (liftM (set sL : StateM PoolSimState Unit) : ExceptT String (StateM PoolSimState) Unit)).run s = (.ok (), sL) from rfl]; dsimp only [tryFinally', MonadFinally.tryFinally']; rw [exceptT_bind_run]; dsimp only [ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]; cases action sL with | mk r _ => cases r <;> rfl
/-- `simFs.mkdir poolDir true true` succeeds on a clean simulation state and installs `normSimPath poolDir` without exceeding its length. -/
theorem simMkdir_clean (s : PoolSimState) (poolDir : String) (hFail : s.failMkdirWith = none) (hFiles : s.files = []) (hSyms : s.symlinks = []) (hValid : validPoolDir poolDir = true) (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length) :
    ∃ s', (simFs.mkdir poolDir true true).run s = (.ok (), s') ∧ s'.files = [] ∧ s'.symlinks = [] ∧ s'.heldLocks = s.heldLocks ∧ s'.externalLeases = s.externalLeases ∧ s'.failMkdirWith = none ∧ s'.monoNanos = s.monoNanos ∧ s'.sleepLog = s.sleepLog ∧ normSimPath poolDir ∈ s'.dirs ∧ ∀ d ∈ s'.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length := by
  let np := normSimPath poolDir; rw [simFs_mkdir_run]
  have hMkPure : simMkdirPure s poolDir true true = if np ∈ s.dirs then .ok s else ensureSimDirChain (np.toList.length + 1) s np := by
    unfold simMkdirPure; rw [hFail]; dsimp only; have hOr : (hasSimFile s np || decide (np ∈ s.symlinks)) = false := by simp [hasSimFile, hFiles, hSyms]
    change (if (!validPoolDir poolDir) = true then _ else if (hasSimFile s np || decide (np ∈ s.symlinks)) = true then _ else if np ∈ s.dirs then _ else _) = _
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hOr]; by_cases hIn : np ∈ s.dirs <;> simp [hIn, np]
  rw [hMkPure]; by_cases hIn : np ∈ s.dirs; exact ⟨s, by simp [hIn], hFiles, hSyms, rfl, rfl, hFail, rfl, rfl, hIn, hDirsLen⟩
  obtain ⟨dirs', hEns, hMem, hD'⟩ := ensureSimDirChain_clean np.toList.length (np.toList.length + 1) s np hFiles hSyms (normSimPath_idempotent poolDir) (Nat.lt_succ_self _) (Nat.le_refl _) hDirsLen; exact ⟨{ s with dirs := dirs' }, by simp [hIn, hEns], hFiles, hSyms, rfl, rfl, hFail, rfl, rfl, hMem, hD'⟩
private theorem mem_nat_cons {α : Type} (f : Nat → α) (xs : Nat → List α) (h0 : xs 0 = []) (hs : ∀ n, xs (n + 1) = f n :: xs n) : ∀ n x, x ∈ xs n ↔ ∃ k < n, x = f k
  | 0, _ => by simp [h0]
  | n + 1, x => by have := mem_nat_cons f xs h0 hs n x; rw [hs]; grind
private theorem conflict_of_ext {s : PoolSimState} {p : String} {rel : Nat} (hMem : (p, rel) ∈ s.externalLeases) (hMono : s.monoNanos < rel) : hasSimLockConflict s p .exclusive = true := by unfold hasSimLockConflict; exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨(p, rel), hMem, by simp [hMono]⟩))
private theorem conflict_false_of_ext {s : PoolSimState} {np : String} (hHeld : s.heldLocks = []) (h : ∀ p r, (p, r) ∈ s.externalLeases → p = np → ¬ s.monoNanos < r) : hasSimLockConflict s np .exclusive = false := by simp only [hasSimLockConflict, hHeld, List.any_nil, Bool.false_or, List.any_eq_false, Prod.forall, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]; exact h
/-- In `leasesBeforeSlot`, slot `i < count` conflicts when `s.monoNanos < relAt`, and slot `count` is free when `heldLocks = []`. -/
theorem leasesBeforeSlot_conflict {s : PoolSimState} {poolDir : String} (hValid : validPoolDir poolDir = true) {relAt count : Nat} (hExt : s.externalLeases = leasesBeforeSlot simFs.join poolDir relAt count) :
    (∀ i, i < count → s.monoNanos < relAt → hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧ (s.heldLocks = [] → hasSimLockConflict s (slotLockPath simFs.join poolDir count) .exclusive = false) := by
  have hm := mem_nat_cons (fun k => (normSimPath (lpJoin poolDir k), relAt)) (leasesBeforeSlot simFs.join poolDir relAt) rfl (fun _ => rfl) count
  exact ⟨fun i hi hM => conflict_of_ext (by rw [hExt, hm]; exact ⟨i, hi, by rw [(slotLockPath_props hValid i).1]⟩) hM, fun hH => conflict_false_of_ext hH fun p r hMem hp _ => by rw [hExt, hm] at hMem; obtain ⟨k, hk, hEq⟩ := hMem; have hP := (Prod.mk.inj hEq).1; rw [(slotLockPath_props hValid k).1] at hP; rw [hP] at hp; have := slotLockPath_inj hValid hp; omega⟩
/-- In `leasesBeforeSlotUntil`, every slot `< count` conflicts before `min targetRel lockedUntil`, slots `< freeIdx` conflict before `lockedUntil`, and `freeIdx` is free once `targetRel ≤ s.monoNanos`. -/
theorem leasesBeforeSlotUntil_conflict {s : PoolSimState} {poolDir : String} (hValid : validPoolDir poolDir = true) {freeIdx targetRel lockedUntil count : Nat} (hExt : s.externalLeases = leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count) :
    (∀ i, i < count → i < freeIdx → s.monoNanos < lockedUntil → hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧ (∀ i, i < count → freeIdx ≤ i → s.monoNanos < targetRel → hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧ (s.heldLocks = [] → freeIdx < count → targetRel ≤ s.monoNanos → hasSimLockConflict s (slotLockPath simFs.join poolDir freeIdx) .exclusive = false) := by
  have hm := mem_nat_cons (fun k => (normSimPath (lpJoin poolDir k), if k < freeIdx then lockedUntil else targetRel)) (leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil) rfl (fun _ => rfl) count
  exact ⟨fun i hi hlt hM => conflict_of_ext (by rw [hExt, hm]; exact ⟨i, hi, by simp [(slotLockPath_props hValid i).1, hlt]⟩) hM,
    fun i hi hge hM => conflict_of_ext (by rw [hExt, hm]; exact ⟨i, hi, by simp [(slotLockPath_props hValid i).1, Nat.not_lt.mpr hge]⟩) hM,
    fun hH _ hGe => conflict_false_of_ext hH fun p r hMem hp => by rw [hExt, hm] at hMem; obtain ⟨k, _, hEq⟩ := hMem; obtain ⟨hP, hr⟩ := Prod.mk.inj hEq; rw [(slotLockPath_props hValid k).1] at hP; rw [hP] at hp; have hkEq := slotLockPath_inj hValid hp; subst hkEq; simp only [Nat.lt_irrefl, ↓reduceIte] at hr; rw [hr]; exact Nat.not_lt.mpr hGe⟩
section
variable (s : PoolSimState) (poolDir : String) (hValid : validPoolDir poolDir = true) (hFiles : s.files = []) (hSyms : s.symlinks = []) (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length) (i : Nat) (hPar : normSimPath poolDir ∈ s.dirs)
include hValid hFiles hSyms hDirsLen hPar
private theorem simTryAcquire_clean_unfold : simTryAcquirePure s (lpJoin poolDir i) .exclusive true = if hasSimLockConflict s (lpJoin poolDir i) .exclusive then .ok none else .ok (some { s with files := (lpJoin poolDir i, "") :: s.files, heldLocks := (lpJoin poolDir i, .exclusive) :: s.heldLocks }) := by
  obtain ⟨hNorm, hLpValid, hLpPar, hLpLen, _, _⟩ := slotLockPath_props hValid i; have hND : ¬ (lpJoin poolDir i ∈ s.dirs) := fun h => by have := hDirsLen _ h; omega
  unfold simTryAcquirePure; rw [hNorm]; simp only [hLpValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hND, hSyms, List.not_mem_nil, hasSimFile, hFiles, List.any_nil, hLpPar, hPar, decide_true]
/-- Attempting to acquire a conflicting exclusive lock on a clean state fails contention without modifying state. -/
theorem simTryAcquire_busy (hConflict : hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) : simTryAcquirePure s (slotLockPath simFs.join poolDir i) .exclusive true = .ok none := by rw [simTryAcquire_clean_unfold s poolDir hValid hFiles hSyms hDirsLen i hPar, hConflict]; rfl
/-- Attempting to acquire a free exclusive lock on a clean state creates the file and acquires the lock. -/
theorem simTryAcquire_free (hFree : hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = false) : simTryAcquirePure s (slotLockPath simFs.join poolDir i) .exclusive true = .ok (some { s with files := (slotLockPath simFs.join poolDir i, "") :: s.files, heldLocks := (slotLockPath simFs.join poolDir i, .exclusive) :: s.heldLocks }) := by rw [simTryAcquire_clean_unfold s poolDir hValid hFiles hSyms hDirsLen i hPar, hFree]; rfl
end
section
variable {s : PoolSimState} {lp : String} (hValid : validPoolDir lp = true) (hNorm : normSimPath lp = lp) (hNotDir : ¬ (lp ∈ s.dirs)) (hNotSym : ¬ (lp ∈ s.symlinks)) (hFile : hasSimFile s lp = true)
include hValid hNorm hNotDir hNotSym hFile
/-- Probing a lock file with `.shared` while holding `(lp, .exclusive)` returns `.ok none` without mutating state. -/
theorem simFs_sharedProbe_held (hHeld : (lp, LockMode.exclusive) ∈ s.heldLocks) : (simFs.tryWithFileLock lp .shared false (pure (.ok ()))).run s = (.ok none, s) := by
  have hEx : (LockMode.exclusive == LockMode.exclusive) = true := rfl; have hConf : hasSimLockConflict s lp .shared = true := by unfold hasSimLockConflict; exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨(lp, .exclusive), hHeld, by simp [hEx]⟩))
  rw [simFs_tryWithFileLock_run]; unfold simTryAcquirePure; rw [hNorm]; simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotDir, hNotSym, hFile, hConf]
/-- Probing an unlocked existing lock file with `.exclusive` and `createIfMissing = false` succeeds without changing `files` or `heldLocks`. -/
theorem simFs_postProbe_ok (hFree : hasSimLockConflict s lp .exclusive = false) : (simFs.tryWithFileLock lp .exclusive false (pure (.ok ()))).run s = (.ok (some ()), { s with heldLocks := removeFirstSimLock lp .exclusive ((lp, .exclusive) :: s.heldLocks) }) := by
  have hAcq : simTryAcquirePure s lp .exclusive false = .ok (some { s with heldLocks := (lp, .exclusive) :: s.heldLocks }) := by unfold simTryAcquirePure; rw [hNorm]; simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotDir, hNotSym, hFile, hFree]
  rw [simFs_tryWithFileLock_run, hAcq, hNorm]; rfl
end
/-- Removing `(lp, mode)` from `(lp, mode) :: xs` drops the head element without inspecting `lp` syntax. -/
theorem removeFirstSimLock_cons_self (lp : String) (mode : LockMode) (xs : List (String × LockMode)) : removeFirstSimLock lp mode ((lp, mode) :: xs) = xs := by
  have hm : (mode == mode) = true := by cases mode <;> rfl
  simp [removeFirstSimLock, show ((lp, mode) == (lp, mode)) = true by change (lp == lp && mode == mode) = true; simp [hm]]

theorem internal_hasNulChar_eq : ∀ cs, Internal.hasNulChar cs = Model.hasNulChar cs
  | [] => rfl
  | c :: cs => by simp [Internal.hasNulChar, Model.hasNulChar, internal_hasNulChar_eq cs]
theorem internal_validPoolDir_eq (p : String) : Internal.validPoolDir p = Model.validPoolDir p := by
  simp [Internal.validPoolDir, Model.validPoolDir, internal_hasNulChar_eq]
theorem internal_validatePoolConfig_eq (cfg : PoolConfig) : Internal.validatePoolConfig cfg = Model.validatePoolConfig cfg := by
  simp [Internal.validatePoolConfig, Model.validatePoolConfig, internal_validPoolDir_eq]
theorem internal_natDecCharsAux_eq : ∀ fuel n acc, Internal.natDecCharsAux fuel n acc = Model.natDecCharsAux fuel n acc
  | 0, _, _ => rfl
  | fuel + 1, n, acc => by
    unfold Internal.natDecCharsAux Model.natDecCharsAux Internal.decDigitChar Model.decDigitChar
    dsimp only; split
    · rfl
    · exact internal_natDecCharsAux_eq fuel (n / 10) _
theorem internal_slotFileName_eq (i : Nat) : Internal.slotFileName i = Model.slotFileName i := by
  simp [Internal.slotFileName, Model.slotFileName, Internal.natDecString, Model.natDecString, internal_natDecCharsAux_eq]
theorem internal_slotLockPath_eq (join : String → String → String) (p : String) (i : Nat) :
    Internal.slotLockPath join p i = Model.slotLockPath join p i := by
  simp [Internal.slotLockPath, Model.slotLockPath, internal_slotFileName_eq]
theorem internal_deadlineNanos_eq (s t : Nat) : Internal.deadlineNanos s t = Model.deadlineNanos s t := rfl
theorem internal_nextSleepMs_eq (p n d : Nat) : Internal.nextSleepMs p n d = Model.nextSleepMs p n d := rfl
theorem internal_maxForeverPolls_eq : Internal.maxForeverPolls = Model.maxForeverPolls := rfl
theorem internal_sleepChunksAux_eq : ∀ fuel ms, Internal.sleepChunksAux fuel ms = Model.sleepChunksAux fuel ms
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | fuel + 1, ms + 1 => by
    unfold Internal.sleepChunksAux Model.sleepChunksAux
    exact congrArg _ (internal_sleepChunksAux_eq fuel _)
theorem internal_sleepChunks_eq (ms : Nat) : Internal.sleepChunks ms = Model.sleepChunks ms :=
  internal_sleepChunksAux_eq _ ms
theorem internal_runSleepChunks_eq {m : Type → Type} [Monad m] (time : TimeOpsM m) :
    ∀ cs, Internal.runSleepChunks time cs = Model.runSleepChunks time cs
  | [] => rfl
  | c :: cs => by
    unfold Internal.runSleepChunks Model.runSleepChunks
    exact congrArg (time.sleep c >>= fun _ => ·) (internal_runSleepChunks_eq time cs)
theorem internal_mapFsError_eq (fe : FsError) : Internal.mapFsError fe = Model.mapFsError fe := by
  cases fe with | mk k p m => cases k <;> rfl
end LeanSwe.SlotPool.Proofs
