import LeanSwe.SlotPool.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.SpecTests

namespace LeanSwe.SlotPool.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model

/-- Unfold `StateM` bind evaluation into a two-step `let` binding. -/
theorem stateM_bind_run {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) :
    (x >>= f).run s = let (a, s') := x.run s; (f a).run s' := rfl

/-- Unfold `ExceptT` bind evaluation over `StateM`. -/
theorem exceptT_bind_run {E S α β : Type} (x : ExceptT E (StateM S) α)
    (f : α → ExceptT E (StateM S) β) (st : S) :
    (ExceptT.run (x >>= f)).run st =
      match (ExceptT.run x).run st with
      | (.error err, st') => (.error err, st')
      | (.ok a, st') => (ExceptT.run (f a)).run st' := by
  show ((ExceptT.run x) >>= ExceptT.bindCont f).run st = _
  rw [stateM_bind_run]
  cases hx : (ExceptT.run x).run st with
  | mk res st' =>
    cases res <;> rfl

/-- Unfold `NondetTest.assert` followed by a continuation in `AllPassRun`. -/
theorem allPass_assert {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) :
    (assert p >>= k) post = (p ∧ k () post) := rfl

/-- Unfold a trailing `NondetTest.assert` in `AllPassRun Unit`. -/
theorem allPass_assert_end (p : Prop) :
    (assert p : AllPassRun Unit) (fun _ => True) = (p ∧ True) := rfl

/-- Exact round-trip `(UInt32.ofNat c).toNat = c` for `c ≤ maxSleepChunkMs`. -/
theorem uint32_ofNat_toNat_of_le (c : Nat) (hc : c ≤ maxSleepChunkMs) :
    (UInt32.ofNat c).toNat = c := by
  have hlt : c < UInt32.size := by
    dsimp [maxSleepChunkMs, UInt32.size] at hc ⊢
    omega
  exact Nat.mod_eq_of_lt hlt

/-- Shift the initial accumulator out of `List.foldl (fun acc c => acc + c.toNat)`. -/
theorem foldl_add_shift (cs : List UInt32) (init : Nat) :
    cs.foldl (fun acc c => acc + c.toNat) init =
      init + cs.foldl (fun acc c => acc + c.toNat) 0 := by
  induction cs generalizing init with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + c.toNat), ih c.toNat]
    omega

/-- Every chunk produced by `sleepChunksAux` is positive and the chunks sum to `ms`. -/
theorem sleepChunksAux_spec (fuel ms : Nat) (h : ms ≤ fuel * maxSleepChunkMs) :
    (sleepChunksAux fuel ms).all (fun c => decide (0 < c.toNat)) = true ∧
    (sleepChunksAux fuel ms).foldl (fun acc c => acc + c.toNat) 0 = ms := by
  induction fuel generalizing ms with
  | zero =>
    have h0 : ms = 0 := by omega
    subst h0
    simp [sleepChunksAux]
  | succ f ih =>
    cases ms with
    | zero =>
      simp [sleepChunksAux]
    | succ m =>
      simp only [sleepChunksAux]
      have hcPos : 0 < (m + 1).min maxSleepChunkMs := by
        have hm : 0 < maxSleepChunkMs := by decide
        exact Nat.lt_min.mpr ⟨Nat.zero_lt_succ m, hm⟩
      have hcLe : (m + 1).min maxSleepChunkMs ≤ maxSleepChunkMs := Nat.min_le_right _ _
      have hToNat : (UInt32.ofNat ((m + 1).min maxSleepChunkMs)).toNat = (m + 1).min maxSleepChunkMs :=
        uint32_ofNat_toNat_of_le _ hcLe
      have hRem : m + 1 - (m + 1).min maxSleepChunkMs ≤ f * maxSleepChunkMs := by
        dsimp only [maxSleepChunkMs] at h
        change m + 1 - min (m + 1) 4294967295 ≤ f * 4294967295
        omega
      obtain ⟨hAll, hSum⟩ := ih (m + 1 - (m + 1).min maxSleepChunkMs) hRem
      constructor
      · simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        rw [hToNat]
        exact ⟨hcPos, hAll⟩
      · simp only [List.foldl_cons, Nat.zero_add]
        rw [foldl_add_shift, hSum, hToNat]
        have hLe : (m + 1).min maxSleepChunkMs ≤ m + 1 := Nat.min_le_left _ _
        omega

/-- Every chunk produced by `sleepChunks ms` is positive and the chunks sum to `ms`. -/
theorem sleepChunks_spec (ms : Nat) :
    (sleepChunks ms).all (fun c => decide (0 < c.toNat)) = true ∧
    (sleepChunks ms).foldl (fun acc c => acc + c.toNat) 0 = ms := by
  apply sleepChunksAux_spec
  dsimp [maxSleepChunkMs]
  omega

/-- Running `runSleepChunks (liftTimeFirst time) cs` leaves `aux` unchanged. -/
theorem runSleepChunks_liftTimeFirst {S Aux : Type} (time : TimeOpsM (StateM S))
    (cs : List UInt32) (st : S) (aux : Aux) :
    (runSleepChunks (liftTimeFirst time) cs).run (st, aux) =
      let ((), st') := (runSleepChunks time cs).run st
      ((), (st', aux)) := by
  induction cs generalizing st with
  | nil => rfl
  | cons c rest ih =>
    unfold runSleepChunks
    rw [stateM_bind_run, stateM_bind_run]
    cases hs : (time.sleep c).run st with
    | mk u st1 =>
      have hLift : ((liftTimeFirst (Aux := Aux) time).sleep c).run (st, aux) = (u, (st1, aux)) := by
        change (let (a, s') := (time.sleep c).run st; (a, (s', aux))) = _
        rw [hs]
      rw [hLift]
      dsimp only
      exact ih st1

/-- Executing `runSleepChunks simTime cs` advances `monoNanos` by the chunk sum and appends `cs` to `sleepLog`. -/
theorem runSleepChunks_simTime (cs : List UInt32) (s : PoolSimState) :
    (runSleepChunks simTime cs).run s =
      ((), { s with
        monoNanos := s.monoNanos + (cs.foldl (fun acc c => acc + c.toNat) 0) * nanosecondsPerMs
        sleepLog := s.sleepLog ++ cs.toArray }) := by
  induction cs generalizing s with
  | nil =>
    simp [runSleepChunks, List.foldl_nil]
    rfl
  | cons c rest ih =>
    unfold runSleepChunks
    rw [stateM_bind_run]
    have hSleep : (simTime.sleep c).run s =
        ((), { s with
          monoNanos := s.monoNanos + c.toNat * nanosecondsPerMs
          sleepLog := s.sleepLog.push c }) := rfl
    rw [hSleep]
    dsimp only
    rw [ih]
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift rest c.toNat]
    have hMono : s.monoNanos + c.toNat * nanosecondsPerMs +
        (rest.foldl (fun acc x => acc + x.toNat) 0) * nanosecondsPerMs =
        s.monoNanos + (c.toNat + rest.foldl (fun acc x => acc + x.toNat) 0) * nanosecondsPerMs := by
      rw [Nat.add_mul, Nat.add_assoc]
    have hLog : s.sleepLog.push c ++ rest.toArray = s.sleepLog ++ (c :: rest).toArray := by
      apply Array.ext'
      simp
    rw [hMono, hLog]

/-- Executing `runSleepChunks simTime (sleepChunks ms)` advances `monoNanos` by `ms * nanosecondsPerMs`. -/
theorem runSleepChunks_simTime_sleepChunks (ms : Nat) (s : PoolSimState) :
    (runSleepChunks simTime (sleepChunks ms)).run s =
      ((), { s with
        monoNanos := s.monoNanos + ms * nanosecondsPerMs
        sleepLog := s.sleepLog ++ (sleepChunks ms).toArray }) := by
  rw [runSleepChunks_simTime, (sleepChunks_spec ms).2]

/-- Invalid `PoolConfig` values fail `validatePoolConfig` with `.invalidInput`, `path = some cfg.poolDir`, and a non-empty message. -/
theorem validatePoolConfig_of_false (cfg : PoolConfig) (h : validPoolConfig cfg = false) :
    ∃ e, validatePoolConfig cfg = .error e ∧ e.kind = .invalidInput ∧
      e.path = some cfg.poolDir ∧ e.message ≠ "" := by
  unfold validPoolConfig at h
  unfold validatePoolConfig
  cases hDir : validPoolDir cfg.poolDir
  · simp
  · simp only [hDir, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and] at h ⊢
    cases hSlots : cfg.totalSlots
    · simp
    · simp only [beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte]
      cases hPoll : cfg.pollIntervalMs
      · simp
      · simp [hSlots, hPoll] at h

/-- Valid `PoolConfig` values pass `validatePoolConfig` and satisfy all positive numeric bounds. -/
theorem validatePoolConfig_of_true (cfg : PoolConfig) (h : validPoolConfig cfg = true) :
    validatePoolConfig cfg = .ok cfg ∧ validPoolDir cfg.poolDir = true ∧
      1 ≤ cfg.totalSlots ∧ 1 ≤ cfg.pollIntervalMs := by
  unfold validPoolConfig at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hDir, hSlots⟩, hPoll⟩
  unfold validatePoolConfig
  have hS0 : (cfg.totalSlots == 0) = false := by
    cases hs : cfg.totalSlots <;> simp_all
  have hP0 : (cfg.pollIntervalMs == 0) = false := by
    cases hp : cfg.pollIntervalMs <;> simp_all
  simp [hDir, hS0, hP0, hSlots, hPoll]

/-- `mapFsError fe` always yields a non-empty diagnostic message. -/
theorem mapFsError_nonEmpty (fe : FsError) : (mapFsError fe).message ≠ "" := by
  unfold mapFsError
  dsimp only
  split
  · decide
  · next h =>
    intro hem
    rw [hem] at h
    contradiction

private def parseDecAcc (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => parseDecAcc (acc * 10 + (c.toNat - 48)) cs

private theorem decDigitChar_val (k : Nat) (hk : k < 10) :
    (decDigitChar k).toNat - 48 = k ∧ decDigitChar k ≠ '/' ∧ decDigitChar k ≠ Char.ofNat 0 := by
  have hFin : ∀ x : Fin 10,
      (decDigitChar x.1).toNat - 48 = x.1 ∧ decDigitChar x.1 ≠ '/' ∧ decDigitChar x.1 ≠ Char.ofNat 0 := by
    decide
  exact hFin ⟨k, hk⟩

private theorem mod_10_lt (n : Nat) : n % 10 < 10 := by omega

private theorem mod_10_of_div_zero {n : Nat} (h : (n / 10 == 0) = true) : n % 10 = n := by
  have h0 : n / 10 = 0 := beq_iff_eq.mp h
  omega

private theorem div_10_lt_of_lt_succ {n f : Nat} (hf : n < f + 1) (h : ¬ (n / 10 == 0) = true) : n / 10 < f := by
  have h0 : n / 10 ≠ 0 := fun e => h (beq_iff_eq.mpr e)
  omega

private theorem div_10_mul_add_mod (n : Nat) : n / 10 * 10 + n % 10 = n := by omega

private theorem parseDecAcc_natDecCharsAux (fuel n : Nat) (ds : List Char) (hf : n < fuel) :
    parseDecAcc 0 (natDecCharsAux fuel n ds) = parseDecAcc n ds := by
  induction fuel generalizing n ds with
  | zero => exact absurd hf (Nat.not_lt_zero n)
  | succ f ih =>
    unfold natDecCharsAux
    dsimp only
    have hd := (decDigitChar_val (n % 10) (mod_10_lt n)).1
    cases hq : (n / 10 == 0)
    · have hIf : (if false = true then decDigitChar (n % 10) :: ds
          else natDecCharsAux f (n / 10) (decDigitChar (n % 10) :: ds)) =
          natDecCharsAux f (n / 10) (decDigitChar (n % 10) :: ds) := rfl
      rw [hIf]
      have hlt : n / 10 < f := div_10_lt_of_lt_succ hf (by simp [hq])
      rw [ih (n / 10) (decDigitChar (n % 10) :: ds) hlt]
      change parseDecAcc (n / 10 * 10 + ((decDigitChar (n % 10)).toNat - 48)) ds = parseDecAcc n ds
      rw [hd, div_10_mul_add_mod]
    · have hIf : (if true = true then decDigitChar (n % 10) :: ds
          else natDecCharsAux f (n / 10) (decDigitChar (n % 10) :: ds)) =
          decDigitChar (n % 10) :: ds := rfl
      rw [hIf]
      change parseDecAcc (0 * 10 + ((decDigitChar (n % 10)).toNat - 48)) ds = parseDecAcc n ds
      rw [Nat.zero_mul, Nat.zero_add, hd, mod_10_of_div_zero hq]

private theorem natDecCharsAux_good (fuel n : Nat) (ds : List Char)
    (hds : ∀ c ∈ ds, c ≠ '/' ∧ c ≠ Char.ofNat 0) :
    ∀ c ∈ natDecCharsAux fuel n ds, c ≠ '/' ∧ c ≠ Char.ofNat 0 := by
  induction fuel generalizing n ds with
  | zero => exact hds
  | succ f ih =>
    simp only [natDecCharsAux]
    have hd := (decDigitChar_val (n % 10) (by omega)).2
    have hds' : ∀ c ∈ decDigitChar (n % 10) :: ds, c ≠ '/' ∧ c ≠ Char.ofNat 0 := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hm
      · exact hd
      · exact hds c hm
    split
    · exact hds'
    · exact ih (n / 10) _ hds'

private theorem slotFileName_toList (i : Nat) :
    (slotFileName i).toList =
      ['s', 'l', 'o', 't', '-'] ++ natDecCharsAux (i + 1) i [] ++ ['.', 'l', 'o', 'c', 'k'] := by
  unfold slotFileName natDecString
  simp [String.toList_append, String.toList_ofList]

/-- `slotFileName` is injective on slot indices. -/
theorem slotFileName_inj {i j : Nat} (h : slotFileName i = slotFileName j) : i = j := by
  have hL : (slotFileName i).toList = (slotFileName j).toList := congrArg String.toList h
  rw [slotFileName_toList, slotFileName_toList, List.append_assoc, List.append_assoc] at hL
  have hMid := List.append_cancel_left hL
  have hDig := List.append_cancel_right hMid
  have ha := parseDecAcc_natDecCharsAux (i + 1) i [] (Nat.lt_succ_self i)
  have hb := parseDecAcc_natDecCharsAux (j + 1) j [] (Nat.lt_succ_self j)
  rw [hDig] at ha
  exact ha.symm.trans hb

private theorem slotFileName_noSlash_noNul (i : Nat) :
    '/' ∉ (slotFileName i).toList ∧ hasNulChar (slotFileName i).toList = false := by
  have hDig := natDecCharsAux_good (i + 1) i [] (by intro _ h; cases h)
  have hAll : ∀ c ∈ (slotFileName i).toList, c ≠ '/' ∧ c ≠ Char.ofNat 0 := by
    rw [slotFileName_toList]
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · rcases List.mem_append.mp h1 with hPre | hMid
      · simp at hPre; rcases hPre with rfl | rfl | rfl | rfl | rfl <;> decide
      · exact hDig c hMid
    · simp at h2; rcases h2 with rfl | rfl | rfl | rfl | rfl <;> decide
  constructor
  · intro hs
    exact (hAll '/' hs).1 rfl
  · generalize (slotFileName i).toList = cs at hAll
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      unfold hasNulChar
      have hc0 : (c == Char.ofNat 0) = false := beq_false_of_ne (hAll c (.head _)).2
      rw [hc0, Bool.false_or]
      exact ih (fun x hx => hAll x (.tail _ hx))

private theorem trimTrailingSlashesRev_nonSlash {c : Char} (hc : c ≠ '/') (xs : List Char) :
    trimTrailingSlashesRev (c :: xs) = c :: xs := by
  simp [trimTrailingSlashesRev, hc]

private theorem slotFileName_norm (i : Nat) : normSimPath (slotFileName i) = slotFileName i := by
  unfold normSimPath
  have hRev : ∃ xs, (slotFileName i).toList.reverse = 'k' :: xs := by
    rw [slotFileName_toList, List.reverse_append, List.reverse_cons]
    exact ⟨_, rfl⟩
  rcases hRev with ⟨xs, hxs⟩
  rw [hxs, trimTrailingSlashesRev_nonSlash (by decide) xs, ← hxs, List.reverse_reverse, String.ofList_toList]

private theorem trimTrailingSlashesRev_props (cs : List Char) :
    (cs ≠ [] → trimTrailingSlashesRev cs ≠ []) ∧
    (trimTrailingSlashesRev cs).length ≤ cs.length ∧
    (∀ c ∈ trimTrailingSlashesRev cs, c ∈ cs) ∧
    (trimTrailingSlashesRev cs = ['/'] ∨ ∀ rest, trimTrailingSlashesRev cs ≠ '/' :: rest) := by
  induction cs with
  | nil => simp [trimTrailingSlashesRev]
  | cons c rest ih =>
    by_cases hc : c = '/'
    · subst hc
      cases rest with
      | nil => simp [trimTrailingSlashesRev]
      | cons c2 tail =>
        have hStep : trimTrailingSlashesRev ('/' :: c2 :: tail) = trimTrailingSlashesRev (c2 :: tail) := rfl
        rw [hStep]
        rcases ih with ⟨ih1, ih2, ih3, ih4⟩
        exact ⟨fun _ => ih1 (List.cons_ne_nil _ _), Nat.le_trans ih2 (Nat.le_succ _),
          fun x hx => List.mem_cons_of_mem _ (ih3 x hx), ih4⟩
    · rw [trimTrailingSlashesRev_nonSlash hc rest]
      refine ⟨fun _ => List.cons_ne_nil _ _, Nat.le_refl _, fun _ hx => hx, Or.inr ?_⟩
      intro tail hEq
      injection hEq with h1
      exact hc h1

/-- `normSimPath` is idempotent on all path strings. -/
theorem normSimPath_idempotent (p : String) : normSimPath (normSimPath p) = normSimPath p := by
  unfold normSimPath
  rw [String.toList_ofList, List.reverse_reverse]
  rcases (trimTrailingSlashesRev_props p.toList.reverse).2.2.2 with hRoot | hNoSlash
  · rw [hRoot]; rfl
  · cases hRev : trimTrailingSlashesRev p.toList.reverse with
    | nil => rfl
    | cons x xs =>
      have hx : x ≠ '/' := fun h => hNoSlash xs (h ▸ hRev)
      rw [trimTrailingSlashesRev_nonSlash hx xs]

private theorem hasNulChar_false_iff (cs : List Char) :
    hasNulChar cs = false ↔ ∀ c ∈ cs, c ≠ Char.ofNat 0 := by
  induction cs with
  | nil => simp [hasNulChar]
  | cons c rest ih =>
    unfold hasNulChar
    simp [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ih]

private theorem dropUntilSlashRev_cons_ne {c : Char} (hc : c ≠ '/') (ys : List Char) :
    dropUntilSlashRev (c :: ys) = dropUntilSlashRev ys := by
  simp [dropUntilSlashRev, hc]

private theorem dropUntilSlashRev_noSlash (xs pre : List Char) (hNo : ∀ c ∈ xs, c ≠ '/') :
    dropUntilSlashRev (xs ++ '/' :: pre) = some pre := by
  induction xs with
  | nil => rfl
  | cons c rest ih =>
    have hc : c ≠ '/' := hNo c (.head _)
    rw [List.cons_append, dropUntilSlashRev_cons_ne hc]
    exact ih (fun x hx => hNo x (.tail _ hx))

private theorem dropUntilSlashRev_lt_len :
    ∀ (xs res : List Char), dropUntilSlashRev xs = some res → res.length < xs.length
  | [], _, h => by cases h
  | c :: rest, res, h => by
    by_cases hc : c = '/'
    · subst hc
      have hEq : some rest = some res := h
      injection hEq with hr
      subst hr
      exact Nat.lt_succ_self _
    · rw [dropUntilSlashRev_cons_ne hc] at h
      exact Nat.lt_trans (dropUntilSlashRev_lt_len rest res h) (Nat.lt_succ_self _)

/-- Any parent path returned by `parentSimPath p` is normalized and strictly shorter than `normSimPath p`. -/
theorem parentSimPath_props {p par : String} (h : parentSimPath p = some par) :
    normSimPath par = par ∧ par.toList.length < (normSimPath p).toList.length := by
  unfold parentSimPath at h
  dsimp only at h
  by_cases h0 : ((normSimPath p).isEmpty || normSimPath p == "/") = true
  · simp [h0] at h
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    let np := normSimPath p
    change (match dropUntilSlashRev np.toList.reverse with
      | none => none
      | some [] => some "/"
      | some revPar => some (normSimPath (String.ofList revPar.reverse))) = some par at h
    cases hd : dropUntilSlashRev np.toList.reverse with
    | none => rw [hd] at h; cases h
    | some revPar =>
      rw [hd] at h
      have hLtRev := dropUntilSlashRev_lt_len np.toList.reverse revPar hd
      rw [List.length_reverse] at hLtRev
      cases revPar with
      | nil =>
        dsimp only at h
        injection h with hPar
        subst hPar
        constructor
        · rfl
        · change "/".toList.length < np.toList.length
          have hLen1 : "/".toList.length = 1 := rfl
          rw [hLen1]
          have hNeEmpty : np.toList ≠ [] := by
            intro hem
            have hEqE : normSimPath p = "" := (@String.ofList_toList (normSimPath p)).symm.trans (by rw [hem])
            have hTrue : ((normSimPath p).isEmpty || normSimPath p == "/") = true := by rw [hEqE]; rfl
            exact h0 hTrue
          have hNeSlash : np.toList ≠ ['/'] := by
            intro hs
            have hEqS : normSimPath p = "/" := (@String.ofList_toList (normSimPath p)).symm.trans (by rw [hs])
            have hTrue : ((normSimPath p).isEmpty || normSimPath p == "/") = true := by rw [hEqS]; rfl
            exact h0 hTrue
          cases hL : np.toList with
          | nil => exact absurd hL hNeEmpty
          | cons a tail =>
            cases tail with
            | nil =>
              rw [hL] at hd
              change dropUntilSlashRev [a] = some [] at hd
              by_cases ha : a = '/'
              · subst ha; exact absurd hL hNeSlash
              · rw [dropUntilSlashRev_cons_ne ha] at hd; cases hd
            | cons b tail2 =>
              simp
      | cons r0 rtail =>
        dsimp only at h
        injection h with hPar
        subst hPar
        constructor
        · exact normSimPath_idempotent _
        · change (normSimPath (String.ofList (r0 :: rtail).reverse)).toList.length < np.toList.length
          unfold normSimPath
          rw [String.toList_ofList, List.length_reverse, String.toList_ofList, List.reverse_reverse]
          have hLe := (trimTrailingSlashesRev_props (r0 :: rtail)).2.1
          exact Nat.lt_of_le_of_lt hLe hLtRev

/-- Structural invariants of `slotLockPath simFs.join poolDir i` for any valid `poolDir`. -/
theorem slotLockPath_props {poolDir : String} (hValid : validPoolDir poolDir = true) (i : Nat) :
    let lp := slotLockPath simFs.join poolDir i
    let nb := normSimPath poolDir
    normSimPath lp = lp ∧
    validPoolDir lp = true ∧
    parentSimPath lp = some nb ∧
    nb.toList.length < lp.toList.length ∧
    lp ≠ "ran-other" ∧
    lp ≠ "ran-expired" := by
  dsimp only
  unfold validPoolDir at hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hValid
  rcases hValid with ⟨hNonEmpty, hNoNulDir⟩
  have hDirChars := (hasNulChar_false_iff poolDir.toList).mp hNoNulDir
  let nb := normSimPath poolDir
  have hDirNeNil : poolDir.toList ≠ [] := by
    intro hem
    have hEq : poolDir = "" := (@String.ofList_toList poolDir).symm.trans (by rw [hem])
    subst hEq; cases hNonEmpty
  have hTrimProps := trimTrailingSlashesRev_props poolDir.toList.reverse
  have hNbNeNil : nb.toList ≠ [] := by
    dsimp only [nb]
    unfold normSimPath
    rw [String.toList_ofList]
    intro hem
    have hRevNil : trimTrailingSlashesRev poolDir.toList.reverse = [] := List.reverse_eq_iff.mp hem
    exact hTrimProps.1 (by simp [hDirNeNil]) hRevNil
  have hNbEmptyF : (normSimPath poolDir).isEmpty = false := by
    cases h : (normSimPath poolDir).isEmpty
    · rfl
    · exfalso
      have : nb = "" := String.isEmpty_iff.mp h
      rw [this] at hNbNeNil
      exact hNbNeNil rfl
  have hNbNoNul : ∀ c ∈ nb.toList, c ≠ Char.ofNat 0 := by
    dsimp only [nb]
    unfold normSimPath
    rw [String.toList_ofList]
    intro c hc
    have hcRev : c ∈ trimTrailingSlashesRev poolDir.toList.reverse := List.mem_reverse.mp hc
    have hcOrig : c ∈ poolDir.toList := List.mem_reverse.mp (hTrimProps.2.2.1 c hcRev)
    exact hDirChars c hcOrig
  obtain ⟨hSubNoSlash, hSubNoNulB⟩ := slotFileName_noSlash_noNul i
  have hSubNoNul := (hasNulChar_false_iff (slotFileName i).toList).mp hSubNoNulB
  have hHeadF : ((slotFileName i).toList.head? == some '/') = false := by
    rw [slotFileName_toList]; rfl
  have hSimJoin : simFs.join = simJoin := rfl
  have hJoinEq : slotLockPath simFs.join poolDir i =
      if nb == "/" then "/" ++ slotFileName i else nb ++ "/" ++ slotFileName i := by
    dsimp only [slotLockPath, nb]
    rw [hSimJoin]
    unfold simJoin
    dsimp only
    simp only [slotFileName_norm, hHeadF, hNbEmptyF, Bool.false_eq_true, ↓reduceIte]
  let lp := slotLockPath simFs.join poolDir i
  have hLpSuffix : ∃ pre, lp.toList = pre ++ '/' :: (slotFileName i).toList ∧
      (nb == "/" ∧ pre = [] ∨ nb != "/" ∧ pre = nb.toList) := by
    dsimp only [lp]
    rw [hJoinEq]
    cases hSlash : (nb == "/")
    · refine ⟨nb.toList, ?_, Or.inr ⟨by simp [bne, hSlash], rfl⟩⟩
      simp [String.toList_append]
    · refine ⟨[], ?_, Or.inl ⟨rfl, rfl⟩⟩
      simp [String.toList_append]
  rcases hLpSuffix with ⟨pre, hLpList, hPreCases⟩
  have hLastK : ∃ xs, lp.toList.reverse = 'k' :: xs := by
    rw [hLpList, slotFileName_toList, List.reverse_append, List.reverse_cons,
      List.reverse_append, List.reverse_append]
    exact ⟨_, rfl⟩
  have hNormLp : normSimPath lp = lp := by
    rcases hLastK with ⟨xs, hxs⟩
    unfold normSimPath
    rw [hxs, trimTrailingSlashesRev_nonSlash (by decide) xs, ← hxs, List.reverse_reverse, String.ofList_toList]
  have hValidLp : validPoolDir lp = true := by
    unfold validPoolDir
    have hLpNe : lp.isEmpty = false := by
      cases h : lp.isEmpty
      · rfl
      · have hem : lp = "" := String.isEmpty_iff.mp h
        rcases hLastK with ⟨xs, hxs⟩
        rw [hem] at hxs
        cases hxs
    have hLpNoNul : hasNulChar lp.toList = false := by
      rw [hasNulChar_false_iff, hLpList]
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · rcases hPreCases with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · cases h1
        · exact hNbNoNul c h1
      · rcases List.mem_cons.mp h2 with rfl | hSub
        · decide
        · exact hSubNoNul c hSub
    simp [hLpNe, hLpNoNul]
  have hLpNotRoot : (lp == "/") = false := by
    rw [beq_eq_false_iff_ne]
    intro hEq
    have hLen : lp.toList.length = 1 := by rw [hEq]; rfl
    rw [hLpList, slotFileName_toList] at hLen
    simp at hLen
    omega
  have hParentLp : parentSimPath lp = some nb := by
    unfold parentSimPath
    rw [hNormLp]
    have hLpEmpty : lp.isEmpty = false := by
      unfold validPoolDir at hValidLp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hValidLp
      exact hValidLp.1
    simp only [hLpEmpty, hLpNotRoot, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    have hRev : lp.toList.reverse = (slotFileName i).toList.reverse ++ '/' :: pre.reverse := by
      rw [hLpList, List.reverse_append, List.reverse_cons, List.append_assoc]
      rfl
    rw [hRev, dropUntilSlashRev_noSlash _ _ (fun c hc => fun hs => hSubNoSlash (hs ▸ List.mem_reverse.mp hc))]
    rcases hPreCases with ⟨hEqSlash, rfl⟩ | ⟨hNeSlash, rfl⟩
    · simp only [beq_iff_eq] at hEqSlash
      exact congrArg some hEqSlash.symm
    · cases hRevNb : nb.toList.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp hRevNb) hNbNeNil
      | cons c0 ctail =>
        dsimp only
        rw [← hRevNb, List.reverse_reverse, String.ofList_toList]
        exact congrArg some (normSimPath_idempotent poolDir)
  have hLenLt : nb.toList.length < lp.toList.length := by
    rw [hLpList, slotFileName_toList]
    rcases hPreCases with ⟨hEqSlash, rfl⟩ | ⟨_, rfl⟩
    · simp only [beq_iff_eq] at hEqSlash
      have h1 : nb.toList.length = 1 := by rw [hEqSlash]; rfl
      simp [h1]
    · simp
  have hNeOther : lp ≠ "ran-other" := by
    intro hEq
    rcases hLastK with ⟨xs, hxs⟩
    rw [hEq] at hxs
    cases hxs
  have hNeExp : lp ≠ "ran-expired" := by
    intro hEq
    rcases hLastK with ⟨xs, hxs⟩
    rw [hEq] at hxs
    cases hxs
  exact ⟨hNormLp, hValidLp, hParentLp, hLenLt, hNeOther, hNeExp⟩

/-- `slotLockPath simFs.join poolDir` is injective on slot indices when `validPoolDir poolDir = true`. -/
theorem slotLockPath_inj {poolDir : String} (hValid : validPoolDir poolDir = true)
    {i j : Nat} (h : slotLockPath simFs.join poolDir i = slotLockPath simFs.join poolDir j) : i = j := by
  unfold validPoolDir at hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hValid
  have hDirNeNil : poolDir.toList ≠ [] := by
    intro hem
    have hEq : poolDir = "" := (@String.ofList_toList poolDir).symm.trans (by rw [hem])
    subst hEq; cases hValid.1
  have hNbNeNil : (normSimPath poolDir).toList ≠ [] := by
    unfold normSimPath; rw [String.toList_ofList]; intro hem
    exact (trimTrailingSlashesRev_props poolDir.toList.reverse).1 (by simp [hDirNeNil]) (List.reverse_eq_iff.mp hem)
  have hNbEmptyF : (normSimPath poolDir).isEmpty = false := by
    cases hb : (normSimPath poolDir).isEmpty
    · rfl
    · exfalso; exact hNbNeNil (congrArg String.toList (String.isEmpty_iff.mp hb))
  have hSimJoin : simFs.join = simJoin := rfl
  have hExpand : ∀ k, slotLockPath simFs.join poolDir k =
      if normSimPath poolDir == "/" then "/" ++ slotFileName k else normSimPath poolDir ++ "/" ++ slotFileName k := by
    intro k
    dsimp only [slotLockPath]
    rw [hSimJoin]
    unfold simJoin
    dsimp only
    have hh : ((slotFileName k).toList.head? == some '/') = false := by rw [slotFileName_toList]; rfl
    simp only [slotFileName_norm, hh, hNbEmptyF, Bool.false_eq_true, ↓reduceIte]
  rw [hExpand i, hExpand j] at h
  have hStrEq : ∀ {s1 s2 : String}, s1.toList = s2.toList → s1 = s2 := fun {s1 s2} he =>
    (@String.ofList_toList s1).symm.trans ((congrArg String.ofList he).trans (@String.ofList_toList s2))
  cases hSlash : (normSimPath poolDir == "/")
  · simp only [hSlash, Bool.false_eq_true, ↓reduceIte] at h
    have hL := congrArg String.toList h
    simp [String.toList_append, List.append_assoc] at hL
    exact slotFileName_inj (hStrEq hL)
  · simp only [hSlash, ↓reduceIte] at h
    have hL := congrArg String.toList h
    simp [String.toList_append] at hL
    exact slotFileName_inj (hStrEq hL)

private theorem ensureSimDirChain_clean (maxLen : Nat) :
    ∀ (fuel : Nat) (s : PoolSimState) (np : String),
      s.files = [] →
      s.symlinks = [] →
      normSimPath np = np →
      np.toList.length < fuel →
      np.toList.length ≤ maxLen →
      (∀ d ∈ s.dirs, d.toList.length ≤ maxLen) →
      ∃ s', ensureSimDirChain fuel s np = .ok s' ∧
        s'.files = [] ∧
        s'.symlinks = [] ∧
        s'.heldLocks = s.heldLocks ∧
        s'.externalLeases = s.externalLeases ∧
        s'.failMkdirWith = s.failMkdirWith ∧
        s'.monoNanos = s.monoNanos ∧
        s'.sleepLog = s.sleepLog ∧
        np ∈ s'.dirs ∧
        ∀ d ∈ s'.dirs, d.toList.length ≤ maxLen
  | 0, _, _, _, _, _, hLt, _, _ => absurd hLt (Nat.not_lt_zero _)
  | fuel + 1, s, np, hFiles, hSyms, hNorm, hLt, hMax, hDirsLen => by
    unfold ensureSimDirChain
    have hNoFile : hasSimFile s np = false := by simp [hasSimFile, hFiles]
    have hNoSym : ¬ (np ∈ s.symlinks) := by simp [hSyms]
    have hOr : (hasSimFile s np || decide (np ∈ s.symlinks)) = false := by simp [hNoFile, hNoSym]
    simp only [hOr, Bool.false_eq_true, ↓reduceIte]
    by_cases hIn : np ∈ s.dirs
    · exact ⟨s, by simp [hIn], hFiles, hSyms, rfl, rfl, rfl, rfl, rfl, hIn, hDirsLen⟩
    · simp only [hIn, ↓reduceIte]
      cases hPar : parentSimPath np with
      | none =>
        refine ⟨{ s with dirs := np :: s.dirs }, rfl, hFiles, hSyms, rfl, rfl, rfl, rfl, rfl, .head _, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hdRest
        · exact hMax
        · exact hDirsLen d hdRest
      | some par =>
        obtain ⟨hParNorm, hParLen⟩ := parentSimPath_props hPar
        rw [hNorm] at hParLen
        have hParLtFuel : par.toList.length < fuel := Nat.lt_of_lt_of_le hParLen (Nat.lt_succ_iff.mp hLt)
        have hParMax : par.toList.length ≤ maxLen := Nat.le_trans (Nat.le_of_lt hParLen) hMax
        obtain ⟨s1, hRec, hF1, hSy1, hH1, hE1, hFM1, hM1, hSL1, _, hD1⟩ :=
          ensureSimDirChain_clean maxLen fuel s par hFiles hSyms hParNorm hParLtFuel hParMax hDirsLen
        dsimp only
        rw [hRec]
        dsimp only
        by_cases hIn1 : np ∈ s1.dirs
        · exact ⟨s1, by simp [hIn1], hF1, hSy1, hH1, hE1, hFM1, hM1, hSL1, hIn1, hD1⟩
        · refine ⟨{ s1 with dirs := np :: s1.dirs }, by simp [hIn1], hF1, hSy1, hH1, hE1, hFM1, hM1, hSL1, .head _, ?_⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hdRest
          · exact hMax
          · exact hD1 d hdRest

/-- Exact evaluation equation for `simFs.mkdir`. -/
theorem simFs_mkdir_run (s : PoolSimState) (p : String) (parents existOk : Bool) :
    (simFs.mkdir p parents existOk).run s =
      match simMkdirPure s p parents existOk with
      | .error e => (.error e, s)
      | .ok s' => (.ok (), s') := by
  dsimp only [simFs]
  rw [stateM_bind_run]
  have hGet : (get : StateM PoolSimState PoolSimState).run s = (s, s) := rfl
  rw [hGet]
  dsimp only
  cases simMkdirPure s p parents existOk <;> rfl

/-- Exact evaluation equation for `simFs.tryWithFileLock`. -/
theorem simFs_tryWithFileLock_run {α : Type} (s : PoolSimState) (p : String) (mode : LockMode)
    (createIfMissing : Bool) (action : StateM PoolSimState (Except FsError α)) :
    (simFs.tryWithFileLock p mode createIfMissing action).run s =
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => (.error e, s)
      | .ok none => (.ok none, s)
      | .ok (some sLocked) =>
        let np := normSimPath p
        let (r, s') := action.run sLocked
        (r.map some, { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }) := by
  dsimp only [simFs]
  rw [stateM_bind_run]
  have hGet : (get : StateM PoolSimState PoolSimState).run s = (s, s) := rfl
  rw [hGet]
  dsimp only
  cases simTryAcquirePure s p mode createIfMissing with
  | error e => rfl
  | ok opt =>
    cases opt with
    | none => rfl
    | some sLocked =>
      dsimp only
      rw [stateM_bind_run]
      have hSet : (set sLocked : StateM PoolSimState Unit).run s = ((), sLocked) := rfl
      rw [hSet]
      dsimp only
      rw [stateM_bind_run]
      cases action.run sLocked with
      | mk r s' =>
        dsimp only
        rw [stateM_bind_run]
        rfl

/-- Exact evaluation equation for `simFsEx.mkdir`. -/
theorem simFsEx_mkdir_run (s : PoolSimState) (p : String) (parents existOk : Bool) :
    (ExceptT.run (simFsEx.mkdir p parents existOk)).run s =
      match (simFs.mkdir p parents existOk).run s with
      | (res, s') => (.ok res, s') := rfl

/-- Exact evaluation equation for `simFsEx.tryWithFileLock`. -/
theorem simFsEx_tryWithFileLock_run {α : Type} (s : PoolSimState) (p : String) (mode : LockMode)
    (createIfMissing : Bool) (action : ExceptT String (StateM PoolSimState) (Except FsError α)) :
    (ExceptT.run (simFsEx.tryWithFileLock p mode createIfMissing action)).run s =
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => (.ok (.error e), s)
      | .ok none => (.ok (.ok none), s)
      | .ok (some sLocked) =>
        let np := normSimPath p
        match (ExceptT.run action).run sLocked with
        | (.error ex, sAfter) => (.error ex, { sAfter with heldLocks := removeFirstSimLock np mode sAfter.heldLocks })
        | (.ok r, sAfter) => (.ok (r.map some), { sAfter with heldLocks := removeFirstSimLock np mode sAfter.heldLocks }) := by
  dsimp only [simFsEx]
  rw [exceptT_bind_run]
  have hGet : (ExceptT.run (get : ExceptT String (StateM PoolSimState) PoolSimState)).run s = (.ok s, s) := rfl
  rw [hGet]
  dsimp only
  cases simTryAcquirePure s p mode createIfMissing with
  | error e => rfl
  | ok opt =>
    cases opt with
    | none => rfl
    | some sLocked =>
      dsimp only
      rw [exceptT_bind_run]
      have hSet : (ExceptT.run (liftM (set sLocked : StateM PoolSimState Unit) :
          ExceptT String (StateM PoolSimState) Unit)).run s = (.ok (), sLocked) := rfl
      rw [hSet]
      dsimp only [tryFinally', MonadFinally.tryFinally']
      rw [exceptT_bind_run]
      dsimp only [ExceptT.run, ExceptT.mk, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
      cases action sLocked with
      | mk r sAfter =>
        cases r <;> rfl

/-- `simFs.mkdir poolDir true true` succeeds on a clean simulation state and installs `normSimPath poolDir` without exceeding its length. -/
theorem simMkdir_clean (s : PoolSimState) (poolDir : String)
    (hFail : s.failMkdirWith = none)
    (hFiles : s.files = [])
    (hSyms : s.symlinks = [])
    (hValid : validPoolDir poolDir = true)
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length) :
    ∃ s', (simFs.mkdir poolDir true true).run s = (.ok (), s') ∧
      s'.files = [] ∧
      s'.symlinks = [] ∧
      s'.heldLocks = s.heldLocks ∧
      s'.externalLeases = s.externalLeases ∧
      s'.failMkdirWith = none ∧
      s'.monoNanos = s.monoNanos ∧
      s'.sleepLog = s.sleepLog ∧
      normSimPath poolDir ∈ s'.dirs ∧
      ∀ d ∈ s'.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length := by
  let np := normSimPath poolDir
  have hMkPure : simMkdirPure s poolDir true true =
      if np ∈ s.dirs then .ok s else ensureSimDirChain (np.toList.length + 1) s np := by
    unfold simMkdirPure
    rw [hFail]
    dsimp only
    have hOr : (hasSimFile s np || decide (np ∈ s.symlinks)) = false := by simp [hasSimFile, hFiles, hSyms]
    change (if (!validPoolDir poolDir) = true then _ else
      if (hasSimFile s np || decide (np ∈ s.symlinks)) = true then _ else
      if np ∈ s.dirs then _ else _) = _
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hOr]
    by_cases hIn : np ∈ s.dirs <;> simp [hIn, np]
  rw [simFs_mkdir_run, hMkPure]
  by_cases hIn : np ∈ s.dirs
  · simp only [hIn, ↓reduceIte]
    exact ⟨s, rfl, hFiles, hSyms, rfl, rfl, hFail, rfl, rfl, hIn, hDirsLen⟩
  · simp only [hIn, ↓reduceIte]
    obtain ⟨s', hEns, hF', hSy', hH', hE', hFM', hM', hSL', hMem, hD'⟩ :=
      ensureSimDirChain_clean np.toList.length (np.toList.length + 1) s np
        hFiles hSyms (normSimPath_idempotent poolDir) (Nat.lt_succ_self _) (Nat.le_refl _) hDirsLen
    rw [hEns]
    exact ⟨s', rfl, hF', hSy', hH', hE', hFail ▸ hFM', hM', hSL', hMem, hD'⟩

private theorem mem_leasesBeforeSlot_iff (poolDir : String) (relAt : Nat) :
    ∀ (n : Nat) (p : String) (r : Nat),
      (p, r) ∈ leasesBeforeSlot simFs.join poolDir relAt n ↔
        ∃ k < n, p = normSimPath (slotLockPath simFs.join poolDir k) ∧ r = relAt
  | 0, _, _ => by simp [leasesBeforeSlot]
  | n + 1, p, r => by
    simp only [leasesBeforeSlot, List.mem_cons]
    constructor
    · intro h
      rcases h with hEq | hTail
      · injection hEq with hp hr
        exact ⟨n, Nat.lt_succ_self n, hp, hr⟩
      · obtain ⟨k, hk, hp, hr⟩ := (mem_leasesBeforeSlot_iff poolDir relAt n p r).mp hTail
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hp, hr⟩
    · rintro ⟨k, hk, hp, hr⟩
      subst hp
      rw [hr]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact Or.inr ((mem_leasesBeforeSlot_iff poolDir relAt n _ _).mpr ⟨k, hlt, rfl, rfl⟩)
      · exact Or.inl rfl

private theorem mem_leasesBeforeSlotUntil_iff (poolDir : String) (freeIdx targetRel lockedUntil : Nat) :
    ∀ (n : Nat) (p : String) (r : Nat),
      (p, r) ∈ leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil n ↔
        ∃ k < n, p = normSimPath (slotLockPath simFs.join poolDir k) ∧
          r = (if k < freeIdx then lockedUntil else targetRel)
  | 0, _, _ => by simp [leasesBeforeSlotUntil]
  | n + 1, p, r => by
    simp only [leasesBeforeSlotUntil, List.mem_cons]
    constructor
    · intro h
      rcases h with hEq | hTail
      · injection hEq with hp hr
        exact ⟨n, Nat.lt_succ_self n, hp, hr⟩
      · obtain ⟨k, hk, hp, hr⟩ := (mem_leasesBeforeSlotUntil_iff poolDir freeIdx targetRel lockedUntil n p r).mp hTail
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hp, hr⟩
    · rintro ⟨k, hk, rfl, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact Or.inr ((mem_leasesBeforeSlotUntil_iff poolDir freeIdx targetRel lockedUntil n _ _).mpr ⟨k, hlt, rfl, rfl⟩)
      · exact Or.inl rfl

/-- In `leasesBeforeSlot`, slot `i < count` conflicts when `s.monoNanos < relAt`, and slot `count` is free when `heldLocks = []`. -/
theorem leasesBeforeSlot_conflict {s : PoolSimState} {poolDir : String} (hValid : validPoolDir poolDir = true)
    {relAt count : Nat} (hExt : s.externalLeases = leasesBeforeSlot simFs.join poolDir relAt count) :
    (∀ i, i < count → s.monoNanos < relAt →
      hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧
    (s.heldLocks = [] →
      hasSimLockConflict s (slotLockPath simFs.join poolDir count) .exclusive = false) := by
  constructor
  · intro i hi hMono
    unfold hasSimLockConflict
    rw [hExt]
    have hMem : (slotLockPath simFs.join poolDir i, relAt) ∈ leasesBeforeSlot simFs.join poolDir relAt count :=
      (mem_leasesBeforeSlot_iff poolDir relAt count _ _).mpr
        ⟨i, hi, (slotLockPath_props hValid i).1.symm, rfl⟩
    have hAny : (leasesBeforeSlot simFs.join poolDir relAt count).any
        (fun (lp, relNs) => lp == slotLockPath simFs.join poolDir i && decide (s.monoNanos < relNs)) = true :=
      List.any_eq_true.mpr ⟨(slotLockPath simFs.join poolDir i, relAt), hMem, by simp [hMono]⟩
    simp [hAny]
  · intro hHeld
    unfold hasSimLockConflict
    rw [hHeld, hExt]
    simp only [List.any_nil, Bool.false_or, List.any_eq_false, Prod.forall, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, not_and]
    intro p r hMem hp _
    obtain ⟨k, hk, hEq, _⟩ := (mem_leasesBeforeSlot_iff poolDir relAt count p r).mp hMem
    rw [(slotLockPath_props hValid k).1] at hEq
    rw [hEq] at hp
    have hkEq := slotLockPath_inj hValid hp
    omega

/-- In `leasesBeforeSlotUntil`, every slot `< count` conflicts before `min targetRel lockedUntil`, slots `< freeIdx` conflict before `lockedUntil`, and `freeIdx` is free once `targetRel ≤ s.monoNanos`. -/
theorem leasesBeforeSlotUntil_conflict {s : PoolSimState} {poolDir : String} (hValid : validPoolDir poolDir = true)
    {freeIdx targetRel lockedUntil count : Nat}
    (hExt : s.externalLeases = leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count) :
    (∀ i, i < count → i < freeIdx → s.monoNanos < lockedUntil →
      hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧
    (∀ i, i < count → freeIdx ≤ i → s.monoNanos < targetRel →
      hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) ∧
    (s.heldLocks = [] → freeIdx < count → targetRel ≤ s.monoNanos →
      hasSimLockConflict s (slotLockPath simFs.join poolDir freeIdx) .exclusive = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hlt hMono
    unfold hasSimLockConflict
    rw [hExt]
    have hMem : (slotLockPath simFs.join poolDir i, lockedUntil) ∈
        leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count :=
      (mem_leasesBeforeSlotUntil_iff poolDir freeIdx targetRel lockedUntil count _ _).mpr
        ⟨i, hi, (slotLockPath_props hValid i).1.symm, by simp [hlt]⟩
    have hAny : (leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count).any
        (fun (lp, relNs) => lp == slotLockPath simFs.join poolDir i && decide (s.monoNanos < relNs)) = true :=
      List.any_eq_true.mpr ⟨(slotLockPath simFs.join poolDir i, lockedUntil), hMem, by simp [hMono]⟩
    simp [hAny]
  · intro i hi hge hMono
    unfold hasSimLockConflict
    rw [hExt]
    have hNotLt : ¬ (i < freeIdx) := Nat.not_lt.mpr hge
    have hMem : (slotLockPath simFs.join poolDir i, targetRel) ∈
        leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count :=
      (mem_leasesBeforeSlotUntil_iff poolDir freeIdx targetRel lockedUntil count _ _).mpr
        ⟨i, hi, (slotLockPath_props hValid i).1.symm, by simp [hNotLt]⟩
    have hAny : (leasesBeforeSlotUntil simFs.join poolDir freeIdx targetRel lockedUntil count).any
        (fun (lp, relNs) => lp == slotLockPath simFs.join poolDir i && decide (s.monoNanos < relNs)) = true :=
      List.any_eq_true.mpr ⟨(slotLockPath simFs.join poolDir i, targetRel), hMem, by simp [hMono]⟩
    simp [hAny]
  · intro hHeld _ hMonoGe
    unfold hasSimLockConflict
    rw [hHeld, hExt]
    simp only [List.any_nil, Bool.false_or, List.any_eq_false, Prod.forall, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, not_and]
    intro p r hMem hp
    obtain ⟨k, _, hEq, hr⟩ := (mem_leasesBeforeSlotUntil_iff poolDir freeIdx targetRel lockedUntil count p r).mp hMem
    rw [(slotLockPath_props hValid k).1] at hEq
    rw [hEq] at hp
    have hkEq : k = freeIdx := slotLockPath_inj hValid hp
    subst hkEq
    simp only [Nat.lt_irrefl, ↓reduceIte] at hr
    rw [hr]
    exact Nat.not_lt.mpr hMonoGe

/-- Attempting to acquire a conflicting exclusive lock on a clean state fails contention without modifying state. -/
theorem simTryAcquire_busy (s : PoolSimState) (poolDir : String) (hValid : validPoolDir poolDir = true)
    (hFiles : s.files = []) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (i : Nat) (hPar : normSimPath poolDir ∈ s.dirs)
    (hConflict : hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = true) :
    simTryAcquirePure s (slotLockPath simFs.join poolDir i) .exclusive true = .ok none := by
  obtain ⟨_, hLpValid, hLpPar, hLpLen, _, _⟩ := slotLockPath_props hValid i
  unfold simTryAcquirePure
  have hNotDir : ¬ (normSimPath (slotLockPath simFs.join poolDir i) ∈ s.dirs) := by
    rw [(slotLockPath_props hValid i).1]
    intro hIn
    have hLe := hDirsLen _ hIn
    omega
  have hNotSym : ¬ (normSimPath (slotLockPath simFs.join poolDir i) ∈ s.symlinks) := by simp [hSyms]
  have hNoFile : hasSimFile s (normSimPath (slotLockPath simFs.join poolDir i)) = false := by
    simp [hasSimFile, hFiles]
  rw [(slotLockPath_props hValid i).1] at hNotDir hNotSym hNoFile ⊢
  simp only [hLpValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hNotDir, hNotSym, hNoFile, hLpPar, hPar, decide_true, hConflict]

/-- Attempting to acquire a free exclusive lock on a clean state creates the file and acquires the lock. -/
theorem simTryAcquire_free (s : PoolSimState) (poolDir : String) (hValid : validPoolDir poolDir = true)
    (hFiles : s.files = []) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (i : Nat) (hPar : normSimPath poolDir ∈ s.dirs)
    (hFree : hasSimLockConflict s (slotLockPath simFs.join poolDir i) .exclusive = false) :
    simTryAcquirePure s (slotLockPath simFs.join poolDir i) .exclusive true =
      .ok (some { s with
        files := (slotLockPath simFs.join poolDir i, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir i, .exclusive) :: s.heldLocks }) := by
  obtain ⟨hLpNorm, hLpValid, hLpPar, hLpLen, _, _⟩ := slotLockPath_props hValid i
  unfold simTryAcquirePure
  have hNotDir : ¬ (normSimPath (slotLockPath simFs.join poolDir i) ∈ s.dirs) := by
    rw [hLpNorm]
    intro hIn
    have hLe := hDirsLen _ hIn
    omega
  have hNotSym : ¬ (normSimPath (slotLockPath simFs.join poolDir i) ∈ s.symlinks) := by simp [hSyms]
  have hNoFile : hasSimFile s (normSimPath (slotLockPath simFs.join poolDir i)) = false := by
    simp [hasSimFile, hFiles]
  rw [hLpNorm] at hNotDir hNotSym hNoFile ⊢
  simp only [hLpValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hNotDir, hNotSym, hNoFile, hLpPar, hPar, decide_true, hFree]

/-- Probing a lock file with `.shared` while holding `(lp, .exclusive)` returns `.ok none` without mutating state. -/
theorem simFs_sharedProbe_held {s : PoolSimState} {lp : String}
    (hValid : validPoolDir lp = true) (hNorm : normSimPath lp = lp)
    (hNotDir : ¬ (lp ∈ s.dirs)) (hNotSym : ¬ (lp ∈ s.symlinks))
    (hFile : hasSimFile s lp = true)
    (hHeld : (lp, LockMode.exclusive) ∈ s.heldLocks) :
    (simFs.tryWithFileLock lp .shared false (pure (.ok ()))).run s = (.ok none, s) := by
  have hConf : hasSimLockConflict s lp .shared = true := by
    unfold hasSimLockConflict
    have h2 : (LockMode.exclusive == LockMode.exclusive) = true := rfl
    have hAny : s.heldLocks.any (fun (p, m) => p == lp && (LockMode.shared == .exclusive || m == .exclusive)) = true :=
      List.any_eq_true.mpr ⟨(lp, .exclusive), hHeld, by simp [h2]⟩
    simp [hAny]
  have hAcq : simTryAcquirePure s lp .shared false = .ok none := by
    unfold simTryAcquirePure
    rw [hNorm]
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hNotDir, hNotSym, hFile, hConf]
  rw [simFs_tryWithFileLock_run, hAcq]

/-- Probing an unlocked existing lock file with `.exclusive` and `createIfMissing = false` succeeds without changing `files` or `heldLocks`. -/
theorem simFs_postProbe_ok {s : PoolSimState} {lp : String}
    (hValid : validPoolDir lp = true) (hNorm : normSimPath lp = lp)
    (hNotDir : ¬ (lp ∈ s.dirs)) (hNotSym : ¬ (lp ∈ s.symlinks))
    (hFile : hasSimFile s lp = true)
    (hFree : hasSimLockConflict s lp .exclusive = false) :
    (simFs.tryWithFileLock lp .exclusive false (pure (.ok ()))).run s =
      (.ok (some ()), { s with heldLocks := removeFirstSimLock lp .exclusive ((lp, .exclusive) :: s.heldLocks) }) := by
  have hAcq : simTryAcquirePure s lp .exclusive false =
      .ok (some { s with heldLocks := (lp, .exclusive) :: s.heldLocks }) := by
    unfold simTryAcquirePure
    rw [hNorm]
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hNotDir, hNotSym, hFile, hFree]
  rw [simFs_tryWithFileLock_run, hAcq, hNorm]
  rfl

/-- Removing `(lp, mode)` from `(lp, mode) :: xs` drops the head element without inspecting `lp` syntax. -/
theorem removeFirstSimLock_cons_self (lp : String) (mode : LockMode) (xs : List (String × LockMode)) :
    removeFirstSimLock lp mode ((lp, mode) :: xs) = xs := by
  unfold removeFirstSimLock
  have h2 : (mode == mode) = true := by cases mode <;> rfl
  have h : ((lp, mode) == (lp, mode)) = true := by
    change (lp == lp && mode == mode) = true
    simp [h2]
  simp [h]

end LeanSwe.SlotPool.Proofs
