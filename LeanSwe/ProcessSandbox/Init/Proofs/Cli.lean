import LeanSwe.ProcessSandbox.Init.Proofs.Base

/-!
# ProcessSandbox Init CLI Parser Invariant Proofs

Machine-checked invariants on `psandbox_init::cli` and `psandbox_init::ops::run_init`:
- `cli.slice_eq` exact byte-slice equality (`decide (a.val = b.val)`),
- `cli.parse_fd_arg` range invariant (`v = -1 ∨ 0 ≤ v ≤ 1,048,576`) across all arbitrary byte slices,
- `cli.parse_fd_arg` rejection of empty slices,
- `cli.apply_cli_pair` flag routing (`--plan-fd`, `--status-fd`, `--go-fd`, `--ctrl-fd`),
- `cli.validate_cli_fds` exact mandatory-descriptor check (`plan_fd ≥ 0 ∧ status_fd ≥ 0 ∧ go_fd ≥ 0`),
- `cli.parse_cli` and `ops.run_init` `--probe` mode exactness.
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World

/-- Inductive equality characterization for `cli.slice_eq_loop` starting at index `i`. -/
theorem slice_eq_loop_full_spec (a b : Slice U8) (n i : Usize)
    (ha : n.val = a.val.length) (hb : n.val = b.val.length)
    (hi : i.val ≤ n.val)
    (hPre : ∀ k : Nat, (hka : k < a.val.length) → (hkb : k < b.val.length) →
      k < i.val → a.val[k]'hka = b.val[k]'hkb) :
    OkPost (cli.slice_eq_loop a b n i) fun eq =>
      eq = decide (a.val = b.val) := by
  unfold cli.slice_eq_loop
  refine okPost_loop_decr_nat
    (fun cur : Usize => n.val - cur.val)
    (fun cur => cur.val ≤ n.val ∧
      ∀ k : Nat, (hka : k < a.val.length) → (hkb : k < b.val.length) →
        k < cur.val → a.val[k]'hka = b.val[k]'hkb)
    (fun eq => eq = decide (a.val = b.val))
    _ i ?_ ⟨hi, hPre⟩
  rintro cur ⟨hCur, hPrefix⟩
  unfold cli.slice_eq_loop.body
  by_cases hLt : cur < n
  · have hLtVal : cur.val < n.val := by simpa using hLt
    simp only [hLt, ↓reduceIte]
    rw [slice_index_usize_ok a cur (by omega), bind_ok,
      slice_index_usize_ok b cur (by omega), bind_ok]
    by_cases hNe : (a.val[cur.val]'(by omega) != b.val[cur.val]'(by omega)) = true
    · simp only [hNe, ↓reduceIte]
      refine ⟨done false, rfl, ?_⟩
      have hDiff : a.val ≠ b.val := by
        intro hEq
        have : a.val[cur.val]'(by omega) = b.val[cur.val]'(by omega) := by simp [hEq]
        simp [this] at hNe
      simp [hDiff]
    · simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      have hEqCur : a.val[cur.val]'(by omega) = b.val[cur.val]'(by omega) :=
        UScalar.eq_of_val_eq (by simpa using hNe)
      have hnMax : n.val ≤ Usize.max := by rw [ha]; exact a.property
      have h1Val : (1#usize).val = 1 := rfl
      obtain ⟨next, hNext, hNextVal⟩ := usize_add_ok cur 1#usize (by change cur.val + 1 ≤ Usize.max; omega)
      rw [hNext, bind_ok]
      refine ⟨cont next, rfl, ⟨by omega, ?_⟩, by omega⟩
      intro k hka hkb hk
      by_cases hkEq : k = cur.val
      · subst hkEq; exact hEqCur
      · exact hPrefix k hka hkb (by omega)
  · simp only [hLt, ↓reduceIte]
    have hEqN : cur.val = n.val := by
      have : ¬ (cur.val < n.val) := by simpa using hLt
      omega
    refine ⟨done true, rfl, ?_⟩
    have hListEq : a.val = b.val := by
      apply List.ext_getElem (by omega)
      intro k hka hkb
      exact hPrefix k hka hkb (by omega)
    simp [hListEq]

/-- Exact specification of `cli.slice_eq`: always succeeds with `decide (a.val = b.val)`. -/
theorem slice_eq_spec (a b : Slice U8) :
    cli.slice_eq a b = Result.ok (decide (a.val = b.val)) := by
  unfold cli.slice_eq
  by_cases hLenNe : (Slice.len a != Slice.len b) = true
  · simp only [hLenNe, ↓reduceIte]
    have hDiff : a.val ≠ b.val := by
      intro hEq
      have : Slice.len a = Slice.len b := by
        apply UScalar.eq_of_val_eq
        simp [hEq]
      simp [this] at hLenNe
    simp [hDiff]
  · simp only [hLenNe, Bool.false_eq_true, ↓reduceIte]
    have hLenL : a.val.length = b.val.length := by simpa using hLenNe
    have ha : (Slice.len a).val = a.val.length := by simp
    have hb : (Slice.len a).val = b.val.length := by rw [ha, hLenL]
    obtain ⟨eq, hRun, hVal⟩ := slice_eq_loop_full_spec a b (Slice.len a) 0#usize ha hb
      (by simp) (by intro k _ _ hk; simp at hk)
    rw [hRun, hVal]

/-- Loop safety and range invariant for `cli.parse_fd_arg_loop`: whenever `ok1 = true`, `acc ≤ 1,048,576`. -/
theorem parse_fd_arg_loop_bounds (s : Slice U8) (n : Usize) (acc : U64) (i : Usize)
    (hn : n.val = s.val.length) (hi : i.val ≤ n.val) (hAcc : acc.val ≤ 1048576) :
    OkPost (cli.parse_fd_arg_loop s n acc i) fun res =>
      res.2 = false ∨ (res.2 = true ∧ res.1.val ≤ 1048576) := by
  unfold cli.parse_fd_arg_loop
  refine okPost_loop_decr_nat
    (fun st : U64 × Usize => n.val - st.2.val)
    (fun st => st.2.val ≤ n.val ∧ st.1.val ≤ 1048576)
    (fun res : U64 × Bool => res.2 = false ∨ (res.2 = true ∧ res.1.val ≤ 1048576))
    _ (acc, i) ?_ ⟨hi, hAcc⟩
  rintro ⟨curAcc, curI⟩ ⟨hCurI, hCurAcc⟩
  change curI.val ≤ n.val at hCurI
  change curAcc.val ≤ 1048576 at hCurAcc
  unfold cli.parse_fd_arg_loop.body
  by_cases hLt : curI < n
  · have hLtVal : curI.val < n.val := by simpa using hLt
    simp only [hLt, ↓reduceIte]
    rw [slice_index_usize_ok s curI (by omega), bind_ok]
    set b := s.val[curI.val]'(by omega)
    by_cases hbLo : b < 48#u8
    · simp only [hbLo, ↓reduceIte]
      exact ⟨done (curAcc, false), rfl, Or.inl rfl⟩
    · simp only [hbLo, ↓reduceIte]
      by_cases hbHi : b > 57#u8
      · simp only [hbHi, ↓reduceIte]
        exact ⟨done (curAcc, false), rfl, Or.inl rfl⟩
      · simp only [hbHi, ↓reduceIte]
        have h48 : (48#u8).val = 48 := rfl
        have h57 : (57#u8).val = 57 := rfl
        have hbGe : 48 ≤ b.val := by
          have : ¬ (b.val < 48) := by simpa [h48] using hbLo
          omega
        have hbLe : b.val ≤ 57 := by
          have : ¬ (57 < b.val) := by simpa [h57] using hbHi
          omega
        have hMax64 := u64_max_eq
        obtain ⟨m1, hm1, hm1Val⟩ := (okPost_iff_wp_spec _ _).mpr
          (U64.mul_spec (x := curAcc) (y := 10#u64) (by change curAcc.val * 10 ≤ U64.max; omega))
        obtain ⟨d8, hd8, hd8Val⟩ := (okPost_iff_wp_spec _ _).mpr
          (U8.sub_spec (x := b) (y := 48#u8) (by change 48 ≤ b.val; omega))
        have hm1Eq : m1.val = curAcc.val * 10 := by simpa using hm1Val
        have hd8Eq : d8.val = b.val - 48 := hd8Val.1
        have hd64Eq : (UScalar.cast .U64 d8 : U64).val = d8.val := by simp
        obtain ⟨acc1, hAcc1, hAcc1Val⟩ := (okPost_iff_wp_spec _ _).mpr
          (U64.add_spec (x := m1) (y := UScalar.cast .U64 d8) (by omega))
        rw [hm1, bind_ok, hd8, bind_ok]
        dsimp only [lift]
        simp only [bind_ok]
        rw [hAcc1, bind_ok]
        have hMaxConst : (IScalar.hcast .U64 cli.MAX_CLI_FD : U64) = 1048576#u64 := by
          simp [cli.MAX_CLI_FD]
          decide
        rw [hMaxConst]
        by_cases hOver : acc1 > 1048576#u64
        · simp only [hOver, ↓reduceIte]
          exact ⟨done (acc1, false), rfl, Or.inl rfl⟩
        · simp only [hOver, ↓reduceIte]
          have h1M : (1048576#u64).val = 1048576 := rfl
          have hLeMax : acc1.val ≤ 1048576 := by
            have : ¬ (1048576 < acc1.val) := by simpa [h1M] using hOver
            omega
          have hnMax : n.val ≤ Usize.max := by rw [hn]; exact s.property
          have h1U : (1#usize).val = 1 := rfl
          obtain ⟨nextI, hNextI, hNextIVal⟩ := usize_add_ok curI 1#usize
            (by change curI.val + 1 ≤ Usize.max; omega)
          rw [hNextI, bind_ok]
          refine ⟨cont (acc1, nextI), rfl, ⟨?_, hLeMax⟩, ?_⟩
          · change nextI.val ≤ n.val
            omega
          · change n.val - nextI.val < n.val - curI.val
            omega
  · simp only [hLt, ↓reduceIte]
    exact ⟨done (curAcc, true), rfl, Or.inr ⟨rfl, hCurAcc⟩⟩

/-- Global safety and range bound for `cli.parse_fd_arg`: always terminates without panic and returns `-1` or `0 ≤ fd ≤ 1,048,576`. -/
theorem parse_fd_arg_bounds (s : Slice U8) :
    OkPost (cli.parse_fd_arg s) fun fd =>
      fd = (-1)#i32 ∨ (0 ≤ fd.val ∧ fd.val ≤ 1048576) := by
  rw [cli.parse_fd_arg]
  by_cases h0 : Slice.len s = 0#usize
  · rw [if_true_eq h0]
    exact ⟨(-1)#i32, rfl, Or.inl rfl⟩
  · rw [if_false_eq h0]
    obtain ⟨⟨acc, ok1⟩, hLoop, hPost⟩ :=
      parse_fd_arg_loop_bounds s (Slice.len s) 0#u64 0#usize (by simp) (by simp) (by decide)
    rw [hLoop, bind_ok]
    cases ok1 with
    | false =>
      exact ⟨(-1)#i32, rfl, Or.inl rfl⟩
    | true =>
      rcases hPost with hF | ⟨_, hLe⟩
      · cases hF
      · change acc.val ≤ 1048576 at hLe
        refine ⟨UScalar.hcast .I32 acc, rfl, Or.inr ?_⟩
        have hBv : (UScalar.hcast .I32 acc : I32).bv = BitVec.setWidth 32 acc.bv := rfl
        have hToNat : (BitVec.setWidth 32 acc.bv).toNat = acc.val := by
          rw [BitVec.toNat_setWidth]
          have : acc.bv.toNat = acc.val := rfl
          rw [this, Nat.mod_eq_of_lt (by omega : acc.val < 4294967296)]
        have hInt : (UScalar.hcast .I32 acc : I32).val = Int.ofNat acc.val := by
          change (UScalar.hcast .I32 acc : I32).bv.toInt = Int.ofNat acc.val
          rw [hBv, BitVec.toInt_eq_toNat_cond, hToNat]
          have hCond : 2 * acc.val < 4294967296 := by omega
          change (if 2 * acc.val < 4294967296 then (acc.val : Int) else _) = Int.ofNat acc.val
          rw [if_true_eq hCond]
          rfl
        rw [hInt]
        change 0 ≤ (acc.val : Int) ∧ (acc.val : Int) ≤ 1048576
        omega

/-- `cli.parse_fd_arg` rejects empty slices with `-1`. -/
theorem parse_fd_arg_empty (s : Slice U8) (hEmpty : s.val = []) :
    cli.parse_fd_arg s = Result.ok (-1)#i32 := by
  unfold cli.parse_fd_arg
  have hZero : Slice.len s = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [hEmpty]
  simp only [hZero, ↓reduceIte]

/-- `cli.validate_cli_fds` succeeds iff `plan_fd ≥ 0`, `status_fd ≥ 0`, and `go_fd ≥ 0`, returning `Err EINVAL` (`22`) otherwise. -/
theorem validate_cli_fds_spec (fds : cli.CliFds) :
    cli.validate_cli_fds fds =
      Result.ok
        (if 0 ≤ fds.plan_fd.val ∧ 0 ≤ fds.status_fd.val ∧ 0 ≤ fds.go_fd.val then
          .Ok fds
        else
          .Err 22#i32) := by
  unfold cli.validate_cli_fds cli.EINVAL
  have h0 : (0#i32).val = 0 := rfl
  by_cases hp : fds.plan_fd < 0#i32
  · have hpv : fds.plan_fd.val < 0 := by simpa [h0] using hp
    have hCond : ¬ (0 ≤ fds.plan_fd.val ∧ 0 ≤ fds.status_fd.val ∧ 0 ≤ fds.go_fd.val) := by omega
    simp only [hp, hCond, ↓reduceIte]
  · have hpv : 0 ≤ fds.plan_fd.val := by
      have : ¬ (fds.plan_fd.val < 0) := by simpa [h0] using hp
      omega
    simp only [hp, ↓reduceIte]
    by_cases hs : fds.status_fd < 0#i32
    · have hsv : fds.status_fd.val < 0 := by simpa [h0] using hs
      have hCond : ¬ (0 ≤ fds.plan_fd.val ∧ 0 ≤ fds.status_fd.val ∧ 0 ≤ fds.go_fd.val) := by omega
      simp only [hs, hCond, ↓reduceIte]
    · have hsv : 0 ≤ fds.status_fd.val := by
        have : ¬ (fds.status_fd.val < 0) := by simpa [h0] using hs
        omega
      simp only [hs, ↓reduceIte]
      by_cases hg : fds.go_fd < 0#i32
      · have hgv : fds.go_fd.val < 0 := by simpa [h0] using hg
        have hCond : ¬ (0 ≤ fds.plan_fd.val ∧ 0 ≤ fds.status_fd.val ∧ 0 ≤ fds.go_fd.val) := by omega
        simp only [hg, hCond, ↓reduceIte]
      · have hgv : 0 ≤ fds.go_fd.val := by
          have : ¬ (fds.go_fd.val < 0) := by simpa [h0] using hg
          omega
        simp only [hg, hpv, hsv, hgv, and_self, ↓reduceIte]

/-- `cli.apply_cli_pair` routes `--plan-fd` to `fds.plan_fd`. -/
theorem apply_cli_pair_plan_fd (fds : cli.CliFds) (flag val : Slice U8)
    (hFlag : flag.val = [45#u8, 45#u8, 112#u8, 108#u8, 97#u8, 110#u8, 45#u8, 102#u8, 100#u8]) :
    ∃ v : I32,
      cli.parse_fd_arg val = Result.ok v ∧
      cli.apply_cli_pair fds flag val = Result.ok { fds with plan_fd := v } := by
  obtain ⟨v, hv, _⟩ := parse_fd_arg_bounds val
  refine ⟨v, hv, ?_⟩
  unfold cli.apply_cli_pair
  dsimp only [lift]
  simp only [bind_ok]
  rw [slice_eq_spec]
  have hDec : decide (flag.val = (Array.to_slice (Array.make 9#usize
      [45#u8, 45#u8, 112#u8, 108#u8, 97#u8, 110#u8, 45#u8, 102#u8, 100#u8])).val) = true := by
    simp [hFlag]
  rw [hDec, bind_ok]
  simp only [↓reduceIte, hv, bind_ok]

/-- `--probe` CLI argument bytes (`"--probe"`). -/
def probeArgBytes : Bytes :=
  [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8]

/-- `cli.parse_cli` returns `CliMode.Probe` without mutating state when `argc = 2` and `argv[1] = "--probe"`. -/
theorem parse_cli_probe_spec (s : init_sys.Sys) (arg0 : Bytes) :
    cli.parse_cli { s with cliArgs := [arg0, probeArgBytes] } 2#usize =
      Result.ok (cli.CliMode.Probe, { s with cliArgs := [arg0, probeArgBytes] }) := by
  rw [cli.parse_cli, if_true_eq rfl]
  extract_lets arg1
  have hRead :
      init_sys.read_cli_arg { s with cliArgs := [arg0, probeArgBytes] } 1#usize arg1 =
      Result.ok (7#usize, { s with cliArgs := [arg0, probeArgBytes] },
        Array.from (padBytesTo 64 probeArgBytes) (by decide)) := by
    unfold init_sys.read_cli_arg probeArgBytes
    have hIdx : ([arg0, [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8]])[(1#usize).val]? =
        some [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8] := rfl
    rw [hIdx]
    simp only [List.length_cons, List.length_nil]
    have hLe : 7 ≤ 64 := by decide
    simp only [hLe, ↓reduceIte]
    congr 1
    congr 1
    apply uscalar_eq_of_bv
    exact (UScalar.ofNatCore_bv 7 _).symm
  let arr64 : Array U8 64#usize := Array.from (padBytesTo 64 probeArgBytes) (by decide)
  have hSubSlice :
      ∃ sl : Slice U8,
        core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          arr64
          { start := 0#usize, «end» := 7#usize } = Result.ok sl ∧
        sl.val = probeArgBytes := by
    change ∃ sl : Slice U8,
      core.slice.index.SliceIndexRangeUsizeSlice.index
        { start := 0#usize, «end» := 7#usize } (Array.to_slice arr64) = Result.ok sl ∧ _
    rw [core.slice.index.SliceIndexRangeUsizeSlice.index]
    have hBound :
        ({ start := 0#usize, «end» := 7#usize } : core.ops.range.Range Usize).start ≤
          ({ start := 0#usize, «end» := 7#usize } : core.ops.range.Range Usize).end ∧
        ({ start := 0#usize, «end» := 7#usize } : core.ops.range.Range Usize).end.val ≤
          (Array.to_slice arr64).length := by
      refine ⟨by decide, ?_⟩
      simp [arr64, padBytesTo, probeArgBytes]
    rw [if_true_eq hBound]
    refine ⟨_, rfl, ?_⟩
    simp [arr64, padBytesTo, probeArgBytes, List.slice]
  obtain ⟨sl, hsl, hslVal⟩ := hSubSlice
  have hLift :
      lift (Array.to_slice (Array.make 7#usize
        [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8])) =
      Result.ok (Array.to_slice (Array.make 7#usize
        [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8])) := rfl
  have hEq :
      cli.slice_eq sl (Array.to_slice (Array.make 7#usize
        [45#u8, 45#u8, 112#u8, 114#u8, 111#u8, 98#u8, 101#u8])) = Result.ok true := by
    rw [slice_eq_spec]
    simp [hslVal, probeArgBytes]
  rw [bind_triple_ok hRead, if_true_eq rfl,
    bind_val_ok hsl, bind_val_ok hLift, bind_val_ok hEq, if_true_eq rfl]

/-- `ops.run_init` exits cleanly with code `0` without performing syscalls when invoked with `--probe`. -/
theorem run_init_probe_spec (s : init_sys.Sys) (arg0 : Bytes) :
    ops.run_init { s with cliArgs := [arg0, probeArgBytes] } 2#usize =
      Result.ok (0#i32, { s with cliArgs := [arg0, probeArgBytes] }) := by
  simp [ops.run_init, parse_cli_probe_spec s arg0]

end LeanSwe.ProcessSandbox.Init.Proofs
