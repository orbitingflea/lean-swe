import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Interface
import LeanSwe.Sqlite.Impl
import LeanSweProofs.Sqlite.SpecTests

namespace LeanSwe.Sqlite.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite

/-- Helper showing `Internal.nonEmptyMsg` never returns `""` when `fallback` is non-empty. -/
theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

/-- Helper showing `pre ++ rest` is non-empty whenever `pre ≠ ""`. -/
theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- Helper showing `Internal.mapRawError` always produces a non-empty error message. -/
theorem mapRawError_ne_empty (raw : SqliteRawError) :
    (Internal.mapRawError raw).message ≠ "" := by
  cases raw with
  | cantOpen _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | busy _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | constraint _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | misuse _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | ioFailure code _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_head_ne_empty "sqlite io failure (" (toString code ++ ")") (by decide))
  | sqliteCodeError code _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_head_ne_empty "sqlite error (" (toString code ++ ")") (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Helper showing `String.fromUTF8?` succeeds on any string's UTF-8 encoding. -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.toUTF8, String.fromUTF8?, s.isValidUTF8]

/-- Helper showing `String.fromUTF8?` succeeds on `s.toByteArray`. -/
theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s :=
  fromUTF8?_toUTF8 s

/-- Helper expanding `s.toUTF8.data.toList` into `flatMap String.utf8EncodeChar`. -/
theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  have h := congrArg (fun ba : ByteArray => ba.data.toList)
    (String.toByteArray_ofList (l := s.toList))
  rw [String.ofList_toList] at h
  simpa [String.toUTF8, List.utf8Encode] using h

/-- Helper distributing `toUTF8.data.toList` over string concatenation. -/
theorem toUTF8_append_data_toList (a b : String) :
    (a ++ b).toUTF8.data.toList = a.toUTF8.data.toList ++ b.toUTF8.data.toList := by
  simp [String.toUTF8, String.toByteArray_append, ByteArray.data_append]

/-- Helper characterizing empty UTF-8 byte list via empty string. -/
theorem toUTF8_data_toList_eq_nil_iff (s : String) :
    s.toUTF8.data.toList = [] ↔ s = "" := by
  constructor
  · intro h
    rw [toUTF8_data_toList] at h
    have hNil : s.toList = [] := by
      cases hl : s.toList with
      | nil => rfl
      | cons c cs =>
        rw [hl] at h
        simp only [List.flatMap_cons, List.append_eq_nil_iff] at h
        exact absurd h.1 String.utf8EncodeChar_ne_nil
    exact String.ext (by simp [hNil])
  · intro hs
    subst hs
    decide

private theorem char_ofNat_lt_128_toNat (b : UInt8) (hb : b.toNat < 128) :
    (Char.ofNat b.toNat).val.toNat = b.toNat := by
  have hvc : Nat.isValidChar b.toNat := by
    simp only [Nat.isValidChar]
    exact Or.inl (Nat.lt_trans hb (by decide))
  simp only [Char.ofNat, hvc, ↓reduceDIte]
  rfl

private theorem mem_utf8EncodeChar_iff_of_lt (b : UInt8) (hb : b.toNat < 128) (c : Char) :
    b ∈ String.utf8EncodeChar c ↔ c = Char.ofNat b.toNat := by
  unfold String.utf8EncodeChar
  dsimp only
  split
  · next h127 =>
    simp only [List.mem_singleton]
    have hlt256 : c.toNat < 256 := Nat.lt_of_le_of_lt h127 (by decide)
    constructor
    · intro heq
      have hnat : b.toNat = c.val.toNat := by
        have := congrArg UInt8.toNat heq
        change b.toNat = c.toNat % 256 at this
        rwa [Nat.mod_eq_of_lt hlt256] at this
      apply Char.ext
      exact UInt32.toNat_inj.mp (by rw [char_ofNat_lt_128_toNat b hb, hnat])
    · intro hc
      subst hc
      apply UInt8.toNat.inj
      have hcnat := char_ofNat_lt_128_toNat b hb
      have h256 : b.toNat < 256 := Nat.lt_trans hb (by decide : 128 < 256)
      change b.toNat = (Char.ofNat b.toNat).val.toNat % 256
      rw [hcnat, Nat.mod_eq_of_lt h256]
  · next hgt =>
    constructor
    · intro hmem
      exfalso
      split at hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> simp at hb <;> omega
      · split at hmem
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl <;> simp at hb <;> omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl | rfl <;> simp at hb <;> omega
    · intro hc
      subst hc
      have hcnat := char_ofNat_lt_128_toNat b hb
      omega

/-- Helper characterizing ASCII byte membership in `s.toUTF8.data.toList`. -/
theorem mem_toUTF8_iff_of_lt (b : UInt8) (hb : b.toNat < 128) (s : String) :
    b ∈ s.toUTF8.data.toList ↔ Char.ofNat b.toNat ∈ s.toList := by
  rw [toUTF8_data_toList, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hmem⟩
    rw [(mem_utf8EncodeChar_iff_of_lt b hb c).mp hmem] at hc
    exact hc
  · intro hmem
    exact ⟨Char.ofNat b.toNat, hmem, (mem_utf8EncodeChar_iff_of_lt b hb _).mpr rfl⟩

/-- Helper characterizing `Internal.hasZeroByte bs = true` via byte `0` membership. -/
theorem hasZeroByte_eq_true_iff (bs : List UInt8) :
    Internal.hasZeroByte bs = true ↔ (0 : UInt8) ∈ bs := by
  induction bs with
  | nil => simp [Internal.hasZeroByte]
  | cons b bs ih =>
    simp only [Internal.hasZeroByte, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (ih.mp h)
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr h)

/-- Helper characterizing `Internal.hasZeroByte s.toUTF8.data.toList = true` via NUL character membership. -/
theorem hasZeroByte_toUTF8_iff (s : String) :
    Internal.hasZeroByte s.toUTF8.data.toList = true ↔ Char.ofNat 0 ∈ s.toList := by
  rw [hasZeroByte_eq_true_iff]
  simpa using mem_toUTF8_iff_of_lt 0 (by decide) s

/-- Helper distributing `Internal.hasZeroByte` over list append. -/
theorem hasZeroByte_append (a b : List UInt8) :
    Internal.hasZeroByte (a ++ b) = (Internal.hasZeroByte a || Internal.hasZeroByte b) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [Internal.hasZeroByte, ih, Bool.or_assoc]

/-- Helper showing `Internal.stripFileScheme` returns `none` when prefix does not equal `"file:"`. -/
theorem stripFileScheme_eq_none_of_take5 (bs : List UInt8)
    (h : bs.take 5 ≠ [0x66, 0x69, 0x6C, 0x65, 0x3A]) :
    Internal.stripFileScheme bs = none := by
  match bs with
  | [] => rfl
  | [_] => simp [Internal.stripFileScheme]
  | [_, _] => simp [Internal.stripFileScheme]
  | [_, _, _] => simp [Internal.stripFileScheme]
  | [_, _, _, _] => simp [Internal.stripFileScheme]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    by_cases h0 : b0 = 0x66 <;> by_cases h1 : b1 = 0x69 <;> by_cases h2 : b2 = 0x6C <;>
      by_cases h3 : b3 = 0x65 <;> by_cases h4 : b4 = 0x3A
    · subst h0 h1 h2 h3 h4
      exact absurd rfl h
    all_goals simp [Internal.stripFileScheme, h0, h1, h2, h3, h4]

private theorem takeBeforeByteAux_eq (d : UInt8) (acc a : List UInt8) (hd : d ∉ a) :
    Internal.takeBeforeByteAux d acc a = acc.reverse ++ a := by
  induction a generalizing acc with
  | nil => simp [Internal.takeBeforeByteAux]
  | cons x xs ih =>
    have hne : x ≠ d := fun heq => hd (by simp [heq])
    have hxs : d ∉ xs := fun hmem => hd (by simp [hmem])
    simp [Internal.takeBeforeByteAux, hne, ih (x :: acc) hxs]

/-- Helper showing `Internal.takeBeforeByte d a = a` when `d ∉ a`. -/
theorem takeBeforeByte_eq_self (d : UInt8) (a : List UInt8) (hd : d ∉ a) :
    Internal.takeBeforeByte d a = a :=
  takeBeforeByteAux_eq d [] a hd

private theorem splitFirstByteAux_eq (d : UInt8) (acc a b : List UInt8) (hd : d ∉ a) :
    Internal.splitFirstByteAux d acc (a ++ d :: b) = (acc.reverse ++ a, some b) := by
  induction a generalizing acc with
  | nil => simp [Internal.splitFirstByteAux]
  | cons x xs ih =>
    have hne : x ≠ d := fun heq => hd (by simp [heq])
    have hxs : d ∉ xs := fun hmem => hd (by simp [hmem])
    simp [Internal.splitFirstByteAux, hne, ih (x :: acc) hxs]

/-- Helper showing `Internal.splitFirstByte d (a ++ d :: b) = (a, some b)` when `d ∉ a`. -/
theorem splitFirstByte_append_left (d : UInt8) (a b : List UInt8) (hd : d ∉ a) :
    Internal.splitFirstByte d (a ++ d :: b) = (a, some b) :=
  splitFirstByteAux_eq d [] a b hd

/-- Helper showing `Internal.stripAuthority bs = bs` when `bs` does not start with `"//"`. -/
theorem stripAuthority_eq_self_of_take2 (bs : List UInt8)
    (h : bs.take 2 ≠ [0x2F, 0x2F]) :
    Internal.stripAuthority bs = bs := by
  match bs with
  | [] => rfl
  | [_] => simp [Internal.stripAuthority]
  | b0 :: b1 :: rest =>
    by_cases h0 : b0 = 0x2F <;> by_cases h1 : b1 = 0x2F
    · subst h0 h1
      exact absurd rfl h
    all_goals simp [Internal.stripAuthority, h0, h1]

/-- Helper showing `.inLineComment` accepts any byte list without `'\n'`. -/
theorem scanSqlTail_inLineComment (bs : List UInt8) (h : (0x0A : UInt8) ∉ bs) :
    Internal.scanSqlTail .inLineComment bs = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hne : b ≠ 0x0A := fun heq => h (by simp [heq])
    have hbs : (0x0A : UInt8) ∉ bs := fun hmem => h (by simp [hmem])
    simp [Internal.scanSqlTail, hne, ih hbs]

/-- Helper resuming `.inSpace` after `'\n'` exits an `.inLineComment`. -/
theorem scanSqlTail_inLineComment_append_nl (bs suf : List UInt8)
    (h : (0x0A : UInt8) ∉ bs) :
    Internal.scanSqlTail .inLineComment (bs ++ 0x0A :: suf) = Internal.scanSqlTail .inSpace suf := by
  induction bs with
  | nil => simp [Internal.scanSqlTail]
  | cons b bs ih =>
    have hne : b ≠ 0x0A := fun heq => h (by simp [heq])
    have hbs : (0x0A : UInt8) ∉ bs := fun hmem => h (by simp [hmem])
    simp [Internal.scanSqlTail, hne, ih hbs]

/-- Helper skipping `'*'`-free bytes inside `.inBlockComment`. -/
theorem scanSqlTail_inBlockComment_append (bs suf : List UInt8)
    (h : (0x2A : UInt8) ∉ bs) :
    Internal.scanSqlTail .inBlockComment (bs ++ suf) = Internal.scanSqlTail .inBlockComment suf := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hne : b ≠ 0x2A := fun heq => h (by simp [heq])
    have hbs : (0x2A : UInt8) ∉ bs := fun hmem => h (by simp [hmem])
    simp [Internal.scanSqlTail, hne, ih hbs]

/-- Helper showing `'/'`-free bytes keep an unclosed block comment rejected. -/
theorem scanSqlTail_unclosed (bs : List UInt8) (h : (0x2F : UInt8) ∉ bs) :
    ∀ st, (st = .inBlockComment ∨ st = .inBlockSawStar) →
      Internal.scanSqlTail st bs = false := by
  induction bs with
  | nil =>
    intro st hst
    rcases hst with rfl | rfl <;> rfl
  | cons b bs ih =>
    intro st hst
    have hne : b ≠ 0x2F := fun heq => h (by simp [heq])
    have hbs : (0x2F : UInt8) ∉ bs := fun hmem => h (by simp [hmem])
    rcases hst with rfl | rfl
    · simp only [Internal.scanSqlTail]
      split
      · exact ih hbs .inBlockSawStar (Or.inr rfl)
      · exact ih hbs .inBlockComment (Or.inl rfl)
    · have hBeq : (b == 0x2F) = false := beq_false_of_ne hne
      rw [Internal.scanSqlTail, hBeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · exact ih hbs .inBlockSawStar (Or.inr rfl)
      · exact ih hbs .inBlockComment (Or.inl rfl)

/-- Helper computing `mockConsumedBytesUpToSemi` after `"SELECT 1;"`. -/
theorem mockConsumedBytesUpToSemi_select1 (suf : List UInt8) :
    mockConsumedBytesUpToSemi ("SELECT 1;".toUTF8.data.toList ++ suf) = 9 := by
  have hBytes : "SELECT 1;".toUTF8.data.toList =
      [0x53, 0x45, 0x4C, 0x45, 0x43, 0x54, 0x20, 0x31, 0x3B] := by decide
  rw [hBytes]
  simp [mockConsumedBytesUpToSemi]

/-- Simp lemma unfolding `DbHandle` BEq. -/
@[simp] theorem dbHandle_beq_eq (a b : DbHandle) :
    (a == b) = (a.id == b.id) := rfl

/-- Simp lemma unfolding `StmtHandle` BEq. -/
@[simp] theorem stmtHandle_beq_eq (a b : StmtHandle) :
    (a == b) = (a.id == b.id && a.dbId == b.dbId) := rfl

/-- Simp lemma reducing `"".toByteArray.data = #[]`. -/
@[simp] theorem empty_data_eq_empty :
    ("".toByteArray.data = #[]) = True := by decide

/-- Simp lemma reducing `"app.db".toByteArray.data = #[]`. -/
@[simp] theorem appDb_data_eq_empty :
    ("app.db".toByteArray.data = #[]) = False := by decide

/-- Simp lemma reducing `":memory:".toByteArray.data = #[]`. -/
@[simp] theorem colonMem_data_eq_empty :
    (":memory:".toByteArray.data = #[]) = False := by decide

/-- Simp lemma reducing `"file:mem?mode=memory".toByteArray.data = #[]`. -/
@[simp] theorem memUri_data_eq_empty :
    ("file:mem?mode=memory".toByteArray.data = #[]) = False := by decide

/-- Simp lemma reducing `Internal.hasZeroByte` on `"SELECT 1"`. -/
@[simp] theorem hasZeroByte_select1 :
    Internal.hasZeroByte "SELECT 1".toByteArray.data.toList = false := by decide

/-- Simp lemma reducing `"SELECT 1"` byte-length check. -/
@[simp] theorem select1_utf8ByteSize :
    (2147483647 < "SELECT 1".utf8ByteSize) = False := by decide

/-- Simp lemma reducing `""` byte-length check. -/
@[simp] theorem empty_utf8ByteSize :
    (2147483647 < "".utf8ByteSize) = False := by decide

/-- Simp lemma reducing `"   \n\t "` byte-length check. -/
@[simp] theorem ws_utf8ByteSize :
    (2147483647 < "   \n\t ".utf8ByteSize) = False := by decide

/-- Simp lemma reducing `Internal.hasZeroByte` on `"app.db"`. -/
@[simp] theorem hasZeroByte_appDb :
    Internal.hasZeroByte "app.db".toByteArray.data.toList = false := by decide

/-- Simp lemma reducing `Internal.hasZeroByte` on `"file:mem?mode=memory"`. -/
@[simp] theorem memUri_hasZeroByte :
    Internal.hasZeroByte "file:mem?mode=memory".toByteArray.data.toList = false := by decide

/-- Simp lemma reducing `Internal.hasZeroByte` on `":memory:"`. -/
@[simp] theorem colonMem_hasZeroByte :
    Internal.hasZeroByte ":memory:".toByteArray.data.toList = false := by decide

/-- Helper stepping `" --"` into `.inLineComment`. -/
theorem scanSqlTail_space_dash_dash (rest : List UInt8) :
    Internal.scanSqlTail .normal (0x20 :: 0x2D :: 0x2D :: rest) =
      Internal.scanSqlTail .inLineComment rest := rfl

/-- Helper stepping `" /*"` into `.inBlockComment`. -/
theorem scanSqlTail_space_slash_star (rest : List UInt8) :
    Internal.scanSqlTail .normal (0x20 :: 0x2F :: 0x2A :: rest) =
      Internal.scanSqlTail .inBlockComment rest := rfl

/-- Simp lemma reducing `Bind.bind` in `Id`. -/
@[simp] theorem id_bind_eq {α β : Type} (x : α) (f : α → β) :
    Bind.bind (m := Id) x f = f x := rfl

/-- Simp lemma reducing `Pure.pure` in `Id`. -/
@[simp] theorem id_pure_eq {α : Type} (x : α) :
    Pure.pure (f := Id) x = x := rfl

/-- Simp lemma reducing `StateT.bind` applied to a state in `Id`. -/
@[simp] theorem stateT_bind_apply {σ α β : Type} (x : StateT σ Id α) (f : α → StateT σ Id β) (s : σ) :
    StateT.bind x f s = (let p := x s; f p.1 p.2) := rfl

/-- Simp lemma reducing `StateT.pure` applied to a state in `Id`. -/
@[simp] theorem stateT_pure_apply {σ α : Type} (a : α) (s : σ) :
    StateT.pure (m := Id) a s = (a, s) := rfl

/-- Simp lemma reducing `StateT.run` applied to a state in `Id`. -/
@[simp] theorem stateT_run_apply {σ α : Type} (x : StateT σ Id α) (s : σ) :
    StateT.run x s = x s := rfl

/-- Witness helper for `.invalidArgument` rejection assertions in `openDb`. -/
theorem assert_invalidInput_record {α : Type} (msg : String) :
    ∃ e : SqliteError,
      (Except.error ({
        kind := SqliteErrorKind.invalidInput
        message := Internal.nonEmptyMsg "invalid sqlite argument" msg
      } : SqliteError) : Except SqliteError α) = Except.error e ∧
        e.kind = SqliteErrorKind.invalidInput ∧ e.message ≠ "" :=
  ⟨_, rfl, rfl, nonEmptyMsg_ne_empty _ _ (by decide)⟩

/-- Helper turning a decidable `SqliteErrorKind` check into an existential witness. -/
theorem errKind_eq_of_isErrorKind {α : Type} (r : Except SqliteError α) (k : SqliteErrorKind)
    (h : (match r with | .error e => e.kind == k | .ok _ => false) = true) :
    ∃ e, r = .error e ∧ e.kind = k := by
  cases r with
  | ok _ => cases h
  | error e =>
    dsimp only at h
    refine ⟨e, rfl, ?_⟩
    cases hk : e.kind <;> cases k <;> rw [hk] at h <;> first | rfl | cases h

private theorem list_drop_eq_cons {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  (List.getElem_cons_drop hi).symm

@[simp] theorem byteArray_size_eq_zero (bs : ByteArray) :
    (bs.size == 0) = bs.data.toList.isEmpty := by
  have hLen : bs.size = bs.data.toList.length := bs.data.length_toList.symm
  cases h : bs.data.toList with
  | nil => simp [hLen, h]
  | cons _ _ =>
    have hPos : bs.size ≠ 0 := by rw [hLen, h]; simp
    simp [beq_false_of_ne hPos]

theorem utf8ByteSize_eq (s : String) : s.utf8ByteSize = s.toUTF8.size :=
  String.size_toByteArray.symm

private theorem hasZeroByteBaAux_eq (bs : ByteArray) :
    ∀ n idx, bs.size - idx = n →
      Internal.hasZeroByteBaAux bs idx n = Internal.hasZeroByte (bs.data.toList.drop idx)
  | 0, idx, hn => by
    have hGe : bs.size ≤ idx := by omega
    have hLen : bs.data.toList.length = bs.size := bs.data.length_toList
    have hDrop : bs.data.toList.drop idx = [] :=
      List.drop_eq_nil_of_le (hLen.symm ▸ hGe)
    simp [Internal.hasZeroByteBaAux, hDrop, Internal.hasZeroByte]
  | n + 1, idx, hn => by
    have hLt : idx < bs.size := by omega
    have hLtLen : idx < bs.data.toList.length := bs.data.length_toList ▸ hLt
    have hDrop : bs.data.toList.drop idx = bs[idx] :: bs.data.toList.drop (idx + 1) :=
      list_drop_eq_cons bs.data.toList idx hLtLen
    have hRec := hasZeroByteBaAux_eq bs n (idx + 1) (by omega)
    unfold Internal.hasZeroByteBaAux
    simp only [hLt, ↓reduceDIte, hDrop, Internal.hasZeroByte]
    cases hb : bs[idx] == 0 <;> simp [hRec]

@[simp] theorem hasZeroByteBa_zero (bs : ByteArray) :
    Internal.hasZeroByteBa bs 0 = Internal.hasZeroByte bs.data.toList := by
  simpa [Internal.hasZeroByteBa] using hasZeroByteBaAux_eq bs bs.size 0 (by simp)

private theorem scanSqlTailBaAux_eq (bs : ByteArray) :
    ∀ n st idx, bs.size - idx = n →
      Internal.scanSqlTailBaAux st bs idx n = Internal.scanSqlTail st (bs.data.toList.drop idx)
  | 0, st, idx, hn => by
    have hGe : bs.size ≤ idx := by omega
    have hLen : bs.data.toList.length = bs.size := bs.data.length_toList
    have hDrop : bs.data.toList.drop idx = [] :=
      List.drop_eq_nil_of_le (hLen.symm ▸ hGe)
    simp only [Internal.scanSqlTailBaAux, hDrop]
    cases st <;> rfl
  | n + 1, st, idx, hn => by
    have hLt : idx < bs.size := by omega
    have hLtLen : idx < bs.data.toList.length := bs.data.length_toList ▸ hLt
    have hDrop : bs.data.toList.drop idx = bs[idx] :: bs.data.toList.drop (idx + 1) :=
      list_drop_eq_cons bs.data.toList idx hLtLen
    have ih := fun st' => scanSqlTailBaAux_eq bs n st' (idx + 1) (by omega)
    unfold Internal.scanSqlTailBaAux
    simp only [hLt, ↓reduceDIte, hDrop]
    cases st <;> simp only [Internal.scanSqlTail, ih]

@[simp] theorem scanSqlTailBa_eq (st : Internal.SqlTailScanState) (bs : ByteArray) (idx : Nat) :
    Internal.scanSqlTailBa st bs idx = Internal.scanSqlTail st (bs.data.toList.drop idx) :=
  scanSqlTailBaAux_eq bs (bs.size - idx) st idx rfl

private def sliceBytes (bs : ByteArray) (start stop : Nat) : List UInt8 :=
  (bs.data.toList.drop start).take (stop - start)

private theorem sliceBytes_step (bs : ByteArray) (idx stop : Nat) (h : idx < stop ∧ idx < bs.size) :
    sliceBytes bs idx stop = bs[idx] :: sliceBytes bs (idx + 1) stop := by
  have hLtLen : idx < bs.data.toList.length := bs.data.length_toList ▸ h.2
  have hDrop : bs.data.toList.drop idx = bs[idx] :: bs.data.toList.drop (idx + 1) :=
    list_drop_eq_cons bs.data.toList idx hLtLen
  have hSub : stop - idx = (stop - (idx + 1)) + 1 := by omega
  simp only [sliceBytes, hDrop, hSub, List.take_succ_cons]

private theorem sliceBytes_empty (bs : ByteArray) (idx stop : Nat) (h : ¬ (idx < stop ∧ idx < bs.size)) :
    sliceBytes bs idx stop = [] := by
  by_cases hStop : idx < stop
  · have hGe : bs.data.toList.length ≤ idx := by
      have : bs.size ≤ idx := by omega
      exact bs.data.length_toList ▸ this
    simp [sliceBytes, List.drop_eq_nil_of_le hGe]
  · have hZero : stop - idx = 0 := by omega
    simp [sliceBytes, hZero]

private def feedUriMatchBytes (rem? : Option (List UInt8)) (xs : List UInt8) : Option (List UInt8) :=
  xs.foldl Internal.feedUriMatchByte rem?

private theorem feedUriMatchBytes_append (rem? : Option (List UInt8)) (xs ys : List UInt8) :
    feedUriMatchBytes rem? (xs ++ ys) = feedUriMatchBytes (feedUriMatchBytes rem? xs) ys :=
  List.foldl_append

private theorem feedUriMatchBytes_none (xs : List UInt8) :
    feedUriMatchBytes none xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem feedUriMatchBytes_eq_some_nil (pat xs : List UInt8) :
    (feedUriMatchBytes (some pat) xs == some []) = (xs == pat) := by
  induction xs generalizing pat with
  | nil =>
    cases pat <;> rfl
  | cons x xs ih =>
    cases pat with
    | nil =>
      change (feedUriMatchBytes none xs == some []) = false
      rw [feedUriMatchBytes_none]
      rfl
    | cons p ps =>
      change (feedUriMatchBytes (if x == p then some ps else none) xs == some []) =
        (x == p && xs == ps)
      cases hxp : x == p
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        rw [feedUriMatchBytes_none]
        rfl
      · simp only [↓reduceIte, Bool.true_and]
        exact ih ps

private theorem decodeUriMatchBaAux_eq (bs : ByteArray) (stop : Nat) (pat : List UInt8) :
    ∀ fuel st acc idx,
      stop - idx ≤ fuel →
      Internal.decodeUriMatchBaAux bs stop st (feedUriMatchBytes (some pat) acc.reverse) idx fuel =
        (Internal.decodeUriBytesAux acc st (sliceBytes bs idx stop) == pat)
  | 0, st, acc, idx, hFuel => by
    have hGe : ¬ (idx < stop ∧ idx < bs.size) := by omega
    rw [sliceBytes_empty bs idx stop hGe]
    cases st with
    | normal =>
      simp only [Internal.decodeUriMatchBaAux, Internal.decodeUriBytesAux]
      exact feedUriMatchBytes_eq_some_nil pat acc.reverse
    | sawPct =>
      simp only [Internal.decodeUriMatchBaAux, Internal.decodeUriBytesAux, List.reverse_cons]
      rw [← feedUriMatchBytes_eq_some_nil pat (acc.reverse ++ [0x25]), feedUriMatchBytes_append]
      rfl
    | sawPctHex hi _ =>
      simp only [Internal.decodeUriMatchBaAux, Internal.decodeUriBytesAux, List.reverse_cons]
      rw [← feedUriMatchBytes_eq_some_nil pat ((acc.reverse ++ [0x25]) ++ [hi]),
        feedUriMatchBytes_append, feedUriMatchBytes_append]
      rfl
  | fuel + 1, st, acc, idx, hFuel => by
    by_cases h : idx < stop ∧ idx < bs.size
    · rw [sliceBytes_step bs idx stop h]
      have hNext : stop - (idx + 1) ≤ fuel := by omega
      cases st with
      | normal =>
        unfold Internal.decodeUriMatchBaAux
        split
        · dsimp only [Internal.decodeUriBytesAux]
          cases hPct : bs[idx] == 0x25
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hAcc :
                Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) bs[idx] =
                  feedUriMatchBytes (some pat) (bs[idx] :: acc).reverse := by
              simp only [List.reverse_cons, feedUriMatchBytes_append]
              rfl
            rw [hAcc]
            exact decodeUriMatchBaAux_eq bs stop pat fuel .normal (bs[idx] :: acc) (idx + 1) hNext
          · simp only [↓reduceIte]
            exact decodeUriMatchBaAux_eq bs stop pat fuel .sawPct acc (idx + 1) hNext
        · contradiction
      | sawPct =>
        unfold Internal.decodeUriMatchBaAux
        split
        · dsimp only [Internal.decodeUriBytesAux]
          cases hHex : Internal.hexByteVal? bs[idx] with
          | some v1 =>
            exact decodeUriMatchBaAux_eq bs stop pat fuel (.sawPctHex bs[idx] v1) acc (idx + 1) hNext
          | none =>
            cases hPct : bs[idx] == 0x25
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hAcc :
                  Internal.feedUriMatchByte
                      (Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) 0x25) bs[idx] =
                    feedUriMatchBytes (some pat) (bs[idx] :: 0x25 :: acc).reverse := by
                simp only [List.reverse_cons, feedUriMatchBytes_append]
                rfl
              rw [hAcc]
              exact decodeUriMatchBaAux_eq bs stop pat fuel .normal (bs[idx] :: 0x25 :: acc) (idx + 1) hNext
            · simp only [↓reduceIte]
              have hAcc :
                  Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) 0x25 =
                    feedUriMatchBytes (some pat) (0x25 :: acc).reverse := by
                simp only [List.reverse_cons, feedUriMatchBytes_append]
                rfl
              rw [hAcc]
              exact decodeUriMatchBaAux_eq bs stop pat fuel .sawPct (0x25 :: acc) (idx + 1) hNext
        · contradiction
      | sawPctHex hiByte v1 =>
        unfold Internal.decodeUriMatchBaAux
        split
        · dsimp only [Internal.decodeUriBytesAux]
          cases hHex : Internal.hexByteVal? bs[idx] with
          | some v2 =>
            dsimp only
            cases hZero : (((v1 <<< 4) ||| v2) == 0 : Bool)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hAcc :
                  Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) ((v1 <<< 4) ||| v2) =
                    feedUriMatchBytes (some pat) (((v1 <<< 4) ||| v2) :: acc).reverse := by
                simp only [List.reverse_cons, feedUriMatchBytes_append]
                rfl
              rw [hAcc]
              exact decodeUriMatchBaAux_eq bs stop pat fuel .normal (((v1 <<< 4) ||| v2) :: acc) (idx + 1) hNext
            · simp only [↓reduceIte]
              exact feedUriMatchBytes_eq_some_nil pat acc.reverse
          | none =>
            cases hPct : bs[idx] == 0x25
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hAcc :
                  Internal.feedUriMatchByte
                      (Internal.feedUriMatchByte
                        (Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) 0x25) hiByte)
                      bs[idx] =
                    feedUriMatchBytes (some pat) (bs[idx] :: hiByte :: 0x25 :: acc).reverse := by
                simp only [List.reverse_cons, feedUriMatchBytes_append]
                rfl
              rw [hAcc]
              exact decodeUriMatchBaAux_eq bs stop pat fuel .normal
                (bs[idx] :: hiByte :: 0x25 :: acc) (idx + 1) hNext
            · simp only [↓reduceIte]
              have hAcc :
                  Internal.feedUriMatchByte
                      (Internal.feedUriMatchByte (feedUriMatchBytes (some pat) acc.reverse) 0x25) hiByte =
                    feedUriMatchBytes (some pat) (hiByte :: 0x25 :: acc).reverse := by
                simp only [List.reverse_cons, feedUriMatchBytes_append]
                rfl
              rw [hAcc]
              exact decodeUriMatchBaAux_eq bs stop pat fuel .sawPct (hiByte :: 0x25 :: acc) (idx + 1) hNext
        · contradiction
    · rw [sliceBytes_empty bs idx stop h]
      cases st with
      | normal =>
        unfold Internal.decodeUriMatchBaAux
        split
        · contradiction
        · simp only [Internal.decodeUriBytesAux]
          exact feedUriMatchBytes_eq_some_nil pat acc.reverse
      | sawPct =>
        unfold Internal.decodeUriMatchBaAux
        split
        · contradiction
        · simp only [Internal.decodeUriBytesAux, List.reverse_cons]
          rw [← feedUriMatchBytes_eq_some_nil pat (acc.reverse ++ [0x25]), feedUriMatchBytes_append]
          rfl
      | sawPctHex hi _ =>
        unfold Internal.decodeUriMatchBaAux
        split
        · contradiction
        · simp only [Internal.decodeUriBytesAux, List.reverse_cons]
          rw [← feedUriMatchBytes_eq_some_nil pat ((acc.reverse ++ [0x25]) ++ [hi]),
            feedUriMatchBytes_append, feedUriMatchBytes_append]
          rfl

private theorem decodeUriMatchBa_eq (bs : ByteArray) (start stop : Nat) (pat : List UInt8) :
    Internal.decodeUriMatchBa bs start stop pat =
      (Internal.decodeUriComponent (sliceBytes bs start stop) == pat) :=
  decodeUriMatchBaAux_eq bs stop pat (stop - start) .normal [] start (Nat.le_refl _)

private theorem findByteBeforeAux_bounds (bs : ByteArray) (d : UInt8) (stop : Nat) :
    ∀ fuel idx, idx ≤ stop →
      idx ≤ Internal.findByteBeforeAux bs d stop idx fuel ∧
        Internal.findByteBeforeAux bs d stop idx fuel ≤ stop
  | 0, idx, h => ⟨h, Nat.le_refl _⟩
  | fuel + 1, idx, h => by
    unfold Internal.findByteBeforeAux
    split
    · split
      · exact ⟨Nat.le_refl _, by omega⟩
      · have hRec := findByteBeforeAux_bounds bs d stop fuel (idx + 1) (by omega)
        exact ⟨Nat.le_trans (Nat.le_succ _) hRec.1, hRec.2⟩
    · exact ⟨h, Nat.le_refl _⟩

private theorem findByteBefore_bounds (bs : ByteArray) (d : UInt8) (idx stop : Nat) (h : idx ≤ stop) :
    idx ≤ Internal.findByteBefore bs d idx stop ∧ Internal.findByteBefore bs d idx stop ≤ stop :=
  findByteBeforeAux_bounds bs d stop (stop - idx) idx h

private theorem findByteBeforeAux_takeBefore (bs : ByteArray) (d : UInt8) (stop : Nat) (hStop : stop ≤ bs.size) :
    ∀ fuel idx acc, idx ≤ stop → stop - idx ≤ fuel →
      acc.reverse ++ sliceBytes bs idx (Internal.findByteBeforeAux bs d stop idx fuel) =
        Internal.takeBeforeByteAux d acc (sliceBytes bs idx stop)
  | 0, idx, acc, hIdx, hFuel => by
    have hEq : idx = stop := by omega
    subst hEq
    have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
    rw [sliceBytes_empty bs idx idx hGe, Internal.findByteBeforeAux]
    rw [sliceBytes_empty bs idx idx hGe, Internal.takeBeforeByteAux]
    simp
  | fuel + 1, idx, acc, hIdx, hFuel => by
    by_cases hLt : idx < stop
    · have hIn : idx < stop ∧ idx < bs.size := ⟨hLt, Nat.lt_of_lt_of_le hLt hStop⟩
      rw [sliceBytes_step bs idx stop hIn]
      unfold Internal.findByteBeforeAux
      split
      · dsimp only [Internal.takeBeforeByteAux]
        cases hEq : bs[idx] == d
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hIdxLtM : idx < Internal.findByteBeforeAux bs d stop (idx + 1) fuel :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (findByteBeforeAux_bounds bs d stop fuel (idx + 1) hLt).1
          rw [sliceBytes_step bs idx _ ⟨hIdxLtM, hIn.2⟩]
          have hRec := findByteBeforeAux_takeBefore bs d stop hStop fuel (idx + 1) (bs[idx] :: acc)
            hLt (by omega)
          simpa [List.reverse_cons, List.append_assoc] using hRec
        · simp only [↓reduceIte]
          have hEmpty : sliceBytes bs idx idx = [] := sliceBytes_empty bs idx idx (by omega)
          rw [hEmpty, List.append_nil]
      · contradiction
    · have hEq : idx = stop := Nat.le_antisymm hIdx (Nat.le_of_not_lt hLt)
      subst hEq
      have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
      unfold Internal.findByteBeforeAux
      split
      · contradiction
      · rw [sliceBytes_empty bs idx idx hGe]
        simp [Internal.takeBeforeByteAux]

private theorem findByteBeforeAux_splitFirst (bs : ByteArray) (d : UInt8) (stop : Nat) (hStop : stop ≤ bs.size) :
    ∀ fuel idx acc, idx ≤ stop → stop - idx ≤ fuel →
      let m := Internal.findByteBeforeAux bs d stop idx fuel
      Internal.splitFirstByteAux d acc (sliceBytes bs idx stop) =
        (acc.reverse ++ sliceBytes bs idx m,
          if m < stop then some (sliceBytes bs (m + 1) stop) else none)
  | 0, idx, acc, hIdx, hFuel => by
    have hEq : idx = stop := by omega
    subst hEq
    have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
    simp [Internal.findByteBeforeAux, sliceBytes_empty bs idx idx hGe, Internal.splitFirstByteAux]
  | fuel + 1, idx, acc, hIdx, hFuel => by
    by_cases hLt : idx < stop
    · have hIn : idx < stop ∧ idx < bs.size := ⟨hLt, Nat.lt_of_lt_of_le hLt hStop⟩
      rw [sliceBytes_step bs idx stop hIn]
      unfold Internal.findByteBeforeAux
      split
      · dsimp only [Internal.splitFirstByteAux]
        cases hEq : bs[idx] == d
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hIdxLtM : idx < Internal.findByteBeforeAux bs d stop (idx + 1) fuel :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (findByteBeforeAux_bounds bs d stop fuel (idx + 1) hLt).1
          rw [sliceBytes_step bs idx _ ⟨hIdxLtM, hIn.2⟩]
          have hRec := findByteBeforeAux_splitFirst bs d stop hStop fuel (idx + 1) (bs[idx] :: acc)
            hLt (by omega)
          simpa [List.reverse_cons, List.append_assoc] using hRec
        · simp only [↓reduceIte, hLt]
          have hEmpty : sliceBytes bs idx idx = [] := sliceBytes_empty bs idx idx (by omega)
          rw [hEmpty, List.append_nil]
      · contradiction
    · have hEq : idx = stop := Nat.le_antisymm hIdx (Nat.le_of_not_lt hLt)
      subst hEq
      have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
      unfold Internal.findByteBeforeAux
      split
      · contradiction
      · dsimp only
        rw [sliceBytes_empty bs idx idx hGe]
        simp [Internal.splitFirstByteAux, hLt]

private theorem findByteBefore_takeBefore (bs : ByteArray) (d : UInt8) (idx stop : Nat)
    (hIdx : idx ≤ stop) (hStop : stop ≤ bs.size) :
    Internal.takeBeforeByte d (sliceBytes bs idx stop) =
      sliceBytes bs idx (Internal.findByteBefore bs d idx stop) :=
  (findByteBeforeAux_takeBefore bs d stop hStop (stop - idx) idx [] hIdx (Nat.le_refl _)).symm

private theorem findByteBefore_splitFirst (bs : ByteArray) (d : UInt8) (idx stop : Nat)
    (hIdx : idx ≤ stop) (hStop : stop ≤ bs.size) :
    Internal.splitFirstByte d (sliceBytes bs idx stop) =
      (sliceBytes bs idx (Internal.findByteBefore bs d idx stop),
        if Internal.findByteBefore bs d idx stop < stop then
          some (sliceBytes bs (Internal.findByteBefore bs d idx stop + 1) stop)
        else none) := by
  have h := findByteBeforeAux_splitFirst bs d stop hStop (stop - idx) idx [] hIdx (Nat.le_refl _)
  dsimp only at h
  rw [List.reverse_nil, List.nil_append] at h
  exact h

private theorem stripAuthorityIdx_eq (bs : ByteArray) (start stop : Nat)
    (hStart : start ≤ stop) (hStop : stop ≤ bs.size) :
    Internal.stripAuthority (sliceBytes bs start stop) =
      sliceBytes bs (Internal.stripAuthorityIdx bs start stop) stop := by
  by_cases h2 : start + 1 < stop
  · have hIn2 : start + 1 < stop ∧ start + 1 < bs.size := ⟨h2, Nat.lt_of_lt_of_le h2 hStop⟩
    have hIn0 : start < stop ∧ start < bs.size := ⟨by omega, by omega⟩
    have hIn1 : start + 1 < stop ∧ start + 1 < bs.size := hIn2
    rw [sliceBytes_step bs start stop hIn0, sliceBytes_step bs (start + 1) stop hIn1]
    unfold Internal.stripAuthorityIdx
    split
    · cases h0 : bs[start] == 0x2F <;> cases h1 : bs[start + 1] == 0x2F
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        unfold Internal.stripAuthority
        split
        · next _ _ heq =>
          have hEq0 : bs[start] = 0x2F := (List.cons.inj heq).1
          simp [hEq0] at h0
        · rw [← sliceBytes_step bs (start + 1) stop hIn1, ← sliceBytes_step bs start stop hIn0]
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        unfold Internal.stripAuthority
        split
        · next _ _ heq =>
          have hEq0 : bs[start] = 0x2F := (List.cons.inj heq).1
          simp [hEq0] at h0
        · rw [← sliceBytes_step bs (start + 1) stop hIn1, ← sliceBytes_step bs start stop hIn0]
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        unfold Internal.stripAuthority
        split
        · next _ _ heq =>
          have hEq1 : bs[start + 1] = 0x2F := (List.cons.inj (List.cons.inj heq).2).1
          simp [hEq1] at h1
        · rw [← sliceBytes_step bs (start + 1) stop hIn1, ← sliceBytes_step bs start stop hIn0]
      · simp only [Bool.and_self, ↓reduceIte]
        have hb0 : bs[start] = 0x2F := beq_iff_eq.mp h0
        have hb1 : bs[start + 1] = 0x2F := beq_iff_eq.mp h1
        rw [hb0, hb1]
        dsimp only [Internal.stripAuthority]
        clear h0 h1 hb0 hb1
        suffices hGen : ∀ fuel idx, idx ≤ stop → stop - idx ≤ fuel →
            Internal.dropUntilSlash (sliceBytes bs idx stop) =
              sliceBytes bs (Internal.findByteBeforeAux bs 0x2F stop idx fuel) stop by
          exact hGen (stop - (start + 2)) (start + 2) (by omega) (Nat.le_refl _)
        intro fuel
        induction fuel with
        | zero =>
          intro idx hIdx hF
          have hEq : idx = stop := by omega
          subst hEq
          have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
          rw [sliceBytes_empty bs idx idx hGe, Internal.findByteBeforeAux,
            sliceBytes_empty bs idx idx hGe]
          rfl
        | succ fuel ih =>
          intro idx hIdx hF
          by_cases hLt : idx < stop
          · have hIn : idx < stop ∧ idx < bs.size := ⟨hLt, Nat.lt_of_lt_of_le hLt hStop⟩
            rw [sliceBytes_step bs idx stop hIn]
            unfold Internal.findByteBeforeAux
            split
            · dsimp only [Internal.dropUntilSlash]
              cases hs : bs[idx] == 0x2F
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih (idx + 1) hLt (by omega)
              · simp only [↓reduceIte]
                rw [sliceBytes_step bs idx stop hIn]
            · contradiction
          · have hEq : idx = stop := Nat.le_antisymm hIdx (Nat.le_of_not_lt hLt)
            subst hEq
            have hGe : ¬ (idx < idx ∧ idx < bs.size) := by omega
            unfold Internal.findByteBeforeAux
            split
            · contradiction
            · rw [sliceBytes_empty bs idx idx hGe]
              rfl
    · contradiction
  · have hNotIn2 : ¬ (start + 1 < stop ∧ start + 1 < bs.size) := by omega
    unfold Internal.stripAuthorityIdx
    split
    · contradiction
    · have hLenLe1 : (sliceBytes bs start stop).length ≤ 1 := by
        simp [sliceBytes, List.length_take]
        omega
      cases hSl : sliceBytes bs start stop with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => simp [Internal.stripAuthority]
        | cons y ys =>
          rw [hSl] at hLenLe1
          simp at hLenLe1

private theorem splitOnByteAux_nil_of_append (d : UInt8) (cur : List UInt8) (acc : List (List UInt8)) (xs : List UInt8) :
    Internal.splitOnByteAux d cur acc xs = acc.reverse ++ Internal.splitOnByteAux d cur [] xs := by
  induction xs generalizing cur acc with
  | nil =>
    simp [Internal.splitOnByteAux, List.reverse_cons]
  | cons x xs ih =>
    unfold Internal.splitOnByteAux
    split
    · rw [ih [] (cur.reverse :: acc), ih [] [cur.reverse]]
      simp [List.append_assoc]
    · exact ih (x :: cur) acc

private theorem splitOnByte_step_found (d : UInt8) (bs : ByteArray) (stop : Nat) (hStop : stop ≤ bs.size) :
    ∀ idx, idx ≤ stop →
      Internal.splitOnByte d (sliceBytes bs idx stop) =
        sliceBytes bs idx (Internal.findByteBefore bs d idx stop) ::
          if Internal.findByteBefore bs d idx stop < stop then
            Internal.splitOnByte d (sliceBytes bs (Internal.findByteBefore bs d idx stop + 1) stop)
          else [] := by
  intro idx hIdx
  suffices hGen : ∀ fuel j cur, j ≤ stop → stop - j ≤ fuel →
      Internal.splitOnByteAux d cur [] (sliceBytes bs j stop) =
        (cur.reverse ++ sliceBytes bs j (Internal.findByteBeforeAux bs d stop j fuel)) ::
          if Internal.findByteBeforeAux bs d stop j fuel < stop then
            Internal.splitOnByte d (sliceBytes bs (Internal.findByteBeforeAux bs d stop j fuel + 1) stop)
          else [] by
    have h := hGen (stop - idx) idx [] hIdx (Nat.le_refl _)
    rw [List.reverse_nil, List.nil_append] at h
    exact h
  intro fuel
  induction fuel with
  | zero =>
    intro j cur hJ hF
    have hEq : j = stop := by omega
    subst hEq
    have hGe : ¬ (j < j ∧ j < bs.size) := by omega
    simp [Internal.findByteBeforeAux, sliceBytes_empty bs j j hGe, Internal.splitOnByteAux]
  | succ fuel ih =>
    intro j cur hJ hF
    by_cases hLt : j < stop
    · have hIn : j < stop ∧ j < bs.size := ⟨hLt, Nat.lt_of_lt_of_le hLt hStop⟩
      rw [sliceBytes_step bs j stop hIn]
      unfold Internal.findByteBeforeAux
      split
      · dsimp only [Internal.splitOnByteAux]
        cases hEq : bs[j] == d
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hJLtM : j < Internal.findByteBeforeAux bs d stop (j + 1) fuel :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (findByteBeforeAux_bounds bs d stop fuel (j + 1) hLt).1
          rw [sliceBytes_step bs j _ ⟨hJLtM, hIn.2⟩]
          have hRec := ih (j + 1) (bs[j] :: cur) hLt (by omega)
          simpa [List.reverse_cons, List.append_assoc] using hRec
        · simp only [↓reduceIte, hLt]
          have hEmpty : sliceBytes bs j j = [] := sliceBytes_empty bs j j (by omega)
          rw [hEmpty, List.append_nil, splitOnByteAux_nil_of_append d [] [cur.reverse]]
          rfl
      · contradiction
    · have hEq : j = stop := Nat.le_antisymm hJ (Nat.le_of_not_lt hLt)
      subst hEq
      have hGe : ¬ (j < j ∧ j < bs.size) := by omega
      unfold Internal.findByteBeforeAux
      split
      · contradiction
      · rw [sliceBytes_empty bs j j hGe]
        simp [Internal.splitOnByteAux]

private theorem extractLastUriModeFlagsBaAux_eq (bs : ByteArray) (stop : Nat) (hStop : stop ≤ bs.size) :
    ∀ fuel (cur? : Option (List UInt8)) idx,
      idx ≤ stop → stop - idx < fuel →
      Internal.extractLastUriModeFlagsBaAux bs stop
          (cur? == some Internal.memoryModeBytes, cur? == some Internal.roModeBytes) idx fuel =
        let res := Internal.extractLastUriModeAux cur? (Internal.splitOnByte 0x26 (sliceBytes bs idx stop))
        (res == some Internal.memoryModeBytes, res == some Internal.roModeBytes)
  | 0, _, _, _, hFuel => by omega
  | fuel + 1, cur?, idx, hIdx, hFuel => by
    unfold Internal.extractLastUriModeFlagsBaAux
    dsimp only
    have hSegSplit := splitOnByte_step_found 0x26 bs stop hStop idx hIdx
    rw [hSegSplit]
    have hSegBounds := findByteBefore_bounds bs 0x26 idx stop hIdx
    have hSplitEq := findByteBefore_splitFirst bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop)
      hSegBounds.1 (Nat.le_trans hSegBounds.2 hStop)
    rw [Internal.extractLastUriModeAux, hSplitEq]
    rw [decodeUriMatchBa_eq bs idx
      (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop))
      Internal.modeKeyBytes]
    have hStepEq :
        (if Internal.decodeUriComponent
              (sliceBytes bs idx (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop))) ==
            Internal.modeKeyBytes then
            if Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) <
                Internal.findByteBefore bs 0x26 idx stop then
              (Internal.decodeUriMatchBa bs
                  (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) + 1)
                  (Internal.findByteBefore bs 0x26 idx stop) Internal.memoryModeBytes,
               Internal.decodeUriMatchBa bs
                  (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) + 1)
                  (Internal.findByteBefore bs 0x26 idx stop) Internal.roModeBytes)
            else (false, false)
          else (cur? == some Internal.memoryModeBytes, cur? == some Internal.roModeBytes)) =
          let next? :=
            if Internal.decodeUriComponent
                  (sliceBytes bs idx (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop))) ==
                Internal.modeKeyBytes then
              some (match
                if Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) <
                    Internal.findByteBefore bs 0x26 idx stop then
                  some (sliceBytes bs
                    (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) + 1)
                    (Internal.findByteBefore bs 0x26 idx stop))
                else none with
                | none => []
                | some rv => Internal.decodeUriComponent rv)
            else cur?
          (next? == some Internal.memoryModeBytes, next? == some Internal.roModeBytes) := by
      cases Internal.decodeUriComponent
          (sliceBytes bs idx (Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop))) ==
          Internal.modeKeyBytes
      · rfl
      · simp only [↓reduceIte]
        by_cases hLtEq :
            Internal.findByteBefore bs 0x3D idx (Internal.findByteBefore bs 0x26 idx stop) <
              Internal.findByteBefore bs 0x26 idx stop
        · simp only [hLtEq, ↓reduceIte, decodeUriMatchBa_eq]
          rfl
        · simp only [hLtEq, ↓reduceIte]
          decide
    rw [hStepEq]
    by_cases hSegLt : Internal.findByteBefore bs 0x26 idx stop < stop
    · simp only [hSegLt, ↓reduceIte]
      have hIdx2 : Internal.findByteBefore bs 0x26 idx stop + 1 ≤ stop := hSegLt
      have hNextFuel : stop - (Internal.findByteBefore bs 0x26 idx stop + 1) < fuel := by
        have : idx ≤ Internal.findByteBefore bs 0x26 idx stop := hSegBounds.1
        omega
      exact extractLastUriModeFlagsBaAux_eq bs stop hStop fuel _
        (Internal.findByteBefore bs 0x26 idx stop + 1) hIdx2 hNextFuel
    · simp only [hSegLt, ↓reduceIte]
      rfl

@[simp] theorem classifyPathBytesBa_eq (bs : ByteArray) :
    Internal.classifyPathBytesBa bs = Internal.classifyPathBytes bs.data.toList := by
  have hGet (i : Nat) (hi : i < bs.size) :
      bs[i] = bs.data.toList[i]'(bs.data.length_toList ▸ hi) := rfl
  have hExact : Internal.isExactColonMemoryBa bs = (bs.data.toList == Internal.colonMemoryColonBytes) := by
    unfold Internal.isExactColonMemoryBa
    split
    · next hBeq =>
      have hEqSz : bs.size = 8 := beq_iff_eq.mp hBeq
      have hLen : bs.data.toList.length = 8 := bs.data.length_toList.trans hEqSz
      match hL : bs.data.toList with
      | [b0, b1, b2, b3, b4, b5, b6, b7] =>
        have hg0 : bs[0] = b0 := by simp [hGet, hL]
        have hg1 : bs[1] = b1 := by simp [hGet, hL]
        have hg2 : bs[2] = b2 := by simp [hGet, hL]
        have hg3 : bs[3] = b3 := by simp [hGet, hL]
        have hg4 : bs[4] = b4 := by simp [hGet, hL]
        have hg5 : bs[5] = b5 := by simp [hGet, hL]
        have hg6 : bs[6] = b6 := by simp [hGet, hL]
        have hg7 : bs[7] = b7 := by simp [hGet, hL]
        simp [hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, Internal.colonMemoryColonBytes, Bool.and_assoc]
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] |
        [_, _, _, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
        simp [hL] at hLen
    · next hNot8 =>
      have hNe : bs.size ≠ 8 := by simpa using hNot8
      have hNeLen : bs.data.toList.length ≠ 8 := by simpa [bs.data.length_toList] using hNe
      symm
      rw [beq_eq_false_iff_ne]
      intro hEq
      exact hNeLen (congrArg List.length hEq)
  unfold Internal.classifyPathBytesBa Internal.classifyPathBytes
  rw [hExact]
  by_cases hCol : (bs.data.toList == Internal.colonMemoryColonBytes) = true
  · simp [hCol]
  · have hColF : (bs.data.toList == Internal.colonMemoryColonBytes) = false := Bool.eq_false_iff.mpr hCol
    simp only [hColF, Bool.false_eq_true, ↓reduceIte]
    have hScheme :
        Internal.hasFileSchemeBa bs = (Internal.stripFileScheme bs.data.toList).isSome := by
      unfold Internal.hasFileSchemeBa
      split
      · next h4 =>
        have hLenGt4 : 4 < bs.data.toList.length := bs.data.length_toList ▸ h4
        match hL : bs.data.toList with
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp [hL] at hLenGt4
        | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
          have hg0 : bs[0] = b0 := by simp [hGet, hL]
          have hg1 : bs[1] = b1 := by simp [hGet, hL]
          have hg2 : bs[2] = b2 := by simp [hGet, hL]
          have hg3 : bs[3] = b3 := by simp [hGet, hL]
          have hg4 : bs[4] = b4 := by simp [hGet, hL]
          simp only [hg0, hg1, hg2, hg3, hg4]
          by_cases c0 : b0 = 0x66 <;> by_cases c1 : b1 = 0x69 <;> by_cases c2 : b2 = 0x6C <;>
            by_cases c3 : b3 = 0x65 <;> by_cases c4 : b4 = 0x3A
          · subst c0 c1 c2 c3 c4; simp [Internal.stripFileScheme]
          all_goals simp [Internal.stripFileScheme, c0, c1, c2, c3, c4]
      · next hNot4 =>
        have hLenLe : bs.data.toList.length ≤ 4 := by
          have : bs.size ≤ 4 := Nat.le_of_not_lt hNot4
          exact bs.data.length_toList ▸ this
        match hL : bs.data.toList with
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp [Internal.stripFileScheme]
        | _ :: _ :: _ :: _ :: _ :: _ => simp [hL] at hLenLe
    by_cases hFs : Internal.hasFileSchemeBa bs = true
    · simp only [hFs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hGe5 : 5 ≤ bs.size := by
        unfold Internal.hasFileSchemeBa at hFs
        split at hFs
        · omega
        · cases hFs
      have hStrip : Internal.stripFileScheme bs.data.toList = some (sliceBytes bs 5 bs.size) := by
        have hLenGe5 : 5 ≤ bs.data.toList.length := bs.data.length_toList ▸ hGe5
        match hL : bs.data.toList with
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp [hL] at hLenGe5
        | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
          have hIsSome : (Internal.stripFileScheme (b0 :: b1 :: b2 :: b3 :: b4 :: rest)).isSome = true := by
            simpa [hL, hFs] using hScheme.symm
          have hSl : sliceBytes bs 5 bs.size = rest := by
            simp only [sliceBytes, hL, List.drop_succ_cons, List.drop_zero]
            have hEqSz : bs.size = (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length := by
              rw [← hL]
              exact bs.data.length_toList.symm
            have hSub : bs.size - 5 = rest.length := by
              simp only [List.length_cons] at hEqSz
              omega
            rw [hSub, List.take_length]
          rw [hSl]
          by_cases c0 : b0 = 0x66 <;> by_cases c1 : b1 = 0x69 <;> by_cases c2 : b2 = 0x6C <;>
            by_cases c3 : b3 = 0x65 <;> by_cases c4 : b4 = 0x3A
          · subst c0 c1 c2 c3 c4; rfl
          all_goals simp [Internal.stripFileScheme, c0, c1, c2, c3, c4] at hIsSome
      rw [hStrip]
      dsimp only
      have hFragB := findByteBefore_bounds bs 0x23 5 bs.size hGe5
      have hBeforeFrag :
          Internal.takeBeforeByte 0x23 (sliceBytes bs 5 bs.size) =
            sliceBytes bs 5 (Internal.findByteBefore bs 0x23 5 bs.size) :=
        findByteBefore_takeBefore bs 0x23 5 bs.size hGe5 (Nat.le_refl _)
      rw [hBeforeFrag]
      have hAfterAuth :
          Internal.stripAuthority (sliceBytes bs 5 (Internal.findByteBefore bs 0x23 5 bs.size)) =
            sliceBytes bs (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
              (Internal.findByteBefore bs 0x23 5 bs.size) :=
        stripAuthorityIdx_eq bs 5 (Internal.findByteBefore bs 0x23 5 bs.size) hFragB.1 hFragB.2
      rw [hAfterAuth]
      have hPathGe :
          5 ≤ Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size) ∧
            Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size) ≤
              Internal.findByteBefore bs 0x23 5 bs.size := by
        unfold Internal.stripAuthorityIdx
        split
        · split
          · exact ⟨by have := (findByteBefore_bounds bs 0x2F (5 + 2) (Internal.findByteBefore bs 0x23 5 bs.size) (by omega)).1; omega,
              (findByteBefore_bounds bs 0x2F (5 + 2) (Internal.findByteBefore bs 0x23 5 bs.size) (by omega)).2⟩
          · exact ⟨Nat.le_refl _, hFragB.1⟩
        · exact ⟨Nat.le_refl _, hFragB.1⟩
      have hSplitQ := findByteBefore_splitFirst bs 0x3F
        (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
        (Internal.findByteBefore bs 0x23 5 bs.size) hPathGe.2 hFragB.2
      rw [hSplitQ]
      dsimp only
      rw [decodeUriMatchBa_eq bs
        (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
        (Internal.findByteBefore bs 0x3F
          (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
          (Internal.findByteBefore bs 0x23 5 bs.size))
        Internal.colonMemoryColonBytes]
      by_cases hQLt :
          Internal.findByteBefore bs 0x3F
              (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
              (Internal.findByteBefore bs 0x23 5 bs.size) <
            Internal.findByteBefore bs 0x23 5 bs.size
      · simp only [hQLt, ↓reduceIte]
        have hModeEq := extractLastUriModeFlagsBaAux_eq bs (Internal.findByteBefore bs 0x23 5 bs.size) hFragB.2
          (Internal.findByteBefore bs 0x23 5 bs.size -
            (Internal.findByteBefore bs 0x3F
              (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
              (Internal.findByteBefore bs 0x23 5 bs.size) + 1) + 1)
          none
          (Internal.findByteBefore bs 0x3F
            (Internal.stripAuthorityIdx bs 5 (Internal.findByteBefore bs 0x23 5 bs.size))
            (Internal.findByteBefore bs 0x23 5 bs.size) + 1)
          hQLt (by omega)
        simp only [Internal.extractLastUriMode]
        have hFalse : (none == some Internal.memoryModeBytes, none == some Internal.roModeBytes) = (false, false) := rfl
        rw [hFalse] at hModeEq
        dsimp only at hModeEq
        rw [hModeEq]
      · simp only [hQLt, ↓reduceIte]
        rfl
    · have hFsF : Internal.hasFileSchemeBa bs = false := Bool.eq_false_iff.mpr hFs
      have hStripNone : Internal.stripFileScheme bs.data.toList = none := by
        rw [hFsF] at hScheme
        cases hOpt : Internal.stripFileScheme bs.data.toList <;> simp [hOpt] at hScheme ⊢
      simp [hFsF, hStripNone]

end LeanSwe.Sqlite.Proofs
