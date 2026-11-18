import LeanSwe.Sqlite.Raw.Types
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Raw.Impl
import LeanSwe.Sqlite.Raw.SpecTests

namespace LeanSwe.Sqlite.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.Sqlite.Raw

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

/-- Helper showing `Internal.takeBeforeByte d a = a` when `d ∉ a`. -/
theorem takeBeforeByte_eq_self (d : UInt8) (a : List UInt8) (hd : d ∉ a) :
    Internal.takeBeforeByte d a = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    have hne : x ≠ d := fun heq => hd (by simp [heq])
    have hxs : d ∉ xs := fun hmem => hd (by simp [hmem])
    simp [Internal.takeBeforeByte, hne, ih hxs]

/-- Helper showing `Internal.splitFirstByte d (a ++ d :: b) = (a, some b)` when `d ∉ a`. -/
theorem splitFirstByte_append_left (d : UInt8) (a b : List UInt8) (hd : d ∉ a) :
    Internal.splitFirstByte d (a ++ d :: b) = (a, some b) := by
  induction a with
  | nil => simp [Internal.splitFirstByte]
  | cons x xs ih =>
    have hne : x ≠ d := fun heq => hd (by simp [heq])
    have hxs : d ∉ xs := fun hmem => hd (by simp [hmem])
    simp [Internal.splitFirstByte, hne, ih hxs]

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

/-- Helper resuming `.normal` after `'\n'` exits an `.inLineComment`. -/
theorem scanSqlTail_inLineComment_append_nl (bs suf : List UInt8)
    (h : (0x0A : UInt8) ∉ bs) :
    Internal.scanSqlTail .inLineComment (bs ++ 0x0A :: suf) = Internal.scanSqlTail .normal suf := by
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

end LeanSwe.Sqlite.Raw.Proofs
