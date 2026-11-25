import Lean.Data.Json.Basic
import LeanSwe.Json.Model

namespace LeanSwe.Json.Proofs

open LeanSwe.Json.Model

/-- Exported simp reduction for `parseDecDigitsLoop` on `[]`. -/
@[simp] theorem parseDecDigitsLoop_nil_simp (acc : Nat) : parseDecDigitsLoop acc [] = acc :=
  parseDecDigitsLoop_nil acc

/-- Exported simp reduction for `parseDecDigitsLoop` on `c :: cs`. -/
@[simp] theorem parseDecDigitsLoop_cons_simp (acc : Nat) (c : Char) (cs : List Char) :
    parseDecDigitsLoop acc (c :: cs) = parseDecDigitsLoop (acc * 10 + (c.toNat - 0x30)) cs :=
  parseDecDigitsLoop_cons acc c cs

/-- Drop leading RFC 8259 JSON whitespace characters from a character list. -/
def dropJsonWs : List Char → List Char
  | [] => []
  | c :: cs => if isJsonWsChar c then dropJsonWs cs else c :: cs

/-- Dropping whitespace past a pure-whitespace prefix reduces to dropping whitespace on the suffix. -/
theorem dropJsonWs_ws_append {ws : List Char} (hws : ws.all isJsonWsChar = true)
    (rest : List Char) : dropJsonWs (ws ++ rest) = dropJsonWs rest := by
  induction ws with
  | nil => rfl
  | cons c cs ih => simp only [List.all_cons, Bool.and_eq_true] at hws; simp [dropJsonWs, hws.1, ih hws.2]

/-- Check whether the remaining character stream starts with a structural delimiter (`','`, `']'`, `'}'`) or EOF. -/
def isDelimOrEof : List Char → Bool
  | [] => true
  | c :: _ => c == ',' || c == ']' || c == '}'

/-- `dropJsonWs` is the identity when the stream starts with a delimiter or EOF. -/
theorem dropJsonWs_of_delimOrEof {after : List Char} (h : isDelimOrEof after = true) :
    dropJsonWs after = after := by
  cases after with
  | nil => rfl
  | cons c cs => simp only [isDelimOrEof, Bool.or_eq_true, beq_iff_eq] at h; rcases h with (rfl | rfl) | rfl <;> rfl

/-- Decode a single hexadecimal ASCII character into `0..15`. -/
def hexCharVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 0x30)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 0x61 + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 0x41 + 10) else none

/-- `hexCharVal?` inverts `renderHexNibble` on every nibble `n < 16`. -/
theorem hexCharVal?_renderHexNibble (upper : Bool) {n : Nat} (hn : n < 16) :
    hexCharVal? (renderHexNibble upper n) = some n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => cases upper <;> decide
  | _ + 16 => omega

/-- Decode four hexadecimal characters into a 16-bit unsigned integer. -/
def decodeHex4? (d0 d1 d2 d3 : Char) : Option Nat := do
  let v0 ← hexCharVal? d0; let v1 ← hexCharVal? d1; let v2 ← hexCharVal? d2; let v3 ← hexCharVal? d3
  some (v0 * 4096 + v1 * 256 + v2 * 16 + v3)

/-- `decodeHex4?` inverts the four hex characters produced by `renderHex4` when `u16 < 0x10000`. -/
theorem decodeHex4?_renderHex4 (casing : HexCase4) {u16 : Nat} (hu : u16 < 0x10000) :
    decodeHex4?
      (renderHexNibble casing.u0 ((u16 / 4096) % 16))
      (renderHexNibble casing.u1 ((u16 / 256) % 16))
      (renderHexNibble casing.u2 ((u16 / 16) % 16))
      (renderHexNibble casing.u3 (u16 % 16)) = some u16 := by
  simp only [decodeHex4?, hexCharVal?_renderHexNibble casing.u0 (Nat.mod_lt _ (by decide)),
    hexCharVal?_renderHexNibble casing.u1 (Nat.mod_lt _ (by decide)),
    hexCharVal?_renderHexNibble casing.u2 (Nat.mod_lt _ (by decide)),
    hexCharVal?_renderHexNibble casing.u3 (Nat.mod_lt _ (by decide)), bind, Option.bind]
  congr 1; omega

/-- Fuel-bounded structural lexer for the interior of an RFC 8259 string literal up to `'"'`. -/
def lexStringBodyFuel : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, ch :: rest =>
    if ch == '"' then some ([], rest)
    else if ch == '\\' then
      match rest with
      | [] => none
      | esc :: rest' =>
        if esc == '"' then (lexStringBodyFuel fuel rest').map fun p => ('"' :: p.1, p.2)
        else if esc == '\\' then (lexStringBodyFuel fuel rest').map fun p => ('\\' :: p.1, p.2)
        else if esc == '/' then (lexStringBodyFuel fuel rest').map fun p => ('/' :: p.1, p.2)
        else if esc == 'b' then (lexStringBodyFuel fuel rest').map fun p => ('\x08' :: p.1, p.2)
        else if esc == 'f' then (lexStringBodyFuel fuel rest').map fun p => ('\x0c' :: p.1, p.2)
        else if esc == 'n' then (lexStringBodyFuel fuel rest').map fun p => ('\n' :: p.1, p.2)
        else if esc == 'r' then (lexStringBodyFuel fuel rest').map fun p => ('\r' :: p.1, p.2)
        else if esc == 't' then (lexStringBodyFuel fuel rest').map fun p => ('\t' :: p.1, p.2)
        else if esc == 'u' then
          match rest' with
          | d0 :: d1 :: d2 :: d3 :: tail =>
            match decodeHex4? d0 d1 d2 d3 with
            | none => none
            | some u1 =>
              if 0xD800 ≤ u1 && u1 < 0xDC00 then
                match tail with
                | '\\' :: 'u' :: e0 :: e1 :: e2 :: e3 :: tail2 =>
                  match decodeHex4? e0 e1 e2 e3 with
                  | some u2 =>
                    if 0xDC00 ≤ u2 && u2 < 0xE000 then
                      let cp := 0x10000 + (u1 - 0xD800) * 1024 + (u2 - 0xDC00)
                      (lexStringBodyFuel fuel tail2).map fun p => (Char.ofNat cp :: p.1, p.2)
                    else none
                  | none => none
                | _ => none
              else if 0xDC00 ≤ u1 && u1 < 0xE000 then none
              else (lexStringBodyFuel fuel tail).map fun p => (Char.ofNat u1 :: p.1, p.2)
          | _ => none
        else none
    else if ch.toNat < 0x20 then none
    else (lexStringBodyFuel fuel rest).map fun p => (ch :: p.1, p.2)

/-- Pure character-level lexer for the interior of an RFC 8259 string literal up to `'"'`. -/
def lexStringBody (cs : List Char) : Option (List Char × List Char) :=
  lexStringBodyFuel (cs.length + 1) cs

/-- Every Lean `Char` has scalar value strictly below `0xD800` or in `[0xE000, 0x110000)`. -/
theorem char_toNat_valid_bounds (c : Char) :
    c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat < 0x110000) := by
  have hv := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at hv
  change c.val.toNat < 0xD800 ∨ (0xE000 ≤ c.val.toNat ∧ c.val.toNat < 0x110000)
  rcases hv with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨Nat.succ_le_of_lt h2, h3⟩

/-- Every valid character escape fragment has length at least `1` and decodes in `1` fuel step. -/
theorem lexStringBodyFuel_renderCharWithStyle (fuel : Nat) (c : Char) (st : CharEscapeStyle)
    {frag : List Char} (h : renderCharWithStyle c st = some frag) (tail : List Char) :
    1 ≤ frag.length ∧
      lexStringBodyFuel (fuel + 1) (frag ++ tail) =
        (lexStringBodyFuel fuel tail).map (fun p => (c :: p.1, p.2)) := by
  have hbQ : ('\\' == '"') = false := by decide
  have hbB : ('\\' == '\\') = true := by decide
  cases st with
  | raw =>
    simp only [renderCharWithStyle, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
    split at h <;> cases h
    rename_i hcond
    rcases hcond with ⟨⟨hge, hneQ⟩, hneB⟩
    have hnotLt : ¬(c.toNat < 0x20) := by omega
    have hc1 : (c == '"') = false := Bool.eq_false_iff.mpr fun h => hneQ (beq_iff_eq.mp h)
    have hc2 : (c == '\\') = false := Bool.eq_false_iff.mpr fun h => hneB (beq_iff_eq.mp h)
    refine ⟨by simp, ?_⟩
    simp only [List.singleton_append, lexStringBodyFuel, hc1, hc2, Bool.false_eq_true, ↓reduceIte, ite_eq_right hnotLt]
  | shortEscape =>
    unfold renderCharWithStyle at h
    by_cases h1 : c == '"'
    · rw [ite_eq_left h1] at h; cases h; rw [beq_iff_eq.mp h1]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
    · rw [ite_eq_right h1] at h; by_cases h2 : c == '\\'
      · rw [ite_eq_left h2] at h; cases h; rw [beq_iff_eq.mp h2]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
      · rw [ite_eq_right h2] at h; by_cases h3 : c == '/'
        · rw [ite_eq_left h3] at h; cases h; rw [beq_iff_eq.mp h3]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
        · rw [ite_eq_right h3] at h; by_cases h4 : c == '\x08'
          · rw [ite_eq_left h4] at h; cases h; rw [beq_iff_eq.mp h4]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
          · rw [ite_eq_right h4] at h; by_cases h5 : c == '\x0c'
            · rw [ite_eq_left h5] at h; cases h; rw [beq_iff_eq.mp h5]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
            · rw [ite_eq_right h5] at h; by_cases h6 : c == '\n'
              · rw [ite_eq_left h6] at h; cases h; rw [beq_iff_eq.mp h6]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
              · rw [ite_eq_right h6] at h; by_cases h7 : c == '\r'
                · rw [ite_eq_left h7] at h; cases h; rw [beq_iff_eq.mp h7]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
                · rw [ite_eq_right h7] at h; by_cases h8 : c == '\t'
                  · rw [ite_eq_left h8] at h; cases h; rw [beq_iff_eq.mp h8]; exact ⟨by decide, by simp [lexStringBodyFuel, hbQ]⟩
                  · rw [ite_eq_right h8] at h; cases h
  | unicodeHex casing =>
    simp only [renderCharWithStyle] at h
    split at h <;> cases h
    rename_i hlt
    have hv1 : ((decide (0xD800 ≤ c.toNat) && decide (c.toNat < 0xDC00)) = false) := by
      apply Bool.eq_false_iff.mpr; intro htrue
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at htrue
      rcases char_toNat_valid_bounds c with h1 | ⟨h2, _⟩
      · exact Nat.not_le.mpr h1 htrue.1
      · exact Nat.not_lt.mpr (Nat.le_trans (by decide : 0xDC00 ≤ 0xE000) h2) htrue.2
    have hv2 : ((decide (0xDC00 ≤ c.toNat) && decide (c.toNat < 0xE000)) = false) := by
      apply Bool.eq_false_iff.mpr; intro htrue
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at htrue
      rcases char_toNat_valid_bounds c with h1 | ⟨h2, _⟩
      · exact Nat.not_le.mpr (Nat.lt_trans h1 (by decide : 0xD800 < 0xDC00)) htrue.1
      · exact Nat.not_lt.mpr h2 htrue.2
    refine ⟨by simp [renderHex4], ?_⟩
    simp only [renderHex4, List.cons_append, List.nil_append, lexStringBodyFuel,
      hbQ, hbB, Bool.false_eq_true, ↓reduceIte,
      (by decide : ('u' == '"') = false), (by decide : ('u' == '\\') = false),
      (by decide : ('u' == '/') = false), (by decide : ('u' == 'b') = false),
      (by decide : ('u' == 'f') = false), (by decide : ('u' == 'n') = false),
      (by decide : ('u' == 'r') = false), (by decide : ('u' == 't') = false),
      (by decide : ('u' == 'u') = true),
      decodeHex4?_renderHex4 casing hlt, hv1, hv2, Char.ofNat_toNat]
  | surrogatePair hiCase loCase =>
    simp only [renderCharWithStyle] at h
    split at h <;> cases h
    rename_i hge
    have hltMax : c.toNat < 0x110000 := by
      rcases char_toNat_valid_bounds c with h1 | ⟨_, h2⟩
      · exact Nat.lt_trans h1 (by decide : 0xD800 < 0x110000)
      · exact h2
    have hvLt : c.toNat - 0x10000 < 1024 * 1024 := Nat.sub_lt_left_of_lt_add hge hltMax
    have hqLt : (c.toNat - 0x10000) / 1024 < 1024 := Nat.div_lt_of_lt_mul hvLt
    have hrLt : (c.toNat - 0x10000) % 1024 < 1024 := Nat.mod_lt _ (by decide)
    have hhiRange2 : 0xD800 + (c.toNat - 0x10000) / 1024 < 0xDC00 :=
      Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hqLt 0xD800) (by decide)
    have hloRange2 : 0xDC00 + (c.toNat - 0x10000) % 1024 < 0xE000 :=
      Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hrLt 0xDC00) (by decide)
    have hhiLt : 0xD800 + (c.toNat - 0x10000) / 1024 < 0x10000 := Nat.lt_trans hhiRange2 (by decide)
    have hloLt : 0xDC00 + (c.toNat - 0x10000) % 1024 < 0x10000 := Nat.lt_trans hloRange2 (by decide)
    have hhiRange : (decide (0xD800 ≤ 0xD800 + (c.toNat - 0x10000) / 1024) &&
        decide (0xD800 + (c.toNat - 0x10000) / 1024 < 0xDC00)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨Nat.le_add_right _ _, hhiRange2⟩
    have hloRange : (decide (0xDC00 ≤ 0xDC00 + (c.toNat - 0x10000) % 1024) &&
        decide (0xDC00 + (c.toNat - 0x10000) % 1024 < 0xE000)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨Nat.le_add_right _ _, hloRange2⟩
    have hcp : 0x10000 + ((0xD800 + (c.toNat - 0x10000) / 1024) - 0xD800) * 1024 +
        ((0xDC00 + (c.toNat - 0x10000) % 1024) - 0xDC00) = c.toNat := by
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.add_assoc,
        Nat.mul_comm _ 1024, Nat.div_add_mod, Nat.add_sub_of_le hge]
    refine ⟨by simp [renderHex4], ?_⟩
    simp only [renderHex4, List.cons_append, List.nil_append, lexStringBodyFuel,
      hbQ, hbB, Bool.false_eq_true, ↓reduceIte,
      (by decide : ('u' == '"') = false), (by decide : ('u' == '\\') = false),
      (by decide : ('u' == '/') = false), (by decide : ('u' == 'b') = false),
      (by decide : ('u' == 'f') = false), (by decide : ('u' == 'n') = false),
      (by decide : ('u' == 'r') = false), (by decide : ('u' == 't') = false),
      (by decide : ('u' == 'u') = true),
      decodeHex4?_renderHex4 hiCase hhiLt, decodeHex4?_renderHex4 loCase hloLt,
      hhiRange, hloRange, hcp, Char.ofNat_toNat]

private theorem lexStringBodyFuel_renderStringChars :
    ∀ (cs : List Char) (styles : List CharEscapeStyle) {body : List Char},
      renderStringChars cs styles = some body →
      cs.length ≤ body.length ∧
      ∀ (after : List Char) (fuel : Nat),
        cs.length + 1 ≤ fuel → lexStringBodyFuel fuel (body ++ '"' :: after) = some (cs, after)
  | [], [], _, h => by
    simp only [renderStringChars, Option.some.injEq] at h; subst h
    refine ⟨Nat.le_refl _, fun after fuel hf => ?_⟩
    cases fuel with
    | zero => omega
    | succ f => simp [lexStringBodyFuel]
  | c :: cs, st :: sts, _, h => by
    simp only [renderStringChars, bind, Option.bind] at h
    cases hc : renderCharWithStyle c st with
    | none => simp [hc] at h
    | some hd =>
      simp only [hc] at h
      cases htl : renderStringChars cs sts with
      | none => simp [htl] at h
      | some tl =>
        simp only [htl, Option.some.injEq] at h; subst h
        obtain ⟨hlenHd, _⟩ := lexStringBodyFuel_renderCharWithStyle 0 c st hc []
        obtain ⟨hlenTl, ihFuel⟩ := lexStringBodyFuel_renderStringChars cs sts htl
        refine ⟨by simp; omega, fun after fuel hf => ?_⟩
        cases fuel with
        | zero => simp at hf
        | succ f =>
          have hstep := (lexStringBodyFuel_renderCharWithStyle f c st hc (tl ++ '"' :: after)).2
          rw [List.append_assoc, hstep, ihFuel after f (by simp at hf; omega)]
          rfl
  | [], _ :: _, _, h => by simp [renderStringChars] at h
  | _ :: _, [], _, h => by simp [renderStringChars] at h

/-- `lexStringBody` inverts `renderStringChars` followed by `'"'`. -/
theorem lexStringBody_renderStringChars (cs : List Char) (styles : List CharEscapeStyle)
    {body : List Char} (h : renderStringChars cs styles = some body) (after : List Char) :
    lexStringBody (body ++ '"' :: after) = some (cs, after) := by
  obtain ⟨hlen, hfuel⟩ := lexStringBodyFuel_renderStringChars cs styles h
  exact hfuel after ((body ++ '"' :: after).length + 1) (by simp; omega)

/-- Pure character-level lexer for a quoted RFC 8259 JSON string literal. -/
def lexStringLit : List Char → Option (String × List Char)
  | '"' :: rest => (lexStringBody rest).map fun p => (String.ofList p.1, p.2)
  | _ => none

/-- `lexStringLit` inverts `renderStringLiteral` on any suffix stream `after`. -/
theorem lexStringLit_renderStringLiteral {s : String} {styles : List CharEscapeStyle}
    {lit : String} (h : renderStringLiteral s styles = some lit) (after : List Char) :
    lexStringLit (lit.toList ++ after) = some (s, after) ∧ 2 ≤ lit.toList.length := by
  simp only [renderStringLiteral, bind, Option.bind] at h
  cases hb : renderStringChars s.toList styles with
  | none => simp [hb] at h
  | some body =>
    simp only [hb, Option.some.injEq] at h
    subst h
    have hlist : ("\"" ++ String.ofList body ++ "\"").toList = '"' :: (body ++ ['"']) := by
      simp [String.toList_append, String.toList_ofList]
    rw [hlist]
    refine ⟨?_, by simp⟩
    simp only [List.cons_append, List.append_assoc, List.nil_append, lexStringLit]
    rw [lexStringBody_renderStringChars s.toList styles hb after]
    simp [String.ofList_toList]

/-- Split maximal leading ASCII decimal digits from a character list. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isAsciiDigit c then
      let p := spanDigits cs
      (c :: p.1, p.2)
    else ([], c :: cs)

/-- Check that a character list does not begin with an ASCII decimal digit. -/
def notDigitHead : List Char → Bool
  | [] => true
  | c :: _ => !isAsciiDigit c

/-- `spanDigits` recovers `ds` and `rest` whenever `ds` is all digits and `rest` does not start with a digit. -/
theorem spanDigits_append {ds : List Char} (hds : ds.all isAsciiDigit = true)
    {rest : List Char} (hrest : notDigitHead rest = true) :
    spanDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c cs =>
      simp only [notDigitHead, Bool.not_eq_true'] at hrest
      simp [spanDigits, hrest]
  | cons d tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp [spanDigits, hds.1, ih hds.2]

/-- `Nat.digitChar d` for `d < 10` is an ASCII decimal digit with numeric value `d`. -/
theorem digitChar_lt10_props {d : Nat} (hd : d < 10) :
    isAsciiDigit (Nat.digitChar d) = true ∧ (Nat.digitChar d).toNat - 0x30 = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

private theorem toDigitsCore_step (f n : Nat) (ds : List Char) :
    Nat.toDigitsCore 10 (f + 1) n ds =
      if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
      else Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: ds) := rfl

/-- Base-10 `Nat.toDigitsCore` emits a non-empty all-digit list inverted by `parseDecDigitsLoop`. -/
theorem toDigitsCore_props (fuel n : Nat) (ds : List Char)
    (hfuel : n < fuel) (hds : ds.all isAsciiDigit = true) :
    (Nat.toDigitsCore 10 fuel n ds) ≠ [] ∧
      (Nat.toDigitsCore 10 fuel n ds).all isAsciiDigit = true ∧
      parseDecDigitsLoop 0 (Nat.toDigitsCore 10 fuel n ds) = parseDecDigitsLoop n ds := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ f ih =>
    rw [toDigitsCore_step]
    have hrem : n % 10 < 10 := Nat.mod_lt _ (by decide)
    obtain ⟨hdDig, hdVal⟩ := digitChar_lt10_props hrem
    generalize Nat.digitChar (n % 10) = dc at hdDig hdVal ⊢
    by_cases hq : n / 10 = 0
    · rw [ite_eq_left hq]
      have hn : n = n % 10 := by omega
      refine ⟨List.cons_ne_nil _ _, by rw [List.all_cons, hdDig, hds]; rfl, ?_⟩
      rw [parseDecDigitsLoop_cons, Nat.zero_mul, Nat.zero_add, hdVal, ← hn]
    · rw [ite_eq_right hq]
      have hlt : n / 10 < f := by omega
      obtain ⟨hne, hall, hval⟩ := ih (n / 10) (dc :: ds) hlt
        (by rw [List.all_cons, hdDig, hds]; rfl)
      refine ⟨hne, hall, ?_⟩
      rw [hval, parseDecDigitsLoop_cons, hdVal, show (n / 10) * 10 + n % 10 = n by omega]

/-- `w.repr` is a non-empty all-digit decimal string whose `parseDecDigitsLoop` value equals `w`. -/
theorem repr_nat_props (w : Nat) :
    w.repr.toList ≠ [] ∧ w.repr.toList.all isAsciiDigit = true ∧
      parseDecDigitsLoop 0 w.repr.toList = w := by
  have hrepr : w.repr.toList = Nat.toDigits 10 w := by
    change (String.ofList (Nat.toDigits 10 w)).toList = Nat.toDigits 10 w
    exact String.toList_ofList
  rw [hrepr]
  exact toDigitsCore_props (w + 1) w [] (by omega) rfl

/-- Check whether a character list starts with a character that terminates a JSON numeric token. -/
def isNumStop : List Char → Bool
  | [] => true
  | c :: _ => !isAsciiDigit c && c != '.' && c != 'e' && c != 'E'

/-- Split optional leading `'-'` sign from a character list. -/
def lexNumSign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | r => (false, r)

/-- Split optional `'.'` fraction part from a character list. -/
def lexFracPart : List Char → Option (Option String × List Char)
  | '.' :: cs2' =>
    let p := spanDigits cs2'
    if p.1.isEmpty then none else some (some (String.ofList p.1), p.2)
  | cs2 => some (none, cs2)

/-- Split optional `'+'` or `'-'` exponent sign from a character list. -/
def lexExpSign : List Char → ExpSign × List Char
  | '+' :: r => (ExpSign.plus, r)
  | '-' :: r => (ExpSign.minus, r)
  | r => (ExpSign.none, r)

/-- Split optional `'e'` or `'E'` exponent part from a character list. -/
def lexExpPart : List Char → Option (Option ExpTape × List Char)
  | 'e' :: cs3' =>
    let ps := lexExpSign cs3'
    let pd := spanDigits ps.2
    if pd.1.isEmpty then none else some (some ⟨false, ps.1, String.ofList pd.1⟩, pd.2)
  | 'E' :: cs3' =>
    let ps := lexExpSign cs3'
    let pd := spanDigits ps.2
    if pd.1.isEmpty then none else some (some ⟨true, ps.1, String.ofList pd.1⟩, pd.2)
  | cs3 => some (none, cs3)

/-- Finish lexing a number after extracting its sign and `spanDigits` split. -/
def lexNumberAfterInt (minus : Bool) (pi : List Char × List Char) : Option (NumTape × List Char) :=
  if pi.1.isEmpty then none
  else
    match lexFracPart pi.2 with
    | none => none
    | some (frac?, cs3) =>
      match lexExpPart cs3 with
      | none => none
      | some (exp?, csOut) => some (⟨minus, parseDecDigitsLoop 0 pi.1, frac?, exp?⟩, csOut)

/-- Pure character-level lexer for an RFC 8259 numeric literal into its `NumTape`. -/
def lexNumberChars (cs : List Char) : Option (NumTape × List Char) :=
  lexNumberAfterInt (lexNumSign cs).1 (spanDigits (lexNumSign cs).2)

private theorem lexNumSign_repr_append (minus : Bool) (w : Nat) (tail : List Char) :
    lexNumSign ((if minus then "-" else "").toList ++ (w.repr.toList ++ tail)) =
      (minus, w.repr.toList ++ tail) := by
  cases minus with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, String.toList_empty, List.nil_append]
    obtain ⟨hne, hall, _⟩ := repr_nat_props w
    cases hw : w.repr.toList with
    | nil => exact absurd hw hne
    | cons c cs =>
      rw [hw] at hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hneMinus : c ≠ '-' := by rintro rfl; have h1 := hall.1; revert h1; decide
      cases c with
      | mk val valid =>
        unfold lexNumSign
        split
        · rename_i r heq; injection heq with hc _; exact absurd hc hneMinus
        · rfl

private theorem lexExpPart_render (exp? : Option ExpTape)
    (hexp : (match exp? with | none => true | some e => isNonEmptyDigits e.digits) = true)
    {rest : List Char} (hstop : isNumStop rest = true) :
    lexExpPart ((match exp? with
      | none => ""
      | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest) =
      some (exp?, rest) := by
  have hStopNoDig : notDigitHead rest = true := by
    cases rest with
    | nil => rfl
    | cons c _ => simp only [isNumStop, Bool.and_eq_true] at hstop; exact hstop.1.1.1
  cases exp? with
  | none =>
    simp only [String.toList_empty, List.nil_append]
    cases rest with
    | nil => rfl
    | cons c tl =>
      simp only [isNumStop, Bool.and_eq_true, bne_iff_ne] at hstop
      unfold lexExpPart
      split
      · rename_i heq; injection heq with hc _; exact absurd hc hstop.1.2
      · rename_i heq; injection heq with hc _; exact absurd hc hstop.2
      · rfl
  | some e =>
    rcases e with ⟨uE, sgn, digs⟩
    simp only [isNonEmptyDigits, Bool.and_eq_true, Bool.not_eq_true'] at hexp
    rcases hexp with ⟨heNe, heAll⟩
    have hSignNone : lexExpSign (digs.toList ++ rest) = (ExpSign.none, digs.toList ++ rest) := by
      cases hd : digs.toList with
      | nil => simp [hd] at heNe
      | cons d dtl =>
        rw [hd] at heAll
        simp only [List.all_cons, Bool.and_eq_true] at heAll
        have hnp : d ≠ '+' := by rintro rfl; have h1 := heAll.1; revert h1; decide
        have hnm : d ≠ '-' := by rintro rfl; have h1 := heAll.1; revert h1; decide
        unfold lexExpSign
        split
        · rename_i heq; injection heq with hc _; exact absurd hc hnp
        · rename_i heq; injection heq with hc _; exact absurd hc hnm
        · rfl
    have heCh : "e".toList = ['e'] := rfl
    have hECh : "E".toList = ['E'] := rfl
    have hpCh : "+".toList = ['+'] := rfl
    have hmCh : "-".toList = ['-'] := rfl
    cases sgn
    · cases uE <;> simp only [Bool.false_eq_true, ↓reduceIte, renderExpSign, String.toList_append,
        String.toList_empty, heCh, hECh, List.cons_append, List.nil_append, lexExpPart] <;>
        rw [hSignNone, spanDigits_append heAll hStopNoDig] <;> simp [heNe, String.ofList_toList]
    · cases uE <;> simp only [Bool.false_eq_true, ↓reduceIte, renderExpSign, String.toList_append,
        heCh, hECh, hpCh, List.cons_append, List.nil_append, lexExpPart, lexExpSign] <;>
        rw [spanDigits_append heAll hStopNoDig] <;> simp [heNe, String.ofList_toList]
    · cases uE <;> simp only [Bool.false_eq_true, ↓reduceIte, renderExpSign, String.toList_append,
        heCh, hECh, hmCh, List.cons_append, List.nil_append, lexExpPart, lexExpSign] <;>
        rw [spanDigits_append heAll hStopNoDig] <;> simp [heNe, String.ofList_toList]

private theorem notDigitHead_expTail (exp? : Option ExpTape) {rest : List Char}
    (hstop : isNumStop rest = true) :
    notDigitHead ((match exp? with
      | none => ""
      | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest) = true := by
  cases exp? with
  | none =>
    cases rest with
    | nil => rfl
    | cons c _ => simp only [String.toList_empty, List.nil_append, isNumStop, Bool.and_eq_true] at hstop ⊢; exact hstop.1.1.1
  | some e =>
    rcases e with ⟨uE, _, _⟩
    cases uE <;> simp [String.toList_append, notDigitHead, isAsciiDigit]

private theorem lexFracPart_render (frac? : Option String) (exp? : Option ExpTape)
    (hfrac : (match frac? with | none => true | some f => isNonEmptyDigits f) = true)
    {rest : List Char} (hstop : isNumStop rest = true) :
    lexFracPart ((match frac? with | none => "" | some f => "." ++ f).toList ++
      ((match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest)) =
      some (frac?, (match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest) := by
  cases frac? with
  | none =>
    simp only [String.toList_empty, List.nil_append]
    have hNoDot : match (match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest with
        | '.' :: _ => False | _ => True := by
      cases exp? with
      | none =>
        cases rest with
        | nil => trivial
        | cons c _ =>
          simp only [String.toList_empty, List.nil_append, isNumStop, Bool.and_eq_true, bne_iff_ne] at hstop ⊢
          split
          · rename_i heq; injection heq with hc _; exact hstop.1.1.2 hc
          · trivial
      | some e =>
        rcases e with ⟨uE, _, _⟩
        cases uE <;> simp [String.toList_append]
    cases ha : (match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest with
    | nil => rfl
    | cons ch tl =>
      rw [ha] at hNoDot; unfold lexFracPart; split
      · rename_i cs2' heq; injection heq with hc _; subst hc; exact False.elim hNoDot
      · rfl
  | some f =>
    simp only [isNonEmptyDigits, Bool.and_eq_true, Bool.not_eq_true'] at hfrac
    rcases hfrac with ⟨hfNe, hfAll⟩
    have hdotCh : ".".toList = ['.'] := rfl
    simp only [String.toList_append, hdotCh, List.cons_append, List.nil_append, lexFracPart]
    rw [spanDigits_append hfAll (notDigitHead_expTail exp? hstop)]
    simp [hfNe, String.ofList_toList]

/-- `lexNumberChars` inverts `renderNumTape` on any valid `NumTape` followed by a numeric stop character. -/
theorem lexNumberChars_renderNumTape {nt : NumTape} (hval : validNumTape nt = true)
    {rest : List Char} (hstop : isNumStop rest = true) :
    lexNumberChars ((renderNumTape nt).toList ++ rest) = some (nt, rest) ∧
      1 ≤ (renderNumTape nt).toList.length := by
  rcases nt with ⟨minus, whole, frac?, exp?⟩
  obtain ⟨hwNe, hwAll, hwVal⟩ := repr_nat_props whole
  have hwNotEmpty : whole.repr.toList.isEmpty = false := by
    cases h : whole.repr.toList with | nil => exact absurd h hwNe | cons _ _ => rfl
  simp only [validNumTape, Bool.and_eq_true] at hval
  rcases hval with ⟨hfrac, hexp⟩
  have hlen : 1 ≤ (renderNumTape ⟨minus, whole, frac?, exp?⟩).toList.length := by
    simp only [renderNumTape, String.toList_append, List.length_append]
    cases hw : whole.repr.toList with
    | nil => exact absurd hw hwNe
    | cons _ _ => simp; omega
  refine ⟨?_, hlen⟩
  unfold renderNumTape lexNumberChars
  simp only [String.toList_append, List.append_assoc]
  rw [lexNumSign_repr_append minus whole _]
  rw [show ∀ (a : Bool) (b : List Char), (a, b).1 = a from fun _ _ => rfl]
  rw [show ∀ (a : Bool) (b : List Char), (a, b).2 = b from fun _ _ => rfl]
  have hFinish : ∀ (tail : List Char),
      notDigitHead tail = true →
      lexFracPart tail = some (frac?, (match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest) →
      lexNumberAfterInt minus (spanDigits (whole.repr.toList ++ tail)) =
        some (⟨minus, whole, frac?, exp?⟩, rest) := by
    intro tail hnd hfp
    rw [spanDigits_append hwAll hnd]
    unfold lexNumberAfterInt
    rw [show ∀ (a b : List Char), (a, b).1 = a from fun _ _ => rfl]
    rw [show ∀ (a b : List Char), (a, b).2 = b from fun _ _ => rfl]
    rw [hwNotEmpty, ite_eq_right Bool.false_ne_true, hwVal, hfp]
    change (match lexExpPart ((match exp? with
        | none => ""
        | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits).toList ++ rest) with
      | none => none
      | some (e?, csOut) => some (NumTape.mk minus whole frac? e?, csOut)) = _
    rw [lexExpPart_render exp? hexp hstop]
  refine hFinish _ ?_ (lexFracPart_render frac? exp? hfrac hstop)
  cases frac? with
  | none => exact notDigitHead_expTail exp? hstop
  | some f => simp [String.toList_append, notDigitHead, isAsciiDigit]

end LeanSwe.Json.Proofs
