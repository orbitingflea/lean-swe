import Core.Refines
import LeanSwe.Time.Model
import LeanSwe.Time.Interface

/-!
# Pure Refinement Proofs for `LeanSwe.Time`

Proves `Core.RefinesPureEq*` equivalences for all 10 pure operations in
`LeanSwe.Time.Interface` against `LeanSwe.Time.Model`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.Time

private theorem splitLeadingDigits_eq : ∀ cs : List Char,
    Internal.splitLeadingDigits cs = Model.splitLeadingDigits cs
  | [] => rfl
  | c :: rest => by
    change (if Internal.isAsciiDigit c then
        let p := Internal.splitLeadingDigits rest
        (c :: p.1, p.2)
      else ([], c :: rest)) =
      (if Model.isAsciiDigit c then
        let p := Model.splitLeadingDigits rest
        (c :: p.1, p.2)
      else ([], c :: rest))
    have hdig : Internal.isAsciiDigit c = Model.isAsciiDigit c := rfl
    rw [hdig, splitLeadingDigits_eq rest]

private theorem fracDigitsToNanos9_eq : ∀ (k acc : Nat) (cs : List Char),
    Internal.fracDigitsToNanos9 k acc cs = Model.fracDigitsToNanos9 k acc cs
  | 0, _, _ => rfl
  | k + 1, acc, c :: rest => by
    change Internal.fracDigitsToNanos9 k (acc * 10 + Internal.digitVal c) rest =
      Model.fracDigitsToNanos9 k (acc * 10 + Model.digitVal c) rest
    exact fracDigitsToNanos9_eq k (acc * 10 + Model.digitVal c) rest
  | k + 1, acc, [] => by
    change Internal.fracDigitsToNanos9 k (acc * 10) [] =
      Model.fracDigitsToNanos9 k (acc * 10) []
    exact fracDigitsToNanos9_eq k (acc * 10) []

private theorem parseOffsetSeconds_eq :
    Internal.parseOffsetSeconds = Model.parseOffsetSeconds :=
  funext fun _ => rfl

/-- Pure refinement of `LeanSwe.Time.elapsedDuration` to `Model.elapsedDuration`. -/
theorem refines_elapsedDuration :
    Core.RefinesPureEq2 LeanSwe.Time.elapsedDuration Model.elapsedDuration := by
  intro a b; rfl

/-- Pure refinement of `LeanSwe.Time.deadlineNanos` to `Model.deadlineNanos`. -/
theorem refines_deadlineNanos :
    Core.RefinesPureEq2 LeanSwe.Time.deadlineNanos Model.deadlineNanos := by
  intro a b; rfl

/-- Pure refinement of `LeanSwe.Time.isMonoExpired` to `Model.isMonoExpired`. -/
theorem refines_isMonoExpired :
    Core.RefinesPureEq2 LeanSwe.Time.isMonoExpired Model.isMonoExpired := by
  intro a b; rfl

/-- Pure refinement of `LeanSwe.Time.formatUtcIso8601` to `Model.formatUtcIso8601`. -/
theorem refines_formatUtcIso8601 :
    Core.RefinesPureEq LeanSwe.Time.formatUtcIso8601 Model.formatUtcIso8601 := by
  intro ts; rfl

private def mkInvalidFormat (message : String) : TimeError :=
  { kind := .invalidFormat, message := message }

private theorem parseIsoTimeAndRest_eq (date : Std.Time.PlainDate) (afterDate : List Char) :
    (match Internal.pop1? afterDate with
      | none => (Except.error (mkInvalidFormat "expected THH:MM:SS time and timezone in ISO 8601 timestamp") :
          Except TimeError Std.Time.Timestamp)
      | some (sep, r0) =>
        if sep != 'T' && sep != 't' then
          Except.error (mkInvalidFormat "expected 'T' separator in ISO 8601 timestamp")
        else
          match Internal.popTwoDigitsNat? r0 with
          | none => Except.error (mkInvalidFormat "invalid hour digits in ISO 8601 timestamp")
          | some (hh, r1) =>
            match Internal.pop1? r1 with
            | some (c1, r2) =>
              if c1 != ':' then
                Except.error (mkInvalidFormat "expected ':' after hour in ISO 8601 timestamp")
              else
                match Internal.popTwoDigitsNat? r2 with
                | none => Except.error (mkInvalidFormat "invalid minute digits in ISO 8601 timestamp")
                | some (mm, r3) =>
                  match Internal.pop1? r3 with
                  | some (c2, r4) =>
                    if c2 != ':' then
                      Except.error (mkInvalidFormat "expected ':' after minute in ISO 8601 timestamp")
                    else
                      match Internal.popTwoDigitsNat? r4 with
                      | none => Except.error (mkInvalidFormat "invalid second digits in ISO 8601 timestamp")
                      | some (ss, afterSec) =>
                        if !(hh ≤ 23 && mm ≤ 59 && ss ≤ 59) then
                          Except.error (mkInvalidFormat "ISO 8601 time field out of range")
                        else do
                          let (nano, zoneCs) ←
                            match afterSec with
                            | dot :: fracStart =>
                              if dot == '.' then
                                let (ds, zc) := Internal.splitLeadingDigits fracStart
                                if ds.isEmpty || ds.length > 9 then
                                  Except.error (mkInvalidFormat "ISO 8601 fractional seconds must have 1..9 digits")
                                else
                                  Except.ok (Internal.fracDigitsToNanos9 9 0 ds, zc)
                              else
                                Except.ok (0, dot :: fracStart)
                            | [] =>
                              Except.ok (0, [])
                          let offSec ← Internal.parseOffsetSeconds zoneCs
                          let wallSec : Int := date.toEpochDay.val * 86400 + Int.ofNat (hh * 3600 + mm * 60 + ss)
                          let utcSec : Int := wallSec - offSec
                          let totalNs : Int := utcSec * 1000000000 + Int.ofNat nano
                          Except.ok (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (Std.Time.Nanosecond.Offset.ofInt totalNs))
                  | none => Except.error (mkInvalidFormat "expected ':SS' in ISO 8601 timestamp")
            | none => Except.error (mkInvalidFormat "expected ':MM:SS' in ISO 8601 timestamp")) =
    (match Model.pop1? afterDate with
      | none => (Except.error (mkInvalidFormat "expected THH:MM:SS time and timezone in ISO 8601 timestamp") :
          Except TimeError Std.Time.Timestamp)
      | some (sep, r0) =>
        if sep != 'T' && sep != 't' then
          Except.error (mkInvalidFormat "expected 'T' separator in ISO 8601 timestamp")
        else
          match Model.popTwoDigitsNat? r0 with
          | none => Except.error (mkInvalidFormat "invalid hour digits in ISO 8601 timestamp")
          | some (hh, r1) =>
            match Model.pop1? r1 with
            | some (c1, r2) =>
              if c1 != ':' then
                Except.error (mkInvalidFormat "expected ':' after hour in ISO 8601 timestamp")
              else
                match Model.popTwoDigitsNat? r2 with
                | none => Except.error (mkInvalidFormat "invalid minute digits in ISO 8601 timestamp")
                | some (mm, r3) =>
                  match Model.pop1? r3 with
                  | some (c2, r4) =>
                    if c2 != ':' then
                      Except.error (mkInvalidFormat "expected ':' after minute in ISO 8601 timestamp")
                    else
                      match Model.popTwoDigitsNat? r4 with
                      | none => Except.error (mkInvalidFormat "invalid second digits in ISO 8601 timestamp")
                      | some (ss, afterSec) =>
                        if !(hh ≤ 23 && mm ≤ 59 && ss ≤ 59) then
                          Except.error (mkInvalidFormat "ISO 8601 time field out of range")
                        else do
                          let (nano, zoneCs) ←
                            match afterSec with
                            | dot :: fracStart =>
                              if dot == '.' then
                                let (ds, zc) := Model.splitLeadingDigits fracStart
                                if ds.isEmpty || ds.length > 9 then
                                  Except.error (mkInvalidFormat "ISO 8601 fractional seconds must have 1..9 digits")
                                else
                                  Except.ok (Model.fracDigitsToNanos9 9 0 ds, zc)
                              else
                                Except.ok (0, dot :: fracStart)
                            | [] =>
                              Except.ok (0, [])
                          let offSec ← Model.parseOffsetSeconds zoneCs
                          let wallSec : Int := date.toEpochDay.val * 86400 + Int.ofNat (hh * 3600 + mm * 60 + ss)
                          let utcSec : Int := wallSec - offSec
                          let totalNs : Int := utcSec * 1000000000 + Int.ofNat nano
                          Except.ok (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (Std.Time.Nanosecond.Offset.ofInt totalNs))
                  | none => Except.error (mkInvalidFormat "expected ':SS' in ISO 8601 timestamp")
            | none => Except.error (mkInvalidFormat "expected ':MM:SS' in ISO 8601 timestamp")) := by
  have hp1 : Internal.pop1? afterDate = Model.pop1? afterDate := rfl
  rw [hp1]
  cases Model.pop1? afterDate with
  | none => rfl
  | some p1 =>
    dsimp only
    by_cases hT : (p1.1 != 'T' && p1.1 != 't') = true
    · simp [hT]
    · simp only [hT, Bool.false_eq_true, ↓reduceIte]
      have hp2 : Internal.popTwoDigitsNat? p1.2 = Model.popTwoDigitsNat? p1.2 := rfl
      rw [hp2]
      cases Model.popTwoDigitsNat? p1.2 with
      | none => rfl
      | some p2 =>
        dsimp only
        have hp3 : Internal.pop1? p2.2 = Model.pop1? p2.2 := rfl
        rw [hp3]
        cases Model.pop1? p2.2 with
        | none => rfl
        | some p3 =>
          dsimp only
          by_cases hc1 : (p3.1 != ':') = true
          · simp [hc1]
          · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
            have hp4 : Internal.popTwoDigitsNat? p3.2 = Model.popTwoDigitsNat? p3.2 := rfl
            rw [hp4]
            cases Model.popTwoDigitsNat? p3.2 with
            | none => rfl
            | some p4 =>
              dsimp only
              have hp5 : Internal.pop1? p4.2 = Model.pop1? p4.2 := rfl
              rw [hp5]
              cases Model.pop1? p4.2 with
              | none => rfl
              | some p5 =>
                dsimp only
                by_cases hc2 : (p5.1 != ':') = true
                · simp [hc2]
                · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
                  have hp6 : Internal.popTwoDigitsNat? p5.2 = Model.popTwoDigitsNat? p5.2 := rfl
                  rw [hp6]
                  cases Model.popTwoDigitsNat? p5.2 with
                  | none => rfl
                  | some p6 =>
                    dsimp only
                    by_cases hrng : (!(p2.1 ≤ 23 && p4.1 ≤ 59 && p6.1 ≤ 59)) = true
                    · simp [hrng]
                    · simp only [hrng, Bool.false_eq_true, ↓reduceIte]
                      dsimp only [Bind.bind, Except.bind]
                      cases p6.2 with
                      | nil => rw [parseOffsetSeconds_eq]
                      | cons dot fracStart =>
                        by_cases hdot : (dot == '.') = true
                        · simp only [hdot, ↓reduceIte, splitLeadingDigits_eq,
                            fracDigitsToNanos9_eq, parseOffsetSeconds_eq]
                        · simp only [hdot, Bool.false_eq_true, ↓reduceIte, parseOffsetSeconds_eq]

/-- Pure refinement of `LeanSwe.Time.parseUtcIso8601` to `Model.parseUtcIso8601`. -/
theorem refines_parseUtcIso8601 :
    Core.RefinesPureEq LeanSwe.Time.parseUtcIso8601 Model.parseUtcIso8601 := by
  intro raw
  dsimp [LeanSwe.Time.parseUtcIso8601, defaultApi, Internal.mkApiM,
    Internal.parseUtcIso8601, Model.parseUtcIso8601, Bind.bind, Except.bind]
  have hhead : Internal.parseDateHead raw.toList = Model.parseDateHead raw.toList := rfl
  rw [hhead]
  cases Model.parseDateHead raw.toList with
  | error _ => rfl
  | ok p => exact parseIsoTimeAndRest_eq p.1 p.2

/-- Pure refinement of `LeanSwe.Time.formatUtcCompact` to `Model.formatUtcCompact`. -/
theorem refines_formatUtcCompact :
    Core.RefinesPureEq LeanSwe.Time.formatUtcCompact Model.formatUtcCompact := by
  intro ts; rfl

/-- Pure refinement of `LeanSwe.Time.formatUtcDate` to `Model.formatUtcDate`. -/
theorem refines_formatUtcDate :
    Core.RefinesPureEq LeanSwe.Time.formatUtcDate Model.formatUtcDate := by
  intro d; rfl

/-- Pure refinement of `LeanSwe.Time.parseUtcDate` to `Model.parseUtcDate`. -/
theorem refines_parseUtcDate :
    Core.RefinesPureEq LeanSwe.Time.parseUtcDate Model.parseUtcDate := by
  intro raw; rfl

/-- Pure refinement of `LeanSwe.Time.utcDateOfTimestamp` to `Model.utcDateOfTimestamp`. -/
theorem refines_utcDateOfTimestamp :
    Core.RefinesPureEq LeanSwe.Time.utcDateOfTimestamp Model.utcDateOfTimestamp := by
  intro ts; rfl

/-- Pure refinement of `LeanSwe.Time.timestampOfUtcDate` to `Model.timestampOfUtcDate`. -/
theorem refines_timestampOfUtcDate :
    Core.RefinesPureEq LeanSwe.Time.timestampOfUtcDate Model.timestampOfUtcDate := by
  intro d; rfl

end LeanSwe.Time.Proofs.RefinesModel
