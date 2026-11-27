import Lean.Data.Json.Basic
import LeanSwe.Json.Impl.Format
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.FormatScalar
import LeanSweProofs.Json.Proofs.FormatNumber

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

private theorem one_le_sizeOf_jsonList (l : List Lean.Json) : 1 ≤ sizeOf l := by
  cases l <;> simp +arith

private theorem sizeOf_append_jsonList (u v : List Lean.Json) :
    sizeOf (u ++ v) = sizeOf u + sizeOf v - 1 := by
  induction u with
  | nil => simp +arith
  | cons _ tl ih =>
    have hv := one_le_sizeOf_jsonList v
    have htl := one_le_sizeOf_jsonList tl
    simp +arith [ih]
    omega

private theorem sizeOf_reverse_jsonList (l : List Lean.Json) :
    sizeOf l.reverse = sizeOf l := by
  induction l with
  | nil => rfl
  | cons _ tl ih =>
    have htl := one_le_sizeOf_jsonList tl
    rw [List.reverse_cons, sizeOf_append_jsonList, ih]
    simp +arith

mutual
  /-- Structural recursive `JsonDoc` specification equivalent to tail-recursive `renderFormat`. -/
  def treeDoc : Lean.Json → JsonDoc
    | .null => .text "null"
    | .bool true => .text "true"
    | .bool false => .text "false"
    | .num n => .text (jsonNumberToString n)
    | .str s => .text (renderString s)
    | .arr elems =>
      match elems.toList with
      | [] => .text "[]"
      | _ :: _ =>
        match _hrev : elems.toList.reverse with
        | [] => .text "[]"
        | last :: restRev =>
          docBracket "[" (joinCommaLineRev (treeDoc last) (treeDocList restRev)) "]"
    | .obj kvs =>
      match kvs.inner.inner with
      | .leaf => .text "{}"
      | _ =>
        match (treeEntriesDoc kvs.inner.inner).reverse with
        | [] => .text "{}"
        | last :: restRev => docBracket "{" (joinCommaLineRev last restRev) "}"
  termination_by j => sizeOf j
  decreasing_by
    · have hmem : last ∈ elems.toList :=
        List.mem_reverse.mp (by rw [_hrev]; exact List.mem_cons_self)
      have hlt := List.sizeOf_lt_of_mem hmem
      cases elems; simp +arith at hlt ⊢; omega
    · have hsz : sizeOf (last :: restRev) = sizeOf elems.toList := by
        rw [← _hrev, sizeOf_reverse_jsonList]
      cases elems; simp +arith at hsz ⊢; omega
    · cases kvs with | mk inner => cases inner; simp +arith

  /-- Map `treeDoc` across a list of `Lean.Json` values. -/
  def treeDocList : List Lean.Json → List JsonDoc
    | [] => []
    | x :: xs => treeDoc x :: treeDocList xs
  termination_by xs => sizeOf xs

  /-- In-order list of formatted key-value `JsonDoc`s for a `Std.DTreeMap` internal tree. -/
  def treeEntriesDoc : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → List JsonDoc
    | .leaf => []
    | .inner _ k v l r =>
      treeEntriesDoc l ++
        JsonDoc.group (.append (.text (renderString k ++ ":")) (.append .line (treeDoc v))) ::
        treeEntriesDoc r
  termination_by t => sizeOf t
end

/-- `treeDocList` distributes over list concatenation. -/
theorem treeDocList_append (a b : List Lean.Json) :
    treeDocList (a ++ b) = treeDocList a ++ treeDocList b := by
  induction a with
  | nil => rw [List.nil_append, treeDocList, List.nil_append]
  | cons u utl ih => rw [List.cons_append, treeDocList, treeDocList, ih, List.cons_append]

/-- `treeDocList` commutes with `List.reverse`. -/
theorem treeDocList_reverse (xs : List Lean.Json) :
    treeDocList xs.reverse = (treeDocList xs).reverse := by
  induction xs with
  | nil => simp [treeDocList]
  | cons x tl ih =>
    have h1 : treeDocList [x] = [treeDoc x] := by rw [treeDocList, treeDocList]
    have h2 : treeDocList (x :: tl) = treeDoc x :: treeDocList tl := by rw [treeDocList]
    rw [List.reverse_cons, treeDocList_append, ih, h1, h2, List.reverse_cons]

/-- Expand a single `ObjWalkItem` into its in-order list of key-value `JsonDoc` nodes. -/
def walkItemDocs : ObjWalkItem → List JsonDoc
  | .tree t => treeEntriesDoc t
  | .emitKv k v =>
    [JsonDoc.group (.append (.text (renderString k ++ ":")) (.append .line (treeDoc v)))]

/-- Evaluate a `PrettyFrame` stack given the `JsonDoc` of the current focus. -/
def evalPrettyFrames : JsonDoc → List PrettyFrame → JsonDoc
  | valFmt, [] => valFmt
  | valFmt, .arr accRev rem :: rest =>
    let allRev := (treeDocList rem).reverse ++ valFmt :: accRev
    match allRev with
    | [] => evalPrettyFrames (.text "[]") rest
    | last :: restRev => evalPrettyFrames (docBracket "[" (joinCommaLineRev last restRev) "]") rest
  | valFmt, .objKv k acc pending :: rest =>
    let kvFmt := JsonDoc.group (.append (.text (renderString k ++ ":")) (.append .line valFmt))
    let finalAcc := (pending.flatMap walkItemDocs).reverse ++ kvFmt :: acc
    let objDoc := match finalAcc with
      | [] => JsonDoc.text "{}"
      | last :: restRev => docBracket "{" (joinCommaLineRev last restRev) "}"
    evalPrettyFrames objDoc rest
termination_by structural _ fs => fs

private theorem renderEval_strong :
    ∀ (W : Nat),
      (∀ (j : Lean.Json) (frames : List PrettyFrame),
        jsonWeight j + prettyFramesWeight frames ≤ W →
        renderEval j frames = evalPrettyFrames (treeDoc j) frames) ∧
      (∀ (acc : List JsonDoc) (pending : List ObjWalkItem) (frames : List PrettyFrame),
        1 + pendingWeight pending + prettyFramesWeight frames ≤ W →
        renderObjNext acc pending frames =
          let finalAcc := (pending.flatMap walkItemDocs).reverse ++ acc
          let doc := match finalAcc with
            | [] => JsonDoc.text "{}"
            | last :: restRev => docBracket "{" (joinCommaLineRev last restRev) "}"
          evalPrettyFrames doc frames) ∧
      (∀ (valFmt : JsonDoc) (frames : List PrettyFrame),
        prettyFramesWeight frames ≤ W →
        renderApply valFmt frames = evalPrettyFrames valFmt frames) := by
  intro W
  induction W using Nat.strongRecOn with
  | ind W ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro j frames hW
      cases j with
      | null =>
        unfold renderEval treeDoc
        exact (ih (prettyFramesWeight frames) (by simp [jsonWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
      | bool b =>
        cases b <;>
          (unfold renderEval treeDoc
           exact (ih (prettyFramesWeight frames) (by simp [jsonWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _))
      | num n =>
        unfold renderEval treeDoc
        exact (ih (prettyFramesWeight frames) (by simp [jsonWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
      | str s =>
        unfold renderEval treeDoc
        exact (ih (prettyFramesWeight frames) (by simp [jsonWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
      | arr elems =>
        rcases elems with ⟨elList⟩
        cases elList with
        | nil =>
          have hre : renderEval (.arr ⟨[]⟩) frames = renderApply (.text "[]") frames := by
            unfold renderEval; rfl
          have htd : treeDoc (.arr ⟨[]⟩) = .text "[]" := by unfold treeDoc; rfl
          rw [hre, htd]
          exact (ih (prettyFramesWeight frames) (by simp [jsonWeight, arrWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
        | cons x xs =>
          have hre : renderEval (.arr ⟨x :: xs⟩) frames = renderEval x (.arr [] xs :: frames) := by
            conv => lhs; unfold renderEval
          have hDec : jsonWeight x + prettyFramesWeight (.arr [] xs :: frames) < W := by
            simp [jsonWeight, arrWeight, prettyFramesWeight, prettyFrameWeight] at hW ⊢; omega
          rw [hre, (ih _ hDec).1 x (.arr [] xs :: frames) (Nat.le_refl _)]
          simp only [evalPrettyFrames]
          have htd : treeDoc (.arr ⟨x :: xs⟩) =
              (match (treeDocList xs).reverse ++ [treeDoc x] with
               | [] => .text "[]"
               | last :: restRev => docBracket "[" (joinCommaLineRev last restRev) "]") := by
            conv => lhs; unfold treeDoc
            dsimp only
            cases hrev : (x :: xs).reverse with
            | nil => exfalso; have := congrArg List.length hrev; simp at this
            | cons last restRev =>
              dsimp only
              have hRevTD : treeDocList ((x :: xs).reverse) = (treeDocList xs).reverse ++ [treeDoc x] := by
                have h1 : treeDocList [x] = [treeDoc x] := by rw [treeDocList, treeDocList]
                rw [List.reverse_cons, treeDocList_append, treeDocList_reverse, h1]
              rw [hrev, treeDocList] at hRevTD
              rw [← hRevTD]
          rw [htd]
          cases (treeDocList xs).reverse ++ [treeDoc x] <;> rfl
      | obj kvs =>
        rcases kvs with ⟨⟨t⟩⟩
        cases t with
        | leaf =>
          have hre : renderEval (.obj ⟨⟨.leaf⟩⟩) frames = renderApply (.text "{}") frames := by
            unfold renderEval; rfl
          have htd : treeDoc (.obj ⟨⟨.leaf⟩⟩) = .text "{}" := by unfold treeDoc; rfl
          rw [hre, htd]
          exact (ih (prettyFramesWeight frames) (by simp [jsonWeight, treeWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
        | inner sz k v l r =>
          have hre : renderEval (.obj ⟨⟨.inner sz k v l r⟩⟩) frames =
              renderObjNext [] [.tree (.inner sz k v l r)] frames := by
            unfold renderEval; rfl
          have hDec : 1 + pendingWeight [.tree (.inner sz k v l r)] + prettyFramesWeight frames < W := by
            simp [jsonWeight, pendingWeight, objWalkWeight] at hW ⊢; omega
          rw [hre, (ih _ hDec).2.1 [] [.tree (.inner sz k v l r)] frames (Nat.le_refl _)]
          have htd : treeDoc (.obj ⟨⟨.inner sz k v l r⟩⟩) =
              (match (treeEntriesDoc (.inner sz k v l r)).reverse with
               | [] => .text "{}"
               | last :: restRev => docBracket "{" (joinCommaLineRev last restRev) "}") := by
            unfold treeDoc; rfl
          simp [htd, walkItemDocs]
    · intro acc pending frames hW
      cases pending with
      | nil =>
        unfold renderObjNext
        simp only [List.flatMap_nil, List.reverse_nil, List.nil_append]
        exact (ih (prettyFramesWeight frames) (by simp [pendingWeight] at hW; omega)).2.2 _ frames (Nat.le_refl _)
      | cons w rest =>
        cases w with
        | tree t =>
          cases t with
          | leaf =>
            unfold renderObjNext
            have hDec : 1 + pendingWeight rest + prettyFramesWeight frames < W := by
              simp [pendingWeight, objWalkWeight, treeWeight] at hW ⊢; omega
            rw [(ih _ hDec).2.1 acc rest frames (Nat.le_refl _)]
            simp [walkItemDocs, treeEntriesDoc]
          | inner sz k v l r =>
            unfold renderObjNext
            dsimp only
            let next0 := match r with | .leaf => rest | .inner _ _ _ _ _ => ObjWalkItem.tree r :: rest
            let next1 := ObjWalkItem.emitKv k v :: next0
            let next2 := match l with | .leaf => next1 | .inner _ _ _ _ _ => ObjWalkItem.tree l :: next1
            have hDec : 1 + pendingWeight next2 + prettyFramesWeight frames < W := by
              dsimp only [next2, next1, next0]
              cases l <;> cases r <;> simp [pendingWeight, objWalkWeight, treeWeight] at hW ⊢ <;> omega
            change renderObjNext acc next2 frames = _
            rw [(ih _ hDec).2.1 acc next2 frames (Nat.le_refl _)]
            have hFlat : next2.flatMap walkItemDocs =
                (ObjWalkItem.tree (.inner sz k v l r) :: rest).flatMap walkItemDocs := by
              dsimp only [next2, next1, next0]
              cases l <;> cases r <;> simp [walkItemDocs, treeEntriesDoc, List.append_assoc]
            rw [hFlat]
        | emitKv k v =>
          unfold renderObjNext
          have hDec : jsonWeight v + prettyFramesWeight (.objKv k acc rest :: frames) < W := by
            simp [pendingWeight, objWalkWeight, prettyFramesWeight, prettyFrameWeight] at hW ⊢; omega
          rw [(ih _ hDec).1 v (.objKv k acc rest :: frames) (Nat.le_refl _)]
          simp [evalPrettyFrames, walkItemDocs, List.append_assoc]
    · intro valFmt frames hW
      cases frames with
      | nil => unfold renderApply evalPrettyFrames; rfl
      | cons f rest =>
        cases f with
        | arr accRev rem =>
          cases rem with
          | nil =>
            unfold renderApply
            have hDec : prettyFramesWeight rest < W := by
              simp [prettyFramesWeight, prettyFrameWeight, arrWeight] at hW ⊢; omega
            rw [(ih _ hDec).2.2 _ rest (Nat.le_refl _)]
            simp [evalPrettyFrames, treeDocList]
          | cons x xs =>
            unfold renderApply
            have hDec : jsonWeight x + prettyFramesWeight (.arr (valFmt :: accRev) xs :: rest) < W := by
              simp [prettyFramesWeight, prettyFrameWeight, arrWeight] at hW ⊢; omega
            rw [(ih _ hDec).1 x (.arr (valFmt :: accRev) xs :: rest) (Nat.le_refl _)]
            have htdCons : treeDocList (x :: xs) = treeDoc x :: treeDocList xs := by rw [treeDocList]
            simp [evalPrettyFrames, htdCons, List.append_assoc]
        | objKv k acc pending =>
          unfold renderApply
          dsimp only
          have hDec : 1 + pendingWeight pending + prettyFramesWeight rest < W := by
            simp [prettyFramesWeight, prettyFrameWeight] at hW ⊢; omega
          rw [(ih _ hDec).2.1 _ pending rest (Nat.le_refl _)]
          simp [evalPrettyFrames]

/-- `renderFormat j` equals structural `treeDoc j` for every `j : Lean.Json`. -/
theorem renderFormat_eq_treeDoc (j : Lean.Json) : renderFormat j = treeDoc j :=
  (renderEval_strong (jsonWeight j + prettyFramesWeight [])).1 j [] (Nat.le_refl _)

end LeanSwe.Json.Proofs
