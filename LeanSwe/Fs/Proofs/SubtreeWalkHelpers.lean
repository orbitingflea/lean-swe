import LeanSwe.Fs.Proofs.SubtreeCore
import LeanSwe.Fs.Proofs.SubtreeIsolation
import LeanSwe.Fs.Proofs.RawDirOps

namespace LeanSwe.Fs.Proofs

open Core LeanSwe.Fs LeanSwe.Fs.Raw LeanSwe.Fs.Model

private theorem splitLastAux_eq_some_of_ne_nil (xs acc : List EntryName) (hNe : xs ≠ []) :
    ∃ pre leaf, Internal.splitLastAux xs acc = some (pre, leaf) ∧ acc.reverse ++ xs = pre ++ [leaf] := by
  induction xs generalizing acc with
  | nil => contradiction
  | cons x rest ih =>
    cases rest with
    | nil =>
      refine ⟨acc.reverse, x, ?_, by simp⟩
      simp [Internal.splitLastAux]
    | cons y ys =>
      rcases ih (x :: acc) (by simp) with ⟨pre, leaf, hEq, hApp⟩
      refine ⟨pre, leaf, ?_, ?_⟩
      · simpa [Internal.splitLastAux] using hEq
      · simpa [List.append_assoc] using hApp

/-- `splitLastAux` decomposes `pre ++ rest` (`rest ≠ []`) so `pre` prefixes the parent path. -/
theorem splitLastAux_prefix_of_append_ne_nil (pre rest : List EntryName) (hRest : rest ≠ []) :
    ∃ parent leaf tail,
      Internal.splitLastAux (pre ++ rest) [] = some (parent, leaf) ∧
        parent = pre ++ tail ∧ rest = tail ++ [leaf] := by
  rcases splitLastAux_eq_some_of_ne_nil rest [] hRest with ⟨tail, leaf, _, hRestApp⟩
  rcases splitLastAux_eq_some_of_ne_nil (pre ++ rest) [] (by intro h; cases rest <;> simp_all) with
    ⟨parent, leaf', hEq, hApp⟩
  have h1 : rest = tail ++ [leaf] := by simpa using hRestApp
  have h2 : pre ++ rest = parent ++ [leaf'] := by simpa using hApp
  rw [h1, ← List.append_assoc] at h2
  have hLen := congrArg List.length h2
  simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hLen
  have hTake := congrArg (List.take (pre.length + tail.length)) h2
  simp only [← List.length_append, List.take_left] at hTake
  have hPar : parent = pre ++ tail := by
    rw [List.take_left'] at hTake
    · exact hTake.symm
    · simp only [List.length_append]; exact hLen.symm
  have hDrop := congrArg (List.drop parent.length) h2
  rw [hPar, List.drop_left] at hDrop
  simp only [← hPar, List.drop_left, List.cons.injEq, and_true] at hDrop
  rw [← hDrop] at hEq
  exact ⟨parent, leaf, tail, hEq, hPar, h1⟩

private theorem validSeg_char_props {s : String} (hs : validSeg s = true) :
    s.toList ≠ [] ∧ '/' ∉ s.toList ∧ Char.ofNat 0 ∉ s.toList ∧ s.toList ≠ ['.'] ∧ s.toList ≠ ['.', '.'] := by
  unfold validSeg at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hs
  rcases hs with ⟨⟨⟨⟨hNe, hSl⟩, hNul⟩, hDot⟩, hDD⟩
  exact ⟨by simpa [String.isEmpty_iff] using hNe,
    by simpa [List.contains_iff_mem] using hSl,
    by simpa [List.contains_iff_mem] using hNul,
    hDot, hDD⟩

private theorem splitCharList_cons (sep c : Char) (cs : List Char) :
    Internal.splitCharList sep (c :: cs) =
      if c == sep then [] :: Internal.splitCharList sep cs
      else
        match Internal.splitCharList sep cs with
        | [] => [[c]]
        | seg :: rest => (c :: seg) :: rest :=
  rfl

private theorem splitCharList_of_not_mem (sep : Char) (cs : List Char) (hNe : cs ≠ []) (hNot : sep ∉ cs) :
    Internal.splitCharList sep cs = [cs] := by
  induction cs with
  | nil => contradiction
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at hNot
    have hcNe : (c == sep) = false := beq_false_of_ne (Ne.symm hNot.1)
    cases rest with
    | nil =>
      rw [splitCharList_cons, hcNe]
      rfl
    | cons d ds =>
      have hSub := ih (by simp) hNot.2
      rw [splitCharList_cons, hcNe]
      simp only [Bool.false_eq_true, ↓reduceIte, hSub]

private theorem joinSlashChars_singleton (x : List Char) : Internal.joinSlashChars [x] = x := by
  simp [Internal.joinSlashChars]

private theorem joinSlashChars_cons2 (x y : List Char) (ys : List (List Char)) :
    Internal.joinSlashChars (x :: y :: ys) = x ++ '/' :: Internal.joinSlashChars (y :: ys) :=
  rfl

private theorem splitCharList_joinSlashChars {segs : List String} (hNe : segs ≠ [])
    (hValid : ∀ s ∈ segs, validSeg s = true) :
    Internal.splitCharList '/' (Internal.joinSlashChars (segs.map String.toList)) = segs.map String.toList := by
  induction segs with
  | nil => contradiction
  | cons s rest ih =>
    have hV := validSeg_char_props (hValid s List.mem_cons_self)
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil]
      rw [joinSlashChars_singleton]
      exact splitCharList_of_not_mem '/' s.toList hV.1 hV.2.1
    | cons r rs =>
      have ihRest := ih (by simp) (fun t ht => hValid t (List.mem_cons_of_mem _ ht))
      have hMap : r.toList :: rs.map String.toList = (r :: rs).map String.toList := rfl
      rw [← hMap] at ihRest
      simp only [List.map_cons]
      rw [joinSlashChars_cons2]
      have hAppend : ∀ cs : List Char, '/' ∉ cs →
          ∀ tail hd tl,
            Internal.splitCharList '/' tail = hd :: tl →
            Internal.splitCharList '/' (cs ++ '/' :: tail) = cs :: hd :: tl := by
        intro cs hNoSl tail hd tl hTail
        induction cs with
        | nil =>
          simp only [List.nil_append]
          rw [splitCharList_cons, beq_self_eq_true]
          simp only [↓reduceIte, hTail]
        | cons c cs ihcs =>
          simp only [List.mem_cons, not_or] at hNoSl
          have hSub := ihcs hNoSl.2
          simp only [List.cons_append]
          rw [splitCharList_cons]
          have hcNe : (c == '/') = false := beq_false_of_ne (Ne.symm hNoSl.1)
          simp only [hcNe, Bool.false_eq_true, ↓reduceIte, hSub]
      exact hAppend s.toList hV.2.1 _ r.toList (rs.map String.toList) ihRest

private theorem collapseChars_nil (abs : Bool) (acc : List (List Char)) :
    Internal.collapseChars abs [] acc = acc.reverse := by
  simp [Internal.collapseChars]

private theorem collapseChars_cons (abs : Bool) (seg : List Char) (rest acc : List (List Char)) :
    Internal.collapseChars abs (seg :: rest) acc =
      if seg.isEmpty || seg == ['.'] then Internal.collapseChars abs rest acc
      else if seg == ['.', '.'] then
        match acc with
        | top :: tail =>
          if top != ['.', '.'] then Internal.collapseChars abs rest tail
          else Internal.collapseChars abs rest (if abs then acc else ['.', '.'] :: acc)
        | [] => Internal.collapseChars abs rest (if abs then [] else [['.', '.']])
      else Internal.collapseChars abs rest (seg :: acc) :=
  rfl

private theorem collapseChars_valid (abs : Bool) (ps acc : List (List Char))
    (hValid : ∀ p ∈ ps, p ≠ [] ∧ p ≠ ['.'] ∧ p ≠ ['.', '.']) :
    Internal.collapseChars abs ps acc = acc.reverse ++ ps := by
  induction ps generalizing acc with
  | nil =>
    rw [collapseChars_nil]
    simp
  | cons p rest ih =>
    have hp := hValid p List.mem_cons_self
    have hC1 : (p.isEmpty || p == ['.']) = false := by
      simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff_exists_mem]
      constructor
      · cases p with
        | nil => exact absurd rfl hp.1
        | cons a _ => exact ⟨a, List.mem_cons_self⟩
      · exact beq_false_of_ne hp.2.1
    have hC2 : (p == ['.', '.']) = false := beq_false_of_ne hp.2.2
    rw [collapseChars_cons, hC1, hC2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ih (p :: acc) (fun q hq => hValid q (List.mem_cons_of_mem _ hq))]
    simp [List.append_assoc]

/-- Canonical `pathOfSegs segs` is fixed by `vfsAbsNorm` when every segment satisfies `validSeg`. -/
theorem vfsAbsNorm_pathOfSegs (cwd : String) (segs : List String) (hValid : ∀ s ∈ segs, validSeg s = true) :
    vfsAbsNorm cwd (pathOfSegs segs) = pathOfSegs segs := by
  cases segs with
  | nil =>
    have hP0 : pathOfSegs [] = "/" := rfl
    rw [hP0]
    unfold vfsAbsNorm
    simp only [show Internal.isAbsolute "/" = true from rfl, ↓reduceIte]
    rfl
  | cons s rest =>
    have hEq := pathOfSegs_eq_ofList_joinSlashChars (s :: rest)
    have hAbs : Internal.isAbsolute (pathOfSegs (s :: rest)) = true := by
      rw [hEq]
      simp [Internal.isAbsolute, Internal.isAbsChars]
    unfold vfsAbsNorm
    simp only [hAbs, ↓reduceIte]
    unfold Internal.normPath
    have hToList : (pathOfSegs (s :: rest)).toList = '/' :: Internal.joinSlashChars ((s :: rest).map String.toList) := by
      rw [hEq]; simp
    rw [hToList]
    have hIsAbs : Internal.isAbsChars ('/' :: Internal.joinSlashChars ((s :: rest).map String.toList)) = true := rfl
    simp only [hIsAbs, ↓reduceIte]
    have hSplit : Internal.splitCharList '/' ('/' :: Internal.joinSlashChars ((s :: rest).map String.toList)) =
        [] :: (s :: rest).map String.toList := by
      have hRest := splitCharList_joinSlashChars (by simp : s :: rest ≠ []) hValid
      rw [splitCharList_cons, beq_self_eq_true]
      simp only [↓reduceIte]
      change [] :: Internal.splitCharList '/' (Internal.joinSlashChars ((s :: rest).map String.toList)) = _
      rw [hRest]
    rw [hSplit]
    have hDropEmpty : Internal.collapseChars true ([] :: (s :: rest).map String.toList) [] =
        Internal.collapseChars true ((s :: rest).map String.toList) [] := by
      rw [collapseChars_cons]
      rfl
    rw [hDropEmpty]
    rw [collapseChars_valid true ((s :: rest).map String.toList) []]
    · simp only [List.reverse_nil, List.nil_append]
      exact hEq.symm
    · intro p hp
      simp only [List.mem_map] at hp
      rcases hp with ⟨t, htMem, rfl⟩
      have htV := validSeg_char_props (hValid t htMem)
      exact ⟨htV.1, htV.2.2.2.1, htV.2.2.2.2⟩

private theorem getLast?_append_ne_nil {α : Type} (xs ys : List α) (h : ys ≠ []) :
    (xs ++ ys).getLast? = ys.getLast? := by
  cases ys with
  | nil => contradiction
  | cons y ys' =>
    induction xs with
    | nil => simp
    | cons _ _ ih => simp [List.getLast?_cons, ih]

private theorem joinSlashChars_ne_nil_and_last_ne_slash (xss : List (List Char)) (hNe : xss ≠ [])
    (hp : ∀ xs ∈ xss, xs ≠ [] ∧ '/' ∉ xs) :
    Internal.joinSlashChars xss ≠ [] ∧ (Internal.joinSlashChars xss).getLast? ≠ some '/' := by
  induction xss with
  | nil => contradiction
  | cons x rest ih =>
    have hx := hp x List.mem_cons_self
    cases rest with
    | nil =>
      rw [joinSlashChars_singleton]
      refine ⟨hx.1, ?_⟩
      intro hLast
      exact hx.2 (List.mem_of_getLast? hLast)
    | cons y ys =>
      have hSub := ih (by simp) (fun z hz => hp z (List.mem_cons_of_mem _ hz))
      rw [joinSlashChars_cons2]
      have hTailNe : '/' :: Internal.joinSlashChars (y :: ys) ≠ [] := by simp
      refine ⟨?_, ?_⟩
      · intro hNil
        simp only [List.append_eq_nil_iff] at hNil
        exact hTailNe hNil.2
      · rw [getLast?_append_ne_nil _ _ hTailNe]
        have hCons : ('/' :: Internal.joinSlashChars (y :: ys)).getLast? = (Internal.joinSlashChars (y :: ys)).getLast? := by
          cases hJ : Internal.joinSlashChars (y :: ys) with
          | nil => exact absurd hJ hSub.1
          | cons _ _ => rfl
        rw [hCons]
        exact hSub.2

/-- Non-empty canonical `pathOfSegs segs` passes `Model.isValidRawPath` when every segment satisfies `validSeg`. -/
theorem isValidRawPath_pathOfSegs {segs : List String} (hNe : segs ≠ []) (hValid : ∀ s ∈ segs, validSeg s = true) :
    Model.isValidRawPath (pathOfSegs segs) = true := by
  have hEq := pathOfSegs_eq_ofList_joinSlashChars segs
  have hList : (pathOfSegs segs).toList = '/' :: Internal.joinSlashChars (segs.map String.toList) := by
    rw [hEq]; simp
  unfold Model.isValidRawPath
  rw [hList]
  have hJProps := joinSlashChars_ne_nil_and_last_ne_slash (segs.map String.toList) (by simp [hNe])
    (fun xs hxs => by
      simp only [List.mem_map] at hxs
      rcases hxs with ⟨t, htMem, rfl⟩
      have ht := validSeg_char_props (hValid t htMem)
      exact ⟨ht.1, ht.2.1⟩)
  have hNul : Char.ofNat 0 ∉ '/' :: Internal.joinSlashChars (segs.map String.toList) := by
    have hJ : ∀ xss : List (List Char), (∀ xs ∈ xss, Char.ofNat 0 ∉ xs) →
        Char.ofNat 0 ∉ Internal.joinSlashChars xss := by
      intro xss hxs
      induction xss with
      | nil => simp [Internal.joinSlashChars]
      | cons x rest ih =>
        cases rest with
        | nil =>
          rw [joinSlashChars_singleton]
          exact hxs x List.mem_cons_self
        | cons y ys =>
          rw [joinSlashChars_cons2]
          simp only [List.mem_append, List.mem_cons, not_or]
          refine ⟨hxs x List.mem_cons_self, by decide, ih (fun z hz => hxs z (List.mem_cons_of_mem _ hz))⟩
    simp only [List.mem_cons, not_or]
    refine ⟨by decide, hJ (segs.map String.toList) ?_⟩
    intro xs hxs
    simp only [List.mem_map] at hxs
    rcases hxs with ⟨t, htMem, rfl⟩
    exact (validSeg_char_props (hValid t htMem)).2.2.1
  have hLast : ('/' :: Internal.joinSlashChars (segs.map String.toList)).getLast? ≠ some '/' := by
    cases hJ : Internal.joinSlashChars (segs.map String.toList) with
    | nil => exact absurd hJ hJProps.1
    | cons hd tl =>
      have hL : ('/' :: hd :: tl).getLast? = (hd :: tl).getLast? := rfl
      rw [hL, ← hJ]
      exact hJProps.2
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_cons, Bool.not_false,
    decide_eq_false_iff_not, Bool.and_eq_false_iff, true_and]
  exact ⟨hNul, Or.inr (beq_false_of_ne hLast)⟩

/-- `st.nodes (pathOfSegs segs)` equals `nodeAt st.tree segs` whenever all segments are valid. -/
theorem vfsState_nodes_pathOfSegs (st : VfsState) (segs : List String) (hValid : ∀ s ∈ segs, validSeg s = true) :
    st.nodes (pathOfSegs segs) = nodeAt st.tree segs := by
  change vfsTreeNodes st.tree (pathOfSegs segs) = nodeAt st.tree segs
  unfold vfsTreeNodes
  simp only [isCanonPath_pathOfSegs segs hValid, ↓reduceIte, vfsSplitSegs_pathOfSegs segs hValid]

/-- `SameOutside root st st'` preserves `nodeAt` at any valid path `p` not under `root`. -/
theorem SameOutside_nodeAt_eq {root : List String} {st st' : VfsState}
    (hSame : SameOutside root st st') {p : List String}
    (hNotPref : ¬ (root <+: p)) (hValid : ∀ s ∈ p, validSeg s = true) :
    nodeAt st'.tree p = nodeAt st.tree p := by
  have hNodes := hSame (pathOfSegs p) (by rw [vfsSplitSegs_pathOfSegs p hValid]; exact hNotPref)
  simpa [vfsState_nodes_pathOfSegs st' p hValid, vfsState_nodes_pathOfSegs st p hValid] using hNodes

/-- Setting `tmp` (`none` initially) to a file and immediately removing `tmp` leaves every `nodeAt` unchanged. -/
theorem nodeAt_vfsTreeSet_temp_roundtrip (t : VfsTree) (parentPos : List String) (tmp : String)
    (v : VfsTree) (hDir : ∃ dm ch, vfsTreeGet t parentPos = some (.dir dm ch))
    (hTmpNone : nodeAt t (parentPos ++ [tmp]) = none) (q : List String) :
    nodeAt (vfsTreeSet (vfsTreeSet t (parentPos ++ [tmp]) (some v)) (parentPos ++ [tmp]) none) q =
      nodeAt t q := by
  let t1 := vfsTreeSet t (parentPos ++ [tmp]) (some v)
  have hDir1 : ∃ dm ch, vfsTreeGet t1 parentPos = some (.dir dm ch) := by
    by_cases hPreSelf : parentPos ++ [tmp] <+: parentPos
    · exfalso
      have hLen := List.IsPrefix.length_le hPreSelf
      simp at hLen
      omega
    · have hPar1 : nodeAt t1 parentPos = nodeAt t parentPos :=
        nodeAt_vfsTreeSet_outside t parentPos tmp (some v) parentPos hDir hPreSelf
      rcases hDir with ⟨dm, ch, hG⟩
      have hPar : nodeAt t parentPos = some (.dir dm) := by simp [nodeAt, hG, vfsTreeTopNode]
      rw [hPar] at hPar1
      exact ⟨dm, vfsTreeGet_dir_of_nodeAt hPar1⟩
  by_cases hPre : parentPos ++ [tmp] <+: q
  · rcases hPre with ⟨rest, rfl⟩
    have hOrigNone : nodeAt t ((parentPos ++ [tmp]) ++ rest) = none :=
      nodeAt_none_desc t (parentPos ++ [tmp]) rest hTmpNone
    rw [hOrigNone]
    cases rest with
    | nil => simpa using nodeAt_vfsTreeSet_eq t1 parentPos tmp none hDir1
    | cons a as =>
      have hTopNone : nodeAt (vfsTreeSet t1 (parentPos ++ [tmp]) none) (parentPos ++ [tmp]) = none := by
        simpa using nodeAt_vfsTreeSet_eq t1 parentPos tmp none hDir1
      exact nodeAt_none_desc _ (parentPos ++ [tmp]) (a :: as) hTopNone
  · rw [nodeAt_vfsTreeSet_outside t1 parentPos tmp none q hDir1 hPre,
      nodeAt_vfsTreeSet_outside t parentPos tmp (some v) q hDir hPre]

private theorem vfsResolveSegs_succ (nodes : String → Option VfsNode) (cur : String) (segs : List String)
    (follow : Bool) (fuel : Nat) :
    vfsResolveSegs nodes cur segs follow (fuel + 1) =
      match segs with
      | [] =>
        match nodes cur with
        | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
        | some (.symlink target m) =>
          if follow then
            let par := (Internal.parent cur).getD "/"
            let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
            vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs) true fuel
          else .ok (cur, .symlink target m)
        | some node => .ok (cur, node)
      | seg :: rest =>
        match nodes cur with
        | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
        | some (.dir mode) =>
          if (mode / 64) % 2 == 0 then
            .error { kind := .permissionDenied, path := some cur, message := s!"permission denied: {cur}" }
          else
            vfsResolveSegs nodes (vfsChildPath cur seg) rest follow fuel
        | some (.symlink target _) =>
          let par := (Internal.parent cur).getD "/"
          let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
          vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs ++ seg :: rest) follow fuel
        | some (.file _ _) =>
          .error { kind := .notADirectory, path := some cur, message := s!"not a directory: {cur}" } :=
  rfl

/-- Resolving along a symlink-free chain of directories inside `vfsResolveSegs` advances to the suffix. -/
theorem vfsResolveSegs_steps (nodes : String → Option VfsNode) (p2 : List String)
    (followLast : Bool) (fuel : Nat) (p1 : List String) (hFuel : p2.length < fuel)
    (hValid1 : ∀ s ∈ p1, validSeg s = true)
    (hValid2 : ∀ s ∈ p2, validSeg s = true)
    (hInter : ∀ k < p2.length, ∃ dm, nodes (pathOfSegs (p1 ++ p2.take k)) = some (.dir dm) ∧ dm / 64 % 2 = 1) :
    vfsResolveSegs nodes (pathOfSegs p1) p2 followLast fuel =
      vfsResolveSegs nodes (pathOfSegs (p1 ++ p2)) [] followLast (fuel - p2.length) := by
  induction p2 generalizing p1 fuel with
  | nil => simp
  | cons seg rest ih =>
    cases fuel with
    | zero => simp at hFuel
    | succ f =>
      have hHere : ∃ dm, nodes (pathOfSegs p1) = some (.dir dm) ∧ dm / 64 % 2 = 1 := by
        simpa using hInter 0 (by simp)
      rcases hHere with ⟨dm, hN, hEx⟩
      have hExF : (dm / 64 % 2 == 0) = false := by
        rw [hEx]
        decide
      rw [vfsResolveSegs_succ]
      dsimp only
      rw [hN]
      simp only [hExF, Bool.false_eq_true, ↓reduceIte]
      have hsValid : validSeg seg = true := hValid2 seg List.mem_cons_self
      rw [vfsChildPath_pathOfSegs p1 seg hValid1]
      have ihRes := ih f (p1 ++ [seg]) (by simp at hFuel; omega)
        (fun s hs => by
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with h1 | rfl
          · exact hValid1 s h1
          · exact hsValid)
        (fun s hs => hValid2 s (List.mem_cons_of_mem _ hs))
        (fun k hk => by
          simpa [List.take, List.append_assoc] using hInter (k + 1) (by simp; omega))
      simpa [List.append_assoc, List.length_cons, Nat.succ_sub_succ_eq_sub] using ihRes

/-- Evaluating `bracketCloseDirM` in `StateM VfsState` runs `act` and closes `dh` on the resulting state. -/
theorem bracketCloseDirM_run {α : Type} (ops : RawDirOpsM (StateM VfsState)) (dh : DirHandle)
    (act : StateM VfsState α) (st : VfsState) :
    Internal.bracketCloseDirM ops dh act st =
      ((act st).1, (ops.closeDir dh (act st).2).2) := by
  unfold Internal.bracketCloseDirM
  simp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure, tryFinally']
  cases hA : act st with
  | mk _ s =>
    dsimp only
    cases hC : ops.closeDir dh s with
    | mk _ _ => rfl

private noncomputable def openDirAtTplH (st : VfsState) (dh : DirHandle) (name : EntryName)
    (id : Nat) : Except FsError DirHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (mInvalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none =>
      (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | none =>
          (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error
            { kind := .invalidInput
              path := some name.val
              message := s!"symlink refused in subtree traversal: {name.val}" },
            st)
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            (.ok { handleId := id, rootPath := pathOfSegs childPos },
              { st with openDirs := (id, childPos) :: st.openDirs, nextDirId := id + 1 })
        | some _ =>
          (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
    | some _ =>
      (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- `vfsDirOps.openDirAt` succeeds when parent is `+x` dir and child is `+r` dir. -/
theorem vfsDirOps_openDirAt_dir_ok (st : VfsState) (dh : DirHandle) (name : EntryName)
    (pos : List String) (parMode mode : Nat)
    (hLd : lookupDir st dh = some pos)
    (hPar : nodeAt st.tree pos = some (.dir parMode))
    (hExec : parMode / 64 % 2 = 1)
    (hChild : nodeAt st.tree (pos ++ [name.val]) = some (.dir mode))
    (hRead : mode / 256 % 2 = 1) :
    ∃ nextDh st', vfsDirOps.openDirAt dh name st = (.ok nextDh, st') := by
  have hTpl : ∃ id, vfsDirOps.openDirAt dh name st = openDirAtTplH st dh name id := ⟨_, rfl⟩
  rcases hTpl with ⟨id, hEq⟩
  rw [hEq]
  unfold openDirAtTplH
  rw [hLd]
  dsimp only
  rw [hPar]
  have hExF : (parMode / 64 % 2 == 0) = false := by rw [hExec]; decide
  have hRdF : (mode / 256 % 2 == 0) = false := by rw [hRead]; decide
  simp only [hExF, Bool.false_eq_true, ↓reduceIte, hChild, hRdF]
  exact ⟨_, _, rfl⟩

/-- `vfsDirOps.closeDir` removes a freshly opened handle `(dh.handleId, pos)` from `st.openDirs`. -/
theorem vfsDirOps_closeDir_fresh (dh : DirHandle) (st : VfsState) (pos : List String)
    (hPos : 0 < dh.handleId) (rest : List (Nat × List String))
    (hOpen : st.openDirs = (dh.handleId, pos) :: rest)
    (hLt : ∀ p ∈ rest, p.1 < dh.handleId) :
    vfsDirOps.closeDir dh st = (.ok (), { st with openDirs := rest }) := by
  rw [vfsDirOps_closeDir_def]
  have hZ : (dh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  have hAny : (st.openDirs.any fun x => x.1 == dh.handleId) = true := by
    rw [hOpen]
    simp
  have hFilt : st.openDirs.filter (fun p => p.1 != dh.handleId) = rest := by
    rw [hOpen]
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [List.filter_eq_self]
    intro p hp
    simp only [bne_iff_ne, ne_eq]
    exact Nat.ne_of_lt (hLt p hp)
  simp only [hZ, Bool.false_eq_true, ↓reduceIte, hAny, hFilt]

/-- `DirHandleInvariant` is preserved when replacing `openDirs` by a subset. -/
theorem dirHandleInvariant_filter (st : VfsState) (hInv : DirHandleInvariant st)
    (dh : DirHandle) :
    DirHandleInvariant { st with openDirs := st.openDirs.filter (fun p => p.1 != dh.handleId) } := by
  intro id pos hm
  simp only [List.mem_filter] at hm
  exact hInv id pos hm.1

private theorem lookupDir_open_close_step (isRoot : Bool) (st st1 : VfsState) (cur nextDh : DirHandle)
    (pos : List String) (s : EntryName)
    (hLd : lookupDir st cur = some pos)
    (hOk : vfsDirOps.openDirAt cur s st = (.ok nextDh, st1)) :
    let stMid := if isRoot then st1 else { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }
    let base0 := if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)
    0 < nextDh.handleId ∧
      stMid.tree = st.tree ∧ stMid.keys = st.keys ∧ stMid.cwd = st.cwd ∧
      stMid.nonce = st.nonce ∧ stMid.locks = st.locks ∧
      lookupDir stMid nextDh = some (pos ++ [s.val]) ∧
      (DirHandleInvariant st → DirHandleInvariant stMid) ∧
      stMid.openDirs = (nextDh.handleId, pos ++ [s.val]) :: base0 ∧
      (∀ p ∈ base0, p.1 < nextDh.handleId) ∧
      (isRoot = false →
        (vfsDirOps.closeDir cur st1).2 = { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }) := by
  rcases vfsDirOps_openDirAt_ok cur s st nextDh st1 hOk with
    ⟨hNextPos, hNextGtId, hNextGt, pos', _, _, hLd', _, _, _, _, _, hSt1⟩
  have hPosEq : pos' = pos := Option.some.inj (hLd'.symm.trans hLd)
  subst hPosEq
  have hCurPos : (cur.handleId == 0) = false := by
    unfold lookupDir at hLd
    cases hZ : cur.handleId == 0 <;> simp [hZ] at hLd ⊢
  have hNextInv1 : DirHandleInvariant st → DirHandleInvariant st1 := by
    intro hInv id p hm
    rw [hSt1] at hm
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hOld
    · rw [hSt1]
      dsimp only
      exact ⟨hNextPos, Nat.lt_succ_self _⟩
    · have hOldInv := hInv id p hOld
      rw [hSt1]
      dsimp only
      exact ⟨hOldInv.1, Nat.lt_trans hOldInv.2 (by omega)⟩
  have hNextNeCur : nextDh.handleId ≠ cur.handleId := by
    unfold lookupDir at hLd
    simp only [hCurPos, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hLd
    rcases hLd with ⟨p, hFind, _⟩
    have hEqId : p.1 = cur.handleId := by simpa using List.find?_some hFind
    have hLt := hNextGt p (List.mem_of_find?_eq_some hFind)
    omega
  let stMid := if isRoot then st1 else { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }
  let base0 := if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)
  have hMidOpen : stMid.openDirs = (nextDh.handleId, pos' ++ [s.val]) :: base0 := by
    cases isRoot
    · simp only [stMid, base0, Bool.false_eq_true, ↓reduceIte, hSt1, List.filter_cons,
        bne_iff_ne, ne_eq, hNextNeCur, not_false_eq_true]
    · simp only [stMid, base0, ↓reduceIte, hSt1]
  have hMidLt : ∀ p ∈ base0, p.1 < nextDh.handleId := by
    intro p hp
    cases isRoot
    · simp only [base0, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hp
      exact hNextGt p hp.1
    · simp only [base0, ↓reduceIte] at hp
      exact hNextGt p hp
  have hMidLd : lookupDir stMid nextDh = some (pos' ++ [s.val]) := by
    unfold lookupDir
    have hNZ : (nextDh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hNextPos)
    simp only [hNZ, Bool.false_eq_true, ↓reduceIte, hMidOpen, List.find?_cons, beq_self_eq_true]
    rfl
  refine ⟨hNextPos, by cases isRoot <;> simp [hSt1], by cases isRoot <;> simp [hSt1],
    by cases isRoot <;> simp [hSt1], by cases isRoot <;> simp [hSt1],
    by cases isRoot <;> simp [hSt1], hMidLd, ?_, hMidOpen, hMidLt, ?_⟩
  · intro hInv
    cases isRoot
    · exact dirHandleInvariant_filter st1 (hNextInv1 hInv) cur
    · exact hNextInv1 hInv
  · intro _
    rw [vfsDirOps_closeDir_def]
    have hCurAny : (st1.openDirs.any fun x => x.1 == cur.handleId) = true := by
      rw [hSt1]
      unfold lookupDir at hLd
      simp only [hCurPos, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hLd
      rcases hLd with ⟨p, hFind, _⟩
      exact List.any_eq_true.mpr ⟨p, List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hFind),
        by simpa using List.find?_some hFind⟩
    simp only [hCurPos, Bool.false_eq_true, ↓reduceIte, hCurAny]

/-- Base case equation for `walkDescendAuxM`. -/
theorem walkDescendAuxM_nil {α : Type} (ops : RawDirOpsM (StateM VfsState))
    (isRoot : Bool) (cur : DirHandle) (act : DirHandle → StateM VfsState (Except FsError α)) :
    Internal.walkDescendAuxM ops isRoot cur [] act =
      (if isRoot then act cur else Internal.bracketCloseDirM ops cur (act cur)) := by
  simp [Internal.walkDescendAuxM]

/-- Step equation for `walkDescendAuxM`. -/
theorem walkDescendAuxM_cons {α : Type} (ops : RawDirOpsM (StateM VfsState))
    (isRoot : Bool) (cur : DirHandle) (s : EntryName) (rest : List EntryName)
    (act : DirHandle → StateM VfsState (Except FsError α)) :
    Internal.walkDescendAuxM ops isRoot cur (s :: rest) act =
      (if isRoot then do
        let rNext ← ops.openDirAt cur s
        match rNext with
        | .error e => pure (.error e)
        | .ok nextDh => Internal.walkDescendAuxM ops false nextDh rest act
      else do
        let rNext ← Internal.bracketCloseDirM ops cur (ops.openDirAt cur s)
        match rNext with
        | .error e => pure (.error e)
        | .ok nextDh => Internal.walkDescendAuxM ops false nextDh rest act) :=
  rfl

private theorem state_bind_pure_eq {α β : Type} (x : StateM VfsState α) (f : α → StateM VfsState β) (st : VfsState) :
    (x >>= f) st = f (x st).1 (x st).2 := by
  cases hX : x st with
  | mk _ _ => simp [Bind.bind, StateT.bind, hX]

/-- Refusing an ancestor symlink in `walkDescendAuxM` yields `.invalidInput` and leaves `nodes`, `locks`, and `openDirs` clean. -/
theorem walkDescendAuxM_symlink_err {α : Type} (pre rest : List EntryName)
    (isRoot : Bool) (cur : DirHandle) (pos : List String) (st : VfsState)
    (t : String) (lm : Nat) (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st cur = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    ∃ e st', Internal.walkDescendAuxM vfsDirOps isRoot cur (pre ++ rest) act st = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧
      st'.openDirs = (if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)) := by
  induction pre generalizing isRoot cur pos st with
  | nil =>
    simp only [List.map_nil, List.append_nil] at hSym
    rcases hPosDir with ⟨dm, hDir, _⟩
    rw [hDir] at hSym
    cases hSym
  | cons s pre' ih =>
    simp only [List.cons_append, walkDescendAuxM_cons]
    rcases hPosDir with ⟨dm, hPosD, _, hPosX⟩
    cases pre' with
    | nil =>
      simp only [List.map_cons, List.map_nil] at hSym
      rcases vfsDirOps_openDirAt_symlink st cur s pos dm t lm hLd hPosD (by simp [hPosX]) hSym with
        ⟨e, hOpSym, hKind⟩
      cases isRoot
      · simp only [Bool.false_eq_true, ↓reduceIte, state_bind_pure_eq, bracketCloseDirM_run, hOpSym]
        rw [vfsDirOps_closeDir_def]
        cases hZ : (cur.handleId == 0) <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · cases hAny : (st.openDirs.any fun x => x.1 == cur.handleId)
          · exfalso
            have hSome := hLd
            unfold lookupDir at hSome
            simp only [hZ, Bool.false_eq_true, ↓reduceIte] at hSome
            cases hFind : st.openDirs.find? (fun p => p.1 == cur.handleId) with
            | none => rw [hFind] at hSome; cases hSome
            | some p =>
              have hpB : p.1 == cur.handleId :=
                List.find?_some (p := fun x : Nat × List String => x.1 == cur.handleId) hFind
              exact absurd (List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hFind, hpB⟩) (by rw [hAny]; decide)
          · exact ⟨e, _, rfl, hKind, rfl, rfl, rfl⟩
        · unfold lookupDir at hLd; simp [hZ] at hLd
      · simp only [↓reduceIte, state_bind_pure_eq, hOpSym]
        exact ⟨e, st, rfl, hKind, rfl, rfl, rfl⟩
    | cons s2 pre'' =>
      have hNextDir : ∃ dm1, nodeAt st.tree (pos ++ [s.val]) = some (.dir dm1) ∧ dm1 / 256 % 2 = 1 ∧ dm1 / 64 % 2 = 1 := by
        simpa [List.take] using hAnc 1 (by simp)
      rcases hNextDir with ⟨dm1, hChildDir, hRead1, hExec1⟩
      rcases vfsDirOps_openDirAt_dir_ok st cur s pos dm dm1 hLd hPosD hPosX hChildDir hRead1 with
        ⟨nextDh, st1, hOp⟩
      rcases lookupDir_open_close_step isRoot st st1 cur nextDh pos s hLd hOp with
        ⟨_, hMidTree, _, _, _, hMidLocks, hMidLd, _, hMidOpen, hMidLt, hCloseStep⟩
      let stMid := if isRoot then st1 else { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }
      have hMidNodes : stMid.nodes = st.nodes := by
        change vfsTreeNodes stMid.tree = vfsTreeNodes st.tree
        rw [hMidTree]
      have hStepEq :
          (if isRoot = true then
            (do
              let rNext ← vfsDirOps.openDirAt cur s
              match rNext with
              | Except.error e => pure (Except.error e)
              | Except.ok nextDh => Internal.walkDescendAuxM vfsDirOps false nextDh ((s2 :: pre'') ++ rest) act)
          else
            (do
              let rNext ← Internal.bracketCloseDirM vfsDirOps cur (vfsDirOps.openDirAt cur s)
              match rNext with
              | Except.error e => pure (Except.error e)
              | Except.ok nextDh => Internal.walkDescendAuxM vfsDirOps false nextDh ((s2 :: pre'') ++ rest) act)) st =
          Internal.walkDescendAuxM vfsDirOps false nextDh ((s2 :: pre'') ++ rest) act stMid := by
        cases isRoot
        · simp only [Bool.false_eq_true, ↓reduceIte, state_bind_pure_eq, bracketCloseDirM_run, hOp]
          rw [hCloseStep rfl]
          rfl
        · simp only [↓reduceIte, state_bind_pure_eq, hOp]
          rfl
      rw [hStepEq]
      have hMidPosDir : ∃ dm, nodeAt stMid.tree (pos ++ [s.val]) = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
        rw [hMidTree]; exact ⟨dm1, hChildDir, hRead1, hExec1⟩
      have hMidAnc : ∀ k < (s2 :: pre'').length,
          ∃ dm, nodeAt stMid.tree ((pos ++ [s.val]) ++ ((s2 :: pre'').take k).map (·.val)) = some (.dir dm) ∧
            dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
        intro k hk
        rw [hMidTree]
        simpa [List.take, List.append_assoc] using hAnc (k + 1) (by simp at hk ⊢; omega)
      have hMidSym : nodeAt stMid.tree ((pos ++ [s.val]) ++ (s2 :: pre'').map (·.val)) = some (.symlink t lm) := by
        rw [hMidTree]
        simpa [List.append_assoc] using hSym
      rcases ih false nextDh (pos ++ [s.val]) stMid hMidLd hMidPosDir hMidAnc hMidSym with
        ⟨e, stFinal, hRecEq, hKind, hNodesEq, hLocksEq, hOpenEq⟩
      refine ⟨e, stFinal, hRecEq, hKind, hNodesEq.trans hMidNodes, hLocksEq.trans hMidLocks, ?_⟩
      rw [hOpenEq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change List.filter (fun p => p.1 != nextDh.handleId) stMid.openDirs = _
      rw [hMidOpen, List.filter_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_eq_self]
      intro p hp
      simp only [bne_iff_ne, ne_eq]
      exact Nat.ne_of_lt (hMidLt p hp)

/-- Base case equation for `mkdirWalkM`. -/
theorem mkdirWalkM_nil (ops : RawDirOpsM (StateM VfsState))
    (isRoot : Bool) (cur : DirHandle) (act : DirHandle → StateM VfsState (Except FsError Unit)) :
    Internal.mkdirWalkM ops isRoot cur [] act =
      (if isRoot then act cur else Internal.bracketCloseDirM ops cur (act cur)) := by
  simp [Internal.mkdirWalkM]

/-- Step equation for `mkdirWalkM`. -/
theorem mkdirWalkM_cons (ops : RawDirOpsM (StateM VfsState))
    (isRoot : Bool) (cur : DirHandle) (s : EntryName) (rest : List EntryName)
    (act : DirHandle → StateM VfsState (Except FsError Unit)) :
    Internal.mkdirWalkM ops isRoot cur (s :: rest) act =
      (let step : StateM VfsState (Except FsError DirHandle) := do
        match ← ops.openDirAt cur s with
        | .ok nextDh => pure (.ok nextDh)
        | .error e =>
          if e.kind == .notFound then
            match ← ops.createDirAt cur s with
            | .ok () => ops.openDirAt cur s
            | .error ce =>
              if ce.kind == .alreadyExists then ops.openDirAt cur s else pure (.error ce)
          else pure (.error e)
      if isRoot then do
        let rNext ← step
        match rNext with
        | .error e => pure (.error e)
        | .ok nextDh => Internal.mkdirWalkM ops false nextDh rest act
      else do
        let rNext ← Internal.bracketCloseDirM ops cur step
        match rNext with
        | .error e => pure (.error e)
        | .ok nextDh => Internal.mkdirWalkM ops false nextDh rest act) :=
  rfl

/-- Refusing an ancestor symlink in `mkdirWalkM` yields `.invalidInput` and leaves `nodes`, `locks`, and `openDirs` clean. -/
theorem mkdirWalkM_symlink_err (pre tail : List EntryName)
    (hPreNe : pre ≠ []) (isRoot : Bool) (cur : DirHandle) (pos : List String) (st : VfsState)
    (t : String) (lm : Nat) (act : DirHandle → StateM VfsState (Except FsError Unit))
    (hLd : lookupDir st cur = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    ∃ e st', Internal.mkdirWalkM vfsDirOps isRoot cur (pre ++ tail) act st = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧
      st'.openDirs = (if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)) := by
  induction pre generalizing isRoot cur pos st with
  | nil => contradiction
  | cons s pre' ih =>
    simp only [List.cons_append, mkdirWalkM_cons]
    rcases hPosDir with ⟨dm, hPosD, _, hPosX⟩
    cases pre' with
    | nil =>
      simp only [List.map_cons, List.map_nil] at hSym
      rcases vfsDirOps_openDirAt_symlink st cur s pos dm t lm hLd hPosD (by simp [hPosX]) hSym with
        ⟨e, hOpSym, hKind⟩
      have hNeNotFound : (e.kind == .notFound) = false := by rw [hKind]; decide
      cases isRoot
      · simp only [Bool.false_eq_true, ↓reduceIte, state_bind_pure_eq, bracketCloseDirM_run, hOpSym, hNeNotFound]
        dsimp only [Pure.pure, StateT.pure]
        rw [vfsDirOps_closeDir_def]
        dsimp only
        have hCurPos : (cur.handleId == 0) = false := by
          unfold lookupDir at hLd
          cases hZ : cur.handleId == 0 <;> simp [hZ] at hLd ⊢
        have hCurAny : (st.openDirs.any fun x => x.1 == cur.handleId) = true := by
          unfold lookupDir at hLd
          simp only [hCurPos, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hLd
          rcases hLd with ⟨p, hFind, _⟩
          have hpB : p.1 == cur.handleId :=
            List.find?_some (p := fun x : Nat × List String => x.1 == cur.handleId) hFind
          exact List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hFind, hpB⟩
        rw [hCurPos, hCurAny]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨e, _, rfl, hKind, rfl, rfl, rfl⟩
      · simp only [↓reduceIte, state_bind_pure_eq, hOpSym, hNeNotFound]
        exact ⟨e, st, rfl, hKind, rfl, rfl, rfl⟩
    | cons s2 pre'' =>
      have hNextDir : ∃ dm1, nodeAt st.tree (pos ++ [s.val]) = some (.dir dm1) ∧ dm1 / 256 % 2 = 1 ∧ dm1 / 64 % 2 = 1 := by
        simpa [List.take] using hAnc 1 (by simp)
      rcases hNextDir with ⟨dm1, hChildDir, hRead1, hExec1⟩
      rcases vfsDirOps_openDirAt_dir_ok st cur s pos dm dm1 hLd hPosD hPosX hChildDir hRead1 with
        ⟨nextDh, st1, hOp⟩
      rcases lookupDir_open_close_step isRoot st st1 cur nextDh pos s hLd hOp with
        ⟨_, hMidTree, _, _, _, hMidLocks, hMidLd, _, hMidOpen, hMidLt, hCloseStep⟩
      let stMid := if isRoot then st1 else { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }
      have hMidNodes : stMid.nodes = st.nodes := by
        change vfsTreeNodes stMid.tree = vfsTreeNodes st.tree
        rw [hMidTree]
      have hStepEq :
          (let step := do
            match ← vfsDirOps.openDirAt cur s with
            | Except.ok nextDh => pure (Except.ok nextDh)
            | Except.error e =>
              if e.kind == FsErrorKind.notFound then
                match ← vfsDirOps.createDirAt cur s with
                | Except.ok () => vfsDirOps.openDirAt cur s
                | Except.error ce =>
                  if ce.kind == FsErrorKind.alreadyExists then vfsDirOps.openDirAt cur s else pure (Except.error ce)
              else pure (Except.error e)
          if isRoot = true then do
            let rNext ← step
            match rNext with
            | Except.error e => pure (Except.error e)
            | Except.ok nextDh => Internal.mkdirWalkM vfsDirOps false nextDh ((s2 :: pre'') ++ tail) act
          else do
            let rNext ← Internal.bracketCloseDirM vfsDirOps cur step
            match rNext with
            | Except.error e => pure (Except.error e)
            | Except.ok nextDh => Internal.mkdirWalkM vfsDirOps false nextDh ((s2 :: pre'') ++ tail) act) st =
          Internal.mkdirWalkM vfsDirOps false nextDh ((s2 :: pre'') ++ tail) act stMid := by
        cases isRoot
        · simp only [Bool.false_eq_true, ↓reduceIte, state_bind_pure_eq, bracketCloseDirM_run, hOp]
          dsimp only [Pure.pure, StateT.pure]
          rw [hCloseStep rfl]
          rfl
        · simp only [↓reduceIte, state_bind_pure_eq, hOp]
          rfl
      rw [hStepEq]
      have hMidPosDir : ∃ dm, nodeAt stMid.tree (pos ++ [s.val]) = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
        rw [hMidTree]; exact ⟨dm1, hChildDir, hRead1, hExec1⟩
      have hMidAnc : ∀ k < (s2 :: pre'').length,
          ∃ dm, nodeAt stMid.tree ((pos ++ [s.val]) ++ ((s2 :: pre'').take k).map (·.val)) = some (.dir dm) ∧
            dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
        intro k hk
        rw [hMidTree]
        simpa [List.take, List.append_assoc] using hAnc (k + 1) (by simp at hk ⊢; omega)
      have hMidSym : nodeAt stMid.tree ((pos ++ [s.val]) ++ (s2 :: pre'').map (·.val)) = some (.symlink t lm) := by
        rw [hMidTree]
        simpa [List.append_assoc] using hSym
      rcases ih (by simp) false nextDh (pos ++ [s.val]) stMid hMidLd hMidPosDir hMidAnc hMidSym with
        ⟨e, stFinal, hRecEq, hKind, hNodesEq, hLocksEq, hOpenEq⟩
      refine ⟨e, stFinal, hRecEq, hKind, hNodesEq.trans hMidNodes, hLocksEq.trans hMidLocks, ?_⟩
      rw [hOpenEq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change List.filter (fun p => p.1 != nextDh.handleId) stMid.openDirs = _
      rw [hMidOpen, List.filter_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_eq_self]
      intro p hp
      simp only [bne_iff_ne, ne_eq]
      exact Nat.ne_of_lt (hMidLt p hp)

/-- Descending through symlink-free directories via `walkDescendAuxM` resolves cleanly to `act leafDh` on a fresh handle. -/
theorem walkDescendAuxM_ok {α : Type} (segs : List EntryName)
    (isRoot : Bool) (cur : DirHandle) (pos : List String) (st : VfsState)
    (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st cur = some pos)
    (hInv : DirHandleInvariant st)
    (hFresh : isRoot = false → ∃ restOpen, st.openDirs = (cur.handleId, pos) :: restOpen ∧
      ∀ p ∈ restOpen, p.1 < cur.handleId)
    (hAnc : ∀ k < segs.length, ∃ dm, nodeAt st.tree (pos ++ (segs.take k).map (·.val)) = some (.dir dm) ∧
      (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1)
    (hLeaf : segs ≠ [] → ∃ dm, nodeAt st.tree (pos ++ segs.map (·.val)) = some (.dir dm) ∧ dm / 256 % 2 = 1) :
    (isRoot = true ∧ segs = [] → Internal.walkDescendAuxM vfsDirOps true cur [] act st = act cur st) ∧
    (segs ≠ [] ∨ isRoot = false →
      ∃ leafDh stMid baseOpen,
        leafDh.handleId > 0 ∧
        lookupDir stMid leafDh = some (pos ++ segs.map (·.val)) ∧
        stMid.tree = st.tree ∧ stMid.keys = st.keys ∧ stMid.cwd = st.cwd ∧
        stMid.nonce = st.nonce ∧ stMid.locks = st.locks ∧
        DirHandleInvariant stMid ∧
        baseOpen = (if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)) ∧
        (∀ p ∈ baseOpen, p.1 < leafDh.handleId) ∧
        stMid.openDirs = (leafDh.handleId, pos ++ segs.map (·.val)) :: baseOpen ∧
        Internal.walkDescendAuxM vfsDirOps isRoot cur segs act st = Internal.bracketCloseDirM vfsDirOps leafDh (act leafDh) stMid) := by
  induction segs generalizing isRoot cur pos st with
  | nil =>
    constructor
    · intro ⟨_, _⟩
      simp [walkDescendAuxM_nil]
    · intro hNot
      have hIsRootF : isRoot = false := by
        rcases hNot with hNe | rfl
        · contradiction
        · rfl
      subst hIsRootF
      rcases hFresh rfl with ⟨restOpen, hOpenEq, hLtCur⟩
      have hCurPos : 0 < cur.handleId := by
        have hMem : (cur.handleId, pos) ∈ st.openDirs := by rw [hOpenEq]; exact List.mem_cons_self
        exact (hInv cur.handleId pos hMem).1
      have hFilt : st.openDirs.filter (fun p => p.1 != cur.handleId) = restOpen := by
        rw [hOpenEq, List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        exact Nat.ne_of_lt (hLtCur p hp)
      refine ⟨cur, st, restOpen, hCurPos, by simpa using hLd, rfl, rfl, rfl, rfl, rfl, hInv, by simp [hFilt],
        hLtCur, by simpa using hOpenEq, ?_⟩
      simp [walkDescendAuxM_nil]
  | cons s rest ih =>
    constructor
    · intro ⟨_, hNil⟩; cases hNil
    · intro _
      simp only [walkDescendAuxM_cons]
      have hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ (0 < 0 → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1 := by
        simpa [List.take] using hAnc 0 (by simp)
      rcases hPosDir with ⟨dm, hPosD, _, hPosX⟩
      have hChildDir : ∃ dm1, nodeAt st.tree (pos ++ [s.val]) = some (.dir dm1) ∧ dm1 / 256 % 2 = 1 := by
        cases rest with
        | nil => exact hLeaf (by simp)
        | cons _ _ =>
          have h1 := hAnc 1 (by simp)
          simp only [List.take] at h1
          rcases h1 with ⟨dm1, hC, hR, _⟩
          exact ⟨dm1, hC, hR (by decide)⟩
      rcases hChildDir with ⟨dm1, hChildD, hRead1⟩
      rcases vfsDirOps_openDirAt_dir_ok st cur s pos dm dm1 hLd hPosD hPosX hChildD hRead1 with
        ⟨nextDh, st1, hOp⟩
      rcases lookupDir_open_close_step isRoot st st1 cur nextDh pos s hLd hOp with
        ⟨_, hMidTree, hMidKeys, hMidCwd, hMidNonce, hMidLocks, hMidLd, hMidInvFn, hMidOpen, hMidLt, hCloseStep⟩
      have hMidInv : DirHandleInvariant _ := hMidInvFn hInv
      let stMidStep := if isRoot then st1 else { st1 with openDirs := st1.openDirs.filter (fun p => p.1 != cur.handleId) }
      let base0 := if isRoot then st.openDirs else st.openDirs.filter (fun p => p.1 != cur.handleId)
      have hStepEq :
          (if isRoot = true then
            (do
              let rNext ← vfsDirOps.openDirAt cur s
              match rNext with
              | Except.error e => pure (Except.error e)
              | Except.ok nextDh => Internal.walkDescendAuxM vfsDirOps false nextDh rest act)
          else
            (do
              let rNext ← Internal.bracketCloseDirM vfsDirOps cur (vfsDirOps.openDirAt cur s)
              match rNext with
              | Except.error e => pure (Except.error e)
              | Except.ok nextDh => Internal.walkDescendAuxM vfsDirOps false nextDh rest act)) st =
          Internal.walkDescendAuxM vfsDirOps false nextDh rest act stMidStep := by
        cases isRoot
        · simp only [Bool.false_eq_true, ↓reduceIte, state_bind_pure_eq, bracketCloseDirM_run, hOp]
          rw [hCloseStep rfl]
          rfl
        · simp only [↓reduceIte, state_bind_pure_eq, hOp]
          rfl
      rw [hStepEq]
      have hRec := ih false nextDh (pos ++ [s.val]) stMidStep hMidLd hMidInv
        (fun _ => ⟨base0, hMidOpen, hMidLt⟩)
        (fun k hk => by
          rw [hMidTree]
          have hk0 := hAnc (k + 1) (by simp at hk ⊢; omega)
          simp only [List.take, List.map_cons] at hk0
          simp only [List.append_assoc, List.singleton_append]
          rcases hk0 with ⟨dm', hN', hR', hE'⟩
          exact ⟨dm', hN', fun _ => hR' (by omega), hE'⟩)
        (fun _ => by
          rw [hMidTree]
          simpa [List.append_assoc] using hLeaf (by simp))
      rcases hRec.2 (Or.inr rfl) with
        ⟨leafDh, stMid, baseOut, hLeafPos, hLeafLd, hT, hK, hC, hN, hL, hInvOut, hBaseEq, hLtOut, hOpenOut, hEqRun⟩
      have hBaseFilt : stMidStep.openDirs.filter (fun p => p.1 != nextDh.handleId) = base0 := by
        rw [hMidOpen, List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        exact Nat.ne_of_lt (hMidLt p hp)
      have hBaseOutEq : baseOut = base0 := by
        simp only [Bool.false_eq_true, ↓reduceIte, hBaseFilt] at hBaseEq
        exact hBaseEq
      subst hBaseOutEq
      refine ⟨leafDh, stMid, base0, hLeafPos, ?_, hT.trans hMidTree, hK.trans hMidKeys,
        hC.trans hMidCwd, hN.trans hMidNonce, hL.trans hMidLocks, hInvOut, rfl, hLtOut, ?_, hEqRun⟩
      · simpa [List.append_assoc] using hLeafLd
      · simpa [List.append_assoc] using hOpenOut

/-- Specialized `walkDescendM` success lemma from root handle `dh`. -/
theorem walkDescendM_ok {α : Type} (segs : List EntryName) (dh : DirHandle) (pos : List String)
    (st : VfsState) (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st dh = some pos)
    (hInv : DirHandleInvariant st)
    (hAnc : ∀ k < segs.length, ∃ dm, nodeAt st.tree (pos ++ (segs.take k).map (·.val)) = some (.dir dm) ∧
      (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1)
    (hLeaf : segs ≠ [] → ∃ dm, nodeAt st.tree (pos ++ segs.map (·.val)) = some (.dir dm) ∧ dm / 256 % 2 = 1) :
    (segs = [] → Internal.walkDescendM vfsDirOps dh [] act st = act dh st) ∧
    (segs ≠ [] →
      ∃ leafDh stMid,
        leafDh.handleId > 0 ∧
        lookupDir stMid leafDh = some (pos ++ segs.map (·.val)) ∧
        stMid.tree = st.tree ∧ stMid.keys = st.keys ∧ stMid.cwd = st.cwd ∧
        stMid.nonce = st.nonce ∧ stMid.locks = st.locks ∧
        DirHandleInvariant stMid ∧
        (∀ p ∈ st.openDirs, p.1 < leafDh.handleId) ∧
        stMid.openDirs = (leafDh.handleId, pos ++ segs.map (·.val)) :: st.openDirs ∧
        Internal.walkDescendM vfsDirOps dh segs act st = Internal.bracketCloseDirM vfsDirOps leafDh (act leafDh) stMid) := by
  have hAux := walkDescendAuxM_ok segs true dh pos st act hLd hInv (fun h => by cases h) hAnc hLeaf
  constructor
  · intro hNil
    subst hNil
    exact hAux.1 ⟨rfl, rfl⟩
  · intro hNe
    rcases hAux.2 (Or.inl hNe) with ⟨leafDh, stMid, baseOpen, hPos, hLL, hT, hK, hC, hN, hL, hInvM, hBase, hLt, hOp, hEq⟩
    simp only [↓reduceIte] at hBase
    subst hBase
    exact ⟨leafDh, stMid, hPos, hLL, hT, hK, hC, hN, hL, hInvM, hLt, hOp, hEq⟩

/-- Base case equation for `atomicWriteAtAuxM`. -/
theorem atomicWriteAtAuxM_zero (ops : RawDirOpsM (StateM VfsState))
    (parDh : DirHandle) (leaf : EntryName) (bytes : ByteArray) :
    Internal.atomicWriteAtAuxM ops parDh leaf bytes 0 =
      pure (.error { kind := .alreadyExists, path := some leaf.val, message := "temporary file name collision limit exceeded" }) := by
  simp [Internal.atomicWriteAtAuxM]

/-- Step equation for `atomicWriteAtAuxM`. -/
theorem atomicWriteAtAuxM_succ (ops : RawDirOpsM (StateM VfsState))
    (parDh : DirHandle) (leaf : EntryName) (bytes : ByteArray) (attempts : Nat) :
    Internal.atomicWriteAtAuxM ops parDh leaf bytes (attempts + 1) =
      (do
        let tmp ← ops.freshTempName
        match ← ops.createFileAt parDh tmp bytes with
        | .ok () =>
          match ← ops.renameAt parDh tmp parDh leaf with
          | .ok () => pure (.ok ())
          | .error e =>
            let _ ← ops.unlinkAt parDh tmp false
            pure (.error e)
        | .error e =>
          if e.kind == .alreadyExists && decide (attempts > 0) then
            Internal.atomicWriteAtAuxM ops parDh leaf bytes attempts
          else
            pure (.error e)) := by
  rfl

/-- `atomicWriteAtAuxM` succeeds in one step when `.t.<nonce>` is absent and `leaf` is not a directory. -/
theorem atomicWriteAtAuxM_ok_fresh (parDh : DirHandle) (parentPos : List String)
    (leaf : EntryName) (bytes : ByteArray) (attempts : Nat) (st : VfsState) (pm : Nat)
    (hLd : lookupDir st parDh = some parentPos)
    (hPar : nodeAt st.tree parentPos = some (.dir pm))
    (hW : pm / 128 % 2 = 1) (hX : pm / 64 % 2 = 1)
    (hTmpNone : nodeAt st.tree (parentPos ++ [".t." ++ toString st.nonce]) = none)
    (hLeafNotDir : match nodeAt st.tree (parentPos ++ [leaf.val]) with | some (.dir _) => False | _ => True) :
    match (Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes (attempts + 1) st) with
    | (res, st') =>
      res = .ok () ∧
      nodeAt st'.tree parentPos = some (.dir pm) ∧
      nodeAt st'.tree (parentPos ++ [leaf.val]) = some (.file bytes 420) ∧
      SameOutside (parentPos ++ [leaf.val]) st st' ∧
      st'.openDirs = st.openDirs := by
  rw [atomicWriteAtAuxM_succ]
  simp only [Bind.bind, Pure.pure, StateT.bind]
  cases hFr : vfsDirOps.freshTempName st with
  | mk tmp st1 =>
    have hFrDef := vfsDirOps_freshTempName_def st
    rw [hFr] at hFrDef
    dsimp only at hFrDef ⊢
    rcases hFrDef with ⟨hTmpVal, hSt1⟩
    have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
    have hTmpNone1 : nodeAt st1.tree (parentPos ++ [tmp.val]) = none := by
      rw [hSt1, hTmpVal]; exact hTmpNone
    have hPar1 : nodeAt st1.tree parentPos = some (.dir pm) := by rw [hSt1]; exact hPar
    have hLd1 : lookupDir st1 parDh = some parentPos := by rw [hSt1]; exact hLd
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
    have hNotPreSelf : ¬ (parentPos ++ [tmp.val] <+: parentPos) := by
      intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
    have hCf : vfsDirOps.createFileAt parDh tmp bytes st1 =
        (.ok (), { st1 with
          tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))
          keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }) := by
      rw [vfsDirOps_createFileAt_def, hLd1]
      dsimp only
      rw [hPar1]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpNone1]
    rw [hCf]
    dsimp only
    let st2 : VfsState :=
      { st1 with
        tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))
        keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }
    have hLd2 : lookupDir st2 parDh = some parentPos := hLd1
    have hDirGet1 : ∃ dm ch, vfsTreeGet st1.tree parentPos = some (.dir dm ch) := by rw [hSt1]; exact hDirGet
    have hPar2 : nodeAt st2.tree parentPos = some (.dir pm) := by
      change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))) parentPos = some (.dir pm)
      rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val _ parentPos hDirGet1 hNotPreSelf, hPar1]
    have hTmpFile2 : vfsTreeGet st2.tree (parentPos ++ [tmp.val]) = some (.file bytes 420) := by
      change vfsTreeGet (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))) (parentPos ++ [tmp.val]) =
        some (.file bytes 420)
      exact vfsTreeGet_vfsTreeSet_eq st1.tree parentPos tmp.val (some (.file bytes 420)) hDirGet1
    by_cases hSameName : parentPos ++ [tmp.val] = parentPos ++ [leaf.val]
    · have hBeqSame : ((parentPos ++ [tmp.val]) == (parentPos ++ [leaf.val])) = true := beq_iff_eq.mpr hSameName
      have hLeafEqTmp : tmp.val = leaf.val := by simpa using hSameName
      have hRen : vfsDirOps.renameAt parDh tmp parDh leaf st2 = (.ok (), st2) := by
        rw [vfsDirOps_renameAt_def, hLd2]
        dsimp only
        rw [hPar2]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpFile2, hBeqSame]
      simp only [StateT.bind]
      dsimp only [st2] at hRen
      rw [hRen]
      have hLeaf2 : nodeAt st2.tree (parentPos ++ [leaf.val]) = some (.file bytes 420) := by
        rw [← hLeafEqTmp]
        simpa [st2, vfsTreeTopNode] using
          nodeAt_vfsTreeSet_eq st1.tree parentPos tmp.val (some (.file bytes 420)) hDirGet1
      have hSame2 : SameOutside (parentPos ++ [leaf.val]) st st2 := by
        intro p hp
        change vfsTreeNodes st2.tree p = vfsTreeNodes st.tree p
        unfold vfsTreeNodes
        cases hCan : isCanonPath p
        · rfl
        · simp only [↓reduceIte]
          change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))) (vfsSplitSegs p) = _
          rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val (some (.file bytes 420)) (vfsSplitSegs p) hDirGet1
            (by rw [hLeafEqTmp]; exact hp), hSt1]
      exact ⟨rfl, hPar2, hLeaf2, hSame2, by simp [hSt1]⟩
    · have hBeqDiff : ((parentPos ++ [tmp.val]) == (parentPos ++ [leaf.val])) = false := beq_false_of_ne hSameName
      have hNotPrefDst : (parentPos ++ [tmp.val]).isPrefixOf parentPos = false := by
        rw [Bool.eq_false_iff]
        intro hP
        have hL := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hP)
        simp at hL
        omega
      have hDst2NotDir : ∀ dm, nodeAt st2.tree (parentPos ++ [leaf.val]) ≠ some (.dir dm) := by
        intro dm hEq
        have hNotPreTmpLeaf : ¬ (parentPos ++ [tmp.val] <+: parentPos ++ [leaf.val]) := by
          intro hP
          rcases hP with ⟨r, hr⟩
          cases r with
          | nil =>
            simp only [List.append_nil] at hr
            exact hSameName hr
          | cons _ _ =>
            have hL := congrArg List.length hr
            simp at hL
        have hOrigEq : nodeAt st2.tree (parentPos ++ [leaf.val]) = nodeAt st.tree (parentPos ++ [leaf.val]) := by
          change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420))) (parentPos ++ [leaf.val]) = _
          rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val _ (parentPos ++ [leaf.val]) hDirGet1 hNotPreTmpLeaf, hSt1]
        rw [hOrigEq] at hEq
        rw [hEq] at hLeafNotDir
        exact hLeafNotDir
      have hRen : vfsDirOps.renameAt parDh tmp parDh leaf st2 =
          (.ok (), { st2 with
            tree := vfsTreeSet (vfsTreeSet st2.tree (parentPos ++ [tmp.val]) none) (parentPos ++ [leaf.val]) (some (.file bytes 420))
            keys := pathOfSegs (parentPos ++ [leaf.val]) :: mRemapKeysAfterRename st2.keys (parentPos ++ [tmp.val]) (parentPos ++ [leaf.val]) }) := by
        rw [vfsDirOps_renameAt_def, hLd2]
        dsimp only
        rw [hPar2]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpFile2, hBeqDiff, hNotPrefDst]
        cases hDN : nodeAt st2.tree (parentPos ++ [leaf.val]) with
        | none => rfl
        | some dn =>
          cases dn with
          | dir dm => exact absurd hDN (hDst2NotDir dm)
          | file _ _ => rfl
          | symlink _ _ => rfl
      simp only [StateT.bind]
      dsimp only [st2] at hRen
      rw [hRen]
      let trTmpRm := vfsTreeSet st2.tree (parentPos ++ [tmp.val]) none
      have hDirGet2 : ∃ dm ch, vfsTreeGet st2.tree parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar2⟩
      have hParRm : nodeAt trTmpRm parentPos = some (.dir pm) := by
        rw [nodeAt_vfsTreeSet_outside st2.tree parentPos tmp.val none parentPos hDirGet2 hNotPreSelf, hPar2]
      have hDirGetRm : ∃ dm ch, vfsTreeGet trTmpRm parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hParRm⟩
      have hLeafFinal : nodeAt (vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 420))) (parentPos ++ [leaf.val]) =
          some (.file bytes 420) := by
        simpa [vfsTreeTopNode] using nodeAt_vfsTreeSet_eq trTmpRm parentPos leaf.val (some (.file bytes 420)) hDirGetRm
      have hSameFinal : SameOutside (parentPos ++ [leaf.val]) st
          { st2 with
            tree := vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 420))
            keys := pathOfSegs (parentPos ++ [leaf.val]) :: mRemapKeysAfterRename st2.keys (parentPos ++ [tmp.val]) (parentPos ++ [leaf.val]) } := by
        intro p hp
        change vfsTreeNodes (vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 420))) p =
          vfsTreeNodes st.tree p
        unfold vfsTreeNodes
        cases hCan : isCanonPath p
        · rfl
        · simp only [↓reduceIte]
          have hNotPreP : ¬ (parentPos ++ [leaf.val] <+: vfsSplitSegs p) := hp
          rw [nodeAt_vfsTreeSet_outside trTmpRm parentPos leaf.val _ (vfsSplitSegs p) hDirGetRm hNotPreP]
          change nodeAt (vfsTreeSet (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 420)))
            (parentPos ++ [tmp.val]) none) (vfsSplitSegs p) = nodeAt st.tree (vfsSplitSegs p)
          rw [nodeAt_vfsTreeSet_temp_roundtrip st1.tree parentPos tmp.val (.file bytes 420) hDirGet1 hTmpNone1, hSt1]
      have hNotPreLeafSelf : ¬ (parentPos ++ [leaf.val] <+: parentPos) := by
        intro hP; have hL := List.IsPrefix.length_le hP; simp at hL; omega
      have hParFinal : nodeAt (vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 420))) parentPos =
          some (.dir pm) := by
        rw [nodeAt_vfsTreeSet_outside trTmpRm parentPos leaf.val _ parentPos hDirGetRm hNotPreLeafSelf, hParRm]
      exact ⟨rfl, hParFinal, hLeafFinal, hSameFinal, by simp [hSt1]⟩

end LeanSwe.Fs.Proofs
