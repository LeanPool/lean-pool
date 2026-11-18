/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Reservation
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card


/-!
# FALLBACK establishes INV-S (Lemma 3.3)

FALLBACK reads only the element list. It cuts the list into groups and chunks with evenly spaced
labels (`fbLayout`) and rebuilds the top structure, whose tags `relabelAll` checks along the
chunk list (renumbering if they do not increase). The result satisfies INV-S with the same
element list, and the element records keep their links, liveness and handles.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Cutting a list into pieces -/

theorem chunksOf_flatten {α : Type} (n : Nat) (l : List α) : (chunksOf n l).flatten = l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
    cases l with
    | nil => simp only [chunksOf, List.flatten_nil]
    | cons x xs =>
      rw [chunksOf]
      simp only [List.flatten_cons]
      rw [ih _ (by
        simp only [List.length_drop, ← h, List.length_cons]
        exact Nat.sub_lt (by omega) (by omega)) _ rfl]
      exact List.take_append_drop _ _

theorem chunksOf_ne_nil {α : Type} (n : Nat) (l : List α) :
    ∀ p ∈ chunksOf n l, p ≠ [] := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
    cases l with
    | nil => simp only [chunksOf, List.not_mem_nil, ne_eq, IsEmpty.forall_iff, implies_true]
    | cons x xs =>
      rw [chunksOf]
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [ne_eq, List.take_eq_nil_iff, Nat.max_eq_zero_iff, Nat.succ_ne_self, and_false,
          reduceCtorEq, or_self, not_false_eq_true]
      · exact ih _ (by
        simp only [List.length_drop, ← h, List.length_cons]
        exact Nat.sub_lt (by omega) (by omega)) _ rfl p hp

/-- The pieces, in closed form. -/
theorem chunksOf_getD {α : Type} (n : Nat) (l : List α) (c : Nat) :
    (chunksOf n l).getD c [] = (l.drop (c * max n 1)).take (max n 1) := by
  induction h : l.length using Nat.strong_induction_on generalizing l c with
  | _ k ih =>
    cases l with
    | nil => simp only [chunksOf, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
        not_false_eq_true, getElem?_neg, Option.getD_none, List.drop_nil,
        List.take_nil]
    | cons x xs =>
      rw [chunksOf]
      cases c with
      | zero => simp only [List.getD_eq_getElem?_getD, List.length_cons, Nat.zero_lt_succ,
          getElem?_pos, List.getElem_cons_zero, Option.getD_some, Nat.zero_mul,
          List.drop_zero]
      | succ c =>
        simp only [List.getD_cons_succ]
        rw [ih _ (by
        simp only [List.length_drop, ← h, List.length_cons]
        exact Nat.sub_lt (by omega) (by omega)) _ c rfl, List.drop_drop]
        congr 2
        rw [Nat.succ_mul]; omega

theorem chunksOf_length {α : Type} (n : Nat) (l : List α) :
    (chunksOf n l).length = (l.length + max n 1 - 1) / max n 1 := by
  have hm : 1 ≤ max n 1 := Nat.le_max_right _ _
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
    cases l with
    | nil =>
      simp only [List.length_nil] at h; subst h
      simp only [chunksOf, List.length_nil, Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega)).symm
    | cons x xs =>
      rw [chunksOf]
      simp only [List.length_cons]
      rw [ih _ (by
        simp only [List.length_drop, ← h, List.length_cons]
        exact Nat.sub_lt (by omega) (by omega)) _ rfl]
      simp only [List.length_drop, List.length_cons] at h ⊢
      rw [← h]
      generalize max n 1 = m at hm ⊢
      by_cases hk : xs.length + 1 ≤ m
      · have : xs.length + 1 - m = 0 := by omega
        rw [this, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
        have h1 : m ≤ xs.length + 1 + m - 1 := by omega
        have h2 : xs.length + 1 + m - 1 < 2 * m := by omega
        have : (xs.length + 1 + m - 1) / m = 1 := by
          apply Nat.le_antisymm
          · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        rw [this]
      · have e : xs.length + 1 + m - 1 = (xs.length + 1 - m + m - 1) + m := by omega
        rw [e, Nat.add_div_right _ (by omega)]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Relabelling the elements -/

/-- The element updates for one group (the `k`-th, numbered `n + 1`). -/
def assignGroup (P : Params) (n : Nat) (g : List Nat) (E : Array Elem) : Array Elem :=
  g.zipIdx.foldl (fun E q =>
    E.modify q.1 fun e => { e with grp := n + 1, lab := (q.2 + 1) * ((1 <<< P.elementBits) /
      (g.length +
      1)) }) E

/-- Assign consecutive fallback group indices and labels to a partition of the elements. -/
def fbE (P : Params) : Nat → List (List Nat) → Array Elem → Array Elem
  | _, [], E => E
  | n, g :: gs, E => fbE P (n + 1) gs (assignGroup P n g E)

theorem fbE_eq_aux (P : Params) (gl : List (List Nat)) (n : Nat) (E : Array Elem) :
    (gl.zipIdx n).foldl (fun E p =>
      let step := (1 <<< P.elementBits) / (p.1.length + 1)
      p.1.zipIdx.foldl (fun E q =>
        E.modify q.1 fun e => { e with grp := p.2 + 1, lab := (q.2 + 1) * step }) E) E =
      fbE P n gl E := by
  induction gl generalizing n E with
  | nil => rfl
  | cons g gs ih => simp only [List.zipIdx_cons, List.foldl_cons]; rw [ih]; rfl

theorem fbElems_eq (P : Params) (gl : List (List Nat)) (E : Array Elem) :
    fbElems P gl E = fbE P 0 gl E := fbE_eq_aux P gl 0 E

/-- A fold of modifications at the members of `l` (one at each, in order). -/
theorem foldl_zipIdx_modify {α : Type} [Inhabited α] (l : List Nat) (f : Nat → α → α) (E : Array
  α) (n : Nat)
    (hnd : l.Nodup) (e : Nat) :
    ((l.zipIdx n).foldl (fun E q => E.modify q.1 (f q.2)) E).getX e =
      if e ∈ l ∧ e < E.size then f (n + l.idxOf e) (E.getX e) else E.getX e := by
  induction l generalizing n E with
  | nil => simp only [List.zipIdx_nil, List.foldl_nil, List.not_mem_nil, false_and, ↓reduceIte]
  | cons a t ih =>
    simp only [List.zipIdx_cons, List.foldl_cons]
    simp only [List.nodup_cons] at hnd
    rw [ih _ _ hnd.2]
    simp only [Array.size_modify', Array.getX_modify, List.mem_cons]
    by_cases hea : e = a
    · subst hea; simp only [hnd.1, false_and, ↓reduceIte, true_and, or_false,
        List.idxOf_cons_self, Nat.add_zero]
    · have : a ≠ e := Ne.symm hea
      by_cases het : e ∈ t
      · simp only [hea, het, this,  true_and, false_and, ite_false,
          List.idxOf_cons_ne _ this, or_true]
        rw [show n + 1 + List.idxOf e t = n + (List.idxOf e t).succ by omega]
      · simp only [het, false_and, ↓reduceIte, this, hea, or_self]

theorem foldl_zipIdx_modify_size {α : Type} (l : List Nat) (f : Nat → α → α) (E : Array α) (n :
  Nat) :
    ((l.zipIdx n).foldl (fun E q => E.modify q.1 (f q.2)) E).size = E.size := by
  induction l generalizing n E with
  | nil => rfl
  | cons a t ih => simp only [List.zipIdx_cons, List.foldl_cons]; rw [ih]; simp only [
      Array.size_modify]

theorem assignGroup_getX (P : Params) (n : Nat) (g : List Nat) (E : Array Elem) (hnd : g.Nodup)
    (e : Nat) :
    (assignGroup P n g E).getX e =
      if e ∈ g ∧ e < E.size then
        { E.getX e with grp := n + 1, lab := (g.idxOf e + 1) * ((1 <<< P.elementBits) /
          (g.length + 1)) }
      else E.getX e := by
  unfold assignGroup
  have := foldl_zipIdx_modify g
    (fun i e => { e with grp := n + 1, lab := (i + 1) * ((1 <<< P.elementBits) / (g.length +
      1)) }) E 0
      hnd e
  simpa using this

theorem assignGroup_size (P : Params) (n : Nat) (g : List Nat) (E : Array Elem) :
    (assignGroup P n g E).size = E.size := by
  unfold assignGroup
  exact foldl_zipIdx_modify_size g
    (fun i e => { e with grp := n + 1, lab := (i + 1) * ((1 <<< P.elementBits) / (g.length +
      1)) }) E 0

theorem fbE_size (P : Params) (gl : List (List Nat)) (n : Nat) (E : Array Elem) :
    (fbE P n gl E).size = E.size := by
  induction gl generalizing n E with
  | nil => rfl
  | cons g gs ih => simp only [fbE]; rw [ih, assignGroup_size]

/-- `fbE` changes only `grp` and `lab`. -/
theorem fbE_other (P : Params) (gl : List (List Nat)) (n : Nat) (E : Array Elem)
    (hnd : gl.flatten.Nodup) (e : Nat) :
    ((fbE P n gl E).getX e).next = (E.getX e).next ∧ ((fbE P n gl E).getX e).prev = (E.getX
      e).prev ∧
    ((fbE P n gl E).getX e).live = (E.getX e).live ∧ ((fbE P n gl E).getX e).h = (E.getX e).h := by
  induction gl generalizing n E with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons g gs ih =>
    simp only [fbE]
    simp only [List.flatten_cons] at hnd
    obtain ⟨h1, h2, h3, h4⟩ := ih (n + 1) (assignGroup P n g E) (List.nodup_append.mp hnd).2.1
    rw [h1, h2, h3, h4, assignGroup_getX P n g E (List.nodup_append.mp hnd).1]
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `fbE` leaves elements outside the groups alone. -/
theorem fbE_out (P : Params) (gl : List (List Nat)) (n : Nat) (E : Array Elem)
    (hnd : gl.flatten.Nodup) {e : Nat} (he : e ∉ gl.flatten) : (fbE P n gl E).getX e = E.getX e
      := by
  induction gl generalizing n E with
  | nil => rfl
  | cons g gs ih =>
    simp only [fbE]
    simp only [List.flatten_cons, List.mem_append, not_or] at hnd he
    rw [ih _ _ (List.nodup_append.mp hnd).2.1 he.2,
      assignGroup_getX P n g E (List.nodup_append.mp hnd).1]
    simp only [he.1, false_and, ↓reduceIte]

/-- The element `e` of the `k`-th group gets group `n + k + 1` and label `(i + 1)·step`. -/
theorem fbE_in (P : Params) (gl : List (List Nat)) (n : Nat) (E : Array Elem)
    (hnd : gl.flatten.Nodup) (hsz : ∀ e ∈ gl.flatten, e < E.size) {k : Nat} (hk : k < gl.length)
    {e : Nat} (he : e ∈ gl[k]) :
    ((fbE P n gl E).getX e).grp = n + k + 1 ∧
    ((fbE P n gl E).getX e).lab = (gl[k].idxOf e + 1) * ((1 <<< P.elementBits) / (gl[k].length
      + 1)) := by
  induction gl generalizing n E k with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons g gs ih =>
    simp only [fbE]
    simp only [List.flatten_cons] at hnd hsz
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at he ⊢
      have hgs : e ∉ gs.flatten := fun h => (List.nodup_append.mp hnd).2.2 e he e h rfl
      rw [fbE_out P gs (n + 1) _ (List.nodup_append.mp hnd).2.1 hgs,
        assignGroup_getX P n g E (List.nodup_append.mp hnd).1]
      have hes := hsz e (List.mem_append_left _ he)
      simp only [he, hes, and_self, ↓reduceIte, Nat.add_zero]
    | succ k =>
      simp only [List.getElem_cons_succ] at he ⊢
      have hk' : k < gs.length := by simpa using hk
      obtain ⟨h1, h2⟩ := ih (n + 1) (assignGroup P n g E) (List.nodup_append.mp hnd).2.1
        (fun e he => by rw [assignGroup_size]; exact hsz e (List.mem_append_right _ he)) hk' he
      exact ⟨by rw [h1]; omega, h2⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Consecutive indices -/

theorem getX_listArray {α : Type} [Inhabited α] (f : Nat → α) (m z : Nat) :
    (default :: (List.range m).map f).toArray.getX z =
      if z = 0 then default else if z ≤ m then f (z - 1) else default := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rcases z with _ | z
  · simp only [List.length_cons, List.length_map, List.length_range, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_zero, Option.getD_some, ↓reduceIte]
  · simp only [List.getElem?_cons_succ, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hz : z < m
    · simp only [List.length_map, List.length_range, hz, getElem?_pos, List.getElem_map,
        List.getElem_range, Option.getD_some, show z + 1 ≤ m by omega, ↓reduceIte]
    · simp only [List.length_map, List.length_range, hz, not_false_eq_true, getElem?_neg,
        Option.getD_none, show ¬z + 1 ≤ m by omega, ↓reduceIte]

theorem size_listArray {α : Type} (d : α) (f : Nat → α) (m : Nat) :
    (d :: (List.range m).map f).toArray.size = m + 1 := by
      simp only [List.size_toArray, List.length_cons, List.length_map, List.length_range]

theorem succOf_range' (a n z : Nat) (hz : z ∈ List.range' a n) :
    succOf (List.range' a n) z = if z + 1 < a + n then z + 1 else NIL := by
  induction n generalizing a with
  | zero => simp only [List.range'_zero, List.not_mem_nil] at hz
  | succ n ih =>
    rw [List.range'_succ, succOf_cons']
    by_cases hza : z = a
    · subst hza
      cases n with
      | zero => simp only [↓reduceIte, List.range'_zero, List.headD_eq_head?_getD,
          List.head?_nil, Option.getD_none, Nat.zero_add, lt_self_iff_false]
      | succ n => simp only [↓reduceIte, List.range'_succ, List.headD_eq_head?_getD,
          List.head?_cons, Option.getD_some, Nat.add_lt_add_iff_left,
          Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
    · rw [ite_eq_right hza]
      have hz' : z ∈ List.range' (a + 1) n := by
        rw [List.range'_succ] at hz
        simp only [List.mem_cons, List.mem_range'_1] at hz
        simp only [List.mem_range'_1] at hz ⊢
        omega
      rw [ih (a + 1) hz']
      congr 1; simp only [eq_iff_iff]; omega

theorem predOf_range' (a n z : Nat) (hz : z ∈ List.range' a n) (ha : 1 ≤ a) :
    predOf (List.range' a n) z = if z = a then NIL else z - 1 := by
  induction n generalizing a with
  | zero => simp only [List.range'_zero, List.not_mem_nil] at hz
  | succ n ih =>
    rw [List.range'_succ]
    have hnd : (a :: List.range' (a + 1) n).Nodup := by
      rw [← List.range'_succ]; exact List.nodup_range'
    rw [predOf_cons hnd]
    by_cases hza : z = a
    · subst hza
      have : z ∉ List.range' (z + 1) n := by
        simp only [List.mem_range'_1, not_and, not_lt, isEmpty_Prop, not_le, Nat.lt_add_one,
          IsEmpty.forall_iff]
      simp only [this, ↓reduceIte]
    · have hz' : z ∈ List.range' (a + 1) n := by
        rw [List.range'_succ] at hz
        simp only [List.mem_cons, List.mem_range'_1] at hz
        simp only [List.mem_range'_1] at hz ⊢
        omega
      rw [ite_eq_left hz', ite_eq_right hza]
      by_cases hz1 : z = a + 1
      · subst hz1; cases n with
        | zero => simp only [List.range'_zero, List.not_mem_nil] at hz'
        | succ n => simp only [List.range'_succ, List.head?_cons, ↓reduceIte,
            Nat.add_one_sub_one]
      · have : (List.range' (a + 1) n).head? ≠ some z := by
          cases n with
          | zero => simp only [List.range'_zero, List.head?_nil, ne_eq, reduceCtorEq,
              not_false_eq_true]
          | succ n => simp only [List.range'_succ, List.head?_cons, ne_eq, Option.some.injEq]; omega
        rw [ite_eq_right this, ih (a + 1) hz' (by omega), ite_eq_right hz1]

theorem llist_range' {nxt prv : Nat → Nat} {a n : Nat} (ha : 1 ≤ a) (hn : 1 ≤ n)
    (hnx : ∀ z ∈ List.range' a n, nxt z = if z + 1 < a + n then z + 1 else NIL)
    (hpv : ∀ z ∈ List.range' a n, prv z = if z = a then NIL else z - 1) :
    LList nxt prv a (List.range' a n) := by
  refine ⟨List.nodup_range', ?_, ?_, ?_, ?_⟩
  · simp only [NIL, List.mem_range'_1, Nat.le_zero_eq, not_and, not_lt, Nat.add_eq_zero_iff]; omega
  · cases n with
    | zero => omega
    | succ n => simp only [List.range'_succ, List.headD_eq_head?_getD, List.head?_cons,
        Option.getD_some]
  · intro z hz; rw [hnx z hz, succOf_range' a n z hz]
  · intro z hz; rw [hpv z hz, predOf_range' a n z hz ha]

/-- Blocks of `gpc` consecutive indices, the last one shorter, cover `1 .. m`. -/
theorem flatMap_blocks (gpc m : Nat) (hg : 1 ≤ gpc) (nc : Nat) :
    (List.range nc).flatMap (fun c => List.range' (c * gpc + 1) (min gpc (m - c * gpc))) =
      List.range' 1 (min m (nc * gpc)) := by
  induction nc with
  | zero => simp only [List.range_zero, List.flatMap_nil, Nat.zero_mul, Nat.zero_le,
      Nat.min_eq_right, List.range'_zero]
  | succ nc ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hm : m ≤ nc * gpc
    · have : m - nc * gpc = 0 := by omega
      rw [this, Nat.min_zero, List.range'_zero, List.append_nil]
      congr 1; rw [Nat.succ_mul]; omega
    · have e1 : min m (nc * gpc) = nc * gpc := by omega
      rw [e1, show nc * gpc + 1 = 1 + nc * gpc by omega, List.range'_append_1]
      congr 1; rw [Nat.succ_mul]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### INV-S without the tag condition -/

/-- The linked-list and allocation part of the core invariant before restoring labels. -/
structure INV0 (s : Core) (A : Abs) : Prop where
  eList : LList (eN s) (eP s) s.head A.elist
  eAlloc : ∀ e, e ∈ A.elist ↔ 1 ≤ e ∧ e < s.E.size
  tail : s.tail = A.elist.getLastD NIL
  gList : LList (gN s) (gP s) s.firstGroup A.glist
  gAlloc : ∀ g ∈ A.glist, g < s.Gs.size
  gPos : 1 ≤ s.Gs.size
  gAlive : ∀ g, 1 ≤ g → g < s.Gs.size → (gA s g = true ↔ g ∈ A.glist)
  gOut : ∀ g, g ∉ A.glist → gN s g = NIL ∧ gP s g = NIL
  free : ∀ g ∈ s.freeG, 1 ≤ g ∧ g < s.Gs.size ∧ g ∉ A.glist
  freeNodup : s.freeG.Nodup
  cList : LList (cN s) (cP s) s.firstChunk A.chunks
  cAlloc : ∀ c, c ∈ A.chunks ↔ 1 ≤ c ∧ c < s.C.size
  cOut : ∀ c, c ∉ A.chunks → cN s c = NIL ∧ cP s c = NIL ∧ cF s c = NIL
  gEnds : ∀ g ∈ A.glist, Ends (gF s g) (gLs s g) (A.elts g)
  cEnds : ∀ c ∈ A.chunks, Ends (cF s c) (cLs s c) (A.grps c)
  grp : ∀ g ∈ A.glist, ∀ e ∈ A.elts g, eG s e = g
  chk : ∀ c ∈ A.chunks, ∀ g ∈ A.grps c, gC s g = c
  eSorted : ∀ g ∈ A.glist, ((A.elts g).map (eL s)).IsChain (· < ·)
  gSorted : ∀ c ∈ A.chunks, ((A.grps c).map (gL s)).IsChain (· < ·)

theorem INV0.toINV {s : Core} {A : Abs} (h : INV0 s A)
    (hs : (A.chunks.map (cT s)).IsChain (· < ·)) : INV s A :=
  ⟨h.eList, h.eAlloc, h.tail, h.gList, h.gAlloc, h.gPos, h.gAlive, h.gOut, h.free, h.freeNodup,
   h.cList, h.cAlloc, h.cOut, h.gEnds, h.cEnds, h.grp, h.chk, h.eSorted, h.gSorted, hs⟩

theorem INV0.of_sameLinks {s s' : Core} {A : Abs} (h : INV0 s A) (hs : SameLinks s s') :
    INV0 s' A := by
  -- reuse INV's transfer with an arbitrary sorted tag function
  have e1 : eN s' = eN s := funext hs.eN
  have e2 : eP s' = eP s := funext hs.eP
  have e3 : gN s' = gN s := funext hs.gN
  have e4 : gP s' = gP s := funext hs.gP
  have e5 : cN s' = cN s := funext hs.cN
  have e6 : cP s' = cP s := funext hs.cP
  have e8 : eL s' = eL s := funext hs.eL
  have e9 : gL s' = gL s := funext hs.gL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2, hs.head]; exact h.eList
  · rw [hs.Esize]; exact h.eAlloc
  · rw [hs.tail]; exact h.tail
  · rw [e3, e4, hs.firstGroup]; exact h.gList
  · rw [hs.Gsize]; exact h.gAlloc
  · rw [hs.Gsize]; exact h.gPos
  · intro g; rw [hs.gA, hs.Gsize]; exact h.gAlive g
  · intro g; rw [e3, e4]; exact h.gOut g
  · rw [hs.freeG, hs.Gsize]; exact h.free
  · rw [hs.freeG]; exact h.freeNodup
  · rw [e5, e6, hs.firstChunk]; exact h.cList
  · rw [hs.Csize]; exact h.cAlloc
  · intro c hc; rw [e5, e6, hs.cF]; exact h.cOut c hc
  · intro g hg; rw [hs.gF, hs.gLs]; exact h.gEnds g hg
  · intro c hc; rw [hs.cF, hs.cLs]; exact h.cEnds c hc
  · intro g hg e he; rw [hs.eG]; exact h.grp g hg e he
  · intro c hc g hg; rw [hs.gC]; exact h.chk c hc g hg
  · rw [e8]; exact h.eSorted
  · rw [e9]; exact h.gSorted

instance : IsPre SameLinks where
  refl := SameLinks.refl
  trans _ _ _ h1 h2 := h1.trans h2

/-! ### The element list part, which FALLBACK reads -/

/-- The element-list, allocation and endpoint invariants needed by a fallback rebuild. -/
structure ElemOK (s : Core) (l : List Nat) : Prop where
  eList : LList (eN s) (eP s) s.head l
  eAlloc : ∀ e, e ∈ l ↔ 1 ≤ e ∧ e < s.E.size
  tail : s.tail = l.getLastD NIL
  ne : l ≠ []

theorem INV.elemOK {s : Core} {A : Abs} (h : INV s A) (hne : A.elist ≠ []) : ElemOK s A.elist :=
  ⟨h.eList, h.eAlloc, h.tail, hne⟩

theorem ElemOK.of_eframe {s s' : Core} {l : List Nat} (h : ElemOK s l) (hf : EFrame s s') :
    ElemOK s' l := by
  refine ⟨?_, ?_, ?_, h.ne⟩
  · rw [show eN s' = eN s from funext hf.next, show eP s' = eP s from funext hf.prev, hf.head]
    exact h.eList
  · rw [hf.size]; exact h.eAlloc
  · rw [hf.tail]; exact h.tail

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Arithmetic of the layout -/

theorem fbGS_pos (P : Params) : 1 ≤ fbGS P := by unfold fbGS; exact Nat.le_max_left _ _
theorem fbGPC_pos (P : Params) : 1 ≤ fbGPC P := by unfold fbGPC; exact Nat.le_max_left _ _

theorem fbNC_mul (P : Params) (m : Nat) : m ≤ fbNC P m * fbGPC P := by
  have hg := fbGPC_pos P
  unfold fbNC
  generalize fbGPC P = g at hg ⊢
  have := Nat.div_add_mod (m + g - 1) g
  have := Nat.mod_lt (m + g - 1) (by omega : g > 0)
  rw [Nat.mul_comm]; omega

theorem lt_fbNC (P : Params) {m c : Nat} (hc : c < fbNC P m) : c * fbGPC P < m := by
  have hg := fbGPC_pos P
  unfold fbNC at hc
  generalize fbGPC P = g at hg hc ⊢
  have h := (Nat.lt_div_iff_mul_lt (by omega)).mp hc
  omega

theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun k => l.getD k d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getD_eq_getElem?_getD, List.getElem_map, List.getElem_range,
      List.getElem?_eq_getElem h2, Option.getD_some]

theorem range'_headD (a n : Nat) (hn : 1 ≤ n) : (List.range' a n).headD NIL = a := by
  cases n with
  | zero => omega
  | succ n => simp only [List.range'_succ, List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some]

theorem range'_getLastD (a n : Nat) (hn : 1 ≤ n) : (List.range' a n).getLastD NIL = a + n - 1 := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp only [Nat.zero_add, List.range'_one, List.getLastD_eq_getLast?,
        List.getLast?_singleton, Option.getD_some, Nat.add_one_sub_one]
    | succ n =>
      rw [List.range'_succ,
        show a :: List.range' (a + 1) (n + 1) = [a] ++ List.range' (a + 1) (n + 1)
        by rfl, show List.range' (a + 1) (n + 1) = (a + 1) :: List.range' (a + 2) n by
          simp only [List.range'_succ], getLastD_append_cons, ← show List.range' (a + 1) (n + 1) =
          (a + 1) :: List.range' (a + 2) n by simp only [List.range'_succ], ih (a + 1) (by omega)]
      omega

theorem isChain_range_mul (n : Nat) {st : Nat} (hst : 1 ≤ st) :
    ((List.range n).map fun i => (i + 1) * st).IsChain (· < ·) := by
  rw [List.isChain_map, List.isChain_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  exact Nat.mul_lt_mul_of_pos_right (by omega) hst

/-- Evenly spaced labels along a list without duplicates increase. -/
theorem isChain_spaced {r : List Nat} (hnd : r.Nodup) {st : Nat} (hst : 1 ≤ st) :
    (r.map fun e => (r.idxOf e + 1) * st).IsChain (· < ·) := by
  have : r.map (fun e => (r.idxOf e + 1) * st) = (List.range r.length).map (fun i => (i + 1) *
    st) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.Nodup.idxOf_getElem hnd i (by simpa using h1)]
  rw [this, List.isChain_map, List.isChain_iff_pairwise]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  exact Nat.mul_lt_mul_of_pos_right (by omega) hst

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The abstract nesting of FALLBACK's layout of `l`. -/
def fbAbs (P : Params) (l : List Nat) : Abs :=
  let groups := chunksOf (fbGS P) l
  let m := groups.length
  { chunks := List.range' 1 (fbNC P m)
    grps := fun c => if 1 ≤ c ∧ c ≤ fbNC P m then
        List.range' ((c - 1) * fbGPC P + 1) (fbChunkLen P m (c - 1)) else []
    elts := fun g => if 1 ≤ g ∧ g ≤ m then groups.getD (g - 1) [] else [] }

theorem fbAbs_glist (P : Params) (l : List Nat) :
    (fbAbs P l).glist = List.range' 1 (chunksOf (fbGS P) l).length := by
  unfold Abs.glist fbAbs
  simp only
  generalize (chunksOf (fbGS P) l).length = m
  rw [List.range'_eq_map_range, List.flatMap_map]
  have : (List.range (fbNC P m)).flatMap (fun c =>
      if 1 ≤ 1 + c ∧ 1 + c ≤ fbNC P m then
        List.range' ((1 + c - 1) * fbGPC P + 1) (fbChunkLen P m (1 + c - 1)) else []) =
      (List.range (fbNC P m)).flatMap (fun c =>
        List.range' (c * fbGPC P + 1) (min (fbGPC P) (m - c * fbGPC P))) := by
    refine List.flatMap_congr fun c hc => ?_
    simp only [List.mem_range] at hc
    rw [ite_eq_left ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, fbChunkLen]
  rw [this, flatMap_blocks _ _ (fbGPC_pos P), Nat.min_eq_left (fbNC_mul P m)]

theorem fbAbs_elist (P : Params) (l : List Nat) : (fbAbs P l).elist = l := by
  unfold Abs.elist
  rw [fbAbs_glist]
  conv_rhs => rw [← chunksOf_flatten (fbGS P) l]
  generalize hg : chunksOf (fbGS P) l = groups
  unfold fbAbs
  simp only [hg]
  rw [List.range'_eq_map_range, List.flatMap_map]
  conv_rhs => rw [← map_getD_range groups []]
  rw [List.flatMap_def]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  simp only [List.mem_range] at hk
  rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Label widths fit FALLBACK's spacing (`docs/PROOF.md` §3.4): every gap is at least 1. -/
def FbOK (P : Params) : Prop := fbGS P < 1 <<< P.elementBits ∧ fbGPC P < 1 <<< P.groupBits

theorem chunksOf_mem_length {α : Type} (n : Nat) (l : List α) :
    ∀ p ∈ chunksOf n l, p.length ≤ max n 1 := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
    cases l with
    | nil => simp only [chunksOf, List.not_mem_nil, le_max_iff, IsEmpty.forall_iff, implies_true]
    | cons x xs =>
      rw [chunksOf]
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact List.length_take_le _ _
      · exact ih _ (by
        simp only [List.length_drop, ← h, List.length_cons]
        exact Nat.sub_lt (by omega) (by omega)) _ rfl p hp

theorem fbChunkLen_pos (P : Params) {m c : Nat} (hc : c < fbNC P m) : 1 ≤ fbChunkLen P m c := by
  have := lt_fbNC P hc; have := fbGPC_pos P; unfold fbChunkLen; omega

theorem fbNC_pos (P : Params) {m : Nat} (hm : 1 ≤ m) : 1 ≤ fbNC P m := by
  have := fbNC_mul P m
  rcases Nat.eq_zero_or_pos (fbNC P m) with h | h
  · rw [h] at this; omega
  · exact h

section layout
variable (P : Params) (l : List Nat) (s : Core)

theorem fbLayout_Gs (g : Nat) : ((fbLayout P l s).Gs.getX g) =
    if g = 0 then default else if g ≤ (chunksOf (fbGS P) l).length then
      fbGroup P (chunksOf (fbGS P) l) (g - 1) else default := by
  simp only [fbLayout]; exact getX_listArray _ _ _

theorem fbLayout_C (c : Nat) : ((fbLayout P l s).C.getX c) =
    if c = 0 then default else if c ≤ fbNC P (chunksOf (fbGS P) l).length then
      fbChunk P (chunksOf (fbGS P) l) (c - 1) else default := by
  simp only [fbLayout]; exact getX_listArray _ _ _

end layout

/-- **FALLBACK's layout** satisfies INV-S without the tag condition, for the nesting `fbAbs`. -/
theorem inv0_fbLayout {s : Core} {l : List Nat} (hE : ElemOK s l) (hP : FbOK s.P) :
    INV0 (fbLayout s.P l s) (fbAbs s.P l) := by
  generalize hP' : s.P = P at hP
  have hnd : l.Nodup := hE.eList.nodup
  have hsz : ∀ e ∈ l, e < s.E.size := fun e he => ((hE.eAlloc e).mp he).2
  generalize hgr : chunksOf (fbGS P) l = groups
  have hfl : groups.flatten = l := hgr ▸ chunksOf_flatten _ _
  have hne : ∀ p ∈ groups, p ≠ [] := hgr ▸ chunksOf_ne_nil _ _
  have hlen : ∀ p ∈ groups, p.length ≤ fbGS P := by
    have := chunksOf_mem_length (fbGS P) l; rw [hgr] at this
    intro p hp; have := this p hp; have := fbGS_pos P; unfold fbGS at *; omega
  generalize hm : groups.length = m
  have hm1 : 1 ≤ m := by
    rcases groups with _ | ⟨p, _⟩
    · simp only [List.flatten_nil, List.nil_eq] at hfl; exact absurd hfl.symm (Ne.symm hE.ne)
    · simp only [← hm, List.length_cons, Nat.le_add_left]
  have hnc := fbNC_pos P hm1
  have gpc := fbGPC_pos P
  -- element records
  have hEo := fun e => fbE_other P groups 0 s.E (hfl ▸ hnd) e
  have hEs : (fbLayout P l s).E.size = s.E.size := by
    simp only [fbLayout, hgr, fbElems_eq, fbE_size]
  have hElem : (fbLayout P l s).E = fbE P 0 groups s.E := by simp only [fbLayout, hgr, fbElems_eq]
  have hAg : ∀ g, (fbAbs P l).elts g = if 1 ≤ g ∧ g ≤ m then groups.getD (g - 1) [] else [] := by
    intro g; simp only [fbAbs, hgr, hm]
  have hAc : ∀ c, (fbAbs P l).grps c = if 1 ≤ c ∧ c ≤ fbNC P m then
      List.range' ((c - 1) * fbGPC P + 1) (fbChunkLen P m (c - 1)) else [] := by
    intro c; simp only [fbAbs, hgr, hm]
  have hAch : (fbAbs P l).chunks = List.range' 1 (fbNC P m) := by simp only [fbAbs, hgr, hm]
  have hgl : (fbAbs P l).glist = List.range' 1 m := by rw [fbAbs_glist, hgr, hm]
  have hel : (fbAbs P l).elist = l := fbAbs_elist P l
  have hG := fbLayout_Gs P l s
  have hC := fbLayout_C P l s
  rw [hgr, hm] at hG hC
  have mem_r : ∀ {a n z : Nat}, z ∈ List.range' a n ↔ a ≤ z ∧ z < a + n := by
    intro a n z; simp only [List.mem_range'_1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- eList
    rw [hel,
      show eN (fbLayout P l s) = eN s from funext fun e => by
        simp only [eN, hElem]; exact (hEo e).1,
      show eP (fbLayout P l s) = eP s from funext fun e => by
        simp only [eP, hElem]; exact (hEo e).2.1]
    exact hE.eList
  · intro e; rw [hel, hEs]; exact hE.eAlloc e
  · rw [hel]; exact hE.tail
  · -- gList
    rw [hgl, show (fbLayout P l s).firstGroup = 1 from rfl]
    refine llist_range' (le_refl 1) hm1 (fun z hz => ?_) (fun z hz => ?_)
    · rw [mem_r] at hz; simp only [gN, hG, ite_eq_right (show z ≠ 0 by omega), ite_eq_left (show
      z ≤ m by omega),
        fbGroup, hm]
      by_cases h : z + 1 < 1 + m
      · rw [ite_eq_left (by omega), ite_eq_left h]; omega
      · rw [ite_eq_right (by omega), ite_eq_right h]
    · rw [mem_r] at hz; simp only [gP, hG, ite_eq_right (show z ≠ 0 by omega), ite_eq_left (show
      z ≤ m by omega),
        fbGroup]
      by_cases h : z = 1
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
  · intro g hg; rw [hgl, mem_r] at hg; simp only [fbLayout, hgr, hm, size_listArray]; omega
  · simp only [fbLayout, size_listArray]; omega
  · intro g h1 h2
    simp only [fbLayout, hgr, hm, size_listArray] at h2
    rw [hgl,
      mem_r]; simp only [gA, hG, ite_eq_right (show g ≠ 0 by omega),
      ite_eq_left (show g ≤ m by omega)]
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro g hg; rw [hgl, mem_r] at hg
    simp only [gN, gP, hG]
    by_cases h0 : g = 0
    · simp only [h0, ite_true]; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right h0, ite_eq_right (show ¬ g ≤ m by omega)]; exact ⟨rfl, rfl⟩
  · intro g hg; simp only [fbLayout, List.not_mem_nil] at hg
  · simp only [fbLayout, List.nodup_nil]
  · -- cList
    rw [hAch, show (fbLayout P l s).firstChunk = 1 from rfl]
    refine llist_range' (le_refl 1) hnc (fun z hz => ?_) (fun z hz => ?_)
    · rw [mem_r] at hz; simp only [cN, hC, ite_eq_right (show z ≠ 0 by omega),
        ite_eq_left (show z ≤ fbNC P m by omega), fbChunk, hm]
      by_cases h : z + 1 < 1 + fbNC P m
      · rw [ite_eq_left (by omega), ite_eq_left h]; omega
      · rw [ite_eq_right (by omega), ite_eq_right h]
    · rw [mem_r] at hz; simp only [cP, hC, ite_eq_right (show z ≠ 0 by omega),
        ite_eq_left (show z ≤ fbNC P m by omega), fbChunk]
      by_cases h : z = 1
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
  · intro c; rw [hAch, mem_r]; simp only [fbLayout, hgr, hm, size_listArray]; omega
  · intro c hc; rw [hAch, mem_r] at hc
    simp only [cN, cP, cF, hC]
    by_cases h0 : c = 0
    · simp only [h0, ite_true]; exact ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right h0, ite_eq_right (show ¬ c ≤ fbNC P m by omega)]; exact ⟨rfl, rfl, rfl⟩
  · -- gEnds
    intro g hg; rw [hgl, mem_r] at hg
    rw [hAg, ite_eq_left ⟨by omega, by omega⟩]
    simp only [gF, gLs, hG, ite_eq_right (show g ≠ 0 by omega), ite_eq_left (show g ≤ m by omega),
      fbGroup]
    exact ⟨rfl, rfl⟩
  · -- cEnds
    intro c hc; rw [hAch, mem_r] at hc
    have hlen1 := fbChunkLen_pos P (m := m) (c := c - 1) (by omega)
    rw [hAc, ite_eq_left ⟨by omega, by omega⟩]
    simp only [cF, cLs, hC, ite_eq_right (show c ≠ 0 by omega),
      ite_eq_left (show c ≤ fbNC P m by omega), fbChunk,
      hm]
    refine ⟨(range'_headD _ _ hlen1).symm, ?_⟩
    rw [range'_getLastD _ _ hlen1]; omega
  · -- grp
    intro g hg e he
    rw [hgl, mem_r] at hg
    rw [hAg, ite_eq_left ⟨by omega, by omega⟩] at he
    have hk : g - 1 < groups.length := by omega
    rw [List.getD_eq_getElem _ _ hk] at he
    simp only [eG, hElem]
    rw [(fbE_in P groups 0 s.E (hfl ▸ hnd) (fun e he => hsz e (hfl ▸ he)) hk he).1]; omega
  · -- chk
    intro c hc g hg
    rw [hAch, mem_r] at hc
    rw [hAc, ite_eq_left ⟨by omega, by omega⟩, mem_r] at hg
    have hlen1 : fbChunkLen P m (c - 1) ≤ m - (c - 1) * fbGPC P := Nat.min_le_right _ _
    have hlen2 : fbChunkLen P m (c - 1) ≤ fbGPC P := Nat.min_le_left _ _
    simp only [gC, hG, ite_eq_right (show g ≠ 0 by omega), ite_eq_left (show g ≤ m by omega),
      fbGroup]
    have : (g - 1) / fbGPC P = c - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm] at *; omega
      · rw [Nat.succ_mul]; omega
    omega
  · -- eSorted
    intro g hg
    rw [hgl, mem_r] at hg
    rw [hAg, ite_eq_left ⟨by omega, by omega⟩]
    have hk : g - 1 < groups.length := by omega
    rw [List.getD_eq_getElem _ _ hk]
    have hmem : groups[g - 1] ∈ groups := List.getElem_mem hk
    have hst : 1 ≤ (1 <<< P.elementBits) / (groups[g - 1].length + 1) := by
      have := hlen _ hmem
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by have := hP.1; omega)
    have hnd' : groups[g - 1].Nodup := by
      have := hfl ▸ hnd; exact List.Nodup.sublist (List.sublist_flatten_of_mem hmem) this
    rw [List.map_congr_left (g := fun e => (groups[g - 1].idxOf e + 1) *
      ((1 <<< P.elementBits) / (groups[g - 1].length + 1))) (fun e he => by
        simp only [eL, hElem]
        exact (fbE_in P groups 0 s.E (hfl ▸ hnd) (fun e he => hsz e (hfl ▸ he)) hk he).2)]
    exact isChain_spaced hnd' hst
  · -- gSorted
    intro c hc
    rw [hAch, mem_r] at hc
    rw [hAc, ite_eq_left ⟨by omega, by omega⟩]
    have hlen1 : fbChunkLen P m (c - 1) ≤ m - (c - 1) * fbGPC P := Nat.min_le_right _ _
    have hlen2 : fbChunkLen P m (c - 1) ≤ fbGPC P := Nat.min_le_left _ _
    generalize hst : (1 <<< P.groupBits) / (fbChunkLen P m (c - 1) + 1) = st
    have hst1 : 1 ≤ st := by
      rw [← hst]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by have := hP.2; omega)
    rw [List.map_congr_left (g := fun g => (g - 1 - (c - 1) * fbGPC P + 1) * st) (fun g hg => by
      rw [mem_r] at hg
      simp only [gL, hG, ite_eq_right (show g ≠ 0 by omega), ite_eq_left (show g ≤ m by omega),
        fbGroup, hm]
      have hd : (g - 1) / fbGPC P = c - 1 := by
        apply Nat.div_eq_of_lt_le
        · omega
        · rw [Nat.succ_mul]; omega
      have hmod : (g - 1) % fbGPC P = g - 1 - (c - 1) * fbGPC P := by
        have := Nat.div_add_mod (g - 1) (fbGPC P); rw [hd] at this; rw [Nat.mul_comm] at this; omega
      rw [hd, hmod, hst])]
    rw [List.range'_eq_map_range, List.map_map]
    rw [List.map_congr_left (g := fun i => (i + 1) * st) (fun i _ => by
      simp only [Function.comp]; congr 1; omega)]
    exact isChain_range_mul _ hst1

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Rebuilding the top structure -/

theorem Pres.sameLinks {α : Type} {m : CM α} (h : Pres Same m) : Pres SameLinks m :=
  h.mono fun _ _ h => h.1

theorem sameLinks_C_tag (s : Core) (C : Array Chunk) (hs : C.size = s.C.size)
    (h : ∀ c, (C.getX c).next = (s.C.getX c).next ∧ (C.getX c).prev = (s.C.getX c).prev ∧
      (C.getX c).first = (s.C.getX c).first ∧ (C.getX c).last = (s.C.getX c).last) :
    SameLinks s { s with C := C } := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ =>
    rfl, rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ =>
      rfl,
    rfl, rfl, rfl, rfl, rfl, hs, fun c => (h c).1, fun c => (h c).2.1, fun c => (h c).2.2.1,
    fun c => (h c).2.2.2, rfl⟩

theorem pres_modC_tag (c t : Nat) : Pres SameLinks (modC c fun C => { C with tag := t }) := by
  unfold modC
  refine Pres.modify fun s => sameLinks_C_tag s _ (by simp) fun x => ?_
  simp only [Array.getX_modify]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem pres_build (cs : List Nat) : Pres SameLinks (build cs) := by
  unfold build
  pres [pres_resetTop.sameLinks, pres_getP, (pres_newNode _).sameLinks, (pres_setInTables _ _
    _).sameLinks,
    (pres_setLpar _ _).sameLinks, (pres_modN _ _).sameLinks, pres_getN _, pres_getLpar _,
    (pres_setPath _ _).sameLinks, (pres_tagOf _).sameLinks, pres_modC_tag _ _]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Walking a linked list -/

theorem walkList_eq {nxt : Nat → Nat} {l : List Nat} (hnd : l.Nodup) (hnil : NIL ∉ l)
    (hn : ∀ x ∈ l, nxt x = succOf l x) {fuel : Nat} (hf : l.length ≤ fuel) :
    walkList nxt fuel (l.headD NIL) = l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> simp only [walkList, List.headD_eq_head?_getD, List.head?_nil,
      Option.getD_none, ↓reduceIte]
  | cons a t ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [List.length_cons] at hf; omega⟩
    have ha : a ≠ NIL := fun h => hnil (h ▸ List.mem_cons_self ..)
    rw [List.headD_cons, walkList, ite_eq_right ha]
    rw [hn a List.mem_cons_self, succOf_cons', ite_eq_left rfl]
    simp only [List.nodup_cons] at hnd
    rw [ih hnd.2 (fun h => hnil (List.mem_cons_of_mem _ h)) (fun x hx => by
      rw [hn x (List.mem_cons_of_mem _ hx), succOf_cons',
        ite_eq_right (fun (e : x = a) => hnd.1 (e ▸ hx))])
      (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hf; omega)]

theorem LList.walk {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l)
    {fuel : Nat} (hf : l.length ≤ fuel) : walkList nxt fuel hd = l := by
  rw [h.head]; exact walkList_eq h.nodup h.nonil h.next hf

/-- A list of distinct numbers in `[1, n)` has length below `n`. -/
theorem length_lt_of_range {l : List Nat} {n : Nat} (hnd : l.Nodup) (h : ∀ x ∈ l, 1 ≤ x ∧ x < n) :
    l.length ≤ n := by
  have : l.toFinset ⊆ Finset.range n := fun x hx => by
    simp only [List.mem_toFinset] at hx; simp only [Finset.mem_range, (h x hx).2]
  have := Finset.card_le_card this
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
  exact this

/-! ### Renumbering the chunks -/

theorem renumber_getX (l : List Nat) (C : Array Chunk) (hnd : l.Nodup) (c : Nat) :
    (renumber l C).getX c =
      if c ∈ l ∧ c < C.size then { C.getX c with tag := 1 + l.idxOf c } else C.getX c := by
  unfold renumber
  exact foldl_zipIdx_modify l (fun i x => { x with tag := i }) C 1 hnd c

theorem renumber_size (l : List Nat) (C : Array Chunk) : (renumber l C).size = C.size := by
  unfold renumber; exact foldl_zipIdx_modify_size l (fun i x => { x with tag := i }) C 1

theorem sameLinks_renumber (s : Core) (l : List Nat) (hnd : l.Nodup) :
    SameLinks s { s with C := renumber l s.C } :=
  sameLinks_C_tag s _ (renumber_size _ _) fun c => by
    rw [renumber_getX _ _ hnd]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem increasing_iff (l : List Nat) : increasing l = true ↔ l.IsChain (· < ·) := by
  induction l with
  | nil => simp only [increasing, List.IsChain.nil]
  | cons a t ih =>
    cases t with
    | nil => simp only [increasing, List.IsChain.singleton]
    | cons b t => simp only [increasing, Bool.and_eq_true, decide_eq_true_eq, ih,
        List.isChain_cons_cons]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem run_tryCatch_unit (m : CM Unit) (s : Core) :
    (tryCatch m (fun _ => pure ()) : CM Unit).run s =
      match m.run s with
      | .ok a s' => .ok a s'
      | .error _ s' => .ok () s' := by
  change EStateM.tryCatch m _ s = _
  simp only [EStateM.tryCatch, EStateM.run]
  rcases m s with ⟨a, s'⟩ | ⟨e, s'⟩ <;> rfl

theorem tryCatch_pres {R : Core → Core → Prop} {m : CM Unit} (hm : Pres R m) (s : Core) :
    ∃ s', (tryCatch m (fun _ => pure ()) : CM Unit).run s = .ok () s' ∧ R s s' := by
  have h := hm s
  rw [run_tryCatch_unit]
  revert h
  rcases m.run s with ⟨⟨⟩, s'⟩ | ⟨e, s'⟩
  · exact fun h => ⟨s', rfl, h⟩
  · rcases e with msg | msg
    · exact fun h => ⟨s', rfl, h⟩
    · exact fun h => h.elim

/-- **FALLBACK's top part**: from INV-S without tags, `relabelAll` succeeds with INV-S. -/
theorem relabelAll_run {s : Core} {A : Abs} (h : INV0 s A) :
    ∃ s', relabelAll.run s = .ok () s' ∧ SameLinks s s' ∧ INV s' A := by
  unfold relabelAll
  rw [run_get_bind]
  have hw : walkList (fun c => (s.C.getX c).next) s.C.size s.firstChunk = A.chunks :=
    h.cList.walk (length_lt_of_range h.cList.nodup fun c hc => (h.cAlloc c).mp hc)
  rw [hw]
  obtain ⟨s1, h1, hs1⟩ := tryCatch_pres (pres_build A.chunks) s
  rw [run_bind, h1]
  simp only [run_get_bind]
  have I1 := h.of_sameLinks hs1
  have hnd := h.cList.nodup
  by_cases hinc : increasing (A.chunks.map fun c => (s1.C.getX c).tag) = true
  · rw [ite_eq_right (by simp only [hinc, Bool.not_true, Bool.false_eq_true, not_false_eq_true])]
    exact ⟨s1, rfl, hs1, I1.toINV ((increasing_iff _).mp hinc)⟩
  · rw [ite_eq_left (by simpa using hinc)]
    refine ⟨_, rfl, hs1.trans (sameLinks_renumber _ _ hnd), ?_⟩
    apply (I1.of_sameLinks (sameLinks_renumber s1 _ hnd)).toINV
    rw [List.map_congr_left (g := fun c => (A.chunks.idxOf c + 1) * 1) (fun c hc => by
      have hcs : c ∈ A.chunks ∧ c < s1.C.size := ⟨hc, ((I1.cAlloc c).mp hc).2⟩
      simp only [cT, renumber_getX _ _ hnd, ite_eq_left hcs]; omega)]
    exact isChain_spaced hnd le_rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem run_elements_bind {β : Type} (k : List Nat → CM β) (s : Core) :
    (elements >>= k).run s = (k (walkList (fun e => (s.E.getX e).next) s.E.size s.head)).run s
      := rfl

theorem eframe_fbLayout (P : Params) (l : List Nat) (s : Core) (hnd : l.Nodup) :
    EFrame s (fbLayout P l s) := by
  have hnd' : (chunksOf (fbGS P) l).flatten.Nodup := by rw [chunksOf_flatten]; exact hnd
  have h := fun e => fbE_other P (chunksOf (fbGS P) l) 0 s.E hnd' e
  refine ⟨?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, rfl, rfl, rfl⟩
  · simp only [fbLayout, fbElems_eq, fbE_size]
  · simp only [eN, fbLayout, fbElems_eq]; exact (h e).1
  · simp only [eP, fbLayout, fbElems_eq]; exact (h e).2.1
  · simp only [fbLayout, fbElems_eq]; exact (h e).2.2.1
  · simp only [fbLayout, fbElems_eq]; exact (h e).2.2.2

/-- **Lemma 3.3 (FALLBACK).** From any state whose element list `l` is a well-formed non-empty
doubly linked list, FALLBACK succeeds, keeps the element records' links, liveness and handles,
and establishes INV-S with the same element list. -/
theorem fallback_run {s : Core} {l : List Nat} (hE : ElemOK s l) (hP : FbOK s.P) :
    ∃ s', fallback.run s = .ok () s' ∧ EFrame s s' ∧ ∃ A, INV s' A ∧ A.elist = l := by
  unfold fallback
  simp only [run_getP_bind, run_modify_bind, run_elements_bind]
  have hw : walkList (fun e => (s.E.getX e).next) s.E.size s.head = l :=
    hE.eList.walk (length_lt_of_range hE.eList.nodup fun e he => (hE.eAlloc e).mp he)
  rw [hw]
  generalize hs0 : { s with fallbacks := s.fallbacks + 1 } = s0
  have e0 : EFrame s s0 := by
    rw [← hs0]; exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩
  have hE0 : ElemOK s0 l := hE.of_eframe e0
  have hPs : s.P = s0.P := by rw [← hs0]
  have hP0 : FbOK s0.P := hPs ▸ hP
  rw [hPs]
  obtain ⟨s2, h2, hs2, I2⟩ := relabelAll_run (inv0_fbLayout hE0 hP0)
  refine ⟨s2, h2, ?_, fbAbs s0.P l, I2, fbAbs_elist _ _⟩
  exact e0.trans ((eframe_fbLayout _ _ _ hE0.eList.nodup).trans hs2.eframe)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Room for the retried insertion -/

/-- Parameters for the retry: FALLBACK's element gap exceeds the append distance
  `elementSpacing ≥ 1`. -/
def RoomP (P : Params) : Prop := 1 ≤ P.elementSpacing ∧ P.elementSpacing < (1 <<<
  P.elementBits) / (fbGS P + 1)

/-- Every element has room for an insertion right after it. -/
def Room (s : Core) (A : Abs) : Prop :=
  1 ≤ s.P.elementSpacing ∧ ∀ x ∈ A.elist, (x = gLs s (eG s x) → eL s x + s.P.elementSpacing < 1
    <<< s.P.elementBits) ∧
    (x ≠ gLs s (eG s x) → eL s x + 1 < eL s (eN s x))

theorem Room.of_sameLinks {s s' : Core} {A : Abs} (h : Room s A) (hs : SameLinks s s') : Room s'
  A := by
  refine ⟨hs.P ▸ h.1, fun x hx => ?_⟩
  rw [hs.eG, hs.gLs, hs.eL, hs.eN, hs.eL, hs.P]
  exact h.2 x hx

theorem succOf_getElem {b : List Nat} (hnd : b.Nodup) {i : Nat} (hi : i + 1 < b.length) :
    succOf b b[i] = b[i + 1] := by
  have e : b = b.take i ++ b[i] :: b.drop (i + 1) := by
    simp only [List.getElem_cons_drop, List.take_append_drop]
  generalize hx : b[i] = x at e
  have hnd' := hnd; rw [e] at hnd'
  calc succOf b x = succOf (b.take i ++ x :: b.drop (i + 1)) x := congrArg (succOf · x) e
    _ = (b.drop (i + 1)).headD NIL := succOf_mid hnd'
    _ = b[i + 1] := by
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hi]; rfl

theorem getLastD_eq_getElem {b : List Nat} (hb : b ≠ []) :
    b.getLastD NIL = b[b.length - 1]'(by have := List.length_pos_iff.mpr hb; omega) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem]; rfl

theorem room_fbLayout {s : Core} {l : List Nat} (hE : ElemOK s l) (hP : RoomP s.P) :
    Room (fbLayout s.P l s) (fbAbs s.P l) := by
  refine ⟨hP.1, fun x hx => ?_⟩
  rw [fbAbs_elist] at hx
  generalize hP' : s.P = P at hP
  have hnd : l.Nodup := hE.eList.nodup
  have hsz : ∀ e ∈ l, e < s.E.size := fun e he => ((hE.eAlloc e).mp he).2
  have hPl : (fbLayout P l s).P = P := hP'
  rw [hPl]
  generalize hgr : chunksOf (fbGS P) l = groups
  have hfl : groups.flatten = l := hgr ▸ chunksOf_flatten _ _
  have hne : ∀ p ∈ groups, p ≠ [] := hgr ▸ chunksOf_ne_nil _ _
  have hlen : ∀ p ∈ groups, p.length ≤ fbGS P := by
    have := chunksOf_mem_length (fbGS P) l; rw [hgr] at this
    intro p hp; have := this p hp; have := fbGS_pos P; unfold fbGS at *; omega
  have hElem : (fbLayout P l s).E = fbE P 0 groups s.E := by simp only [fbLayout, hgr, fbElems_eq]
  have hG := fbLayout_Gs P l s
  rw [hgr] at hG
  -- the group of `x`
  rw [← hfl, List.mem_flatten] at hx
  obtain ⟨b, hb, hxb⟩ := hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
  have hin := fbE_in P groups 0 s.E (hfl ▸ hnd) (fun e he => hsz e (hfl ▸ he)) hk hxb
  have hbnd : groups[k].Nodup := List.Nodup.sublist (List.sublist_flatten_of_mem hb) (hfl ▸ hnd)
  have hbne := hne _ hb
  generalize hst : (1 <<< P.elementBits) / (groups[k].length + 1) = st at hin
  have hD : P.elementSpacing < st := by
    rw [← hst]
    exact Nat.lt_of_lt_of_le hP.2 (Nat.div_le_div_left (by have := hlen _ hb; omega) (by omega))
  have hstB : (groups[k].length + 1) * st ≤ 1 <<< P.elementBits := by
    rw [← hst, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  generalize hi : groups[k].idxOf x = i at hin
  have hil : i < groups[k].length := hi ▸ List.idxOf_lt_length_of_mem hxb
  have hxi : groups[k][i] = x := by subst hi; exact List.getElem_idxOf hil
  have heG : eG (fbLayout P l s) x = k + 1 := by simp only [eG, hElem]; rw [hin.1]; omega
  have hgl : gLs (fbLayout P l s) (k + 1) = groups[k].getLastD NIL := by
    simp only [gLs, hG, ite_eq_right (show k + 1 ≠ 0 by omega),
      ite_eq_left (show k + 1 ≤ groups.length by omega),
      fbGroup, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hk]
  have heL : eL (fbLayout P l s) x = (i + 1) * st := by simp only [eL, hElem]; exact hin.2
  rw [heG, hgl, heL, getLastD_eq_getElem hbne]
  refine ⟨fun hlast => ?_, fun hnl => ?_⟩
  · have : i = groups[k].length - 1 := by
      rw [← hxi] at hlast; exact (List.Nodup.getElem_inj_iff hbnd).mp hlast
    have : (i + 1) * st + st ≤ 1 <<< P.elementBits := by
      rw [← Nat.succ_mul]; refine Nat.le_trans (Nat.mul_le_mul_right _ ?_) hstB; omega
    omega
  · have hi1 : i + 1 < groups[k].length := by
      by_contra h
      exact hnl (by rw [← hxi]; congr 1; omega)
    have hN : eN (fbLayout P l s) x = groups[k][i + 1] := by
      have := (eframe_fbLayout P l s hnd).next x
      rw [this, hE.eList.next x (hfl ▸ List.mem_flatten.mpr ⟨_, hb, hxb⟩), ← hfl,
        succOf_flatten (hfl ▸ hnd) hb hxb (by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          intro h; apply hnl; rw [Option.some_inj] at h; exact h ▸ rfl),
        ← hxi, succOf_getElem hbnd hi1]
    have hmem : groups[k][i + 1] ∈ groups[k] := List.getElem_mem _
    have hin2 := fbE_in P groups 0 s.E (hfl ▸ hnd) (fun e he => hsz e (hfl ▸ he)) hk hmem
    rw [hst, List.Nodup.idxOf_getElem hbnd] at hin2
    rw [hN]; simp only [eL, hElem]; rw [hin2.2]
    have := hP.1
    rw [Nat.succ_mul (i + 1)]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **Lemma 3.3 with room**: under `RoomP`, every element also has room after FALLBACK. -/
theorem fallback_run_room {s : Core} {l : List Nat} (hE : ElemOK s l) (hP : FbOK s.P)
    (hR : RoomP s.P) :
    ∃ s', fallback.run s = .ok () s' ∧ EFrame s s' ∧ ∃ A, INV s' A ∧ A.elist = l ∧ Room s' A := by
  unfold fallback
  simp only [run_getP_bind, run_modify_bind, run_elements_bind]
  have hw : walkList (fun e => (s.E.getX e).next) s.E.size s.head = l :=
    hE.eList.walk (length_lt_of_range hE.eList.nodup fun e he => (hE.eAlloc e).mp he)
  rw [hw]
  generalize hs0 : { s with fallbacks := s.fallbacks + 1 } = s0
  have e0 : EFrame s s0 := by
    rw [← hs0]; exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩
  have hE0 : ElemOK s0 l := hE.of_eframe e0
  have hPs : s.P = s0.P := by rw [← hs0]
  have hP0 : FbOK s0.P := hPs ▸ hP
  have hR0 : RoomP s0.P := hPs ▸ hR
  rw [hPs]
  obtain ⟨s2, h2, hs2, I2⟩ := relabelAll_run (inv0_fbLayout hE0 hP0)
  refine ⟨s2, h2, ?_, fbAbs s0.P l, I2, fbAbs_elist _ _, (room_fbLayout hE0 hR0).of_sameLinks hs2⟩
  exact e0.trans ((eframe_fbLayout _ _ _ hE0.eList.nodup).trans hs2.eframe)

end OrderMaintenance.Proof
