/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
public import LeanPool.DynamicMcs.Correctness
public import LeanPool.DynamicMcs.McsInvariant

/-!
# The executable dynamic updates refine the abstract ones

On a symmetric loop-free square matrix whose graph differs from the old one by
a flip of `{u, v}`, the executable `execInsertUpdate` / `execDeleteUpdate`
applied to (the values of) the old canonical ordering return (the values of)
the abstract `insertUpdate` / `deleteUpdate`, which is the from-scratch
canonical ordering `mcsOrder` of the new matrix.

The operational cost theorems at the end bound the instrumented versions
`execInsertUpdateC` / `execDeleteUpdateC`, whose first component is the
executable update itself.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs
namespace Proofs

open UGraph Transport

variable {n : ℕ}

/-! ## List helpers -/

lemma idxOf_map_val (l : List (Fin n)) (x : Fin n) :
    (l.map Fin.val).idxOf x.val = l.idxOf x := by
  induction l with
  | nil => simp
  | cons y l ih => simp [List.idxOf_cons, ih, Fin.val_inj]

lemma mem_remOf {m : ℕ} {chosen : List ℕ} {v : ℕ} :
    v ∈ remOf m chosen ↔ v < m ∧ v ∉ chosen := by
  simp [remOf]

lemma remOf_nodup (m : ℕ) (chosen : List ℕ) : (remOf m chosen).Nodup :=
  List.Nodup.filter _ List.nodup_range

lemma remOf_erase (m : ℕ) (Q : List ℕ) (w : ℕ) :
    (remOf m Q).erase w = remOf m (Q ++ [w]) := by
  rw [List.Nodup.erase_eq_filter (remOf_nodup m Q), remOf, remOf, List.filter_filter]
  apply List.filter_congr
  intro v _
  by_cases h1 : v = w <;> by_cases h2 : v ∈ Q <;> simp [h1, h2]

lemma cardC_reverse (a : Adj n) (l : List ℕ) (w : ℕ) : cardC a l.reverse w = cardC a l w := by
  simp [cardC, List.filter_reverse]

lemma bestPick_reverse (a : Adj n) (l rem : List ℕ) :
    bestPick a l.reverse rem = bestPick a l rem := by
  unfold bestPick
  simp only [cardC_reverse]

lemma mcsStep_cons (a : Adj n) (chosen rem : List ℕ) (h : rem ≠ []) :
    mcsStep a (chosen, rem) =
      (bestPick a chosen rem :: chosen, rem.erase (bestPick a chosen rem)) := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

lemma chosenFin_map_val (P : List (Fin n)) (h : ∀ v ∈ P.map Fin.val, v < n) :
    CardBridge.chosenFin n (P.map Fin.val) h = P := by
  unfold CardBridge.chosenFin
  induction P with
  | nil => rfl
  | cons x P ih =>
      simp only [List.map_cons, List.pmap_cons]
      exact congrArg (x :: ·) (ih _)

lemma listInv_remOf (P : List (Fin n)) (hP : P.Nodup) :
    McsInvariant.McListInv n (P.map Fin.val, remOf n (P.map Fin.val)) := by
  refine ⟨List.Nodup.map Fin.val_injective hP, remOf_nodup n _, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hv
    exact x.2
  · intro v hv
    exact (mem_remOf.1 hv).1
  · intro v hv
    exact ⟨fun h => (mem_remOf.1 h).2, fun h => mem_remOf.2 ⟨hv, h⟩⟩

lemma exists_not_mem (P : List (Fin n)) (hP : P.Nodup) (hlt : P.length < n) :
    ∃ x : Fin n, x ∉ P := by
  by_contra hall
  push Not at hall
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ P.toFinset :=
    fun x _ => List.mem_toFinset.2 (hall x)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hP] at hcard
  omega

/-- A prefix of a canonical ordering has canonical steps. -/
lemma steps_of_prefix {G : UGraph n} {pref rest : List (Fin n)}
    (h : IsMCSOrdering G (pref ++ rest)) :
    pref.Nodup ∧ ∀ i (hi : i < pref.length),
      IsMCSNext G (pref.take i).toFinset (pref.get ⟨i, hi⟩) := by
  refine ⟨(List.nodup_append.1 h.1).1, fun i hi => ?_⟩
  have hi' : i < (pref ++ rest).length := by
    rw [List.length_append]
    omega
  have hstep := h.2.2 i hi'
  have htake : (pref ++ rest).take i = pref.take i := by
    rw [List.take_append]
    have h0 : i - pref.length = 0 := Nat.sub_eq_zero_of_le (le_of_lt hi)
    simp [h0]
  have hget : (pref ++ rest).get ⟨i, hi'⟩ = pref.get ⟨i, hi⟩ := by
    apply List.getElem_append_left
  rwa [htake, hget] at hstep

/-- Appending one step preserves any per-step predicate. -/
lemma steps_append {Q : Finset (Fin n) → Fin n → Prop} (P : List (Fin n)) (w : Fin n)
    (hP : ∀ i (hi : i < P.length), Q (P.take i).toFinset (P.get ⟨i, hi⟩))
    (hw : Q P.toFinset w) :
    ∀ i (hi : i < (P ++ [w]).length),
      Q ((P ++ [w]).take i).toFinset ((P ++ [w]).get ⟨i, hi⟩) := by
  intro i hi
  by_cases hlt : i < P.length
  · have htake : (P ++ [w]).take i = P.take i := by
      rw [List.take_append]
      have h0 : i - P.length = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      simp [h0]
    have hget : (P ++ [w]).get ⟨i, hi⟩ = P.get ⟨i, hlt⟩ := by
      apply List.getElem_append_left
    rw [htake, hget]
    exact hP i hlt
  · have hi_eq : i = P.length := by
      have hlen : (P ++ [w]).length = P.length + 1 := by simp
      omega
    subst hi_eq
    have htake : (P ++ [w]).take P.length = P := by
      rw [List.take_append]
      simp
    have hget : (P ++ [w]).get ⟨P.length, hi⟩ = w := by
      simp [List.get_eq_getElem, List.getElem_append_right (le_refl P.length)]
    rw [htake, hget]
    exact hw

/-! ## The executable pick is the canonical pick -/

section Matrix

variable (a : Adj n) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
  (hloop : ∀ u : ℕ, getAdj a u u = false) (ha : a.length = n)

include hsymm hloop ha in
theorem pickAt_spec (P : List (Fin n)) (hP : P.Nodup) (hlt : P.length < n) :
    ∃ w : Fin n, pickAt a (P.map Fin.val) = w.val ∧
      IsMCSNext (toUGraph a hsymm hloop) P.toFinset w := by
  have hinv := listInv_remOf P hP
  obtain ⟨x, hx⟩ := exists_not_mem P hP hlt
  have hrem : remOf n (P.map Fin.val) ≠ [] := by
    intro h
    have hxm : x.val ∈ remOf n (P.map Fin.val) := by
      refine mem_remOf.2 ⟨x.2, fun hm => hx ?_⟩
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hm
      rwa [← Fin.ext hyx]
    rw [h] at hxm
    simp at hxm
  have hbest := McsInvariant.bestPick_IsMCSNext n a hsymm hloop _ _ hinv hrem
  rw [chosenFin_map_val] at hbest
  obtain ⟨hmem, _, _⟩ :=
    BridgeSteps.bestPick_lex a (P.map Fin.val) (remOf n (P.map Fin.val)) hrem
  have hlt' : bestPick a (P.map Fin.val) (remOf n (P.map Fin.val)) < n :=
    hinv.2.2.2.1 _ hmem
  refine ⟨@Fin.mk n (bestPick a (P.map Fin.val) (remOf n (P.map Fin.val))) hlt', ?_, ?_⟩
  · change bestPick a (P.map Fin.val) (remOf a.length (P.map Fin.val)) =
      bestPick a (P.map Fin.val) (remOf n (P.map Fin.val))
    rw [ha]
  · exact hbest

include hsymm hloop ha in
theorem pickAt_eq_iff (P : List (Fin n)) (hP : P.Nodup) (hlt : P.length < n) (x : Fin n) :
    pickAt a (P.map Fin.val) = x.val ↔ IsMCSNext (toUGraph a hsymm hloop) P.toFinset x := by
  obtain ⟨w, hw, hnext⟩ := pickAt_spec a hsymm hloop ha P hP hlt
  rw [hw]
  constructor
  · intro h
    rwa [← Fin.ext h]
  · intro h
    rw [IsMCSNext_unique hnext h]

include hsymm hloop ha in
/-- The executable probe computes the abstract scan. -/
theorem execFirstBreak_map (ord : List (Fin n)) (hnd : ord.Nodup) :
    ∀ (k : ℕ) (xs : List (Fin n)), k + xs.length ≤ n →
      execFirstBreak a (ord.map Fin.val) k (xs.map Fin.val) =
        firstBreakAux (toUGraph a hsymm hloop) ord k xs := by
  intro k xs
  induction xs generalizing k with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hlen
      rw [List.length_cons] at hlen
      have hP : (ord.take k).Nodup := hnd.sublist (List.take_sublist _ _)
      have hPlen : (ord.take k).length < n := by
        rw [List.length_take]
        omega
      have htake : (ord.map Fin.val).take k = (ord.take k).map Fin.val := by
        simp [List.map_take]
      have hiff := pickAt_eq_iff a hsymm hloop ha (ord.take k) hP hPlen x
      rw [List.map_cons, execFirstBreak, firstBreakAux, htake]
      by_cases hx : IsMCSNext (toUGraph a hsymm hloop) (ord.take k).toFinset x
      · simp only [hiff.2 hx, hx, ↓reduceIte]
        exact ih (k + 1) (by omega)
      · simp only [mt hiff.1 hx, hx, ↓reduceIte]

include hsymm hloop ha in
lemma regreedy_inv (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    ∀ j, pref.length + j ≤ n → ∃ P : List (Fin n), P.length = pref.length + j ∧ P.Nodup ∧
      (∀ i (hi : i < P.length),
        IsMCSNext (toUGraph a hsymm hloop) (P.take i).toFinset (P.get ⟨i, hi⟩)) ∧
      (List.range j).foldl (fun s _ => mcsStep a s)
          ((pref.map Fin.val).reverse, remOf a.length (pref.map Fin.val)) =
        ((P.map Fin.val).reverse, remOf a.length (P.map Fin.val)) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨pref, rfl, hnd, hsteps, rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨P, hlen, hPnd, hPsteps, hfold⟩ := ih (by omega)
      obtain ⟨w, hw, hnext⟩ := pickAt_spec a hsymm hloop ha P hPnd (by omega)
      have hwP : w ∉ P := fun hm => (Finset.mem_sdiff.1 hnext.1).2 (List.mem_toFinset.2 hm)
      have hrem : remOf a.length (P.map Fin.val) ≠ [] := by
        intro h
        have hwm : w.val ∈ remOf a.length (P.map Fin.val) := by
          refine mem_remOf.2 ⟨by rw [ha]; exact w.2, fun hm => hwP ?_⟩
          obtain ⟨y, hy, hyw⟩ := List.mem_map.1 hm
          rwa [← Fin.ext hyw]
        rw [h] at hwm
        simp at hwm
      refine ⟨P ++ [w], by simp [hlen]; omega, ?_, steps_append P w hPsteps hnext, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hPnd, List.nodup_singleton w, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        intro hxy
        subst hxy
        exact hwP hx
      · rw [List.range_succ, List.foldl_append, hfold]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [mcsStep_cons a _ _ hrem, bestPick_reverse]
        have hpick : bestPick a (P.map Fin.val) (remOf a.length (P.map Fin.val)) = w.val := hw
        rw [hpick, remOf_erase]
        simp

include hsymm hloop ha in
/-- The executable regreedy from a canonical prefix returns a canonical
ordering. -/
theorem regreedy_spec (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    ∃ ord : List (Fin n), IsMCSOrdering (toUGraph a hsymm hloop) ord ∧
      regreedy a (pref.map Fin.val) = ord.map Fin.val := by
  have hle : pref.length ≤ n := by simpa using hnd.length_le_card
  obtain ⟨P, hlen, hPnd, hPsteps, hfold⟩ :=
    regreedy_inv a hsymm hloop ha pref hnd hsteps (n - pref.length) (by omega)
  refine ⟨P, ⟨hPnd, by omega, hPsteps⟩, ?_⟩
  unfold regreedy
  rw [List.length_map, show a.length - pref.length = n - pref.length by rw [ha], hfold]
  simp

/-- Regreedy from a canonical prefix is canonical (abstract side). -/
theorem greedySuffix_valid (G : UGraph n) (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length), IsMCSNext G (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    IsMCSOrdering G (greedySuffix G pref) := by
  rw [greedySuffix_eq, IsMCSOrdering_toDyn]
  exact UGraph.greedySuffix_valid _ pref hnd
    (fun i hi => (IsMCSNext_toDyn G _ _).1 (hsteps i hi))

include hsymm hloop ha in
theorem regreedy_eq_greedySuffix (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    regreedy a (pref.map Fin.val) = (greedySuffix (toUGraph a hsymm hloop) pref).map Fin.val := by
  obtain ⟨ord, hord, heq⟩ := regreedy_spec a hsymm hloop ha pref hnd hsteps
  rw [heq, IsMCSOrdering_unique hord (greedySuffix_valid _ pref hnd hsteps)]

lemma mcsOrder_eq_regreedy : mcsOrder a = regreedy a [] := by
  simp [mcsOrder, regreedy, remOf]

include hsymm hloop ha in
/-- The executable from-scratch ordering is the canonical ordering. -/
theorem mcsOrder_eq_initOrder :
    mcsOrder a = (initOrder (toUGraph a hsymm hloop)).map Fin.val := by
  rw [mcsOrder_eq_regreedy, initOrder]
  exact regreedy_eq_greedySuffix a hsymm hloop ha [] List.nodup_nil
    (fun i hi => absurd hi (by simp))

end Matrix

/-! ## Refinement of the dynamic updates -/

section Refine

variable (a a' : Adj n)
  (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u) (hloop : ∀ u : ℕ, getAdj a u u = false)
  (hsymm' : ∀ u v : ℕ, getAdj a' u v = getAdj a' v u) (hloop' : ∀ u : ℕ, getAdj a' u u = false)
  (ha' : a'.length = n)

lemma mem_of_valid {G : UGraph n} {ord : List (Fin n)} (h : IsMCSOrdering G ord) (x : Fin n) :
    x ∈ ord :=
  List.mem_toFinset.1 ((order_toFinset_univ h).symm ▸ Finset.mem_univ x)

lemma idxOf_lt_of_valid {G : UGraph n} {ord : List (Fin n)} (h : IsMCSOrdering G ord) (x : Fin n) :
    ord.idxOf x < n := by
  have hlen : ord.length = n := h.2.1
  have hlt : ord.idxOf x < ord.length := List.idxOf_lt_length_of_mem (mem_of_valid h x)
  rw [hlen] at hlt
  exact hlt

include hsymm' hloop' ha' in
theorem insertProbe_map (u v : Fin n) (ord : List (Fin n))
    (hvalid : IsMCSOrdering (toUGraph a hsymm hloop) ord) :
    insertProbe a' (ord.map Fin.val) u.val v.val =
      firstBreakWindow (toUGraph a' hsymm' hloop') ord (earlierPos ord u v + 1)
        (laterPos ord u v) := by
  have he : execEarlierPos (ord.map Fin.val) u.val v.val = earlierPos ord u v := by
    simp [execEarlierPos, earlierPos, idxOf_map_val]
  have hl : execLaterPos (ord.map Fin.val) u.val v.val = laterPos ord u v := by
    simp [execLaterPos, laterPos, idxOf_map_val]
  have hu := idxOf_lt_of_valid hvalid u
  have hv := idxOf_lt_of_valid hvalid v
  have hlen : ord.length = n := hvalid.2.1
  have hel : earlierPos ord u v ≤ laterPos ord u v := by
    unfold earlierPos laterPos
    omega
  have helt : earlierPos ord u v < n := by
    unfold earlierPos
    omega
  have hwin : insertWindow (ord.map Fin.val) u.val v.val =
      ((ord.drop (earlierPos ord u v + 1)).take (laterPos ord u v - earlierPos ord u v)).map
        Fin.val := by
    rw [insertWindow, he, hl]
    simp [List.map_drop, List.map_take]
  unfold insertProbe firstBreakWindow
  rw [he, hwin, show laterPos ord u v + 1 - (earlierPos ord u v + 1) =
    laterPos ord u v - earlierPos ord u v by omega]
  refine execFirstBreak_map a' hsymm' hloop' ha' ord hvalid.1 _ _ ?_
  simp only [List.length_take, List.length_drop]
  omega

include hsymm' hloop' ha' in
/-- The executable insertion probe-and-repair computes the abstract insertion
update, for every flip of `{u, v}`. -/
theorem exec_insert_update_eq (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph a hsymm hloop) (toUGraph a' hsymm' hloop') u v)
    (hvalid : IsMCSOrdering (toUGraph a hsymm hloop) ord) :
    execInsertUpdate a' (ord.map Fin.val) u.val v.val =
      (insertUpdate (toUGraph a' hsymm' hloop') ord u v).map Fin.val := by
  have hprobe := insertProbe_map a a' hsymm hloop hsymm' hloop' ha' u v ord hvalid
  unfold execInsertUpdate
  rw [hprobe]
  cases hw : firstBreakWindow (toUGraph a' hsymm' hloop') ord (earlierPos ord u v + 1)
      (laterPos ord u v) with
  | none =>
      rw [insert_update_of_no_break u v ord hvalid hw]
  | some k =>
      have habs : insertUpdate (toUGraph a' hsymm' hloop') ord u v =
          greedySuffix (toUGraph a' hsymm' hloop') (ord.take k) := by
        simp only [insertUpdate, hw, Option.getD_some]
      have hv := insert_update_valid u v ord hflip hvalid
      rw [habs] at hv
      unfold greedySuffix at hv
      obtain ⟨hnd, hsteps⟩ := steps_of_prefix hv
      change regreedy a' ((ord.map Fin.val).take k) = _
      rw [habs, ← List.map_take]
      exact regreedy_eq_greedySuffix a' hsymm' hloop' ha' (ord.take k) hnd hsteps

include hsymm' hloop' ha' in
/-- The executable insertion update returns the from-scratch canonical
ordering of the new matrix. -/
theorem exec_insert_update_eq_mcsOrder (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph a hsymm hloop) (toUGraph a' hsymm' hloop') u v)
    (hvalid : IsMCSOrdering (toUGraph a hsymm hloop) ord) :
    execInsertUpdate a' (ord.map Fin.val) u.val v.val = mcsOrder a' := by
  rw [exec_insert_update_eq a a' hsymm hloop hsymm' hloop' ha' u v ord hflip hvalid,
    insert_update_eq_initOrder u v ord hflip hvalid,
    mcsOrder_eq_initOrder a' hsymm' hloop' ha']

include hsymm' hloop' ha' in
/-- The executable deletion probe-and-repair computes the abstract deletion
update. -/
theorem exec_delete_update_eq (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph a hsymm hloop) (toUGraph a' hsymm' hloop') u v)
    (hdel : getAdj a u.val v.val = true) (hdel' : getAdj a' u.val v.val = false)
    (hvalid : IsMCSOrdering (toUGraph a hsymm hloop) ord) :
    execDeleteUpdate a' (ord.map Fin.val) u.val v.val =
      (deleteUpdate (toUGraph a' hsymm' hloop') ord u v).map Fin.val := by
  have hdel'G : ¬ (toUGraph a' hsymm' hloop').adj u v := by
    intro h
    change getAdj a' u.val v.val = true at h
    rw [hdel'] at h
    exact Bool.false_ne_true h
  have hl : execLaterPos (ord.map Fin.val) u.val v.val = laterPos ord u v := by
    simp [execLaterPos, laterPos, idxOf_map_val]
  have hw : execLaterVert (ord.map Fin.val) u.val v.val = (laterVert ord u v).val := by
    unfold execLaterVert laterVert
    rw [idxOf_map_val, idxOf_map_val]
    split_ifs <;> rfl
  have hu := idxOf_lt_of_valid hvalid u
  have hv := idxOf_lt_of_valid hvalid v
  have hlen : ord.length = n := hvalid.2.1
  have hP : (ord.take (laterPos ord u v)).Nodup := hvalid.1.sublist (List.take_sublist _ _)
  have hPlen : (ord.take (laterPos ord u v)).length < n := by
    rw [List.length_take]
    unfold laterPos
    omega
  have hiff := pickAt_eq_iff a' hsymm' hloop' ha' _ hP hPlen (laterVert ord u v)
  have hvalid' := delete_update_valid u v ord hflip hdel hdel'G hvalid
  unfold execDeleteUpdate
  rw [hl, hw, show (ord.map Fin.val).take (laterPos ord u v) =
    (ord.take (laterPos ord u v)).map Fin.val by simp [List.map_take]]
  unfold deleteUpdate deletionBreaks UGraph.isFalse at hvalid' ⊢
  by_cases hlegal : IsMCSNext (toUGraph a' hsymm' hloop')
      (ord.take (laterPos ord u v)).toFinset (laterVert ord u v)
  · rw [hiff.2 hlegal]
    simp [hlegal]
  · simp only [hlegal, ↓reduceIte] at hvalid' ⊢
    rw [ite_eq_right (mt hiff.1 hlegal)]
    unfold greedySuffix at hvalid'
    obtain ⟨hnd, hsteps⟩ := steps_of_prefix hvalid'
    exact regreedy_eq_greedySuffix a' hsymm' hloop' ha' _ hnd hsteps

include hsymm' hloop' ha' in
/-- The executable deletion update returns the from-scratch canonical
ordering of the new matrix. -/
theorem exec_delete_update_eq_mcsOrder (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph a hsymm hloop) (toUGraph a' hsymm' hloop') u v)
    (hdel : getAdj a u.val v.val = true) (hdel' : getAdj a' u.val v.val = false)
    (hvalid : IsMCSOrdering (toUGraph a hsymm hloop) ord) :
    execDeleteUpdate a' (ord.map Fin.val) u.val v.val = mcsOrder a' := by
  have hdel'G : ¬ (toUGraph a' hsymm' hloop').adj u v := by
    intro h
    change getAdj a' u.val v.val = true at h
    rw [hdel'] at h
    exact Bool.false_ne_true h
  rw [exec_delete_update_eq a a' hsymm hloop hsymm' hloop' ha' u v ord hflip hdel hdel' hvalid,
    delete_update_eq_initOrder u v ord hflip hdel hdel'G hvalid,
    mcsOrder_eq_initOrder a' hsymm' hloop' ha']

end Refine

/-! ## Operational cost (unit-cost query model) -/

section Cost

variable (a : Adj n) (o : List ℕ)

lemma execFirstBreakC_fst : ∀ k xs, (execFirstBreakC a o k xs).1 = execFirstBreak a o k xs := by
  intro k xs
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : pickAt a (o.take k) = x
      · simp [execFirstBreakC, execFirstBreak, hx, ih]
      · simp [execFirstBreakC, execFirstBreak, hx]

lemma execFirstBreakC_snd_le : ∀ k xs, (execFirstBreakC a o k xs).2 ≤ xs.length := by
  intro k xs
  induction xs generalizing k with
  | nil => simp [execFirstBreakC]
  | cons x xs ih =>
      by_cases hx : pickAt a (o.take k) = x
      · simp only [execFirstBreakC, hx, ↓reduceIte, List.length_cons]
        have := ih (k + 1)
        omega
      · simp [execFirstBreakC, hx]

lemma execFirstBreak_some : ∀ k xs j, execFirstBreak a o k xs = some j →
    k ≤ j ∧ j < k + xs.length ∧ (execFirstBreakC a o k xs).2 = j - k + 1 := by
  intro k xs
  induction xs generalizing k with
  | nil => intro j h; simp [execFirstBreak] at h
  | cons x xs ih =>
      intro j h
      by_cases hx : pickAt a (o.take k) = x
      · simp only [execFirstBreak, hx, ↓reduceIte] at h
        obtain ⟨h1, h2, h3⟩ := ih (k + 1) j h
        simp only [execFirstBreakC, hx, ↓reduceIte, List.length_cons]
        refine ⟨by omega, by omega, ?_⟩
        rw [h3]
        omega
      · simp only [execFirstBreak, hx, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp [execFirstBreakC, hx]

lemma mcsStepC_fst (st : List ℕ × List ℕ) : (mcsStepC a st).1 = mcsStep a st := by
  rcases st with ⟨c, r⟩
  cases r <;> rfl

lemma mcsStepC_snd_le (st : List ℕ × List ℕ) : (mcsStepC a st).2 ≤ 1 := by
  rcases st with ⟨c, r⟩
  cases r <;> simp [mcsStepC]

lemma foldl_mcsStepC : ∀ (l : List ℕ) (st : List ℕ × List ℕ) (c : ℕ),
    (l.foldl (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2)) (st, c)).1 =
        l.foldl (fun s _ => mcsStep a s) st ∧
      (l.foldl (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2)) (st, c)).2 ≤
        c + l.length := by
  intro l
  induction l with
  | nil => intro st c; simp
  | cons x l ih =>
      intro st c
      simp only [List.foldl_cons, List.length_cons]
      rw [← mcsStepC_fst]
      obtain ⟨h1, h2⟩ := ih (mcsStepC a st).1 (c + (mcsStepC a st).2)
      exact ⟨h1, le_trans h2 (by have := mcsStepC_snd_le a st; omega)⟩

lemma regreedyC_fst (pref : List ℕ) : (regreedyC a pref).1 = regreedy a pref := by
  simp only [regreedyC, regreedy, (foldl_mcsStepC a _ _ 0).1]

lemma regreedyC_snd_le (pref : List ℕ) : (regreedyC a pref).2 ≤ a.length - pref.length := by
  have := (foldl_mcsStepC a (List.range (a.length - pref.length))
    (pref.reverse, remOf a.length pref) 0).2
  simp only [regreedyC]
  simpa using this

/-- The counted insertion update returns the same list as the plain update (the
count is the second projection). This is the link between the cost bounds and
the real executable update. -/
theorem exec_insert_update_c_fst (u v : ℕ) :
    (execInsertUpdateC a o u v).1 = execInsertUpdate a o u v := by
  simp only [execInsertUpdateC, execInsertUpdate, insertProbeC, insertProbe, execFirstBreakC_fst]
  cases execFirstBreak a o (execEarlierPos o u v + 1) (insertWindow o u v) with
  | none => rfl
  | some k => simp [regreedyC_fst]

/-- The counted deletion update returns the same list as the plain update. -/
theorem exec_delete_update_c_fst (u v : ℕ) :
    (execDeleteUpdateC a o u v).1 = execDeleteUpdate a o u v := by
  unfold execDeleteUpdateC execDeleteUpdate
  split_ifs <;> simp [regreedyC_fst]

lemma insertWindow_length_le (u v : ℕ) :
    (insertWindow o u v).length ≤ execLaterPos o u v - execEarlierPos o u v := by
  simp [insertWindow, List.length_take]

/-- If the insertion probe finds no break, the update costs at most the window
length `laterPos - earlierPos` and performs no regreedy. -/
theorem exec_insert_cost_of_no_break (u v : ℕ) (h : insertProbe a o u v = none) :
    (execInsertUpdateC a o u v).2 ≤ execLaterPos o u v - execEarlierPos o u v := by
  unfold insertProbe at h
  have hle := (execFirstBreakC_snd_le a o (execEarlierPos o u v + 1) (insertWindow o u v)).trans
    (insertWindow_length_le o u v)
  simp only [execInsertUpdateC, insertProbeC, execFirstBreakC_fst, h]
  exact hle

/-- If the insertion probe breaks at position `k`, the update costs the
`k - earlierPos` probe checks plus at most `n - k` regreedy steps. -/
theorem exec_insert_cost_of_break (u v k : ℕ) (h : insertProbe a o u v = some k) :
    (execInsertUpdateC a o u v).2 ≤ (k - execEarlierPos o u v) + (a.length - k) := by
  unfold insertProbe at h
  obtain ⟨hk1, hk2, hcost⟩ := execFirstBreak_some a o _ _ k h
  have hwin : (insertWindow o u v).length ≤ o.length - (execEarlierPos o u v + 1) := by
    simp [insertWindow, List.length_take, List.length_drop]
  have hko : (o.take k).length = k := by
    rw [List.length_take]
    omega
  have hr := regreedyC_snd_le a (o.take k)
  rw [hko] at hr
  simp only [execInsertUpdateC, insertProbeC, execFirstBreakC_fst, h]
  rw [hcost]
  omega

/-- If the deletion probe does not fire, the update costs exactly one check. -/
theorem exec_delete_cost_of_no_break (u v : ℕ)
    (h : pickAt a (o.take (execLaterPos o u v)) = execLaterVert o u v) :
    (execDeleteUpdateC a o u v).2 = 1 := by
  simp [execDeleteUpdateC, h]

/-- If the deletion probe fires, the update costs one check plus at most
`n - laterPos` regreedy steps. -/
theorem exec_delete_cost_of_break (u v : ℕ)
    (h : pickAt a (o.take (execLaterPos o u v)) ≠ execLaterVert o u v) :
    (execDeleteUpdateC a o u v).2 ≤ 1 + (a.length - execLaterPos o u v) := by
  have hle : execLaterPos o u v ≤ o.length := by
    unfold execLaterPos
    exact max_le (List.idxOf_le_length) (List.idxOf_le_length)
  have hr := regreedyC_snd_le a (o.take (execLaterPos o u v))
  rw [List.length_take, min_eq_left hle] at hr
  simp only [execDeleteUpdateC, h, ↓reduceIte]
  omega

/-- Worst case: an insertion costs at most `n` units (static recomputation
also costs `Θ(n)` picks). -/
theorem exec_insert_cost_le (u v : ℕ) (ho : o.length = a.length) :
    (execInsertUpdateC a o u v).2 ≤ a.length := by
  cases h : insertProbe a o u v with
  | none =>
      have := exec_insert_cost_of_no_break a o u v h
      have hle : execLaterPos o u v ≤ o.length := by
        unfold execLaterPos
        exact max_le (List.idxOf_le_length) (List.idxOf_le_length)
      omega
  | some k =>
      have := exec_insert_cost_of_break a o u v k h
      unfold insertProbe at h
      obtain ⟨hk1, hk2, -⟩ := execFirstBreak_some a o _ _ k h
      have hwin : (insertWindow o u v).length ≤ o.length - (execEarlierPos o u v + 1) := by
        simp [insertWindow, List.length_take, List.length_drop]
      omega

/-- Worst case: a deletion costs at most `n + 1` units. -/
theorem exec_delete_cost_le (u v : ℕ) :
    (execDeleteUpdateC a o u v).2 ≤ a.length + 1 := by
  by_cases h : pickAt a (o.take (execLaterPos o u v)) = execLaterVert o u v
  · rw [exec_delete_cost_of_no_break a o u v h]
    omega
  · have := exec_delete_cost_of_break a o u v h
    omega

end Cost

end Proofs
end DynamicMcs
