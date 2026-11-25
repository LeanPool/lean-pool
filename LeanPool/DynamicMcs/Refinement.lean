/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

import Mathlib.Tactic.Push
public import LeanPool.DynamicMcs.McsInvariant

/-!
# Refinement of executable maximum-cardinality search

A canonical prefix extends under the Boolean-matrix implementation to the
same ordering as abstract greedy search. The empty prefix gives correctness
of recomputation from scratch.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs

open UGraph

variable {n : ℕ}

namespace Proofs

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

lemma cardC_reverse (a : Adj) (l : List ℕ) (w : ℕ) : cardC a l.reverse w = cardC a l w := by
  simp [cardC, List.filter_reverse]

lemma bestPick_reverse (a : Adj) (l rem : List ℕ) :
    bestPick a l.reverse rem = bestPick a l rem := by
  unfold bestPick better
  simp only [cardC_reverse]

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

/-! ## The executable pick is the canonical pick -/

section Matrix

variable (a : Adj) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
  (hloop : ∀ u : ℕ, getAdj a u u = false) (ha : a.length = n)

include hsymm hloop ha in
theorem pickAt_spec (P : List (Fin n)) (hP : P.Nodup) (hlt : P.length < n) :
    ∃ w : Fin n, pickAt a (P.map Fin.val) = w.val ∧
      IsMCSNext (toUGraph (n := n) a hsymm hloop) P.toFinset w := by
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
    pickAt a (P.map Fin.val) = x.val ↔
      IsMCSNext (toUGraph (n := n) a hsymm hloop) P.toFinset x := by
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
        firstBreakAux (toUGraph (n := n) a hsymm hloop) ord k xs := by
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
      by_cases hx : IsMCSNext (toUGraph (n := n) a hsymm hloop) (ord.take k).toFinset x
      · simp only [hiff.2 hx, hx, ↓reduceIte]
        exact ih (k + 1) (by omega)
      · simp only [mt hiff.1 hx, hx, ↓reduceIte]

include hsymm hloop ha in
lemma regreedy_inv (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph (n := n) a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    ∀ j, pref.length + j ≤ n → ∃ P : List (Fin n), P.length = pref.length + j ∧ P.Nodup ∧
      (∀ i (hi : i < P.length),
        IsMCSNext (toUGraph (n := n) a hsymm hloop) (P.take i).toFinset (P.get ⟨i, hi⟩)) ∧
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
        rw [McsInvariant.mcsStep_eq a _ _ hrem, bestPick_reverse]
        have hpick : bestPick a (P.map Fin.val) (remOf a.length (P.map Fin.val)) = w.val := hw
        rw [hpick, remOf_erase]
        simp

include hsymm hloop ha in
/-- The executable regreedy from a canonical prefix returns a canonical
ordering. -/
theorem regreedy_spec (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph (n := n) a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    ∃ ord : List (Fin n), IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord ∧
      regreedy a (pref.map Fin.val) = ord.map Fin.val := by
  have hle : pref.length ≤ n := by simpa using hnd.length_le_card
  obtain ⟨P, hlen, hPnd, hPsteps, hfold⟩ :=
    regreedy_inv a hsymm hloop ha pref hnd hsteps (n - pref.length) (by omega)
  refine ⟨P, ⟨hPnd, by omega, hPsteps⟩, ?_⟩
  unfold regreedy mcsFinish
  rw [List.length_map, show a.length - pref.length = n - pref.length by rw [ha], hfold]
  simp

include hsymm hloop ha in
theorem regreedy_eq_greedySuffix (pref : List (Fin n)) (hnd : pref.Nodup)
    (hsteps : ∀ i (hi : i < pref.length),
      IsMCSNext (toUGraph (n := n) a hsymm hloop) (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    regreedy a (pref.map Fin.val) =
      (greedySuffix (toUGraph (n := n) a hsymm hloop) pref).map Fin.val := by
  obtain ⟨ord, hord, heq⟩ := regreedy_spec a hsymm hloop ha pref hnd hsteps
  rw [heq, IsMCSOrdering_unique hord (UGraph.greedySuffix_valid _ pref hnd hsteps)]

lemma mcsOrder_eq_regreedy : mcsOrder a = regreedy a [] := by
  simp [mcsOrder, regreedy, remOf]

include hsymm hloop ha in
/-- The executable from-scratch ordering is the canonical ordering. -/
theorem mcsOrder_eq_initOrder :
    mcsOrder a = (initOrder (toUGraph (n := n) a hsymm hloop)).map Fin.val := by
  rw [mcsOrder_eq_regreedy, initOrder]
  exact regreedy_eq_greedySuffix a hsymm hloop ha [] List.nodup_nil
    (fun i hi => absurd hi (by simp))

end Matrix

end Proofs

namespace ExecBridge

/-- The executable ordering is a canonical ordering of the matrix graph. -/
theorem mcsOrder_eq_greedySuffix
    (a : Adj)
    (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false)
    (ha_len : a.length = n) :
    let G := toUGraph (n := n) a hsymm hloop
    ∃ (ord : List (Vert n)),
      UGraph.IsMCSOrdering G ord ∧
      ord.map (fun v => v.val) = mcsOrder a := by
  obtain ⟨ord, valid, computed⟩ :=
    Proofs.regreedy_spec a hsymm hloop ha_len [] List.nodup_nil (fun i hi => by simp at hi)
  exact ⟨ord, valid, computed.symm.trans (Proofs.mcsOrder_eq_regreedy a).symm⟩

end ExecBridge

end DynamicMcs
