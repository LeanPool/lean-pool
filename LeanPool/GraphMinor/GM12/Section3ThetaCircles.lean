/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph
public import LeanPool.GraphMinor.GM12.Section3CircleInclusion
import LeanPool.GraphMinor.GM11.Ties

/-!
# Circles in the three-branch shape

The third schismatic shape in VII Section 8, used by XII (3.1), page
245, consists of three lines with common ends and otherwise disjoint.
It is a finite graph with exactly those lines as edges. A circle either
contains a whole branch or misses its interior. It must contain two
branches, since a circle cannot lie in a line. The two branches already
form a circle, so they are the entire circle under consideration.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Three internally disjoint lines with common distinct ends form
a finite graph whose edges are precisely the three branches. -/
theorem isGraph_three_branches
    {S : Type*} [TopologicalSpace S] {P Q R : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v}) :
    IsGraph ({u, v} : Set S) {P, Q, R} := by
  have he : ∀ L : Set S, IsLineWithEnds L u v → L ∩ {u, v} = {u, v} := by
    intro L hL
    apply inter_eq_right.mpr
    rintro x (hxu | hxv)
    · exact hxu.symm ▸ hL.left_mem
    · exact hxv.symm ▸ hL.right_mem
  refine ⟨(finite_singleton v).insert u, ((finite_singleton R).insert Q).insert P, ?_, ?_⟩
  · rintro L (rfl | rfl | rfl)
    · exact ⟨u, v, huv, hP, he _ hP⟩
    · exact ⟨u, v, huv, hQ, he _ hQ⟩
    · exact ⟨u, v, huv, hR, he _ hR⟩
  · rintro L (rfl | rfl | rfl) M (rfl | rfl | rfl) hne
    · exact (hne rfl).elim
    · exact hPQ.le
    · exact hPR.le
    · rw [inter_comm]
      exact hPQ.le
    · exact (hne rfl).elim
    · exact hQR.le
    · rw [inter_comm]
      exact hPR.le
    · rw [inter_comm]
      exact hQR.le
    · exact (hne rfl).elim

private theorem not_circle_of_misses_two_branches
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {L M N Z : Set S} {u v : S} (hL : IsLineWithEnds L u v) (hZ : IsOArc Z)
    (hcover : Z ⊆ L ∪ M ∪ N)
    (hM : Disjoint (M \ {u, v}) Z) (hN : Disjoint (N \ {u, v}) Z) : False := by
  apply GM11.not_isOArc_of_subset_line ⟨hL.choose⟩ hZ
  intro x hxZ
  have hends : x ∈ ({u, v} : Set S) → x ∈ L := by
    rintro (hxu | hxv)
    · exact hxu.symm ▸ hL.left_mem
    · exact hxv.symm ▸ hL.right_mem
  rcases hcover hxZ with (hxL | hxM) | hxN
  · exact hxL
  · by_cases hxV : x ∈ ({u, v} : Set S)
    · exact hends hxV
    · exact (Set.disjoint_left.mp hM ⟨hxM, hxV⟩ hxZ).elim
  · by_cases hxV : x ∈ ({u, v} : Set S)
    · exact hends hxV
    · exact (Set.disjoint_left.mp hN ⟨hxN, hxV⟩ hxZ).elim

/-- Two lines with common distinct ends and no other common point
form a circle. The parametrizations agree at their ends and nowhere
else, so the two-arc circle construction applies. -/
theorem isOArc_union_of_lines_inter_eq_ends
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {P Q : Set S} {u v : S}
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v)
    (hPQ : P ∩ Q = {u, v}) : IsOArc (P ∪ Q) := by
  obtain ⟨φ, hφ0, hφ1⟩ := hP
  obtain ⟨ψ, hψ0, hψ1⟩ := hQ
  let a : unitInterval → S := fun t => (φ t).val
  let b : unitInterval → S := fun t => (ψ t).val
  have ha : IsArcMap a := ⟨continuous_subtype_val.comp φ.continuous,
    fun s t he => φ.injective (Subtype.ext he)⟩
  have hb : IsArcMap b := ⟨continuous_subtype_val.comp ψ.continuous,
    fun s t he => ψ.injective (Subtype.ext he)⟩
  have hi : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hx : a s ∈ P ∩ Q := ⟨(φ s).property, he.symm ▸ (ψ t).property⟩
    rw [hPQ] at hx
    rcases hx with hxu | hxv
    · exact Or.inl ⟨ha.2 (hxu.trans hφ0.symm), hb.2 (he.symm.trans (hxu.trans hψ0.symm))⟩
    · exact Or.inr ⟨ha.2 (hxv.trans hφ1.symm), hb.2 (he.symm.trans (hxv.trans hψ1.symm))⟩
  have ho := oArc_of_two_arcs ha hb (hφ0.trans hψ0.symm) (hφ1.trans hψ1.symm) hi
  have hrP : range a = P := (φ.surjective.range_comp Subtype.val).trans Subtype.range_val
  have hrQ : range b = Q := (ψ.surjective.range_comp Subtype.val).trans Subtype.range_val
  rw [hrP, hrQ] at ho
  exact ho

/-- The only circles in the three-branch shape are its three pairs
of branches. This proves the circle-classification step needed for the
minimal-circle clause of VII's third schismatic shape. -/
theorem oArc_eq_pair_of_three_branches
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {P Q R Z : Set S} {u v : S} (huv : u ≠ v)
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    (hZ : IsOArc Z) (hZY : Z ⊆ P ∪ Q ∪ R) :
    Z = P ∪ Q ∨ Z = P ∪ R ∨ Z = Q ∪ R := by
  classical
  have hoPQ := isOArc_union_of_lines_inter_eq_ends hP hQ hPQ
  have hoPR := isOArc_union_of_lines_inter_eq_ends hP hR hPR
  have hoQR := isOArc_union_of_lines_inter_eq_ends hQ hR hQR
  have hG := isGraph_three_branches huv hP hQ hR hPQ hPR hQR
  have hZG : Z ⊆ gr ({u, v} : Set S) {P, Q, R} := by
    intro x hx
    rcases hZY hx with (hxP | hxQ) | hxR
    · exact Or.inr ⟨P, Or.inl rfl, hxP⟩
    · exact Or.inr ⟨Q, Or.inr (Or.inl rfl), hxQ⟩
    · exact Or.inr ⟨R, Or.inr (Or.inr rfl), hxR⟩
  have hm : ∀ L ∈ ({P, Q, R} : Set (Set S)), ¬ L ⊆ Z → Disjoint (L \ {u, v}) Z :=
    fun L hL hn => (hG.edge_or hZ hZG hL).resolve_left hn
  by_cases hPZ : P ⊆ Z
  · by_cases hQZ : Q ⊆ Z
    · exact Or.inl (oArc_eq_of_subset hoPQ hZ (union_subset hPZ hQZ)).symm
    · by_cases hRZ : R ⊆ Z
      · exact Or.inr (Or.inl (oArc_eq_of_subset hoPR hZ (union_subset hPZ hRZ)).symm)
      · exact (not_circle_of_misses_two_branches hP hZ hZY
          (hm Q (Or.inr (Or.inl rfl)) hQZ) (hm R (Or.inr (Or.inr rfl)) hRZ)).elim
  · by_cases hQZ : Q ⊆ Z
    · by_cases hRZ : R ⊆ Z
      · exact Or.inr (Or.inr (oArc_eq_of_subset hoQR hZ (union_subset hQZ hRZ)).symm)
      · have hcover : Z ⊆ Q ∪ P ∪ R := by rwa [union_comm Q P]
        exact (not_circle_of_misses_two_branches hQ hZ hcover
          (hm P (Or.inl rfl) hPZ) (hm R (Or.inr (Or.inr rfl)) hRZ)).elim
    · have hcover : Z ⊆ R ∪ P ∪ Q := by rwa [union_assoc, union_comm R (P ∪ Q)]
      exact (not_circle_of_misses_two_branches hR hZ hcover
        (hm P (Or.inl rfl) hPZ) (hm Q (Or.inr (Or.inl rfl)) hQZ)).elim

end GraphMinor.GM12
