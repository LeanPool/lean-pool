/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaSchismatic

/-!
# Each pair circle is proper in a theta

For VII Section 8's third schismatic shape, used by XII (3.1), page
245, the minimal-circle clause applies to each pair of branches. The
opposite line has a midpoint which is neither end, so it cannot lie in
the pair. Thus each pair is a proper subset, and all three pair circles
of a schismatic theta are near-planar.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem line_not_subset_ends
    {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) : ¬ L ⊆ {u, v} := by
  obtain ⟨e, he0, he1⟩ := hL
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  have ht0 : t ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [t] at hv
  have ht1 : t ≠ 1 := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [t] at hv
  intro hsub
  rcases hsub (e t).property with htu | htv
  · exact ht0 (e.injective (Subtype.ext (htu.trans he0.symm)))
  · exact ht1 (e.injective (Subtype.ext (htv.trans he1.symm)))

/-- The opposite branch has an interior point outside the other two,
so their union is a proper subset of all three branches. -/
theorem pair_strict_subset_three_branches
    {S : Type*} [TopologicalSpace S] {P Q R : Set S} {u v : S}
    (hR : IsLineWithEnds R u v)
    (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v}) :
    P ∪ Q ⊂ P ∪ Q ∪ R := by
  refine ⟨subset_union_left, ?_⟩
  intro hsub
  apply line_not_subset_ends hR
  intro x hx
  rcases hsub (Or.inr hx) with hxP | hxQ
  · exact hPR ▸ (show x ∈ P ∩ R from ⟨hxP, hx⟩)
  · exact hQR ▸ (show x ∈ Q ∩ R from ⟨hxQ, hx⟩)

/-- All three pair circles of a schismatic theta are near-planar.
This discharges the proper-subset premise in VII Section 8's definition. -/
theorem nearPlanar_pairs_of_schismatic_theta
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {P Q R : Set S} {u v : S}
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hPQ : P ∩ Q = {u, v}) (hPR : P ∩ R = {u, v}) (hQR : Q ∩ R = {u, v})
    (hX : GM07.IsSchismatic (P ∪ Q ∪ R)) :
    GM07.IsNearPlanar (P ∪ Q) ∧ GM07.IsNearPlanar (P ∪ R) ∧ GM07.IsNearPlanar (Q ∪ R) := by
  have hQP : Q ∩ P = {u, v} := (inter_comm Q P).trans hPQ
  have hRP : R ∩ P = {u, v} := (inter_comm R P).trans hPR
  have hRQ : R ∩ Q = {u, v} := (inter_comm R Q).trans hQR
  refine ⟨hX.2.2 _ (isOArc_union_of_lines_inter_eq_ends hP hQ hPQ)
    (pair_strict_subset_three_branches hR hPR hQR), ?_, ?_⟩
  · apply hX.2.2 _ (isOArc_union_of_lines_inter_eq_ends hP hR hPR)
    simpa only [union_right_comm] using pair_strict_subset_three_branches hQ hPQ hRQ
  · apply hX.2.2 _ (isOArc_union_of_lines_inter_eq_ends hQ hR hQR)
    simpa only [union_assoc, union_left_comm, union_comm] using
      pair_strict_subset_three_branches hP hQP hRP

end GraphMinor.GM12
