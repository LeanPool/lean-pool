/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.SmallCase

/-!
# Counting high-degree vertices without a high-degree triangle

The high-degree vertices span a triangle-free graph. A common-neighbour
count at the ends of one edge gives the exact `-4` correction needed later.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

private theorem highNeighbor_lower (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (Vb : Finset V)
    (hVb : Vb = Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v))
    {v : V} (hv : v ∈ Vb) :
    G.minDegree + 2 + Vb.card - Fintype.card V ≤
      (G.neighborFinset v ∩ Vb).card := by
  have hvdeg : G.minDegree + 2 ≤ G.degree v := by
    rw [hVb] at hv
    exact (Finset.mem_filter.mp hv).2
  have hsub : G.neighborFinset v \ Vb ⊆ Finset.univ \ Vb := by
    simp [Finset.sdiff_subset_sdiff]
  have hout : (G.neighborFinset v \ Vb).card ≤ Fintype.card V - Vb.card := by
    calc
      (G.neighborFinset v \ Vb).card ≤ (Finset.univ \ Vb).card :=
        Finset.card_le_card hsub
      _ = Fintype.card V - Vb.card := by simp [Finset.card_sdiff]
  have hunion : G.neighborFinset v =
      (G.neighborFinset v ∩ Vb) ∪ (G.neighborFinset v \ Vb) := by
    ext x
    simp
    tauto
  have hdisj : Disjoint (G.neighborFinset v ∩ Vb) (G.neighborFinset v \ Vb) := by
    rw [Finset.disjoint_left]
    intro x hx hxn
    exact (Finset.mem_sdiff.mp hxn).2 (Finset.mem_inter.mp hx).2
  have hcard : (G.neighborFinset v).card =
      (G.neighborFinset v ∩ Vb).card + (G.neighborFinset v \ Vb).card := by
    conv_lhs => rw [hunion]
    rw [Finset.card_union_of_disjoint hdisj]
  have hdeg : G.degree v = (G.neighborFinset v).card := rfl
  have hVb_bound : Vb.card ≤ Fintype.card V := Finset.card_le_univ Vb
  omega

/-- Without a triangle whose three vertices have degree at least
`minDegree + 2`, the number of such vertices is at most twice the
deficiency minus four, provided the deficiency is at least two. -/
public theorem nb_bound_tight (G : SimpleGraph V) [DecidableRel G.Adj]
    (_h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (_hn20 : 20 ≤ Fintype.card V)
    (hdef2 : 2 ≤ Fintype.card V - G.minDegree)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    (Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card
      ≤ 2 * (Fintype.card V - G.minDegree) - 4 := by
  classical
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVb
  by_cases hVb_empty : Vb.card = 0
  · rw [hVb_empty]
    omega
  · by_contra hbad
    push Not at hbad
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hVb_empty)
    have hv_lower := highNeighbor_lower G Vb hVb hv
    have hv_pos : 0 < (G.neighborFinset v ∩ Vb).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hv_pos
    have huv : G.Adj v u := (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1
    have huVb : u ∈ Vb := (Finset.mem_inter.mp hu).2
    have hu_lower := highNeighbor_lower G Vb hVb huVb
    have hdisjoint : Disjoint (G.neighborFinset u ∩ Vb) (G.neighborFinset v ∩ Vb) := by
      rw [Finset.disjoint_left]
      intro w hwu hwv
      have hwu' := Finset.mem_inter.mp hwu
      have hwv' := Finset.mem_inter.mp hwv
      have hdu : G.minDegree + 2 ≤ G.degree u := by
        rw [hVb] at huVb
        exact (Finset.mem_filter.mp huVb).2
      have hdv : G.minDegree + 2 ≤ G.degree v := by
        rw [hVb] at hv
        exact (Finset.mem_filter.mp hv).2
      have hdw : G.minDegree + 2 ≤ G.degree w := by
        rw [hVb] at hwu'
        exact (Finset.mem_filter.mp hwu'.2).2
      exact hNoHDT u v w huv.symm
        ((G.mem_neighborFinset u w).mp hwu'.1)
        ((G.mem_neighborFinset v w).mp hwv'.1) hdu hdv hdw
    have hUnion_sub :
        (G.neighborFinset u ∩ Vb) ∪ (G.neighborFinset v ∩ Vb) ⊆ Vb := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxu | hxv
      · exact (Finset.mem_inter.mp hxu).2
      · exact (Finset.mem_inter.mp hxv).2
    have hUnion_card :
        ((G.neighborFinset u ∩ Vb) ∪ (G.neighborFinset v ∩ Vb)).card =
          (G.neighborFinset u ∩ Vb).card + (G.neighborFinset v ∩ Vb).card :=
      Finset.card_union_of_disjoint hdisjoint
    have hVb_card_ge : Vb.card ≥ (G.neighborFinset u ∩ Vb).card +
        (G.neighborFinset v ∩ Vb).card := by
      rw [← hUnion_card]
      exact Finset.card_le_card hUnion_sub
    omega

end LeanPool.DrossFractionalTriangleDecomposition
