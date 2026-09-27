/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **conservation law** behind the fine block-allocation residual

`Nibble.AX1.BlockCoverResidualFine` (`Nibble.CoreGapBlockCover`) asks for a family of block
sub-triples with pairwise disjoint vertex-pair rectangles whose density-weighted area recovers
`ν₃*` of the regularity-reduced graph up to `ε|V|²`.  This file proves the *exact ceiling* of any
such family, with no hypothesis at all beyond the geometry:

> **`Nibble.AX1.cover_sum_le_cluster_capacity`.**  If the members of a family of block sub-triples
> sit on pairwise distinct clusters of `P` and have pairwise disjoint vertex-pair rectangles, then
> its covering sum is at most `(1/3)·∑_{cluster pairs} d(S,T)·#S·#T`.

The right-hand side is precisely the value of the linear-programming relaxation of the fractional
triangle packing LP of the weighted cluster graph — the same quantity that caps `ν₃*` of the reduced
graph through the capacity constraint `Nibble.AX1.sum_fracPacking_cluster_pair_le`
(`Nibble.CoreGapClusterCapacity`), and which `ν₃*` **attains** for the complete graph
(`Nibble.AX1.nu3star_fivePartite_ge`, `Nibble.CoreGapBlockCoverRefute`).

So the fine residual carries **no slack whatsoever**: closing it is exactly the problem of realising
a near-optimal solution of the cluster capacity LP by disjoint rectangles, and every lossy
allocation — in particular every allocation that leaves a constant fraction of the area of a cluster
pair unused — necessarily fails.  Together with
`Nibble.AX1.not_blockCoverResidualFineClusterPacking` (`Nibble.CoreGapClusterPackingRefute`), which
rules out cluster-edge-disjoint families, this delimits what a construction can look like.

The proof is a two-step accounting.  Each member `i` contributes, to the ordered cluster pair
`(S, T)`, the area `#(Rᵢ ∩ (S ×ˢ T))` of its rectangle set inside that pair; because the three
clusters of a member are distinct parts of `P`, the six ordered pairs it uses are distinct and pick
up twice each of its three rectangle areas.  Summing in the other order, for a fixed ordered pair
the rectangle sets are pairwise disjoint subsets of `S ×ˢ T`, so their areas add up to at most
`#S·#T`.

* `Nibble.AX1.pairArea` — the density-weighted area a rectangle set occupies in an ordered pair;
* `Nibble.AX1.sum_card_inter_le` — disjoint sets meet a fixed set in at most its cardinality;
* `Nibble.AX1.two_cover_le_sum_pairArea` — the six-term lower bound for a single member;
* `Nibble.AX1.cover_sum_le_cluster_capacity` — the conservation law.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockCover

/-! # CoreGapCoverCapacity -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The six rectangles of a block sub-triple -/

theorem prod_subset_tripleRect_AB (A B C : Finset V) : (A ×ˢ B) ⊆ tripleRect A B C :=
  (Finset.subset_union_left.trans Finset.subset_union_left).trans Finset.subset_union_left

theorem prod_subset_tripleRect_BA (A B C : Finset V) : (B ×ˢ A) ⊆ tripleRect A B C :=
  (Finset.subset_union_right.trans Finset.subset_union_left).trans Finset.subset_union_left

theorem prod_subset_tripleRect_AC (A B C : Finset V) : (A ×ˢ C) ⊆ tripleRect A B C :=
  (Finset.subset_union_left.trans Finset.subset_union_right).trans Finset.subset_union_left

theorem prod_subset_tripleRect_CA (A B C : Finset V) : (C ×ˢ A) ⊆ tripleRect A B C :=
  (Finset.subset_union_right.trans Finset.subset_union_right).trans Finset.subset_union_left

theorem prod_subset_tripleRect_BC (A B C : Finset V) : (B ×ˢ C) ⊆ tripleRect A B C :=
  Finset.subset_union_left.trans Finset.subset_union_right

theorem prod_subset_tripleRect_CB (A B C : Finset V) : (C ×ˢ B) ⊆ tripleRect A B C :=
  Finset.subset_union_right.trans Finset.subset_union_right

/-! ### The density-weighted area occupied in one ordered cluster pair -/

/-- **The density-weighted area a rectangle set occupies inside the ordered cluster pair `p`.** -/
noncomputable def pairArea (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset (V × V))
    (p : Finset V × Finset V) : ℝ :=
  (G.edgeDensity p.1 p.2 : ℝ) * (#(R ∩ (p.1 ×ˢ p.2)) : ℝ)

theorem pairArea_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset (V × V))
    (p : Finset V × Finset V) : 0 ≤ pairArea G R p := by
  have : (0 : ℝ) ≤ (G.edgeDensity p.1 p.2 : ℝ) := by exact_mod_cast G.edgeDensity_nonneg p.1 p.2
  exact mul_nonneg this (Nat.cast_nonneg _)

/-- A rectangle inside the ordered pair `(S, T)` contributes at most the pair's occupied area. -/
theorem rect_le_pairArea (G : SimpleGraph V) [DecidableRel G.Adj] {R : Finset (V × V)}
    {S T D E : Finset V} (hDS : D ⊆ S) (hET : E ⊆ T) (hDE : (D ×ˢ E) ⊆ R) :
    (G.edgeDensity S T : ℝ) * (#D : ℝ) * (#E : ℝ) ≤ pairArea G R (S, T) := by
  have hsub : (D ×ˢ E) ⊆ R ∩ (S ×ˢ T) :=
    Finset.subset_inter hDE (Finset.product_subset_product hDS hET)
  have hcard : (#D : ℝ) * (#E : ℝ) ≤ (#(R ∩ (S ×ˢ T)) : ℝ) := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_product] at h
    exact_mod_cast h
  have hd : (0 : ℝ) ≤ (G.edgeDensity S T : ℝ) := by exact_mod_cast G.edgeDensity_nonneg S T
  calc (G.edgeDensity S T : ℝ) * (#D : ℝ) * (#E : ℝ)
      = (G.edgeDensity S T : ℝ) * ((#D : ℝ) * (#E : ℝ)) := by ring
    _ ≤ pairArea G R (S, T) := by
        exact mul_le_mul_of_nonneg_left hcard hd

/-- **Pairwise disjoint sets meet a fixed set in at most its cardinality.** -/
theorem sum_card_inter_le (R : ℕ → Finset (V × V)) (F : Finset ℕ) (S : Finset (V × V))
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j)) :
    ∑ i ∈ F, (#(R i ∩ S) : ℝ) ≤ (#S : ℝ) := by
  classical
  have hcard : ∑ i ∈ F, #(R i ∩ S) = #(F.biUnion fun i => R i ∩ S) :=
    (Finset.card_biUnion fun i hi j hj hij =>
      (hdisj i hi j hj hij).mono Finset.inter_subset_left Finset.inter_subset_left).symm
  have hsub : (F.biUnion fun i => R i ∩ S) ⊆ S := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.1 hx
    exact (Finset.mem_inter.1 hxi).2
  have h : ∑ i ∈ F, #(R i ∩ S) ≤ #S := by
    rw [hcard]; exact Finset.card_le_card hsub
  exact_mod_cast h

/-- **The six-term lower bound.**  Twice the (undivided) covering sum of one block sub-triple is
picked up by the six ordered cluster pairs it occupies. -/
theorem two_cover_le_sum_pairArea (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {U W X A B C : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hX : X ∈ P.parts)
    (hUW : U ≠ W) (hUX : U ≠ X) (hWX : W ≠ X)
    (hA : A ⊆ U) (hB : B ⊆ W) (hC : C ⊆ X) :
    2 * ((G.edgeDensity U W : ℝ) * (#A : ℝ) * (#B : ℝ)
        + (G.edgeDensity U X : ℝ) * (#A : ℝ) * (#C : ℝ)
        + (G.edgeDensity W X : ℝ) * (#B : ℝ) * (#C : ℝ))
      ≤ ∑ p ∈ P.parts.offDiag, pairArea G (tripleRect A B C) p := by
  classical
  set s6 : Finset (Finset V × Finset V) := {(U, W), (W, U), (U, X), (X, U), (W, X), (X, W)}
    with hs6def
  have hsub6 : s6 ⊆ P.parts.offDiag := by
    intro p hp
    simp only [hs6def, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Finset.mem_offDiag, hU, hW, hX, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]
  have hsumsub : ∑ p ∈ s6, pairArea G (tripleRect A B C) p
      ≤ ∑ p ∈ P.parts.offDiag, pairArea G (tripleRect A B C) p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub6 fun p _ _ => pairArea_nonneg _ _ _
  have hs6 : ∑ p ∈ s6, pairArea G (tripleRect A B C) p =
      pairArea G (tripleRect A B C) (U, W) + pairArea G (tripleRect A B C) (W, U)
        + pairArea G (tripleRect A B C) (U, X) + pairArea G (tripleRect A B C) (X, U)
        + pairArea G (tripleRect A B C) (W, X) + pairArea G (tripleRect A B C) (X, W) := by
    rw [hs6def]
    rw [Finset.sum_insert (by simp [Prod.ext_iff, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]),
      Finset.sum_insert (by simp [Prod.ext_iff, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]),
      Finset.sum_insert (by simp [Prod.ext_iff, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]),
      Finset.sum_insert (by simp [Prod.ext_iff, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]),
      Finset.sum_insert (by simp [Prod.ext_iff, hUW, hUX, hWX, hUW.symm, hUX.symm, hWX.symm]),
      Finset.sum_singleton]
    ring
  have h1 := rect_le_pairArea G hA hB (prod_subset_tripleRect_AB A B C)
  have h2 := rect_le_pairArea G hB hA (prod_subset_tripleRect_BA A B C)
  have h3 := rect_le_pairArea G hA hC (prod_subset_tripleRect_AC A B C)
  have h4 := rect_le_pairArea G hC hA (prod_subset_tripleRect_CA A B C)
  have h5 := rect_le_pairArea G hB hC (prod_subset_tripleRect_BC A B C)
  have h6 := rect_le_pairArea G hC hB (prod_subset_tripleRect_CB A B C)
  rw [show ((G.edgeDensity W U : ℝ)) = ((G.edgeDensity U W : ℝ)) by
    rw [SimpleGraph.edgeDensity_comm]] at h2
  rw [show ((G.edgeDensity X U : ℝ)) = ((G.edgeDensity U X : ℝ)) by
    rw [SimpleGraph.edgeDensity_comm]] at h4
  rw [show ((G.edgeDensity X W : ℝ)) = ((G.edgeDensity W X : ℝ)) by
    rw [SimpleGraph.edgeDensity_comm]] at h6
  rw [hs6] at hsumsub
  linarith

/-- **The conservation law of the fine block-allocation residual.**  A family of block sub-triples
whose three clusters are distinct parts of `P` and whose vertex-pair rectangles are pairwise
disjoint has covering sum at most one third of the total capacity `∑ d(S,T)·#S·#T` of the cluster
pairs (the sum on the right runs over *ordered* pairs, whence the `6`). -/
theorem cover_sum_le_cluster_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    (k : ℕ) (U W X A B C : ℕ → Finset V)
    (hU : ∀ i < k, U i ∈ P.parts) (hW : ∀ i < k, W i ∈ P.parts) (hX : ∀ i < k, X i ∈ P.parts)
    (hUW : ∀ i < k, U i ≠ W i) (hUX : ∀ i < k, U i ≠ X i) (hWX : ∀ i < k, W i ≠ X i)
    (hA : ∀ i < k, A i ⊆ U i) (hB : ∀ i < k, B i ⊆ W i) (hC : ∀ i < k, C i ⊆ X i)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    ∑ i ∈ Finset.range k, ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
        + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
        + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
      ≤ (∑ p ∈ P.parts.offDiag, (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)) / 6 := by
  classical
  have step2 : ∀ p ∈ P.parts.offDiag,
      ∑ i ∈ Finset.range k, pairArea G (tripleRect (A i) (B i) (C i)) p
        ≤ (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
    intro p _
    have hd : (0 : ℝ) ≤ (G.edgeDensity p.1 p.2 : ℝ) := by
      exact_mod_cast G.edgeDensity_nonneg p.1 p.2
    have harea : ∑ i ∈ Finset.range k,
        (#(tripleRect (A i) (B i) (C i) ∩ (p.1 ×ˢ p.2)) : ℝ) ≤ (#(p.1 ×ˢ p.2) : ℝ) :=
      sum_card_inter_le (fun i => tripleRect (A i) (B i) (C i)) (Finset.range k) _
        (fun i hi j hj hij => hdisj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
    calc ∑ i ∈ Finset.range k, pairArea G (tripleRect (A i) (B i) (C i)) p
        = (G.edgeDensity p.1 p.2 : ℝ) * ∑ i ∈ Finset.range k,
            (#(tripleRect (A i) (B i) (C i) ∩ (p.1 ×ˢ p.2)) : ℝ) := by
          rw [Finset.mul_sum]; rfl
      _ ≤ (G.edgeDensity p.1 p.2 : ℝ) * (#(p.1 ×ˢ p.2) : ℝ) := mul_le_mul_of_nonneg_left harea hd
      _ = (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
          rw [Finset.card_product]; push_cast; ring
  have hcomb : ∑ i ∈ Finset.range k,
      2 * ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
        + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
        + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))
      ≤ ∑ p ∈ P.parts.offDiag, (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
    calc ∑ i ∈ Finset.range k,
          2 * ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ ∑ i ∈ Finset.range k,
            ∑ p ∈ P.parts.offDiag, pairArea G (tripleRect (A i) (B i) (C i)) p := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik := Finset.mem_range.1 hi
          exact two_cover_le_sum_pairArea G P (hU i hik) (hW i hik) (hX i hik) (hUW i hik)
            (hUX i hik) (hWX i hik) (hA i hik) (hB i hik) (hC i hik)
      _ = ∑ p ∈ P.parts.offDiag,
            ∑ i ∈ Finset.range k, pairArea G (tripleRect (A i) (B i) (C i)) p := Finset.sum_comm
      _ ≤ ∑ p ∈ P.parts.offDiag, (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) :=
          Finset.sum_le_sum step2
  rw [← Finset.mul_sum] at hcomb
  rw [← Finset.sum_div]
  linarith only [hcomb]

end Nibble.AX1
