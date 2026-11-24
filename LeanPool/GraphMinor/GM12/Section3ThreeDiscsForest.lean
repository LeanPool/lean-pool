/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3GeometricReduction
public import LeanPool.GraphMinor.GM12.Section3ForestAlphaReduction
import LeanPool.GraphMinor.GM12.Section3CandidateExistence
public import LeanPool.GraphMinor.GM12.Section3SmallCircleConditions
public import LeanPool.GraphMinor.GM12.Section3MeetingCircleCondition
public import LeanPool.GraphMinor.GM12.Section3JoinedCircleCondition
public import LeanPool.GraphMinor.GM12.Section3ThetaCondition

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The three-disc case with a supplied feasibility forest

In the two-disc case of XII (3.2), page 247, add an auxiliary disc
away from the boundary-connection forest. The three-disc argument
then uses this same forest in the VII reduction. This file records
that form of the argument, using the five geometric checks already
proved for (3.2).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

universe u

/-- The three-disc case of XII (3.2), with the forest used in the
VII (7.5) reduction supplied explicitly. -/
theorem theorem_3_2_three_discs_of_forest
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Γ K : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Drawing S → Set S) (Δ r : Fin 3 → Set S) (p : ℕ) (Zs : Fin p → Set S),
      GM10.IsTangle Γ.toHypergraph θ T →
      (PaintingOrDrawing.drawing Γ).IsRespectful θ T →
      (PaintingOrDrawing.drawing Γ).IsRadialDrawing K →
      IsDerivedSlope (.drawing Γ) K θ T ins → η ≤ θ →
      (∀ i, IsClosedDisc (Δ i)) → Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      (∀ i, r i ∈ Γ.R) → (∀ i, (r i ∩ Δ i).Nonempty) →
      (∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → ∀ (H : Drawing (discComplement Δ)),
        GM07.IsSurfaceForest H →
      H.V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' ⋃ j, Zs j →
      (∀ j, ∀ x ∈ (Subtype.val : discComplement Δ → S) ⁻¹' Zs j,
        ∀ y ∈ H.V ∩ bd (discComplement Δ),
          Nonempty (GraphWalk H.toGraph x y) ↔ y.val ∈ Zs j) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  have hcase : ¬ IsSphere S ∨ 3 ≤ 3 := Or.inr le_rfl
  obtain ⟨a, b, hcomplex, hmodel⟩ := exists_uniform_discComplement_model hS 3 hcase
  let N := 42 * (z + 3 + 1) * GM07.vModel a b (3 + 1) (z + 3 + 1)
  let η := 2 * max N z + 1
  have h2N : 2 * N < η := Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (le_max_left N z))
  have hNη : N < η := (Nat.le_mul_of_pos_left N (by decide : 0 < 2)).trans_lt h2N
  have hzη : z ≤ η := (le_max_right N z).trans
    ((Nat.le_mul_of_pos_left (max N z) (by decide : 0 < 2)).trans (Nat.le_succ _))
  refine ⟨η, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  intro Γ K θ T ins Δ r p Zs hT hrespect hK hd hη hΔ hdis havoid hr hrΔ hsep hfree
    hcount hcover hdisZ H hHF hHB hclasses
  have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin 3) := by simpa only [Nat.card_fin] using hcase
  have hbound : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      ∀ D : Set S, IsClosedDisc D → discBd D = F →
      ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
        (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard := by
    intro F hn hF hstar D hD hbD i hi
    exact free_boundary_count_le_of_enclosing_disc hS hT hrespect hK hd hη hzη Δ r hΔ
      hcase' hr hrΔ hsep hcount hfree hF hn hstar hD hbD i hi
  apply connecting_subdrawings_of_alpha_bound_of_forest hS Γ Δ hΔ hdis havoid Zs
    hcover hdisZ H hHF hHB hclasses hbound a b 3 z hcomplex (hmodel Δ hΔ hdis) hcount
  apply Nat.le_of_lt
  have hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdis havoid
  apply alpha_gt_of_geometric_conditions hS Γ Δ hΔ hdis hcase hUC N
  · intro F hn hF _ hsmall
    exact small_circle_bounds_at_most_one_prescribed_disc hS hT hrespect hK hd hη hNη
      Δ r hr hrΔ hsep hF hn hsmall
  · intro A B P D E u v hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
    exact joined_circle_vertex_count_gt hS hT hrespect hK hd hη Δ r hΔ hcase' hr hrΔ hsep
      h2N hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
  · intro A B D E hn hA hB hstar hD hE hbD hbE hcap hi hj
    exact meeting_circle_vertex_count_gt hS hT hrespect hK hd hη Δ r hΔ hcase' hr hrΔ hsep
      h2N hn hA hB hstar hD hE hbD hbE hcap hi hj
  · intro ht _ P D a b _ hn hP hPP hstar hDs
    apply theta_vertex_count_gt hS hT hrespect hK hd hη Δ r hΔ hr hrΔ hsep hNη P D
      hn hP hPP hstar (fun i => (hDs i).1) (fun i => (hDs i).2.1)
    · intro i
      have hcast : Fin.cast ht.symm i = i := Fin.ext rfl
      simpa only [hcast] using (hDs i).2.2.1
    · exact fun i => (hDs i).2.2.2
  · exact exists_alphaCandidate_in_discComplement hS (by decide : 3 ≠ 0)
      hcase Γ Δ hΔ hdis havoid

end GraphMinor.GM12
