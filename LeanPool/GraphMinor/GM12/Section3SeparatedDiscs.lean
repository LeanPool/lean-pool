/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3GeometricReduction
public import LeanPool.GraphMinor.GM12.Section3SmallCircleConditions
public import LeanPool.GraphMinor.GM12.Section3MeetingCircleCondition
public import LeanPool.GraphMinor.GM12.Section3JoinedCircleCondition
public import LeanPool.GraphMinor.GM12.Section3ThetaCondition

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Separated free discs outside the small sphere cases

This assembles the first case of XII (3.2), pages 246--247.
Choose the geometric threshold from (3.1), increasing it to the
total boundary bound if needed, and take twice that bound plus one.
The short-circle, joined-circle, meeting-circle, and theta-face
lemmas verify the geometric conditions. Freeness gives the remaining
boundary inequality, so (3.1) supplies the connected subdrawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

universe u

/-- Graph Minors XII (3.2), pages 246--247, when the surface is not
a sphere or there are at least three prescribed discs. The regions
and radial metric are displayed explicitly. -/
theorem theorem_3_2_of_not_sphere_or_three_le
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Γ K : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Drawing S → Set S) (Δ r : Fin t → Set S) (p : ℕ) (Zs : Fin p → Set S),
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
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨N, hN⟩ := theorem_3_1_proof hS t z hcase
  let η := 2 * max N z + 1
  have h2N : 2 * N < η := Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (le_max_left N z))
  have hNη : N < η := (Nat.le_mul_of_pos_left N (by decide : 0 < 2)).trans_lt h2N
  have hzη : z ≤ η := (le_max_right N z).trans
    ((Nat.le_mul_of_pos_left (max N z) (by decide : 0 < 2)).trans (Nat.le_succ _))
  refine ⟨η, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  intro Γ K θ T ins Δ r p Zs hT hrespect hK hd hη hΔ hdis havoid hr hrΔ hsep hfree
    hcount hcover hdisZ hfeasible
  have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin t) := by simpa only [Nat.card_fin] using hcase
  apply hN Γ Δ hΔ hdis havoid p Zs
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
    subst t
    apply theta_vertex_count_gt hS hT hrespect hK hd hη Δ r hΔ hr hrΔ hsep hNη P D
      hn hP hPP hstar (fun i => (hDs i).1) (fun i => (hDs i).2.1)
    · intro i
      simpa only [Fin.cast_refl, id_eq] using (hDs i).2.2.1
    · exact fun i => (hDs i).2.2.2
  · exact hcover
  · exact hdisZ
  · exact hfeasible
  · intro F hn hF hstar D hD hbD i hi
    exact free_boundary_count_le_of_enclosing_disc hS hT hrespect hK hd hη hzη Δ r hΔ
      hcase' hr hrΔ hsep hcount hfree hF hn hstar hD hbD i hi
  · exact hcount

end GraphMinor.GM12
