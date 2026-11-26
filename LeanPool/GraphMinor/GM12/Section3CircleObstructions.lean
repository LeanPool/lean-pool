/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3JoiningCircles
public import LeanPool.GraphMinor.GM12.Section3SurroundingUnique

/-!
# Two-loop obstructions inside a solid set

In the Section 8 reduction used in XII (3.1), page 245, disjoint
selected circles surrounding distinct cuffs give the first two-loop
shape. Connectedness and local arc-connectedness supply its joining
line. The two distinct cuffs make the resulting set not near-planar.
Circles meeting at one point give the second two-loop shape directly.
Everything stays in the original candidate, preserving its vertex bound.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Disjoint surrounding subcircles of a connected solid set give an
actual first two-loop obstruction contained in that set. -/
theorem exists_x1_obstruction_of_disjoint_surrounding_subcircles
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X F A : Set (discComplement Δ)} (hX : IsSolid X) (hconn : IsConnected X)
    {i j : ι} (hij : i ≠ j) (hF : IsOArc F) (hA : IsOArc A)
    (hFX : F ⊆ X) (hAX : A ⊆ X) (hFA : Disjoint F A)
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsX1Arc Y ∧ ¬ GM07.IsNearPlanar Y := by
  have harc := isArcConnected_of_isConnected_isLocallyArcConnected hconn hX.1
  obtain ⟨P, a, b, hP, hPX, ha, hb, _, hPF, hPA⟩ :=
    exists_joining_line_between_disjoint_circles harc hF hA hFX hAX hFA
  let Y := F ∪ A ∪ P
  have hYX : Y ⊆ X := union_subset (union_subset hFX hAX) hPX
  have hshape : GM07.IsX1Arc Y :=
    ⟨F, A, P, a, b, hF, hA, hFA, hP, ha, hb, hPF, hPA, rfl⟩
  have hnot : ¬ GM07.IsNearPlanar Y :=
    not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij hF hA
      (subset_union_left.trans subset_union_left) (subset_union_right.trans subset_union_left) hsi
        hsj
  exact ⟨Y, hYX, hshape, hnot⟩

/-- Selected circles meeting at one point and surrounding distinct
cuffs give a second two-loop obstruction inside their containing set. -/
theorem exists_x2_obstruction_of_meeting_surrounding_subcircles
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X F A : Set (discComplement Δ)} {u : discComplement Δ}
    {i j : ι} (hij : i ≠ j) (hF : IsOArc F) (hA : IsOArc A)
    (hFX : F ⊆ X) (hAX : A ⊆ X) (hFA : F ∩ A = {u})
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsX2Arc Y ∧ ¬ GM07.IsNearPlanar Y := by
  refine ⟨F ∪ A, union_subset hFX hAX, ⟨F, A, u, hF, hA, hFA, rfl⟩, ?_⟩
  exact not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij hF hA
    subset_union_left subset_union_right hsi hsj

end GraphMinor.GM12
