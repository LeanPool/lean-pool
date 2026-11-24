/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CircleObstructions
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# The second two-loop obstruction is schismatic

For VII Section 8, used by XII (3.1), page 245, circles inside two
loops meeting once stay in a single loop. Remove the common point
and use connectedness of the punctured circle to choose a side.
Restoring the point does not change that side, since it belongs to
both loops. Near-planarity of each loop then proves the minimal-circle
clause for the second schismatic shape.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A circle inside two loops meeting once is contained in one loop. -/
theorem oArc_subset_meeting_circle_or
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A Z : Set S} {u : S}
    (hF : IsOArc F) (hA : IsOArc A) (hcap : F ∩ A = {u})
    (hZ : IsOArc Z) (hZY : Z ⊆ F ∪ A) : Z ⊆ F ∨ Z ⊆ A := by
  have hu : u ∈ F ∩ A := hcap.symm ▸ mem_singleton u
  have hcover : Z \ {u} ⊆ F ∪ A := sdiff_subset.trans hZY
  have hmiss : ∀ x ∈ Z \ {u}, x ∈ F → x ∉ A := by
    intro x hx hxF hxA
    exact hx.2 (hcap ▸ (show x ∈ F ∩ A from ⟨hxF, hxA⟩))
  rcases subset_or_subset_of_closed (hZ.twoConn u) hF.isCompact.isClosed hA.isCompact.isClosed
    hcover hmiss with hZF | hZA
  · left
    intro x hx
    by_cases hxu : x = u
    · exact hxu.symm ▸ hu.1
    · exact hZF ⟨hx, hxu⟩
  · right
    intro x hx
    by_cases hxu : x = u
    · exact hxu.symm ▸ hu.2
    · exact hZA ⟨hx, hxu⟩

/-- Two near-planar loops meeting once form a schismatic set whenever
their union is not near-planar. -/
theorem isSchismatic_x2_of_nearPlanar_loops
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A : Set S} {u : S}
    (hF : IsOArc F) (hA : IsOArc A) (hcap : F ∩ A = {u})
    (hnearF : GM07.IsNearPlanar F) (hnearA : GM07.IsNearPlanar A)
    (hnot : ¬ GM07.IsNearPlanar (F ∪ A)) : GM07.IsSchismatic (F ∪ A) := by
  refine ⟨Or.inr (Or.inr (Or.inl ⟨F, A, u, hF, hA, hcap, rfl⟩)), hnot, ?_⟩
  intro Z hZ hZY
  rcases oArc_subset_meeting_circle_or hF hA hcap hZ hZY.1 with hZF | hZA
  · exact isNearPlanar_mono hZF hnearF
  · exact isNearPlanar_mono hZA hnearA

/-- Selected circles meeting once around distinct prescribed cuffs
supply a schismatic second two-loop set inside their containing set. -/
theorem exists_schismatic_x2_of_meeting_surrounding_subcircles
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X F A : Set (discComplement Δ)} {u : discComplement Δ}
    {i j : ι} (hij : i ≠ j) (hF : IsOArc F) (hA : IsOArc A)
    (hFX : F ⊆ X) (hAX : A ⊆ X) (hFA : F ∩ A = {u})
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsSchismatic Y := by
  refine ⟨F ∪ A, union_subset hFX hAX, ?_⟩
  have hnot := not_isNearPlanar_of_distinct_surrounding_subcircles hS Δ hΔ hdisj hcase hij hF hA
    subset_union_left subset_union_right hsi hsj
  exact isSchismatic_x2_of_nearPlanar_loops hF hA hFA
    (Or.inr ⟨_, hsi.1, hsi.2.1⟩) (Or.inr ⟨_, hsj.1, hsj.2.1⟩) hnot

end GraphMinor.GM12
