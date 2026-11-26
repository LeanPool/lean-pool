/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SolidPlanarity
import LeanPool.GraphMinor.GM12.Section3PlanarityMaps

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Cuff labels for shapes with two circles

For the first two schismatic shapes in VII Section 8, used by XII
(3.1), page 245, every circle lies in one of two distinguished loops.
If both loops are planar in the same cap, VII (5.1) makes the whole
solid shape planar in that cap. Minimality makes the two loops
near-planar. Neither can be planar, and their surrounding cuffs must
be distinct, since either possibility would make the whole shape
near-planar.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- If every circle in a solid set lies in one of two sets, planarity
of those sets in one cap makes the whole solid set planar there. -/
theorem planarInCappedCuff_of_two_circle_cover
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {X F A C : Set S} (hX : IsSolid X)
    (hcover : ∀ Z : Set S, IsOArc Z → Z ⊆ X → Z ⊆ F ∨ Z ⊆ A)
    (hpF : GM07.IsPlanarInCappedCuff C F) (hpA : GM07.IsPlanarInCappedCuff C A) :
    GM07.IsPlanarInCappedCuff C X := by
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hpF.1
  let := tT
  apply planarInCappedCuff_of_all_subcircles hS hcap hX
  intro Z hZ hZX
  rcases hcover Z hZ hZX with hZF | hZA
  · exact isPlanarInCappedCuff_mono hZF hpF
  · exact isPlanarInCappedCuff_mono hZA hpA

/-- A non-near-planar solid set covered by two circle types cannot
have one type planar when the other is near-planar. -/
theorem not_planar_of_two_circle_cover
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hcuffs : (cuffs S).Nonempty) {X F A : Set S} (hX : IsSolid X)
    (hcover : ∀ Z : Set S, IsOArc Z → Z ⊆ X → Z ⊆ F ∨ Z ⊆ A)
    (hnot : ¬ GM07.IsNearPlanar X) (hnA : GM07.IsNearPlanar A) : ¬ IsPlanar F := by
  intro hpF
  have hex : ∃ C, GM07.IsPlanarInCappedCuff C A := by
    rcases hnA with hpA | ⟨C, _, hpA⟩
    · obtain ⟨C, hC⟩ := hcuffs
      exact ⟨C, isPlanarInCappedCuff_of_isPlanar hS hC hpA⟩
    · exact ⟨C, hpA⟩
  obtain ⟨C, hpA⟩ := hex
  have hpFC := isPlanarInCappedCuff_of_isPlanar hS hpA.1 hpF
  have hpX := planarInCappedCuff_of_two_circle_cover hS hX hcover hpFC hpA
  exact hnot (Or.inr ⟨C, hpX.1, hpX⟩)

/-- Two proper distinguished loops containing all circles of a
schismatic shape surround distinct cuffs. This supplies the common
argument for VII Section 8's first two shapes, page 241. -/
theorem surrounding_cuffs_of_two_circle_cover
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hcuffs : (cuffs S).Nonempty) {X F A : Set S} (hsolid : IsSolid X)
    (hF : IsOArc F) (hA : IsOArc A) (hFX : F ⊂ X) (hAX : A ⊂ X)
    (hcover : ∀ Z : Set S, IsOArc Z → Z ⊆ X → Z ⊆ F ∨ Z ⊆ A)
    (hX : GM07.IsSchismatic X) :
    ∃ C D : Set S, GM07.SurroundsCuff F C ∧ GM07.SurroundsCuff A D ∧ C ≠ D := by
  have hnF := hX.2.2 F hF hFX
  have hnA := hX.2.2 A hA hAX
  have hnpF := not_planar_of_two_circle_cover hS hcuffs hsolid hcover hX.2.1 hnA
  have hnpA := not_planar_of_two_circle_cover hS hcuffs hsolid
    (fun Z hZ hZX => (hcover Z hZ hZX).symm) hX.2.1 hnF
  obtain ⟨C, hC, hpF⟩ : ∃ C, C ∈ cuffs S ∧ GM07.IsPlanarInCappedCuff C F := by
    rcases hnF with hp | ⟨C, hC, hp⟩
    · exact (hnpF hp).elim
    · exact ⟨C, hC, hp⟩
  obtain ⟨D, hD, hpA⟩ : ∃ D, D ∈ cuffs S ∧ GM07.IsPlanarInCappedCuff D A := by
    rcases hnA with hp | ⟨D, hD, hp⟩
    · exact (hnpA hp).elim
    · exact ⟨D, hD, hp⟩
  refine ⟨C, D, ⟨hC, hpF, hnpF⟩, ⟨hD, hpA, hnpA⟩, ?_⟩
  intro heq
  subst D
  have hpX := planarInCappedCuff_of_two_circle_cover hS hsolid hcover hpF hpA
  exact hX.2.1 (Or.inr ⟨C, hpX.1, hpX⟩)

end GraphMinor.GM12
