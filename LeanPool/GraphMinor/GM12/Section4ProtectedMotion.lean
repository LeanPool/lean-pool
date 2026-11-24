/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4ProtectedArc
import LeanPool.GraphMinor.GM12.Section4AmbientMotion
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Moving a point while preserving a finite family of discs

In XII (4.3), claim (7), page 251, disc placements can be made
successively only if each new motion preserves the earlier ones.
Join two points by an arc outside the protected closed discs, then
apply the ambient endpoint motion with their union as forbidden set.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Any point outside finitely many disjoint closed discs can be
moved to any other such point, fixing all the discs pointwise. -/
theorem exists_point_motion_fixing_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : ι → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (hDD : Pairwise (fun i j => Disjoint (D i) (D j)))
    {x y : S} (hx : x ∉ ⋃ i, D i) (hy : y ∉ ⋃ i, D i) :
    ∃ e : S ≃ₜ S, e x = y ∧ ∀ i z, z ∈ D i → e z = z := by
  by_cases hxy : x = y
  · exact ⟨Homeomorph.refl S, hxy, fun _ _ _ => rfl⟩
  obtain ⟨a, ha, ha0, ha1, havoid⟩ :=
    exists_arc_avoiding_closed_discs hS D hD hDD hxy hx hy
  have hclosed : IsClosed (⋃ i, D i) := isClosed_iUnion_of_finite fun i => (hD i).isClosed
  obtain ⟨e, hend, hfix⟩ := exists_ambient_endpoint_motion hS ha hclosed havoid
  have heyx : e y = x := by rwa [ha0, ha1] at hend
  refine ⟨e.symm, ?_, ?_⟩
  · exact e.symm_apply_eq.mpr heyx.symm
  · intro i z hz
    exact e.symm_apply_eq.mpr (hfix z (mem_iUnion.mpr ⟨i, hz⟩)).symm

end GraphMinor.GM12
