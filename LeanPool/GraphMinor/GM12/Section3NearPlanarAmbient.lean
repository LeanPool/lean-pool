/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CapOneDisc
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# Near-planar sets are planar after all deleted discs are filled

In the candidate-existence step used by XII (3.1), page 245, a
near-planar set in the punctured surface becomes planar in the
original closed surface. If it is already planar, include its
containing disc. Otherwise fill its one cuff first, use the containing
disc in that partial fill, and include that disc in the closed surface.
Both inclusions preserve the points of the original set.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A near-planar set in the disc complement is planar in the original
surface, since each actual single-cuff cap includes in that surface. -/
theorem isPlanar_image_of_isNearPlanar_discComplement
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {X : Set (discComplement Δ)} (hnear : GM07.IsNearPlanar X) :
    IsPlanar ((Subtype.val : discComplement Δ → S) '' X) := by
  rcases hnear with ⟨D, hD, hXD⟩ | ⟨C, hC, hpC⟩
  · exact ⟨Subtype.val '' D, (isClosedDisc_subtype_image hD).1, image_mono hXD⟩
  · have hC' := hC
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hC'
    obtain ⟨i, rfl⟩ := hC'
    obtain ⟨j, hj, hjval⟩ := exists_cap_discComplement_cuff hS Δ hΔ hdisj i
    obtain ⟨D, hD, hXD⟩ := hpC.2.2 _ j (Subtype.val ⁻¹' Δ i) hj
    refine ⟨Subtype.val '' D, (isClosedDisc_subtype_image hD).1, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    exact ⟨j y, hXD (mem_image_of_mem j hy), hjval y⟩

end GraphMinor.GM12
