/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CollarChart
public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# The punctured surface in collar coordinates

For XII (3.1), page 245, a collar of one deleted disc is chosen to miss
all the others. In this collar, the remaining surface consists exactly
of points outside the open unit disc. This follows from the exact
boundary parametrization, including points on the unit circle.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- In a collar missing the other discs, membership in Sigma-star is
exactly the inequality defining the outside of the unit circle. -/
theorem collar_mem_discComplement_iff {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S)
    (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (i : ι) {E : Set S} {c : ℂ → S} {c' : S → ℂ}
    (hcE : MapsTo c (closedBall 0 2) E)
    (hmiss : ∀ j, j ≠ i → Disjoint E (Δ j))
    (hl : LeftInvOn c' c (closedBall 0 2))
    (himage : c '' closedBall 0 1 = Δ i)
    (p : Circle ≃ₜ discBd (Δ i)) (hp : ∀ w : Circle, c w = (p w).val)
    {z : ℂ} (hz : z ∈ closedBall 0 2) :
    c z ∈ discComplement Δ ↔ 1 ≤ ‖z‖ := by
  have hsphere := collar_image_unit_sphere p hp
  have h12 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 :=
    closedBall_subset_closedBall (by norm_num)
  constructor
  · intro hx
    by_contra hn
    have hn' : ‖z‖ < 1 := lt_of_not_ge hn
    have hz1 : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hn'.le
    have hxD : c z ∈ Δ i := himage ▸ mem_image_of_mem c hz1
    have hxB := discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hx, hxD⟩
    obtain ⟨w, hw, he⟩ := hsphere.symm ▸ hxB
    have hwz : w = z := hl.injOn (h12 (sphere_subset_closedBall hw)) hz he
    have hnorm : ‖z‖ = 1 := hwz ▸ mem_sphere_zero_iff_norm.mp hw
    exact hn'.ne hnorm
  · intro hn
    by_cases heq : ‖z‖ = 1
    · apply disc_boundary_subset_discComplement hS Δ hΔ hdisj i
      rw [← hsphere]
      exact mem_image_of_mem c (mem_sphere_zero_iff_norm.mpr heq)
    · apply subset_closure
      intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j
        obtain ⟨w, hw, he⟩ := himage.symm ▸ hj
        have hwz : w = z := hl.injOn (h12 hw) hz he
        have hz1 : ‖z‖ ≤ 1 := hwz ▸ mem_closedBall_zero_iff.mp hw
        exact heq (le_antisymm hz1 hn)
      · exact Set.disjoint_left.mp (hmiss j hji) (hcE hz) hj

end GraphMinor.GM12
