/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar

/-!
# Coordinates on the inner disc of a collar

In XII (3.1), page 245, a collar of each deleted disc supplies coordinates
near its boundary. The collar maps the unit circle onto that boundary.
Restricting its inverse maps therefore gives a chart of the inner disc.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- The boundary parametrization in a disc collar identifies the unit
sphere exactly with the boundary of the inner disc. -/
theorem collar_image_unit_sphere {S : Type*} [TopologicalSpace S]
    {D : Set S} (p : Circle ≃ₜ discBd D) {c : ℂ → S}
    (hp : ∀ w : Circle, c w = (p w).val) :
    c '' sphere 0 1 = discBd D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let w : Circle := ⟨z, by simpa [Submonoid.unitSphere] using
      (mem_sphere_zero_iff_norm.mp hz)⟩
    exact hp w ▸ (p w).property
  · intro hx
    obtain ⟨w, hw⟩ := p.surjective ⟨x, hx⟩
    refine ⟨w, ?_, ?_⟩
    · exact mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    · exact (hp w).trans (congrArg Subtype.val hw)

/-- Restriction of the collar coordinates to its inner disc is a disc
chart. The left inverse on the larger disc ensures that its inverse
sends precisely the inner boundary to the unit sphere. -/
theorem collar_inner_isChart {S : Type*} [TopologicalSpace S]
    {D E : Set S} {c : ℂ → S} {c' : S → ℂ}
    (hDE : D ⊆ E)
    (hc : ContinuousOn c (closedBall 0 2)) (hc' : ContinuousOn c' E)
    (hl : LeftInvOn c' c (closedBall 0 2))
    (hr : RightInvOn c' c E) (hD : c '' closedBall 0 1 = D)
    (p : Circle ≃ₜ discBd D) (hp : ∀ w : Circle, c w = (p w).val) :
    IsChart D c' c := by
  have h12 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hsmall : LeftInvOn c' c (closedBall 0 1) := hl.mono h12
  refine ⟨hc'.mono hDE, hc.mono h12, ?_, ?_, hr.mono hDE, hsmall, ?_⟩
  · rintro x hx
    obtain ⟨z, hz, rfl⟩ := hD.symm ▸ hx
    rw [hsmall hz]
    exact hz
  · intro z hz
    rw [← hD]
    exact mem_image_of_mem c hz
  · rw [← collar_image_unit_sphere p hp, hsmall.mono sphere_subset_closedBall |>.image_image]

end GraphMinor.GM12
