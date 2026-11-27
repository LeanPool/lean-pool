/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSlices
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroAlgebra

/-!
# Every evolved spacetime slice is localized in the same time-zero ball

The shrinking slice radius `r − |t|` and the proved finite propagation
radius `|t|` cancel exactly. Slices outside the compact time interval are
identically zero, so no propagation theorem is applied with negative radius.
-/

@[expose] public section

namespace VacuumBellSeparation

@[simp] theorem spatialCauchyTest_zero_zero {m : ℝ} (hm : 0 < m) (t : ℝ) :
    spatialCauchyTest hm t 0 0 = 0 := by
  apply Subtype.ext
  funext x
  change (massiveSchwartzCauchy m t (spatialSchwartz 0) (spatialSchwartz 0) x).re = 0
  simp [massiveSchwartzCauchy, spatialSchwartz_zero]

@[simp] theorem evolvedSpatialSource_zero {m : ℝ} (hm : 0 < m) (t : ℝ) :
    evolvedSpatialSource hm t 0 = 0 := by
  simp [evolvedSpatialSource]

theorem evolvedSpatialSource_spacetimeSlice_mem {m r : ℝ} (hm : 0 < m)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (hF : ∀ y ∈ tsupport F.1, |y.1| + ‖y.2 - x₀‖ ≤ r) (t : ℝ) :
    evolvedSpatialSource hm t (spacetimeSpatialSlice F t) ∈
      localizedTimeZeroSources (Metric.closedBall x₀ r) := by
  by_cases ht : |t| ≤ r
  · have hr : 0 ≤ r - |t| := sub_nonneg.mpr ht
    have hrad : r - |t| + |t| = r := sub_add_cancel r |t|
    have hs := tsupport_spacetimeSpatialSlice_subset x₀ F hF t
    constructor
    · simpa only [evolvedSpatialSource, hrad] using
        tsupport_spatialCauchyTest_subset hm hr t x₀ (spacetimeSpatialSlice F t) 0 hs
          (by change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ _; simp)
    · simpa only [evolvedSpatialSource, hrad] using
        tsupport_spatialCauchyTest_subset hm hr t x₀ 0 (spacetimeSpatialSlice F t)
          (by change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ _; simp) hs
  · rw [spacetimeSpatialSlice_eq_zero_outside x₀ F hF (lt_of_not_ge ht),
      evolvedSpatialSource_zero]
    exact (localizedTimeZeroSources _).zero_mem

theorem evolvedSpatialSource_spacetimeSlice_mem_ball {m r R : ℝ} (hm : 0 < m)
    (hrR : r < R) (x₀ : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (hF : ∀ y ∈ tsupport F.1, |y.1| + ‖y.2 - x₀‖ ≤ r) (t : ℝ) :
    evolvedSpatialSource hm t (spacetimeSpatialSlice F t) ∈
      localizedTimeZeroSources (Metric.ball x₀ R) :=
  localizedTimeZeroSources_mono (Metric.closedBall_subset_ball hrR)
    (evolvedSpatialSource_spacetimeSlice_mem hm x₀ F hF t)

/-- All slices, including their actual evolution, give generators of the
same time-zero algebra. The source F itself is localized in the open cone. -/
theorem evolvedSpatialSource_spacetimeSlice_mem_ball_of_doubleCone {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ doubleCone (0, x₀) R) (t : ℝ) :
    evolvedSpatialSource hm t (spacetimeSpatialSlice F t) ∈
      localizedTimeZeroSources (Metric.ball x₀ R) := by
  obtain ⟨r, _, hrR, hs⟩ := exists_doubleCone_support_margin hR x₀ F hF
  exact evolvedSpatialSource_spacetimeSlice_mem_ball hm hrR x₀ F hs t

end VacuumBellSeparation
