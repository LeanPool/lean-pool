/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialLaplaceMoments

/-!
# Shifted-Laplace integrability and the two spatial kernel bounds

These are actual positive Lebesgue integrals. Their equality to the
cosh-integral definitions of modified Bessel functions is a separate
change-of-variables obligation.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

/-- Shifted Bessel Laplace one defined as `Real.exp (-x) * ∫ v in Ioi (0 : ℝ),
shiftedBesselDensityOne v * Real.exp (-x * v)`. -/
noncomputable def shiftedBesselLaplaceOne (x : ℝ) : ℝ :=
  Real.exp (-x) * ∫ v in Ioi (0 : ℝ),
    shiftedBesselDensityOne v * Real.exp (-x * v)

/-- Shifted Bessel Laplace two defined as `Real.exp (-x) * ∫ v in Ioi (0 : ℝ),
shiftedBesselDensityTwo v * Real.exp (-x * v)`. -/
noncomputable def shiftedBesselLaplaceTwo (x : ℝ) : ℝ :=
  Real.exp (-x) * ∫ v in Ioi (0 : ℝ),
    shiftedBesselDensityTwo v * Real.exp (-x * v)

theorem integrableOn_shiftedBessel_majorant_one {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => (1 + (Real.sqrt (2 * v))⁻¹) * Real.exp (-x * v))
      (Ioi 0) := by
  simpa only [Pi.add_def, Pi.add_apply, add_mul, one_mul] using
    (integrableOn_laplace_constant hx).add (integrableOn_laplace_inverse_sqrt hx)

theorem integrableOn_shiftedBessel_majorant_two {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ =>
      (2 * v + 4 + (Real.sqrt (2 * v))⁻¹) * Real.exp (-x * v)) (Ioi 0) := by
  simpa only [IntegrableOn, Pi.add_def, Pi.add_apply, add_mul, mul_assoc] using
    (((integrableOn_laplace_linear hx).const_mul 2).add
      ((integrableOn_laplace_constant hx).const_mul 4)).add
      (integrableOn_laplace_inverse_sqrt hx)

theorem integrableOn_shiftedBessel_density_one {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => shiftedBesselDensityOne v * Real.exp (-x * v))
      (Ioi 0) := by
  apply (integrableOn_shiftedBessel_majorant_one hx).mono_nonneg
  · exact (show Measurable (fun v : ℝ =>
        shiftedBesselDensityOne v * Real.exp (-x * v)) by
      unfold shiftedBesselDensityOne
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (shiftedBesselDensityOne_nonneg hv) (Real.exp_pos _).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_le_mul_of_nonneg_right (shiftedBesselDensityOne_le hv) (Real.exp_pos _).le

theorem integrableOn_shiftedBessel_density_two {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => shiftedBesselDensityTwo v * Real.exp (-x * v))
      (Ioi 0) := by
  apply (integrableOn_shiftedBessel_majorant_two hx).mono_nonneg
  · exact (show Measurable (fun v : ℝ =>
        shiftedBesselDensityTwo v * Real.exp (-x * v)) by
      unfold shiftedBesselDensityTwo
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (shiftedBesselDensityTwo_nonneg hv) (Real.exp_pos _).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_le_mul_of_nonneg_right (shiftedBesselDensityTwo_le hv) (Real.exp_pos _).le

theorem shiftedBesselLaplaceOne_nonneg (x : ℝ) : 0 ≤ shiftedBesselLaplaceOne x := by
  apply mul_nonneg (Real.exp_pos _).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact mul_nonneg (shiftedBesselDensityOne_nonneg hv) (Real.exp_pos _).le

theorem shiftedBesselLaplaceTwo_nonneg (x : ℝ) : 0 ≤ shiftedBesselLaplaceTwo x := by
  apply mul_nonneg (Real.exp_pos _).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact mul_nonneg (shiftedBesselDensityTwo_nonneg hv) (Real.exp_pos _).le

theorem shiftedBesselLaplaceOne_le {x : ℝ} (hx : 0 < x) :
    shiftedBesselLaplaceOne x ≤ Real.exp (-x) *
      (x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ∫ v in Ioi (0 : ℝ), (1 + (Real.sqrt (2 * v))⁻¹) *
        Real.exp (-x * v) := by
      apply integral_mono_ae (integrableOn_shiftedBessel_density_one hx)
        (integrableOn_shiftedBessel_majorant_one hx)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_le_mul_of_nonneg_right (shiftedBesselDensityOne_le hv) (Real.exp_pos _).le
    _ = _ := by
      simp_rw [add_mul, one_mul]
      rw [integral_add (integrableOn_laplace_constant hx)
        (integrableOn_laplace_inverse_sqrt hx), integral_laplace_constant hx,
        integral_laplace_inverse_sqrt hx]

theorem shiftedBesselLaplaceTwo_le {x : ℝ} (hx : 0 < x) :
    shiftedBesselLaplaceTwo x ≤ Real.exp (-x) *
      (2 * (x ^ 2)⁻¹ + 4 * x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ∫ v in Ioi (0 : ℝ), (2 * v + 4 + (Real.sqrt (2 * v))⁻¹) *
        Real.exp (-x * v) := by
      apply integral_mono_ae (integrableOn_shiftedBessel_density_two hx)
        (integrableOn_shiftedBessel_majorant_two hx)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_le_mul_of_nonneg_right (shiftedBesselDensityTwo_le hv) (Real.exp_pos _).le
    _ = _ := by
      simp_rw [add_mul, mul_assoc]
      have hsum : IntegrableOn (fun v : ℝ => 2 * (v * Real.exp (-x * v)) +
          4 * Real.exp (-x * v)) (Ioi 0) := by
        simpa only [IntegrableOn, Pi.add_def, Pi.add_apply] using
          ((integrableOn_laplace_linear hx).const_mul 2).add
            ((integrableOn_laplace_constant hx).const_mul 4)
      rw [integral_add hsum
        (integrableOn_laplace_inverse_sqrt hx),
        integral_add ((integrableOn_laplace_linear hx).const_mul 2)
        ((integrableOn_laplace_constant hx).const_mul 4), integral_const_mul,
        integral_const_mul, integral_laplace_linear hx, integral_laplace_constant hx,
        integral_laplace_inverse_sqrt hx]

end VacuumBellSeparation.Gaussian
