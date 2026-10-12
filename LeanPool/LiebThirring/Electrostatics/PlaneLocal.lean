/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.PlaneDistance
public import LeanPool.LiebThirring.Electrostatics.PlanePolar
public import LeanPool.LiebThirring.Electrostatics.PlaneRadialIntegral

/-!
# Local planar Coulomb integration

The truncated radial inverse-distance integrand is Borel measurable.

Exact planar Coulomb integral with arbitrary nonnegative normal height.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- The truncated radial inverse-distance integrand is Borel measurable. -/
theorem measurable_truncated_planar_coulomb (h ε : ℝ) :
    Measurable (fun r : ℝ => if Real.sqrt (r ^ 2 + h ^ 2) < ε then
      (ENNReal.ofReal (Real.sqrt (r ^ 2 + h ^ 2)))⁻¹ else 0) := by
  have hc : Continuous (fun r : ℝ => Real.sqrt (r ^ 2 + h ^ 2)) :=
    Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const)
  exact (hc.measurable.ennreal_ofReal.inv).ite
    (isOpen_lt hc continuous_const).measurableSet measurable_const

/-- Exact planar Coulomb integral with arbitrary nonnegative normal height. -/
theorem lintegral_planar_coulomb_cutoff (h ε : ℝ) (hh : 0 ≤ h) :
    (∫⁻ q : Planar, if Real.sqrt (‖q‖ ^ 2 + h ^ 2) < ε then
      (ENNReal.ofReal (Real.sqrt (‖q‖ ^ 2 + h ^ 2)))⁻¹ else 0) =
      ENNReal.ofReal (2 * Real.pi * max (ε - h) 0) := by
  rw [lintegral_planar_norm _ (measurable_truncated_planar_coulomb h ε),
    lintegral_coulomb_radial h ε hh,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]

/-- Exact local Coulomb mass in a plane at any centre, on or off the plane. -/
theorem lintegral_coulombKernel_ball_planeMeasure_eq (n b x : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b)) (ε : ℝ) :
    (∫⁻ y in Metric.ball x ε, coulombKernel x y ∂planeMeasure F) =
      ENNReal.ofReal (2 * Real.pi * max (ε - planeHeight n b x) 0) := by
  rw [lintegral_coulombKernel_ball_planeMeasure n b x hn F ε,
    lintegral_planar_coulomb_cutoff _ ε (planeHeight_nonneg n b x)]

/-- The local planar Coulomb bound, including off-plane centres and the
infinite diagonal value of the Coulomb kernel. -/
theorem lintegral_coulombKernel_ball_planeMeasure_le (n b x : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b)) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ y in Metric.ball x ε, coulombKernel x y ∂planeMeasure F) ≤
      ENNReal.ofReal (2 * Real.pi * ε) := by
  rw [lintegral_coulombKernel_ball_planeMeasure_eq n b x hn F]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi)
  exact max_le (sub_le_self ε (planeHeight_nonneg n b x)) hε.le

end LiebThirring

end
