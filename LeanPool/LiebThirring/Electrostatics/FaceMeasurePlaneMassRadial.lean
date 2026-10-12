/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.PlaneRadialIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Scalar radial mass integral for a planar face charge

Radial integration of `r / (sqrt (r² + a²))³` at positive height gives the planar mass
calculation.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LiebThirring

/-- The primitive of the radial planar face density. -/
theorem hasDerivAt_faceDensity_primitive (a r : ℝ) (ha : 0 < a) :
    HasDerivAt (fun t : ℝ => -(Real.sqrt (t ^ 2 + a ^ 2))⁻¹)
      (r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3) r := by
  have hs : Real.sqrt (r ^ 2 + a ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_pos ha)))
  convert ((hasDerivAt_sqrt_sq_add_sq a r ha).inv hs).neg using 1
  field_simp

/-- The radial primitive tends to zero at infinity. -/
theorem tendsto_faceDensity_primitive_atTop (a : ℝ) :
    Tendsto (fun r : ℝ => -(Real.sqrt (r ^ 2 + a ^ 2))⁻¹) atTop (𝓝 0) := by
  have hsq : Tendsto (fun r : ℝ => r ^ 2 + a ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop (by decide : 2 ≠ 0))
  simpa only [Function.comp_apply, neg_zero] using
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hsq)).neg

/-- The radial planar face density is integrable on the positive half-line. -/
theorem integrableOn_faceDensity_radial (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => hasDerivAt_faceDensity_primitive a r ha)
    (fun r hr => div_nonneg hr.le (pow_nonneg (Real.sqrt_nonneg _) _))
    (tendsto_faceDensity_primitive_atTop a)

/-- Exact real radial mass integral at positive height. -/
theorem integral_faceDensity_radial (a : ℝ) (ha : 0 < a) :
    (∫ r in Ioi (0 : ℝ), r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3) = a⁻¹ := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_hr : r ∈ Ici (0 : ℝ)) => hasDerivAt_faceDensity_primitive a r ha)
    (fun r hr => div_nonneg hr.le (pow_nonneg (Real.sqrt_nonneg _) _))
    (tendsto_faceDensity_primitive_atTop a)
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq ha.le,
    zero_sub, neg_neg] using hi

/-- Exact extended nonnegative radial mass integral at positive height. -/
theorem lintegral_faceDensity_radial (a : ℝ) (ha : 0 < a) :
    (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3)) = ENNReal.ofReal a⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_faceDensity_radial a ha) ?_,
    integral_faceDensity_radial a ha]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact div_nonneg hr.le (pow_nonneg (Real.sqrt_nonneg _) _)

end LiebThirring

end
