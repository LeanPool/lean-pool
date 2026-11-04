/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration
import LeanPool.LiebThirring.Electrostatics.SphereRadial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Inverse-distance cutoff integrals

The scalar radial integral is finite and equals twice the square root of the radius.

The radial Jacobian cancels two powers of the inverse-distance power.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring.Assembly

/-- The scalar radial integral is finite and equals twice the square root of the radius. -/
theorem lintegral_rpow_neg_half (r : ℝ) (hr : 0 < r) :
    ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (-(1 : ℝ) / 2)) =
      ENNReal.ofReal (2 * Real.sqrt r) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioc 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.mono_set Ioo_subset_Ioc_self) hn]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by norm_num))]
  congr 1
  rw [Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The radial Jacobian cancels two powers of the inverse-distance power. -/
theorem radial_inv_rpow_integrand (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (t ^ 2) * ((ENNReal.ofReal t)⁻¹) ^ ((5 : ℝ) / 2) =
      ENNReal.ofReal (t ^ (-(1 : ℝ) / 2)) := by
  rw [← Real.rpow_natCast t 2, ← ENNReal.ofReal_rpow_of_pos ht,
    ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul]
  rw [← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top]
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) + -1 * (5 / 2) = -1 / 2 by norm_num]
  rw [ENNReal.ofReal_rpow_of_pos ht]

/-- The extended inverse-distance power integrates to `8π√r` on the radius cutoff. -/
theorem lintegral_ball_inv_rpow (r : ℝ) (hr : 0 < r) :
    ∫⁻ x : LiebThirring.Position,
      (if ‖x‖ < r then (ENNReal.ofReal ‖x‖)⁻¹ else 0) ^ ((5 : ℝ) / 2) =
      ENNReal.ofReal (8 * Real.pi * Real.sqrt r) := by
  have hm : Measurable (fun t : ℝ =>
      (if t < r then (ENNReal.ofReal t)⁻¹ else 0) ^ ((5 : ℝ) / 2)) := by
    have hm0 : Measurable (fun t : ℝ => if t < r then (ENNReal.ofReal t)⁻¹ else 0) :=
      Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_id.ennreal_ofReal.inv measurable_const
    fun_prop
  rw [LiebThirring.lintegral_norm _ hm]
  have he :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ 2) *
        (if t < r then (ENNReal.ofReal t)⁻¹ else 0) ^ ((5 : ℝ) / 2)) =
      ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (-(1 : ℝ) / 2)) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), (Iio r).indicator
          (fun t : ℝ => ENNReal.ofReal (t ^ (-(1 : ℝ) / 2))) t := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        by_cases htr : t < r
        · simp only [htr, ite_true, indicator_of_mem (show t ∈ Iio r from htr)]
          exact radial_inv_rpow_integrand t ht
        · simp only [htr, ite_false, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 5 / 2),
            mul_zero, indicator_of_notMem (show t ∉ Iio r from htr)]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        rw [show Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r by
          ext t; exact and_comm]
  rw [he, lintegral_rpow_neg_half r hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The cutoff of the inverse distance to a single nucleus. -/
@[expose] noncomputable def nucleusCutoff (a r : ℝ) (z x : Position) : ℝ≥0∞ :=
  if ‖x - z‖ < r then ENNReal.ofReal a * (ENNReal.ofReal ‖x - z‖)⁻¹ else 0

/-- One-center cutoffs are measurable, including their infinite value at the center. -/
theorem measurable_nucleusCutoff (a r : ℝ) (z : Position) :
    Measurable (nucleusCutoff a r z) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_id.sub measurable_const).norm measurable_const
  · exact measurable_const.mul (measurable_id.sub measurable_const).norm.ennreal_ofReal.inv
  · exact measurable_const

/-- The exact one-center power integral used to majorize the nearest-nucleus cutoff. -/
theorem lintegral_nucleusCutoff_rpow (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r)
    (z : Position) :
    ∫⁻ x : Position, nucleusCutoff a r z x ^ ((5 : ℝ) / 2) =
      ENNReal.ofReal (8 * Real.pi * a ^ ((5 : ℝ) / 2) * Real.sqrt r) := by
  have he : ∀ x : Position, nucleusCutoff a r z x = ENNReal.ofReal a *
      (if ‖x - z‖ < r then (ENNReal.ofReal ‖x - z‖)⁻¹ else 0) := by
    intro x
    unfold nucleusCutoff
    split_ifs <;> simp only [mul_zero]
  simp_rw [he, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
  rw [lintegral_sub_right_eq_self
    (fun x : Position => (if ‖x‖ < r then (ENNReal.ofReal ‖x‖)⁻¹ else 0) ^ ((5 : ℝ) / 2)) z]
  rw [lintegral_ball_inv_rpow r hr, ENNReal.ofReal_rpow_of_nonneg ha (by norm_num),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
  congr 1
  ring

end LiebThirring.Assembly

end
