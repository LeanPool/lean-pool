/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The scalar Newton angular integral

The elementary height integral used to evaluate the potential of a spherical shell.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Integrability of the real power after the Newton affine substitution. -/
lemma intervalIntegrable_newton_rpow {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    IntervalIntegrable (fun t : ℝ => (u ^ 2 + r ^ 2 - 2 * u * r * t) ^ (-(1 / 2 : ℝ))) volume (-1)
      1 := by
  let c := 2 * u * r
  let d := u ^ 2 + r ^ 2
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := d + c) (b := d - c)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left d
  have hj := hi.comp_mul_left (c := c)
  convert hj using 1 <;> dsimp [c, d] at * <;>
    field_simp [ne_of_gt hu, ne_of_gt hr] <;> ring

/-- Real-valued angular integral for a positive observation radius. -/
lemma integral_newton_rpow {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    (∫ t : ℝ in (-1)..1, (u ^ 2 + r ^ 2 - 2 * u * r * t) ^ (-(1 / 2 : ℝ))) =
      2 / max u r := by
  have hc : 2 * u * r ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_sub_mul (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) hc,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  have ha : u ^ 2 + r ^ 2 - 2 * u * r * 1 = (u - r) ^ 2 := by ring
  have hb : u ^ 2 + r ^ 2 - 2 * u * r * (-1) = (u + r) ^ 2 := by ring
  norm_num only [neg_div, neg_add_eq_sub, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  rw [ha, hb, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ u + r)]
  simp only [smul_eq_mul]
  rcases le_total u r with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    field_simp [ne_of_gt hu, ne_of_gt hr]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    field_simp [ne_of_gt hu, ne_of_gt hr]
    ring

/-- The squared distance is positive before the possibly singular right endpoint. -/
lemma newton_polynomial_pos {u r t : ℝ} (hu : 0 < u) (hr : 0 < r)
    (ht : t < 1) : 0 < u ^ 2 + r ^ 2 - 2 * u * r * t := by
  have hp : 0 < (2 * u * r) * (1 - t) := mul_pos (by positivity) (sub_pos.mpr ht)
  nlinarith only [sq_nonneg (u - r), hp]

/-- Evaluation of the extended integral, retaining its possibly infinite endpoint value. -/
lemma lintegral_newton_rpow {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    (∫⁻ t : ℝ in Icc (-1) 1,
      (ENNReal.ofReal (Real.sqrt (u ^ 2 + r ^ 2 - 2 * u * r * t)))⁻¹) =
      ENNReal.ofReal (2 / max u r) := by
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
    (intervalIntegrable_newton_rpow hu hr)
  have heq : (fun t : ℝ => (ENNReal.ofReal (Real.sqrt (u ^ 2 + r ^ 2 - 2 * u * r * t)))⁻¹) =ᵐ[
      volume.restrict (Icc (-1 : ℝ) 1)]
      (fun t : ℝ => ENNReal.ofReal ((u ^ 2 + r ^ 2 - 2 * u * r * t) ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht hne
    have hp := newton_polynomial_pos hu hr (lt_of_le_of_ne ht.2 hne)
    rw [← ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hp),
      Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hfi]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by norm_num : (-1 : ℝ) ≤ 1), integral_newton_rpow hu hr]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply Real.rpow_nonneg
    have hp : 0 ≤ (2 * u * r) * (1 - t) := mul_nonneg (by positivity) (sub_nonneg.mpr ht.2)
    nlinarith only [sq_nonneg (u - r), hp]

/-- The one-dimensional Newton average, including the singular endpoint when `u = r`. -/
theorem newton_angular_integral {u r : ℝ} (hu : 0 ≤ u) (hr : 0 < r) :
    (ENNReal.ofReal 2)⁻¹ * (∫⁻ t : ℝ in Icc (-1) 1,
      (ENNReal.ofReal (Real.sqrt (u ^ 2 + r ^ 2 - 2 * u * r * t)))⁻¹) =
      (ENNReal.ofReal (max u r))⁻¹ := by
  rcases hu.eq_or_lt with hu | hu
  · subst u
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add, sub_zero,
      Real.sqrt_sq hr.le, lintegral_const, max_eq_right hr.le]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num only [show (1 : ℝ) - (-1) = 2 by norm_num]
    rw [mul_comm ((ENNReal.ofReal r)⁻¹), ← mul_assoc]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  · rw [lintegral_newton_rpow hu hr,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    have hcalc : (2 : ℝ)⁻¹ * (2 / max u r) = (max u r)⁻¹ := by ring
    rw [hcalc, ENNReal.ofReal_inv_of_pos (lt_of_lt_of_le hr (le_max_right u r))]

end LiebThirring

end
