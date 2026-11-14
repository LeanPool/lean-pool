/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The scalar radial Coulomb integral in a plane

The Coulomb radial primitive is differentiable at every point for positive height.

The real radial Coulomb integral at positive height.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- The Coulomb radial primitive is differentiable at every point for positive height. -/
lemma hasDerivAt_sqrt_sq_add_sq (h x : ℝ) (hh : 0 < h) :
    HasDerivAt (fun ρ : ℝ => Real.sqrt (ρ ^ 2 + h ^ 2))
      (x / Real.sqrt (x ^ 2 + h ^ 2)) x := by
  have hpos : 0 < x ^ 2 + h ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hh)
  have hd : HasDerivAt (fun ρ : ℝ => ρ ^ 2 + h ^ 2) (2 * x) x := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      using ((hasDerivAt_id x).pow 2).add_const (h ^ 2)
  convert hd.sqrt (ne_of_gt hpos) using 1
  field_simp

/-- The real radial Coulomb integral at positive height. -/
lemma integral_coulomb_radial_of_pos (h R : ℝ) (hh : 0 < h) :
    (∫ ρ in (0 : ℝ)..R, ρ / Real.sqrt (ρ ^ 2 + h ^ 2)) =
      Real.sqrt (R ^ 2 + h ^ 2) - h := by
  have hc : Continuous (fun ρ : ℝ => ρ / Real.sqrt (ρ ^ 2 + h ^ 2)) := by
    refine continuous_id.div (Real.continuous_sqrt.comp
      ((continuous_id.pow 2).add continuous_const)) ?_
    intro ρ
    exact ne_of_gt (Real.sqrt_pos.2
      (add_pos_of_nonneg_of_pos (sq_nonneg ρ) (sq_pos_of_pos hh)))
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq hh.le] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_sqrt_sq_add_sq h x hh) (hc.intervalIntegrable 0 R)

/-- Exact nonnegative radial integral on an open interval, including zero height. -/
theorem lintegral_coulomb_radial_Ioo (h R : ℝ) (hh : 0 ≤ h) (hR : 0 ≤ R) :
    (∫⁻ ρ in Ioo (0 : ℝ) R,
      ENNReal.ofReal ρ * (ENNReal.ofReal (Real.sqrt (ρ ^ 2 + h ^ 2)))⁻¹) =
      ENNReal.ofReal (Real.sqrt (R ^ 2 + h ^ 2) - h) := by
  rcases eq_or_lt_of_le hh with rfl | hhpos
  · calc
      _ = ∫⁻ _ρ in Ioo (0 : ℝ) R, (1 : ℝ≥0∞) := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => ?_)
        simp only [zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq hρ.1.le]
        exact ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.2 hρ.1))
          ENNReal.ofReal_ne_top
      _ = _ := by simp only [lintegral_const, one_mul, Measure.restrict_apply_univ,
        Real.volume_Ioo, sub_zero,
        zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq hR]
  · have hc : Continuous (fun ρ : ℝ => ρ / Real.sqrt (ρ ^ 2 + h ^ 2)) := by
      refine continuous_id.div (Real.continuous_sqrt.comp
        ((continuous_id.pow 2).add continuous_const)) ?_
      intro ρ
      exact ne_of_gt (Real.sqrt_pos.2
        (add_pos_of_nonneg_of_pos (sq_nonneg ρ) (sq_pos_of_pos hhpos)))
    calc
      _ = ∫⁻ ρ in Ioo (0 : ℝ) R,
          ENNReal.ofReal (ρ / Real.sqrt (ρ ^ 2 + h ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun ρ _ => ?_)
        rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2
          (add_pos_of_nonneg_of_pos (sq_nonneg ρ) (sq_pos_of_pos hhpos))),
          div_eq_mul_inv]
      _ = ENNReal.ofReal (∫ ρ in Ioo (0 : ℝ) R,
          ρ / Real.sqrt (ρ ^ 2 + h ^ 2)) := by
        apply (ofReal_integral_eq_lintegral_ofReal
          (hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
        exact div_nonneg hρ.1.le (Real.sqrt_nonneg _)
      _ = _ := by
        rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hR,
          integral_coulomb_radial_of_pos h R hhpos]

/-- Distance from a point of the plane to a centre at height `h` is at least `h`. -/
lemma le_sqrt_sq_add_sq (h ρ : ℝ) (hh : 0 ≤ h) :
    h ≤ Real.sqrt (ρ ^ 2 + h ^ 2) := by
  calc
    h = Real.sqrt (h ^ 2) := (Real.sqrt_sq hh).symm
    _ ≤ Real.sqrt (ρ ^ 2 + h ^ 2) := Real.sqrt_le_sqrt
      (le_add_of_nonneg_left (sq_nonneg ρ))

/-- Exact truncated radial Coulomb integral for every nonnegative height.

This includes centres outside the ball (`ε ≤ h`), whose contribution is zero,
and centres in the plane (`h = 0`), whose kernel is infinite at the origin.
The radial origin is excluded by `Ioi 0`, as in planar polar coordinates.
-/
theorem lintegral_coulomb_radial (h ε : ℝ) (hh : 0 ≤ h) :
    (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ *
      (if Real.sqrt (ρ ^ 2 + h ^ 2) < ε then
        (ENNReal.ofReal (Real.sqrt (ρ ^ 2 + h ^ 2)))⁻¹ else 0)) =
      ENNReal.ofReal (max (ε - h) 0) := by
  classical
  by_cases hlt : h < ε
  · have hε : 0 < ε := lt_of_le_of_lt hh hlt
    have hd : 0 ≤ ε ^ 2 - h ^ 2 := by
      nlinarith only [hh, hlt, hε]
    let R : ℝ := Real.sqrt (ε ^ 2 - h ^ 2)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have hs : Real.sqrt (R ^ 2 + h ^ 2) = ε := by
      dsimp [R]
      rw [Real.sq_sqrt hd, sub_add_cancel, Real.sqrt_sq hε.le]
    have hiff (ρ : ℝ) (hρ : 0 < ρ) :
        Real.sqrt (ρ ^ 2 + h ^ 2) < ε ↔ ρ < R := by
      rw [Real.sqrt_lt' hε, Real.lt_sqrt hρ.le]
      constructor <;> intro h <;> linarith only [h]
    calc
      _ = ∫⁻ ρ in Ioi (0 : ℝ), (Iio R).indicator
          (fun ρ : ℝ => ENNReal.ofReal ρ *
            (ENNReal.ofReal (Real.sqrt (ρ ^ 2 + h ^ 2)))⁻¹) ρ := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        by_cases hρR : ρ < R
        · rw [ite_eq_left ((hiff ρ hρ).2 hρR), indicator_of_mem (show ρ ∈ Iio R from hρR)]
        · rw [ite_eq_right (fun h => hρR ((hiff ρ hρ).1 h)),
            mul_zero, indicator_of_notMem (show ρ ∉ Iio R from hρR)]
      _ = ∫⁻ ρ in Ioo (0 : ℝ) R,
          ENNReal.ofReal ρ * (ENNReal.ofReal (Real.sqrt (ρ ^ 2 + h ^ 2)))⁻¹ := by
        rw [setLIntegral_indicator measurableSet_Iio, Iio_inter_Ioi]
      _ = _ := by
        rw [lintegral_coulomb_radial_Ioo h R hh hR, hs, max_eq_left (sub_nonneg.2 hlt.le)]
  · have hε : ε ≤ h := le_of_not_gt hlt
    rw [max_eq_right (sub_nonpos.2 hε), ENNReal.ofReal_zero]
    refine setLIntegral_eq_zero measurableSet_Ioi (fun ρ _ => ?_)
    rw [ite_eq_right (not_lt_of_ge (hε.trans (le_sqrt_sq_add_sq h ρ hh))), mul_zero, Pi.zero_apply]

end LiebThirring

end
