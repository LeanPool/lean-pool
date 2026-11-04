/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Scalar integrals for the half-space inverse-fourth mass

Primitive for the planar radial inverse-fourth integrand.

The radial primitive vanishes at infinity.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LiebThirring

/-- Primitive for the planar radial inverse-fourth integrand. -/
lemma hasDerivAt_inverse_fourth_radial (s r : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => -((s ^ 2 + t ^ 2)⁻¹) / 2)
      (r / (s ^ 2 + r ^ 2) ^ 2) r := by
  have hpos : 0 < s ^ 2 + r ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hs) (sq_nonneg r)
  have hd : HasDerivAt (fun t : ℝ => s ^ 2 + t ^ 2) (2 * r) r := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      using ((hasDerivAt_id r).pow 2).const_add (s ^ 2)
  convert (hd.inv (ne_of_gt hpos)).neg.div_const 2 using 1
  field_simp

/-- The radial primitive vanishes at infinity. -/
lemma tendsto_inverse_fourth_radial_primitive (s : ℝ) :
    Tendsto (fun r : ℝ => -((s ^ 2 + r ^ 2)⁻¹) / 2) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => s ^ 2 + r ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0))
  simpa only [Function.comp_def, neg_zero, zero_div] using (tendsto_inv_atTop_zero.comp
    hp).neg.div_const 2

/-- The radial inverse-fourth integrand is integrable for positive height. -/
lemma integrableOn_inverse_fourth_radial (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun r : ℝ => r / (s ^ 2 + r ^ 2) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => hasDerivAt_inverse_fourth_radial s r hs)
    (fun _r hr => div_nonneg hr.le (sq_nonneg _))
    (tendsto_inverse_fourth_radial_primitive s)

/-- Exact nonnegative radial inverse-fourth mass at a positive height. -/
theorem lintegral_inverse_fourth_radial (s : ℝ) (hs : 0 < s) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r / (s ^ 2 + r ^ 2) ^ 2)) =
      ENNReal.ofReal (1 / (2 * s ^ 2)) := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_hr : r ∈ Ici (0 : ℝ)) => hasDerivAt_inverse_fourth_radial s r hs)
    (fun _r hr => div_nonneg hr.le (sq_nonneg _))
    (tendsto_inverse_fourth_radial_primitive s)
  have hreal : (∫ r in Ioi (0 : ℝ), r / (s ^ 2 + r ^ 2) ^ 2) = 1 / (2 * s ^ 2) := by
    calc
      _ = -(-(s ^ 2)⁻¹ / 2) := by
        simpa only [zero_pow (by decide : 2 ≠ 0), add_zero, zero_sub] using hi
      _ = _ := by field_simp
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_inverse_fourth_radial s hs) ?_, hreal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact div_nonneg hr.le (sq_nonneg _)

/-- Primitive for the positive-height inverse-square integral. -/
lemma hasDerivAt_inverse_square_height (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => -Real.pi / t) (Real.pi / s ^ 2) s := by
  have hd : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s := by
    convert (hasDerivAt_id s).inv (ne_of_gt hs) using 1
    · funext t
      rw [Pi.inv_apply, id_eq]
    · simp only [id_eq, neg_div, one_div]
  convert (hd.const_mul Real.pi).neg using 1
  · funext t
    simp only [div_eq_mul_inv, neg_mul, Pi.neg_apply]
  · simp only [mul_neg, neg_neg, div_eq_mul_inv]

/-- The inverse-square height integrand is integrable away from zero. -/
lemma integrableOn_inverse_square_height (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.pi / s ^ 2) (Ioi a) := by
  have hlim : Tendsto (fun t : ℝ => -Real.pi / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun s hs => hasDerivAt_inverse_square_height s (ha.trans_le hs))
    (fun s _ => div_nonneg Real.pi_pos.le (sq_nonneg s)) hlim

/-- Exact nonnegative inverse-square height integral, including its lower endpoint. -/
theorem lintegral_inverse_square_height (a : ℝ) (ha : 0 < a) :
    (∫⁻ s in Ici a, ENNReal.ofReal (Real.pi / s ^ 2)) = ENNReal.ofReal (Real.pi / a) := by
  have hlim : Tendsto (fun t : ℝ => -Real.pi / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun s (hs : s ∈ Ici a) => hasDerivAt_inverse_square_height s (ha.trans_le hs))
    (fun s (_hs : s ∈ Ioi a) => div_nonneg Real.pi_pos.le (sq_nonneg s)) hlim
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_inverse_square_height a ha)
      (Eventually.of_forall (fun s => div_nonneg Real.pi_pos.le (sq_nonneg s)))]
  simpa only [zero_sub, neg_div, neg_neg] using congrArg ENNReal.ofReal hi

end LiebThirring

end
