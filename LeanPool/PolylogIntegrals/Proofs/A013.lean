/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.ArctanTrilog

/-!
# A013: `∫₀¹ arctan x / (x+1) · log² x dx = -(π²/24) G - (π³/32) log 2 + (21π/64) ζ(3)`

Integrate by parts with `u = arctan x` and
`H(x) = -2 Li₃(-x) + 2 log x · Li₂(-x) + log(1+x) log² x`, an antiderivative of `log² x/(1+x)`
that is continuous on `[0, 1]` with `H(0) = 0`. The boundary term is
`(π/4) H(1) = (π/4) (-2 Li₃(-1)) = (3π/8) ζ(3)`, and the remaining integral splits as
`∫₀¹ H(x)/(1+x²) dx = -2 𝒥 + 2 𝒦 + ℳ`, where
* `𝒥 = ∫₀¹ Li₃(-x)/(1+x²) dx`,
* `𝒦 = ∫₀¹ log x · Li₂(-x)/(1+x²) dx = π² G/48`
  (`LeanPolyLog.Arctan.integral_log_mul_Lir_two_neg_div_one_add_sq`),
* `ℳ = ∫₀¹ log(1+x) log² x/(1+x²) dx`.

Writing `Li₃(-x) = -½ ∫₀¹ x log² y/(1+xy) dy` and swapping the order of integration turns `𝒥`
into `-½ ∫₀¹ log² y · K(y) dy`, with the same kernel `K(y) = (log 2/2 + πy/4 - log(1+y))/(1+y²)`
as in A012. Hence `-2 𝒥 = (log 2/2)(π³/16) + (π/4)(3/16) ζ(3) - ℳ`, and `ℳ` cancels.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Proofs

open Arctan

/-- A013: `∫₀¹ arctan x / (x+1) · log² x dx = -(π²/24) G - (π³/32) log 2 + (21π/64) ζ(3)`. -/
public theorem A013 : ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x ^ 2 =
    -π ^ 2 / 24 * G - π ^ 3 / 32 * Real.log 2 + 21 * π / 64 * zeta3 := by
  have hlog2 : IntervalIntegrable (fun t : ℝ ↦ log t ^ 2) volume 0 1 := by
    simpa only [pow_zero, one_mul] using intervalIntegrable_pow_mul_log_sq 0
  have hH : ContinuousOn (fun x ↦ -2 * Lir 3 (-x) + 2 * (log x * Lir 2 (-x)) +
      log (1 + x) * log x ^ 2) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((continuousOn_const.mul (continuousOn_Lir_neg (by norm_num))).add
      (continuousOn_const.mul continuousOn_log_mul_Lir_two_neg)).add
      continuousOn_log_one_add_mul_log_sq
  have hv' : IntervalIntegrable (fun x : ℝ ↦ log x ^ 2 / (1 + x)) volume 0 1 := by
    have h := hlog2.mul_continuousOn (g := fun x : ℝ ↦ (1 + x)⁻¹) (by
      refine ContinuousOn.inv₀ (by fun_prop) fun x hx ↦ ?_
      rw [uIcc_of_le zero_le_one] at hx
      linarith [hx.1])
    simpa only [div_eq_mul_inv] using h
  -- integration by parts against `arctan`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := arctan) (u' := fun x ↦ 1 / (1 + x ^ 2)) (a := 0) (b := 1)
    continuous_arctan.continuousOn hH (fun x _ ↦ hasDerivAt_arctan x)
    (fun x hx ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
      exact hasDerivAt_trilog_primitive hx.1 hx.2)
    ((continuous_const.div (by fun_prop) fun x ↦ by positivity).intervalIntegrable 0 1) hv'
  simp only [arctan_one, arctan_zero, zero_mul, sub_zero, log_one, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Lir_three_neg_one] at hibp
  -- integrability of the pieces
  have iLi3 : IntervalIntegrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹ * Lir 3 (-x)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuous_inv_one_add_sq.continuousOn.mul (continuousOn_Lir_neg (by norm_num))
  have iK : IntervalIntegrable (fun x : ℝ ↦ log x * Lir 2 (-x) / (1 + x ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_log_mul_Lir_two_neg.div (by fun_prop) fun x _ ↦ by positivity
  have iM : IntervalIntegrable (fun x : ℝ ↦ log (1 + x) * log x ^ 2 / (1 + x ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_log_one_add_mul_log_sq.div (by fun_prop) fun x _ ↦ by positivity
  have jA : IntervalIntegrable (fun y : ℝ ↦ log y ^ 2 / (1 + y ^ 2)) volume 0 1 := by
    have h := hlog2.mul_continuousOn (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹)
      continuous_inv_one_add_sq.continuousOn
    simpa only [div_eq_mul_inv] using h
  have jB : IntervalIntegrable (fun y : ℝ ↦ y * log y ^ 2 / (1 + y ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_mul_log_sq.mono Icc_subset_Ici_self).div (by fun_prop)
      fun x _ ↦ by positivity
  -- split the remaining integral into `-2 𝒥 + 2 𝒦 + ℳ`
  have hsplit : ∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2) * (-2 * Lir 3 (-x) +
      2 * (log x * Lir 2 (-x)) + log (1 + x) * log x ^ 2) =
      -2 * (∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 3 (-x)) +
        2 * (∫ x in (0 : ℝ)..1, log x * Lir 2 (-x) / (1 + x ^ 2)) +
        ∫ x in (0 : ℝ)..1, log (1 + x) * log x ^ 2 / (1 + x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (iLi3.const_mul _) (iK.const_mul _),
      ← intervalIntegral.integral_add ((iLi3.const_mul _).add (iK.const_mul _)) iM]
    congr 1
    ext x
    ring
  -- `𝒥`: `Li₃(-x) = -½ ∫₀¹ x log² y/(1+xy) dy`, then Fubini and the kernel
  have hLi3 : ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 3 (-x) =
      -(1 / 2) * (log 2 / 2 * (π ^ 3 / 16) + π / 4 * (3 / 16 * zeta3) -
        ∫ y in (0 : ℝ)..1, log (1 + y) * log y ^ 2 / (1 + y ^ 2)) := by
    have h1 : ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 3 (-x) = -(1 / 2) *
        ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * ∫ y in (0 : ℝ)..1, x * log y ^ 2 / (1 + x * y) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp only [integral_mul_log_sq_div_one_add_mul hx.1 hx.2]
      ring
    have h2 : ∫ y in (0 : ℝ)..1, log y ^ 2 * ∫ x in (0 : ℝ)..1, x / ((1 + x ^ 2) * (1 + x * y)) =
        ∫ y in (0 : ℝ)..1, (log 2 / 2 * (log y ^ 2 / (1 + y ^ 2)) +
          π / 4 * (y * log y ^ 2 / (1 + y ^ 2)) - log (1 + y) * log y ^ 2 / (1 + y ^ 2)) := by
      refine intervalIntegral.integral_congr fun y hy ↦ ?_
      rw [uIcc_of_le zero_le_one] at hy
      simp only [integral_kernel hy.1]
      ring
    rw [h1, integral_integral_swap_kernel hlog2, h2,
      intervalIntegral.integral_sub ((jA.const_mul _).add (jB.const_mul _)) iM,
      intervalIntegral.integral_add (jA.const_mul _) (jB.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_log_sq_div_one_add_sq, integral_mul_log_sq_div_one_add_sq]
  have hlhs : ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x ^ 2 =
      ∫ x in (0 : ℝ)..1, arctan x * (log x ^ 2 / (1 + x)) := by
    congr 1
    ext x
    ring
  rw [hlhs, hibp, hsplit, hLi3, integral_log_mul_Lir_two_neg_div_one_add_sq]
  ring

end LeanPolyLog.Proofs
