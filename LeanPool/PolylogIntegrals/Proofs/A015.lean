/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.LogSinSqSeries
public import LeanPool.PolylogIntegrals.Lemmas.Radial

/-!
# A015: `∫₀^{π/2} x log² sin x dx = Li₄(1/2) - 19π⁴/2880 + log⁴2/24 + π² log²2/12`

Let `L = ∫₀^{π/2} log² sin x dx = π³/24 + (π/2) log² 2`
(`LeanPool.PolylogIntegrals.Lemmas.LogSinSq`) and
`C = ∫₀^{π/2} x log² cos x dx`.

* The reflection `x ↦ π/2 - x` gives `A015 = (π/2) L - C`, since `∫₀^{π/2} log² cos = L`.
* For `|x| < π/2`, `log((1 + e^{2ix})/2) = log cos x + ix`, so
  `Im log³((1 + e^{2ix})/2) = 3x log² cos x - x³`. With `θ = 2x`,
  `C = π⁴/192 + T/6`, where `T = ∫₀^π Im log³((1 + e^{iθ})/2) dθ`.
* The radial argument of `LeanPool.PolylogIntegrals.Lemmas.Radial` (in place of a contour
integral over the upper
  half disk) gives `T = ∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr`, and
  `LeanPool.PolylogIntegrals.Lemmas.LogSinSqSeries` evaluates this as
  `2π⁴/15 + π² log² 2 - log⁴ 2/4 - 6 Li₄(1/2)`.

Altogether `A015 = π⁴/48 + (π²/4) log² 2 - π⁴/192 - T/6`, which is the claimed value.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Proofs

/-- `x log² cos x` is integrable on `[0, π/2]`. -/
public theorem intervalIntegrable_mul_log_cos_sq :
    IntervalIntegrable (fun x ↦ x * log (cos x) ^ 2) volume 0 (π / 2) :=
  LogSinSq.intervalIntegrable_log_cos_sq.continuousOn_mul continuousOn_id

/-- `∫₀^{π/2} x log² cos x dx = π⁴/192 + T/6`, where
`T = ∫₀^π Im log³((1 + e^{iθ})/2) dθ`. -/
public theorem integral_mul_log_cos_sq_eq :
    ∫ x in (0 : ℝ)..(π / 2), x * log (cos x) ^ 2 = π ^ 4 / 192 +
      (∫ θ in (0 : ℝ)..π, (Complex.log ((1 + Complex.exp (θ * Complex.I)) / 2) ^ 3).im) / 6 := by
  set g : ℝ → ℝ := fun θ ↦ (Complex.log ((1 + Complex.exp (θ * Complex.I)) / 2) ^ 3).im with hg
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have h := intervalIntegral.integral_comp_mul_left g (two_ne_zero (α := ℝ)) (a := 0) (b := π / 2)
  rw [mul_zero, show 2 * (π / 2) = π by ring, smul_eq_mul] at h
  have h2 : ∫ x in (0 : ℝ)..(π / 2), g (2 * x) =
      ∫ x in (0 : ℝ)..(π / 2), (3 * (x * log (cos x) ^ 2) - x ^ 3) := by
    rw [intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hπ,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
    have hx' : |x| < π / 2 := by rw [abs_of_pos hx.1]; exact hx.2
    simp only [hg]
    rw [Radial.im_logCube_exp_two_mul hx']
    ring
  rw [h2, intervalIntegral.integral_sub (intervalIntegrable_mul_log_cos_sq.const_mul 3)
    ((by fun_prop : Continuous fun x : ℝ ↦ x ^ 3).intervalIntegrable 0 (π / 2)),
    intervalIntegral.integral_const_mul, integral_pow] at h
  linear_combination h / 3

/-- A015: `∫₀^{π/2} x log² sin x dx = Li₄(1/2) - 19π⁴/2880 + log⁴2/24 + π² log²2/12`. -/
public theorem A015 : ∫ x in (0 : ℝ)..(π / 2), x * Real.log (Real.sin x) ^ 2 =
    Lir 4 (1 / 2) - 19 * π ^ 4 / 2880 + Real.log 2 ^ 4 / 24 + π ^ 2 * Real.log 2 ^ 2 / 12 := by
  have hrefl : ∫ x in (0 : ℝ)..(π / 2), x * log (sin x) ^ 2 =
      π / 2 * (∫ x in (0 : ℝ)..(π / 2), log (cos x) ^ 2) -
        ∫ x in (0 : ℝ)..(π / 2), x * log (cos x) ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_left (fun x ↦ x * log (sin x) ^ 2) (π / 2)
      (a := 0) (b := π / 2)
    simp only [sin_pi_div_two_sub, sub_zero, sub_self] at h
    rw [← h]
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (LogSinSq.intervalIntegrable_log_cos_sq.const_mul _)
      intervalIntegrable_mul_log_cos_sq, intervalIntegral.integral_const_mul]
  rw [hrefl, LogSinSq.integral_log_cos_sq, LogSinSq.integral_log_sin_sq,
    integral_mul_log_cos_sq_eq, Radial.integral_im_logCube LogSinSq.intervalIntegrable_log_cube_div,
    LogSinSq.integral_log_cube_div]
  ring

end LeanPolyLog.Proofs
