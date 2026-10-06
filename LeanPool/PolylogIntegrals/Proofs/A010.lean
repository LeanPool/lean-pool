/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Proofs.A006

/-!
# A010: `∫₀^{π/4} x² tan² x dx = -G + π²/16 - π³/192 + (π/4) log 2`

On `[0, π/4]` the function `H x = x² tan x + 2x log cos x - x³/3` has derivative
`x² tan² x + 2 log cos x`, because `1/cos² x - 1 = tan² x`. Hence
`∫₀^{π/4} x² tan² x dx = H(π/4) - H(0) - 2 ∫₀^{π/4} log cos x dx`, and A006 gives the last
integral.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A010: `∫₀^{π/4} x² tan² x dx = -G + π²/16 - π³/192 + (π/4) log 2`. -/
public theorem A010 : ∫ x in (0 : ℝ)..(π / 4), x ^ 2 * Real.tan x ^ 2 =
    -G + π ^ 2 / 16 - π ^ 3 / 192 + π / 4 * Real.log 2 := by
  have hcos : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 4), 0 < cos x := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2, pi_pos]
  set H : ℝ → ℝ := fun x ↦ x ^ 2 * tan x + 2 * x * log (cos x) - x ^ 3 / 3 with hH
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 4),
      HasDerivAt H (x ^ 2 * tan x ^ 2 + 2 * log (cos x)) x := by
    intro x hx
    have hc := (hcos x hx).ne'
    have h1 := (hasDerivAt_pow 2 x).mul (hasDerivAt_tan hc)
    have h2 := ((hasDerivAt_id x).const_mul 2).mul ((hasDerivAt_cos x).log hc)
    have h3 := (hasDerivAt_pow 3 x).div_const 3
    convert (h1.add h2).sub h3 using 1
    · rfl
    rw [tan_eq_sin_div_cos, id]
    field_simp
    linear_combination (3 * x ^ 2) * sin_sq_add_cos_sq x
  have hint1 : IntervalIntegrable (fun x ↦ x ^ 2 * tan x ^ 2) MeasureTheory.volume 0 (π / 4) :=
    ContinuousOn.intervalIntegrable fun x hx ↦
      ((continuousAt_id.pow 2).mul
        ((hasDerivAt_tan (hcos x hx).ne').continuousAt.pow 2)).continuousWithinAt
  have hint2 : IntervalIntegrable (fun x ↦ 2 * log (cos x)) MeasureTheory.volume 0 (π / 4) :=
    intervalIntegrable_log_cos.const_mul 2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul,
    A006_cos] at hFTC
  have hlog : log (√2 / 2) = -(log 2 / 2) := by
    rw [log_div (by positivity) two_ne_zero, log_sqrt zero_le_two]
    ring
  simp only [hH, tan_pi_div_four, cos_pi_div_four, hlog] at hFTC
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, cos_zero,
    log_one, mul_zero, add_zero, zero_div, sub_zero] at hFTC
  linear_combination hFTC

end LeanPolyLog.Proofs
