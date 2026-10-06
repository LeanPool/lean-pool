/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.TrilogLogOneAddSq
public import LeanPool.PolylogIntegrals.Lemmas.TrilogLogSubLogSq

/-!
# A014: `∫₀¹ log x · log(1+x)/(1+x²) dx = 11π³/128 + (3π/32) log²2 - 2G log 2 - 3 Im Li₃((1+i)/2)`

As in the tutorial, `log x · log(1+x) = ½ (log² x + log²(1+x) - log²(x/(1+x)))` splits the
integral as `½ (𝒦 + ℳ - 𝒥)`, where
* `𝒦 = ∫₀¹ log² x/(1+x²) dx = π³/16` (`LeanPolyLog.Arctan.integral_log_sq_div_one_add_sq`),
* `ℳ = ∫₀¹ log²(1+x)/(1+x²) dx = 7π³/64 + (3π/16) log²2 - 2G log 2 - 4 Im Li₃((1+i)/2)`
  (`LeanPolyLog.Trilog.integral_log_one_add_sq_div_one_add_sq`),
* `𝒥 = ∫₀¹ log²(x/(1+x))/(1+x²) dx = 2G log 2 + 2 Im Li₃((1+i)/2)`
  (`LeanPolyLog.Trilog.integral_log_sub_log_sq_div_one_add_sq`).

The tutorial evaluates `ℳ` through `Li₃(1+i)`, outside the unit disk, where the series `Li`
is not defined. Here `ℳ` and `𝒥` come from explicit complex primitives whose polylogarithms are
only evaluated at points of norm at most `1`: `ψ(x) = ((1-x) + (1+x)i)/2` and
`φ(x) = (x-i)/(x+1)` for `ℳ`, and `χ(x) = x(1-i)/(1+x)` for `𝒥`.
-/

open Real MeasureTheory

namespace LeanPolyLog.Proofs

/-- A014 (simplified form):
`∫₀¹ log x · log(1+x) / (1+x²) dx = 11π³/128 + (3π/32) log²2 - 2G log 2 - 3 Im Li₃((1+i)/2)`. -/
public theorem A014 : ∫ x in (0 : ℝ)..1, Real.log x * Real.log (x + 1) / (x ^ 2 + 1) =
    11 * π ^ 3 / 128 + 3 * π / 32 * Real.log 2 ^ 2 - 2 * G * Real.log 2
      - 3 * (Li 3 ((1 + Complex.I) / 2)).im := by
  have hK : IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2 / (1 + x ^ 2)) volume 0 1 := by
    have hlog2 : IntervalIntegrable (fun t : ℝ ↦ Real.log t ^ 2) volume 0 1 := by
      simpa only [pow_zero, one_mul] using Arctan.intervalIntegrable_pow_mul_log_sq 0
    have h := hlog2.mul_continuousOn (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹)
      Arctan.continuous_inv_one_add_sq.continuousOn
    simpa only [div_eq_mul_inv] using h
  have hM : IntervalIntegrable (fun x : ℝ ↦ Real.log (1 + x) ^ 2 / (1 + x ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (Trilog.continuousOn_log_one_add.pow 2).div (by fun_prop) fun t _ ↦ by positivity
  have hJ := Trilog.intervalIntegrable_log_sub_log_sq_div_one_add_sq
  have hpt : (fun x : ℝ ↦ Real.log x * Real.log (x + 1) / (x ^ 2 + 1)) = fun x ↦
      (Real.log x ^ 2 / (1 + x ^ 2) + Real.log (1 + x) ^ 2 / (1 + x ^ 2) -
        (Real.log x - Real.log (1 + x)) ^ 2 / (1 + x ^ 2)) / 2 := by
    funext x
    rw [add_comm x 1]
    ring
  rw [hpt, intervalIntegral.integral_div, intervalIntegral.integral_sub (hK.add hM) hJ,
    intervalIntegral.integral_add hK hM, Arctan.integral_log_sq_div_one_add_sq,
    Trilog.integral_log_one_add_sq_div_one_add_sq, Trilog.integral_log_sub_log_sq_div_one_add_sq]
  ring

end LeanPolyLog.Proofs
