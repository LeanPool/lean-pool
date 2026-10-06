/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Fourier

/-!
# A007: `∫₀^{π/4} x log cos x dx = πG/8 - (π²/32) log 2 - (21/128) ζ(3)`

`LeanPolyLog.Lemmas.Fourier` computes `∫₀^{π/4} x log (2 + 2 cos 2x) dx = (π/4) G - (21/64) ζ(3)`
by integrating the Fourier series of `log (1 + 2r cos 2x + r²)` term by term and letting `r → 1⁻`.
On `[0, π/4]` we have `2 + 2 cos 2x = 4 cos² x`, so `log (2 + 2 cos 2x) = 2 log 2 + 2 log cos x`,
and `∫₀^{π/4} x dx = π²/32`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A007: `∫₀^{π/4} x log cos x dx = πG/8 - (π²/32) log 2 - (21/128) ζ(3)`. -/
public theorem A007 : ∫ x in (0 : ℝ)..(π / 4), x * Real.log (Real.cos x) =
    π * G / 8 - π ^ 2 / 32 * Real.log 2 - 21 / 128 * zeta3 := by
  have hcos : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 4), 0 < cos x := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2, pi_pos]
  have heq : Set.EqOn (fun x ↦ x * log (1 + 2 * 1 * cos (2 * x) + 1 ^ 2))
      (fun x ↦ 2 * log 2 * x + 2 * (x * log (cos x))) (Set.uIcc 0 (π / 4)) := by
    intro x hx
    have hc := (hcos x hx).ne'
    simp only
    rw [cos_two_mul, show 1 + 2 * 1 * (2 * cos x ^ 2 - 1) + (1 : ℝ) ^ 2 = 2 ^ 2 * cos x ^ 2 by ring,
      log_mul (by positivity) (pow_ne_zero 2 hc), log_pow, log_pow]
    push_cast
    ring
  have hint1 : IntervalIntegrable (fun x : ℝ ↦ 2 * log 2 * x) MeasureTheory.volume 0 (π / 4) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x ↦ 2 * (x * log (cos x))) MeasureTheory.volume 0 (π / 4) :=
    (ContinuousOn.intervalIntegrable fun x hx ↦
      (continuousAt_id.mul (continuous_cos.continuousAt.log (hcos x hx).ne')).continuousWithinAt
      ).const_mul 2
  have h := Fourier.integral_mul_log_two_add_two_cos
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id] at h
  linear_combination h / 2

end LeanPolyLog.Proofs
