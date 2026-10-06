/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Proofs.A006
public import LeanPool.PolylogIntegrals.Proofs.A007

/-!
# A008: `∫₀^{π/4} x log (1 + tan x) dx = (π²/64) log 2 - πG/8 + 21ζ(3)/64`

On `[0, π/4]` we have `1 + tan x = √2 cos (π/4 - x) / cos x`, since
`cos x + sin x = √2 cos (π/4 - x)`. Hence
`x log (1 + tan x) = (log 2 / 2) x + x log cos (π/4 - x) - x log cos x`.
The substitution `u = π/4 - x` turns the middle term into `∫₀^{π/4} (π/4 - u) log cos u du`, so
`A008 = (π²/64) log 2 + (π/4) ∫₀^{π/4} log cos - 2 ∫₀^{π/4} x log cos x`, and A006 and A007 give
the two integrals.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A008: `∫₀^{π/4} x log (1 + tan x) dx = (π²/64) log 2 - πG/8 + 21ζ(3)/64`. -/
public theorem A008 : ∫ x in (0 : ℝ)..(π / 4), x * Real.log (1 + Real.tan x) =
    π ^ 2 / 64 * Real.log 2 - π * G / 8 + 21 * zeta3 / 64 := by
  have hcos : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 4), 0 < cos x := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2, pi_pos]
  have hcos' : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 4), 0 < cos (π / 4 - x) := by
    intro x hx
    apply hcos
    rw [Set.uIcc_of_le (by positivity)] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have heq : Set.EqOn (fun x ↦ x * log (1 + tan x))
      (fun x ↦ log 2 / 2 * x + (x * log (cos (π / 4 - x)) - x * log (cos x)))
      (Set.uIcc 0 (π / 4)) := by
    intro x hx
    have hc := (hcos x hx).ne'
    have h1 : 1 + tan x = √2 * cos (π / 4 - x) / cos x := by
      rw [tan_eq_sin_div_cos, cos_sub, cos_pi_div_four, sin_pi_div_four]
      field_simp
      linear_combination (-(cos x + sin x)) * Real.sq_sqrt (zero_le_two (α := ℝ))
    simp only
    rw [h1, log_div (by positivity [hcos' x hx]) hc, log_mul (by positivity) (hcos' x hx).ne',
      log_sqrt zero_le_two]
    ring
  have hA : IntervalIntegrable (fun x : ℝ ↦ log 2 / 2 * x) MeasureTheory.volume 0 (π / 4) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x ↦ x * log (cos (π / 4 - x))) MeasureTheory.volume 0
      (π / 4) :=
    ContinuousOn.intervalIntegrable fun x hx ↦ (continuousAt_id.mul
      ((continuous_cos.comp (continuous_const.sub continuous_id)).continuousAt.log
        (hcos' x hx).ne')).continuousWithinAt
  have hC : IntervalIntegrable (fun x ↦ x * log (cos x)) MeasureTheory.volume 0 (π / 4) :=
    ContinuousOn.intervalIntegrable fun x hx ↦
      (continuousAt_id.mul (continuous_cos.continuousAt.log (hcos x hx).ne')).continuousWithinAt
  have hD : IntervalIntegrable (fun x ↦ log (cos x)) MeasureTheory.volume 0 (π / 4) :=
    intervalIntegrable_log_cos
  have hsub : ∫ x in (0 : ℝ)..(π / 4), x * log (cos (π / 4 - x)) =
      π / 4 * (∫ x in (0 : ℝ)..(π / 4), log (cos x)) -
        ∫ x in (0 : ℝ)..(π / 4), x * log (cos x) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 4)
      (fun u ↦ (π / 4 - u) * log (cos u)) (π / 4)
    simp only [sub_sub_cancel, sub_self, sub_zero] at h
    rw [h]
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hD.const_mul _) hC, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add hA (hB.sub hC),
    intervalIntegral.integral_sub hB hC, intervalIntegral.integral_const_mul, integral_id, hsub,
    A006_cos, A007]
  ring

end LeanPolyLog.Proofs
