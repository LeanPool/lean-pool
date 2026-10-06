/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Arctan

/-!
# A012: `∫₀¹ arctan x / (x+1) · log x dx = -π³/64 + (G/2) log 2`

Integrate by parts with `u = arctan x` and `v = Li₂(-x) + log x · log(1+x)`, an antiderivative of
`log x/(1+x)` that is continuous on `[0, 1]` (Lean's `log 0 = 0` gives `v(0) = 0`). The boundary
term is `(π/4) Li₂(-1) = -π³/48`, so the integral equals
`-π³/48 - ∫₀¹ Li₂(-x)/(1+x²) dx - M`, where `M = ∫₀¹ log x · log(1+x)/(1+x²) dx`.

Writing `Li₂(-x) = ∫₀¹ x log y/(1+xy) dy` and swapping the order of integration turns
`∫₀¹ Li₂(-x)/(1+x²) dx` into `∫₀¹ log y · K(y) dy` with the kernel
`K(y) = (log 2/2 + πy/4 - log(1+y))/(1+y²)`. The `log(1+y)` part of the kernel gives `-M`, which
cancels, and what is left is `(log 2/2) ∫₀¹ log y/(1+y²) dy + (π/4) ∫₀¹ y log y/(1+y²) dy`
`= -(G/2) log 2 - π³/192`.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Proofs

open Arctan

/-- A012: `∫₀¹ arctan x / (x+1) · log x dx = -π³/64 + (G/2) log 2`. -/
public theorem A012 :
    ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x = -π ^ 3 / 64 + G / 2 * Real.log 2 := by
  have hV : ContinuousOn (fun x ↦ Lir 2 (-x) + log x * log (1 + x)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_Lir_neg le_rfl).add continuous_log_mul_log_one_add.continuousOn
  have hv' : IntervalIntegrable (fun x : ℝ ↦ log x / (1 + x)) volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (g := fun x : ℝ ↦ (1 + x)⁻¹) (a := 0) (b := 1) (by
        refine ContinuousOn.inv₀ (by fun_prop) fun x hx ↦ ?_
        rw [uIcc_of_le zero_le_one] at hx
        linarith [hx.1])
    simpa only [div_eq_mul_inv] using h
  -- integration by parts against `arctan`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := arctan) (u' := fun x ↦ 1 / (1 + x ^ 2)) (a := 0) (b := 1)
    continuous_arctan.continuousOn hV (fun x _ ↦ hasDerivAt_arctan x)
    (fun x hx ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
      exact hasDerivAt_Lir_two_neg_add hx.1 hx.2)
    ((continuous_const.div (by fun_prop) fun x ↦ by positivity).intervalIntegrable 0 1) hv'
  rw [arctan_one, arctan_zero, Dilog.Lir_two_neg_one, log_one, zero_mul, zero_mul, add_zero,
    sub_zero] at hibp
  -- integrability of the pieces
  have iA : IntervalIntegrable (fun y : ℝ ↦ log y / (1 + y ^ 2)) volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (a := 0) (b := 1) continuous_inv_one_add_sq.continuousOn
    simpa only [div_eq_mul_inv] using h
  have iB : IntervalIntegrable (fun y : ℝ ↦ y * log y / (1 + y ^ 2)) volume 0 1 :=
    (continuous_mul_log.div (by fun_prop) fun y ↦ by positivity).intervalIntegrable 0 1
  have iC : IntervalIntegrable (fun y : ℝ ↦ log y * log (1 + y) / (1 + y ^ 2)) volume 0 1 :=
    (continuous_log_mul_log_one_add.div (by fun_prop) fun y ↦ by positivity).intervalIntegrable 0 1
  have iLi : IntervalIntegrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹ * Lir 2 (-x)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuous_inv_one_add_sq.continuousOn.mul (continuousOn_Lir_neg le_rfl)
  -- split the remaining integral
  have hsplit : ∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2) * (Lir 2 (-x) + log x * log (1 + x)) =
      (∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 2 (-x)) +
        ∫ x in (0 : ℝ)..1, log x * log (1 + x) / (1 + x ^ 2) := by
    rw [← intervalIntegral.integral_add iLi iC]
    congr 1
    ext x
    ring
  -- the double integral: `Li₂(-x) = ∫₀¹ x log y/(1+xy) dy`, then Fubini and the kernel
  have hLi : ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 2 (-x) =
      log 2 / 2 * -G + π / 4 * -(π ^ 2 / 48) -
        ∫ y in (0 : ℝ)..1, log y * log (1 + y) / (1 + y ^ 2) := by
    have h1 : ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * Lir 2 (-x) =
        ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * ∫ y in (0 : ℝ)..1, x * log y / (1 + x * y) := by
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp only [integral_mul_log_div_one_add_mul hx.1 hx.2]
    have h2 : ∫ y in (0 : ℝ)..1, log y * ∫ x in (0 : ℝ)..1, x / ((1 + x ^ 2) * (1 + x * y)) =
        ∫ y in (0 : ℝ)..1, (log 2 / 2 * (log y / (1 + y ^ 2)) +
          π / 4 * (y * log y / (1 + y ^ 2)) - log y * log (1 + y) / (1 + y ^ 2)) := by
      refine intervalIntegral.integral_congr fun y hy ↦ ?_
      rw [uIcc_of_le zero_le_one] at hy
      simp only [integral_kernel hy.1]
      ring
    rw [h1, integral_integral_swap_kernel intervalIntegral.intervalIntegrable_log', h2,
      intervalIntegral.integral_sub ((iA.const_mul _).add (iB.const_mul _)) iC,
      intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_log_div_one_add_sq, integral_mul_log_div_one_add_sq]
  have hlhs : ∫ x in (0 : ℝ)..1, Real.arctan x / (x + 1) * Real.log x =
      ∫ x in (0 : ℝ)..1, arctan x * (log x / (1 + x)) := by
    congr 1
    ext x
    ring
  rw [hlhs, hibp, hsplit, hLi]
  ring

end LeanPolyLog.Proofs
