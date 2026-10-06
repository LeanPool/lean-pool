/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Series
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A004: `∫₀¹ log(1+x²)/x dx = π²/24`

On `(0, 1)` we have `log(1+x²)/x = ∑_{n ≥ 0} (-1)ⁿ x^(2n+1)/(n+1)`. The integrals of the
absolute values of the terms are `1/(2(n+1)²)`, which are summable, so the series may be
integrated term by term (`MeasureTheory.hasSum_integral_of_summable_integral_norm`). The result
is `∑_{n ≥ 0} (-1)ⁿ/(2(n+1)²) = η(2)/2 = π²/24`.

In Lean the integrand at `x = 0` is `log 1 / 0 = 0`; a single point does not affect the integral.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A004 (corrected): `∫₀¹ log(1+x²)/x dx = π²/24`. -/
public theorem A004 : ∫ x in (0 : ℝ)..1, Real.log (1 + x ^ 2) / x = π ^ 2 / 24 := by
  set F : ℕ → ℝ → ℝ := fun n x => (-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ (2 * n + 1)
  have hint : ∀ n, MeasureTheory.Integrable (F n)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun n =>
    (by fun_prop : Continuous (F n)).integrableOn_Ioc
  have hval : ∀ n : ℕ,
      ∫ x in Set.Ioc (0 : ℝ) 1, F n x = (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 / 2 := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
      integral_pow]
    push_cast
    field_simp
    ring
  have hnorm : ∀ n : ℕ, ∫ x in Set.Ioc (0 : ℝ) 1, ‖F n x‖ = 1 / ((n : ℝ) + 1) ^ 2 / 2 := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have h : Set.EqOn (fun x => ‖F n x‖) (fun x => 1 / ((n : ℝ) + 1) * x ^ (2 * n + 1))
        (Set.uIcc 0 1) := by
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      simp only [F, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
        abs_of_nonneg hx.1]
      rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    field_simp
    ring
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm hint (by
    simp_rw [hnorm]
    exact ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).div_const 2
      |>.congr fun n => by push_cast; ring)
  simp_rw [hval] at hsum
  have heq : ∫ x in Set.Ioc (0 : ℝ) 1, ∑' n, F n x =
      ∫ x in (0 : ℝ)..1, Real.log (1 + x ^ 2) / x := by
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx =>
      (Series.hasSum_log_one_add_sq_div hx).tsum_eq
  rw [heq] at hsum
  refine hsum.unique ?_
  convert Series.hasSum_eta_two.div_const 2 using 1
  ring

end LeanPolyLog.Proofs
