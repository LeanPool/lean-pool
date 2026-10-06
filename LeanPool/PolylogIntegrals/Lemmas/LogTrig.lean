/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Defs
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Log-trigonometric integrals on `[0, π/4]`

This file collects the lemmas behind A006, the values of `∫₀^{π/4} log cos x dx` and
`∫₀^{π/4} log sin x dx`.

## Main results

* `LeanPolyLog.LogTrig.integral_pow_mul_neg_log`: `∫₀¹ t^m (-log t) dt = 1/(m+1)²`.
* `LeanPolyLog.LogTrig.integral_neg_log_div_one_add_sq`: `∫₀¹ -log t / (1+t²) dt = G`.
* `LeanPolyLog.LogTrig.integral_log_cos_sub_log_sin`: `∫₀^{π/4} (log cos x - log sin x) dx = G`.
* `LeanPolyLog.LogTrig.integral_log_sin_add_integral_log_cos`:
  `∫₀^{π/4} log sin x dx + ∫₀^{π/4} log cos x dx = -(π/2) log 2`.
* `LeanPolyLog.LogTrig.integral_log_cos_sub_integral_log_sin`:
  `∫₀^{π/4} log cos x dx - ∫₀^{π/4} log sin x dx = G`.

## Proof sketch

* The sum: `cos x = sin (π/2 - x)` turns `∫₀^{π/4} log cos` into `∫_{π/4}^{π/2} log sin`, and
  Mathlib knows `∫₀^{π/2} log sin = -(π/2) log 2`.
* The difference: the substitution `x = arctan t` turns it into `∫₀¹ -log t / (1+t²) dt`. Expanding
  `1/(1+t²) = ∑ (-1)ⁿ t²ⁿ` and integrating term by term gives `∑ (-1)ⁿ/(2n+1)² = G`. The
  interchange of sum and integral is justified by `∫₀¹ t²ⁿ (-log t) dt = 1/(2n+1)²`, which is
  summable.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.LogTrig

/-! ### The moments `∫₀¹ t^m (-log t) dt` -/

/-- An antiderivative of `t ^ m * -log t`, namely `t^(m+1)/(m+1)² - t^(m+1) log t/(m+1)`.
It is continuous on all of `ℝ` and vanishes at `0`. -/
@[expose] public noncomputable def powMulNegLogPrimitive (m : ℕ) (x : ℝ) : ℝ :=
  x ^ (m + 1) / ((m : ℝ) + 1) ^ 2 - x ^ (m + 1) * log x / ((m : ℝ) + 1)

/-- Away from `0`, the derivative of `powMulNegLogPrimitive m` is `t ^ m * -log t`. -/
public theorem hasDerivAt_powMulNegLogPrimitive (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (powMulNegLogPrimitive m) (t ^ m * -log t) t := by
  have h₁ := (hasDerivAt_pow (m + 1) t).div_const (((m : ℝ) + 1) ^ 2)
  have h₂ := ((hasDerivAt_pow (m + 1) t).mul (hasDerivAt_log ht)).div_const ((m : ℝ) + 1)
  refine (h₁.sub h₂).congr_deriv ?_
  have ht' : t ^ (m + 1) * t⁻¹ = t ^ m := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ ht, mul_one]
  rw [Nat.add_sub_cancel, ht']
  push_cast
  field_simp
  ring

/-- `x ^ (m + 1) * log x` is continuous, including at `0`. -/
public theorem continuous_pow_succ_mul_log (m :
    ℕ) : Continuous fun x : ℝ ↦ x ^ (m + 1) * log x := by
  have : (fun x : ℝ ↦ x ^ (m + 1) * log x) = fun x ↦ x ^ m * (x * log x) := by
    ext x
    ring
  rw [this]
  exact (continuous_pow m).mul continuous_mul_log

/-- The antiderivative `powMulNegLogPrimitive m` is continuous. -/
public theorem continuous_powMulNegLogPrimitive (m : ℕ) : Continuous (powMulNegLogPrimitive m) :=
  ((continuous_pow (m + 1)).div_const _).sub ((continuous_pow_succ_mul_log m).div_const _)

/-- `t ^ m * -log t` is integrable on `(0, 1]`: it is the nonnegative derivative of a
continuous function. -/
public theorem integrableOn_pow_mul_neg_log (m : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ m * -log t) (Ioc 0 1) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (continuous_powMulNegLogPrimitive m).continuousOn
  · intro x hx
    exact hasDerivAt_powMulNegLogPrimitive m hx.1.ne'
  · intro x hx
    exact mul_nonneg (pow_nonneg hx.1.le m) (neg_nonneg.mpr (log_neg hx.1 hx.2).le)

/-- `∫₀¹ t^m (-log t) dt = 1/(m+1)²`. -/
public theorem integral_pow_mul_neg_log (m : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ m * -log t = 1 / ((m : ℝ) + 1) ^ 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuous_powMulNegLogPrimitive m).continuousOn
    (fun x hx ↦ hasDerivAt_powMulNegLogPrimitive m hx.1.ne')
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (integrableOn_pow_mul_neg_log m))]
  simp [powMulNegLogPrimitive]

/-! ### The Catalan integral `∫₀¹ -log t / (1 + t²) dt = G` -/

/-- On `(0, 1]`, `-log t / (1 + t²) = ∑ (-1)ⁿ t²ⁿ (-log t)`. At `t = 1` both sides vanish. -/
public theorem hasSum_neg_one_pow_mul_pow_mul_neg_log {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n * (t ^ (2 * n) * -log t)) (-log t / (1 + t ^ 2)) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    simp
  · have habs : |-t ^ 2| < 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      nlinarith [ht.1]
    have := (hasSum_geometric_of_abs_lt_one habs).mul_right (-log t)
    convert this using 1
    · ext n
      rw [neg_pow (t ^ 2), ← pow_mul]
      ring
    · rw [sub_neg_eq_add, div_eq_mul_inv]
      ring

/-- `∑ 1/(2n+1)²` converges. -/
public theorem summable_one_div_two_mul_add_one_sq :
    Summable fun n : ℕ ↦ 1 / (2 * (n : ℝ) + 1) ^ 2 := by
  have h : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2 := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) h
  gcongr
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `∫₀¹ -log t / (1 + t²) dt = G`, by termwise integration of `∑ (-1)ⁿ t²ⁿ (-log t)`. -/
public theorem integral_neg_log_div_one_add_sq :
    ∫ t in (0 : ℝ)..1, -log t / (1 + t ^ 2) = G := by
  have hint : ∀ n : ℕ,
      IntegrableOn (fun t : ℝ ↦ (-1 : ℝ) ^ n * (t ^ (2 * n) * -log t)) (Ioc 0 1) :=
    fun n ↦ (integrableOn_pow_mul_neg_log (2 * n)).const_mul _
  have hval : ∀ n : ℕ,
      ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * n) * -log t = 1 / (2 * (n : ℝ) + 1) ^ 2 := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow_mul_neg_log]
    push_cast
    ring
  have hnorm : ∀ n : ℕ,
      ∫ t in Ioc (0 : ℝ) 1, ‖(-1 : ℝ) ^ n * (t ^ (2 * n) * -log t)‖ =
        1 / (2 * (n : ℝ) + 1) ^ 2 := by
    intro n
    rw [← hval n]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have : 0 ≤ t ^ (2 * n) * -log t :=
      mul_nonneg (pow_nonneg ht.1.le _) (neg_nonneg.mpr (log_nonpos ht.1.le ht.2))
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_of_nonneg this]
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_fun measurableSet_Ioc
      fun t ht ↦ (hasSum_neg_one_pow_mul_pow_mul_neg_log ht).tsum_eq.symm,
    ← integral_tsum_of_summable_integral_norm hint
      (by simpa only [hnorm] using summable_one_div_two_mul_add_one_sq)]
  unfold G
  congr 1
  ext n
  rw [MeasureTheory.integral_const_mul, hval]
  ring

/-! ### The integrals of `log cos` and `log sin` on `[0, π/4]` -/

/-- `∫₀^{π/4} (log cos x - log sin x) dx = G`, via the substitution `x = arctan t`. -/
public theorem integral_log_cos_sub_log_sin :
    ∫ x in (0 : ℝ)..(π / 4), (log (cos x) - log (sin x)) = G := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := 1)
    (f := arctan) (f' := fun t ↦ 1 / (1 + t ^ 2)) (g := fun x ↦ log (cos x) - log (sin x))
    continuous_arctan.continuousOn (fun x _ ↦ hasDerivAt_arctan x) (fun x _ ↦ by positivity)
  rw [arctan_zero, arctan_one] at h
  rw [← h, ← integral_neg_log_div_one_add_sq]
  congr 1
  ext t
  simp only [Function.comp, cos_arctan, sin_arctan]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hs : √(1 + t ^ 2) ≠ 0 := by positivity
    rw [log_div ht hs, one_div, log_inv]
    ring

/-- `∫₀^{π/4} log cos x dx = ∫_{π/4}^{π/2} log sin x dx`, since `cos x = sin (π/2 - x)`. -/
public theorem integral_log_cos_eq_integral_log_sin :
    ∫ x in (0 : ℝ)..(π / 4), log (cos x) = ∫ x in (π / 4)..(π / 2), log (sin x) := by
  simp_rw [← sin_pi_div_two_sub]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x))]
  congr 1 <;> ring

/-- `∫₀^{π/4} log sin x dx + ∫₀^{π/4} log cos x dx = -(π/2) log 2`. -/
public theorem integral_log_sin_add_integral_log_cos :
    (∫ x in (0 : ℝ)..(π / 4), log (sin x)) + ∫ x in (0 : ℝ)..(π / 4), log (cos x) =
      -(π / 2 * log 2) := by
  have hs : ∀ a b : ℝ, IntervalIntegrable (fun x ↦ log (sin x)) volume a b :=
    fun _ _ ↦ intervalIntegrable_log_sin
  rw [integral_log_cos_eq_integral_log_sin,
    intervalIntegral.integral_add_adjacent_intervals (hs _ _) (hs _ _),
    integral_log_sin_zero_pi_div_two]
  ring

/-- `∫₀^{π/4} log cos x dx - ∫₀^{π/4} log sin x dx = G`. -/
public theorem integral_log_cos_sub_integral_log_sin :
    (∫ x in (0 : ℝ)..(π / 4), log (cos x)) - ∫ x in (0 : ℝ)..(π / 4), log (sin x) = G := by
  have hc : IntervalIntegrable (fun x ↦ log (cos x)) volume 0 (π / 4) := intervalIntegrable_log_cos
  have hs : IntervalIntegrable (fun x ↦ log (sin x)) volume 0 (π / 4) := intervalIntegrable_log_sin
  rw [← intervalIntegral.integral_sub hc hs]
  exact integral_log_cos_sub_log_sin

end LeanPolyLog.LogTrig
