/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.DifferentialInterpolation
public import LeanPool.NairTenenbaum.Arithmetic.RootPrimeSeriesDerivative

/-! # Removing the linear term in the Hooley differential inequality

The exact prime root series supplies the integrating factor. After the
divisor Euler bound, the derivative majorant contains only the two prime
series and explicit constants.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial MeasureTheory

/-- The Hooley moment after removing the principal singular factor. -/
noncomputable def hooleyReducedMoment (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (-(2 : ℝ) ^ (t / q) * (1 / ((q : ℝ) - 1)) * rootPrimePowerSum Q σ) *
    hooleyDirichlet Q t q σ ^ (1 / ((q : ℝ) - 1))

theorem differentiableAt_hooleyReducedMoment {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    DifferentiableAt ℝ (hooleyReducedMoment Q t q) σ := by
  unfold hooleyReducedMoment
  exact (hasDerivAt_exp_mul_rpow (hasDerivAt_hooleyDirichlet hQ ht hq hσ)
    (hasDerivAt_rootPrimePowerSum hQ hσ)
    (lt_of_lt_of_le zero_lt_one (one_le_hooleyDirichlet hQ ht hq hσ))).differentiableAt

theorem neg_deriv_hooleyReducedMoment_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (htq : t ≤ q) (hσ : 1 < σ) :
    -deriv (hooleyReducedMoment Q t q) σ ≤
      (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
        rootPrimeDirichletSum Q σ ^ (1 - t / q) *
        Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * rootPrimePowerSum Q σ) := by
  let h : ℝ := 1 / ((q : ℝ) - 1)
  let θ : ℝ := t / q
  let A : ℝ := (2 : ℝ) ^ θ
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 ≤ h := (one_div_pos.mpr (by linarith : 0 < (q : ℝ) - 1)).le
  have hpos : 0 < hooleyDirichlet Q t q σ :=
    lt_of_lt_of_le zero_lt_one (one_le_hooleyDirichlet hQ ht (by omega) hσ)
  have hineq : -deriv (hooleyDirichlet Q t q) σ ≤
      A * rootPrimeDirichletSum Q σ * hooleyDirichlet Q t q σ +
      (rootPrimeDirichletSum Q σ ^ (1 - θ) *
        (hooleyPrimeErrorConstant Q q ^ θ * hooleyDirichlet Q t 1 σ ^ h)) *
          hooleyDirichlet Q t q σ ^ (1 - h) := by
    simpa only [mul_assoc] using neg_deriv_hooleyDirichlet_le hQ ht hq htq hσ
  have Hbase := neg_deriv_exp_mul_rpow_le
    (hasDerivAt_hooleyDirichlet hQ ht (by omega : 0 < q) hσ).differentiableAt.hasDerivAt
    (hasDerivAt_rootPrimePowerSum hQ hσ) hpos hh hineq
  have hD : hooleyDirichlet Q t 1 σ ^ h ≤ Real.exp (((2 : ℝ) ^ t * rootPrimePowerSum Q σ) * h) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (hooleyDirichlet_nonneg Q t 1 σ)
      (hooleyDivisorDirichlet_le_exp_prime_sum hQ t hσ) hh
  change -deriv (fun s => Real.exp (-A * h * rootPrimePowerSum Q s) * hooleyDirichlet Q t q s ^ h)
      σ ≤ _
  calc
    _ ≤ h * Real.exp (-A * h * rootPrimePowerSum Q σ) *
        (rootPrimeDirichletSum Q σ ^ (1 - θ) *
          (hooleyPrimeErrorConstant Q q ^ θ * hooleyDirichlet Q t 1 σ ^ h)) := Hbase
    _ ≤ h * Real.exp (-A * h * rootPrimePowerSum Q σ) *
        (rootPrimeDirichletSum Q σ ^ (1 - θ) *
          (hooleyPrimeErrorConstant Q q ^ θ * Real.exp (((2 : ℝ) ^ t * rootPrimePowerSum Q σ) *
              h))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hh (Real.exp_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (rootPrimeDirichletSum_nonneg Q σ) _)
      exact mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg (hooleyPrimeErrorConstant_nonneg Q q) _)
    _ = _ := by
      rw [show ((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * rootPrimePowerSum Q σ =
          -A * h * rootPrimePowerSum Q σ + ((2 : ℝ) ^ t * rootPrimePowerSum Q σ) * h by
        dsimp [A, θ, h]; ring, Real.exp_add]
      dsimp [h, θ]
      ring

end NairTenenbaum
