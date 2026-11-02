/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.SeriesInterpolation
public import LeanPool.NairTenenbaum.Hooley.HooleyInfinitePrimeStep

/-! # Summing the mixed error in the Dirichlet series

Hölder interpolation keeps the moment series in the error term, instead of
replacing it by a divisor bound. This is the nonlinear term needed in the
differential inequality.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

/-- A uniform constant controlling the prime-step error for Hooley moments. -/
noncomputable def hooleyPrimeErrorConstant (Q : ℤ[X]) (q : ℕ) : ℝ :=
  (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) * (4 : ℝ) ^ q)

theorem hooleyPrimeErrorConstant_nonneg (Q : ℤ[X]) (q : ℕ) :
    0 ≤ hooleyPrimeErrorConstant Q q := by
  unfold hooleyPrimeErrorConstant
  positivity

theorem hooleyPrimeErrorBound_factor (Q : ℤ[X]) (q n : ℕ) :
    hooleyPrimeErrorBound Q q n = hooleyPrimeErrorConstant Q q *
      ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
        hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1))) := by
  unfold hooleyPrimeErrorBound hooleyPrimeErrorConstant
  ring

theorem weighted_moment_error_factor {C T M w r : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hw : 0 ≤ w) (hr : 1 < r) (t : ℝ) :
    w * (C * (T ^ (r / (r - 1)) * M ^ ((r - 2) / (r - 1)))) ^ (t / r) =
      C ^ (t / r) * (T ^ t * w) ^ (1 / (r - 1)) *
        (M ^ (t / r) * w) ^ (1 - 1 / (r - 1)) := by
  have hr₀ : r ≠ 0 := by linarith
  have hr₁ : r - 1 ≠ 0 := by linarith
  have hTexp : r / (r - 1) * (t / r) = t * (1 / (r - 1)) := by field_simp
  have hMexp : (r - 2) / (r - 1) * (t / r) = t / r * (1 - 1 / (r - 1)) := by
    field_simp
    ring
  have hwexp : w ^ (1 / (r - 1)) * w ^ (1 - 1 / (r - 1)) = w := by
    rw [← Real.rpow_add' hw (by ring_nf; norm_num), add_sub_cancel, Real.rpow_one]
  rw [Real.mul_rpow hC (mul_nonneg (Real.rpow_nonneg hT _) (Real.rpow_nonneg hM _)),
    Real.mul_rpow (Real.rpow_nonneg hT _) (Real.rpow_nonneg hM _),
    Real.mul_rpow (Real.rpow_nonneg hT _) hw, Real.mul_rpow (Real.rpow_nonneg hM _) hw]
  simp only [← Real.rpow_mul hT, ← Real.rpow_mul hM, hTexp, hMexp]
  calc
    _ = C ^ (t / r) * T ^ (t * (1 / (r - 1))) * M ^ (t / r * (1 - 1 / (r - 1))) * w := by ring
    _ = _ := by
      conv_lhs => rw [← hwexp]
      ring

/-- The Dirichlet-series term contributed by the Hooley prime-step error. -/
noncomputable def hooleyErrorDirichletTerm (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then
    (rootCount Q n : ℝ) * (n : ℝ) ^ (-σ) * hooleyPrimeErrorBound Q q n ^ (t / q)
  else 0

theorem hooleyErrorDirichletTerm_factor (Q : ℤ[X]) (t σ : ℝ) {q : ℕ} (hq : 2 < q) (n : ℕ) :
    hooleyErrorDirichletTerm Q t q σ n = hooleyPrimeErrorConstant Q q ^ (t / q) *
      (hooleyMomentCoefficient Q t 1 n * (n : ℝ) ^ (-σ)) ^ (1 / ((q : ℝ) - 1)) *
      (hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) ^ (1 - 1 / ((q : ℝ) - 1)) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have ha : 0 < 1 / ((q : ℝ) - 1) := one_div_pos.mpr (by linarith)
  by_cases hn : Squarefree n
  · simp only [hooleyErrorDirichletTerm, hooleyMomentCoefficient, ite_eq_left hn,
      hooleyMoment_one, Nat.cast_one, div_one, hooleyPrimeErrorBound_factor]
    simpa only [mul_assoc] using weighted_moment_error_factor (hooleyPrimeErrorConstant_nonneg Q
        q) (Nat.cast_nonneg n.divisors.card)
      (hooleyMoment_nonneg q n) (mul_nonneg (Nat.cast_nonneg (rootCount Q n))
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))) (by linarith : (1 : ℝ) < q) t
  · simp only [hooleyErrorDirichletTerm, hooleyMomentCoefficient, ite_eq_right hn, zero_mul,
      Real.zero_rpow ha.ne', mul_zero]

theorem summable_and_hooleyErrorDirichlet_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (hσ : 1 < σ) :
    Summable (hooleyErrorDirichletTerm Q t q σ) ∧
      (∑' n, hooleyErrorDirichletTerm Q t q σ n) ≤
        hooleyPrimeErrorConstant Q q ^ (t / q) *
          hooleyDirichlet Q t 1 σ ^ (1 / ((q : ℝ) - 1)) *
          hooleyDirichlet Q t q σ ^ (1 - 1 / ((q : ℝ) - 1)) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have ha : 0 < 1 / ((q : ℝ) - 1) := one_div_pos.mpr (by linarith)
  have ha₁ : 1 / ((q : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have H := summable_and_tsum_mul_rpow_le
    (fun n => hooleyMomentCoefficient Q t 1 n * (n : ℝ) ^ (-σ))
    (fun n => hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ))
    (fun n => mul_nonneg (hooleyMomentCoefficient_nonneg Q t 1 n) (Real.rpow_nonneg
        (Nat.cast_nonneg _) _))
    (fun n => mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n) (Real.rpow_nonneg
        (Nat.cast_nonneg _) _))
    (summable_hooleyDirichlet hQ ht (by decide) hσ)
    (summable_hooleyDirichlet hQ ht (by omega) hσ) ha ha₁
  constructor
  · change Summable (fun n => hooleyErrorDirichletTerm Q t q σ n)
    simpa only [hooleyErrorDirichletTerm_factor Q t σ hq, mul_assoc] using
      H.1.mul_left (hooleyPrimeErrorConstant Q q ^ (t / q))
  · simp only [hooleyErrorDirichletTerm_factor Q t σ hq, mul_assoc, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left H.2 (Real.rpow_nonneg (hooleyPrimeErrorConstant_nonneg Q q) _)

end NairTenenbaum
