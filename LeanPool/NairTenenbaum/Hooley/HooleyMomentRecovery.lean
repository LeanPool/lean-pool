/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyIntegratedPowerBound

/-! # Recovering the original moment Dirichlet series

Undoing the exact integrating factor gives the exponent `2^t−t+t/q`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem hooleyDirichlet_eq_reducedMoment (Q : ℤ[X]) (t σ : ℝ) {q : ℕ} (hq : 1 < q) :
    hooleyDirichlet Q t q σ =
      Real.exp ((2 : ℝ) ^ (t / q) * rootPrimePowerSum Q σ) *
        hooleyReducedMoment Q t q σ ^ ((q : ℝ) - 1) := by
  have hd : (q : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (q : ℤ) - 1 ≠ 0 by omega)
  unfold hooleyReducedMoment
  rw [Real.mul_rpow (Real.exp_nonneg _) (Real.rpow_nonneg (hooleyDirichlet_nonneg Q t q σ) _),
    ← Real.rpow_mul (hooleyDirichlet_nonneg Q t q σ), one_div_mul_cancel hd, Real.rpow_one,
    ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
  rw [show (2 : ℝ) ^ (t / q) * rootPrimePowerSum Q σ +
      (-(2 : ℝ) ^ (t / q) * (1 / ((q : ℝ) - 1)) * rootPrimePowerSum Q σ) * ((q : ℝ) - 1) = 0 by
    field_simp
    ring, Real.exp_zero, one_mul]

theorem hooleyMomentExponentGap_identity (t : ℝ) {q : ℕ} (hq : 1 < q) :
    (2 : ℝ) ^ (t / q) + hooleyMomentExponentGap t q * ((q : ℝ) - 1) =
      (2 : ℝ) ^ t - t + t / q := by
  have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hd : (q : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (q : ℤ) - 1 ≠ 0 by omega)
  unfold hooleyMomentExponentGap
  field_simp
  ring

theorem hooleyDirichlet_le_of_reducedMoment_bound (Q : ℤ[X]) {t σ C K : ℝ}
    {q : ℕ} (hq : 1 < q) (hσ : 1 < σ) (hK : 0 ≤ K)
    (hR : rootPrimePowerSum Q σ ≤ C - Real.log (σ - 1))
    (hU : hooleyReducedMoment Q t q σ ≤ K * (σ - 1) ^ (-hooleyMomentExponentGap t q)) :
    hooleyDirichlet Q t q σ ≤ Real.exp ((2 : ℝ) ^ (t / q) * C) * K ^ ((q : ℝ) - 1) *
      (σ - 1) ^ (-((2 : ℝ) ^ t - t + t / q)) := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hδ : 0 < σ - 1 := by linarith
  have hUnonneg : 0 ≤ hooleyReducedMoment Q t q σ := by
    unfold hooleyReducedMoment
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hooleyDirichlet_nonneg Q t q σ) _)
  have HU := Real.rpow_le_rpow hUnonneg hU (by linarith : 0 ≤ (q : ℝ) - 1)
  have HR := exp_mul_le_of_log_pole hδ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (t / q)) hR
  rw [hooleyDirichlet_eq_reducedMoment Q t σ hq]
  apply (mul_le_mul HR HU (Real.rpow_nonneg hUnonneg _) (by positivity)).trans_eq
  rw [Real.mul_rpow hK (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
  calc
    _ = Real.exp ((2 : ℝ) ^ (t / q) * C) * K ^ ((q : ℝ) - 1) *
        ((σ - 1) ^ (-(2 : ℝ) ^ (t / q)) *
          (σ - 1) ^ (-hooleyMomentExponentGap t q * ((q : ℝ) - 1))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ]
      congr 2
      have H := hooleyMomentExponentGap_identity t hq
      linarith

end NairTenenbaum
