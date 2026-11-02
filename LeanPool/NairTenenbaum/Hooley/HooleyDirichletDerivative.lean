/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletSeries
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Differentiating the Hooley moment Dirichlet series

A summable logarithmic majorant on each smaller half-line justifies the
termwise derivative used in the weighted mean proof.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem hasDerivAt_hooleyDirichlet_term (Q : ℤ[X]) (t : ℝ) (q n : ℕ) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-s))
      (-(hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-σ))) σ := by
  by_cases hn : n = 0
  · subst n
    simpa only [hooleyMomentCoefficient_zero, zero_mul, neg_zero] using hasDerivAt_const σ (0 : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  convert (HasDerivAt.const_rpow hn' (hasDerivAt_id σ).neg).const_mul
    (hooleyMomentCoefficient Q t q n) using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_hooleyDirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    HasDerivAt (hooleyDirichlet Q t q)
      (-(∑' n : ℕ, hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-σ))) σ := by
  let b := (1 + σ) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbσ : b < σ := by dsimp [b]; linarith
  have hmajor := summable_log_hooleyDirichlet hQ ht hq hb
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Set.Ioi b) :
      ‖-(hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-s))‖ ≤
        hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-b) := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
      (hooleyMomentCoefficient_nonneg Q t q n) (Real.log_natCast_nonneg n))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
    by_cases hn : n = 0
    · simp [hn]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg
      (hooleyMomentCoefficient_nonneg Q t q n) (Real.log_natCast_nonneg n))
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) (neg_le_neg hs.le)
  have H := hasDerivAt_tsum_of_isPreconnected hmajor isOpen_Ioi (convex_Ioi b).isPreconnected
    (fun n s _ => hasDerivAt_hooleyDirichlet_term Q t q n s) hbound hbσ
    (summable_hooleyDirichlet hQ ht hq hσ) hbσ
  unfold hooleyDirichlet
  simpa only [tsum_neg] using H

theorem deriv_hooleyDirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    deriv (hooleyDirichlet Q t q) σ =
      -(∑' n : ℕ, hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-σ)) :=
  (hasDerivAt_hooleyDirichlet hQ ht hq hσ).deriv

end NairTenenbaum
