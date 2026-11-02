/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletError

/-! # The weighted Hooley differential inequality

The prime recurrence and Hölder interpolation yield an unconditional
differential inequality. The prime series and the divisor Dirichlet series
are explicit; sharp bounds for them are not assumed here.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem hooleyPrimeDirichlet_row_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 1 < q) (htq : t ≤ q) (hσ : 1 < σ) (n : ℕ) :
    (∑' p : Nat.Primes, hooleyPrimeDirichletTerm Q t q σ p.1 n) ≤
      (2 : ℝ) ^ (t / q) * rootPrimeDirichletSum Q σ *
        (hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) +
      rootPrimeDirichletSum Q σ ^ (1 - t / q) * hooleyErrorDirichletTerm Q t q σ n := by
  by_cases hn : Squarefree n
  · have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have H := infinite_root_weighted_hooleyMoment_rpow_le hQ n hq hσ
      (div_nonneg ht hq'.le) ((div_le_one hq').mpr htq)
    have hrow : (∑' p : Nat.Primes, hooleyPrimeDirichletTerm Q t q σ p.1 n) =
        (rootCount Q n : ℝ) * (n : ℝ) ^ (-σ) *
          ∑' p : Nat.Primes, if ¬p.1 ∣ n then
            rootPrimeLogWeight Q σ p.1 * hooleyMoment q (p.1 * n) ^ (t / q) else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      by_cases hp : p.1 ∣ n
      · simp [hooleyPrimeDirichletTerm, hn, hp]
      · simp only [hooleyPrimeDirichletTerm, hn, hp, not_false_eq_true, and_self, ite_true]
        ring
    rw [hrow]
    apply (mul_le_mul_of_nonneg_left H (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
        (Nat.cast_nonneg _) _))).trans_eq
    rw [hooleyMomentCoefficient, ite_eq_left hn, hooleyErrorDirichletTerm, ite_eq_left hn,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hooleyMoment_nonneg q n)]
    ring
  · simp [hooleyPrimeDirichletTerm, hooleyMomentCoefficient, hooleyErrorDirichletTerm, hn]

/-- The nonlinear differential inequality before the arithmetic bounds on
the two auxiliary series. It holds throughout `σ>1` and for `0≤t≤q`, `q>2`. -/
theorem neg_deriv_hooleyDirichlet_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (htq : t ≤ q) (hσ : 1 < σ) :
    -deriv (hooleyDirichlet Q t q) σ ≤
      (2 : ℝ) ^ (t / q) * rootPrimeDirichletSum Q σ * hooleyDirichlet Q t q σ +
      rootPrimeDirichletSum Q σ ^ (1 - t / q) *
        (hooleyPrimeErrorConstant Q q ^ (t / q) *
          hooleyDirichlet Q t 1 σ ^ (1 / ((q : ℝ) - 1)) *
          hooleyDirichlet Q t q σ ^ (1 - 1 / ((q : ℝ) - 1))) := by
  have hq₀ : 0 < q := by omega
  have Herr := summable_and_hooleyErrorDirichlet_le hQ ht hq hσ
  have hmain := (summable_hooleyDirichlet hQ ht hq₀ hσ).mul_left
    ((2 : ℝ) ^ (t / q) * rootPrimeDirichletSum Q σ)
  have herror := Herr.1.mul_left (rootPrimeDirichletSum Q σ ^ (1 - t / q))
  rw [neg_deriv_hooleyDirichlet_eq_cofactor_sum hQ ht hq₀ hσ]
  calc
    _ ≤ ∑' n : ℕ,
        ((2 : ℝ) ^ (t / q) * rootPrimeDirichletSum Q σ *
          (hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) +
        rootPrimeDirichletSum Q σ ^ (1 - t / q) * hooleyErrorDirichletTerm Q t q σ n) :=
      Summable.tsum_le_tsum (hooleyPrimeDirichlet_row_le hQ ht (by omega) htq hσ)
        (summable_hooleyPrimeDirichletTerm_nat hQ ht hq₀ hσ).prod_symm.prod (hmain.add herror)
    _ = (2 : ℝ) ^ (t / q) * rootPrimeDirichletSum Q σ * hooleyDirichlet Q t q σ +
        rootPrimeDirichletSum Q σ ^ (1 - t / q) * ∑' n, hooleyErrorDirichletTerm Q t q σ n := by
      rw [hmain.tsum_add herror, tsum_mul_left, tsum_mul_left]
      rfl
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left Herr.2
      (Real.rpow_nonneg (rootPrimeDirichletSum_nonneg Q σ) _)) _

end NairTenenbaum
