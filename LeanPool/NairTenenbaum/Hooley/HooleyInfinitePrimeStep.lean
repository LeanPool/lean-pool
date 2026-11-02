/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletPrimeExpansion

/-! # The convergent infinite weighted prime step

The finite recurrence passes to all primes. The main prime series is kept
explicit, so its sharp arithmetic estimate remains a separate task.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

/-- The prime Dirichlet sum weighted by polynomial root counts. -/
noncomputable def rootPrimeDirichletSum (Q : ℤ[X]) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, rootPrimeLogWeight Q σ p.1

theorem rootPrimeDirichletSum_nonneg (Q : ℤ[X]) (σ : ℝ) :
    0 ≤ rootPrimeDirichletSum Q σ :=
  tsum_nonneg (fun p => rootPrimeLogWeight_nonneg Q σ p.2)

theorem summable_rootPrimeLogWeight {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => rootPrimeLogWeight Q σ p.1) := by
  have H := (summable_log_hooleyDirichlet hQ (le_refl (0 : ℝ)) (by
    decide : 0 < 1) hσ).subtype Nat.Prime
  apply H.congr
  intro p
  dsimp only [Function.comp_def]
  simp only [hooleyMomentCoefficient, ite_eq_left p.2.squarefree, zero_mul, Real.rpow_zero,
    one_mul, rootPrimeLogWeight, Real.rpow_neg (Nat.cast_nonneg p.1), div_eq_mul_inv]

theorem finite_root_weighted_hooleyMoment_rpow_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (S : Finset Nat.Primes) (n : ℕ) {q : ℕ} (hq : 1 < q) {σ θ : ℝ}
    (hσ : 1 < σ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (∑ p ∈ S, if ¬p.1 ∣ n then rootPrimeLogWeight Q σ p.1 * hooleyMoment q (p.1 * n) ^ θ else 0) ≤
      (2 * hooleyMoment q n) ^ θ * rootPrimeDirichletSum Q σ +
        rootPrimeDirichletSum Q σ ^ (1 - θ) * hooleyPrimeErrorBound Q q n ^ θ := by
  have hinj : Set.InjOn (fun p : Nat.Primes => p.1) (↑S : Set Nat.Primes) :=
    fun _ _ _ _ h => Subtype.ext h
  have H := root_weighted_hooleyMoment_rpow_prime_step hQ (S.image (fun p => p.1))
    (by intro p hp; obtain ⟨r, _, rfl⟩ := mem_image.mp hp; exact r.2) n hq hσ.le hθ₀ hθ₁
  simp only [sum_filter, sum_image hinj] at H
  have hmass : (∑ p ∈ S, rootPrimeLogWeight Q σ p.1) ≤ rootPrimeDirichletSum Q σ :=
    (summable_rootPrimeLogWeight hQ hσ).sum_le_tsum S
      (fun p _ => rootPrimeLogWeight_nonneg Q σ p.2)
  apply H.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hmass
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (hooleyMoment_nonneg q n)) _)
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow
      (sum_nonneg fun p _ => rootPrimeLogWeight_nonneg Q σ p.2) hmass (by linarith))
      (Real.rpow_nonneg (hooleyPrimeErrorBound_nonneg Q q n) _)

theorem infinite_root_weighted_hooleyMoment_rpow_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (n : ℕ) {q : ℕ} (hq : 1 < q) {σ θ : ℝ}
    (hσ : 1 < σ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (∑' p : Nat.Primes, if ¬p.1 ∣ n then rootPrimeLogWeight Q σ p.1 * hooleyMoment q (p.1 * n) ^ θ
        else 0) ≤
      (2 * hooleyMoment q n) ^ θ * rootPrimeDirichletSum Q σ +
        rootPrimeDirichletSum Q σ ^ (1 - θ) * hooleyPrimeErrorBound Q q n ^ θ := by
  apply Real.tsum_le_of_sum_le
  · intro p
    change 0 ≤ if ¬p.1 ∣ n then rootPrimeLogWeight Q σ p.1 * hooleyMoment q (p.1 * n) ^ θ else 0
    by_cases hp : p.1 ∣ n
    · simp [hp]
    · rw [ite_eq_left hp]
      exact mul_nonneg (rootPrimeLogWeight_nonneg Q σ p.2) (Real.rpow_nonneg (hooleyMoment_nonneg
          _ _) _)
  · intro S
    exact finite_root_weighted_hooleyMoment_rpow_le hQ S n hq hσ hθ₀ hθ₁

end NairTenenbaum
