/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeFactorReindex
public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletDerivative

/-! # Prime expansion of the Dirichlet-series derivative

The reindexing in (2.9) of the weighted Hooley mean proof retains squarefree
support and the exclusion of primes dividing the cofactor. Its convergence
follows from the already proved logarithmic Dirichlet-series convergence.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

/-- The prime-step term in the Dirichlet expansion of the Hooley moment. -/
noncomputable def hooleyPrimeDirichletTerm (Q : ℤ[X]) (t : ℝ) (q : ℕ)
    (σ : ℝ) (p m : ℕ) : ℝ :=
  if Squarefree m ∧ ¬p ∣ m then
    (rootCount Q m : ℝ) * (m : ℝ) ^ (-σ) * rootPrimeLogWeight Q σ p *
      hooleyMoment q (p * m) ^ (t / q)
  else 0

theorem hooleyPrimeDirichletTerm_nonneg (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ)
    {p : ℕ} (hp : p.Prime) (m : ℕ) : 0 ≤ hooleyPrimeDirichletTerm Q t q σ p m := by
  unfold hooleyPrimeDirichletTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (Nat.cast_nonneg _) _))
      (rootPrimeLogWeight_nonneg Q σ hp)) (Real.rpow_nonneg (hooleyMoment_nonneg _ _) _)
  · rfl

@[simp] theorem hooleyPrimeDirichletTerm_zero (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ) (p : ℕ) :
    hooleyPrimeDirichletTerm Q t q σ p 0 = 0 := by
  simp [hooleyPrimeDirichletTerm]

theorem hooleyPrimeDirichletTerm_eq (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ)
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    hooleyMomentCoefficient Q t q (p * m) * (p * m : ℕ) ^ (-σ) * Real.log p =
      hooleyPrimeDirichletTerm Q t q σ p m := by
  have heq : Squarefree (p * m) ↔ Squarefree m ∧ ¬p ∣ m := by
    simp [Nat.squarefree_mul_iff, hp.squarefree, hp.coprime_iff_not_dvd, and_comm]
  by_cases h : Squarefree m ∧ ¬p ∣ m
  · rw [hooleyPrimeDirichletTerm, ite_eq_left h, hooleyMomentCoefficient,
      ite_eq_left (heq.mpr h), rootCount_mul Q (hp.coprime_iff_not_dvd.mpr h.2),
      Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      rootPrimeLogWeight, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg p)]
    ring
  · rw [hooleyPrimeDirichletTerm, ite_eq_right h, hooleyMomentCoefficient,
      ite_eq_right (heq.not.mpr h), zero_mul, zero_mul]

theorem summable_hooleyPrimeDirichletTerm {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    Summable (fun x : Nat.Primes × ℕ+ => hooleyPrimeDirichletTerm Q t q σ x.1.1 x.2.1) := by
  have H := summable_squarefree_prime_cofactors
    (fun n => hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ))
    (fun n => mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n hn => by simp [hooleyMomentCoefficient, hn])
    (by simpa only [mul_right_comm] using summable_log_hooleyDirichlet hQ ht hq hσ)
  exact H.congr (fun x => hooleyPrimeDirichletTerm_eq Q t q σ x.1.2 x.2.1)

theorem neg_deriv_hooleyDirichlet_eq_prime_sum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    -deriv (hooleyDirichlet Q t q) σ =
      ∑' p : Nat.Primes, ∑' m : ℕ, hooleyPrimeDirichletTerm Q t q σ p.1 m := by
  rw [deriv_hooleyDirichlet hQ ht hq hσ, neg_neg]
  have H := tsum_squarefree_log_eq_prime_cofactors
    (fun n => hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ))
    (fun n => mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n hn => by simp [hooleyMomentCoefficient, hn])
    (by simpa only [mul_right_comm] using summable_log_hooleyDirichlet hQ ht hq hσ)
  calc
    _ = ∑' n : ℕ, (hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) * Real.log n := by
      apply tsum_congr
      intro n
      ring
    _ = _ := H.trans (by
      apply tsum_congr
      intro p
      rw [← tsum_pnat_eq_tsum_of_eq_zero (hooleyPrimeDirichletTerm_zero Q t q σ p.1)]
      apply tsum_congr
      intro m
      exact hooleyPrimeDirichletTerm_eq Q t q σ p.2 m.1)

theorem summable_hooleyPrimeDirichletTerm_nat {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    Summable (fun x : Nat.Primes × ℕ => hooleyPrimeDirichletTerm Q t q σ x.1.1 x.2) := by
  have H := summable_hooleyPrimeDirichletTerm hQ ht hq hσ
  apply (summable_prod_of_nonneg (fun x => hooleyPrimeDirichletTerm_nonneg Q t q σ x.1.2 x.2)).mpr
  refine ⟨fun p => summable_pnat_iff_summable_nat.mp (H.prod_factor p), ?_⟩
  convert H.prod using 1
  ext p
  exact (tsum_pnat_eq_tsum_of_eq_zero (hooleyPrimeDirichletTerm_zero Q t q σ p.1)).symm

theorem neg_deriv_hooleyDirichlet_eq_cofactor_sum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    -deriv (hooleyDirichlet Q t q) σ =
      ∑' n : ℕ, ∑' p : Nat.Primes, hooleyPrimeDirichletTerm Q t q σ p.1 n := by
  rw [neg_deriv_hooleyDirichlet_eq_prime_sum hQ ht hq hσ]
  exact (Summable.tsum_comm
    (f := fun (p : Nat.Primes) (n : ℕ) => hooleyPrimeDirichletTerm Q t q σ p.1 n)
    (summable_hooleyPrimeDirichletTerm_nat hQ ht hq hσ)).symm

end NairTenenbaum
