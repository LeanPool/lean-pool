/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateCoefficientNorm
public import LeanPool.VacuumBellSeparation.Polynomial.ComplexCoefficientBounds
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The original real selector substituted into an actual multivariable polynomial -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace VacuumBellSeparation

variable {σ τ : Type*}

/-- Substitution of q into the original real polynomial, with complex coefficients. -/
def realPolynomialSubstitution (p : Polynomial ℝ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.C (p.coeff i : ℂ) * q ^ i

theorem eval_realPolynomialSubstitution (p : Polynomial ℝ) (q : MvPolynomial σ ℂ)
    (z : σ → ℂ) :
    MvPolynomial.eval z (realPolynomialSubstitution p q) =
      complexPolynomialEval p (MvPolynomial.eval z q) := by
  rw [complexPolynomialEval_sum]
  simp only [realPolynomialSubstitution, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_C]

theorem realPolynomialSubstitution_totalDegree_le (p : Polynomial ℝ)
    (q : MvPolynomial σ ℂ) :
    (realPolynomialSubstitution p q).totalDegree ≤ p.natDegree * q.totalDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow q i).trans
    (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

theorem realPolynomialSubstitution_coefficientNorm_le (p : Polynomial ℝ)
    (q : MvPolynomial σ ℂ) {B : ℝ} (hB : 1 ≤ B) (hq : mvCoefficientNorm q ≤ B) :
    mvCoefficientNorm (realPolynomialSubstitution p q) ≤ coeffAbsSum p * B ^ p.natDegree := by
  rw [coeffAbsSum, Finset.sum_mul]
  apply (mvCoefficientNorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ‖(p.coeff i : ℂ)‖ * mvCoefficientNorm (q ^ i) := by
      simpa only [mvCoefficientNorm_C] using mvCoefficientNorm_mul_le (MvPolynomial.C
        (p.coeff i : ℂ)) (q ^ i)
    _ ≤ |p.coeff i| * B ^ p.natDegree := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (mvCoefficientNorm_pow_le q i).trans
        ((pow_le_pow_left₀ (mvCoefficientNorm_nonneg q) hq i).trans
          (pow_le_pow_right₀ hB (Nat.le_of_lt_succ (Finset.mem_range.mp hi))))

theorem selectorSubstitution_totalDegree_le (N : ℕ) (q : MvPolynomial σ ℂ)
    (hq : q.totalDegree ≤ 1) :
    (realPolynomialSubstitution (selector N) q).totalDegree ≤ 2 * N := by
  have hdeg := realPolynomialSubstitution_totalDegree_le (selector N) q
  have hsel := selector_natDegree_le N
  have hmul := Nat.mul_le_mul_left (selector N).natDegree hq
  omega

theorem selectorSubstitution_coefficientNorm_le (N : ℕ) (q : MvPolynomial σ ℂ)
    (hq : mvCoefficientNorm q ≤ 2) :
    mvCoefficientNorm (realPolynomialSubstitution (selector N) q) ≤ 32 ^ N := by
  calc
    _ ≤ coeffAbsSum (selector N) * 2 ^ (selector N).natDegree :=
      realPolynomialSubstitution_coefficientNorm_le _ _ (by norm_num) hq
    _ ≤ 8 ^ N * 2 ^ (2 * N) := mul_le_mul (coeffAbsSum_selector_le N)
      (pow_le_pow_right₀ (by norm_num) ((selector_natDegree_le N).trans (Nat.sub_le _ _)))
      (by positivity) (by positivity)
    _ = _ := by rw [pow_mul, ← mul_pow]; norm_num

@[simp] theorem mvCoefficientNorm_neg (p : MvPolynomial σ ℂ) :
    mvCoefficientNorm (-p) = mvCoefficientNorm p := by
  simp [mvCoefficientNorm]

theorem mvCoefficientNorm_rename_le (f : σ → τ) (p : MvPolynomial σ ℂ) :
    mvCoefficientNorm (MvPolynomial.rename f p) ≤ mvCoefficientNorm p := by
  classical
  have heq : MvPolynomial.rename f p =
      ∑ k ∈ p.support, MvPolynomial.monomial (Finsupp.mapDomain f k) (p.coeff k) := by
    calc
      _ = MvPolynomial.rename f (∑ k ∈ p.support, MvPolynomial.monomial k (p.coeff k)) := by
        rw [MvPolynomial.support_sum_monomial_coeff]
      _ = _ := by simp only [map_sum, MvPolynomial.rename_monomial]
  rw [heq]
  calc
    _ ≤ ∑ k ∈ p.support,
        mvCoefficientNorm (MvPolynomial.monomial (Finsupp.mapDomain f k) (p.coeff k)) :=
      mvCoefficientNorm_sum_le _ _
    _ = _ := by
      simp only [mvCoefficientNorm_monomial]
      rfl

end VacuumBellSeparation
