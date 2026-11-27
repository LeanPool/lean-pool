/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Basic

/-! # The actual coefficient l1 norm of a multivariable polynomial -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace VacuumBellSeparation

variable {σ : Type*}

/-- Finite l1 norm of the actual complex coefficient vector. -/
def mvCoefficientNorm (p : MvPolynomial σ ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖

theorem mvCoefficientNorm_nonneg (p : MvPolynomial σ ℂ) : 0 ≤ mvCoefficientNorm p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

@[simp] theorem mvCoefficientNorm_zero : mvCoefficientNorm (0 : MvPolynomial σ ℂ) = 0 := by
  simp [mvCoefficientNorm]

theorem mvCoefficientNorm_eq_sum {p : MvPolynomial σ ℂ} {s : Finset (σ →₀ ℕ)}
    (h : p.support ⊆ s) : mvCoefficientNorm p = ∑ k ∈ s, ‖p.coeff k‖ := by
  classical
  apply Finset.sum_subset h
  intro k hk hkp
  simp only [MvPolynomial.mem_support_iff, not_not] at hkp
  simp only [hkp, norm_zero]

theorem mvCoefficientNorm_add_le (p q : MvPolynomial σ ℂ) :
    mvCoefficientNorm (p + q) ≤ mvCoefficientNorm p + mvCoefficientNorm q := by
  classical
  rw [mvCoefficientNorm_eq_sum (MvPolynomial.support_add (p := p) (q := q)),
    mvCoefficientNorm_eq_sum (Finset.subset_union_left : p.support ⊆ p.support ∪ q.support),
    mvCoefficientNorm_eq_sum (Finset.subset_union_right : q.support ⊆ p.support ∪ q.support),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun k _ => by
    rw [AddMonoidAlgebra.coeff_add]
    exact norm_add_le (p.coeff k) (q.coeff k))

theorem mvCoefficientNorm_sum_le {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    mvCoefficientNorm (∑ i ∈ s, p i) ≤ ∑ i ∈ s, mvCoefficientNorm (p i) :=
  Finset.le_sum_of_subadditive mvCoefficientNorm mvCoefficientNorm_zero.le
    mvCoefficientNorm_add_le s p

@[simp] theorem mvCoefficientNorm_monomial (k : σ →₀ ℕ) (a : ℂ) :
    mvCoefficientNorm (MvPolynomial.monomial k a) = ‖a‖ := by
  classical
  change (MvPolynomial.monomial k a).coeff.sum (fun _ b => ‖b‖) = _
  exact MvPolynomial.sum_monomial_eq (by simp)

@[simp] theorem mvCoefficientNorm_C (a : ℂ) :
    mvCoefficientNorm (MvPolynomial.C a : MvPolynomial σ ℂ) = ‖a‖ :=
  mvCoefficientNorm_monomial 0 a

@[simp] theorem mvCoefficientNorm_one : mvCoefficientNorm (1 : MvPolynomial σ ℂ) = 1 := by
  simpa only [map_one, norm_one] using (mvCoefficientNorm_C (σ := σ) (1 : ℂ))

@[simp] theorem mvCoefficientNorm_X (j : σ) :
    mvCoefficientNorm (MvPolynomial.X j : MvPolynomial σ ℂ) = 1 := by
  simpa only [MvPolynomial.X, norm_one] using
    mvCoefficientNorm_monomial (Finsupp.single j 1) (1 : ℂ)

theorem mvCoefficientNorm_mul_le (p q : MvPolynomial σ ℂ) :
    mvCoefficientNorm (p * q) ≤ mvCoefficientNorm p * mvCoefficientNorm q := by
  classical
  have heq : p * q = ∑ i ∈ p.support, ∑ j ∈ q.support,
      MvPolynomial.monomial (i + j) (p.coeff i * q.coeff j) := by
    simp only [← MvPolynomial.monomial_mul_monomial, ← Finset.mul_sum, ← Finset.sum_mul,
      MvPolynomial.support_sum_monomial_coeff]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ p.support, mvCoefficientNorm (∑ j ∈ q.support,
        MvPolynomial.monomial (i + j) (p.coeff i * q.coeff j)) := mvCoefficientNorm_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        mvCoefficientNorm (MvPolynomial.monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum (fun _ _ => mvCoefficientNorm_sum_le _ _)
    _ = _ := by
      simp only [mvCoefficientNorm_monomial, norm_mul]
      simp only [mvCoefficientNorm, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

theorem mvCoefficientNorm_pow_le (p : MvPolynomial σ ℂ) (n : ℕ) :
    mvCoefficientNorm (p ^ n) ≤ mvCoefficientNorm p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mvCoefficientNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (mvCoefficientNorm_nonneg p))

theorem mvCoefficientNorm_prod_le {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    mvCoefficientNorm (∏ i ∈ s, p i) ≤ ∏ i ∈ s, mvCoefficientNorm (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (mvCoefficientNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (mvCoefficientNorm_nonneg _))

theorem mvCoefficientNorm_affine_le (a b : ℂ) (j : σ) :
    mvCoefficientNorm (MvPolynomial.C a * MvPolynomial.X j + MvPolynomial.C b) ≤ ‖a‖ + ‖b‖ := by
  exact (mvCoefficientNorm_add_le _ _).trans (by
    have h := mvCoefficientNorm_mul_le (MvPolynomial.C a) (MvPolynomial.X j)
    simp only [mvCoefficientNorm_C, mvCoefficientNorm_X, mul_one] at h ⊢
    linarith)

end VacuumBellSeparation
