/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.PositiveSeries
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Scalar functional calculus at a positive noncommutative series

Substituting a positive series into a scalar series uses only a finite prefix
in every degree. The target algebra is allowed to be noncommutative. Scalar
polynomial evaluation is multiplicative because rational scalars are central.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- Substitution of a positive series into a scalar series, degree by degree. -/
def scalarSeriesApply (c : PowerSeries ℚ) (u : ℕ → A) : PowerSeries A :=
  mk fun n ↦ ∑ k ∈ range (n + 1), coeff k c • positivePowerCoeff u k n

/-- A polynomial evaluated at a positive series reads only the necessary scalar prefix. -/
theorem coeff_aeval_positiveSeries (p : Polynomial ℚ) (u : ℕ → A) (n : ℕ) :
    coeff n (Polynomial.aeval (positiveSeries u) p) =
      ∑ k ∈ range (n + 1), p.coeff k • positivePowerCoeff u k n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, Polynomial.coeff_add, add_smul, sum_add_distrib]
  | monomial j r =>
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def, coeff_smul, coeff_positiveSeries_pow]
    simp only [Polynomial.coeff_monomial_apply, ite_smul, zero_smul]
    rw [sum_ite_eq]
    split_ifs with hj
    · rfl
    · rw [positivePowerCoeff_eq_zero_of_lt u j n (by
        have := mem_range.not.mp hj
        lia), smul_zero]

/-- Truncation above the requested degree suffices for scalar substitution. -/
theorem coeff_scalarSeriesApply_eq_aeval_trunc (c : PowerSeries ℚ) (u : ℕ → A)
    (n N : ℕ) (hn : n < N) :
    coeff n (scalarSeriesApply c u) =
      coeff n (Polynomial.aeval (positiveSeries u) (trunc N c)) := by
  rw [coeff_aeval_positiveSeries]
  simp only [scalarSeriesApply, coeff_mk]
  apply sum_congr rfl
  intro k hk
  rw [coeff_trunc, ite_eq_left (by have := mem_range.mp hk; lia)]

/-- Polynomial evaluation depends only on scalar coefficients up to the requested degree. -/
theorem coeff_aeval_positiveSeries_congr (p q : Polynomial ℚ) (u : ℕ → A) (n : ℕ)
    (h : ∀ k, k ≤ n → p.coeff k = q.coeff k) :
    coeff n (Polynomial.aeval (positiveSeries u) p) =
      coeff n (Polynomial.aeval (positiveSeries u) q) := by
  simp only [coeff_aeval_positiveSeries]
  exact sum_congr rfl fun k hk ↦ congrArg (· • positivePowerCoeff u k n)
    (h k (by have := mem_range.mp hk; lia))

/-- Scalar functional calculus preserves products of scalar series. -/
theorem scalarSeriesApply_mul (c d : PowerSeries ℚ) (u : ℕ → A) :
    scalarSeriesApply (c * d) u = scalarSeriesApply c u * scalarSeriesApply d u := by
  ext n
  rw [coeff_scalarSeriesApply_eq_aeval_trunc (c * d) u n (n + 1) (by lia)]
  calc
    coeff n (Polynomial.aeval (positiveSeries u) (trunc (n + 1) (c * d))) =
        coeff n (Polynomial.aeval (positiveSeries u) (trunc (n + 1) c * trunc (n + 1) d)) := by
      apply coeff_aeval_positiveSeries_congr
      intro k hk
      have ht := congrArg (fun p : Polynomial ℚ ↦ p.coeff k)
        (trunc_trunc_mul_trunc (n := n + 1) c d)
      simpa only [coeff_trunc, ite_eq_left (by lia : k < n + 1),
        ← Polynomial.coe_mul, Polynomial.coeff_coe] using ht.symm
    _ = coeff n (Polynomial.aeval (positiveSeries u) (trunc (n + 1) c) *
        Polynomial.aeval (positiveSeries u) (trunc (n + 1) d)) := by rw [map_mul]
    _ = coeff n (scalarSeriesApply c u * scalarSeriesApply d u) := by
      simp only [coeff_mul]
      apply sum_congr rfl
      intro ij hij
      have hij' := mem_antidiagonal.mp hij
      rw [← coeff_scalarSeriesApply_eq_aeval_trunc c u ij.1 (n + 1) (by lia),
        ← coeff_scalarSeriesApply_eq_aeval_trunc d u ij.2 (n + 1) (by lia)]

/-- Scalar polynomial substitution agrees with the usual algebra evaluation map. -/
theorem scalarSeriesApply_coe (p : Polynomial ℚ) (u : ℕ → A) :
    scalarSeriesApply (p : PowerSeries ℚ) u = Polynomial.aeval (positiveSeries u) p := by
  ext n
  simp only [scalarSeriesApply, coeff_mk, Polynomial.coeff_coe, coeff_aeval_positiveSeries]

/-- Substitution preserves scalar multiples. -/
theorem scalarSeriesApply_smul (c : PowerSeries ℚ) (u : ℕ → A) (r : ℚ) :
    scalarSeriesApply (r • c) u = r • scalarSeriesApply c u := by
  ext n
  simp only [scalarSeriesApply, coeff_mk, coeff_smul, smul_sum, smul_smul, smul_eq_mul]

/-- Functional calculus at one positive series is an algebra homomorphism on scalar series. -/
def scalarSeriesApplyHom (u : ℕ → A) : PowerSeries ℚ →ₐ[ℚ] PowerSeries A where
  toFun c := scalarSeriesApply c u
  map_zero' := by
    simpa only [Polynomial.coe_zero, map_zero] using scalarSeriesApply_coe (0 : Polynomial ℚ) u
  map_one' := by
    simpa only [Polynomial.coe_one, map_one] using scalarSeriesApply_coe (1 : Polynomial ℚ) u
  map_add' c d := by
    ext n
    simp only [scalarSeriesApply, coeff_mk, map_add, add_smul, sum_add_distrib]
  map_mul' c d := scalarSeriesApply_mul c d u
  commutes' r := by
    simpa only [Polynomial.coe_C, Polynomial.aeval_C, algebraMap_eq] using
      scalarSeriesApply_coe (Polynomial.C r) u

@[simp]
theorem scalarSeriesApplyHom_apply (u : ℕ → A) (c : PowerSeries ℚ) :
    scalarSeriesApplyHom u c = scalarSeriesApply c u := rfl

@[simp]
theorem scalarSeriesApply_C (r : ℚ) (u : ℕ → A) :
    scalarSeriesApply (C r) u = algebraMap ℚ (PowerSeries A) r := by
  simpa only [algebraMap_eq, scalarSeriesApplyHom_apply] using
    (scalarSeriesApplyHom u).commutes r

@[simp]
theorem scalarSeriesApply_X (u : ℕ → A) : scalarSeriesApply X u = positiveSeries u := by
  simpa only [Polynomial.coe_X, Polynomial.aeval_X] using
    scalarSeriesApply_coe (Polynomial.X : Polynomial ℚ) u

/-- Substitution is local in the scalar series argument. -/
theorem coeff_scalarSeriesApply_congr (c d : PowerSeries ℚ) (u : ℕ → A) (n : ℕ)
    (h : ∀ k, k ≤ n → coeff k c = coeff k d) :
    coeff n (scalarSeriesApply c u) = coeff n (scalarSeriesApply d u) := by
  simp only [scalarSeriesApply, coeff_mk]
  exact sum_congr rfl fun k hk ↦ congrArg (· • positivePowerCoeff u k n)
    (h k (by have := mem_range.mp hk; lia))

/-- The ignored constant input has no effect on scalar substitution. -/
theorem scalarSeriesApply_congr (c : PowerSeries ℚ) (u v : ℕ → A)
    (h : positiveSeries u = positiveSeries v) : scalarSeriesApply c u = scalarSeriesApply c v := by
  ext n
  simp only [scalarSeriesApply, coeff_mk, ← coeff_positiveSeries_pow, h]

omit [Algebra ℚ A] in
/-- Equality of finite prefixes is preserved by powers, including noncommutative powers. -/
theorem coeff_pow_congr_of_le (p q : PowerSeries A) (n : ℕ)
    (h : ∀ k, k ≤ n → coeff k p = coeff k q) (j k : ℕ) (hk : k ≤ n) :
    coeff k (p ^ j) = coeff k (q ^ j) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', coeff_mul]
    apply sum_congr rfl
    intro ij hij
    have hij' := mem_antidiagonal.mp hij
    rw [h ij.1 (by lia), ih ij.2 (by lia)]

end FQFP
