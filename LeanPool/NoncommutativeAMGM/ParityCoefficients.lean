/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CoefficientTail

/-!
# Even and odd coefficient decomposition

The exact coefficient identities and endpoint bookkeeping used in Section 3.5.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial
open scoped BigOperators

/-- The polynomial formed from the even coefficients. -/
noncomputable def evenCoefficients (p : Polynomial ℝ) : Polynomial ℝ := p.contract 2

/-- The polynomial formed from the odd coefficients. -/
noncomputable def oddCoefficients (p : Polynomial ℝ) : Polynomial ℝ := p.divX.contract 2

theorem evenCoefficients_coeff (p : Polynomial ℝ) (i : ℕ) :
    (evenCoefficients p).coeff i = p.coeff (2 * i) := by
  simp [evenCoefficients, coeff_contract, mul_comm]

theorem oddCoefficients_coeff (p : Polynomial ℝ) (i : ℕ) :
    (oddCoefficients p).coeff i = p.coeff (2 * i + 1) := by
  simp [oddCoefficients, coeff_contract, mul_comm]

/-- Multiplication by `X²-1` becomes multiplication by `u-1` in the even part. -/
theorem evenCoefficients_mul_step (p : Polynomial ℝ) :
    evenCoefficients (p * (X ^ 2 - 1)) = evenCoefficients p * (X - 1) := by
  have he : expand ℝ 2 (X - 1) = (X ^ 2 - 1 : Polynomial ℝ) := by simp
  change contract 2 (p * (X ^ 2 - 1)) = contract 2 p * (X - 1)
  rw [← he, contract_mul_expand (by decide)]

/-- The same multiplication rule holds in the odd part. -/
theorem oddCoefficients_mul_step (p : Polynomial ℝ) :
    oddCoefficients (p * (X ^ 2 - 1)) = oddCoefficients p * (X - 1) := by
  ext i
  rw [oddCoefficients_coeff]
  simp only [mul_sub, mul_one, coeff_sub]
  cases i with
  | zero => simp [coeff_mul_X_pow', oddCoefficients_coeff]
  | succ i =>
    rw [coeff_mul_X, oddCoefficients_coeff, oddCoefficients_coeff]
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega, coeff_mul_X_pow]

theorem sum_range_double (f : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range (2 * M), f i =
      (∑ i ∈ Finset.range M, f (2 * i)) + ∑ i ∈ Finset.range M, f (2 * i + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = (2 * M + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem sum_range_double_succ (f : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range (2 * M + 1), f i =
      (∑ i ∈ Finset.range (M + 1), f (2 * i)) + ∑ i ∈ Finset.range M, f (2 * i + 1) := by
  rw [Finset.sum_range_succ, sum_range_double, Finset.sum_range_succ]
  ring

theorem evenCoefficients_degree_lt {p : Polynomial ℝ} {M : ℕ}
    (hp : p.degree < (2 * M + 1 : ℕ)) : (evenCoefficients p).degree < (M + 1 : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  rw [evenCoefficients_coeff]
  exact (degree_lt_iff_coeff_zero _ _).mp hp _ (by omega)

theorem oddCoefficients_degree_lt {p : Polynomial ℝ} {M : ℕ}
    (hp : p.degree < (2 * M + 1 : ℕ)) : (oddCoefficients p).degree < M := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  rw [oddCoefficients_coeff]
  exact (degree_lt_iff_coeff_zero _ _).mp hp _ (by omega)

theorem realCoefficientNorm_eq_range {p : Polynomial ℝ} {N : ℕ} (hp : p.degree < N) :
    realCoefficientInner p p = ∑ i ∈ Finset.range N, p.coeff i ^ 2 := by
  by_cases hpz : p = 0
  · simp [hpz, realCoefficientInner]
  · rw [realCoefficientInner_eq_sum p p ((natDegree_lt_iff_degree_lt hpz).mpr hp)]
    simp only [pow_two]

/-- The full coefficient norm splits into the even and odd coefficient norms. -/
theorem realCoefficientNorm_parity {p : Polynomial ℝ} {M : ℕ}
    (hp : p.degree < (2 * M + 1 : ℕ)) :
    realCoefficientInner p p = realCoefficientInner (evenCoefficients p) (evenCoefficients p) +
      realCoefficientInner (oddCoefficients p) (oddCoefficients p) := by
  rw [realCoefficientNorm_eq_range hp,
    realCoefficientNorm_eq_range (evenCoefficients_degree_lt hp),
    realCoefficientNorm_eq_range (oddCoefficients_degree_lt hp)]
  simp_rw [evenCoefficients_coeff, oddCoefficients_coeff]
  exact sum_range_double_succ (fun i ↦ p.coeff i ^ 2) M

/-- Delete the first and last two coefficients at fixed ambient degree `2D`. -/
noncomputable def twoInteriorCoefficientNormSq (D : ℕ) (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 * D + 1), if 2 ≤ i ∧ i + 2 ≤ 2 * D then p.coeff i ^ 2 else 0

/-- Exact endpoint deletion under the even/odd decomposition. -/
theorem twoInteriorCoefficientNormSq_parity (D : ℕ) (hD : 1 ≤ D) (p : Polynomial ℝ) :
    twoInteriorCoefficientNormSq D p =
      interiorCoefficientNormSq D (evenCoefficients p) +
        interiorCoefficientNormSq (D - 1) (oddCoefficients p) := by
  rw [twoInteriorCoefficientNormSq, sum_range_double_succ]
  simp only [interiorCoefficientNormSq, evenCoefficients_coeff, oddCoefficients_coeff,
    Nat.sub_add_cancel hD]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hiD : i < D + 1 := Finset.mem_range.mp hi
    by_cases he : i = 0 ∨ i = D
    · have hc : ¬(2 ≤ 2 * i ∧ 2 * i + 2 ≤ 2 * D) := by omega
      rw [ite_eq_right hc, ite_eq_left he]
    · have hc : 2 ≤ 2 * i ∧ 2 * i + 2 ≤ 2 * D := by omega
      rw [ite_eq_left hc, ite_eq_right he]
  · apply Finset.sum_congr rfl
    intro i hi
    have hiD : i < D := Finset.mem_range.mp hi
    by_cases he : i = 0 ∨ i = D - 1
    · have hc : ¬(2 ≤ 2 * i + 1 ∧ 2 * i + 1 + 2 ≤ 2 * D) := by omega
      rw [ite_eq_right hc, ite_eq_left he]
    · have hc : 2 ≤ 2 * i + 1 ∧ 2 * i + 1 + 2 ≤ 2 * D := by omega
      rw [ite_eq_left hc, ite_eq_right he]

end NoncommutativeAMGM
