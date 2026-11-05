/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # Coefficient-height bounds for polynomial values -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem coeff_natAbs_le_height (Q : ℤ[X]) (i : ℕ) :
    (Q.coeff i).natAbs ≤ polynomialHeight Q := by
  by_cases hi : i ∈ Q.support
  · exact Finset.le_sup (f := fun i => (Q.coeff i).natAbs) hi
  · simp only [Polynomial.mem_support_iff, not_not] at hi
    simp [hi]

theorem polynomialHeight_pos {Q : ℤ[X]} (hQ : Q ≠ 0) : 0 < polynomialHeight Q :=
  (Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ)).trans_le
    (coeff_natAbs_le_height Q Q.natDegree)

/-- A nonzero integral polynomial has real coefficient height at least one. -/
theorem one_le_polynomialHeight {Q : ℤ[X]} (hQ : Q ≠ 0) :
    (1 : ℝ) ≤ polynomialHeight Q := by
  exact_mod_cast polynomialHeight_pos hQ

/-- A coefficient-uniform bound on integral polynomial values. -/
theorem eval_natAbs_le_height (Q : ℤ[X]) (n : ℤ) :
    (Q.eval n).natAbs ≤ polynomialHeight Q * (Q.natDegree + 1) *
      max 1 n.natAbs ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i * n ^ i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ range (Q.natDegree + 1),
        polynomialHeight Q * max 1 n.natAbs ^ Q.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Int.natAbs_mul, Int.natAbs_pow]
      apply Nat.mul_le_mul (coeff_natAbs_le_height Q i)
      exact (Nat.pow_le_pow_left (le_max_right 1 n.natAbs) i).trans
        (Nat.pow_le_pow_right (by omega : 0 < max 1 n.natAbs)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp; ring

end NairTenenbaum
