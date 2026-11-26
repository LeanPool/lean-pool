/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! Explicit squared Frobenius energy and its orthogonal invariance. -/

@[expose] public section

namespace C145DRE8
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared Frobenius norm written as a sum of squares of matrix entries. -/
noncomputable def matrixSq (R : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, R i j ^ 2
/-- The squared Euclidean norm of the matrix diagonal. -/
noncomputable def diagonalSq (R : Matrix ι ι ℝ) : ℝ := ∑ i, R i i ^ 2

omit [DecidableEq ι] in
theorem matrixSq_nonneg (R : Matrix ι ι ℝ) : 0 ≤ matrixSq R := by
  unfold matrixSq; positivity

omit [DecidableEq ι] in
theorem diagonalSq_nonneg (R : Matrix ι ι ℝ) : 0 ≤ diagonalSq R := by
  unfold diagonalSq; positivity

theorem orthogonal_rows (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    Q * Q.transpose = 1 := mul_eq_one_comm.mp hQ

theorem orthogonal_columns_entry (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (a b : ι) : (∑ i, Q i a * Q i b) = if a = b then 1 else 0 := by
  have h := congrArg (fun R : Matrix ι ι ℝ => R a b) hQ
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem orthogonal_energy (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (x : ι → ℝ) : ∑ i, (∑ j, Q i j * x j) ^ 2 = ∑ j, x j ^ 2 := by
  have hexp (i : ι) : (∑ j, Q i j * x j) ^ 2 =
      ∑ a, ∑ b, Q i a * Q i b * x a * x b := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b hb
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, (∑ i, Q i a * Q i b) * x a * x b := by
      apply Finset.sum_congr rfl; intro b hb
      simp_rw [Finset.sum_mul]
    _ = x a ^ 2 := by
      simp_rw [orthogonal_columns_entry Q hQ]
      simp [pow_two]

omit [DecidableEq ι] in
theorem matrixSq_transpose (R : Matrix ι ι ℝ) : matrixSq R.transpose = matrixSq R := by
  unfold matrixSq
  exact Finset.sum_comm

theorem matrixSq_left (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    matrixSq (Q * R) = matrixSq R := by
  unfold matrixSq
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact orthogonal_energy Q hQ (fun k => R k j)

theorem matrixSq_right (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    matrixSq (R * Q) = matrixSq R := by
  rw [← matrixSq_transpose (R * Q), Matrix.transpose_mul]
  rw [matrixSq_left Q.transpose R.transpose]
  · exact matrixSq_transpose R
  · simpa using orthogonal_rows Q hQ

theorem matrixSq_conjugate (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    matrixSq (Q.transpose * R * Q) = matrixSq R := by
  rw [matrixSq_right Q (Q.transpose * R) hQ, matrixSq_left Q.transpose R]
  simpa using orthogonal_rows Q hQ

/-- The difference between the products in the two possible orders. -/
noncomputable def commutator (R S : Matrix ι ι ℝ) : Matrix ι ι ℝ := R * S - S * R

/-- Conjugate the diagonal formed from a row of the transport matrix by that matrix. -/
noncomputable def physicalMatrix (Q : Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  Q * Matrix.diagonal (Q i) * Q.transpose

theorem conjugate_commutator (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) (i : ι) :
    Q.transpose * commutator R (physicalMatrix Q i) * Q =
      commutator (Q.transpose * R * Q) (Matrix.diagonal (Q i)) := by
  have hcancel (X : Matrix ι ι ℝ) : Q.transpose * (Q * X) = X := by
    rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  unfold commutator physicalMatrix
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc, hQ, Matrix.mul_one, hcancel]

theorem commutator_diagonal_entry (R : Matrix ι ι ℝ) (d : ι → ℝ) (a b : ι) :
    commutator R (Matrix.diagonal d) a b = R a b * (d b - d a) := by
  simp only [commutator, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- Orthogonal columns have squared pairwise distance two (zero on the diagonal). -/
theorem orthogonal_column_distance (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (a b : ι) : ∑ i, (Q i b - Q i a) ^ 2 = if a = b then 0 else 2 := by
  have hh (i : ι) : (Q i b - Q i a) ^ 2 =
      Q i b * Q i b + Q i a * Q i a - 2 * (Q i a * Q i b) := by ring
  simp_rw [hh, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [orthogonal_columns_entry Q hQ b b, orthogonal_columns_entry Q hQ a a,
    orthogonal_columns_entry Q hQ a b]
  simp only [ite_true]
  split_ifs <;> norm_num

/-- Exact DRE8 equation (5.3); symmetry of R is unnecessary for this real-coordinate identity. -/
theorem physical_commutator_energy (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    (∑ i, matrixSq (commutator R (physicalMatrix Q i))) =
      2 * (matrixSq R - diagonalSq (Q.transpose * R * Q)) := by
  let A := Q.transpose * R * Q
  have he (i : ι) : matrixSq (commutator R (physicalMatrix Q i)) =
      ∑ a, ∑ b, A a b ^ 2 * (Q i b - Q i a) ^ 2 := by
    rw [← matrixSq_conjugate Q _ hQ, conjugate_commutator Q R hQ]
    unfold matrixSq
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    rw [commutator_diagonal_entry, mul_pow]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hz : (∑ a, ∑ i, ∑ b, A a b ^ 2 * (Q i b - Q i a) ^ 2) =
      ∑ a, ∑ b, A a b ^ 2 * (if a = b then 0 else 2) := by
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b hb
    rw [← Finset.mul_sum, orthogonal_column_distance Q hQ a b]
  rw [hz]
  have hp (a b : ι) : A a b ^ 2 * (if a = b then 0 else 2) =
      2 * A a b ^ 2 - (if a = b then 2 * A a b ^ 2 else 0) := by
    split_ifs <;> ring
  simp_rw [hp, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Fintype.sum_ite_eq]
  rw [← Finset.mul_sum]
  change 2 * matrixSq A - 2 * diagonalSq A = _
  rw [show matrixSq A = matrixSq R from matrixSq_conjugate Q R hQ]
  ring

theorem physical_commutator_bound (Q R : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1) :
    (∑ i, matrixSq (commutator R (physicalMatrix Q i))) ≤ 2 * matrixSq R := by
  rw [physical_commutator_energy Q R hQ]
  have h := diagonalSq_nonneg (Q.transpose * R * Q)
  linarith

end C145DRE8

end
