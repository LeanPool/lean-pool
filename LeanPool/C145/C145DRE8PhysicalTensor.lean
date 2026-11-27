/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8CommonUnit
public import LeanPool.C145.C145DRE8Frobenius

/-! Actual coordinatewise multiplication tensors in orthogonal frames, sharing the unit. -/

@[expose] public section

namespace C145DRE8
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cubic coordinate tensor with unit entries on the full diagonal. -/
noncomputable def coordinateTensor (i j k : ι) : ℝ := if i = j ∧ j = k then 1 else 0
/-- Sum the cubic outer products of the columns of the candidate transport matrix. -/
noncomputable def competitorTensor (Q : Matrix ι ι ℝ) (i j k : ι) : ℝ :=
  ∑ v, Q i v * Q j v * Q k v
/-- The candidate cubic tensor minus the coordinate tensor. -/
noncomputable def physicalDifference (Q : Matrix ι ι ℝ) (i j k : ι) : ℝ :=
  competitorTensor Q i j k - coordinateTensor i j k
/-- Contract a cubic tensor against a vector on its first index. -/
noncomputable def tensorSlice (E : ι → ι → ι → ℝ) (h : ι → ℝ) : Matrix ι ι ℝ :=
  fun j k => ∑ i, h i * E i j k

/-- Fix the first index of the physical tensor difference to obtain a matrix. -/
noncomputable def differenceMatrix (Q : Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  fun j k => physicalDifference Q i j k

omit [DecidableEq ι] in
theorem competitor_symm12 (Q : Matrix ι ι ℝ) (i j k : ι) :
    competitorTensor Q i j k = competitorTensor Q j i k := by
  unfold competitorTensor
  apply Finset.sum_congr rfl; intro v hv; ring

omit [DecidableEq ι] in
theorem competitor_symm13 (Q : Matrix ι ι ℝ) (i j k : ι) :
    competitorTensor Q i j k = competitorTensor Q k j i := by
  unfold competitorTensor
  apply Finset.sum_congr rfl; intro v hv; ring

omit [Fintype ι] in
theorem coordinate_symm12 (i j k : ι) : coordinateTensor i j k = coordinateTensor j i k := by
  unfold coordinateTensor
  split_ifs <;> simp_all

omit [Fintype ι] in
theorem coordinate_symm13 (i j k : ι) : coordinateTensor i j k = coordinateTensor k j i := by
  unfold coordinateTensor
  split_ifs <;> simp_all

theorem difference_symm12 (Q : Matrix ι ι ℝ) (i j k : ι) :
    physicalDifference Q i j k = physicalDifference Q j i k := by
  unfold physicalDifference
  rw [competitor_symm12 Q i j k, coordinate_symm12 i j k]

theorem difference_symm13 (Q : Matrix ι ι ℝ) (i j k : ι) :
    physicalDifference Q i j k = physicalDifference Q k j i := by
  unfold physicalDifference
  rw [competitor_symm13 Q i j k, coordinate_symm13 i j k]

/-- A real orthogonal matrix fixing the vector of ones also has column sums one. -/
theorem orthogonal_column_unit (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (v : ι) : ∑ i, Q i v = 1 := by
  calc
    _ = ∑ i, Q i v * (∑ w, Q i w) := by simp_rw [hunit]; simp
    _ = ∑ w, ∑ i, Q i v * Q i w := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = 1 := by simp_rw [orthogonal_columns_entry Q hQ]; simp

theorem competitor_common_unit (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (j k : ι) :
    (∑ i, competitorTensor Q i j k) = if j = k then 1 else 0 := by
  unfold competitorTensor
  rw [Finset.sum_comm]
  calc
    _ = ∑ v, (∑ i, Q i v) * Q j v * Q k v := by
      simp_rw [Finset.sum_mul]
    _ = ∑ v, Q j v * Q k v := by simp_rw [orthogonal_column_unit Q hQ hunit]; simp
    _ = _ := by
      simpa only [Matrix.transpose_apply] using
        orthogonal_columns_entry Q.transpose (by simpa using orthogonal_rows Q hQ) j k

theorem difference_common_unit (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (j k : ι) :
    (∑ i, physicalDifference Q i j k) = 0 := by
  unfold physicalDifference
  rw [Finset.sum_sub_distrib, competitor_common_unit Q hQ hunit]
  have hc : (∑ i, coordinateTensor i j k) = if j = k then 1 else 0 := by
    simp only [coordinateTensor, ite_and]
    simp
  rw [hc, sub_self]

theorem physicalMatrix_entry (Q : Matrix ι ι ℝ) (i j k : ι) :
    physicalMatrix Q i j k = competitorTensor Q i j k := by
  unfold physicalMatrix competitorTensor
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl; intro v hv; ring

omit [Fintype ι] in
theorem coordinateSlice (i : ι) :
    (fun j k => coordinateTensor i j k) = Matrix.diagonal (fun j => if i = j then (1 : ℝ) else 0)
      := by
  ext j k
  simp only [coordinateTensor, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem physicalMatrices_commute (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (i j : ι) : physicalMatrix Q i * physicalMatrix Q j =
      physicalMatrix Q j * physicalMatrix Q i := by
  have hcancel (X : Matrix ι ι ℝ) : Q.transpose * (Q * X) = X := by
    rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  unfold physicalMatrix
  simp only [Matrix.mul_assoc, hcancel]
  have hd : Matrix.diagonal (Q i) * Matrix.diagonal (Q j) =
      Matrix.diagonal (Q j) * Matrix.diagonal (Q i) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext v; ring
  simpa only [Matrix.mul_assoc] using congrArg (fun X => Q * X * Q.transpose) hd

theorem differenceMatrix_eq (Q : Matrix ι ι ℝ) (i : ι) :
    differenceMatrix Q i = physicalMatrix Q i -
      Matrix.diagonal (fun j => if i = j then (1 : ℝ) else 0) := by
  ext j k
  change competitorTensor Q i j k - coordinateTensor i j k = _
  rw [← physicalMatrix_entry Q i j k]
  rw [show coordinateTensor i j k =
    Matrix.diagonal (fun j => if i = j then (1 : ℝ) else 0) j k from
      congrFun (congrFun (coordinateSlice i) j) k]
  rfl

theorem physical_slice_eq_sum (Q : Matrix ι ι ℝ) (h : ι → ℝ) :
    (∑ i, h i • physicalMatrix Q i) = Matrix.diagonal h + tensorSlice (physicalDifference Q) h := by
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, tensorSlice,
    physicalMatrix_entry, physicalDifference, mul_sub, Finset.sum_sub_distrib]
  have hc : (∑ i, h i * coordinateTensor i j k) = Matrix.diagonal h j k := by
    simp only [coordinateTensor, ite_and, mul_ite, mul_zero, mul_one]
    simp [Matrix.diagonal_apply]
  rw [hc]
  ring

theorem physical_slice_commutes (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (h : ι → ℝ) (i : ι) :
    (∑ j, h j • physicalMatrix Q j) * physicalMatrix Q i =
      physicalMatrix Q i * (∑ j, h j • physicalMatrix Q j) := by
  simp only [Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl; intro j hj
  rw [physicalMatrices_commute Q hQ]

/-- Actual DRE8 physical common-unit tensor satisfies the entire combinatorial energy estimate. -/
theorem physical_common_unit_tensor_bound (Q : Matrix ι ι ℝ)
    (hQ : Q.transpose * Q = 1) (hunit : ∀ i, ∑ v, Q i v = 1) :
    2 * tensorSq (physicalDifference Q) ≤ ((Fintype.card ι : ℝ) + 2) * offSq (physicalDifference
      Q) := by
  exact common_unit_tensor_bound _ (difference_symm13 Q) (difference_symm12 Q)
    (fun j => difference_common_unit Q hQ hunit j j)

end C145DRE8

end
