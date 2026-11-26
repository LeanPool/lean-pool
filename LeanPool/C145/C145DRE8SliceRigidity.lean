/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8PhysicalTensor

/-! Global finite-dimensional physical slice rigidity, C145 DRE8 Lemma B. -/

@[expose] public section

namespace C145DRE8
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matrixSq_neg (R : Matrix ι ι ℝ) : matrixSq (-R) = matrixSq R := by
  simp [matrixSq]

theorem physical_commutator_identity (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (h : ι → ℝ) (i : ι) :
    commutator (Matrix.diagonal h) (differenceMatrix Q i) =
      -commutator (tensorSlice (physicalDifference Q) h) (physicalMatrix Q i) := by
  have hc := physical_slice_commutes Q hQ h i
  rw [physical_slice_eq_sum] at hc
  have hd : Matrix.diagonal h * Matrix.diagonal (fun j => if i = j then (1 : ℝ) else 0) =
      Matrix.diagonal (fun j => if i = j then (1 : ℝ) else 0) * Matrix.diagonal h := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; ext j; ring
  rw [differenceMatrix_eq]
  unfold commutator
  calc
    _ = Matrix.diagonal h * physicalMatrix Q i - physicalMatrix Q i * Matrix.diagonal h := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hd]
      abel
    _ = -(tensorSlice (physicalDifference Q) h * physicalMatrix Q i -
        physicalMatrix Q i * tensorSlice (physicalDifference Q) h) := by
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        _ = (Matrix.diagonal h + tensorSlice (physicalDifference Q) h) * physicalMatrix Q i -
            physicalMatrix Q i * (Matrix.diagonal h + tensorSlice (physicalDifference Q) h) := by
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
        _ = 0 := sub_eq_zero.mpr hc

theorem diagonal_difference_commutator_entry (Q : Matrix ι ι ℝ) (h : ι → ℝ) (i j k : ι) :
    commutator (Matrix.diagonal h) (differenceMatrix Q i) j k =
      (h j - h k) * physicalDifference Q i j k := by
  simp only [commutator, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    differenceMatrix]
  ring

/-- The physical slice commutator is bounded using actual orthogonal tensor multiplication. -/
theorem physical_slice_commutator_bound (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (h : ι → ℝ) :
    (∑ i, matrixSq (commutator (Matrix.diagonal h) (differenceMatrix Q i))) ≤
      2 * matrixSq (tensorSlice (physicalDifference Q) h) := by
  simp_rw [physical_commutator_identity Q hQ, matrixSq_neg]
  exact physical_commutator_bound Q _ hQ

variable {ρ : Type*} [Fintype ρ]

/-- Squared distance between vertices in the full family of signature coordinates. -/
noncomputable def signatureSq (h : ρ → ι → ℝ) (j k : ι) : ℝ :=
  ∑ r, (h r j - h r k) ^ 2
/-- Sum of the squared Frobenius norms of the slices along all signature vectors. -/
noncomputable def sliceSq (E : ι → ι → ι → ℝ) (h : ρ → ι → ℝ) : ℝ :=
  ∑ r, matrixSq (tensorSlice E (h r))

theorem signature_separation_energy (Q : Matrix ι ι ℝ) (h : ρ → ι → ℝ) (δ : ℝ)
    (hsep : ∀ j k, j ≠ k → δ ^ 2 ≤ signatureSq h j k) :
    δ ^ 2 * offSq (physicalDifference Q) ≤
      ∑ r, ∑ i, matrixSq (commutator (Matrix.diagonal (h r)) (differenceMatrix Q i)) := by
  have hp (i j k : ι) :
      δ ^ 2 * (if j = k then 0 else physicalDifference Q i j k ^ 2) ≤
        ∑ r, ((h r j - h r k) * physicalDifference Q i j k) ^ 2 := by
    by_cases hjk : j = k
    · simp [hjk]
    · simp only [hjk, ↓reduceIte]
      have hh := mul_le_mul_of_nonneg_right (hsep j k hjk) (sq_nonneg (physicalDifference Q i j k))
      simpa only [signatureSq, mul_pow, Finset.sum_mul] using hh
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hp i j k)))
  simp only [← Finset.mul_sum] at hh
  change δ ^ 2 * offSq (physicalDifference Q) ≤ _ at hh
  refine hh.trans_eq ?_
  simp only [matrixSq, diagonal_difference_commutator_entry]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact Finset.sum_comm

/-- DRE8 equation (5.4), with the separating-signature lower bound stated pointwise. -/
theorem physical_off_slice_bound (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (h : ρ → ι → ℝ) (δ : ℝ)
    (hsep : ∀ j k, j ≠ k → δ ^ 2 ≤ signatureSq h j k) :
    δ ^ 2 * offSq (physicalDifference Q) ≤ 2 * sliceSq (physicalDifference Q) h := by
  apply (signature_separation_energy Q h δ hsep).trans
  have hh := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
    physical_slice_commutator_bound Q hQ (h r))
  simpa only [sliceSq, Finset.mul_sum] using hh

/-- Full global physical slice rigidity, DRE8 Lemma B (5.1).
Q is an actual finite real orthogonal matrix fixing the vector of ones.
No physical commutation or target norm inequality is supplied as an assumption. -/
theorem physical_slice_rigidity (Q : Matrix ι ι ℝ) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (h : ρ → ι → ℝ) (δ : ℝ)
    (hsep : ∀ j k, j ≠ k → δ ^ 2 ≤ signatureSq h j k) :
    δ ^ 2 * tensorSq (physicalDifference Q) ≤
      ((Fintype.card ι : ℝ) + 2) * sliceSq (physicalDifference Q) h := by
  have hc := physical_common_unit_tensor_bound Q hQ hunit
  have hs := physical_off_slice_bound Q hQ h δ hsep
  have hδ := sq_nonneg δ
  have hN : (0 : ℝ) ≤ (Fintype.card ι : ℝ) + 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hc hδ
  have h2 := mul_le_mul_of_nonneg_left hs hN
  nlinarith

end C145DRE8

end
