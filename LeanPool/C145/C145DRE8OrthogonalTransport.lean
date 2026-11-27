/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8SpectralContraction

/-! Exact orthogonal change of coordinates for tensor and slice energies.
This is the modal-to-vertex bridge needed to apply physical Lemma B. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Apply the transport matrix to the first tensor index. -/
def rotateFirst (U : Matrix ι ι ℝ) (E : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ r, U i r * E r j k

/-- Apply the transport matrix to the second tensor index. -/
def rotateSecond (U : Matrix ι ι ℝ) (E : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ r, U j r * E i r k

/-- Apply the transport matrix to the third tensor index. -/
def rotateThird (U : Matrix ι ι ℝ) (E : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ r, U k r * E i j r

/-- Same orthogonal U in each of the three slots. -/
def rotateTensor (U : Matrix ι ι ℝ) (E : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  rotateFirst U (rotateSecond U (rotateThird U E))

omit [DecidableEq ι] in
theorem tensorSq_sum_order (E : ι → ι → ι → ℝ) :
    (∑ j, ∑ k, ∑ i, E i j k ^ 2) = tensorSq E := by
  unfold tensorSq
  calc
    _ = ∑ j, ∑ i, ∑ k, E i j k ^ 2 := by
      apply Finset.sum_congr rfl; intro j hj; exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem tensorSq_rotateFirst (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) : tensorSq (rotateFirst U E) = tensorSq E := by
  rw [← tensorSq_sum_order]
  simp only [rotateFirst, orthogonal_energy U hU]
  exact tensorSq_sum_order E

theorem tensorSq_rotateSecond (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) : tensorSq (rotateSecond U E) = tensorSq E := by
  unfold tensorSq
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  calc
    _ = ∑ k, ∑ r, E i r k ^ 2 := by
      apply Finset.sum_congr rfl; intro k hk
      exact orthogonal_energy U hU (fun r => E i r k)
    _ = _ := Finset.sum_comm

theorem tensorSq_rotateThird (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) : tensorSq (rotateThird U E) = tensorSq E := by
  unfold tensorSq rotateThird
  simp_rw [orthogonal_energy U hU]

/-- Frobenius tensor energy is preserved in the actual orthogonal frame. -/
theorem tensorSq_rotateTensor (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) : tensorSq (rotateTensor U E) = tensorSq E := by
  simp only [rotateTensor, tensorSq_rotateFirst U hU,
    tensorSq_rotateSecond U hU, tensorSq_rotateThird U hU]

/-- The signature is rotated by the very same U as the tensor. -/
theorem signature_pairing (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (a : ι → ℝ) (r : ι) : ∑ i, (U.mulVec a) i * U i r = a r := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, (∑ i, U i s * U i r) * a s := by
      apply Finset.sum_congr rfl; intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = _ := by simp_rw [orthogonal_columns_entry U hU]; simp

theorem slice_rotateFirst (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) (a : ι → ℝ) :
    tensorSlice (rotateFirst U E) (U.mulVec a) = tensorSlice E a := by
  funext j k
  simp only [tensorSlice, rotateFirst, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r, (∑ i, (U.mulVec a) i * U i r) * E r j k := by
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = _ := by simp_rw [signature_pairing U hU]

omit [DecidableEq ι] in
theorem slice_rotateSecond (U : Matrix ι ι ℝ)
    (E : ι → ι → ι → ℝ) (a : ι → ℝ) :
    tensorSlice (rotateSecond U E) a = U * tensorSlice E a := by
  funext j k
  simp only [tensorSlice, rotateSecond, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r hr
  apply Finset.sum_congr rfl; intro i hi; ring

omit [DecidableEq ι] in
theorem slice_rotateThird (U : Matrix ι ι ℝ)
    (E : ι → ι → ι → ℝ) (a : ι → ℝ) :
    tensorSlice (rotateThird U E) a = tensorSlice E a * U.transpose := by
  funext j k
  simp only [tensorSlice, rotateThird, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r hr
  apply Finset.sum_congr rfl; intro i hi; ring

/-- Exact slice covariance and its actual frame identity. -/
theorem slice_rotateTensor (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) (a : ι → ℝ) :
    tensorSlice (rotateTensor U E) (U.mulVec a) =
      U * tensorSlice E a * U.transpose := by
  rw [rotateTensor, slice_rotateFirst U hU, slice_rotateSecond,
    slice_rotateThird, Matrix.mul_assoc]

theorem matrixSq_slice_rotateTensor (U : Matrix ι ι ℝ) (hU : U.transpose * U = 1)
    (E : ι → ι → ι → ℝ) (a : ι → ℝ) :
    matrixSq (tensorSlice (rotateTensor U E) (U.mulVec a)) =
      matrixSq (tensorSlice E a) := by
  rw [slice_rotateTensor U hU, matrixSq_right U.transpose]
  · exact matrixSq_left U _ hU
  · simpa using orthogonal_rows U hU

variable {n : ℕ}

/-- Modal signature of b_perp: zero in the calibrated ground direction. -/
def residualVector (a : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases 0 a

/-- Embedding a residual tensor adds no ground energy, including n=0. -/
theorem tensorSq_groundZero (E : Tensor n) : tensorSq (groundZero E) = tensorSq E := by
  simp [tensorSq, Fin.sum_univ_succ, groundZero]

/-- The embedded residual slice likewise adds zero rows and columns. -/
theorem matrixSq_slice_groundZero (E : Tensor n) (a : Fin n → ℝ) :
    matrixSq (tensorSlice (groundZero E) (residualVector a)) =
      matrixSq (tensorSlice E a) := by
  simp [matrixSq, tensorSlice, Fin.sum_univ_succ, residualVector, groundZero]

/-- Full modal-to-vertex tensor and signature energy transport, with exactly
one shared orthogonal basis map U and the zero-ground embedding explicit. -/
theorem residual_transport (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U.transpose * U = 1) (E : Tensor n) (a : Fin n → ℝ) :
    tensorSq (rotateTensor U (groundZero E)) = tensorSq E ∧
    matrixSq (tensorSlice (rotateTensor U (groundZero E)) (U.mulVec (residualVector a))) =
      matrixSq (tensorSlice E a) := by
  constructor
  · rw [tensorSq_rotateTensor U hU, tensorSq_groundZero]
  · rw [matrixSq_slice_rotateTensor U hU, matrixSq_slice_groundZero]

end C145DRE8

end
