/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order
public import LeanPool.Besicovitch.SixPoint.NormEstimates

/-!
# Shared rank-one matrix corrections

Certificate families use these signed corrections to dominate their off-diagonal residuals.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

variable {ι : Type*} [DecidableEq ι]

/-- Sign used for the off-diagonal entry of a rank-one correction. -/
def pairSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

/-- The two-coordinate vector for a signed matrix correction. -/
def pairVector (r : ℝ) (i j : ι) : ι → ℝ :=
  fun k ↦ if k = i then 1 else if k = j then pairSign r else 0

/-- A positive semidefinite rank-one correction. -/
def pairCorrection (r : ℝ) (i j : ι) : Matrix ι ι ℝ :=
  |r| • Matrix.vecMulVec (pairVector r i j) (pairVector r i j)

/-- The correction matrix is positive semidefinite. -/
theorem pairCorrection_posSemidef (r : ℝ) (i j : ι) :
    (pairCorrection r i j).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (pairVector r i j)).smul (abs_nonneg r)

/-- Complete a five-vector certificate with positive two-coordinate corrections. -/
def fivePairCompletion (base : Matrix (Fin 5) (Fin 5) ℝ)
    (residual : Fin 5 → Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  base +
    pairCorrection (residual 0 1) 0 1 +
    pairCorrection (residual 0 2) 0 2 +
    pairCorrection (residual 0 3) 0 3 +
    pairCorrection (residual 0 4) 0 4 +
    pairCorrection (residual 1 2) 1 2 +
    pairCorrection (residual 1 3) 1 3 +
    pairCorrection (residual 1 4) 1 4 +
    pairCorrection (residual 2 3) 2 3 +
    pairCorrection (residual 2 4) 2 4 +
    pairCorrection (residual 3 4) 3 4

/-- Pairwise completion preserves positive semidefiniteness. -/
theorem fivePairCompletion_posSemidef {base : Matrix (Fin 5) (Fin 5) ℝ}
    (hbase : base.PosSemidef) (residual : Fin 5 → Fin 5 → ℝ) :
    (fivePairCompletion base residual).PosSemidef := by
  have h := hbase.add (pairCorrection_posSemidef (residual 0 1) 0 1)
  have h := h.add (pairCorrection_posSemidef (residual 0 2) 0 2)
  have h := h.add (pairCorrection_posSemidef (residual 0 3) 0 3)
  have h := h.add (pairCorrection_posSemidef (residual 0 4) 0 4)
  have h := h.add (pairCorrection_posSemidef (residual 1 2) 1 2)
  have h := h.add (pairCorrection_posSemidef (residual 1 3) 1 3)
  have h := h.add (pairCorrection_posSemidef (residual 1 4) 1 4)
  have h := h.add (pairCorrection_posSemidef (residual 2 3) 2 3)
  have h := h.add (pairCorrection_posSemidef (residual 2 4) 2 4)
  exact h.add (pairCorrection_posSemidef (residual 3 4) 3 4)

omit [DecidableEq ι] in
/-- The signed absolute value recovers the original residual. -/
theorem abs_mul_pairSign (r : ℝ) : |r| * pairSign r = r := by
  by_cases hr : 0 ≤ r
  · simp [pairSign, hr, abs_of_nonneg hr]
  · simp [pairSign, hr, abs_of_neg (lt_of_not_ge hr)]

/-- The corrected off-diagonal entry. -/
@[simp]
theorem pairCorrection_apply_pair (r : ℝ) {i j : ι} (hij : i ≠ j) :
    pairCorrection r i j i j = r := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hij.symm, abs_mul_pairSign]

/-- The transposed corrected off-diagonal entry. -/
@[simp]
theorem pairCorrection_apply_pair_rev (r : ℝ) {i j : ι} (hij : i ≠ j) :
    pairCorrection r i j j i = r := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hij.symm, abs_mul_pairSign, mul_comm]

/-- The first diagonal entry is the residual magnitude. -/
@[simp]
theorem pairCorrection_apply_left_left (r : ℝ) {i j : ι} :
    pairCorrection r i j i i = |r| := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector]

/-- The second diagonal entry is the residual magnitude. -/
@[simp]
theorem pairCorrection_apply_right_right (r : ℝ) {i j : ι} (hij : i ≠ j) :
    pairCorrection r i j j j = |r| := by
  by_cases hr : 0 ≤ r <;>
    simp [pairCorrection, Matrix.vecMulVec, pairVector, pairSign, hij.symm, hr]

/-- Other rows of the correction vanish. -/
@[simp]
theorem pairCorrection_apply_zero_left (r : ℝ) {i j k l : ι}
    (hki : k ≠ i) (hkj : k ≠ j) : pairCorrection r i j k l = 0 := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hki, hkj]

/-- Other columns of the correction vanish. -/
@[simp]
theorem pairCorrection_apply_zero_right (r : ℝ) {i j k l : ι}
    (hli : l ≠ i) (hlj : l ≠ j) : pairCorrection r i j k l = 0 := by
  simp [pairCorrection, Matrix.vecMulVec, pairVector, hli, hlj]

omit [DecidableEq ι] in
/-- A positive semidefinite matrix has a nonnegative sum against vector inner products. -/
theorem matrix_inner_sum_nonneg [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {matrix : Matrix ι ι ℝ} (hmatrix : matrix.PosSemidef)
    (v : ι → E) : 0 ≤ ∑ i, ∑ j, matrix i j * ⟪v i, v j⟫_ℝ := by
  classical
  have h := (hmatrix.hadamard (Matrix.posSemidef_gram ℝ v)).dotProduct_mulVec_nonneg
    (fun _ ↦ (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using h

/-- Gram matrix entry of a three-row factor, evaluated over ℚ. -/
def rationalGramEntry (factor : Fin 3 → Fin 5 → ℚ) (i j : Fin 5) : ℚ :=
  ∑ k, factor k i * factor k j

/-- Computing the Gram entry in the rationals commutes with casting to the reals. -/
theorem cast_rationalGramEntry (factor : Fin 3 → Fin 5 → ℚ) (i j : Fin 5) :
    (rationalGramEntry factor i j : ℝ) =
      (∑ k, Matrix.vecMulVec (fun a ↦ (factor k a : ℝ)) (fun a ↦ (factor k a : ℝ))) i j := by
  simp only [rationalGramEntry, Matrix.sum_apply, Matrix.vecMulVec_apply, Fin.sum_univ_three,
    Rat.cast_add, Rat.cast_mul]

/-- Each diagonal entry gains the absolute residual for each pair incident to its index.
The residual is taken in upper-triangular order, as in `fivePairCompletion`. -/
def rationalCorrectedDiagonal (factor : Fin 3 → Fin 5 → ℚ)
    (target : Matrix (Fin 5) (Fin 5) ℚ) (offset : ℚ) : Fin 5 → ℚ :=
  let gram := rationalGramEntry factor
  let correction i j := |target i j - gram i j|
  ![gram 0 0 + offset + correction 0 1 + correction 0 2 + correction 0 3 + correction 0 4,
    gram 1 1 + offset + correction 0 1 + correction 1 2 + correction 1 3 + correction 1 4,
    gram 2 2 + offset + correction 0 2 + correction 1 2 + correction 2 3 + correction 2 4,
    gram 3 3 + offset + correction 0 3 + correction 1 3 + correction 2 3 + correction 3 4,
    gram 4 4 + offset + correction 0 4 + correction 1 4 + correction 2 4 + correction 3 4]

end LeanPool.Besicovitch
