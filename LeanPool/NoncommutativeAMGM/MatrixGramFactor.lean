/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.MatrixSlicePositivity

/-! # Real Gram factorizations and rectangular contractions -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix
open scoped MatrixOrder

/-- A positive semidefinite real matrix has an actual real Gram factor. -/
theorem posSemidef_exists_gram {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) : ∃ R : Matrix ι ι ℝ, A = R * R.transpose := by
  classical
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hA.nonneg
  refine ⟨R, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hR

/-- A rectangular contraction satisfies both of the corresponding Gram inequalities. -/
theorem rectangular_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ)
    (hR : (1 - R * R.transpose).PosSemidef) : (1 - R.transpose * R).PosSemidef := by
  let : Invertible (1 : Matrix ι ι ℝ) := invertibleOne
  let : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have hb : (fromBlocks (1 : Matrix ι ι ℝ) R R.conjTranspose
      (1 : Matrix κ κ ℝ)).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ _ R Matrix.PosDef.one).mpr
    simpa only [inv_one, Matrix.mul_one, conjTranspose_eq_transpose_of_trivial] using hR
  have h := (Matrix.PosDef.fromBlocks₁₁ R (1 : Matrix κ κ ℝ) Matrix.PosDef.one).mp hb
  simpa only [inv_one, Matrix.mul_one, conjTranspose_eq_transpose_of_trivial] using h

/-- The defect of a rectangular contraction has a real Gram factor. -/
theorem rectangular_contraction_defect_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ)
    (hR : (1 - R * R.transpose).PosSemidef) :
    ∃ Q : Matrix κ κ ℝ, 1 - R.transpose * R = Q * Q.transpose :=
  posSemidef_exists_gram _ (rectangular_contraction R hR)

end NoncommutativeAMGM
