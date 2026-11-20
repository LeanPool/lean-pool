/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.BooleanMatrix
public import LeanPool.NoncommutativeAMGM.MatrixGramFactor

/-! # The degree-one Gram factor of the Boolean matrix variance -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix

/-- The algebraic projection/compression identity behind the even Chebyshev square factor. -/
theorem matrix_projection_variance_gram {A : Type*} [CommRing A]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (R : Matrix ι κ A) (Z Q : Matrix κ κ A)
    (hZt : Z.transpose = Z) (hZ : Z * Z = Z)
    (hQ : Q * Q.transpose = 1 - R.transpose * R) :
    R * Z * R.transpose - (R * Z * R.transpose) * (R * Z * R.transpose) =
      (R * Z * Q) * (R * Z * Q).transpose := by
  symm
  calc
    _ = R * Z * (Q * Q.transpose) * Z * R.transpose := by
      simp only [transpose_mul, hZt, Matrix.mul_assoc]
    _ = R * Z * (1 - R.transpose * R) * Z * R.transpose := by rw [hQ]
    _ = R * Z * Z * R.transpose - R * Z * (R.transpose * R) * Z * R.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one]
    _ = _ := by
      have he : R * Z * Z = R * Z := by rw [Matrix.mul_assoc, hZ]
      rw [he]
      simp only [Matrix.mul_assoc]

/-- The Boolean compression of a real rectangular matrix through the selection projection. -/
noncomputable def booleanCompression (n d : ℕ) (R : Matrix (Fin d) (Fin n × Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (BooleanPolynomial n) :=
  constantBooleanMatrix n R * booleanSelectionMatrix n d * (constantBooleanMatrix n R).transpose

/-- The variance `B-B²` has an actual Boolean Gram factor whose entries have degree at most one. -/
theorem booleanCompression_variance_factor (n d : ℕ)
    (R : Matrix (Fin d) (Fin n × Fin d) ℝ) (hR : (1 - R * R.transpose).PosSemidef) :
    ∃ G : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (G i a) 1) ∧
      booleanCompression n d R - booleanCompression n d R * booleanCompression n d R =
        booleanGram G := by
  obtain ⟨Q, hQ⟩ := rectangular_contraction_defect_factor R hR
  let G := constantBooleanMatrix n R * booleanSelectionMatrix n d * constantBooleanMatrix n Q
  refine ⟨G, ?_, ?_⟩
  · have hdeg := booleanMatrix_mul_degree
      (constantBooleanMatrix n R * booleanSelectionMatrix n d) (constantBooleanMatrix n Q)
      (booleanMatrix_mul_degree _ _ (constantBooleanMatrix_degree n R)
        (booleanSelectionMatrix_degree n d)) (constantBooleanMatrix_degree n Q)
    simpa only [zero_add, add_zero] using hdeg
  · have hQB : constantBooleanMatrix n Q * (constantBooleanMatrix n Q).transpose =
        1 - (constantBooleanMatrix n R).transpose * constantBooleanMatrix n R := by
      have he := congrArg (constantBooleanMatrix n) hQ
      rw [constantBooleanMatrix_sub, constantBooleanMatrix_one,
        constantBooleanMatrix_mul, constantBooleanMatrix_transpose,
        constantBooleanMatrix_mul, constantBooleanMatrix_transpose] at he
      exact he.symm
    exact matrix_projection_variance_gram _ _ _ (booleanSelectionMatrix_transpose n d)
      (booleanSelectionMatrix_idempotent n d) hQB

end NoncommutativeAMGM
