/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.BooleanDegree
public import Mathlib.Data.Matrix.Basic

/-! # Degree arithmetic and constant matrices over the Boolean algebra -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- Embed a real matrix entrywise as constant Boolean polynomials. -/
noncomputable def constantBooleanMatrix (n : ℕ) {ι κ : Type*} (A : Matrix ι κ ℝ) :
    Matrix ι κ (BooleanPolynomial n) := A.map (algebraMap ℝ (BooleanPolynomial n))

theorem constantBooleanMatrix_degree (n : ℕ) {ι κ : Type*} (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    BooleanDegreeLE (constantBooleanMatrix n A i j) 0 := by
  simpa only [constantBooleanMatrix, Matrix.map_apply, Algebra.algebraMap_eq_smul_one] using
    booleanDegreeLE_smul (A i j) (booleanDegreeLE_one n)

theorem booleanMatrix_mul_degree {n d e : ℕ} {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ (BooleanPolynomial n)) (B : Matrix κ μ (BooleanPolynomial n))
    (hA : ∀ i j, BooleanDegreeLE (A i j) d) (hB : ∀ i j, BooleanDegreeLE (B i j) e) :
    ∀ i j, BooleanDegreeLE ((A * B) i j) (d + e) := by
  intro i j
  apply booleanDegreeLE_sum
  intro a _
  exact booleanDegreeLE_mul (hA i a) (hB a j)

theorem constantBooleanMatrix_mul (n : ℕ) {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) :
    constantBooleanMatrix n (A * B) = constantBooleanMatrix n A * constantBooleanMatrix n B := by
  exact Matrix.map_mul

theorem constantBooleanMatrix_transpose (n : ℕ) {ι κ : Type*} (A : Matrix ι κ ℝ) :
    constantBooleanMatrix n A.transpose = (constantBooleanMatrix n A).transpose := rfl

theorem constantBooleanMatrix_one (n : ℕ) {ι : Type*} [DecidableEq ι] :
    constantBooleanMatrix n (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem constantBooleanMatrix_sub (n : ℕ) {ι κ : Type*} (A B : Matrix ι κ ℝ) :
    constantBooleanMatrix n (A - B) = constantBooleanMatrix n A - constantBooleanMatrix n B := by
  apply Matrix.ext
  intro i j
  exact map_sub (algebraMap ℝ (BooleanPolynomial n)) (A i j) (B i j)

/-- The diagonal Boolean selection matrix in the square-root block construction. -/
noncomputable def booleanSelectionMatrix (n d : ℕ) :
    Matrix (Fin n × Fin d) (Fin n × Fin d) (BooleanPolynomial n) :=
  diagonal (fun i ↦ booleanVar i.1)

theorem booleanSelectionMatrix_transpose (n d : ℕ) :
    (booleanSelectionMatrix n d).transpose = booleanSelectionMatrix n d := by
  exact diagonal_transpose _

theorem booleanSelectionMatrix_idempotent (n d : ℕ) :
    booleanSelectionMatrix n d * booleanSelectionMatrix n d = booleanSelectionMatrix n d := by
  rw [booleanSelectionMatrix, diagonal_mul_diagonal]
  congr 1
  funext i
  simpa only [pow_two] using booleanVar_sq i.1

theorem booleanSelectionMatrix_degree (n d : ℕ) (i j : Fin n × Fin d) :
    BooleanDegreeLE (booleanSelectionMatrix n d i j) 1 := by
  classical
  unfold booleanSelectionMatrix
  rw [diagonal_apply]
  split_ifs
  · exact booleanDegreeLE_monomial _ _ (by simp)
  · exact booleanDegreeLE_zero _ _

/-- Apply a scalar Boolean linear functional to every entry of a matrix. -/
noncomputable def booleanMatrixImage {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (M : Matrix ι κ (BooleanPolynomial n)) :
    Matrix ι κ ℝ := fun i j ↦ L (M i j)

/-- A rectangular Boolean matrix times its transpose. -/
noncomputable def booleanGram {n : ℕ} {ι κ : Type*} [Fintype κ]
    (F : Matrix ι κ (BooleanPolynomial n)) : Matrix ι ι (BooleanPolynomial n) :=
  fun i j ↦ ∑ a, F i a * F j a

theorem booleanMatrixImage_one {n : ℕ} {ι : Type*} [DecidableEq ι]
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (hL : L 1 = 1) :
    booleanMatrixImage L (1 : Matrix ι ι (BooleanPolynomial n)) = 1 := by
  apply Matrix.ext
  intro i j
  change L ((1 : Matrix ι ι (BooleanPolynomial n)) i j) = (1 : Matrix ι ι ℝ) i j
  simp only [Matrix.one_apply]
  split_ifs <;> simp [hL]

theorem booleanMatrixImage_add {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (A B : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage L (A + B) = booleanMatrixImage L A + booleanMatrixImage L B := by
  apply Matrix.ext
  intro i j
  exact map_add L (A i j) (B i j)

theorem booleanMatrixImage_sub {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (A B : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage L (A - B) = booleanMatrixImage L A - booleanMatrixImage L B := by
  apply Matrix.ext
  intro i j
  exact map_sub L (A i j) (B i j)

theorem booleanGram_smul {n : ℕ} {ι κ : Type*} [Fintype κ]
    (a : ℝ) (F : Matrix ι κ (BooleanPolynomial n)) :
    booleanGram (a • F) = (a * a) • booleanGram F := by
  change (a • F) * (a • F).transpose = (a * a) • (F * F.transpose)
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem booleanGram_mul {n : ℕ} {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (U : Matrix ι κ (BooleanPolynomial n)) (F : Matrix κ μ (BooleanPolynomial n)) :
    booleanGram (U * F) = U * booleanGram F * U.transpose := by
  change (U * F) * (U * F).transpose = U * (F * F.transpose) * U.transpose
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end NoncommutativeAMGM
