/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ChebyshevEvenGram
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Degree-one Gram factors of the input and its complement -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

theorem booleanGram_fromCols {n : ℕ} {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (F : Matrix ι κ (BooleanPolynomial n)) (H : Matrix ι μ (BooleanPolynomial n)) :
    booleanGram (Matrix.fromCols F H) = booleanGram F + booleanGram H := by
  apply Matrix.ext
  intro i j
  simp [booleanGram, Matrix.fromCols, Fintype.sum_sum_type]

theorem booleanCompression_gram (n d : ℕ) (R : Matrix (Fin d) (Fin n × Fin d) ℝ) :
    ∃ F : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) 1) ∧ booleanCompression n d R = booleanGram F := by
  let Z := booleanSelectionMatrix n d
  let A := constantBooleanMatrix n R
  refine ⟨A * Z, ?_, ?_⟩
  · have hh := booleanMatrix_mul_degree A Z (constantBooleanMatrix_degree n R)
      (booleanSelectionMatrix_degree n d)
    simpa only [zero_add] using hh
  · change A * Z * A.transpose = (A * Z) * (A * Z).transpose
    rw [Matrix.transpose_mul, booleanSelectionMatrix_transpose]
    symm
    calc
      _ = A * (Z * Z) * A.transpose := by simp only [Matrix.mul_assoc, Z]
      _ = _ := by rw [booleanSelectionMatrix_idempotent]

theorem booleanCompression_complement_gram (n d : ℕ)
    (R : Matrix (Fin d) (Fin n × Fin d) ℝ) (hR : (1 - R * R.transpose).PosSemidef) :
    ∃ F : Matrix (Fin d) ((Fin n × Fin d) ⊕ Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) 1) ∧ 1 - booleanCompression n d R = booleanGram F := by
  obtain ⟨H, hH⟩ := posSemidef_exists_gram (1 - R * R.transpose) hR
  let Z := booleanSelectionMatrix n d
  let A := constantBooleanMatrix n R
  let K := constantBooleanMatrix n H
  let F := A * (1 - Z)
  have hZt : Z.transpose = Z := booleanSelectionMatrix_transpose n d
  have hZ : Z * Z = Z := booleanSelectionMatrix_idempotent n d
  have hCt : (1 - Z).transpose = 1 - Z := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hZt]
  have hC : (1 - Z) * (1 - Z) = 1 - Z := by
    calc
      _ = 1 - Z - Z + Z * Z := by noncomm_ring
      _ = _ := by rw [hZ]; abel
  have hFG : booleanGram F = A * A.transpose - booleanCompression n d R := by
    change (A * (1 - Z)) * (A * (1 - Z)).transpose =
      A * A.transpose - A * Z * A.transpose
    rw [Matrix.transpose_mul, hCt]
    calc
      _ = A * ((1 - Z) * (1 - Z)) * A.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hC, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  have hKG : booleanGram K = 1 - A * A.transpose := by
    have he := congrArg (constantBooleanMatrix n) hH
    rw [constantBooleanMatrix_sub, constantBooleanMatrix_one, constantBooleanMatrix_mul,
      constantBooleanMatrix_transpose, constantBooleanMatrix_mul,
      constantBooleanMatrix_transpose] at he
    exact he.symm
  refine ⟨Matrix.fromCols F K, ?_, ?_⟩
  · intro i a
    cases a with
    | inl a =>
      have hCD : ∀ i j, BooleanDegreeLE ((1 - Z) i j) 1 := fun i j ↦
        booleanDegreeLE_sub (booleanDegreeLE_mono (booleanMatrix_one_degree n i j) (by omega))
          (booleanSelectionMatrix_degree n d i j)
      exact booleanDegreeLE_mono (booleanMatrix_mul_degree A (1 - Z)
        (constantBooleanMatrix_degree n R) hCD i a) (by omega)
    | inr a => exact booleanDegreeLE_mono (constantBooleanMatrix_degree n H i a) (by omega)
  · rw [booleanGram_fromCols, hFG, hKG]
    abel

/-- An arbitrary admissible PSD linear Boolean input has a degree-one Gram factor. -/
theorem booleanLinearMatrix_gram {n d : ℕ} (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) :
    ∃ F : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) 1) ∧ booleanLinearMatrix E = booleanGram F := by
  choose S hS using fun a ↦ posSemidef_exists_gram (E a) (hE a)
  obtain ⟨F, hF, he⟩ := booleanCompression_gram n d (gramBlockRow S)
  refine ⟨F, hF, ?_⟩
  simpa only [booleanCompression_blockRow, ← hS] using he

/-- The complement has a degree-one Gram factor with the exact slack contribution. -/
theorem booleanLinearMatrix_complement_gram {n d : ℕ}
    (E : Fin n → Matrix (Fin d) (Fin d) ℝ) (hE : ∀ a, (E a).PosSemidef)
    (hmean : (1 - ∑ a, E a).PosSemidef) :
    ∃ F : Matrix (Fin d) ((Fin n × Fin d) ⊕ Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) 1) ∧ 1 - booleanLinearMatrix E = booleanGram F := by
  choose S hS using fun a ↦ posSemidef_exists_gram (E a) (hE a)
  have hR : (1 - gramBlockRow S * (gramBlockRow S).transpose).PosSemidef := by
    rw [gramBlockRow_mul_transpose]
    simpa only [← hS] using hmean
  obtain ⟨F, hF, he⟩ := booleanCompression_complement_gram n d (gramBlockRow S) hR
  refine ⟨F, hF, ?_⟩
  simpa only [booleanCompression_blockRow, ← hS] using he

end NoncommutativeAMGM
